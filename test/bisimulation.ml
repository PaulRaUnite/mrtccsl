open Mrtccsl
open Common
open Prelude
module N = Number.Rational
module NaiveBackend = Backend.Naive.Make (String) (N)
module Label = NaiveBackend.L

module Trace = struct
  include Trace.MakeIO (N) (Label)

  type t = trace
end

module DiagramBackend = struct
  module Acceptance = struct
    include Backend.Machine.Diagram.Acceptance

    let accept_trace m trace =
      accept_trace
        m
        (Seq.map
           Trace.(
             fun { label; time } ->
               let label =
                 STS.Interpretation.VarMap.of_seq
                   (Seq.map (fun c -> c, true) (Label.to_seq label))
               in
               { label; time })
           trace)
    ;;
  end

  module Simulation = struct
    include Backend.Machine.Diagram.Simulation

    let gen_trace strategy repr =
      let trace = gen_trace strategy repr in
      Seq.map
        (fun Trace.{ label; time } ->
           Trace.
             { label =
                 label
                 |> Interpretation.VarMap.to_seq
                 |> Seq.filter_map (fun (c, b) -> if b then Some c else None)
                 |> Label.of_seq
             ; time
             })
        trace
    ;;
  end
end

module NumStrat = Backend.Strategy.Num (NaiveBackend.N) (NaiveBackend.NI)
module LabelStrat = Backend.Strategy.Solution (NaiveBackend.L) (NaiveBackend.NI)
open Number

let leap_strat ~rounding_error ~upper_bound =
  NumStrat.random_leap
    ~upper_bound
    ~ceil:(Rational.round_up rounding_error)
    ~floor:(Rational.round_down rounding_error)
    ~rand:Rational.random
;;

let random_strat ~rounding_error ~upper_bound =
  LabelStrat.refuse_empty
  @@ LabelStrat.random_label (leap_strat ~rounding_error ~upper_bound)
;;

let specs =
  [ (* "sequence_diagram" *)
    "prec"
  ; "delay"
  ; "causality_chain"
  ; "exclusion"
  ; "synch"
  ; "fastslow"
  ; "sample_period"
  ; "rt"
  ; "forbid_allow"
  ; "pool"
  ]
;;

let rounding_error = Rational.of_frac 1 1000
let upper_bound = Rational.of_int 1000

module DiagramStrat =
  Backend.Strategy.Num (Rational) (Backend.Machine.Diagram.Simulation.RI)
let diagram_leap =
  DiagramStrat.random_leap
    ~upper_bound
    ~ceil:(Rational.round_up rounding_error)
    ~floor:(Rational.round_down rounding_error)
    ~rand:Rational.random
;;

let trace_length = 10000

let from_naive_to_diagram name spec =
  let clocks = List.sort_uniq String.compare @@ CCSL.Language.Specification.clocks spec in
  let naive = NaiveBackend.of_spec spec in
  let trace = NaiveBackend.gen_trace (random_strat ~rounding_error ~upper_bound) naive in
  let trace = Seq.take 10000 trace in
  let trace = Trace.persist ~size_hint:10000 trace in
  print_endline "trace generated";
  if Seq.length trace <> trace_length
  then (
    print_endline "naive trace is short";
    Trace.CSV.write
      (open_out (Printf.sprintf "test/bisimulation/debug/%s_naive.trace" name))
      clocks
      trace);
  let diagram = DiagramBackend.Acceptance.of_spec spec in
  print_endline "diagram built";
  let accepted = DiagramBackend.Acceptance.accept_trace diagram trace in
  Printf.printf "naive->diagram : %b\n" (Result.is_ok accepted);
  match accepted with
  | Error (_, atom_index) ->
    Trace.CSV.write
      (open_out (Printf.sprintf "test/bisimulation/debug/%s_naive.trace" name))
      clocks
      trace;
    let diagram, cstr_index = diagram in
    let graph = STS.Interpretation.Diagram.to_graph ~cstr_index ~atom_index diagram in
    STS.Interpretation.Diagram.Dot.output_graph
      (open_out (Printf.sprintf "test/bisimulation/debug/%s_accept.dot" name))
      graph
  | _ -> ()
;;

let from_diagram_to_naive name spec =
  let clocks = List.sort_uniq String.compare @@ CCSL.Language.Specification.clocks spec in
  let diagram = List.hd @@ DiagramBackend.Simulation.sim_of_spec spec in
  print_endline "diagram built";
  let trace = DiagramBackend.Simulation.gen_trace diagram_leap diagram in
  let trace = Seq.take 10000 trace in
  let trace = Trace.persist ~size_hint:10000 trace in
  print_endline "trace generated";
  if Seq.length trace <> trace_length
  then (
    print_endline "diagram trace is short";
    Trace.CSV.write
      (open_out (Printf.sprintf "test/bisimulation/debug/%s_diagram.trace" name))
      clocks
      trace);
  let naive = NaiveBackend.of_spec spec in
  let accepted = NaiveBackend.accept_trace naive trace in
  Printf.printf "diagram->naive : %b\n" accepted;
  if not accepted
  then (
    Trace.CSV.write
      (open_out (Printf.sprintf "test/bisimulation/debug/%s_diagram.trace" name))
      clocks
      trace;
    let STS.Interpretation.Diagram.{ diagram; _ }, cstr_index = diagram in
    let graph = STS.Interpretation.Diagram.to_graph ~cstr_index diagram in
    STS.Interpretation.Diagram.Dot.output_graph
      (open_out (Printf.sprintf "test/bisimulation/debug/%s_simulate.dot" name))
      graph)
;;

module Opt = Mrtccsl.Optimization.Order.Make (String)

let _ =
  Ocolor_format.prettify_formatter Format.std_formatter;
  List.iter
    (fun name ->
       Printf.printf "testing file: %s\n" name;
       let path = Printf.sprintf "test/bisimulation/%s.mrtccsl" name in
       let _, m = Mrtccslparsing.load_with_string path Format.std_formatter in
       let spec = m.structure in
       let spec = Opt.optimize spec in
       from_naive_to_diagram name spec;
       from_diagram_to_naive name spec)
    specs
;;
