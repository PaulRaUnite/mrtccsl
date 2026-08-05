open Common.Prelude
open Common.Number

let jitter i = Printf.sprintf "j_%i" i
let out i = Printf.sprintf "out_%i" i
let offset i = Printf.sprintf "phi_%i" i

let make_spec size =
  let clock =
    List.init size (fun i ->
      Mrtccsl.CCSL.Language.Cstr.AbsPeriodic
        { out = out i
        ; period = Rational.of_int 5
        ; error = Var (jitter i)
        ; offset = Var (offset i)
        })
  in
  let duration =
    List.flatten
    @@ List.init size (fun i ->
      Mrtccsl.CCSL.Language.Cstr.
        [ NumRelation (jitter i, `LessEq, Const (Rational.of_int 1))
        ; NumRelation (jitter i, `MoreEq, Const (Rational.of_int (-1)))
        ; NumRelation (offset i, `LessEq, Const (Rational.of_int 1))
        ; NumRelation (offset i, `MoreEq, Const (Rational.of_int 0))
        ])
  in
  let probabilistic =
    List.flatten
    @@ List.init size (fun i ->
      Mrtccsl.CCSL.Language.Cstr.
        [ ContinuousValued { name = jitter i; dist = Uniform }
        ; ContinuousValued { name = offset i; dist = Uniform }
        ])
  in
  let spec =
    Mrtccsl.CCSL.Language.Specification.{ clock; duration; integer = []; probabilistic }
  in
  spec
;;

module Sim = Mrtccsl.Backend.Naive.Make (String) (Rational)
module SolStrat = Mrtccsl.Backend.Strategy.Solution (Sim.L) (Sim.NI)
module NumStrat = Mrtccsl.Backend.Strategy.Num (Rational) (Sim.NI)

let upper_bound = Rational.of_int 10

let convert_step =
  Common.Trace.(
    fun { label; time } ->
      let label =
        STS.Interpretation.VarMap.of_seq (Seq.map (fun c -> c, true) (Sim.L.to_seq label))
      in
      { label; time })
;;

let generate_traces ~duplicates ~length spec =
  let simulations = List.init duplicates (fun _ -> Sim.of_spec spec) in
  let traces =
    List.map
      (fun sim ->
         let trace =
           Sim.gen_trace
             (SolStrat.refuse_empty
                (SolStrat.random_label
                   (NumStrat.random_leap
                      ~upper_bound
                      ~ceil:Rational.round_ceil
                      ~floor:Rational.round_floor
                      ~rand:Rational.random)))
             sim
           |> Seq.take length
           |> Seq.map convert_step
           |> Dynarray.of_seq
         in
         if Dynarray.length trace = length
         then trace
         else failwith "trace length does not match")
      simulations
  in
  traces
;;

let memory_size () =
  Gc.full_major ();
  Gc.full_major ();
  let stats = Gc.stat () in
  stats.major_words +. stats.minor_words
;;

type report =
  { build_time : Mtime.span
  ; accept_time : Mtime.span
  ; diagram_memory : float
  }

let accept_traces spec traces =
  let open Mrtccsl.Backend.Machine.Diagram.ParallelAcceptance in
  let memory_before = memory_size () in
  let before_build = Mtime_clock.elapsed () in
  let acceptor = of_spec spec in
  let acceptor_built = Mtime_clock.elapsed () in
  let memory_after = memory_size () in
  let before_accept = Mtime_clock.elapsed () in
  let trace_length = List.length traces in
  let all_correct =
    List.for_all (fun trace -> satisfied_by acceptor (Dynarray.to_seq trace)) traces
  in
  let finished_accept = Mtime_clock.elapsed () in
  if all_correct
  then
    { build_time = Mtime.Span.abs_diff acceptor_built before_build
    ; accept_time =
        Mtime.Span.of_uint64_ns
          (Int64.div
             (Mtime.Span.to_uint64_ns (Mtime.Span.abs_diff finished_accept before_accept))
             (Int64.of_int trace_length))
    ; diagram_memory = memory_after -. memory_before
    }
  else failwith "trace acceptance failed"
;;

let () =
  let sizes = List.init 10 (fun i -> (i + 1) * 10) in
  Printf.printf "size,memory,build_time,accept_time\n";
  List.iter
    (fun size ->
       let spec = make_spec size in
       let traces = generate_traces ~length:10000 ~duplicates:20 spec in
       let stats = accept_traces spec traces in
       Printf.printf
         "%i,%f,%i,%i\n"
         size
         stats.diagram_memory
         (Int64.to_int @@ Mtime.Span.to_uint64_ns stats.build_time)
         (Int64.to_int @@ Mtime.Span.to_uint64_ns stats.accept_time))
    sizes
;;
