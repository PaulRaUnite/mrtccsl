open Common
open Prelude
open Mrtccsl
open Number
module Clock = String

module L = struct
  module E = Clock
  include Set.Make (Clock)
end

module IO = Common.Trace.MakeIO (Rational) (L)
open Aux

type check_result =
  { satisfies : bool
  ; message : string
  }

let print_result ch { satisfies; message } =
  Printf.fprintf
    ch
    "{\"satisfies\": %s, \"message\": \"%s\"}\n"
    (if satisfies then "true" else "false")
    message
;;

let do_command ~reaction ~target_prob ~input ~output =
  let csv = Csv.of_channel ~has_header:true input in
  let rows = Iter.from_labelled_iter (Csv.Rows.iter csv) in
  let check_prob state row =
    let bin = Rational.of_string @@ Csv.Row.get row 0
    and prob = Rational.of_string @@ Csv.Row.get row 1 in
    match state with
    | Either.Left total_prob, _ ->
      let total_prob = Rational.(prob + total_prob) in
      if Rational.Operators.(bin <= reaction && total_prob >= target_prob)
      then Either.Right (bin, total_prob), bin
      else Either.Left total_prob, bin
    | Either.Right x, _ -> Either.Right x, bin
  in
  let result, last_bin =
    Iter.fold check_prob (Either.Left Rational.zero, Rational.zero) rows
  in
  let result =
    match result with
    | Either.Left _ -> { satisfies = false; message = Printf.sprintf "" }
    | Either.Right (init_bin, prob) ->
      { satisfies = true
      ; message =
          Rational.(
            Printf.sprintf
              "margin >= %s with probability %s"
              (to_string (last_bin - init_bin))
              (to_string (one - prob)))
      }
  in
  print_result output result;
  ()
;;

open Cmdliner
open Cmdliner.Term.Syntax

let reaction_arg =
  Arg.(
    value
    & pos 0 (some rational) None
    & info [] ~doc:"The reaction to check." ~docv:"REACT")
;;

let probability_arg =
  Arg.(
    value
    & pos 1 (some rational) None
    & info [] ~doc:"The probability to check." ~docv:"PROB")
;;

let input_arg =
  Arg.(
    value
    & pos 2 (some inline_in_channel) None
    & info
        []
        ~doc:"Histogram to be checked. Skip or use - to indicate stdin."
        ~docv:"HISTOGRAM")
;;

let output_arg =
  Arg.(
    value
    & opt (some inline_out_channel) None
    & info
        [ "o"; "output" ]
        ~doc:"File with check results. Skip or use - to indicate stdout."
        ~docv:"OUTPUT")
;;

let cmd =
  let man = [ `S Manpage.s_description; `P "$(cmd) computes reaction time" ] in
  Cmd.v
    (Cmd.info
       "reaction_check"
       ~version
       ~doc:"Check if reaction time satisfies a property `<= REACT` in PROB cases"
       ~man)
  @@ Term.ret
  @@
  let+ input_file = input_arg
  and+ reaction = reaction_arg
  and+ target_prob = probability_arg
  and+ output_file = output_arg in
  let input = Option.value ~default:stdin (Option.map Aux.get_in_channel input_file) in
  let output =
    Option.value ~default:stdout (Option.map Aux.get_out_channel output_file)
  in
  `Ok
    (Ok
       (do_command
          ~reaction:(Option.unwrap ~expect:"Reaction bound present." reaction)
          ~target_prob:(Option.unwrap ~expect:"Probability bound present" target_prob)
          ~input
          ~output))
;;

let main () = Cmd.eval_result cmd
