open Common
open Prelude
open Aux
open Cmdliner
open Cmdliner.Term.Syntax

let hist1_arg =
  Arg.(
    required
    & pos 0 (some inline_in_channel) None
    & info [] ~doc:"First histogram file." ~docv:"HIST1")
;;

let hist2_arg =
  Arg.(
    required
    & pos 1 (some inline_in_channel) None
    & info [] ~doc:"Second histogram file." ~docv:"HIST2")
;;

let scale_arg =
  Arg.(
    required
    & opt (some int) None
    & info [ "s"; "scale" ] ~doc:"Scale used for the histograms." ~docv:"SCALE")
;;

let confidence_arg =
  Arg.(
    required
    & opt (some float) None
    & info [ "c"; "conf" ] ~doc:"Confidence level for testing" ~docv:"CONF")
;;

let read_histogram_csv ~scale file =
  let csv = Csv.of_channel ~has_header:true file in
  let header = Csv.Rows.header csv in
  let total_column = List.find_index (String.equal "total") header in
  let bin_column = List.find_index (String.equal "bin") header in
  match total_column, bin_column with
  | Some total_column, Some bin_column ->
    let arr = Dynarray.create () in
    Csv.Rows.iter
      ~f:(fun row ->
        let bin = Float.of_string (Csv.Row.get row bin_column)
        and total = Float.of_string (Csv.Row.get row total_column) in
        let total = Int.of_float (Float.mul total scale) in
        for _ = 1 to total do
          Dynarray.add_last arr bin
        done)
      csv;
    Dynarray.to_array arr
  | _ -> failwith "incorrect histogram format, expected bin and total columns"
;;

let do_command ~file1 ~file2 ~scale ~alpha =
  let scale = Float.of_int scale in
  let hist1_samples = read_histogram_csv ~scale file1 in
  let hist2_samples = read_histogram_csv ~scale file2 in
  let hypothesis = Owl_stats.ks2_test ~alpha hist1_samples hist2_samples in
  Owl_stats.pp_hypothesis Format.std_formatter hypothesis;
  Format.pp_print_newline Format.std_formatter ()
;;

let cmd =
  let man = [ `S Manpage.s_description; `P "$(cmd) computes reaction time" ] in
  Cmd.v
    (Cmd.info
       "compare"
       ~version
       ~doc:"Performs Kolmogorov-Smirnov test on two histograms."
       ~man)
  @@ Term.ret
  @@
  let+ file1 = hist1_arg
  and+ file2 = hist2_arg
  and+ scale = scale_arg
  and+ alpha = confidence_arg in
  let file1 = get_in_channel file1
  and file2 = get_in_channel file2 in
  `Ok (Ok (do_command ~file1 ~file2 ~scale ~alpha))
;;

let main () = Cmd.eval_result cmd
