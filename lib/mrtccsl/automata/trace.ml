open Prelude

type 'c task =
  { name : string
  ; start : 'c
  ; finish : 'c
  ; release : 'c
  ; deadline : 'c
  }
[@@deriving map]

module type Container = sig
  type 'a t
end

module type Element = sig
  include Interface.Stringable
  include Interface.OrderedType with type t := t
  include Interface.Parseble with type t := t
end

module type Label = sig
  module E : Element

  type t
  type elt := E.t

  val mem : elt -> t -> bool
  val to_iter : t -> (elt -> unit) -> unit
  val of_iter : elt Iter.t -> t
end

module type Timestamp = sig
  type t

  val ( + ) : t -> t -> t
  val ( - ) : t -> t -> t
  val zero : t

  include Interface.Stringable with type t := t
  include Interface.Parseble with type t := t
end

(* module Make (C : Container) (L : Label) (T : Timestamp) = struct
  type t = L.t C.t

  module Export = struct end
  module Import = struct end
end *)

type ('l, 'n) step =
  { label : 'l
  ; time : 'n
  }

module Make (N : Timestamp) (L : Label) = struct
  type nonrec step = (L.t, N.t) step

  module Svgbob = struct
    let print_horizontal ?(numbers = false) ?precision ~tasks clocks formatter trace =
      if List.is_empty clocks
      then ()
      else (
        let clocks =
          clocks
          |> List.to_seq
          |> Seq.filter (fun c ->
            not
              (List.exists
                 (fun { release; start; finish; deadline; _ } ->
                    L.E.compare c release = 0
                    || L.E.compare c start = 0
                    || L.E.compare c finish = 0
                    || L.E.compare c deadline = 0)
                 tasks))
          |> Array.of_seq
        in
        let clock_strs = Array.map L.E.to_string clocks in
        let len = Array.length clocks in
        let biggest_clock =
          clock_strs |> Array.to_seq |> Seq.map String.length |> Seq.fold_left Int.max 0
        in
        let biggest_task_name =
          tasks
          |> List.map (fun { name; _ } -> String.length name)
          |> List.fold_left Int.max 0
        in
        let graph_prefix = Int.max biggest_task_name biggest_clock in
        let buffers =
          Array.init len (fun i ->
            let c = Array.get clock_strs i in
            let b = Buffer.create (graph_prefix + 32) in
            let symbol = if i = 0 then '+' else '|' in
            Printf.bprintf b "%*s %c-" graph_prefix c symbol;
            b)
        and footer = Buffer.create (graph_prefix + 32)
        and history = Buffer.create (graph_prefix + 32) in
        let _ =
          Buffer.add_chars footer graph_prefix ' ';
          Buffer.add_string footer " +-";
          Buffer.add_chars history (graph_prefix + 3) ' '
        in
        let clock_counters = Array.make len 0 in
        let counter i =
          let c = clock_counters.(i) in
          let _ = Array.set clock_counters i (c + 1) in
          c + 1
        in
        let marker i =
          if numbers
          then Int.to_string (counter i)
          else (
            match Int.rem i 6 with
            | 0 -> "*"
            | 1 -> "o"
            | 2 -> "◆"
            | 3 -> ">"
            | 4 -> "O"
            | 5 -> "^"
            | 6 -> "#"
            | _ -> failwith "unreachable")
        in
        let module TMap =
          Map.Make (struct
            type t = L.E.t * L.E.t * L.E.t * L.E.t

            let compare = Tuple.compare_same4 L.E.compare
          end)
        in
        let serialize_label task_state (l, n') =
          (* let delta = N.(n' - n) in *)
          let time_label = N.to_string n' in
          let time_label =
            match precision with
            | Some precision ->
              let dot_index = String.index time_label '.' in
              let right_bound =
                Int.min (String.length time_label) (dot_index + precision + 1)
              in
              String.sub time_label 0 right_bound
            | None -> time_label
          in
          let step_len = String.length time_label + 1 in
          let print_task (({ release; start; finish; deadline; _ } as t), (buf, executes))
            =
            let release_present = L.mem release l
            and start_present = L.mem start l
            and finish_present = L.mem finish l
            and deadline_present = L.mem deadline l in
            let executes = (executes || start_present) && not finish_present in
            let symbol =
              match release_present, deadline_present with
              | true, true -> "╳"
              | true, false -> "("
              | false, true -> ")"
              | false, false ->
                if start_present || finish_present || executes then "#" else "-"
            in
            Buffer.add_string buf symbol;
            if executes
            then Buffer.add_chars buf (step_len - 1) '#'
            else Buffer.add_chars buf (step_len - 1) '-';
            t, (buf, executes)
          in
          let task_state = List.map print_task task_state in
          let print_clock placed i c =
            let buf = Array.get buffers i in
            let symbol, placed =
              if L.mem c l
              then marker i, true
              else if placed
              then "|", true
              else "-", false
            in
            Buffer.add_string buf symbol;
            Buffer.add_chars buf (step_len - String.grapheme_length symbol) '-';
            (*FIXME: numbers can have non-1 width, will crash when number is bigger than window length*)
            placed
          in
          let placed = Seq.fold_lefti print_clock false (Array.to_seq clocks) in
          Buffer.add_string footer (if placed then "┴" else "+");
          Buffer.add_chars footer (step_len - 1) '-';
          Printf.bprintf history "%s " time_label;
          task_state
        in
        let task_state =
          Iter.fold
            serialize_label
            (List.map (fun t -> t, (Buffer.create 32, false)) tasks)
            trace
        in
        let total = Buffer.create 1024 in
        let _ =
          List.iter
            (fun ({ name; _ }, (buf, _)) ->
               Printf.bprintf total "%*s |-" graph_prefix name;
               Buffer.add_buffer total buf;
               Buffer.add_char total '\n';
               Buffer.add_chars total graph_prefix ' ';
               Buffer.add_string total " |\n")
            task_state;
          Array.iter
            (fun b ->
               Buffer.add_buffer total b;
               Buffer.add_char total '\n')
            buffers;
          Buffer.add_buffer total footer;
          Buffer.add_string total ">\n";
          Buffer.add_buffer total history;
          Buffer.add_string total "seconds"
        in
        Format.fprintf formatter "%s" (Buffer.contents total))
    ;;

    let print_vertical ?(numbers = false) ~tasks clocks ch trace =
      if List.is_empty clocks
      then ()
      else (
        let marker =
          if numbers
          then fun _ j -> Int.to_string j
          else
            fun i _ ->
              match Int.rem i 9 with
              | 0 -> "*"
              | 1 -> "o"
              | 2 -> "◆"
              | 3 -> ">"
              | 4 -> "O"
              | 5 -> "^"
              | 6 -> "#"
              | 7 -> "<"
              | 8 -> "v"
              | _ -> failwith "unreachable"
        in
        let clocks =
          clocks
          |> List.filter (fun c ->
            not
              (List.exists
                 (fun { release; start; finish; deadline; _ } ->
                    L.E.compare c release = 0
                    || L.E.compare c start = 0
                    || L.E.compare c finish = 0
                    || L.E.compare c deadline = 0)
                 tasks))
          |> Array.of_list
        in
        let width =
          List.fold_left
            (fun off { name; _ } ->
               Format.fprintf ch "%*s\n" (off + String.grapheme_length name + 1) name;
               off + 8)
            0
            tasks
        in
        let width =
          Array.fold_left
            (fun off clock ->
               let s = L.E.to_string clock in
               Format.fprintf ch "%*s\n" (off + String.grapheme_length s) s;
               off + 2)
            width
            clocks
        in
        let _ =
          for _ = 1 to List.length tasks do
            Format.fprintf ch "-+---+--"
          done
        in
        let _ =
          for _ = 1 to Array.length clocks do
            Format.fprintf ch "+-"
          done
        in
        let _ = Format.fprintf ch "+\n" in
        let[@inline hint] serialize_record (tasks, clocks) (l, n) =
          let new_tasks =
            Array.map
              (fun (({ release; start; finish; deadline; _ } as t), executes, constrains) ->
                 let release_present = L.mem release l
                 and start_present = L.mem start l
                 and finish_present = L.mem finish l
                 and deadline_present = L.mem deadline l in
                 let now_executes = (executes || start_present) && not finish_present
                 and now_constrains =
                   (constrains || release_present) && not deadline_present
                 in
                 let _ =
                   match executes, now_executes with
                   | false, true -> Format.fprintf ch ".+."
                   | true, true ->
                     Format.fprintf
                       ch
                       (if start_present
                        then if finish_present then "###" else ".-."
                        else "| |")
                   | false, false ->
                     Format.fprintf
                       ch
                       (if start_present && finish_present then "###" else " | ")
                   | true, false -> Format.fprintf ch "'+'"
                 in
                 Format.fprintf ch " ";
                 let _ =
                   match constrains, now_constrains with
                   | false, true -> Format.fprintf ch ".+."
                   | true, true ->
                     Format.fprintf
                       ch
                       (if release_present
                        then if deadline_present then ":=:" else ".-."
                        else ": :")
                   | false, false ->
                     Format.fprintf
                       ch
                       (if release_present && deadline_present then ".+." else " | ")
                   | true, false -> Format.fprintf ch "'+'"
                 in
                 Format.fprintf ch " ";
                 t, now_executes, now_constrains)
              tasks
          in
          let horizontal = ref false in
          let new_clocks =
            Array.mapi
              (fun i (clock, count) ->
                 let count =
                   if L.mem clock l
                   then (
                     horizontal := true;
                     Format.fprintf ch "%s" (marker i count);
                     count + 1)
                   else (
                     Format.fprintf ch "+";
                     count)
                 in
                 Format.fprintf ch (if !horizontal then "-" else " ");
                 clock, count)
              clocks
          in
          let time_label = N.to_string n in
          Format.fprintf ch "+ %s\n" time_label;
          Array.iter
            (fun ({ release; deadline; _ }, executes, constrains) ->
               let ready = L.mem release l
               and deadline = L.mem deadline l in
               Format.fprintf ch (if executes then "| | " else " |  ");
               Format.fprintf
                 ch
                 (if constrains
                  then ": : "
                  else if ready && deadline
                  then "'+' "
                  else " |  "))
            new_tasks;
          Array.iter (fun _ -> Format.fprintf ch "| ") new_clocks;
          Format.fprintf ch "|\n";
          new_tasks, new_clocks
        in
        let task_states =
          tasks |> List.map (fun task -> task, false, false) |> Array.of_list
        in
        let clock_states = Array.map (fun clock -> clock, 0) clocks in
        let _ = Iter.fold serialize_record (task_states, clock_states) trace in
        let _ =
          for _ = 0 to width do
            Format.fprintf ch " "
          done
        in
        Format.fprintf ch "v")
    ;;
  end

  module Serialize = struct
    (** [undefined] serializes the step in order defined by the label implementation.*)
    let undefined l = L.to_iter l

    (** [random] serializes the step in randomly.*)
    let random l = l |> L.to_iter |> Iter.shuffle

    (** [respect_microstep] serializes the step randomly while respecting partial ordering.*)
    let respect_microstep order_hints l =
      l |> L.to_iter |> Microstep.arrange_randomly order_hints |> Iter.of_list
    ;;
  end

  module Tag = struct
    let none = (fun () -> ()), fun () _ l -> l

    let tag_round_timestamp round =
      let init () = ref N.zero
      and tag previous_aligned now serialization =
        let n_steps, diff_aligned, _ = round N.(now - !previous_aligned) in
        (previous_aligned := N.(!previous_aligned + diff_aligned));
        serialization
        |> Iter.zip_i
        |> Iter.map (fun (i, e) ->
          Printf.sprintf "%s %i" e (if i = 0 then n_steps else 0))
      in
      init, tag
    ;;
  end

  (** Import/Export into comma-separated lists. *)
  module CSL = struct
    let print ?step_sep ~tagger ~serialize formatter trace =
      let init_tagger, tag = tagger in
      let tag_state = init_tagger () in
      let pp_step f (label, now) =
        let serialization = serialize label in
        let serialization = tag tag_state now @@ Iter.map L.E.to_string serialization in
        Iter.pp_seq ~sep:"," Format.pp_print_string f serialization
      in
      Iter.pp_seq ~sep:(Option.value ~default:"," step_sep) pp_step formatter trace;
      Format.pp_print_flush formatter ()
    ;;
  end

  module CSV = struct
    let timestamp_column = "t"

    let read ch =
      Csv.of_channel ~has_header:true ch
      |> Csv.Rows.iter
      |> Iter.from_labelled_iter
      |> Iter.map (fun row ->
        let timestamp = N.of_string (Csv.Row.find row timestamp_column) in
        let label =
          row
          |> Csv.Row.to_assoc
          |> Iter.of_list
          |> Iter.filter_map (fun (name, value) ->
            if
              name = timestamp_column
              || String.contains name '{'
              || String.contains name '}'
              || name = ""
            then None
            else (
              match value with
              | "0" -> None
              | "1" -> Some name
              | str -> failwithf "incorrect value in column %s: %s" name str))
          |> Iter.map L.E.of_string
          |> L.of_iter
        in
        { label; time = timestamp })
    ;;

    let write ch clocks trace =
      let clocks = List.sort_uniq L.E.compare clocks in
      let out = Csv.to_channel ~quote_all:false ch in
      let clock_strs = List.map L.E.to_string clocks in
      Csv.output_record out (timestamp_column :: clock_strs);
      Iter.iter
        (fun step ->
           let presence =
             clocks
             |> List.map (fun clock -> L.mem clock step.label)
             |> List.map (function
               | true -> "1"
               | false -> "0")
           in
           let timestamp = N.to_string step.time in
           Csv.output_record out (timestamp :: presence))
        trace
    ;;
  end
end
