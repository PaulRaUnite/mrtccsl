open Prelude
(*taken from https://github.com/andrejbauer/plzoo/blob/master/src/zoo/zoo.ml*)

type location =
  | Location of Lexing.position * Lexing.position (** delimited location *)
  | Nowhere (** no location *)

type 'a t =
  { data : 'a
  ; loc : location
  }

let make loc1 loc2 data = { loc = Location (loc1, loc2); data }
let nowhere data = { loc = Nowhere; data }
let copy (loc : 'a t) (data : 'b) : 'b t = { loc = loc.loc; data }

let shift_position (p : Lexing.position) offset =
  let open Lexing in
  let { pos_cnum; pos_bol; _ } = p in
  { p with pos_cnum = pos_cnum + offset; pos_bol = pos_bol + offset }
;;

let highlight ~warning lexbuf (s : Lexing.position) (f : Lexing.position) (msg : string) =
  if not (String.equal s.pos_fname f.pos_fname)
  then
    failwithf
      "Trying to highlight range in different files: first %s then %s"
      s.pos_fname
      f.pos_fname
  else if s.pos_lnum = f.pos_lnum
  then (
    (* Format.printf "start=%i finish=%i %i %i\n" s.pos_cnum f.pos_cnum s.pos_bol (Bytes.length lexbuf); *)
    let prefix = Bytes.sub lexbuf s.pos_bol (s.pos_cnum - s.pos_bol) in
    let offset =
      Bytes.fold_right
        (fun c mono ->
           mono
           +
           match c with
           | '\t' -> 4
           | _ -> 1)
        prefix
        0
    and width = max (f.pos_cnum - s.pos_cnum) 1
    and linenum = Format.sprintf "%i | " s.pos_lnum
    and linewidth =
      Fun.catch_with_default
        (Bytes.index_from lexbuf f.pos_cnum)
        '\n'
        (Bytes.length lexbuf)
      - s.pos_bol
    in
    let line =
      String.replace ~sub:"\t" ~by:"    " (Bytes.sub_string lexbuf s.pos_bol linewidth)
    in
    fun formatter () ->
      let range = MenhirLib.LexerUtil.range (s, f) in
      Format.pp_print_string formatter range;
      Format.pp_print_string formatter linenum;
      Format.pp_print_string formatter line;
      Format.pp_print_newline formatter ();
      let buf = Buffer.create 16 in
      Buffer.add_chars buf (String.length linenum + offset) ' ';
      Buffer.add_chars buf width '^';
      Buffer.add_char buf '\n';
      Buffer.add_string buf (if warning then "Warning: " else "Error: ");
      Buffer.add_string buf msg;
      if warning
      then Format.fprintf formatter "@{<yellow>%s@}\n" (Buffer.contents buf)
      else Format.fprintf formatter "@{<red>%s@}\n" (Buffer.contents buf))
  else failwith "start and finish are in the same place"
;;

let pp_warning = highlight ~warning:true
let pp_error = highlight ~warning:false

let repack list =
  let data = List.map (fun v -> v.data) list in
  match List.first list, List.last list with
  | Some { loc = Location (start, _); _ }, Some { loc = Location (_, finish); _ } ->
    { data; loc = Location (start, finish) }
  | _ -> nowhere data
;;

let strip_list list = List.map (fun { data; _ } -> data) list
let map f { data; loc } = { data = f data; loc }
let where { loc; _ } = loc
let unwrap { data; _ } = data
let wrap data loc = { data; loc }

let bounding_box list =
  match List.first list, List.last list with
  | Some { loc = Location (start, _); _ }, Some { loc = Location (_, finish); _ } ->
    Location (start, finish)
  | _ -> Nowhere
;;

let highlight ~color ~symbol loc msg =
  match loc with
  | Nowhere -> fun fmt -> Format.fprintf fmt "Unknown location"
  | Location (s, f) ->
    if not (String.equal s.pos_fname f.pos_fname)
    then
      failwithf
        "Trying to highlight range in different files: first %s then %s"
        s.pos_fname
        f.pos_fname
    else if s.pos_lnum = f.pos_lnum
    then (
      let _, lexbuf = MenhirLib.LexerUtil.read s.pos_fname in
      let lexbuf = lexbuf.lex_buffer in
      (* Format.printf "start=%i finish=%i %i %i\n" s.pos_cnum f.pos_cnum s.pos_bol (Bytes.length lexbuf); *)
      let prefix = Bytes.sub lexbuf s.pos_bol (s.pos_cnum - s.pos_bol) in
      let offset =
        Bytes.fold_right
          (fun c mono ->
             mono
             +
             match c with
             | '\t' -> 4
             | _ -> 1)
          prefix
          0
      and width = max (f.pos_cnum - s.pos_cnum) 1
      and linenum = Format.sprintf "%i |" s.pos_lnum
      and linewidth =
        Fun.catch_with_default
          (Bytes.index_from lexbuf f.pos_cnum)
          '\n'
          (Bytes.length lexbuf)
        - s.pos_bol
      in
      let line =
        String.replace ~sub:"\t" ~by:"    " (Bytes.sub_string lexbuf s.pos_bol linewidth)
      in
      fun formatter ->
        let range = MenhirLib.LexerUtil.range (s, f) in
        Format.pp_print_string formatter range;
        Format.pp_print_string formatter linenum;
        Format.pp_print_string formatter line;
        Format.pp_print_newline formatter ();
        let buf = Buffer.create 16 in
        Buffer.add_chars buf (String.length linenum + offset) ' ';
        Buffer.add_chars buf width symbol;
        Ocolor_format.pp_open_style formatter (Ocolor_types.Fg color);
        Format.fprintf formatter "%s %s\n\n" (Buffer.contents buf) msg;
        Ocolor_format.pp_close_style formatter ())
    else ignore
;;
