open Sexplib0.Sexp_conv
open Ppx_compare_lib.Builtin

(** Function composition, [f << g] if the same as f(g(x)).*)
let ( << ) f g x = f (g x)

let ( >> ) g f x = f (g x)
let ( >== ) = Option.bind
let ( let* ) = Option.bind

let ( and* ) x y =
  let* x = x in
  let* y = y in
  Some (x, y)
;;

let failwithf f = Printf.ksprintf failwith f

module Fun = struct
  include Fun

  let catch_to_opt f v =
    try Some (f v) with
    | _ -> None
  ;;

  let catch_with_default f v default = catch_to_opt f v |> Option.value ~default
end

module Int = struct
  include Int

  let rec pow a = function
    | 0 -> 1
    | 1 -> a
    | n ->
      let b = pow a (n / 2) in
      b * b * if n mod 2 = 0 then 1 else a
  ;;
end

module Option = struct
  include Option

  let bind_or x f =
    match x with
    | Some x -> Some x
    | None -> f ()
  ;;

  let bind_else f x =
    match x with
    | Some x -> x
    | None -> f ()
  ;;

  let split2 = function
    | Some (x, y) -> Some x, Some y
    | None -> None, None
  ;;

  let map_or ~default f = function
    | Some x -> f x
    | None -> default
  ;;

  let unwrap ~expect = function
    | Some x -> x
    | None -> failwithf "expected: %s" expect
  ;;

  let to_string ~default f = function
    | Some x -> f x
    | None -> default
  ;;
end

module Result = struct
  include Result

  module Syntax = struct
    let ( let* ) = Result.bind

    let ( and* ) x y =
      let* x = x in
      let* y = y in
      Ok (x, y)
    ;;
  end

  let unwrap_to_ch ~msg ch = function
    | Ok x -> x
    | Error e ->
      Format.fprintf ch "%a" e ();
      failwith msg
  ;;

  let unwrap = unwrap_to_ch Format.std_formatter
end

module Seq = struct
  include Seq

  (** [int_seq n] returns sequence [0...n] (not included).*)
  let int_seq ?(step = 1) n = ints 0 |> take (n / step) |> map (Int.mul step)

  let%test _ = List.of_seq (int_seq 3) = [ 0; 1; 2 ]

  (** [int_seq n] returns sequence [0..=n] (not included).*)
  let int_seq_inclusive (starts, ends) =
    assert (ends >= starts);
    take (ends - starts + 1) (ints starts)
  ;;

  let%test _ = List.of_seq (int_seq_inclusive (0, 2)) = [ 0; 1; 2 ]
  let%test _ = List.of_seq (int_seq_inclusive (-3, 0)) = [ -3; -2; -1; 0 ]

  (** Returns sequence of lists from list of sequences. Ends when any sequence ends.*)
  let rec zip_list seq_list () : 'a list node =
    match seq_list with
    | [] -> Nil
    | list ->
      let values_seqs = List.filter_map Seq.uncons list in
      if List.compare_lengths seq_list values_seqs <> 0
      then Nil
      else (
        let values, seqs = List.split values_seqs in
        Cons (values, zip_list seqs))
  ;;

  let rec fold_left_until p f acc xs =
    match xs () with
    | Nil -> acc, None, xs
    | Cons (x, xs) ->
      if p x
      then (
        let acc = f acc x in
        fold_left_until p f acc xs)
      else acc, Some x, xs
  ;;

  let%test _ =
    let left, delim, right =
      fold_left_until (fun x -> x < 5) (fun acc x -> x :: acc) [] (int_seq 10)
    in
    left = [ 4; 3; 2; 1; 0 ] && delim = Some 5 && List.of_seq right = [ 6; 7; 8; 9 ]
  ;;

  let return2 x y = cons y (return x)

  let to_string ?(sep = ", ") ets seq =
    let buf = Buffer.create 32 in
    let _ =
      Seq.fold_left
        (fun first x ->
           if not first then Buffer.add_string buf sep;
           Buffer.add_string buf (ets x);
           false)
        true
        seq
    in
    Buffer.contents buf
  ;;

  let unfold_for_while f init n p =
    let was_cut = ref false in
    ( Seq.unfold f init
      |> Seq.zip (Seq.ints 1)
      |> Seq.take_while (fun (i, v) ->
        if i < n && p v
        then true
        else (
          was_cut := true;
          false))
      |> Seq.map (fun (_, v) -> v)
    , was_cut )
  ;;

  let append_list l = List.fold_left append empty l

  (**[reduce_left] is similar to [fold_left], except it uses first element as as its init.*)
  let reduce_left f acc (seq : 'a t) : 'a t =
    match seq () with
    | Nil -> invalid_arg "empty seq"
    | Cons (x, xs) -> fold_left f (acc x) xs
  ;;

  let of_pair (x, y) = return2 x y

  let product_seq (seq : 'a t t) : 'a t t =
    reduce_left
      (fun acc seq -> product acc seq |> map (fun (f, s) -> cons s f))
      (map return)
      seq
  ;;

  let%test_unit _ =
    [%test_eq: int list list]
      (return2 (int_seq 2) (int_seq 2) |> product_seq |> map List.of_seq |> List.of_seq)
      [ [ 0; 0 ]; [ 0; 1 ]; [ 1; 0 ]; [ 1; 1 ] ]
  ;;

  let uncons_exn seq = Option.get @@ uncons seq

  let to_tuple2 seq =
    let x, seq = uncons_exn seq in
    let y, _ = uncons_exn seq in
    x, y
  ;;

  let to_tuple3 seq =
    let x, seq = uncons_exn seq in
    let y, seq = uncons_exn seq in
    let z, _ = uncons_exn seq in
    x, y, z
  ;;

  let to_tuple4 seq =
    let x, seq = uncons_exn seq in
    let y, seq = uncons_exn seq in
    let z, seq = uncons_exn seq in
    let v, _ = uncons_exn seq in
    x, y, z, v
  ;;

  let to_tuple5 seq =
    let x, seq = uncons_exn seq in
    let y, seq = uncons_exn seq in
    let z, seq = uncons_exn seq in
    let v, seq = uncons_exn seq in
    let w, _ = uncons_exn seq in
    x, y, z, v, w
  ;;
end

module List = struct
  include List

  let return x = [ x ]

  let is_empty = function
    | [] -> true
    | _ -> false
  ;;

  let is_one = function
    | [] -> false
    | _ :: [] -> true
    | _ -> false
  ;;

  let first = function
    | x :: _ -> Some x
    | [] -> None
  ;;

  let first_partition = function
    | x :: tail -> Some x, tail
    | [] -> None, []
  ;;

  let rec last_partition = function
    | [] -> None, []
    | x :: [] -> Some x, []
    | x :: tail ->
      let last, rest = last_partition tail in
      last, x :: rest
  ;;

  let last l =
    let rec aux prev = function
      | [] -> prev
      | x :: tail -> aux x tail
    in
    match l with
    | [] -> None
    | x :: tail -> Some (aux x tail)
  ;;

  let ints len = List.init len Fun.id

  let flatten_opt list =
    fold_left
      (fun (acc, missing) x ->
         match x with
         | Some x -> x :: acc, missing
         | None -> acc, true)
      ([], false)
      list
  ;;

  let[@tail_mod_cons] rec zip3 l1 l2 l3 =
    match l1, l2, l3 with
    | [], [], [] | [], _, _ | _, [], _ | _, _, [] -> []
    | a1 :: l1, a2 :: l2, a3 :: l3 -> (a1, a2, a3) :: zip3 l1 l2 l3
  ;;

  let[@tail_mod_cons] rec zip4 l1 l2 l3 l4 =
    match l1, l2, l3, l4 with
    | [], [], [], [] -> []
    | a1 :: l1, a2 :: l2, a3 :: l3, a4 :: l4 -> (a1, a2, a3, a4) :: zip4 l1 l2 l3 l4
    | _ -> invalid_arg "lists in the tuple should have the same length"
  ;;

  let rec split3 = function
    | [] -> [], [], []
    | (x, y, z) :: tail ->
      let tx, ty, tz = split3 tail in
      x :: tx, y :: ty, z :: tz
  ;;

  let rec split4 = function
    | [] -> [], [], [], []
    | (x, y, z, w) :: tail ->
      let tx, ty, tz, tw = split4 tail in
      x :: tx, y :: ty, z :: tz, w :: tw
  ;;

  (** Cartesian product of 2 lists. *)
  let cartesian l l' = Seq.product (to_seq l) (to_seq l') |> of_seq

  let map_cartesian f l l' = Seq.map_product f (to_seq l) (to_seq l') |> of_seq

  (** Makes cartesian product of two lists of lists as another list of lists. *)
  let flat_cartesian l l' = map_cartesian append l l'

  (** Returns a powerset (all subsets) of the given list.*)
  let rec powerset = function
    (*stolen from https://stackoverflow.com/questions/40141955/computing-a-set-of-all-subsets-power-set*)
    | [] -> [ [] ]
    | x :: xs ->
      let ps = powerset xs in
      ps @ map (fun ss -> x :: ss) ps
  ;;

  (** Returns powerset without the empty list.*)
  let powerset_nz elements = filter (fun l -> l <> []) @@ powerset elements

  let rec powerset_partition = function
    | [] -> [ [], [] ]
    | x :: xs ->
      let ps = powerset_partition xs in
      map (fun (part, other) -> part, x :: other) ps
      @ map (fun (part, other) -> x :: part, other) ps
  ;;

  let%test_unit _ =
    [%test_eq: (int list * int list) list]
      (powerset_partition [ 1; 2 ])
      [ [], [ 1; 2 ]; [ 2 ], [ 1 ]; [ 1 ], [ 2 ]; [ 1; 2 ], [] ]
  ;;

  let flat_map f = flatten << map f

  let general_cartesian ll =
    fold_left
      (fun acc vars ->
         if is_empty acc
         then List.map (fun x -> [ x ]) vars
         else map_cartesian (fun e l -> l @ [ e ]) vars acc)
      []
      ll
  ;;

  let%test_unit _ =
    [%test_eq: int list list]
      (general_cartesian [ [ 1; 2 ]; [ 3; 4 ] ])
      [ [ 1; 3 ]; [ 1; 4 ]; [ 2; 3 ]; [ 2; 4 ] ]
  ;;

  let unfold_for f init n : 'a list = Seq.unfold f init |> Seq.take n |> List.of_seq

  let unfold_while f init p : 'a list =
    Seq.unfold f init |> Seq.take_while p |> List.of_seq
  ;;

  let unfold_for_while f init n p : 'a list * bool =
    let seq, was_cut = Seq.unfold_for_while f init n p in
    let list = List.of_seq seq in
    list, !was_cut
  ;;

  let[@tail_mod_cons] rec drop_nth l i =
    match l with
    | x :: tail -> if i = 0 then tail else x :: drop_nth tail (i - 1)
    | [] -> []
  ;;

  let any = List.exists Fun.id
  let all = List.for_all Fun.id
  let flat l = filter_map Fun.id l

  let minmax compare l =
    let rec aux (gmin, gmax) = function
      | [] -> gmin, gmax
      | x :: tail ->
        let gmin = if compare x gmin < 0 then x else gmin
        and gmax = if compare x gmax > 0 then x else gmax in
        aux (gmin, gmax) tail
    in
    match l with
    | [] -> invalid_arg "List.min: list is empty"
    | x :: tail -> aux (x, x) tail
  ;;

  let find_opt_partition p l =
    let rec aux unsats = function
      | [] -> None, unsats
      | x :: tail ->
        if p x then Some x, List.rev_append unsats tail else aux (x :: unsats) tail
    in
    aux [] l
  ;;

  let print pp l =
    iter pp l;
    print_newline ()
  ;;

  let argmax_opt compare = function
    | [] -> None
    | x :: tail ->
      let rec argmax j i x = function
        | [] -> i
        | y :: tail ->
          if compare y x > 0 then argmax (j + 1) j y tail else argmax (j + 1) i x tail
      in
      Some (argmax 1 0 x tail)
  ;;

  let to_string ?(sep = ", ") ppv list =
    let buf = Buffer.create 32 in
    let _ =
      List.fold_left
        (fun first x ->
           if not first then Buffer.add_string buf sep;
           Buffer.add_string buf (ppv x);
           false)
        true
        list
    in
    Buffer.contents buf
  ;;

  (** Replaces an element inplace with [`Replace], drops when [`Drop] and skips if [`Skip]*)
  let rec map_inplace_or_drop f = function
    | [] -> None, []
    | x :: tail ->
      (match f x with
       | `Replace v -> None, v :: tail
       | `Drop -> Some x, tail
       | `Skip ->
         let drop, tail = map_inplace_or_drop f tail in
         drop, x :: tail)
  ;;

  (** Modifies first element encountered when [f x = Some _], returns [_, true] if happened. *)
  let rec map_inplace_once_indicate f = function
    | [] -> [], false
    | x :: tail ->
      (match f x with
       | Some y -> y :: tail, true
       | None ->
         let tail, happened = map_inplace_once_indicate f tail in
         x :: tail, happened)
  ;;

  (** Modifies first element encountered when [f x = Some _]*)
  let[@tail_mod_cons] rec map_inplace_once f = function
    | [] -> []
    | x :: tail ->
      (match f x with
       | Some y -> y :: tail
       | None -> x :: map_inplace_once f tail)
  ;;

  let map_inplace_once_or f g list =
    let list, happened = map_inplace_once_indicate f list in
    if not happened then g list else list
  ;;

  let[@tail_mod_cons] rec filter_mapi f i = function
    | [] -> []
    | x :: l ->
      let i' = i + 1 in
      (match f i x with
       | Some y -> y :: filter_mapi f i' l
       | None -> filter_mapi f i' l)
  ;;

  let filter_mapi f l = filter_mapi f 0 l

  (**[reduce_left] is similar to [fold_left], except it uses [acc l0] as its accumulator.*)
  let reduce_left f acc = function
    | [] -> invalid_arg "empty list"
    | x :: xs -> fold_left f (acc x) xs
  ;;

  (**[reduce_right] is similar to [fold_right], except is uses [acc ltail] as its accumulator.*)
  let rec reduce_right f acc = function
    | [] -> invalid_arg "empty list"
    | x :: [] -> acc x
    | x :: xs -> f x (reduce_right f acc xs)
  ;;

  (** [zip_list] zips list of lists from list of sequences. Ends when any outer list ends.*)
  let zip_list l = l |> map to_seq |> Seq.zip_list |> of_seq

  let%test_unit _ =
    [%test_eq: int list list] (zip_list [ [ 1; 2 ]; [ 3; 4 ] ]) [ [ 1; 3 ]; [ 2; 4 ] ]
  ;;

  let rec pair_apply f = function
    | [] -> []
    | x :: [] -> [ x ]
    | x :: y :: tail -> f x y :: pair_apply f tail
  ;;

  let rec fold_merge f = function
    | [] -> failwith "fold_merge: cannot merge empty list"
    | x :: [] -> x
    | l -> fold_merge f (pair_apply f l)
  ;;

  let%test_unit _ =
    [%test_eq: string]
      (fold_merge (fun x y -> Printf.sprintf "(%s %s)" x y) [ "a"; "b"; "c"; "d"; "e" ])
      "(((a b) (c d)) e)"
  ;;

  let uncons = function
    | [] -> failwith "uncons: empty list"
    | x :: xs -> x, xs
  ;;

  let rec fold_lefti f acc i = function
    | [] -> acc
    | x :: tail -> fold_lefti f (f acc i x) (i + 1) tail
  ;;

  let fold_lefti f acc = fold_lefti f acc 0

  let fold_left_mapr f accu l =
    let rec aux accu l_accu = function
      | [] -> Ok (accu, rev l_accu)
      | x :: l -> Result.bind (f accu x) (fun (accu, x) -> aux accu (x :: l_accu) l)
    in
    aux accu [] l
  ;;

  let rec insert list x index =
    match list with
    | [] -> [ x ]
    | h :: tail ->
      (match index with
       | 0 -> x :: list
       | index when index > 0 -> h :: insert tail x (index - 1)
       | _ -> invalid_arg "index cannot be less than 0")
  ;;
end

module String = struct
  include CCString

  let sexp_of_t = Sexplib0.Sexp_conv.sexp_of_string
  let t_of_sexp = Sexplib0.Sexp_conv.string_of_sexp
  let to_string = Fun.id
  let init_char n c = init n (fun _ -> c)
  let grapheme_length = Uuseg_string.fold_utf_8 `Grapheme_cluster (fun x _ -> x + 1) 0
  let of_string = Fun.id
end

module Buffer = struct
  include Buffer

  let add_chars b n c : unit =
    for _ = 0 to n - 1 do
      add_char b c
    done
  ;;
end

(*TODO: maybe use doubleended list as discussed here: https://discuss.ocaml.org/t/how-to-represent-a-double-ended-linked-list/13354*)
(*TODO: refactor out*)
module ExpirationQueue = struct
  open Sexplib0.Sexp_conv

  type 'a t =
    { mutable data : 'a list
    ; cycling : 'a -> 'a option
    }
  [@@deriving sexp]

  let create c : 'a t = { data = []; cycling = c }
  let push q x = q.data <- q.data @ [ x ]

  let pop q =
    match q.data with
    | [] -> None
    | x :: tail ->
      q.data <- tail;
      Some x
  ;;

  let peek q =
    match q.data with
    | [] -> None
    | x :: _ -> Some x
  ;;

  let expiration_step q =
    let list, discard =
      List.fold_right
        (fun x (l, discard) ->
           match q.cycling x with
           | None -> l, true
           | Some x -> x :: l, discard)
        q.data
        ([], false)
    in
    q.data <- list;
    discard
  ;;

  let is_empty q = List.is_empty q.data
  let last q = List.last q.data
  let to_list q = q.data
  let map q f c = { data = List.map f q.data; cycling = c }
  let map_inplace q f = q.data <- List.map f q.data

  let%test _ =
    let q = create Option.some in
    let _ = push q 2 in
    let _ = push q 1 in
    let _ = push q 0 in
    peek q = Some 2
  ;;
end

module Tuple = struct
  let map2 f (x, y) = f x, f y
  let map3 f (x, y, z) = f x, f y, f z
  let map4 f (x, y, z, w) = f x, f y, f z, f w
  let map5 f (x, y, z, w, v) = f x, f y, f z, f w, f v
  let fn2 f (x, y) = f x y
  let compare2 c1 c2 (x1, y1) (x2, y2) = if c1 x1 x2 = 0 then c2 y1 y2 else c1 x1 x2

  let compare3 c1 c2 c3 (x1, y1, z1) (x2, y2, z2) =
    compare2 c1 (compare2 c2 c3) (x1, (y1, z1)) (x2, (y2, z2))
  ;;

  let compare4 c1 c2 c3 c4 (x1, y1, z1, w1) (x2, y2, z2, w2) =
    compare2 c1 (compare2 c2 (compare2 c3 c4)) (x1, (y1, (z1, w1))) (x2, (y2, (z2, w2)))
  ;;

  let compare_same2 c = compare2 c c
  let compare_same3 c = compare3 c c c
  let compare_same4 c = compare4 c c c c
  let extend2 (x, y) z = x, y, z
  let extend3 (x, y, z) w = x, y, z, w
  let all2 (x, y) = x && y
  let all3 (x, y, z) = x && y && z
  let any2 (x, y) = x || y
  let any3 (x, y, z) = x || y || z
  let list2 (x, y) = [ x; y ]
  let list3 (x, y, z) = [ x; y; z ]
  let list4 (x, y, z, w) = [ x; y; z; w ]
  let to_string2 f (x, y) = Printf.sprintf "(%s, %s)" (f x) (f y)
  let swap2 (x, y) = y, x
end

(* module type Entry = sig
  type unknown
  type occupied

  type (_, 'k, 'v) t

  val or_insert : default:'v -> ('a, 'k, 'v) t -> (occupied, 'k, 'v) t
  val or_insert_with : (unit -> 'v) -> ('a, 'k, 'v) t -> (occupied, 'k, 'v) t
  val and_modify : ('v -> 'v) -> ('a, 'k, 'v) t -> ('a, 'k, 'v) t
  val get : (occupied, 'k, 'v) t -> 'v
  val maybe_get : ('a, 'k, 'v) t -> 'v option
end *)

module Hashtbl = struct
  include Hashtbl

  let entry ~default f key tbl =
    let v = find_opt tbl key |> Option.value ~default in
    replace tbl key (f v)
  ;;

  (* TODO: continue work on proper Entry later
  module Entry : Entry = struct
    type unknown = private Unknown
    type occupied= private Occupied
    
  type (_, 'k, 'v) val =
    | Unknown : 'k -> (unknown, 'k, 'v) t
    | Occupied : ('k * 'v) -> (occupied, 'k, 'v) t

    let or_insert ~default e = 
  end *)

  let value ~default key tbl = Hashtbl.find_opt tbl key |> Option.value ~default

  let[@inline] value_mut ~default key tbl =
    match Hashtbl.find_opt tbl key with
    | Some v -> v
    | None ->
      let v = default () in
      Hashtbl.add tbl key v;
      v
  ;;

  module Collect = struct
    let count ?(size = 64) seq =
      let tbl = create size in
      Seq.fold_left
        (fun tbl v ->
           entry (Int.add 1) ~default:0 v tbl;
           tbl)
        tbl
        seq
    ;;

    let by_tags ?(size = 64) seq =
      let tbl = create size in
      Seq.iter
        (fun (kl, v) -> List.iter (fun k -> entry (List.cons v) ~default:[] k tbl) kl)
        seq;
      tbl
    ;;
  end

  let map kf vf tbl = tbl |> to_seq |> Seq.map (fun (k, v) -> kf k, vf v) |> of_seq
  let map_v f tbl = tbl |> to_seq |> Seq.map (fun (k, v) -> k, f v) |> of_seq

  module Make (H : HashedType) = struct
    include Make (H)

    let entry f default key tbl =
      let v = find_opt tbl key |> Option.value ~default in
      replace tbl key (f v)
    ;;

    let entry_mut f default key tbl =
      let v = find_opt tbl key |> Option.bind_else default in
      replace tbl key (f v)
    ;;

    module Collect = struct
      let count ?(size = 64) seq =
        let tbl = create size in
        Seq.fold_left
          (fun tbl v ->
             entry (Int.add 1) 0 v tbl;
             tbl)
          tbl
          seq
      ;;

      let by_tags ?(size = 64) seq =
        let tbl = create size in
        Seq.iter (fun (kl, v) -> List.iter (fun k -> entry (List.cons v) [] k tbl) kl) seq;
        tbl
      ;;
    end

    let map kf vf tbl = tbl |> to_seq |> Seq.map (fun (k, v) -> kf k, vf v) |> of_seq
    let map_v f tbl = tbl |> to_seq |> Seq.map (fun (k, v) -> k, f v) |> of_seq
  end
end

module Map = struct
  include Map

  module Make (K : OrderedType) = struct
    include Make (K)

    (**[entry update default key map]*)
    let entry ~default f k m =
      update
        k
        (fun x ->
           let acc = Option.value x ~default in
           Some (f acc))
        m
    ;;

    (**[entry update default key map]*)
    let entry_mut ~default f k m =
      update
        k
        (fun x ->
           let acc =
             match x with
             | Some x -> x
             | None -> default ()
           in
           Some (f acc))
        m
    ;;

    let to_string ?(sep = ", ") (ppk : K.t -> string) (ppv : 'a -> string) (map : 'a t)
      : string
      =
      map
      |> to_seq
      |> Seq.to_string ~sep (fun (k, v) -> Printf.sprintf "%s -> %s" (ppk k) (ppv v))
    ;;

    let value ~default k map = Option.value ~default (find_opt k map)

    let value_mut ~default k map =
      match find_opt k map with
      | Some v -> map, v
      | None ->
        let v = default () in
        let map = add k v map in
        map, v
    ;;

    let to_iter m f = iter (fun k v -> f (k, v)) m
  end
end

module Set = struct
  include Set

  module Make (K : OrderedType) = struct
    include Make (K)

    let to_iter s f = iter f s

    let of_iter iter =
      let acc = ref empty in
      iter (fun e -> acc := add e !acc);
      !acc
    ;;

    let equal_modulo ~modulo a b = equal (inter a modulo) (inter b modulo)
  end
end

(**[fixpoint init eq f start] returns a value [v] such that [f(v) = v] by starting from [v].*)
let rec fixpoint eq f v =
  let next = f v in
  if eq next v then next else fixpoint eq f next
;;

module CircularList = struct
  type 'a t =
    { mutable data : 'a list
    ; max : int
    }

  let make size =
    assert (size > 0);
    { data = []; max = size }
  ;;

  let push l v =
    if List.length l.data = l.max
    then (
      match l.data with
      | _ :: tail -> l.data <- List.append tail [ v ]
      | [] -> invalid_arg "cannot cycle though empty list")
    else l.data <- List.append l.data [ v ]
  ;;

  let content l = l.data
end

module Array = struct
  include Array

  let updatei a f i = Array.set a i (f (Array.get a i))

  (**[fold_lefti] is like [fold_left] just with index. *)
  let fold_lefti f x a =
    let r = ref x in
    for i = 0 to length a - 1 do
      r := f !r i (unsafe_get a i)
    done;
    !r
  ;;

  let to_tuple2 a = a.(0), a.(1)
  let to_tuple3 a = a.(0), a.(1), a.(2)
  let to_tuple4 a = a.(0), a.(1), a.(2), a.(3)
  let to_tuple5 a = a.(0), a.(1), a.(2), a.(3), a.(4)
  let to_tuple6 a = a.(0), a.(1), a.(2), a.(3), a.(4), a.(5)
end

module Dynarray = struct
  include Dynarray

  let rev_iteri f a =
    for i = length a - 1 downto 0 do
      f i (get a i)
    done
  ;;

  let filter_mapi f a =
    let b = create () in
    iteri
      (fun i x ->
         match f i x with
         | None -> ()
         | Some y -> add_last b y)
      a;
    b
  ;;

  let of_iter ?(size_hint = 16) iter =
    let a = create () in
    ensure_capacity a size_hint;
    iter (fun el -> add_last a el);
    a
  ;;

  let to_iter a f = iter f a
  let map_inplace f a = iteri (fun i v -> Dynarray.set a i (f v)) a
end

module Iter = struct
  include Iter

  let last iter =
    fold
      (fun acc x ->
         match acc with
         | Some _ -> Some x
         | None -> Some x)
      None
      iter
  ;;

  let to_dynarray = Dynarray.of_iter
  let of_dynarray = Dynarray.to_iter
end

module Queue = struct
  exception Empty

  type 'a cell =
    | Nil
    | Cons of
        { content : 'a
        ; mutable next : 'a cell
        }

  type 'a t =
    { mutable length : int
    ; mutable first : 'a cell
    ; mutable last : 'a cell
    }

  let create () = { length = 0; first = Nil; last = Nil }

  let clear q =
    q.length <- 0;
    q.first <- Nil;
    q.last <- Nil
  ;;

  let add x q =
    let cell = Cons { content = x; next = Nil } in
    match q.last with
    | Nil ->
      q.length <- 1;
      q.first <- cell;
      q.last <- cell
    | Cons last ->
      q.length <- q.length + 1;
      last.next <- cell;
      q.last <- cell
  ;;

  let push = add

  let peek q =
    match q.first with
    | Nil -> raise Empty
    | Cons { content; _ } -> content
  ;;

  let peek_opt q =
    match q.first with
    | Nil -> None
    | Cons { content; _ } -> Some content
  ;;

  let top = peek

  let take q =
    match q.first with
    | Nil -> raise Empty
    | Cons { content; next = Nil } ->
      clear q;
      content
    | Cons { content; next } ->
      q.length <- q.length - 1;
      q.first <- next;
      content
  ;;

  let take_opt q =
    match q.first with
    | Nil -> None
    | Cons { content; next = Nil } ->
      clear q;
      Some content
    | Cons { content; next } ->
      q.length <- q.length - 1;
      q.first <- next;
      Some content
  ;;

  let pop = take

  let drop q =
    match q.first with
    | Nil -> raise Empty
    | Cons { content = _; next = Nil } -> clear q
    | Cons { content = _; next } ->
      q.length <- q.length - 1;
      q.first <- next
  ;;

  let copy =
    let rec copy q_res prev cell =
      match cell with
      | Nil ->
        q_res.last <- prev;
        q_res
      | Cons { content; next } ->
        let res = Cons { content; next = Nil } in
        (match prev with
         | Nil -> q_res.first <- res
         | Cons p -> p.next <- res);
        copy q_res res next
    in
    fun q -> copy { length = q.length; first = Nil; last = Nil } Nil q.first
  ;;

  let is_empty q = q.length = 0
  let length q = q.length

  let iter =
    let rec iter f cell =
      match cell with
      | Nil -> ()
      | Cons { content; next } ->
        f content;
        iter f next
    in
    fun f q -> iter f q.first
  ;;

  let fold =
    let rec fold f accu cell =
      match cell with
      | Nil -> accu
      | Cons { content; next } ->
        let accu = f accu content in
        fold f accu next
    in
    fun f accu q -> fold f accu q.first
  ;;

  let transfer q1 q2 =
    if q1.length > 0
    then (
      match q2.last with
      | Nil ->
        q2.length <- q1.length;
        q2.first <- q1.first;
        q2.last <- q1.last;
        clear q1
      | Cons last ->
        q2.length <- q2.length + q1.length;
        last.next <- q1.first;
        q2.last <- q1.last;
        clear q1)
  ;;

  (** {1 Iterators} *)

  let to_seq q =
    let rec aux c () =
      match c with
      | Nil -> Seq.Nil
      | Cons { content = x; next } -> Seq.Cons (x, aux next)
    in
    aux q.first
  ;;

  let add_seq q i = Seq.iter (fun x -> push x q) i

  let of_seq g =
    let q = create () in
    add_seq q g;
    q
  ;;

  let to_iter v f = iter f v

  let last q =
    match q.last with
    | Nil -> None
    | Cons { content; _ } -> Some content
  ;;
end

(* We present our priority queues as a functor
   parametrized on the comparison function. *)
module Heap (Elem : Map.OrderedType) : sig
  type t

  val create : unit -> t
  val add : t -> Elem.t -> unit
  val pop_min : t -> Elem.t option
  val peek : t -> Elem.t option
  val map : (Elem.t -> Elem.t) -> t -> unit
  val exists : (Elem.t -> bool) -> t -> bool
  val length : t -> int
  val to_list : t -> Elem.t list
end = struct
  (* Our priority queues are implemented using the standard "min heap"
     data structure, a dynamic array representing a binary tree. *)
  type t = Elem.t Dynarray.t

  let create = Dynarray.create

  (* The node of index [i] has as children the nodes of index [2 * i + 1]
    and [2 * i + 2] -- if they are valid indices in the dynarray. *)
  let left_child i = (2 * i) + 1
  let right_child i = (2 * i) + 2
  let parent_node i = (i - 1) / 2

  (* We use indexing operators for convenient notations. *)
  let ( .!() ) = Dynarray.get
  let ( .!()<- ) = Dynarray.set

  (* Auxiliary functions to compare and swap two elements
     in the dynamic array. *)
  let order h i j = Elem.compare h.!(i) h.!(j)

  let swap h i j =
    let v = h.!(i) in
    h.!(i) <- h.!(j);
    h.!(j) <- v
  ;;

  (* We say that a heap respects the "heap ordering" if the value of
     each node is smaller than the value of its children. The
     algorithm manipulates arrays that respect the heap algorithm,
     except for one node whose value may be too small or too large.

     The auxiliary functions [heap_up] and [heap_down] take
     such a misplaced value, and move it "up" (respectively: "down")
     the tree by permuting it with its parent value (respectively:
     a child value) until the heap ordering is restored. *)

  let rec heap_up h i =
    if i = 0
    then ()
    else (
      let parent = parent_node i in
      if order h i parent < 0
      then (
        swap h i parent;
        heap_up h parent))
  ;;

  let rec heap_down h ~len i =
    let left, right = left_child i, right_child i in
    if left >= len
    then ()
    (* no child, stop *)
    else (
      let smallest =
        if right >= len
        then left (* no right child *)
        else if order h left right < 0
        then left
        else right
      in
      if order h i smallest > 0
      then (
        swap h i smallest;
        heap_down h ~len smallest))
  ;;

  let add h s =
    let i = Dynarray.length h in
    Dynarray.add_last h s;
    heap_up h i
  ;;

  let peek h = if Dynarray.is_empty h then None else Some (Dynarray.get h 0)

  let pop_min h =
    if Dynarray.is_empty h
    then None
    else (
      (* Standard trick: swap the 'best' value at index 0
         with the last value of the array. *)
      let last = Dynarray.length h - 1 in
      swap h 0 last;
      (* At this point [pop_last] returns the 'best' value,
         and leaves a heap with one misplaced element at index [0]. *)
      let best = Dynarray.pop_last h in
      (* Restore the heap ordering -- does nothing if the heap is empty. *)
      heap_down h ~len:last 0;
      Some best)
  ;;

  let map f h = Dynarray.map_inplace f h
  let exists = Dynarray.exists
  let length = Dynarray.length
  let to_list = Dynarray.to_list
end

module In_channel = struct
  include In_channel

  let lines_seq ch =
    Seq.unfold
      (fun ch ->
         let* line = In_channel.input_line ch in
         Some (line, ch))
      ch
  ;;
end

module Sys = struct
  include Sys

  let rec create_dir fn =
    if not (Sys.file_exists fn)
    then (
      let parent_dir = Filename.dirname fn in
      create_dir parent_dir;
      Sys.mkdir fn 0o755)
  ;;

  let write_file ~filename f =
    let parent = Filename.dirname filename in
    create_dir parent;
    let file = open_out filename in
    Fun.protect
      ~finally:(fun () ->
        flush file;
        close_out file)
      (fun () -> f file)
  ;;
end
