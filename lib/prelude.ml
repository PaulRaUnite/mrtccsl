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

module Fun = struct
  include Fun

  let catch_to_opt f v =
    try Some (f v) with
    | _ -> None
  ;;

  let catch_with_default f v default = catch_to_opt f v |> Option.value ~default
end

module Option = struct
  include Option

  let bind_or x f =
    match x with
    | Some x -> Some x
    | None -> f ()
  ;;

  let split2 = function
    | Some (x, y) -> Some x, Some y
    | None -> None, None
  ;;
end

module List = struct
  include List

  let is_empty = function
    | [] -> true
    | _ -> false
  ;;

  let is_one = function
    | [] -> false
    | _ :: [] -> true
    | _ -> false
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

  let rec zip3 l1 l2 l3 =
    match l1, l2, l3 with
    | [], [], [] | [], _, _ | _, [], _ | _, _, [] -> []
    | a1 :: l1, a2 :: l2, a3 :: l3 -> (a1, a2, a3) :: zip3 l1 l2 l3
  ;;

  let rec zip4 l1 l2 l3 l4 =
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
  let cartesian l l' = concat (map (fun e -> map (fun e' -> e, e') l') l)

  let map_cartesian f l l' = concat (map (fun e -> map (fun e' -> f e e') l') l)

  (** Makes cartesian product of two lists of lists as another list of lists. *)
  let flat_cartesian l l' = map (fun (x, y) -> x @ y) (cartesian l l')

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

  open Sexplib0.Sexp_conv
  open Ppx_compare_lib.Builtin

  let%test_unit _ =
    [%test_eq: (int list * int list) list]
      (powerset_partition [ 1; 2 ])
      [[], [ 1; 2 ];  [ 2 ], [ 1 ] ; [ 1 ], [ 2 ]; [ 1; 2 ], []]
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
      [ [ 1; 3 ]; [ 2; 3 ]; [ 1; 4 ]; [ 2; 4 ] ]
  ;;

  let unfold_for f init n : 'a list = Seq.unfold f init |> Seq.take n |> List.of_seq

  let unfold_while f init p : 'a list =
    Seq.unfold f init |> Seq.take_while p |> List.of_seq
  ;;

  let unfold_for_while f init n p : 'a list * bool =
    let was_cut = ref false in
    let list =
      Seq.unfold f init
      |> Seq.zip (Seq.ints 1)
      |> Seq.take_while (fun (i, v) ->
        if i < n && p v
        then true
        else (
          was_cut := true;
          false))
      |> Seq.map (fun (_, v) -> v)
      |> List.of_seq
    in
    ( list
    , !was_cut
      (*tricky part: list variable enforces order, otherwise it was always false*) )
  ;;

  let rec drop_nth l i =
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

  (** Modifies first element encountered*)
  let rec map_inplace_once f = function
    | [] -> []
    | x :: tail ->
      (match f x with
       | Some y -> y :: tail
       | None -> x :: map_inplace_once f tail)
  ;;
end

module String = struct
  include CCString

  let sexp_of_t = Sexplib0.Sexp_conv.sexp_of_string
  let t_of_sexp = Sexplib0.Sexp_conv.string_of_sexp
  let to_string = Fun.id
  let init_char n c = init n (fun _ -> c)
  let grapheme_length = Uuseg_string.fold_utf_8 `Grapheme_cluster (fun x _ -> x + 1) 0
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

module Seq = struct
  include Seq

  let rec zip_list seq_list () =
    match seq_list with
    | [] -> Nil
    | list ->
      let values_seqs, ended = List.flatten_opt (List.map Seq.uncons list) in
      if ended
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
      fold_left_until
        (fun x -> x < 5)
        (fun acc x -> x :: acc)
        []
        (List.to_seq @@ List.ints 10)
    in
    left = [ 4; 3; 2; 1; 0 ] && delim = Some 5 && List.of_seq right = [ 6; 7; 8; 9 ]
  ;;

  let int_seq n = take n (ints 0)
  let%test _ = List.of_seq (int_seq 3) = [ 0; 1; 2 ]

  let int_seq_inclusive (starts, ends) =
    assert (ends >= starts);
    take (ends - starts + 1) (ints starts)
  ;;

  let%test _ = List.of_seq (int_seq_inclusive (0, 2)) = [ 0; 1; 2 ]
  let%test _ = List.of_seq (int_seq_inclusive (-3, 0)) = [ -3; -2; -1; 0 ]
  let return2 x y = cons x (return y)

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
end

module Tuple = struct
  let map2 f (x, y) = f x, f y
  let map3 f (x, y, z) = f x, f y, f z
  let map4 f (x, y, z, w) = f x, f y, f z, f w
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

module Hashtbl = struct
  include Hashtbl

  let entry f default key tbl =
    let v = find_opt tbl key |> Option.value ~default in
    replace tbl key (f v)
  ;;

  let value default key tbl = Hashtbl.find_opt tbl key |> Option.value ~default

  module Collect = struct
    let count ?(size = 64) seq =
      let tbl = Hashtbl.create size in
      Seq.fold_left
        (fun tbl v ->
           entry (Int.add 1) 0 v tbl;
           tbl)
        tbl
        seq
    ;;
  end
end

module Map = struct
  include Map

  module Make (K : OrderedType) = struct
    include Make (K)

    let entry f default k m =
      update
        k
        (fun x ->
           let acc = Option.value x ~default in
           Some (f acc))
        m
    ;;

    let to_string ?(sep = ", ") (ppk : K.t -> string) (ppv : 'a -> string) (map : 'a t)
      : string
      =
      map
      |> to_seq
      |> Seq.to_string ~sep (fun (k, v) -> Format.sprintf "%s -> %s" (ppk k) (ppv v))
    ;;
  end
end

let fixpoint init eq trans start =
  let rec aux value =
    let next = trans value in
    if eq next value then next else aux next
  in
  aux (init start)
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
end
