module ExpOrder = struct
  module type T = sig
    type t

    val compare : t -> t -> int
    val less : t -> t -> bool
    val more : t -> t -> bool
    val equal : t -> t -> bool
    val less_eq : t -> t -> bool
    val more_eq : t -> t -> bool
    val min : t -> t -> t
    val max : t -> t -> t
  end

  module Make (M : Set.OrderedType) = struct
    include M

    let compare = M.compare
    let less x y = M.compare x y < 0
    let more x y = M.compare x y > 0
    let equal x y = M.compare x y = 0
    let less_eq x y = M.compare x y <= 0
    let more_eq x y = M.compare x y >= 0
    let min x y = if less_eq x y then x else y
    let max x y = if more_eq x y then x else y
  end
end

(** Cartesian product of 2 lists. *)
let cartesian l l' = List.concat (List.map (fun e -> List.map (fun e' -> e, e') l') l)

(** Makes cartesian product of two lists of lists as another list of lists. *)
let flat_cartesian l l' = List.map (fun (x, y) -> x @ y) (cartesian l l')

let id x = x

module List = struct
  include List

  let is_empty = function
    | [] -> true
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

  let ints len = List.init len id

  let flatten_opt list =
    fold_left
      (fun (acc, missing) x ->
        match x with
        | Some x -> x :: acc, missing
        | None -> acc, true)
      ([], false)
      list
  ;;
end

(*stolen from https://stackoverflow.com/questions/40141955/computing-a-set-of-all-subsets-power-set*)
let rec powerset = function
  | [] -> [ [] ]
  | x :: xs ->
    let ps = powerset xs in
    ps @ List.map (fun ss -> x :: ss) ps
;;

let powerset_nz elements = List.filter (fun l -> l <> []) @@ powerset elements
let ( << ) f g x = f (g x)
let ( let* ) = Option.bind

let ( and* ) x y =
  let* x = x in
  let* y = y in
  Some (x, y)
;;

let rec collect n init f : 'a list =
  if n = 0
  then []
  else (
    match f init with
    | Some (r, v) -> r :: collect (n - 1) v f
    | None -> [])
;;

module type Stringable = sig
  type t

  val to_string : t -> string
end

module String = struct
  include String

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

let rec ints n : int Seq.t = fun () -> Seq.Cons (n, ints (n + 1))

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
      List.fold_left
        (fun (l, discard) x ->
          match q.cycling x with
          | None -> l, true
          | Some x -> x :: l, discard)
        ([], false)
        q.data
    in
    q.data <- list;
    discard
  ;;

  let is_empty q = List.is_empty q.data
  let last q = List.last q.data
  let to_list q = q.data
  let map q f c = { data = List.map f q.data; cycling = c }
  let map_inplace q f = q.data <- List.map f q.data
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
end
