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

let cartesian l l' = List.concat (List.map (fun e -> List.map (fun e' -> e, e') l') l)

let is_empty = function
  | [] -> true
  | _ -> false
;;

(*stolen from https://stackoverflow.com/questions/40141955/computing-a-set-of-all-subsets-power-set*)
let rec powerset = function
  | [] -> [ [] ]
  | x :: xs ->
    let ps = powerset xs in
    ps @ List.map (fun ss -> x :: ss) ps
;;

let powerset_nz elements = List.filter (fun l -> l <> []) @@ powerset elements
let ( let* ) = Option.bind

let ( and* ) x y =
  let* x = x in
  let* y = y in
  Some (x, y)
;;

let rec collect n init f : 'a list = if n = 0 then [] else
  match f init with
  | Some (r, v) -> r :: collect (n - 1) v f
  | None -> []
;;