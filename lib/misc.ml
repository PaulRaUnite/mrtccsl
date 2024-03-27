module MakeCompare (M : Set.OrderedType) = struct
  type t = M.t

  let compare = M.compare
  let less x y = M.compare x y < 0
  let more x y = M.compare x y > 0
  let equal x y = M.compare x y = 0

  let less_eq x y = M.compare x y <= 0
  let more_eq x y = M.compare x y >= 0

  let min x y = if less_eq x y then x else y
  let max x y = if more_eq x y then x else y
end

let cartesian l l' =
  List.concat (List.map (fun e -> List.map (fun e' -> (e, e')) l') l)

let empty = function [] -> true | _ -> false
