

(* 
module Bit = struct
  module Make(K: sig
    type t
  end): Set.S = struct
    let count = ref 0
    let get_index () = let current = !count in count := current + 1; current
    
let arena = Hashtbl.create 128 

    type elt = K.t

    type t = 
  end
end *)