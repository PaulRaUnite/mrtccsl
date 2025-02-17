(* open Ast

module Type = struct

  module Plain = struct 
    type t = [ `Int
    | `Rational
    | `Time
    | `Interval of t
    | `Frequency
    | `Clock
    ] [@@deriving compare]
  end
  module Complex = struct
  type t = [ Plain.t
  | `Block 
  ] [@@deriving compare]

end
end

module StringMap = Map.Make(String)
type calls = (Type.Complex.t StringMap.t * type_assignment) StringMap.t

and type_assignment = {calls : calls ; blocks: type_assignment StringMap.t; variables: Type.Plain.t StringMap.t }

let toplevel typing = function
| ModuleDec _ -> 
  | Check _ ->  

    let statement  *)

    (* type context =  *)