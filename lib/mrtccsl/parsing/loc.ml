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
