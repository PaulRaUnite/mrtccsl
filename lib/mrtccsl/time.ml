open !Prelude

module Duration = Interface.ExpOrder.Make (Float)

module Interval = struct
  type t = Duration.t * Duration.t

  let from_duration d = (d, d)

  let from_bounds d1 d2 =
    if Duration.more d1 d2 then failwith "incorrect duration interval: d1 >= d2"
    else (d1, d2)
end
