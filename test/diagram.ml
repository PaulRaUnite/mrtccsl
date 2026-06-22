open Mrtccsl
open Common
open Prelude
module SSet = Set.Make (String)

module DiagramBackend = struct
  let test_name = "diagram"

  module N = Number.Rational

  module Backend = struct
    include Backend.Machine.Diagram

    let accept_trace m trace =
      accept_trace
        m
        (Seq.map
           Trace.(fun { label; time } -> { label = SSet.to_list label; time })
           trace)
    ;;
  end

  module Trace = struct
    include
      Trace.MakeIO
        (N)
        (struct
          include SSet
          module E = String
        end)

    type t = trace
  end
end

include Correctness.Make (DiagramBackend)
