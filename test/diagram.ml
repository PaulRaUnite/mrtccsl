open Mrtccsl
open Common
open Prelude
module SSet = Set.Make (String)

module DiagramBackend = struct
  let test_name = "diagram"

  module N = Number.Rational

  module Backend = struct
    include Backend.Machine.Diagram.Acceptance

    let accept_trace m trace =
      let convert_step =
        let open Trace in
        fun { label; time } ->
          { label =
              STS.Interpretation.VarMap.of_seq
              @@ Seq.map (fun c -> c, true) (SSet.to_seq label)
          ; time
          }
      in
      satisfied_by m (Seq.map convert_step trace)
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
