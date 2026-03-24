open Common
open Prelude

module Make (Impl : Impl.S) = struct
  module IDs = struct
    module Event = String
    module Color = String
    module Place = String
    module Probe = Number.Integer
  end

  open IDs
  module Probes = Map.Make (IDs.Probe)
  module Time = Number.Integer
  module Impl = Impl (IDs) (Time)
  module Token = Impl.Token

  let s = "sensor"
  let c = "controller"
  let a = "actuator"
  let q = "queue"
  let v = "variable"
  let chain_color = "test"
  let chain_probe = 0

  (** s -> c ? a
     s period = 3
     c event-triggered on s
     a period = 5 *)
  let net_description =
    Declaration.
      [ Variable { name = v; writes = [ c ]; reads = [ a ] }
      ; Queue { name = q; writes = [ s ]; reads = [ c ] }
      ; Inject { at = s; color = chain_color }
      ; Probe { name = chain_probe; color = chain_color; at = a }
      ]
  ;;

  let trace1 =
    Trace.
      [ { label = [ s; c; a ]; time = 0 }
      ; { label = []; time = 1 }
      ; { label = []; time = 2 }
      ; { label = [ s; c ]; time = 3 }
      ; { label = []; time = 4 }
      ; { label = [ a ]; time = 5 }
      ; { label = [ s; c ]; time = 6 }
      ]
  ;;

  let trace2 = Trace.[ { label = [ s; a; c ]; time = 0 } ]

  open Ppx_sexp_conv_lib.Conv
  open Ppx_compare_lib.Builtin

  let get_tokens trace =
    let net = Impl.of_decl net_description in
    let tokens = Dynarray.create () in
    let consume_one_iter probe token =
      if IDs.Probe.equal probe chain_probe then Dynarray.add_last tokens token
    in
    Impl.consume_trace net ~start:(fun _ _ -> ()) ~finish:consume_one_iter trace;
    Dynarray.to_list tokens
  ;;

  let%test_unit "nominal" =
    let construct_visits colors list =
      let first instant = Token.build_external instant colors [] in
      let wrap instant cause = Token.build_external instant colors [ cause ] in
      List.reduce_right wrap first list
    in
    let colors = Token.Coloring.singleton chain_color in
    let trace1 = List.to_seq trace1 in
    [%test_eq: Token.t list]
      (get_tokens @@ Trace.sequalize_trace ~label_to_seq:List.to_seq trace1)
      [ construct_visits colors [ a, 0; c, 0; s, 0 ]
      ; construct_visits colors [ a, 5; c, 3; s, 3 ]
      ]
  ;;

  let%test_unit "unfavorable microstep" =
    let trace2 = List.to_seq trace2 in
    [%test_eq: Token.t list]
      (get_tokens @@ Trace.sequalize_trace ~label_to_seq:List.to_seq trace2)
      []
  ;;

  let%test_unit "same sexp" =
    [%test_eq: (Event.t, Place.t, Color.t, Probe.t) Declaration.t]
      net_description
      (Declaration.t_of_sexp
         Event.t_of_sexp
         Place.t_of_sexp
         Color.t_of_sexp
         Probe.t_of_sexp
       @@ Sexplib.Sexp.of_string
            "((Variable (name variable)(writes(controller))(reads(actuator)))\n\
             (Queue(name queue)(writes(sensor))(reads(controller)))\n\
             (Inject(at sensor)(color test))\n\
             (Probe(name 0)(color test)(at actuator)))")
  ;;
end
