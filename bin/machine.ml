(* module Q = Common.Number.Rational *)
open Common.Prelude
open Common.Number

let () =
  let simulation = true in
  let _ = Bdd.init () in
  let open Mrtccsl in
  let spec =
    CCSL.Language.Specification.
      { clock =
          CCSL.Language.Cstr.
            [ (* AbsPeriodic
                  { out = "tick"
                  ; period = Q.from_pair (5, 1)
                  ; error = Var "jitter"
                  ; offset = Var "offset"
                  } *)
              CCSL.Language.Cstr.Causality { cause = "a"; conseq = "b" }
            ; CCSL.Language.Cstr.Causality { cause = "b"; conseq = "c" }
            ; CCSL.Language.Cstr.Causality { cause = "c"; conseq = "d" }
              (* Periodic
                  { out = "b"; period = 5; error = Var "e"; offset = Const 0; base = "r" } *)
              (* Exclusion { args = [ "a"; "b" ]; choice = Some "c" } *)
              (* Periodic
                  { out = "o"; base = "b"; period = 3; error = var "e"; offset = const 2 } *)
              (* Delay { out = "o"; arg = "i"; delay = var "e"; base = "i" } *)
              (* RTdelay { arg = "i"; out = "o"; delay = var "t" } *)
            ]
      ; probabilistic = []
      ; duration =
          [ (* NumRelation ("t", `LessEq, Const (Rational.of_int 3))
            ; NumRelation ("t", `MoreEq, Const (Rational.of_int 1)) *) ]
      ; integer =
          [ (* NumRelation ("e", `LessEq, Const 2)
            ; NumRelation ("e", `MoreEq, Const (0)) *) ]
      }
  in
  let open STS.Interpretation.Diagram in
  let d, cstr_index =
    if simulation
    then (
      let clocks =
        List.sort_uniq String.compare (CCSL.Language.Specification.clocks spec)
      in
      let now, m, cstr_index = Backend.Machine.Literal.of_spec spec in
      simulation_diagram now m clocks cstr_index)
    else (
      let now, m, cstr_index = Backend.Machine.Literal.of_spec spec in
      let open STS.Interpretation.Diagram in
      acceptance_diagram now m cstr_index)
  in
  to_dot @@ to_graph ~cstr_index d
;;
