(* module Q = Common.Number.Rational *)
open Common.Prelude
open Common.Number

let () =
  let _ = Bdd.init () in
  let open Mrtccsl in
  let now, m, cstr_index =
    Backend.Machine.Literal.of_spec
      CCSL.Language.Specification.
        { clock =
            CCSL.Language.Cstr.
              [ (* AbsPeriodic
                  { out = "tick"
                  ; period = Q.from_pair (5, 1)
                  ; error = Var "jitter"
                  ; offset = Var "offset"
                  } *)
                (* CCSL.Language.Cstr.Causality { cause = "a"; conseq = "b" } *)
                (* Periodic
                  { out = "b"; period = 5; error = Var "e"; offset = Const 0; base = "r" } *)
                (* Exclusion { args = [ "a"; "b" ]; choice = Some "c" } *)
                Periodic
                  { out = "o"; base = "b"; period = 3; error = var "e"; offset = const 2 }
                (* Delay { out = "o"; arg = "i"; delay = var "e"; base = "i" } *)
                (* RTdelay { arg = "i"; out = "o"; delay = var "t" } *)
              ]
        ; probabilistic = []
        ; duration =
            [ (* NumRelation ("t", `LessEq, Const (Rational.of_int 3))
            ; NumRelation ("t", `MoreEq, Const (Rational.of_int 1)) *) ]
        ; integer =
            [ NumRelation ("e", `LessEq, Const 2)
            ; NumRelation ("e", `MoreEq, Const (0))
            ]
        }
  in
  let open STS.Interpretation.Diagram in
  let d = of_machine ~order:Order.state_bool_now_numeric now m in
  to_dot @@ to_graph ~cstr_index d
;;
