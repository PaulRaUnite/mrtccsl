module Q = Common.Number.Rational

let () =
  let _ = Bdd.init () in
  let open Mrtccsl in
  let (now, m), cstr_index =
    Backend.Machine.of_spec
      CCSL.Language.Specification.
        { clock =
            CCSL.Language.Cstr.
              [ (* AbsPeriodic
                  { out = "tick"
                  ; period = Q.from_pair (5, 1)
                  ; error = Var "jitter"
                  ; offset = Var "offset"
                  } *)
                CCSL.Language.Cstr.Precedence { cause = "a"; conseq = "b" }
              ; Periodic
                  { out = "b"; period = 5; error = Var "e"; offset = Const 0; base = "r" }
              ]
        ; probabilistic = []
        ; duration = []
        ; integer =
            [ NumRelation ("e", `LessEq, Const 1)
            ; NumRelation ("e", `MoreEq, Const (-1))
            ]
        }
  in
  let open STS.Interpretation.Diagram in
  let d = of_machine ~order:Order.state_bool_now_numeric now m in
  to_dot @@ to_graph ~cstr_index d
;;
