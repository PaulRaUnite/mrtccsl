module Make (N : Denotational.Num) = struct
  let lc_init c = Denotational.Syntax.(Const N.zero < c @ 0)
  let lc_connection c = Denotational.Syntax.(c @ -1 < c @ 0)
  let inductive_step x = x
  let precondition x = x
  let postcondition x = x

  let make formula =
    precondition formula, inductive_step formula, postcondition formula
  ;;
end
