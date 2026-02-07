open Prelude

(** Disjunctive normal form. *)
module DNF = struct
  type 'v term =
    | Atom of 'v
    | False

  type 'v nterm =
    | T of 'v term
    | Neg of 'v term

  let neg_term = function
    | T t -> Neg t
    | Neg t -> T t
  ;;

  type 'v conj = 'v nterm list
  type 'v t = 'v conj list

  let as_seqs disjunctions : 'v nterm Seq.t Seq.t =
    disjunctions |> List.to_seq |> Seq.map List.to_seq
  ;;

  (** True value. *)
  let top : _ t = [ [ Neg False ] ]

  (** False value. *)
  let bot : _ t = []

  (** Conjunction of formula. *)
  let ( && ) x y = List.cartesian x y |> List.map (Tuple.fn2 List.append)

  (** Disjunction of formula. *)
  let ( || ) x y = List.append x y

  (** Negation of formula. *)
  let not disjunctions =
    disjunctions
    |> List.to_seq
    |> Seq.map (fun conj -> conj |> List.to_seq |> Seq.map neg_term)
    |> Seq.product_seq
    |> List.of_seq
  ;;

  (** Tries to rewrite each atom negation as a disjunction. For example, [neg (0 < x < 1)] should rewrite as [x <= 0 \/ 1 <= x]. *)
  let expand_negative_terms ~expander disjunctions =
    let expand_nterm = function
      | T t -> Seq.singleton t
      | Neg t -> expander t
    in
    let split_conj nterms = nterms |> Seq.map expand_nterm |> Seq.product_seq in
    Seq.flat_map split_conj (as_seqs disjunctions)
  ;;

  (** Formula evaluation on boolean atoms. *)
  let eval_bool ~atom_value disjunctions =
    let eval_term = function
      | Atom a -> atom_value a
      | False -> false
    in
    let eval_nterm = function
      | T t -> eval_term t
      | Neg t -> Bool.not @@ eval_term t
    in
    List.exists (List.for_all eval_nterm) disjunctions
  ;;
end
