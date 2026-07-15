(* Fixture: no C001 violation. Do NOT compile. *)
Definition EncArity := forall (A : finType), {RV P -> A} -> Prop.

Inductive enc_contractible {C : finType} (Z : {RV P -> C}) (target : R)
    : EncArity :=
  | ec_base : forall (A : finType) (X : {RV P -> A}),
      `H(Z | X) = target -> enc_contractible Z target A X.
