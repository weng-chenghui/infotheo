(* Fixture: triggers C001. Do NOT compile. *)
Inductive enc_contractible {C : finType} (Z : {RV P -> C}) (target : R)
    : forall {A : finType}, {RV P -> A} -> Prop :=
  | ec_base : forall {A : finType} (X : {RV P -> A}),
      `H(Z | X) = target -> enc_contractible Z target X.
