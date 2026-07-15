(* Fixture: no B001 violation. Do NOT compile. *)
Lemma good_eqVneq : forall a b : nat, a = b \/ a <> b.
Proof.
move=> a b.
case: (eqVneq a b) => ab.
  by left.
right.
exact: ab.
Qed.
