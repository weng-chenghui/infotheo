(* Fixture: triggers B001. Do NOT compile. *)
Lemma bad_boolP : forall a b : nat, a = b \/ a <> b.
Proof.
move=> a b.
have [/eqP ab|ab] := boolP (a == b).
  by left.
right.
exact: ab.
Qed.
