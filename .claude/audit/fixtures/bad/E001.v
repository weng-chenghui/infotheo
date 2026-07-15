(* Fixture: triggers E001. Do NOT compile. *)
Lemma too_long : forall n, 0 < n.+1.
Proof.
move=> n.
have H := ltn0Sn n.
exact: H.
have extra : 1 = 1 by reflexivity.
move=> _.
Qed.
