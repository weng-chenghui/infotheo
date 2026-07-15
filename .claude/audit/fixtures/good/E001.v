(* Fixture: no E001 violation. Do NOT compile. *)
Lemma tight : forall n, 0 < n.+1.
Proof.
move=> n.
have H := ltn0Sn n.
exact: H.
Qed.
