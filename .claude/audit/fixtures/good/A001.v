(* Fixture: no A001 violation. Do NOT compile. *)
Lemma good_have : forall n : nat, 0 < n.+1.
Proof.
move=> n.
have Hn := ltn0Sn n.
exact: Hn.
Qed.
