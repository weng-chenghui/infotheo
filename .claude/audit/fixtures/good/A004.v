(* Fixture: no A004 violation. Do NOT compile. *)
Lemma good_have : forall n, 0 < n.+1.
Proof.
move=> n.
have Hn : 0 < n.+1 by apply: ltn0Sn.
exact: Hn.
Qed.
