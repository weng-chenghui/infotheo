(* Fixture: triggers A001. Do NOT compile. *)
Lemma bad_pose : forall n : nat, 0 < n.+1.
Proof.
move=> n.
pose proof (ltn0Sn n) as Hn.
exact: Hn.
Qed.
