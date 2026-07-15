(* Fixture: triggers A004. Do NOT compile. *)
Lemma bad_assert : forall n, 0 < n.+1.
Proof.
move=> n.
assert (0 < n.+1) as Hn.
  by apply: ltn0Sn.
exact: Hn.
Qed.
