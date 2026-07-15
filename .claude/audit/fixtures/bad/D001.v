(* Fixture: triggers D001. Do NOT compile. *)
Section Foo.
Variable n : nat.
Hypothesis n_gt1 : 1 < n.
Hypothesis n_gt0 : 0 < n.

Lemma foo_ge0 : 0 < n.+1.
Proof. by apply: ltn0Sn. Qed.

End Foo.
