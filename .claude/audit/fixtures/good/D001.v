(* Fixture: no D001 violation. Do NOT compile. *)
Section Foo.
Variable n : nat.

Lemma foo_ge0 : 0 < n.+1.
Proof. by apply: ltn0Sn. Qed.

End Foo.
