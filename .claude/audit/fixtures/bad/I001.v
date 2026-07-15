(* Fixture: triggers I001. Do NOT compile. *)

Lemma my_proof_works : forall n : nat, 0 < n.+1.
Proof.
by [].
Qed.

Definition schreier_gen_count_test_table : nat := 42.

Section Foo.
Variable n : nat.
Hypothesis n_is_old_new : 1 < n.

(* Helper lemma with unjustified drift name and nested let. *)
Lemma helper_tmp : True.
Proof.
exact: I.
Qed.

End Foo.
