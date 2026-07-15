(* Fixture: no I001 violation. Do NOT compile. *)

Lemma ord_pos_ge0 : forall n : nat, 0 < n.+1.
Proof.
by [].
Qed.

(** my_proof_works — alternate alias of ord_pos_ge0 kept to match an
    external reference module.
    Kind: helper.
    Why: referenced by tests importing the external module.
    Used by: ord_pos_ge0_test.
    Naming: intentional; the name mirrors the upstream Python reference. *)
Lemma my_proof_works : forall n : nat, 0 < n.+1.
Proof.
by [].
Qed.

Definition schreier_gen_count : nat := 42.

Section Foo.
Variable n : nat.
Hypothesis n_gt1 : 1 < n.

Lemma succ_pos : 0 < n.
Proof.
by apply: leqW.
Qed.

End Foo.
