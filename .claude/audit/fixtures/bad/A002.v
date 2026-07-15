(* Fixture: triggers A002. Do NOT compile. *)
(* Covers tactic form, view form, and the arity alias. *)

(* Tactic form: f_equal. as a standalone step. *)
Lemma bad_fequal_tactic : forall a b : nat, a = b -> S a = S b.
Proof.
move=> a b eq_ab.
f_equal.
exact: eq_ab.
Qed.

(* View form: f_equal applied via a move view. *)
Lemma bad_fequal_view : forall n m : nat, n = m -> n - 1 = m - 1.
Proof.
move=> n m /(f_equal (fun z => z - 1)).
by [].
Qed.

(* Arity alias: f_equal2 / f_equal_dep are also in scope. *)
Lemma bad_fequal_arity : forall a b c d : nat, a = c -> b = d -> a + b = c + d.
Proof.
move=> a b c d Hac Hbd.
apply: f_equal2; by [].
Qed.
