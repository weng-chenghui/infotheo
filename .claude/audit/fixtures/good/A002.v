(* Fixture: no A002 violation. Do NOT compile. *)
(* Every case uses goal-level `congr <head>` — the canonical form. *)

(* Canonical goal-level tactic use. *)
Lemma good_congr_tactic : forall a b : nat, a = b -> S a = S b.
Proof.
move=> a b eq_ab.
congr S.
exact: eq_ab.
Qed.

(* Restructured view-turned-goal case: hoist the equality, then `congr`. *)
Lemma good_congr_restructured : forall n m : nat, n = m -> n - 1 = m - 1.
Proof.
move=> n m Hnm.
rewrite Hnm; congr (_ - 1).
Qed.

(* Arity case handled via goal-level `congr` on the binary head. *)
Lemma good_congr_arity : forall a b c d : nat, a = c -> b = d -> a + b = c + d.
Proof.
move=> a b c d Hac Hbd.
by congr (_ + _).
Qed.
