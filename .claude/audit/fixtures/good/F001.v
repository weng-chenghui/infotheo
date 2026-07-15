(* Fixture: no F001 violation. Do NOT compile. *)
Lemma schreier_transition_ge0 : forall n, 0 <= n.
Proof.
by [].
Qed.

Lemma mem_head_of_list : forall (T : Type) (x : T) (xs : list T),
  List.In x (x :: xs).
Proof.
by move=> T x xs; left.
Qed.
