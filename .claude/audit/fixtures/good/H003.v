(* Fixture: no H003 violation. Do NOT compile. *)

(** m.  @main correctness: the headline result. *)
Lemma headline : 0 < 1.
Proof. by []. Qed.

(** a.  @composes: headline *)
Lemma reaches_main : 0 < 2.
Proof. by []. Qed.
