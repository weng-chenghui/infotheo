(* Fixture: triggers H003. Do NOT compile. *)

(** a.  @composes: helper_b *)
Lemma helper_a : 0 < 1.
Proof. by []. Qed.

(** b.  @composes: helper_a *)
Lemma helper_b : 0 < 2.
Proof. by []. Qed.
