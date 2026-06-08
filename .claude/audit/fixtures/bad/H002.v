(* Fixture: triggers H002. Do NOT compile. *)

(** a.  @main security: x *)
Lemma empty_value_tag : 0 < 1.
Proof. by []. Qed.

(** b.  @main leakage: this label is not in the enum at all. *)
Lemma bad_label_tag : 0 < 2.
Proof. by []. Qed.

(** c.  @composes: nonexistent_xyz_target *)
Lemma dangling_composes : 0 < 3.
Proof. by []. Qed.
