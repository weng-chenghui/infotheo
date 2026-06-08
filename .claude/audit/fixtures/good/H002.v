(* Fixture: no H002 violation. Do NOT compile. *)

(** a.  @main security: abelian words leak no card identity. *)
Lemma well_formed_main : 0 < 1.
Proof. by []. Qed.

(** b.  @composes: well_formed_main *)
Lemma well_formed_helper : 0 < 2.
Proof. by []. Qed.
