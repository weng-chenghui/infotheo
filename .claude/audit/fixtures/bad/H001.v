(* Fixture: triggers H001. Do NOT compile. *)

Lemma no_tag_no_comment : 0 < 1.
Proof. by []. Qed.

(* TODO *)
Lemma no_tag_degenerate_comment : 0 < 2.
Proof. by []. Qed.

(** plain prose with no role tag at all here. *)
Lemma no_role_tag : 0 < 3.
Proof. by []. Qed.
