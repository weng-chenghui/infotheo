(* Fixture: triggers H001. Do NOT compile. *)

Lemma no_preceding_comment : 0 < 1.
Proof. by []. Qed.

(* TODO *)
Lemma degenerate_comment : 0 < 2.
Proof. by []. Qed.

#[local] Arguments attr_separated_lemma _ _.
Lemma attr_separated_lemma (a b : nat) : a + b = b + a.
Proof. by rewrite addnC. Qed.
