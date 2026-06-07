(* Fixture: no H001 violation. Do NOT compile. *)

(** zero_lt_one.  @composes: ord_pos_ge0 *)
Lemma zero_lt_one : 0 < 1.
Proof. by []. Qed.

(** commuted_add.  @main correctness: addition commutes on nat. *)
#[local] Arguments commuted_add _ _.
Lemma commuted_add (a b : nat) : a + b = b + a.
Proof. by rewrite addnC. Qed.

(** deck_index.  @intent: canonical index type for the deck. *)
Definition deck_index (n : nat) : Type := 'I_n * 'I_n.

(* Out-of-scope: single-line Definition with trivial RHS is not audited. *)
Definition x := 1.
