(* Fixture: no H001 violation. Do NOT compile. *)

(** zero_lt_one — zero is strictly less than one.
    Kind: helper.
    Why: base case for ord_pos_ge0 induction.
    Used by: ord_pos_ge0. *)
Lemma zero_lt_one : 0 < 1.
Proof. by []. Qed.

(** commuted_add — addition commutes on nat.
    Kind: main. *)
#[local] Arguments commuted_add _ _.
Lemma commuted_add (a b : nat) : a + b = b + a.
Proof. by rewrite addnC. Qed.

(* Out-of-scope: single-line Definition with trivial RHS is not audited. *)
Definition x := 1.
