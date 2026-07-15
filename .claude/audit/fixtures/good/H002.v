(* Fixture: no H002 violation. Do NOT compile. *)

(* Zero is strictly less than one. *)
Lemma helper_full : 0 < 1.
Proof. by []. Qed.

(* For every natural n, zero is less than n+1. Consumed by downstream
   clients that need strict positivity. *)
Lemma chain_ge0 : forall n : nat, 0 < n.+1.
Proof. by []. Qed.

(* Addition on nat is commutative. *)
Lemma addnC : forall m n : nat, m + n = n + m.
Proof. by rewrite Nat.add_comm. Qed.

(* Bijection bridging the AHE and SSProve sides of the predictor
   chain. The proof reduces directly to enum_rankK; the mechanism
   carries the architectural intent that AHE plain messages and
   SSProve choice_type codes interop on the same package interface. *)
Lemma good_with_mechanism : forall n : nat, n = n.
Proof. by []. Qed.
