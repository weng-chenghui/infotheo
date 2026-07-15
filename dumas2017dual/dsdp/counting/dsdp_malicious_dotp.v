From mathcomp Require Import all_boot all_order all_algebra reals.
Require Import realType_ext fdist proba.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(* Formalization of:                                                          *)
(*                                                                            *)
(* Dumas, J. G., Lafourcade, P., Orfila, J. B., & Puys, M. (2017).            *)
(* Dual protocols for private multi-party matrix multiplication               *)
(* and trust computations.                                                    *)
(* Computers & security, 71, 51-70.                                           *)
(*                                                                            *)
(******************************************************************************)

(******************************************************************************)
(* N-party malicious-Alice extraction for the DSDP protocol, generalizing the *)
(* 2D dot product analysis to N-1 dimensions.                                 *)
(*                                                                            *)
(* malicious_n : Alice querying with US = e_1 obtains relay party 1's input   *)
(*   from the dot product, dotp_n ConstUS_n v = v ord0.                       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

Section malicious_n.

Context {R : realType}.
Variable T : finType.
Variable P : R.-fdist T.

(* Z/pqZ parameters *)
Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Local Notation m := (p * q).
Local Notation msg := 'Z_m.

Variable n_relay : nat.

(* N-dimensional dot product *)
Definition dotp_n (x y : {ffun 'I_n_relay.+1 -> msg}) : msg :=
  \sum_(i < n_relay.+1) x i * y i.

(* Dot product as random variable *)
Definition Dotp_n_rv (X Y : {RV P -> {ffun 'I_n_relay.+1 -> msg}}) : {RV P -> msg} :=
  fun t => dotp_n (X t) (Y t).

(* First basis vector: e_1 = (1, 0, ..., 0) *)
Definition ConstUS_n : {ffun 'I_n_relay.+1 -> msg} :=
  [ffun i => if i == ord0 then 1 else 0].

(* e_1 . v = v_1: the first basis vector extracts the first component *)
Lemma dotp_n_e1 (v : {ffun 'I_n_relay.+1 -> msg}) :
  dotp_n ConstUS_n v = v ord0.
Proof.
rewrite /dotp_n (bigD1 ord0) //=.
rewrite ffunE eq_refl mul1r.
rewrite big1 ?addr0 //.
move=> i Hi.
by rewrite ffunE (negbTE Hi) mul0r.
Qed.

End malicious_n.

