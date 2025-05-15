From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import mathcomp_extra contra Rstruct ring reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.

(* Iwamoto2024: https://doi.org/10.1587/transfun.2023TAI0001 *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.

Reserved Notation "u *d w" (at level 40).
Reserved Notation "u \*d w" (at level 40).

Section shamirss.
Context {R : realType}.
Variables (T : finType) (m k : nat).
Let k' := k.-1. 
Let TX := [the finComRingType of 'I_m.+2].
Let VX := 'rV[TX]_k'.
Variables (s : TX) (v_c : 'rV[TX]_k') (r_k : 'rV[TX]_k').
Let psi_C' := fun v_c : 'rV[TX]_k' => r_k.
About psi_C'.
(* The type: psi_C' : 'rV_k' -> 'rV_k' is not useful.
   In Iwamoto2024, the \psi_C between eqn 8 and 9 looks typed with something
   more than just vectors of TX, but not yet random variables:

   \psi_C: (s,vi1 ,vi2 ,...,vik−1 ) |-> (s,r1,r2,...,rk−1).

   Anyway, the critical property about \psi_C is injectivity.
   To prove it we need to implement the function,
   then use can_inj.
*)
Let psi_C'_inj : injective psi_C'.
Admitted.

Variables (U : finType) .
Variables (P : R.-fdist U).
Variables (S : {RV P -> TX}).
(* TODO: do we need vector of RVs for R_K'? *)
Variables (V_C : {RV P -> 'rV[TX]_k'}) (R_K' : {RV P -> 'rV[TX]_k'}).

(* pull/161 *)
Let mutual_info_RVX  (C D : finType) (X : {RV P -> C}) (Y : {RV P -> D}):
  `I(X; Y) = `I(Y; X).
Proof. by rewrite /mutual_info_RV mutual_info_sym fdistX_RV2. Qed.

(* pull/161 *)
Let mutual_info_RVE  (C D : finType) (X : {RV P -> C}) (Y : {RV P -> D}):
  `I(X;Y) = `H `p_X - `H(X | Y).
Proof. Admitted.

(* pull/158 *)
Let joint_entropy_RVX  (A B : finType) (f : A -> B)
(RA : {RV P -> A}) (RB : {RV P -> B}) (X : {RV P -> TX}):
  injective f -> `H(RA, X) = `H(RB, X).
Proof. Admitted.

Lemma eqn10:
  `I(V_C; S) = 0.
Proof.
rewrite mutual_info_RVX.
rewrite mutual_info_RVE.
have ->: `H( S | V_C) = `H(V_C, S) - `H `p_ V_C.
  by rewrite chain_rule_RV addrAC addrC addrA addrK.
rewrite joint_entropy_RVC.
rewrite opprB addrA.
have H := joint_entropy_RVX V_C R_K' S psi_C'_inj.
rewrite joint_entropy_RVC in H.
rewrite H.
have ->: `H(R_K', S) = `H `p_ S + `H `p_ R_K' - `I(S; R_K').
  rewrite mutual_info_RVE.
  rewrite opprB addrA addrAC addrC addrAC addrA addrC addrA addrA addrK.
  exact: chain_rule_RV.
rewrite opprB addrA addrAC addrC addrAC addrA addrC addrA addrA opprB.
have ->: \sum_(a in matrix_matrix__canonical__fintype_Finite TX 1 k') `p_ R_K' a * log (`p_ R_K' a) =
  -(`H `p_ R_K').
  by rewrite /entropy opprK. (* opprB expands `H and -/entropy won't work *)
rewrite addrA addrAC addrK.
Abort.



End shamirss.
