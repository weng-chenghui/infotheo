(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG: Single-Component Sum-mod-N Reconstruction                              *)
(*                                                                            *)
(* In the PGG protocol, a hidden value m in Z/NZ is encoded as T starting     *)
(* card positions s_0, ..., s_{T-1} such that sum s_i = m (mod N). After the  *)
(* walk, player i observes endpoint e_i = sigma_P(s_i). To reconstruct, the   *)
(* players *)
(* pool their endpoints and compute sum e_i mod N.  If sigma_P preserves the  *)
(* sum mod N, then sum e_i = sum s_i = m (mod N).                             *)
(*                                                                            *)
(* Section sum_mod_encoding:                                                  *)
(*   sum_mod_check  == check that T sheets sum to m mod N                     *)
(*   sum_mod_valid  == validity predicate: sheets sum to the target message   *)
(*                                                                            *)
(* Section reconstruction_correctness:                                        *)
(*   reconstruct_sum  == compute sum sigma(s_i) mod N                         *)
(*   reconstruct_correct == if sigma preserves sum mod N, reconstruction      *)
(*                          recovers the original message                     *)
(*                                                                            *)
(* Section partial_reconstruction:                                            *)
(*   partial_sum  == partial sum over a coalition C of parties                 *)
(*   partial_sum_no_info == partial sums don't reveal m                      *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop div.
From pgg_smc Require Import pgg_interface.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     Section 1: Sum-mod-N Encoding of Starting Sheets                       *)
(******************************************************************************)

Section sum_mod_encoding.

Variable N' : nat.
Let N := N'.+2.  (* N >= 2 for non-trivial modular arithmetic *)

Variable T' : nat.
Let T := T'.+1.

(* Starting sheets assigned to T parties, each an ordinal < N *)
Variable sheets : T.-tuple 'I_N.

(* The sum of starting sheet values modulo N *)
Definition sheets_sum : nat :=
  (\sum_(i < T) (tnth sheets i : nat)) %% N.

(* Check whether the sheets encode message m *)
Definition sum_mod_check (m : 'I_N) : bool :=
  sheets_sum == m.

(* Validity predicate: sheets encode the target message m *)
Definition sum_mod_valid (m : 'I_N) : Prop :=
  sheets_sum = m :> nat.

(* sum_mod_check is decidable and reflects sum_mod_valid *)
Lemma sum_mod_checkP (m : 'I_N) :
  reflect (sum_mod_valid m) (sum_mod_check m).
Proof.
rewrite /sum_mod_check /sum_mod_valid /sheets_sum.
apply: (iffP eqP) => [|->] //.
Qed.

End sum_mod_encoding.

(* Special case: single-sheet encoding *)
Section sum_mod_single.

Variable N' : nat.
Let N := N'.+2.

Variable s : 'I_N.
Let sheets := [tuple s].

Lemma sum_mod_single_sheet :
  @sheets_sum N' 0 sheets = s %% N.
Proof.
rewrite /sheets_sum big_ord_recl big_ord0 addn0.
by rewrite (tnth_nth s) /=.
Qed.

End sum_mod_single.

Arguments sheets_sum {N' T'}.
Arguments sum_mod_check {N' T'}.
Arguments sum_mod_valid {N' T'}.

(******************************************************************************)
(*     Section 2: Reconstruction Correctness                                  *)
(******************************************************************************)

Section reconstruction_correctness.

Variable N' : nat.
Let N := N'.+2.

Variable T' : nat.
Let T := T'.+1.

(* A permutation "preserves sum mod N" if for all tuples of sheet indices,
   the sum of their images equals the sum of the originals mod N *)
Definition preserves_sum_mod (sigma : {perm 'I_N}) : Prop :=
  forall (s : T.-tuple 'I_N),
    (\sum_(i < T) (sigma (tnth s i) : nat)) %% N =
    (\sum_(i < T) (tnth s i : nat)) %% N.

(* The sum of endpoints after applying sigma *)
Definition endpoint_sum (sheets : T.-tuple 'I_N) (sigma : {perm 'I_N}) : nat :=
  (\sum_(i < T) (sigma (tnth sheets i) : nat)) %% N.

(* Reconstruct: compute sum of endpoints mod N *)
Definition reconstruct_sum (sheets : T.-tuple 'I_N) (sigma : {perm 'I_N}) : nat :=
  endpoint_sum sheets sigma.

(* Main correctness theorem: if sigma preserves sum mod N,
   then the reconstruction recovers the original message *)
Theorem reconstruct_correct (sheets : T.-tuple 'I_N)
    (sigma : {perm 'I_N}) (m : 'I_N) :
  preserves_sum_mod sigma ->
  sum_mod_valid sheets m ->
  reconstruct_sum sheets sigma = m :> nat.
Proof.
rewrite /preserves_sum_mod /sum_mod_valid /reconstruct_sum /endpoint_sum
        /sheets_sum.
move=> Hpres Hvalid.
by rewrite Hpres Hvalid.
Qed.

(* The identity permutation preserves sum mod N *)
Lemma id_preserves_sum_mod :
  preserves_sum_mod (1 : {perm 'I_N}).
Proof.
by move=> s; congr (_ %% N); apply: eq_bigr => i _; rewrite perm1.
Qed.

(* Composition of sum-preserving permutations preserves sum mod N *)
Lemma comp_preserves_sum_mod (sigma1 sigma2 : {perm 'I_N}) :
  preserves_sum_mod sigma1 ->
  preserves_sum_mod sigma2 ->
  preserves_sum_mod (sigma1 * sigma2)%g.
Proof.
move=> H1 H2 s.
have -> : (\sum_(i < T) ((sigma1 * sigma2)%g (tnth s i) : nat)) =
          (\sum_(i < T) (sigma2 (sigma1 (tnth s i)) : nat)).
  by apply: eq_bigr => i _; rewrite permM.
set s' := [tuple sigma1 (tnth s i) | i < T].
have -> : (\sum_(i < T) (sigma2 (sigma1 (tnth s i)) : nat)) =
          (\sum_(i < T) (sigma2 (tnth s' i) : nat)).
  by apply: eq_bigr => i _; rewrite /s' tnth_mktuple.
rewrite (H2 s').
have -> : (\sum_(i < T) (tnth s' i : nat)) =
          (\sum_(i < T) (sigma1 (tnth s i) : nat)).
  by apply: eq_bigr => i _; rewrite /s' tnth_mktuple.
exact: (H1 s).
Qed.

End reconstruction_correctness.

Arguments preserves_sum_mod {N' T'}.
Arguments reconstruct_sum {N' T'}.
Arguments endpoint_sum {N' T'}.

(******************************************************************************)
(*     Section 3: Integration with PGG Interface                              *)
(******************************************************************************)

Section pgg_reconstruction.

Variable M : MonodromyReprType.
Variable PI : PGGInterface M.

Let gT := pgg_gT M.
Let N := (pgg_N' M).+1.
Let T := (pi_T' PI).+1.
Let rho := @pgg_rho M.
Let starts := pi_starts PI.

(* The sum of starting sheet values mod N *)
Definition pgg_sheets_sum : nat :=
  (\sum_(i < T) (tnth starts i : nat)) %% N.

(* The sum of endpoint values after applying rho(P) *)
Definition pgg_endpoint_sum (P : gT) : nat :=
  (\sum_(i < T) (rho P (tnth starts i) : nat)) %% N.

(* If rho(P) preserves sum mod N, reconstruction recovers the encoded message *)
Lemma pgg_reconstruct_correct (P : gT) (m : 'I_N) :
  (\sum_(i < T) (rho P (tnth starts i) : nat)) %% N =
  (\sum_(i < T) (tnth starts i : nat)) %% N ->
  pgg_sheets_sum = m :> nat ->
  pgg_endpoint_sum P = m :> nat.
Proof.
rewrite /pgg_endpoint_sum /pgg_sheets_sum.
by move=> -> ->.
Qed.

(* The identity group element always preserves reconstruction *)
Lemma pgg_reconstruct_id (m : 'I_N) :
  pgg_sheets_sum = m :> nat ->
  pgg_endpoint_sum (1%g : gT) = m :> nat.
Proof.
rewrite /pgg_endpoint_sum /pgg_sheets_sum => <-.
congr (_ %% N); apply: eq_bigr => i _.
by rewrite morph1 perm1.
Qed.

End pgg_reconstruction.

Arguments pgg_sheets_sum {M}.
Arguments pgg_endpoint_sum {M}.

(******************************************************************************)
(*     Section 4: Partial Reconstruction (Coalition Analysis)                 *)
(******************************************************************************)

Section partial_reconstruction.

Variable N' : nat.
Let N := N'.+2.

Variable T' : nat.
Let T := T'.+1.

(* Starting sheets *)
Variable sheets : T.-tuple 'I_N.

(* The permutation applied by the walk *)
Variable sigma : {perm 'I_N}.

(* A coalition: a subset of party indices *)
Variable C : {set 'I_T}.

(* Partial sum: sum of endpoints for parties in the coalition *)
Definition partial_sum : nat :=
  (\sum_(i in C) (sigma (tnth sheets i) : nat)) %% N.

(* Full sum: the coalition is all parties *)
Lemma partial_sum_full :
  C = [set: 'I_T] ->
  partial_sum = (\sum_(i < T) (sigma (tnth sheets i) : nat)) %% N.
Proof.
move=> HC; rewrite /partial_sum HC.
congr (_ %% N); apply: eq_bigl => i.
by rewrite in_setT.
Qed.

(* Partial sums of strict subsets do not determine m.
   Informally: knowing sum_{i in C} e_i mod N does not reveal m
   when |C| < T, because the remaining T - |C| unknown sheets
   can sum to any residue mod N. *)
Lemma partial_sum_no_info :
  forall (m1 m2 : 'I_N),
    #|C| < T ->
    sum_mod_valid sheets m1 ->
    (* There exist alternative sheets encoding m2 that agree on C *)
    exists sheets' : T.-tuple 'I_N,
      sum_mod_valid sheets' m2 /\
      (forall i : 'I_T, i \in C -> tnth sheets' i = tnth sheets i) /\
      (\sum_(i in C) (sigma (tnth sheets' i) : nat)) %% N = partial_sum.
Proof.
move=> m1 m2 HC Hvalid.
have HCT : ~~ (setT \subset C).
  apply/negP => /subset_leqif_cards [].
  by rewrite cardsT card_ord leqNgt HC.
have [j _ HjC] : exists2 j, j \in [set: 'I_T] & j \notin C.
  exact/subsetPn.
set rest := \sum_(i < T | i != j) (tnth sheets i : nat).
set new_j_val := (val m2 + N * rest.+1 - rest) %% N.
have Hnew_j_lt : new_j_val < N by exact: ltn_pmod.
set new_j := Ordinal Hnew_j_lt : 'I_N.
set sheets' := [tuple if i == j then new_j else tnth sheets i | i < T].
exists sheets'.
have Hsheet_other : forall i : 'I_T, i != j -> tnth sheets' i = tnth sheets i.
  by move=> i Hi; rewrite /sheets' tnth_mktuple (negbTE Hi).
have Hj_notin : forall i : 'I_T, i \in C -> i != j.
  move=> i HiC; apply/negP => /eqP Hij.
  by move: HjC; rewrite -Hij HiC.
split; [|split].
- rewrite /sum_mod_valid /sheets_sum.
  have -> : \sum_(i < T) (tnth sheets' i : nat) = new_j_val + rest.
    rewrite /rest (bigD1 j) //=.
    congr (_ + _).
    + by rewrite /sheets' tnth_mktuple eqxx.
    + by apply: eq_bigr => i Hi; rewrite Hsheet_other.
  rewrite /new_j_val modnDml subnK; last first.
    have H1 : rest <= rest.+1 := leqnSn rest.
    have H2 : rest.+1 <= N * rest.+1 := leq_pmull rest.+1 (isT : 0 < N).
    exact: leq_trans H1 (leq_trans H2 (leq_addl _ _)).
  rewrite mulnC addnC modnMDl.
  apply: modn_small.
  exact: (valP m2).
- by move=> i HiC; rewrite Hsheet_other // Hj_notin.
- rewrite /partial_sum; congr (_ %% N).
  by apply: eq_bigr => i HiC; rewrite Hsheet_other // Hj_notin.
Qed.

End partial_reconstruction.

Arguments partial_sum {N' T'}.
