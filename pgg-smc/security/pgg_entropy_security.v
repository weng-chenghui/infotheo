(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG Entropy Security                                                       *)
(*                                                                            *)
(* Connects the PGG piSMC protocol to information-theoretic security via      *)
(* Shannon entropy. All definitions are generic over any group described by    *)
(* generators (GeneratedMonodromyReprType), not RAAG-specific.                *)
(*                                                                            *)
(* Key insight: var_dist and entropy are BOTH functions of the same fiber     *)
(* distribution. Given fiber counts c_x = |{σ ∈ achievable : σ(s) = x}|:    *)
(*   var_dist = 2*(N - |{x : c_x > 0}|) / N    [image-based]               *)
(*   H(P_s)   = log(Tg^L) - (1/Tg^L) Σ c_x log(c_x)  [fiber-based]        *)
(*                                                                            *)
(* Sections:                                                                  *)
(*   1. entropy_uniform_supp — H(uniform_supp C) = log |C|                   *)
(*   2. fiber_entropy — H of endpoint distribution                           *)
(*   3. entropy_divergence — D(P_s || U_N) = log N - H(P_s)                  *)
(*   4. protocol_rvs — Endpoint_RV and Share_RV random variables             *)
(*   5. entropy_security — perfect entropy security theorems                  *)
(*   6. entropy_witness — EntropyWitness record                               *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From mathcomp Require Import boolp reals.
From mathcomp Require Import reals exp.
From infotheo Require Import realType_ext realType_ln fdist proba variation_dist.
From infotheo Require Import divergence entropy.
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj.
From pgg_smc Require Import pgg_collusion_bound.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope divergence_scope.

Import GRing.Theory Num.Theory.

(******************************************************************************)
(*  Section 1: Entropy of uniform_supp                                        *)
(*                                                                            *)
(*  H(uniform_supp C) = log |C|, derivable from entropy_uniform via the      *)
(*  fact that uniform_supp C is just uniform on |C| elements restricted to    *)
(*  the ambient type.                                                         *)
(******************************************************************************)

Section entropy_uniform_supp.

Context {R : realType}.
Variable A : finType.
Variable C : {set A}.
Hypothesis HC : (0 < #|C|)%N.

Lemma entropy_uniform_supp :
  `H (@fdist_uniform_supp R A C HC) = log #|C|%:R :> R.
Proof.
rewrite /entropy fdist_uniform_supp_restrict.
have -> : \sum_(t in C) (`U HC) t * log ((`U HC) t) =
          \sum_(t in C) #|C|%:R^-1 * log (#|C|%:R^-1 : R).
  apply: eq_bigr => i Hi. by rewrite fdist_uniform_supp_in.
rewrite big_const iter_addr addr0 logV; last by rewrite ltr0n.
rewrite -mulNrn mulrN opprK -mulrnAr -(mulr_natr (log _) #|C|) mulrCA.
by rewrite mulVf ?mulr1 // pnatr_eq0 -lt0n.
Qed.

End entropy_uniform_supp.

(******************************************************************************)
(*  Section 2: Fiber Entropy Definition                                       *)
(*                                                                            *)
(*  The entropy of the endpoint distribution at sheet s, under random word    *)
(*  evaluation. Works for ANY group described by generators.                  *)
(******************************************************************************)

Section fiber_entropy.

Context {R : realType}.
Variable N'' : nat.
Let N' := N''.+1.
Let N := N'.+1.

Variable m : nat.
Let Tg := m.+1.
Variable L : nat.
Variable sigmas : Tg.-tuple {perm 'I_N}.
Let M := Gen_PGGTypes sigmas.

(* Fiber entropy at sheet s — works for ANY group *)
Definition fiber_entropy (s : 'I_N) : R :=
  `H (fdistmap (fun sigma : {perm 'I_N} => sigma s)
               (rho_from_words (R:=R) L sigmas)).

(* Under weval_inj, rho_from_words = uniform_supp(achievable), so
   fiber_entropy s = H(fdistmap eval_s (uniform_supp achievable)).
   When eval_s is also injective on achievable, the pushforward is
   uniform_supp(image_s), and H = log(Tg^L). *)
Lemma fiber_entropy_injective (s : 'I_N)
    (Hlfree : @weval_inj M L)
    (Hinj_s : {in @achievable M L &,
               injective (fun sigma : {perm 'I_N} => sigma s)}) :
  fiber_entropy s = log (Tg ^ L)%:R.
Proof.
rewrite /fiber_entropy (rho_from_words_uniform_supp Hlfree).
rewrite (fdistmap_uniform_supp_inj _ Hinj_s) entropy_uniform_supp.
congr (log _%:R).
rewrite card_in_imset //.
have -> : #|@achievable M L| = @search_space M L by [].
by rewrite weval_inj_search_space.
Qed.

(* Perfect case: Tg^L = N and eval_s injective → H = log(N) *)
Lemma fiber_entropy_perfect (s : 'I_N)
    (Hlfree : @weval_inj M L)
    (Hinj_s : {in @achievable M L &,
               injective (fun sigma : {perm 'I_N} => sigma s)})
    (Hbal : (Tg ^ L = N)%N) :
  fiber_entropy s = log N%:R.
Proof. by rewrite fiber_entropy_injective // Hbal. Qed.

(* Upper bound: always H ≤ log(N) *)
Lemma fiber_entropy_le_logN (s : 'I_N) :
  fiber_entropy s <= log N%:R.
Proof.
rewrite /fiber_entropy.
have Hcard : #|'I_N| = N by rewrite card_ord.
have -> : log N%:R = log #|'I_N|%:R :> R by rewrite Hcard.
exact: entropy_max.
Qed.

End fiber_entropy.

(******************************************************************************)
(*  Section 3: Entropy-Divergence Identity                                    *)
(*                                                                            *)
(*  D(P_s || U_N) = log(N) - H(P_s)                                          *)
(*  This follows from expanding KL divergence when Q is uniform.              *)
(******************************************************************************)

Section entropy_divergence.

Context {R : realType}.
Variable N'' : nat.
Let N' := N''.+1.
Let N := N'.+1.

Variable m : nat.
Let Tg := m.+1.
Variable L : nat.
Variable sigmas : Tg.-tuple {perm 'I_N}.
Let M := Gen_PGGTypes sigmas.

Let P_s (s : 'I_N) : R.-fdist 'I_N :=
  fdistmap (fun sigma : {perm 'I_N} => sigma s)
           (rho_from_words (R:=R) L sigmas).

(* Fundamental identity: entropy gap = KL divergence from uniform *)
Lemma fiber_entropy_gap (s : 'I_N) :
  log N%:R - fiber_entropy (R:=R) L sigmas s =
  D(P_s s || fdist_uniform (card_ord N)).
Proof.
rewrite /fiber_entropy /entropy /div opprK.
have -> : log N%:R = \sum_(a in 'I_N) P_s s a * log N%:R.
  by rewrite -mulr_suml FDist.f1 mul1r.
rewrite -big_split /=.
apply: eq_bigr => a _.
rewrite addrC -mulrDr fdist_uniformE card_ord.
have [->|Hpos] := eqVneq (P_s s a) 0.
  by rewrite mul0r mul0r.
congr (_ * _).
have Hgt : (0 < P_s s a) by rewrite lt0r Hpos FDist.ge0.
rewrite logDiv ?Hgt ?invr_gt0 ?ltr0n //.
rewrite logV ?ltr0n //.
by rewrite opprK.
Qed.

(* Entropy gap is non-negative (consequence of div_ge0 or entropy_max) *)
Lemma fiber_entropy_gap_ge0 (s : 'I_N) :
  0 <= log N%:R - fiber_entropy (R:=R) L sigmas s.
Proof.
by rewrite subr_ge0; exact: fiber_entropy_le_logN.
Qed.

End entropy_divergence.

(******************************************************************************)
(*  Section 4: Protocol Random Variables                                      *)
(*                                                                            *)
(*  Endpoint_RV: the random variable "party at sheet s sees endpoint x"      *)
(*  under uniform word sampling. Its entropy equals fiber_entropy.            *)
(******************************************************************************)

Section protocol_rvs.

Context {R : realType}.
Variable N'' : nat.
Let N' := N''.+1.
Let N := N'.+1.

Variable m : nat.
Let Tg := m.+1.
Variable L : nat.
Variable sigmas : Tg.-tuple {perm 'I_N}.
Let M := Gen_PGGTypes sigmas.

Hypothesis Hlfree : @weval_inj M L.

Let card_word_L' : #|{: L.-tuple 'I_Tg}| = (Tg ^ L).-1.+1.
Proof. by rewrite card_tuple card_ord prednK // expn_gt0. Qed.

Let w_uniform : R.-fdist (L.-tuple 'I_Tg) :=
  fdist_uniform card_word_L'.

(* Endpoint RV: party at sheet s sees endpoint under random word *)
Definition Endpoint_RV (s : 'I_N) : L.-tuple 'I_Tg -> 'I_N :=
  fun w => @endpoint M (@word_eval M L w) s.

(* Bridge: entropy of Endpoint_RV = fiber_entropy *)
Lemma Endpoint_RV_entropy (s : 'I_N) :
  `H (fdistmap (Endpoint_RV s) w_uniform) =
  fiber_entropy (R:=R) L sigmas s.
Proof.
rewrite /fiber_entropy /rho_from_words fdistmap_comp.
congr (`H (fdistmap _ _)).
rewrite /w_uniform /word_uniform.
congr (fdist_uniform _).
exact: eq_irrelevance.
Qed.

End protocol_rvs.

(******************************************************************************)
(*  Section 5: Entropy Security Theorems                                      *)
(*                                                                            *)
(*  Perfect case: maximum entropy = no information leakage.                   *)
(******************************************************************************)

Section entropy_security.

Context {R : realType}.
Variable N'' : nat.
Let N' := N''.+1.
Let N := N'.+1.

Variable m : nat.
Let Tg := m.+1.
Variable L : nat.
Variable sigmas : Tg.-tuple {perm 'I_N}.
Let M := Gen_PGGTypes sigmas.

Hypothesis Hlfree : @weval_inj M L.

(* Perfect entropy security: H = log N when eval_s injective and Tg^L = N *)
Theorem pgg_entropy_security_perfect (s : 'I_N)
    (Hinj_s : {in @achievable M L &,
               injective (fun sigma : {perm 'I_N} => sigma s)})
    (Hbal : (Tg ^ L = N)%N) :
  fiber_entropy (R:=R) L sigmas s = log N%:R.
Proof. exact: fiber_entropy_perfect. Qed.

(* Entropy lower bound from eval_s injectivity *)
Theorem pgg_entropy_lower_bound (s : 'I_N)
    (Hinj_s : {in @achievable M L &,
               injective (fun sigma : {perm 'I_N} => sigma s)}) :
  log (Tg ^ L)%:R <= fiber_entropy (R:=R) L sigmas s.
Proof.
by rewrite fiber_entropy_injective //; exact: Order.POrderTheory.lexx.
Qed.

End entropy_security.

(******************************************************************************)
(*  Section 6: EntropyWitness Record                                          *)
(*                                                                            *)
(*  Generic over M : GeneratedMonodromyReprType (not RAAG-specific).          *)
(*  Packages a min-entropy lower bound for all sheets.                        *)
(******************************************************************************)

Section entropy_witness.

Variable R : realType.
Variable M : GeneratedMonodromyReprType.
Let N' := pgg_N' M.

Record EntropyWitness := MkEntropyWitness {
  ew_L : nat;
  ew_min_entropy : R;
  ew_rho_dist : R.-fdist {perm 'I_N'.+1};
  ew_entropy_bound :
    forall (s : 'I_N'.+1),
    (ew_min_entropy <= `H (fdistmap (fun sigma : {perm 'I_N'.+1} => sigma s)
                                    ew_rho_dist))%O
}.

(* Construct EntropyWitness from a rho_dist + entropy bound — ANY group.
   When used with SecurityWitness, pass sw_L and sw_rho_dist directly. *)
Definition entropy_witness_from_rho
    (L : nat)
    (rho_dist : R.-fdist {perm 'I_N'.+1})
    (H_min : R)
    (Hbound : forall s : 'I_N'.+1,
      (H_min <= `H (fdistmap (fun sigma : {perm 'I_N'.+1} => sigma s)
                             rho_dist))%O)
    : EntropyWitness :=
  @MkEntropyWitness L H_min rho_dist Hbound.

End entropy_witness.

Arguments MkEntropyWitness {R M}.
Arguments entropy_witness_from_rho {R M}.

(******************************************************************************)
(*  Section 7: Injective-eval_s EntropyWitness constructor                    *)
(*                                                                            *)
(*  For groups where word_eval AND eval_s are injective on achievable(L),     *)
(*  we get H(P_s) = log(Tg^L) for all s, giving a clean EntropyWitness.      *)
(******************************************************************************)

Section entropy_witness_injective.

Variable R : realType.
Variable m n' : nat.
Variable sigmas : m.+1.-tuple {perm 'I_n'.+2}.
Let M := Gen_PGGTypes sigmas.

Definition entropy_witness_inj (L : nat)
    (Hlfree : @weval_inj M L)
    (Hinj_s : forall s : 'I_n'.+2,
      {in @achievable M L &,
       injective (fun sigma : {perm 'I_n'.+2} => sigma s)})
    : EntropyWitness R M.
Proof.
refine (@MkEntropyWitness R M L (log (m.+1 ^ L)%:R)
         (rho_from_words (R:=R) L sigmas) _).
move=> s.
rewrite -(fiber_entropy_injective (R:=R) (N'':=n') (sigmas:=sigmas) Hlfree
          (Hinj_s s)).
exact: Order.POrderTheory.lexx.
Defined.

End entropy_witness_injective.
