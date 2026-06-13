(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Protocol Parameter Landscape — Demo                                       *)
(*                                                                            *)
(* Demonstrates the landscape API: given one AlgebraicRigidity instance,     *)
(* read off both security (epsilon) and threshold (gap) in one place.        *)
(*                                                                            *)
(* Two concrete instances illustrate the two regimes:                         *)
(*                                                                            *)
(*   OC(2,3):  |G| small  -> genus 0 -> gap = 0, eps = 1                    *)
(*   Monster:  |G| huge   -> genus > 0 -> gap >= 2, eps ~ 0                 *)
(*                                                                            *)
(* The point: ar_genus_gap_dichotomy forces exactly one of these two regimes.           *)
(* The landscape lemmas (ar_genus0_exact, ar_genus1_gap2, ar_hurwitz)        *)
(* refine each branch, telling you WHAT threshold you get and WHY.           *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop div order ssrnum ssralg.
From mathcomp Require Import boolp reals exp.
From infotheo Require Import realType_ext realType_ln fdist proba
                             variation_dist divergence entropy pinsker.
From mathcomp Require Import prime ssralg finalg zmodp poly cyclic.
Require Import ssralg_ext reed_solomon.
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj
                            pgg_collusion_bound pgg_entropy_security
                            pgg_schreier.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    cover_tradeoff algebraic_rigidity
                                    pgg_protocol_landscape.
From pgg_smc Require Import rigidity_monster_instance
                             rigidity_oc_instance.
From pgg_reconstruct Require Import cover_genus0 coord_perm_compatible.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope divergence_scope.

Import GRing.Theory Num.Theory.

(******************************************************************************)
(*     Monster: large group regime — both discovery and certification       *)
(*                                                                            *)
(*   Phase 1 (Discovery):                                                    *)
(*     The Schreier certificate found L*=67 where eps ~ 0.                   *)
(*     Convergence rate: eps(L) = sqrt(N) * (1-lambda)^L.                    *)
(*     At L=67: geometric decay beats sqrt(N) ~ 10^10.                       *)
(*                                                                            *)
(*   Phase 2 (Certification, from monster_rigidity):                         *)
(*     Security: eps = 2*(N - 2^67)/N ~ 0 (perfect endpoint security)       *)
(*     Entropy: H(P_s) ~ log N (near-maximum, minimal leakage)              *)
(*     Threshold: genus > 0, so gap >= 2 (forced by |G| ~ 10^53)            *)
(*                                                                            *)
(*   The landscape refines:                                                   *)
(*     - ar_large_group_forces_genus: |G| > PGL -> genus > 0                 *)
(*     - ar_genus1_gap2: even genus 1 gives gap only 2                       *)
(*     - ar_hurwitz: genus >= 2 -> |G| <= 84*(g-1), explaining WHY          *)
(*       the genus must be so large for the Monster                          *)
(*     - ar_entropy: information-theoretic view of security                  *)
(*     - ar_var_dist_from_entropy: Pinsker bridge (entropy -> var_dist)     *)
(******************************************************************************)

Section monster_landscape.

Variable R : realType.

Let ar := monster_rigidity R.

(* --- Security side --- *)

(* Q: What security does the Monster achieve? *)
(* A: For every sheet s, var_dist <= epsilon ~ 0. *)
Lemma monster_security_demo (s : 'I_monster_n.+2) :
  (var_dist (fdistmap (fun sigma : {perm 'I_monster_n.+2} => sigma s)
                      (sw_rho_dist (ar_security ar)))
            (fdist_uniform (card_ord monster_n.+2))
   <= sw_bound_eps (ar_security ar))%O.
Proof. exact: ar_security_per_position ar s. Qed.

(* --- Threshold side --- *)

(* Q: What threshold regime is the Monster forced into? *)
(* A: One of two branches — and large |G| forces the right branch. *)
Lemma monster_tradeoff_demo :
  let cs := tw_covering (ar_threshold ar) in
  (cd_genus (cs_data cs) = 0 /\
   (#|pgg_G R_monster| <= klein_genus0_bound R_monster)%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))%N)
  \/
  ((0 < cd_genus (cs_data cs))%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) +
    2 * cd_genus (cs_data cs))%N).
Proof. exact: ar_genus_gap_dichotomy ar. Qed.

(* Q: Is genus 0 available to the Monster? *)
(* A: No — |G| > PGL forces genus > 0. *)
Lemma monster_genus_forced_demo :
  (klein_genus0_bound R_monster < #|pgg_G R_monster|)%N ->
  let cs := tw_covering (ar_threshold ar) in
  (0 < cd_genus (cs_data cs))%N.
Proof. exact: ar_large_group_forces_genus ar. Qed.

(* Q: If the Monster uses a genus-1 covering, what gap? *)
(* A: At most 2 — one extra share beyond k. *)
Lemma monster_genus1_demo :
  let cs := tw_covering (ar_threshold ar) in
  cd_genus (cs_data cs) = 1 ->
  (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2)%N.
Proof. exact: ar_genus1_gap2 ar. Qed.

(* Q: If genus >= 2, why is it so large? *)
(* A: Hurwitz forces |G| <= 84*(g-1), so g >= |G|/84 + 1 ~ 10^51. *)
Lemma monster_hurwitz_demo :
  let cs := tw_covering (ar_threshold ar) in
  (2 <= cd_genus (cs_data cs))%N ->
  (ts_T (cs_scheme cs) - ts_k (cs_scheme cs) <=
   2 * cd_genus (cs_data cs))%N /\
  (#|pgg_G R_monster| <= 84 * (cd_genus (cs_data cs) - 1))%N.
Proof. exact: ar_hurwitz ar. Qed.

(* --- Phase 2: Certification — entropy view --- *)

(* Q: What is the entropy at each sheet? *)
(* A: H(P_s) <= log N — near-maximum for the Monster. *)
Lemma monster_entropy_demo (s : 'I_monster_n.+2) :
  ar_entropy ar s <= log monster_n.+2%:R.
Proof. exact: ar_entropy_le_logN. Qed.

(* Q: What is the entropy gap (information leakage)? *)
(* A: D(P_s || U_N) = log N - H(P_s), the KL divergence. *)
Lemma monster_entropy_gap_demo (s : 'I_monster_n.+2) :
  log monster_n.+2%:R - ar_entropy ar s =
  D(fdistmap (fun sigma : {perm 'I_monster_n.+2} => sigma s)
             (sw_rho_dist (ar_security ar)) ||
    fdist_uniform (card_ord monster_n.+2)).
Proof. exact: (ar_entropy_gap ar s). Qed.

(* Q: Can we bound var_dist from entropy? *)
(* A: Yes — Pinsker gives var_dist <= sqrt(2 * entropy_gap). *)
Lemma monster_pinsker_demo (s : 'I_monster_n.+2) :
  var_dist (fdistmap (fun sigma : {perm 'I_monster_n.+2} => sigma s)
                     (sw_rho_dist (ar_security ar)))
           (fdist_uniform (card_ord monster_n.+2)) <=
  Num.sqrt (2%:R * (log monster_n.+2%:R - ar_entropy ar s)).
Proof. exact: (ar_var_dist_from_entropy ar s). Qed.

(* --- Both sides from one choice --- *)

(* The Monster landscape in one theorem: *)
(* Security is near-perfect (eps ~ 0), but this forces genus > 0, *)
(* and Hurwitz tells us the covering genus must be enormous. *)
(* This IS the algebraic rigidity: you cannot have both *)
(* perfect security AND exact threshold. *)

End monster_landscape.

(******************************************************************************)
(*     OC(2,3): small group regime — certification only                     *)
(*                                                                            *)
(*   Phase 1 (Discovery):                                                    *)
(*     OC has no Schreier certificate — L*=2 was found by vm_compute scan   *)
(*     in pgg_security_demo.v (fiber_eps_scan). This is the alternative     *)
(*     discovery method for small groups where direct enumeration is fast.   *)
(*                                                                            *)
(*   Phase 2 (Certification, from oc_rigidity):                              *)
(*     Security: eps = 1 (fiber-counted, worst-case sheet s=1)              *)
(*     Threshold: genus 0 -> exact (T = k), gap = 0                         *)
(*                                                                            *)
(*   OC is the opposite extreme from the Monster: small |G| allows          *)
(*   genus 0 (exact threshold) but security is weaker (eps = 1).            *)
(******************************************************************************)

Section oc_landscape.

Variable R : realType.

(* OC rigidity requires several hypotheses about the Reed-Solomon
   code construction. We state them as local hypotheses. *)
Variables (q m' : nat) (primeq : prime q).
Variable n'' : nat.
Variable a : GF m' primeq.
Hypothesis qn : ~~ (q %| n''.+3)%nat.
Hypothesis an : (n''.+3).-primitive_root a.

Let R_oc : MonodromyReprWithGeneratorType := @Gen_PGGTypes 1 2 oc_sigmas.
Hypothesis HN : (pgg_N' R_oc).+1 = #|GF m' primeq|.
Hypothesis HG_oc : (1 < #|pgg_G R_oc|)%N.

Variable sigma_code : pgg_gT R_oc -> {perm 'I_n''.+3}.
Hypothesis sigma_fix0 :
  forall g, g \in pgg_G R_oc -> sigma_code g ord0 = ord0.
Hypothesis code_auto :
  forall g, g \in pgg_G R_oc ->
  coord_perm_compatible (RS.code a n''.+3 1) (sigma_code g).
Hypothesis oc_genus0_klein : (#|pgg_G R_oc| <= klein_genus0_bound R_oc)%N.

Let ar := oc_rigidity R HG_oc qn an HN sigma_fix0 code_auto oc_genus0_klein.

(* --- Phase 2: Certification — security side --- *)

(* Q: What security does OC achieve? *)
(* A: eps = 1 (fiber-counted). Weaker than Monster but exact threshold. *)
Lemma oc_security_demo (s : 'I_4) :
  (var_dist (fdistmap (fun sigma : {perm 'I_4} => sigma s)
                      (sw_rho_dist (ar_security ar)))
            (fdist_uniform (card_ord 4))
   <= sw_bound_eps (ar_security ar))%O.
Proof. exact: ar_security_per_position ar s. Qed.

(* Q: What is the entropy bound? *)
(* A: H(P_s) <= log 4 = 2 bits. *)
Lemma oc_entropy_demo (s : 'I_4) :
  ar_entropy ar s <= log 4%:R.
Proof. exact: ar_entropy_le_logN. Qed.

(* --- Phase 2: Certification — threshold side --- *)

(* Q: What threshold regime does OC use? *)
(* A: Genus 0, so T <= k (exact threshold, no gap). *)
Lemma oc_tradeoff_demo :
  let cs := tw_covering (ar_threshold ar) in
  (cd_genus (cs_data cs) = 0 /\
   (#|pgg_G R_oc| <= klein_genus0_bound R_oc)%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))%N)
  \/
  ((0 < cd_genus (cs_data cs))%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) +
    2 * cd_genus (cs_data cs))%N).
Proof. exact: ar_genus_gap_dichotomy ar. Qed.

(* Q: If genus 0, what's the threshold? *)
(* A: Exact: T <= k. *)
Lemma oc_genus0_demo :
  let cs := tw_covering (ar_threshold ar) in
  cd_genus (cs_data cs) = 0 ->
  (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))%N.
Proof. exact: ar_genus0_exact ar. Qed.

End oc_landscape.
