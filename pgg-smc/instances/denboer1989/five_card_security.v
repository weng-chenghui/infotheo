(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Five-Card Trick: Transitivity and Regularity of the C_5 Action            *)
(*                                                                            *)
(* The five-card trick uses fc_sigma = (0 1 2 3 4), a 5-cycle generating      *)
(* C_5. This file proves:                                                     *)
(*                                                                            *)
(*   fc_G_pos       == the group C_5 is non-trivial (0 < |G|)                 *)
(*   fc_orbit_full  == C_5 acts transitively on 'I_5: the orbit of any        *)
(*                     sheet s under G is all of 'I_5                         *)
(*   fc_eval_inj    == C_5 acts regularly: eval_at s is injective on G        *)
(*                     (since |G| = |'I_5| = 5)                               *)
(*                                                                            *)
(* These properties are prerequisites for the SecurityWitness instantiation.  *)
(*                                                                            *)
(* The ThresholdWitness and AlgebraicRigidity are vacuous for this instance:  *)
(* |C_5| = 5 << 120 = PGL(2,5) = n(n^2-1), so the genus-0 regime holds      *)
(* trivially and T = k (every party's reveal is essential).                   *)
(*                                                                            *)
(* sw_exact is populated through uniform_security_witness, which sets         *)
(* sw_exact = Some (MkSecurityExact rho_uniform 0 endpoint_exact). The exact  *)
(* var_dist = 0 equality follows from regularity and transitivity of the     *)
(* C_5 action proved below.                                                  *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm action.
From mathcomp Require Import morphism ssralg boolp reals.
From mathcomp Require Import prime finalg zmodp poly cyclic.
From infotheo Require Import realType_ext fdist proba variation_dist.
Require Import pgg_interface.
From pgg_smc Require Import five_card_group pgg_collusion_bound
                            pgg_uniform_security five_card_program
                            five_card_scheme_I5.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    algebraic_rigidity.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope group_scope.

Section five_card_security.

(** Local abbreviations *)
Let G := pgg_G FiveCard_M.
Let sigma := fc_sigma.

(******************************************************************************)
(** * Auxiliary: fc_sigma computes as expected                                *)
(******************************************************************************)

Lemma fc_sigma_perm (x : 'I_5) : sigma x = fc_sigma_fun x.
Proof. by rewrite /sigma permE. Qed.

(** sigma^5 = 1 by direct computation *)
Lemma fc_sigma5 : sigma ^+ 5 = 1 :> {perm 'I_5}.
Proof.
apply/permP => x; rewrite perm1.
by case: x => [[|[|[|[|[|x]]]]] hx];
  rewrite !expgSr expg0 !permM !permE //=; apply/val_inj.
Qed.

(** sigma is in G *)
Lemma fc_sigma_in_G : sigma \in G.
Proof.
rewrite /G /FiveCard_M /=.
apply: mem_gen.
by apply/imsetP; exists (Ordinal (ltn0Sn 0)); rewrite // tnth_ord_tuple.
Qed.

(** All powers of sigma are in G *)
Lemma fc_sigma_pow_in_G (k : nat) : sigma ^+ k \in G.
Proof. by apply: groupX; exact: fc_sigma_in_G. Qed.

(******************************************************************************)
(** * Concrete evaluation of sigma^k at each sheet                            *)
(******************************************************************************)

(** We compute sigma^k(s) for k=0..4 and all s by direct expansion. *)

Lemma fc_pow0 (s : 'I_5) : (sigma ^+ 0) s = s.
Proof. by rewrite expg0 perm1. Qed.

(** fc_pow1 — sigma applied once advances a sheet by 1 mod 5.
    Kind: helper.
    Why: Base case for the sigma^k case-splits feeding fc_reach and fc_pow_fix_zero.
    Used by: fc_reach, fc_pow_fix_zero.
*)
Lemma fc_pow1 (s : 'I_5) : val ((sigma ^+ 1) s) = (val s).+1 %% 5.
Proof.
rewrite expg1 fc_sigma_perm /fc_sigma_fun.
by case: s => [[|[|[|[|[|s]]]]] hs].
Qed.

(** For each target x, we exhibit the power of sigma that maps s to x. *)
Lemma fc_reach (s x : 'I_5) :
  exists k : 'I_5, (sigma ^+ val k) s = x.
Proof.
case: s => [[|[|[|[|[|s]]]]] hs];
case: x => [[|[|[|[|[|x]]]]] hx] //;
  try (by exists (Ordinal (isT : (0 < 5)%N)); rewrite expg0 perm1; apply/val_inj);
  try (by exists (Ordinal (isT : (1 < 5)%N));
    rewrite expg1 permE /fc_sigma_fun /=; apply/val_inj);
  try (by exists (Ordinal (isT : (2 < 5)%N));
    rewrite expgSr expg1 permM !permE /fc_sigma_fun /=; apply/val_inj);
  try (by exists (Ordinal (isT : (3 < 5)%N));
    rewrite !expgSr expg0 !permM perm1 !permE /fc_sigma_fun /=; apply/val_inj);
  try (by exists (Ordinal (isT : (4 < 5)%N));
    rewrite !expgSr expg0 !permM perm1 !permE /fc_sigma_fun /=; apply/val_inj).
Qed.

(******************************************************************************)
(** * Non-triviality of G                                                     *)
(******************************************************************************)

Lemma fc_G_pos : (0 < #|G|)%N.
Proof. exact: cardG_gt0. Qed.

(******************************************************************************)
(** * Transitivity: the orbit of any sheet s under G is all of 'I_5          *)
(******************************************************************************)

Lemma fc_orbit_full (s : 'I_5) :
  [set (g : {perm 'I_5}) s | g in G] = [set: 'I_5].
Proof.
have H : forall x : 'I_5, x \in [set (g : {perm 'I_5}) s | g in G] = (x \in [set: 'I_5]).
  move=> x; rewrite inE; apply/imsetP.
  have [k Hk] := fc_reach s x.
  exists (sigma ^+ val k); first exact: fc_sigma_pow_in_G.
  exact/esym/Hk.
apply/setP => x; exact: H.
Qed.

(******************************************************************************)
(** * Regularity: eval_at s is injective on G                                *)
(******************************************************************************)

(** Helper: sigma^k fixes any sheet s implies k is a multiple of 5. *)
Lemma fc_pow_fix_zero (k : nat) (s : 'I_5) :
  (sigma ^+ k) s = s -> k %% 5 = 0%N.
Proof.
rewrite -(expg_mod k fc_sigma5).
have Hlt : k %% 5 < 5 by exact: ltn_pmod.
case: s => [[|[|[|[|[|s]]]]] hs];
  case: (k %% 5) Hlt => [|[|[|[|[|j]]]]] //= Hlt;
  rewrite ?expgSr ?expg0 ?permM ?perm1 ?permE /fc_sigma_fun //=;
  move=> /val_inj //=.
Qed.

(** Key: any element of G that fixes a sheet must be the identity. *)
Lemma fc_fix_imp_id (g : {perm 'I_5}) (s : 'I_5) :
  g \in G -> g s = s -> g = 1.
Proof.
move=> gG gfix.
have Gcyc : G = <[sigma]>.
  rewrite /G /FiveCard_M /=.
  congr (<<_>>%G).
  apply/setP => x; apply/imsetP/set1P.
    by move=> [i _ ->]; rewrite fc_sigmasE.
  by move=> ->; exists ord0; rewrite // fc_sigmasE.
rewrite Gcyc in gG.
have /cycleP [k gk] := gG.
rewrite gk in gfix *.
rewrite -(expg_mod k fc_sigma5).
by rewrite (fc_pow_fix_zero gfix) expg0.
Qed.

(** fc_eval_inj — evaluation at any sheet s is injective on G: two elements of G that agree on s are equal.
    Kind: helper.
    Why: Regularity of the C_5 action; follows from fc_fix_imp_id and underlies fc_rhoG_regular.
    Used by: fc_rhoG_regular.
*)
Lemma fc_eval_inj (s : 'I_5) :
  {in G &, injective (fun g : {perm 'I_5} => g s)}.
Proof.
move=> g1 g2 g1G g2G Heq.
apply: (mulIg g2^-1).
rewrite mulgV.
apply: (fc_fix_imp_id (s:=s)).
  by rewrite groupM ?groupV.
by rewrite permM Heq permK.
Qed.

(******************************************************************************)
(** * Bridge: pgg_rho is the identity for Gen_PGGTypes                       *)
(******************************************************************************)

(** For Gen_PGGTypes, pgg_rho = gen_incl_morph = id on {perm 'I_5}.
    So the image rhoG = G, and all G-level properties lift to rhoG. *)
Lemma fc_rho_id (g : {perm 'I_5}) : g \in G -> @pgg_rho FiveCard_M g = g.
Proof. by []. Qed.

Let rho := morphism.mfun (@pgg_rho FiveCard_M).

(** fc_rhoG_eq — the image of G under rho equals G itself (rho is the identity morphism here).
    Kind: helper.
    Why: Lets us transport G-level facts (regularity, transitivity) into rhoG as required by the generic SecurityWitness builders.
    Used by: fc_rhoG_pos, fc_rhoG_regular, fc_rhoG_trans.
*)
Lemma fc_rhoG_eq : [set rho x | x in G] = G.
Proof.
apply/setP => x; apply/imsetP/idP.
- by move=> [g gG ->].
- by move=> xG; exists x.
Qed.

(******************************************************************************)
(** * SecurityWitness: dealing-phase security with eps = 0                    *)
(******************************************************************************)

Lemma fc_rhoG_pos : (0 < #|[set rho x | x in G]|)%N.
Proof. by rewrite fc_rhoG_eq; exact: fc_G_pos. Qed.

(** fc_rhoG_regular — the rho-image of G acts regularly (free + transitive) on every sheet.
    Kind: helper.
    Why: Regularity input to uniform_security_witness; transports fc_eval_inj across the identity morphism.
    Used by: fc_security_uniform.
*)
Lemma fc_rhoG_regular (s : 'I_5) :
  {in [set rho x | x in G] &,
   injective (fun sigma0 : {perm 'I_5} => sigma0 s)}.
Proof.
by move=> g1 g2; rewrite fc_rhoG_eq => g1G g2G; exact: (fc_eval_inj g1G g2G).
Qed.

(** fc_rhoG_trans — the rho-image of G acts transitively on every sheet.
    Kind: helper.
    Why: Transitivity input to uniform_security_witness; derived from fc_rhoG_eq + fc_orbit_full.
    Used by: fc_security_uniform.
*)
Lemma fc_rhoG_trans (s : 'I_5) :
  [set (sigma0 : {perm 'I_5}) s | sigma0 in [set rho x | x in G]] =
  [set: 'I_5].
Proof.
rewrite fc_rhoG_eq; exact: fc_orbit_full.
Qed.

Section fc_dealing_security.
Variable R : realType.

(** fc_security_uniform — uniform SecurityWitness for the five-card trick with epsilon = 0.
    Kind: instance.
    Why: Instantiates uniform_security_witness from non-triviality, regularity, and transitivity of rho(G) on the five sheets.
*)
Definition fc_security_uniform : SecurityWitness R FiveCard_M :=
  uniform_security_witness fc_rhoG_pos fc_rhoG_regular fc_rhoG_trans 1.

(** fc_eps_zero — the uniform-security witness achieves epsilon = 0.
    Kind: main.
    Why: Records the perfect-security headline: the five-card trick's dealing phase leaks nothing.
*)
Lemma fc_eps_zero : sw_bound_eps fc_security_uniform = GRing.zero.
Proof. reflexivity. Qed.

End fc_dealing_security.

End five_card_security.

(******************************************************************************)
(** * Reconstruction plug and end-to-end protocol correctness                 *)
(*                                                                            *)
(* The genus-0 RS5 ThresholdWitness/AlgebraicRigidity block (fc_covering,     *)
(* fc_covering_realised Axiom, fc_genus0_automorphism, fc_threshold_witness,  *)
(* fc_rigidity, fc_tradeoff, fc_ts_recon_correct) was removed: it was a       *)
(* vacuous (RS5_witness_trivial) packaging with no external consumer, and the *)
(* secret-space cardinality forced an 'I_5 secret that cannot model the       *)
(* one-bit (a AND b) five-card trick. The heterogeneous-secret ReconPlug      *)
(* (covering_scheme.v) replaces it: shares are card positions in 'I_5, the    *)
(* secret is a bool, and reconstruction is the rotation-invariant             *)
(* three-consecutive-hearts read (fcI_scheme, five_card_scheme_I5.v).         *)
(******************************************************************************)

(** den_boer_plug — the five-card reconstruction plug.
    Kind: instance.
    Why: the heterogeneous-secret ReconPlug for FiveCard_M: the bool/'I_5
    scheme fcI_scheme, the identity content readout fc_content, the C_5
    monodromy pgg_rho, and the proven full-group reconstruction invariance
    fcI_perm_compatible. Routes the five-card trick through the shared
    MonodromyProfile program. Used-by: den_boer_profile, the protocol
    correctness theorem. *)
Definition den_boer_plug : ReconPlug FiveCard_M bool :=
  @MkReconPlug FiveCard_M bool fcI_scheme fc_content
    (morphism.mfun (@pgg_rho FiveCard_M)) fcI_perm_compatible.

(** fc_starts_uniq — the five starting card positions are distinct.
    Kind: helper. What: uniq (ord_tuple 5). Why: the uniqueness witness for
    FiveCard_PI. Used-by: FiveCard_PI. *)
Lemma fc_starts_uniq : uniq (ord_tuple 5).
Proof. by rewrite val_ord_tuple enum_uniq. Qed.

(** FiveCard_PI — the concrete five-sheet starting interface.
    Kind: instance. What: the identity start tuple (ord_tuple 5) over the five
    card positions. Why: the identity starts make the G_stable condition reduce
    to reflexivity of pgg_rho (content = fc_content = id). Used-by:
    den_boer_HT, den_boer_protocol_correct, den_boer_profile. *)
Definition FiveCard_PI : PGGInterface FiveCard_M :=
  @MkPGGI FiveCard_M 4 (ord_tuple 5) fc_starts_uniq.

(** den_boer_HT — the scheme and interface party counts agree (both 4).
    Kind: helper. What: the cast witness, kept as erefl so tuple casts reduce
    away. Why: bridges ts_T' fcI_scheme with pi_T' FiveCard_PI in the protocol
    statements. Used-by: den_boer_G_stable, den_boer_protocol_correct. *)
Definition den_boer_HT : ts_T' fcI_scheme = pi_T' FiveCard_PI := erefl.

(** den_boer_G_stable — the monodromy permutes the starts as the share
    permutation (content = fc_content = id form).
    Kind: main.
    Why: the structural condition of protocol correctness, proven not assumed.
    With starts = ord_tuple 5 and fc_content the identity, both sides collapse
    to pgg_rho g i. Mirrors s5x5_G_stable. Used-by: den_boer_protocol_correct. *)
Lemma den_boer_G_stable :
  forall g, g \in pgg_G FiveCard_M ->
  forall i : 'I_(ts_T' fcI_scheme).+1,
    fc_content (@pgg_rho FiveCard_M g
      (tnth (cast_tuple (esym (congr1 S den_boer_HT)) (pi_starts FiveCard_PI)) i)) =
    tnth [tuple fc_content
            (tnth (cast_tuple (esym (congr1 S den_boer_HT)) (pi_starts FiveCard_PI)) j)
         | j < (ts_T' fcI_scheme).+1] (morphism.mfun (@pgg_rho FiveCard_M) g i).
Proof.
move=> g Hg i.
by rewrite tnth_mktuple /fc_content !tnth_cast_tuple !tnth_ord_tuple !cast_ord_id.
Qed.

(** den_boer_protocol_correct — recovery of the dealt endpoints returns the
    secret bit (unconditional, concrete interface).
    Kind: main.
    Why: the end-to-end guarantee for the five-card trick. For any hidden
    element P of the full C_5 monodromy, reconstructing the revealed endpoints
    recovers the secret bit, via the generic pgg_hidden_invariant_perm fed the
    proven G_stable and the plug's full-group reconstruction invariance. The
    one-bit secret (bool) is now expressible because shares are 'I_5 positions
    and the secret is the AND. *)
Theorem den_boer_protocol_correct (s : bool) (P : pgg_gT FiveCard_M) :
  P \in pgg_G FiveCard_M ->
  ts_valid fcI_scheme s
    [tuple fc_content
       (tnth (cast_tuple (esym (congr1 S den_boer_HT)) (pi_starts FiveCard_PI)) j)
    | j < (ts_T' fcI_scheme).+1] ->
  @pgg_recon_endpoints FiveCard_M FiveCard_PI bool fcI_scheme den_boer_HT
    fc_content P = s.
Proof.
move=> PG Hvalid.
apply: (@pgg_hidden_invariant_perm FiveCard_M FiveCard_PI bool fcI_scheme
          den_boer_HT fc_content (pgg_G FiveCard_M) s P
          (morphism.mfun (@pgg_rho FiveCard_M)));
  [exact: subxx | exact: den_boer_G_stable | exact: PG | exact: Hvalid
  | exact: fcI_perm_compatible].
Qed.

(** den_boer_recovers_and — reading the shuffled canonical arrangement returns
    the AND of the two input bits.
    Kind: main.
    Why: the literal den-Boer semantics tied to a AND b. The canonical
    arrangement fcI_encode (a && b) is shuffled by any monodromy element g
    (the random cyclic shift) and the three-consecutive-hearts read still
    returns a && b, because reconstruction is invariant under the C_5 action.
    This is the protocol statement specialised to the standard arrangement. *)
Corollary den_boer_recovers_and (a b : bool) (g : pgg_gT FiveCard_M) :
  g \in pgg_G FiveCard_M ->
  ts_recon fcI_scheme
    [tuple tnth (fcI_encode (a && b)) (morphism.mfun (@pgg_rho FiveCard_M) g i)
    | i < (ts_T' fcI_scheme).+1] = a && b.
Proof.
move=> Hg.
exact: (fcI_perm_compatible Hg (fcI_encode_valid (a && b))).
Qed.
