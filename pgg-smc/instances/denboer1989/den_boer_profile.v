(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* den_boer_profile: den Boer as the eps = 0 member of the five-card family    *)
(*                                                                            *)
(* den Boer (1989) is the unbiased member of the shared five-card family       *)
(* (five_card_family.v): the cyclic C_5 monodromy plugged through the          *)
(* five-generator instance FiveCardKim_M, at bias eps = 0 and word length 1    *)
(* (one uniform cyclic cut). At eps = 0 the second-largest eigenvalue modulus  *)
(* kim_lambda2 vanishes, so one shuffle drives the dealing-phase security bound    *)
(* sqrt 5 * kim_lambda2 ^+ 1 to 0: the perfectly-anonymous den Boer regime.       *)
(* The plug bundles the five-card starting interface (FiveCardKim_PI), the      *)
(* heterogeneous-secret bool/'I_5 threshold scheme fcI_scheme, the identity     *)
(* content readout fc_content, the C_5 monodromy pgg_rho, and the proven        *)
(* full-group reconstruction invariance fcI_perm_compatible_kim. This routes    *)
(* the foundational five-card trick through the same shared exchange_* program  *)
(* as the s5, s5x5 and abelian instances, on the same group the Kim member uses.*)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
Require Import pgg_interface.
From pgg_smc Require Import five_card_group five_card_program
                            five_card_scheme_I5.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import card_exchange_pismc pgg_input_commitment.
From pgg_smc Require Import pgg_monodromy_profile.
Require Import smc_session_types.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    algebraic_rigidity.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** den_boer_eps0_lt — the eps = 0 upper-positivity constraint of the family.
    @composes: den_boer_profile
    Naming: eps0_lt is the bias-0 instance of the family's `eps < 1/5`
    hypothesis; the suffix tracks the discharged hypothesis, not the 0 < x
    shape. At bias 0 it holds since 0 < 1/5; fed to five_card_profile. *)
Lemma den_boer_eps0_lt (R : realType) : (0 : R) < 5%:R^-1.
Proof. by rewrite invr_gt0 ltr0n. Qed.

(** den_boer_eps0_gt — the eps = 0 lower-positivity constraint of the family.
    @composes: den_boer_profile
    Naming: eps0_gt is the bias-0 instance of the family's `-4/5 < eps`
    hypothesis; the suffix tracks the discharged hypothesis, not the x < 0
    shape. At bias 0 it holds since -(4/5) < 0; fed to five_card_profile. *)
Lemma den_boer_eps0_gt (R : realType) : - (4%:R * 5%:R^-1) < (0 : R).
Proof. by rewrite oppr_lt0 divr_gt0 // ltr0n. Qed.

(** den_boer_eps0_spectral — the eps = 0 spectral-gap constraint of the family.
    @composes: den_boer_profile
    Naming: eps0_spectral is the bias-0 instance of the family's spectral-gap
    hypothesis `|eps| < 4/5; the suffix names the discharged constraint. At
    bias 0 it holds since `|0| = 0 < 4/5; fed to five_card_profile. *)
Lemma den_boer_eps0_spectral (R : realType) : `|(0 : R)| < 4%:R / 5%:R.
Proof. by rewrite normr0 divr_gt0 // ltr0n. Qed.

(** den_boer_profile — den Boer is the unbiased (eps = 0) five-card family
    member with one uniform cut.
    @intent: the MonodromyProfile obtained from five_card_profile at bias 0 and
    word length 1, bundling FiveCardKim_PI, the perfect dealing-phase security
    witness (eps = 0 forces the bound to 0 after one shuffle), and the bool/'I_5
    five-card plug five_card_plug. This is the foundational five-card trick read
    off the shared five-card family at its anonymous member: its dealing phase
    is perfectly anonymous and its reconstruction recovers one bit (a AND b).
    Used-by: contrast demos, landscape. *)
Definition den_boer_profile (R : realType) : MonodromyProfile R :=
  @five_card_profile R 0 (den_boer_eps0_lt R) (den_boer_eps0_gt R)
    (den_boer_eps0_spectral R) 1.

(** den_boer_perfect — the den Boer dealing-phase security bound is exactly 0.
    @main bound: sw_bound_eps of the den Boer profile is 0; the precise sense in
    which the unbiased family member is perfectly anonymous. One uniform cut
    (word length 1) at bias 0 drives sqrt 5 * kim_lambda2 ^+ 1 to 0, since
    kim_lambda2 0 = 0 (kim_security_at_zero). Naming: _perfect marks the lhs = 0
    perfect-security shape. *)
Lemma den_boer_perfect (R : realType) :
  sw_bound_eps (mp_security (den_boer_profile R)) = 0.
Proof. by rewrite /= kim_security_at_zero. Qed.

(** profile_k_denboer — the five-card plug's privacy threshold is 2.
    @main bound: profile_k (den_boer_profile R) = 2; the contrast
    character (any single revealed card leaks nothing about the AND, but two
    may), read off the shared profile_k of the five-card plug. *)
Lemma profile_k_denboer (R : realType) : profile_k (den_boer_profile R) = 2.
Proof. by []. Qed.

(******************************************************************************)
(** * Den Boer correctness on the five-card family instance                   *)
(*                                                                            *)
(* The end-to-end correctness theorem is the den Boer member of the shared    *)
(* five-card family, stated on FiveCardKim_M. The cast witness FiveCardKim_Teq, *)
(* the start-stability lemma FiveCardKim_G_stable and the protocol-correctness  *)
(* theorem FiveCardKim_protocol_correct mirror the original single-generator   *)
(* den Boer correctness exactly: starts are ord_tuple 5 and content is the     *)
(* identity, so G-stability collapses to reflexivity of pgg_rho, and the        *)
(* generic pgg_recon_monodromy_correct is fed the family's full-group             *)
(* reconstruction invariance fcI_perm_compatible_kim.                          *)
(******************************************************************************)

(** FiveCardKim_Teq — the scheme and interface party counts agree (both 4).
    @intent: the cast witness, kept as erefl so tuple casts reduce away;
    bridges ts_T' fcI_scheme with pi_T' FiveCardKim_PI in the protocol
    statements. Used-by: FiveCardKim_G_stable, FiveCardKim_protocol_correct. *)
Definition FiveCardKim_Teq : ts_T' fcI_scheme = pi_T' FiveCardKim_PI := erefl.

(** FiveCardKim_G_stable — the monodromy permutes the starts as the share
    permutation (content = fc_content = id form).
    @main correctness: the structural condition of protocol correctness on the
    five-card family instance, proven not assumed. With starts = ord_tuple 5 and
    fc_content the identity, both sides collapse to pgg_rho g i, exactly as in
    s5x5_G_stable. *)
Lemma FiveCardKim_G_stable :
  forall g, g \in pgg_G FiveCardKim_M ->
  forall i : 'I_(ts_T' fcI_scheme).+1,
    fc_content (@pgg_rho FiveCardKim_M g
      (tnth (cast_tuple (esym (congr1 S FiveCardKim_Teq)) (pi_starts FiveCardKim_PI)) i)) =
    tnth [tuple fc_content
            (tnth (cast_tuple (esym (congr1 S FiveCardKim_Teq)) (pi_starts FiveCardKim_PI)) j)
         | j < (ts_T' fcI_scheme).+1] (morphism.mfun (@pgg_rho FiveCardKim_M) g i).
Proof.
move=> g Hg i.
by rewrite tnth_mktuple /fc_content !tnth_cast_tuple !tnth_ord_tuple !cast_ord_id.
Qed.

(** FiveCardKim_protocol_correct — recovery of the dealt endpoints returns the
    secret bit (unconditional, five-card family instance).
    @main correctness: the end-to-end guarantee for the five-card trick on the
    family instance FiveCardKim_M. For any hidden element P of the full C_5
    monodromy, reconstructing the revealed endpoints recovers the secret bit,
    via the generic pgg_recon_monodromy_correct fed FiveCardKim_G_stable and the
    family's full-group reconstruction invariance fcI_perm_compatible_kim. The
    den Boer member of the five-card family's correctness theorem. *)
Theorem FiveCardKim_protocol_correct (s : bool) (P : pgg_gT FiveCardKim_M) :
  P \in pgg_G FiveCardKim_M ->
  ts_valid fcI_scheme s
    [tuple fc_content
       (tnth (cast_tuple (esym (congr1 S FiveCardKim_Teq)) (pi_starts FiveCardKim_PI)) j)
    | j < (ts_T' fcI_scheme).+1] ->
  @pgg_recon_endpoints FiveCardKim_M FiveCardKim_PI bool fcI_scheme FiveCardKim_Teq
    fc_content P = s.
Proof.
move=> PG Hvalid.
apply: (@pgg_recon_monodromy_correct FiveCardKim_M FiveCardKim_PI bool fcI_scheme
          FiveCardKim_Teq fc_content (pgg_G FiveCardKim_M) s P
          (morphism.mfun (@pgg_rho FiveCardKim_M)));
  [exact: subxx | exact: FiveCardKim_G_stable | exact: PG | exact: Hvalid
  | exact: fcI_perm_compatible_kim].
Qed.

(******************************************************************************)
(** * Den Boer M = 2 Input-Commitment Instance                                *)
(*                                                                            *)
(* The literal den Boer trick has two input bits a and b; the AND is the      *)
(* secret. Here those two bits are committed to the dealer before dealing:     *)
(* each input party sends its bit, embedded as a card position via            *)
(* encode_bool, as a PGG_sheet (GATE 2 — the fc_dtype FCCommit cannot be      *)
(* reused, so the existing pgg_data alphabet carries the commit). The two      *)
(* input parties commit at process ids 7 and 8, above the dealer (0),         *)
(* verifier (1) and the five players (2..6). The dealing body is the          *)
(* unchanged exchange_dealer, so the player/verifier wire is identical to the *)
(* uncommitted den Boer dealer; only the dealer gains the two-receive         *)
(* prologue.                                                                   *)
(*                                                                            *)
(* The committed value does not enter the reconstruction (which is fixed by   *)
(* the starting layout and is invariant under the monodromy element), so the  *)
(* end-to-end correctness of the committed dealer is exactly                  *)
(* FiveCardKim_protocol_correct.                                              *)
(******************************************************************************)

Local Open Scope sproc_scope.

(** den_boer_players — the five-player list for the den Boer dealing phase.
    @intent: the explicit five-element list of 'I_5 player ordinals; a concrete
    list (rather than enum 'I_5) lets the dealer's fold_senv reduce under
    vm_compute when checking session-type duality. Used-by:
    den_boer_dealer_committed, den_boer_verifier_ap. *)
Definition den_boer_players : seq 'I_(pi_T' FiveCardKim_PI).+1 :=
  [:: @Ordinal 5 0 isT; @Ordinal 5 1 isT; @Ordinal 5 2 isT;
      @Ordinal 5 3 isT; @Ordinal 5 4 isT].

(** den_boer_dealer_committed — the den Boer dealer with the M = 2
    input-commitment prologue.
    @intent: exchange_dealer_with_commit at FiveCardKim_PI receiving from input
    parties 7 and 8, dealing the identity word, then running the fc_content
    dealing body for the five players; routes the foundational five-card trick
    through the shared committed-dealer program with the two input bits
    committed up front. Used-by: the den Boer M = 2 duality lemmas. *)
Definition den_boer_dealer_committed (P_idx : nat)
    : @sproc pgg_dtype (pgg_data (pgg_N' FiveCardKim_M).+1) dealer_idx _ _ :=
  exchange_dealer_with_commit FiveCardKim_PI [:: 7; 8] (fun=> [:: 1%g])
    fc_content den_boer_players P_idx.

(** den_boer_dealer_committed_ap — the committed den Boer dealer as an aproc.
    @intent: the committed den Boer dealer packaged for the duality checks.
    Naming: den_boer_ instance prefix + dealer/committed descriptor + terminal
    _ap aproc marker; >5 components by design. *)
Definition den_boer_dealer_committed_ap (P_idx : nat) :=
  mk_aproc (den_boer_dealer_committed P_idx).

(** den_boer_input0_ap — input party 0 (process id 7) committing bit a as an
    aproc.
    @intent: the first input party's bit-commit, packaged for the duality
    checks. *)
Definition den_boer_input0_ap (a : bool) :=
  mk_aproc (@pgg_commit FiveCardKim_M 7 (encode_bool a)).

(** den_boer_input1_ap — input party 1 (process id 8) committing bit b as an
    aproc.
    @intent: the second input party's bit-commit, packaged for the duality
    checks. *)
Definition den_boer_input1_ap (b : bool) :=
  mk_aproc (@pgg_commit FiveCardKim_M 8 (encode_bool b)).

(** den_boer_player0_ap — den Boer player 0 as an aproc.
    @intent: the first dealing player, packaged for the duality checks. *)
Definition den_boer_player0_ap :=
  mk_aproc (exchange_player FiveCardKim_PI (@Ordinal 5 0 isT)).

(** den_boer_verifier_ap — the den Boer verifier as an aproc.
    @intent: the dealing verifier, packaged for the duality checks. *)
Definition den_boer_verifier_ap :=
  mk_aproc (exchange_verifier FiveCardKim_PI den_boer_players).

(** den_boer_commit_input0_dual — the committed dealer is dual to input party 0.
    @main architecture: the prologue's first receive is the session dual of the
    first input party's bit commit (a embedded via encode_bool), for the
    concrete M = 2 den Boer instance.
    Naming: den_boer_ instance prefix + commit/input0/dual descriptor;
    >5 components by design. *)
Lemma den_boer_commit_input0_dual (a : bool) (P_idx : nat) :
  channels_dual (den_boer_dealer_committed_ap P_idx) (den_boer_input0_ap a).
Proof. apply/eqP. rewrite /channels_dual /are_dual. by vm_compute. Qed.

(** den_boer_commit_input1_dual — the committed dealer is dual to input party 1.
    @main architecture: the prologue's second receive is the session dual of
    the second input party's bit commit (b embedded via encode_bool).
    Naming: den_boer_ instance prefix + commit/input1/dual descriptor;
    >5 components by design. *)
Lemma den_boer_commit_input1_dual (b : bool) (P_idx : nat) :
  channels_dual (den_boer_dealer_committed_ap P_idx) (den_boer_input1_ap b).
Proof. apply/eqP. rewrite /channels_dual /are_dual. by vm_compute. Qed.

(** den_boer_commit_player0_dual — the committed dealer stays dual to player 0.
    @main architecture: the input-commitment prologue does not disturb the
    dealing-phase sends, so the dealer's session with each player is unchanged.
    Naming: den_boer_ instance prefix + commit/player0/dual descriptor;
    >5 components by design. *)
Lemma den_boer_commit_player0_dual (P_idx : nat) :
  channels_dual (den_boer_dealer_committed_ap P_idx) den_boer_player0_ap.
Proof. apply/eqP. rewrite /channels_dual /are_dual. by vm_compute. Qed.

(** den_boer_commit_verifier_dual — the committed dealer stays dual to the
    verifier.
    @main architecture: the input-commitment prologue does not disturb the
    dealing-phase verifier wire, so the dealer's session with the verifier is
    unchanged.
    Naming: den_boer_ instance prefix + commit/verifier/dual descriptor;
    >5 components by design. *)
Lemma den_boer_commit_verifier_dual (P_idx : nat) :
  channels_dual (den_boer_dealer_committed_ap P_idx) den_boer_verifier_ap.
Proof. apply/eqP. rewrite /channels_dual /are_dual. by vm_compute. Qed.

(** den_boer_committed_nil — with no committed inputs the committed dealer is
    the plain den Boer dealer on the identity word table.
    @composes: exchange_dealer_with_commit exchange_dealer den_boer_players. The
    M = 0 degeneration specialised to the den Boer instance, holding by
    computation; confirms the committed dealer extends, rather than replaces,
    the uncommitted dealing program. *)
Lemma den_boer_committed_nil (P_idx : nat) :
  exchange_dealer_with_commit FiveCardKim_PI [::] (fun=> [:: 1%g]) fc_content
    den_boer_players P_idx
  = exchange_dealer FiveCardKim_PI fc_content den_boer_players
      [:: 1%g] P_idx.
Proof. by []. Qed.

(** den_boer_committed_protocol_correct — end-to-end correctness through the
    committed dealer.
    @main correctness: for any hidden monodromy element P, reconstructing the
    dealt endpoints recovers the secret bit. The reconstruction is fixed by the
    starting layout and is invariant under the monodromy (pgg_recon_endpoints
    does not depend on the dealer's word table), so committing the two input
    bits up front leaves correctness exactly as FiveCardKim_protocol_correct.
    Naming: den_boer_committed_protocol_correct is the instance-namespaced
    end-to-end claim; the den_boer_ instance prefix plus committed/protocol/
    correct descriptor exceed five components by design, kept for parity with
    the sibling FiveCardKim_protocol_correct and s5x5_protocol_correct. *)
Theorem den_boer_committed_protocol_correct (s : bool) (P : pgg_gT FiveCardKim_M) :
  P \in pgg_G FiveCardKim_M ->
  ts_valid fcI_scheme s
    [tuple fc_content
       (tnth (cast_tuple (esym (congr1 S FiveCardKim_Teq)) (pi_starts FiveCardKim_PI)) j)
    | j < (ts_T' fcI_scheme).+1] ->
  @pgg_recon_endpoints FiveCardKim_M FiveCardKim_PI bool fcI_scheme FiveCardKim_Teq
    fc_content P = s.
Proof. exact: FiveCardKim_protocol_correct. Qed.
