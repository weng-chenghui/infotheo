(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* den_boer_profile: the five-card (C_5) plug of the shared MonodromyProfile   *)
(*                                                                            *)
(* The plug bundles the five-card starting interface (FiveCard_PI, the five    *)
(* card positions in order), the uniform dealing-phase security witness        *)
(* (epsilon = 0, perfect security), and den_boer_plug: the bool/'I_5 threshold *)
(* scheme fcI_scheme, the identity content readout fc_content, the C_5          *)
(* monodromy pgg_rho, and the proven full-group reconstruction invariance       *)
(* fcI_perm_compatible. This routes the foundational five-card trick through    *)
(* the same shared exchange_* program as the s5, s5x5 and abelian instances.    *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
Require Import pgg_interface.
From pgg_smc Require Import five_card_group five_card_program
                            five_card_scheme_I5 five_card_security.
From pgg_smc Require Import card_exchange_pismc pgg_input_commitment.
From pgg_smc Require Import pgg_monodromy_profile.
Require Import smc_session_types.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** den_boer_profile — plug the five-card C_5 cyclic-shift monodromy (N = 5).
    Kind: instance. What: the MonodromyProfile bundling FiveCard_PI, the
    perfect (epsilon = 0) uniform security witness, and den_boer_plug, with
    secret type bool. Why: the foundational five-card-trick plug of the shared
    program; its dealing phase is perfectly anonymous and its reconstruction
    recovers one bit (a AND b). Used-by: contrast demos, landscape. *)
Definition den_boer_profile (R : realType) : MonodromyProfile R :=
  @MkMonodromyProfile R FiveCard_M bool FiveCard_PI
    (fc_security_uniform R) den_boer_plug.

(** run_k_den_boer — the five-card plug's privacy threshold is 2.
    Kind: example. What: run_k (den_boer_profile R) = 2. Why: contrast
    character (any single revealed card leaks nothing about the AND, but two
    may), read off the shared run_k. *)
Lemma run_k_den_boer (R : realType) : run_k (den_boer_profile R) = 2.
Proof. by []. Qed.

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
(* den_boer_protocol_correct.                                                 *)
(******************************************************************************)

Local Open Scope sproc_scope.

(** den_boer_assemble — assemble the two committed input bits into the dealing
    word table.
    Kind: helper.
    What: returns the singleton identity word, so the dealer deals the
    canonical (unshuffled) den Boer arrangement readout. Why: the committed
    bits drive the input-commitment stage; the reconstruction is fixed by the
    starting layout, so any word table preserves correctness. The identity
    word is the canonical den Boer arrangement read. Used-by:
    den_boer_dealer_committed. *)
Definition den_boer_assemble (committed : seq 'I_(pgg_N' FiveCard_M).+1)
    : seq (pgg_gT FiveCard_M) := [:: 1%g].

(** den_boer_players — the five-player list for the den Boer dealing phase.
    Kind: helper.
    What: the explicit five-element list of 'I_5 player ordinals. Why: a
    concrete list (rather than enum 'I_5) lets the dealer's fold_senv reduce
    under vm_compute when checking session-type duality. Used-by:
    den_boer_dealer_committed, den_boer_verifier_committed. *)
Definition den_boer_players : seq 'I_(pi_T' FiveCard_PI).+1 :=
  [:: @Ordinal 5 0 isT; @Ordinal 5 1 isT; @Ordinal 5 2 isT;
      @Ordinal 5 3 isT; @Ordinal 5 4 isT].

(** den_boer_dealer_committed — the den Boer dealer with the M = 2
    input-commitment prologue.
    Kind: instance.
    What: exchange_dealer_with_commit at FiveCard_PI receiving from input
    parties 7 and 8, assembling via den_boer_assemble, then running the
    fc_content dealing body for the five players. Why: routes the foundational
    five-card trick through the shared committed-dealer program with the two
    input bits committed up front. Used-by: the den Boer M = 2 duality
    lemmas. *)
Definition den_boer_dealer_committed (P_idx : nat)
    : @sproc pgg_dtype (pgg_data (pgg_N' FiveCard_M).+1) dealer_idx _ _ :=
  exchange_dealer_with_commit FiveCard_PI [:: 7; 8] den_boer_assemble
    fc_content den_boer_players P_idx.

(** den_boer_ap_dealer_committed — the committed den Boer dealer as an aproc.
    Kind: example. *)
Definition den_boer_ap_dealer_committed (P_idx : nat) :=
  mk_aproc (den_boer_dealer_committed P_idx).

(** den_boer_ap_input0 — input party 0 (process id 7) committing bit a as an
    aproc.
    Kind: example. *)
Definition den_boer_ap_input0 (a : bool) :=
  mk_aproc (@pgg_commit FiveCard_M 7 (encode_bool a)).

(** den_boer_ap_input1 — input party 1 (process id 8) committing bit b as an
    aproc.
    Kind: example. *)
Definition den_boer_ap_input1 (b : bool) :=
  mk_aproc (@pgg_commit FiveCard_M 8 (encode_bool b)).

(** den_boer_ap_player0 — den Boer player 0 as an aproc.
    Kind: example. *)
Definition den_boer_ap_player0 :=
  mk_aproc (exchange_player FiveCard_PI (@Ordinal 5 0 isT)).

(** den_boer_ap_verifier — the den Boer verifier as an aproc.
    Kind: example. *)
Definition den_boer_ap_verifier :=
  mk_aproc (exchange_verifier FiveCard_PI den_boer_players).

(** den_boer_commit_input0_dual — the committed dealer is dual to input party 0.
    Kind: main.
    Why: the prologue's first receive is the session dual of the first input
    party's bit commit (a embedded via encode_bool), for the concrete M = 2
    den Boer instance. *)
Lemma den_boer_commit_input0_dual (a : bool) (P_idx : nat) :
  channels_dual (den_boer_ap_dealer_committed P_idx) (den_boer_ap_input0 a).
Proof. apply/eqP. rewrite /channels_dual /are_dual. by vm_compute. Qed.

(** den_boer_commit_input1_dual — the committed dealer is dual to input party 1.
    Kind: main. *)
Lemma den_boer_commit_input1_dual (b : bool) (P_idx : nat) :
  channels_dual (den_boer_ap_dealer_committed P_idx) (den_boer_ap_input1 b).
Proof. apply/eqP. rewrite /channels_dual /are_dual. by vm_compute. Qed.

(** den_boer_commit_player0_dual — the committed dealer stays dual to player 0.
    Kind: main.
    Why: the input-commitment prologue does not disturb the dealing-phase
    sends, so the dealer's session with each player is unchanged. *)
Lemma den_boer_commit_player0_dual (P_idx : nat) :
  channels_dual (den_boer_ap_dealer_committed P_idx) den_boer_ap_player0.
Proof. apply/eqP. rewrite /channels_dual /are_dual. by vm_compute. Qed.

(** den_boer_commit_verifier_dual — the committed dealer stays dual to the
    verifier.
    Kind: main. *)
Lemma den_boer_commit_verifier_dual (P_idx : nat) :
  channels_dual (den_boer_ap_dealer_committed P_idx) den_boer_ap_verifier.
Proof. apply/eqP. rewrite /channels_dual /are_dual. by vm_compute. Qed.

(** den_boer_committed_nil — with no committed inputs the committed dealer is
    the plain den Boer dealer on the assembled-from-nothing word table.
    Kind: helper.
    What: the M = 0 degeneration specialised to the den Boer instance, holding
    by computation. Why: confirms the committed dealer extends, rather than
    replaces, the uncommitted dealing program. Used-by: documentation of the
    prologue's conservativity. *)
Lemma den_boer_committed_nil (P_idx : nat) :
  exchange_dealer_with_commit FiveCard_PI [::] den_boer_assemble fc_content
    den_boer_players P_idx
  = exchange_dealer FiveCard_PI fc_content den_boer_players
      (den_boer_assemble [::]) P_idx.
Proof. by []. Qed.

(** den_boer_committed_protocol_correct — end-to-end correctness through the
    committed dealer.
    Kind: main.
    What: for any hidden monodromy element P, reconstructing the dealt
    endpoints recovers the secret bit. Why: the reconstruction is fixed by the
    starting layout and is invariant under the monodromy (pgg_recon_endpoints
    does not depend on the dealer's word table), so committing the two input
    bits up front leaves correctness exactly as den_boer_protocol_correct.
    Used-by: the den Boer input-commitment correctness claim. *)
Theorem den_boer_committed_protocol_correct (s : bool) (P : pgg_gT FiveCard_M) :
  P \in pgg_G FiveCard_M ->
  ts_valid fcI_scheme s
    [tuple fc_content
       (tnth (cast_tuple (esym (congr1 S den_boer_HT)) (pi_starts FiveCard_PI)) j)
    | j < (ts_T' fcI_scheme).+1] ->
  @pgg_recon_endpoints FiveCard_M FiveCard_PI bool fcI_scheme den_boer_HT
    fc_content P = s.
Proof. exact: den_boer_protocol_correct. Qed.
