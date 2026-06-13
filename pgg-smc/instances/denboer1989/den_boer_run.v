From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg boolp reals.
Require Import pgg_interface.
From pgg_smc Require Import five_card_group five_card_program five_card_scheme_I5.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import card_exchange_pismc pgg_input_commitment.
Require Import smc_interpreter pismc smc_session_types.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme input_encoding.
From pgg_smc Require Import den_boer_profile den_boer_encoding.

(******************************************************************************)
(** * Den Boer operational realization                                        *)
(*                                                                            *)
(* The committed input bits determine the starting layout den_boer_layout ab, *)
(* injected through the dealer content readout. With starts = ord_tuple the   *)
(* endpoint recovery is the reindex form, so the running protocol recovers    *)
(* ab.1 && ab.2 rather than a constant.                                       *)
(******************************************************************************)

(** den_boer_run_output — recovering the dealt endpoints of the input-derived
    layout returns the AND of the committed bits.
    @main correctness: the running den Boer protocol computes ab.1 && ab.2, not
    a constant. The committed layout den_boer_layout ab is injected through the
    dealer content readout tnth (den_boer_layout ab); with starts = ord_tuple the
    endpoint recovery is the reindex form, discharged by pgg_recon_monodromy_correct
    fed the layout-content G-stability and den_boer_assemble_valid. *)
Lemma den_boer_run_output (ab : bool * bool) (P : pgg_gT FiveCardKim_M) :
  P \in pgg_G FiveCardKim_M ->
  @pgg_recon_endpoints FiveCardKim_M FiveCardKim_PI bool fcI_scheme FiveCardKim_Teq
    (tnth (den_boer_layout ab)) P = ab.1 && ab.2.
Proof.
move=> PG.
apply: (@pgg_recon_monodromy_correct FiveCardKim_M FiveCardKim_PI bool fcI_scheme
          FiveCardKim_Teq (tnth (den_boer_layout ab)) (pgg_G FiveCardKim_M)
          (ab.1 && ab.2) P (morphism.mfun (@pgg_rho FiveCardKim_M))).
- exact: subxx.
- by move=> g Hg i;
     rewrite tnth_mktuple !tnth_cast_tuple !tnth_ord_tuple !cast_ord_id.
- exact: PG.
- have Hlay :
    [tuple tnth (den_boer_layout ab)
       (tnth (cast_tuple (esym (congr1 succn FiveCardKim_Teq))
                (pi_starts FiveCardKim_PI)) j)
     | j < (ts_T' fcI_scheme).+1] = den_boer_layout ab.
    apply: eq_from_tnth => j.
    by rewrite tnth_mktuple !tnth_cast_tuple !tnth_ord_tuple !cast_ord_id.
  rewrite Hlay.
  exact: den_boer_assemble_valid.
- exact: fcI_perm_compatible_kim.
Qed.

(** den_boer_decode — recover the two committed input bits from their card
    encodings.
    @intent: reads the bits committed by the two input parties back out of their
    encode_bool card positions via decode_bool. *)
Definition den_boer_decode (committed : seq 'I_(pgg_N' FiveCardKim_M).+1)
    : bool * bool :=
  (decode_bool (nth ord0 committed 0), decode_bool (nth ord0 committed 1)).

(** den_boer_decodeK — decoding the honestly committed bits returns them.
    @composes: den_boer_run_output. *)
Lemma den_boer_decodeK (a b : bool) :
  den_boer_decode [:: encode_bool a; encode_bool b] = (a, b).
Proof. by rewrite /den_boer_decode /= !decode_encode_bool. Qed.

(** den_boer_dealer_layout — the den Boer committed dealer injecting the
    input-derived layout through the content readout.
    @intent: like den_boer_dealer_committed, but the dealt content readout is
    tnth (den_boer_layout (den_boer_decode committed)) instead of fc_content, so
    the dealing phase carries the input-derived layout; the bits committed at
    parties 7 and 8 then determine the recovered secret (den_boer_run_output). *)
Definition den_boer_dealer_layout (P_idx : nat) :=
  pgg_commit_prologue
    (fun committed => exchange_dealer FiveCardKim_PI
       (tnth (den_boer_layout (den_boer_decode committed)))
       den_boer_players (den_boer_assemble committed) P_idx)
    [::] [:: 7; 8].

(** den_boer_dealer_layout_ap — the input-derived-content den Boer dealer as an
    aproc.
    @intent: den_boer_dealer_layout packaged for the session-type duality
    checks. *)
Definition den_boer_dealer_layout_ap (P_idx : nat) :=
  mk_aproc (den_boer_dealer_layout P_idx).

(** den_boer_layout_player0_dual — the input-derived-content dealer stays dual to
    player 0.
    @main architecture: injecting the layout through the content readout leaves
    the dealing-phase session structure unchanged, so the dealer's session with
    each player is the same as for den_boer_dealer_committed. *)
Lemma den_boer_layout_player0_dual (P_idx : nat) :
  channels_dual (den_boer_dealer_layout_ap P_idx) den_boer_player0_ap.
Proof. apply/eqP. rewrite /channels_dual /are_dual. by vm_compute. Qed.

(** den_boer_layout_input0_dual — the input-derived-content dealer is dual to
    input party 0.
    @main architecture: the prologue's first receive is the session dual of the
    first input party's bit commit, unchanged by the content readout. *)
Lemma den_boer_layout_input0_dual (a : bool) (P_idx : nat) :
  channels_dual (den_boer_dealer_layout_ap P_idx) (den_boer_input0_ap a).
Proof. apply/eqP. rewrite /channels_dual /are_dual. by vm_compute. Qed.

(** den_boer_layout_input1_dual — the input-derived-content dealer is dual to
    input party 1.
    @main architecture: the prologue's second receive is the session dual of the
    second input party's bit commit, unchanged by the content readout. *)
Lemma den_boer_layout_input1_dual (b : bool) (P_idx : nat) :
  channels_dual (den_boer_dealer_layout_ap P_idx) (den_boer_input1_ap b).
Proof. apply/eqP. rewrite /channels_dual /are_dual. by vm_compute. Qed.

(** den_boer_layout_verifier_dual — the input-derived-content dealer stays dual
    to the verifier.
    @main architecture: the content readout leaves the dealing-phase verifier
    wire unchanged, so the dealer's session with the verifier is the same as for
    den_boer_dealer_committed. *)
Lemma den_boer_layout_verifier_dual (P_idx : nat) :
  channels_dual (den_boer_dealer_layout_ap P_idx) den_boer_verifier_ap.
Proof. apply/eqP. rewrite /channels_dual /are_dual. by vm_compute. Qed.
