(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe P-B: the two count bridges of a MonodromyProfile                     *)
(*                                                                            *)
(* A MonodromyProfile carries three independent counts: the seat count        *)
(* pi_T' (mp_PI mp), the share count ts_T' (rp_scheme (mp_plug mp)) and the   *)
(* card count pgg_N' (mp_M mp). Two equalities relate them:                   *)
(*   bridge 1 (players vs shares) pi_T' (mp_PI mp) = ts_T' (rp_scheme ...)    *)
(*   bridge 2 (cards vs shares)   (pgg_N' (mp_M mp)).+1 = (ts_T' ...).+1      *)
(* Neither is a field of the record and neither holds for a generic mp.       *)
(*                                                                            *)
(* Section generic_count_bridge assumes both as section Hypotheses and builds *)
(* the endpoint decoder gen_decode (the profile-level form of the per-        *)
(* instance cast tcast (pgl27_endpoints_size s w0) of pgg-smc/instances/      *)
(* pgl27/pgl27_run.v), the plug-derived share readout gen_content_from_plug   *)
(* (bridge 2 repairs the readout rejected in probe_a_sufficiency.v), and the  *)
(* round trip gen_decode_encoded, which passes through both casts.            *)
(*                                                                            *)
(* The two instantiation sections discharge the bridges at pgl27_profile      *)
(* (seats 7, shares 7, cards 8) and at five_card_profile with bias 0 (seats   *)
(* 4, shares 4, cards 5); every bridge is erefl at both carriers.             *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    algebraic_rigidity input_encoding.
From pgg_smc Require Import pgl27_group pgl27_scheme pgl27_profile pgl27_run.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_scheme_I5.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_profile den_boer_encoding den_boer_run.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     The two bridges and what they type                                     *)
(******************************************************************************)

Section generic_count_bridge.

Variable R : realType.
Variable mp : MonodromyProfile R.

Let M   := mp_M mp.
Let PI  := mp_PI mp.
Let N   := (pgg_N' M).+1.
Let sch := rp_scheme (mp_plug mp).

(* Bridge 1: the seats of the interface and the shares of the plug's scheme
   are equinumerous. *)
Hypothesis Hplayers : pi_T' PI = ts_T' sch.

(* Bridge 2: the cards of the group and the shares of the plug's scheme are
   equinumerous. *)
Hypothesis Hcards : N = (ts_T' sch).+1.

(** gen_seat_share_count — bridge 1 in successor form.
    @main architecture: (pi_T' PI).+1 = (ts_T' sch).+1, the equality between
    the length of a collected endpoint list and the arity of run_recover. *)
Lemma gen_seat_share_count : (pi_T' PI).+1 = (ts_T' sch).+1.
Proof. by rewrite Hplayers. Qed.

(** gen_decode — the endpoint decoder of the profile.
    @intent: an endpoint list of one card per seat, transported along bridge 1
    into the argument type of run_recover and reconstructed there. *)
Definition gen_decode (ep : seq 'I_N) (Hsz : size ep = (pi_T' PI).+1)
    : mp_secretT mp :=
  run_recover (tcast (etrans Hsz gen_seat_share_count) (in_tuple ep)).

(** gen_content_from_plug — the secret-dependent share readout of the plug.
    @intent: the share tnth (ts_encode sch s) at a card position, transported
    along bridge 2; the readout probe_a_sufficiency.v records as untypable
    without that equality. *)
Definition gen_content_from_plug (s : mp_secretT mp)
    : seq 'I_N -> ('I_N -> 'I_N) :=
  fun _ i => tnth (ts_encode sch s) (cast_ord Hcards i).

(** gen_encoded_tuple — the card-indexed table of the shares of a secret.
    @intent: gen_content_from_plug read at every card position. *)
Definition gen_encoded_tuple (s : mp_secretT mp) : N.-tuple 'I_N :=
  [tuple gen_content_from_plug s [::] i | i < N].

(** gen_encoded_tuple_cast — the card-indexed table is the canonical encoding.
    @main correctness: tcast Hcards (gen_encoded_tuple s) = ts_encode sch s. *)
Lemma gen_encoded_tuple_cast (s : mp_secretT mp) :
  tcast Hcards (gen_encoded_tuple s) = ts_encode sch s.
Proof.
by apply: eq_from_tnth => j;
  rewrite tcastE tnth_mktuple /gen_content_from_plug cast_ordKV.
Qed.

(** gen_encoded_size — the card-indexed table has one entry per seat.
    @main architecture: size (gen_encoded_tuple s) = (pi_T' PI).+1, both
    bridges composed. *)
Lemma gen_encoded_size (s : mp_secretT mp) :
  size (gen_encoded_tuple s) = (pi_T' PI).+1.
Proof. by rewrite size_tuple Hcards Hplayers. Qed.

(** gen_decode_encoded — decoding the shares of a secret returns that secret.
    @main correctness: the round trip of gen_decode against
    gen_content_from_plug, through the bridge-2 cast of the readout and the
    bridge-1 cast of the decoder. *)
Lemma gen_decode_encoded (s : mp_secretT mp) :
  @gen_decode (gen_encoded_tuple s) (gen_encoded_size s) = s.
Proof.
rewrite /gen_decode -[RHS](profile_recon_encode s).
congr run_recover; apply: eq_from_tnth => j.
rewrite tcastE -gen_encoded_tuple_cast tcastE.
by rewrite (tnth_nth ord0) (tnth_nth ord0).
Qed.

End generic_count_bridge.

(******************************************************************************)
(*     Both bridges at pgl27_profile: seats 7, shares 7, cards 8              *)
(******************************************************************************)

Section pgl27_count_bridge.

Variable R : realType.

Let mpP : MonodromyProfile R := pgl27_profile R.

(** pgl_seat_count — the PGL(2,7) interface has eight seats.
    @main architecture: pi_T' (mp_PI mpP) = 7. *)
Lemma pgl_seat_count : pi_T' (mp_PI mpP) = 7.
Proof. by []. Qed.

(** pgl_share_count — the PGL(2,7) plug's scheme has eight shares.
    @main architecture: ts_T' (rp_scheme (mp_plug mpP)) = 7. *)
Lemma pgl_share_count : ts_T' (rp_scheme (mp_plug mpP)) = 7.
Proof. by []. Qed.

(** pgl_card_count — the PGL(2,7) group acts on eight cards.
    @main architecture: (pgg_N' (mp_M mpP)).+1 = 8. *)
Lemma pgl_card_count : (pgg_N' (mp_M mpP)).+1 = 8.
Proof. by []. Qed.

(** pgl_players_bridge — bridge 1 at pgl27_profile.
    @intent: pi_T' (mp_PI mpP) = ts_T' (rp_scheme (mp_plug mpP)), both sides
    reducing to 7. *)
Definition pgl_players_bridge
    : pi_T' (mp_PI mpP) = ts_T' (rp_scheme (mp_plug mpP)) := erefl.

(** pgl_cards_bridge — bridge 2 at pgl27_profile.
    @intent: (pgg_N' (mp_M mpP)).+1 = (ts_T' (rp_scheme (mp_plug mpP))).+1,
    both sides reducing to 8. *)
Definition pgl_cards_bridge
    : (pgg_N' (mp_M mpP)).+1 = (ts_T' (rp_scheme (mp_plug mpP))).+1 := erefl.

(** pgl_decode — the PGL(2,7) endpoint decoder.
    @intent: gen_decode at mpP along pgl_players_bridge. *)
Definition pgl_decode (ep : seq 'I_(pgg_N' (mp_M mpP)).+1)
    (Hsz : size ep = (pi_T' (mp_PI mpP)).+1) : mp_secretT mpP :=
  @gen_decode R mpP pgl_players_bridge ep Hsz.

(** pgl_decodeE — the PGL(2,7) endpoint decoder is the instance's own cast.
    @main architecture: pgl_decode agrees with
    ts_recon orbit_scheme (tcast _ (in_tuple ep)), the reconstruction shape of
    pgl27_run_recovers, for every endpoint list of the right length. *)
Lemma pgl_decodeE (ep : seq 'I_(pgg_N' (mp_M mpP)).+1)
    (Hsz : size ep = (pi_T' (mp_PI mpP)).+1)
    (Hsz' : size ep = (ts_T' orbit_scheme).+1) :
  pgl_decode Hsz = ts_recon orbit_scheme (tcast Hsz' (in_tuple ep)).
Proof.
rewrite /pgl_decode /gen_decode /run_recover.
by rewrite (eq_irrelevance
  (etrans Hsz (gen_seat_share_count pgl_players_bridge)) Hsz').
Qed.

(** pgl_decode_encoded — the PGL(2,7) round trip.
    @main correctness: decoding the card-indexed shares of an orbit secret
    returns that secret. *)
Lemma pgl_decode_encoded (s : bool) :
  pgl_decode (@gen_encoded_size R mpP pgl_players_bridge pgl_cards_bridge s)
  = s.
Proof. exact: gen_decode_encoded. Qed.

End pgl27_count_bridge.

(******************************************************************************)
(*     Both bridges at five_card_profile with bias 0: seats 4, shares 4,      *)
(*     cards 5                                                                *)
(******************************************************************************)

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section fivecard_count_bridge.

Variable R : realType.
Variable L : nat.

(** fc_lt0 — the bias 0 is below 5%:R^-1.
    @main bound: the first Kim positivity constraint at bias 0. *)
Lemma fc_lt0 : (0:R) < 5%:R^-1.
Proof. by rewrite invr_gt0 ltr0n. Qed.

(** fc_gt0 — the bias 0 is above - (4%:R * 5%:R^-1).
    @main bound: the second Kim positivity constraint at bias 0. *)
Lemma fc_gt0 : - (4%:R * 5%:R^-1) < (0:R).
Proof. by rewrite oppr_lt0 mulr_gt0 // ?ltr0n // invr_gt0 ltr0n. Qed.

(** fc_spec0 — the bias 0 satisfies the spectral-gap constraint.
    @main bound: `|0| < 4%:R / 5%:R. *)
Lemma fc_spec0 : `|(0:R)| < 4%:R / 5%:R.
Proof. by rewrite normr0 divr_gt0 // ltr0n. Qed.

Let mpD : MonodromyProfile R := @five_card_profile R 0 fc_lt0 fc_gt0 fc_spec0 L.

(** db_seat_count — the five-card interface has five seats.
    @main architecture: pi_T' (mp_PI mpD) = 4. *)
Lemma db_seat_count : pi_T' (mp_PI mpD) = 4.
Proof. by []. Qed.

(** db_share_count — the five-card plug's scheme has five shares.
    @main architecture: ts_T' (rp_scheme (mp_plug mpD)) = 4. *)
Lemma db_share_count : ts_T' (rp_scheme (mp_plug mpD)) = 4.
Proof. by []. Qed.

(** db_card_count — the five-card group acts on five cards.
    @main architecture: (pgg_N' (mp_M mpD)).+1 = 5. *)
Lemma db_card_count : (pgg_N' (mp_M mpD)).+1 = 5.
Proof. by []. Qed.

(** db_players_bridge — bridge 1 at five_card_profile with bias 0.
    @intent: pi_T' (mp_PI mpD) = ts_T' (rp_scheme (mp_plug mpD)), both sides
    reducing to 4. *)
Definition db_players_bridge
    : pi_T' (mp_PI mpD) = ts_T' (rp_scheme (mp_plug mpD)) := erefl.

(** db_cards_bridge — bridge 2 at five_card_profile with bias 0.
    @intent: (pgg_N' (mp_M mpD)).+1 = (ts_T' (rp_scheme (mp_plug mpD))).+1,
    both sides reducing to 5. *)
Definition db_cards_bridge
    : (pgg_N' (mp_M mpD)).+1 = (ts_T' (rp_scheme (mp_plug mpD))).+1 := erefl.

(** db_decode — the five-card endpoint decoder.
    @intent: gen_decode at mpD along db_players_bridge. *)
Definition db_decode (ep : seq 'I_(pgg_N' (mp_M mpD)).+1)
    (Hsz : size ep = (pi_T' (mp_PI mpD)).+1) : mp_secretT mpD :=
  @gen_decode R mpD db_players_bridge ep Hsz.

(** db_decodeE — the five-card endpoint decoder is the instance's own cast.
    @main architecture: db_decode agrees with
    ts_recon fcI_scheme (tcast _ (in_tuple ep)) for every endpoint list of the
    right length. *)
Lemma db_decodeE (ep : seq 'I_(pgg_N' (mp_M mpD)).+1)
    (Hsz : size ep = (pi_T' (mp_PI mpD)).+1)
    (Hsz' : size ep = (ts_T' fcI_scheme).+1) :
  db_decode Hsz = ts_recon fcI_scheme (tcast Hsz' (in_tuple ep)).
Proof.
rewrite /db_decode /gen_decode /run_recover.
by rewrite (eq_irrelevance
  (etrans Hsz (gen_seat_share_count db_players_bridge)) Hsz').
Qed.

(** db_decode_encoded — the five-card round trip.
    @main correctness: decoding the card-indexed shares of the one-bit secret
    returns that secret. *)
Lemma db_decode_encoded (s : bool) :
  db_decode (@gen_encoded_size R mpD db_players_bridge db_cards_bridge s) = s.
Proof. exact: gen_decode_encoded. Qed.

End fivecard_count_bridge.
