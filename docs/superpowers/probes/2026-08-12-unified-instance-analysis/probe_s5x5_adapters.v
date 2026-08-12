(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* probe_s5x5_adapters: the S_5 x S_5 sample adapters and the reader bridges  *)
(*                                                                            *)
(* Phase 0 probe for the unified-instance-analysis request, sections 6.5, 6.6 *)
(* and 8.2 to 8.6. Two sample layers sit over the two S_5 x S_5 execution     *)
(* plugs: the randomized product exact-secrecy adapter on s5x5_rand_plug at   *)
(* the product uniform iid tape distribution with the identity cut, and the   *)
(* finite-word endpoint adapter on s5x5_det_plug at a secret prior times the  *)
(* uniform eight-letter word distribution with the evaluated word as cut.     *)
(*                                                                            *)
(* Build order: probe_s5_rand_plug.v, probe_s5x5_det_plug.v and               *)
(* probe_s5x5_rand_plug.v first.                                             *)
(*                                                                            *)
(* Probe claims:                                                             *)
(*   s5x5_sample_content_traceE == the executed content reader at seat j is   *)
(*                                 s5x5_player_trace j                        *)
(*   s5x5_sample_trace_secrecy  == s5x5_trace_secrecy at the executed reader  *)
(*   s5x5_p1_viewE / s5x5_p2_viewE == the executed pile coalition readers are *)
(*                                 the two piles' rsh_view                    *)
(*   s5x5_joint_viewE           == the executed joint reader is the           *)
(*                                 leakage_product view                       *)
(*   s5x5_joint_secrecy         == s5x5_joint_view_secrecy at the executed    *)
(*                                 joint reader                               *)
(*   s5x5_word_cut_distE        == the word adapter's cut distribution is     *)
(*                                 rho_from_words L s5x5_gen_tuple            *)
(*   s5x5_word_pile1_floor      == the reverse-triangle lower bound to global *)
(*                                 uniform on ten seats                       *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals zmodp matrix.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
From infotheo Require Import variation_dist.
Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter pgg_collusion_bound.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_reconstruct Require Import product_threshold.
From pgg_smc Require Import pgg_leakage_witness pgg_randomized_sharing.
From pgg_smc Require Import pgg_canonical_sharing pgg_sharing_mechanism.
From pgg_smc Require Import pgg_leakage_product pgg_trace_secrecy.
From pgg_smc Require Import pgg_s5x5 s5x5_pile rigidity_s5x5_instance.
From pgg_smc Require Import s5x5_profile s5x5_run s5x5_trace s5x5_secrecy.
From pgg_smc Require Import s5_mixing s5x5_mixing.
From uia_probe Require Import probe_s5_rand_plug.
From uia_probe Require Import probe_s5x5_det_plug probe_s5x5_rand_plug.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory Order.POrderTheory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Section s5x5_sample_layers.

Let mpX : MonodromyProfile := s5x5_profile.

Variable R : realType.

(******************************************************************************)
(*     The randomized product exact-secrecy sample layer                      *)
(******************************************************************************)

(** s5x5_rand_sampleP — the product uniform iid sampler distribution over the
    two pile tapes.
    @intent: the s5x5_trace secrecy distribution respelled, that file keeping
    one factor as a section-local Let: the square of fdist_uniform
    (card_ZN_subproof 3) raised to the fifth power. *)
Definition s5x5_rand_sampleP : R.-fdist ('rV['Z_5]_5 * 'rV['Z_5]_5)%type :=
  ((fdist_uniform (pgg_canonical_sharing.card_ZN_subproof 3) `^ 5)
   `x (fdist_uniform (pgg_canonical_sharing.card_ZN_subproof 3) `^ 5))%fdist.

(** s5x5_rand_samplePE — the respelled product distribution is the trace
    file's product sampler.
    @composes: s5x5_sample_trace_secrecy *)
Lemma s5x5_rand_samplePE : s5x5_rand_sampleP = Pprod R.
Proof. by []. Qed.

(** s5x5_rand_sample — the S_5 x S_5 randomized exact-secrecy sample adapter.
    @intent: the sample layer over s5x5_rand_plug whose sample space is the
    product tape under s5x5_rand_sampleP, the run argument being the tape
    itself and the cut the identity. *)
Definition s5x5_rand_sample : SampleAdapter R s5x5_rand_plug :=
  @MkSampleAdapter R mpX s5x5_rand_plug
    [the finType of ('rV['Z_5]_5 * 'rV['Z_5]_5)%type]
    s5x5_rand_sampleP idfun (fun _ => 1%g).

(** s5x5_rand_sample_argE — the randomized adapter's run argument is the tape.
    @composes: s5x5_sample_content_traceE *)
Lemma s5x5_rand_sample_argE (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type) :
  s5x5_rand_sample.(sa_arg) uv = uv.
Proof. by []. Qed.

(** s5x5_rand_sample_cutE — the randomized adapter's cut is the identity.
    @composes: s5x5_sample_content_traceE, s5x5_p1_viewE *)
Lemma s5x5_rand_sample_cutE (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type) :
  s5x5_rand_sample.(sa_cut) uv = (1%g : pgg_gT s5x5_M).
Proof. by []. Qed.

(** s5x5_rand_cut_distE — the randomized adapter's cut distribution is the
    point distribution at the identity.
    @main architecture: sa_cut_dist s5x5_rand_sample = fdist1 1. *)
Lemma s5x5_rand_cut_distE :
  @sa_cut_dist R mpX s5x5_rand_plug s5x5_rand_sample
  = fdist1 (1%g : pgg_gT s5x5_M).
Proof.
rewrite /sa_cut_dist; apply/fdist_ext => g; rewrite fdistmapE fdist1E /=.
case: (eqVneq g (1%g : pgg_gT s5x5_M)) => [->|Hg].
- rewrite -[RHS](FDist.f1 s5x5_rand_sampleP); apply: eq_bigl => a.
  by rewrite inE /= eqxx.
- by rewrite big_pred0 // => a; rewrite inE /= eq_sym (negbTE Hg).
Qed.

(******************************************************************************)
(*     The finite content-trace reader on the randomized layer                *)
(******************************************************************************)

(** s5x5_sample_content_trace — seat j's executed trace content as a random
    variable on the product tape distribution.
    @intent: content_of applied to the plug's raw participant trace at the
    sample's argument and cut, a finite reader of a sequence-carried trace. *)
Definition s5x5_sample_content_trace (j : 'I_(pi_T' (mp_PI mpX)).+1)
    : {RV s5x5_rand_sampleP -> 'I_(pgg_N' (mp_M mpX)).+1} :=
  fun uv => content_of (@exec_participant_trace mpX s5x5_rand_plug
                          (s5x5_rand_sample.(sa_arg) uv)
                          (s5x5_rand_sample.(sa_cut) uv) 0 j).

(** s5x5_sample_content_traceE — the executed content reader is the landed
    player-trace random variable.
    @main architecture: s5x5_sample_content_trace j = s5x5_player_trace R j,
    the equality identifying the executed observer with the observer of
    s5x5_trace_secrecy. *)
Lemma s5x5_sample_content_traceE (j : 'I_(pi_T' (mp_PI mpX)).+1) :
  s5x5_sample_content_trace j = s5x5_player_trace R j.
Proof.
apply: boolp.funext => uv.
rewrite /s5x5_sample_content_trace /exec_participant_trace /exec_seat_id
        /exec_run s5x5_rand_fuelE s5x5_rand_sample_argE s5x5_rand_sample_cutE
        s5x5_rand_procsE (s5x5_rprocs_cut1 R uv).
by rewrite /s5x5_player_trace.
Qed.

(** s5x5_sample_trace_secrecy — a single corrupted seat's executed trace
    leaves the joint product secret's conditional entropy equal to its plain
    entropy.
    @main security: s5x5_trace_secrecy restated at the executed content reader
    of s5x5_rand_sample. *)
Theorem s5x5_sample_trace_secrecy (j : 'I_(pi_T' (mp_PI mpX)).+1) :
  `H( JointSecret R | s5x5_sample_content_trace j ) = `H `p_ (JointSecret R).
Proof. by rewrite s5x5_sample_content_traceE; exact: s5x5_trace_secrecy. Qed.

(******************************************************************************)
(*     The pile-restricted executed readers                                   *)
(******************************************************************************)

(** p1_idx_inj — the pile-1 seat embedding is injective.
    @composes: s5x5_p1_viewE *)
Lemma p1_idx_inj : injective p1_idx.
Proof.
by move=> a b H; apply: ord_inj; rewrite -(p1_idx_val a) -(p1_idx_val b) H.
Qed.

(** p2_idx_inj — the pile-2 seat embedding is injective.
    @composes: s5x5_p2_viewE *)
Lemma p2_idx_inj : injective p2_idx.
Proof.
move=> a b H.
have Hv : (5 + a)%N = (5 + b)%N by rewrite -(p2_idx_val a) -(p2_idx_val b) H.
by apply: ord_inj; exact: addnI Hv.
Qed.

(** s5x5_p1_seats — the ten-seat image of a pile-1 coalition.
    @intent: the seats of the first pile occupied by the coalition C1. *)
Definition s5x5_p1_seats (C1 : {set 'I_5})
    : {set 'I_(pi_T' (mp_PI mpX)).+1} := [set p1_idx j | j in C1].

(** s5x5_p2_seats — the ten-seat image of a pile-2 coalition.
    @intent: the seats of the second pile occupied by the coalition C2. *)
Definition s5x5_p2_seats (C2 : {set 'I_5})
    : {set 'I_(pi_T' (mp_PI mpX)).+1} := [set p2_idx j | j in C2].

(** s5x5_p1_seatsE — a pile-1 seat is in the image exactly when its party is
    in the coalition.
    @composes: s5x5_p1_viewE *)
Lemma s5x5_p1_seatsE (C1 : {set 'I_5}) (j : 'I_5) :
  (p1_idx j \in s5x5_p1_seats C1) = (j \in C1).
Proof.
apply/idP/idP; last by move=> Hj; apply/imsetP; exists j.
by case/imsetP => k Hk /p1_idx_inj ->.
Qed.

(** s5x5_p2_seatsE — a pile-2 seat is in the image exactly when its party is
    in the coalition.
    @composes: s5x5_p2_viewE *)
Lemma s5x5_p2_seatsE (C2 : {set 'I_5}) (j : 'I_5) :
  (p2_idx j \in s5x5_p2_seats C2) = (j \in C2).
Proof.
apply/idP/idP; last by move=> Hj; apply/imsetP; exists j.
by case/imsetP => k Hk /p2_idx_inj ->.
Qed.

(** proj_pile0 — the pile projection sends the default card to zero.
    @composes: s5x5_p1_viewE, s5x5_p2_viewE *)
Lemma proj_pile0 : proj_pile (ord0 : 'I_10) = 0%R.
Proof.
by apply: ord_inj; rewrite /proj_pile inordK.
Qed.

(** s5x5_p1_view — the executed pile-1 coalition reader.
    @intent: the pile shares read off the executed coalition endpoints at the
    pile-1 seats of C1, through the codec left inverse proj_pile. *)
Definition s5x5_p1_view (C1 : {set 'I_5})
    : {RV s5x5_rand_sampleP -> {ffun 'I_5 -> 'Z_5}} :=
  fun uv => [ffun j : 'I_5 =>
    proj_pile (@sa_coalition_view R mpX s5x5_rand_plug s5x5_rand_sample 0
                 (s5x5_p1_seats C1) uv (p1_idx j))].

(** s5x5_p2_view — the executed pile-2 coalition reader.
    @intent: the pile shares read off the executed coalition endpoints at the
    pile-2 seats of C2, through the codec left inverse proj_pile. *)
Definition s5x5_p2_view (C2 : {set 'I_5})
    : {RV s5x5_rand_sampleP -> {ffun 'I_5 -> 'Z_5}} :=
  fun uv => [ffun j : 'I_5 =>
    proj_pile (@sa_coalition_view R mpX s5x5_rand_plug s5x5_rand_sample 0
                 (s5x5_p2_seats C2) uv (p2_idx j))].

(** s5x5_p1_viewE — the executed pile-1 coalition reader is the first pile's
    randomized sharing view on the first tape.
    @main architecture: s5x5_p1_view C1 = fun uv => rsh_view rs1 C1 uv.1, the
    two readers sharing the finfun carrier {ffun 'I_5 -> 'Z_5} and the party
    indexing of the first pile. *)
Lemma s5x5_p1_viewE (C1 : {set 'I_5}) :
  s5x5_p1_view C1 = (fun uv => rsh_view (rs1 R) C1 uv.1).
Proof.
apply: boolp.funext => uv; apply/ffunP => j.
rewrite /s5x5_p1_view ffunE /sa_coalition_view.
rewrite (@exec_coalition_endpointsE mpX s5x5_rand_plug s5x5_rcontent_obs _ _ 0
  (s5x5_rand_endpoints _ _) (s5x5_p1_seats C1)).
rewrite ffunE /rsh_view ffunE s5x5_p1_seatsE.
case: ifP => Hin; last exact: proj_pile0.
rewrite /s5x5_rcontent_obs s5x5_rand_sample_cutE s5x5_rho1_index.
rewrite /s5x5_rfree_layout tnth_mktuple.
have Hlt : (p1_idx j < 5)%N by rewrite p1_idx_val; exact: ltn_ord.
case: (ltnP (p1_idx j) 5) => Hc; last by rewrite (leq_gtF Hc) in Hlt.
by rewrite cancel_p1 p1_idx_val inord_val /rs1 s5_rfree_shareE.
Qed.

(** s5x5_p2_viewE — the executed pile-2 coalition reader is the second pile's
    randomized sharing view on the second tape.
    @main architecture: s5x5_p2_view C2 = fun uv => rsh_view rs2 C2 uv.2. *)
Lemma s5x5_p2_viewE (C2 : {set 'I_5}) :
  s5x5_p2_view C2 = (fun uv => rsh_view (rs2 R) C2 uv.2).
Proof.
apply: boolp.funext => uv; apply/ffunP => j.
rewrite /s5x5_p2_view ffunE /sa_coalition_view.
rewrite (@exec_coalition_endpointsE mpX s5x5_rand_plug s5x5_rcontent_obs _ _ 0
  (s5x5_rand_endpoints _ _) (s5x5_p2_seats C2)).
rewrite ffunE /rsh_view ffunE s5x5_p2_seatsE.
case: ifP => Hin; last exact: proj_pile0.
rewrite /s5x5_rcontent_obs s5x5_rand_sample_cutE s5x5_rho1_index.
rewrite /s5x5_rfree_layout tnth_mktuple.
case: (ltnP (p2_idx j) 5) => Hc; first by rewrite (leq_gtF (p2_idx_ge j)) in Hc.
by rewrite cancel_p2 p2_idx_val addKn inord_val /rs2 s5_rfree_shareE.
Qed.

(** s5x5_p1_seat_view — the executed pile-1 seat reader.
    @intent: the pile share read off the executed seat endpoint of pile-1
    party j, through the codec left inverse proj_pile. *)
Definition s5x5_p1_seat_view (j : 'I_5) : {RV s5x5_rand_sampleP -> 'Z_5} :=
  fun uv => proj_pile (@sa_seat_view R mpX s5x5_rand_plug s5x5_rand_sample 0
                         (p1_idx j) uv).

(** s5x5_p2_seat_view — the executed pile-2 seat reader.
    @intent: the pile share read off the executed seat endpoint of pile-2
    party j, through the codec left inverse proj_pile. *)
Definition s5x5_p2_seat_view (j : 'I_5) : {RV s5x5_rand_sampleP -> 'Z_5} :=
  fun uv => proj_pile (@sa_seat_view R mpX s5x5_rand_plug s5x5_rand_sample 0
                         (p2_idx j) uv).

(** s5x5_p1_seat_viewE — the executed pile-1 seat reader is that party's
    first-pile share.
    @main architecture: s5x5_p1_seat_view j = fun uv => rsh_share rs1 j uv.1. *)
Lemma s5x5_p1_seat_viewE (j : 'I_5) :
  s5x5_p1_seat_view j = (fun uv => rsh_share (rs1 R) j uv.1).
Proof.
apply: boolp.funext => uv.
rewrite /s5x5_p1_seat_view /sa_seat_view.
rewrite (@exec_seat_endpointE mpX s5x5_rand_plug s5x5_rcontent_obs _ _ 0
  (s5x5_rand_endpoints _ _) (p1_idx j)).
rewrite /s5x5_rcontent_obs s5x5_rand_sample_cutE s5x5_rho1_index.
rewrite /s5x5_rfree_layout tnth_mktuple.
have Hlt : (p1_idx j < 5)%N by rewrite p1_idx_val; exact: ltn_ord.
case: (ltnP (p1_idx j) 5) => Hc; last by rewrite (leq_gtF Hc) in Hlt.
by rewrite cancel_p1 p1_idx_val inord_val /rs1 s5_rfree_shareE.
Qed.

(** s5x5_p2_seat_viewE — the executed pile-2 seat reader is that party's
    second-pile share.
    @main architecture: s5x5_p2_seat_view j = fun uv => rsh_share rs2 j uv.2. *)
Lemma s5x5_p2_seat_viewE (j : 'I_5) :
  s5x5_p2_seat_view j = (fun uv => rsh_share (rs2 R) j uv.2).
Proof.
apply: boolp.funext => uv.
rewrite /s5x5_p2_seat_view /sa_seat_view.
rewrite (@exec_seat_endpointE mpX s5x5_rand_plug s5x5_rcontent_obs _ _ 0
  (s5x5_rand_endpoints _ _) (p2_idx j)).
rewrite /s5x5_rcontent_obs s5x5_rand_sample_cutE s5x5_rho1_index.
rewrite /s5x5_rfree_layout tnth_mktuple.
case: (ltnP (p2_idx j) 5) => Hc; first by rewrite (leq_gtF (p2_idx_ge j)) in Hc.
by rewrite cancel_p2 p2_idx_val addKn inord_val /rs2 s5_rfree_shareE.
Qed.

(******************************************************************************)
(*     Executed per-pile and joint secrecy                                    *)
(******************************************************************************)

(** s5x5_p1_view_indep — a sub-threshold pile-1 coalition view is independent
    of the joint product secret.
    @composes: s5x5_p1_secrecy *)
Lemma s5x5_p1_view_indep (C1 : {set 'I_5}) (HC1 : (#|C1| < 5)%N) :
  Pprod R |= (fun uv => rsh_view (rs1 R) C1 uv.1) _|_ JointSecret R.
Proof.
have HC0 : (#|[set (ord0 : 'I_5)]| < 5)%N by rewrite cards1.
pose lw := leakage_product (additive_leakage (rs1 R) HC1)
                           (additive_leakage (rs2 R) HC0).
have Hview : (fun uv => rsh_view (rs1 R) C1 uv.1)
           = (fun vv : lw_viewT lw => vv.1) `o lw_view lw by [].
have Hsec : JointSecret R = lw_secret lw by [].
rewrite Hview Hsec.
apply: inde_RV_comp; exact: lw_indep lw.
Qed.

(** s5x5_p2_view_indep — a sub-threshold pile-2 coalition view is independent
    of the joint product secret.
    @composes: s5x5_p2_secrecy *)
Lemma s5x5_p2_view_indep (C2 : {set 'I_5}) (HC2 : (#|C2| < 5)%N) :
  Pprod R |= (fun uv => rsh_view (rs2 R) C2 uv.2) _|_ JointSecret R.
Proof.
have HC0 : (#|[set (ord0 : 'I_5)]| < 5)%N by rewrite cards1.
pose lw := leakage_product (additive_leakage (rs1 R) HC0)
                           (additive_leakage (rs2 R) HC2).
have Hview : (fun uv => rsh_view (rs2 R) C2 uv.2)
           = (fun vv : lw_viewT lw => vv.2) `o lw_view lw by [].
have Hsec : JointSecret R = lw_secret lw by [].
rewrite Hview Hsec.
apply: inde_RV_comp; exact: lw_indep lw.
Qed.

(** s5x5_p1_secrecy — a sub-threshold pile-1 coalition's executed endpoint
    readings leave the joint product secret's entropy unchanged.
    @main security: zero mutual information and unchanged conditional entropy
    for the executed pile-1 coalition reader against the joint secret. *)
Theorem s5x5_p1_secrecy (C1 : {set 'I_5}) (HC1 : (#|C1| < 5)%N) :
  `I( JointSecret R ; s5x5_p1_view C1 ) = 0%R /\
  `H( JointSecret R | s5x5_p1_view C1 ) = `H `p_ (JointSecret R).
Proof.
rewrite s5x5_p1_viewE; apply: leakage_of_view_indep.
exact: s5x5_p1_view_indep HC1.
Qed.

(** s5x5_p2_secrecy — a sub-threshold pile-2 coalition's executed endpoint
    readings leave the joint product secret's entropy unchanged.
    @main security: zero mutual information and unchanged conditional entropy
    for the executed pile-2 coalition reader against the joint secret. *)
Theorem s5x5_p2_secrecy (C2 : {set 'I_5}) (HC2 : (#|C2| < 5)%N) :
  `I( JointSecret R ; s5x5_p2_view C2 ) = 0%R /\
  `H( JointSecret R | s5x5_p2_view C2 ) = `H `p_ (JointSecret R).
Proof.
rewrite s5x5_p2_viewE; apply: leakage_of_view_indep.
exact: s5x5_p2_view_indep HC2.
Qed.

(** s5x5_joint_view — the executed joint coalition reader.
    @intent: the pair of the two executed pile coalition readers, keeping the
    two pile memberships separate. *)
Definition s5x5_joint_view (C1 C2 : {set 'I_5})
    : {RV s5x5_rand_sampleP
       -> ({ffun 'I_5 -> 'Z_5} * {ffun 'I_5 -> 'Z_5})%type} :=
  fun uv => (s5x5_p1_view C1 uv, s5x5_p2_view C2 uv).

(** s5x5_joint_viewE — the executed joint reader is the product leakage
    witness's view.
    @main architecture: s5x5_joint_view C1 C2 = lw_view (leakage_product ...),
    the reader of s5x5_joint_view_secrecy. *)
Lemma s5x5_joint_viewE (C1 C2 : {set 'I_5})
    (HC1 : (#|C1| < 5)%N) (HC2 : (#|C2| < 5)%N) :
  s5x5_joint_view C1 C2
  = lw_view (leakage_product
               (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC1))
               (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC2))).
Proof. by rewrite /s5x5_joint_view s5x5_p1_viewE s5x5_p2_viewE. Qed.

(** s5x5_joint_secrecy — two sub-threshold pile coalitions' executed endpoint
    readings leave the joint product secret's entropy unchanged.
    @main security: s5x5_joint_view_secrecy restated at the executed joint
    coalition reader of s5x5_rand_sample. *)
Theorem s5x5_joint_secrecy (C1 C2 : {set 'I_5})
    (HC1 : (#|C1| < 5)%N) (HC2 : (#|C2| < 5)%N) :
  `I( JointSecret R ; s5x5_joint_view C1 C2 ) = 0%R /\
  `H( JointSecret R | s5x5_joint_view C1 C2 ) = `H `p_ (JointSecret R).
Proof.
rewrite (s5x5_joint_viewE HC1 HC2).
exact: (@s5x5_joint_view_secrecy R C1 C2 HC1 HC2).
Qed.

(******************************************************************************)
(*     The finite-word endpoint sample layer on the deterministic plug        *)
(******************************************************************************)

(* The secret prior of the word sample space, arbitrary where the randomized
   sample space fixes the product uniform iid tape. *)
Variable secretP : R.-fdist 'I_10.
Variable L : nat.

(** s5x5_word_sampleT — the finite-word sample space.
    @intent: pairs of a dealt position and an L-letter word over the eight
    pile-local generators. *)
Definition s5x5_word_sampleT : finType :=
  [the finType of ('I_10 * L.-tuple 'I_8)%type].

(** s5x5_word_sampleP — the finite-word sample distribution.
    @intent: the product of the secret prior with the uniform word
    distribution word_uniform 7 L, the distribution rho_from_words is the
    image of. *)
Definition s5x5_word_sampleP : R.-fdist s5x5_word_sampleT :=
  (secretP `x (@word_uniform R 7 L))%fdist.

(** s5x5_word_cut — the finite-word cut map.
    @intent: the evaluation in S_5 x S_5 of the sampled generator word. *)
Definition s5x5_word_cut (u : s5x5_word_sampleT) : pgg_gT (mp_M mpX) :=
  @word_eval s5x5_M L u.2.

(** s5x5_word_sample — the S_5 x S_5 finite-word endpoint sample adapter.
    @intent: the sample layer over s5x5_det_plug whose sample space is
    s5x5_word_sampleT under s5x5_word_sampleP, the run argument being the
    dealt position and the cut the evaluated word. *)
Definition s5x5_word_sample : SampleAdapter R s5x5_det_plug :=
  @MkSampleAdapter R mpX s5x5_det_plug s5x5_word_sampleT s5x5_word_sampleP
    fst s5x5_word_cut.

(** s5x5_word_snd — the word marginal of the finite-word sample distribution
    is the uniform word distribution.
    @composes: s5x5_word_cut_distE *)
Lemma s5x5_word_snd : fdist_snd s5x5_word_sampleP = @word_uniform R 7 L.
Proof. by rewrite /s5x5_word_sampleP -fdistX_prod fdistX2 fdist_prod1. Qed.

(** s5x5_word_cut_distE — the finite-word adapter's cut distribution is the
    word-induced shuffle distribution the spectral theorems bound.
    @main architecture: sa_cut_dist s5x5_word_sample = rho_from_words L
    s5x5_gen_tuple. *)
Lemma s5x5_word_cut_distE :
  @sa_cut_dist R mpX s5x5_det_plug s5x5_word_sample
  = @rho_from_words R 8 7 L s5x5_gen_tuple.
Proof.
rewrite /sa_cut_dist /rho_from_words -s5x5_word_snd /fdist_snd fdistmap_comp.
by [].
Qed.

(** s5x5_word_pile1_bound — the landed pile-1 spectral bound holds at the
    finite-word adapter's own cut distribution.
    @main bound: the variation distance between the pile-1 position
    pushforward of sa_cut_dist s5x5_word_sample and the pile-1 uniform
    distribution is at most sqrt 5 times the lazy spectral ratio to the power
    L; conditional on s5_rayleigh_Q2_R. *)
Lemma s5x5_word_pile1_bound (s : 'I_5) :
  (var_dist (fdistmap (fun sigma : {perm 'I_10} => sigma (widen5to10 s))
               (@sa_cut_dist R mpX s5x5_det_plug s5x5_word_sample))
            (fdist_uniform_pile1 R)
   <= Num.sqrt 5%:R * (s5_lazy_alpha_R R) ^+ L)%R.
Proof. by rewrite s5x5_word_cut_distE; exact: s5x5_pile1_TV_bound. Qed.

(** s5x5_word_pile2_bound — the landed pile-2 spectral bound holds at the
    finite-word adapter's own cut distribution.
    @main bound: the variation distance between the pile-2 position
    pushforward of sa_cut_dist s5x5_word_sample and the pile-2 uniform
    distribution is at most sqrt 5 times the lazy spectral ratio to the power
    L; conditional on s5_rayleigh_Q2_R. *)
Lemma s5x5_word_pile2_bound (s : 'I_5) :
  (var_dist (fdistmap (fun sigma : {perm 'I_10} => sigma (rshift5to10 s))
               (@sa_cut_dist R mpX s5x5_det_plug s5x5_word_sample))
            (fdist_uniform_pile2 R)
   <= Num.sqrt 5%:R * (s5_lazy_alpha_R R) ^+ L)%R.
Proof. by rewrite s5x5_word_cut_distE; exact: s5x5_pile2_TV_bound. Qed.

(** s5x5_word_seat_bound — the landed one-seat spectral bound holds at the
    finite-word adapter's own cut distribution.
    @main bound: the variation distance between any seat's position
    pushforward of sa_cut_dist s5x5_word_sample and the uniform distribution
    on ten seats is at most 1 + sqrt 5 times the lazy spectral ratio to the
    power L; conditional on s5_rayleigh_Q2_R. This is a one-seat statement and
    its bound does not vanish. *)
Lemma s5x5_word_seat_bound (s : 'I_10) :
  (var_dist (fdistmap (fun sigma : {perm 'I_10} => sigma s)
               (@sa_cut_dist R mpX s5x5_det_plug s5x5_word_sample))
            (fdist_uniform (card_ord 10))
   <= 1 + Num.sqrt 5%:R * (s5_lazy_alpha_R R) ^+ L)%R.
Proof. by rewrite s5x5_word_cut_distE; exact: s5x5_spectral_TV_bound. Qed.

(******************************************************************************)
(*     The negative-transfer floors to global uniform                         *)
(******************************************************************************)

(** s5x5_word_pile1_floor — the reverse-triangle lower bound between the
    pile-1 endpoint distribution and global uniform on ten seats.
    @main bound: 1 - sqrt 5 * lazy ^+ L is a lower bound on the variation
    distance between the pile-1 position pushforward of the word-induced cut
    distribution and the uniform distribution on ten seats; conditional on
    s5_rayleigh_Q2_R. The bound is positive exactly when
    sqrt 5 * lazy ^+ L < 1. *)
Lemma s5x5_word_pile1_floor (s : 'I_5) :
  (1 - Num.sqrt 5%:R * (s5_lazy_alpha_R R) ^+ L
   <= var_dist (fdistmap (fun sigma : {perm 'I_10} => sigma (widen5to10 s))
                  (@sa_cut_dist R mpX s5x5_det_plug s5x5_word_sample))
               (fdist_uniform (card_ord 10)))%R.
Proof.
set A := fdistmap _ _.
have H1 := var_dist_triangle (fdist_uniform_pile1 R) A (fdist_uniform (card_ord 10)).
rewrite var_dist_uniform_pile1_uniform10 in H1.
have H2 : (var_dist (fdist_uniform_pile1 R) A
           <= Num.sqrt 5%:R * (s5_lazy_alpha_R R) ^+ L)%R.
  by rewrite symmetric_var_dist; exact: s5x5_word_pile1_bound.
have H3 : (1 <= Num.sqrt 5%:R * (s5_lazy_alpha_R R) ^+ L
                + var_dist A (fdist_uniform (card_ord 10)))%R.
  by apply: (le_trans H1); rewrite lerD2r; exact: H2.
have H4 : (1 <= var_dist A (fdist_uniform (card_ord 10))
                + Num.sqrt 5%:R * (s5_lazy_alpha_R R) ^+ L)%R
  by rewrite addrC.
by rewrite lerBlDl.
Qed.

(** s5x5_word_pile2_floor — the reverse-triangle lower bound between the
    pile-2 endpoint distribution and global uniform on ten seats.
    @main bound: 1 - sqrt 5 * lazy ^+ L is a lower bound on the variation
    distance between the pile-2 position pushforward of the word-induced cut
    distribution and the uniform distribution on ten seats; conditional on
    s5_rayleigh_Q2_R. *)
Lemma s5x5_word_pile2_floor (s : 'I_5) :
  (1 - Num.sqrt 5%:R * (s5_lazy_alpha_R R) ^+ L
   <= var_dist (fdistmap (fun sigma : {perm 'I_10} => sigma (rshift5to10 s))
                  (@sa_cut_dist R mpX s5x5_det_plug s5x5_word_sample))
               (fdist_uniform (card_ord 10)))%R.
Proof.
set A := fdistmap _ _.
have H1 := var_dist_triangle (fdist_uniform_pile2 R) A (fdist_uniform (card_ord 10)).
rewrite var_dist_uniform_pile2_uniform10 in H1.
have H2 : (var_dist (fdist_uniform_pile2 R) A
           <= Num.sqrt 5%:R * (s5_lazy_alpha_R R) ^+ L)%R.
  by rewrite symmetric_var_dist; exact: s5x5_word_pile2_bound.
have H3 : (1 <= Num.sqrt 5%:R * (s5_lazy_alpha_R R) ^+ L
                + var_dist A (fdist_uniform (card_ord 10)))%R.
  by apply: (le_trans H1); rewrite lerD2r; exact: H2.
have H4 : (1 <= var_dist A (fdist_uniform (card_ord 10))
                + Num.sqrt 5%:R * (s5_lazy_alpha_R R) ^+ L)%R
  by rewrite addrC.
by rewrite lerBlDl.
Qed.

(* Phase 2 numeric corollary, not required here. Its exact form is
     Lemma s5x5_word_pile1_floor_pos (s : 'I_5) :
       (17 <= L)%N ->
       (0 < var_dist (fdistmap (fun sigma : {perm 'I_10} => sigma (widen5to10 s))
                        (sa_cut_dist s5x5_word_sample))
                     (fdist_uniform (card_ord 10)))%R,
   obtained from s5x5_word_pile1_floor and a numeric bound
   Num.sqrt 5%:R * s5_lazy_alpha_R R ^+ L < 1 at L >= 17. *)

(******************************************************************************)
(*     The generic transfer theorem at the cut carrier                        *)
(******************************************************************************)

(** s5x5_word_base_premise — the base-distribution premise of the generic
    transfer theorem at the cut carrier.
    @intent: a variation-distance bound between the finite-word adapter's cut
    distribution on {perm 'I_10} and a reference distribution on the same
    carrier. The landed spectral theorems bound pushforwards along position
    readers, on the carrier 'I_10, and therefore do not instantiate this
    proposition. *)
Definition s5x5_word_base_premise (Q : R.-fdist {perm 'I_10}) (delta : R)
    : Prop :=
  (var_dist (@sa_cut_dist R mpX s5x5_det_plug s5x5_word_sample) Q <= delta)%R.

(** s5x5_word_transfer_conditional — the generic transfer theorem applies to
    any pair of cut readers once the base-distribution premise is supplied.
    @main bound: two readers of the finite-word cut distribution whose
    pushforwards along Q agree have pushforwards within delta + delta,
    provided s5x5_word_base_premise Q delta. *)
Lemma s5x5_word_transfer_conditional
    (Q : R.-fdist {perm 'I_10}) (delta : R) (B : finType)
    (fx fy : {perm 'I_10} -> B) :
  s5x5_word_base_premise Q delta ->
  fdistmap fx Q = fdistmap fy Q ->
  (var_dist (fdistmap fx (@sa_cut_dist R mpX s5x5_det_plug s5x5_word_sample))
            (fdistmap fy (@sa_cut_dist R mpX s5x5_det_plug s5x5_word_sample))
   <= delta + delta)%R.
Proof.
move=> H1 H2.
exact: (var_dist_fdistmap_transfer R _ _ _ _ _ _ _ H1 H2).
Qed.

(* The pile spectral theorems live at the carrier 'I_10, the premise at the
   carrier {perm 'I_10}; the guard below records that the two do not unify, so
   no cast turns an endpoint pushforward bound into a base-distribution
   bound. *)
Fail Check (fun s : 'I_5 =>
  (@s5x5_pile1_TV_bound R L s
     : s5x5_word_base_premise (fdist_uniform_pile1 R)
         (Num.sqrt 5%:R * s5_lazy_alpha_R R ^+ L)%R)).

End s5x5_sample_layers.

Print Assumptions s5x5_sample_content_traceE.
Print Assumptions s5x5_sample_trace_secrecy.
Print Assumptions s5x5_p1_viewE.
Print Assumptions s5x5_p2_viewE.
Print Assumptions s5x5_p1_secrecy.
Print Assumptions s5x5_p2_secrecy.
Print Assumptions s5x5_joint_viewE.
Print Assumptions s5x5_joint_secrecy.
Print Assumptions s5x5_p1_seat_viewE.
Print Assumptions s5x5_word_cut_distE.
Print Assumptions s5x5_word_pile1_bound.
Print Assumptions s5x5_word_pile2_bound.
Print Assumptions s5x5_word_seat_bound.
Print Assumptions s5x5_word_pile1_floor.
Print Assumptions s5x5_word_pile2_floor.
Print Assumptions s5x5_word_transfer_conditional.
Print Assumptions s5x5_rand_cut_distE.
