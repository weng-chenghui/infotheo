(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* s5x5_models: the S_5 x S_5 sample layers and their executed bridges        *)
(*                                                                            *)
(* Two sample layers sit over the two S_5 x S_5 execution plugs. The          *)
(* randomized product exact-secrecy layer sits over s5x5_rand_exec_plug at    *)
(* the product uniform iid tape distribution with the identity cut, which is  *)
(* the cut the landed executed results are stated at. The finite-word         *)
(* endpoint layer sits over s5x5_exec_plug at a secret prior times the        *)
(* uniform eight-letter word distribution, with the evaluated generator word  *)
(* as cut.                                                                    *)
(*                                                                            *)
(* The two sample spaces are different by definition: the first is the pair   *)
(* of randomized-sharing tapes 'rV['Z_5]_5 * 'rV['Z_5]_5 and the second is a  *)
(* pair of a dealt position and an L-letter word. The finite-word layer is    *)
(* not a finite approximation of the randomized layer, no theorem here        *)
(* relating the two base distributions.                                       *)
(*                                                                            *)
(* Every executed reader below keeps the pile structure in its type. The two  *)
(* pile coalitions are sets of five-element party indices {set 'I_5} embedded *)
(* into the ten seats by s5x5_p1_idx and s5x5_p2_idx, the pile readers have   *)
(* the pile carrier {ffun 'I_5 -> 'Z_5} and 'Z_5, and the joint reader is     *)
(* their pair. No statement flattens the two piles into one ten-seat          *)
(* coalition.                                                                 *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   s5x5_rand_sampleP        == the product uniform iid tape distribution    *)
(*   s5x5_rand_sample         == the randomized product exact-secrecy sample  *)
(*                               adapter                                      *)
(*   s5x5_sample_content_trace == seat j's executed trace content as a random *)
(*                               variable on the product tape distribution    *)
(*   s5x5_p1_seats, s5x5_p2_seats == the ten-seat images of a pile-1 and a    *)
(*                               pile-2 coalition                             *)
(*   s5x5_p1_seat_view, s5x5_p2_seat_view == the executed pile share of one   *)
(*                               pile party, carrier 'Z_5                     *)
(*   s5x5_p1_view, s5x5_p2_view == the executed pile shares of a pile         *)
(*                               coalition, carrier {ffun 'I_5 -> 'Z_5}       *)
(*   s5x5_joint_view          == the pair of the two executed pile coalition  *)
(*                               readers                                      *)
(*   s5x5_word_sampleT        == the finite-word sample space                 *)
(*   s5x5_word_sampleP        == the secret prior times the uniform word      *)
(*                               distribution                                 *)
(*   s5x5_word_cut            == the evaluation in S_5 x S_5 of the sampled   *)
(*                               generator word                               *)
(*   s5x5_word_sample         == the finite-word endpoint sample adapter      *)
(*   s5x5_word_base_premise   == the base-distribution premise of the generic *)
(*                               transfer theorem at the carrier {perm 'I_10} *)
(*                                                                            *)
(* Key results:                                                               *)
(*   s5x5_rand_cut_distE      == the randomized adapter's cut distribution is *)
(*                               the point distribution at the identity       *)
(*   s5x5_sample_content_traceE == the executed content reader at seat j is   *)
(*                               s5x5_player_trace j                          *)
(*   s5x5_exec_trace_secrecy  == the conditional entropy of the joint product *)
(*                               secret given one seat's executed trace       *)
(*                               content is its entropy                       *)
(*   s5x5_p1_viewE, s5x5_p2_viewE == the executed pile coalition readers are  *)
(*                               the two piles' randomized sharing views      *)
(*   s5x5_p1_seat_viewE, s5x5_p2_seat_viewE == the executed pile seat readers *)
(*                               are the two piles' shares                    *)
(*   s5x5_exec_p1_secrecy, s5x5_exec_p2_secrecy == a sub-threshold pile       *)
(*                               coalition's executed readings have zero      *)
(*                               mutual information with the joint product    *)
(*                               secret                                       *)
(*   s5x5_joint_viewE         == the executed joint reader is the product     *)
(*                               leakage witness's view                       *)
(*   s5x5_exec_joint_secrecy  == two sub-threshold pile coalitions' executed  *)
(*                               readings leave the joint product secret's    *)
(*                               entropy unchanged                            *)
(*   s5x5_word_cut_distE      == the word adapter's cut distribution is       *)
(*                               rho_from_words L s5x5_gen_tuple              *)
(*   s5x5_word_pile1_bound, s5x5_word_pile2_bound == the per-pile endpoint    *)
(*                               marginal bounds at that cut distribution     *)
(*   s5x5_word_seat_bound     == the one-seat endpoint marginal bound to      *)
(*                               global uniform on ten seats                  *)
(*   s5x5_lazy_bound_lt1      == the lazy mixing factor sqrt 5 times the L-th *)
(*                               power is below one from word length          *)
(*                               seventeen on                                 *)
(*   s5x5_word_pile1_floor, s5x5_word_pile2_floor == the reverse-triangle     *)
(*                               lower bounds from each pile endpoint         *)
(*                               distribution to global uniform on ten seats  *)
(*   s5x5_word_pile1_floor_gt0, s5x5_word_pile2_floor_gt0 == those lower      *)
(*                               bounds are positive from word length         *)
(*                               seventeen on                                 *)
(*   s5x5_word_transfer_conditional == the generic transfer inequality at the *)
(*                               cut carrier, under the base-distribution     *)
(*                               premise the repository does not supply       *)
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
From pgg_smc Require Import s5_exec s5x5_exec pgg_analysis_status.

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
    @composes: s5x5_exec_trace_secrecy *)
Lemma s5x5_rand_samplePE : s5x5_rand_sampleP = Pprod R.
Proof. by []. Qed.

(** s5x5_rand_sample — the S_5 x S_5 randomized exact-secrecy sample adapter.
    @intent: the sample layer over s5x5_rand_exec_plug whose sample space is
    the product tape under s5x5_rand_sampleP, the run argument being the tape
    itself and the cut the identity, the cut the landed executed results are
    stated at. *)
Definition s5x5_rand_sample : SampleAdapter R s5x5_rand_exec_plug :=
  @MkSampleAdapter R mpX s5x5_rand_exec_plug
    [the finType of ('rV['Z_5]_5 * 'rV['Z_5]_5)%type]
    s5x5_rand_sampleP idfun (fun _ => 1%g).

(** s5x5_rand_sample_argE — the randomized adapter's run argument is the
    product tape.
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
  @sa_cut_dist R mpX s5x5_rand_exec_plug s5x5_rand_sample
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
    @intent: s5x5_trace.content_of applied to the plug's raw participant trace
    at the sample's argument and cut, a finite reader of a sequence-carried
    trace. *)
Definition s5x5_sample_content_trace (j : 'I_(pi_T' (mp_PI mpX)).+1)
    : {RV s5x5_rand_sampleP -> 'I_(pgg_N' (mp_M mpX)).+1} :=
  fun uv => s5x5_trace.content_of
              (@exec_participant_trace mpX s5x5_rand_exec_plug
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

(** s5x5_exec_trace_secrecy — a single corrupted seat's executed trace leaves
    the joint product secret's conditional entropy equal to its plain entropy.
    @main security: trace secrecy in conditional-entropy form, at the executed
    content reader of s5x5_rand_sample: `H( JointSecret R |
    s5x5_sample_content_trace j ) = `H `p_ (JointSecret R), for every seat
    j. *)
Theorem s5x5_exec_trace_secrecy (j : 'I_(pi_T' (mp_PI mpX)).+1) :
  `H( JointSecret R | s5x5_sample_content_trace j ) = `H `p_ (JointSecret R).
Proof. by rewrite s5x5_sample_content_traceE; exact: s5x5_trace_secrecy. Qed.

(******************************************************************************)
(*     The pile-restricted executed readers                                   *)
(******************************************************************************)

(** s5x5_p1_idx_inj — the pile-1 seat embedding is injective.
    @composes: s5x5_p1_viewE *)
Lemma s5x5_p1_idx_inj : injective s5x5_p1_idx.
Proof.
move=> a b H; apply: ord_inj.
by rewrite -(s5x5_p1_idx_val a) -(s5x5_p1_idx_val b) H.
Qed.

(** s5x5_p2_idx_inj — the pile-2 seat embedding is injective.
    @composes: s5x5_p2_viewE *)
Lemma s5x5_p2_idx_inj : injective s5x5_p2_idx.
Proof.
move=> a b H.
have Hv : (5 + a)%N = (5 + b)%N
  by rewrite -(s5x5_p2_idx_val a) -(s5x5_p2_idx_val b) H.
by apply: ord_inj; exact: addnI Hv.
Qed.

(** s5x5_p1_seats — the ten-seat image of a pile-1 coalition.
    @intent: the seats of the first pile occupied by the coalition C1. *)
Definition s5x5_p1_seats (C1 : {set 'I_5})
    : {set 'I_(pi_T' (mp_PI mpX)).+1} := [set s5x5_p1_idx j | j in C1].

(** s5x5_p2_seats — the ten-seat image of a pile-2 coalition.
    @intent: the seats of the second pile occupied by the coalition C2. *)
Definition s5x5_p2_seats (C2 : {set 'I_5})
    : {set 'I_(pi_T' (mp_PI mpX)).+1} := [set s5x5_p2_idx j | j in C2].

(** s5x5_p1_seatsE — a pile-1 seat is in the image exactly when its party is
    in the coalition.
    @composes: s5x5_p1_viewE *)
Lemma s5x5_p1_seatsE (C1 : {set 'I_5}) (j : 'I_5) :
  (s5x5_p1_idx j \in s5x5_p1_seats C1) = (j \in C1).
Proof.
apply/idP/idP; last by move=> Hj; apply/imsetP; exists j.
by case/imsetP => k Hk /s5x5_p1_idx_inj ->.
Qed.

(** s5x5_p2_seatsE — a pile-2 seat is in the image exactly when its party is
    in the coalition.
    @composes: s5x5_p2_viewE *)
Lemma s5x5_p2_seatsE (C2 : {set 'I_5}) (j : 'I_5) :
  (s5x5_p2_idx j \in s5x5_p2_seats C2) = (j \in C2).
Proof.
apply/idP/idP; last by move=> Hj; apply/imsetP; exists j.
by case/imsetP => k Hk /s5x5_p2_idx_inj ->.
Qed.

(** s5x5_proj_pile0 — the pile projection sends the default card to zero.
    @composes: s5x5_p1_viewE, s5x5_p2_viewE *)
Lemma s5x5_proj_pile0 : proj_pile (ord0 : 'I_10) = 0%R.
Proof. by apply: ord_inj; rewrite /proj_pile inordK. Qed.

(** s5x5_p1_view — the executed pile-1 coalition reader.
    @intent: the pile shares read off the executed coalition endpoints at the
    pile-1 seats of C1, through the codec left inverse proj_pile. *)
Definition s5x5_p1_view (C1 : {set 'I_5})
    : {RV s5x5_rand_sampleP -> {ffun 'I_5 -> 'Z_5}} :=
  fun uv => [ffun j : 'I_5 =>
    proj_pile (@sa_coalition_view R mpX s5x5_rand_exec_plug s5x5_rand_sample 0
                 (s5x5_p1_seats C1) uv (s5x5_p1_idx j))].

(** s5x5_p2_view — the executed pile-2 coalition reader.
    @intent: the pile shares read off the executed coalition endpoints at the
    pile-2 seats of C2, through the codec left inverse proj_pile. *)
Definition s5x5_p2_view (C2 : {set 'I_5})
    : {RV s5x5_rand_sampleP -> {ffun 'I_5 -> 'Z_5}} :=
  fun uv => [ffun j : 'I_5 =>
    proj_pile (@sa_coalition_view R mpX s5x5_rand_exec_plug s5x5_rand_sample 0
                 (s5x5_p2_seats C2) uv (s5x5_p2_idx j))].

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
rewrite (@exec_coalition_endpointsE mpX s5x5_rand_exec_plug s5x5_rcontent_obs
  _ _ 0 (s5x5_rand_endpoints _ _) (s5x5_p1_seats C1)).
rewrite ffunE /rsh_view ffunE s5x5_p1_seatsE.
case: ifP => Hin; last exact: s5x5_proj_pile0.
rewrite /s5x5_rcontent_obs s5x5_rand_sample_cutE s5x5_rho1_index.
rewrite /s5x5_rfree_layout tnth_mktuple.
have Hlt : (s5x5_p1_idx j < 5)%N by rewrite s5x5_p1_idx_val; exact: ltn_ord.
case: (ltnP (s5x5_p1_idx j) 5) => Hc; last by rewrite (leq_gtF Hc) in Hlt.
by rewrite cancel_p1 s5x5_p1_idx_val inord_val /rs1 s5_rfree_shareE.
Qed.

(** s5x5_p2_viewE — the executed pile-2 coalition reader is the second pile's
    randomized sharing view on the second tape.
    @main architecture: s5x5_p2_view C2 = fun uv => rsh_view rs2 C2 uv.2, the
    two readers sharing the finfun carrier {ffun 'I_5 -> 'Z_5} and the party
    indexing of the second pile. *)
Lemma s5x5_p2_viewE (C2 : {set 'I_5}) :
  s5x5_p2_view C2 = (fun uv => rsh_view (rs2 R) C2 uv.2).
Proof.
apply: boolp.funext => uv; apply/ffunP => j.
rewrite /s5x5_p2_view ffunE /sa_coalition_view.
rewrite (@exec_coalition_endpointsE mpX s5x5_rand_exec_plug s5x5_rcontent_obs
  _ _ 0 (s5x5_rand_endpoints _ _) (s5x5_p2_seats C2)).
rewrite ffunE /rsh_view ffunE s5x5_p2_seatsE.
case: ifP => Hin; last exact: s5x5_proj_pile0.
rewrite /s5x5_rcontent_obs s5x5_rand_sample_cutE s5x5_rho1_index.
rewrite /s5x5_rfree_layout tnth_mktuple.
case: (ltnP (s5x5_p2_idx j) 5) => Hc;
  first by rewrite (leq_gtF (s5x5_p2_idx_ge j)) in Hc.
by rewrite cancel_p2 s5x5_p2_idx_val addKn inord_val /rs2 s5_rfree_shareE.
Qed.

(** s5x5_p1_seat_view — the executed pile-1 seat reader.
    @intent: the pile share read off the executed seat endpoint of pile-1
    party j, through the codec left inverse proj_pile. *)
Definition s5x5_p1_seat_view (j : 'I_5) : {RV s5x5_rand_sampleP -> 'Z_5} :=
  fun uv => proj_pile (@sa_seat_view R mpX s5x5_rand_exec_plug
                         s5x5_rand_sample 0 (s5x5_p1_idx j) uv).

(** s5x5_p2_seat_view — the executed pile-2 seat reader.
    @intent: the pile share read off the executed seat endpoint of pile-2
    party j, through the codec left inverse proj_pile. *)
Definition s5x5_p2_seat_view (j : 'I_5) : {RV s5x5_rand_sampleP -> 'Z_5} :=
  fun uv => proj_pile (@sa_seat_view R mpX s5x5_rand_exec_plug
                         s5x5_rand_sample 0 (s5x5_p2_idx j) uv).

(** s5x5_p1_seat_viewE — the executed pile-1 seat reader is that party's
    first-pile share.
    @main architecture: s5x5_p1_seat_view j = fun uv => rsh_share rs1 j uv.1,
    a reader with the pile carrier 'Z_5 and the party indexing of the first
    pile. *)
Lemma s5x5_p1_seat_viewE (j : 'I_5) :
  s5x5_p1_seat_view j = (fun uv => rsh_share (rs1 R) j uv.1).
Proof.
apply: boolp.funext => uv.
rewrite /s5x5_p1_seat_view /sa_seat_view.
rewrite (@exec_seat_endpointE mpX s5x5_rand_exec_plug s5x5_rcontent_obs _ _ 0
  (s5x5_rand_endpoints _ _) (s5x5_p1_idx j)).
rewrite /s5x5_rcontent_obs s5x5_rand_sample_cutE s5x5_rho1_index.
rewrite /s5x5_rfree_layout tnth_mktuple.
have Hlt : (s5x5_p1_idx j < 5)%N by rewrite s5x5_p1_idx_val; exact: ltn_ord.
case: (ltnP (s5x5_p1_idx j) 5) => Hc; last by rewrite (leq_gtF Hc) in Hlt.
by rewrite cancel_p1 s5x5_p1_idx_val inord_val /rs1 s5_rfree_shareE.
Qed.

(** s5x5_p2_seat_viewE — the executed pile-2 seat reader is that party's
    second-pile share.
    @main architecture: s5x5_p2_seat_view j = fun uv => rsh_share rs2 j uv.2,
    a reader with the pile carrier 'Z_5 and the party indexing of the second
    pile. *)
Lemma s5x5_p2_seat_viewE (j : 'I_5) :
  s5x5_p2_seat_view j = (fun uv => rsh_share (rs2 R) j uv.2).
Proof.
apply: boolp.funext => uv.
rewrite /s5x5_p2_seat_view /sa_seat_view.
rewrite (@exec_seat_endpointE mpX s5x5_rand_exec_plug s5x5_rcontent_obs _ _ 0
  (s5x5_rand_endpoints _ _) (s5x5_p2_idx j)).
rewrite /s5x5_rcontent_obs s5x5_rand_sample_cutE s5x5_rho1_index.
rewrite /s5x5_rfree_layout tnth_mktuple.
case: (ltnP (s5x5_p2_idx j) 5) => Hc;
  first by rewrite (leq_gtF (s5x5_p2_idx_ge j)) in Hc.
by rewrite cancel_p2 s5x5_p2_idx_val addKn inord_val /rs2 s5_rfree_shareE.
Qed.

(******************************************************************************)
(*     Executed per-pile and joint secrecy                                    *)
(******************************************************************************)

(* The secret of the three theorems below is JointSecret R, the pair of the
   two pile secrets. They are therefore not restatements of
   s5x5_secrecy.s5x5_view_secrecy_concrete, which pairs a pile-1 coalition
   view with the pile-1 secret alone at the first tape: the secret carrier
   here is ('Z_5 * 'Z_5) and the reader is the executed one. *)

(** s5x5_p1_view_indep — a sub-threshold pile-1 coalition view is independent
    of the joint product secret.
    @composes: s5x5_exec_p1_secrecy *)
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
    @composes: s5x5_exec_p2_secrecy *)
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

(** s5x5_exec_p1_secrecy — a sub-threshold pile-1 coalition's executed
    endpoint readings leave the joint product secret's entropy unchanged.
    @main security: exact privacy in mutual information and conditional
    entropy form, at the executed pile-1 coalition reader of s5x5_rand_sample
    and against the joint product secret JointSecret R, whenever #|C1| < 5. *)
Theorem s5x5_exec_p1_secrecy (C1 : {set 'I_5}) (HC1 : (#|C1| < 5)%N) :
  `I( JointSecret R ; s5x5_p1_view C1 ) = 0%R /\
  `H( JointSecret R | s5x5_p1_view C1 ) = `H `p_ (JointSecret R).
Proof.
rewrite s5x5_p1_viewE; apply: leakage_of_view_indep.
exact: s5x5_p1_view_indep HC1.
Qed.

(** s5x5_exec_p2_secrecy — a sub-threshold pile-2 coalition's executed
    endpoint readings leave the joint product secret's entropy unchanged.
    @main security: exact privacy in mutual information and conditional
    entropy form, at the executed pile-2 coalition reader of s5x5_rand_sample
    and against the joint product secret JointSecret R, whenever #|C2| < 5. *)
Theorem s5x5_exec_p2_secrecy (C2 : {set 'I_5}) (HC2 : (#|C2| < 5)%N) :
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
               (mechanism_leakage
                  (Additive (@unif_randomized_sharing R 3 4) HC1))
               (mechanism_leakage
                  (Additive (@unif_randomized_sharing R 3 4) HC2))).
Proof. by rewrite /s5x5_joint_view s5x5_p1_viewE s5x5_p2_viewE. Qed.

(** s5x5_exec_joint_secrecy — two sub-threshold pile coalitions' executed
    endpoint readings leave the joint product secret's entropy unchanged.
    @main security: exact privacy in mutual information and conditional
    entropy form, at the executed joint coalition reader of s5x5_rand_sample,
    under the two per-pile coalition bounds #|C1| < 5 and #|C2| < 5. *)
Theorem s5x5_exec_joint_secrecy (C1 C2 : {set 'I_5})
    (HC1 : (#|C1| < 5)%N) (HC2 : (#|C2| < 5)%N) :
  `I( JointSecret R ; s5x5_joint_view C1 C2 ) = 0%R /\
  `H( JointSecret R | s5x5_joint_view C1 C2 ) = `H `p_ (JointSecret R).
Proof.
rewrite (s5x5_joint_viewE HC1 HC2).
exact: (@s5x5_joint_view_secrecy R C1 C2 HC1 HC2).
Qed.

(******************************************************************************)
(*     The lazy mixing factor below one from word length seventeen on         *)
(*                                                                            *)
(* The block below bounds the numeric factor sqrt 5 * lazy ^+ L of the two    *)
(* pile bounds. The lazy coefficient is the rational 381/400, and each step   *)
(* squares a rational upper bound written with denominator 1000, so every     *)
(* arithmetic side condition is a closed comparison of two products of        *)
(* three-digit natural numbers. The exponent 17 is the least one at which the *)
(* resulting product is below one.                                            *)
(******************************************************************************)

Section s5x5_lazy_numeric.

Local Open Scope ring_scope.

(** s5x5_lazy_alphaE — the lazy mixing coefficient is 381/400.
    @composes: s5x5_lazy_pow1 *)
Lemma s5x5_lazy_alphaE : s5_lazy_alpha_R R = 381%:R / 400%:R.
Proof.
rewrite /s5_lazy_alpha_R /s5_alpha_R.
have -> : (1 + 181%:R / 200%:R : R) = 381%:R / 200%:R.
  by rewrite -{1}(@divff _ (200%:R : R)) ?pnatr_eq0 // -mulrDl -natrD.
by rewrite -mulrA -invfM -natrM.
Qed.

(** s5x5_lazy_sq_step — squaring a rational upper bound of a power of the lazy
    coefficient, at denominator 1000.
    @composes: s5x5_lazy_pow2, s5x5_lazy_pow4, s5x5_lazy_pow8,
    s5x5_lazy_pow16, s5x5_lazy_pow32 *)
Lemma s5x5_lazy_sq_step (k p q : nat) : (p * p <= q * 1000)%N ->
  (s5_lazy_alpha_R R ^+ k * 1000%:R <= p%:R)%R ->
  (s5_lazy_alpha_R R ^+ (2 * k) * 1000%:R <= q%:R)%R.
Proof.
move=> Hpq Hk.
have Ha0 : (0 <= s5_lazy_alpha_R R)%R := s5_lazy_alpha_R_ge0 R.
have H0 : (0 <= s5_lazy_alpha_R R ^+ k * 1000%:R)%R
  by rewrite mulr_ge0 ?exprn_ge0 ?ler0n.
have Hsq : ((s5_lazy_alpha_R R ^+ k * 1000%:R) ^+ 2 <= (p%:R : R) ^+ 2)%R.
  by apply: lerXn2r; rewrite ?nnegrE // ler0n.
rewrite exprMn -exprM -natrX in Hsq.
have Hp : ((p ^ 2)%:R : R) <= (q * 1000)%:R by rewrite ler_nat -mulnn in Hpq *.
have Hchain := le_trans Hsq Hp.
rewrite natrM expr2 mulrA in Hchain.
by rewrite mulnC -(@ler_pM2r _ (1000%:R : R)) ?ltr0n.
Qed.

(** s5x5_lazy_pow1 — the lazy coefficient is at most 953/1000.
    @composes: s5x5_lazy_pow2 *)
Lemma s5x5_lazy_pow1 : (s5_lazy_alpha_R R ^+ 1 * 1000%:R <= 953%:R)%R.
Proof.
rewrite s5x5_lazy_alphaE expr1 mulrAC ler_pdivrMr ?ltr0n // -!natrM ler_nat.
by vm_compute.
Qed.

(** s5x5_lazy_pow2 — the second power is at most 909/1000.
    @composes: s5x5_lazy_pow4, s5x5_lazy_pow34 *)
Lemma s5x5_lazy_pow2 : (s5_lazy_alpha_R R ^+ 2 * 1000%:R <= 909%:R)%R.
Proof.
apply: (@s5x5_lazy_sq_step 1 953 909); [by vm_compute | exact: s5x5_lazy_pow1].
Qed.

(** s5x5_lazy_pow4 — the fourth power is at most 827/1000.
    @composes: s5x5_lazy_pow8 *)
Lemma s5x5_lazy_pow4 : (s5_lazy_alpha_R R ^+ 4 * 1000%:R <= 827%:R)%R.
Proof.
apply: (@s5x5_lazy_sq_step 2 909 827); [by vm_compute | exact: s5x5_lazy_pow2].
Qed.

(** s5x5_lazy_pow8 — the eighth power is at most 684/1000.
    @composes: s5x5_lazy_pow16 *)
Lemma s5x5_lazy_pow8 : (s5_lazy_alpha_R R ^+ 8 * 1000%:R <= 684%:R)%R.
Proof.
apply: (@s5x5_lazy_sq_step 4 827 684); [by vm_compute | exact: s5x5_lazy_pow4].
Qed.

(** s5x5_lazy_pow16 — the sixteenth power is at most 468/1000.
    @composes: s5x5_lazy_pow32 *)
Lemma s5x5_lazy_pow16 : (s5_lazy_alpha_R R ^+ 16 * 1000%:R <= 468%:R)%R.
Proof.
apply: (@s5x5_lazy_sq_step 8 684 468); [by vm_compute | exact: s5x5_lazy_pow8].
Qed.

(** s5x5_lazy_pow32 — the thirty-second power is at most 220/1000.
    @composes: s5x5_lazy_pow34 *)
Lemma s5x5_lazy_pow32 : (s5_lazy_alpha_R R ^+ 32 * 1000%:R <= 220%:R)%R.
Proof.
apply: (@s5x5_lazy_sq_step 16 468 220); [by vm_compute | exact: s5x5_lazy_pow16].
Qed.

(** s5x5_lazy_pow34 — five times the thirty-fourth power is below one.
    @composes: s5x5_lazy_bound_lt1 *)
Lemma s5x5_lazy_pow34 : (5%:R * s5_lazy_alpha_R R ^+ 34 < 1 :> R)%R.
Proof.
have Ha0 : (0 <= s5_lazy_alpha_R R)%R := s5_lazy_alpha_R_ge0 R.
have H32 : (0 <= s5_lazy_alpha_R R ^+ 32 * 1000%:R)%R
  by rewrite mulr_ge0 ?exprn_ge0 ?ler0n.
have H2 : (0 <= s5_lazy_alpha_R R ^+ 2 * 1000%:R)%R
  by rewrite mulr_ge0 ?exprn_ge0 ?ler0n.
have Hprod : ((s5_lazy_alpha_R R ^+ 32 * 1000%:R)
              * (s5_lazy_alpha_R R ^+ 2 * 1000%:R) <= 220%:R * 909%:R)%R.
  by apply: ler_pM => //; [exact: s5x5_lazy_pow32 | exact: s5x5_lazy_pow2].
rewrite mulrACA -exprD -natrM in Hprod.
have Hp2 : (s5_lazy_alpha_R R ^+ 34 * (1000%:R * 1000%:R)
            <= (220 * 909)%:R :> R)%R by exact: Hprod.
rewrite -(@ltr_pM2r _ (1000%:R * 1000%:R : R)) ?mulr_gt0 ?ltr0n //.
rewrite mul1r -mulrA.
apply: (@le_lt_trans _ _ (5%:R * (220 * 909)%:R)).
  by rewrite ler_pM2l ?ltr0n //.
rewrite -natrM -natrM ltr_nat.
by vm_compute.
Qed.

(** s5x5_lazy_sqrt17 — the mixing factor at word length seventeen is below
    one.
    @composes: s5x5_lazy_bound_lt1 *)
Lemma s5x5_lazy_sqrt17 :
  (Num.sqrt 5%:R * s5_lazy_alpha_R R ^+ 17 < 1 :> R)%R.
Proof.
have Ha0 : (0 <= s5_lazy_alpha_R R)%R := s5_lazy_alpha_R_ge0 R.
rewrite -(@ltr_pXn2r R 2 isT).
2: by rewrite nnegrE mulr_ge0 ?sqrtr_ge0 ?exprn_ge0.
2: by rewrite nnegrE ler01.
rewrite exprMn sqr_sqrtr ?ler0n // -exprM expr1n.
exact: s5x5_lazy_pow34.
Qed.

(** s5x5_lazy_bound_lt1 — the mixing factor of the two pile bounds is below
    one from word length seventeen on.
    @main bound: Num.sqrt 5%:R * s5_lazy_alpha_R R ^+ n < 1 whenever
    17 <= n. *)
Lemma s5x5_lazy_bound_lt1 (n : nat) : (17 <= n)%N ->
  (Num.sqrt 5%:R * s5_lazy_alpha_R R ^+ n < 1 :> R)%R.
Proof.
move=> Hn.
apply: (@le_lt_trans _ _ (Num.sqrt 5%:R * s5_lazy_alpha_R R ^+ 17));
  last exact: s5x5_lazy_sqrt17.
rewrite ler_pM2l ?sqrtr_gt0 ?ltr0n //.
exact: (ler_wiXn2l (s5_lazy_alpha_R_ge0 R) (s5_lazy_alpha_R_le1 R) Hn).
Qed.

End s5x5_lazy_numeric.

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
    @intent: the sample layer over s5x5_exec_plug whose sample space is
    s5x5_word_sampleT under s5x5_word_sampleP, the run argument being the
    dealt position and the cut the evaluated word. *)
Definition s5x5_word_sample : SampleAdapter R s5x5_exec_plug :=
  @MkSampleAdapter R mpX s5x5_exec_plug s5x5_word_sampleT s5x5_word_sampleP
    fst s5x5_word_cut.

(** s5x5_word_sndE — the word marginal of the finite-word sample distribution
    is the uniform word distribution.
    @composes: s5x5_word_cut_distE *)
Lemma s5x5_word_sndE : fdist_snd s5x5_word_sampleP = @word_uniform R 7 L.
Proof. by rewrite /s5x5_word_sampleP -fdistX_prod fdistX2 fdist_prod1. Qed.

(** s5x5_word_cut_distE — the finite-word adapter's cut distribution is the
    word-induced shuffle distribution the spectral theorems bound.
    @main architecture: sa_cut_dist s5x5_word_sample = rho_from_words L
    s5x5_gen_tuple. *)
Lemma s5x5_word_cut_distE :
  @sa_cut_dist R mpX s5x5_exec_plug s5x5_word_sample
  = @rho_from_words R 8 7 L s5x5_gen_tuple.
Proof.
rewrite /sa_cut_dist /rho_from_words -s5x5_word_sndE /fdist_snd fdistmap_comp.
by [].
Qed.

(** s5x5_word_pile1_bound — the landed pile-1 spectral bound holds at the
    finite-word adapter's own cut distribution.
    @main bound: endpoint marginal mixing inside the first pile, conditional
    on the trusted analytical certificate s5_rayleigh_Q2_R: the variation
    distance between the pile-1 position pushforward of
    sa_cut_dist s5x5_word_sample and the pile-1 uniform distribution is at
    most sqrt 5 times the lazy spectral ratio to the power L, in the
    repository's full-L1 convention. The statement quantifies over one pile-1
    position, so it bounds one seat's endpoint marginal and not a coalition
    view. *)
Lemma s5x5_word_pile1_bound (s : 'I_5) :
  (var_dist (fdistmap (fun sigma : {perm 'I_10} => sigma (widen5to10 s))
               (@sa_cut_dist R mpX s5x5_exec_plug s5x5_word_sample))
            (fdist_uniform_pile1 R)
   <= Num.sqrt 5%:R * (s5_lazy_alpha_R R) ^+ L)%R.
Proof. by rewrite s5x5_word_cut_distE; exact: s5x5_pile1_TV_bound. Qed.

(** s5x5_word_pile2_bound — the landed pile-2 spectral bound holds at the
    finite-word adapter's own cut distribution.
    @main bound: endpoint marginal mixing inside the second pile, conditional
    on the trusted analytical certificate s5_rayleigh_Q2_R: the variation
    distance between the pile-2 position pushforward of
    sa_cut_dist s5x5_word_sample and the pile-2 uniform distribution is at
    most sqrt 5 times the lazy spectral ratio to the power L, in the
    repository's full-L1 convention. The statement quantifies over one pile-2
    position, so it bounds one seat's endpoint marginal and not a coalition
    view. *)
Lemma s5x5_word_pile2_bound (s : 'I_5) :
  (var_dist (fdistmap (fun sigma : {perm 'I_10} => sigma (rshift5to10 s))
               (@sa_cut_dist R mpX s5x5_exec_plug s5x5_word_sample))
            (fdist_uniform_pile2 R)
   <= Num.sqrt 5%:R * (s5_lazy_alpha_R R) ^+ L)%R.
Proof. by rewrite s5x5_word_cut_distE; exact: s5x5_pile2_TV_bound. Qed.

(** s5x5_word_seat_bound — the landed one-seat spectral bound holds at the
    finite-word adapter's own cut distribution.
    @main bound: endpoint marginal mixing of one of the ten seats against
    global uniform on ten seats, conditional on the trusted analytical
    certificate s5_rayleigh_Q2_R: the variation distance is at most
    1 + sqrt 5 times the lazy spectral ratio to the power L, in the
    repository's full-L1 convention. The leading summand 1 is the distance
    between a pile-uniform distribution and global uniform, the shuffle
    preserving each pile; the bound therefore does not vanish with L. The
    statement quantifies over one seat and is not a joint statement about two
    seats. *)
Lemma s5x5_word_seat_bound (s : 'I_10) :
  (var_dist (fdistmap (fun sigma : {perm 'I_10} => sigma s)
               (@sa_cut_dist R mpX s5x5_exec_plug s5x5_word_sample))
            (fdist_uniform (card_ord 10))
   <= 1 + Num.sqrt 5%:R * (s5_lazy_alpha_R R) ^+ L)%R.
Proof. by rewrite s5x5_word_cut_distE; exact: s5x5_spectral_TV_bound. Qed.

(******************************************************************************)
(*     The negative-transfer floors to global uniform                         *)
(******************************************************************************)

(** s5x5_word_pile1_floor — the reverse-triangle lower bound between the
    pile-1 endpoint distribution and global uniform on ten seats.
    @main bound: negative mixing result for the first pile, conditional on the
    trusted analytical certificate s5_rayleigh_Q2_R:
    1 - sqrt 5 * lazy ^+ L is a lower bound on the variation distance between
    the pile-1 position pushforward of the word-induced cut distribution and
    the uniform distribution on ten seats, in the repository's full-L1
    convention. *)
Lemma s5x5_word_pile1_floor (s : 'I_5) :
  (1 - Num.sqrt 5%:R * (s5_lazy_alpha_R R) ^+ L
   <= var_dist (fdistmap (fun sigma : {perm 'I_10} => sigma (widen5to10 s))
                  (@sa_cut_dist R mpX s5x5_exec_plug s5x5_word_sample))
               (fdist_uniform (card_ord 10)))%R.
Proof.
set A := fdistmap _ _.
have H1 := var_dist_triangle (fdist_uniform_pile1 R) A
             (fdist_uniform (card_ord 10)).
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
    @main bound: negative mixing result for the second pile, conditional on
    the trusted analytical certificate s5_rayleigh_Q2_R:
    1 - sqrt 5 * lazy ^+ L is a lower bound on the variation distance between
    the pile-2 position pushforward of the word-induced cut distribution and
    the uniform distribution on ten seats, in the repository's full-L1
    convention. *)
Lemma s5x5_word_pile2_floor (s : 'I_5) :
  (1 - Num.sqrt 5%:R * (s5_lazy_alpha_R R) ^+ L
   <= var_dist (fdistmap (fun sigma : {perm 'I_10} => sigma (rshift5to10 s))
                  (@sa_cut_dist R mpX s5x5_exec_plug s5x5_word_sample))
               (fdist_uniform (card_ord 10)))%R.
Proof.
set A := fdistmap _ _.
have H1 := var_dist_triangle (fdist_uniform_pile2 R) A
             (fdist_uniform (card_ord 10)).
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

(** s5x5_word_pile1_floor_gt0 — the pile-1 floor is positive from word length
    seventeen on.
    @main bound: negative mixing result for the first pile in its positive
    regime, conditional on the trusted analytical certificate
    s5_rayleigh_Q2_R: at 17 <= L the pile-1 position pushforward of the
    word-induced cut distribution is at positive variation distance from the
    uniform distribution on ten seats, in the repository's full-L1
    convention. *)
Lemma s5x5_word_pile1_floor_gt0 (s : 'I_5) : (17 <= L)%N ->
  (0 < var_dist (fdistmap (fun sigma : {perm 'I_10} => sigma (widen5to10 s))
                   (@sa_cut_dist R mpX s5x5_exec_plug s5x5_word_sample))
                (fdist_uniform (card_ord 10)))%R.
Proof.
move=> HL.
apply: (@lt_le_trans _ _
  (1 - Num.sqrt 5%:R * (s5_lazy_alpha_R R) ^+ L)%R);
  last exact: s5x5_word_pile1_floor.
by rewrite subr_gt0; exact: (s5x5_lazy_bound_lt1 HL).
Qed.

(** s5x5_word_pile2_floor_gt0 — the pile-2 floor is positive from word length
    seventeen on.
    @main bound: negative mixing result for the second pile in its positive
    regime, conditional on the trusted analytical certificate
    s5_rayleigh_Q2_R: at 17 <= L the pile-2 position pushforward of the
    word-induced cut distribution is at positive variation distance from the
    uniform distribution on ten seats, in the repository's full-L1
    convention. *)
Lemma s5x5_word_pile2_floor_gt0 (s : 'I_5) : (17 <= L)%N ->
  (0 < var_dist (fdistmap (fun sigma : {perm 'I_10} => sigma (rshift5to10 s))
                   (@sa_cut_dist R mpX s5x5_exec_plug s5x5_word_sample))
                (fdist_uniform (card_ord 10)))%R.
Proof.
move=> HL.
apply: (@lt_le_trans _ _
  (1 - Num.sqrt 5%:R * (s5_lazy_alpha_R R) ^+ L)%R);
  last exact: s5x5_word_pile2_floor.
by rewrite subr_gt0; exact: (s5x5_lazy_bound_lt1 HL).
Qed.

(******************************************************************************)
(*     The generic transfer theorem at the cut carrier                        *)
(******************************************************************************)

(** s5x5_word_base_premise — the base-distribution premise of the generic
    transfer theorem at the cut carrier.
    @intent: a variation-distance bound between the finite-word adapter's cut
    distribution on {perm 'I_10} and a reference distribution on the same
    carrier. The landed spectral theorems bound pushforwards along position
    readers, on the carrier 'I_10, and therefore do not instantiate this
    proposition. The bound is read in the repository's full-L1 convention,
    the convention of s5x5_word_pile1_bound. *)
Definition s5x5_word_base_premise (Q : R.-fdist {perm 'I_10}) (delta : R)
    : Prop :=
  (var_dist (@sa_cut_dist R mpX s5x5_exec_plug s5x5_word_sample) Q <= delta)%R.

(** s5x5_word_transfer_conditional — the generic transfer theorem applies to
    any pair of cut readers once the base-distribution premise is supplied.
    @main bound: two readers of the finite-word cut distribution whose
    pushforwards along Q agree have pushforwards within delta + delta, in the
    repository's full-L1 convention, provided s5x5_word_base_premise
    Q delta. *)
Lemma s5x5_word_transfer_conditional
    (Q : R.-fdist {perm 'I_10}) (delta : R) (B : finType)
    (fx fy : {perm 'I_10} -> B) :
  s5x5_word_base_premise Q delta ->
  fdistmap fx Q = fdistmap fy Q ->
  (var_dist (fdistmap fx (@sa_cut_dist R mpX s5x5_exec_plug s5x5_word_sample))
            (fdistmap fy (@sa_cut_dist R mpX s5x5_exec_plug s5x5_word_sample))
   <= delta + delta)%R.
Proof.
move=> H1 H2.
exact: (var_dist_fdistmap_transfer R _ _ _ _ _ _ _ H1 H2).
Qed.

(* The pile spectral theorems live at the carrier 'I_10, the premise at the
   carrier {perm 'I_10}; the guard below records that the two do not unify, so
   no cast turns an endpoint pushforward bound into a base-distribution bound.
   The positive Check pins the failure to that mismatch and not to a later
   name or arity change of the pile spectral theorem. *)
Check (fun s : 'I_5 => @s5x5_pile1_TV_bound R L s).
Fail Check (fun s : 'I_5 =>
  (@s5x5_pile1_TV_bound R L s
     : s5x5_word_base_premise (fdist_uniform_pile1 R)
         (Num.sqrt 5%:R * s5_lazy_alpha_R R ^+ L)%R)).

End s5x5_sample_layers.

(******************************************************************************)
(*     The typed model families of the S_5 x S_5 analysis paths               *)
(******************************************************************************)

(** s5x5_rand_family — the randomized product-tape model as a unit-indexed
    family.
    @intent: the AnalysisModelFamily over s5x5_rand_observed whose one
    member at every real field is s5x5_rand_sample. *)
Definition s5x5_rand_family : AnalysisModelFamily s5x5_rand_observed :=
  @MkAnalysisModelFamily s5x5_rand_observed (fun _ => unit)
    (fun R _ => s5x5_rand_sample R).

(** s5x5_word_family — the finite-word model family, indexed by a secret
    prior and a word length; the one family shared by the two endpoint and
    the two limitation rows.
    @intent: the AnalysisModelFamily over s5x5_observed sending an index
    (secretP, L) to s5x5_word_sample secretP L. *)
Definition s5x5_word_family : AnalysisModelFamily s5x5_observed :=
  @MkAnalysisModelFamily s5x5_observed
    (fun R => (R.-fdist 'I_10 * nat)%type)
    (fun R p => s5x5_word_sample p.1 p.2).
