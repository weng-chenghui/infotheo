(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* s5_models: the S_5 sample layers and their executed security bridges       *)
(*                                                                            *)
(* Two sample layers sit over the two S_5 execution plugs. The randomized     *)
(* exact-secrecy layer sits over s5_rand_exec_plug at the uniform iid tape    *)
(* distribution with the identity cut, which is the cut the landed executed   *)
(* results are stated at. The finite-word endpoint layer sits over            *)
(* s5_exec_plug at a secret prior times the uniform word distribution, with   *)
(* the evaluated generator word as cut.                                       *)
(*                                                                            *)
(* The two sample spaces are different by definition: the first is the        *)
(* randomized-sharing tape 'rV['Z_5]_5 and the second is a pair of a dealt    *)
(* position and an L-letter word. The finite-word layer is not a finite       *)
(* approximation of the randomized layer, no theorem here relating the two    *)
(* base distributions.                                                        *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   s5_rand_sampleP          == the uniform iid tape distribution            *)
(*   s5_rand_sample           == the randomized exact-secrecy sample adapter  *)
(*   s5_sample_content_trace  == seat i's executed trace content as a random  *)
(*                               variable on the tape distribution            *)
(*   s5_word_sampleT          == the finite-word sample space                 *)
(*   s5_word_sampleP          == the secret prior times the uniform word      *)
(*                               distribution                                 *)
(*   s5_word_cut              == the evaluation in S_5 of the sampled word    *)
(*   s5_word_sample           == the finite-word endpoint sample adapter      *)
(*   s5_word_base_premise     == the base-distribution premise of the generic *)
(*                               transfer theorem at the carrier {perm 'I_5}  *)
(*                                                                            *)
(* Key results:                                                               *)
(*   s5_sample_content_traceE == the executed content reader at seat i is     *)
(*                               s5_player_trace i                            *)
(*   s5_exec_trace_secrecy    == the conditional entropy of the tape secret   *)
(*                               given one seat's executed trace content is   *)
(*                               its entropy                                  *)
(*   s5_sample_coalition_viewE == the executed coalition endpoint reader is   *)
(*                               the randomized sharing's coalition view      *)
(*   s5_exec_coalition_secrecy == a coalition of fewer than five seats has    *)
(*                               zero mutual information with the tape secret *)
(*                               and leaves its conditional entropy equal to  *)
(*                               its entropy                                  *)
(*   s5_rand_cut_distE        == the randomized adapter's cut distribution is *)
(*                               the point distribution at the identity       *)
(*   s5_word_cut_distE        == the word adapter's cut distribution is       *)
(*                               rho_from_words L (path_gen_tuple 3)          *)
(*   s5_word_cut_imageE       == the word adapter's shuffle-image             *)
(*                               distribution is that same word-induced       *)
(*                               distribution, the representation being the   *)
(*                               identity                                     *)
(*   s5_word_endpoint_bound   == the endpoint marginal bound at that cut      *)
(*                               distribution, conditional on s5_rayleigh_Q2_R*)
(*   s5_word_transfer_conditional == the generic transfer inequality at the   *)
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
From pgg_smc Require Import pgg_raag_s5 pgg_raag_path s5_profile s5_run.
From pgg_smc Require Import pgg_leakage_witness pgg_randomized_sharing.
From pgg_smc Require Import pgg_canonical_sharing pgg_sharing_mechanism.
From pgg_smc Require Import pgg_trace_secrecy s5_trace s5_secrecy s5_mixing.
From pgg_smc Require Import s5_exec pgg_analysis_status.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Section s5_sample_layers.

(** s5_M — the S_5 adjacent-transposition monodromy template at N = 5.
    @intent: the Gen_PGGTypes form s5_PI and s5_plug carry, spelled out here
    because the instance files keep it section-local. *)
Local Notation s5_M := (@Gen_PGGTypes 3 3 (path_gen_tuple 3)).

Let mpS : MonodromyProfile := s5_profile.

Variable R : realType.

(******************************************************************************)
(*     The randomized exact-secrecy sample layer                              *)
(******************************************************************************)

(** s5_rand_sampleP — the uniform iid sampler distribution over the tape.
    @intent: the distribution of s5_trace's secrecy results respelled, that
    file keeping it as a section-local Let: fdist_uniform (card_ZN_subproof 3)
    raised to the fifth power. *)
Definition s5_rand_sampleP : R.-fdist 'rV['Z_5]_5 :=
  fdist_uniform (pgg_canonical_sharing.card_ZN_subproof 3) `^ 5.

(** s5_rand_sample — the S_5 randomized exact-secrecy sample adapter.
    @intent: the sample layer over s5_rand_exec_plug whose sample space is the
    tape 'rV['Z_5]_5 under s5_rand_sampleP, the run argument being the tape
    itself and the cut the identity, the cut the landed executed results are
    stated at. *)
Definition s5_rand_sample : SampleAdapter R s5_rand_exec_plug :=
  @MkSampleAdapter R mpS s5_rand_exec_plug [the finType of 'rV['Z_5]_5]
    s5_rand_sampleP idfun (fun _ => 1%g).

(** s5_rand_sample_argE — the randomized adapter's run argument is the tape.
    @composes: s5_sample_content_traceE *)
Lemma s5_rand_sample_argE (u : 'rV['Z_5]_5) : s5_rand_sample.(sa_arg) u = u.
Proof. by []. Qed.

(** s5_rand_sample_cutE — the randomized adapter's cut is the identity.
    @composes: s5_sample_content_traceE, s5_sample_coalition_viewE *)
Lemma s5_rand_sample_cutE (u : 'rV['Z_5]_5) :
  s5_rand_sample.(sa_cut) u = (1%g : pgg_gT s5_M).
Proof. by []. Qed.

(** s5_rand_cut_distE — the randomized adapter's cut distribution is the point
    distribution at the identity.
    @main architecture: sa_cut_dist s5_rand_sample = fdist1 1. *)
Lemma s5_rand_cut_distE :
  @sa_cut_dist R mpS s5_rand_exec_plug s5_rand_sample
  = fdist1 (1%g : pgg_gT s5_M).
Proof.
rewrite /sa_cut_dist; apply/fdist_ext => g; rewrite fdistmapE fdist1E /=.
case: (eqVneq g (1%g : pgg_gT s5_M)) => [->|Hg].
- rewrite -[RHS](FDist.f1 s5_rand_sampleP); apply: eq_bigl => a.
  by rewrite inE /= eqxx.
- by rewrite big_pred0 // => a; rewrite inE /= eq_sym (negbTE Hg).
Qed.

(******************************************************************************)
(*     The finite content-trace reader on the randomized layer                *)
(******************************************************************************)

(** s5_sample_content_trace — seat i's executed trace content as a random
    variable on the tape distribution.
    @intent: s5_trace.content_of applied to the plug's raw participant trace
    at the sample's argument and cut, a finite reader of a sequence-carried
    trace. *)
Definition s5_sample_content_trace (i : 'I_(pi_T' (mp_PI mpS)).+1)
    : {RV s5_rand_sampleP -> 'I_(pgg_N' (mp_M mpS)).+1} :=
  fun u => s5_trace.content_of (@exec_participant_trace mpS s5_rand_exec_plug
                         (s5_rand_sample.(sa_arg) u)
                         (s5_rand_sample.(sa_cut) u) 0 i).

(** s5_sample_content_traceE — the executed content reader is the landed
    player-trace random variable.
    @composes: s5_exec_trace_secrecy *)
Lemma s5_sample_content_traceE (i : 'I_(pi_T' (mp_PI mpS)).+1) :
  s5_sample_content_trace i = s5_player_trace R i.
Proof.
apply: boolp.funext => u.
rewrite /s5_sample_content_trace /exec_participant_trace /exec_seat_id
        /exec_run s5_rand_fuelE s5_rand_sample_argE s5_rand_sample_cutE
        s5_rand_procsE (s5_rprocs_cut1 R u).
by rewrite /s5_player_trace.
Qed.

(** s5_exec_trace_secrecy — a single corrupted seat's executed trace leaves the
    tape secret's conditional entropy equal to its plain entropy.
    @main security: trace secrecy in conditional-entropy form, at the executed
    content reader of s5_rand_sample: `H( rsh_secret (unif_randomized_sharing
    R 3 4) | s5_sample_content_trace i ) = `H `p_ (rsh_secret
    (unif_randomized_sharing R 3 4)), for every seat i. *)
Theorem s5_exec_trace_secrecy (i : 'I_(pi_T' (mp_PI mpS)).+1) :
  `H( rsh_secret (@unif_randomized_sharing R 3 4)
      | s5_sample_content_trace i )
  = `H `p_ (rsh_secret (@unif_randomized_sharing R 3 4)).
Proof. by rewrite s5_sample_content_traceE; exact: s5_trace_secrecy. Qed.

(******************************************************************************)
(*     The coalition endpoint reader on the randomized layer                  *)
(******************************************************************************)

(** s5_sample_coalition_viewE — the executed coalition endpoint reader is the
    randomized sharing's coalition view.
    @composes: s5_exec_coalition_secrecy *)
Lemma s5_sample_coalition_viewE (C : {set 'I_(pi_T' (mp_PI mpS)).+1}) :
  @sa_coalition_view R mpS s5_rand_exec_plug s5_rand_sample 0 C
  = rsh_view (@unif_randomized_sharing R 3 4) C.
Proof.
apply: boolp.funext => u; apply/ffunP => j.
rewrite /sa_coalition_view (@exec_coalition_endpointsE mpS s5_rand_exec_plug
  s5_rcontent_obs _ _ 0 (s5_rand_endpoints _ _) C).
rewrite /rsh_view !ffunE; case: ifP => // _.
rewrite /s5_rcontent_obs s5_rand_sample_cutE s5_rho1_index.
by rewrite /s5_rfree_layout tnth_mktuple s5_rfree_shareE.
Qed.

(** s5_exec_coalition_secrecy — a coalition of fewer than five seats reads its
    executed endpoints without learning anything about the tape secret.
    @main security: exact secrecy at the executed coalition reader of
    s5_rand_sample, in both forms: the mutual information of the tape secret
    and sa_coalition_view s5_rand_sample 0 C is zero, and the conditional
    entropy of the tape secret given that reading is its entropy, whenever
    #|C| < 5. *)
Theorem s5_exec_coalition_secrecy (C : {set 'I_(pi_T' (mp_PI mpS)).+1})
    (HC : (#|C| < 5)%N) :
  `I( rsh_secret (@unif_randomized_sharing R 3 4) ;
      @sa_coalition_view R mpS s5_rand_exec_plug s5_rand_sample 0 C ) = 0%R /\
  `H( rsh_secret (@unif_randomized_sharing R 3 4)
      | @sa_coalition_view R mpS s5_rand_exec_plug s5_rand_sample 0 C )
    = `H `p_ (rsh_secret (@unif_randomized_sharing R 3 4)).
Proof.
rewrite s5_sample_coalition_viewE.
exact: (@s5_view_secrecy_concrete R C HC).
Qed.

(******************************************************************************)
(*     The finite-word endpoint sample layer                                  *)
(******************************************************************************)

(* The secret prior of the word sample space, arbitrary where the randomized
   sample space fixes the uniform iid tape. *)
Variable secretP : R.-fdist 'I_5.
Variable L : nat.

(** s5_word_sampleT — the finite-word sample space.
    @intent: pairs of a dealt position and an L-letter word over the four
    path-graph generators. *)
Definition s5_word_sampleT : finType :=
  [the finType of ('I_5 * L.-tuple 'I_4)%type].

(** s5_word_sampleP — the finite-word sample distribution.
    @intent: the product of the secret prior with the uniform word
    distribution word_uniform 3 L, the distribution rho_from_words is the
    image of. *)
Definition s5_word_sampleP : R.-fdist s5_word_sampleT :=
  (secretP `x (@word_uniform R 3 L))%fdist.

(** s5_word_cut — the finite-word cut map.
    @intent: the evaluation in S_5 of the sampled generator word. *)
Definition s5_word_cut (u : s5_word_sampleT) : pgg_gT (mp_M mpS) :=
  @word_eval s5_M L u.2.

(** s5_word_sample — the S_5 finite-word endpoint sample adapter.
    @intent: the sample layer over s5_exec_plug whose sample space is
    s5_word_sampleT under s5_word_sampleP, the run argument being the dealt
    position and the cut the evaluated word. *)
Definition s5_word_sample : SampleAdapter R s5_exec_plug :=
  @MkSampleAdapter R mpS s5_exec_plug s5_word_sampleT s5_word_sampleP
    fst s5_word_cut.

(** s5_word_sndE — the word marginal of the finite-word sample distribution is
    the uniform word distribution.
    @composes: s5_word_cut_distE *)
Lemma s5_word_sndE : fdist_snd s5_word_sampleP = @word_uniform R 3 L.
Proof. by rewrite /s5_word_sampleP -fdistX_prod fdistX2 fdist_prod1. Qed.

(** s5_word_cut_distE — the finite-word adapter's cut distribution is the
    word-induced shuffle distribution the spectral theorem bounds.
    @composes: s5_word_endpoint_bound, s5_word_cut_imageE *)
Lemma s5_word_cut_distE :
  @sa_cut_dist R mpS s5_exec_plug s5_word_sample
  = rho_from_words L (path_gen_tuple 3).
Proof.
rewrite /sa_cut_dist /rho_from_words -s5_word_sndE /fdist_snd fdistmap_comp.
by [].
Qed.

(** s5_word_cut_imageE — the finite-word adapter's shuffle-image distribution
    is the same word-induced distribution.
    @main architecture: sa_cut_dist_image s5_word_sample = rho_from_words L
    (path_gen_tuple 3), the representation of this instance being the
    identity. *)
Lemma s5_word_cut_imageE :
  @sa_cut_dist_image R mpS s5_exec_plug s5_word_sample
  = rho_from_words L (path_gen_tuple 3).
Proof.
rewrite /sa_cut_dist_image s5_word_cut_distE.
rewrite -[in RHS](fdistmap_id (rho_from_words L (path_gen_tuple 3))).
by congr fdistmap; exact: boolp.funext.
Qed.

(** s5_word_endpoint_bound — the endpoint marginal bound at the finite-word
    adapter's own cut distribution.
    @main bound: endpoint marginal mixing, conditional on the trusted
    analytical certificate s5_rayleigh_Q2_R: the variation distance between
    the position pushforward of sa_cut_dist s5_word_sample and the uniform
    distribution on 'I_5 is at most sqrt 5 times alpha to the power L, in the
    repository's full-L1 convention. The statement quantifies over one
    position, so it bounds one seat's endpoint marginal and not a coalition
    view. *)
Lemma s5_word_endpoint_bound (s : 'I_5) :
  (var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
               (@sa_cut_dist R mpS s5_exec_plug s5_word_sample))
            (fdist_uniform (card_ord 5))
   <= Num.sqrt 5%:R * (s5_alpha_R R) ^+ L)%R.
Proof. by rewrite s5_word_cut_distE; exact: s5_spectral_convergence_proved. Qed.

(******************************************************************************)
(*     The generic transfer theorem at the cut carrier                        *)
(******************************************************************************)

(** s5_word_base_premise — the base-distribution premise of the generic
    transfer theorem at the cut carrier.
    @intent: a variation-distance bound between the finite-word adapter's cut
    distribution on {perm 'I_5} and a reference distribution on the same
    carrier. The landed spectral theorem bounds the pushforward along a
    position reader, on the carrier 'I_5, and therefore does not instantiate
    this proposition. The bound is read in the repository's full-L1
    convention, the convention of s5_word_endpoint_bound. *)
Definition s5_word_base_premise (Q : R.-fdist {perm 'I_5}) (delta : R) : Prop :=
  (var_dist (@sa_cut_dist R mpS s5_exec_plug s5_word_sample) Q <= delta)%R.

(** s5_word_transfer_conditional — the generic transfer theorem applies to any
    pair of cut readers once the base-distribution premise is supplied.
    @main bound: two readers of the finite-word cut distribution whose
    pushforwards along Q agree have pushforwards within delta + delta, in the
    repository's full-L1 convention, provided s5_word_base_premise Q delta. *)
Lemma s5_word_transfer_conditional
    (Q : R.-fdist {perm 'I_5}) (delta : R) (B : finType)
    (fx fy : {perm 'I_5} -> B) :
  s5_word_base_premise Q delta ->
  fdistmap fx Q = fdistmap fy Q ->
  (var_dist (fdistmap fx (@sa_cut_dist R mpS s5_exec_plug s5_word_sample))
            (fdistmap fy (@sa_cut_dist R mpS s5_exec_plug s5_word_sample))
   <= delta + delta)%R.
Proof.
move=> H1 H2.
exact: (var_dist_fdistmap_transfer R _ _ _ _ _ _ _ H1 H2).
Qed.

(* The spectral theorem lives at the carrier 'I_5, the premise at the carrier
   {perm 'I_5}; the guard below records that the two do not unify, so no cast
   turns an endpoint pushforward bound into a base-distribution bound. The
   positive Check pins the failure to that mismatch and not to a later name or
   arity change of the spectral theorem. *)
Check (fun s : 'I_5 => s5_spectral_convergence_proved R L s).
Fail Check (fun s : 'I_5 =>
  (s5_spectral_convergence_proved R L s
     : s5_word_base_premise (fdist_uniform (card_ord 5))
         (Num.sqrt 5%:R * s5_alpha_R R ^+ L)%R)).

End s5_sample_layers.

(******************************************************************************)
(*     The executed endpoint bound against the encoder-image ideal            *)
(*                                                                            *)
(* Amended work package A (user-approved 2026-08-13): the executed seat      *)
(* reading is compared with the encoder-image ideal, not with uniform. The   *)
(* uniform-ideal form is false for this plug's deterministic encoder; its    *)
(* compiled refutation is recorded in the 2026-08-13 completion response.    *)
(******************************************************************************)

Section s5_exec_ideal.

Variable R : realType.
Let mpS : MonodromyProfile := s5_profile.

Import GRing.Theory Num.Theory Order.POrderTheory.
Local Open Scope ring_scope.

Local Notation s5_M := (@Gen_PGGTypes 3 3 (path_gen_tuple 3)).

(** s5_ideal_reading — the encoder-image ideal reading: the content one seat
    reads when the dealt position is exactly uniform, mixed over the secret
    prior.
    @intent: the pushforward of secretP times the uniform position along the
    encoder tnth (ts_encode s5_scheme). The ideal is neither uniform nor
    secret-independent. *)
Definition s5_ideal_reading (secretP : R.-fdist 'I_5) : R.-fdist 'I_5 :=
  fdistmap (fun sq : 'I_5 * 'I_5 => tnth (ts_encode s5_scheme sq.1) sq.2)
    (secretP `x (fdist_uniform (card_ord 5))).

(** s5_exec_endpoint_bound — executed endpoint marginal mixing, conditional
    on the trusted analytical certificate s5_rayleigh_Q2_R.
    @main bound: the variation distance, in the repository's full-L1
    convention, between sa_seat_dist of the interpreter-executed finite-word
    adapter at one seat and the encoder-image ideal reading, the content
    that seat reads when the dealt position is exactly uniform mixed over
    the secret prior, is at most sqrt 5 times alpha to the power L. The
    statement bounds one seat's endpoint marginal, the ideal reading is
    neither uniform nor secret-independent, and no coalition, privacy,
    secrecy or leakage conclusion is claimed. *)
Lemma s5_exec_endpoint_bound (secretP : R.-fdist 'I_5) (L : nat)
    (i : 'I_(pi_T' (mp_PI mpS)).+1) :
  var_dist
    (@sa_seat_dist R mpS s5_exec_plug (s5_word_sample secretP L) 0 i)
    (s5_ideal_reading secretP)
  <= Num.sqrt 5%:R * (s5_alpha_R R) ^+ L.
Proof.
have Hsp : sa_sampleP (s5_word_sample secretP L)
         = (secretP `x (@word_uniform R 3 L))%fdist by [].
have Hview : @sa_seat_view R mpS s5_exec_plug (s5_word_sample secretP L) 0 i
  = (fun u : ('I_5 * L.-tuple 'I_4)%type =>
       tnth (ts_encode s5_scheme u.1) (@word_eval s5_M L u.2 i)).
  apply: boolp.funext => u.
  by rewrite /sa_seat_view /= s5_exec_seat_endpointE /s5_content_obs /=
             tnth_ord_tuple.
rewrite /sa_seat_dist Hview Hsp /s5_ideal_reading.
apply: (@var_dist_fdistmap_prod_mix R _ _ _ _ secretP _ _
          (fun (a : 'I_5) (w : L.-tuple 'I_4) =>
             tnth (ts_encode s5_scheme a) (@word_eval s5_M L w i))
          (fun (a : 'I_5) (q : 'I_5) => tnth (ts_encode s5_scheme a) q) _)
  => a.
have E1 : fdistmap (fun w : L.-tuple 'I_4 =>
             tnth (ts_encode s5_scheme a) (@word_eval s5_M L w i))
            (@word_uniform R 3 L)
        = fdistmap (fun c : 'I_5 => tnth (ts_encode s5_scheme a) c)
            (fdistmap (fun sigma : {perm 'I_5} => sigma i)
               (@rho_from_words R 3 3 L (path_gen_tuple 3))).
  by rewrite fdistmap_comp /rho_from_words fdistmap_comp.
rewrite E1.
apply: (le_trans (var_dist_fdistmap _ _ _)).
exact: s5_spectral_convergence_proved.
Qed.

(* The executed bound lives at the endpoint carrier 'I_5. The guard below
   records that it does not instantiate the cut-carrier base premise
   s5_word_base_premise on {perm 'I_5}: the encoder-image transfer is
   observer-level and never discharges the absent group-level premise,
   which for the group-uniform ideal remains unsatisfiable. The positive
   Check pins the failure to that carrier mismatch and not to a later name
   or arity change. *)
Check (fun (secretP : R.-fdist 'I_5) (L : nat)
           (i : 'I_(pi_T' (mp_PI mpS)).+1) =>
  s5_exec_endpoint_bound secretP L i).
Fail Check (fun (secretP : R.-fdist 'I_5) (L : nat)
                (i : 'I_(pi_T' (mp_PI mpS)).+1) =>
  (s5_exec_endpoint_bound secretP L i
     : s5_word_base_premise secretP L (fdist_uniform (card_ord 5))
         (Num.sqrt 5%:R * s5_alpha_R R ^+ L)%R)).

End s5_exec_ideal.

(******************************************************************************)
(*     The typed model families of the S_5 analysis paths                     *)
(******************************************************************************)

(** s5_rand_family — the randomized tape model as a unit-indexed family.
    @intent: the AnalysisModelFamily over s5_rand_observed whose one member
    at every real field is s5_rand_sample. *)
Definition s5_rand_family : AnalysisModelFamily s5_rand_observed :=
  @MkAnalysisModelFamily s5_rand_observed (fun _ => unit)
    (fun R _ => s5_rand_sample R).

(** s5_word_family — the finite-word model family, indexed by a secret prior
    and a word length.
    @intent: the AnalysisModelFamily over s5_observed sending an index
    (secretP, L) to s5_word_sample secretP L. *)
Definition s5_word_family : AnalysisModelFamily s5_observed :=
  @MkAnalysisModelFamily s5_observed
    (fun R => (R.-fdist 'I_5 * nat)%type)
    (fun R p => s5_word_sample p.1 p.2).
