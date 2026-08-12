(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe D2, mutation check: the cut map, the coalition guard and the fixed   *)
(* secret are all load-bearing                                               *)
(*                                                                           *)
(* Section 15.5 claims that the PGL(2,7) fixed-secret word model carries the *)
(* word shuffle as its cut distribution, that the executed content reader    *)
(* reports a coalition's seats and nothing else, and that the 2^-39          *)
(* miniature compares two fixed secrets.  This file checks the three claims  *)
(* that make those statements honest.                                        *)
(*                                                                           *)
(*   M1  the cut map is load-bearing.  Replacing the word evaluation by the  *)
(*       constant identity cut breaks the cut-distribution equation, both    *)
(*       under the control's own script (M1a) and under the sharper closer   *)
(*       exact: erefl (M1b).                                                 *)
(*                                                                           *)
(*   M2  the coalition guard is load-bearing.  Dropping the i \in C test     *)
(*       from the content reader breaks the agreement with the landed        *)
(*       coalition trace (M2a).  The rejection is not an artefact of the     *)
(*       script: at C = [set ord0], secret true and identity cut the two     *)
(*       finfuns differ at seat one (mu2_content_trace_neq), because the     *)
(*       unguarded reader reports the dealt card there while the coalition   *)
(*       trace reports ord0.                                                 *)
(*                                                                           *)
(*   M3  the fixed secret is load-bearing.  Using the same secret on both    *)
(*       sides degenerates the bound to 0 <= 2^-39, which holds with no      *)
(*       reference to the shuffle (mu3_same_secret), so the two-secret form  *)
(*       is the contentful one.  Substituting the arbitrary-prior model      *)
(*       pgl27_word_sample for a fixed-secret model is rejected, both in the *)
(*       miniature's proof (M3a) and in the distribution identity the        *)
(*       miniature rewrites by (M3b).                                        *)
(*                                                                           *)
(* Each rejection is wrapped in Fail, so the file compiles green exactly     *)
(* when all five are rejected.  The unmutated twins are declared first as    *)
(* positive controls, so a Fail cannot pass by a mistake shared with the     *)
(* honest case.                                                             *)
(*                                                                           *)
(* The message quoted above a Fail is the verbatim diagnostic obtained by    *)
(* removing that one Fail and re-elaborating the declaration under the       *)
(* interactive checker: batch mode does not echo the message of a Fail that  *)
(* succeeds in failing.                                                     *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_weighted_words.
From pgg_smc Require Import pgg_sample_adapter.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    algebraic_rigidity input_encoding.
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_scheme pgl27_profile.
From pgg_smc Require Import pgl27_run pgl27_secrecy pgl27_trace pgl27_mixing.
From pgg_smc Require Import pgl27_word_privacy pgl27_exec.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Section d2_mutations.

Variable R : realType.

Let mpP : MonodromyProfile R := pgl27_profile R.

(******************************************************************************)
(*     The copied definitions the controls are stated over                    *)
(******************************************************************************)

(** pgl27_fixed_word_sample — the word model at a fixed secret.
    @intent: copied from probe_d2_pgl27_models, the sample layer whose cut is
    the evaluated two-hundred-letter word and whose run argument is the
    constant s. *)
Definition pgl27_fixed_word_sample (s : bool)
    : SampleAdapter (pgl27_exec_plug R) :=
  @MkSampleAdapter R mpP (pgl27_exec_plug R)
    [the finType of (200.-tuple 'I_5)%type] (pgl27_word_wordP R) (fun _ => s)
    (fun w => @word_eval pgl27_Msym 200 w).

(** pgl27_exec_content_trace — the guarded executed content reader.
    @intent: copied from probe_d2_pgl27_models, the finfun sending a seat in C
    to the content of that seat's executed interpreter row and every seat
    outside C to ord0. *)
Definition pgl27_exec_content_trace (C : {set 'I_8}) (s : bool)
    (w0 : pgg_gT pgl27_M) : {ffun 'I_8 -> 'I_8} :=
  [ffun i => if i \in C
             then content_of
                    (@exec_participant_trace R mpP (pgl27_exec_plug R) s w0 0 i)
             else ord0].

(** pgl27_exec_rowE — the executed participant trace at seat i is the
    interpreter row of pgl27_procs at process 2 + i.
    @composes: pgl27_seat_contentE *)
Lemma pgl27_exec_rowE (s : bool) (w0 : pgg_gT pgl27_M) (i : 'I_8) :
  @exec_participant_trace R mpP (pgl27_exec_plug R) s w0 0 i
  = nth [::] (run_interp pgl27_fuel (pgl27_procs s w0)).2 (2 + i).
Proof.
have -> : @exec_participant_trace R mpP (pgl27_exec_plug R) s w0 0 i
        = pgl27_exec_player_raw_trace (R:=R) s w0 i by exact: erefl.
exact: (@pgl27_exec_raw_traceE R s w0 i).
Qed.

(** pgl27_seat_contentE — the content of seat i's executed row is the landed
    single-player trace random variable.
    @composes: mu2_content_trace_neq *)
Lemma pgl27_seat_contentE (s : bool) (w0 : pgg_gT pgl27_M) (i : 'I_8) :
  content_of (@exec_participant_trace R mpP (pgl27_exec_plug R) s w0 0 i)
  = pgl27_player_trace R i (s, w0).
Proof. by rewrite pgl27_exec_rowE /pgl27_player_trace. Qed.

(** pgl27_static_coalition_viewE — the executed coalition endpoints are the
    static coalition view.
    @composes: pgl27_fixed_word_coalition_distE *)
Lemma pgl27_static_coalition_viewE (C : {set 'I_8}) (s : bool)
    (w0 : pgg_gT pgl27_M) :
  @exec_coalition_endpoints R mpP (pgl27_exec_plug R) s w0 0 C
  = pgl27_view R C (s, w0).
Proof.
rewrite (@pgl27_exec_coalition_endpointsE R s w0 C).
apply/ffunP => i; rewrite /pgl27_view [LHS]ffunE [RHS]ffunE.
by case: ifP => // _; rewrite /pgl27_content_obs /= tnth_ord_tuple.
Qed.

(** pgl27_fixed_word_coalition_distE — the executed coalition distribution of
    the fixed-secret word model is the pushforward of the word shuffle along
    the static view at secret s.
    @composes: mu3_control *)
Lemma pgl27_fixed_word_coalition_distE (C : {set 'I_8}) (s : bool) :
  @sa_coalition_dist R mpP (pgl27_exec_plug R) (pgl27_fixed_word_sample s) 0 C
  = fdistmap (fun g => pgl27_view R C (s, g)) (rho_word R).
Proof.
have Hview : @sa_coalition_view R mpP (pgl27_exec_plug R)
               (pgl27_fixed_word_sample s) 0 C
           = (fun g : pgg_gT pgl27_M => pgl27_view R C (s, g))
             \o (fun w : 200.-tuple 'I_5 => @word_eval pgl27_Msym 200 w).
  by apply: boolp.funext => w; exact: pgl27_static_coalition_viewE.
rewrite /sa_coalition_dist Hview.
rewrite -(fdistmap_comp (fun g : pgg_gT pgl27_M => pgl27_view R C (s, g))
            (fun w : 200.-tuple 'I_5 => @word_eval pgl27_Msym 200 w)).
by rewrite /sa_cut_dist /rho_word /rho_from_words_weighted /pgl27_word_wordP.
Qed.

(******************************************************************************)
(*     M1: the cut map is load-bearing                                        *)
(******************************************************************************)

(** mu1_control — with the word evaluation as the cut the cut distribution is
    the word shuffle.
    @composes: mu1_attempt *)
Definition mu1_control (s : bool) :
  @sa_cut_dist R mpP (pgl27_exec_plug R) (pgl27_fixed_word_sample s)
  = rho_word R :=
  ltac:(by rewrite /sa_cut_dist /rho_word /rho_from_words_weighted
             /pgl27_word_wordP).

(** mu1_word_sample — the mutated word model whose cut is the constant
    identity.
    @intent: pgl27_fixed_word_sample with the word evaluation replaced by the
    constant group unit, the sample space and distribution unchanged. *)
Definition mu1_word_sample (s : bool) : SampleAdapter (pgl27_exec_plug R) :=
  @MkSampleAdapter R mpP (pgl27_exec_plug R)
    [the finType of (200.-tuple 'I_5)%type] (pgl27_word_wordP R) (fun _ => s)
    (fun _ => 1%g).

(* M1a: the constant cut pushes the whole word distribution onto the group
   unit, so the cut distribution is a Dirac mass rather than the word
   shuffle.  Rejected with

     No applicable tactic. *)
Fail Definition mu1_attempt (s : bool) :
  @sa_cut_dist R mpP (pgl27_exec_plug R) (mu1_word_sample s) = rho_word R :=
  ltac:(by rewrite /sa_cut_dist /rho_word /rho_from_words_weighted
             /pgl27_word_wordP).

(* M1b: the rejection is not an artefact of the closing tactic; the sharper
   conversion closer is rejected too.  Rejected with

     Cannot apply lemma erefl *)
Fail Definition mu1_attempt_erefl (s : bool) :
  @sa_cut_dist R mpP (pgl27_exec_plug R) (mu1_word_sample s) = rho_word R :=
  ltac:(exact: erefl).

(******************************************************************************)
(*     M2: the coalition guard is load-bearing                                *)
(******************************************************************************)

(** mu2_control — the guarded reader agrees with the landed coalition trace.
    @composes: mu2_attempt *)
Definition mu2_control (C : {set 'I_8}) (u : bool * pgg_gT pgl27_M) :
  pgl27_exec_content_trace C u.1 u.2 = pgl27_coalition_trace R C u :=
  ltac:(apply/ffunP => i;
        rewrite /pgl27_exec_content_trace /pgl27_coalition_trace;
        rewrite [LHS]ffunE [RHS]ffunE;
        case Hi: (i \in C); last by [];
        rewrite pgl27_exec_rowE;
        by rewrite /pgl27_player_trace).

(** mu2_content_trace — the mutated reader with the coalition guard dropped.
    @intent: pgl27_exec_content_trace reporting the content of every seat's
    executed row, so that C no longer restricts what is read. *)
Definition mu2_content_trace (C : {set 'I_8}) (s : bool)
    (w0 : pgg_gT pgl27_M) : {ffun 'I_8 -> 'I_8} :=
  [ffun i => content_of
               (@exec_participant_trace R mpP (pgl27_exec_plug R) s w0 0 i)].

(* M2a: without the guard the reader must also match the coalition trace at
   the seats outside C, where the trace is ord0.  Rejected with

     No applicable tactic. *)
Fail Definition mu2_attempt (C : {set 'I_8}) (u : bool * pgg_gT pgl27_M) :
  mu2_content_trace C u.1 u.2 = pgl27_coalition_trace R C u :=
  ltac:(apply/ffunP => i;
        rewrite /mu2_content_trace /pgl27_coalition_trace;
        rewrite [LHS]ffunE [RHS]ffunE;
        case Hi: (i \in C); last by [];
        rewrite pgl27_exec_rowE;
        by rewrite /pgl27_player_trace).

(** mu2_content_trace_neq — at the singleton coalition of seat zero, secret
    true and identity cut the unguarded reader differs from the landed
    coalition trace.
    @main architecture: the M2a rejection is semantic, the two finfuns differ
    at seat one, where the unguarded reader reports the dealt card and the
    coalition trace reports ord0. *)
Lemma mu2_content_trace_neq :
  mu2_content_trace [set ord0] true (1%g : pgg_gT pgl27_M)
  <> pgl27_coalition_trace R [set ord0] (true, (1%g : pgg_gT pgl27_M)).
Proof.
move=> /ffunP /(_ (@Ordinal 8 1 isT)).
rewrite /mu2_content_trace /pgl27_coalition_trace [LHS]ffunE [RHS]ffunE.
rewrite pgl27_seat_contentE (pgl27_player_trace_E R (@Ordinal 8 1 isT)).
rewrite in_set1.
by rewrite /= perm1 (tnth_nth ord0) /=.
Qed.

(******************************************************************************)
(*     M3: the fixed secret is load-bearing                                   *)
(******************************************************************************)

(** mu3_control — two fixed secrets give executed coalition distributions
    within 2^-39.
    @composes: mu3_prior_attempt *)
Definition mu3_control (C : {set 'I_8}) (s s' : bool) : (#|C| <= 3)%N ->
  var_dist
    (@sa_coalition_dist R mpP (pgl27_exec_plug R)
       (pgl27_fixed_word_sample s) 0 C)
    (@sa_coalition_dist R mpP (pgl27_exec_plug R)
       (pgl27_fixed_word_sample s') 0 C)
  <= 2%:R^-39 :=
  ltac:(move=> HC;
        rewrite (pgl27_fixed_word_coalition_distE C s)
                (pgl27_fixed_word_coalition_distE C s');
        exact: pgl27_word_view_indist).

(** mu3_same_secret — with the same secret on both sides the miniature
    degenerates to the positivity of 2^-39.
    @main architecture: the s = s' instance holds with no reference to the
    shuffle, so the two-secret form of mu3_control is the contentful one. *)
Lemma mu3_same_secret (C : {set 'I_8}) (s : bool) : (#|C| <= 3)%N ->
  var_dist
    (@sa_coalition_dist R mpP (pgl27_exec_plug R)
       (pgl27_fixed_word_sample s) 0 C)
    (@sa_coalition_dist R mpP (pgl27_exec_plug R)
       (pgl27_fixed_word_sample s) 0 C)
  <= 2%:R^-39.
Proof.
move=> _.
have -> : var_dist
    (@sa_coalition_dist R mpP (pgl27_exec_plug R)
       (pgl27_fixed_word_sample s) 0 C)
    (@sa_coalition_dist R mpP (pgl27_exec_plug R)
       (pgl27_fixed_word_sample s) 0 C)
  = 0 by rewrite /var_dist; apply: big1 => a _; rewrite subrr normr0.
by rewrite invr_ge0 exprn_ge0.
Qed.

(* M3a: the arbitrary-prior model pgl27_word_sample averages the two secrets,
   so its coalition distribution is not the fixed-secret pushforward the
   miniature compares.  Rejected with

     Cannot apply lemma pgl27_word_view_indist *)
Fail Definition mu3_prior_attempt (secretP : R.-fdist bool) (C : {set 'I_8})
    (s' : bool) :
  (#|C| <= 3)%N ->
  var_dist
    (@sa_coalition_dist R mpP (pgl27_exec_plug R)
       (pgl27_word_sample secretP) 0 C)
    (@sa_coalition_dist R mpP (pgl27_exec_plug R)
       (pgl27_fixed_word_sample s') 0 C)
  <= 2%:R^-39 :=
  ltac:(move=> HC;
        rewrite (pgl27_fixed_word_coalition_distE C s');
        exact: pgl27_word_view_indist).

(* M3b: the same substitution is rejected one level down, in the distribution
   identity the miniature rewrites by.  Rejected with

     Cannot apply lemma (pgl27_fixed_word_coalition_distE C true) *)
Fail Definition mu3_prior_rewrite (secretP : R.-fdist bool)
    (C : {set 'I_8}) :
  @sa_coalition_dist R mpP (pgl27_exec_plug R) (pgl27_word_sample secretP) 0 C
  = fdistmap (fun g => pgl27_view R C (true, g)) (rho_word R) :=
  ltac:(exact: (pgl27_fixed_word_coalition_distE C true)).

End d2_mutations.

Print Assumptions mu1_control.
Print Assumptions mu2_control.
Print Assumptions mu2_content_trace_neq.
Print Assumptions mu3_control.
Print Assumptions mu3_same_secret.
