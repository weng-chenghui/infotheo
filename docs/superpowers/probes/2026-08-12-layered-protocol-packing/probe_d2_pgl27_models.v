(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* probe_d2_pgl27_models: the two fixed-secret PGL(2,7) sample models, the    *)
(* finite executed content reader, and the executed 2^-39 miniatures          *)
(*                                                                            *)
(* Probe unit D2 of the 2026-08-12 layered-protocol-packing gate: the PGL     *)
(* half of section 15.5.  Everything is stated over the landed                *)
(* R-parameterized API of pgl27_exec.v, pgl27_trace.v, pgl27_secrecy.v,       *)
(* pgl27_profile.v and pgl27_word_privacy.v.                                  *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   pgl27_fixed_sample        == the exact-shuffle sample adapter at a fixed *)
(*                                secret: uniform PGL(2,7) cuts, the run      *)
(*                                argument constant                           *)
(*   pgl27_fixed_word_sample   == the word-shuffle sample adapter at a fixed  *)
(*                                secret: two-hundred-letter words, the cut   *)
(*                                the evaluated word                          *)
(*   pgl27_exec_content_trace  == the coalition's executed trace read through *)
(*                                content_of, a finite {ffun 'I_8 -> 'I_8}    *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_fixed_cut_distE      == the fixed-secret exact model's cut         *)
(*                                 distribution is the uniform shuffle        *)
(*   pgl27_fixed_word_cut_distE == the fixed-secret word model's cut          *)
(*                                 distribution is rho_word                   *)
(*   pgl27_exec_rowE            == the executed participant trace at          *)
(*                                 seat i is the interpreter row at           *)
(*                                 process 2 + i                              *)
(*   pgl27_content_traceE       == the executed content reader is the landed  *)
(*                                 coalition trace random variable            *)
(*   pgl27_static_coalition_viewE == the executed coalition endpoints are the *)
(*                                 static coalition view                      *)
(*   pgl27_fixed_word_coalition_distE == the executed coalition distribution  *)
(*                                 of the fixed-secret word model is the      *)
(*                                 pushforward of rho_word along the static   *)
(*                                 view                                       *)
(*   pgl27_fixed_word_content_trace_distE == the same for the                 *)
(*                                 executed content trace                     *)
(*   pgl27_word_joint_viewE     == the joint executed view-and-secret         *)
(*                                 distribution over the arbitrary-prior word *)
(*                                 sample is the static joint distribution    *)
(*                                 pgl27_view_mixing is stated at             *)
(*   pgl27_exec_view_indist     == two fixed secrets give executed coalition  *)
(*                                 distributions within 2^-39                 *)
(*   pgl27_exec_trace_indist    == the same for the executed content trace    *)
(*   pgl27_exact_coalition_distE == the exact model's executed coalition      *)
(*                                 distribution is the pushforward of pgl27P  *)
(*                                 along the static view                      *)
(*   pgl27_exec_exact_view_indep == the executed coalition                    *)
(*                                 observation and the orbit secret           *)
(*                                 have a product joint distribution          *)
(*                                 at three cards                             *)
(*                                                                            *)
(* The import of pgl27_trace is the one edge this probe adds beyond the cone  *)
(* of pgl27_exec: content_of, pgl27_player_trace and pgl27_coalition_trace    *)
(* live there.  pgl27_trace does not import pgl27_exec, and this file is a    *)
(* leaf, so the edge is acyclic.                                              *)
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

Section d2_pgl27_models.

Variable R : realType.

Let mpP : MonodromyProfile R := pgl27_profile R.

(******************************************************************************)
(*     Part 1: the two fixed-secret sample models                             *)
(******************************************************************************)

(* The two landed models are not reproved here: pgl27_sample is the exact
   model at the uniform secret prior, with cut distribution
   pgl27_sample_cut_distE, and pgl27_word_sample secretP is the word model at
   an arbitrary secret prior, with cut distribution pgl27_word_cut_distE. *)
Check (pgl27_sample R).
Check (@pgl27_sample_cut_distE R).
Check (@pgl27_word_cut_distE R).

(** pgl27_fixed_sample — the exact model at a fixed secret.
    @intent: the sample layer over pgl27_exec_plug whose sample space is the
    group pgg_gT pgl27_M under the uniform distribution, the run argument the
    constant s and the cut the sampled group element. *)
Definition pgl27_fixed_sample (s : bool) : SampleAdapter (pgl27_exec_plug R) :=
  @MkSampleAdapter R mpP (pgl27_exec_plug R)
    (pgg_gT pgl27_M : finType) (`U pgl27_G_pos) (fun _ => s) idfun.

(** pgl27_fixed_word_sample — the word model at a fixed secret.
    @intent: the sample layer over pgl27_exec_plug whose sample space is the
    two-hundred-letter words under pgl27_word_wordP, the run argument the
    constant s and the cut the evaluated word. *)
Definition pgl27_fixed_word_sample (s : bool)
    : SampleAdapter (pgl27_exec_plug R) :=
  @MkSampleAdapter R mpP (pgl27_exec_plug R)
    [the finType of (200.-tuple 'I_5)%type] (pgl27_word_wordP R) (fun _ => s)
    (fun w => @word_eval pgl27_Msym 200 w).

(** pgl27_fixed_cut_distE — the fixed-secret exact model draws its cut
    uniformly from the group.
    @main architecture: sa_cut_dist (pgl27_fixed_sample s) = `U pgl27_G_pos. *)
Lemma pgl27_fixed_cut_distE (s : bool) :
  @sa_cut_dist R mpP (pgl27_exec_plug R) (pgl27_fixed_sample s)
  = (`U pgl27_G_pos : R.-fdist (pgg_gT pgl27_M)).
Proof. rewrite /sa_cut_dist /=; exact: fdistmap_id. Qed.

(** pgl27_fixed_word_cut_distE — the fixed-secret word model draws its cut
    from the word shuffle.
    @main architecture: sa_cut_dist (pgl27_fixed_word_sample s) = rho_word. *)
Lemma pgl27_fixed_word_cut_distE (s : bool) :
  @sa_cut_dist R mpP (pgl27_exec_plug R) (pgl27_fixed_word_sample s)
  = rho_word R.
Proof.
by rewrite /sa_cut_dist /rho_word /rho_from_words_weighted /pgl27_word_wordP.
Qed.

(** pgl27_word_rho_wordE — the image of the word distribution under word
    evaluation is the word shuffle.
    @composes: pgl27_fixed_word_content_trace_distE *)
Lemma pgl27_word_rho_wordE :
  fdistmap (fun w : 200.-tuple 'I_5 => @word_eval pgl27_Msym 200 w)
    (pgl27_word_wordP R) = rho_word R.
Proof. exact: (pgl27_fixed_word_cut_distE false). Qed.

(******************************************************************************)
(*     Part 2: the finite executed content reader                             *)
(******************************************************************************)

(** pgl27_exec_content_trace — the coalition's executed trace read through
    content_of.
    @intent: the finfun sending a seat in C to the content of that seat's
    executed interpreter row and every seat outside C to ord0; the seat index
    type of the profile is 'I_8 by pgl27_exec_seat_countE, so no transport is
    needed between the execution layer and the eight-seat coalition view. *)
Definition pgl27_exec_content_trace (C : {set 'I_8}) (s : bool)
    (w0 : pgg_gT pgl27_M) : {ffun 'I_8 -> 'I_8} :=
  [ffun i => if i \in C
             then content_of
                    (@exec_participant_trace R mpP (pgl27_exec_plug R) s w0 0 i)
             else ord0].

(** pgl27_exec_rowE — the executed participant trace at seat i is the
    interpreter row of pgl27_procs at process 2 + i.
    @composes: pgl27_content_traceE *)
Lemma pgl27_exec_rowE (s : bool) (w0 : pgg_gT pgl27_M) (i : 'I_8) :
  @exec_participant_trace R mpP (pgl27_exec_plug R) s w0 0 i
  = nth [::] (run_interp pgl27_fuel (pgl27_procs s w0)).2 (2 + i).
Proof.
(* The landed pgl27_exec_raw_traceE is stated at the folded constant
   pgl27_exec_player_raw_trace.  Folding first is essential: applying the
   landed lemma directly to the unfolded row leaves R undetermined and sends
   the unifier into the interpreter. *)
have -> : @exec_participant_trace R mpP (pgl27_exec_plug R) s w0 0 i
        = pgl27_exec_player_raw_trace (R:=R) s w0 i by exact: erefl.
exact: (@pgl27_exec_raw_traceE R s w0 i).
Qed.

(** pgl27_content_traceE — the executed content reader is the landed coalition
    trace random variable.
    @main architecture: pgl27_exec_content_trace C u.1 u.2 =
    pgl27_coalition_trace C u. *)
Lemma pgl27_content_traceE (C : {set 'I_8}) (u : bool * pgg_gT pgl27_M) :
  pgl27_exec_content_trace C u.1 u.2 = pgl27_coalition_trace R C u.
Proof.
apply/ffunP => i.
rewrite /pgl27_exec_content_trace /pgl27_coalition_trace.
(* An unscoped rewrite ffunE diverges here: the occurrence search reaches
   inside the finfun body and evaluates the interpreter.  The [LHS]/[RHS]
   scoped form fires immediately. *)
rewrite [LHS]ffunE [RHS]ffunE.
case Hi: (i \in C); last by [].
rewrite pgl27_exec_rowE.
by rewrite /pgl27_player_trace.
Qed.

(******************************************************************************)
(*     Part 3: the executed endpoints against the static view                 *)
(******************************************************************************)

(** pgl27_static_coalition_viewE — the executed coalition endpoints are the
    static coalition view.
    @main architecture: exec_coalition_endpoints s w0 0 C = pgl27_view C
    (s, w0). *)
Lemma pgl27_static_coalition_viewE (C : {set 'I_8}) (s : bool)
    (w0 : pgg_gT pgl27_M) :
  @exec_coalition_endpoints R mpP (pgl27_exec_plug R) s w0 0 C
  = pgl27_view R C (s, w0).
Proof.
rewrite (@pgl27_exec_coalition_endpointsE R s w0 C).
apply/ffunP => i; rewrite /pgl27_view [LHS]ffunE [RHS]ffunE.
(* ts_encode orbit_scheme is orbit_encode by projection, and the profile's
   starting tuple is ord_tuple 8, so the start of seat i is i itself. *)
by case: ifP => // _; rewrite /pgl27_content_obs /= tnth_ord_tuple.
Qed.

(******************************************************************************)
(*     Part 4: the fixed-secret distribution equalities                       *)
(******************************************************************************)

(** pgl27_fixed_word_coalition_distE — the executed coalition distribution of
    the fixed-secret word model is the pushforward of the word shuffle along
    the static view at secret s.
    @main architecture: sa_coalition_dist (pgl27_fixed_word_sample s) 0 C =
    fdistmap (fun g => pgl27_view C (s, g)) rho_word. *)
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
by rewrite
   -/(@sa_cut_dist R mpP (pgl27_exec_plug R) (pgl27_fixed_word_sample s))
   pgl27_fixed_word_cut_distE.
Qed.

(** pgl27_fixed_word_content_trace_distE — the executed content trace of the
    fixed-secret word model has the distribution of the landed coalition trace
    under the word shuffle.
    @main architecture: fdistmap (fun w => pgl27_exec_content_trace C s
    (word_eval w)) pgl27_word_wordP = fdistmap (fun g => pgl27_coalition_trace
    C (s, g)) rho_word. *)
Lemma pgl27_fixed_word_content_trace_distE (C : {set 'I_8}) (s : bool) :
  fdistmap (fun w : 200.-tuple 'I_5 =>
              pgl27_exec_content_trace C s (@word_eval pgl27_Msym 200 w))
    (pgl27_word_wordP R)
  = fdistmap (fun g => pgl27_coalition_trace R C (s, g)) (rho_word R).
Proof.
have Hmap : (fun w : 200.-tuple 'I_5 =>
               pgl27_exec_content_trace C s (@word_eval pgl27_Msym 200 w))
          = (fun g : pgg_gT pgl27_M => pgl27_coalition_trace R C (s, g))
            \o (fun w : 200.-tuple 'I_5 => @word_eval pgl27_Msym 200 w).
  apply: boolp.funext => w.
  exact: (pgl27_content_traceE C (s, @word_eval pgl27_Msym 200 w)).
rewrite Hmap.
rewrite -(fdistmap_comp
            (fun g : pgg_gT pgl27_M => pgl27_coalition_trace R C (s, g))
            (fun w : 200.-tuple 'I_5 => @word_eval pgl27_Msym 200 w)).
by rewrite pgl27_word_rho_wordE.
Qed.

(** pgl27_word_joint_viewE — the joint executed view-and-secret distribution
    over the arbitrary-prior word sample is the static joint distribution
    pgl27_view_mixing is stated at.
    @main architecture: fdistmap (fun u => (exec_coalition_endpoints u.1
    (word_eval u.2) 0 C, u.1)) pgl27_word_sampleP = fdistmap (fun v =>
    (pgl27_view C v, pgl27_secret v)) (pgl27P_word_gen secretP). *)
Lemma pgl27_word_joint_viewE (secretP : R.-fdist bool) (C : {set 'I_8}) :
  fdistmap (fun u : bool * 200.-tuple 'I_5 =>
              (@exec_coalition_endpoints R mpP (pgl27_exec_plug R) u.1
                 (@word_eval pgl27_Msym 200 u.2) 0 C, u.1))
    (@pgl27_word_sampleP R secretP)
  = fdistmap (fun v : bool * pgg_gT pgl27_M =>
                (pgl27_view R C v, pgl27_secret R v))
      (pgl27P_word_gen secretP).
Proof.
have Hmap : (fun u : bool * 200.-tuple 'I_5 =>
               (@exec_coalition_endpoints R mpP (pgl27_exec_plug R) u.1
                  (@word_eval pgl27_Msym 200 u.2) 0 C, u.1))
          = (fun v : bool * pgg_gT pgl27_M =>
               (pgl27_view R C v, pgl27_secret R v))
            \o (fun u : bool * 200.-tuple 'I_5 =>
                  (u.1, @word_eval pgl27_Msym 200 u.2)).
  apply: boolp.funext => u /=.
  by rewrite
    (pgl27_static_coalition_viewE C u.1 (@word_eval pgl27_Msym 200 u.2)).
rewrite Hmap.
rewrite -(fdistmap_comp (fun v : bool * pgg_gT pgl27_M =>
                           (pgl27_view R C v, pgl27_secret R v))
                        (fun u : bool * 200.-tuple 'I_5 =>
                           (u.1, @word_eval pgl27_Msym 200 u.2))).
rewrite -(pgl27_word_sample_joint_distE secretP).
by rewrite /sa_joint_dist.
Qed.

(******************************************************************************)
(*     Part 5: the executed 2^-39 miniatures and the exact bridge             *)
(******************************************************************************)

(** pgl27_exec_view_indist — two fixed secrets give executed coalition
    distributions within 2^-39 in variation distance, at three cards.
    @main security: the word-shuffle coalition-privacy bound stated over the
    executed sample layer. *)
Lemma pgl27_exec_view_indist (C : {set 'I_8}) (s s' : bool) : (#|C| <= 3)%N ->
  var_dist
    (@sa_coalition_dist R mpP (pgl27_exec_plug R)
       (pgl27_fixed_word_sample s) 0 C)
    (@sa_coalition_dist R mpP (pgl27_exec_plug R)
       (pgl27_fixed_word_sample s') 0 C)
  <= 2%:R^-39.
Proof.
move=> HC.
rewrite (pgl27_fixed_word_coalition_distE C s)
        (pgl27_fixed_word_coalition_distE C s').
exact: pgl27_word_view_indist.
Qed.

(** pgl27_exec_trace_indist — two fixed secrets give executed content-trace
    distributions within 2^-39 in variation distance, at three cards.
    @main security: the word-shuffle trace-privacy bound stated over the
    executed content reader. *)
Lemma pgl27_exec_trace_indist (C : {set 'I_8}) (s s' : bool) : (#|C| <= 3)%N ->
  var_dist
    (fdistmap (fun w : 200.-tuple 'I_5 =>
                 pgl27_exec_content_trace C s (@word_eval pgl27_Msym 200 w))
       (pgl27_word_wordP R))
    (fdistmap (fun w : 200.-tuple 'I_5 =>
                 pgl27_exec_content_trace C s' (@word_eval pgl27_Msym 200 w))
       (pgl27_word_wordP R))
  <= 2%:R^-39.
Proof.
move=> HC.
rewrite (pgl27_fixed_word_content_trace_distE C s)
        (pgl27_fixed_word_content_trace_distE C s').
exact: pgl27_word_trace_indist.
Qed.

(** pgl27_exact_coalition_distE — the exact model's executed coalition
    distribution is the pushforward of pgl27P along the static view.
    @main architecture: sa_coalition_dist pgl27_sample 0 C = fdistmap
    (pgl27_view C) pgl27P. *)
Lemma pgl27_exact_coalition_distE (C : {set 'I_8}) :
  @sa_coalition_dist R mpP (pgl27_exec_plug R) (pgl27_sample R) 0 C
  = fdistmap (pgl27_view R C) (pgl27P R).
Proof.
rewrite /sa_coalition_dist; congr fdistmap.
by apply: boolp.funext => u; exact: (pgl27_static_coalition_viewE C u.1 u.2).
Qed.

(** pgl27_exec_exact_view_indep — at three cards the executed coalition
    observation of the exact model and the orbit secret have a product joint
    distribution.
    @main security: pgl27_view_indep read over the executed sample layer. *)
Corollary pgl27_exec_exact_view_indep (C : {set 'I_8}) : (#|C| <= 3)%N ->
  fdistmap (fun u => (pgl27_view R C u, pgl27_secret R u)) (pgl27P R)
  = ((@sa_coalition_dist R mpP (pgl27_exec_plug R) (pgl27_sample R) 0 C)
     `x (fdistmap (pgl27_secret R) (pgl27P R)))%fdist.
Proof.
move=> HC; rewrite pgl27_exact_coalition_distE.
exact: (inde_dist_of_RV2 (pgl27_view_indep R (C:=C) HC)).
Qed.

End d2_pgl27_models.

(******************************************************************************)
(*     Axiom hygiene                                                          *)
(******************************************************************************)

Print Assumptions pgl27_fixed_cut_distE.
Print Assumptions pgl27_fixed_word_cut_distE.
Print Assumptions pgl27_content_traceE.
Print Assumptions pgl27_static_coalition_viewE.
Print Assumptions pgl27_fixed_word_coalition_distE.
Print Assumptions pgl27_fixed_word_content_trace_distE.
Print Assumptions pgl27_word_joint_viewE.
Print Assumptions pgl27_exec_view_indist.
Print Assumptions pgl27_exec_trace_indist.
Print Assumptions pgl27_exec_exact_view_indep.
