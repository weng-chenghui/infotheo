(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_word_privacy: coalition privacy of the eight-card orbit scheme under *)
(* the two-hundred-letter word shuffle                                        *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_word_run_recovers == decoding the executed endpoints returns the   *)
(*     dealt secret, for every two-hundred-letter generator word              *)
(*   pgl27_view_law_classes == at most three positions see the same law of    *)
(*     the uniformly shuffled deal in both orbit classes                      *)
(*   pgl27_word_view_indist == two secrets give coalition-view laws within    *)
(*     2^-39 in variation distance under the word shuffle                     *)
(*   pgl27_word_trace_indist == the same for the executed coalition trace     *)
(*   pgl27_view_mixing == the joint view-and-secret law under the word        *)
(*     shuffle is within 2^-40 of the product of its exact-shuffle marginals, *)
(*     for every Boolean prior                                                *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import primitive_action.
From mathcomp Require Import order ssralg ssrnum boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_collusion_bound.
From pgg_smc Require Import pgg_weighted_words.
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_profile pgl27_scheme.
From pgg_smc Require Import card_exchange_pismc pgg_input_commitment pgg_run.
From pgg_reconstruct Require Import covering_scheme pgg_sharing_framework.
From pgg_reconstruct Require Import transitivity_privacy.
From pgg_smc Require Import pgl27_run pgl27_secrecy pgl27_trace pgl27_mixing.
Require Import smc_interpreter pismc smc_session_types.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Notation pgl27_Msym := (Gen_PGGTypes pgl27_sym_sigmas).

(** pgl27_word_run_recovers — the executed endpoints of a run whose shuffle is
    the product of a two-hundred-letter generator word decode to the dealt
    secret.
    @main correctness: correctness under the word shuffle is exact and holds
    at probability one. *)
Corollary pgl27_word_run_recovers (s : bool) (w : 200.-tuple 'I_5) :
  ts_recon orbit_scheme
    (tcast (pgl27_endpoints_size s (@word_eval pgl27_Msym 200 w))
       (in_tuple (endpoints_of_trace
          (nth [::] (run_interp pgl27_fuel
             (pgl27_procs s (@word_eval pgl27_Msym 200 w))).2 1))))
  = s.
Proof.
apply: pgl27_run_recovers; exact: pgl27_mixing.word_eval_in_G.
Qed.

Section pgl27_word_privacy.
Variable R : realType.

(** rho_word — the law of the product of two hundred independent uniform
    letters of the symmetrized five-letter generator alphabet.
    @intent: the realistic word shuffle law on PGL(2,7). *)
Definition rho_word : R.-fdist (pgg_gT pgl27_M) :=
  @rho_from_words_weighted R 6 4 200 pgl27_sym_sigmas (Wuni R).

(** pgl27P_gen — the joint law of a secret drawn from secretP and an
    independent uniform PGL(2,7) shuffle.
    @intent: the exact-shuffle sample space at an arbitrary Boolean prior. *)
Definition pgl27P_gen (secretP : R.-fdist bool)
    : R.-fdist (bool * pgg_gT pgl27_M)%type := secretP `x (`U pgl27_G_pos).

(** pgl27P_word_gen — the joint law of a secret drawn from secretP and an
    independent word shuffle.
    @intent: the word-shuffle sample space at an arbitrary Boolean prior. *)
Definition pgl27P_word_gen (secretP : R.-fdist bool)
    : R.-fdist (bool * pgg_gT pgl27_M)%type := secretP `x rho_word.

(** pgl27_equianharmonic_view — the coalition's observation at shuffle g when
    the dealt deck is the equianharmonic representative orbit_encode true.
    @intent: the equianharmonic branch of the coalition observable. *)
Definition pgl27_equianharmonic_view (C : {set 'I_8}) (g : pgg_gT pgl27_M)
    : {ffun 'I_8 -> 'I_8} := pgl27_view R C (true, g).

(** pgl27_harmonic_view — the coalition's observation at shuffle g when the
    dealt deck is the harmonic representative orbit_encode false.
    @intent: the harmonic branch of the coalition observable. *)
Definition pgl27_harmonic_view (C : {set 'I_8}) (g : pgg_gT pgl27_M)
    : {ffun 'I_8 -> 'I_8} := pgl27_view R C (false, g).

(** pgl27_view_law_classes — under the uniform PGL(2,7) shuffle, a coalition
    of at most three positions sees the same law whether the dealt deck is the
    equianharmonic representative or the harmonic one.
    @composes: pgl27_view_law_const *)
Lemma pgl27_view_law_classes (C : {set 'I_8}) : (#|C| <= 3)%N ->
  fdistmap (pgl27_equianharmonic_view C)
    (`U pgl27_G_pos : R.-fdist (pgg_gT pgl27_M))
  = fdistmap (pgl27_harmonic_view C)
    (`U pgl27_G_pos : R.-fdist (pgg_gT pgl27_M)).
Proof.
move=> HC.
pose k := size (enum C).
pose p : k.-tuple 'I_8 := in_tuple (enum C).
have Hk : (k <= 3)%N by rewrite /k -cardE.
have Hp : p \in dtuple_on k [set: 'I_8].
  by rewrite inE; apply/andP;
     split; [exact: enum_uniq | apply/subsetP => x _; rewrite inE].
have Hdt : (0 < #|dtuple_on k [set: 'I_8]|)%N by apply/card_gt0P; exists p.
pose maskf := fun r : k.-tuple 'I_8 =>
  [ffun i : 'I_8 => nth ord0 (val r) (index i (enum C))].
have Hone : forall b : bool,
    fdistmap (fun g : pgg_gT pgl27_M => pgl27_view R C (b, g))
      (`U pgl27_G_pos : R.-fdist (pgg_gT pgl27_M))
    = fdistmap maskf (`U Hdt : R.-fdist (k.-tuple 'I_8)).
  move=> b.
  have Hcomp : (fun g : pgg_gT pgl27_M => pgl27_view R C (b, g))
      = maskf \o (fun g : pgg_gT pgl27_M =>
          [tuple tnth (orbit_encode b) (@pgg_rho pgl27_M g (tnth p l)) | l < k]).
    apply: boolp.funext => g; apply/ffunP => i.
    rewrite /= /maskf ffunE /pgl27_view ffunE.
    case Hi: (i \in C).
      have Hmem : i \in enum C by rewrite mem_enum Hi.
      have Hj : (index i (enum C) < k)%N by rewrite /k index_mem.
      rewrite -(tnth_nth ord0 _ (Ordinal Hj)) tnth_mktuple.
      have -> : tnth p (Ordinal Hj) = i by rewrite (tnth_nth i) nth_index.
      by [].
    have Hni : i \notin enum C by rewrite mem_enum Hi.
    have Hidx : index i (enum C) = k.
      apply/eqP; rewrite eqn_leq; apply/andP.
      by split; [rewrite /k; exact: index_size | rewrite /k leqNgt index_mem].
    by rewrite Hidx nth_default // size_tuple.
  rewrite Hcomp -fdistmap_comp.
  by rewrite (@ktuple_encode_uniform (pgg_N' pgl27_M) (pgg_gT pgl27_M)
    (pgg_G pgl27_M) (@pgg_rho pgl27_M) 3 pgl27_3transitive R pgl27_G_pos
    orbit_encode k p b Hdt Hk (orbit_encode_deck b) Hp).
by rewrite /pgl27_equianharmonic_view /pgl27_harmonic_view
  (Hone true) (Hone false).
Qed.

(** pgl27_view_law_const — under the uniform PGL(2,7) shuffle the law of the
    view of a coalition of at most three positions does not depend on the
    dealt secret.
    @composes: pgl27_word_view_indist *)
Corollary pgl27_view_law_const (C : {set 'I_8}) (s s' : bool) : (#|C| <= 3)%N ->
  fdistmap (fun g : pgg_gT pgl27_M => pgl27_view R C (s, g))
    (`U pgl27_G_pos : R.-fdist (pgg_gT pgl27_M))
  = fdistmap (fun g : pgg_gT pgl27_M => pgl27_view R C (s', g))
    (`U pgl27_G_pos : R.-fdist (pgg_gT pgl27_M)).
Proof.
by move=> HC; case: s; case: s'; rewrite ?(pgl27_view_law_classes HC).
Qed.

(* Two halves of 2^-40 make 2^-39.  The mulr_natl and mulr_natr routes fail
   here because the ring numeral 2 is itself a natmul and the rewrite fires
   inside it, yielding (2 * 1) ^- 40. *)
Let pow2_split : (2%:R : R)^-40 + 2%:R^-40 = 2%:R^-39.
Proof. by rewrite [RHS]splitr exprSr invfM. Qed.

(** pgl27_word_view_indist — under the two-hundred-letter word shuffle the
    coalition-view laws of two secrets are within 2^-39 in variation distance,
    for every coalition of at most three positions.
    @main security: statistical coalition privacy under the realistic
    shuffle. *)
Theorem pgl27_word_view_indist (C : {set 'I_8}) (s s' : bool) :
  (#|C| <= 3)%N ->
  var_dist (fdistmap (fun g => pgl27_view R C (s, g)) rho_word)
           (fdistmap (fun g => pgl27_view R C (s', g)) rho_word)
  <= 2%:R^-39.
Proof.
move=> HC.
apply: (Order.POrderTheory.le_trans (var_dist_triangle _
  (fdistmap (fun g => pgl27_view R C (s, g)) (`U pgl27_G_pos)) _)).
rewrite -pow2_split; apply: lerD.
- apply: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _)).
  exact: pgl27_word_mixing.
- rewrite (pgl27_view_law_const (C:=C) s s' HC) symmetric_var_dist.
  apply: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _)).
  exact: pgl27_word_mixing.
Qed.

(** pgl27_word_trace_indist — under the two-hundred-letter word shuffle the
    executed coalition traces of two secrets are within 2^-39 in variation
    distance, for every coalition of at most three positions.
    @main security: the coalition-view bound transported to the executed
    interpreter trace. *)
Theorem pgl27_word_trace_indist (C : {set 'I_8}) (s s' : bool) :
  (#|C| <= 3)%N ->
  var_dist (fdistmap (fun g => pgl27_coalition_trace R C (s, g)) rho_word)
           (fdistmap (fun g => pgl27_coalition_trace R C (s', g)) rho_word)
  <= 2%:R^-39.
Proof.
by rewrite (pgl27_coalition_trace_E R C); exact: pgl27_word_view_indist.
Qed.

(** pgl27_view_indep_gen — at every Boolean prior, a coalition of at most
    three positions has a view of the uniformly shuffled dealt arrangement
    independent of the orbit secret.
    @composes: pgl27_view_mixing *)
Lemma pgl27_view_indep_gen (secretP : R.-fdist bool) (C : {set 'I_8}) :
  (#|C| <= 3)%N -> pgl27P_gen secretP |= pgl27_view R C _|_ pgl27_secret R.
Proof.
move=> HC.
exact: (@ttrans_view_indep_gen (pgg_N' pgl27_M) (pgg_gT pgl27_M) (pgg_G pgl27_M)
  (@pgg_rho pgl27_M) 3 pgl27_3transitive R secretP pgl27_G_pos
  orbit_encode C HC orbit_encode_deck).
Qed.

(** pgl27_view_mixing — at every Boolean prior, the joint view-and-secret law
    under the two-hundred-letter word shuffle is within 2^-40 of the product
    of the two exact-shuffle marginals.
    @main bound: proximity of the word-shuffle joint law to the ideal
    independent execution. *)
Theorem pgl27_view_mixing (secretP : R.-fdist bool) (C : {set 'I_8}) :
  (#|C| <= 3)%N ->
  var_dist (fdistmap (fun u => (pgl27_view R C u, pgl27_secret R u))
                     (pgl27P_word_gen secretP))
           ((fdistmap (pgl27_view R C) (pgl27P_gen secretP))
              `x (fdistmap (pgl27_secret R) (pgl27P_gen secretP)))
  <= 2%:R^-40.
Proof.
move=> HC; rewrite -(inde_dist_of_RV2 (pgl27_view_indep_gen secretP HC)).
apply: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _)).
exact: (pgl27_joint_mixing secretP).
Qed.

End pgl27_word_privacy.
