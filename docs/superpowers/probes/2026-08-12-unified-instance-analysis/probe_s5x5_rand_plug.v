(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* probe_s5x5_rand_plug: the S_5 x S_5 randomized security plug               *)
(*                                                                            *)
(* Phase 0 probe for the unified-instance-analysis request, sections 6.3, 6.4 *)
(* and 8.1. The randomized execution path of s5x5_profile carries an          *)
(* ExecutionPlug whose run argument is the product sampler tape               *)
(* 'rV['Z_5]_5 * 'rV['Z_5]_5 and whose content readout is the                 *)
(* probability-free two-pile layout s5x5_rfree_layout. The run skeleton       *)
(* s5x5_aprocs_cut generalizes s5x5_trace.s5x5_aprocs_abs to an arbitrary     *)
(* cut; its identity-cut specialization is s5x5_rprocs.                       *)
(*                                                                            *)
(* The reconstruction proof does not use ts_valid s5x5_scheme. An arbitrary   *)
(* product tape does not satisfy product_valid at the combine_secret image    *)
(* of its two pile secrets, because split_combineK is partial. The proof      *)
(* instead reduces the product reconstruction to its two factor sum           *)
(* reconstructions and reindexes each pile by the pile-preserving monodromy.  *)
(*                                                                            *)
(* Build order: probe_s5x5_det_plug.v and probe_s5_rand_plug.v first.         *)
(*                                                                            *)
(* Probe claims:                                                             *)
(*   s5x5_rfree_layoutE    == the probability-free layout is s5x5_rlayout     *)
(*   s5x5_rprocs_cut1      == the identity cut specializes to s5x5_rprocs     *)
(*   s5x5_rand_terminates  == the randomized run reaches Finish at 12 procs   *)
(*   s5x5_rand_endpoints   == the randomized endpoints are the static reading *)
(*   s5x5_rand_run_recovers == reconstruction returns combine_secret of the   *)
(*                             two pile secrets                               *)
(*   s5x5_rand_observed    == the packaged ObservedExecution                  *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals zmodp matrix.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_reconstruct Require Import product_threshold.
From pgg_smc Require Import pgg_leakage_witness pgg_randomized_sharing.
From pgg_smc Require Import pgg_canonical_sharing pgg_sharing_mechanism.
From pgg_smc Require Import pgg_trace_secrecy.
From pgg_smc Require Import pgg_s5x5 s5x5_pile rigidity_s5x5_instance.
From pgg_smc Require Import s5x5_profile s5x5_run s5x5_trace.
From uia_probe Require Import probe_s5_rand_plug probe_s5x5_det_plug.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Section s5x5_randomized_execution.

Let mpX : MonodromyProfile := s5x5_profile.

(******************************************************************************)
(*     The two pile index embeddings                                          *)
(******************************************************************************)

(** p1_idx — the seat of pile-1 party i.
    @intent: the ten-seat index of the i-th first-pile party, of value i. *)
Definition p1_idx (i : 'I_5) : 'I_10 := widen_ord (isT : (5 <= 10)%N) i.

(** p1_idx_val — the seat of pile-1 party i has value i.
    @composes: s5x5_pile1_sharesE *)
Lemma p1_idx_val (i : 'I_5) : p1_idx i = i :> nat.
Proof. by []. Qed.

(** p2_idx_lt — the ten-seat bound of the i-th second-pile party.
    @composes: p2_idx *)
Lemma p2_idx_lt (i : 'I_5) : (5 + i < 10)%N.
Proof. by rewrite -[10]/(5 + 5) ltn_add2l; exact: ltn_ord. Qed.

(** p2_idx — the seat of pile-2 party i.
    @intent: the ten-seat index of the i-th second-pile party, of value
    5 + i. *)
Definition p2_idx (i : 'I_5) : 'I_10 := Ordinal (p2_idx_lt i).

(** p2_idx_val — the seat of pile-2 party i has value 5 + i.
    @composes: s5x5_pile2_sharesE *)
Lemma p2_idx_val (i : 'I_5) : p2_idx i = (5 + i)%N :> nat.
Proof. by []. Qed.

(** p2_idx_ge — the seat of pile-2 party i lies in the upper half.
    @composes: s5x5_p2_layoutE *)
Lemma p2_idx_ge (i : 'I_5) : (5 <= p2_idx i)%N.
Proof. by rewrite p2_idx_val leq_addr. Qed.

(******************************************************************************)
(*     The probability-free two-pile layout                                   *)
(******************************************************************************)

(** s5x5_rfree_layout — the dealt layout at a product tape, stated without a
    realType.
    @intent: the probability-free twin of s5x5_trace.s5x5_rlayout; seat i below
    five carries the embedded pile-1 share i, seat i at least five carries the
    embedded pile-2 share i - 5. *)
Definition s5x5_rfree_layout (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type)
    : 10.-tuple 'I_10 :=
  [tuple if (i < 5)%N then embed_p1 (s5_rfree_share (inord i) uv.1)
         else embed_p2 (s5_rfree_share (inord (i - 5)) uv.2) | i < 10].

(** s5x5_rfree_layoutE — the probability-free layout is the randomized layout,
    at every realType.
    @composes: s5x5_rprocs_cut1 *)
Lemma s5x5_rfree_layoutE (R : realType)
    (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type) :
  s5x5_rlayout R uv = s5x5_rfree_layout uv.
Proof.
apply: eq_from_tnth => i.
rewrite /s5x5_rlayout /s5x5_rfree_layout !tnth_mktuple.
by rewrite /rs1 /rs2 !s5_rfree_shareE.
Qed.

(******************************************************************************)
(*     The pile codec cancellations                                           *)
(******************************************************************************)

(** project_pile1_val — the pile-1 projection of a product index is its
    residue.
    @composes: project_embed_p1K *)
Lemma project_pile1_val (y : 'I_10) :
  \val (@project_pile1 3 3 y) = (\val y %% 5)%N.
Proof. by []. Qed.

(** project_pile2_val — the pile-2 projection of a product index is the
    residue of its offset.
    @composes: project_embed_p2K *)
Lemma project_pile2_val (y : 'I_10) :
  \val (@project_pile2 3 3 y) = ((\val y - 5) %% 5)%N.
Proof. by []. Qed.

(** embed_p1_val — the pile-1 embedding preserves the value.
    @composes: project_embed_p1K *)
Lemma embed_p1_val (x : 'I_5) : \val (embed_p1 x) = \val x.
Proof.
have Hx10 : (\val x < 10)%N by apply: (leq_trans (ltn_ord x)).
exact: (inordK Hx10).
Qed.

(** embed_p2_val — the pile-2 embedding shifts the value by five.
    @composes: project_embed_p2K *)
Lemma embed_p2_val (x : 'I_5) : \val (embed_p2 x) = (5 + \val x)%N.
Proof.
have Hx10 : (5 + \val x < 10)%N := p2_idx_lt x.
exact: (inordK Hx10).
Qed.

(** project_embed_p1K — the product pile-1 projection cancels the pile-1
    embedding of s5x5_trace.
    @composes: s5x5_p1_layoutE *)
Lemma project_embed_p1K (x : 'I_5) : @project_pile1 3 3 (embed_p1 x) = x.
Proof.
apply: val_inj; rewrite project_pile1_val embed_p1_val.
exact: modn_small (ltn_ord x).
Qed.

(** project_embed_p2K — the product pile-2 projection cancels the pile-2
    embedding of s5x5_trace.
    @composes: s5x5_p2_layoutE *)
Lemma project_embed_p2K (x : 'I_5) : @project_pile2 3 3 (embed_p2 x) = x.
Proof.
apply: val_inj; rewrite project_pile2_val embed_p2_val addKn.
exact: modn_small (ltn_ord x).
Qed.

(******************************************************************************)
(*     The two pile-restricted monodromy maps                                 *)
(******************************************************************************)

(** s5x5_p1_map — the pile-1 restriction of the monodromy at a cut.
    @intent: the five-element reindexing party i of pile 1 undergoes when the
    deck is cut at w0. *)
Definition s5x5_p1_map (w0 : pgg_gT s5x5_M) (i : 'I_5) : 'I_5 :=
  inord (@pgg_rho s5x5_M w0 (p1_idx i)).

(** s5x5_p2_map — the pile-2 restriction of the monodromy at a cut.
    @intent: the five-element reindexing party i of pile 2 undergoes when the
    deck is cut at w0. *)
Definition s5x5_p2_map (w0 : pgg_gT s5x5_M) (i : 'I_5) : 'I_5 :=
  inord (@pgg_rho s5x5_M w0 (p2_idx i) - 5)%N.

(** s5x5_p1_stab — a group cut sends a pile-1 seat to a pile-1 seat.
    @composes: s5x5_p1_map_inj, s5x5_p1_layoutE *)
Lemma s5x5_p1_stab (w0 : pgg_gT s5x5_M) (Hw0 : w0 \in pgg_G s5x5_M)
    (i : 'I_5) : (@pgg_rho s5x5_M w0 (p1_idx i) < 5)%N.
Proof. exact: (@s5x5_pile1_stab w0 Hw0 (p1_idx i) (ltn_ord i)). Qed.

(** s5x5_p2_stab — a group cut sends a pile-2 seat to a pile-2 seat.
    @composes: s5x5_p2_map_inj, s5x5_p2_layoutE *)
Lemma s5x5_p2_stab (w0 : pgg_gT s5x5_M) (Hw0 : w0 \in pgg_G s5x5_M)
    (i : 'I_5) : (5 <= @pgg_rho s5x5_M w0 (p2_idx i))%N.
Proof.
have H1 : ~~ (p2_idx i < 5)%N by rewrite -leqNgt; exact: p2_idx_ge.
have H2 : ~~ (@pgg_rho s5x5_M w0 (p2_idx i) < 5)%N
  := @s5x5_preserves_pile2_proved w0 Hw0 (p2_idx i) H1.
by rewrite leqNgt.
Qed.

(** s5x5_p2_stab_sub — the offset image of a pile-2 seat is a pile index.
    @composes: s5x5_p2_map_inj, s5x5_p2_layoutE *)
Lemma s5x5_p2_stab_sub (w0 : pgg_gT s5x5_M) (Hw0 : w0 \in pgg_G s5x5_M)
    (i : 'I_5) : (@pgg_rho s5x5_M w0 (p2_idx i) - 5 < 5)%N.
Proof.
rewrite -(ltn_add2r 5) (subnK (s5x5_p2_stab Hw0 i)).
exact: (ltn_ord (@pgg_rho s5x5_M w0 (p2_idx i))).
Qed.

(** s5x5_p1_map_val — the pile-1 reindexing has the value of the cut image.
    @composes: s5x5_p1_map_inj *)
Lemma s5x5_p1_map_val (w0 : pgg_gT s5x5_M) (i : 'I_5)
    (H : (@pgg_rho s5x5_M w0 (p1_idx i) < 5)%N) :
  s5x5_p1_map w0 i = @pgg_rho s5x5_M w0 (p1_idx i) :> nat.
Proof. exact: (inordK H). Qed.

(** s5x5_p2_map_val — the pile-2 reindexing has the offset value of the cut
    image.
    @composes: s5x5_p2_map_inj *)
Lemma s5x5_p2_map_val (w0 : pgg_gT s5x5_M) (i : 'I_5)
    (H : (@pgg_rho s5x5_M w0 (p2_idx i) - 5 < 5)%N) :
  s5x5_p2_map w0 i = (@pgg_rho s5x5_M w0 (p2_idx i) - 5)%N :> nat.
Proof. exact: (inordK H). Qed.

(** s5x5_p1_map_inj — the pile-1 restriction of a group cut is injective.
    @composes: s5x5_rfree_recon *)
Lemma s5x5_p1_map_inj (w0 : pgg_gT s5x5_M) (Hw0 : w0 \in pgg_G s5x5_M) :
  injective (s5x5_p1_map w0).
Proof.
move=> a b Hab.
have Hrho : @pgg_rho s5x5_M w0 (p1_idx a) = @pgg_rho s5x5_M w0 (p1_idx b).
  apply: ord_inj.
  by rewrite -(s5x5_p1_map_val (s5x5_p1_stab Hw0 a))
             -(s5x5_p1_map_val (s5x5_p1_stab Hw0 b)) Hab.
have Hidx := @perm_inj _ (@pgg_rho s5x5_M w0) _ _ Hrho.
by apply: ord_inj; rewrite -(p1_idx_val a) -(p1_idx_val b) Hidx.
Qed.

(** s5x5_p2_map_inj — the pile-2 restriction of a group cut is injective.
    @composes: s5x5_rfree_recon *)
Lemma s5x5_p2_map_inj (w0 : pgg_gT s5x5_M) (Hw0 : w0 \in pgg_G s5x5_M) :
  injective (s5x5_p2_map w0).
Proof.
move=> a b Hab.
have Hrho : @pgg_rho s5x5_M w0 (p2_idx a) = @pgg_rho s5x5_M w0 (p2_idx b).
  apply: ord_inj.
  rewrite -(subnK (s5x5_p2_stab Hw0 a)) -(subnK (s5x5_p2_stab Hw0 b)).
  by rewrite -(s5x5_p2_map_val (s5x5_p2_stab_sub Hw0 a))
             -(s5x5_p2_map_val (s5x5_p2_stab_sub Hw0 b)) Hab.
have Hidx := @perm_inj _ (@pgg_rho s5x5_M w0) _ _ Hrho.
apply: ord_inj; apply: (@addnI 5).
by rewrite -(p2_idx_val a) -(p2_idx_val b) Hidx.
Qed.

(******************************************************************************)
(*     The product reconstruction reduced to its two factor sums              *)
(******************************************************************************)

(** pile_valid — the probability-free five-party layout is a valid sum-mod
    sharing of the tape's secret coordinate.
    @composes: s5x5_rfree_recon *)
Lemma pile_valid (u : 'rV['Z_5]_5) :
  ts_valid (@sum_mod_scheme 3 4) (u ord0 ord0) (s5_rfree_layout u).
Proof. exact: s5_rfree_valid. Qed.

(** sum_mod5_recon_reindex — five-party sum-mod reconstruction is invariant
    under an injective reindexing of the share positions.
    @composes: s5x5_rfree_recon *)
Lemma sum_mod5_recon_reindex (f : 'I_5 -> 'I_5) (Hf : injective f)
    (s : 'I_5) (sh : 5.-tuple 'I_5) :
  ts_valid (@sum_mod_scheme 3 4) s sh ->
  ts_recon (@sum_mod_scheme 3 4) [tuple tnth sh (f i) | i < 5] = s.
Proof.
move=> Hvalid.
have Hv : @sum_mod_valid_pred 3 4 s sh := Hvalid.
apply: sum_mod_scheme_correct.
rewrite /sum_mod_valid_pred -Hv; congr (_ %% _).
under eq_bigr do rewrite tnth_mktuple.
symmetry; rewrite (reindex_inj Hf).
by apply: eq_bigr.
Qed.

(** s5x5_reconE — the product reconstruction is the combination of the two
    factor sum reconstructions.
    @composes: s5x5_rfree_recon *)
Lemma s5x5_reconE (t : 10.-tuple 'I_10) :
  ts_recon s5x5_scheme t
  = @combine_secret 3 3
      (ts_recon (@sum_mod_scheme 3 4)
        (@pile1_shares 3 3 (@sum_mod_scheme 3 4) (@sum_mod_scheme 3 4) t))
      (ts_recon (@sum_mod_scheme 3 4)
        (@pile2_shares 3 3 (@sum_mod_scheme 3 4) (@sum_mod_scheme 3 4) t)).
Proof. by []. Qed.

(** s5x5_pile1_sharesE — the pile-1 shares are the projections at the pile-1
    seats.
    @composes: s5x5_rfree_recon *)
Lemma s5x5_pile1_sharesE (t : 10.-tuple 'I_10) :
  @pile1_shares 3 3 (@sum_mod_scheme 3 4) (@sum_mod_scheme 3 4) t
  = [tuple @project_pile1 3 3 (tnth t (p1_idx i)) | i < 5].
Proof.
apply: eq_from_tnth => i; rewrite /pile1_shares !tnth_mktuple.
by congr (@project_pile1 3 3 _); congr (tnth t _); apply: val_inj.
Qed.

(** s5x5_pile2_sharesE — the pile-2 shares are the projections at the pile-2
    seats.
    @composes: s5x5_rfree_recon *)
Lemma s5x5_pile2_sharesE (t : 10.-tuple 'I_10) :
  @pile2_shares 3 3 (@sum_mod_scheme 3 4) (@sum_mod_scheme 3 4) t
  = [tuple @project_pile2 3 3 (tnth t (p2_idx i)) | i < 5].
Proof.
apply: eq_from_tnth => i; rewrite /pile2_shares !tnth_mktuple.
by congr (@project_pile2 3 3 _); congr (tnth t _); apply: val_inj.
Qed.

(** s5x5_pile1_layoutE — the pile-1 projections of the cut-permuted layout are
    the pile-1 shares at the reindexed parties.
    @composes: s5x5_rfree_recon *)
Lemma s5x5_pile1_layoutE (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type)
    (w0 : pgg_gT s5x5_M) (Hw0 : w0 \in pgg_G s5x5_M) :
  [tuple @project_pile1 3 3
      (tnth [tuple tnth (s5x5_rfree_layout uv) (@pgg_rho s5x5_M w0 j) | j < 10]
            (p1_idx i)) | i < 5]
  = [tuple tnth (s5_rfree_layout uv.1) (s5x5_p1_map w0 i) | i < 5].
Proof.
apply: eq_from_tnth => i; rewrite !tnth_mktuple.
have Hlt := s5x5_p1_stab Hw0 i.
case: (ltnP (@pgg_rho s5x5_M w0 (p1_idx i)) 5) => Hc;
  last by rewrite (leq_gtF Hc) in Hlt.
rewrite /s5x5_p1_map.
exact: project_embed_p1K.
Qed.

(** s5x5_pile2_layoutE — the pile-2 projections of the cut-permuted layout are
    the pile-2 shares at the reindexed parties.
    @composes: s5x5_rfree_recon *)
Lemma s5x5_pile2_layoutE (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type)
    (w0 : pgg_gT s5x5_M) (Hw0 : w0 \in pgg_G s5x5_M) :
  [tuple @project_pile2 3 3
      (tnth [tuple tnth (s5x5_rfree_layout uv) (@pgg_rho s5x5_M w0 j) | j < 10]
            (p2_idx i)) | i < 5]
  = [tuple tnth (s5_rfree_layout uv.2) (s5x5_p2_map w0 i) | i < 5].
Proof.
apply: eq_from_tnth => i; rewrite !tnth_mktuple.
have Hge := s5x5_p2_stab Hw0 i.
case: (ltnP (@pgg_rho s5x5_M w0 (p2_idx i)) 5) => Hc;
  first by rewrite (leq_gtF Hge) in Hc.
rewrite /s5x5_p2_map.
exact: project_embed_p2K.
Qed.

(** s5x5_rfree_recon — reconstructing the cut-permuted probability-free layout
    returns the combination of the two pile secrets, for any cut in the group.
    @main correctness: the product reconstruction of the ten cut-permuted
    layout entries is combine_secret (uv.1 ord0 ord0) (uv.2 ord0 ord0), proved
    from the two factor sum reconstructions and pile preservation, without
    ts_valid s5x5_scheme. *)
Lemma s5x5_rfree_recon (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type)
    (w0 : pgg_gT s5x5_M) (Hw0 : w0 \in pgg_G s5x5_M) :
  ts_recon s5x5_scheme
    [tuple tnth (s5x5_rfree_layout uv) (@pgg_rho s5x5_M w0 i) | i < 10]
  = @combine_secret 3 3 (uv.1 ord0 ord0) (uv.2 ord0 ord0).
Proof.
rewrite s5x5_reconE s5x5_pile1_sharesE s5x5_pile2_sharesE.
congr (@combine_secret 3 3).
- rewrite (s5x5_pile1_layoutE uv Hw0).
  exact: (@sum_mod5_recon_reindex (s5x5_p1_map w0) (@s5x5_p1_map_inj w0 Hw0)
            (uv.1 ord0 ord0) (s5_rfree_layout uv.1) (pile_valid uv.1)).
- rewrite (s5x5_pile2_layoutE uv Hw0).
  exact: (@sum_mod5_recon_reindex (s5x5_p2_map w0) (@s5x5_p2_map_inj w0 Hw0)
            (uv.2 ord0 ord0) (s5_rfree_layout uv.2) (pile_valid uv.2)).
Qed.

(******************************************************************************)
(*     The cut-generalized run skeleton                                       *)
(******************************************************************************)

(** s5x5_aprocs_cut — the twelve-process S_5 x S_5 run skeleton at an abstract
    content readout and an arbitrary cut.
    @intent: s5x5_trace.s5x5_aprocs_abs with the dealer's singleton deck
    [:: w0] in place of the identity cut. *)
Definition s5x5_aprocs_cut (g : 'I_10 -> 'I_10) (w0 : pgg_gT s5x5_M) :=
  erase_aprocs
  [:: mk_aproc (dealer_with_input_encoding s5x5_PI
                  (fun _ => g) [:: w0] [::] s5x5_players 0)
    ; mk_aproc (exchange_verifier s5x5_PI s5x5_players)
    ; mk_aproc (exchange_player s5x5_PI (@Ordinal 10 0 isT))
    ; mk_aproc (exchange_player s5x5_PI (@Ordinal 10 1 isT))
    ; mk_aproc (exchange_player s5x5_PI (@Ordinal 10 2 isT))
    ; mk_aproc (exchange_player s5x5_PI (@Ordinal 10 3 isT))
    ; mk_aproc (exchange_player s5x5_PI (@Ordinal 10 4 isT))
    ; mk_aproc (exchange_player s5x5_PI (@Ordinal 10 5 isT))
    ; mk_aproc (exchange_player s5x5_PI (@Ordinal 10 6 isT))
    ; mk_aproc (exchange_player s5x5_PI (@Ordinal 10 7 isT))
    ; mk_aproc (exchange_player s5x5_PI (@Ordinal 10 8 isT))
    ; mk_aproc (exchange_player s5x5_PI (@Ordinal 10 9 isT))].

(** s5x5_aprocs_cut1 — the identity cut gives the landed abstract skeleton.
    @composes: s5x5_rprocs_cut1 *)
Lemma s5x5_aprocs_cut1 (g : 'I_10 -> 'I_10) :
  s5x5_aprocs_cut g 1%g = s5x5_aprocs_abs g.
Proof. by []. Qed.

(** s5x5_rprocs_cut — the randomized run at a product tape and an arbitrary
    cut.
    @intent: s5x5_aprocs_cut fed the probability-free layout of the tape. *)
Definition s5x5_rprocs_cut (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type)
    (w0 : pgg_gT s5x5_M) :=
  s5x5_aprocs_cut (tnth (s5x5_rfree_layout uv)) w0.

(** s5x5_rprocs_cut1 — the identity-cut specialization is the landed randomized
    process list.
    @main architecture: s5x5_rprocs_cut uv 1 = s5x5_rprocs R uv, at every
    realType. *)
Lemma s5x5_rprocs_cut1 (R : realType)
    (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type) :
  s5x5_rprocs_cut uv 1%g = s5x5_rprocs R uv.
Proof.
by rewrite /s5x5_rprocs_cut s5x5_aprocs_cut1 /s5x5_rprocs s5x5_rfree_layoutE.
Qed.

(** s5x5_abs_terminates — every process of the cut-generalized run reaches
    Finish.
    @composes: s5x5_rand_terminates *)
Lemma s5x5_abs_terminates (g : 'I_10 -> 'I_10) (w0 : pgg_gT s5x5_M) :
  (run_interp 300 (s5x5_aprocs_cut g w0)).1 = nseq 12 Finish.
Proof. by vm_compute. Qed.

(** s5x5_abs_endpoints — the cut-generalized verifier endpoints are the
    abstract readout at the cut images of the starts.
    @composes: s5x5_rand_endpoints, s5x5_rand_run_recovers *)
Lemma s5x5_abs_endpoints (g : 'I_10 -> 'I_10) (w0 : pgg_gT s5x5_M) :
  endpoints_of_trace (nth [::] (run_interp 300 (s5x5_aprocs_cut g w0)).2 1)
  = [seq g (@pgg_rho s5x5_M w0 (tnth (pi_starts s5x5_PI) i))
     | i <- s5x5_players].
Proof.
rewrite /s5x5_aprocs_cut /dealer_with_input_encoding.
exact: (@s5x5_verifier_endpoints (fun=> g) w0 (ord_tuple 10) s5x5_starts_uniq).
Qed.

(******************************************************************************)
(*     The randomized execution plug                                          *)
(******************************************************************************)

(** s5x5_rand_endpoints_size — the randomized run collects one endpoint per
    share.
    @composes: s5x5_rand_run_recovers, s5x5_rand_recon *)
Lemma s5x5_rand_endpoints_size (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type)
    (w0 : pgg_gT s5x5_M) :
  size (endpoints_of_trace
          (nth [::] (run_interp 300 (s5x5_rprocs_cut uv w0)).2 1))
  = (ts_T' s5x5_scheme).+1.
Proof. by rewrite /s5x5_rprocs_cut s5x5_abs_endpoints size_map. Qed.

(** s5x5_rand_run_recovers — reconstructing the randomized run's endpoints
    returns the combination of the two pile secrets, for any cut in the group.
    @main correctness: ts_recon s5x5_scheme of the cut-permuted endpoints of
    s5x5_rprocs_cut uv w0 is combine_secret (uv.1 ord0 ord0) (uv.2 ord0 ord0),
    for any cut w0 in the group. *)
Lemma s5x5_rand_run_recovers (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type)
    (w0 : pgg_gT s5x5_M) :
  w0 \in pgg_G s5x5_M ->
  ts_recon s5x5_scheme
    (tcast (s5x5_rand_endpoints_size uv w0)
       (in_tuple (endpoints_of_trace
          (nth [::] (run_interp 300 (s5x5_rprocs_cut uv w0)).2 1))))
  = @combine_secret 3 3 (uv.1 ord0 ord0) (uv.2 ord0 ord0).
Proof.
move=> Hw0.
have Hgoal : forall (ep : seq 'I_(pgg_N' s5x5_M).+1)
    (Hsz : size ep = (ts_T' s5x5_scheme).+1),
    ep = [seq tnth (s5x5_rfree_layout uv)
                (pgg_rho w0 (tnth (pi_starts s5x5_PI) i))
          | i <- enum 'I_(pi_T' s5x5_PI).+1] ->
    ts_recon s5x5_scheme (tcast Hsz (in_tuple ep))
    = @combine_secret 3 3 (uv.1 ord0 ord0) (uv.2 ord0 ord0).
  move=> ep Hsz Hep.
  rewrite -(@s5x5_rfree_recon uv w0 Hw0).
  congr (ts_recon _ _).
  apply: eq_from_tnth => i.
  rewrite tcastE tnth_mktuple.
  rewrite (tnth_nth ord0) /= Hep.
  rewrite (nth_map i) ?nth_ord_enum ?tnth_ord_tuple;
    last by rewrite size_enum_ord ltn_ord.
  by [].
apply: Hgoal.
by rewrite /s5x5_rprocs_cut s5x5_abs_endpoints s5x5_players_enumE.
Qed.

(** s5x5_rand_plug — the S_5 x S_5 randomized execution plug.
    @intent: the execution layer over s5x5_profile with run argument the
    product sampler tape 'rV['Z_5]_5 * 'rV['Z_5]_5, the seat/share bridge erefl
    at 10 seats and 10 shares, participant list s5x5_run.s5x5_players, content
    the probability-free two-pile layout of the tape and fuel 300. *)
Definition s5x5_rand_plug : ExecutionPlug mpX :=
  @dealer_secret_plug mpX ('rV['Z_5]_5 * 'rV['Z_5]_5)%type erefl
    s5x5_run.s5x5_players s5x5_players_enumE
    (fun uv _ => tnth (s5x5_rfree_layout uv)) 300.

(** s5x5_rcontent_obs — the S_5 x S_5 randomized static observation.
    @intent: the two-pile layout entry at the cut image of a starting position,
    namely tnth (s5x5_rfree_layout uv) (pgg_rho w0 p). *)
Definition s5x5_rcontent_obs (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type)
    (p : pgg_gT (mp_M mpX) * 'I_(pgg_N' (mp_M mpX)).+1)
    : 'I_(pgg_N' (mp_M mpX)).+1 :=
  tnth (s5x5_rfree_layout uv) (@pgg_rho (mp_M mpX) p.1 p.2).

(** s5x5_rand_procsE — the derived process list is the cut-generalized
    randomized list.
    @composes: s5x5_rand_terminates, s5x5_rand_endpoints, s5x5_rand_recon *)
Lemma s5x5_rand_procsE (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type)
    (w0 : pgg_gT s5x5_M) :
  @exec_procs mpX s5x5_rand_plug uv w0 0 = s5x5_rprocs_cut uv w0.
Proof. by []. Qed.

(** s5x5_rand_fuelE — the randomized plug's fuel is 300.
    @composes: s5x5_rand_terminates, s5x5_rand_endpoints, s5x5_rand_recon *)
Lemma s5x5_rand_fuelE : ep_fuel s5x5_rand_plug = 300.
Proof. by []. Qed.

(** s5x5_rand_playersE — the randomized plug's participant list is the
    instance's list.
    @composes: s5x5_rand_endpoints *)
Lemma s5x5_rand_playersE :
  ep_players s5x5_rand_plug = s5x5_run.s5x5_players.
Proof. by []. Qed.

(** s5x5_rand_procs_size — the randomized run has twelve processes.
    @composes: s5x5_rand_terminates *)
Lemma s5x5_rand_procs_size (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type)
    (w0 : pgg_gT s5x5_M) :
  size (@exec_procs mpX s5x5_rand_plug uv w0 0) = 12.
Proof. by []. Qed.

(** s5x5_rand_terminates — every process of the randomized run reaches Finish.
    @composes: s5x5_rand_observed *)
Lemma s5x5_rand_terminates (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type)
    (w0 : pgg_gT s5x5_M) :
  (@exec_run mpX s5x5_rand_plug uv w0 0).1
  = nseq (size (@exec_procs mpX s5x5_rand_plug uv w0 0)) Finish.
Proof.
rewrite s5x5_rand_procs_size /exec_run s5x5_rand_fuelE s5x5_rand_procsE.
exact: s5x5_abs_terminates.
Qed.

(** s5x5_rand_endpoints — the randomized verifier endpoints are the static
    observation over the seats.
    @composes: s5x5_rand_recon, s5x5_rand_observed *)
Lemma s5x5_rand_endpoints (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type)
    (w0 : pgg_gT s5x5_M) :
  @exec_endpoints mpX s5x5_rand_plug uv w0 0
  = @exec_static_endpoints mpX s5x5_rand_plug s5x5_rcontent_obs uv w0.
Proof.
rewrite /exec_endpoints /exec_run s5x5_rand_fuelE s5x5_rand_procsE
        /exec_verifier_id.
rewrite /exec_static_endpoints s5x5_rand_playersE.
by rewrite /s5x5_rprocs_cut s5x5_abs_endpoints.
Qed.

(** s5x5_rand_endpoint_count — the randomized run collects ten endpoints.
    @main correctness: size (exec_endpoints s5x5_rand_plug uv w0 0) = 10. *)
Lemma s5x5_rand_endpoint_count (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type)
    (w0 : pgg_gT s5x5_M) :
  size (@exec_endpoints mpX s5x5_rand_plug uv w0 0) = 10.
Proof. by rewrite (exec_endpoints_size (s5x5_rand_endpoints uv w0)). Qed.

(** s5x5_rand_decodeE — the randomized plug's decoder is the instance's
    reconstruction.
    @composes: s5x5_rand_recon *)
Lemma s5x5_rand_decodeE (ep : seq 'I_(pgg_N' (mp_M mpX)).+1)
    (Hsz : size ep = (pi_T' (mp_PI mpX)).+1)
    (Hsz' : size ep = (ts_T' s5x5_scheme).+1) :
  @exec_decode mpX s5x5_rand_plug ep Hsz
  = ts_recon s5x5_scheme (tcast Hsz' (in_tuple ep)).
Proof.
by rewrite /exec_decode /run_recover (eq_irrelevance (etrans Hsz _) Hsz').
Qed.

(** s5x5_joint_tape_secret — the pair of pile secrets of a product tape.
    @intent: coordinate 0 of each pile tape, the two values the two additive
    sharings share. *)
Definition s5x5_joint_tape_secret (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type)
    : ('Z_5 * 'Z_5)%type := (uv.1 ord0 ord0, uv.2 ord0 ord0).

(** s5x5_joint_tape_secretE — the pair of pile secrets is the trace file's
    joint product secret, at every realType.
    @composes: s5x5_rand_observed *)
Lemma s5x5_joint_tape_secretE (R : realType) :
  JointSecret R = s5x5_joint_tape_secret.
Proof. by []. Qed.

(** s5x5_codec — the codec from the joint pile secret to the profile secret
    carrier 'I_10.
    @intent: combine_secret at the two five-element pile alphabets. *)
Definition s5x5_codec (z : ('Z_5 * 'Z_5)%type) : 'I_10 :=
  @combine_secret 3 3 z.1 z.2.

(** s5x5_decodec — the codec from the profile secret carrier to a pile pair.
    @intent: split_secret at the two five-element pile alphabets. *)
Definition s5x5_decodec (s : 'I_10) : ('Z_5 * 'Z_5)%type := @split_secret 3 3 s.

(** s5x5_decodecK — encoding cancels decoding on the whole profile carrier.
    @composes: s5x5_rand_observed *)
Lemma s5x5_decodecK : cancel s5x5_decodec s5x5_codec.
Proof.
by move=> s; rewrite /s5x5_codec /s5x5_decodec; exact: (@combine_splitK 3 3 s).
Qed.

(** s5x5_codecK_partial — decoding cancels encoding exactly on the pile pairs
    whose combination does not wrap.
    @composes: s5x5_rand_observed *)
Lemma s5x5_codecK_partial (z : ('Z_5 * 'Z_5)%type) :
  (val z.1 + 5 * val z.2 < 10)%N -> s5x5_decodec (s5x5_codec z) = z.
Proof.
case: z => z1 z2 Hlt.
rewrite /s5x5_decodec /s5x5_codec /=.
by rewrite (@split_combineK 3 3 z1 z2 Hlt).
Qed.

(** s5x5_rand_recon — decoding the randomized static observation returns the
    combined pile secrets.
    @composes: s5x5_rand_observed *)
Lemma s5x5_rand_recon (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type)
    (w0 : pgg_gT s5x5_M) :
  w0 \in pgg_G s5x5_M ->
  forall Hsz : size (@exec_static_endpoints mpX s5x5_rand_plug
                       s5x5_rcontent_obs uv w0)
               = (pi_T' (mp_PI mpX)).+1,
  @exec_decode mpX s5x5_rand_plug
    (@exec_static_endpoints mpX s5x5_rand_plug s5x5_rcontent_obs uv w0) Hsz
  = s5x5_codec (s5x5_joint_tape_secret uv).
Proof.
move=> Hw0.
rewrite -s5x5_rand_endpoints /exec_endpoints /exec_run s5x5_rand_fuelE
        s5x5_rand_procsE /exec_verifier_id => Hsz.
rewrite (s5x5_rand_decodeE Hsz (s5x5_rand_endpoints_size uv w0)).
exact: (@s5x5_rand_run_recovers uv w0 Hw0).
Qed.

(** s5x5_rand_observed — the S_5 x S_5 randomized observed execution.
    @intent: s5x5_profile with plug s5x5_rand_plug at process offset 0, static
    observation s5x5_rcontent_obs and expected value the combined pile secrets;
    the three run facts are s5x5_rand_terminates, s5x5_rand_endpoints and
    s5x5_rand_recon. *)
Definition s5x5_rand_observed : OE.ObservedExecution :=
  OE.MkObservedExecution mpX s5x5_rand_plug 0
    s5x5_rcontent_obs (fun uv => s5x5_codec (s5x5_joint_tape_secret uv))
    s5x5_rand_terminates s5x5_rand_endpoints (@s5x5_rand_recon).

(** s5x5_rand_observed_recovers — the packaged randomized run decodes to the
    combined pile secrets.
    @main correctness: exec_decode of the executed endpoints of
    s5x5_rand_observed at tape uv and cut w0 is
    s5x5_codec (s5x5_joint_tape_secret uv), for any cut w0 in the group. *)
Theorem s5x5_rand_observed_recovers (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type)
    (w0 : pgg_gT s5x5_M) (Hw0 : w0 \in pgg_G s5x5_M) :
  @exec_decode mpX s5x5_rand_plug
    (@exec_endpoints mpX s5x5_rand_plug uv w0 0)
    (OE.oe_endpoints_size s5x5_rand_observed uv w0)
  = s5x5_codec (s5x5_joint_tape_secret uv).
Proof. exact: (OE.oe_run_recovers s5x5_rand_observed uv w0 Hw0). Qed.

(** s5x5_rand_correct — termination, endpoint count and recovery of the
    randomized run.
    @main correctness: the run of s5x5_rand_plug reaches Finish at each of its
    twelve processes, collects one endpoint per seat, and decodes to the
    combined pile secrets, for any cut w0 in the group. *)
Theorem s5x5_rand_correct (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type)
    (w0 : pgg_gT s5x5_M) (Hw0 : w0 \in pgg_G s5x5_M) :
  [/\ (@exec_run mpX s5x5_rand_plug uv w0 0).1
        = nseq (size (@exec_procs mpX s5x5_rand_plug uv w0 0)) Finish,
      size (@exec_endpoints mpX s5x5_rand_plug uv w0 0)
        = (pi_T' (mp_PI mpX)).+1 &
      @exec_decode mpX s5x5_rand_plug
        (@exec_endpoints mpX s5x5_rand_plug uv w0 0)
        (exec_endpoints_size (s5x5_rand_endpoints uv w0))
      = s5x5_codec (s5x5_joint_tape_secret uv)].
Proof.
exact: (@exec_run_correct mpX s5x5_rand_plug s5x5_rcontent_obs
          (fun uv => s5x5_codec (s5x5_joint_tape_secret uv)) uv w0 0
          (s5x5_rand_terminates uv w0) (s5x5_rand_endpoints uv w0)
          (s5x5_rand_recon Hw0)).
Qed.

End s5x5_randomized_execution.

Print Assumptions s5x5_rfree_layoutE.
Print Assumptions s5x5_rprocs_cut1.
Print Assumptions s5x5_rfree_recon.
Print Assumptions s5x5_rand_run_recovers.
Print Assumptions s5x5_rand_observed_recovers.
Print Assumptions s5x5_rand_correct.
