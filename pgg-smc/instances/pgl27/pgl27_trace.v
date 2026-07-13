(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGL(2,7) executed-trace secrecy                                            *)
(*                                                                            *)
(* The eight-card orbit run deals the encoded shares of a bool orbit secret   *)
(* with the shuffle cut w0. A corrupted player's executed trace, projected to *)
(* its dealt card, is fed through trace_secrecy_of_view (cancel = id) to make *)
(* its conditional entropy of the secret equal to the plain entropy. The      *)
(* coalition corollary states the same over the joint trace of any coalition  *)
(* of at most three cards.                                                    *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_run_recovers_class      == record-free axiom-free run recovery     *)
(*   pgl27_player_trace_full       == the full player trace is its dealt card *)
(*   pgl27_trace_secrecy           == one player's trace keeps the secret     *)
(*   pgl27_coalition_trace_secrecy == any <= 3 coalition trace keeps it       *)
(*   pgl27_alldecks_trace_secrecy  == one player's trace keeps the secret     *)
(*                                    under the all-decks dealer              *)
(*   pgl27_alldecks_coalition_secrecy == any <= 3 coalition trace keeps it    *)
(*                                    under the all-decks dealer              *)
(*   pgl27_deck_trace_secrecy      == one player's trace keeps the secret     *)
(*                                    under the shuffle-free dealer           *)
(*   pgl27_deck_coalition_secrecy  == any <= 3 coalition trace keeps it       *)
(*                                    under the shuffle-free dealer           *)
(*                                                                            *)
(* The secrecy statements concern the pre-reveal execution: after the public  *)
(* reveal every player learns the secret by design.                           *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg boolp reals zmodp matrix.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
Require Import pgg_interface.
From pgg_smc Require Import card_exchange_pismc pgg_input_commitment pgg_run.
Require Import smc_interpreter pismc smc_session_types.
From pgg_reconstruct Require Import covering_scheme pgg_sharing_framework.
From pgg_reconstruct Require Import transitivity_privacy.
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_scheme pgl27_profile.
From pgg_smc Require Import pgl27_run pgl27_secrecy.
From pgg_smc Require Import pgg_trace_secrecy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Section pgl27_trace_sec.
Variable R : realType.

(** content_of — the informative coordinate of a player's executed trace: the
    head of the first dealt hand, with default ord0 for an empty trace.
    @intent: extract a finType content from a non-finite seq (pgg_data N.+1)
    trace. *)
Definition content_of (N : nat) (tr : seq (pgg_data N.+1)) : 'I_N.+1 :=
  if tr is _ :: PGG_hand (x :: _) :: _ then x else ord0.

Section abstract_leaf.
Variable g : 'I_8 -> 'I_8.
Variable w0 : pgg_gT pgl27_M.

(** pgl27_aprocs_abs — dealer (content readout g, shuffle cut w0, empty input
    prologue) ++ verifier ++ eight players, with the content function held
    abstract so vm_compute reduces the run skeleton without unfolding the dealt
    card value.
    @intent: the ten session-typed processes of one PGL(2,7) run over an
    abstract content readout g at the symbolic cut w0. *)
Definition pgl27_aprocs_abs :=
  erase_aprocs
  [:: mk_aproc (dealer_with_input_encoding pgl27_PI
                  (fun _ => g) [:: w0] [::] pgl27_players 0)
    ; mk_aproc (exchange_verifier pgl27_PI pgl27_players)
    ; mk_aproc (exchange_player pgl27_PI (@Ordinal 8 0 isT))
    ; mk_aproc (exchange_player pgl27_PI (@Ordinal 8 1 isT))
    ; mk_aproc (exchange_player pgl27_PI (@Ordinal 8 2 isT))
    ; mk_aproc (exchange_player pgl27_PI (@Ordinal 8 3 isT))
    ; mk_aproc (exchange_player pgl27_PI (@Ordinal 8 4 isT))
    ; mk_aproc (exchange_player pgl27_PI (@Ordinal 8 5 isT))
    ; mk_aproc (exchange_player pgl27_PI (@Ordinal 8 6 isT))
    ; mk_aproc (exchange_player pgl27_PI (@Ordinal 8 7 isT))].

(* The eight player traces are stated per concrete player index so that both
   the process-list ordinal and the readout index share the canonical isT
   proof, which lets vm_compute close each case by reflexivity. *)
(** pgl27_abs_p0 — player 0's executed-trace content is g at the cut-permuted
    starting position of player 0.
    @composes: pgl27_trace_secrecy *)
Lemma pgl27_abs_p0 :
  content_of (nth [::] (run_interp pgl27_fuel pgl27_aprocs_abs).2 (2 + 0))
  = g (@pgg_rho pgl27_M w0 (tnth (pi_starts pgl27_PI) (@Ordinal 8 0 isT))).
Proof. rewrite /pgl27_aprocs_abs; vm_compute; reflexivity. Qed.

(** pgl27_abs_p1 — player 1's executed-trace content is g at the cut-permuted
    starting position of player 1.
    @composes: pgl27_trace_secrecy *)
Lemma pgl27_abs_p1 :
  content_of (nth [::] (run_interp pgl27_fuel pgl27_aprocs_abs).2 (2 + 1))
  = g (@pgg_rho pgl27_M w0 (tnth (pi_starts pgl27_PI) (@Ordinal 8 1 isT))).
Proof. rewrite /pgl27_aprocs_abs; vm_compute; reflexivity. Qed.

(** pgl27_abs_p2 — player 2's executed-trace content is g at the cut-permuted
    starting position of player 2.
    @composes: pgl27_trace_secrecy *)
Lemma pgl27_abs_p2 :
  content_of (nth [::] (run_interp pgl27_fuel pgl27_aprocs_abs).2 (2 + 2))
  = g (@pgg_rho pgl27_M w0 (tnth (pi_starts pgl27_PI) (@Ordinal 8 2 isT))).
Proof. rewrite /pgl27_aprocs_abs; vm_compute; reflexivity. Qed.

(** pgl27_abs_p3 — player 3's executed-trace content is g at the cut-permuted
    starting position of player 3.
    @composes: pgl27_trace_secrecy *)
Lemma pgl27_abs_p3 :
  content_of (nth [::] (run_interp pgl27_fuel pgl27_aprocs_abs).2 (2 + 3))
  = g (@pgg_rho pgl27_M w0 (tnth (pi_starts pgl27_PI) (@Ordinal 8 3 isT))).
Proof. rewrite /pgl27_aprocs_abs; vm_compute; reflexivity. Qed.

(** pgl27_abs_p4 — player 4's executed-trace content is g at the cut-permuted
    starting position of player 4.
    @composes: pgl27_trace_secrecy *)
Lemma pgl27_abs_p4 :
  content_of (nth [::] (run_interp pgl27_fuel pgl27_aprocs_abs).2 (2 + 4))
  = g (@pgg_rho pgl27_M w0 (tnth (pi_starts pgl27_PI) (@Ordinal 8 4 isT))).
Proof. rewrite /pgl27_aprocs_abs; vm_compute; reflexivity. Qed.

(** pgl27_abs_p5 — player 5's executed-trace content is g at the cut-permuted
    starting position of player 5.
    @composes: pgl27_trace_secrecy *)
Lemma pgl27_abs_p5 :
  content_of (nth [::] (run_interp pgl27_fuel pgl27_aprocs_abs).2 (2 + 5))
  = g (@pgg_rho pgl27_M w0 (tnth (pi_starts pgl27_PI) (@Ordinal 8 5 isT))).
Proof. rewrite /pgl27_aprocs_abs; vm_compute; reflexivity. Qed.

(** pgl27_abs_p6 — player 6's executed-trace content is g at the cut-permuted
    starting position of player 6.
    @composes: pgl27_trace_secrecy *)
Lemma pgl27_abs_p6 :
  content_of (nth [::] (run_interp pgl27_fuel pgl27_aprocs_abs).2 (2 + 6))
  = g (@pgg_rho pgl27_M w0 (tnth (pi_starts pgl27_PI) (@Ordinal 8 6 isT))).
Proof. rewrite /pgl27_aprocs_abs; vm_compute; reflexivity. Qed.

(** pgl27_abs_p7 — player 7's executed-trace content is g at the cut-permuted
    starting position of player 7.
    @composes: pgl27_trace_secrecy *)
Lemma pgl27_abs_p7 :
  content_of (nth [::] (run_interp pgl27_fuel pgl27_aprocs_abs).2 (2 + 7))
  = g (@pgg_rho pgl27_M w0 (tnth (pi_starts pgl27_PI) (@Ordinal 8 7 isT))).
Proof. rewrite /pgl27_aprocs_abs; vm_compute; reflexivity. Qed.

(* The full per-player trace is the two-element list of an index marker and a
   singleton hand: [:: PGG_idx 0; PGG_hand [:: card]]. Each card value is held
   abstract in g so vm_compute closes the list skeleton by reflexivity. *)
(** pgl27_full_p0 — player 0's full executed trace: the index marker PGG_idx 0
    and the singleton hand g at the cut-permuted starting position of player 0.
    @composes: pgl27_player_trace_full *)
Lemma pgl27_full_p0 :
  nth [::] (run_interp pgl27_fuel pgl27_aprocs_abs).2 (2 + 0)
  = [:: PGG_idx 0;
        PGG_hand
          [:: g (@pgg_rho pgl27_M w0
                   (tnth (pi_starts pgl27_PI) (@Ordinal 8 0 isT)))]].
Proof. rewrite /pgl27_aprocs_abs; vm_compute; reflexivity. Qed.

(** pgl27_full_p1 — player 1's full executed trace: the index marker PGG_idx 0
    and the singleton hand g at the cut-permuted starting position of player 1.
    @composes: pgl27_player_trace_full *)
Lemma pgl27_full_p1 :
  nth [::] (run_interp pgl27_fuel pgl27_aprocs_abs).2 (2 + 1)
  = [:: PGG_idx 0;
        PGG_hand
          [:: g (@pgg_rho pgl27_M w0
                   (tnth (pi_starts pgl27_PI) (@Ordinal 8 1 isT)))]].
Proof. rewrite /pgl27_aprocs_abs; vm_compute; reflexivity. Qed.

(** pgl27_full_p2 — player 2's full executed trace: the index marker PGG_idx 0
    and the singleton hand g at the cut-permuted starting position of player 2.
    @composes: pgl27_player_trace_full *)
Lemma pgl27_full_p2 :
  nth [::] (run_interp pgl27_fuel pgl27_aprocs_abs).2 (2 + 2)
  = [:: PGG_idx 0;
        PGG_hand
          [:: g (@pgg_rho pgl27_M w0
                   (tnth (pi_starts pgl27_PI) (@Ordinal 8 2 isT)))]].
Proof. rewrite /pgl27_aprocs_abs; vm_compute; reflexivity. Qed.

(** pgl27_full_p3 — player 3's full executed trace: the index marker PGG_idx 0
    and the singleton hand g at the cut-permuted starting position of player 3.
    @composes: pgl27_player_trace_full *)
Lemma pgl27_full_p3 :
  nth [::] (run_interp pgl27_fuel pgl27_aprocs_abs).2 (2 + 3)
  = [:: PGG_idx 0;
        PGG_hand
          [:: g (@pgg_rho pgl27_M w0
                   (tnth (pi_starts pgl27_PI) (@Ordinal 8 3 isT)))]].
Proof. rewrite /pgl27_aprocs_abs; vm_compute; reflexivity. Qed.

(** pgl27_full_p4 — player 4's full executed trace: the index marker PGG_idx 0
    and the singleton hand g at the cut-permuted starting position of player 4.
    @composes: pgl27_player_trace_full *)
Lemma pgl27_full_p4 :
  nth [::] (run_interp pgl27_fuel pgl27_aprocs_abs).2 (2 + 4)
  = [:: PGG_idx 0;
        PGG_hand
          [:: g (@pgg_rho pgl27_M w0
                   (tnth (pi_starts pgl27_PI) (@Ordinal 8 4 isT)))]].
Proof. rewrite /pgl27_aprocs_abs; vm_compute; reflexivity. Qed.

(** pgl27_full_p5 — player 5's full executed trace: the index marker PGG_idx 0
    and the singleton hand g at the cut-permuted starting position of player 5.
    @composes: pgl27_player_trace_full *)
Lemma pgl27_full_p5 :
  nth [::] (run_interp pgl27_fuel pgl27_aprocs_abs).2 (2 + 5)
  = [:: PGG_idx 0;
        PGG_hand
          [:: g (@pgg_rho pgl27_M w0
                   (tnth (pi_starts pgl27_PI) (@Ordinal 8 5 isT)))]].
Proof. rewrite /pgl27_aprocs_abs; vm_compute; reflexivity. Qed.

(** pgl27_full_p6 — player 6's full executed trace: the index marker PGG_idx 0
    and the singleton hand g at the cut-permuted starting position of player 6.
    @composes: pgl27_player_trace_full *)
Lemma pgl27_full_p6 :
  nth [::] (run_interp pgl27_fuel pgl27_aprocs_abs).2 (2 + 6)
  = [:: PGG_idx 0;
        PGG_hand
          [:: g (@pgg_rho pgl27_M w0
                   (tnth (pi_starts pgl27_PI) (@Ordinal 8 6 isT)))]].
Proof. rewrite /pgl27_aprocs_abs; vm_compute; reflexivity. Qed.

(** pgl27_full_p7 — player 7's full executed trace: the index marker PGG_idx 0
    and the singleton hand g at the cut-permuted starting position of player 7.
    @composes: pgl27_player_trace_full *)
Lemma pgl27_full_p7 :
  nth [::] (run_interp pgl27_fuel pgl27_aprocs_abs).2 (2 + 7)
  = [:: PGG_idx 0;
        PGG_hand
          [:: g (@pgg_rho pgl27_M w0
                   (tnth (pi_starts pgl27_PI) (@Ordinal 8 7 isT)))]].
Proof. rewrite /pgl27_aprocs_abs; vm_compute; reflexivity. Qed.

End abstract_leaf.

(** pgl27_procs_abs — the concrete run at secret s and cut w0 is the abstract
    run with the dealt readout tnth (orbit_encode s).
    @composes: pgl27_player_trace_E *)
Lemma pgl27_procs_abs (s : bool) (w0 : pgg_gT pgl27_M) :
  pgl27_procs s w0 = pgl27_aprocs_abs (tnth (orbit_encode s)) w0.
Proof. by []. Qed.

(** pgl27_aprocs_endpoints — the abstract run's collected endpoints are the
    readout g at each cut-permuted starting position, one per player.
    @composes: pgl27_run_recovers_class *)
Lemma pgl27_aprocs_endpoints (g : 'I_8 -> 'I_8) (w0 : pgg_gT pgl27_M) :
  endpoints_of_trace
    (nth [::] (run_interp pgl27_fuel (pgl27_aprocs_abs g w0)).2 1)
  = [seq g (@pgg_rho pgl27_M w0 (tnth (pi_starts pgl27_PI) i))
     | i <- enum 'I_(pi_T' pgl27_PI).+1].
Proof.
rewrite /pgl27_aprocs_abs /dealer_with_input_encoding /identity_deck.
rewrite (@pgl27_verifier_endpoints (fun _ : seq _ => g) w0
           (ord_tuple 8) pgl27_starts_uniq).
have Hde : pgl27_players = enum 'I_8.
  by apply: (inj_map val_inj); rewrite val_enum_ord.
by rewrite Hde.
Qed.

(** pgl27_aprocs_endpoints_size — the abstract run collects exactly eight
    endpoints.
    @composes: pgl27_run_recovers_class *)
Lemma pgl27_aprocs_endpoints_size (g : 'I_8 -> 'I_8) (w0 : pgg_gT pgl27_M) :
  size (endpoints_of_trace
          (nth [::] (run_interp pgl27_fuel (pgl27_aprocs_abs g w0)).2 1)) = 8.
Proof. by rewrite pgl27_aprocs_endpoints size_map size_enum_ord. Qed.

(** pgl27_run_recovers_class — executed run over the abstract dealt readout
    tnth (orbit_encode s) recovers the orbit class s from the verifier's
    cut-permuted endpoints, for any cut w0 in the group, with neither the
    threshold-scheme record nor its privacy axiom in scope.
    @main correctness: record-free axiom-free recovery of the dealt orbit
    secret s : bool by the orbit classifier, via its shuffle invariance
    (orbit_class_invariant) and section (orbit_encodeK) at w0. *)
Lemma pgl27_run_recovers_class (s : bool) (w0 : pgg_gT pgl27_M) :
  w0 \in pgg_G pgl27_M ->
  orbit_class (tcast (pgl27_aprocs_endpoints_size (tnth (orbit_encode s)) w0)
     (in_tuple (endpoints_of_trace
        (nth [::]
          (run_interp pgl27_fuel
             (pgl27_aprocs_abs (tnth (orbit_encode s)) w0)).2 1)))) = s.
Proof.
move=> Hw0.
have Hgoal : forall (ep : seq 'I_(pgg_N' pgl27_M).+1) (H8 : size ep = 8),
    ep = [seq tnth (orbit_encode s)
              (@pgg_rho pgl27_M w0 (tnth (pi_starts pgl27_PI) i))
            | i <- enum 'I_(pi_T' pgl27_PI).+1] ->
    orbit_class (tcast H8 (in_tuple ep)) = s.
  move=> ep H8 Hep.
  have -> : tcast H8 (in_tuple ep)
          = [tuple tnth (orbit_encode s) (@pgg_rho pgl27_M w0 j) | j < 8].
    apply: eq_from_tnth => j.
    rewrite tcastE tnth_mktuple (tnth_nth ord0) /= Hep.
    rewrite (nth_map j) ?nth_ord_enum ?tnth_ord_tuple;
      last by rewrite size_enum_ord ltn_ord.
    by [].
  by rewrite (orbit_class_invariant w0 (orbit_encode s) Hw0) orbit_encodeK.
apply: Hgoal.
by rewrite pgl27_aprocs_endpoints.
Qed.

(** pgl27_player_trace — player i's executed-trace content, lifted over the
    joint secret-and-shuffle sampler via the run_interp projection at process
    index 2+i.
    @intent: single-player executed trace as a content random variable. *)
Definition pgl27_player_trace (i : 'I_8) : {RV (pgl27P R) -> 'I_8} :=
  fun u =>
    content_of
      (nth [::] (run_interp pgl27_fuel (pgl27_procs u.1 u.2)).2 (2 + i)).

(** pgl27_player_trace_E — the lifted player trace equals the dealt card of
    player i, the cut-permuted encoded value.
    @composes: pgl27_trace_secrecy *)
Lemma pgl27_player_trace_E (i : 'I_8) :
  pgl27_player_trace i
  = (fun u => tnth (orbit_encode u.1) (@pgg_rho pgl27_M u.2 i)).
Proof.
apply: boolp.funext => u; rewrite /pgl27_player_trace pgl27_procs_abs.
case: i => -[|[|[|[|[|[|[|[|//]]]]]]]] Hi.
- rewrite (pgl27_abs_p0 (tnth (orbit_encode u.1)) u.2) tnth_ord_tuple.
  by congr (tnth (orbit_encode u.1) (@pgg_rho pgl27_M u.2 _)); apply: val_inj.
- rewrite (pgl27_abs_p1 (tnth (orbit_encode u.1)) u.2) tnth_ord_tuple.
  by congr (tnth (orbit_encode u.1) (@pgg_rho pgl27_M u.2 _)); apply: val_inj.
- rewrite (pgl27_abs_p2 (tnth (orbit_encode u.1)) u.2) tnth_ord_tuple.
  by congr (tnth (orbit_encode u.1) (@pgg_rho pgl27_M u.2 _)); apply: val_inj.
- rewrite (pgl27_abs_p3 (tnth (orbit_encode u.1)) u.2) tnth_ord_tuple.
  by congr (tnth (orbit_encode u.1) (@pgg_rho pgl27_M u.2 _)); apply: val_inj.
- rewrite (pgl27_abs_p4 (tnth (orbit_encode u.1)) u.2) tnth_ord_tuple.
  by congr (tnth (orbit_encode u.1) (@pgg_rho pgl27_M u.2 _)); apply: val_inj.
- rewrite (pgl27_abs_p5 (tnth (orbit_encode u.1)) u.2) tnth_ord_tuple.
  by congr (tnth (orbit_encode u.1) (@pgg_rho pgl27_M u.2 _)); apply: val_inj.
- rewrite (pgl27_abs_p6 (tnth (orbit_encode u.1)) u.2) tnth_ord_tuple.
  by congr (tnth (orbit_encode u.1) (@pgg_rho pgl27_M u.2 _)); apply: val_inj.
- rewrite (pgl27_abs_p7 (tnth (orbit_encode u.1)) u.2) tnth_ord_tuple.
  by congr (tnth (orbit_encode u.1) (@pgg_rho pgl27_M u.2 _)); apply: val_inj.
Qed.

(** pgl27_player_trace_full — player i's full executed trace is a two-element
    list [:: PGG_idx 0; PGG_hand [:: pgl27_player_trace i u]] of the index
    marker and the singleton hand holding the dealt card; the trace is a
    deterministic function of that single card, so content_of is a lossless
    projection and conditioning on it equals conditioning on the whole trace.
    @main security: the full executed player trace carries no more information
    about the secret than its single dealt-card content. *)
Lemma pgl27_player_trace_full (i : 'I_8) (u : bool * pgg_gT pgl27_M) :
  nth [::] (run_interp pgl27_fuel (pgl27_procs u.1 u.2)).2 (2 + i)
  = [:: PGG_idx 0; PGG_hand [:: pgl27_player_trace i u]].
Proof.
rewrite pgl27_procs_abs pgl27_player_trace_E.
case: i => -[|[|[|[|[|[|[|[|//]]]]]]]] Hi.
- have -> : (@Ordinal 8 0 Hi) = (@Ordinal 8 0 isT) by apply: val_inj.
  by rewrite (pgl27_full_p0 (tnth (orbit_encode u.1)) u.2) tnth_ord_tuple.
- have -> : (@Ordinal 8 1 Hi) = (@Ordinal 8 1 isT) by apply: val_inj.
  by rewrite (pgl27_full_p1 (tnth (orbit_encode u.1)) u.2) tnth_ord_tuple.
- have -> : (@Ordinal 8 2 Hi) = (@Ordinal 8 2 isT) by apply: val_inj.
  by rewrite (pgl27_full_p2 (tnth (orbit_encode u.1)) u.2) tnth_ord_tuple.
- have -> : (@Ordinal 8 3 Hi) = (@Ordinal 8 3 isT) by apply: val_inj.
  by rewrite (pgl27_full_p3 (tnth (orbit_encode u.1)) u.2) tnth_ord_tuple.
- have -> : (@Ordinal 8 4 Hi) = (@Ordinal 8 4 isT) by apply: val_inj.
  by rewrite (pgl27_full_p4 (tnth (orbit_encode u.1)) u.2) tnth_ord_tuple.
- have -> : (@Ordinal 8 5 Hi) = (@Ordinal 8 5 isT) by apply: val_inj.
  by rewrite (pgl27_full_p5 (tnth (orbit_encode u.1)) u.2) tnth_ord_tuple.
- have -> : (@Ordinal 8 6 Hi) = (@Ordinal 8 6 isT) by apply: val_inj.
  by rewrite (pgl27_full_p6 (tnth (orbit_encode u.1)) u.2) tnth_ord_tuple.
- have -> : (@Ordinal 8 7 Hi) = (@Ordinal 8 7 isT) by apply: val_inj.
  by rewrite (pgl27_full_p7 (tnth (orbit_encode u.1)) u.2) tnth_ord_tuple.
Qed.

(** pgl27_point_indep — one player's dealt card is independent of the secret,
    reducing the singleton coalition view to that single card.
    @composes: pgl27_trace_secrecy *)
Lemma pgl27_point_indep (i : 'I_8) :
  pgl27P R |= (fun u => tnth (orbit_encode u.1) (@pgg_rho pgl27_M u.2 i))
              _|_ pgl27_secret R.
Proof.
have Hcard : (#|[set i]| <= 3)%N by rewrite cards1.
have Hview := pgl27_view_indep R (C := [set i]) Hcard.
have -> : (fun u => tnth (orbit_encode u.1) (@pgg_rho pgl27_M u.2 i))
        = (fun f : {ffun 'I_8 -> 'I_8} => f i) `o pgl27_view R [set i].
  by apply: boolp.funext => u; rewrite /comp_RV /pgl27_view ffunE in_set1 eqxx.
exact: (inde_RV_comp (fun f : {ffun 'I_8 -> 'I_8} => f i) Hview).
Qed.

(** pgl27_trace_secrecy — a single corrupted player's executed PGL(2,7) trace
    leaves the secret's conditional entropy equal to its plain entropy.
    @main security: single-player executed-trace secrecy over the eight-card
    orbit run, via the executed-trace bridge with cancel = id. *)
Lemma pgl27_trace_secrecy (i : 'I_8) :
  `H( pgl27_secret R | pgl27_player_trace i ) = `H `p_ (pgl27_secret R).
Proof.
apply: (trace_secrecy_of_view
          (view := (fun u => tnth (orbit_encode u.1) (@pgg_rho pgl27_M u.2 i)))
          (trace_of := id) (view_of := id)).
- by rewrite pgl27_player_trace_E.
- by [].
- exact: pgl27_point_indep i.
Qed.

(** pgl27_coalition_trace — the coalition's joint executed-trace record: the
    dealt card each member of C observes, and ord0 outside C.
    @intent: the coalition's joint executed trace as a random variable. *)
Definition pgl27_coalition_trace (C : {set 'I_8}) :
    {RV (pgl27P R) -> {ffun 'I_8 -> 'I_8}} :=
  fun u => [ffun i => if i \in C then pgl27_player_trace i u else ord0].

(** pgl27_coalition_trace_E — the coalition's joint executed trace equals its
    coalition view.
    @composes: pgl27_coalition_trace_secrecy *)
Lemma pgl27_coalition_trace_E (C : {set 'I_8}) :
  pgl27_coalition_trace C = pgl27_view R C.
Proof.
apply: boolp.funext => u; apply/ffunP => i.
rewrite /pgl27_coalition_trace /pgl27_view !ffunE.
case: ifP => // _.
by rewrite (pgl27_player_trace_E i).
Qed.

(** pgl27_coalition_trace_secrecy — the joint executed trace of any coalition
    of at most three cards leaves the secret's conditional entropy equal to its
    plain entropy.
    @main security: coalition executed-trace secrecy over the eight-card orbit
    run, via the executed-trace bridge with cancel = id. *)
Lemma pgl27_coalition_trace_secrecy (C : {set 'I_8}) :
  (#|C| <= 3)%N ->
  `H( pgl27_secret R | pgl27_coalition_trace C ) = `H `p_ (pgl27_secret R).
Proof.
move=> HC.
apply: (trace_secrecy_of_view (view := pgl27_view R C)
          (trace_of := id) (view_of := id)).
- by rewrite pgl27_coalition_trace_E.
- by [].
- exact: pgl27_view_indep R C HC.
Qed.

(* -------------------------------------------------------------------------- *)
(* All-decks dealer: executed-trace secrecy when the dealt arrangement is a   *)
(* uniform valid deck of the secret's class, shuffled by a uniform cut.       *)
(* -------------------------------------------------------------------------- *)

(** pgl27_procs_deck_abs — the all-decks run at arrangement sh and cut w0 is
    the abstract run with the dealt readout tnth sh.
    @composes: pgl27_alldecks_trace_E *)
Lemma pgl27_procs_deck_abs (sh : 8.-tuple 'I_8) (w0 : pgg_gT pgl27_M) :
  pgl27_procs_deck sh w0 = pgl27_aprocs_abs (tnth sh) w0.
Proof. by []. Qed.

(** pgl27P_alldecks — the all-decks joint law of the eight-card orbit scheme:
    a uniform orbit secret, a uniform valid deck of its class and an
    independent uniform PGL(2,7) shuffle.
    @intent: the all-decks dealer sample space of the executed run. *)
Definition pgl27P_alldecks :
    R.-fdist (bool * (8.-tuple 'I_8 * pgg_gT pgl27_M)) :=
  alldecksP (fdist_uniform card_bool) pgl27_G_pos (R:=R) pgl27_class_decks_pos.

(** pgl27_alldecks_secret — the dealt orbit-class secret component of an
    all-decks sample.
    @intent: the orbit-secret random variable of the all-decks run. *)
Definition pgl27_alldecks_secret : {RV pgl27P_alldecks -> bool} :=
  alldecks_secret (fdist_uniform card_bool) pgl27_G_pos pgl27_class_decks_pos.

(** pgl27_alldecks_trace — player i's executed-trace content over the
    all-decks sampler: the run_interp projection at process index 2+i of the
    run dealing the sampled arrangement at the sampled cut.
    @intent: single-player executed trace of the all-decks run. *)
Definition pgl27_alldecks_trace (i : 'I_8) : {RV pgl27P_alldecks -> 'I_8} :=
  fun u =>
    content_of
      (nth [::] (run_interp pgl27_fuel (pgl27_procs_deck u.2.1 u.2.2)).2
           (2 + i)).

(** pgl27_alldecks_trace_E — the all-decks player trace equals the dealt card
    of player i, the cut-permuted card of the sampled arrangement.
    @composes: pgl27_alldecks_trace_secrecy *)
Lemma pgl27_alldecks_trace_E (i : 'I_8) :
  pgl27_alldecks_trace i
  = (fun u => tnth u.2.1 (@pgg_rho pgl27_M u.2.2 i)).
Proof.
apply: boolp.funext => u; rewrite /pgl27_alldecks_trace pgl27_procs_deck_abs.
case: i => -[|[|[|[|[|[|[|[|//]]]]]]]] Hi.
- rewrite (pgl27_abs_p0 (tnth u.2.1) u.2.2) tnth_ord_tuple.
  by congr (tnth u.2.1 (@pgg_rho pgl27_M u.2.2 _)); apply: val_inj.
- rewrite (pgl27_abs_p1 (tnth u.2.1) u.2.2) tnth_ord_tuple.
  by congr (tnth u.2.1 (@pgg_rho pgl27_M u.2.2 _)); apply: val_inj.
- rewrite (pgl27_abs_p2 (tnth u.2.1) u.2.2) tnth_ord_tuple.
  by congr (tnth u.2.1 (@pgg_rho pgl27_M u.2.2 _)); apply: val_inj.
- rewrite (pgl27_abs_p3 (tnth u.2.1) u.2.2) tnth_ord_tuple.
  by congr (tnth u.2.1 (@pgg_rho pgl27_M u.2.2 _)); apply: val_inj.
- rewrite (pgl27_abs_p4 (tnth u.2.1) u.2.2) tnth_ord_tuple.
  by congr (tnth u.2.1 (@pgg_rho pgl27_M u.2.2 _)); apply: val_inj.
- rewrite (pgl27_abs_p5 (tnth u.2.1) u.2.2) tnth_ord_tuple.
  by congr (tnth u.2.1 (@pgg_rho pgl27_M u.2.2 _)); apply: val_inj.
- rewrite (pgl27_abs_p6 (tnth u.2.1) u.2.2) tnth_ord_tuple.
  by congr (tnth u.2.1 (@pgg_rho pgl27_M u.2.2 _)); apply: val_inj.
- rewrite (pgl27_abs_p7 (tnth u.2.1) u.2.2) tnth_ord_tuple.
  by congr (tnth u.2.1 (@pgg_rho pgl27_M u.2.2 _)); apply: val_inj.
Qed.

(** pgl27_alldecks_trace_full — player i's full executed trace over the
    all-decks sampler is the index marker and the singleton hand holding the
    dealt card; the trace is a deterministic function of that single card.
    @main security: the full all-decks executed player trace carries no more
    information about the secret than its single dealt-card content. *)
Lemma pgl27_alldecks_trace_full (i : 'I_8)
    (u : bool * (8.-tuple 'I_8 * pgg_gT pgl27_M)) :
  nth [::] (run_interp pgl27_fuel (pgl27_procs_deck u.2.1 u.2.2)).2 (2 + i)
  = [:: PGG_idx 0; PGG_hand [:: pgl27_alldecks_trace i u]].
Proof.
rewrite pgl27_procs_deck_abs pgl27_alldecks_trace_E.
case: i => -[|[|[|[|[|[|[|[|//]]]]]]]] Hi.
- have -> : (@Ordinal 8 0 Hi) = (@Ordinal 8 0 isT) by apply: val_inj.
  by rewrite (pgl27_full_p0 (tnth u.2.1) u.2.2) tnth_ord_tuple.
- have -> : (@Ordinal 8 1 Hi) = (@Ordinal 8 1 isT) by apply: val_inj.
  by rewrite (pgl27_full_p1 (tnth u.2.1) u.2.2) tnth_ord_tuple.
- have -> : (@Ordinal 8 2 Hi) = (@Ordinal 8 2 isT) by apply: val_inj.
  by rewrite (pgl27_full_p2 (tnth u.2.1) u.2.2) tnth_ord_tuple.
- have -> : (@Ordinal 8 3 Hi) = (@Ordinal 8 3 isT) by apply: val_inj.
  by rewrite (pgl27_full_p3 (tnth u.2.1) u.2.2) tnth_ord_tuple.
- have -> : (@Ordinal 8 4 Hi) = (@Ordinal 8 4 isT) by apply: val_inj.
  by rewrite (pgl27_full_p4 (tnth u.2.1) u.2.2) tnth_ord_tuple.
- have -> : (@Ordinal 8 5 Hi) = (@Ordinal 8 5 isT) by apply: val_inj.
  by rewrite (pgl27_full_p5 (tnth u.2.1) u.2.2) tnth_ord_tuple.
- have -> : (@Ordinal 8 6 Hi) = (@Ordinal 8 6 isT) by apply: val_inj.
  by rewrite (pgl27_full_p6 (tnth u.2.1) u.2.2) tnth_ord_tuple.
- have -> : (@Ordinal 8 7 Hi) = (@Ordinal 8 7 isT) by apply: val_inj.
  by rewrite (pgl27_full_p7 (tnth u.2.1) u.2.2) tnth_ord_tuple.
Qed.

(** pgl27_alldecks_point_indep — one player's dealt card under the all-decks
    sampler is independent of the secret.
    @composes: pgl27_alldecks_trace_secrecy *)
Lemma pgl27_alldecks_point_indep (i : 'I_8) :
  pgl27P_alldecks |= (fun u => tnth u.2.1 (@pgg_rho pgl27_M u.2.2 i))
              _|_ pgl27_alldecks_secret.
Proof.
have Hcard : (#|[set i]| <= 3)%N by rewrite cards1.
have Hview := pgl27_view_indep_alldecks R (C := [set i]) Hcard.
have -> : (fun u : bool * (8.-tuple 'I_8 * pgg_gT pgl27_M) =>
             tnth u.2.1 (@pgg_rho pgl27_M u.2.2 i))
        = (fun f : {ffun 'I_8 -> 'I_8} => f i)
          `o alldecks_view (R:=R) (@pgg_rho pgl27_M)
               (fdist_uniform card_bool) pgl27_G_pos
               pgl27_class_decks_pos [set i].
  by apply: boolp.funext => u;
     rewrite /comp_RV /alldecks_view ffunE in_set1 eqxx.
exact: (inde_RV_comp (fun f : {ffun 'I_8 -> 'I_8} => f i) Hview).
Qed.

(** pgl27_alldecks_trace_secrecy — a single corrupted player's executed trace
    of the all-decks run leaves the secret's conditional entropy equal to its
    plain entropy.
    @main security: single-player executed-trace secrecy under the all-decks
    dealer, via the executed-trace bridge with cancel = id. *)
Lemma pgl27_alldecks_trace_secrecy (i : 'I_8) :
  `H( pgl27_alldecks_secret | pgl27_alldecks_trace i )
  = `H `p_ pgl27_alldecks_secret.
Proof.
apply: (trace_secrecy_of_view
          (view := (fun u => tnth u.2.1 (@pgg_rho pgl27_M u.2.2 i)))
          (trace_of := id) (view_of := id)).
- by rewrite pgl27_alldecks_trace_E.
- by [].
- exact: pgl27_alldecks_point_indep i.
Qed.

(** pgl27_alldecks_coalition_trace — the coalition's joint executed-trace
    record over the all-decks sampler: the dealt card each member of C
    observes, and ord0 outside C.
    @intent: the coalition's joint executed trace of the all-decks run. *)
Definition pgl27_alldecks_coalition_trace (C : {set 'I_8}) :
    {RV pgl27P_alldecks -> {ffun 'I_8 -> 'I_8}} :=
  fun u => [ffun i => if i \in C then pgl27_alldecks_trace i u else ord0].

(** pgl27_alldecks_coalition_trace_E — the coalition's joint executed trace
    over the all-decks sampler equals its all-decks coalition view.
    @composes: pgl27_alldecks_coalition_secrecy *)
Lemma pgl27_alldecks_coalition_trace_E (C : {set 'I_8}) :
  pgl27_alldecks_coalition_trace C
  = alldecks_view (R:=R) (@pgg_rho pgl27_M) (fdist_uniform card_bool)
      pgl27_G_pos pgl27_class_decks_pos C.
Proof.
apply: boolp.funext => u; apply/ffunP => i.
rewrite /pgl27_alldecks_coalition_trace /alldecks_view !ffunE.
case: ifP => // _.
by rewrite (pgl27_alldecks_trace_E i).
Qed.

(** pgl27_alldecks_coalition_secrecy — the joint executed trace of any
    coalition of at most three cards under the all-decks dealer leaves the
    secret's conditional entropy equal to its plain entropy.
    @main security: coalition executed-trace secrecy under the all-decks
    dealer, via the executed-trace bridge with cancel = id. *)
Lemma pgl27_alldecks_coalition_secrecy (C : {set 'I_8}) :
  (#|C| <= 3)%N ->
  `H( pgl27_alldecks_secret | pgl27_alldecks_coalition_trace C )
  = `H `p_ pgl27_alldecks_secret.
Proof.
move=> HC.
apply: (trace_secrecy_of_view
          (view := alldecks_view (R:=R) (@pgg_rho pgl27_M)
                     (fdist_uniform card_bool) pgl27_G_pos
                     pgl27_class_decks_pos C)
          (trace_of := id) (view_of := id)).
- by rewrite pgl27_alldecks_coalition_trace_E.
- by [].
- exact: (pgl27_view_indep_alldecks R (C:=C) HC).
Qed.

(* -------------------------------------------------------------------------- *)
(* Shuffle-free dealer: executed-trace secrecy when a uniform valid deck of   *)
(* the secret's class is dealt at the identity cut, with no shuffle at all.   *)
(* -------------------------------------------------------------------------- *)

(** pgl27P_deck — the shuffle-free all-decks joint law: a uniform orbit
    secret and a uniform valid deck of its class, no cut.
    @intent: the shuffle-free dealer sample space of the executed run. *)
Definition pgl27P_deck : R.-fdist (bool * 8.-tuple 'I_8) :=
  uniform_deckP (fdist_uniform card_bool) (R:=R) pgl27_class_decks_pos.

(** pgl27_deck_secret — the dealt orbit-class secret component.
    @intent: the orbit-secret random variable of the shuffle-free run. *)
Definition pgl27_deck_secret : {RV pgl27P_deck -> bool} := fun u => u.1.

(** pgl27_deck_trace — player i's executed-trace content when the sampled
    deck is dealt at the identity cut.
    @intent: single-player executed trace of the shuffle-free run. *)
Definition pgl27_deck_trace (i : 'I_8) : {RV pgl27P_deck -> 'I_8} :=
  fun u =>
    content_of
      (nth [::] (run_interp pgl27_fuel (pgl27_procs_deck u.2 1%g)).2 (2 + i)).

(** pgl27_deck_trace_E — the shuffle-free player trace is the dealt card at
    the player's own position.
    @composes: pgl27_deck_trace_secrecy *)
Lemma pgl27_deck_trace_E (i : 'I_8) :
  pgl27_deck_trace i = (fun u => tnth u.2 i).
Proof.
apply: boolp.funext => u; rewrite /pgl27_deck_trace pgl27_procs_deck_abs.
case: i => -[|[|[|[|[|[|[|[|//]]]]]]]] Hi.
- rewrite (pgl27_abs_p0 (tnth u.2) 1%g) tnth_ord_tuple morph1 perm1.
  by congr (tnth u.2 _); apply: val_inj.
- rewrite (pgl27_abs_p1 (tnth u.2) 1%g) tnth_ord_tuple morph1 perm1.
  by congr (tnth u.2 _); apply: val_inj.
- rewrite (pgl27_abs_p2 (tnth u.2) 1%g) tnth_ord_tuple morph1 perm1.
  by congr (tnth u.2 _); apply: val_inj.
- rewrite (pgl27_abs_p3 (tnth u.2) 1%g) tnth_ord_tuple morph1 perm1.
  by congr (tnth u.2 _); apply: val_inj.
- rewrite (pgl27_abs_p4 (tnth u.2) 1%g) tnth_ord_tuple morph1 perm1.
  by congr (tnth u.2 _); apply: val_inj.
- rewrite (pgl27_abs_p5 (tnth u.2) 1%g) tnth_ord_tuple morph1 perm1.
  by congr (tnth u.2 _); apply: val_inj.
- rewrite (pgl27_abs_p6 (tnth u.2) 1%g) tnth_ord_tuple morph1 perm1.
  by congr (tnth u.2 _); apply: val_inj.
- rewrite (pgl27_abs_p7 (tnth u.2) 1%g) tnth_ord_tuple morph1 perm1.
  by congr (tnth u.2 _); apply: val_inj.
Qed.

(** pgl27_deck_point_indep — one player's dealt card under the shuffle-free
    dealer is independent of the secret.
    @composes: pgl27_deck_trace_secrecy *)
Lemma pgl27_deck_point_indep (i : 'I_8) :
  pgl27P_deck |= (fun u => tnth u.2 i) _|_ pgl27_deck_secret.
Proof.
have Hcard : (#|[set i]| <= 3)%N by rewrite cards1.
have Hview := pgl27_view_indep_deck R (C := [set i]) Hcard.
have -> : (fun u : bool * 8.-tuple 'I_8 => tnth u.2 i)
        = (fun f : {ffun 'I_8 -> 'I_8} => f i)
          `o uniform_deck_view (R:=R) (fdist_uniform card_bool)
               pgl27_class_decks_pos [set i].
  by apply: boolp.funext => u;
     rewrite /comp_RV /uniform_deck_view ffunE in_set1 eqxx.
exact: (inde_RV_comp (fun f : {ffun 'I_8 -> 'I_8} => f i) Hview).
Qed.

(** pgl27_deck_trace_secrecy — a single corrupted player's executed trace of
    the shuffle-free run leaves the secret's conditional entropy equal to its
    plain entropy.
    @main security: shuffle-free executed-trace secrecy. *)
Lemma pgl27_deck_trace_secrecy (i : 'I_8) :
  `H( pgl27_deck_secret | pgl27_deck_trace i ) = `H `p_ pgl27_deck_secret.
Proof.
apply: (trace_secrecy_of_view (view := (fun u => tnth u.2 i))
          (trace_of := id) (view_of := id)).
- by rewrite pgl27_deck_trace_E.
- by [].
- exact: pgl27_deck_point_indep i.
Qed.

(** pgl27_deck_coalition_trace — the coalition's joint executed-trace record
    of the shuffle-free run, ord0 outside C.
    @intent: the coalition's joint executed trace of the shuffle-free run. *)
Definition pgl27_deck_coalition_trace (C : {set 'I_8}) :
    {RV pgl27P_deck -> {ffun 'I_8 -> 'I_8}} :=
  fun u => [ffun i => if i \in C then pgl27_deck_trace i u else ord0].

(** pgl27_deck_coalition_trace_E — the coalition's joint executed trace of
    the shuffle-free run equals its shuffle-free coalition view.
    @composes: pgl27_deck_coalition_secrecy *)
Lemma pgl27_deck_coalition_trace_E (C : {set 'I_8}) :
  pgl27_deck_coalition_trace C
  = uniform_deck_view (R:=R) (fdist_uniform card_bool)
      pgl27_class_decks_pos C.
Proof.
apply: boolp.funext => u; apply/ffunP => i.
rewrite /pgl27_deck_coalition_trace /uniform_deck_view !ffunE.
case: ifP => // _.
by rewrite (pgl27_deck_trace_E i).
Qed.

(** pgl27_deck_coalition_secrecy — the joint executed trace of any coalition
    of at most three cards under the shuffle-free dealer leaves the secret's
    conditional entropy equal to its plain entropy.
    @main security: shuffle-free coalition executed-trace secrecy. *)
Lemma pgl27_deck_coalition_secrecy (C : {set 'I_8}) :
  (#|C| <= 3)%N ->
  `H( pgl27_deck_secret | pgl27_deck_coalition_trace C )
  = `H `p_ pgl27_deck_secret.
Proof.
move=> HC.
apply: (trace_secrecy_of_view
          (view := uniform_deck_view (R:=R) (fdist_uniform card_bool)
                     pgl27_class_decks_pos C)
          (trace_of := id) (view_of := id)).
- by rewrite pgl27_deck_coalition_trace_E.
- by [].
- exact: (pgl27_view_indep_deck R (C:=C) HC).
Qed.

End pgl27_trace_sec.
