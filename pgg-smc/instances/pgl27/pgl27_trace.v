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
(*   pgl27_trace_secrecy           == one player's trace keeps the secret     *)
(*   pgl27_coalition_trace_secrecy == any <= 3 coalition trace keeps it       *)
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

End abstract_leaf.

(** pgl27_procs_abs — the concrete run at secret s and cut w0 is the abstract
    run with the dealt readout tnth (orbit_encode s).
    @composes: pgl27_player_trace_E *)
Lemma pgl27_procs_abs (s : bool) (w0 : pgg_gT pgl27_M) :
  pgl27_procs s w0 = pgl27_aprocs_abs (tnth (orbit_encode s)) w0.
Proof. by []. Qed.

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

End pgl27_trace_sec.
