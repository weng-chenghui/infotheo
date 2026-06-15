(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Executed-trace bridge: a single player's recorded trace, determined by the *)
(* player's view through a global cancel, has the same conditional entropy of  *)
(* the secret as the view itself, so view secrecy transports to trace secrecy. *)
(******************************************************************************)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype finfun finset bigop ssralg ssrnum reals.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
From pgg_smc Require Import pgg_leakage_witness.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Section TraceTransport.
Context {R : realType} {U : finType} {P : R.-fdist U}.

(** inde_RV_comp — independence of a view from the secret is preserved by
    deterministic post-processing of the view, reducing a coalition's structured
    view to one player's single share.
    @composes: trace_secrecy_of_view *)
Lemma inde_RV_comp (secretT viewT viewT' : finType)
    (secret : {RV P -> secretT}) (view : {RV P -> viewT}) (f : viewT -> viewT') :
  P |= view _|_ secret -> P |= (f `o view) _|_ secret.
Proof. by move=> Hindep; exact: (proba.inde_RV_comp f idfun Hindep). Qed.

(** trace_secrecy_of_view — a single player's executed trace, recorded in a
    content finType determined by the player's view through a global cancel,
    leaves the secret's conditional entropy equal to its plain entropy.
    @main security: trace secrecy follows from view secrecy. *)
Lemma trace_secrecy_of_view (secretT viewT traceT : finType)
    (secret : {RV P -> secretT}) (view : {RV P -> viewT})
    (player_trace : {RV P -> traceT})
    (trace_of : viewT -> traceT) (view_of : traceT -> viewT) :
  player_trace = trace_of `o view ->
  cancel trace_of view_of ->
  P |= view _|_ secret ->
  `H( secret | player_trace ) = `H `p_ secret.
Proof.
move=> Htrace Hcancel Hindep.
have Hview : view = view_of `o player_trace.
  rewrite Htrace; apply: boolp.funext => u /=.
  by rewrite /comp_RV Hcancel.
rewrite -(centropy_RV_contraction secret player_trace view_of).
rewrite -Hview centropyC.
rewrite Htrace centropy_RV_contraction.
exact: (proj2 (leakage_of_view_indep secret view Hindep)).
Qed.

(** trace_secrecy_of_witness — the per-instance entry point packaging the trace
    transport for a LeakageWitness whose view has already been reduced to the
    trace-content finType.
    @composes: trace_secrecy_of_view *)
Lemma trace_secrecy_of_witness (lw : LeakageWitness P) (traceT : finType)
    (player_trace : {RV P -> traceT})
    (trace_of : lw_viewT lw -> traceT) (view_of : traceT -> lw_viewT lw) :
  player_trace = trace_of `o lw.(lw_view) ->
  cancel trace_of view_of ->
  `H( lw.(lw_secret) | player_trace ) = `H `p_ lw.(lw_secret).
Proof.
move=> Htr Hcan; apply: trace_secrecy_of_view.
- exact: Htr.
- exact: Hcan.
- exact: lw_indep.
Qed.

End TraceTransport.
