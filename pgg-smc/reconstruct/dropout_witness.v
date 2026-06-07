(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* DropoutWitness: Capability obligation on top of ThresholdWitness          *)
(*                                                                            *)
(* ThresholdWitness is purely structural: it says the covering's parameters   *)
(* fit together legally. DropoutWitness is a capability claim: a specific     *)
(* decoder exists meeting a specific bound. Different kinds of obligations,   *)
(* even though both attach to the same CoveringScheme.                        *)
(*                                                                            *)
(* The structural obligations come from CoveringData + CoveringScheme +       *)
(* ThresholdWitness: privacy threshold k, total share count T, monodromy      *)
(* permutation invariance, the gap inequality T <= k + 2g. The capability     *)
(* obligation answers a different question: given the full deck and a set    *)
(* of revealed positions of size at least dw_min_revealed, can the recovery  *)
(* function return the unique secret while remaining G-equivariant under     *)
(* the monodromy shuffle? The structural layer cannot answer that on its     *)
(* own; it only bounds what is possible (cs_gap T - k as a ceiling, 2g as a  *)
(* curve-derived bound). DropoutWitness is the place where a concrete        *)
(* recovery function, when constructed, is recorded.                          *)
(*                                                                            *)
(* The framework currently provides NO instance of DropoutWitness. The s5x5  *)
(* abstract's "five-card dropout tolerance" target corresponds to            *)
(* constructing a DropoutWitness with dw_min_revealed = k + 1 = 6 for the    *)
(* s5x5 covering scheme. That construction is open future work.              *)
(*                                                                            *)
(* Record:                                                                    *)
(*   DropoutWitness M tw == capability witness on a ThresholdWitness:        *)
(*                          a G-equivariant recovery function from any       *)
(*                          revealed subset of size >= dw_min_revealed       *)
(*                                                                            *)
(* Derived:                                                                   *)
(*   dw_dropout          == T - dw_min_revealed                              *)
(*   dw_dropout_leq_gap  == dropout count <= T - k                           *)
(*   dw_dropout_bound    == dropout count <= 2 * cd_genus                    *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop.
From pgg_smc Require Import pgg_interface.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    cover_tradeoff algebraic_rigidity.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     DropoutWitness Record                                                  *)
(******************************************************************************)

Section dropout_witness_def.

Variable M : MonodromyReprWithGeneratorType.
Variable tw : ThresholdWitness M.

(* Local aliases. The covering scheme threshold has secret and share types
   'I_N where N = (pgg_N' M).+1; these come from [cs_scheme]'s declared type
   in covering_scheme.v:122. ts_T ts and (ts_T' ts).+1 are definitionally
   equal (see ts_T at pgg_sharing_framework.v), so the codomain of
   rp_monodromy (cs_plug cs) g is interchangeable with {perm 'I_(ts_T ts)}. *)
Let N : nat := (pgg_N' M).+1.
Let cs : CoveringScheme M := tw_covering tw.
Let ts : ThresholdScheme 'I_N 'I_N := cs_scheme cs.
Let shareT : Type := 'I_N.
Let secretT : Type := 'I_N.

Record DropoutWitness := MkDropoutWitness {

  (** Minimum number of cards that must be face-up for the protocol to
      recover the secret. *)
  dw_min_revealed : nat ;

  (** Privacy floor: the reveal count is at least the privacy
      threshold k. A coalition of fewer than k shares learns nothing
      about the secret (per the privacy lemma); recovery from exactly
      k shares is consistent with this, since the privacy lemma is
      silent at |C| = k. *)
  dw_min_revealed_ge_ts_k :
    (ts_k ts <= dw_min_revealed)%N ;

  (** Total-deck ceiling: the reveal count cannot exceed the total card
      count T. *)
  dw_min_revealed_leq_T :
    (dw_min_revealed <= ts_T ts)%N ;

  (** Partial recovery: given the set [visible] of revealed card positions
      and the full deck record, return the secret. The recovery function
      is only constrained to be correct when [#|visible| >= dw_min_revealed];
      see [dw_recover_uses_revealed_only] and [dw_recover_shuffle_invariant]
      below for the obligations under that condition. *)
  dw_recover_from_revealed :
    {set 'I_(ts_T ts)} -> (ts_T ts).-tuple shareT -> secretT ;

  (** Revealed-only dependence: when at least [dw_min_revealed] positions
      are visible, recovery looks at the revealed cards only. Two decks
      agreeing on every revealed position give the same secret, no matter
      what is on the face-down cards. *)
  dw_recover_uses_revealed_only :
    forall (visible : {set 'I_(ts_T ts)})
           (sh1 sh2 : (ts_T ts).-tuple shareT),
      (dw_min_revealed <= #|visible|)%N ->
      (forall i, i \in visible -> tnth sh1 i = tnth sh2 i) ->
      dw_recover_from_revealed visible sh1 =
      dw_recover_from_revealed visible sh2 ;

  (** Shuffle invariance: recovery commutes with the monodromy shuffle
      induced by the deck-group action. Shuffling the deck by [g] and then
      revealing at least [dw_min_revealed] positions still yields the same
      secret. Parallels [ts_recon_perm_invariant] in
      [pgg_sharing_framework.v]. Taking g = 1 specialises to plain
      correctness; general g records the G-equivariance the framework
      requires. *)
  dw_recover_shuffle_invariant :
    forall (g : pgg_gT M) (s : secretT)
           (shares : (ts_T ts).-tuple shareT)
           (visible : {set 'I_(ts_T ts)}),
      (dw_min_revealed <= #|visible|)%N ->
      g \in pgg_G M ->
      ts_valid ts s shares ->
      dw_recover_from_revealed visible
        [tuple tnth shares (rp_monodromy (cs_plug cs) g i) | i < ts_T ts] = s ;
}.

End dropout_witness_def.

Arguments DropoutWitness {M} tw.
Arguments MkDropoutWitness {M tw}.

(******************************************************************************)
(*     Derived: dropout count and its bounds                                  *)
(******************************************************************************)

Section dropout_witness_derived.

Variable M : MonodromyReprWithGeneratorType.
Variable tw : ThresholdWitness M.
Let cs := tw_covering tw.
Let ts := cs_scheme cs.

(** dw_dropout — the dropout count of a DropoutWitness: number of cards
    that may be face-down while the recovery function still returns
    the secret.
    Kind: definition.
    Why: the operational accessor on the card-protocol side, parallel
    to [cs_gap] on the structural side. *)
Definition dw_dropout (dw : DropoutWitness tw) : nat :=
  ts_T ts - dw_min_revealed dw.

(** dw_dropout_leq_gap — the dropout count is bounded above by the
    privacy-vs-reveal gap T - k.
    Kind: helper.
    Why: an honest dropout decoder cannot drop more cards than the
    structural privacy-vs-reveal gap allows. *)
Lemma dw_dropout_leq_gap (dw : DropoutWitness tw) :
  (dw_dropout dw <= ts_T ts - ts_k ts)%N.
Proof.
rewrite /dw_dropout.
apply: leq_sub2l.
exact: (dw_min_revealed_ge_ts_k dw).
Qed.

(** dw_dropout_bound — the dropout count is bounded above by twice the
    genus of the covering curve. Parallels [ar_gap_bound]
    (algebraic_rigidity.v) on the structural side.
    Kind: main.
    Why: the operational rigidity statement on the card-protocol side;
    binds the dropout count to the geometric invariant of the curve. *)
Lemma dw_dropout_bound (dw : DropoutWitness tw) :
  (dw_dropout dw <= 2 * cd_genus (cs_data cs))%N.
Proof.
apply: leq_trans (dw_dropout_leq_gap dw) _.
exact: gap_bound.
Qed.

End dropout_witness_derived.
