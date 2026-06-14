(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Cyclic-cut family leakage data: a uniform cut makes a sub-threshold card   *)
(* view independent of the secret. The concrete den Boer and kim witnesses    *)
(* (built from five_card_leakage's counting) live in the instance files.       *)
(******************************************************************************)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype finfun finset bigop ssralg ssrnum reals.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
From pgg_smc Require Import pgg_leakage_witness.

Import GRing.Theory Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Section cyclic_cut.
Variable R : realType.
Variable U : finType.
Variable P : R.-fdist U.

(** CyclicCutData — a card-family secret with a sub-threshold view that a
    uniform cyclic cut renders independent of it.
    @intent: the cyclic-cut analogue of RandomizedSharing; the secret and view
    finTypes are fields so card instances (bool secret) inhabit it. *)
Record CyclicCutData := MkCyclicCutData {
  ccd_secretT : finType ;
  ccd_viewT   : finType ;
  ccd_secret  : {RV P -> ccd_secretT} ;
  ccd_view    : {RV P -> ccd_viewT} ;
  ccd_indep   : P |= ccd_view _|_ ccd_secret }.

(** cyclic_cut_leakage — the leakage witness carried by cyclic-cut data.
    @composes: mechanism_leakage *)
Definition cyclic_cut_leakage (cc : CyclicCutData) : LeakageWitness P :=
  let: MkCyclicCutData sT vT sec view ind := cc in
  @MkLeakageWitness _ _ P sT vT sec view ind.

End cyclic_cut.

Arguments CyclicCutData {R U} P.
Arguments cyclic_cut_leakage {R U P}.
