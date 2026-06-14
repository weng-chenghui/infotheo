(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* The sharing-mechanism family marker: an instance is either an additive     *)
(* (one-time-pad) sharing or a cyclic-cut card scheme, and either dispatches   *)
(* to the common LeakageWitness consumed by the generic secrecy tail.          *)
(******************************************************************************)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype finfun finset bigop ssralg ssrnum reals.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
From pgg_smc Require Import pgg_leakage_witness pgg_randomized_sharing.
From pgg_smc Require Import pgg_cyclic_cut_leakage.

Import GRing.Theory Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Section sharing_mechanism.
Variable R : realType.
Variable U : finType.
Variable P : R.-fdist U.
Variable N' T' : nat.

(** SharingMechanism — the randomization mechanism of a PGG instance: an
    additive T-of-T one-time-pad sharing, or a cyclic-cut card scheme.
    @intent: the family marker over the two randomization mechanisms; the
    Additive branch fixes the additive dimensions, the CyclicCut branch ignores
    them. *)
Variant SharingMechanism :=
  | Additive  (rs : RandomizedSharing P N' T')
              (C : {set 'I_T'.+1}) (HC : (#|C| < T'.+1)%N)
  | CyclicCut (cc : CyclicCutData P).

(** mechanism_leakage — the leakage witness a mechanism dispatches to.
    @intent: maps each family to the one LeakageWitness type, which is possible
    because LeakageWitness packs the secret and view finTypes as fields. *)
Definition mechanism_leakage (m : SharingMechanism) : LeakageWitness P :=
  match m with
  | Additive rs C HC => additive_leakage rs HC
  | CyclicCut cc     => cyclic_cut_leakage cc
  end.

End sharing_mechanism.

Arguments SharingMechanism {R U} P N' T'.
Arguments mechanism_leakage {R U P N' T'}.
