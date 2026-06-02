(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Invariant-Submodule Profiler                                               *)
(*                                                                            *)
(* The "available dimensions" half of early feasibility rejection. A wired    *)
(* secret-sharing instance assigns shares along a group action on a vector    *)
(* space; the recoverable structure is a G-invariant submodule (a submodule   *)
(* in the representation-theoretic sense). This file packages, for a fixed     *)
(* finite-group representation rG : mx_representation F G n and a chosen        *)
(* secret coordinate e0, the predicates                                        *)
(*   inv_dim d         : some G-invariant submodule has dimension d;           *)
(*   secret_inv_dim d  : some G-invariant submodule of dimension d actually    *)
(*                       carries the secret coordinate e0 (e0 lies in its row  *)
(*                       space);                                               *)
(*   feasible window   : some dimension required by the gate (a member of      *)
(*                       window) is achievable as a secret-encoding invariant. *)
(* The gap_dimension.v window supplies the required dimensions; this profiler  *)
(* supplies the available secret-encoding dimensions; the cs_gap_feasible gate *)
(* rejects an instance when the two are disjoint. The Maschke lemma records     *)
(* the regime (coprime characteristic) in which the available dimensions are    *)
(* closed under complementation, i.e. the cheap subset-sum reasoning is valid;  *)
(* the s5_nogo.v instance is precisely the MODULAR regime where it fails.       *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect all_fingroup all_algebra all_solvable.
From mathcomp Require Import mxrepresentation.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Section invariant_profiler.

Variable F : fieldType.
Variable gT : finGroupType.
Variable G : {group gT}.
Variable n : nat.
Variable rG : mx_representation F G n.
Variable e0 : 'rV[F]_n.

(** inv_dim — a G-invariant submodule of a given dimension exists.
    Kind: main.
    What: inv_dim d holds when some matrix U (with m rows) is a G-submodule of
          the representation rG and has rank exactly d, i.e. the representation
          admits an invariant subspace of dimension d.
    Why: the unguarded "available dimensions" profile of the representation,
         used as the substrate for the secret-encoding refinement secret_inv_dim
         and, through it, for the feasibility gate. *)
Definition inv_dim (d : nat) : Prop :=
  exists m (U : 'M[F]_(m, n)), mxmodule rG U /\ \rank U = d.

(** secret_inv_dim — a secret-encoding G-invariant submodule of a given
    dimension exists.
    Kind: main.
    What: secret_inv_dim d holds when some G-submodule U of rG has rank d and
          carries the secret coordinate e0, namely (e0 <= U)%MS (e0 lies in the
          row space of U).
    Why: only invariant submodules containing the secret direction can encode
         the secret; the no-go theorem (s5_nogo.v) refutes this at the gate's
         required dimensions, proving the wired instance impossible. The
         membership form (e0 <= U)%MS is chosen over the "not inside the
         secret-zero hyperplane" form because the no-go reduction works directly
         with "U contains e0": such a U decomposes as <e0> (+) (U cap P),
         reducing a dimension-d secret-encoding submodule to a dimension-(d-1)
         submodule of the natural permutation module P. *)
Definition secret_inv_dim (d : nat) : Prop :=
  exists m (U : 'M[F]_(m, n)),
    [/\ mxmodule rG U, \rank U = d & (e0 <= U)%MS].

(** feasible — some gate-required dimension is achievable as a secret-encoding
    invariant submodule.
    Kind: main.
    What: feasible window holds when there is a dimension d in the list window
          for which secret_inv_dim d holds.
    Why: the gate side of early rejection. gap_dimension.v computes the window
         of dimensions a feasible covering scheme would need; feasible window
         asserts at least one of them is realised by a secret-encoding invariant
         submodule. The no-go theorem proves ~ feasible rG e0 [:: 3; 4] for the
         S_5 instance, so the gate rejects it before any code is built. *)
Definition feasible (window : seq nat) : Prop :=
  exists d, d \in window /\ secret_inv_dim d.

(** maschke_ss — Maschke's theorem in coprime characteristic: the full module
    is completely reducible.
    Kind: main.
    What: when G is a p'-group for every p dividing the characteristic of F
          (the hypothesis pgroup [pchar F]^' G), the regular module 1%:M of rG
          is completely reducible; this is a direct specialisation of
          mx_Maschke_pchar.
    Why: documents the regime in which the available invariant dimensions are
         closed under taking complements, so the cheap subset-sum reasoning over
         the dimension profile is sound. The S_5-on-GF(5)^6 instance violates
         this hypothesis (5 divides both the number of permuted points and the
         characteristic of GF(5)), which is exactly why its profile is uniserial
         and the no-go theorem bites. *)
Lemma maschke_ss :
  pgroup [pchar F]^' G -> mx_completely_reducible rG 1%:M.
Proof. exact: mx_Maschke_pchar. Qed.

End invariant_profiler.

Arguments inv_dim {F gT G n} rG d.
Arguments secret_inv_dim {F gT G n} rG e0 d.
Arguments feasible {F gT G n} rG e0 window.
