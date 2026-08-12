(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe B, mutation check: the bundle's rho index and its optional slots     *)
(* still discriminate                                                         *)
(*                                                                            *)
(* The split of SecurityWitness into ShuffleMarginalBound plus                *)
(* ShuffleCertificateBundle keeps the exact-equality certificate indexed by    *)
(* the bound's own distribution. This file checks that the index still binds:  *)
(*                                                                            *)
(*   M1a  a certificate for the same group at a different word length cannot   *)
(*        be attached to the length-1 bound (same M, different rho term);      *)
(*   M1b  a five-card certificate cannot be attached to the eight-card orbit   *)
(*        bound (different M, different rho term);                             *)
(*   M2   a bundle whose exact slot is emptied no longer satisfies the         *)
(*        exact-projection equation of its unmutated twin;                     *)
(*   M3   the same for the asymptotic slot.                                    *)
(*                                                                            *)
(* Each rejection is wrapped in Fail, so the file compiles green exactly when  *)
(* all four are rejected. The unmutated twins are declared first as positive   *)
(* controls, so a Fail cannot pass by a mistake shared with the honest case.   *)
(* For M2 and M3 the None-shape and isSome facts below the Fail show that the  *)
(* rejected equation is not merely beyond by [] but false.                     *)
(*                                                                            *)
(* The message quoted above each Fail is the verbatim diagnostic obtained by   *)
(* removing that one Fail and re-elaborating the declaration, one per run:     *)
(* batch mode does not echo the message of a Fail that succeeds. M1b and M2   *)
(* were harvested by a full rebuild.sh run each; M1a and M3 were harvested    *)
(* under the interactive checker, which reproduced both batch messages        *)
(* character for character.                                                   *)
(*                                                                            *)
(* Module WS below repeats the two revised records, the two Arguments lines    *)
(* they need and the two converters of probe_b_witness_split.v. It is a copy   *)
(* rather than an import because the probe directory carries a dash-bearing    *)
(* name and so is not a legal Rocq logical path under the -R flags of          *)
(* rebuild.sh.                                                                 *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_weighted_words.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    algebraic_rigidity.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_scheme_I5.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_profile.
From pgg_smc Require Import pgl27_group pgl27_scheme pgl27_profile.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.

(******************************************************************************)
(*     The two revised records (copied from probe_b_witness_split.v)          *)
(******************************************************************************)

Module WS.

(** ShuffleMarginalBound — the single-position marginal bound of a shuffle
    distribution against the uniform distribution on sheets.
    @intent: the four always-present fields of algebraic_rigidity.v:147-157. *)
Record ShuffleMarginalBound (R : realType) (M : MonodromyReprWithGeneratorType)
  := MkShuffleMarginalBound {
  sw_L : nat;
  sw_bound_eps : R;
  sw_rho_dist : R.-fdist {perm 'I_(pgg_N' M).+1};
  sw_bound : forall s,
    (var_dist (fdistmap (fun sigma : {perm 'I_(pgg_N' M).+1} => sigma s)
                        sw_rho_dist)
              (fdist_uniform (card_ord (pgg_N' M).+1)) <= sw_bound_eps)%O }.

(** ShuffleCertificateBundle — a marginal bound together with the optional
    exact-equality and asymptotic-convergence certificates for the same
    shuffle distribution.
    @intent: the two optional fields of SecurityWitness, re-indexed on the
    bound's own sw_rho_dist. *)
Record ShuffleCertificateBundle (R : realType)
    (M : MonodromyReprWithGeneratorType) := MkShuffleCertificateBundle {
  scb_bound : ShuffleMarginalBound R M;
  scb_exact : option (SecurityExact (sw_rho_dist scb_bound));
  scb_asymptotic : option (@SecurityAsymptotic R M) }.

Arguments MkShuffleMarginalBound {R M} _ _ _ _.
Arguments MkShuffleCertificateBundle {R M} _ _ _.
Arguments ShuffleMarginalBound R M : clear implicits.
Arguments ShuffleCertificateBundle R M : clear implicits.

(** bound_of_witness — the marginal bound of an old six-field witness.
    @intent: the four always-present fields of a SecurityWitness read as a
    ShuffleMarginalBound. *)
Definition bound_of_witness R M (w : SecurityWitness R M)
  : ShuffleMarginalBound R M :=
  MkShuffleMarginalBound (algebraic_rigidity.sw_L w)
    (algebraic_rigidity.sw_bound_eps w) (algebraic_rigidity.sw_rho_dist w)
    (algebraic_rigidity.sw_bound w).

(** bundle_of_witness — the certificate bundle of an old six-field witness.
    @intent: the whole SecurityWitness read as a ShuffleCertificateBundle. *)
Definition bundle_of_witness R M (w : SecurityWitness R M)
  : ShuffleCertificateBundle R M :=
  MkShuffleCertificateBundle (bound_of_witness w)
    (algebraic_rigidity.sw_exact w) (algebraic_rigidity.sw_asymptotic w).

(******************************************************************************)
(*     The honest material                                                    *)
(******************************************************************************)

Section probe_mut.
Variable R : realType.

(** db_bound1 — the marginal bound of the unbiased five-card member at one cut.
    @intent: the bound half of fc_kim_security_witness at bias 0 and L = 1. *)
Definition db_bound1 :=
  bound_of_witness (fc_kim_security_witness (den_boer_eps0_lt R)
    (den_boer_eps0_gt R) (den_boer_eps0_spectral R) 1).

(** db_exact1 — the exact-equality certificate at bias 0 and L = 1.
    @intent: the exact slot of the same witness. *)
Definition db_exact1 :=
  algebraic_rigidity.sw_exact (fc_kim_security_witness (den_boer_eps0_lt R)
    (den_boer_eps0_gt R) (den_boer_eps0_spectral R) 1).

(** db_exact2 — the exact-equality certificate at bias 0 and L = 2.
    @intent: the same group and the same construction at a different word
    length, hence a different rho term. *)
Definition db_exact2 :=
  algebraic_rigidity.sw_exact (fc_kim_security_witness (den_boer_eps0_lt R)
    (den_boer_eps0_gt R) (den_boer_eps0_spectral R) 2).

(** db_asym1 — the asymptotic certificate at bias 0 and L = 1.
    @intent: the asymptotic slot of the same witness. *)
Definition db_asym1 :=
  algebraic_rigidity.sw_asymptotic (fc_kim_security_witness (den_boer_eps0_lt R)
    (den_boer_eps0_gt R) (den_boer_eps0_spectral R) 1).

(** db_bundle_ok — the honest bundle: the L = 1 bound with its own two
    certificates.
    @intent: the positive control for M1a, M1b, M2 and M3. *)
Definition db_bundle_ok := MkShuffleCertificateBundle db_bound1 db_exact1 db_asym1.

(** pgl27_marginal_boundB — the marginal bound of the eight-card orbit shuffle.
    @intent: the bound half of pgl27_security. *)
Definition pgl27_marginal_boundB := bound_of_witness (pgl27_security R).

(** pgl27_bundle_ok — the honest eight-card orbit bundle.
    @intent: the positive control for M1b. *)
Definition pgl27_bundle_ok := bundle_of_witness (pgl27_security R).

(******************************************************************************)
(*     M1a: same group, different word length                                 *)
(******************************************************************************)

(* Verbatim diagnostic, harvested by removing this one Fail:

     In environment
     R : realType
     The term "db_exact2" has type
      "option
         (SecurityExact
            (algebraic_rigidity.sw_rho_dist
               (fc_kim_security_witness (den_boer_eps0_lt R)
                  (den_boer_eps0_gt R) (den_boer_eps0_spectral R) 2)))"
     while it is expected to have type
      "option (SecurityExact (sw_rho_dist db_bound1))".
*)
Fail Definition db_bundle_wrong_rho :=
  MkShuffleCertificateBundle db_bound1 db_exact2 db_asym1.

(******************************************************************************)
(*     M1b: different group                                                   *)
(******************************************************************************)

(* Verbatim diagnostic, harvested by removing this one Fail:

     In environment
     R : realType
     The term "db_exact1" has type
      "option
         (SecurityExact
            (algebraic_rigidity.sw_rho_dist
               (fc_kim_security_witness (den_boer_eps0_lt R)
                  (den_boer_eps0_gt R) (den_boer_eps0_spectral R) 1)))"
     while it is expected to have type
      "option (SecurityExact (sw_rho_dist pgl27_marginal_boundB))".
*)
Fail Definition pgl27_bundle_alien_exact :=
  MkShuffleCertificateBundle pgl27_marginal_boundB db_exact1 None.

(******************************************************************************)
(*     M2: the emptied exact slot                                             *)
(******************************************************************************)

(** db_bundle_mutated_exact — the L = 1 bound with its exact slot emptied.
    @intent: the M2 mutant. *)
Definition db_bundle_mutated_exact :=
  MkShuffleCertificateBundle db_bound1 None db_asym1.

(** db_unmutated_exact_eq — the exact-projection equation on the honest bundle.
    @composes: db_bundle_ok *)
Definition db_unmutated_exact_eq : scb_exact db_bundle_ok = db_exact1 :=
  ltac:(by []).

(* Verbatim diagnostic, harvested by removing this one Fail:

     Error: No applicable tactic.
*)
Fail Definition db_mutated_exact_eq :
  scb_exact db_bundle_mutated_exact = db_exact1 := ltac:(by []).

(* The rejected equation is false, not merely beyond by []: the mutant's slot
   is None and the honest slot is Some. *)

(** db_mutated_exact_noneE — the mutant's exact slot is empty.
    @composes: db_bundle_mutated_exact *)
Definition db_mutated_exact_noneE : scb_exact db_bundle_mutated_exact = None :=
  ltac:(by []).

(** db_exact1_isSome — the honest exact slot is inhabited.
    @composes: db_bundle_ok *)
Lemma db_exact1_isSome : isSome db_exact1.
Proof. by []. Qed.

(** db_bundle_mutated_exact_boundE — the mutation touched only the exact slot.
    @composes: db_bundle_mutated_exact *)
Lemma db_bundle_mutated_exact_boundE :
  scb_bound db_bundle_mutated_exact = db_bound1.
Proof. by []. Qed.

(******************************************************************************)
(*     M3: the emptied asymptotic slot                                        *)
(******************************************************************************)

(** db_bundle_mutated_asym — the L = 1 bound with its asymptotic slot emptied.
    @intent: the M3 mutant. *)
Definition db_bundle_mutated_asym :=
  MkShuffleCertificateBundle db_bound1 db_exact1 None.

(** db_unmutated_asym_eq — the asymptotic-projection equation on the honest
    bundle.
    @composes: db_bundle_ok *)
Definition db_unmutated_asym_eq : scb_asymptotic db_bundle_ok = db_asym1 :=
  ltac:(by []).

(* Verbatim diagnostic, harvested by removing this one Fail:

     Error: No applicable tactic.
*)
Fail Definition db_mutated_asym_eq :
  scb_asymptotic db_bundle_mutated_asym = db_asym1 := ltac:(by []).

(** db_mutated_asym_noneE — the mutant's asymptotic slot is empty.
    @composes: db_bundle_mutated_asym *)
Definition db_mutated_asym_noneE :
  scb_asymptotic db_bundle_mutated_asym = None := ltac:(by []).

(** db_asym1_isSome — the honest asymptotic slot is inhabited.
    @composes: db_bundle_ok *)
Lemma db_asym1_isSome : isSome db_asym1.
Proof. by []. Qed.

(** db_bundle_mutated_asym_boundE — the mutation touched only the asymptotic
    slot.
    @composes: db_bundle_mutated_asym *)
Lemma db_bundle_mutated_asym_boundE :
  scb_bound db_bundle_mutated_asym = db_bound1.
Proof. by []. Qed.

End probe_mut.

End WS.

Print Assumptions WS.db_exact1_isSome.
Print Assumptions WS.db_asym1_isSome.
Print Assumptions WS.db_bundle_mutated_exact_boundE.
Print Assumptions WS.db_bundle_mutated_asym_boundE.
Check WS.db_bundle_ok.
Check WS.pgl27_bundle_ok.
