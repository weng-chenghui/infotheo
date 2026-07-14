(** SSProve extension: bounded simulation security.

    [adv_sim_le E adm Real Ideal Sim eps] — every valid adversary in the
    admissible class [adm] distinguishes [Real] from [Sim ∘ Ideal] with
    advantage at most [eps].  [adv_sim_le_from_endpoint] converts a
    real-versus-endpoint game bound plus a perfect endpoint factorization
    into bounded simulation security; [adv_sim_le_reduction] transports the
    bound to any common left context [T]. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra reals.

Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve.Crypt Require Import Package pkg_composition Pr.
Set Warnings "notation-overridden,ambiguous-paths".

From Stdlib Require Import Utf8.
From extructures Require Import ord fset fmap.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Set Bullet Behavior "Strict Subproofs".

Import GRing.Theory Num.Theory Order.POrderTheory.
Import PackageNotation.
Local Open Scope package_scope.
Local Open Scope ring_scope.

(* Pin SSProve's real type as the ambient realType. *)
Local Notation R := SSProve.Crypt.Axioms.R.

Section bounded_simulation.

Context (E : Interface) (adm : Locations -> raw_package -> Prop).

(* adv_sim_le E adm Real Ideal Sim eps — bounded simulation security relative
   to the admissible-adversary class adm: every valid, admissible adversary
   distinguishes the real package from the simulator composed with the ideal
   package with advantage at most eps. *)
Definition adv_sim_le (Real Ideal Sim : raw_package) (eps : R) : Prop :=
  forall (LA : Locations) (A : raw_package),
    ValidPackage LA E A_export A -> adm LA A ->
    AdvantageE Real (Sim ∘ Ideal) A <= eps.

(* adv_sim_le_from_endpoint — a real-versus-endpoint advantage bound eps
   and a perfect equivalence between the endpoint and the simulated ideal
   package give bounded simulation security with bound eps.
   Naming: subject-prefixed by [adv_sim_le]; the descriptive [from_endpoint]
   suffix names the construction input, not a MathComp abbreviation. *)
Lemma adv_sim_le_from_endpoint
    (Real Endpoint Ideal Sim : raw_package) (eps : R)
    (game_le : forall (LA : Locations) (A : raw_package),
       ValidPackage LA E A_export A -> adm LA A ->
       AdvantageE Real Endpoint A <= eps)
    (sim_eq0 : forall (LA : Locations) (A : raw_package),
       ValidPackage LA E A_export A -> adm LA A ->
       AdvantageE Endpoint (Sim ∘ Ideal) A = 0) :
  adv_sim_le Real Ideal Sim eps.
Proof.
move=> LA A A_valid A_adm.
apply: (le_trans (Advantage_triangle Real (Sim ∘ Ideal) Endpoint A)).
rewrite (sim_eq0 LA A A_valid A_adm) addr0.
exact: (game_le LA A A_valid A_adm).
Qed.

(* adv_sim_le_reduction — bounded simulation security transports across a
   common context T applied on the left: for any admissible composite
   adversary [A ∘ T], the advantage of A against the T-linked real and
   simulated ideal packages is at most eps.  Admissibility must be closed
   under [A ∘ T]. *)
Lemma adv_sim_le_reduction
    (Real Ideal Sim : raw_package) (eps : R)
    (sim_le : adv_sim_le Real Ideal Sim eps)
    (T A : raw_package) (LAT : Locations)
    (AT_valid : ValidPackage LAT E A_export (A ∘ T))
    (AT_adm : adm LAT (A ∘ T)) :
  AdvantageE (T ∘ Real) (T ∘ Sim ∘ Ideal) A <= eps.
Proof.
rewrite -Advantage_link.
exact: (sim_le LAT (A ∘ T) AT_valid AT_adm).
Qed.

End bounded_simulation.
