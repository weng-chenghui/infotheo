(* Standalone probe for item 8 SSProve algebra:
   - validity of  challenger ∘ par predictor (ID E1)
   - the Advantage_par rewrite to AdvantageE real game (challenger ∘ par predictor (ID E1))
   Uses abstract packages with the same interface shapes as the real file. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap reals realsum.

Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve.Crypt Require Import Package pkg_composition Pr.
Set Warnings "notation-overridden,ambiguous-paths".

From Stdlib Require Import Utf8.
From extructures Require Import ord fset fmap.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import GRing.Theory Num.Theory Order.POrderTheory.
Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.
#[local] Open Scope real_scope.

Notation R := SSProve.Crypt.Axioms.R.

Section probe.
(* abstract interfaces with the right shape *)
Variable game_iface : Interface.
Variable guesser_export : Interface.
(* the challenger: imports unionm game_iface guesser_export, exports A_export, locs emptym *)
Variable challenger : package (unionm game_iface guesser_export) A_export.
Hypothesis Hch_locs : locs challenger = emptym.
Variable predictor : package [interface] guesser_export.
Variable real_game zero_game : package [interface] game_iface.
Hypothesis Hcompat : fcompat guesser_export game_iface.

Let guess_reduction : raw_package :=
  challenger ∘ par (pack predictor) (ID game_iface).

Goal ValidPackage (locs predictor) game_iface A_export guess_reduction.
Proof.
rewrite /guess_reduction.
have Vpar : ValidPackage (unionm (locs predictor) emptym)
    game_iface (unionm guesser_export game_iface)
    (par (pack predictor) (ID game_iface)).
{ have := @valid_par (locs predictor) emptym [interface] game_iface
    guesser_export game_iface (pack predictor) (ID game_iface)
    (pack_valid predictor) (valid_ID game_iface).
  rewrite union0m; apply.
  - by fmap_solve.
  - by rewrite /fcompat union0m unionm0. }
eapply valid_package_inject_locations.
2:{
  eapply valid_link_weak.
  - exact: (pack_valid challenger).
  - exact: Vpar.
  - rewrite Hch_locs. exact: fcompat0m.
  - rewrite -Hcompat. exact: fsubmapxx.
}
rewrite Hch_locs union0m unionm0.
exact: fsubmapxx.
Qed.

(* lemma 4: advantage_eq *)
Let success (g : raw_package) : R :=
  distr.mu (pkg_advantage.Pr (challenger ∘ par (pack predictor) g)) true.

Goal `| success real_game - success zero_game |
   = AdvantageE real_game zero_game guess_reduction.
Proof.
rewrite /success /guess_reduction.
have Hpar := @Advantage_par (pack predictor) real_game zero_game challenger
   (locs predictor) (locs real_game) (locs zero_game) guesser_export game_iface
   (pack_valid predictor) (pack_valid real_game) (pack_valid zero_game).
rewrite -Hpar /AdvantageE.
reflexivity.
Qed.

End probe.
