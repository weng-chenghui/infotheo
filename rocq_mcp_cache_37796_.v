From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra reals realsum distr.
Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve.Crypt Require Import Package Pr.
Set Warnings "notation-overridden,ambiguous-paths".
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
Local Notation R := SSProve.Crypt.Axioms.R.
