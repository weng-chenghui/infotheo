(* MUTANT 1 of probe_party_dffun.v: the hypothesis trace_records_inputs
   is dropped, leaving in_adv_records without its premise.
   This file is EXPECTED TO FAIL to compile.

   Probe P3 — claims S10-S11 / L9: the n-party observation-diagram layer.
   Tests that (a) the dependent product over the adversary subset,
   {dffun forall i : {i | i \in A}, Si (val i)}, carries a finType
   instance by canonical inference alone, (b) the read-off square is
   provable by ffunP at this carrier, (c) the party data assembles into
   the kernel section's parameters (S11) — the party_to_kernel payoff.
   Compile from repo root:
     /Users/cheng-huiweng/Projects/coq/_opam/bin/coqc -R . infotheo \
       smc/security_models/.scratch/probe_party_dffun.v                *)

From mathcomp Require Import all_ssreflect all_algebra reals.
Require Import realType_ext fdist proba.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Section party.
Context {R : realType}.
Variable n : nat.
Variables Xi Si Yi : 'I_n -> finType.
Variable Y : finType.

Definition x_all := {dffun forall i, Xi i}.
Definition s_all := {dffun forall i, Si i}.
Definition y_all := {dffun forall i, Yi i}.

Variable Omega : finType.
Variable P_Omega : R.-fdist Omega.
Definition exec_ctx := (x_all * Omega)%type.

Variable trace_map : exec_ctx -> s_all.
Variable out_i : forall i, Si i -> Yi i.
Variable in_i : forall i, Si i -> Xi i.
Variable agg : y_all -> Y.
Variable f : x_all -> Y.

Definition out_all (s : s_all) : y_all := [ffun i => out_i (s i)].

Hypothesis correctness : forall e, agg (out_all (trace_map e)) = f e.1.

Variable A : {set 'I_n}.

(* L9: the adversary-indexed dependent product.  #|view_space| forces the
   finType instance to be inferred, not just the type to be formed. *)
Definition view_space := {dffun forall i : {i : 'I_n | i \in A}, Si (val i)}.
Definition probe_card := #|view_space|.

Definition x_adv := {dffun forall i : {i : 'I_n | i \in A}, Xi (val i)}.
Definition y_adv := {dffun forall i : {i : 'I_n | i \in A}, Yi (val i)}.

Definition proj_adv (s : s_all) : view_space := [ffun j => s (val j)].
Definition proj_x_adv (x : x_all) : x_adv := [ffun j => x (val j)].
Definition proj_y_adv (y : y_all) : y_adv := [ffun j => y (val j)].

Definition view : exec_ctx -> view_space := proj_adv \o trace_map.

Definition out_adv (b : view_space) : y_adv := [ffun j => out_i (b j)].
Definition in_adv (b : view_space) : x_adv := [ffun j => in_i (b j)].

(* S10: eq:smc:readoff-square, "commutes by construction". *)
Lemma readoff_square (s : s_all) :
  out_adv (proj_adv s) = proj_y_adv (out_all s).
Proof. by apply/ffunP => j; rewrite !ffunE. Qed.

(* Glossary identity for the input read-off. *)
Lemma in_adv_records (e : exec_ctx) :
  in_adv (view e) = proj_x_adv e.1.
Proof. by apply/ffunP => j; rewrite !ffunE trace_records_inputs. Qed.

(* eq:smc:reveal-criterion and its chain computation. *)
Definition reveals_output (p : y_adv -> Y) :=
  forall y : y_all, p (proj_y_adv y) = agg y.

Lemma reveal_chain (p : y_adv -> Y) (e : exec_ctx) :
  reveals_output p -> p (out_adv (view e)) = f e.1.
Proof. by move=> pr; rewrite readoff_square pr correctness. Qed.

(* S11: the party data instantiates the kernel parameter block.  Local
   mirror of the kernel section signature (kept in sync with probe P1);
   the probe payoff is that this Definition ELABORATES, i.e. every field
   has the type the kernel section expects at this carrier. *)
Record kernel_data := {
  kX : finType; kYfull : finType; kY : finType;
  kXa : finType; kYa : finType; kBv : finType; kOmega : finType;
  kf : kX -> kY;
  kagg : kYfull -> kY;
  kproj_xa : kX -> kXa;
  kproj_ya : kYfull -> kYa;
  kP_Omega : R.-fdist kOmega;
  kview_at : kX * kOmega -> kBv;
  krun : kX * kOmega -> kYfull;
  krun_correct : forall e, kagg (krun e) = kf e.1
}.

Definition party_to_kernel : kernel_data :=
  {| kX := x_all; kYfull := y_all; kY := Y;
     kXa := x_adv; kYa := y_adv; kBv := view_space; kOmega := Omega;
     kf := f; kagg := agg;
     kproj_xa := proj_x_adv; kproj_ya := proj_y_adv;
     kP_Omega := P_Omega;
     kview_at := view;
     krun := fun e => out_all (trace_map e);
     krun_correct := correctness |}.

End party.

(* Concrete elaboration at n = 3, A = {0, 1}: the vacuity check that the
   abstract section applies to an actual small carrier. *)
Section concrete.
Context {R : realType}.

Definition c_fam (i : 'I_3) : finType := 'I_2.
Definition c_out (i : 'I_3) : c_fam i -> c_fam i := id.
Definition c_in (i : 'I_3) : c_fam i -> c_fam i := id.
Definition c_ctx := exec_ctx c_fam 'I_1.
Definition c_trace (e : c_ctx) : s_all c_fam := e.1.
Definition c_agg (y : y_all c_fam) : 'I_2 := y ord0.
Definition c_f (x : x_all c_fam) : 'I_2 := x ord0.
Definition c_adv : {set 'I_3} := [set i : 'I_3 | (i < 2)%N].
Definition c_P_Omega : R.-fdist 'I_1 := @fdist1 R _ ord0.

Lemma c_correctness (e : c_ctx) :
  c_agg (out_all c_out (c_trace e)) = c_f e.1.
Proof. by rewrite /c_agg /c_f ffunE. Qed.

Lemma c_trace_records (e : c_ctx) i : c_in (c_trace e i) = e.1 i.
Proof. by []. Qed.

Lemma c_readoff_square (s : s_all c_fam) :
  out_adv c_out (proj_adv c_adv s) = proj_y_adv c_adv (out_all c_out s).
Proof. exact: readoff_square. Qed.

Lemma c_in_adv_records (e : c_ctx) :
  in_adv c_in (view c_trace c_adv e) = proj_x_adv c_adv e.1.
Proof. exact: (in_adv_records c_trace_records). Qed.

Lemma c_reveal_chain (p : y_adv c_fam c_adv -> 'I_2) (e : c_ctx) :
  reveals_output c_agg p ->
  p (out_adv c_out (view c_trace c_adv e)) = c_f e.1.
Proof. exact: (reveal_chain c_correctness). Qed.

Definition c_kernel : kernel_data :=
  party_to_kernel c_P_Omega c_correctness c_adv.

Lemma concrete_ok (e : kX c_kernel * kOmega c_kernel) :
  c_kernel.(kagg) (c_kernel.(krun) e) = c_kernel.(kf) e.1.
Proof. exact: c_kernel.(krun_correct). Qed.

End concrete.

(* MUTATION CHECKS — AGENT: record here that
   1. in_adv_records with trace_records_inputs dropped FAILS;
   2. readoff_square with out_adv misdefined as [ffun j => out_i (b j)]
      swapped to use in_i FAILS to typecheck.                          *)
