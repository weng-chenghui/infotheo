(* Probe P3 — claims S10-S11 / L9: the n-party observation-diagram layer.
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
Hypothesis trace_records_inputs :
  forall e i, in_i (trace_map e i) = e.1 i.

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

(* Concrete elaboration at n = 3 with every family constant 'I_2, a
   one-point randomness space, the trace recording the inputs verbatim,
   the read-offs the identity, the aggregate and the specification both
   reading coordinate 0, and the adversary holding A = {0, 1}. *)
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

(* FINDINGS
   1. The file as delivered did not compile: R.-fdist needs fdist_scope,
      so Local Open Scope fdist_scope was added to the preamble.  Every
      declaration from Variable P_Omega onwards, including kernel_data
      and party_to_kernel, was silently absent before that fix.
   2. Claim (a) holds unchanged.  The dependent product over the
      adversary subset gets its finType by canonical inference alone:
      #|view_space| elaborates with no added instance, resolving through
      mathcomp.boot.fintype line 1509,
      HB.instance Definition _ := [Finite of {x | P x} by <:].
      The inferred instance prints as
      Specif_sig__canonical__fintype_Finite (in_mem^~ (mem A)).
   3. Claim (b) holds.  The extensionality lemma is mathcomp's ffunP,
      already stated at the dependent finfun type
      (mathcomp.boot.finfun line 181,
      ffunP (f1 f2 : fT) : (forall x, f1 x = f2 x) <-> f1 = f2).
      There is no dffunP: the reference is not in the environment.
      eq_dffun does exist (finfun line 197) and is not needed here.
      apply/ffunP then rewrite !ffunE discharges both read-off squares.
   4. A record field whose type mentions earlier fields takes the record
      argument implicitly, so kagg c_kernel y is rejected with
      the term c_kernel has type kernel_data while it is expected to
      have type Finite.sort (kYfull ?k).  The projection form
      c_kernel.(kagg) works.  kernel_data itself takes R implicitly and
      is spelled kernel_data, not kernel_data R.
   5. In party_to_kernel the arguments trace_map, out_i, agg and f are
      implicit, inferred from the correctness proof, so the call reads
      party_to_kernel c_P_Omega c_correctness c_adv.

   AXIOMS
   readoff_square, in_adv_records and reveal_chain are each Closed under
   the global context.  concrete_ok and c_kernel additionally rest on the
   mathcomp-analysis trio boolp.propositional_extensionality,
   boolp.functional_extensionality_dep and
   boolp.constructive_indefinite_description, which is the standing
   infotheo fdist baseline rather than anything new here.

   MUTATION CHECKS, copies kept in this directory
   1. probe_party_dffun_mut1.v drops Hypothesis trace_records_inputs;
      coqc exits 1 at line 75 with
      Error: The variable trace_records_inputs was not found in the
      current environment.
   2. probe_party_dffun_mut2.v defines out_adv by in_i instead of out_i;
      coqc exits 1 at line 66 with
      Error: ... has type {ffun forall x : ..., Xi (\val x)} while it is
      expected to have type y_adv.                                     *)
