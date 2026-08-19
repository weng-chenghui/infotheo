(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_boot reals.
Require Import fdist privacy_model.

(**md**************************************************************************)
(* # The n-party observation diagram                                          *)
(*                                                                            *)
(* An n-party protocol is presented by per-party input, trace and output      *)
(* spaces, a trace map on the execution context, per-party input and output   *)
(* read-offs, an aggregation and an ideal function, subject to the            *)
(* correctness square and to the trace recording the initialized inputs.  An  *)
(* adversary is a set A of parties: its view space is the product of its      *)
(* trace spaces and its view is its share of the trace of a run.  The output  *)
(* read-off commutes with the two projections, the input read-off of a view   *)
(* returns the adversary's inputs, and a map computing the aggregation off    *)
(* the adversary's delivered outputs computes the ideal function off its      *)
(* view.  The view map is an observation of the privacy model, and the        *)
(* model's view law at the party data is the law of the adversary's view.     *)
(*                                                                            *)
(* ```                                                                        *)
(*                   x_all == the joint input space, the dependent product    *)
(*                            of the per-party input spaces                   *)
(*                   s_all == the joint trace space                           *)
(*                   y_all == the delivery space                              *)
(*                exec_ctx == the execution context, a joint input with an    *)
(*                            ancilla                                         *)
(*               out_all s == the output read-off of a joint trace            *)
(*              view_space == the adversary's share of the joint trace space  *)
(*                   x_adv == the adversary's input space                     *)
(*                   y_adv == the adversary's delivery space                  *)
(*              proj_adv s == the adversary's share of a joint trace          *)
(*            proj_x_adv x == the adversary's share of a joint input          *)
(*            proj_y_adv y == the adversary's share of a delivery             *)
(*                    view == the view map, sending an execution context to   *)
(*                            the adversary's share of the trace of the run   *)
(*               out_adv b == the output read-off on the view space           *)
(*                in_adv b == the input read-off on the view space            *)
(*          readoff_square == the output read-off after the trace             *)
(*                            projection is the delivery projection after     *)
(*                            the output read-off                             *)
(*          in_adv_records == the input read-off of a view returns the        *)
(*                            adversary's share of the inputs                 *)
(*        reveals_output p == p computes the aggregation after the delivery   *)
(*                            projection                                      *)
(*            reveal_chain == a map revealing the output computes the ideal   *)
(*                            function off the adversary's view               *)
(*          party_view_law == the model's view law at the party data          *)
(*    three_party_identity == three parties holding one bit each whose trace  *)
(*                            records the inputs verbatim, an instance of     *)
(*                            the observation diagram                         *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope fdist_scope.

Section party.
Context {R : realType}.
Variable n : nat.
Variables Xi Si Yi : 'I_n -> finType.
Variable Y : finType.

(* fig:smc:observation *)
(* The joint input space is the dependent product of the per-party input
   spaces. *)
Definition x_all := {dffun forall i, Xi i}.

(* fig:smc:observation *)
(* The joint trace space is the dependent product of the per-party trace
   spaces. *)
Definition s_all := {dffun forall i, Si i}.

(* fig:smc:observation *)
(* The delivery space is the dependent product of the per-party output
   spaces. *)
Definition y_all := {dffun forall i, Yi i}.

Variable Omega : finType.
Variable P_Omega : R.-fdist Omega.

(* fig:smc:observation *)
(* An execution context is a joint input together with an ancilla. *)
Definition exec_ctx := (x_all * Omega)%type.

Variable trace_map : exec_ctx -> s_all.
Variable out_i : forall i, Si i -> Yi i.

(* Naming: intentional; throughout this file the in_ prefix abbreviates
   input, pairing with out_ for output, and never marks a
   membership-predicate unfold in the sense of in_cons. *)
Variable in_i : forall i, Si i -> Xi i.
Variable agg : y_all -> Y.
Variable f : x_all -> Y.

(* fig:smc:observation *)
(* The output read-off of a joint trace applies each party's read-off to
   that party's trace. *)
Definition out_all (s : s_all) : y_all := [ffun i => out_i (s i)].

(* The aggregated output read-off of the trace of a run is the ideal
   function of the inputs.
   Naming: intentional; a model assumption of the diagram, named for the
   property it assumes rather than by the E suffix that its equational
   shape would otherwise take. *)
Hypothesis correctness : forall e, agg (out_all (trace_map e)) = f e.1.

(* The trace of a run records the initialized inputs.
   Naming: intentional; a model assumption of the diagram, named for the
   property it assumes rather than by the E suffix that its equational
   shape would otherwise take. *)
Hypothesis trace_records_inputs :
  forall e i, in_i (trace_map e i) = e.1 i.

Variable A : {set 'I_n}.

(* def:smc:view *)
(* The view space is the product of the adversary's trace spaces, indexed
   by the subtype of the parties in A, whose finite structure is the
   canonical one of a subtype of a finite type. *)
Definition view_space := {dffun forall i : {i : 'I_n | i \in A}, Si (val i)}.

(* def:smc:view *)
(* The adversary's input space is the product of its parties' input
   spaces. *)
Definition x_adv := {dffun forall i : {i : 'I_n | i \in A}, Xi (val i)}.

(* def:smc:view *)
(* The adversary's delivery space is the product of its parties' output
   spaces. *)
Definition y_adv := {dffun forall i : {i : 'I_n | i \in A}, Yi (val i)}.

(* def:smc:view *)
(* The adversary's share of a joint trace keeps its parties' traces. *)
Definition proj_adv (s : s_all) : view_space := [ffun j => s (val j)].

(* fig:smc:observation *)
(* The adversary's share of a joint input keeps its parties' inputs. *)
Definition proj_x_adv (x : x_all) : x_adv := [ffun j => x (val j)].

(* fig:smc:observation *)
(* The adversary's share of a delivery keeps its parties' outputs. *)
Definition proj_y_adv (y : y_all) : y_adv := [ffun j => y (val j)].

(* def:smc:view *)
(* The view map sends an execution context to the adversary's share of the
   trace of the run at that context. *)
Definition view : exec_ctx -> view_space := proj_adv \o trace_map.

(* def:smc:view *)
(* The output read-off on the view space applies each corrupted party's
   read-off to its trace. *)
Definition out_adv (b : view_space) : y_adv := [ffun j => out_i (b j)].

(* def:smc:view *)
(* The input read-off on the view space returns the corrupted parties'
   initialized inputs. *)
Definition in_adv (b : view_space) : x_adv := [ffun j => in_i (b j)].

(* eq:smc:readoff-square *)
(* The output read-off after the trace projection is the delivery
   projection after the output read-off.
   Naming: the diagram-shape name of the blueprint node
   eq:smc:readoff-square. *)
Lemma readoff_square (s : s_all) :
  out_adv (proj_adv s) = proj_y_adv (out_all s).
Proof. by apply/ffunP => j; rewrite !ffunE. Qed.

(* def:smc:view *)
(* The input read-off of the view at an execution context returns the
   adversary's share of the inputs of that context. *)
Lemma in_adv_records (e : exec_ctx) :
  in_adv (view e) = proj_x_adv e.1.
Proof. by apply/ffunP => j; rewrite !ffunE trace_records_inputs. Qed.

(* eq:smc:reveal-criterion *)
(* A map on the adversary's delivery space reveals the output when it
   computes the aggregation after the delivery projection. *)
Definition reveals_output (p : y_adv -> Y) :=
  forall y : y_all, p (proj_y_adv y) = agg y.

(* eq:smc:reveal-criterion *)
(* A map revealing the output composed with the output read-off of the view
   computes the ideal function on the inputs.
   Naming: the chain name of the blueprint node eq:smc:reveal-criterion. *)
Lemma reveal_chain (p : y_adv -> Y) (e : exec_ctx) :
  reveals_output p -> p (out_adv (view e)) = f e.1.
Proof. by move=> pr; rewrite readoff_square pr correctness. Qed.

(* def:smc:view-law *)
(* The view law of the privacy model at the party data, the observation
   being the view map and the ancilla law being P_Omega. *)
Definition party_view_law : x_all -> R.-fdist view_space :=
  view_law P_Omega view.

End party.

(* Three parties holding one bit each, a one-point ancilla space, the trace
   recording the inputs verbatim, the read-offs the identity, the
   aggregation and the ideal function both reading party 0, and the
   adversary holding parties 0 and 1. *)
Module three_party_identity.
Section instance.
Context {R : realType}.

(* Every party's input, trace and output space is the two-point space. *)
Definition bit_space (i : 'I_3) : finType := 'I_2.

(* The output read-off returns the party's trace unchanged. *)
Definition out_map (i : 'I_3) : bit_space i -> bit_space i := id.

(* The input read-off returns the party's trace unchanged.
   Naming: intentional; in_ abbreviates input and pairs with out_map. *)
Definition in_map (i : 'I_3) : bit_space i -> bit_space i := id.

(* The execution context pairs a joint input with a one-point ancilla. *)
Definition execution_context := exec_ctx bit_space 'I_1.

(* The trace of a run is the joint input. *)
Definition trace (e : execution_context) : s_all bit_space := e.1.

(* The aggregation returns party 0's delivered output. *)
Definition aggregate (y : y_all bit_space) : 'I_2 := y ord0.

(* The ideal function returns party 0's input. *)
Definition ideal_function (x : x_all bit_space) : 'I_2 := x ord0.

(* The adversary holds parties 0 and 1. *)
Definition adversary : {set 'I_3} := [set i : 'I_3 | (i < 2)%N].

(* The ancilla law is the point mass on the one-point ancilla space. *)
Definition ancilla : R.-fdist 'I_1 := fdist1 ord0.

(* The aggregated output read-off of the trace of a run is the ideal
   function of the inputs.
   Naming: intentional; mirrors the section hypothesis correctness it
   discharges and feeds to reveal_chain, the statement being an equation
   that would otherwise take an E suffix. *)
Lemma correctness (e : execution_context) :
  aggregate (out_all out_map (trace e)) = ideal_function e.1.
Proof. by rewrite /aggregate /ideal_function ffunE. Qed.

(* The trace of a run records the initialized inputs.
   Naming: intentional; mirrors the section hypothesis
   trace_records_inputs it discharges and feeds to in_adv_records, the
   statement being an equation that would otherwise take an E suffix. *)
Lemma trace_records_inputs (e : execution_context) i :
  in_map (trace e i) = e.1 i.
Proof. by []. Qed.

(* eq:smc:readoff-square *)
(* The read-off square at this instance.
   Naming: _holds separates the instance from the general lemma
   readoff_square, which stays in scope inside the module. *)
Lemma readoff_square_holds (s : s_all bit_space) :
  out_adv out_map (proj_adv adversary s)
  = proj_y_adv adversary (out_all out_map s).
Proof. exact: readoff_square. Qed.

(* def:smc:view *)
(* The input read-off of the view returns the adversary's share of the
   inputs at this instance.
   Naming: the leading in_ is part of the read-off name in_adv rather
   than the in_-unfold idiom, and _holds separates the instance from the
   general lemma in_adv_records, which stays in scope inside the
   module. *)
Lemma in_adv_records_holds (e : execution_context) :
  in_adv in_map (view trace adversary e) = proj_x_adv adversary e.1.
Proof. exact: (in_adv_records trace_records_inputs). Qed.

(* eq:smc:reveal-criterion *)
(* The revelation chain at this instance.
   Naming: _holds separates the instance from the general lemma
   reveal_chain, which stays in scope inside the module. *)
Lemma reveal_chain_holds (p : y_adv bit_space adversary -> 'I_2)
    (e : execution_context) :
  reveals_output aggregate p ->
  p (out_adv out_map (view trace adversary e)) = ideal_function e.1.
Proof. exact: (reveal_chain correctness). Qed.

(* def:smc:view-law *)
(* The model's view law at this instance is the point mass at the view of
   the run with the one-point ancilla. *)
Lemma party_view_lawE (x : x_all bit_space) :
  party_view_law ancilla trace adversary x
  = fdist1 (view trace adversary (x, ord0)).
Proof. by rewrite /party_view_law view_lawE /ancilla fdistmap1. Qed.

End instance.
End three_party_identity.
