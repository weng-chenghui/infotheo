From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg ring.
From mathcomp Require Import Rstruct reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_proba smc_entropy.
Require Import smc_interpreter smc_entropy.
Require Import scalar_product_program scalar_product_proof.

Import GRing.Theory.
Import Num.Theory.
Module scp := smc_interpreter.

(******************************************************************************)
(*                                                                            *)
(*   For Connecting the Zn-to-Z2 Protocol and the SMC Interpreter             *)
(*                                                                            *)
(*   Previous Zn-to-Z2 is a global view implementation, no parties and        *)
(*   communications like in the SMC interpreter model. In this file           *)
(*   we introduce the same model for the Zn-to-Z2 protocol.                   *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.

Section smc_def.

Variable data : Type.
Inductive proc : Type :=
  | Init : data -> proc -> proc
  | ScalarProduct : nat -> nat -> data -> (data -> proc) -> proc
  | Finish : proc
  | Fail : proc.

Definition SMC := data -> data -> data.

Definition step (sps : seq SMC) (A : Type) (ps : seq proc)
  (trace : seq data)
  (yes no : (proc * seq data -> A)) (i : nat) : A :=
  let ps := nth Fail ps in
  let p := ps i in
  let nop := no (p, trace) in
  let '(sp) := nth (fun a _ => a) sps i in
  match p with
  | ScalarProduct id1 id2 x1 f1 =>
      match ps id2 with
      |  ScalarProduct id2 id1 x2 f2 =>
           if (id1, id2) == (alice, bob) then
                yes (f1 (sp x1 x2), sp x1 x2 :: trace)
           else
             if (id1, id2) == (bob, alice) then
                yes (f2 (sp x2 x1), sp x2 x1 :: trace)
             else
               nop
      | _ => nop
      end
  | Init d next =>
      yes (next, d :: trace)
  | Finish | Fail =>
      nop
  end.

End smc_def.

Arguments Finish {data}.
Arguments Fail {data}.

Section znto_program.
  
Variable n m : nat.
Let TX := [the finComRingType of 'I_m.+2].
Let VX := 'rV[TX]_n.
Local Notation "u *d w" := (scp.dotproduct u w).

Definition data := (VX + (TX * TX))%type.
Definition inp x : data := inl x.
Definition out x : data := inr x.

Definition palice (xa : VX) :=
  Init (inp xa) (
  ScalarProduct alice bob (inp xa) (fun y =>
  ScalarProduct alice bob (inp (xa+xa)) (fun y =>
  Finish))).

Definition pbob (xb : VX) :=
  Init (inp xb) (
  ScalarProduct bob alice (inp xb) (fun y =>
  ScalarProduct bob alice (inp (xb+xb)) (fun y =>
  Finish))).

Let results (trs :  smc_scalar_product_party_tracesT VX) :=
  let 'ya :=
    if tnth trs 0 is Bseq [:: inl ya; _; _; _; _; _] _ then ya
    else 0 in
  let 'yb :=
    if tnth trs 1 is Bseq [:: inl yb; _; _; _; _; _] _ then yb
    else 0 in
  out (ya, yb).

Let sp sa sb ra yb (xa xb : data) :=
      let xa_ := if xa is inl xa then xa else 0 in
      let xb_ := if xb is inl xb then xb else 0 in
      results (@smc_scalar_product_traces TX VX scp.dotproduct sa sb ra yb xa_ xb_).

Variable (rs : seq (VX * VX * TX * TX)).
Variable (sa1 sa2 sb1 sb2 : VX) (ra1 ra2 yb1 yb2 : TX).

Let rs' := [:: (sa1, sb1, ra1, yb1); (sa2, sb2, ra2, yb2)].

Let sps := map (fun r => let '(sa, sb, ra, yb) := r in
  sp sa sb ra yb) rs'.

Fixpoint interp h (ps : seq (proc data)) (traces : seq (seq data)) :=
  if h is h.+1 then
    if has (fun i => step sps ps [::] (fun=>true) (fun=>false) i)
        (iota 0 (size ps)) then
      let ps_trs' := [seq step sps ps (nth [::] traces i) idfun idfun i
                     | i <- iota 0 (size ps)] in
      let ps' := unzip1 ps_trs' in
      let trs' := unzip2 ps_trs' in
        interp h ps' trs'
    else (ps, traces)
  else (ps, traces).

Variable (xa xb : VX).
Let smc_program := interp 11 [:: palice xa; pbob xb] [::[::]].

Goal smc_program = ([::Finish; Finish], [::]).
rewrite /smc_program.
rewrite (lock (11 : nat)) /=.
rewrite -lock (lock (10 : nat)) /=.
rewrite -lock (lock (9 : nat)) /=.
rewrite -lock (lock (8 : nat)) /=.
rewrite -lock (lock (7 : nat)) /=.
rewrite /sp.
rewrite !{1}smc_scalar_product_traces_ok.
rewrite /results /=.
Abort.

Definition sig_smc_program : {trace | smc_program =
  ([:: Finish; Finish], trace)}.
Proof.
eexists.
rewrite /smc_program.
rewrite (lock (11 : nat)) /=.
rewrite -lock (lock (10 : nat)) /=.
rewrite -lock (lock (9 : nat)) /=.
rewrite -lock (lock (8 : nat)) /=.
rewrite -lock (lock (7 : nat)) /=.
rewrite /sp.
rewrite !{1}smc_scalar_product_traces_ok.
rewrite /results [LHS]/=.
abstract reflexivity.
Defined.

Eval simpl in sval sig_smc_program.

Lemma smc_program_ok : smc_program = 
  ([:: Finish; Finish],
   [::
       [:: out ((xa + xa + sa1) *d (xa + xa) + (sa1 *d sb1 - ra1) -
                 yb1 - (xa + xa + sb1) *d sa1 + ra1,
               yb1);
           out ((xa + sa1) *d xb + (sa1 *d sb1 - ra1) -
                 yb1 - (xb + sb1) *d sa1 + ra1,
               yb1); 
           inp xa];
       [:: out ((xa + xa + sa2) *d (xa + xa) + (sa2 *d sb2 - ra2) -
                 yb2 - (xa + xa + sb2) *d sa2 + ra2,
               yb2);
           out ((xa + sa2) *d xb + (sa2 *d sb2 - ra2) -
                 yb2 - (xb + sb2) *d sa2 + ra2,
               yb2); 
           inp xb]]).
Proof.
rewrite /smc_program.
rewrite (lock (11 : nat)) /=.
rewrite -lock (lock (10 : nat)) /=.
rewrite -lock (lock (9 : nat)) /=.
rewrite -lock (lock (8 : nat)) /=.
rewrite -lock (lock (7 : nat)) /=.
rewrite /sp.
rewrite !{1}smc_scalar_product_traces_ok.
rewrite /results [LHS]/=.
reflexivity. Qed.

End znto_program.
