From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg ring.
From mathcomp Require Import Rstruct reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_proba smc_entropy.
Require Import smc_interpreter.
Require Import scalar_product_program scalar_product_proof.

Import GRing.Theory.
Import Num.Theory.
Module scp := smc_interpreter.

(******************************************************************************)
(*                                                                            *)
(*  An upper-level language and interpreter for protocols based on the        *)
(*  SMC scalar product. In the language, the only method to exchange          *)
(*  party data is ScalarProduct. Depends on the inputs, it is used as         *)
(*  secure addition and other different arithmetic oprations.                 *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Section def.

Variable n m : nat.
Let TX := [the finComRingType of 'I_m.+2].
Let VX := 'rV[TX]_n.
Let data := (TX + VX)%type.
Let one x : data := inl x.
Let vec x : data := inr x.
Local Notation "u *d w" := (scp.dotproduct u w).

Inductive proc : Type :=
  | Init : VX -> proc -> proc
  | ScalarProduct : nat -> nat -> VX -> (TX -> proc) -> proc
  | Finish : proc
  | Fail : proc.

Definition SMC := VX -> VX -> (TX * TX).

Definition step (sps : seq SMC) (A : Type) (ps : seq proc)
  (trace : seq data)
  (yes no : (proc * seq data -> A)) (i : nat) : A :=
  let ps := nth Fail ps in
  let p := ps i in
  let nop := no (p, trace) in
  let '(sp) := nth (fun a _ => (0, 0)) sps i in
  match p with
  | ScalarProduct id1 id2 x1 f1 =>
      match ps id2 with
      |  ScalarProduct id2 id1 x2 f2 =>
           if (id1, id2) == (alice, bob) then
                yes (f1 (sp x1 x2).1, one (sp x1 x2).1 :: trace)
           else
             if (id1, id2) == (bob, alice) then
                yes (f2 (sp x2 x1).2, one (sp x2 x1).2 :: trace)
             else
               nop
      | _ => nop
      end
  | Init d next =>
      yes (next, vec d :: trace)
  | Finish | Fail =>
      nop
  end.

Variable (sa1 sa2 sb1 sb2 : VX) (ra1 ra2 yb1 yb2 : TX).

(* Because we haven't built-in RNG into our language,
   all random values are pre-generated.
*)
Let rand_values := [:: (sa1, sb1, ra1, yb1); (sa2, sb2, ra2, yb2)].

Let results (trs :  smc_scalar_product_party_tracesT VX) :=
  let 'ya :=
    if tnth trs 0 is Bseq [:: inl ya; _; _; _; _; _] _ then ya
    else 0 in
  let 'yb :=
    if tnth trs 1 is Bseq [:: inl yb; _; _; _; _; _] _ then yb
    else 0 in
  (ya, yb).

Let scalar_product sa sb ra yb xa xb :=
      results
        (@smc_scalar_product_traces TX VX scp.dotproduct sa sb ra yb xa xb).

(* Scalar products which are pre-filled with random values.
   So only secret inputs are needed during the protocol executions.
*)
Let sps := map (fun r => let '(sa, sb, ra, yb) := r in
    scalar_product sa sb ra yb) rand_values.

(* For each step needs scalar product, the interpreter fetch one
   from the pre-filled scalar products, and interpret the step
   with that scalar product.
*)
Fixpoint interp h (ps : seq proc) (traces : seq (seq data)) :=
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

End def.

Arguments Finish {n m}.
Arguments Fail {n m}.
