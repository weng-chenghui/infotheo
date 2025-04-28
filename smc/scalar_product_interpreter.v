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

Variable n m k : nat.
Let TX := [the finComRingType of 'I_m.+2].
Let VX := 'rV[TX]_n.
Let data := (TX + VX)%type.
Let one x : data := inl x.
Let vec x : data := inr x.
Local Notation "u *d w" := (scp.dotproduct u w).

Inductive proc : Type :=
  | ScalarProduct : nat -> nat -> VX -> (TX -> proc) -> proc
  | Init : VX -> proc -> proc
  | Finish : proc
  | Fail : proc
   (* Wait partial result from a specific fuel and id round 

      fuel -> id -> f
   *)
  | _WaitRecv : nat -> nat ->  (TX -> proc) -> proc
   (* Use proc as mbox to store the 2nd partial result.
      This term blocks the following proc until the result TX is fetched.

      fuel -> id -> result -> next
    *)
  | _WantSend : nat -> nat -> TX -> proc -> proc.

Definition SMC := VX -> VX -> (TX * TX).

Definition step (h : nat) (sp : SMC) (A : Type) (ps : seq proc)
  (trace : seq data) (yes no : (proc * seq data -> A)) (i : nat) : A :=
  let ps := nth Fail ps in
  let p := ps i in
  let nop := no (p, trace) in
  match p with
  | ScalarProduct id1 id2 x1 f1 =>
      match ps id2 with
      | ScalarProduct id2 id1 x2 _ =>
          if (id1, id2) == (alice, bob) then
            yes (_WantSend h id2 (sp x1 x2).2 (f1 (sp x1 x2).1),
                 one (sp x1 x2).1 :: trace)
          else nop
      | _WantSend fuel id r _ => (* ScalarProduct has no fuel mark so mark it *)
          if id == id1 then yes (_WaitRecv h id1 f1, trace) else nop
      | _ => nop
      end
  | _WantSend fuel id r next =>
      match ps id with
      | _WaitRecv fuel' id' f =>
          if (fuel == fuel') && (id == id') then
            yes (next, trace) else nop
      | _ => nop
      end
  | _WaitRecv fuel id f =>
      match ps id with
      | _WantSend fuel' id' r _ =>
          if (fuel == fuel') && (id == id') then
            yes (f r, one r :: trace) else nop 
      | _ => nop
      end
  | Init d next =>
      yes (next, vec d :: trace)
  | Finish | Fail =>
      nop
  end.

(* Because we haven't built-in RNG into our language,
   all random values are pre-generated.

   TODO: when proving randomness we need a hypothesis
   states that

   h (fuel of the interpreter) > k >= times of scalar product in the program.
*)
Variable rand_values : k.-tuple (VX * VX * TX * TX).

(* Get the underlying scalar product results from the underlying traces. *)
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
Let sps : k.-tuple SMC := map (fun r => let '(sa, sb, ra, yb) := r in
    scalar_product sa sb ra yb) rand_values.

(* For each step needs scalar product, the interpreter fetch one
   from the pre-filled scalar products, and interpret the step
   with that scalar product.

   Need h: fuel for interpretation, and v: index of pre-filled scalar products;
   tried to use h as v but the type difference is difficult to remove.
   And ord_pred causes that Coq cannot guess the decrease of v for the
   fixpoint definition if replacing h with v.
*)
Fixpoint interp (h : nat)(v : 'I_k) (ps : seq proc) (traces : seq (seq data)) :=
  let v' := ord_pred v in
  let sp := tnth sps v in
  if h is h'.+1 then
    if has (fun i => step h sp ps [::] (fun=>true) (fun=>false) i)
        (iota 0 (size ps)) then
      let ps_trs' := [seq step h sp ps (nth [::] traces i) idfun idfun i
                     | i <- iota 0 (size ps)] in
      let ps' := unzip1 ps_trs' in
      let trs' := unzip2 ps_trs' in
        interp h' v' ps' trs'
    else (ps, traces)
  else (ps, traces).

End def.

Arguments Finish {n m}.
Arguments Fail {n m}.

