From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix Rstruct ring.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter.

Import GRing.Theory.
Import Num.Theory.

(*******************************************************************************************)
(*                                                                                         *)
(* Formalization of:                                                                       *)
(*                                                                                         *)
(* Dumas, J. G., Lafourcade, P., Orfila, J. B., & Puys, M. (2017).                         *)
(* Dual protocols for private multi-party matrix multiplication and trust computations.    *)
(* Computers & security, 71, 51-70.                                                        *)
(*                                                                                         *)
(*******************************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.

Local Definition R := Rdefinitions.R.

Reserved Notation "u *h w" (at level 40).
Reserved Notation "u ^h w" (at level 40).

Section dsdp.

Variable msg : finComRingType.  (* TODO message must be modulo M *)

Inductive enc : Type :=
  | E : nat -> msg -> enc.

Definition D (p : nat) (e : enc) : msg :=
  match e with
  | E i m => if i == p then m else 0
  (* TODO: returning 0 instead of making it an option because it is
     troublesome when mixing with Send, Recv, etc.
  *)
  end.

Definition Emul (e1 e2 : enc) : enc := 
  match (e1, e2) with
  | (E i1 m1, E i2 m2) => if i1 == i2 then E i1 (m1 + m2) else E 0 0 (* TODO: mod M?*)
  end.

Definition Epow (e : enc) (m2 : msg) : enc :=
  match e with
  | E i m1 => E i (m1 * m2) (* TODO: mod M?*)
  end.

Notation "u *h w" := (Emul u w).
Notation "u ^h w" := (Epow u w).

Definition alice : nat := 0.
Definition bob : nat := 1.
Definition charlie : nat := 2.

Definition data := (msg + enc)%type.
Definition d x : data := inl x.
Definition e x : data := inr x.

Definition Recv_enc frm f : proc data :=
  Recv frm (fun x => if x is inr v then f v else Fail).

Definition pbob (v2 : msg) : proc data :=
  Init (d v2) (
  Send alice (e (E bob v2)) (
  Recv_enc alice (fun a2 =>
  Recv_enc alice (fun a3 =>
  let d2 := D bob a2 in  
    Send charlie (e (a3 *h (E charlie d2))) (
  Finish))))).

Definition pcharlie (v3 : msg) : proc data :=
  Init (d v3) (
  Send alice (e (E charlie v3)) (
  Recv_enc bob (fun b3 => (
  let d3 := D charlie b3 in
    Send alice (e (E alice d3))
  Finish)))).

Definition palice (v1 u1 u2 u3 r2 r3: msg) : proc data :=
  Init (d v1) (
  Init (d u1) (
  Init (d u2) (
  Init (d u3) (
  Init (d r2) (
  Init (d r3) (
  Recv_enc bob (fun c2 =>
  Recv_enc charlie (fun c3 =>
  let a2 := (c2 ^h u2 *h (E bob r2)) in
  let a3 := (c3 ^h u3 *h (E charlie r3)) in
    Send bob (e a2) (
    Send bob (e a3) (
    Recv_enc charlie (fun g =>
    Ret (d ((D alice g) - r2 - r3 + u1 * v1))))))))))))).
  
Variables (v1 v2 v3 u1 u2 u3 r2 r3 : msg).
Definition dsdp h :=
  (interp h [:: palice v1 u1 u2 u3 r2 r3; pbob v2; pcharlie v3] [::[::];[::];[::]]).


(* Different from SMC scalar product: has much less calculations *)
Goal (dsdp 15).2 = ([::]).
cbv -[GRing.add GRing.opp GRing.Ring.sort].
Undo 1.
rewrite /dsdp.
rewrite (lock (15 : nat)) /=.
rewrite -lock (lock (14 : nat)) /=.
rewrite -lock (lock (13 : nat)) /=.
rewrite -lock (lock (12 : nat)) /=.
rewrite -lock (lock (11 : nat)) /=.
rewrite -lock (lock (10 : nat)) /=.
rewrite -lock (lock (9 : nat)) /=.
rewrite -lock (lock (8 : nat)) /=.
rewrite -lock (lock (7 : nat)) /=.
rewrite -lock (lock (6 : nat)) /=.
rewrite -lock (lock (5 : nat)) /=.
rewrite -lock (lock (4 : nat)) /=.
rewrite -lock (lock (3 : nat)) /=.
rewrite -lock (lock (2 : nat)) /=.
rewrite -lock (lock (1 : nat)) /=.
Abort.
  

End dsdp.
