(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* AG Code Multiplicative Property (Issue #41)                                *)
(*                                                                            *)
(* The Hadamard (coordinatewise) product of two AG codewords from C(D,G)      *)
(* and C(D,G') lies in C(D,G+G'). This is the algebraic foundation for       *)
(* multiplicative secret sharing: multiplying shares locally corresponds to   *)
(* evaluating the product of the underlying functions, yielding a codeword   *)
(* in a code with doubled degree parameter.                                   *)
(*                                                                            *)
(*   hadamard c1 c2  == coordinatewise product of row vectors                 *)
(*   ag_multiplicative == axiomatized: C(D,k) * C(D,k) \subset C(D,2k)      *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg finalg zmodp.
From mathcomp Require Import matrix mxalgebra vector.
Require Import ssr_ext ssralg_ext hamming linearcode.
From pgg_reconstruct Require Import ag_code.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Open Scope ring_scope.

(******************************************************************************)
(*     Section 1: Hadamard (Coordinatewise) Product                           *)
(******************************************************************************)

Section hadamard.

Variable F : fieldType.
Variable n : nat.

Definition hadamard (c1 c2 : 'rV[F]_n) : 'rV[F]_n :=
  \row_(i < n) (c1 ord0 i * c2 ord0 i).

Lemma hadamard_comm (c1 c2 : 'rV[F]_n) :
  hadamard c1 c2 = hadamard c2 c1.
Proof. by apply/rowP => i; rewrite !mxE mulrC. Qed.

Lemma hadamardE (c1 c2 : 'rV[F]_n) (i : 'I_n) :
  (hadamard c1 c2) ord0 i = c1 ord0 i * c2 ord0 i.
Proof. by rewrite mxE. Qed.

End hadamard.

(******************************************************************************)
(*     Section 2: Multiplicative Property for AG Codes (axiomatized)          *)
(******************************************************************************)

Section ag_multiplicative_sect.

Variable F : finFieldType.
Variable n : nat.

(* Two AG codes: C(D,k) and C(D,2k) from degree-k and degree-2k divisors *)
Variables (k_1 k_2 : nat).
Variable ev_k : 'M[F]_(k_1, n).
Variable ev_2k : 'M[F]_(k_2, n).

(* Multiplicative property: codeword * codeword lands in the doubled code.
   This follows from: if f \in L(G) and g \in L(G'), then fg \in L(G+G').
   Evaluating: ev(f)*ev(g) = ev(fg) coordinatewise.
   Currently axiomatized — proving it requires the function-field
   interpretation of AG codes, not just the generator matrix definition. *)
Hypothesis ag_mult :
  forall c1 c2 : 'rV[F]_n,
    c1 \in ag_code ev_k -> c2 \in ag_code ev_k ->
    hadamard c1 c2 \in ag_code ev_2k.

End ag_multiplicative_sect.
