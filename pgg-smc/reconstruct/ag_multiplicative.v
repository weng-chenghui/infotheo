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
(*   MultiplicativeScheme == record bundling base/doubled ThresholdSchemes   *)
(*     with proof that Hadamard of valid shares produces valid doubled shares *)
(*   ag_mult_scheme  == MultiplicativeScheme from AG codes via Massey         *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg finalg zmodp.
From mathcomp Require Import fingroup matrix mxalgebra vector.
Require Import ssr_ext ssralg_ext hamming linearcode.
From pgg_reconstruct Require Import pgg_sharing_framework massey
  ag_code ag_massey_bridge.

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

(******************************************************************************)
(*     Section 3: MultiplicativeScheme Record                                 *)
(******************************************************************************)

(* A multiplicative secret sharing scheme: two Massey-based threshold schemes
   (base from C(D,k) and doubled from C(D,2k)) such that the Hadamard product
   of valid base shares yields valid doubled shares with secret = product. *)

Section mult_scheme_def.

Variable F : finFieldType.

Record MultiplicativeScheme := {
  ms_base : ThresholdScheme F F ;
  ms_doubled : ThresholdScheme F F ;
  ms_T_eq : ts_T' ms_base = ts_T' ms_doubled ;
  ms_mult : forall (s1 s2 : F)
    (shares1 shares2 : (ts_T' ms_base).+1.-tuple F),
    ts_valid ms_base s1 shares1 ->
    ts_valid ms_base s2 shares2 ->
    ts_valid ms_doubled (s1 * s2)
      (cast_tuple (congr1 S ms_T_eq)
        [tuple tnth shares1 i * tnth shares2 i | i < (ts_T' ms_base).+1]) ;
}.

End mult_scheme_def.

Arguments MultiplicativeScheme {F}.

(******************************************************************************)
(*     Section 4: Hadamard-Massey Bridge                                      *)
(******************************************************************************)

(* Key lemma: Hadamard product of massey_codewords yields a massey_codeword
   with secret = product of secrets. *)

Section hadamard_massey.

Variable F : finFieldType.
Variable n' : nat.
Let n := n'.+2.

Lemma hadamard_massey_codeword (s1 s2 : F)
    (sh1 sh2 : 'rV[F]_n'.+1) :
  hadamard (massey_codeword s1 sh1) (massey_codeword s2 sh2) =
  massey_codeword (s1 * s2) (hadamard sh1 sh2).
Proof.
apply/rowP => i; rewrite hadamardE.
case: (unliftP ord0 i) => [j ->|->].
- by rewrite !massey_codewordS hadamardE.
- by rewrite !massey_codeword0.
Qed.

End hadamard_massey.

(******************************************************************************)
(*     Section 5: AG Multiplicative Scheme Construction                       *)
(******************************************************************************)

Section ag_mult_scheme_sect.

Variable F : finFieldType.
Variable n'' : nat.
Let n := n''.+2.

(* Base code C(D,k) parameters *)
Variables (k g : nat).
Variable ev : 'M[F]_(k, n).

Hypothesis ev_rank : \rank ev = k.
Hypothesis Hk : 0 < k.
Hypothesis Hkn : k <= n.
Hypothesis Hkg : g < k.
Hypothesis Hkgn : k + g < n.
Hypothesis goppa_wt :
  forall m : 'rV[F]_k, m != 0 -> n - (k + g - 1) <= wH (m *m ev).
Hypothesis ag_priv_surj :
  forall (S : {set 'I_n}) (target : 'rV[F]_n),
    #|S| < (k - g).-1.+2 ->
    exists c : 'rV[F]_n, c \in ag_code ev /\ vproj c S = vproj target S.

(* Doubled code C(D,2k) parameters *)
Variable k2 : nat.
Variable ev_2k : 'M[F]_(k2, n).

Hypothesis ev_2k_rank : \rank ev_2k = k2.
Hypothesis Hk2 : 0 < k2.
Hypothesis Hk2n : k2 <= n.
Variable g2 : nat.
Hypothesis Hk2g : g2 < k2.
Hypothesis Hk2gn : k2 + g2 < n.
Hypothesis goppa_2k_wt :
  forall m : 'rV[F]_k2, m != 0 -> n - (k2 + g2 - 1) <= wH (m *m ev_2k).
Hypothesis ag_2k_priv_surj :
  forall (S : {set 'I_n}) (target : 'rV[F]_n),
    #|S| < (k2 - g2).-1.+2 ->
    exists c : 'rV[F]_n, c \in ag_code ev_2k /\ vproj c S = vproj target S.

(* Multiplicative property: C(D,k) * C(D,k) ⊆ C(D,2k) *)
Hypothesis ag_mult :
  forall c1 c2 : 'rV[F]_n,
    c1 \in ag_code ev -> c2 \in ag_code ev ->
    hadamard c1 c2 \in ag_code ev_2k.

(* Equal code lengths means equal ts_T' values *)
Hypothesis HT_eq : ts_T' (ag_massey ev_rank Hk Hkn Hkgn goppa_wt ag_priv_surj) =
  ts_T' (ag_massey ev_2k_rank Hk2 Hk2n Hk2gn goppa_2k_wt ag_2k_priv_surj).

Let base := ag_massey ev_rank Hk Hkn Hkgn goppa_wt ag_priv_surj.
Let doubled := ag_massey ev_2k_rank Hk2 Hk2n Hk2gn goppa_2k_wt ag_2k_priv_surj.

(* Core: multiplying valid base shares gives valid doubled shares.
   Proof: the Hadamard product of two massey_codewords is a massey_codeword
   with secret = product (hadamard_massey_codeword), and ag_mult ensures
   the result lies in the doubled code. The cast_tuple handles the
   type-level equality ts_T' base = ts_T' doubled.
   Currently axiomatized due to cast_tuple / tuple_to_rV alignment. *)
Lemma ag_massey_mult (s1 s2 : F)
    (shares1 shares2 : (ts_T' base).+1.-tuple F) :
  ts_valid base s1 shares1 ->
  ts_valid base s2 shares2 ->
  ts_valid doubled (s1 * s2)
    (cast_tuple (congr1 S HT_eq)
      [tuple tnth shares1 i * tnth shares2 i | i < (ts_T' base).+1]).
Proof.
move=> Hv1 Hv2.
rewrite /ts_valid /= /massey_valid_tuple.
have -> : congr1 S HT_eq = erefl _ by exact: eq_irrelevance.
rewrite /cast_tuple /=.
have -> : tuple_to_rV [tuple tnth shares1 i * tnth shares2 i | i < n''.+1]
          = hadamard (tuple_to_rV shares1) (tuple_to_rV shares2).
  by apply/rowP => i; rewrite !mxE tnth_mktuple.
rewrite -hadamard_massey_codeword.
exact: ag_mult Hv1 Hv2.
Qed.

Definition ag_mult_scheme : MultiplicativeScheme :=
  {| ms_base := base ;
     ms_doubled := doubled ;
     ms_T_eq := HT_eq ;
     ms_mult := ag_massey_mult |}.

End ag_mult_scheme_sect.

(******************************************************************************)
(*     Section 6: Strong Multiplication Threshold (axiomatized)               *)
(******************************************************************************)

Section strong_mult.

Variable F : finFieldType.

Variable ms : @MultiplicativeScheme F.

(* Strong multiplication condition (BGW88): the base threshold satisfies
   T <= 2*k + k', equivalently t < n/3 - 4g/3 for genus g.
   This ensures that T parties hold enough shares for both base and
   doubled scheme reconstruction, enabling secure multiplication. *)
Hypothesis strong_mult_threshold :
  ts_T (ms_base ms) <= 2 * ts_k (ms_base ms) + ts_k (ms_doubled ms).

End strong_mult.
