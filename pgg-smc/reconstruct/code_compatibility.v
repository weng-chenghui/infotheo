(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Code Compatibility: Share-level Axiom for Monodromy Preservation           *)
(*                                                                            *)
(* Reformulates the ts_compatible hypothesis (Issue #39) at the code level.   *)
(* Instead of axiomatizing that a group action preserves ThresholdScheme      *)
(* reconstruction, we axiomatize that applying the action to share            *)
(* coordinates of a codeword yields another codeword with the same secret.    *)
(* This is mathematically equivalent for Massey-based schemes, but more       *)
(* transparent: the hypothesis speaks about the linear code C and the         *)
(* action sigma, not the ThresholdScheme abstraction.                         *)
(*                                                                            *)
(*   share_compatible C sigma == sigma applied to share coordinates of a      *)
(*     codeword in C yields a codeword with the same secret                   *)
(*   share_compat_massey_compat == share_compatible implies ts_compatible     *)
(*     for massey_scheme                                                      *)
(*   transport_ts_compatible == ts_compatible lifts through transport_scheme  *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg finalg zmodp.
From mathcomp Require Import fingroup matrix mxalgebra vector.
Require Import ssr_ext ssralg_ext hamming linearcode.
From pgg_reconstruct Require Import pgg_sharing_framework massey
  rs_massey_bridge.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Open Scope ring_scope.

(* IMPORTANT: share_compatible is the wrong abstraction for monodromy
   compatibility. Monodromy permutes sheet coordinates (evaluation points),
   but share_compatible transforms codeword values. For d=1 RS codes, the
   only sigma satisfying share_compatible is the identity. See
   notes/20260316_share_compatible_analysis.md for the full impossibility
   analysis. The bridge lemmas below are retained for potential future use
   with genuine value-transformation actions. *)

(******************************************************************************)
(*     Section 1: Share Compatibility Definition                              *)
(******************************************************************************)

Section share_compatible_def.

Variable F : finFieldType.
Variable n' : nat.
Let n := n'.+2.

Variable C : Lcode0.t F n.

(* sigma preserves codeword membership when applied only to share coordinates:
   if (s, shares) forms a codeword, then (s, sigma(shares)) also does. *)
Definition share_compatible (sigma : F -> F) : Prop :=
  forall (s : F) (shares : 'rV[F]_n'.+1),
    massey_codeword s shares \in C ->
    massey_codeword s (\row_(j < n'.+1) sigma (shares ord0 j)) \in C.

End share_compatible_def.

Arguments share_compatible {F n'} C sigma.

(******************************************************************************)
(*     Section 2: share_compatible -> ts_compatible for massey_scheme         *)
(******************************************************************************)

Section share_compat_massey.

Variable F : finFieldType.
Variable n' : nat.
Let n := n'.+2.

Variable C : Lcode0.t F n.
Hypothesis C_nt : not_trivial C.
Let d := min_dist C_nt.
Hypothesis Hd2 : 1 < d.

Variable d_perp' : nat.
Hypothesis priv_surj :
  forall (S : {set 'I_n}) (target : 'rV[F]_n),
    #|S| < d_perp'.+2 ->
    exists c : 'rV[F]_n, c \in C /\ vproj c S = vproj target S.

Variable gT : finGroupType.
Variable G : {group gT}.
Variable sigma : gT -> F -> F.

Lemma share_compat_massey_compat :
  (forall h, h \in G -> share_compatible C (sigma h)) ->
  @ts_compatible gT G _ _ (massey_scheme C_nt Hd2 priv_surj)
    (fun h x => sigma h x).
Proof.
move=> Hsc h s shares hG Hvalid.
(* Prove: acted shares form a valid codeword with secret s *)
have Hmem : @massey_codeword F n' s
    (tuple_to_rV [tuple sigma h (tnth shares i) | i < n'.+1]) \in C.
  suff -> : tuple_to_rV [tuple sigma h (tnth shares i) | i < n'.+1] =
            \row_(j < n'.+1) sigma h ((tuple_to_rV shares) ord0 j).
    exact: (Hsc _ hG _ _ Hvalid).
  by apply/rowP => j; rewrite !mxE tnth_mktuple.
(* Conclude by massey_reconstruct_correct (conversion handles record unfolding) *)
exact: @massey_reconstruct_correct F n' C C_nt Hd2 _ _ Hmem.
Qed.

End share_compat_massey.

(******************************************************************************)
(*     Section 3: ts_compatible lifts through transport_scheme                *)
(******************************************************************************)

Section transport_compat.

Variables (A B : Type).
Variable (f : A -> B) (g_inv : B -> A).
Hypothesis Hgi : cancel g_inv f.
Hypothesis Hfg : cancel f g_inv.

Variable ts : ThresholdScheme A A.

Variable gT : finGroupType.
Variable G : {group gT}.
Variable act_A : gT -> A -> A.
Variable act_B : gT -> B -> B.

Hypothesis intertwine :
  forall h, h \in G -> forall x : A, act_B h (f x) = f (act_A h x).

Lemma transport_ts_compatible :
  @ts_compatible gT G _ _ ts act_A ->
  @ts_compatible gT G _ _ (transport_scheme Hgi Hfg ts) act_B.
Proof.
move=> Hcompat h s shares hG.
(* Unfold transport_valid in hypothesis, transport_recon in goal *)
set T := (ts_T' ts).+1.
change (ts_valid ts (g_inv s) [tuple g_inv (tnth shares i) | i < T] ->
  f (ts_recon ts
    [tuple g_inv (tnth [tuple act_B h (tnth shares i0) | i0 < T] i)
    | i < T]) = s).
move=> Hvalid.
(* Step 1: rewrite g_inv . act_B to act_A . g_inv via intertwining *)
have Heq : [tuple g_inv (tnth [tuple act_B h (tnth shares i0)
              | i0 < T] i) | i < T] =
           [tuple act_A h (tnth [tuple g_inv (tnth shares i0)
              | i0 < T] i) | i < T].
  apply: eq_from_tnth => i; rewrite !tnth_mktuple.
  by rewrite -{1}(Hgi (tnth shares i)) intertwine // Hfg.
(* Step 2: apply base compatibility to get ts_recon = g_inv s *)
have Hc := Hcompat h (g_inv s)
  [tuple g_inv (tnth shares i0) | i0 < T] hG Hvalid.
by rewrite Heq Hc Hgi.
Qed.

End transport_compat.

Arguments transport_ts_compatible {A B f g_inv} Hgi Hfg {ts gT G}
  act_A act_B intertwine.
