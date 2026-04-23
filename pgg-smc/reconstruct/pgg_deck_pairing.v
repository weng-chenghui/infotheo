(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.

(******************************************************************************)
(*                     Deck-Pairing Bit Encoding for PGG                      *)
(*                                                                            *)
(* This file formalizes the deck-pairing bit encoding used in PGG             *)
(* protocols. A "deck" is a set of N cards indexed by 'I_N. A pairing is      *)
(* an involution (a permutation g with g * g = 1) that pairs cards together.  *)
(* Bits are encoded by whether two cards form a matched pair under g, and      *)
(* reconstruction relies on equivariance: permutations that commute with g    *)
(* preserve the bit encoding.                                                 *)
(*                                                                            *)
(* Section 1: Involutions                                                     *)
(*   is_involution g  == g * g = 1 (g is an involution)                       *)
(*   is_fpf g         == g has no fixed points (fixed-point-free)             *)
(*                                                                            *)
(* Section 2: Bit Encoding                                                    *)
(*   encode_bit g b s == encodes bit b at starting position s using           *)
(*                       involution g: bit 1 -> (s, g s), bit 0 -> (s, s)    *)
(*   decode_bit g eA eB == decodes a bit from exposed cards eA, eB:           *)
(*                         true iff g eA == eB                                *)
(*                                                                            *)
(* Section 3: Equivariance and Reconstruction                                 *)
(*   equivariant_commute  == if sigma commutes with g, then                   *)
(*                           sigma (g s) = g (sigma s)                        *)
(*   decode_encode_1      == encoding bit 1 and applying a commuting          *)
(*                           permutation preserves the bit                    *)
(*   decode_encode_0      == encoding bit 0 and applying a commuting          *)
(*                           permutation preserves the bit (needs fpf)        *)
(*                                                                            *)
(* Section 4: Multi-bit encoding                                              *)
(*   multi_encode gs bs s == encodes a sequence of bits bs using a sequence   *)
(*                           of involutions gs at starting position s         *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ========================================================================== *)
(* Section 1: Involutions                                                     *)
(* ========================================================================== *)

Section involutions.

Variable N : nat.

(** An involution is a permutation that is its own inverse: g * g = 1. *)
Definition is_involution (g : {perm 'I_N}) : Prop :=
  (g * g = 1)%g.

(** A fixed-point-free (fpf) permutation has no fixed points. *)
Definition is_fpf (g : {perm 'I_N}) : Prop :=
  forall x : 'I_N, g x != x.

(** An fpf involution pairs each element with a distinct partner. *)
Lemma involution_partner (g : {perm 'I_N}) (x : 'I_N) :
  is_involution g -> g (g x) = x.
Proof.
rewrite /is_involution => Hinv.
have := congr1 (fun f : {perm 'I_N} => f x) Hinv.
by rewrite permM perm1.
Qed.

(** fpf_involution_partner_neq — fixed-point-free involutions map x to a distinct partner.
    Kind: helper.
    Why: combines the fixed-point-free predicate with the involution structure
         to give the neq witness used by deck pairing arguments.
    Used by: deck-pairing constructions where x and g x form paired slots.
    Naming: intentional; five-component name parallels the deck-pairing
            terminology "fpf + involution + partner + neq" and renaming
            would touch downstream call sites. *)
Lemma fpf_involution_partner_neq (g : {perm 'I_N}) (x : 'I_N) :
  is_involution g -> is_fpf g -> g x != x.
Proof. by move=> _ Hfpf; exact: Hfpf. Qed.

End involutions.

(* ========================================================================== *)
(* Section 2: Bit Encoding                                                    *)
(* ========================================================================== *)

Section bit_encoding.

Variable N : nat.

(** Encode a bit using an involution g at starting position s.
    - Bit 1 is encoded as the pair (s, g(s)): the two matched cards.
    - Bit 0 is encoded as the pair (s, s): the same card twice. *)
Definition encode_bit (g : {perm 'I_N}) (b : bool) (s : 'I_N) : 'I_N * 'I_N :=
  if b then (s, g s) else (s, s).

(** Decode a bit from two exposed card positions eA and eB.
    Returns true iff eB is the partner of eA under g. *)
Definition decode_bit (g : {perm 'I_N}) (eA eB : 'I_N) : bool :=
  g eA == eB.

(** Decoding the encoding of bit 1 yields true. *)
Lemma decode_encode_bit1 (g : {perm 'I_N}) (s : 'I_N) :
  decode_bit g s (g s) = true.
Proof. by rewrite /decode_bit eq_refl. Qed.

(** Decoding the encoding of bit 0 yields false, provided g is fpf. *)
Lemma decode_encode_bit0 (g : {perm 'I_N}) (s : 'I_N) :
  is_fpf g -> decode_bit g s s = false.
Proof. by rewrite /decode_bit => Hfpf; apply/negbTE; exact: Hfpf. Qed.

End bit_encoding.

(* ========================================================================== *)
(* Section 3: Equivariance and Reconstruction                                 *)
(* ========================================================================== *)

Section equivariance.

Variable N : nat.

(** Key equivariance property: if sigma commutes with g (in the group sense),
    then sigma preserves the action of g pointwise.

    Proof sketch: commute g sigma means (g * sigma = sigma * g)%g.
    Evaluating both sides at s using permM: (a * b) x = b (a x):
    - LHS: (g * sigma) s = sigma (g s)
    - RHS: (sigma * g) s = g (sigma s)
    So sigma (g s) = g (sigma s). *)
Lemma equivariant_commute (g sigma : {perm 'I_N}) (s : 'I_N) :
  commute g sigma ->
  sigma (g s) = g (sigma s).
Proof.
move=> Hcomm.
have := congr1 (fun f : {perm 'I_N} => f s) Hcomm.
by rewrite !permM.
Qed.

(** Reconstruction correctness for bit 1:
    After encoding bit 1 as (s, g(s)) and applying a commuting permutation
    sigma, the pair becomes (sigma(s), sigma(g(s))). Decoding recovers
    true because g(sigma(s)) = sigma(g(s)) by equivariance. *)
Theorem decode_encode_1 (g sigma : {perm 'I_N}) (s : 'I_N) :
  is_involution g -> commute g sigma ->
  decode_bit g (sigma s) (sigma (g s)) = true.
Proof.
move=> Hinv Hcomm.
rewrite /decode_bit (equivariant_commute _ Hcomm).
by rewrite eq_refl.
Qed.

(** Reconstruction correctness for bit 0:
    After encoding bit 0 as (s, s) and applying sigma, the pair becomes
    (sigma(s), sigma(s)). Decoding recovers false because g is fpf,
    so g(sigma(s)) != sigma(s). *)
Theorem decode_encode_0 (g sigma : {perm 'I_N}) (s : 'I_N) :
  is_involution g -> is_fpf g -> commute g sigma ->
  decode_bit g (sigma s) (sigma s) = false.
Proof.
move=> Hinv Hfpf Hcomm.
rewrite /decode_bit.
by apply/negbTE; exact: Hfpf.
Qed.

(** Equivariance extends to the full encoding: applying a commuting
    permutation to an encoded bit preserves the decoded value. *)
Theorem decode_encode_correct (g sigma : {perm 'I_N}) (b : bool) (s : 'I_N) :
  is_involution g -> is_fpf g -> commute g sigma ->
  let p := encode_bit g b s in
  decode_bit g (sigma p.1) (sigma p.2) = b.
Proof.
move=> Hinv Hfpf Hcomm /=.
case: b => /=.
- exact: decode_encode_1.
- exact: decode_encode_0.
Qed.

End equivariance.

(* ========================================================================== *)
(* Section 4: Multi-bit Encoding                                              *)
(* ========================================================================== *)

Section multi_bit.

Variable N : nat.

(** Encode multiple bits using a sequence of involutions, one per bit.
    Each involution gs_i encodes the i-th bit at starting position s. *)
Definition multi_encode (gs : seq {perm 'I_N}) (bs : seq bool)
    (s : 'I_N) : seq ('I_N * 'I_N) :=
  [seq encode_bit (nth 1%g gs i) (nth false bs i) s | i <- iota 0 (minn (size gs) (size bs))].

(** Multi-bit decoding: decode each pair using the corresponding involution.
    A dummy element is needed for [nth] on the pair sequence. *)
Definition multi_decode (gs : seq {perm 'I_N})
    (pairs : seq ('I_N * 'I_N)) (dummy : 'I_N) : seq bool :=
  [seq decode_bit (nth 1%g gs i) (nth (dummy, dummy) pairs i).1
                                  (nth (dummy, dummy) pairs i).2
    | i <- iota 0 (minn (size gs) (size pairs))].

(** Reconstruction correctness for multi-bit encoding:
    if every involution commutes with sigma and is fpf, then decoding
    after applying sigma recovers the original bits. *)
Theorem multi_decode_encode_correct
    (gs : seq {perm 'I_N}) (bs : seq bool) (sigma : {perm 'I_N})
    (s : 'I_N) (dummy : 'I_N) :
  size gs = size bs ->
  (forall i, (i < size gs)%N -> is_involution (nth 1%g gs i)) ->
  (forall i, (i < size gs)%N -> is_fpf (nth 1%g gs i)) ->
  (forall i, (i < size gs)%N -> commute (nth 1%g gs i) sigma) ->
  let encoded := multi_encode gs bs s in
  let shuffled := [seq (sigma p.1, sigma p.2) | p <- encoded] in
  multi_decode gs shuffled dummy = bs.
Proof.
move=> Hsz Hinv Hfpf Hcomm /=.
rewrite /multi_decode /multi_encode.
have Hminn : minn (size gs) (size bs) = size gs by rewrite Hsz minnn.
rewrite Hminn !size_map size_iota minnn.
apply: (@eq_from_nth _ false).
  by rewrite size_map size_iota -Hsz.
move=> i; rewrite size_map size_iota => Hi.
rewrite (nth_map 0); last by rewrite size_iota.
rewrite nth_iota //=.
rewrite (nth_map (dummy, dummy)); last by rewrite size_map size_iota.
rewrite (nth_map 0); last by rewrite size_iota.
rewrite nth_iota //=.
have := @decode_encode_correct N (nth 1%g gs i) sigma (nth false bs i) s
          (Hinv _ Hi) (Hfpf _ Hi) (Hcomm _ Hi).
by rewrite /=.
Qed.

End multi_bit.
