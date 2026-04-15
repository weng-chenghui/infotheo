(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop.
From pgg_smc Require Import pgg_interface.

(******************************************************************************)
(* PGG: Parametric Overlapping Cycles OC(k,p)                                *)
(*                                                                            *)
(* OC(k,p): k+1 overlapping (p+3)-cycles on N = k + p + 3 card positions.   *)
(*   sigma_i rotates positions [i, i+1, ..., i+p+2], fixing everything else. *)
(*   Existing OC(2,3) (pgg_weval_inj.v) is the special case k=1, p=0, N=4.  *)
(*                                                                            *)
(*   oc_shift_fun i x == the windowed rotation function for generator i       *)
(*   oc_gen i         == generator i as a permutation in S_N                  *)
(*   oc_param_tuple   == (k+1)-tuple of generators                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section oc_param.

Variable k : nat.
Variable p : nat.
Let Tg := k.+1.
Let cycle_len := p.+3.
Let N := k + cycle_len.

Lemma oc_N_pos : 0 < N.
Proof. by rewrite /N addnC. Qed.

Lemma oc_base_bound (i : 'I_Tg) : val i < N.
Proof.
have Hi := valP i.
apply: (leq_trans Hi).
change (k.+1 <= k + p.+3).
by rewrite -{1}(addn0 k) ltn_add2l.
Qed.

(* Generator i acts on window [i, i + cycle_len - 1]:
   maps j -> j+1 for j in [i, i+cycle_len-2], wraps i+cycle_len-1 -> i.
   Proven injective via cancel with oc_unshift_fun. *)

Definition oc_shift_fun_raw (a : nat) (clen : nat) (bound : nat)
    (x : nat) : nat :=
  if (a <= x) && (x < a + clen) then
    if x < a + clen - 1 then x.+1 else a
  else x.

Lemma oc_shift_fun_lt (i : 'I_Tg) (x : 'I_N) :
  oc_shift_fun_raw (val i) cycle_len N (val x) < N.
Proof.
rewrite /oc_shift_fun_raw.
case: ifP => [/andP[Hi1 Hi2]|_]; last exact: valP x.
case: ifP => [Hx|_]; last exact: oc_base_bound i.
rewrite ltn_subRL add1n in Hx.
apply: leq_trans Hx _.
rewrite leq_add2r.
exact: (valP i).
Qed.

Definition oc_shift_fun (i : 'I_Tg) (x : 'I_N) : 'I_N :=
  Ordinal (oc_shift_fun_lt i x).

(* Inverse windowed rotation: undoes the shift *)
Definition oc_unshift_fun_raw (a : nat) (clen : nat) (bound : nat)
    (x : nat) : nat :=
  if (a <= x) && (x < a + clen) then
    if a < x then x.-1 else a + clen - 1
  else x.

Lemma oc_unshift_fun_lt (i : 'I_Tg) (x : 'I_N) :
  oc_unshift_fun_raw (val i) cycle_len N (val x) < N.
Proof.
rewrite /oc_unshift_fun_raw.
case: ifP => [/andP[Hi1 Hi2]|_]; last exact: valP x.
case: ifP => [Hx|_]; first exact: leq_ltn_trans (leq_pred _) (valP x).
have H1 : val i + cycle_len - 1 < val i + cycle_len.
{ rewrite ltn_subrL; apply/andP; split => //.
  rewrite addn_gt0; apply/orP; right; change (0 < p.+3); done. }
have H2 : val i + cycle_len <= N by rewrite leq_add2r; exact: valP i.
exact: (@leq_trans (val i + cycle_len) _ _ H1 H2).
Qed.

Definition oc_unshift_fun (i : 'I_Tg) (x : 'I_N) : 'I_N :=
  Ordinal (oc_unshift_fun_lt i x).

(* Cancellation: unshift cancels shift on raw nats within bounds *)
Lemma oc_shift_unshiftK (i : 'I_Tg) : cancel (oc_shift_fun i) (oc_unshift_fun i).
Proof.
move=> x; apply: val_inj => /=.
rewrite /oc_shift_fun_raw /oc_unshift_fun_raw.
case Hwin: ((val i <= val x) && (val x < val i + cycle_len)).
  move/andP: Hwin => [Hi1 Hi2].
  case Hmid: (val x < val i + cycle_len - 1).
  - (* shift gives x.+1; unshift should give x.+1 - 1 = x *)
    (* x.+1 is in window: i <= x implies i <= x.+1, and x.+1 < i + clen *)
    rewrite ltn_subRL add1n in Hmid.
    have Hwin2 : (val i <= (val x).+1) && ((val x).+1 < val i + cycle_len).
    { by rewrite (leq_trans Hi1 (leqnSn _)) Hmid. }
    rewrite Hwin2.
    (* Is i < x.+1? Yes since i <= x *)
    have -> : val i < (val x).+1 by rewrite ltnS.
    by [].
  - (* shift gives a = val i; unshift should give i + clen - 1 *)
    (* val i is in window [i, i+clen): i <= i and i < i + clen *)
    have Hwin2 : (val i <= val i) && (val i < val i + cycle_len).
    { by rewrite leqnn /= -{1}(addn0 (val i)) ltn_add2l. }
    rewrite Hwin2.
    (* Is i < i? No, so we get i + clen - 1, which equals val x *)
    rewrite ltnn.
    move/negbT: Hmid; rewrite -leqNgt => Hmid2.
    apply/eqP; rewrite eqn_leq Hmid2 andTb.
    rewrite /cycle_len subn1 -ltnS prednK;
      last by rewrite addn_gt0; apply/orP; right.
    exact: Hi2.
- (* outside window: both are identity *)
  have -> : (val i <= val x) && (val x < val i + cycle_len) = false.
  { exact: negbTE (negbT Hwin). }
  by [].
Qed.

Lemma oc_shift_fun_inj (i : 'I_Tg) : injective (oc_shift_fun i).
Proof. apply: can_inj; exact: oc_shift_unshiftK. Qed.

Definition oc_gen (i : 'I_Tg) : {perm 'I_N} := perm (@oc_shift_fun_inj i).

Definition oc_param_tuple : Tg.-tuple {perm 'I_N} := gen_tuple_of oc_gen.

Lemma oc_param_tupleE (i : 'I_Tg) : tnth oc_param_tuple i = oc_gen i.
Proof. exact: gen_tuple_ofE. Qed.

End oc_param.
