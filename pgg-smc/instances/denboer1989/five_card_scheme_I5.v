(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Den Boer's Five-Card Trick: the bool/'I_5 ThresholdScheme                   *)
(*                                                                            *)
(* The five-card trick recovers ONE bit (a AND b), so its secret type is      *)
(* [bool], while its shares are card POSITIONS in 'I_5. With shareT = 'I_5    *)
(* and secretT = bool, reconstruction is surjective onto bool (no cardinality  *)
(* contradiction), which is exactly what the heterogeneous-secret ReconPlug    *)
(* of covering_scheme.v requires.                                              *)
(*                                                                            *)
(* Section contents:                                                          *)
(*   fcI_valid / fcI_recon / fcI_encode == bool-secret, 'I_5-share scheme     *)
(*     ops; validity and reconstruction decode each position to a bool with   *)
(*     decode_bool, then read three-consecutive-hearts (fc_three_consec).     *)
(*   fcI_wit* == single-position privacy witness lifted to 'I_5 shares.       *)
(*   fcI_scheme == the packaged ThresholdScheme bool 'I_5.                     *)
(*   fc_sigma_pow_val == the 5-cycle power acts as +k mod 5 on positions.     *)
(*   fc_three_consec_rot == three-consecutive-hearts is rotation-invariant    *)
(*     for shifts k < 5 (essential: MathComp rot j s = s for j >= size s).    *)
(*                                                                            *)
(* The full-group reconstruction invariance over the Kim-family monodromy     *)
(* (fcI_perm_compatible_kim) lives in five_card_family.v and is built from    *)
(* fc_sigma_pow_val and fc_three_consec_rot.                                  *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_reconstruct Require Import pgg_sharing_framework.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope group_scope.

Section five_card_scheme_I5.

(******************************************************************************)
(** * Scheme operations: bool secret over 'I_5 shares                        *)
(******************************************************************************)

(** fcI_valid — shares (card positions in 'I_5) encode secret bit s iff the
    decoded heart-pattern has three consecutive hearts equal to s.
    Kind: definition. What: fc_three_consec of the decoded share row equals s.
    Why: the validity predicate of the bool/'I_5 threshold scheme. Used-by:
    fcI_scheme, fcI_reconK, fcI_encode_valid, fcI_perm_compatible_kim. *)
Definition fcI_valid (s : bool) (shares : 5.-tuple 'I_5) : Prop :=
  fc_three_consec [seq decode_bool x | x <- shares] = s.

(** fcI_recon — recover the secret bit from 'I_5 shares.
    Kind: definition. What: decode each position, then read three consecutive
    hearts. Why: the reconstruction map of the bool/'I_5 threshold scheme.
    Used-by: fcI_scheme, fcI_reconK, fcI_perm_compatible_kim. *)
Definition fcI_recon (shares : 5.-tuple 'I_5) : bool :=
  fc_three_consec [seq decode_bool x | x <- shares].

(** fcI_encode — canonical 'I_5 share row for a secret bit.
    Kind: definition. What: encode the canonical bool arrangement
    fc_arrange_tup s s into positions via encode_bool. Why: the encoding map of
    the bool/'I_5 threshold scheme. Used-by: fcI_scheme, fcI_encode_valid,
    fcI_private. *)
Definition fcI_encode (s : bool) : 5.-tuple 'I_5 :=
  [tuple of [seq encode_bool x | x <- fc_arrange_tup s s]].

(** fcI_reconK — reconstruction of valid shares returns the secret.
    Kind: helper.
    Why: the ts_correct field of fcI_scheme; both fcI_recon and fcI_valid are
    the same fc_three_consec expression, so validity is exactly the recovered
    value.
    Used by: fcI_scheme. *)
Lemma fcI_reconK (s : bool) (shares : 5.-tuple 'I_5) :
  fcI_valid s shares -> fcI_recon shares = s.
Proof. by rewrite /fcI_recon /fcI_valid => ->. Qed.

(** fcI_encode_valid — the canonical encoding is valid for its secret.
    Kind: helper.
    Why: the ts_encode_valid field of fcI_scheme. The codec round-trips
    (decode_encode_bool), reducing to fc_three_consec (fc_arrange s s) = s,
    which is fc_correct at shift 0 (rot 0 = id) with s && s = s.
    Used by: fcI_scheme, fcI_private. *)
Lemma fcI_encode_valid s : fcI_valid s (fcI_encode s).
Proof.
rewrite /fcI_valid /fcI_encode /=.
rewrite -map_comp.
under eq_map => x do rewrite /comp decode_encode_bool.
rewrite map_id.
by have := fc_correct s s (k:=0) isT; rewrite /fc_shuffle rot0 andbb.
Qed.

(******************************************************************************)
(** * Single-position privacy witness                                         *)
(******************************************************************************)

(** fcI_wit — a bool heart-pattern, valid for secret s, with a chosen value at
    a chosen position i (so a single revealed card leaks nothing).
    Kind: definition. What: per (s, i, v) a concrete five-bool row that is
    valid for s and carries v at position i. Why: the privacy witness reused at
    the 'I_5 level (each individual card position is compatible with both
    AND = 0 and AND = 1). Used-by: fcI_wit_tup, fcI_wit_valid, fcI_wit_tnth. *)
Definition fcI_wit (s : bool) (i : nat) (v : bool) : seq bool :=
  match s, v with
  | false, false => [:: false; false; false; false; false]
  | false, true =>
    match i with
    | 0 => [:: true; false; false; false; false]
    | 1 => [:: false; true; false; false; false]
    | 2 => [:: false; false; true; false; false]
    | 3 => [:: false; false; false; true; false]
    | _ => [:: false; false; false; false; true]
    end
  | true, false =>
    match i with
    | 0 => [:: false; false; true; true; true]
    | 1 => [:: false; false; true; true; true]
    | 2 => [:: true; false; false; true; true]
    | 3 => [:: true; true; false; false; true]
    | _ => [:: false; true; true; true; false]
    end
  | true, true =>
    match i with
    | 0 => [:: true; false; false; true; true]
    | 1 => [:: false; true; true; true; false]
    | 2 => [:: false; false; true; true; true]
    | 3 => [:: false; false; true; true; true]
    | _ => [:: false; false; true; true; true]
    end
  end.

(** fcI_wit_size — every branch of fcI_wit returns a five-element seq.
    Kind: helper.
    Why: the size proof to wrap fcI_wit into a 5.-tuple.
    Used by: fcI_wit_tup. *)
Lemma fcI_wit_size (s : bool) (i : nat) (v : bool) :
  i < 5 -> size (fcI_wit s i v) == 5.
Proof. by case: s; case: v; case: i => [|[|[|[|[|]]]]]. Qed.

(** fcI_wit_tup — the privacy witness as a 5-tuple of bools.
    Kind: helper.
    Why: lifts fcI_wit to the tuple expected by fc_three_consec.
    Used by: fcI_private (via fcI_wit_valid and fcI_wit_tnth). *)
Definition fcI_wit_tup (s : bool) (i : 'I_5) (v : bool) : 5.-tuple bool :=
  Tuple (@fcI_wit_size s (val i) v (ltn_ord i)).

(** fcI_wit_valid — the witness tuple reconstructs the secret s.
    Kind: helper.
    Why: shows fcI_wit_tup is valid for s so it serves as a privacy witness.
    Used by: fcI_private. *)
Lemma fcI_wit_valid s (i : 'I_5) v :
  fc_three_consec (val (fcI_wit_tup s i v)) = s.
Proof. by case: s; case: v; case: i => [[|[|[|[|[|]]]]]] //. Qed.

(** fcI_wit_tnth — the witness tuple carries value v at position i.
    Kind: helper.
    Why: lets the privacy proof pin one position to the actual share value while
    keeping the reconstructed secret fixed.
    Used by: fcI_private. *)
Lemma fcI_wit_tnth s (i : 'I_5) v :
  tnth (fcI_wit_tup s i v) i = v.
Proof.
rewrite (tnth_nth false) /=.
by case: s; case: v; case: i => [[|[|[|[|[|]]]]]] //.
Qed.

(** fcI_private — any single card position (|C| < 2) can be matched by shares
    valid for a different secret.
    Kind: helper.
    Why: the ts_private field of fcI_scheme. For the singleton coalition {j} we
    build an 'I_5 share row that carries the actual revealed value at j (so the
    coalition view is identical) while decoding to a bool witness valid for the
    other secret elsewhere; encode_bool injectivity (via decode_encode_bool)
    transports the bool witness's validity through the codec.
    Used by: fcI_scheme. *)
Lemma fcI_private (s1 s2 : bool) (shares : 5.-tuple 'I_5) (C : {set 'I_5}) :
  #|C| < 2 ->
  fcI_valid s1 shares ->
  exists shares' : 5.-tuple 'I_5,
    fcI_valid s2 shares' /\
    (forall i : 'I_5, i \in C -> tnth shares' i = tnth shares i).
Proof.
case Hs12: (s1 == s2).
- by move/eqP: Hs12 => ->; move=> _ Hv; exists shares.
- move=> HC Hv.
  case: (set_0Vmem C) => [HC0 | [j Hj]].
  + exists (fcI_encode s2); split; first exact: fcI_encode_valid.
    by move=> i; rewrite HC0 inE.
  + pose v := tnth shares j.
    pose W := fcI_wit_tup s2 j (decode_bool v).
    exists [tuple (if i == j then v else encode_bool (tnth W i)) | i < 5].
    have HCle1 : #|C| <= 1 by rewrite -ltnS.
    have Hmap : [seq decode_bool x
        | x <- [tuple if i == j then v else encode_bool (tnth W i) | i < 5]]
        = val W.
      apply: (@eq_from_nth _ false); first by rewrite size_map !size_tuple.
      move=> i Hi; rewrite size_map size_tuple in Hi.
      rewrite (nth_map (encode_bool false)); last by rewrite size_tuple.
      rewrite (nth_mktuple _ (encode_bool false) (Ordinal Hi)).
      rewrite -(tnth_nth false W (Ordinal Hi)).
      case: eqVneq => [Hij | Hij].
        by rewrite Hij /W fcI_wit_tnth.
      by rewrite decode_encode_bool.
    split.
      by rewrite /fcI_valid Hmap; exact: fcI_wit_valid.
    move=> i Hi.
    have /card_le1_eqP Heq := HCle1.
    have -> : i = j by apply: Heq.
    by rewrite tnth_mktuple eqxx.
Qed.

(** fcI_scheme — the five-card threshold scheme with a boolean secret and 'I_5
    (card-position) shares: 5 shares, privacy threshold 2 (any single card
    position reveals nothing about the AND).
    Kind: instance.
    Why: the heterogeneous-secret scheme plugged into the Kim-family
    reconstruction plug (five_card_plug, five_card_family.v); secretT =
    bool dodges the surjectivity contradiction that blocks an 'I_5 secret. *)
Definition fcI_scheme : ThresholdScheme bool 'I_5 :=
  @MkThresholdScheme bool 'I_5 4 1
    fcI_valid fcI_recon fcI_encode
    fcI_reconK fcI_private fcI_encode_valid.

(******************************************************************************)
(** * The 5-cycle as a cyclic shift, and rotation invariance                  *)
(******************************************************************************)

(** fc_sigma_pow_val — the k-th power of the 5-cycle advances a position by k
    modulo 5.
    Kind: helper.
    Why: turns the monodromy reindexing tnth shares ((fc_sigma^k) i) into a
    cyclic rotation of the decoded share row.
    Used by: fcI_perm_compatible_kim (five_card_family.v). *)
Lemma fc_sigma_pow_val (k : nat) (i : 'I_5) :
  val ((fc_sigma ^+ k) i) = (val i + k) %% 5.
Proof.
elim: k => [|k IH].
  by rewrite expg0 perm1 addn0 modn_small // ltn_ord.
rewrite expgSr permM fc_sigma_funE /fc_sigma_fun IH.
have Hstep : (val i + k.+1) %% 5 = ((val i + k) %% 5).+1 %% 5.
  by rewrite addnS -addn1 -modnDml addn1.
rewrite Hstep.
case E: ((val i + k) %% 5) => [|[|[|[|[|m]]]]] //=.
have Hlt : (val i + k) %% 5 < 5 by exact: ltn_pmod.
by rewrite E in Hlt.
Qed.

(** fc_three_consec_rot — three consecutive hearts is invariant under a cyclic
    shift by k < 5 of a five-card row.
    Kind: helper.
    Why: the rotation-invariance behind fcI_perm_compatible_kim. The hypothesis
    k < 5 is essential: MathComp's rot j s returns s unchanged when
    j >= size s, so only genuine shifts (k = k mod 5 < 5) rotate the row.
    Used by: fcI_perm_compatible_kim (five_card_family.v). *)
Lemma fc_three_consec_rot (k : nat) (s : seq bool) :
  k < 5 -> size s = 5 -> fc_three_consec (rot k s) = fc_three_consec s.
Proof.
move=> Hk Hs.
case: k Hk => [|[|[|[|[|k]]]]] // _.
all: move: Hs; case: s => [|a [|b [|c [|d [|e []]]]]] //= _.
all: by rewrite /fc_three_consec /=; case: a; case: b; case: c; case: d; case: e.
Qed.

End five_card_scheme_I5.
