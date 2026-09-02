(******************************************************************************)
(*                                                                            *)
(* Homomorphic Encryption: Party-Labeled Types                                *)
(*                                                                            *)
(* This file provides party-labeled encryption types for protocol proofs,     *)
(* used by dumas2017dual/dsdp/.                                               *)
(*                                                                            *)
(* == Architecture ==                                                         *)
(*                                                                            *)
(*   AHEAlgebra structure (defined using Hierarchy Builder):                  *)
(*   - HETypes bundles: party, plain, rand, cipher, party_cipher, pkey        *)
(*   - isEncDec mixin: enc, dec, key, dec_correct                             *)
(*   - isAHEnc mixin: Emul, Epow, morphism_2 properties                       *)
(*   - isAHEAlgebra mixin: assoc, comm, id properties                         *)
(*                     |               \                                      *)
(*                     v                v                                     *)
(*            Benaloh_Party_AHE    Paillier_Party_AHE                         *)
(*               ct = 'Z_n        ct = 'Z_{n²}                                *)
(*               Emul = *         Emul = *                                    *)
(*               Epow = ^+        Epow = ^+                                   *)
(*                                                                            *)
(* == This File ==                                                            *)
(*                                                                            *)
(*   party type             - protocol participant type                       *)
(*   Party_Enc_Types        - idealized enc = (party * msg) for DSDP proofs   *)
(*   p.-enc, p.-key types   - type-level party tagging for entropy proofs     *)
(*                                                                            *)
(* == Related Files ==                                                        *)
(*                                                                            *)
(*   he_types.v             - HETypes and key_type type                       *)
(*   enc_dec.v              - isEncDec mixin                                  *)
(*   ahe_enc.v              - isAHEnc mixin (morphism_2 style)                *)
(*   ahe_algebra.v          - isAHEAlgebra mixin and AHEAlgebra               *)
(*   benaloh1994/benaloh_party_ahe.v - Benaloh Party_AHE instance             *)
(*   paillier1999/paillier_party_ahe.v - Paillier Party_AHE instance          *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg matrix.
From mathcomp Require Import ring boolp finmap reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.
Require Import spp_proba spp_entropy.

Import GRing.Theory.
Import Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.

Reserved Notation "u *h w" (at level 40).
Reserved Notation "u ^h w" (at level 40).

(* AHE types and structures *)
Require Export key_type.
Require Export he_types.
Require Export enc_dec.
Require Export ahe_enc.
Require Export ahe_monoid.

(* ========================================================================== *)
(*                          Party and Type Definitions                         *)
(* ========================================================================== *)

Section party_id_def.

(* party_id: concrete party identifiers for DSDP protocol.
   Named party_id to avoid shadowing HETypes.party field accessor. *)
Inductive party_id := Alice | Bob | Charlie | NoParty.

Definition party_id_eqb_subproof (p1 p2: party_id) : { p1 = p2 } + { p1 <> p2 }.
Proof. decide equality. Defined.

Definition party_id_eqb (p1 p2: party_id) : bool :=
  if party_id_eqb_subproof p1 p2 then true else false. 

Lemma party_id_eqP : Equality.axiom party_id_eqb.
Proof.
move=> p1 p2.
rewrite /party_id_eqb.
by case: party_id_eqb_subproof => /= H;constructor.
Qed.

HB.instance Definition _ := hasDecEq.Build party_id party_id_eqP.

Definition party_id_to_nat (a : party_id) : nat :=
  match a with Alice => 0 | Bob => 1 | Charlie => 2 | NoParty => 3 end.

Definition nat_to_party_id (a : nat) : party_id :=
  match a with 0 => Alice | 1 => Bob | 2 => Charlie | _ => NoParty end.

Lemma party_id_natK : cancel party_id_to_nat nat_to_party_id.
Proof. by case. Qed.

HB.instance Definition _ : isCountable party_id := CanIsCountable party_id_natK.

Definition party_id_enum := [:: Alice; Bob; Charlie; NoParty].

Lemma party_id_enumP : Finite.axiom party_id_enum.
Proof. by case. Qed.

HB.instance Definition _ := isFinite.Build party_id party_id_enumP.

End party_id_def.

Notation "'n(' w ')' " := (party_id_to_nat w).

(* ========================================================================== *)
(*                   Party-Labeled Encryption Types (for DSDP)                 *)
(* ========================================================================== *)

(* This section provides the basic party-labeled encryption types and operations
   used by the DSDP protocol proofs. This is an idealized model where
   enc = (party * msg). Secrecy is justified computationally, through the
   IND-CPA game of [dumas2017dual/dsdp/hopping/indcpa_game.v]. The
   IT-only hypotheses [E_enc_unif] and [E_enc_inde] are retired.

   For concrete encryption (Benaloh, Paillier), see sections below. *)

Section Party_Enc_Types.

Variable party : finType.
Variable msg : finComNzRingType.

(* Idealized party-labeled encryption types.
   Prefixed with party_ to avoid shadowing enc/Emul/Epow from HB mixins. *)
Definition party_enc := (party * msg)%type.
Definition party_pkey := (party * key_type * msg)%type.

Definition party_E i m : party_enc := (i, m).
Definition party_K i k m : party_pkey := (i, k, m).

Definition party_D (dk : party_pkey) (e : party_enc) : option msg :=
  match dk, e with
  | (i, k, _), (j, m) => if (i == j) && (k == Dec) then Some m else None
  end.

Definition party_Emul (e1 e2 : party_enc) : party_enc := 
  match (e1, e2) with
  | ((i1, m1), (i2, m2)) => if i1 == i2 then party_E i1 (m1 + m2) else party_E i1 0
  end.

Definition party_Epow (e : party_enc) (m2 : msg) : party_enc :=
  match e with
  | (i, m1) => party_E i (m1 * m2)
  end.

End Party_Enc_Types.

Section party_key_def.


(* Need something like {RV P -> Alice.-key Dec T} in view;
   `T` means any type of the key's value.
*)

Variant party_key (p : party_id) (k : key_type) (T : Type) : Type :=
  KeyOf of T.

Definition party_key_v p k T (pk : party_key p k T) : T :=
  let 'KeyOf v := pk in v.

Variable (p : party_id) (k : key_type)(T : Type).

HB.instance Definition _ := [isNew for @party_key_v p k T].

End party_key_def.

(* The [.-key] postfix is MathComp's indexed-by spelling, as in [pi.-group]
   and in infotheo's own [R.-fdist T].  The two indices here are a party tag
   and a key sort, so a value of [p.-key k T] is a key of sort k held by
   party p, carrying a payload in T. *)
Notation "p .-key k" := (party_key p k)
  (at level 2, format "p .-key k") : type_scope.

Coercion tuple_of_party_key p k T (pk : p.-key k T) : (party_id * key_type * T) :=
  let 'KeyOf v := pk in (p, k, v).

Section party_key_types.

HB.instance Definition _ p k (T : eqType) : hasDecEq (p.-key k T) :=
  [Equality of p.-key k T by <:].
HB.instance Definition _ p k (T : choiceType) :=
  [Choice of p.-key k T by <:].
HB.instance Definition _ p k (T : countType) :=
  [Countable of p.-key k T by <:].
HB.instance Definition _ p k (T : finType) :=
  [Finite of p.-key k T by <:].

Variable (p : party_id)(k : key_type)(T : finType).

Lemma card_party_key : #|{:p.-key k T}| = #|T|.
Proof.
apply (bij_eq_card (f:=@party_key_v p k T)).
exists (@KeyOf p k T).
by case.
by [].
Qed.

End party_key_types.


Section enc_type_def.

(*
  Because {RV P -> enc} is wrong:
  we have no random variables that output
  (different parties x different messages),
  but only (one fixed party x different messages).
  
  So we need to define a type level label like: {RV P -> Alice.-enc}.
*)

Variant enc_for (p : party_id) (T : Type) : Type :=
  EncFor of T.

Variable (p : party_id) (T : Type).

Definition enc_for_v p T (e : enc_for p T) : T :=
  let 'EncFor v := e in v.

HB.instance Definition _ := [isNew for @enc_for_v p T].

End enc_type_def.

Notation "p .-enc" := (enc_for p)
  (at level 2, format "p .-enc") : type_scope.

Notation "{ 'enc_for' p 'of' T }" := (p.-enc T : predArgType)
  (at level 0, only parsing) : type_scope.

Coercion tuple_of_enc_for p T (e : p.-enc T) : (party_id * T) :=
  let 'EncFor v := e in (p, v).

Section enc_types.

HB.instance Definition _ p (T : eqType) : hasDecEq (p.-enc T) :=
  [Equality of p.-enc T by <:].
HB.instance Definition _ p (T : choiceType) :=
  [Choice of p.-enc T by <:].
HB.instance Definition _ p (T : countType) :=
  [Countable of p.-enc T by <:].
HB.instance Definition _ p (T : finType) :=
  [Finite of p.-enc T by <:].

Definition E' (T : Type) (p : party_id) (t : T) : p.-enc T :=
  EncFor p t.

Variable (p : party_id) (T : finType).

Lemma card_enc_for :
  #|{:p.-enc T}| = #|T|.
Proof.
apply (bij_eq_card (f:=@enc_for_v p T)).
exists (@EncFor p T).
by case.
by [].
Qed.

Lemma card_enc_for' : forall (n : nat),
  #|T| = n.+1 -> #|{:p.-enc T}| = n.+1.
Proof. by rewrite card_enc_for. Qed.

End enc_types.

Section enc_lemmas.

Context {R : realType}.
Variables (T : finType)(P : R.-fdist T).

(* The IT-only hypotheses [E_enc_unif] and [E_enc_inde] used to live here.
   They postulated that fresh ciphertexts are uniform over the ciphertext
   space and independent of all other random variables. The second is unsound
   for any correct encryption scheme over more than one plaintext, since
   decryption relates a ciphertext to its plaintext, so both are retired.
   Secrecy of the
   DSDP protocol is justified computationally instead, through the IND-CPA
   game of [dumas2017dual/dsdp/hopping/indcpa_game.v]. The contraction
   lemma [E_enc_ce_contract] below takes an explicit independence hypothesis
   as input, so it remains usable wherever such an assumption is locally
   justified. *)

(* Ciphertext conditioning contract: when the ciphertext E is independent of
   the pair (X, Z), conditioning on E alongside X leaves the conditional
   entropy of Z given X unchanged.
   Independence is a hypothesis, not a property of encryption, and it is the
   only one: neither uniformity of E nor non-vanishing of the conditioning
   events is assumed.  Wherever a protocol can justify that independence
   locally, this contracts the ciphertext out of a conditioner; where it
   cannot, the ciphertext is charged for computationally instead. *)
Lemma E_enc_ce_contract (A B C : finType) (p : party_id)
  (X : {RV P -> A})(E : {RV P -> p.-enc B})(Z : {RV P -> C})(n : nat):
  P |= [%X, Z] _|_ E ->
  #|B| = n.+1 ->
  `H(Z | [%X, E]) = `H(Z | X).
Proof.
move=> HindeXZ_E card_B.
apply (cpr_centropy (Y2:=X)(Y3:=E)) => c a b.
move=> XEab_neq0.
have HindeZX_E : P |= [%Z, X] _|_ E.
  exact: (inde_RV_comp (fun p => (p.2, p.1)) idfun HindeXZ_E).
have HindeZE_X : Z _|_ E | X.
  exact: (inde_RV2_cinde HindeZX_E).
rewrite pfwd1_pairC in XEab_neq0.
have H2 := (cinde_alt c HindeZE_X XEab_neq0).
rewrite cpr_eq_pairCr.
exact: H2.
Qed.

End enc_lemmas.

(*
  Methodology note (two-layer justification for HE-based SMC proofs)

  An idealized IT interface would postulate that ciphertext random variables
  are uniform over the ciphertext type and independent of all other random
  variables. The second postulate is unsound for any correct encryption
  scheme over more than one plaintext, since decryption relates the
  ciphertext to its plaintext, so this development states secrecy
  computationally instead. Each of the two hops of the DSDP corrupted-Alice
  argument is priced by [indcpa_epsilon], the advantage defined in
  [dumas2017dual/dsdp/hopping/indcpa_game.v], of a reduction adversary
  built in [dumas2017dual/dsdp/hopping/dsdp_alice_hop_secrecy.v]. The
  contraction lemma [E_enc_ce_contract] above takes its independence
  hypothesis explicitly and is usable wherever that hypothesis is locally
  justified.

  Two things carry a bound of that shape to a concrete scheme. The first is
  an adversary class: [indcpa_epsilon_assumption], in the same file, packages
  a Boolean classifier on adversaries, one epsilon, and the assumption that
  every classified adversary stays below it at every key built from a private
  key. The class restriction is what keeps the assumed epsilon small: an
  adversary holding the matching private key and submitting a nonzero
  challenge plaintext decrypts the challenge, so a class admitting every
  adversary is forced to assume an epsilon of at least 1 whenever the
  plaintext space has more than one element. The second is an instantiation of that record at a
  scheme, which [dumas2017dual/dsdp/hopping/paillier_indcpa_instance.v]
  does for Paillier, leaving the whole assumption a parameter that a proof
  from decisional composite residuosity would supply.

  Replacing the retired hypotheses does not make the resulting bounds purely
  computational. The DSDP guessing bound sums an unconditional
  information-theoretic term, the inverse plaintext-space cardinality left by
  the leaked output, with the assumption-conditional advantage term; the two
  DSDP files label the summands where they state them.
*)
