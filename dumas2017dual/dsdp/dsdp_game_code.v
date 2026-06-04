(* DSDP symbolic-to-game derivation — back end (game-code reification).

   Scaffolding for the symbolic-to-game derivation of the DSDP protocol
   (design doc: dumas2017dual/notes/20260604-symbolic-to-game-derivation-design.md).

   This file mirrors the import header + Section parameter block + SSProve
   interface vocabulary of dumas2017dual/dsdp/ref/dsdp_security_indcpa.v so
   that game_iface, cipher_list, t_msg, t_cipher, AHE, pkey_of_party,
   card_msg, msg_of_idx, ... are in scope for the later derivation tasks.
   The inductives (he_term, game_code), denotation functions, and lemmas are
   added by subsequent tasks; per convention they are inserted BEFORE the
   final [End dsdp_game_code.] so the file keeps compiling at every step. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap reals realsum.

Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve.Crypt Require Import Package pkg_composition Pr.
Set Warnings "notation-overridden,ambiguous-paths".

From Stdlib Require Import Utf8.
From extructures Require Import ord fset fmap.

Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter spp_proba bayes.
Require Import spp_entropy.
Require Import homomorphic_encryption indcpa_ror.
Require Import dsdp_program dsdp_entropy dsdp_pismc.
Require Import smc.ssprove_ext_lossless.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import GRing.Theory Num.Theory Order.POrderTheory.
Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.
#[local] Open Scope real_scope.

(* Pin SSProve's real type as the ambient realType for this file. *)
Notation R := SSProve.Crypt.Axioms.R.

(* Deep embedding of the HE message algebra (single-sorted; Plain/Cipher
   sort-indexing deferred). nat args: HE_var/HE_const pool index; HE_enc/HE_dec
   carry a pubkey id and (for enc) a randomness slot. *)
Inductive he_term : Type :=
| HE_var   : nat -> he_term
| HE_const : nat -> he_term
| HE_enc   : nat -> he_term -> nat -> he_term
| HE_dec   : nat -> he_term -> he_term
| HE_emul  : he_term -> he_term -> he_term
| HE_epow  : he_term -> he_term -> he_term
| HE_add   : he_term -> he_term -> he_term
| HE_sub   : he_term -> he_term -> he_term
| HE_mul   : he_term -> he_term -> he_term.

(* Reified body of the id_game_run oracle. nat args are de Bruijn-style pool
   indices / pubkey ids / randomness slots. GC_enc_hop is the only hoppable
   statement; GC_let carries non-hoppable he_terms (incl. encryptions of masks). *)
Inductive game_code : Type :=
| GC_sample  : nat -> game_code -> game_code
| GC_put     : he_term -> game_code -> game_code
| GC_let     : he_term -> game_code -> game_code
| GC_enc_hop : nat -> he_term -> nat -> game_code -> game_code
| GC_ret     : seq he_term -> game_code.

(* ------------------------------------------------------------------ *)
(* Structural functions over game_code (parameter-free).              *)
(*                                                                    *)
(* Encrypt-mode mechanism for the hybrid ladder: a GC_enc_hop node is *)
(* "addressed" by its 0-based position in left-to-right traversal     *)
(* order.  zero_hop_prefix i replaces the secret plaintext of every   *)
(* hop with index < i by the canonical zero (HE_const 0) and leaves   *)
(* the rest real.  all_real / all_zero are the two endpoints of this  *)
(* prefix family; hop_sites enumerates the addressable site indices.  *)
(* ------------------------------------------------------------------ *)

(* Hybrid-ladder rung function: [zero_hop_prefix i gc] is the game at rung i
   of the AdvantageE telescoping chain — the first i GC_enc_hop sites encrypt
   the zero plaintext, the rest encrypt their real secret.  Adjacent rungs i
   and i+1 differ at exactly one hop, so each ladder step is a single IND-CPA
   reduction. *)
Fixpoint zero_hop_prefix (i : nat) (gc : game_code) : game_code :=
  match gc with
  | GC_sample n k => GC_sample n (zero_hop_prefix i k)
  | GC_put e k => GC_put e (zero_hop_prefix i k)
  | GC_let e k => GC_let e (zero_hop_prefix i k)
  | GC_enc_hop pk secret rnd k =>
      match i with
      | O => GC_enc_hop pk secret rnd (zero_hop_prefix 0 k)
      | S i' => GC_enc_hop pk (HE_const 0) rnd (zero_hop_prefix i' k)
      end
  | GC_ret outs => GC_ret outs
  end.

(* Length of the hybrid ladder: the GC_enc_hop count is the number of rung
   transitions, and the full-prefix argument that makes zero_hop_prefix
   yield all_zero. *)
Fixpoint count_hops (gc : game_code) : nat :=
  match gc with
  | GC_sample _ k => count_hops k
  | GC_put _ k => count_hops k
  | GC_let _ k => count_hops k
  | GC_enc_hop _ _ _ k => S (count_hops k)
  | GC_ret _ => 0
  end.

(* Index domain for the AdvantageE telescoping sum: each element i names one
   rung transition (zero_hop_prefix i to zero_hop_prefix i.+1), so summing
   over hop_sites gc covers every hop in the ladder exactly once. *)
Definition hop_sites (gc : game_code) : seq nat := iota 0 (count_hops gc).

(* Real-game endpoint of the hybrid ladder: every GC_enc_hop encrypts its
   real secret.  Defined via zero_hop_prefix 0 so it shares the structural
   shape of all_zero, keeping the two endpoint lemmas symmetric. *)
Definition all_real (gc : game_code) : game_code := zero_hop_prefix 0 gc.

(* Ideal-game endpoint of the hybrid ladder: every GC_enc_hop encrypts the
   canonical zero plaintext (HE_const 0).  The IND-CPA argument bounds the
   whole ladder by the distance between all_real and this endpoint. *)
Definition all_zero (gc : game_code) : game_code := zero_hop_prefix (count_hops gc) gc.

Section dsdp_game_code.

(* ------------------------------------------------------------------ *)
(* Section parameters mirrored from dsdp_security_indcpa.v lines ~105-217. *)
(* ------------------------------------------------------------------ *)

(* AHE scheme is parametric, matching the project convention from dsdp_pismc.v. *)
Variable AHE : AHEncType.

(* Refined finType carrier for encryption randomness: [rand AHE] is a bare
   Type and SSProve cannot sample over it.  card_renc / renc_card tie its
   cardinality to a nat so a uniform sample value lifts to an Renc. *)
Variable Renc : finType.
Variable card_renc : nat.
Hypothesis renc_card : #|Renc| = card_renc.

(* sample_to_renc — convert an SSProve uniform-index ['I_card_renc] to an
   [Renc] value via [enum_val] and the cardinality cast. *)
Definition sample_to_renc (i : 'I_card_renc) : Renc :=
  enum_val (cast_ord (esym renc_card) i).

(* rand_of_renc — bridge from the finType [Renc] to the AHE-side
   encryption-randomness type [rand AHE]. *)
Variable rand_of_renc : Renc -> rand AHE.

(* Section-parametric SSProve [choice_type] carriers for the message and
   ciphertext spaces, with conversions to/from the AHE [plain]/[cipher]
   types.  Mirrors indcpa_ror.v so the files share interface shapes. *)
Variable t_msg : choice_type.
Variable t_cipher : choice_type.
Variable msg_of_chmsg : t_msg -> plain AHE.
Variable chmsg_of_msg : plain AHE -> t_msg.
Variable chcipher_of_cipher : cipher AHE -> t_cipher.

(* cipher_of_chcipher — inverse of [chcipher_of_cipher], bringing an
   SSProve-side ciphertext back into [cipher AHE]. *)
Variable cipher_of_chcipher : t_cipher -> cipher AHE.

(* chcipher_of_cipherK / chmsg_of_msgK — cancel laws witnessing the
   SSProve/AHE ciphertext and message carriers are biject on representatives.
   Concrete instantiations (Benaloh/Paillier) discharge these. *)
Hypothesis chcipher_of_cipherK :
  cancel chcipher_of_cipher cipher_of_chcipher.
Hypothesis chmsg_of_msgK :
  cancel chmsg_of_msg msg_of_chmsg.

(* Public-key supply per party, parametric (no commitment to a key-generation
   strategy). *)
Variable pkey_of_party : party_id -> pub_key AHE.

(* card_msg — cardinality of the protocol-level scalar carrier ('Z_m / 'F_m
   in instantiated proofs), so [sample uniform card_msg] is well-typed. *)
Variable card_msg : nat.

(* msg_of_idx — bridge from the SSProve uniform-sample index ['I_card_msg]
   to a [plain AHE] value. *)
Variable msg_of_idx : 'I_card_msg -> plain AHE.

(* ------------------------------------------------------------------ *)
(* SSProve interface vocabulary (mirrors dsdp_security_indcpa.v ~219-309). *)
(* ------------------------------------------------------------------ *)

Local Notation "'cipher_t'" := t_cipher (in custom pack_type at level 2).

(* cipher_list — choice_type carrier for the return-value accumulator: an
   SSProve list of ciphertexts.  Each game produces a value of this type as
   its single observable output. *)
Definition cipher_list : choice_type := chList t_cipher.

Local Notation "'ciphers'" := cipher_list (in custom pack_type at level 2).

(* id_game_run — the cipher-output operation identifier exported by every
   game.  Running it executes the joint protocol run and returns the
   ciphertext accumulator visible to corrupted Alice. *)
Definition id_game_run : nat := 0%N.

(* id_v2_get — the V_2-reveal operation identifier exported by every game.
   Running it returns the protocol-side V_2 sample written into V_2_cell by
   the previous call to id_game_run. *)
Definition id_v2_get : nat := 2%N.

(* V_2_cell — shared SSProve [Location] storing the protocol-side V_2 sample,
   as an [option t_msg]: the cipher oracle [#put]s it before returning, the
   V_2 oracle [get]s it back. *)
Definition V_2_cell : Location := mkloc 8 (None : option t_msg).

(* protocol_state — the [Locations] fmap holding V_2_cell, shared as the
   [locs] field of every game and translation package. *)
Definition protocol_state : Locations := [fmap V_2_cell].

Local Notation "'msg'" := t_msg (in custom pack_type at level 2).

(* Shared export interface for every derived game (the real game, the hybrid
   ladder, the all-zero endpoint) and the oracle shims.  A single common
   interface is what keeps AdvantageE and the ≈₀ perfect-equivalence steps
   well-typed across the whole ladder, so no game needs an interface cast. *)
Definition game_iface : Interface :=
  [interface
     #val #[ id_game_run ] : 'unit → ciphers ;
     #val #[ id_v2_get   ] : 'unit → msg ].

End dsdp_game_code.
