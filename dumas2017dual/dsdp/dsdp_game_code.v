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

(* game_iface — shared export interface of the games: id_game_run takes
   ['unit] and returns the ciphertext accumulator [ciphers], id_v2_get takes
   ['unit] and returns the protocol-side V_2 sample ([msg]). *)
Definition game_iface : Interface :=
  [interface
     #val #[ id_game_run ] : 'unit → ciphers ;
     #val #[ id_v2_get   ] : 'unit → msg ].

End dsdp_game_code.
