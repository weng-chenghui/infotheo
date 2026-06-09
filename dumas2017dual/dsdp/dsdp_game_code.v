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

(* Reified body of the id_game_run oracle. GC_sample's nat is a sample
   cardinality; GC_enc_hop's is a pubkey id (its randomness is sampled inline).
   GC_enc_hop is the only hoppable statement; GC_let carries non-hoppable
   he_terms (incl. mask encryptions, whose he_term randomness slots index the
   de_rand pool). GC_put writes the V_2 cell, GC_put_output the S output cell;
   neither is a hop and neither contributes to the return list. *)
Inductive game_code : Type :=
| GC_sample     : nat -> game_code -> game_code
| GC_put        : he_term -> game_code -> game_code
| GC_put_output : he_term -> game_code -> game_code
| GC_let        : he_term -> game_code -> game_code
| GC_enc_hop    : nat -> he_term -> game_code -> game_code
| GC_ret        : seq he_term -> game_code.

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
  | GC_put_output e k => GC_put_output e (zero_hop_prefix i k)
  | GC_let e k => GC_let e (zero_hop_prefix i k)
  | GC_enc_hop pk secret k =>
      match i with
      | O => GC_enc_hop pk secret (zero_hop_prefix 0 k)
      | S i' => GC_enc_hop pk (HE_const 0) (zero_hop_prefix i' k)
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
  | GC_put_output _ k => count_hops k
  | GC_let _ k => count_hops k
  | GC_enc_hop _ _ k => S (count_hops k)
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

(* cipher_of_chcipher brings an oracle-returned ciphertext back to [cipher AHE]
   in denote_game_shim; chcipher_of_cipherK and chmsg_of_msgK discharge the
   encode/decode round-trips at the target hop in denote_run_shim_real_equiv
   and denote_run_shim_zero_equiv, mirroring the *_equiv_* lemmas of
   dsdp_security_indcpa.v. *)

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

(* id_s_get — the output-reveal operation identifier exported by the
   output-exposing games.  Running it returns the scalar-product output S
   written into S_output_cell by the previous call to id_game_run. *)
Definition id_s_get : nat := 3%N.

(* V_2_cell — shared SSProve [Location] storing the protocol-side V_2 sample,
   as an [option t_msg]: the cipher oracle [#put]s it before returning, the
   V_2 oracle [get]s it back. *)
Definition V_2_cell : Location := mkloc 8 (None : option t_msg).

(* S_output_cell — shared SSProve [Location] storing the scalar-product output
   S, as an [option t_msg], parallel to [V_2_cell]: an output-exposing game
   [#put]s it from a [GC_put_output] statement, the output oracle [id_s_get]
   [get]s it back. *)
Definition S_output_cell : Location := mkloc 9 (None : option t_msg).

(* protocol_state — the [Locations] fmap holding V_2_cell and S_output_cell,
   shared as the [locs] field of every game and translation package. *)
Definition protocol_state : Locations := [fmap V_2_cell ; S_output_cell].

Local Notation "'msg'" := t_msg (in custom pack_type at level 2).

(* Shared export interface for every derived game (the real game, the hybrid
   ladder, the all-zero endpoint) and the oracle shims.  A single common
   interface is what keeps AdvantageE and the ≈₀ perfect-equivalence steps
   well-typed across the whole ladder, so no game needs an interface cast. *)
Definition game_iface : Interface :=
  [interface
     #val #[ id_game_run ] : 'unit → ciphers ;
     #val #[ id_v2_get   ] : 'unit → msg ].

(* game_iface_leak_S — the output-exposing export interface: [game_iface]
   extended with the output-reveal operation [id_s_get : 'unit → msg].  Kept
   separate from [game_iface] so Part I's games, perfect-equivalence steps and
   generic hybrid bound stay over the unextended interface. *)
Definition game_iface_leak_S : Interface :=
  [interface
     #val #[ id_game_run ] : 'unit → ciphers ;
     #val #[ id_v2_get   ] : 'unit → msg ;
     #val #[ id_s_get    ] : 'unit → msg ].

(* rand0 — default encryption-randomness value, used only as the [nth]
   fallback when a [HE_enc]/[GC_enc_hop] randomness slot indexes past the
   denotation env's randomness pool.  Well-formed game_code never reaches it
   (every slot is populated by a prior [GC_sample]); it exists solely to keep
   [de_rand_nth] total, since [rand AHE] is a bare Type with no canonical 0. *)
Variable rand0 : rand AHE.

(* ------------------------------------------------------------------ *)
(* Denotation env (Checkpoint 1): the single-sort value pool, the     *)
(* randomness pool, their pushers, and the indexed lookup helpers.    *)
(* ------------------------------------------------------------------ *)

(* gval — single-sort denotation value: a denoted he_term is either a plaintext
   scalar (Gplain) or a ciphertext (Gcipher).  Sort indexing is deferred, so
   the projections [as_plain]/[as_cipher] coerce on the wrong constructor by
   returning the ring 0, mirroring the deep embedding's single-sort he_term. *)
Inductive gval : Type :=
| Gplain  : plain AHE -> gval
| Gcipher : cipher AHE -> gval.

(* as_plain — project a [gval] to its plaintext component, defaulting to 0 on a
   ciphertext (the wrong sort).  Used wherever a denoted he_term is consumed in
   a plaintext position (encryption message, [Epow] exponent, ring ops). *)
Definition as_plain (g : gval) : plain AHE :=
  match g with Gplain p => p | Gcipher _ => 0 end.

(* as_cipher — project a [gval] to its ciphertext component, defaulting to 0 on
   a plaintext (the wrong sort).  Used wherever a denoted he_term is consumed in
   a ciphertext position ([Emul]/[Epow] base, [GC_ret] output). *)
Definition as_cipher (g : gval) : cipher AHE :=
  match g with Gcipher c => c | Gplain _ => 0 end.

(* denv — denotation environment threaded through [denote_run].  Two de
   Bruijn-style pools, each pushed at the front (index 0 is most recent):
   [de_val] holds scalar/cipher values addressed by [HE_var], and [de_rand]
   holds encryption-randomness addressed by the [HE_enc]/[GC_enc_hop] slot. *)
Record denv := MkDenv {
  de_val  : seq gval ;
  de_rand : seq (rand AHE) ;
}.

(* empty_denv — the initial denotation env: both pools empty.  [denote_run]
   starts from here at the top of the id_game_run oracle body. *)
Definition empty_denv : denv := MkDenv [::] [::].

(* push_val — extend the value pool with a fresh denoted value at index 0
   (consumed by [GC_sample]'s scalar branch, [GC_let], and [GC_enc_hop]). *)
Definition push_val (g : gval) (e : denv) : denv :=
  MkDenv (g :: de_val e) (de_rand e).

(* push_rand — extend the randomness pool with a fresh randomness at index 0
   (consumed by [GC_sample]'s randomness branch). *)
Definition push_rand (r : rand AHE) (e : denv) : denv :=
  MkDenv (de_val e) (r :: de_rand e).

(* de_val_nth — look up the i-th value-pool entry, defaulting to [Gplain 0]
   when the index is out of range (only in malformed game_code). *)
Definition de_val_nth (e : denv) (i : nat) : gval :=
  nth (Gplain 0) (de_val e) i.

(* de_rand_nth — look up the i-th randomness-pool entry, defaulting to [rand0]
   when the index is out of range (only in malformed game_code). *)
Definition de_rand_nth (e : denv) (i : nat) : rand AHE :=
  nth rand0 (de_rand e) i.

(* ------------------------------------------------------------------ *)
(* Denotation of he_term (Checkpoint 2): the single-sort evaluator    *)
(* mapping a deep-embedded message-algebra term to a [gval] under an  *)
(* env, reusing the project's AHE operations (enc/Emul/Epow) and ring *)
(* operations on [plain AHE].                                         *)
(* ------------------------------------------------------------------ *)

(* denote_he — evaluate a deep-embedded [he_term] to a [gval] under a denotation
   env.  Variables resolve through [de_val]; encryptions consume a randomness
   slot from [de_rand] and the party's public key via [nat_to_party_id];
   homomorphic [Emul]/[Epow] and the plaintext ring ops are the project's own
   AHE operations (never redefined).  [HE_dec] has no secret-key supply in this
   game-code denotation and never occurs on the game path, so it defaults to
   [Gplain 0]. *)
Fixpoint denote_he (e : denv) (t : he_term) : gval :=
  match t with
  | HE_var i => de_val_nth e i
  | HE_const k => Gplain (k%:R)
  | HE_enc pk m r =>
      Gcipher (enc (pkey_of_party (nat_to_party_id pk))
                   (as_plain (denote_he e m)) (de_rand_nth e r))
  | HE_dec _ _ => Gplain 0
  | HE_emul a b =>
      Gcipher (Emul (as_cipher (denote_he e a)) (as_cipher (denote_he e b)))
  | HE_epow c x =>
      Gcipher (Epow (as_cipher (denote_he e c)) (as_plain (denote_he e x)))
  | HE_add a b => Gplain (as_plain (denote_he e a) + as_plain (denote_he e b))
  | HE_sub a b => Gplain (as_plain (denote_he e a) - as_plain (denote_he e b))
  | HE_mul a b => Gplain (as_plain (denote_he e a) * as_plain (denote_he e b))
  end.

(* ------------------------------------------------------------------ *)
(* Denotation of game_code (Checkpoint 3): the raw_code core of the   *)
(* id_game_run oracle.  Recurses on the game_code structure, threading *)
(* the denotation env through each continuation and extending it INSIDE *)
(* the continuation (so de Bruijn indices align with the binder depth). *)
(* ------------------------------------------------------------------ *)

(* denote_run — lower a [game_code] body to an SSProve [raw_code cipher_list]
   under a denotation env.  [GC_sample] routes on the requested cardinality
   (an n-discriminator, NOT a dependent cast): [card_msg] samples a scalar and
   pushes it on the value pool, [card_renc] samples encryption-randomness and
   pushes it on the randomness pool, any other [n] samples without pushing
   (a default unused by well-formed game_code).  [GC_put] writes the protocol
   V_2 cell; [GC_put_output] writes the scalar-product output [S_output_cell];
   [GC_let] pushes a denoted value; [GC_enc_hop] pushes the denoted
   encryption (the zero/real secret choice is already baked into [secret] by
   [zero_hop_prefix]); [GC_ret] returns the denoted output ciphertext list. *)
Fixpoint denote_run (e : denv) (gc : game_code) : raw_code cipher_list :=
  match gc with
  | GC_sample n k =>
      if n == card_msg then
        x ← sample uniform card_msg ;;
        denote_run (push_val (Gplain (msg_of_idx x)) e) k
      else if n == card_renc then
        x ← sample uniform card_renc ;;
        denote_run (push_rand (rand_of_renc (sample_to_renc x)) e) k
      else
        x ← sample uniform n ;; denote_run e k
  | GC_put t k =>
      #put V_2_cell := Some (chmsg_of_msg (as_plain (denote_he e t))) ;;
      denote_run e k
  | GC_put_output t k =>
      #put S_output_cell := Some (chmsg_of_msg (as_plain (denote_he e t))) ;;
      denote_run e k
  | GC_let t k =>
      denote_run (push_val (denote_he e t) e) k
  | GC_enc_hop pk secret k =>
      ir_hop ← sample uniform card_renc ;;
      denote_run
        (push_val
           (Gcipher (enc (pkey_of_party (nat_to_party_id pk))
                         (as_plain (denote_he e secret))
                         (rand_of_renc (sample_to_renc ir_hop))))
           e) k
  | GC_ret outs =>
      ret ([seq chcipher_of_cipher (as_cipher (denote_he e o)) | o <- outs]
           : cipher_list)
  end.

(* ------------------------------------------------------------------ *)
(* Denotation of game_code as a package (Checkpoint 4): wrap the       *)
(* raw_code core as the id_game_run oracle and pair it with the fixed  *)
(* id_v2_get oracle (copied verbatim from game_real), over the shared  *)
(* protocol_state locs and game_iface export interface.                *)
(* ------------------------------------------------------------------ *)

(* Lets denote_game_valid assemble the package: SSProve's mkpackage cannot
   infer validity through the opaque denote_run recursion, so this ValidCode
   certificate is supplied explicitly, by structural induction on gc.  Generic
   over the env and game_code so every hybrid-ladder rung reuses one proof.
   Naming: the _valid suffix follows SSProve's ValidCode/ValidPackage
   certificate convention (cf. pack_valid) — the project's upstream-class
   naming exception — and is shared by the three denote_*_valid lemmas. *)
Lemma denote_run_valid (e : denv) (gc : game_code) :
  ValidCode protocol_state [interface] (denote_run e gc).
Proof.
elim: gc e => [n k IH|t k IH|t k IH|t k IH|pk secret k IH|outs] e /=.
- case: (n == card_msg); last case: (n == card_renc).
  + by apply: valid_sampler => x; exact: IH.
  + by apply: valid_sampler => x; exact: IH.
  + by apply: valid_sampler => x; exact: IH.
- by apply: valid_putr; last exact: IH.
- by apply: valid_putr; last exact: IH.
- exact: IH.
- by apply: valid_sampler => x; exact: IH.
- exact: valid_ret.
Qed.

(* denote_v2_get_body — the V_2-reveal oracle body, copied verbatim from
   [game_real]'s [id_v2_get] oracle: read [V_2_cell] and return the stored
   sample (or the canonical 0 message when unset). *)
Definition denote_v2_get_body : raw_code t_msg :=
  stored ← get V_2_cell ;;
  match stored with
  | Some v => @ret t_msg v
  | None   => @ret t_msg (chmsg_of_msg (0%R : plain AHE))
  end.

(* Validity certificate for the V_2-reveal oracle: denote_game_valid assembles
   the two-oracle package by name and must supply a valid-code proof for each
   oracle independently. *)
Lemma denote_v2_get_valid :
  ValidCode protocol_state [interface] denote_v2_get_body.
Proof.
rewrite /denote_v2_get_body.
apply: valid_getr; first by [].
by case=> [v|]; exact: valid_ret.
Qed.

(* denote_game_raw — the raw two-oracle map underlying [denote_game]: the
   [id_game_run] oracle runs [denote_run] from the empty env, the [id_v2_get]
   oracle reveals the protocol-side V_2 sample. *)
Definition denote_game_raw (gc : game_code) : raw_package :=
  mkfmap
    [:: (id_game_run, mkdef 'unit cipher_list (fun _ => denote_run empty_denv gc))
      ; (id_v2_get,   mkdef 'unit t_msg       (fun _ => denote_v2_get_body)) ].

(* Discharges the pack_valid field of denote_game: SSProve cannot infer
   ValidPackage through the opaque denote_game_raw map, so the certificate is
   supplied explicitly (the V_2-reveal oracle via denote_v2_get_valid, the run
   oracle via denote_run_valid). *)
Lemma denote_game_valid (gc : game_code) :
  ValidPackage protocol_state [interface] game_iface (denote_game_raw gc).
Proof.
rewrite /denote_game_raw /game_iface.
apply: valid_package_cons; last by move=> x; exact: denote_run_valid.
by apply: valid_package_cons; last by move=> x; exact: denote_v2_get_valid.
Qed.

(* denote_game — lower a [game_code] to an SSProve package exporting
   [game_iface].  The [id_game_run] oracle runs [denote_run] from the empty
   env; the [id_v2_get] oracle reveals the protocol-side V_2 sample written
   into [V_2_cell] (verbatim from [game_real]).  Every derived game (real
   endpoint, hybrid rungs, all-zero endpoint) is the image under [denote_game]
   of a [game_code], so AdvantageE / perfect-equivalence steps stay well-typed
   across the ladder without an interface cast. *)
Definition denote_game (gc : game_code) :
  package [interface] game_iface :=
  mkpackage protocol_state (denote_game_raw gc) (denote_game_valid gc).

(* ------------------------------------------------------------------ *)
(* Output-exposing denotation: the same two oracles as denote_game     *)
(* plus an id_s_get oracle reading the scalar-product output written    *)
(* into S_output_cell by a GC_put_output statement.                     *)
(* ------------------------------------------------------------------ *)

(* denote_s_get_body — the output-reveal oracle body, mirroring
   [denote_v2_get_body] on [S_output_cell]: read the cell and return the stored
   output S (or the canonical 0 message when unset, i.e. for game_code with no
   [GC_put_output] statement). *)
Definition denote_s_get_body : raw_code t_msg :=
  stored ← get S_output_cell ;;
  match stored with
  | Some v => @ret t_msg v
  | None   => @ret t_msg (chmsg_of_msg (0%R : plain AHE))
  end.

(* Validity certificate for the output-reveal oracle, supplied explicitly to
   denote_game_leak_S_valid alongside the run and V_2-reveal oracles. *)
Lemma denote_s_get_valid :
  ValidCode protocol_state [interface] denote_s_get_body.
Proof.
rewrite /denote_s_get_body.
apply: valid_getr; first by [].
by case=> [v|]; exact: valid_ret.
Qed.

(* denote_game_leak_S_raw — the raw three-oracle map underlying
   [denote_game_leak_S]: the [id_game_run] and [id_v2_get] oracles are the
   [denote_game_raw] pair, plus an [id_s_get] oracle revealing the output S. *)
Definition denote_game_leak_S_raw (gc : game_code) : raw_package :=
  mkfmap
    [:: (id_game_run, mkdef 'unit cipher_list (fun _ => denote_run empty_denv gc))
      ; (id_v2_get,   mkdef 'unit t_msg       (fun _ => denote_v2_get_body))
      ; (id_s_get,    mkdef 'unit t_msg       (fun _ => denote_s_get_body)) ].

(* Discharges the pack_valid field of denote_game_leak_S: SSProve cannot infer
   ValidPackage through the opaque denote_game_leak_S_raw map, so the
   certificate is supplied explicitly (run oracle via denote_run_valid, the two
   reveal oracles via denote_v2_get_valid / denote_s_get_valid). *)
Lemma denote_game_leak_S_valid (gc : game_code) :
  ValidPackage protocol_state [interface] game_iface_leak_S
    (denote_game_leak_S_raw gc).
Proof.
rewrite /denote_game_leak_S_raw /game_iface_leak_S.
apply: valid_package_cons; last by move=> x; exact: denote_run_valid.
apply: valid_package_cons; last by move=> x; exact: denote_v2_get_valid.
by apply: valid_package_cons; last by move=> x; exact: denote_s_get_valid.
Qed.

(* denote_game_leak_S — lower a [game_code] to an SSProve package exporting
   [game_iface_leak_S].  The [id_game_run] and [id_v2_get] oracles are exactly
   those of [denote_game]; the [id_s_get] oracle reveals the scalar-product
   output S written into [S_output_cell] by a [GC_put_output] statement.  It is
   generic over [game_code]: for code without a [GC_put_output] the cell stays
   [None] and [id_s_get] returns the canonical 0 message; for output-exposing
   code it returns the written S. *)
Definition denote_game_leak_S (gc : game_code) :
  package [interface] game_iface_leak_S :=
  mkpackage protocol_state (denote_game_leak_S_raw gc)
    (denote_game_leak_S_valid gc).

(* ------------------------------------------------------------------ *)
(* Oracle-routed denotation (one-hop shim): the raw_code core and      *)
(* package that route a single GC_enc_hop site through the IND-CPA     *)
(* encryption oracle, leaving every other node identical to denote_run.*)
(* ------------------------------------------------------------------ *)

(* denote_run_shim — oracle-importing variant of [denote_run] for a single
   IND-CPA reduction: routes exactly the [site]-th [GC_enc_hop] through the
   imported encryption oracle, so composing with the real/zero IND-CPA oracle
   yields one rung of the hybrid ladder.  All other nodes denote identically to
   [denote_run], preserving the sample sequence.  Threads the denotation env and
   a hop counter [hop] (the running index of [GC_enc_hop] nodes seen so far):
   the counter advances only at [GC_enc_hop], so every [GC_sample], [GC_put],
   [GC_let] and every off-target [GC_enc_hop] denotes exactly as in [denote_run]
   — the sample sequence is therefore identical to [denote_run]'s (the target
   hop's randomness is still drawn by its [GC_sample] into [de_rand], just left
   unused once the oracle supplies the ciphertext).  At the matching hop the
   oracle is queried on the hop's party index and plaintext (encoded via
   [chmsg_of_msg]); the returned [t_cipher] is brought back into [cipher AHE] by
   [cipher_of_chcipher] and pushed as the hop's value (so a downstream [GC_ret]
   re-encodes it through [chcipher_of_cipher], collapsing the round-trip by
   [chcipher_of_cipherK] in the later hop-equivalence proof). *)
Fixpoint denote_run_shim
    (site : nat) (hop : nat) (e : denv) (gc : game_code) :
    raw_code cipher_list :=
  match gc with
  | GC_sample n k =>
      if n == card_msg then
        x ← sample uniform card_msg ;;
        denote_run_shim site hop (push_val (Gplain (msg_of_idx x)) e) k
      else if n == card_renc then
        x ← sample uniform card_renc ;;
        denote_run_shim site hop
          (push_rand (rand_of_renc (sample_to_renc x)) e) k
      else
        x ← sample uniform n ;; denote_run_shim site hop e k
  | GC_put t k =>
      #put V_2_cell := Some (chmsg_of_msg (as_plain (denote_he e t))) ;;
      denote_run_shim site hop e k
  | GC_put_output t k =>
      #put S_output_cell := Some (chmsg_of_msg (as_plain (denote_he e t))) ;;
      denote_run_shim site hop e k
  | GC_let t k =>
      denote_run_shim site hop (push_val (denote_he e t) e) k
  | GC_enc_hop pk secret k =>
      if hop == site then
        #import {sig #[ id_oracle_encrypt ] : 'nat × msg → cipher_t }
          as oracle_enc ;;
        ch ← oracle_enc
               (pk, chmsg_of_msg (as_plain (denote_he e secret))) ;;
        denote_run_shim site hop.+1
          (push_val (Gcipher (cipher_of_chcipher ch)) e) k
      else
        ir_hop ← sample uniform card_renc ;;
        denote_run_shim site hop.+1
          (push_val
             (Gcipher (enc (pkey_of_party (nat_to_party_id pk))
                           (as_plain (denote_he e secret))
                           (rand_of_renc (sample_to_renc ir_hop))))
             e) k
  | GC_ret outs =>
      ret ([seq chcipher_of_cipher (as_cipher (denote_he e o)) | o <- outs]
           : cipher_list)
  end.

(* Certificate that the oracle-routed run core type-checks against the IND-CPA
   encryption import: SSProve cannot infer [ValidCode] through the opaque
   [denote_run_shim] recursion, so it is supplied explicitly by structural
   induction on [gc], generic over [site], [hop] and the env.  The
   oracle-routed hop discharges its [fhas] obligation against
   [oracle_encrypt_iface t_msg t_cipher]; all other nodes mirror
   [denote_run_valid]. *)
Lemma denote_run_shim_valid (site hop : nat) (e : denv) (gc : game_code) :
  ValidCode protocol_state (oracle_encrypt_iface t_msg t_cipher)
    (denote_run_shim site hop e gc).
Proof.
elim: gc site hop e => [n k IH|t k IH|t k IH|t k IH|pk secret k IH|outs] site hop e /=.
- case: (n == card_msg); last case: (n == card_renc).
  + by apply: valid_sampler => x; exact: IH.
  + by apply: valid_sampler => x; exact: IH.
  + by apply: valid_sampler => x; exact: IH.
- by apply: valid_putr; last exact: IH.
- by apply: valid_putr; last exact: IH.
- exact: IH.
- case: (hop == site).
  + by apply: valid_opr; last by move=> v; exact: IH.
  + by apply: valid_sampler => x; exact: IH.
- exact: valid_ret.
Qed.

(* ValidPackage certificate for denote_game_shim, needed because SSProve cannot
   infer it through the opaque oracle-routed run map.  The run oracle uses
   denote_run_shim_valid; the V_2-reveal oracle lifts its empty-import
   certificate via valid_injectMap. *)
Lemma denote_game_shim_valid (gc : game_code) (site : nat) :
  ValidPackage protocol_state (oracle_encrypt_iface t_msg t_cipher) game_iface
    (mkfmap
       [:: (id_game_run, mkdef 'unit cipher_list
              (fun _ => denote_run_shim site 0 empty_denv gc))
         ; (id_v2_get,   mkdef 'unit t_msg (fun _ => denote_v2_get_body)) ]).
Proof.
rewrite /game_iface.
apply: valid_package_cons; last by move=> x; exact: denote_run_shim_valid.
apply: valid_package_cons; last first.
- by move=> x; apply: valid_injectMap; last exact: denote_v2_get_valid.
Qed.

(* denote_game_shim — oracle-routed image of a [game_code]: a package importing
   the IND-CPA encryption oracle [oracle_encrypt_iface t_msg t_cipher] and
   exporting [game_iface].  The [id_game_run] oracle runs [denote_run_shim]
   from the empty env with hop counter 0, routing the [site]-th [GC_enc_hop]
   through the imported oracle and inlining every other hop; the [id_v2_get]
   oracle is the fixed V_2-reveal body shared with [denote_game].  Composing
   it with the real / zero IND-CPA oracle reproduces one hybrid-ladder rung;
   the corresponding perfect-equivalence proof transfers the IND-CPA advantage
   to [denote_game]. *)
Definition denote_game_shim (gc : game_code) (site : nat) :
  package (oracle_encrypt_iface t_msg t_cipher) game_iface :=
  mkpackage protocol_state
    (mkfmap
       [:: (id_game_run, mkdef 'unit cipher_list
              (fun _ => denote_run_shim site 0 empty_denv gc))
         ; (id_v2_get,   mkdef 'unit t_msg (fun _ => denote_v2_get_body)) ])
    (denote_game_shim_valid gc site).

(* ------------------------------------------------------------------ *)
(* IND-CPA encryption oracle at this section's parameters: the two     *)
(* package forms (carry .(locs)) and their raw aliases (for the        *)
(* oracle composition in the per-hop equivalence).                     *)
(* ------------------------------------------------------------------ *)

(* oracle_real_pkg — the real-encryption IND-CPA oracle instantiated at this
   Section's AHE parameters.  The package (not raw_package) form is needed
   wherever the hybrid-ladder advantage bound's adversary-disjointness premises
   consume a located package via [.(locs)]. *)
Definition oracle_real_pkg :
  package [interface] (oracle_encrypt_iface t_msg t_cipher) :=
  oracle_encrypt_real_pkg AHE Renc card_renc renc_card rand_of_renc
                          t_msg t_cipher msg_of_chmsg chcipher_of_cipher
                          pkey_of_party.

(* oracle_zero_pkg — the zero-encryption IND-CPA oracle instantiated at this
   Section's AHE parameters.  Paired with [oracle_real_pkg] as the real-or-zero
   pair; both package forms supply [.(locs)] to the adversary-disjointness
   premises of the hybrid-ladder advantage bound. *)
Definition oracle_zero_pkg :
  package [interface] (oracle_encrypt_iface t_msg t_cipher) :=
  oracle_encrypt_zero_pkg AHE Renc card_renc renc_card rand_of_renc
                          t_msg t_cipher chcipher_of_cipher pkey_of_party.

(* oracle_real — raw-package alias of the real-encryption IND-CPA oracle, for the
   [∘] composition [denote_game_shim gc site ∘ oracle_real] that reproduces a
   real-hop rung of the hybrid ladder. *)
Definition oracle_real : raw_package :=
  oracle_encrypt_real AHE Renc card_renc renc_card rand_of_renc
                      t_msg t_cipher msg_of_chmsg chcipher_of_cipher
                      pkey_of_party.

(* oracle_zero — raw-package alias of the zero-encryption IND-CPA oracle, for the
   [∘] composition [denote_game_shim gc site ∘ oracle_zero] that reproduces a
   zero-hop rung of the hybrid ladder. *)
Definition oracle_zero : raw_package :=
  oracle_encrypt_zero AHE Renc card_renc renc_card rand_of_renc
                      t_msg t_cipher chcipher_of_cipher pkey_of_party.

(* ------------------------------------------------------------------ *)
(* Hybrid ladder: the intermediate rungs of the AdvantageE telescoping *)
(* chain whose endpoints are the real and all-zero games.              *)
(* ------------------------------------------------------------------ *)

(* hybrid_ladder — the intermediate rungs of the hybrid ladder, for use as the
   middle argument of [Advantage_triangle_chain].  Rung i is
   [denote_game (zero_hop_prefix i gc)] for i in 1 .. count_hops gc - 1; the
   endpoints [denote_game (all_real gc)] (rung 0) and [denote_game (all_zero gc)]
   (rung count_hops gc) are supplied separately as [P] and [Q], so
   [advantage_sum P (hybrid_ladder gc) Q A] telescopes into count_hops gc
   consecutive single-hop AdvantageE terms. *)
Definition hybrid_ladder (gc : game_code) : seq raw_package :=
  [seq (denote_game (zero_hop_prefix i gc) : raw_package)
     | i <- iota 1 (count_hops gc - 1)].

(* ------------------------------------------------------------------ *)
(* Per-hop perfect equivalence: each hybrid-ladder rung equals the     *)
(* oracle-routed shim composed with the matching IND-CPA oracle.       *)
(* ------------------------------------------------------------------ *)

(* Run-level witness that the directly-denoted game and the oracle-routed shim
   composed with the real-encryption oracle are perfectly equivalent at every
   site and hop.  Used by hop_equiv_real once simplify_eq_rel exposes the
   run-oracle goal; proved by structural induction on gc, collapsing the target
   hop's encode/decode round-trip via chcipher_of_cipherK and chmsg_of_msgK.
   Naming: _equiv marks an SSProve relational perfect-equivalence (≈), not an
   equation, in the *_equiv_* family of dsdp_security_indcpa.v (MathComp's _E is
   for equational rewrites and would misdescribe it). *)
Lemma denote_run_shim_real_equiv (gc : game_code) :
  forall (e : denv) (site hop : nat),
  ⊢ ⦃ λ '(s0, s1), s0 = s1 ⦄
     denote_run e gc
   ≈ code_link (denote_run_shim site hop e gc) oracle_real
   ⦃ eq ⦄.
Proof.
elim: gc => [n k IH|t k IH|t k IH|t k IH|pk secret k IH|outs] e site hop /=.
- case: (n == card_msg); last case: (n == card_renc).
  + rewrite [code_link _ _]/=. ssprove_sync_eq=> x. apply: IH.
  + rewrite [code_link _ _]/=. ssprove_sync_eq=> x. apply: IH.
  + rewrite [code_link _ _]/=. ssprove_sync_eq=> x. apply: IH.
- ssprove_sync_eq. apply: IH.
- ssprove_sync_eq. apply: IH.
- apply: IH.
- case Hhs: (hop == site).
  + rewrite [code_link _ _]/=. ssprove_code_simpl. rewrite /bind /=.
    ssprove_sync_eq=> x. rewrite chcipher_of_cipherK chmsg_of_msgK. apply: IH.
  + rewrite [code_link _ _]/=. ssprove_sync_eq=> x. apply: IH.
- apply: rreflexivity_rule.
Qed.

(* Real-side per-hop equivalence: ladder rung i equals the shim addressed at
   site i composed with the real-encryption oracle.  Left endpoint of one
   IND-CPA hop; the right endpoint is [hop_equiv_zero].  Discharged through
   [denote_run_shim_real_equiv] on the run oracle and a [V_2_cell] read on the
   reveal oracle. *)
Lemma hop_equiv_real (gc : game_code) (i : nat) :
  denote_game (zero_hop_prefix i gc) ≈₀ denote_game_shim (zero_hop_prefix i gc) i ∘ oracle_real.
Proof.
eapply eq_rel_perf_ind_eq.
simplify_eq_rel m.
- apply: rpost_weaken_rule; first by apply: denote_run_shim_real_equiv.
  by move=> [? ?] [? ?] [-> ->].
- ssprove_sync_eq=> stored.
  by case: stored => [v|]; apply: r_ret.
Qed.

(* Suffix lemma for the zero-side per-hop equivalence: once the addressed site
   has been passed (site < hop), no remaining GC_enc_hop matches, so the
   oracle-routed shim and denote_run agree on every remaining constructor
   without ever querying oracle_zero.  Closes the tail of the induction in
   denote_run_shim_zero_equiv after the target hop is consumed.
   Naming: a condition-tail helper name (post-target regime, zero side) for an
   SSProve relational equivalence with no canonical MathComp suffix; matches the
   file's descriptive *_shim_* helper convention. *)
Lemma denote_run_shim_post_target_zero (gc : game_code) :
  forall (e : denv) (site hop : nat), (site < hop)%N ->
  ⊢ ⦃ λ '(s0, s1), s0 = s1 ⦄
     code_link (denote_run_shim site hop e gc) oracle_zero
   ≈ denote_run e gc
   ⦃ eq ⦄.
Proof.
elim: gc => [n k IH|t k IH|t k IH|t k IH|pk secret k IH|outs] e site hop Hlt /=.
- case: (n == card_msg); last case: (n == card_renc).
  + rewrite [code_link _ _]/=. ssprove_sync_eq=> x. by apply: IH.
  + rewrite [code_link _ _]/=. ssprove_sync_eq=> x. by apply: IH.
  + rewrite [code_link _ _]/=. ssprove_sync_eq=> x. by apply: IH.
- ssprove_sync_eq. by apply: IH.
- ssprove_sync_eq. by apply: IH.
- by apply: IH.
- rewrite (gtn_eqF Hlt) [code_link _ _]/=.
  ssprove_sync_eq=> x. apply: IH. by rewrite ltnS ltnW.
- apply: rreflexivity_rule.
Qed.

(* Run-level half of the zero-side per-hop equivalence: the shim over
   [zero_hop_prefix p gc] composed with the zero-encryption oracle equals the
   directly-denoted run over [zero_hop_prefix p.+1 gc], the rung with one extra
   leading hop zeroed.  The site is pinned at [p + hop] so the addressed hop is
   reached exactly when the prefix is exhausted; at that hop the zero oracle
   discards its message and reproduces the [HE_const 0] encryption of the
   denoted rung, after which [denote_run_shim_post_target_zero] closes the
   suffix.  Used by [hop_equiv_zero] after [simplify_eq_rel].
   Naming: _equiv marks the SSProve relational equivalence (≈), zero-oracle side;
   pairs with denote_run_shim_real_equiv in the *_equiv_* family (MathComp's _E
   is for equations). *)
Lemma denote_run_shim_zero_equiv (gc : game_code) :
  forall (e : denv) (p hop : nat),
  ⊢ ⦃ λ '(s0, s1), s0 = s1 ⦄
     code_link (denote_run_shim (p + hop) hop e (zero_hop_prefix p gc)) oracle_zero
   ≈ denote_run e (zero_hop_prefix p.+1 gc)
   ⦃ eq ⦄.
Proof.
elim: gc => [n k IH|t k IH|t k IH|t k IH|pk secret k IH|outs] e p hop /=.
- case: (n == card_msg); last case: (n == card_renc).
  + rewrite [code_link _ _]/=. ssprove_sync_eq=> x. apply: IH.
  + rewrite [code_link _ _]/=. ssprove_sync_eq=> x. apply: IH.
  + rewrite [code_link _ _]/=. ssprove_sync_eq=> x. apply: IH.
- ssprove_sync_eq. apply: IH.
- ssprove_sync_eq. apply: IH.
- apply: IH.
- case: p => [|i'] /=.
  + rewrite add0n eqxx [code_link _ _]/=. ssprove_code_simpl. rewrite /bind /=.
    ssprove_sync_eq=> x. rewrite chcipher_of_cipherK.
    apply: denote_run_shim_post_target_zero. by rewrite ltnSn.
  + have Hne : (hop == (i'.+1 + hop)%N) = false
      by apply: ltn_eqF; rewrite -{1}[hop]add0n ltn_add2r.
    rewrite Hne [code_link _ _]/=. ssprove_sync_eq=> x. rewrite addSnnS. apply: IH.
- apply: rreflexivity_rule.
Qed.

(* Zero-side per-hop equivalence: the shim addressed at site i composed with the
   zero-encryption oracle equals ladder rung i+1, the rung with one extra
   leading hop zeroed.  Right endpoint of one IND-CPA hop; the left endpoint is
   [hop_equiv_real].  Discharged through [denote_run_shim_zero_equiv] on the run
   oracle (the [i] site is matched to the helper's [p + hop] form by [addn0])
   and a [V_2_cell] read on the reveal oracle; the message cancel [chmsg_of_msgK]
   is unused since the zero oracle discards its message. *)
Lemma hop_equiv_zero (gc : game_code) (i : nat) :
  denote_game_shim (zero_hop_prefix i gc) i ∘ oracle_zero ≈₀ denote_game (zero_hop_prefix i.+1 gc).
Proof.
eapply eq_rel_perf_ind_eq.
simplify_eq_rel m.
- rewrite -[i in denote_run_shim i]addn0.
  apply: rpost_weaken_rule; first by apply: denote_run_shim_zero_equiv.
  by move=> [? ?] [? ?] [-> ->].
- rewrite /denote_v2_get_body.
  ssprove_sync_eq=> stored.
  by case: stored => [v|]; rewrite [code_link _ _]/=; apply: r_ret.
Qed.

(* ------------------------------------------------------------------ *)
(* Single-rung IND-CPA advantage bound: adjacent hybrid-ladder rungs   *)
(* are at most epsilon_cpa apart.                                       *)
(* ------------------------------------------------------------------ *)

(* advantage_hop — one rung of the hybrid ladder costs at most epsilon_cpa: any
   adversary's SSProve advantage between ladder rungs i and i+1 is bounded by the
   IND-CPA hardness parameter.  Mirrors advantage_hop_real_h1 of
   dsdp_security_indcpa.v: Advantage_triangle_chain inserts the two oracle-routed
   shim intermediates [denote_game_shim (zero_hop_prefix i gc) i ∘ oracle_real]
   and [… ∘ oracle_zero]; hop_equiv_real and hop_equiv_zero zero the two outer
   perfect-equivalence hops; Advantage_link folds the shim into the adversary so
   the cryptographic middle hop is exactly enc_ind_cpa_real_or_zero at the
   reduction [A ∘ denote_game_shim (zero_hop_prefix i gc) i]. *)
Lemma advantage_hop
    (LA : Locations) (A : raw_package) (gc : game_code) (i : nat)
    (A_valid : ValidPackage LA game_iface A_export A)
    (A_disj_state : fseparate LA protocol_state)
    (A_disj_ore : fseparate LA oracle_real_pkg.(locs))
    (A_disj_oze : fseparate LA oracle_zero_pkg.(locs)) :
  AdvantageE (denote_game (zero_hop_prefix i gc))
             (denote_game (zero_hop_prefix i.+1 gc)) A
    <= epsilon_cpa.
Proof.
have triangle_ineq :=
  Advantage_triangle_chain (denote_game (zero_hop_prefix i gc) : raw_package)
    [:: (denote_game_shim (zero_hop_prefix i gc) i ∘ oracle_real : raw_package)
      ; (denote_game_shim (zero_hop_prefix i gc) i ∘ oracle_zero : raw_package) ]
    (denote_game (zero_hop_prefix i.+1 gc) : raw_package) A.
cbn [advantage_sum] in triangle_ineq.
rewrite ?addrA in triangle_ineq.
apply: (le_trans triangle_ineq).
clear triangle_ineq.
erewrite hop_equiv_real by ssprove_valid.
erewrite hop_equiv_zero by ssprove_valid.
rewrite GRing.add0r GRing.addr0.
rewrite -Advantage_link.
apply: (enc_ind_cpa_real_or_zero AHE Renc card_renc renc_card
          rand_of_renc t_msg t_cipher msg_of_chmsg
          chcipher_of_cipher pkey_of_party).
Qed.

(* ------------------------------------------------------------------ *)
(* Telescoping advantage bound: a contiguous block of ladder rungs     *)
(* costs at most one epsilon_cpa per rung.                             *)
(* ------------------------------------------------------------------ *)

(* advantage_sum_ladder_le — the advantage_sum over the [start+1 .. start+n]
   intermediate rungs, bracketed by rungs [start] and [start+n+1], is bounded by
   [n.+1] copies of epsilon_cpa.  This is the telescoping that turns
   Advantage_triangle_chain's fold into the per-rung IND-CPA bound.  Proved by
   induction on the rung count n: the base case is a single advantage_hop; the
   step splits advantage_sum's leading term off via advantage_hop and folds the
   tail through the induction hypothesis, the endpoint indices realigning by
   addSnnS.  Used by advantage_le.
   Naming: advantage_sum_<shape>_le names a telescoping bound on advantage_sum
   (the SSProve fold of AdvantageE terms), following the file's SSProve
   advantage-lemma convention; not a MathComp algebraic property. *)
Lemma advantage_sum_ladder_le
    (LA : Locations) (A : raw_package) (gc : game_code)
    (A_valid : ValidPackage LA game_iface A_export A)
    (A_disj_state : fseparate LA protocol_state)
    (A_disj_ore : fseparate LA oracle_real_pkg.(locs))
    (A_disj_oze : fseparate LA oracle_zero_pkg.(locs)) :
  forall (n start : nat),
  advantage_sum (denote_game (zero_hop_prefix start gc))
    [seq (denote_game (zero_hop_prefix l gc) : raw_package) | l <- iota start.+1 n]
    (denote_game (zero_hop_prefix (start + n.+1) gc)) A
    <= n.+1 %:R * epsilon_cpa.
Proof.
elim=> [|n IHn] start.
- cbn [iota map advantage_sum]. rewrite addn1 mul1r. by apply: advantage_hop.
- cbn [iota map advantage_sum]. rewrite mulrSr mulrDl mul1r addrC. apply: lerD.
  + rewrite -addSnnS. exact: IHn.
  + by apply: advantage_hop.
Qed.

(* advantage_self_zero — the SSProve advantage between a game and itself is zero
   for any adversary: the two run probabilities coincide, so their absolute
   difference vanishes.  Closes the empty-ladder ([count_hops gc = 0]) branch of
   advantage_le, where all_real and all_zero are the same game_code.
   Naming: advantage_self_<value> records the AdvantageE of a package against
   itself, in the file's SSProve advantage-lemma convention. *)
Lemma advantage_self_zero (G A : raw_package) :
  AdvantageE G G A = 0.
Proof. by rewrite /AdvantageE subrr normr0. Qed.

(* ------------------------------------------------------------------ *)
(* Full hybrid-ladder advantage bound: the real-to-all-zero distance   *)
(* is at most (number of hops) * epsilon_cpa.                          *)
(* ------------------------------------------------------------------ *)

(* advantage_le — the SSProve advantage of any adversary distinguishing the
   real game from the all-zero game is bounded by [size (hop_sites gc)] copies
   of epsilon_cpa, i.e. one IND-CPA cost per GC_enc_hop site.  Mirrors
   advantage_game_real_game_enc_zero of dsdp_security_indcpa.v generalised to an
   arbitrary game_code: Advantage_triangle_chain inserts the hybrid_ladder rungs,
   the empty ladder collapses to advantage_self_zero, and the non-empty ladder
   telescopes through advantage_sum_ladder_le into [count_hops gc] single-rung
   bounds.  size (hop_sites gc) = count_hops gc since hop_sites enumerates
   [iota 0 (count_hops gc)]. *)
Lemma advantage_le
    (LA : Locations) (A : raw_package) (gc : game_code)
    (A_valid : ValidPackage LA game_iface A_export A)
    (A_disj_state : fseparate LA protocol_state)
    (A_disj_ore : fseparate LA oracle_real_pkg.(locs))
    (A_disj_oze : fseparate LA oracle_zero_pkg.(locs)) :
  AdvantageE (denote_game (all_real gc)) (denote_game (all_zero gc)) A
    <= (size (hop_sites gc))%:R * epsilon_cpa.
Proof.
rewrite /all_real /all_zero /hop_sites size_iota.
case Hch: (count_hops gc) => [|m].
- by rewrite advantage_self_zero mul0r.
- have tri :=
    Advantage_triangle_chain (denote_game (zero_hop_prefix 0 gc) : raw_package)
      (hybrid_ladder gc)
      (denote_game (zero_hop_prefix m.+1 gc) : raw_package) A.
  apply: (le_trans tri).
  rewrite /hybrid_ladder Hch subn1 succnK.
  apply: advantage_sum_ladder_le.
  + exact: A_disj_state.
  + exact: A_disj_ore.
  + exact: A_disj_oze.
Qed.

(* ------------------------------------------------------------------ *)
(* Concrete 2-hop DSDP fixture: a back-end validation of the game-code *)
(* pipeline on the corrupted-Alice view of the 3-party DSDP protocol.  *)
(* ------------------------------------------------------------------ *)

(* gc_dsdp — a TEMPORARY FIXTURE game_code standing in for the output the
   future symbolic-to-game front end will emit for the DSDP corrupted-Alice
   view.  It is NOT a hand-written SSProve game: the actual game is the derived
   [denote_game (all_real gc_dsdp)] (whose body mirrors [game_real] of
   dsdp_security_indcpa.v).  This fixture exists only to exercise the back end
   (denote_run / count_hops / hop_sites / all_real / all_zero / advantage_le)
   end-to-end on a concrete two-encryption-hop instance, until the symbolic
   front end is in place to produce such game_code automatically.

   Structure (de Bruijn indices into the de_val / de_rand stacks, index 0 = most
   recent push; computed against the push convention of [denote_run]):
   - 6 [GC_sample card_msg] draw the protocol scalars iV2, iV3, iU2, iR2, iU3,
     iR3 onto the value stack (this is the first-appearance structural order the
     derived corrupted-Alice trace emits: v2, v3, then per hop its u-then-r pair,
     so iU2/iR2 precede iU3/iR3);
   - 2 [GC_sample card_renc] draw the two MASK randomnesses ra1, ra2 onto the
     randomness stack (the hop randomnesses rb1/rc1 are sampled INLINE at the
     [GC_enc_hop] sites by [denote_run], per the T8 inline-hop convention, so
     they are NOT pre-sampled here);
   - [GC_put (HE_var 5)] writes V_2 (iV2, at value index 5) into [V_2_cell];
   - [GC_enc_hop 1 (HE_var 5)] = c2 = Enc(pk_Bob, v2, inline) (Bob = party id 1);
   - [GC_enc_hop 2 (HE_var 5)] = c3 = Enc(pk_Charlie, v3, inline) (Charlie = 2);
   - [GC_let (HE_emul (HE_epow c2 iU2) (HE_enc 1 iR2 ra1))] = a1;
   - [GC_let (HE_emul (HE_epow c3 iU3) (HE_enc 2 iR3 ra2))] = a2;
   - [GC_ret [a1; a2; c2; c3]] leaks the four Alice-visible ciphertext slots.
   Its two [GC_enc_hop] nodes give [count_hops gc_dsdp = 2], the validation
   target of [hop_sites_gc_dsdp]. *)
Definition gc_dsdp : game_code :=
  (* iV2 iV3 iU2 iR2 iU3 iR3 *)
  GC_sample card_msg (GC_sample card_msg (GC_sample card_msg
  (GC_sample card_msg (GC_sample card_msg (GC_sample card_msg
  (* ra1 ra2 (mask randomness) *)
  (GC_sample card_renc (GC_sample card_renc
  (* write V_2 = iV2 (value index 5) into V_2_cell *)
  (GC_put (HE_var 5)
  (* c2 = Enc(pk_Bob, v2 = iV2@5, inline rand) ; pushes c2 at index 0 *)
  (GC_enc_hop 1 (HE_var 5)
  (* c3 = Enc(pk_Charlie, v3 = iV3@5, inline rand) ; pushes c3 at index 0 *)
  (GC_enc_hop 2 (HE_var 5)
  (* a1 = Emul (Epow c2@1 iU2@5) (Enc 1 iR2@4 ra1@rand1) ; pushes a1 at index 0 *)
  (GC_let (HE_emul (HE_epow (HE_var 1) (HE_var 5)) (HE_enc 1 (HE_var 4) 1))
  (* a2 = Emul (Epow c3@1 iU3@4) (Enc 2 iR3@3 ra2@rand0) ; pushes a2 at index 0 *)
  (GC_let (HE_emul (HE_epow (HE_var 1) (HE_var 4)) (HE_enc 2 (HE_var 3) 0))
  (* leak [a1@1; a2@0; c2@3; c3@2] *)
  (GC_ret [:: HE_var 1 ; HE_var 0 ; HE_var 3 ; HE_var 2 ])
  )))))))))))).

(* hop_sites_gc_dsdp — back-end validation: the fixture has exactly two
   encryption hops (the Bob-to-Alice c2 and Charlie-to-Alice c3 slots), so its
   hybrid ladder enumerates two addressable sites.  Computational ([reflexivity]
   through [size_iota] / [count_hops]); pins the [2] in [advantage_gc_dsdp]. *)
Lemma hop_sites_gc_dsdp : size (hop_sites gc_dsdp) = 2.
Proof. by []. Qed.

(* advantage_gc_dsdp — headline back-end validation: any adversary's SSProve
   advantage distinguishing the real DSDP corrupted-Alice game (derived from the
   fixture) from its all-zero endpoint is at most [2 * epsilon_cpa], one IND-CPA
   cost per encryption hop.  Specialises the generic [advantage_le] to [gc_dsdp]
   and rewrites [size (hop_sites gc_dsdp)] to [2] via [hop_sites_gc_dsdp]; the
   four premises are exactly [advantage_le]'s adversary well-formedness and
   state-disjointness hypotheses. *)
Lemma advantage_gc_dsdp
    (LA : Locations) (A : raw_package)
    (A_valid : ValidPackage LA game_iface A_export A)
    (A_disj_state : fseparate LA protocol_state)
    (A_disj_ore : fseparate LA oracle_real_pkg.(locs))
    (A_disj_oze : fseparate LA oracle_zero_pkg.(locs)) :
  AdvantageE (denote_game (all_real gc_dsdp)) (denote_game (all_zero gc_dsdp)) A
    <= 2%:R * epsilon_cpa.
Proof.
have H := advantage_le gc_dsdp A_valid A_disj_state A_disj_ore A_disj_oze.
rewrite hop_sites_gc_dsdp in H.
exact: H.
Qed.

End dsdp_game_code.
