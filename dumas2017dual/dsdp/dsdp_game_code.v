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

(* Forward scaffolding (unused until the hop tasks): cipher_of_chcipher brings
   an oracle-returned ciphertext back to [cipher AHE] in denote_game_shim, and
   the two cancel laws collapse the encode/decode round-trips in the later
   hop-equivalence proofs, mirroring the *_equiv_* lemmas of
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
   V_2 cell; [GC_let] pushes a denoted value; [GC_enc_hop] pushes the denoted
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
  | GC_let t k =>
      denote_run (push_val (denote_he e t) e) k
  | GC_enc_hop pk secret rnd k =>
      denote_run
        (push_val
           (Gcipher (enc (pkey_of_party (nat_to_party_id pk))
                         (as_plain (denote_he e secret)) (de_rand_nth e rnd)))
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
elim: gc e => [n k IH|t k IH|t k IH|pk secret rnd k IH|outs] e /=.
- case: (n == card_msg); last case: (n == card_renc).
  + by apply: valid_sampler => x; exact: IH.
  + by apply: valid_sampler => x; exact: IH.
  + by apply: valid_sampler => x; exact: IH.
- by apply: valid_putr; last exact: IH.
- exact: IH.
- exact: IH.
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
  | GC_let t k =>
      denote_run_shim site hop (push_val (denote_he e t) e) k
  | GC_enc_hop pk secret rnd k =>
      if hop == site then
        #import {sig #[ id_oracle_encrypt ] : 'nat × msg → cipher_t }
          as oracle_enc ;;
        ch ← oracle_enc
               (pk, chmsg_of_msg (as_plain (denote_he e secret))) ;;
        denote_run_shim site hop.+1
          (push_val (Gcipher (cipher_of_chcipher ch)) e) k
      else
        denote_run_shim site hop.+1
          (push_val
             (Gcipher (enc (pkey_of_party (nat_to_party_id pk))
                           (as_plain (denote_he e secret)) (de_rand_nth e rnd)))
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
elim: gc site hop e => [n k IH|t k IH|t k IH|pk secret rnd k IH|outs] site hop e /=.
- case: (n == card_msg); last case: (n == card_renc).
  + by apply: valid_sampler => x; exact: IH.
  + by apply: valid_sampler => x; exact: IH.
  + by apply: valid_sampler => x; exact: IH.
- by apply: valid_putr; last exact: IH.
- exact: IH.
- case: (hop == site).
  + by apply: valid_opr; last by move=> v; exact: IH.
  + exact: IH.
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

End dsdp_game_code.
