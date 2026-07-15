(* SCRATCH ELABORATION HARNESS — do NOT Require Import this from anywhere.
   /rocq:draft --mode=skeleton for the symbolic-to-game derivation back end
   (design doc: dumas2017dual/notes/20260604-symbolic-to-game-derivation-design.md).

   Goal: every declaration elaborates against installed SSProve + project.
   Real proofs are deliberately NOT here: lemmas are Admitted, signatures are
   Parameter. Mirrors the import header + Section param block of
   dumas2017dual/dsdp/ref/dsdp_security_indcpa.v so that game_iface, cipher_list,
   t_msg, t_cipher, AHE, pkey_of_party, card_msg, msg_of_idx, ... are in scope. *)

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

(* ================================================================== *)
(* INDUCTIVES (concrete; must elaborate)                              *)
(* ================================================================== *)

(* he_term — single-sort deep embedding of the HE message algebra.
   Plain/Cipher sort-indexing is deliberately deferred (§9.4): keep it
   untyped. nat args are de Bruijn-style variable / const / pubkey-id /
   rand-slot indices. *)
Inductive he_term : Type :=
| HE_var   (_ : nat)
| HE_const (_ : nat)
| HE_enc   (_ : nat) (_ : he_term) (_ : nat)
| HE_dec   (_ : nat) (_ : he_term)
| HE_emul  (_ _ : he_term)
| HE_epow  (_ _ : he_term)
| HE_add   (_ _ : he_term)
| HE_sub   (_ _ : he_term)
| HE_mul   (_ _ : he_term).

(* game_code — statement list reifying the id_game_run body.
   nat args are de Bruijn-style pool indices / pubkey ids / rand slots. *)
Inductive game_code : Type :=
| GC_sample  (_ : nat) (_ : game_code)
| GC_put     (_ : he_term) (_ : game_code)
| GC_let     (_ : he_term) (_ : game_code)
| GC_enc_hop (_ : nat) (_ : he_term) (_ : nat) (_ : game_code)
| GC_ret     (_ : seq he_term).

Section symbolic_game_derivation.

(* ------------------------------------------------------------------ *)
(* Section parameters mirrored from dsdp_security_indcpa.v lines ~101-217 *)
(* ------------------------------------------------------------------ *)

Variable AHE : AHEncType.

Variable Renc : finType.
Variable card_renc : nat.
Hypothesis renc_card : #|Renc| = card_renc.

Definition sample_to_renc (i : 'I_card_renc) : Renc :=
  enum_val (cast_ord (esym renc_card) i).

Variable rand_of_renc : Renc -> rand AHE.

Variable t_msg : choice_type.
Variable t_cipher : choice_type.
Variable msg_of_chmsg : t_msg -> plain AHE.
Variable chmsg_of_msg : plain AHE -> t_msg.
Variable chcipher_of_cipher : cipher AHE -> t_cipher.
Variable cipher_of_chcipher : t_cipher -> cipher AHE.
Hypothesis chcipher_of_cipherK : cancel chcipher_of_cipher cipher_of_chcipher.
Hypothesis chmsg_of_msgK : cancel chmsg_of_msg msg_of_chmsg.

Variable pkey_of_party : party_id -> pub_key AHE.

Variable card_msg : nat.
Variable msg_of_idx : 'I_card_msg -> plain AHE.

Local Notation "'cipher_t'" := t_cipher (in custom pack_type at level 2).

Definition cipher_list : choice_type := chList t_cipher.

Local Notation "'ciphers'" := cipher_list (in custom pack_type at level 2).

Definition id_game_run : nat := 0%N.
Definition id_v2_get : nat := 2%N.

Definition V_2_cell : Location := mkloc 8 (None : option t_msg).
Definition protocol_state : Locations := [fmap V_2_cell].

Local Notation "'msg'" := t_msg (in custom pack_type at level 2).

Definition game_iface : Interface :=
  [interface
     #val #[ id_game_run ] : 'unit → ciphers ;
     #val #[ id_v2_get   ] : 'unit → msg ].

(* ================================================================== *)
(* SIGNATURES (Parameter — skeleton stubs; types per design doc §4-§7) *)
(* ================================================================== *)

(* hop_sites — the list of GC_enc_hop positions in a game_code (§5). *)
Parameter hop_sites : game_code -> seq nat.

(* all_real / all_zero — interpret every GC_enc_hop as a real / zero
   encryption respectively (§5). *)
Parameter all_real : game_code -> game_code.
Parameter all_zero : game_code -> game_code.

(* denote_game — denotation into an SSProve package exporting game_iface
   with no imports.  The fixed id_v2_get oracle and protocol_state are
   added by the wrapper (§6). *)
Parameter denote_game : game_code -> package [interface] game_iface.

(* denote_game_shim — route the chosen hop site through the IND-CPA
   real-or-zero encryption oracle; mirrors game_via_oracle_charlie/bob
   (§6).  Imports oracle_encrypt_iface, exports game_iface. *)
Parameter denote_game_shim :
  game_code -> nat -> package (oracle_encrypt_iface t_msg t_cipher) game_iface.

(* hybrid_ladder — the chain of raw_packages over the k hop sites (§7). *)
Parameter hybrid_ladder : game_code -> seq raw_package.

(* ------------------------------------------------------------------ *)
(* Local aliases of the IND-CPA oracles at this section's parameters,
   mirroring oracle_real / oracle_zero in dsdp_security_indcpa.v (~787). *)
(* ------------------------------------------------------------------ *)

Definition oracle_real : raw_package :=
  oracle_encrypt_real AHE Renc card_renc renc_card rand_of_renc
                      t_msg t_cipher msg_of_chmsg chcipher_of_cipher
                      pkey_of_party.

Definition oracle_zero : raw_package :=
  oracle_encrypt_zero AHE Renc card_renc renc_card rand_of_renc
                      t_msg t_cipher chcipher_of_cipher pkey_of_party.

(* Package-level oracle aliases, used for the .(locs) disjointness premises
   (the raw_package aliases above have no locs projection; mirror the
   advantage_game_real_game_enc_zero premise block at ~1376). *)
Definition oracle_real_pkg : package [interface] (oracle_encrypt_iface t_msg t_cipher) :=
  oracle_encrypt_real_pkg AHE Renc card_renc renc_card rand_of_renc
                          t_msg t_cipher msg_of_chmsg chcipher_of_cipher
                          pkey_of_party.

Definition oracle_zero_pkg : package [interface] (oracle_encrypt_iface t_msg t_cipher) :=
  oracle_encrypt_zero_pkg AHE Renc card_renc renc_card rand_of_renc
                          t_msg t_cipher chcipher_of_cipher pkey_of_party.

(* ================================================================== *)
(* LEMMAS (Admitted — stated only, NOT proved)                        *)
(* ================================================================== *)

(* denote_game_valid — package validity of a generated game, parametric
   over gc (§6, named risk §9.2).  Mirrors the ValidPackage shape used
   in dsdp_security_indcpa.v (Locations -> import iface -> export iface
   -> raw_package). *)
Lemma denote_game_valid (gc : game_code) :
  ValidPackage protocol_state [interface] game_iface (denote_game gc).
Proof. Admitted.

(* hop_equiv — the single generic per-hop perfect equivalence (§7,
   highest risk §9.1).  Mirrors game_real_equiv_charlie_real (~833):
   the inlined game at one real hop site is ≈₀ the shim composed with
   the real encryption oracle. *)
Lemma hop_equiv (gc : game_code) (site : nat) :
  denote_game gc ≈₀ denote_game_shim gc site ∘ oracle_real.
Proof. Admitted.

(* advantage_le — generic hybrid-ladder advantage bound (§7).  Mirrors
   the validity + disjointness premise block of
   advantage_game_real_game_enc_zero (~1360).  Bound:
   AdvantageE (real) (all-zero) A ≤ (size (hop_sites gc))%:R * epsilon_cpa. *)
Lemma advantage_le
    (LA : Locations) (A : raw_package) (gc : game_code)
    (A_valid : ValidPackage LA game_iface A_export A)
    (A_disj_real : fseparate LA (denote_game (all_real gc)).(locs))
    (A_disj_zero : fseparate LA (denote_game (all_zero gc)).(locs))
    (A_disj_oracle_real : fseparate LA oracle_real_pkg.(locs))
    (A_disj_oracle_zero : fseparate LA oracle_zero_pkg.(locs)) :
  AdvantageE (denote_game (all_real gc)) (denote_game (all_zero gc)) A
    <= (size (hop_sites gc))%:R * epsilon_cpa.
Proof. Admitted.

(* ================================================================== *)
(* VALIDATION (§8): hand-built DSDP body gc_dsdp + 2-epsilon instance  *)
(* ================================================================== *)

(* gc_dsdp — the two-hop DSDP body matching dsdp_security_indcpa.v's
   game_real (line ~325).  Canonical sample order (§5): the six protocol
   scalars V2/V3/U2/U3/R2/R3 then the four randomness slots
   ra1/ra2/rb1/rc1.  De Bruijn variable indices:
     0=V2 1=V3 2=U2 3=U3 4=R2 5=R3 | 6=ra1 7=ra2 8=rb1 9=rc1 | 10=c2 11=c3
   pubkey ids: 1=Bob 2=Charlie (party_id_to_nat).
   - GC_put (HE_var 0): write the V_2 secret into V_2_cell.
   - GC_enc_hop Bob   c2 = Enc(pk_b, V2, rb1)   (rand slot 8)
   - GC_enc_hop Charlie c3 = Enc(pk_c, V3, rc1) (rand slot 9)
   - GC_let a1 = Emul (Epow c2 U2) (enc pk_b R2 ra1)
   - GC_let a2 = Emul (Epow c3 U3) (enc pk_c R3 ra2)
   - GC_ret [a1; a2; c2; c3]. *)
Definition gc_dsdp : game_code :=
  GC_sample card_msg  (* iV2  -> var 0 *)
 (GC_sample card_msg  (* iV3  -> var 1 *)
 (GC_sample card_msg  (* iU2  -> var 2 *)
 (GC_sample card_msg  (* iU3  -> var 3 *)
 (GC_sample card_msg  (* iR2  -> var 4 *)
 (GC_sample card_msg  (* iR3  -> var 5 *)
 (GC_sample card_renc (* ira1 -> var 6 *)
 (GC_sample card_renc (* ira2 -> var 7 *)
 (GC_sample card_renc (* irb1 -> var 8 *)
 (GC_sample card_renc (* irc1 -> var 9 *)
 (GC_put (HE_var 0)   (* #put V_2_cell := Some V2 *)
 (GC_enc_hop 1 (HE_var 0) 8  (* c2 = Enc(pk_b, V2, rb1) -> var 10 *)
 (GC_enc_hop 2 (HE_var 1) 9  (* c3 = Enc(pk_c, V3, rc1) -> var 11 *)
 (GC_let
    (HE_emul (HE_epow (HE_var 10) (HE_var 2))
             (HE_enc 1 (HE_var 4) 6))   (* a1 *)
 (GC_let
    (HE_emul (HE_epow (HE_var 11) (HE_var 3))
             (HE_enc 2 (HE_var 5) 7))   (* a2 *)
 (GC_ret [:: HE_var 12   (* a1 *)
           ; HE_var 13   (* a2 *)
           ; HE_var 10   (* c2 *)
           ; HE_var 11   (* c3 *) ]))))))))))))))).

(* hop_sites gc_dsdp has length 2 (Bob's c2, Charlie's c3); advantage_le
   then yields 2 * epsilon_cpa, reproducing
   advantage_game_real_game_enc_zero (~1386).  Stated and Admitted:
   derivation from advantage_le is deferred. *)
Lemma advantage_gc_dsdp
    (LA : Locations) (A : raw_package)
    (A_valid : ValidPackage LA game_iface A_export A)
    (A_disj_real : fseparate LA (denote_game (all_real gc_dsdp)).(locs))
    (A_disj_zero : fseparate LA (denote_game (all_zero gc_dsdp)).(locs))
    (A_disj_oracle_real : fseparate LA oracle_real_pkg.(locs))
    (A_disj_oracle_zero : fseparate LA oracle_zero_pkg.(locs)) :
  AdvantageE (denote_game (all_real gc_dsdp)) (denote_game (all_zero gc_dsdp)) A
    <= 2%:R * epsilon_cpa.
Proof. Admitted.

End symbolic_game_derivation.
