(* DSDP Alice secrecy under IND-CPA.

   Hybrid (computational + information-theoretic) closed-form bound

       Pr[A(AliceView) = V_2] <= 1 / m + 2 * epsilon_cpa

   for the 3-party DSDP protocol against static semi-honest corrupted Alice.
   Two real-or-zero IND-CPA ciphertext swaps plus an information-theoretic
   residual-uniformity step.
*)
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

Notation R := SSProve.Crypt.Axioms.R.

Notation adversary := (package _ _ _).

(* A package in SSProve is a finite map: operation_name ↦ body.
   The number of bodies equals the number of operations the package's
   export interface declares.

  - game_real exports game_iface, which has two entries
      (id_game_run, id_v2_get). So game_real has two bodies.
  - guessing_challenger exports A_export, which has one entry (0%N : 'unit → 'bool).
      So the adversary guessing_challenger ∘ pred has one body:
      the bool-returning entrypoint.

  And in our work we need a composed (linked) adversary by guessing_challenger ∘ pred.
  where `guessing_challenger` converts a guess from `pred` into a boolean,
  and `pred` expects one game-run to produce that guess (linked later);
  linking the two yields a boolean distinguisher, and the lemma is used
  to verify that the linkage is valid.
*)
Lemma valid_code_link_residual :
  forall (A : choice_type) (L : Locations) (Im Ir E : Interface)
    (v : raw_code A) (p : raw_package),
    ValidCode L Im v ->
    ValidPackage L Ir E p ->
    ValidCode L Ir (code_link v p).
Proof.
move=> A L Im Ir E v p hv hp.
elim: hv => //=.
(* doing batch processing of heterogeneous goals *)
all: try by [move=> *; constructor; auto].
(* Or we do this:
  all: first
    [ by move=> ?;        apply: valid_ret
    | by move=> ? ? _ ?;  apply: valid_getr
    | by move=> ? ? ? _ ?; apply: valid_putr
    | by move=> ? ? ?;    apply: valid_sampler
    | idtac (* opr falls through *) ].
*)
move=> o x k _ _ IH.
apply: valid_bind.
rewrite /resolve.
case Eo: (p o.1) => [[S [T g]] | ].
- have body_valid : forall y, ValidCode L Ir (g y).
  { by case: hp => _ hi y; exact: (hi o.1 (existT _ S (existT _ T g)) y Eo). }
  rewrite /coerce_kleisli -lock /coerce_code.
  case: (coerce x) => [s | ] /=.
  + apply: valid_bind.
    move=> a /=.
    by case: (coerce a) => [r' | ];
      [constructor | apply: valid_sampler => ?; constructor].
  + apply: valid_sampler => r.
    apply: valid_bind.
    move=> a /=.
    by case: (coerce a) => [r' | ];
      [constructor | apply: valid_sampler => ?; constructor].
- by apply: valid_sampler => ?; constructor.
Qed.

Section dsdp_security_indcpa.

Variable AHE : AHEncType.

Variable Renc : finType.

(* renc: randomness for encryption *)
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

(* Proof is in dsdp_security_indcpa_concrete.v when realizing instances of
   different AHE schemes.
*)
Hypothesis chcipher_of_cipherK :
  cancel chcipher_of_cipher cipher_of_chcipher.

Hypothesis chmsg_of_msgK :
  cancel chmsg_of_msg msg_of_chmsg.

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

(* game_iface is an SSProve Interface — a finite set of entries,
   each entry being (operation_id, input_type → output_type)
*)
Definition game_iface : Interface :=
  [interface
     #val #[ id_game_run ] : 'unit → ciphers ;
     #val #[ id_v2_get   ] : 'unit → msg ].

Definition game_real :
  package [interface] game_iface :=
  [package protocol_state ;
    #def #[ id_game_run ] (_ : 'unit) : ciphers
    {

      iV2 ← sample uniform card_msg ;;
      iV3 ← sample uniform card_msg ;;
      iU2 ← sample uniform card_msg ;;
      iU3 ← sample uniform card_msg ;;
      iR2 ← sample uniform card_msg ;;
      iR3 ← sample uniform card_msg ;;

      ira1 ← sample uniform card_renc ;;
      ira2 ← sample uniform card_renc ;;
      irb1 ← sample uniform card_renc ;;
      irc1 ← sample uniform card_renc ;;
      let v2 := msg_of_idx iV2 in
      #put V_2_cell := Some (chmsg_of_msg v2) ;;
      let v3 := msg_of_idx iV3 in
      let u2 := msg_of_idx iU2 in
      let u3 := msg_of_idx iU3 in
      let r2 := msg_of_idx iR2 in
      let r3 := msg_of_idx iR3 in
      let ra1 := rand_of_renc (sample_to_renc ira1) in
      let ra2 := rand_of_renc (sample_to_renc ira2) in
      let rb1 := rand_of_renc (sample_to_renc irb1) in
      let rc1 := rand_of_renc (sample_to_renc irc1) in
      let pk_b := pkey_of_party Bob in
      let pk_c := pkey_of_party Charlie in
      let c2 := enc pk_b v2 rb1 in
      let c3 := enc pk_c v3 rc1 in
      let a1 := Emul (Epow c2 u2) (enc pk_b r2 ra1) in
      let a2 := Emul (Epow c3 u3) (enc pk_c r3 ra2) in
      ret ([:: chcipher_of_cipher a1
             ; chcipher_of_cipher a2
             ; chcipher_of_cipher c2
             ; chcipher_of_cipher c3 ] : cipher_list)
    } ;
    #def #[ id_v2_get ] (_ : 'unit) : msg
    {
      stored ← get V_2_cell ;;
      match stored with
      | Some v => @ret t_msg v
      | None   => @ret t_msg (chmsg_of_msg (0%R : plain AHE))
      end
    }
  ].

Definition game_hybrid_one :
  package [interface] game_iface :=
  [package protocol_state ;
    #def #[ id_game_run ] (_ : 'unit) : ciphers
    {
      iV2 ← sample uniform card_msg ;;
      iV3 ← sample uniform card_msg ;;
      iU2 ← sample uniform card_msg ;;
      iU3 ← sample uniform card_msg ;;
      iR2 ← sample uniform card_msg ;;
      iR3 ← sample uniform card_msg ;;
      ira1 ← sample uniform card_renc ;;
      ira2 ← sample uniform card_renc ;;
      irb1 ← sample uniform card_renc ;;
      irc1 ← sample uniform card_renc ;;
      let v2 := msg_of_idx iV2 in
      #put V_2_cell := Some (chmsg_of_msg v2) ;;
      let _v3 := msg_of_idx iV3 in
      let u2 := msg_of_idx iU2 in
      let u3 := msg_of_idx iU3 in
      let r2 := msg_of_idx iR2 in
      let r3 := msg_of_idx iR3 in
      let ra1 := rand_of_renc (sample_to_renc ira1) in
      let ra2 := rand_of_renc (sample_to_renc ira2) in
      let rb1 := rand_of_renc (sample_to_renc irb1) in
      let rc1 := rand_of_renc (sample_to_renc irc1) in
      let pk_b := pkey_of_party Bob in
      let pk_c := pkey_of_party Charlie in
      let c2 := enc pk_b v2 rb1 in

      (* c3 is replaced by enc 0. *)
      let c3 := enc pk_c (0 : plain AHE) rc1 in
      let a1 := Emul (Epow c2 u2) (enc pk_b r2 ra1) in
      let a2 := Emul (Epow c3 u3) (enc pk_c r3 ra2) in
      ret ([:: chcipher_of_cipher a1
             ; chcipher_of_cipher a2
             ; chcipher_of_cipher c2
             ; chcipher_of_cipher c3 ] : cipher_list)
    } ;
    #def #[ id_v2_get ] (_ : 'unit) : msg
    {
      stored ← get V_2_cell ;;
      match stored with
      | Some v => @ret t_msg v
      | None   => @ret t_msg (chmsg_of_msg (0%R : plain AHE))
      end
    }
  ].

Definition game_hybrid_two :
  package [interface] game_iface :=
  [package protocol_state ;
    #def #[ id_game_run ] (_ : 'unit) : ciphers
    {
      iV2 ← sample uniform card_msg ;;
      iV3 ← sample uniform card_msg ;;
      iU2 ← sample uniform card_msg ;;
      iU3 ← sample uniform card_msg ;;
      iR2 ← sample uniform card_msg ;;
      iR3 ← sample uniform card_msg ;;
      ira1 ← sample uniform card_renc ;;
      ira2 ← sample uniform card_renc ;;
      irb1 ← sample uniform card_renc ;;
      irc1 ← sample uniform card_renc ;;
      let v2 := msg_of_idx iV2 in
      #put V_2_cell := Some (chmsg_of_msg v2) ;;
      let _v3 := msg_of_idx iV3 in
      let u2 := msg_of_idx iU2 in
      let u3 := msg_of_idx iU3 in
      let r2 := msg_of_idx iR2 in
      let r3 := msg_of_idx iR3 in
      let ra1 := rand_of_renc (sample_to_renc ira1) in
      let ra2 := rand_of_renc (sample_to_renc ira2) in
      let rb1 := rand_of_renc (sample_to_renc irb1) in
      let rc1 := rand_of_renc (sample_to_renc irc1) in
      let pk_b := pkey_of_party Bob in
      let pk_c := pkey_of_party Charlie in

      (* c2 and c3 are replaced by enc 0. *)
      let c2 := enc pk_b (0 : plain AHE) rb1 in
      let c3 := enc pk_c (0 : plain AHE) rc1 in
      let a1 := Emul (Epow c2 u2) (enc pk_b r2 ra1) in
      let a2 := Emul (Epow c3 u3) (enc pk_c r3 ra2) in
      ret ([:: chcipher_of_cipher a1
             ; chcipher_of_cipher a2
             ; chcipher_of_cipher c2
             ; chcipher_of_cipher c3 ] : cipher_list)
    } ;
    #def #[ id_v2_get ] (_ : 'unit) : msg
    {
      stored ← get V_2_cell ;;
      match stored with
      | Some v => @ret t_msg v
      | None   => @ret t_msg (chmsg_of_msg (0%R : plain AHE))
      end
    }
  ].

(* Both IND-CPA swaps applied: c2, c3 encrypt 0 rather than the protocol
  shares; the distinct name marks the
  transition from the cryptographic chain to the IT analysis, since
  `game_enc_zero` is the input to the information-theoretic step.
  It is the game over which the residual analysis
  (Pr_guess_enc_zero_le_invm, the IT uniformity argument, the 1/m bound)
  operates. Every lemma in the IT half of the proof starts from this name.
*)
Definition game_enc_zero :
  package [interface] game_iface :=
  [package protocol_state ;
    #def #[ id_game_run ] (_ : 'unit) : ciphers
    {
      iV2 ← sample uniform card_msg ;;
      iV3 ← sample uniform card_msg ;;
      iU2 ← sample uniform card_msg ;;
      iU3 ← sample uniform card_msg ;;
      iR2 ← sample uniform card_msg ;;
      iR3 ← sample uniform card_msg ;;
      ira1 ← sample uniform card_renc ;;
      ira2 ← sample uniform card_renc ;;
      irb1 ← sample uniform card_renc ;;
      irc1 ← sample uniform card_renc ;;
      let v2 := msg_of_idx iV2 in
      #put V_2_cell := Some (chmsg_of_msg v2) ;;
      let _v3 := msg_of_idx iV3 in
      let u2 := msg_of_idx iU2 in
      let u3 := msg_of_idx iU3 in
      let r2 := msg_of_idx iR2 in
      let r3 := msg_of_idx iR3 in
      let ra1 := rand_of_renc (sample_to_renc ira1) in
      let ra2 := rand_of_renc (sample_to_renc ira2) in
      let rb1 := rand_of_renc (sample_to_renc irb1) in
      let rc1 := rand_of_renc (sample_to_renc irc1) in
      let pk_b := pkey_of_party Bob in
      let pk_c := pkey_of_party Charlie in
      let c2 := enc pk_b (0 : plain AHE) rb1 in
      let c3 := enc pk_c (0 : plain AHE) rc1 in
      let a1 := Emul (Epow c2 u2) (enc pk_b r2 ra1) in
      let a2 := Emul (Epow c3 u3) (enc pk_c r3 ra2) in
      ret ([:: chcipher_of_cipher a1
             ; chcipher_of_cipher a2
             ; chcipher_of_cipher c2
             ; chcipher_of_cipher c3 ] : cipher_list)
    } ;
    #def #[ id_v2_get ] (_ : 'unit) : msg
    {
      stored ← get V_2_cell ;;
      match stored with
      | Some v => @ret t_msg v
      | None   => @ret t_msg (chmsg_of_msg (0%R : plain AHE))
      end
    }
  ].

Check game_real.
Check game_hybrid_one.
Check game_hybrid_two.
Check game_enc_zero.

(* Re-implement party programs in SSProve game.

  "Via oracle" means the encryption is delegated through a named interface to
  an external implementation, rather than computed inline.
  SSProve has no special "oracle" type — an oracle is just a package whose role
  in the proof is to be queried as a black box.
*)
Definition game_via_oracle_charlie :
  package
    (oracle_encrypt_iface t_msg t_cipher)
    game_iface :=
  [package protocol_state ;
    #def #[ id_game_run ] (_ : 'unit) : ciphers
    {
      #import {sig #[ id_oracle_encrypt ] : 'nat × msg → cipher_t } as oracle_enc ;;
      iV2 ← sample uniform card_msg ;;
      iV3 ← sample uniform card_msg ;;
      iU2 ← sample uniform card_msg ;;
      iU3 ← sample uniform card_msg ;;
      iR2 ← sample uniform card_msg ;;
      iR3 ← sample uniform card_msg ;;
      ira1 ← sample uniform card_renc ;;
      ira2 ← sample uniform card_renc ;;
      irb1 ← sample uniform card_renc ;;
      let v2 := msg_of_idx iV2 in
      #put V_2_cell := Some (chmsg_of_msg v2) ;;
      let v3 := msg_of_idx iV3 in
      let u2 := msg_of_idx iU2 in
      let u3 := msg_of_idx iU3 in
      let r2 := msg_of_idx iR2 in
      let r3 := msg_of_idx iR3 in
      let ra1 := rand_of_renc (sample_to_renc ira1) in
      let ra2 := rand_of_renc (sample_to_renc ira2) in
      let rb1 := rand_of_renc (sample_to_renc irb1) in
      let pk_b := pkey_of_party Bob in
      let pk_c := pkey_of_party Charlie in
      let c2 := enc pk_b v2 rb1 in
      ch3 ← oracle_enc (party_id_to_nat Charlie, chmsg_of_msg v3) ;;
      let c3 := cipher_of_chcipher ch3 in
      let a1 := Emul (Epow c2 u2) (enc pk_b r2 ra1) in
      let a2 := Emul (Epow c3 u3) (enc pk_c r3 ra2) in
      ret ([:: chcipher_of_cipher a1
             ; chcipher_of_cipher a2
             ; chcipher_of_cipher c2
             ; ch3 ] : cipher_list)
    } ;
    #def #[ id_v2_get ] (_ : 'unit) : msg
    {
      stored ← get V_2_cell ;;
      match stored with
      | Some v => @ret t_msg v
      | None   => @ret t_msg (chmsg_of_msg (0%R : plain AHE))
      end
    }
  ].

Definition game_via_oracle_bob :
  package
    (oracle_encrypt_iface t_msg t_cipher)
    game_iface :=
  [package protocol_state ;
    #def #[ id_game_run ] (_ : 'unit) : ciphers
    {
      #import {sig #[ id_oracle_encrypt ] : 'nat × msg → cipher_t } as oracle_enc ;;
      iV2 ← sample uniform card_msg ;;
      iV3 ← sample uniform card_msg ;;
      iU2 ← sample uniform card_msg ;;
      iU3 ← sample uniform card_msg ;;
      iR2 ← sample uniform card_msg ;;
      iR3 ← sample uniform card_msg ;;
      ira1 ← sample uniform card_renc ;;
      ira2 ← sample uniform card_renc ;;
      irc1 ← sample uniform card_renc ;;
      let v2 := msg_of_idx iV2 in
      #put V_2_cell := Some (chmsg_of_msg v2) ;;
      let _v3 := msg_of_idx iV3 in
      let u2 := msg_of_idx iU2 in
      let u3 := msg_of_idx iU3 in
      let r2 := msg_of_idx iR2 in
      let r3 := msg_of_idx iR3 in
      let ra1 := rand_of_renc (sample_to_renc ira1) in
      let ra2 := rand_of_renc (sample_to_renc ira2) in
      let rc1 := rand_of_renc (sample_to_renc irc1) in
      let pk_b := pkey_of_party Bob in
      let pk_c := pkey_of_party Charlie in
      ch2 ← oracle_enc (party_id_to_nat Bob, chmsg_of_msg v2) ;;
      let c2 := cipher_of_chcipher ch2 in
      let c3 := enc pk_c (0%R : plain AHE) rc1 in
      let a1 := Emul (Epow c2 u2) (enc pk_b r2 ra1) in
      let a2 := Emul (Epow c3 u3) (enc pk_c r3 ra2) in
      ret ([:: chcipher_of_cipher a1
             ; chcipher_of_cipher a2
             ; ch2
             ; chcipher_of_cipher c3 ] : cipher_list)
    } ;
    #def #[ id_v2_get ] (_ : 'unit) : msg
    {
      stored ← get V_2_cell ;;
      match stored with
      | Some v => @ret t_msg v
      | None   => @ret t_msg (chmsg_of_msg (0%R : plain AHE))
      end
    }
  ].

(* Compse any predictor against the DSDP game's interface,
  outputs a new adversary, against the IND-CPA oracle's interface.

  `pack` is to take the typed package game_via_oracle_charlie and
  gives its raw_package body so we can use it in the raw_package-level
  composition. SSProve uses it as a noun — "the pack" in the sense of
  "the payload inside the package."
*)
Definition predictor_via_oracle_charlie (predictor : raw_package) : raw_package :=
  predictor ∘ pack game_via_oracle_charlie.

Definition predictor_via_oracle_bob (predictor : raw_package) : raw_package :=
  predictor ∘ pack game_via_oracle_bob.

Check game_via_oracle_charlie.
Check game_via_oracle_bob.
Check (predictor_via_oracle_charlie : raw_package -> _).
Check (predictor_via_oracle_bob : raw_package -> _).

Section reduction_typecheck.
Variable predictor : raw_package.
Check (enc_ind_cpa_real_or_zero
         AHE Renc card_renc renc_card rand_of_renc
         t_msg t_cipher msg_of_chmsg chcipher_of_cipher pkey_of_party
         (predictor_via_oracle_charlie predictor)).
Check (enc_ind_cpa_real_or_zero
         AHE Renc card_renc renc_card rand_of_renc
         t_msg t_cipher msg_of_chmsg chcipher_of_cipher pkey_of_party
         (predictor_via_oracle_bob predictor)).
End reduction_typecheck.

Definition oracle_real : raw_package :=
  oracle_encrypt_real AHE Renc card_renc renc_card rand_of_renc
                      t_msg t_cipher msg_of_chmsg chcipher_of_cipher
                      pkey_of_party.

Definition oracle_zero : raw_package :=
  oracle_encrypt_zero AHE Renc card_renc renc_card rand_of_renc
                      t_msg t_cipher chcipher_of_cipher pkey_of_party.

Lemma game_real_equiv_charlie_real :
  game_real ≈₀ game_via_oracle_charlie ∘ oracle_real.
Proof.
(* Use [eapply] (not ssreflect [apply:]).  On a linked package of this
   size, ssreflect's [apply:] runs an aggressive higher-order unification
   that delta-unfolds the [raw_package] bodies while inferring the
   implicit [{L0 L1 E}] arguments, duplicating a huge term in memory
   (observed: ~80 GiB before OOM kill on this lemma).  Vanilla [eapply]
   leaves [L0]/[L1]/[E] as existentials and resolves them lazily after
   [ValidPackage] typeclass search finds the instances, so the package
   term is never duplicated.  All SSProve upstream examples
   ([PRF.v], [Schnorr.v]) use [eapply] at this step for the same reason.
   The remaining ssreflect tactics in this and the sibling equivalence
   proofs ([apply:], [by]) are unaffected because they operate on the
   smaller post-[simplify_eq_rel] goals.

   (L0, L1 are the sets of mutable state cells that p₀ and p₁ are allowed
    to touch (their "private heap")).
   (E: the export interface, i.e., the set of operations the package offers
    to the outside world. Both packages must export the same interface —
    that is what makes them interchangeable for an adversary).
*)
(* eq_rel_perf_ind_eq: if executing each exported operation on the two
   packages produces the same answer and the same updated heap,
   then no adversary can ever tell them apart.

   The goal after this eapply:

   eq_up_to_inv game_iface (λ '(h₀, h₁), h₀ = h₁) game_real
     (game_via_oracle_charlie ∘ oracle_real)

   eq_up_to_inv E I p₀ p₁:  a per-operation observational-equivalence
   judgement in the relational program logic: for every operation op ∈ E
   and every argument, the two implementations of op produce the same return
   value and leave the heap in a related final state, provided the initial
   heaps were related by the invariant I. Here I = (λ '(h₀, h₁), h₀ = h₁),
   i.e., heaps are required to be bit-identical on both sides.

   Since game_real and game_via_oracle_charlie ∘ oracle_real are literally
   different terms, even they have heap equality, they are not equal.
   Although heap equality is already the strongest invariant
   we can have to prove.

   The purpose: now there is no universal quantifier over adversaries.
   So we don't need to prove "for all adversaries" which is difficult.
   We just have to compare the code of each operation in game_iface on
   the two sides, under heap equality.
*)
eapply eq_rel_perf_ind_eq.

(* Once unfolding eq_up_to_inv, it says that
   for every operation op in the export interface and every argument m,
   the two implementations are related by a relational Hoare triple over the
   heap-equality invariant. This is still abstract.

   simplify_eq_rel m: 

   1. Introduce the operation.
   2. Case-split on which operation we are handling: one subgoal per
      declaration in E. So an interface with two operations produces
      two subgoals.
   3. Unfold the pack / lookup_op
   4. Tidies up the resulting match on the op tag.

   The end state of each subgoal is a concrete relational Hoare triple of the
   form ⊢ ⦃ h₀ = h₁ ⦄ ⟦ code₀(m) ⟧ ≈ ⟦ code₁(m) ⟧ ⦃ ... ⦄, where code₀ and code₁
   are the actual #sample / #put / #get / ret programs we wrote in the package
   definition.
*)
simplify_eq_rel m.
(* ssprove_swap_rhs N swaps the two adjacent commands at position N and N+1 in
   the program text on the right-hand side of a relational triple. *)
- ssprove_swap_rhs 9%N.
(* ssprove_sync_eq is the tactic that takes one identical "probabilistic step"
   off the front of both sides of a relational Hoare triple under the
   heap-equality invariant, from:

   ⊢ ⦃ h₀ = h₁ ⦄  s ← sample D ;; k₀ s   ≈   s ← sample D ;; k₁ s   ⦃ post ⦄

   To:

   ∀ v : D,
    ⊢ ⦃ h₀ = h₁ ⦄   k₀ v   ≈   k₁ v   ⦃ post ⦄

   So it peels off one synchronized (sampling) step.
   Then we by `=> ?` drop the value.
   So those `sample uniform ...` lines in the goal are gone.

   If at any iteration the next instruction on the two sides was not identical,
   say one side had a sample uniform card_msg and the other had a sample uniform
   card_renc, or one side had a #put and the other had a sample,
   ssprove_sync_eq would fail and we need a different relational rule.
*)
  do 10 ssprove_sync_eq=> ?.
  ssprove_sync_eq.
  rewrite chcipher_of_cipherK chmsg_of_msgK.
  
(* The two ret [...] blocks in the goal are huge because they contain the entire
   returned ciphertext list spelled out with all the
   Epow/enc/pkey_of_party/msg_of_idx plumbing.


   rpost_weaken_rule is the consequence rule on the post-condition side.
   Given a relational triple, you may strengthen the program-side post-condition
   provided you supply an implication back to the original one:

     ⊢ ⦃ pre ⦄ c₀ ≈ c₁ ⦃ post' ⦄         ∀ a₀ a₁,  post' a₀ a₁  →  post a₀ a₁
     ───────────────────────────────────────────────────────────────────────
                           ⊢ ⦃ pre ⦄ c₀ ≈ c₁ ⦃ post ⦄

   and it generates two subgoals:

   (a)  ⊢ ⦃ h₀ = h₁ ⦄  ret [...]  ≈  ret [...]  ⦃ ?post' ⦄
   (b)  ∀ a₀ a₁, ?post' a₀ a₁  →  (λ '(b₀,s₀) '(b₁,s₁), b₀ = b₁ ∧ s₀ = s₁) a₀ a₁

   then the rreflexivity_rule is the relational Hoare counterpart of reflexivity
   says: when the two sides of a relational triple are the same program up to
   convertibility, you can close the triple with the strong post-condition
   λ a₀ a₁, a₀ = a₁ (i.e., the result pairs are literally equal).

   In your printout the LHS contains

     rand_of_renc (sample_to_renc _a9_)

   while one item on the RHS displays as

     rand_of_renc (indcpa_ror.sample_to_renc Renc card_renc renc_card _a9_) 

  But actually the local `sample_to_renc` is a wrapper of the latter,
  so they are convertible. The LHS comes from game_real
  (written using the local abbreviation),
  the RHS comes from game_via_oracle_charlie ∘ oracle_real where the oracle was
  defined in indcpa_ror and refers to the fully-qualified name directly.

  Note that the two program game_real and
  are not convertible at top-level. This is the whole point of lines before:
  by peeling layers that are not convertible, the residual part are convertible.
  In other words:

  After a sound permutation of the sample sequence (the swap),
  the diagonal coupling of every shared random choice (the eleven syncs),
  and the cancellation of an artificial encoding round-trip (the two rewrites),
  what remains of the two programs is the same expression.
*)
  apply: rpost_weaken_rule; first exact: rreflexivity_rule.
  by move=> [? ?] [? ?] [-> ->].
- ssprove_sync_eq=> stored.
  by case: stored => [v|]; apply: r_ret.
Qed.

Lemma charlie_zero_equiv_game_hybrid_one :
  game_via_oracle_charlie ∘ oracle_zero ≈₀ game_hybrid_one.
Proof.
eapply eq_rel_perf_ind_eq.
simplify_eq_rel m.
- ssprove_swap_lhs 9%N.
  do 10 ssprove_sync_eq=> ?.
  ssprove_sync_eq.
  rewrite chcipher_of_cipherK.
  apply: rpost_weaken_rule; first exact: rreflexivity_rule.
  by move=> [? ?] [? ?] [-> ->].
- ssprove_sync_eq=> stored.
  by case: stored => [v|]; apply: r_ret.
Qed.

Lemma game_hybrid_one_equiv_bob_real :
  game_hybrid_one ≈₀ game_via_oracle_bob ∘ oracle_real.
Proof.
eapply eq_rel_perf_ind_eq.
simplify_eq_rel m.
- ssprove_swap_rhs 9%N.
  ssprove_swap_rhs 8%N.
  do 10 ssprove_sync_eq=> ?.
  ssprove_sync_eq.
  rewrite chcipher_of_cipherK chmsg_of_msgK.
  apply: rpost_weaken_rule; first exact: rreflexivity_rule.
  by move=> [? ?] [? ?] [-> ->].
- ssprove_sync_eq=> stored.
  by case: stored => [v|]; apply: r_ret.
Qed.

Lemma bob_zero_equiv_game_hybrid_two :
  game_via_oracle_bob ∘ oracle_zero ≈₀ game_hybrid_two.
Proof.
eapply eq_rel_perf_ind_eq.
simplify_eq_rel m.
- ssprove_swap_lhs 9%N.
  ssprove_swap_lhs 8%N.
  do 10 ssprove_sync_eq=> ?.
  ssprove_sync_eq.
  rewrite chcipher_of_cipherK.
  apply: rpost_weaken_rule; first exact: rreflexivity_rule.
  by move=> [? ?] [? ?] [-> ->].
- ssprove_sync_eq=> stored.
  by case: stored => [v|]; apply: r_ret.
Qed.

Lemma game_hybrid_two_perfect_game_enc_zero :
  game_hybrid_two ≈₀ game_enc_zero.
Proof.
eapply eq_rel_perf_ind_eq.
simplify_eq_rel m.
- do 10 ssprove_sync_eq=> ?.
  ssprove_sync_eq.
  apply: rpost_weaken_rule; first exact: rreflexivity_rule.
  by move=> [? ?] [? ?] [-> ->].
- ssprove_sync_eq=> stored.
  by case: stored => [v|]; apply: r_ret.
Qed.

(* For any predictor A, AdvantageE game_real game_hybrid_one A ≤ epsilon_cpa.*)
(* The signature is long because we need to introduce the adversary with
   predictor and locations.

   The five predictor_disj_* hypotheses are location-disjointness
   side-conditions.

   In SSProve two packages can be composed only if their mutable locations do
   not overlap; otherwise behaviour would be undefined.

   The lemma needs disjointness against each of the five things its proof
   links the predictor against: the two games (game_real, game_hybrid_one,
   game_via_oracle_charlie) and the two oracles (oracle_encrypt_real_pkg,
   oracle_encrypt_zero_pkg).
*)
Lemma advantage_hop_real_h1
    (LA : Locations) (predictor : raw_package)
    (predictor_valid :
       ValidPackage LA game_iface A_export predictor)
    (predictor_disj_real : fseparate LA game_real.(locs))
    (predictor_disj_h1 : fseparate LA game_hybrid_one.(locs))
    (predictor_disj_via_oracle_charlie : fseparate LA game_via_oracle_charlie.(locs))
    (predictor_disj_ore :
       fseparate LA
         (oracle_encrypt_real_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher msg_of_chmsg
            chcipher_of_cipher pkey_of_party).(locs))
    (predictor_disj_oze :
       fseparate LA
         (oracle_encrypt_zero_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher chcipher_of_cipher
            pkey_of_party).(locs)) :
  AdvantageE game_real game_hybrid_one predictor <= epsilon_cpa.
Proof.
  have triangle_ineq :=
    Advantage_triangle_chain (game_real : raw_package)
      [:: (game_via_oracle_charlie ∘ oracle_real : raw_package)
        ; (game_via_oracle_charlie ∘ oracle_zero : raw_package) ]
      (game_hybrid_one : raw_package) predictor.
  cbn in triangle_ineq.
  rewrite ?addrA in triangle_ineq.
  apply: (le_trans triangle_ineq).
  clear triangle_ineq.
  erewrite game_real_equiv_charlie_real by ssprove_valid.
  erewrite charlie_zero_equiv_game_hybrid_one by ssprove_valid.
  rewrite GRing.add0r GRing.addr0.
  rewrite -Advantage_link.
  apply: (enc_ind_cpa_real_or_zero AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher msg_of_chmsg
            chcipher_of_cipher pkey_of_party).
Qed.

Lemma advantage_hop_h1_h2
    (LA : Locations) (predictor : raw_package)
    (predictor_valid :
       ValidPackage LA game_iface A_export predictor)
    (predictor_disj_h1 : fseparate LA game_hybrid_one.(locs))
    (predictor_disj_h2 : fseparate LA game_hybrid_two.(locs))
    (predictor_disj_via_oracle_bob : fseparate LA game_via_oracle_bob.(locs))
    (predictor_disj_ore :
       fseparate LA
         (oracle_encrypt_real_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher msg_of_chmsg
            chcipher_of_cipher pkey_of_party).(locs))
    (predictor_disj_oze :
       fseparate LA
         (oracle_encrypt_zero_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher chcipher_of_cipher
            pkey_of_party).(locs)) :
  AdvantageE game_hybrid_one game_hybrid_two predictor <= epsilon_cpa.
Proof.
  have triangle_ineq :=
    Advantage_triangle_chain (game_hybrid_one : raw_package)
      [:: (game_via_oracle_bob ∘ oracle_real : raw_package)
        ; (game_via_oracle_bob ∘ oracle_zero : raw_package) ]
      (game_hybrid_two : raw_package) predictor.
  cbn in triangle_ineq.
  rewrite ?addrA in triangle_ineq.
  eapply le_trans. 1: exact triangle_ineq.
  clear triangle_ineq.
  erewrite game_hybrid_one_equiv_bob_real by ssprove_valid.
  erewrite bob_zero_equiv_game_hybrid_two by ssprove_valid.
  rewrite GRing.add0r GRing.addr0.
  rewrite -Advantage_link.
  apply: (enc_ind_cpa_real_or_zero AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher msg_of_chmsg
            chcipher_of_cipher pkey_of_party).
Qed.

Lemma advantage_game_real_game_enc_zero
    (LA : Locations) (predictor : raw_package)
    (predictor_valid :
       ValidPackage LA game_iface A_export predictor)
    (predictor_disj_real :
       fseparate LA game_real.(locs))
    (predictor_disj_h1 :
       fseparate LA game_hybrid_one.(locs))
    (predictor_disj_h2 :
       fseparate LA game_hybrid_two.(locs))
    (predictor_disj_enc_zero :
       fseparate LA game_enc_zero.(locs))
    (predictor_disj_via_oracle_charlie :
       fseparate LA game_via_oracle_charlie.(locs))
    (predictor_disj_via_oracle_bob :
       fseparate LA game_via_oracle_bob.(locs))
    (predictor_disj_ore :
       fseparate LA
         (oracle_encrypt_real_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher msg_of_chmsg
            chcipher_of_cipher pkey_of_party).(locs))
    (predictor_disj_oze :
       fseparate LA
         (oracle_encrypt_zero_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher chcipher_of_cipher
            pkey_of_party).(locs)) :
  AdvantageE game_real game_enc_zero predictor <= epsilon_cpa + epsilon_cpa.
Proof.
  ssprove triangle (game_real : raw_package)
    [:: (game_hybrid_one : raw_package)
      ; (game_hybrid_two : raw_package) ]
    (game_enc_zero : raw_package) predictor as advantage_bound.
  eapply le_trans. 1: exact advantage_bound.
  clear advantage_bound.
  erewrite game_hybrid_two_perfect_game_enc_zero by ssprove_valid.
  rewrite GRing.addr0.
  apply lerD.
  - exact: advantage_hop_real_h1.
  - exact: advantage_hop_h1_h2.
Qed.

Definition id_guess : nat := 1%N.

Definition guesser_export : Interface :=
  [interface #val #[ id_guess ] : ciphers → msg ].

Definition predictor_guesser : Type :=
  package [interface] guesser_export.

Definition guessing_challenger :
  package (unionm game_iface guesser_export) A_export :=
  [package emptym ;
    #def #[ 0%N ] (_ : 'unit) : 'bool
    {
      #import {sig #[ id_game_run ] : 'unit → ciphers } as call_run ;;
      #import {sig #[ id_guess     ] : ciphers → msg   } as call_pred ;;
      #import {sig #[ id_v2_get    ] : 'unit → msg     } as call_v2 ;;
      view  ← call_run tt ;;
      guess ← call_pred view ;;
      v2    ← call_v2 tt ;;
      ret (guess == v2 : 'bool)
    }
  ].

Definition guessing_experiment
    (predictor : predictor_guesser)
    (game : package [interface] game_iface) : raw_package :=
  guessing_challenger ∘ predictor ∘ game.

Variable card_t_msg : nat.

Hypothesis card_t_msg_gt0 : (0 < card_t_msg)%N.

Hypothesis Pr_guess_enc_zero_le_invm :
  forall (predictor : predictor_guesser),
    distr.mu (pkg_advantage.Pr
                (guessing_experiment predictor game_enc_zero)) true
      <= (card_t_msg%:R)^-1.

Lemma guessing_challenger_pack_setm :
  guessing_challenger.(pack) =
  setm emptym 0%N
    (mkdef 'unit 'bool
      (fun _ : 'unit =>
        view  ← op {sig #[id_game_run] : 'unit → ciphers } ⋅ tt ;;
        guess ← op {sig #[id_guess]    : ciphers → msg } ⋅ view ;;
        v2    ← op {sig #[id_v2_get]   : 'unit → msg } ⋅ tt ;;
        ret (guess == v2 : 'bool))).
Proof.
change guessing_challenger.(pack) with
  (setm emptym 0%N
    (mkdef 'unit 'bool
      (fun _ : 'unit =>
        view  ← op {sig #[id_game_run] : 'unit → ciphers } ⋅ tt ;;
        guess ← op {sig #[id_guess]    : ciphers → msg } ⋅ view ;;
        v2    ← op {sig #[id_v2_get]   : 'unit → msg } ⋅ tt ;;
        ret (guess == v2 : 'bool)))).
reflexivity.
Qed.

Lemma valid_guessing_challenger_link
    (pred : predictor_guesser) :
  ValidPackage (locs pred) game_iface A_export (guessing_challenger ∘ pred).
Proof.
case: guessing_challenger.(pack_valid) => he1 hi1.
split.
- move=> o.
  rewrite he1 /link.
  split.
  + move=> [f Hf].
    exists (fun x => code_link (f x) pred).
    by rewrite //= mapmE Hf.
  + rewrite //= mapmE.
    change (setm emptym _ _) with (guessing_challenger.(pack)).
    move=> [f Hf].
    change (setm emptym _ _) with (guessing_challenger.(pack)) in Hf.
    case Eb: (guessing_challenger.(pack) o.1) => [[S [T g]]|].
    * rewrite Eb /= in Hf.
      by move: Hf => [= ? ?]; subst; exists g.
    * by rewrite Eb /= in Hf.
- move=> n F x.
  rewrite /fhas /link mapmE.
  change (setm emptym _ _) with (guessing_challenger.(pack)).
  case Eb: (guessing_challenger.(pack) n) => [[S' [T' f']]|]; last by [].
  move=> /= [= ?]; subst F => /=.
  eapply (@valid_code_link_residual _ (locs pred)
            (unionm game_iface guesser_export) game_iface guesser_export).
  + have /= Hbs_valid := hi1 n (existT _ S' (existT _ T' f')) x Eb.
    eapply valid_injectLocations; [| exact: Hbs_valid].
    exact: fsub0map.
  +
    eapply valid_package_inject_import; last exact: pred.(pack_valid).
    fmap_solve.
Qed.

Lemma Pr_guess_le
    (LA : Locations) (predictor : predictor_guesser)
    (chain_valid :
       ValidPackage LA game_iface A_export
         (guessing_challenger ∘ predictor))
    (chain_disj_real :
       fseparate LA game_real.(locs))
    (chain_disj_h1 :
       fseparate LA game_hybrid_one.(locs))
    (chain_disj_h2 :
       fseparate LA game_hybrid_two.(locs))
    (chain_disj_enc_zero :
       fseparate LA game_enc_zero.(locs))
    (chain_disj_via_oracle_charlie :
       fseparate LA game_via_oracle_charlie.(locs))
    (chain_disj_via_oracle_bob :
       fseparate LA game_via_oracle_bob.(locs))
    (chain_disj_ore :
       fseparate LA
         (oracle_encrypt_real_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher msg_of_chmsg
            chcipher_of_cipher pkey_of_party).(locs))
    (chain_disj_oze :
       fseparate LA
         (oracle_encrypt_zero_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher chcipher_of_cipher
            pkey_of_party).(locs)) :
  distr.mu (pkg_advantage.Pr
              (guessing_experiment predictor game_real)) true
    <= (card_t_msg%:R)^-1 + 2%:R * epsilon_cpa.
Proof.
set Pr_real :=
  distr.mu (pkg_advantage.Pr
              (guessing_experiment predictor game_real)) true.
set Pr_enc_zero :=
  distr.mu (pkg_advantage.Pr
              (guessing_experiment predictor game_enc_zero)) true.
apply: le_trans (_ : Pr_enc_zero + `|Pr_real - Pr_enc_zero| <= _);
  first by rewrite -lerBlDl; exact: ler_norm.
apply: lerD; first exact: Pr_guess_enc_zero_le_invm.
rewrite /Pr_real /Pr_enc_zero /guessing_experiment
        !link_assoc mulr_natl mulr2n.
exact: advantage_game_real_game_enc_zero.
Qed.

Check predictor_guesser.
Check guessing_challenger.
Check guessing_experiment.
Check Pr_guess_le.

Theorem dsdp_alice_secrecy
    (LA : Locations) (predictor : predictor_guesser)
    (chain_valid :
       ValidPackage LA game_iface A_export
         (guessing_challenger ∘ predictor))
    (chain_disj_real :
       fseparate LA game_real.(locs))
    (chain_disj_h1 :
       fseparate LA game_hybrid_one.(locs))
    (chain_disj_h2 :
       fseparate LA game_hybrid_two.(locs))
    (chain_disj_enc_zero :
       fseparate LA game_enc_zero.(locs))
    (chain_disj_via_oracle_charlie :
       fseparate LA game_via_oracle_charlie.(locs))
    (chain_disj_via_oracle_bob :
       fseparate LA game_via_oracle_bob.(locs))
    (chain_disj_ore :
       fseparate LA
         (oracle_encrypt_real_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher msg_of_chmsg
            chcipher_of_cipher pkey_of_party).(locs))
    (chain_disj_oze :
       fseparate LA
         (oracle_encrypt_zero_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher chcipher_of_cipher
            pkey_of_party).(locs)) :
  distr.mu (pkg_advantage.Pr
              (guessing_experiment predictor game_real)) true
    <= (card_t_msg%:R)^-1 + 2%:R * epsilon_cpa.
Proof.
exact: Pr_guess_le.
Qed.

Check dsdp_alice_secrecy.

Hypothesis epsilon_cpa_ge0 : (0 <= epsilon_cpa)%R.

Lemma log_id (m : nat) (eps : R) :
  (0 < m)%N -> (0 <= eps)%R ->
  (- log (m%:R^-1 + 2%:R * eps) = log m%:R - log (1 + 2%:R * m%:R * eps))%R.
Proof.
move=> Hm Heps.
have Hm_pos : (0 < m%:R :> R)%R by rewrite ltr0n.
have Hmeps_pos : (0 < 1 + 2%:R * m%:R * eps :> R)%R
  by rewrite ltr_pwDl ?ltr01 // !mulr_ge0 // ?ler0n.
have Heq : (m%:R^-1 + 2%:R * eps =
            (1 + 2%:R * m%:R * eps) / m%:R :> R)%R
  by rewrite [RHS]mulrDl mul1r mulrAC mulfK // gt_eqF.
by rewrite Heq logDiv // opprB.
Qed.

Definition Hunp (predictor : predictor_guesser) : R :=
  (- log (distr.mu
            (pkg_advantage.Pr
               (guessing_experiment predictor game_real)) true))%R.

Definition bound : R :=
  (log card_t_msg%:R - log (1 + 2%:R * card_t_msg%:R * epsilon_cpa))%R.

Theorem Hunp_ge_bound
    (LA : Locations) (predictor : predictor_guesser)
    (chain_valid :
       ValidPackage LA game_iface A_export
         (guessing_challenger ∘ predictor))
    (chain_disj_real :
       fseparate LA game_real.(locs))
    (chain_disj_h1 :
       fseparate LA game_hybrid_one.(locs))
    (chain_disj_h2 :
       fseparate LA game_hybrid_two.(locs))
    (chain_disj_enc_zero :
       fseparate LA game_enc_zero.(locs))
    (chain_disj_via_oracle_charlie :
       fseparate LA game_via_oracle_charlie.(locs))
    (chain_disj_via_oracle_bob :
       fseparate LA game_via_oracle_bob.(locs))
    (chain_disj_ore :
       fseparate LA
         (oracle_encrypt_real_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher msg_of_chmsg
            chcipher_of_cipher pkey_of_party).(locs))
    (chain_disj_oze :
       fseparate LA
         (oracle_encrypt_zero_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher chcipher_of_cipher
            pkey_of_party).(locs))
    (Pr_real_gt0 :
       (0 < distr.mu (pkg_advantage.Pr
                        (guessing_experiment predictor game_real)) true)%R) :
  (bound <= Hunp predictor)%R.
Proof.
unfold Hunp, bound.
set Pr_real := distr.mu (pkg_advantage.Pr
                          (guessing_experiment predictor game_real)) true.
have Hpr_le : (Pr_real <= (card_t_msg%:R)^-1 + 2%:R * epsilon_cpa)%R
  by apply: Pr_guess_le.
have Hinvm_pos : (0 < (card_t_msg%:R)^-1 :> R)%R
  by rewrite invr_gt0 ltr0n card_t_msg_gt0.
have Hbound_pos : (0 < (card_t_msg%:R)^-1 + 2%:R * epsilon_cpa :> R)%R
  by rewrite ltr_pwDl // mulr_ge0 //.
rewrite -(log_id (m := card_t_msg) (eps := epsilon_cpa)
                 card_t_msg_gt0 epsilon_cpa_ge0).
by rewrite lerN2 ler_log //.
Qed.

Check log_id.
Check Hunp.
Check bound.
Check Hunp_ge_bound.

End dsdp_security_indcpa.
