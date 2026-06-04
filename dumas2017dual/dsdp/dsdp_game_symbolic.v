(* DSDP symbolic-to-game derivation — front end (sub-project 2).

   The back end (dsdp_game_code.v) lowers a reified [game_code] AST to an
   SSProve [package] and proves the generic hybrid-ladder bound
   [advantage_le : AdvantageE (denote_game (all_real gc)) (denote_game
   (all_zero gc)) A <= (size (hop_sites gc)) * epsilon_cpa].  Its [gc_dsdp]
   was a HAND-BUILT fixture standing in for the AST a symbolic execution of
   the piSMC source should emit.

   This file replaces that hand-build with a DERIVATION: a corrupted-Alice
   observation trace ([dsdp_alice_obs]) at the protocol-action abstraction
   level, lowered to [game_code] by a generic pass ([game_of_trace]) that
   synthesises the canonical sample prefix and assigns de Bruijn indices.  The
   headline result [dsdp_faithful] shows the pass reproduces [gc_dsdp]
   exactly, and [dsdp_advantage_derived] transports the back-end IND-CPA bound
   onto the derived game.

   Design note (the [Symbolic_AHEnc] finType wall).  The design doc named a
   symbolic [AHEncType] instance over [he_term] to re-run the interpreter.
   That is impossible at the type-class level: [AHEncType] requires
   [plain : finComNzRingType] and [cipher : nzRingType], but a free [he_term]
   message algebra is infinite, so it is not a finType.  The feasible symbolic
   realisation is the parameter-free [he_term] smart-constructor algebra
   ([s_enc]/[s_emul]/[s_epow]/[s_dec]) below, which the back end's [denote_he]
   already lowers to the real [enc]/[Emul]/[Epow].  Producing the trace by an
   observer-hooked run of the piSMC interpreter (rather than the hand-built
   [dsdp_alice_obs] here) remains the next increment. *)

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
Require Import dsdp_game_code.

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

(* ------------------------------------------------------------------ *)
(* Symbolic AHE algebra (deliverable 1): the [he_term] smart           *)
(* constructors the symbolic execution uses.  Parameter-free, defeq to *)
(* the raw [he_term] constructors; named [s_*] to mark them as the     *)
(* symbolic realisation of the AHE operations, and lowered to the real *)
(* [enc]/[Emul]/[Epow] by the back end's [denote_he].                  *)
(* ------------------------------------------------------------------ *)

(* s_enc — symbolic encryption of plaintext term [m] under the public key of
   party [p], drawing randomness from slot [r]. *)
Definition s_enc (p : nat) (m : he_term) (r : nat) : he_term := HE_enc p m r.

(* s_emul — symbolic homomorphic addition (ciphertext multiplication). *)
Definition s_emul (a b : he_term) : he_term := HE_emul a b.

(* s_epow — symbolic homomorphic scalar multiplication (ciphertext power). *)
Definition s_epow (a k : he_term) : he_term := HE_epow a k.

(* s_dec — symbolic decryption under party [p]'s secret key. *)
Definition s_dec (p : nat) (c : he_term) : he_term := HE_dec p c.

(* ------------------------------------------------------------------ *)
(* Corrupted-Alice observation trace (deliverable 2).                  *)
(* ------------------------------------------------------------------ *)

(* alice_obs — one step of the corrupted-Alice symbolic view, at the
   protocol-action abstraction level (no de Bruijn indices: variables are
   referred to by stable NAMES, which [game_of_trace] resolves):
   - [AO_sample_val card name] — a fresh protocol scalar of cardinality
     [card] enters the view, bound to [name] on the value stack;
   - [AO_sample_rnd card name] — a fresh encryption randomness of cardinality
     [card], bound to [name] on the randomness stack;
   - [AO_put name] — the challenge secret [name] is written to the V_2 cell;
   - [AO_recv_hop p secret result] — Alice receives from party [p] an
     encryption of secret input [secret], bound to [result].  This is the
     ONLY hoppable step (it becomes [GC_enc_hop]); encryptions of random
     masks are emitted by [AO_combine] and stay real;
   - [AO_combine result expr] — Alice binds a homomorphic assembly [expr]
     (over named variables) to [result];
   - [AO_leak names] — the named ciphertexts leaked to the adversary. *)
Inductive alice_obs : Type :=
| AO_sample_val : nat -> nat -> alice_obs
| AO_sample_rnd : nat -> nat -> alice_obs
| AO_put        : nat -> alice_obs
| AO_recv_hop   : nat -> nat -> nat -> alice_obs
| AO_combine    : nat -> he_term -> alice_obs
| AO_leak       : seq nat -> alice_obs.

(* count_obs_hops — the number of hoppable receptions ([AO_recv_hop]) before
   the leak that ends the trace.  This is the protocol-side count the IND-CPA
   ladder length is determined by; [count_hops_game_of_trace] proves it equals
   the back-end [count_hops] of the lowered game. *)
Fixpoint count_obs_hops (obs : seq alice_obs) : nat :=
  match obs with
  | [::] => 0
  | AO_recv_hop _ _ _ :: rest => (count_obs_hops rest).+1
  | AO_leak _ :: _ => 0
  | _ :: rest => count_obs_hops rest
  end.

(* ------------------------------------------------------------------ *)
(* The lowering pass (deliverable 3): game_of_trace.                   *)
(* ------------------------------------------------------------------ *)

(* resolve_term — rewrite a named [he_term] into the de Bruijn form the back
   end's [denote_he] expects, against the value environment [venv] (index 0 =
   most recently bound) and the randomness environment [renv].  A variable
   name becomes its position [index name venv]; an [HE_enc] randomness-slot
   name becomes [index r renv]; party-id tags are literal and pass through. *)
Fixpoint resolve_term (venv renv : seq nat) (t : he_term) : he_term :=
  match t with
  | HE_var x => HE_var (index x venv)
  | HE_const k => HE_const k
  | HE_enc p m r => HE_enc p (resolve_term venv renv m) (index r renv)
  | HE_dec p c => HE_dec p (resolve_term venv renv c)
  | HE_emul a b => HE_emul (resolve_term venv renv a) (resolve_term venv renv b)
  | HE_epow a b => HE_epow (resolve_term venv renv a) (resolve_term venv renv b)
  | HE_add a b => HE_add (resolve_term venv renv a) (resolve_term venv renv b)
  | HE_sub a b => HE_sub (resolve_term venv renv a) (resolve_term venv renv b)
  | HE_mul a b => HE_mul (resolve_term venv renv a) (resolve_term venv renv b)
  end.

(* lower_obs — the worker of [game_of_trace]: fold the observation trace into
   a [game_code], threading the value/randomness name environments.  Each
   binding step pushes its result name on the appropriate environment so that
   subsequent [resolve_term] calls assign the correct de Bruijn index; the
   leak ends the straight-line code as [GC_ret]. *)
Fixpoint lower_obs (venv renv : seq nat) (obs : seq alice_obs) : game_code :=
  match obs with
  | [::] => GC_ret [::]
  | o :: rest =>
    match o with
    | AO_sample_val c name => GC_sample c (lower_obs (name :: venv) renv rest)
    | AO_sample_rnd c name => GC_sample c (lower_obs venv (name :: renv) rest)
    | AO_put name =>
        GC_put (resolve_term venv renv (HE_var name)) (lower_obs venv renv rest)
    | AO_recv_hop p secret result =>
        GC_enc_hop p (resolve_term venv renv (HE_var secret))
          (lower_obs (result :: venv) renv rest)
    | AO_combine result expr =>
        GC_let (resolve_term venv renv expr) (lower_obs (result :: venv) renv rest)
    | AO_leak names =>
        GC_ret [seq resolve_term venv renv (HE_var n) | n <- names]
    end
  end.

(* game_of_trace — lower a corrupted-Alice observation trace to the [game_code]
   that the back end then denotes to an SSProve game. *)
Definition game_of_trace (obs : seq alice_obs) : game_code :=
  lower_obs [::] [::] obs.

(* ------------------------------------------------------------------ *)
(* Hop-count adequacy: the lowered game's hop count is the protocol's. *)
(* ------------------------------------------------------------------ *)

(* count_hops_lower_obs — environment-generalised induction lemma: lowering
   neither creates nor drops hop sites, so the back-end [count_hops] of the
   lowered code is the protocol-side [count_obs_hops], for any environments. *)
Lemma count_hops_lower_obs venv renv obs :
  count_hops (lower_obs venv renv obs) = count_obs_hops obs.
Proof. elim: obs venv renv => [|o rest IH] venv renv //=; case: o => //= *; rewrite ?IH //. Qed.

(* count_hops_game_of_trace — the IND-CPA ladder length of the derived game is
   exactly the number of hoppable receptions in the trace.  This is what ties
   the [k * epsilon_cpa] bound's [k] to the protocol structure generically.
   Naming: the [mainSymbol_argument] form [count_hops] of [game_of_trace]
   (cf. MathComp [size_map] / [count_map]); the five underscore segments are
   the two multi-word identifiers [count_hops] and [game_of_trace], not grammar
   drift. *)
Lemma count_hops_game_of_trace obs :
  count_hops (game_of_trace obs) = count_obs_hops obs.
Proof. exact: count_hops_lower_obs. Qed.

(* ------------------------------------------------------------------ *)
(* The DSDP corrupted-Alice trace and the faithfulness result.        *)
(* ------------------------------------------------------------------ *)

(* dsdp_alice_obs — the corrupted-Alice observation trace of DSDP, at the
   protocol-action level (names: 10..15 = v2 v3 u2 u3 r2 r3 the sampled
   scalars; 20,21 = ra1 ra2 the mask randomness; 30,31 = c2 c3 the ciphertexts
   received from Bob/Charlie; 40,41 = a1 a2 the homomorphic assemblies).
   Alice samples the scalars and mask randomness, writes V_2, receives the two
   secret-input encryptions (the hops), assembles a1 and a2, and leaks
   [a1;a2;c2;c3].  This is the trace the observer-hooked interpreter is meant
   to emit; it is hand-built here only until that interpreter lands. *)
Definition dsdp_alice_obs (card_msg card_renc : nat) : seq alice_obs :=
  [:: AO_sample_val card_msg 10 ; AO_sample_val card_msg 11 ;
      AO_sample_val card_msg 12 ; AO_sample_val card_msg 13 ;
      AO_sample_val card_msg 14 ; AO_sample_val card_msg 15 ;
      AO_sample_rnd card_renc 20 ; AO_sample_rnd card_renc 21 ;
      AO_put 10 ;
      AO_recv_hop 1 10 30 ; AO_recv_hop 2 11 31 ;
      AO_combine 40
        (s_emul (s_epow (HE_var 30) (HE_var 12)) (s_enc 1 (HE_var 14) 20)) ;
      AO_combine 41
        (s_emul (s_epow (HE_var 31) (HE_var 13)) (s_enc 2 (HE_var 15) 21)) ;
      AO_leak [:: 40 ; 41 ; 30 ; 31 ] ].

(* dsdp_faithful — headline of the front end: the generic lowering pass applied
   to the DSDP corrupted-Alice trace reproduces the back-end fixture [gc_dsdp]
   EXACTLY (de Bruijn indices and all), by full computation ([index] on the
   concrete name lists).  The fixture is therefore DERIVED, not hand-written:
   any property proved of [gc_dsdp] now holds of [game_of_trace dsdp_alice_obs].
   ([gc_dsdp]'s discharged argument order is [card_renc] then [card_msg].) *)
Lemma dsdp_faithful (card_msg card_renc : nat) :
  game_of_trace (dsdp_alice_obs card_msg card_renc) = gc_dsdp card_renc card_msg.
Proof. by []. Qed.

(* dsdp_obs_hops — the DSDP trace has exactly two hoppable receptions (Bob's
   c2 and Charlie's c3), so via [count_hops_game_of_trace] the derived game's
   ladder has two rungs, matching [hop_sites_gc_dsdp]. *)
Lemma dsdp_obs_hops (card_msg card_renc : nat) :
  count_obs_hops (dsdp_alice_obs card_msg card_renc) = 2.
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(* Capstone: the IND-CPA bound holds for the DERIVED game.             *)
(* ------------------------------------------------------------------ *)

(* dsdp_advantage_derived — transports the back-end headline [advantage_gc_dsdp]
   onto the game DERIVED from the corrupted-Alice trace: any adversary's
   advantage distinguishing the real derived game from its all-zero endpoint is
   at most [2 * epsilon_cpa].  Parameters and premises mirror [advantage_gc_dsdp]
   verbatim; the proof rewrites by [dsdp_faithful] and applies it.

   PROOF TARGET for /rocq:prove. *)
Lemma dsdp_advantage_derived
    (AHE : AHEncType) (Renc : finType) (card_renc : nat)
    (renc_card : #|Renc| = card_renc) (rand_of_renc : Renc -> rand AHE)
    (t_msg t_cipher : choice_type) (msg_of_chmsg : t_msg -> plain AHE)
    (chmsg_of_msg : plain AHE -> t_msg)
    (chcipher_of_cipher : cipher AHE -> t_cipher)
    (cipher_of_chcipher : t_cipher -> cipher AHE)
    (chcipher_of_cipherK : cancel chcipher_of_cipher cipher_of_chcipher)
    (chmsg_of_msgK : cancel chmsg_of_msg msg_of_chmsg)
    (pkey_of_party : party_id -> pub_key AHE)
    (card_msg : nat) (msg_of_idx : 'I_card_msg -> plain AHE)
    (rand0 : rand AHE) (LA : Locations) (A : raw_package)
    (A_valid : ValidPackage LA (game_iface t_msg t_cipher) A_export A)
    (A_disj_state : fseparate LA (protocol_state t_msg))
    (A_disj_ore : fseparate LA
       (locs (oracle_real_pkg renc_card rand_of_renc msg_of_chmsg
                chcipher_of_cipher pkey_of_party)))
    (A_disj_oze : fseparate LA
       (locs (oracle_zero_pkg renc_card rand_of_renc t_msg
                chcipher_of_cipher pkey_of_party))) :
  AdvantageE
    (denote_game renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
       pkey_of_party msg_of_idx rand0
       (all_real (game_of_trace (dsdp_alice_obs card_msg card_renc))))
    (denote_game renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
       pkey_of_party msg_of_idx rand0
       (all_zero (game_of_trace (dsdp_alice_obs card_msg card_renc))))
    A <= 2%:R * epsilon_cpa.
Proof.
rewrite (dsdp_faithful card_msg card_renc).
apply: advantage_gc_dsdp => //.
Qed.
