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

   Design note (the [Symbolic_AHEnc] finType wall, RESOLVED).  The design doc
   named a symbolic [AHEncType] instance over [he_term] to re-run the
   interpreter.  That is impossible at the type-class level: [AHEncType]
   requires [plain : finComNzRingType] and [cipher : nzRingType], but a free
   [he_term] algebra is infinite.  Resolution: the protocol is re-parameterised
   over a standalone [DSDP_Interface] (no AHEncType, hence no finType/ring/law
   constraints), and [dsdp_symbolic.v] instantiates it at
   [Symbolic_DSDP_Interface] over [he_term].  [dsdp_alice_obs]'s homomorphic
   combine terms ([AO_combine] payloads) are now DERIVED by symbolically running
   [palice] at that instance ([dsdp_observed_combines]), not hand-written; the
   sample/put/hop/leak structure is the explicit, generic corrupted-view
   security model. *)

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
Require Import dsdp_symbolic.

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
   - [AO_recv_output out] — Alice's decrypt-receive followed by the final
     return: [out] is the output [he_term] Alice computes (the scalar-product
     [S]).  Not a hop and binds no new value (it becomes [GC_put_output]);
   - [AO_leak names] — the named ciphertexts leaked to the adversary. *)
Inductive alice_obs : Type :=
| AO_sample_val  : nat -> nat -> alice_obs
| AO_sample_rnd  : nat -> nat -> alice_obs
| AO_put         : nat -> alice_obs
| AO_recv_hop    : nat -> nat -> nat -> alice_obs
| AO_combine     : nat -> he_term -> alice_obs
| AO_recv_output : he_term -> alice_obs
| AO_leak        : seq nat -> alice_obs.

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
   output step writes the resolved [S] term via [GC_put_output] without binding
   a new value; the leak ends the straight-line code as [GC_ret]. *)
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
    | AO_recv_output out =>
        GC_put_output (resolve_term venv renv out) (lower_obs venv renv rest)
    | AO_leak names =>
        GC_ret [seq resolve_term venv renv (HE_var n) | n <- names]
    end
  end.

(* game_of_trace — lower a corrupted-Alice observation trace to the [game_code]
   that the back end then denotes to an SSProve game. *)
Definition game_of_trace (obs : seq alice_obs) : game_code :=
  lower_obs [::] [::] obs.

(* game_of_trace_seeded — [game_of_trace] with a pre-seeded value environment
   [wnames] (the fixed input-weight names, placed at the env bottom so the sample
   pushes give them stable high de Bruijn indices, matching the seeded
   denotation env [MkDenv weight_values [::]]). *)
Definition game_of_trace_seeded (wnames : seq nat) (obs : seq alice_obs)
  : game_code := lower_obs wnames [::] obs.

(* ------------------------------------------------------------------ *)
(* Hop-count adequacy: the lowered game's hop count is the protocol's. *)
(* ------------------------------------------------------------------ *)

(* count_hops_lower_obs — environment-generalised induction lemma: lowering
   neither creates nor drops hop sites, so the back-end [count_hops] of the
   lowered code is the protocol-side [count_obs_hops], for any environments.
   Naming: the [mainSymbol_argument] form [count_hops] of [lower_obs]
   (cf. MathComp [count_map]); the four segments are the multi-word identifiers
   [count_hops] and [lower_obs], not grammar drift. *)
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

(* count_hops_game_of_trace_seeded — the seeded lowering has the same ladder
   length as the trace's hoppable receptions (a pre-seeded value env adds no
   hops). *)
Lemma count_hops_game_of_trace_seeded wnames obs :
  count_hops (game_of_trace_seeded wnames obs) = count_obs_hops obs.
Proof. exact: count_hops_lower_obs. Qed.

(* ------------------------------------------------------------------ *)
(* Deriving the corrupted-view trace from the symbolic programs.       *)
(* ------------------------------------------------------------------ *)

(* walk_obs — the dual-purpose drive over a corrupted party's symbolic
   program [p].  At each [Recv] whose response is a structured secret-bearing
   ciphertext ([HE_enc party (HE_var secret) _]) it emits an [AO_recv_hop] bound
   to a fresh result name [next], feeding the reception result back as
   [SD_cipher (HE_var next)] so subsequent statements reference it by name; at a
   [Recv] whose response is a non-[HE_enc] ciphertext (the decrypt-receive) it
   binds the raw response into the continuation WITHOUT emitting a hop, letting
   the walk continue to the return.  At each [Send] whose payload carries a
   ciphertext it emits an [AO_combine] of that he_term, also bound to a fresh
   [next].  The single counter allocates distinct names for hops and combines
   alike (the only property the lowering pass [game_of_trace] needs; it resolves
   de Bruijn indices by position).  At [Ret (SD_plain s)] it emits the output
   [AO_recv_output s] ([s] is the scalar-product [S] Alice returns); halts at
   [Finish]/[Fail] and at an empty response stream. *)
Fixpoint walk_obs (p : proc symbolic_data) (resp : seq symbolic_data)
    (next : nat) : seq alice_obs :=
  match p with
  | smc_interpreter.Init _ k => walk_obs k resp next
  | smc_interpreter.Recv _ f =>
      match resp with
      | [::] => [::]
      | r :: rs =>
          match symbolic_get_cipher r with
          | Some (HE_enc party (HE_var secret) _) =>
              AO_recv_hop party secret next
                :: walk_obs (f (SD_cipher (HE_var next))) rs next.+1
          | Some _ => walk_obs (f r) rs next
          | None => [::]
          end
      end
  | smc_interpreter.Send _ d k =>
      match symbolic_get_cipher d with
      | Some c => AO_combine next c :: walk_obs k resp next.+1
      | None => walk_obs k resp next
      end
  | smc_interpreter.Ret x =>
      match x with
      | SD_plain s => [:: AO_recv_output s]
      | _ => [::]
      end
  | smc_interpreter.Finish => [::]
  | smc_interpreter.Fail => [::]
  end.

(* walk_obs_dsdp — the load-bearing reduction: walking [palice_sym] against the
   two received hop ciphertexts, starting result names at 100, yields the two
   [AO_recv_hop]s (Bob's secret 10 bound to 100, Charlie's 11 to 101) and the
   two homomorphic [AO_combine] assemblies (each referencing its hop result
   100/101 by name).  Closes by computation.
   Naming: this is the equational characterisation of [walk_obs] on the DSDP
   inputs (the MathComp [_E]-suffix convention would render it [walk_obsE], but
   the [_dsdp] suffix pins the specific instance rather than a generic equation,
   so the four-segment snake_case name reads [walk_obs] applied to [dsdp]). *)
Lemma walk_obs_dsdp :
  walk_obs palice_sym dsdp_received_hop_ciphertexts 100
  = [:: AO_recv_hop 1 10 100 ; AO_recv_hop 2 11 101
      ; AO_combine 102 (HE_emul (HE_epow (HE_var 100) (HE_var 12))
                                (HE_enc 1 (HE_var 14) 20))
      ; AO_combine 103 (HE_emul (HE_epow (HE_var 101) (HE_var 13))
                                (HE_enc 2 (HE_var 15) 21)) ].
Proof. by []. Qed.

(* dsdp_received_responses_output — the response stream that drives the walk
   PAST Alice's decrypt-receive: the two structured hop ciphertexts
   ([dsdp_received_hop_ciphertexts]) followed by the named placeholder
   [SD_cipher (HE_var 50)] Charlie returns, mirroring the third entry of
   [dsdp_symbolic.dsdp_recv_responses].  Feeding this third response lets the
   walk continue to Alice's [Ret], where the scalar-product output [S] is read
   off the return payload. *)
Definition dsdp_received_responses_output : seq symbolic_data :=
  dsdp_received_hop_ciphertexts ++ [:: SD_cipher (HE_var 50) ].

(* walk_obs_dsdp_leak_S — the output-exposing reduction: walking [palice_sym]
   against [dsdp_received_responses_output] extends [walk_obs_dsdp] with the
   final [AO_recv_output S], where [S] is the scalar-product output
   [g - r2 - r3 + u1*v1] Alice returns ([g] = [HE_dec 0 (HE_var 50)] the
   decrypted aggregate; r2,r3,u1,v1 = HE_var 14,15,17,16).  The decrypt-receive
   binds the third response without emitting a hop, so the two [AO_recv_hop]s and
   two [AO_combine]s are unchanged.  Closes by computation. *)
Lemma walk_obs_dsdp_leak_S :
  walk_obs palice_sym dsdp_received_responses_output 100
  = [:: AO_recv_hop 1 10 100 ; AO_recv_hop 2 11 101
      ; AO_combine 102 (HE_emul (HE_epow (HE_var 100) (HE_var 12))
                                (HE_enc 1 (HE_var 14) 20))
      ; AO_combine 103 (HE_emul (HE_epow (HE_var 101) (HE_var 13))
                                (HE_enc 2 (HE_var 15) 21))
      ; AO_recv_output
          (HE_add (HE_sub (HE_sub (HE_dec 0 (HE_var 50)) (HE_var 14))
                          (HE_var 15))
                  (HE_mul (HE_var 17) (HE_var 16))) ].
Proof. by []. Qed.

(* bound_names — the result names that the walk binds (one per [AO_recv_hop] and
   per [AO_combine]).  These name reception/assembly results, NOT free inputs, so
   the sample synthesis below must exclude them. *)
Definition bound_names (w : seq alice_obs) : seq nat :=
  foldr (fun o acc =>
    match o with
    | AO_recv_hop _ _ result => result :: acc
    | AO_combine result _ => result :: acc
    | _ => acc
    end) [::] w.

(* term_value_names — the free [HE_var] value names occurring in a he_term, in
   first-appearance (left-to-right) order.  An [HE_enc]'s randomness slot is a
   nat, not a he_term, so it is not collected here (see [term_rnd_names]). *)
Fixpoint term_value_names (t : he_term) : seq nat :=
  match t with
  | HE_var x => [:: x]
  | HE_const _ => [::]
  | HE_enc _ m _ => term_value_names m
  | HE_dec _ c => term_value_names c
  | HE_emul a b => term_value_names a ++ term_value_names b
  | HE_epow a b => term_value_names a ++ term_value_names b
  | HE_add a b => term_value_names a ++ term_value_names b
  | HE_sub a b => term_value_names a ++ term_value_names b
  | HE_mul a b => term_value_names a ++ term_value_names b
  end.

(* term_rnd_names — the [HE_enc] randomness-slot names occurring in a he_term, in
   first-appearance order (each encryption's slot is appended after its plaintext
   subterm's slots). *)
Fixpoint term_rnd_names (t : he_term) : seq nat :=
  match t with
  | HE_var _ => [::]
  | HE_const _ => [::]
  | HE_enc _ m r => term_rnd_names m ++ [:: r]
  | HE_dec _ c => term_rnd_names c
  | HE_emul a b => term_rnd_names a ++ term_rnd_names b
  | HE_epow a b => term_rnd_names a ++ term_rnd_names b
  | HE_add a b => term_rnd_names a ++ term_rnd_names b
  | HE_sub a b => term_rnd_names a ++ term_rnd_names b
  | HE_mul a b => term_rnd_names a ++ term_rnd_names b
  end.

(* obs_value_names — the value names one observation step contributes: a hop's
   encrypted secret, or every value name of a combine's assembled term. *)
Definition obs_value_names (o : alice_obs) : seq nat :=
  match o with
  | AO_recv_hop _ secret _ => [:: secret]
  | AO_combine _ expr => term_value_names expr
  | _ => [::]
  end.

(* obs_rnd_names — the randomness names one observation step contributes: the
   encryption-randomness slots of a combine's assembled term. *)
Definition obs_rnd_names (o : alice_obs) : seq nat :=
  match o with
  | AO_combine _ expr => term_rnd_names expr
  | _ => [::]
  end.

(* collect_samples — the free-variable / sample-synthesis pass.  It gathers the
   value names then the randomness names contributed by the walk, dedups each by
   [undup] (first appearance), drops any that name a walk-bound result, and emits
   the surviving value names as [AO_sample_val card_msg] then the randomness
   names as [AO_sample_rnd card_renc].  This is the canonical sample prefix the
   lowering pass expects ahead of the put/hop/combine body. *)
Definition collect_samples (card_msg card_renc : nat) (w : seq alice_obs)
  : seq alice_obs :=
  let bound := bound_names w in
  let vals  := undup (flatten [seq obs_value_names o | o <- w]) in
  let rnds  := undup (flatten [seq obs_rnd_names o | o <- w]) in
  let vals' := [seq x <- vals | x \notin bound] in
  let rnds' := [seq x <- rnds | x \notin bound] in
  [seq AO_sample_val card_msg x | x <- vals']
    ++ [seq AO_sample_rnd card_renc x | x <- rnds'].

(* combine_names — the result names bound by the walk's [AO_combine]s, in order
   (the homomorphic assemblies Alice leaks). *)
Definition combine_names (w : seq alice_obs) : seq nat :=
  pmap (fun o => match o with
                 | AO_combine result _ => Some result | _ => None end) w.

(* recv_names — the result names bound by the walk's [AO_recv_hop]s, in order
   (the received hop ciphertexts Alice leaks). *)
Definition recv_names (w : seq alice_obs) : seq nat :=
  pmap (fun o => match o with
                 | AO_recv_hop _ _ result => Some result | _ => None end) w.

(* obs_of_procs — assemble the whole corrupted-view trace from loose symbolic
   arguments (not a record, so [dsdp_alice_obs] stays scheme-agnostic): run the
   walk on [corrupt] against [hop_sends] (result names from 100), prepend the
   synthesised sample prefix and the [AO_put challenge] cell write, then append
   the walk body and the final [AO_leak] of the leaked-view names ([leak] orders
   the combine and recv result names). *)
Definition obs_of_procs (corrupt : proc symbolic_data)
    (hop_sends : seq symbolic_data) (challenge : nat)
    (leak : seq nat -> seq nat -> seq nat) (card_msg card_renc : nat)
  : seq alice_obs :=
  let w := walk_obs corrupt hop_sends 100 in
  collect_samples card_msg card_renc w
    ++ [:: AO_put challenge]
    ++ w
    ++ [:: AO_leak (leak (combine_names w) (recv_names w)) ].

(* obs_of_procs_dsdp — the derived corrupted-Alice trace for DSDP: walking
   [palice_sym] against the two hop ciphertexts, with the leak ordering
   combines-then-recvs, reproduces the 14-element trace.  The value samples come
   out in first-appearance order 10,11,12,14,13,15 (= v2,v3,u2,r2,u3,r3) and the
   walk-bound result names 100..103 are correctly excluded from the prefix.
   Closes by computation.
   Naming: the equational characterisation of [obs_of_procs] on the DSDP inputs;
   as with [walk_obs_dsdp] the [_dsdp] suffix pins the instance (the generic
   [_E] convention would give [obs_of_procsE]), so the four-segment snake_case
   name reads [obs_of_procs] applied to [dsdp]. *)
Lemma obs_of_procs_dsdp (cm cr : nat) :
  obs_of_procs palice_sym dsdp_received_hop_ciphertexts 10
    (fun combines recvs => combines ++ recvs) cm cr
  = [:: AO_sample_val cm 10 ; AO_sample_val cm 11 ; AO_sample_val cm 12 ;
        AO_sample_val cm 14 ; AO_sample_val cm 13 ; AO_sample_val cm 15 ;
        AO_sample_rnd cr 20 ; AO_sample_rnd cr 21 ;
        AO_put 10 ;
        AO_recv_hop 1 10 100 ; AO_recv_hop 2 11 101 ;
        AO_combine 102 (HE_emul (HE_epow (HE_var 100) (HE_var 12))
                                (HE_enc 1 (HE_var 14) 20)) ;
        AO_combine 103 (HE_emul (HE_epow (HE_var 101) (HE_var 13))
                                (HE_enc 2 (HE_var 15) 21)) ;
        AO_leak [:: 102 ; 103 ; 100 ; 101 ] ].
Proof. by []. Qed.

(* obs_of_procs_dsdp_leak_S — the output-exposing corrupted-Alice trace for DSDP:
   walking [palice_sym] against [dsdp_received_responses_output] is the Part I
   trace [obs_of_procs_dsdp] with one [AO_recv_output S] inserted before the
   final [AO_leak].  The sample prefix, the [AO_put], the two [AO_recv_hop]s, the
   two [AO_combine]s and the leak are unchanged: [AO_recv_output] contributes no
   sampled value, binds no walk result, and is neither leaked nor counted.  [S]
   is Alice's scalar-product return [g - r2 - r3 + u1*v1].  Closes by
   computation. *)
Lemma obs_of_procs_dsdp_leak_S (cm cr : nat) :
  obs_of_procs palice_sym dsdp_received_responses_output 10
    (fun combines recvs => combines ++ recvs) cm cr
  = [:: AO_sample_val cm 10 ; AO_sample_val cm 11 ; AO_sample_val cm 12 ;
        AO_sample_val cm 14 ; AO_sample_val cm 13 ; AO_sample_val cm 15 ;
        AO_sample_rnd cr 20 ; AO_sample_rnd cr 21 ;
        AO_put 10 ;
        AO_recv_hop 1 10 100 ; AO_recv_hop 2 11 101 ;
        AO_combine 102 (HE_emul (HE_epow (HE_var 100) (HE_var 12))
                                (HE_enc 1 (HE_var 14) 20)) ;
        AO_combine 103 (HE_emul (HE_epow (HE_var 101) (HE_var 13))
                                (HE_enc 2 (HE_var 15) 21)) ;
        AO_recv_output
          (HE_add (HE_sub (HE_sub (HE_dec 0 (HE_var 50)) (HE_var 14))
                          (HE_var 15))
                  (HE_mul (HE_var 17) (HE_var 16))) ;
        AO_leak [:: 102 ; 103 ; 100 ; 101 ] ].
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(* The DSDP corrupted-Alice trace and the faithfulness result.        *)
(* ------------------------------------------------------------------ *)

(* dsdp_alice_obs — the corrupted-Alice observation trace of DSDP, DERIVED by
   running the generic [obs_of_procs] walk on [palice_sym] (the corrupted
   party's symbolic program) against [dsdp_received_hop_ciphertexts] (the
   derived hop-reception stream from Bob and Charlie).  Nothing here is
   hand-written: the walk reads the two received ciphertexts off the stream and
   the two AO_combine homomorphic assemblies off [palice_sym]'s [Send] payloads,
   threads fresh result names from 100, synthesises the sample prefix from the
   trace's free variables in first-appearance order, and frames the put and the
   leak.  The fixed derivation parameters are: challenge secret [dsdp_v2_name]
   (= v2, Bob's secret = the V_2 cell write); leak ordering [combines ++ recvs]
   (Alice's view ciphertexts, combines before receptions). *)
Definition dsdp_alice_obs (card_msg card_renc : nat) : seq alice_obs :=
  obs_of_procs palice_sym dsdp_received_hop_ciphertexts dsdp_v2_name
    (fun combines recvs => combines ++ recvs) card_msg card_renc.

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

(* dsdp_alice_obs_leak_S — the output-exposing corrupted-Alice observation trace
   of DSDP, DERIVED by running [obs_of_procs] on [palice_sym] against
   [dsdp_received_responses_output] (the hop-reception stream extended with the
   decrypt-receive response).  Identical to [dsdp_alice_obs] except that the walk
   continues across Alice's decrypt-receive and emits the [AO_recv_output S]
   output step, which the lowering pass [game_of_trace] routes to
   [S_output_cell] via [GC_put_output]. *)
Definition dsdp_alice_obs_leak_S (card_msg card_renc : nat) : seq alice_obs :=
  obs_of_procs palice_sym dsdp_received_responses_output dsdp_v2_name
    (fun combines recvs => combines ++ recvs) card_msg card_renc.

(* dsdp_obs_hops_leak_S — the output-exposing DSDP trace still has exactly two
   hoppable receptions: the added [AO_recv_output] is not counted ([count_obs_-
   hops]'s catch-all) and sits before the leak, so the derived game's ladder
   length is unchanged at two, matching [dsdp_obs_hops]. *)
Lemma dsdp_obs_hops_leak_S (card_msg card_renc : nat) :
  count_obs_hops (dsdp_alice_obs_leak_S card_msg card_renc) = 2.
Proof. by []. Qed.

(* dsdp_weight_names — the fixed input-weight names in seed-env order
   (u1, u2, u3, v1), carried at the denotation env bottom by the seed
   [MkDenv [:: Gplain u1; Gplain u2; Gplain u3; Gplain v1] [::]]. *)
Definition dsdp_weight_names : seq nat := [:: 17; 12; 13; 16].

(* dsdp_alice_obs_leak_S_seeded — the output-exposing trace with the input weights
   u1,u2,u3,v1 carried by the seed (excluded from the sample prefix) and the
   output S the genuine scalar product u1*v1 + u2*v2 + u3*v3.  The two AO_combine
   homomorphic assemblies are the auto-derived ones (obs_of_procs_dsdp_leak_S);
   the sample prefix samples only the secrets v2 (=10), v3 (=11) and the masks
   r2 (=14), r3 (=15).  Names: 10 v2, 11 v3, 12 u2, 13 u3, 14 r2, 15 r3, 16 v1,
   17 u1. *)
Definition dsdp_alice_obs_leak_S_seeded (card_msg card_renc : nat)
  : seq alice_obs :=
  [:: AO_sample_val card_msg 10 ; AO_sample_val card_msg 11 ;
      AO_sample_val card_msg 14 ; AO_sample_val card_msg 15 ;
      AO_sample_rnd card_renc 20 ; AO_sample_rnd card_renc 21 ;
      AO_put 10 ;
      AO_recv_hop 1 10 100 ; AO_recv_hop 2 11 101 ;
      AO_combine 102 (HE_emul (HE_epow (HE_var 100) (HE_var 12))
                              (HE_enc 1 (HE_var 14) 20)) ;
      AO_combine 103 (HE_emul (HE_epow (HE_var 101) (HE_var 13))
                              (HE_enc 2 (HE_var 15) 21)) ;
      AO_recv_output (HE_add (HE_add (HE_mul (HE_var 17) (HE_var 16))
                                     (HE_mul (HE_var 12) (HE_var 10)))
                             (HE_mul (HE_var 13) (HE_var 11))) ;
      AO_leak [:: 102 ; 103 ; 100 ; 101 ] ].

(* dsdp_obs_hops_leak_S_seeded — the seeded trace still has two hoppable
   receptions, so the derived ladder has two rungs. *)
Lemma dsdp_obs_hops_leak_S_seeded (card_msg card_renc : nat) :
  count_obs_hops (dsdp_alice_obs_leak_S_seeded card_msg card_renc) = 2.
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(* The one-record IND-CPA secrecy facade.                              *)
(* ------------------------------------------------------------------ *)

(* dsdp_indcpa_secrecy_problem — every input that drives the DSDP corrupted-view
   IND-CPA secrecy derivation, from the symbolic trace to the advantage bound.
   One value determines the real game, the zero game, and the hop count.  The
   scheme/marshalling block is exactly the parameter list of [dsdp_advantage_-
   derived], with each abbreviated name expanded into [X_of_Y]/[K]-suffix form. *)
Record dsdp_indcpa_secrecy_problem := {
  (* sample-domain sizes (shared by the symbolic trace and the game) *)
  sp_card_plaintext  : nat ;
    (* size of the plaintext-scalar sample space *)
  sp_card_randomness : nat ;
    (* size of the encryption-randomness sample space *)
  (* the corrupted-view model (the security question) *)
  sp_corrupted_party_program : proc symbolic_data ;
    (* the corrupted party's protocol program at the symbolic interface;
       [obs_of_procs] walks it to read off what the party samples, receives,
       assembles, and leaks *)
  sp_received_hop_ciphertexts : seq symbolic_data ;
    (* the ciphertexts the corrupted party receives that carry other parties'
       secret inputs, in reception order; each is a sender's first send and
       becomes one IND-CPA hop, and supplying exactly these fixes where the
       walk stops (the party's later decrypt-receive gets no response) *)
  sp_challenge_secret : nat ;
    (* the name of the secret the game challenges; written to the challenge cell *)
  sp_leak_order : seq nat -> seq nat -> seq nat ;
    (* given the names of the ciphertexts the corrupted party ASSEMBLED and the
       names of those it RECEIVED, returns the ordered name list the game leaks *)
  (* the concrete scheme the abstract game is denoted into *)
  sp_enc_scheme : AHEncType ;
  sp_rand_carrier : finType ;
  sp_rand_carrier_card : #|sp_rand_carrier| = sp_card_randomness ;
  sp_rand_of_carrier : sp_rand_carrier -> rand sp_enc_scheme ;
  sp_choice_msg_type : choice_type ;
    (* the choice_type a plaintext is encoded as on the oracle interface *)
  sp_choice_cipher_type : choice_type ;
    (* the choice_type a ciphertext is encoded as; the type of each leaked slot *)
  sp_choice_msg_of_plain : plain sp_enc_scheme -> sp_choice_msg_type ;
  sp_plain_of_choice_msg : sp_choice_msg_type -> plain sp_enc_scheme ;
  sp_choice_msg_of_plainK : cancel sp_choice_msg_of_plain sp_plain_of_choice_msg ;
  sp_choice_cipher_of_cipher : cipher sp_enc_scheme -> sp_choice_cipher_type ;
  sp_cipher_of_choice_cipher : sp_choice_cipher_type -> cipher sp_enc_scheme ;
  sp_choice_cipher_of_cipherK :
    cancel sp_choice_cipher_of_cipher sp_cipher_of_choice_cipher ;
  sp_pub_key_of_party : party_id -> pub_key sp_enc_scheme ;
  sp_msg_of_index : 'I_sp_card_plaintext -> plain sp_enc_scheme ;
  sp_fallback_rand : rand sp_enc_scheme ;
    (* randomness returned by an out-of-range slot lookup; dead in a well-formed
       game (every slot is filled by a prior sample), present only for totality *)
}.

(* corrupted_view — applies the generic lowering pass [obs_of_procs] to the
   symbolic fields of [P], yielding the corrupted party's whole observation
   trace; for the DSDP instance it reduces to [dsdp_alice_obs]. *)
Definition corrupted_view (P : dsdp_indcpa_secrecy_problem) : seq alice_obs :=
  obs_of_procs (sp_corrupted_party_program P) (sp_received_hop_ciphertexts P)
    (sp_challenge_secret P) (sp_leak_order P)
    (sp_card_plaintext P) (sp_card_randomness P).

(* game_of_problem — lowers the corrupted view to the back-end [game_code]
   through the reused [game_of_trace]. *)
Definition game_of_problem (P : dsdp_indcpa_secrecy_problem) : game_code :=
  game_of_trace (corrupted_view P).

(* game_iface_P — the oracle interface the adversary plugs into, the back-end
   [game_iface] applied to [P]'s message/cipher choice types.  (The [_P] suffix
   avoids a clash with the imported back-end [game_iface].) *)
Definition game_iface_P (P : dsdp_indcpa_secrecy_problem) : Interface :=
  game_iface (sp_choice_msg_type P) (sp_choice_cipher_type P).

(* protocol_state_P — the game's protocol-state locations, the back-end
   [protocol_state] at [P]'s message choice type. *)
Definition protocol_state_P (P : dsdp_indcpa_secrecy_problem) : Locations :=
  protocol_state (sp_choice_msg_type P).

(* real_oracle_P — the real IND-CPA encryption oracle for [P]; its arg-3 is the
   [t_msg -> plain] decoder [sp_plain_of_choice_msg]. *)
Definition real_oracle_P (P : dsdp_indcpa_secrecy_problem) :=
  oracle_real_pkg (sp_rand_carrier_card P) P.(sp_rand_of_carrier)
    P.(sp_plain_of_choice_msg) P.(sp_choice_cipher_of_cipher) (sp_pub_key_of_party P).

(* zero_oracle_P — the all-zero oracle for [P]; asymmetric to [real_oracle_P],
   its arg-3 is the choice_type [sp_choice_msg_type] itself, not the decoder. *)
Definition zero_oracle_P (P : dsdp_indcpa_secrecy_problem) :=
  oracle_zero_pkg (sp_rand_carrier_card P) P.(sp_rand_of_carrier)
    (sp_choice_msg_type P) P.(sp_choice_cipher_of_cipher) (sp_pub_key_of_party P).

(* real_game — the denoted real game for [P]: [game_of_problem]'s all-real
   endpoint denoted into [P]'s concrete scheme. *)
Definition real_game (P : dsdp_indcpa_secrecy_problem) : raw_package :=
  denote_game (sp_rand_carrier_card P) P.(sp_rand_of_carrier)
    P.(sp_choice_msg_of_plain) P.(sp_choice_cipher_of_cipher)
    (sp_pub_key_of_party P) P.(sp_msg_of_index) (sp_fallback_rand P)
    (all_real (game_of_problem P)).

(* zero_game — the denoted all-zero endpoint for [P], the distinguishing target
   of the secrecy bound. *)
Definition zero_game (P : dsdp_indcpa_secrecy_problem) : raw_package :=
  denote_game (sp_rand_carrier_card P) P.(sp_rand_of_carrier)
    P.(sp_choice_msg_of_plain) P.(sp_choice_cipher_of_cipher)
    (sp_pub_key_of_party P) P.(sp_msg_of_index) (sp_fallback_rand P)
    (all_zero (game_of_problem P)).

(* dsdp_indcpa_adversary P — a distinguisher against problem [P] bundled with its
   well-formedness; the secrecy theorem quantifies over this record, so it
   quantifies over all valid adversaries. *)
Record dsdp_indcpa_adversary (P : dsdp_indcpa_secrecy_problem) := {
  adv_locations : Locations ;
  adv_package   : raw_package ;
  adv_valid : ValidPackage adv_locations (game_iface_P P) A_export adv_package ;
  adv_disjoint_from_protocol_state : fseparate adv_locations (protocol_state_P P) ;
  adv_disjoint_from_real_oracle : fseparate adv_locations (real_oracle_P P).(locs) ;
  adv_disjoint_from_zero_oracle : fseparate adv_locations (zero_oracle_P P).(locs) ;
}.

(* dsdp_indcpa_secrecy — the one-record IND-CPA secrecy bound, GENERIC over any
   problem [P]: every valid adversary's advantage distinguishing the real game
   from its all-zero endpoint is at most [count_obs_hops (corrupted_view P)] times
   [epsilon_cpa].  Proved via the back end's [advantage_le] (bridging
   [count_obs_hops] to [size (hop_sites ...)] then [eapply advantage_le]), NOT the
   [gc_dsdp]-specific [advantage_gc_dsdp], which times out for an abstract [P].
   The DSDP [2 * epsilon_cpa] bound is the [dsdp_advantage_derived] corollary. *)
Theorem dsdp_indcpa_secrecy (P : dsdp_indcpa_secrecy_problem)
    (Adv : dsdp_indcpa_adversary P) :
  AdvantageE (real_game P) (zero_game P) (adv_package Adv)
    <= (count_obs_hops (corrupted_view P))%:R * epsilon_cpa.
Proof.
rewrite /real_game /zero_game /game_of_problem.
have Hcnt : count_obs_hops (corrupted_view P)
    = size (hop_sites (game_of_trace (corrupted_view P)))
  by rewrite -count_hops_game_of_trace /hop_sites size_iota.
rewrite Hcnt.
eapply advantage_le.
3: apply: (adv_valid Adv).
1: apply: (P.(sp_choice_cipher_of_cipherK)).
1: apply: (P.(sp_choice_msg_of_plainK)).
1: apply: (adv_disjoint_from_protocol_state Adv).
1: apply: (adv_disjoint_from_real_oracle Adv).
1: apply: (adv_disjoint_from_zero_oracle Adv).
Qed.
