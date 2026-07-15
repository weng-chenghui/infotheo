(* Probe P2 — machine-checked structural facts about the all-zero endpoint
   of the corrupted-Alice DSDP game code.

   Object of interest: the game_code

     all_zero (game_of_trace_seeded dsdp_weight_names
                 (dsdp_alice_obs_leak_S_seeded card_msg card_renc))

   denoted (via denote_game_leak_S over a weight seed) by the
   real_game_leak_S / zero_game_leak_S of dsdp_indcpa_advantage.v.  This file
   records, as computational Examples, (1) the constant-zero hop plaintexts,
   (2) which seed/sample slots reach the ciphers view, (3) where the challenge
   V_2 and the output S enter, and (4) the export interface signatures.

   Structural facts (the code shape, hop count, view/put/output terms, and the
   interface) hold for arbitrary card_msg, card_renc.  The dataflow Examples
   route GC_sample by comparing its cardinality against card_msg / card_renc,
   so they are stated at the concrete instantiation card_msg := 5,
   card_renc := 7 (two distinct cardinalities); the de Bruijn structure they
   analyse is independent of these values.

   Provenance tag legend (source atoms tracked by view_provenance /
   cell_write_provenance below), for card_msg := 5, card_renc := 7:
     seed slot 0 .. 3 : the weight seed de_val_nth seed 0..3 = u1, u2, u3, v1
     10 : first  card_msg sample = v2   (Bob's honest input)
     11 : second card_msg sample = v3   (Charlie's honest input)
     12 : third  card_msg sample = r2   (Alice's mask of the Bob term)
     13 : fourth card_msg sample = r3   (Alice's mask of the Charlie term)
     14 : first  card_renc sample = ra1 (randomness of the r2 encryption)
     15 : second card_renc sample = ra2 (randomness of the r3 encryption)
     16 : inline randomness of hop c2 = Enc(pk_Bob, .)
     17 : inline randomness of hop c3 = Enc(pk_Charlie, .) *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap reals realsum.

Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve.Crypt Require Import Package pkg_composition Pr.
Set Warnings "notation-overridden,ambiguous-paths".

From Stdlib Require Import Utf8.
From extructures Require Import ord fset fmap.

Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter.
Require Import spp_proba bayes spp_entropy.
Require Import homomorphic_encryption indcpa_ror.
Require Import dsdp_program dsdp_entropy dsdp_pismc.
Require Import smc.ssprove_ext_lossless.
Require Import dsdp_game_code.
Require Import dsdp_symbolic_exec.
Require Import dsdp_game_derivation.

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

(* ------------------------------------------------------------------ *)
(* Structural extractors over game_code (parameter-free).             *)
(* ------------------------------------------------------------------ *)

(* enc_hop_plaintexts gc — the plaintext of each GC_enc_hop of gc, in
   left-to-right order. *)
Fixpoint enc_hop_plaintexts (gc : game_code) : seq he_term :=
  match gc with
  | GC_sample _ k | GC_put _ k | GC_put_output _ k | GC_let _ k =>
      enc_hop_plaintexts k
  | GC_enc_hop _ secret k => secret :: enc_hop_plaintexts k
  | GC_ret _ => [::]
  end.

(* ret_outputs gc — the GC_ret output list of gc (the ciphers view). *)
Fixpoint ret_outputs (gc : game_code) : seq he_term :=
  match gc with
  | GC_sample _ k | GC_put _ k | GC_put_output _ k | GC_let _ k
  | GC_enc_hop _ _ k => ret_outputs k
  | GC_ret outs => outs
  end.

(* put_terms gc — the term written by each GC_put of gc (the V_2 cell
   writes), in order. *)
Fixpoint put_terms (gc : game_code) : seq he_term :=
  match gc with
  | GC_put t k => t :: put_terms k
  | GC_sample _ k | GC_put_output _ k | GC_let _ k | GC_enc_hop _ _ k =>
      put_terms k
  | GC_ret _ => [::]
  end.

(* put_output_terms gc — the term written by each GC_put_output of gc (the
   Sout cell writes), in order. *)
Fixpoint put_output_terms (gc : game_code) : seq he_term :=
  match gc with
  | GC_put_output t k => t :: put_output_terms k
  | GC_sample _ k | GC_put _ k | GC_let _ k | GC_enc_hop _ _ k =>
      put_output_terms k
  | GC_ret _ => [::]
  end.

(* ------------------------------------------------------------------ *)
(* Provenance abstract interpreter: a taint twin of denote_run whose    *)
(* control flow matches it constructor-for-constructor, tracking for    *)
(* each stack value the set of source atoms it transitively reads.      *)
(* ------------------------------------------------------------------ *)

(* provenance — a set of source atoms (seed slots and freshly sampled
   values), as a seq nat. *)
Definition provenance := seq nat.

(* term_reads vals rnds t — the source atoms a resolved he_term reads under a
   value/randomness provenance environment, mirroring denote_he: a variable
   reads its value slot, an encryption reads its plaintext and its randomness
   slot, homomorphic and ring nodes union their subterms' reads. *)
Fixpoint term_reads (vals rnds : seq provenance) (t : he_term) : provenance :=
  match t with
  | HE_var i => nth [::] vals i
  | HE_const _ => [::]
  | HE_enc _ m r => undup (term_reads vals rnds m ++ nth [::] rnds r)
  | HE_dec _ c => term_reads vals rnds c
  | HE_emul a b => undup (term_reads vals rnds a ++ term_reads vals rnds b)
  | HE_epow a b => undup (term_reads vals rnds a ++ term_reads vals rnds b)
  | HE_add a b => undup (term_reads vals rnds a ++ term_reads vals rnds b)
  | HE_sub a b => undup (term_reads vals rnds a ++ term_reads vals rnds b)
  | HE_mul a b => undup (term_reads vals rnds a ++ term_reads vals rnds b)
  end.

(* view_provenance card_msg card_renc fresh vals rnds gc — the source atoms
   read by each GC_ret output of gc.  It threads value/randomness provenance
   stacks and a fresh-atom counter with the same routing as denote_run: a
   card_msg sample pushes a fresh value atom, a card_renc sample a fresh
   randomness atom, GC_let pushes its term's reads, GC_enc_hop pushes its
   plaintext's reads together with a fresh inline-randomness atom, GC_put and
   GC_put_output write cells and push nothing. *)
Fixpoint view_provenance (card_msg card_renc fresh : nat)
    (vals rnds : seq provenance) (gc : game_code) : seq provenance :=
  match gc with
  | GC_sample n k =>
      if n == card_msg then
        view_provenance card_msg card_renc fresh.+1 ([:: fresh] :: vals) rnds k
      else if n == card_renc then
        view_provenance card_msg card_renc fresh.+1 vals ([:: fresh] :: rnds) k
      else view_provenance card_msg card_renc fresh.+1 vals rnds k
  | GC_put _ k => view_provenance card_msg card_renc fresh vals rnds k
  | GC_put_output _ k => view_provenance card_msg card_renc fresh vals rnds k
  | GC_let t k =>
      view_provenance card_msg card_renc fresh
        (term_reads vals rnds t :: vals) rnds k
  | GC_enc_hop _ secret k =>
      view_provenance card_msg card_renc fresh.+1
        (undup (term_reads vals rnds secret ++ [:: fresh]) :: vals) rnds k
  | GC_ret outs => [seq term_reads vals rnds o | o <- outs]
  end.

(* cell_write_provenance card_msg card_renc fresh vals rnds gc — the source
   atoms read by each GC_put / GC_put_output write of gc, in order (V_2 cell
   then Sout cell), threaded exactly as view_provenance. *)
Fixpoint cell_write_provenance (card_msg card_renc fresh : nat)
    (vals rnds : seq provenance) (gc : game_code) : seq provenance :=
  match gc with
  | GC_sample n k =>
      if n == card_msg then
        cell_write_provenance card_msg card_renc fresh.+1
          ([:: fresh] :: vals) rnds k
      else if n == card_renc then
        cell_write_provenance card_msg card_renc fresh.+1
          vals ([:: fresh] :: rnds) k
      else cell_write_provenance card_msg card_renc fresh.+1 vals rnds k
  | GC_put t k =>
      term_reads vals rnds t
        :: cell_write_provenance card_msg card_renc fresh vals rnds k
  | GC_put_output t k =>
      term_reads vals rnds t
        :: cell_write_provenance card_msg card_renc fresh vals rnds k
  | GC_let t k =>
      cell_write_provenance card_msg card_renc fresh
        (term_reads vals rnds t :: vals) rnds k
  | GC_enc_hop _ secret k =>
      cell_write_provenance card_msg card_renc fresh.+1
        (undup (term_reads vals rnds secret ++ [:: fresh]) :: vals) rnds k
  | GC_ret _ => [::]
  end.

(* seed_slots — the initial value-provenance stack for the weight seed: slot j
   is the singleton atom j, so a view/cell read of atom j < 4 is a read of
   de_val_nth seed j (= u1, u2, u3, v1). *)
Definition seed_slots : seq provenance := [:: [:: 0]; [:: 1]; [:: 2]; [:: 3]].

(* zero_code_5_7 / real_code_5_7 — the all-zero and all-real endpoints of the
   seeded DSDP corrupted-Alice game code at card_msg := 5, card_renc := 7. *)
Definition zero_code_5_7 : game_code :=
  all_zero (game_of_trace_seeded dsdp_weight_names
              (dsdp_alice_obs_leak_S_seeded 5 7)).

Definition real_code_5_7 : game_code :=
  all_real (game_of_trace_seeded dsdp_weight_names
              (dsdp_alice_obs_leak_S_seeded 5 7)).

(* ------------------------------------------------------------------ *)
(* The all-zero endpoint game code in full (structural, any card).     *)
(* ------------------------------------------------------------------ *)

(* zero_code_literal — the seeded DSDP all-zero endpoint game code, in de
   Bruijn form: six samples, the V_2 write, two zero-plaintext hops, two
   homomorphic combines, the S write, and the four-slot leak. *)
Example zero_code_literal (cm cr : nat) :
  all_zero (game_of_trace_seeded dsdp_weight_names
              (dsdp_alice_obs_leak_S_seeded cm cr))
  = GC_sample cm (GC_sample cm (GC_sample cm (GC_sample cm (GC_sample cr
    (GC_sample cr (GC_put (HE_var 3) (GC_enc_hop 1 (HE_const 0)
    (GC_enc_hop 2 (HE_const 0)
    (GC_let (HE_emul (HE_epow (HE_var 1) (HE_var 7)) (HE_enc 1 (HE_var 3) 1))
    (GC_let (HE_emul (HE_epow (HE_var 1) (HE_var 9)) (HE_enc 2 (HE_var 3) 0))
    (GC_put_output
      (HE_add (HE_add (HE_mul (HE_var 8) (HE_var 11))
                      (HE_mul (HE_var 9) (HE_var 7)))
              (HE_mul (HE_var 10) (HE_var 6)))
    (GC_ret [:: HE_var 1; HE_var 0; HE_var 3; HE_var 2])))))))))))).
Proof. by []. Qed.

(* Q1 — Hop plaintexts: both encryption hops of the all-zero endpoint carry
   the constant zero plaintext HE_const 0. *)
Example hop_plaintexts_all_zero (cm cr : nat) :
  enc_hop_plaintexts (all_zero (game_of_trace_seeded dsdp_weight_names
                        (dsdp_alice_obs_leak_S_seeded cm cr)))
  = [:: HE_const 0; HE_const 0].
Proof. by []. Qed.

(* The all-zero endpoint has exactly two encryption hops. *)
Example hop_count_all_zero (cm cr : nat) :
  count_hops (all_zero (game_of_trace_seeded dsdp_weight_names
                (dsdp_alice_obs_leak_S_seeded cm cr))) = 2.
Proof. by []. Qed.

(* The source trace has exactly two hoppable receptions. *)
Example obs_hop_count (cm cr : nat) :
  count_obs_hops (dsdp_alice_obs_leak_S_seeded cm cr) = 2.
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(* Q2 — Seed and sample reads in the ciphers view.                     *)
(* ------------------------------------------------------------------ *)

(* The ciphers view of the all-zero endpoint is the four leaked slots
   [a1; a2; c2; c3]. *)
Example ret_outputs_all_zero (cm cr : nat) :
  ret_outputs (all_zero (game_of_trace_seeded dsdp_weight_names
                 (dsdp_alice_obs_leak_S_seeded cm cr)))
  = [:: HE_var 1; HE_var 0; HE_var 3; HE_var 2].
Proof. by []. Qed.

(* Per-output source atoms of the all-zero ciphers view: a1 reads {inline c2
   rand 16, seed u2 = slot 1, mask r2 = 12, ra1 = 14}; a2 reads {inline c3
   rand 17, seed u3 = slot 2, mask r3 = 13, ra2 = 15}; c2 reads {16}; c3
   reads {17}. *)
Example view_provenance_all_zero :
  view_provenance 5 7 10 seed_slots [::] zero_code_5_7
  = [:: [:: 16; 1; 12; 14]; [:: 17; 2; 13; 15]; [:: 16]; [:: 17]].
Proof. by []. Qed.

(* The seed slots the all-zero ciphers view reads are exactly slots 1 and 2,
   i.e. de_val_nth seed 1 (= u2) and de_val_nth seed 2 (= u3); slots 0 (u1)
   and 3 (v1) do not reach the view. *)
Example view_seed_slots_all_zero :
  [seq a <- undup (flatten
     (view_provenance 5 7 10 seed_slots [::] zero_code_5_7)) | (a < 4)%N]
  = [:: 1; 2].
Proof. by []. Qed.

(* The honest inputs v2 (atom 10) and v3 (atom 11) do not reach the all-zero
   ciphers view. *)
Example v2_absent_from_zero_view :
  (10 \in flatten (view_provenance 5 7 10 seed_slots [::] zero_code_5_7))
  = false.
Proof. by []. Qed.

Example v3_absent_from_zero_view :
  (11 \in flatten (view_provenance 5 7 10 seed_slots [::] zero_code_5_7))
  = false.
Proof. by []. Qed.

(* Per-output source atoms of the all-real ciphers view: v2 (10) and v3 (11)
   reach it through the real hop ciphertexts c2 and c3. *)
Example view_provenance_all_real :
  view_provenance 5 7 10 seed_slots [::] real_code_5_7
  = [:: [:: 10; 16; 1; 12; 14]; [:: 11; 17; 2; 13; 15];
        [:: 10; 16]; [:: 11; 17]].
Proof. by []. Qed.

(* The honest inputs v2 (atom 10) and v3 (atom 11) reach the all-real ciphers
   view; the IND-CPA hop to the zero endpoint removes them. *)
Example v2_present_in_real_view :
  10 \in flatten (view_provenance 5 7 10 seed_slots [::] real_code_5_7).
Proof. by []. Qed.

Example v3_present_in_real_view :
  11 \in flatten (view_provenance 5 7 10 seed_slots [::] real_code_5_7).
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(* Q3 — Where the challenge V_2 and the output S enter.                *)
(* ------------------------------------------------------------------ *)

(* The all-zero endpoint has one V_2 cell write, of HE_var 3 (= v2). *)
Example put_terms_all_zero (cm cr : nat) :
  put_terms (all_zero (game_of_trace_seeded dsdp_weight_names
               (dsdp_alice_obs_leak_S_seeded cm cr)))
  = [:: HE_var 3].
Proof. by []. Qed.

(* The all-zero endpoint has one Sout cell write, the scalar product
   u1*v1 + u2*v2 + u3*v3 (de Bruijn HE_var 8,11,9,7,10,6). *)
Example put_output_terms_all_zero (cm cr : nat) :
  put_output_terms (all_zero (game_of_trace_seeded dsdp_weight_names
                      (dsdp_alice_obs_leak_S_seeded cm cr)))
  = [:: HE_add (HE_add (HE_mul (HE_var 8) (HE_var 11))
                       (HE_mul (HE_var 9) (HE_var 7)))
               (HE_mul (HE_var 10) (HE_var 6))].
Proof. by []. Qed.

(* Source atoms of the two cell writes of the all-zero endpoint: the V_2 write
   reads only v2 (atom 10); the Sout write reads all four seed weights
   (slots 0..3 = u1, v1, u2, u3) together with the honest inputs v2 (10) and
   v3 (11).  V_2 and S land only in their state cells, not the ciphers view. *)
Example cell_writes_all_zero :
  cell_write_provenance 5 7 10 seed_slots [::] zero_code_5_7
  = [:: [:: 10]; [:: 0; 3; 1; 10; 2; 11]].
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(* Q4 — Export interface signatures of the output-exposing game.       *)
(* ------------------------------------------------------------------ *)

(* The ciphers export type is the SSProve list of ciphertexts chList
   t_cipher. *)
Example ciphers_is_chList (tc : choice_type) : cipher_list tc = chList tc.
Proof. by []. Qed.

(* The three export operation identifiers are 0 (id_game_run), 2 (id_v2_get)
   and 3 (id_Sout_get). *)
Example export_ids : (id_game_run, id_v2_get, id_Sout_get) = (0, 2, 3).
Proof. by []. Qed.

(* game_iface_leak_S t_msg t_cipher exports three operations, each with source
   'unit (chUnit): id 0 returns chList t_cipher (the ciphers view), id 2
   returns t_msg (V_2), id 3 returns t_msg (Sout). *)
Example iface_leak_S_signatures (tm tc : choice_type) :
  FMap.fmval (game_iface_leak_S tm tc) =
  [:: (0%N, (chUnit, chList tc)) ;
      (2%N, (chUnit, tm)) ;
      (3%N, (chUnit, tm)) ].
Proof. by []. Qed.
