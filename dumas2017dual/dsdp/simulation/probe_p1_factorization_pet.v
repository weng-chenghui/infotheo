(* Probe P1 — PET (probabilistic-equivalence-tactic) feasibility timing probe
   for the planned DSDP factorization

     zero_game_leak_S  ≈₀  dsdp_simulator_pkg ∘ dsdp_ideal_pkg.

   TIMING / FEASIBILITY probe, not a finished proof.  It measures the wall-time
   and memory cost of the rhl entry tactic
   [eapply eq_rel_perf_ind_eq; simplify_eq_rel m] on the real all-zero endpoint
   game [zero_game_leak_S] against a hand-rolled simulator/ideal composition,
   plus the first swap/sync steps.

   The local packages [probe_ideal_pkg] / [probe_sim_pkg] are structurally
   analogous to the target factorization: the ideal samples the honest inputs
   v2, v3, writes the V_2 and Sout cells, and returns unit; the simulator
   samples the masks and hop randomness, rebuilds the four-cipher view, and
   passes the two cell reads through.

   Measured results (recorded in the block below the packages) come from the
   rocq-mcp interactive engine (per-command wall-time) and a coqc/rocqworker RSS
   sampler; they are NOT re-run at compile time (the [simplify_eq_rel] step costs
   240 s / 11.6 GB), so the goals here stop at the entry tactic. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap reals realsum.

Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve.Crypt Require Import Package pkg_composition Pr pkg_rhl.
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
Require Import dsdp_indcpa_advantage.

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

Section probe_p1.
(* cloned context of Section dsdp_alice_guess (dsdp_main.v ~705). *)
Variables (AHE : AHEncType) (Renc : finType) (card_renc : nat)
  (renc_card : #|Renc| = card_renc) (rand_of_renc : Renc -> rand AHE)
  (t_msg t_cipher : choice_type)
  (chmsg_of_msg : plain AHE -> t_msg)
  (chcipher_of_cipher : cipher AHE -> t_cipher)
  (pkey_of_party : party_id -> pub_key AHE)
  (card_msg : nat) (msg_of_idx : 'I_card_msg -> plain AHE) (rand0 : rand AHE).
Variable seed : denv AHE.

Local Notation "'msg'" := t_msg (in custom pack_type at level 2).
Local Notation "'ciphers'" := (cipher_list t_cipher)
  (in custom pack_type at level 2).

(* zero_game_leak_S instantiated at this section's parameters (dsdp_main.v
   ~744). *)
Let zero_game : raw_package :=
  zero_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
    pkey_of_party msg_of_idx rand0 seed.

(* I_ideal — the ideal package's export interface: op 1 runs the honest-input
   protocol (returns unit); ops 2 / 3 reveal the V_2 and Sout cells.  Op id 1 is
   free in game_iface_leak_S (which uses 0 / 2 / 3). *)
Definition I_ideal : Interface :=
  [interface
     #val #[ 1%N ] : 'unit → 'unit ;
     #val #[ 2%N ] : 'unit → msg ;
     #val #[ 3%N ] : 'unit → msg ].

(* probe_ideal_pkg — the ideal functionality over the shared protocol state: op
   1 samples the honest inputs v2, v3, writes V_2_cell (v2) and Sout_cell (the
   scalar product u2*v2 + u3*v3 + u1*v1 from the seed weights), returns unit; ops
   2 / 3 read the cells.  Mirrors denote_run's V_2 / Sout writes, but performs
   the two writes up front, before the mask/hop sampling done by the simulator. *)
Definition probe_ideal_pkg :
  package [interface] I_ideal :=
  [package (protocol_state t_msg) ;
    #def #[ 1%N ] (_ : 'unit) : 'unit
    {
      x2 ← sample uniform card_msg ;;
      x3 ← sample uniform card_msg ;;
      let v2 := msg_of_idx x2 in
      let v3 := msg_of_idx x3 in
      let u1 := as_plain (de_val_nth seed 0) in
      let u2 := as_plain (de_val_nth seed 1) in
      let u3 := as_plain (de_val_nth seed 2) in
      let v1 := as_plain (de_val_nth seed 3) in
      #put (V_2_cell t_msg) := Some (chmsg_of_msg v2) ;;
      #put (Sout_cell t_msg) := Some (chmsg_of_msg (u2 * v2 + u3 * v3 + u1 * v1))
        ;;
      ret tt
    } ;
    #def #[ 2%N ] (_ : 'unit) : msg
    {
      stored ← get (V_2_cell t_msg) ;;
      match stored with
      | Some v => ret v
      | None   => ret (chmsg_of_msg (0%R : plain AHE))
      end
    } ;
    #def #[ 3%N ] (_ : 'unit) : msg
    {
      stored ← get (Sout_cell t_msg) ;;
      match stored with
      | Some v => ret v
      | None   => ret (chmsg_of_msg (0%R : plain AHE))
      end
    }
  ].

(* probe_sim_pkg — the simulator over the ideal interface: op 0 (id_game_run)
   calls the ideal (writing the cells), samples the two masks r2, r3, the two
   mask-encryption randomnesses ra1, ra2 and the two hop randomnesses, rebuilds
   the four-cipher view [a1; a2; c2; c3] with the project's own enc / Emul / Epow,
   and returns it; ops 2 / 3 (id_v2_get / id_Sout_get) pass the ideal's cell
   reads through.  Mirrors denote_run's mask/hop sampling and the a1 / a2
   homomorphic combines, but the honest-input v2 / v3 sampling and the cell
   writes live in the ideal, ahead of these samples. *)
Definition probe_sim_pkg :
  package I_ideal (game_iface_leak_S t_msg t_cipher) :=
  [package emptym ;
    #def #[ 0%N ] (_ : 'unit) : ciphers
    {
      #import {sig #[ 1%N ] : 'unit → 'unit } as call_ideal ;;
      _ ← call_ideal Datatypes.tt ;;
      x_r2  ← sample uniform card_msg ;;
      x_r3  ← sample uniform card_msg ;;
      x_ra1 ← sample uniform card_renc ;;
      x_ra2 ← sample uniform card_renc ;;
      x_c2  ← sample uniform card_renc ;;
      x_c3  ← sample uniform card_renc ;;
      let r2  := msg_of_idx x_r2 in
      let r3  := msg_of_idx x_r3 in
      let ra1 := rand_of_renc (@sample_to_renc _ _ renc_card x_ra1) in
      let ra2 := rand_of_renc (@sample_to_renc _ _ renc_card x_ra2) in
      let pk1 := pkey_of_party (nat_to_party_id 1) in
      let pk2 := pkey_of_party (nat_to_party_id 2) in
      let c2c := enc pk1 (0%R : plain AHE)
                     (rand_of_renc (@sample_to_renc _ _ renc_card x_c2)) in
      let c3c := enc pk2 (0%R : plain AHE)
                     (rand_of_renc (@sample_to_renc _ _ renc_card x_c3)) in
      let u2 := as_plain (de_val_nth seed 1) in
      let u3 := as_plain (de_val_nth seed 2) in
      let a1c := Emul (Epow c2c u2) (enc pk1 r2 ra1) in
      let a2c := Emul (Epow c3c u3) (enc pk2 r3 ra2) in
      ret ([:: chcipher_of_cipher a1c; chcipher_of_cipher a2c;
               chcipher_of_cipher c2c; chcipher_of_cipher c3c ]
           : cipher_list t_cipher)
    } ;
    #def #[ 2%N ] (_ : 'unit) : msg
    {
      #import {sig #[ 2%N ] : 'unit → msg } as call_v2 ;;
      v ← call_v2 Datatypes.tt ;;
      ret v
    } ;
    #def #[ 3%N ] (_ : 'unit) : msg
    {
      #import {sig #[ 3%N ] : 'unit → msg } as call_Sout ;;
      s ← call_Sout Datatypes.tt ;;
      ret s
    }
  ].

(* probe_factored — the simulator/ideal composition, exporting
   game_iface_leak_S, the RHS of the factorization to distinguish from
   zero_game. *)
Definition probe_factored : raw_package := probe_sim_pkg ∘ probe_ideal_pkg.

(* ================================================================= *)
(* MEASUREMENTS.  The compiled goals below stop at the entry tactic; *)
(* the [simplify_eq_rel] and swap/sync costs (recorded in the comment *)
(* blocks) were measured interactively (rocq-mcp per-command wall-time *)
(* + a coqc/rocqworker RSS sampler) and are NOT re-run at compile time *)
(* because each [simplify_eq_rel] step costs 2-4 min and 6-12 GB.     *)
(* ================================================================= *)

(* Both ≈₀ statements TYPE-CHECK directly.  The ENTRY tactic
   [eapply eq_rel_perf_ind_eq] resolves the two ValidPackage instances
   automatically AND leaves a single [eq_up_to_inv] goal with no residual
   side-conditions — PROVIDED the composition is written inline as
   [probe_sim_pkg ∘ probe_ideal_pkg].  Hiding it behind the opaque alias
   [probe_factored] makes instance resolution FAIL
   ("Could not find an instance for ?H0 : ValidPackage ?L₁ Game_import ?E
   probe_factored"): the [valid_link] hint needs the [∘] structure visible. *)

(* probe_t0 — baseline: the all-zero endpoint against itself.  Entry
   [eapply eq_rel_perf_ind_eq] : ~7 ms.  [simplify_eq_rel m] : 240 s, producing
   a 195 MB first goal (the id_game_run oracle), peak coqc/PET RSS 11.6 GB
   (cumulative, holding several states).  The 195 MB is dominated by the
   un-reduced [if card_msg == card_msg then _ else _] cardinality-dispatch
   guards from denote_run — each of the four keeps its discarded else-branch, and
   both sides carry the giant term — and by the Sout term re-embedding the whole
   denotation env at every de_val_nth read. *)
Goal zero_game ≈₀ zero_game.
Proof. Time eapply eq_rel_perf_ind_eq. Abort.

(* probe_t1 — the headline: the all-zero endpoint against the simulator/ideal
   composition.  Entry [eapply eq_rel_perf_ind_eq] : ~15 ms (resolves the
   composite ValidPackage, single [eq_up_to_inv] goal).  [simplify_eq_rel m] :
   124.9 s, producing a 97.7 MB first goal (id_game_run), fresh-session PET
   resident 5.64 GB.  Faster and smaller than probe_t0 because only the LHS
   [zero_game] blows up; the simulator/ideal RHS code-links to a modest term. *)
Goal zero_game ≈₀ (probe_sim_pkg ∘ probe_ideal_pkg).
Proof. Time eapply eq_rel_perf_ind_eq. Abort.

(* T2 — first proof steps after [simplify_eq_rel m] on probe_t1's id_game_run
   goal (recorded interactively, NOT re-run here):
     - [ssprove_sync_eq] on the raw goal FAILS with "No head found": the code
       head is a stuck [if card_msg == card_msg then _ else _], not a sample.
     - [rewrite eqxx] reduces the four reflexive guards and collapses the goal
       (195 MB -> 1.36 MB on probe_t0; 12.5 s standalone).
     - two [ssprove_sync_eq] then FIRE (matching the two honest inputs v2, v3);
       [rewrite eqxx] + the two syncs together cost 5.4 s.
     - the THIRD [ssprove_sync_eq] FAILS: the LHS head is a sample (mask r2) while
       the RHS head is a [#put] — the ideal writes its cells right after v2, v3.
     - [ssprove_swap_rhs 0], [ssprove_swap_rhs 1] and [ssprove_swap_lhs 0] all
       FIRE at that point, commuting the ideal's early cell writes past the
       simulator's mask samples to re-align, as the swap inventory predicts.
   The two [if card_renc == card_msg then _ else _] guards need the
   [card_renc != card_msg] hypothesis (present as [card_renc_neq] in the real
   dsdp_alice_guess section, omitted here) to reduce via [rewrite (negbTE …)]. *)

End probe_p1.
