# N-Party DSDP Progress: How It's Done

The notes confirm **all 6 pipeline steps are complete** for the n-party case. The key innovation is replacing `native_compute` (which works for 3-party) with a **manual phase invariant** (`dsdp_inv`) that tracks the exact protocol state at each step.

The file is **3690 lines** with the proof architecture:
1. General infrastructure (lines 37–320): stepping lemmas, fixed-point, invariant induction
2. Ranking/acyclicity (lines 326–360): wait-for DAG via ranking functions
3. DSDP-specific (lines 366–3690): the invariant, deadlock-freedom, and termination

---

## Why `dsdp_progress.v` Proofs Are Tedious

| # | Symptom | Lines affected | Root cause | Improvement |
|---|---------|---------------|------------|-------------|
| **S1** | **7-constructor case splits repeated N times** | `dsdp_inv_acyclic` (395 lines), `dsdp_inv_no_orphan` (297 lines), `dsdp_inv_all_targets_valid` (162 lines) | Every lemma about `dsdp_inv` starts with `case: Hinv` and re-proves the same structural facts for all 7 constructors (AR, AS0, AS1, ASj, drain, tail, ret). The `acyclic` and `no_orphan` proofs are structurally identical modulo the ranking function. | **Extract a uniform "frontier descriptor"** — a record `{zone_finish; zone_sender; zone_receiver; active_body; pending_bodies}` — and prove each constructor maps to one. Then `acyclic`, `no_orphan`, and `targets_valid` become single-case proofs over the descriptor. |
| **S2** | **Sub-case explosion on `j` value** (`j=0`, `j=1`, `j=2`, `j≥3`) | `dsdp_inv_step_AR` (337 lines), `dsdp_inv_step_ASj` (361 lines) | The invariant has special hypotheses for j=1 (H6), j=2 (H8), j≥3 (H9). Each step lemma must re-split on j's value to pick the right hypothesis. The boundary between AS0/AS1/ASj is j=0/1/≥2 — a *different* split than H6/H8/H9's j=1/2/≥3. | **Unify the small-j cases** — collapse Inv_AS0, Inv_AS1 into Inv_ASj by allowing j=0 and j=1 with degenerate frontier. The 3 hypotheses H6/H8/H9 can be a single "frontier description" function `frontier_state : nat → _` with a proof that it's correct for all j. |
| **S3** | **Manual `nth_one_step` / `step_nop` threading** | Every step lemma (2328–3422) | After one step, *every* position's new value must be derived via `nth_one_step` + `smc_interpreter.step` + case analysis on whether it fired. The interpreter has no "only matched pairs change" lemma — you must re-derive each position individually. | **Prove a `step_frame` lemma**: if process `i` didn't participate in any matched pair this round, `nth (one_step_procs ps) i = nth ps i`. Then step proofs only need to reason about the 2–3 positions that actually changed. |
| **S4** | **Repeated `exfalso; move/andP: Hstuck` pattern** | `dsdp_inv_acyclic` (lines 1619, 1628, 1683, 1689, ...), `dsdp_inv_no_orphan` | Each "ready" process must be proved not-stuck by showing its Send/Recv partner exists. The proof is always: destruct `is_stuck`, get `¬ is_ready`, show `is_ready` by exhibiting the match, contradiction. | **Tactic or lemma `ready_not_stuck`**: given `nth ps i = Send j v k` and `nth ps j = Recv i f`, produce `¬ is_stuck tps (Ordinal i)`. Eliminates ~30 instances of the exfalso pattern. |
| **S5** | **`inord` / ordinal bookkeeping** | Throughout (esp. 2878–2889, 2914–2917) | Constantly converting between `'I_n_relay.+1`, `nat`, and `inord` — proving `inordK`, `val_inj`, `prednK`, adjusting successor/predecessor bounds. | **Define `relay_idx j` as a coercion** with pre-proved bound lemmas. Or use `{i : 'I_n | P i}` sub-types so the cast is automatic. |
| **S6** | **Frontier zone arithmetic** (`j.-1`, `j.-2`, `j-3`) | Inv_AR H9, Inv_ASj B9 (lines 1249–1257, 2864–2868) | The "Finish zone + frontier sender + frontier receiver" pattern requires manipulating `j.-1`, `j.-2`, `j-3` with `prednK`, `subnSK`, case-splits on j≥3. Every step lemma re-derives these inequalities. | **Package the frontier** as a record with pre-proved arithmetic. Or switch to **ascending indexing** (distance from Alice) instead of descending (distance from active relay), avoiding the subtraction entirely. |
| **S7** | **No automation for "all other positions unchanged"** | Every `dsdp_inv_step_*` lemma's "pending" / "finish zone" sub-goals | After proving the 2–3 active positions moved correctly, you must *also* show all other positions stayed the same (relay_at_body, relay_at_finish_pred). This is pure bookkeeping. | **Combine with S3's `step_frame`**: a tactic `unchanged_positions` that, given the set of matched pairs, automatically discharges all unchanged-position goals. |
| **S8** | **Duplicated constructor-specific body lemmas** | `relay0_body_structure` (816), `relay_inter_body_structure` (838), `relay_last_body_structure` (851), `relay_last_recv_concrete` (862) | Each relay template (first/intermediate/last) needs its own "the body looks like Send 0 (enc ...) (Recv 0 ...)" lemma, hand-unfolded from the session-typed program. | **Single generic `relay_body_structure` lemma** parameterized by position, returning a uniform `{send_val; recv_cont}` record. The 3 template variants would be instances. |

---

## Summary of Effort Distribution

```
Invariant step proofs    (S2,S3,S5,S6,S7):  ~1050 lines  (28%)
Deadlock-freedom via DAG (S1,S4):            ~700 lines   (19%)
Template body lemmas     (S8):               ~250 lines   (7%)
General infrastructure:                      ~320 lines   (9%)
Invariant definition + init:                 ~320 lines   (9%)
Remaining (glue + final thm):               ~1050 lines  (28%)
```

The single highest-leverage improvement is **S3 (step_frame)** — a "frame rule" for stepping would cut the step lemmas roughly in half and also address S7 automatically. The second-highest is **S1 (uniform frontier descriptor)** — it would collapse the three 150–400 line case-explosion proofs into one ~100 line proof.

---

## Proposed New Architecture: `dsdp_symbolic_state`

The core idea is to separate the **symbolic evaluation function** from the **invariant proof obligations**.

### Current architecture (why it's painful)

```
dsdp_inv : seq (proc data) → Prop     (* 7 constructors, each with ~10 hypotheses *)
dsdp_inv_step_AR   : ... → all_terminated ∨ dsdp_inv    (* 337 lines *)
dsdp_inv_step_AS0  : ... → all_terminated ∨ dsdp_inv    (* 61 lines *)
dsdp_inv_step_AS1  : ... → all_terminated ∨ dsdp_inv    (* 115 lines *)
dsdp_inv_step_ASj  : ... → all_terminated ∨ dsdp_inv    (* 361 lines *)
dsdp_inv_step_drain: ... → all_terminated ∨ dsdp_inv    (* 176 lines *)
dsdp_inv_step_TAIL : ... → all_terminated ∨ dsdp_inv    (* 36 lines *)
dsdp_inv_step_RET  : ... → all_terminated ∨ dsdp_inv    (* 27 lines *)
```

Every downstream lemma (`acyclic`, `no_orphan`, `targets_valid`) then does a 7-way case split and re-derives the same facts. The "computation" (what values appear where) is entangled with the "progress" (which pair fires).

### Proposed architecture

#### Layer 1: `dsdp_symbolic_state` — the computation

A single function that, given a phase index, returns the exact process list:

```coq
(* Phase = which communication round we're at *)
Inductive dsdp_phase :=
  | Phase_AR  (j : 'I_n_relay.+1)          (* Alice receiving from relay j *)
  | Phase_AS  (j : 'I_n_relay.+1)          (* Alice sending to relay j *)
  | Phase_drain (j : 'I_n_relay.+1)        (* relay chain draining, frontier at j *)
  | Phase_tail                              (* last relay sending to Alice *)
  | Phase_ret                               (* Alice at Ret, all others Finish *)
  | Phase_done.                             (* all Finish *)

(* The symbolic evaluator: phase → process list *)
Definition dsdp_symbolic_state (ph : dsdp_phase) : seq (proc data) := ...

(* The successor function: which phase comes next *)
Definition dsdp_phase_step (ph : dsdp_phase) : dsdp_phase := ...
```

This is pure — no Prop, no invariant. It's the n-party analogue of what `native_compute` produces for 3-party. The `alice_enc`, `chain_acc`, `term` definitions stay, but they're used inside `dsdp_symbolic_state` directly.

#### Layer 2: `dsdp_step_correct` — one proof per phase transition

```coq
(* The symbolic state after one interpreter step matches the next phase *)
Lemma dsdp_step_correct ph :
  ph <> Phase_done ->
  one_step_procs data (dsdp_symbolic_state ph) = dsdp_symbolic_state (dsdp_phase_step ph).
```

This single lemma replaces all seven `dsdp_inv_step_*` lemmas. The proof is still by cases on `ph`, but each case is much shorter because you're just showing two concrete `seq (proc data)` expressions are equal — no invariant re-establishment, no existential witnesses, no frontier zone bookkeeping. It's pure computation with algebraic rewrites.

#### Layer 3: Properties become trivial

```coq
(* Progress: the symbolic state at any non-done phase has a matched pair *)
Lemma dsdp_symbolic_has_progress ph :
  ph <> Phase_done -> has_progress data (dsdp_symbolic_state ph).

(* Acyclicity: derive ranking from the phase, not from 7 invariant constructors *)
Lemma dsdp_symbolic_acyclic ph (Hsz : ...) :
  wait_for_acyclic (mk_tup (dsdp_symbolic_state ph) Hsz).

(* Termination: by induction on the phase ordering *)
Theorem dsdp_interp_terminates h : ...
```

`acyclic` becomes one proof because the ranking function is derived from `ph` uniformly. `no_orphan` and `targets_valid` similarly collapse.

#### Layer 4: Bridge to interpreter

```coq
(* The interpreter's actual state matches the symbolic state at each round *)
Lemma interp_comp_matches_symbolic k :
  exists ph, interp_comp data procs k = dsdp_symbolic_state ph.
```

This is the inductive glue — proved by `dsdp_step_correct` at each step.

### What changes vs. current

| Aspect | Current | Proposed |
|--------|---------|---------|
| "What values appear" | Scattered across 7 constructor hypotheses | Centralized in `dsdp_symbolic_state` |
| "Which pair fires" | Re-derived in each `dsdp_inv_step_*` | Once in `dsdp_step_correct` |
| "Unchanged positions" | Manual per-position `nth_one_step` threading | Follows from extensional equality of the two lists |
| Downstream properties | 7-way case split each time | Case on `dsdp_phase` (5-6 cases, but the state is fully concrete — most cases are trivial) |
| Frontier bookkeeping | H6/H8/H9 conditional hypotheses | Built into `dsdp_symbolic_state` definition — no conditionals needed |

### The key simplification

The current pain comes from `dsdp_inv` being a **relational** specification ("`ps` satisfies these 10 properties"). Every lemma must re-extract the concrete values from those properties.

`dsdp_symbolic_state` is a **functional** specification ("at phase `ph`, the state **is** this list"). Downstream lemmas just unfold the definition — no extraction needed. This is exactly how the 3-party case works: `native_compute` gives you the concrete list, and you reason about it directly. The proposed design gives you the same concrete list, just built by a function instead of an evaluator.

### The hard part

The `Phase_AS j` and `Phase_drain j` cases still need the AHE homomorphism rewrites (`Epow_scalarM`, `Emul_addM`) to show that the relay's output ciphertext equals `enc(ek(j+1), chain_acc(j), rr')`. But this work is done once, inside `dsdp_symbolic_state` or `dsdp_step_correct`, rather than being repeated across step lemmas and then again across `acyclic`/`no_orphan`/`targets_valid`.

---

## Future Work: Topology Abstraction

The `dsdp_symbolic_state` approach hardcodes the relay-chain topology into the phase definition and the state function. If the topology changes (e.g., tree instead of chain, bidirectional communication, or a different party arrangement), you'd need to rewrite `dsdp_phase`, `dsdp_symbolic_state`, `dsdp_phase_step`, and `dsdp_step_correct`. But that's exactly the same as the current `dsdp_inv` approach — you'd also need to rewrite all 7 constructors and all 7 step lemmas. The symbolic state approach doesn't make topology changes harder; it just makes the *same-topology* proofs shorter.

The real question is: **can the topology be abstracted?**

The reason the current proof is DSDP-specific is that progress depends on knowing which Send/Recv pairs match at each phase. That's a property of the communication graph, not of the cryptographic payload. In principle you could factor it as:

```
Protocol topology          →  progress/deadlock-freedom
  (who sends to whom,           (generic, reusable)
   in what order)

Cryptographic payload      →  correctness/security  
  (what values are sent,         (protocol-specific)
   HE homomorphism)
```

The `smc_deadlock.v` bridge already does the first part generically — it proves deadlock-freedom from `wf_targets + acyclic + no_orphan`. The topology-dependent work is proving those three properties. For a **linear chain** (which DSDP is), those properties follow from a single ranking function `rank(i) = distance from active position`. That argument generalizes to any DAG-structured protocol.

So the real improvement isn't abstracting `dsdp_symbolic_state` over topology — it's making the `smc_deadlock.v` interface powerful enough that protocol-specific files only need to provide:
1. The communication graph at each phase (who targets whom)
2. A ranking function (or a proof that the wait-for graph is a DAG)
3. The concrete values (for correctness/security)

The current code already has (1) and (2) embedded in the invariant, but entangled with (3). Separating them is the leverage — and that separation holds regardless of topology.
