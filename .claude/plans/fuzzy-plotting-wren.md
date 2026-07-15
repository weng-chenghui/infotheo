# Plan: `dsdp_trace_infra.v` — Simpler Invariant for Trace/Correctness Proofs

## Context

`dsdp_entropy_trace.v` and `dsdp_trace_progress.v` import `dsdp_progress.v` (3821 lines) and case-split on `dsdp_inv` (7 constructors). But downstream proofs only care about Alice's phase — not relay states. This file provides a 3-constructor abstraction that encapsulates `dsdp_inv` as opaque cargo, giving downstream files 3-case analysis instead of 7.

## Design: `alice_phase` with embedded `dsdp_inv`

**Audit-corrected design.** Three critical findings from audit:
1. AS-constructors have Alice at `Send(...)`, not `alice_foldr_at j` — AP_loop needs a disjunction
2. Step-preservation needs `dsdp_inv` internally — embed as opaque field
3. Trace content lemmas need relay info — derive from embedded `dsdp_inv`

```coq
Inductive alice_phase : nat -> seq (proc data) -> Prop :=
| AP_loop (j : nat) ps :
    dsdp_inv ps ->
    (j < n_relay.+1)%N ->
    (* Alice is either at Recv(j+1, ...) or at Send(dest, ..., alice_foldr_at(j+1)) *)
    (nth default_proc ps 0 = alice_foldr_at j \/
     exists dest sv, nth default_proc ps 0 = Send dest sv (alice_foldr_at j.+1)) ->
    alice_phase j ps

| AP_tail ps :
    dsdp_inv ps ->
    nth default_proc ps 0 = alice_foldr_at n_relay.+1 ->
    alice_phase n_relay.+1 ps

| AP_ret ps :
    dsdp_inv ps ->
    all_terminated ps ->
    ret_val_inv ps ->
    alice_phase n_relay.+2 ps.
```

**Why this works:** Downstream files match on `AP_loop`/`AP_tail`/`AP_ret` (3 cases). The `dsdp_inv ps` field is never case-split by downstream code — it's only used internally by the infra lemmas to prove step-preservation and trace content.

## File: `dsdp_trace_infra.v`

### Imports
```coq
Require Import dsdp_progress.       (* for dsdp_inv, dsdp_inv_step, dsdp_inv_has_progress *)
Require Import dsdp_pismc.           (* for alice_foldr_at, dsdp_n_procs *)
Require Import smc_interpreter.      (* for step, has_progress, all_terminated *)
Require Import dsdp_entropy_trace.   (* for concrete_val, ret_val_inv, inv_step_terminated_concrete *)
```

### Definition and Lemma Table

| # | Type | Name | Signature | Why needed | Difficulty |
|---|------|------|-----------|------------|------------|
| 1 | Inductive | `alice_phase` | 3 constructors (AP_loop, AP_tail, AP_ret) as above | The simpler invariant. Downstream files case-split on this, not `dsdp_inv`. | Easy (def) |
| 2 | Lemma | `dsdp_inv_to_alice_phase` | `dsdp_inv ps -> exists j, alice_phase j ps` | Derives simpler from complex. Case split on 7 `dsdp_inv` constructors → map to 3. For Inv_AR(j): AP_loop j (Left). For Inv_AS0: AP_loop 0 (Right with dest=1). For Inv_AS1: AP_loop 1 (Right). For Inv_ASj(j): AP_loop j (Right). For Inv_drain: AP_tail. For Inv_tail: AP_tail. For Inv_ret: AP_ret. | Easy (7-case dispatch, each 2-3 lines) |
| 3 | Lemma | `alice_phase_has_progress` | `alice_phase j ps -> (j < n_relay.+2)%N -> has_progress data ps` | Progress from simpler invariant. For AP_loop/AP_tail: from embedded `dsdp_inv` via `dsdp_inv_has_progress`. | Easy (2 lines) |
| 4 | Lemma | `alice_phase_step` | `alice_phase j ps -> ~~ all_terminated ps -> exists j', alice_phase j' (one_step_procs data ps) /\ (j <= j')%N` | Step preservation with phase monotonicity. Proof: extract `dsdp_inv` from alice_phase, apply `dsdp_inv_step`, then `dsdp_inv_to_alice_phase`. Phase monotonicity from the transition structure. | Medium (needs careful j tracking) |
| 5 | Lemma | `alice_phase_ret_val` | `alice_phase j ps -> ~~ all_terminated ps -> ret_val_inv (one_step_procs data ps)` | Return value correctness after step. From embedded `dsdp_inv` + `inv_step_gives_inv_ret_val_inv`. | Easy (delegation) |
| 6 | Lemma | `alice_phase_terminated_concrete` | `alice_phase j ps -> ~~ all_terminated ps -> all_terminated (one_step_procs data ps) -> nth default_proc (one_step_procs data ps) 0 = Ret concrete_val` | Terminal step correctness. From embedded `dsdp_inv` + `inv_step_terminated_concrete`. | Easy (delegation) |
| 7 | Lemma | `alice_phase_init` | `alice_phase 0 procs` | Initial state is phase 0. From `dsdp_inv_init` + mapping (Alice starts at Init, which maps to AP_loop 0 after init steps). | Easy |
| 8 | Lemma | `alice_phase_not_terminated` | `alice_phase j ps -> (j < n_relay.+2)%N -> ~~ all_terminated ps` | Non-terminal phases aren't terminated. Alice at Recv/Send ≠ Finish/Ret. | Easy |
| 9 | Lemma | `alice_phase_fuel_terminates` | `alice_phase j ps_tup -> ret_val_inv ps -> (h >= fuel_bound)%N -> exists ps' tr, rsteps ps_tup ps' tr /\ all_terminated (tval ps') /\ nth default_proc (tval ps') 0 = Ret concrete_val` | Fuel-based termination with correctness. Induction on h using alice_phase_step. Replaces `inv_rsteps_ret_terminates` for downstream. | Medium |

### Per-phase trace content lemmas

| # | Name | Signature | Why needed | Difficulty |
|---|------|-----------|------------|------------|
| 10 | `alice_trace_at_AP_loop_recv` | `AP_loop j ps -> nth default_proc ps 0 = alice_foldr_at j -> exists v, (step ps nil 0).1.2 = [:: v]` | At loop-recv phase, Alice receives → trace has 1 entry. Derived from embedded `dsdp_inv` (Inv_AR case has relay at Send). | Medium |
| 11 | `alice_trace_at_AP_loop_send` | `AP_loop j ps -> (exists dest sv, nth default_proc ps 0 = Send dest sv ...) -> (step ps nil 0).1.2 = nil` | At loop-send phase, Alice sends → trace empty. Direct from step semantics. | Easy |
| 12 | `alice_trace_at_AP_tail_recv` | `AP_tail ps -> (step produces match) -> exists v, (step ps nil 0).1.2 = [:: v]` | At tail phase when last relay sends to Alice → trace has 1 entry. From embedded `dsdp_inv` (Inv_tail has last relay at Send). | Medium |
| 13 | `alice_trace_at_AP_tail_drain` | `AP_tail ps -> (step is relay-relay) -> (step ps nil 0).1.2 = nil` | During drain, Alice not involved → trace empty. From step semantics. | Easy |

## Downstream Refactoring

### `dsdp_entropy_trace.v` changes

**Before:** `inv_step_gives_inv_ret_val_inv` has two 7-way case splits (lines 1054-1165 and 1170-1237) totaling ~200 lines.

**After:** Replace with delegation to `alice_phase_ret_val` (1 line) and `alice_phase_step` (1 line). The 7-way case analysis moves INTO `dsdp_trace_infra.v`'s proofs. Net change: the complexity doesn't disappear, but it's **encapsulated** — `dsdp_entropy_trace.v` only sees 3-case analysis.

**Estimated refactoring in `dsdp_entropy_trace.v`:** Replace ~50-70 lines of 7-case dispatch with 3-case dispatch using `alice_phase`.

### `dsdp_trace_progress.v` changes

**Before:** `inv_rsteps_ret_with_trace` (line 287) uses `dsdp_inv` for 7-case dispatch on phase.

**After:** Use `alice_phase` for 3-case dispatch. The Recv/Send distinction within AP_loop is handled by the disjunction in the constructor.

**Estimated refactoring:** Replace ~20-30 lines.

## Effort Estimate

| Component | Lines |
|-----------|-------|
| `dsdp_trace_infra.v` (new) | ~200-250 |
| `dsdp_entropy_trace.v` (refactor) | -50 to -70 net |
| `dsdp_trace_progress.v` (refactor) | -20 to -30 net |
| **Total new code** | ~200-250 |
| **Total savings** | ~70-100 |

The primary benefit is **conceptual clarity**, not line count. Downstream proofs see 3 phases instead of 7.

## Verification

```bash
make -j1 dumas2017dual/dsdp/dsdp_trace_infra.vo
make -j1 dumas2017dual/dsdp/dsdp_entropy_trace.vo
make -j1 dumas2017dual/dsdp/dsdp_trace_progress.vo
make -j1 dumas2017dual/dsdp/dsdp_security_instantiation.vo
```

## Dependency graph (after)

```
dsdp_progress.v (unchanged)
       ↓
dsdp_trace_infra.v (NEW ~250 lines)
  - Exports: alice_phase (3 constructors), 13 lemmas
  - Encapsulates: dsdp_inv as opaque internal detail
       ↓
dsdp_entropy_trace.v (refactored: 3-case instead of 7-case)
       ↓
dsdp_trace_progress.v (refactored: 3-case instead of 7-case)
       ↓
dsdp_security_instantiation.v (unchanged)
```
