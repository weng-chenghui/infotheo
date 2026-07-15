# Plan: Close N-Party Correctness Gap — COMPLETED

## Status: ALL PROVED (0 Admitted across all 3 files)

Completed 2026-04-02. All lemmas proved and compiled.

## Context

3-party DSDP uses `native_compute` to evaluate `interp_comp` and get concrete trace values, then `dsdp_is_correct` checks the Ret value equals the dot product. N-party cannot compute (parametric `n_relay`), but has manually enriched `dsdp_inv` constructors with concrete HE values. Security is fully proved via RV lifting + DPI. The original gap was: **no lemma connects the `d` in `Inv_ret` to the dot product formula**.

### Final state

| What | 3-party | n-party | Status |
|------|---------|---------|--------|
| Program definition | palice/pbob/pcharlie | palice_n + relay templates | Both DONE |
| rsteps (termination + no-fail) | native_compute | dsdp_inv induction | Both DONE |
| Trace content (concrete values) | native_compute → dsdp_traces_ok | dsdp_inv enrichment → alice_trace_concrete_AR/tail | Both DONE |
| **Correctness (Ret = dot product)** | **dsdp_is_correct (ring)** | **n_party_correctness** | **Both DONE** |
| RV security | dsdp_entropic_security | dsdp_entropic_security_n_concrete | Both DONE |
| Trace security | implicit | trace_eavesdropper_security_n | Both DONE |

---

## Lemma Table — All Proved

### Phase 1: chain_acc ↔ bigop bridge (dsdp_progress.v)

| # | Name | Status | Location |
|---|------|--------|----------|
| L1 | `chain_acc_eq` | **DONE** | dsdp_progress.v, after line 1161 |
| L2 | `chain_acc_sum` | **DONE** | dsdp_progress.v |
| L3 | `chain_acc_minus_masks` | **DONE** | dsdp_progress.v |

### Phase 2: Concrete Ret value (dsdp_progress.v)

| # | Name | Status | Location |
|---|------|--------|----------|
| L4 | `alice_tail_recv_ret_concrete` | **DONE** | dsdp_progress.v, after line 1004 |

### Phase 3: Correctness theorem (dsdp_progress.v + dsdp_entropy_trace.v)

| # | Name | Status | Location |
|---|------|--------|----------|
| L5 | `inv_tail_to_ret_concrete` | **DONE** | dsdp_progress.v, after dsdp_inv_step_TAIL |
| L5b | `dsdp_init_not_terminated` | **DONE** | dsdp_progress.v — `~~ all_terminated` after 2 init steps |
| L5c | `inv_step_gives_inv_ret_val_inv` | **DONE** | dsdp_entropy_trace.v — 7-way case split on dsdp_inv |
| L5d | `inv_step_terminated_concrete` | **DONE** | dsdp_entropy_trace.v — inv + step → all_terminated implies Ret concrete_val |
| L5e | `inv_rsteps_ret_terminates` | **DONE** | dsdp_entropy_trace.v — stops at FIRST all_terminated (Inv_ret) |
| L6 | `n_party_correctness` | **DONE** | dsdp_entropy_trace.v |

### Key insight for L6

The original approach used `interp_comp_preserves_inv_rv` which returned `inv \/ all_terminated`. This was fundamentally broken: with enough fuel, `interp_comp` steps past `Inv_ret` (Alice at `Ret`) to all-`Finish`, landing in the `all_terminated` branch where Alice is at `Finish` (not `Ret`). The fix was `inv_rsteps_ret_terminates` which stops at the FIRST `all_terminated` state, where Alice is still at `Ret concrete_val`.

The bridge `interp_comp data procs 2 = tval ps_init` was proved using:
- `dsdp_initial_progress`: initial state has progress
- `dsdp_terminated_or_progress 1` + `dsdp_init_not_terminated`: second step also has progress
- Two applications of `interp_comp_unfold_eq`

---

## Dependency Graph (all edges satisfied)

```
dec_correct (HB axiom)          key_alice (Section hyp)
        \                            /
         \                          /
          L4: alice_tail_recv_ret_concrete ✓
                     |
L1: chain_acc_eq ✓   |
     |               |
L2: chain_acc_sum ✓  |
     |               |
L3: chain_acc_minus_masks ✓
     |               |
     +-------+-------+
             |
   L5: inv_tail_to_ret_concrete ✓
             |
   L5e: inv_rsteps_ret_terminates ✓
             |
   L6: n_party_correctness ✓
```

---

## Files — Admitted counts

| File | Admitted | Compiled |
|------|---------|----------|
| `dumas2017dual/dsdp/dsdp_progress.v` | 0 | ✓ |
| `dumas2017dual/dsdp/dsdp_entropy_trace.v` | 0 | ✓ |
| `dumas2017dual/dsdp/dsdp_security.v` | 0 | ✓ |

## Commits

- `fa48079` dsdp_progress: concretize HE chain — 0 Admitted
- `d536564` trace→security bridge: concrete trace values + eavesdropper security
- `7e714a0` n_party_correctness: concrete Ret value through protocol execution (WIP)
- `e6ac4c1` n_party_correctness: inv + ret_val_inv through interp_comp (3 admits)
- `71f6b8e` n_party_correctness: 0 Admitted — close all admits
- `8fa1cbc` rename n_party_computational_correctness → n_party_correctness
