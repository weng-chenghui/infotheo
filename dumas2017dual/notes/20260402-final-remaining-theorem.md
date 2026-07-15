# Comparison: DSDP 3-Party vs N-Party Pipelines

## Context

Compare how the 3-party case (computable via `native_compute`) and n-party case (parametric, not computable) each connect piSMC programs to correctness and security proofs. Identify what is fully connected and what gaps remain.

---

## Pipeline Overview

Both cases share the same architecture with two paths:

- **Path A (Computation)**: piSMC program → interpreter → traces → correctness
- **Path B (Lifting)**: protocol ops → RV composition → entropy → security

Both cases now complete both paths. The n-party case substitutes manual invariant enrichment (`dsdp_inv`) for `native_compute`.

---

## Detailed Comparison

### Step 1: Program Definition

| Aspect | 3-party | n-party |
|--------|---------|---------|
| File | `dsdp_pismc.v:105-195` | `dsdp_pismc.v` (palice_n, relay templates) |
| Programs | `palice`, `pbob`, `pcharlie` — concrete fixed processes | `palice_n` + `relay_first`/`relay_intermediate`/`relay_last` templates, parametric in `n_relay` |
| Fuel | 27 steps (15+7+6, computed) | `[> saprocs]` (symbolic, depends on n) |

### Step 2: Interpreter Execution → rsteps

| Aspect | 3-party | n-party |
|--------|---------|---------|
| Method | `native_compute` evaluates `interp_comp` with fuel 27 | `interp_sound` (same) but NO `native_compute` — fuel is symbolic |
| Termination | `dsdp_3party_terminates` — by `native_compute` | `dsdp_interp_terminates` (dsdp_progress.v) — by `dsdp_inv` induction + deadlock-freedom |
| No-fail | `dsdp_3party_no_fail` — by `native_compute` | `dsdp_interp_nofail` (dsdp_nofail.v) — by well-formedness invariant |
| rsteps theorem | `dsdp_3party_rsteps` (dsdp_pismc.v:1195) | `dsdp_n_rsteps` (dsdp_rsteps.v:97) |
| Status | **DONE** | **DONE** |

### Step 3: Trace Content (What values appear in traces?)

| Aspect | 3-party | n-party |
|--------|---------|---------|
| Method | `native_compute` evaluates `interp_traces` → `dsdp_traces_ok` gives exact concrete values | Manual: `dsdp_inv` constructors enriched with HE values → per-constructor trace lemmas |
| Key result | `dsdp_traces_ok` (dsdp_correctness.v:186): full trace = concrete tuple of `d/e/k` values | `alice_full_trace_n` (dsdp_entropy_trace.v:998): trace = `flatten(rev frags) ++ [d v0; priv_key dk]` |
| Per-step concreteness | All values explicit (e.g., `e (v3 * u3 + r3 + (v2 * u2 + r2))`) | Partially concrete: Init values = `[d v0; priv_key dk]`, Inv_AR = `enc(ek(j+1), v_relay(j), r1_relay(j))`, Inv_tail = `enc(ek(alice), chain_acc(n-1), rr_tail)`, Inv_ret = opaque `d` |
| Concrete lemmas | N/A (computation gives everything) | `alice_trace_concrete_AR` (line 699), `alice_trace_concrete_tail` (line 717) |
| Status | **DONE** | **DONE** (per-step concrete; full trace assembled but Ret value `d` not connected to formula) |

### Step 4: Correctness (Does the protocol compute the dot product?)

| Aspect | 3-party | n-party |
|--------|---------|---------|
| Algebraic | `dsdp_computes_dot_product` (dsdp_program.v:257): `alice_result = u1*v1 + u2*v2 + u3*v3` | `dsdp_computes_dot_product_n` (dsdp_program.v:288): `alice_result_n = Σ u_i * v_i` |
| Computational | `dsdp_is_correct` (dsdp_correctness.v:201): evaluates trace, checks Ret value = dot product | `n_party_correctness` (dsdp_entropy_trace.v): `rsteps procs_tup final tr ∧ all_terminated final ∧ nth final 0 = Ret (d (Σ u·v + u₀·v₀))` |
| Bridge | `dsdp_traces_ok` → `is_dsdp dsdp_traces` → `ring` | `inv_rsteps_ret_terminates` stops at first `all_terminated` (Inv_ret), `chain_acc_minus_masks` converts `chain_acc - Σr + u₀·v₀` to `Σ u·v + u₀·v₀` |
| Status | **DONE** | **DONE** |

### Step 5: Security (Entropic bounds on secret leakage)

| Aspect | 3-party | n-party |
|--------|---------|---------|
| Alice's view | `AliceView` (dsdp_security.v:144): `[% Dk_a, S, V1, U1, U2, U3, R2, R3, E_alice_d3, E_charlie_v3, E_bob_v2]` | `AliceView_n` (dsdp_security.v:2032): `[% E_relay_RV, [% [%Dk_a, R_relay_RV], CondRV]]` |
| Main theorem | `dsdp_entropic_security` (line 265): `H(V2\|AliceView) = log(m)` | `dsdp_entropic_security_n_concrete` (line 2159): `H(VarRV\|AliceView_n) = log(m^n_relay)` |
| Proof method | Strip encryptions (cinde) → strip independent components → fiber counting on constraint | Same: `alice_view_contract_n` strips E_relay + Dk_a + R_relay → `dsdp_centropy_n` (fiber counting) |
| Status | **DONE** | **DONE** |

### Step 6: Trace Security (Eavesdropper on communication channel)

| Aspect | 3-party | n-party |
|--------|---------|---------|
| Trace projection | Not explicitly defined (3 parties, fixed structure) | `trace_proj_n` (dsdp_security.v:2044): drops `R_relay_RV`, keeps `E_relay_RV, Dk_a, CondRV` |
| DPI bound | Not explicitly stated (but follows from Step 5 by DPI) | `eavesdropper_security_n` (line 2185): `∀ f, H(VarRV\|f∘AliceView_n) ≥ log(m^n_relay)` |
| Trace corollary | Not stated | `trace_eavesdropper_security_n` (line 2208): instantiates with `f = trace_proj_n` |
| Status | **implicit** | **DONE** |

---

## Summary: What's Connected and What's Not

```
                        3-party              n-party
                        ═══════              ═══════
Program definition      ✓ palice/pbob/       ✓ palice_n + relay
                          pcharlie              templates

Interpreter → rsteps   ✓ native_compute      ✓ interp_sound +
                                                dsdp_inv induction

Trace content           ✓ native_compute      ✓ dsdp_inv enrichment
(concrete values)         gives all values      → per-constructor lemmas

Correctness             ✓ dsdp_is_correct     ✓ n_party_correctness
(trace output =           (trace → ring)        (inv_rsteps_ret_terminates
 dot product)                                    + chain_acc_minus_masks)

RV security             ✓ dsdp_entropic_      ✓ dsdp_entropic_
                          security               security_n_concrete

Trace security          (implicit by DPI)     ✓ trace_eavesdropper_
(eavesdropper bound)                            security_n
```

---

## Former Gap: Correctness for N-Party — NOW CLOSED

**Closed by:** `n_party_correctness` (dsdp_entropy_trace.v), proved 2026-04-02.

**Statement:**
```coq
Theorem n_party_correctness (h : nat)
    (Hfuel : h >= [> saprocs]) :
  (1 <= n_relay)%N ->
  exists (final : n_parties.-tuple (proc data)) tr,
    rsteps procs_tup final tr /\
    all_terminated (tval final) /\
    nth (default_proc data) (tval final) 0 =
      Ret (d (\sum_(j : 'I_n_relay.+1) u (lift ord0 j) * v_relay j + u ord0 * v0)).
```

**How it was closed:** The chain of equalities is:
1. `inv_tail_to_ret_concrete`: after Inv_tail step, Alice decrypts to `Ret (d (chain_acc n_relay.-1 - Σr + u₀·v₀))` via `dec_correct` + `key_alice`
2. `chain_acc_minus_masks`: `chain_acc n_relay.-1 - Σr = Σ u·v_relay` (bigop manipulation via `chain_acc_eq` + `chain_acc_sum`)
3. `inv_rsteps_ret_terminates`: stops at FIRST `all_terminated` state (Inv_ret, Alice at `Ret`), unlike `interp_comp` which steps past `Ret→Finish`
4. Bridge: `interp_comp data procs 2 = tval ps_init` via `dsdp_initial_progress` + `dsdp_terminated_or_progress`

**Key difficulty resolved:** The original approach used `interp_comp_preserves_inv_rv` returning `inv \/ all_terminated`. With enough fuel, `interp_comp` steps past Inv_ret to all-Finish, always landing in the `all_terminated` branch where Alice is at `Finish` (not `Ret`). Fixed by `inv_rsteps_ret_terminates` which stops at the first `all_terminated` state.

---

## How N-Party Replaces Computation

The n-party case cannot use `native_compute` because `n_relay` is a variable. It replaces computation with three techniques:

1. **Invariant enrichment** (dsdp_progress.v): Each `dsdp_inv` constructor carries the *exact* HE ciphertext/plaintext values at that protocol phase. This is the manual equivalent of "evaluating one step."

2. **Per-constructor trace lemmas** (dsdp_entropy_trace.v): `alice_trace_concrete_AR` and `alice_trace_concrete_tail` extract the concrete communicated value from the enriched constructor. This replaces `native_compute`'s role of revealing trace content.

3. **RV lifting + DPI** (dsdp_security.v): Security is proved purely information-theoretically via conditional independence and entropy, bypassing traces entirely. The trace connection (`trace_eavesdropper_security_n`) then follows as a 1-line corollary via DPI.

The key insight: for security, computation is unnecessary — RV lifting handles it. For correctness, computation was replaced by `dsdp_inv` invariant enrichment + `inv_rsteps_ret_terminates` + `chain_acc_minus_masks`. All gaps are now closed.
