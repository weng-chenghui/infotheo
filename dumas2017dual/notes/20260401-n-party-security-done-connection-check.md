# Audit: DSDP Program→Security Pipeline (3-party vs n-party)

## Context

The user wants a revised comparison of how the 3-party and n-party DSDP cases connect from program definition to security proof, and whether the n-party case is missing anything. The n-party case is NOT computable (no `native_compute` verification), so it follows a different path — but the end goal is the same: entropic security.

**Status**: All DSDP files have **0 Admitted**. Everything that exists is fully proved.

---

## 3-Party Pipeline (complete)

```
dsdp_pismc.v          palice, pbob, pcharlie (session-typed programs)
    │                 channels_dual verified by native_compute
    │
    ├── cross_eq ──→  dsdp_program.v    palice_orig, pbob_orig, pcharlie_orig
    │                                    dsdp_computes_dot_product (algebraic)
    │
    ├── correctness → dsdp_correctness.v  dsdp_is_correct (Benaloh, Paillier instances)
    │
    ├── traces ────→  dsdp_entropy_trace.v  dsdp_traces (explicit 3-tuple of bounded seqs)
    │                                        dsdp_result_correct (ring)
    │                                        dsdp_algebraic_correctness (RV version)
    │
    ├── entropy ───→  dsdp_entropy.v
    │                   dsdp_centropy_uniform: H(V2,V3 | V1,U1,U2,U3,S) = log(m)
    │                   alice_view_to_cond: H(V2 | AliceView) = H(V2 | CondRV)
    │                     (strips 3 encryptions + Dk_a + R2,R3 via cinde)
    │                   V3_determined_centropy_v2: chain rule + functional determination
    │
    └── security ──→  dsdp_security.v
          Section dsdp_security:
            dsdp_entropic_security: H(V2|AliceView) = log(m) > 0
          Section bob_security:
            BobView_indep_V1, BobView_indep_V3 (graphoid axioms)
            bob_privacy_V1, bob_privacy_V3: H(V1|BobView) = H(V3|BobView) = log(m)
          Section charlie_security:
            CharlieView_indep_V2, CharlieView_indep_V1 (OTP masking)
            charlie_privacy_V1, charlie_privacy_V2: log(m) > 0
          Section malicious:
            US_compromised_leaks_V2 (if Alice cheats with e_1, V2 leaks)
```

**Key connection**: `alice_view_to_cond` is the bridge — it manually strips 3 encryptions (E_bob_v2, E_charlie_v3, E_alice_d3) one by one using `E_enc_ce_contract`, then strips (Dk_a, R2, R3) via conditional independence (`cinde_V2V3`). This reduces `H(V2 | AliceView)` to `H(V2 | CondRV)` where `CondRV = [%V1, U1, U2, U3, S]`.

---

## N-Party Pipeline (complete for what it covers)

```
dsdp_pismc.v          palice_n (sproc_iter), DParty_first/intermediate/last
    │                 channels_dual for 4-party, 5-party (native_compute)
    │                 NO general n-party duality proof
    │
    ├── program ───→  dsdp_program.v    dsdp_computes_dot_product_n (algebraic, generic n)
    │
    ├── progress ──→  dsdp_progress.v   dsdp_inv (7-constructor invariant)
    │                                    dsdp_reachable_progress (termination)
    │
    ├── traces ────→  dsdp_entropy_trace.v
    │                   alice_trace_at_inv (per-round: [::v] or [::])
    │                   dsdp_inv_rsteps_trace_frags (multi-round fragment characterization)
    │                   (L5c structural foundation — all Qed)
    │
    ├── entropy ───→  dsdp_entropy.v
    │                   dsdp_centropy_uniform_n: H(VarRV | CondRV) = log(m^n_relay)
    │                   where VarRV : {ffun 'I_n_relay.+1 -> msg}
    │
    └── security ──→  dsdp_security.v
          Section relay_security_n (generic OTP):
            relay_otp_indep, relay_enc_otp_indep, relay_privacy_logm
          Section enc_contraction_n:
            enc_ce_contract_ind (inductive encryption stripping)
          Section dsdp_security_n (abstract view):
            dsdp_entropic_security_n: H(VarRV|AliceView) = log(m^n) > 0
              (takes alice_view_contract as hypothesis)
          Section dsdp_concrete_n (concrete view):
            AliceView_n = [%E_relay_RV, [%[%Dk_a, R_relay_RV], CondRV]]
            alice_view_contract_n: H(VarRV|AliceView_n) = H(VarRV|CondRV)
              Step 1: strip E_relay_RV via cinde_centropy_eq + E_relay_cinde_VarRV
              Step 2: strip [%Dk_a, R_relay_RV] via cinde_centropy_eq + cinde_V_relay
            dsdp_entropic_security_n_concrete: H(VarRV|AliceView_n) = log(m^n) > 0
            eavesdropper_security_n: H(VarRV|f∘AliceView_n) >= log(m^n) > 0  (DPI)
          Section malicious_n:
            dotp_n_e1 (if Alice cheats with basis vector e_1)
          Section relay_privacy_concrete_n:
            relay_view_indep_V (graphoid mixing_rule, 2 steps)
            relay_otp_mask_indep: D_i = V_i*U_i + R_i ⊥ V_j
            relay_indep_V_target_n: RelayView_n(i) ⊥ V_j
            relay_privacy_n: H(V_j|RelayView_n(i)) = log(m) > 0
```

---

## Gap Analysis: What n-party has vs what 3-party has

### Fully covered (n-party matches 3-party)

| Aspect | 3-party | n-party | Status |
|--------|---------|---------|--------|
| Algebraic correctness | `dsdp_computes_dot_product` | `dsdp_computes_dot_product_n` | **Done** |
| Fiber entropy bound | `dsdp_centropy_uniform` (log m) | `dsdp_centropy_uniform_n` (log m^n) | **Done** |
| Alice view contraction | `alice_view_to_cond` (manual 3-enc strip) | `alice_view_contract_n` (inductive enc strip) | **Done** |
| Alice entropic security | `dsdp_entropic_security` | `dsdp_entropic_security_n_concrete` | **Done** |
| Eavesdropper security | (not in 3-party) | `eavesdropper_security_n` (DPI) | **N-party only** |
| Relay OTP independence | (bob/charlie manual) | `relay_otp_indep` (generic) | **Done** |
| Per-relay privacy | `bob_privacy_V1/V3`, `charlie_privacy_V1/V2` | `relay_privacy_n` (generic i≠j) | **Done** |
| Malicious adversary | `US_compromised_leaks_V2` | `dotp_n_e1` | **Done** |
| Progress/termination | (not formalized for 3-party) | `dsdp_reachable_progress` | **N-party only** |
| Trace characterization | `dsdp_traces` (explicit) | `dsdp_inv_rsteps_trace_frags` (structural) | **Done** |

### Not missing — different by design

| Aspect | 3-party | n-party | Why different |
|--------|---------|---------|---------------|
| Session duality | `native_compute` (3 pairs) | `native_compute` for 4-party (6 pairs), 5-party (10 pairs) | General n duality needs reflection or induction; verified up to n=5 |
| Cross-equality | `alice_cross_eq` etc. (piSMC↔dsdp_program) | **None** | n-party security goes piSMC→progress→traces→entropy directly; algebraic `dsdp_computes_dot_product_n` exists separately but is not bridged to `palice_n` |
| piSMC programs | palice, pbob, pcharlie | palice_n, DParty_first/intermediate/last, dsdp_n_procs | Both exist; n-party used by dsdp_progress.v and dsdp_entropy_trace.v |
| Trace = concrete values | `dsdp_traces` lists exact ciphertexts | `dsdp_inv_rsteps_trace_frags` gives structural shape | n-party can't enumerate; structural shape suffices for security |
| View type | 11-tuple (Dk_a, S, V1, ..., E_bob_v2) | 7-nested (Dk_a, S, V0, U0, U_relay_RV, R_relay_RV, E_relay_RV) | Same information, different packaging for generality |

### Genuine gaps (n-party things that exist for 3-party but not n-party)

| Gap | 3-party has | n-party status | Impact |
|-----|------------|----------------|--------|
| **Cross-equality** (piSMC↔algebraic) | `alice_cross_eq`, `bob_cross_eq`, `charlie_cross_eq` bridge `palice`↔`palice_orig` in `dsdp_program.v` | **Missing** — `palice_n` (dsdp_pismc.v) and `dsdp_computes_dot_product_n` (dsdp_program.v) are not connected | MEDIUM — the two n-party pipelines (piSMC→traces and algebraic→correctness) are independent |
| **General duality** | All 3 pairs by `native_compute` | 4-party (6 pairs) and 5-party (10 pairs) by `native_compute`; no general-n proof | LOW — duality for specific n is mechanical; general proof needs reflection |
| **N8b-d: Full relay view** | Bob/Charlie views include received ciphertexts | Simplified view [%V_i, U_i, R_i] only; comments at lines 2311-2338 note extension deferred | LOW — current `relay_privacy_n` is fully proved with simplified view |
| **Bundled record** | `dsdp_random_inputs` bundles all RVs + hypotheses | 15+ individual hypotheses in `dsdp_concrete_n` | LOW — packaging, not logical gap |

### Assessment of the cross-equality gap

The 3-party pipeline has TWO paths that meet:
- **piSMC path**: `palice` → `dsdp_traces` → entropy analysis → security
- **Algebraic path**: `palice_orig` → `dsdp_computes_dot_product` → `dsdp_correctness`

`alice_cross_eq` bridges them: `palice = palice_orig`, proving the session-typed program computes the same thing as the algebraic definition.

The n-party pipeline has these two paths separately:
- **piSMC path**: `palice_n`/`dsdp_n_procs` → `dsdp_progress` → `dsdp_entropy_trace` → security (via `dsdp_concrete_n`)
- **Algebraic path**: `dsdp_computes_dot_product_n` → standalone correctness

**What's missing**: An n-party `alice_n_cross_eq` showing that `palice_n` (the piSMC program that `dsdp_progress.v` and `dsdp_entropy_trace.v` actually execute) computes the same algebraic dot product as `dsdp_computes_dot_product_n`. Without this, the two paths don't connect — we know the piSMC program terminates and has structural trace properties (from progress/trace files), and we know the algebraic formula is correct (from dsdp_program.v), but we don't formally prove the piSMC program implements that formula.

**However**: The security proof in `dsdp_concrete_n` does NOT depend on this bridge. It takes `dsdp_centropy_n` as a hypothesis (from the algebraic fiber counting) and `alice_view_contract_n` (from graphoid independence). The piSMC execution is used for progress/termination/traces, but security itself is purely information-theoretic.

---

## Summary

**The n-party pipeline is complete for its stated goal (entropic security).** Every theorem is Qed'd. The pipeline covers:
1. Algebraic correctness
2. Fiber-counting entropy bound
3. View contraction (encryption stripping + conditional independence)
4. Alice's entropic security: H(VarRV | AliceView) = log(m^n) > 0
5. Eavesdropper security via DPI
6. Per-relay privacy: H(V_j | RelayView_i) = log(m) > 0
7. Malicious adversary analysis
8. Progress/termination (n-party only, via dsdp_inv)
9. Trace structural characterization (L5c)

**No missing piece blocks the security proof.** The three "deferred" items (N8b/c/d) are about extending relay views to include ciphertexts, which would be a stronger result but is not needed for the current privacy theorems.
