# Audit Report: Phase 3D Operational-Distributional Bridge Plan

## Executive Summary

The plan correctly identifies the fundamental gap between the operational trace world (`seq data`, `cipher AHE : nzRingType`) and the distributional security world (`enc_msg : finType`, `{RV P -> enc_msg}`). The overall architecture (two-level bridge + IND-CPA axiom) is sound in principle. However, there are several significant issues with type accuracy, difficulty underestimation, missing prerequisites, and a critical design question that the plan leaves partially unresolved. The plan is also overly optimistic about certain "Easy" items.

---

## 1. Type Bridge: Is `enc_msg = p.-enc msg` really just wrapping a plaintext?

**Verified: YES.** This is accurate and is perhaps the plan's most important insight.

From `homomorphic_encryption.v` line 219:
```coq
Variant enc_for (p : party_id) (T : Type) : Type := EncFor of T.
```

So `p.-enc msg` is literally `EncFor p (v : msg)` — a party-labeled plaintext. It is finType because `msg = 'Z_m` is finType, and `enc_for` inherits finType via `[isNew for @enc_for_v p T]` (line 227).

The security proof's `enc_msg` variable (line 1957 of `dsdp_security.v`) is abstract, but the comment on line 1996 says it is concretely `pty.-enc msg`. The hypotheses `E_enc_unif` and `E_enc_inde` then assert that any RV of type `{RV P -> pty.-enc A}` is uniform and independent — these are the ideal cipher properties.

**Key consequence**: The security proof never sees actual ciphertexts. "Encryption" is modeled purely at the message level with ideal distributional properties. This is a deliberate cryptographic abstraction — standard in symbolic/information-theoretic security proofs.

**How does encryption enter the picture?** It doesn't, directly. The security proof says: "IF the encryptions Alice sees are uniform and independent (of everything), THEN the entropy bound holds." The IND-CPA axiom's job is to justify this "IF" — but within the formalization, the security proof is purely about labeled plaintexts.

---

## 2. Sample Space Design (Option B: reduced sample space)

**Assessment: Compatible but with significant caveats.**

The plan's Option B proposes `T_dsdp` containing only `plain AHE` (finType) quantities, with keys and randomness as external parameters. This is compatible with `dsdp_security.v`'s approach — that section also treats `T`, `P` as abstract with no key/randomness RVs in the sample space.

**However, there are problems:**

### Problem 2a: `dsdp_centropy_uniform_n` requires more than just RV projections

Looking at `dsdp_entropy.v` lines 420-438, `dsdp_centropy_uniform_n` requires:
- `constraint_fiber_n`: `forall t, VarRV t \in dsdp_fiber_fn_n (CondRV t)` — VarRV must satisfy the algebraic constraint at every sample point
- `InputRV_proj_n`: `forall t, InputRV t = dsdp_proj_input_n (CondRV t)`
- `VarRV_uniform_n`: `\`p_ VarRV = fdist_uniform card_ffun_msg` — VarRV is uniformly distributed
- `VarRV_indep_inputs_n`: `P |= InputRV _|_ VarRV`
- `joint_eq_input_n`: a technical condition on joint probabilities

The plan's Lemma #21 (`dsdp_centropy_n_concrete`) is rated "Hard" — this is **underrated**. It should be "Very Hard" because:

1. You need to define `P_dsdp` such that `VarRV` is **uniform** (not just a projection from a product distribution). But `VarRV` is the relay values `v_relay`, which in the real protocol are chosen independently and uniformly — so this is achievable if `T_dsdp` includes `v_relay` as an independent uniform component.

2. The `constraint_fiber_n` hypothesis requires `VarRV t \in dsdp_fiber_fn_n (CondRV t)` for ALL `t`. This means the algebraic constraint `s - u0*v0 = \sum u_i * v_relay_i` must hold at every sample point. If `S` is defined as a derived RV (`S := fun t => \sum u_i(t) * v_relay_i(t) + u0(t) * v0(t)`), this holds by definition. The plan's Recommendation (b) on "S as derived RV" (Question 3, line 309) is correct here.

3. The `joint_eq_input_n` hypothesis is subtle: it says the joint distribution of `(VarRV, CondRV)` equals that of `(VarRV, InputRV)` for fiber members. This requires careful construction of the distribution.

### Problem 2b: `E_relay` cannot be derived from `T_dsdp`

The plan acknowledges this (lines 216-224) but the resolution is unclear. Approach (a) — extending `T_dsdp` with independent `{ffun 'I_n_relay.+1 -> enc_msg}` — works for the security proof but makes the "bridge" to operational traces meaningless. If `E_relay` is just a fresh independent uniform RV, it has nothing to do with `enc(ek_j, v_relay_j, r1_relay_j)`.

**This is the fundamental tension the plan must resolve more clearly.** See Section 5 below.

---

## 3. E_relay Decoupling (Approach (a))

**Assessment: Logically sound for the security proof, but defeats the purpose of the bridge.**

The security section's hypotheses (`E_enc_unif`, `E_enc_inde`, `E_relay_indep_all`) say: encryptions are uniform and independent of everything. The approach (a) — making `E_relay` an independent component in a product distribution — trivially satisfies these hypotheses.

**But this raises a conceptual question**: what does the bridge actually prove?

With approach (a), the bridge would say: "There exists a probability space and RV definitions satisfying all hypotheses of `dsdp_security_n`, therefore the entropy bound holds." But it would NOT say: "The concrete operational execution's trace satisfies the entropy bound." The `E_relay` in the probability space would be unrelated to the actual ciphertexts in the operational trace.

**The plan recognizes this** (lines 248-265) but doesn't resolve it. The "operational_distributional_equiv" axiom (line 257) is the key missing piece, and it's left as an axiom.

**Recommendation**: The plan should be explicit that there are two distinct theorems:
1. **Instantiation theorem** (no axioms beyond `E_enc_unif`/`E_enc_inde`): "There exist concrete RVs satisfying all hypotheses of `dsdp_security_n`." This is achievable with approach (a).
2. **Operational security theorem** (requires IND-CPA axiom): "The entropy bound applies to the actual operational trace distribution." This requires either `cipher AHE : finType` + `rand AHE : finType`, or an external axiom.

The plan conflates these two theorems, which creates confusion about what is actually being proved.

---

## 4. `dsdp_centropy_n` Instantiation Difficulty

**Assessment: The plan rates this "Hard". I rate it "Very Hard — the hardest single item in the plan."**

To instantiate `dsdp_centropy_uniform_n`, you need ALL of:
- `VarRV_uniform_n`: VarRV uniformly distributed over `{ffun 'I_n_relay.+1 -> 'Z_m}`
- `VarRV_indep_inputs_n`: VarRV independent of `(v0, u0, u_relay_vec)`
- `constraint_fiber_n`: algebraic constraint holds at all sample points
- `joint_eq_input_n`: joint probability equality for fiber members

For a product distribution `P_dsdp` where `v_relay` is an independent uniform component:
- `VarRV_uniform_n` is a marginal uniformity lemma for a product distribution — Medium difficulty in infotheo (need to build the marginal projection and show it equals `fdist_uniform`)
- `VarRV_indep_inputs_n` follows from product structure — Medium
- `constraint_fiber_n` holds if `S` is derived — Easy
- `joint_eq_input_n` is the hardest: it requires showing `Pr[(VarRV, CondRV) = (var, cond)] = Pr[(VarRV, InputRV) = (var, input)]`. Since `CondRV = (v0, u0, u_rel, S)` and `InputRV = (v0, u0, u_rel)`, and `S` is determined by the other components, this is a conditional probability equality. It requires careful computation with the product distribution's probability mass function.

**Estimated effort for Lemma #21 alone: 200-400 lines.** The plan's overall estimate of 800-1200 lines is reasonable but tight.

---

## 5. Pointwise vs. Distributional

**Assessment: The plan correctly identifies this as distributional, but underestimates the implications.**

`trace_eavesdropper_security_n` (line 2208) gives:
```coq
`H(VarRV | AliceTraces_n) >= log ((m ^ n_relay)%:R : R)
```

This is a statement about the **distribution** `P` — specifically about the conditional entropy of `VarRV` given `AliceTraces_n`, both of which are RVs on `(T, P)`.

For the bridge to connect this to operational execution, you need to show that the operational trace, viewed as a random function of the protocol inputs, has the same distribution as `AliceTraces_n` under `P_dsdp`.

With approach (a) for `E_relay`, this is **impossible pointwise** — at a given sample point `w`, the operational trace contains `enc(ek_j, v_relay_j(w), r1_relay_j)` (a concrete ciphertext), while `AliceTraces_n(w)` contains an independent `enc_msg` value unrelated to actual encryption.

**The bridge can only work distributionally**, and only if:
- Either `cipher AHE : finType` and `rand AHE : finType` (so actual encryption can be modeled as a finType RV), or
- An IND-CPA axiom bridges the gap externally.

**Recommendation**: For a clean formalization, the strongest achievable result without new axioms is the **instantiation theorem** (item 1 from Section 3 above). To get operational security, either:
- (Best) Add `cipher_finType` and `rand_finType` hypotheses, make `E_relay j := fun w => enc(ek_j, v_relay_j(w), r1_relay_j(w))`, and prove `E_enc_unif`/`E_enc_inde` from a scheme-specific IND-CPA property.
- (Acceptable) State `operational_distributional_equiv` as a Section hypothesis (not an `Axiom`), clearly documenting it as the cryptographic assumption.

---

## 6. Missing Items and Dependencies

### 6a: CondRV construction is harder than stated

The plan lists `dsdp_CondRV` (Lemma #17) as "Easy (def)" — just a projection. But `CondRV` in `dsdp_security.v` is an abstract `Variable CondRV : {RV P -> CondT_n}`, and in `dsdp_entropy.v` it must satisfy `constraint_fiber_n`. So defining `CondRV` as `fun t => (V0 t, U0 t, U_relay_ffun t, S t)` where `S` is derived is straightforward, but **proving it satisfies the fiber constraint requires that S = u0*v0 + \sum u_i * v_i**, which links back to the protocol correctness.

This is actually fine if you define S as this sum, but the plan should be explicit about it.

### 6b: `InputRV` is missing from the plan entirely

`dsdp_centropy_uniform_n` requires an `InputRV : {RV P -> InputT_n}` satisfying `InputRV_proj_n` and `VarRV_indep_inputs_n` and `joint_eq_input_n`. The plan defines `dsdp_VarRV_indep_inputs` (Lemma #18) but doesn't define `InputRV` or prove `joint_eq_input_n`. This is a significant omission.

### 6c: `u_of_cond` preconditions

`dsdp_centropy_uniform_n` requires:
- `forall t, (0 < val (u_of_cond (CondRV t) ord_max))%N`
- `forall t, (val (u_of_cond (CondRV t) ord_max) < minn p q)%N`

These say the last relay's coefficient `u_{n+1}` is nonzero and less than `min(p,q)` at every sample point. The plan doesn't mention these preconditions at all. They must either be:
- Hypotheses of the bridge theorem (propagated from the protocol setup), or
- Proved from the distribution construction (if `u` coefficients are deterministic parameters).

In the operational code (`dsdp_trace_progress.v`), `u : 'I_n_relay.+2 -> plain AHE` is a Section variable — it's deterministic. So if `U_relay` in the sample space is a deterministic function (constant RV), these conditions become conditions on the coefficient values, which should be stated as hypotheses of the bridge.

### 6d: `Dk_a_indep_all` and `R_relay_RV_indep_all` and `E_relay_indep_all`

The security section requires three "independent of everything" hypotheses (lines 2068, 2073, 2106). The plan's approach (a) for `E_relay` handles `E_relay_indep_all` trivially (independent component). But `Dk_a_indep_all` and `R_relay_RV_indep_all` need to be proved from the product distribution — this is not listed in the plan's lemma table.

### 6e: Trace prefix characterization (Phase 3D-1) lacks key detail

The plan says `alice_trace_ciphers_concrete` (Lemma #1) gives an `(n_relay.+1).+1.-tuple (cipher AHE)`. But looking at the operational trace structure:
- AR phases produce `n_relay.+1` ciphertexts (one per relay)
- Tail phase produces 1 ciphertext
- Total: `n_relay.+2` ciphertexts

The plan says `(n_relay.+1).+1 = n_relay.+2` which is correct. But the indexing in Lemma #2 (`alice_cipher_at_AR`) uses `widen_ord ... j` for `j : 'I_n_relay.+1`, and Lemma #3 says `tnth cs ord_max` is the tail cipher. This assumes ciphertexts are ordered oldest-first in the tuple. But from `alice_trace_after_AR` (line 251 of `dsdp_trace_progress.v`), ciphertexts are prepended — so the trace is in **reverse chronological order**:
```
[cipher_j(n_relay); ...; cipher_j(0); d v0; priv_key dk]
```

The tuple indexing in the plan's lemmas may need to account for this reversal. This is not a showstopper but adds complexity.

---

## 7. Difficulty Rating Assessment

| Plan Rating | My Rating | Item | Reason |
|-------------|-----------|------|--------|
| Medium | Medium | Lemma 1 (alice_trace_ciphers_concrete) | Correct assessment |
| Medium | Medium-Hard | Lemma 2 (alice_cipher_at_AR) | Reverse order complicates indexing |
| Easy | Easy | Lemma 3 (alice_cipher_at_tail) | Correct |
| Medium-Hard | Medium | Lemma 6 (dsdp_inv_phase_sequence) | Already partially established by `dsdp_inv_step` |
| Medium | Easy (def) | Lemma 10 (dsdp_sample_space) | Correct |
| Medium | Medium-Hard | Lemma 11 (dsdp_distribution) | Product distribution with correct marginals |
| Medium | Medium | Lemma 18-20 (independence/uniformity) | Standard product distribution lemmas |
| Hard | **Very Hard** | Lemma 21 (dsdp_centropy_n_concrete) | Missing InputRV, joint_eq, u_of_cond preconditions |
| Easy | Easy | Lemma 22-26 (enc_msg, E_relay) | Correct for approach (a) |
| Hard/Axiom | **Axiom** | Lemma 28 (trace_cipher_ffun_correct) | Cannot be proved without finType hypotheses |
| Medium | Medium | Lemma 29-30 (operational_security) | Correct once bridge exists |

---

## 8. Design Decision Assessment

### Option 2 for enc_msg (party-labeled plaintext): **SOUND**
This is the right choice. It matches the existing security proof exactly.

### Option B for sample space (reduced, finType only): **SOUND with caveats**
Correct for the instantiation theorem. For operational security, need finType hypotheses on cipher/rand.

### Approach (a) for E_relay (independent uniform): **SOUND for instantiation, INSUFFICIENT for operational bridge**
The plan should clearly separate these two goals.

### S as derived RV (Question 3, Recommendation (b)): **CORRECT**
Essential for `constraint_fiber_n`.

### IND-CPA as Section hypothesis (Question 4, Recommendation (c)): **CORRECT**
Best approach for modularity.

---

## 9. Simpler Alternatives the Plan Missed

### Alternative A: Two-theorem approach (recommended)

Split the work into:
1. **`dsdp_security_instantiation`** (~500 lines): Define `T_dsdp`, `P_dsdp`, all RVs, prove all hypotheses of `dsdp_security_n`. This gives `H(VarRV | AliceTraces_n) >= log(m^n_relay)` for the abstract RVs. No axioms needed beyond `E_enc_unif`/`E_enc_inde` (which are Section hypotheses in the security proof).
2. **`dsdp_operational_security`** (~300 lines, requires axioms): Assuming `cipher_finType` and `rand_finType`, define a richer sample space where `E_relay` comes from actual encryption, prove operational trace correspondence.

This separation clarifies what is proved vs. assumed and allows the first result to be completed independently.

### Alternative B: Skip the bridge entirely

The existing theorems already give:
- **Operational correctness**: the protocol computes `sum u_i * v_i` (proved)
- **Distributional security**: any eavesdropper's view has high conditional entropy (proved)

The "bridge" adds: "the concrete protocol execution IS the thing that's secure." In many formalizations, this connection is left as a standard argument. The plan could document this as a "future work" item and focus on Alternative A (instantiation), which already provides significant value.

### Alternative C: Paillier-specific bridge

For Paillier: `cipher = 'Z_(n^2)` (finType), `rand = {unit 'Z_(n^2)}` (finType). A Paillier-specific bridge avoids all the finType issues. This could serve as a proof-of-concept before attempting generalization.

---

## 10. Biggest Risks

1. **Risk: `joint_eq_input_n` proof** — This is the most technically challenging hypothesis to satisfy, and it's not even listed in the plan. Without it, `dsdp_centropy_uniform_n` cannot be instantiated.

2. **Risk: Product distribution infrastructure** — infotheo may not have convenient lemmas for constructing product distributions on large tuple types and proving marginal/independence properties. This could require 200+ lines of infrastructure.

3. **Risk: Conflation of instantiation vs. operational bridge** — If the plan proceeds with approach (a) for `E_relay`, the "bridge" to operational traces is vacuous. The plan should be clear about this to avoid wasted effort.

4. **Risk: The `u_of_cond` preconditions** — These constrain the coefficient distribution. If not handled, the final theorem will have unexpected hypotheses.

5. **Risk: Reverse trace ordering** — The operational trace is in reverse chronological order. The plan's tuple indexing assumes a specific order that needs to be verified against the actual trace accumulation.

---

## 11. Summary of Recommendations

1. **Split into two clear theorems**: instantiation (no new axioms) and operational bridge (requires finType/IND-CPA axioms). Prioritize instantiation.

2. **Add `InputRV` to the plan**: Define it, prove `InputRV_proj_n`, and especially `joint_eq_input_n`.

3. **Add `u_of_cond` preconditions**: Either as hypotheses of the bridge or derivable from the setup.

4. **Add `Dk_a_indep_all`, `R_relay_RV_indep_all` proof items**: Missing from the hypothesis verification phase.

5. **Upgrade Lemma #21 difficulty to "Very Hard"**: It subsumes multiple non-trivial proof obligations.

6. **Clarify that approach (a) for `E_relay` gives instantiation, NOT operational bridge**: The plan currently suggests it gives both.

7. **Consider Paillier-specific bridge as a first milestone**: Avoids finType issues entirely.

8. **Verify trace ordering before committing to tuple indexing**: The reverse-chronological accumulation in `alice_trace_after_AR` may affect Phase 3D-1 lemma signatures.

9. **Estimated total effort**: 1000-1500 lines (plan says 800-1200; I think this underestimates the distribution infrastructure and `joint_eq_input_n`).
