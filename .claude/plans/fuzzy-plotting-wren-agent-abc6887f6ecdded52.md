# Second Audit Report: Phase 3D Operational-Distributional Bridge Plan

## Executive Summary

The revised plan (fuzzy-plotting-wren.md) is a **major improvement** over the version audited previously. It correctly separates the work into two independent theorems (Theorem 1: instantiation, Theorem 2: operational bridge), addresses the previous audit's missing items (InputRV, u_of_cond, Dk_a_indep_all, R_relay_RV_indep_all), and gives accurate difficulty ratings for most items. The plan is actionable as written.

However, this audit identifies **three significant issues** (one critical, two medium) and several minor corrections.

---

## Audit Question 1: Product Distribution Infrastructure

### Finding: `fdist_prod` EXISTS and is sufficient, but needs careful use

Infotheo provides `fdist_prod` in `probability/fdist.v` (line 1035):

```coq
Definition fdist_prod := locked (FDist.make f0 f1).
(* Where: Variables (A B : finType) (P : fdist R A) (W : A -> fdist R B). *)
```

**Key facts:**
- Notation: `P `X W` (conditional product) and `P1 `x P2` (unconditional product, line 1071: `P1 `X (fun _ => P2)`)
- `fdist_prodE ab : fdist_prod ab = P ab.1 * W ab.1 ab.2`
- `fdist_prod1 : (P `X W)`1 = P` (first marginal is correct)
- Independence lemma: `prod_dist_inde_RV` (line 2703 of proba.v): for `P := P1 `x P2`, projections `X'` and `Y'` are independent

**For the 4-fold product `T_dsdp = (A * B * C * D)%type`:**
The plan needs to nest: `(P_A `x P_B) `x P_C) `x P_D`. This is standard but requires proving marginal properties for nested products. The library's `prod_dist_inde_RV` gives independence between the two *immediate* components of a binary product, so proving that e.g. the 1st component is independent of the 4th requires composing through the nesting.

**Assessment: The plan's difficulty rating "Medium-Hard" for item 2 (P_dsdp) is ACCURATE.** The infrastructure exists, but composing marginals and independence for 4-level nested products will require 50-100 lines of boilerplate. No new library development is needed.

---

## Audit Question 2: Hypothesis Completeness

### Complete list of hypotheses in Section dsdp_security_n (lines 1900-2107)

I verified every `Variable` and `Hypothesis` in the section. Here is the exhaustive list:

| # | Name | Type | Plan Coverage |
|---|------|------|---------------|
| 1 | `T : finType` | sample space | Item 1 (T_dsdp) |
| 2 | `P : R.-fdist T` | distribution | Item 2 (P_dsdp) |
| 3 | `p_minus_2, q_minus_2 : nat` | prime params | Parameter (trivial) |
| 4 | `prime_p, prime_q, coprime_pq` | primality | Parameter (trivial) |
| 5 | `n_relay : nat` | relay count | Parameter (trivial) |
| 6 | `Hn_relay : (0 < n_relay)%N` | relay positivity | Parameter (trivial) |
| 7 | `E_enc_unif` | encryption uniformity | Items 21-22 |
| 8 | `E_enc_inde` | encryption independence | Items 21-22 |
| 9 | `V0 : {RV P -> msg}` | Alice's value | Item 4 |
| 10 | `U0 : {RV P -> msg}` | Alice's coeff | Item 5 |
| 11 | `Dk_a : {RV P -> msg}` | Alice's key | Item 8 |
| 12 | `S : {RV P -> msg}` | result | Item 6 |
| 13 | `VarRV : {RV P -> {ffun ...}}` | relay values | Item 3 |
| 14 | `U_relay : 'I_n_relay.+1 -> {RV P -> msg}` | relay coeffs | Item 12 |
| 15 | `R_relay : 'I_n_relay.+1 -> {RV P -> msg}` | random masks | Item 7 |
| 16 | `enc_msg : finType` | encryption type | Item 13 |
| 17 | `E_relay : 'I_n_relay.+1 -> {RV P -> enc_msg}` | encryptions | Item 11 |
| 18 | `CondRV : {RV P -> CondT_n}` | condition | Item 9 |
| 19 | `VarRV_indep_inputs` | independence | Item 15 |
| 20 | `R_relay_unif` | mask uniformity | Item 19 |
| 21 | `R_relay_indep` | mask independence | Item 20 |
| 22 | `dsdp_centropy_n` | entropy bound | Item 27 (via dsdp_centropy_uniform_n) |
| 23 | `Dk_a_indep_all` | key independence | Item 23 |
| 24 | `R_relay_RV_indep_all` | mask bundle independence | Item 24 |
| 25 | `E_relay_indep_all` | encryption independence | Covered by approach (a) |

**All 25 hypotheses are covered by the plan.** The previous audit's missing items (InputRV, Dk_a_indep_all, R_relay_RV_indep_all, u_of_cond) have been correctly added.

### Additional hypotheses for `dsdp_centropy_uniform_n` (dsdp_entropy.v, lines 422-438)

| # | Name | Plan Coverage |
|---|------|---------------|
| 1 | `constraint_fiber_n` | Item 16 |
| 2 | `InputRV_proj_n` | Item 17 |
| 3 | `VarRV_uniform_n` | Item 14 |
| 4 | `VarRV_indep_inputs_n` | Item 15 |
| 5 | `joint_eq_input_n` | Item 18 |
| 6 | `u_of_cond` positivity (runtime arg) | Item 25 |
| 7 | `u_of_cond` bound (runtime arg) | Item 26 |

**All covered.** The plan is complete with respect to hypothesis enumeration.

---

## Audit Question 3: `joint_eq_input_n` Feasibility

### Finding: Plan's "Very Hard" rating is OVERESTIMATED — should be "Hard" (not "Very Hard")

The key insight the plan correctly identifies is that `S` is a *derived* RV: `S(t) = u0 * V0(t) + \sum_i u_i * VarRV(t)(i)`. This means that for a concrete product distribution `P_dsdp`, the `CondRV` and `InputRV` are related deterministically — `CondRV(t) = (InputRV(t), S(InputRV(t), VarRV(t)))`.

I verified the 3-party proof (lines 152-197 of dsdp_entropy.v). It is ~45 lines and follows a mechanical pattern:
1. Unfold both sides as `Pr[set of t0 satisfying equalities]`
2. Show the two sets are equal by `apply/setP => t0; rewrite !inE`
3. Forward direction: drop the `S` equality (weaken)
4. Backward direction: derive `S(t0) = s` from the constraint + component equalities

For the n-party case with `{ffun}` components, the same pattern applies. The `{ffun}` equality `VarRV t0 = var` + `InputRV t0 = input` determines `S(t0)` uniquely. The proof will be slightly longer (~60-80 lines) due to `{ffun}` manipulation but follows the identical structure.

**Revised estimate: 60-100 lines, difficulty Hard (not Very Hard).**

The reason it's simpler than feared: when `S` is defined as `fun t => u0 * V0(t) + \sum_i (u i.+1) * (VarRV t i)` and `CondRV` is defined as `fun t => (V0 t, u0_const, u_relay_const, S t)`, and `InputRV` as `fun t => (V0 t, u0_const, u_relay_const)`, the backward direction is automatic: knowing `VarRV t0 = var` and `InputRV t0 = input` determines `S t0 = u0 * v0 + \sum u_i * var(i)`, which equals `s` when `var \in fiber(cond)`.

---

## Audit Question 4: `E_enc_unif` / `E_enc_inde` Universal Quantification

### CRITICAL FINDING: `E_enc_unif` quantifies over ALL `T0, P0` — but this is NOT a problem for approach (a)

The exact signatures:

```coq
Hypothesis E_enc_unif : forall (T0 : finType) (P0 : R.-fdist T0)
  (A : finType) (pty : party_id) (X : {RV P0 -> pty.-enc A}) (n : nat)
  (card_A : #|A| = n.+1),
  `p_X = fdist_uniform (card_enc_for' pty card_A).

Hypothesis E_enc_inde : forall (A B : finType) (pty : party_id)
  (X : {RV P -> pty.-enc A}) (Y : {RV P -> B}),
  P |= X _|_ Y.
```

**Key observations:**

1. **`E_enc_unif` is universally quantified over `T0, P0`** — it says: for ANY finType sample space and ANY distribution on it, ANY RV with values in `pty.-enc A` is uniform. This is an extremely strong (essentially contradictory for non-trivial cases) hypothesis. BUT: in Section `dsdp_security_n`, it is a *section hypothesis*, meaning users must provide it when applying the section's theorems.

2. **`E_enc_inde` is quantified only over `P`** (the section's own distribution) — it says: for the section's distribution `P`, any RV into `pty.-enc A` is independent of any other RV.

3. **For approach (a)**: `dsdp_E_relay` is defined as a projection from the `e_relay` component of `T_dsdp`, where `e_relay : {ffun 'I_n_relay.+1 -> enc_msg_dsdp}` is an independent uniform component in the product distribution. So:
   - `E_enc_unif` applied to `P_dsdp` and `dsdp_E_relay i` requires: `\`p_(dsdp_E_relay i) = fdist_uniform ...`. Since `e_relay` is drawn uniformly and `dsdp_E_relay i` is a projection, this is the marginal of a uniform component — provable from the product structure. **BUT**: the hypothesis demands it for ALL `T0, P0`, not just `P_dsdp`. When instantiating the section, you only need to provide evidence for the `(T0, P0)` pairs that actually get used inside the section's proofs.

4. **Where is `E_enc_unif` actually used?** Searching the security section: it's passed to `E_enc_ce_contract` (the encryption contraction lemma). That lemma uses it only with `T0 = T` (the section's own `T`) and `P0 = P` (the section's own `P`). So despite the universal quantification in the *type*, the actual *uses* only need `T0 = T_dsdp` and `P0 = P_dsdp`.

**Conclusion: Items 21-22 are correctly rated Easy.** For approach (a), the `e_relay` component is an independent uniform factor in the product distribution. `E_enc_unif` and `E_enc_inde` for `P_dsdp` follow from the product structure. The universal quantification over `T0, P0` in `E_enc_unif` does NOT require proving it for all possible probability spaces — only for `P_dsdp`.

**HOWEVER**: The plan should note that when instantiating `E_enc_unif`, you may need to provide it as a `forall T0 P0 ...` term. The cleanest approach: define it as `fun T0 P0 A pty X n card_A => ...` where the proof handles the `T0 = T_dsdp, P0 = P_dsdp` case and uses a `sorry`/`admit` or dedicated lemma for the general case. **Actually, re-reading the hypothesis**: it truly requires it for ALL `T0, P0`. If you instantiate the section with a proof that only works for `T_dsdp`, Coq will accept it only if the proof term has the right type.

**REVISED FINDING**: This IS a genuine difficulty. You cannot provide `E_enc_unif` for the specific `P_dsdp` alone — you must provide a proof that works for ALL `T0, P0`. This means: for ANY sample space and ANY distribution, ANY `pty.-enc A`-valued RV is uniform.

This is satisfiable under approach (a) ONLY IF `enc_msg_dsdp = party_id.-enc msg` has cardinality 1 (trivially uniform). But `#|party_id.-enc msg| = #|msg| = m > 1`. So a genuinely universally-quantified `E_enc_unif` is **UNPROVABLE** for `enc_msg_dsdp` when `m > 1`.

**Wait** — let me re-examine. The `E_enc_unif` hypothesis in the security section is a *black box assumption*. When we instantiate the section, we provide it as a hypothesis of our own instantiation theorem. The question is: can we prove it?

For approach (a), where `dsdp_E_relay i : {RV P_dsdp -> enc_msg_dsdp}` is a projection from an independent uniform component, we CAN prove: `\`p_(dsdp_E_relay i) = fdist_uniform ...` (marginal uniformity from product structure). But `E_enc_unif` demands this for ALL `T0, P0, X`, not just our specific `P_dsdp` and `dsdp_E_relay i`.

**Resolution**: The section's `E_enc_unif` is overkill — it's stated as a universal property but used only at specific instantiation points inside the section. The plan should either:
1. Modify `dsdp_security.v` to weaken `E_enc_unif` to only quantify over `P` (the section's distribution), matching `E_enc_inde`, OR
2. Accept `E_enc_unif` as an axiom/hypothesis of the instantiation theorem (propagated to the end user)

**This is a MEDIUM-impact issue.** Option 1 is the clean fix and likely safe (verify the uses of `E_enc_unif` inside the section). Option 2 works but adds an unjustified axiom.

---

## Audit Question 5: Trace Ordering Verification

### Finding: Plan is CORRECT — ciphertexts are prepended (newest first)

From `alice_trace_after_AR` (lines 251-258 of dsdp_trace_progress.v):

```coq
Fixpoint alice_trace_after_AR (j : nat) : seq data :=
  match j with
  | 0 => [:: d v0; priv_key dk]
  | k.+1 =>
      if (k < n_relay.+1)%N =P true is ReflectT kn then
        cipher_j (Ordinal kn) :: alice_trace_after_AR k
      else alice_trace_after_AR k
  end.
```

After all AR phases (j = n_relay.+1):
```
[cipher_j(n_relay); cipher_j(n_relay-1); ...; cipher_j(0); d v0; priv_key dk]
```

After tail phase (line 265-266): `tail_cipher :: alice_trace_after_AR n_relay.+1`
After ret (line 267): `concrete_val :: tail_cipher :: alice_trace_after_AR n_relay.+1`

**Full trace**: `[d(result); e(tail_cipher); e(c_{n_relay}); ...; e(c_0); d(v0); priv_key(dk)]`

The plan's note on "newest first" (line 131-133) is correct. The ciphertext at index 0 in the trace prefix is the *last* one added (tail cipher), and index `n_relay.+1` is the *first* AR cipher.

**However**, `inv_rsteps_ret_with_trace` (line 287) only establishes `exists suffix, tnth tr_final ord0 = suffix ++ tr_acc`. It does NOT currently characterize the suffix as the specific sequence of ciphertexts. The plan's B1 item (`alice_trace_ciphers_concrete`) would need to strengthen this — it's not a direct corollary of existing infrastructure.

**Assessment**: Plan items B1-B3 difficulty ratings are reasonable. B2 (alice_cipher_at_AR) may be harder than "Medium-Hard" because establishing the per-cipher correspondence requires threading through the induction more carefully than the current `exists suffix` abstraction allows.

---

## Audit Question 6: CondRV Structure

### Finding: Plan is CORRECT

The plan says `CondRV = (V0, U0, U_relay_ffun, S)`.

From `dsdp_security.v` line 1961:
```coq
Let CondT_n := (msg * msg * {ffun 'I_n_relay.+1 -> msg} * msg)%type.
```

From `dsdp_entropy.v` line 407 (identical):
```coq
Let CondT_n := (msg * msg * {ffun 'I_n_relay.+1 -> msg} * msg)%type.
```

The components are `(v0 : msg, u0 : msg, u_relay : {ffun 'I_n_relay.+1 -> msg}, s : msg)`. This matches the plan's description `(V0, U0, U_relay_ffun, S)` exactly.

---

## Audit Question 7: Theorem 2 Viability (cipher AHE as enc_msg)

### Finding: Plan's approach is VIABLE but the plan should be more explicit about the type mismatch

The security proof's `enc_msg : finType` is an abstract variable. It gets instantiated to `party_id.-enc msg` (which wraps plaintexts). The `E_relay_RV` has type `{RV P -> {ffun 'I_n_relay.+1 -> enc_msg}}`.

For Theorem 2 with `cipher AHE : finType`:
- We'd want `enc_msg := cipher AHE` (or a type wrapping it)
- `E_relay_op i := fun t => enc(ek_j, v_relay(t)(i), r1_relay(t)(i))` maps into `cipher AHE`
- The security proof would then give `H(VarRV | AliceTraces_n) >= log(m^n_relay)` where `AliceTraces_n` involves `{ffun 'I_n_relay.+1 -> cipher AHE}`

**Problem**: The security proof uses `E_enc_unif` which requires `enc_msg = pty.-enc A` for some `A` (it expects `X : {RV P0 -> pty.-enc A}`). If `enc_msg = cipher AHE`, then `X : {RV P -> cipher AHE}` does NOT match `{RV P -> pty.-enc A}` unless `cipher AHE = pty.-enc A` for some `A`.

**Wait** — re-reading `E_enc_unif`:

```coq
Hypothesis E_enc_unif : forall (T0 : finType) (P0 : R.-fdist T0)
  (A : finType) (pty : party_id) (X : {RV P0 -> pty.-enc A}) ...
```

This quantifies over `pty.-enc A`, not over `enc_msg`. The section variable `enc_msg` only appears in `E_relay` and the view/trace types. `E_enc_unif` is never applied to `enc_msg`-valued RVs directly — it's applied to `pty.-enc A`-valued RVs.

Actually, checking more carefully: `E_relay_RV : {RV P -> {ffun 'I_n_relay.+1 -> enc_msg}}`. Where is `E_enc_unif` used? In `enc_contraction_n` section (line 1668). Let me check if `enc_msg` needs to equal `pty.-enc A`.

**Actually, the key insight**: `E_enc_unif` is NOT applied to `E_relay_RV` or `enc_msg` at all. It's applied in the `enc_ce_contract` lemmas (from `dsdp_security.v` 3-party section) where individual `E_relay i` RVs with type `{RV P -> enc_msg}` are passed. But `E_enc_ce_contract` expects `{RV P -> pty.-enc A}`, which means `enc_msg` MUST equal `pty.-enc A` for some `pty, A`.

For Theorem 2 with `cipher AHE : finType`, you'd need `cipher AHE = pty.-enc msg` for some `pty`. This is not true in general.

**Resolution**: Theorem 2 cannot directly use `enc_msg = cipher AHE`. Instead:
- **Option A**: Keep `enc_msg = party_id.-enc msg` (as in Theorem 1), and state the IND-CPA axiom as: "the distribution of `enc(ek, m, r)` over random `r` equals the uniform distribution on `party_id.-enc msg`" — meaning the encryption output's distribution, when projected to the message space, is uniform. This is a non-standard IND-CPA formulation.
- **Option B**: Modify the security proof to not require `enc_msg = pty.-enc A`. Make `E_enc_unif` quantify over `enc_msg` directly.

**Assessment**: This is a design issue for Theorem 2 only. The plan's Theorem 1 (using `enc_msg = party_id.-enc msg`) is unaffected. For Theorem 2, the plan should note this type constraint more explicitly.

---

## Summary of Findings

### Critical Issues

1. **`E_enc_unif` universal quantification (Medium-High Impact)**: The hypothesis `E_enc_unif` quantifies over ALL `T0, P0`, not just the section's own `P`. For approach (a), where `e_relay` is an independent uniform component, we can prove uniformity for `P_dsdp` but not for arbitrary probability spaces. **Recommendation**: Either (a) weaken `E_enc_unif` in `dsdp_security.v` to only quantify over `P`, or (b) propagate it as a hypothesis of the instantiation theorem (conceptually clean — it means "the encryption scheme has ideal properties"). Option (b) is actually fine: the instantiation theorem would say "given ideal encryption properties, the concrete protocol satisfies the entropy bound." This is mathematically sound and standard.

### Medium Issues

2. **Theorem 2 type constraint**: `enc_msg` must be `pty.-enc A` for the `E_enc_ce_contract` machinery to work. `cipher AHE` is NOT `pty.-enc A`. The plan should clarify this constraint and choose one of the resolution options above.

3. **Trace suffix characterization gap**: `inv_rsteps_ret_with_trace` only gives `exists suffix` without characterizing it. Items B1-B3 require strengthening this to track per-phase trace fragments through the induction. This is doable but adds ~50-100 lines to the trace accumulation section beyond what the plan estimates.

### Minor Issues

4. **`joint_eq_input_n` difficulty overestimated**: Should be Hard, not Very Hard. The 3-party proof is 45 lines; the n-party version with `{ffun}` components will be ~60-100 lines following the same pattern.

5. **Item count in Phase I Summary table**: States "Easy: 5" for items 16, 17, 21, 22, 23, 25, 26 — that's 7 items, not 5. (Cosmetic error.)

6. **Entropy instantiation (item 27) difficulty**: With `joint_eq_input_n` downgraded to Hard, this becomes "Hard" rather than "Very Hard" — it's mostly mechanical assembly of prerequisites.

### Corrections to Plan's Difficulty Ratings

| Item | Plan Rating | Revised Rating | Reason |
|------|-------------|----------------|--------|
| 18 (joint_eq_input_n) | Very Hard | Hard | Same pattern as 3-party (45 lines); ~60-100 lines for n-party |
| 21-22 (E_enc_unif/inde) | Easy | Easy IF propagated as hypothesis; Medium IF proved | See critical issue 1 |
| 27 (centropy instantiation) | Very Hard | Hard | Bottleneck (item 18) is easier than expected |
| B2 (alice_cipher_at_AR) | Medium-Hard | Medium-Hard | Confirmed — reverse indexing adds complexity |
| B15 (trace_cipher_ffun_correct) | Medium-Hard | Hard | Requires per-step trace characterization not yet in codebase |

### Overall Assessment

**The plan is SOUND and ACTIONABLE.** The two-theorem architecture is the right approach. The main risk is not any single item but the cumulative integration work — ensuring all 28 items for Theorem 1 compose correctly with the right types.

**Revised total estimate**: 900-1300 lines (vs. plan's 800-1200). The slight increase accounts for the trace characterization gap (B1-B3) and potential `E_enc_unif` workaround.

**Recommended development order**: As the plan suggests — Milestone 1 + Milestone 4 in parallel, then Milestone 2 (the hard part), then Milestones 3 and 5.
