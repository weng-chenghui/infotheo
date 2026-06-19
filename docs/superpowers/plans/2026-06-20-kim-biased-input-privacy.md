# Kim biased-cut input privacy — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove `kim_input_private`: under Kim's biased cut, a partial card view leaks `O(eps^2)` conditional mutual information about the individual inputs `(a,b)` given the output `a&&b`, recovering den Boer's exact zero at `eps=0`.

**Architecture:** One new file `pgg-smc/instances/kim2025/kim_input_privacy.v`. Build a biased joint law `kim_input_dist` over `bool*bool*'I_5`; reduce `cond_mutual_info` to the output-0 fibre via `cond_mutual_infoE2`; bound each fibre KL term by `chi2` (helper `le_div_chi2`) using the reused combinatorial core `den_boer_view_count_eq` and the weight deviation `|w_k - 1/5| <= |eps|`.

**Tech Stack:** Rocq 9.0, MathComp 2.5, mathcomp-analysis 1.15, infotheo. Proving driven by the `mathcomp-skills` skill + `rocq-mcp` (4-phase loop). Commits skip rocq-audit Stage 2 via `ROCQ_AUDIT_BYPASS=fast`.

**Conventions for every task below:**
- Iterate with `rocq-mcp` (`rocq_start` → `rocq_query` Search → `rocq_step_multi` battery → `rocq_check` commit → `rocq_assumptions`). Max 2 full-file `make` builds per task.
- "Compiles" = `make -j1 pgg-smc/instances/kim2025/kim_input_privacy.vo` exits 0 (or `rocq_compile_file`).
- Commit with: `ROCQ_AUDIT_BYPASS=fast git add <file> && ROCQ_AUDIT_BYPASS=fast git commit -m "<msg>"`.
- A lemma stated with `Admitted.` is the "red" state; the same lemma `Qed.` with the file compiling is "green".

---

## File Structure

- Create: `pgg-smc/instances/kim2025/kim_input_privacy.v` — the entire deliverable.
- Reuses (no edits): `five_card_kim.v` (`kim_weight_dist`, `kim_weight_distE`, positivity hyps), `five_card_leakage.v` (`Omega`, `arr`, `Secret`, `ViewA`, `stepO`, `count_pr`), `den_boer_encoding.v` (`Inputs`, `den_boer_view_count_eq`), infotheo `entropy.v` (`cond_mutual_info`, `cond_mutual_infoE2`, `cdiv1`, `cdiv1_is_div`), `lib/realType_ln.v` (`ln_id_cmp`).
- Register in `_CoqProject` if the build does not auto-discover it (check first; the dir is already mapped to `pgg_smc`).

---

### Task 1: Scaffold — biased joint law, RVs, and the Admitted statement

**Files:**
- Create: `pgg-smc/instances/kim2025/kim_input_privacy.v`

- [ ] **Step 1: Write the header + imports + section skeleton.** Paste the verbatim header from the spec (§4). Imports:

```coq
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset bigop ssralg ssrnum reals.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
From pgg_smc Require Import five_card_leakage den_boer_encoding five_card_kim.
Import GRing.Theory Num.Theory.
Set Implicit Arguments. Unset Strict Implicit. Import Prenex Implicits.
Local Open Scope fdist_scope. Local Open Scope proba_scope.
Local Open Scope entropy_scope. Local Open Scope ring_scope.
Section kim_input_privacy. Variable R : realType.
Variable eps : R.
Hypothesis eps_lt_inv5 : eps < 5%:R^-1.
Hypothesis eps_gt_neg4inv5 : - (4%:R * 5%:R^-1) < eps.
```

- [ ] **Step 2: Define `kim_input_dist` and the RVs.**

```coq
Definition kim_input_dist : R.-fdist Omega :=
  (fdist_uniform (card_bool2)) `x (kim_weight_dist eps_lt_inv5 eps_gt_neg4inv5).
(* bool*bool uniform `x Kim cut law; confirm the product constructor name/order *)
Definition kim_inputs : {RV kim_input_dist -> bool * bool} :=
  fun w => let: (a, b, _) := w in (a, b).
Definition kim_secret : {RV kim_input_dist -> bool} :=
  fun w => let: (a, b, _) := w in a && b.
Definition kim_view (A : seq nat) : {RV kim_input_dist -> (size A).-tuple bool} :=
  fun w => map_tuple (fun i => nth false (arr w) i) (in_tuple A).
```

Use `rocq_query` to confirm: the fdist product notation (`` `x `` vs `fdist_prod`), the `bool*bool` uniform card lemma name, and the exact applied form of `kim_weight_dist` after section discharge. Fix names until it typechecks.

- [ ] **Step 3: State the headline as `Admitted`.**

```coq
Lemma kim_input_private (A : seq nat) :
  cond_mutual_info (`p_ [% kim_inputs, kim_view A, kim_secret]) <= kim_leak_bound eps.
Admitted.
```

For Step 3 to typecheck, a provisional `kim_leak_bound` must exist; add a stub
`Definition kim_leak_bound (e : R) : R := (3%:R / 4%:R) * e ^+ 2 / (5%:R^-1 - `|e|).`
(final form refined in Task 5). End the section.

- [ ] **Step 4: Verify it compiles.** Run `make -j1 pgg-smc/instances/kim2025/kim_input_privacy.vo`. Expected: PASS (one `Admitted` warning). If `kim_input_dist`/RVs do not typecheck, this is the first place a *design defect* (wrong product constructor, RV-over-fdist mismatch) would surface — fix names via `rocq_query`/`Search`, or report if the joint law cannot be formed.

- [ ] **Step 5: Commit.**

```bash
ROCQ_AUDIT_BYPASS=fast git add pgg-smc/instances/kim2025/kim_input_privacy.v
ROCQ_AUDIT_BYPASS=fast git commit -m "kim: scaffold biased-cut input-privacy file (Admitted statement)"
```

---

### Task 2: Reduce `cond_mutual_info` to the output-0 fibre

**Files:** Modify `kim_input_privacy.v` (inside the section).

- [ ] **Step 1: State the singleton-fibre fact (`Admitted`).**

```coq
Let PQR (A : seq nat) := `p_ [% kim_inputs, kim_view A, kim_secret].
Fact cdiv1_secret_true0 (A : seq nat) : cdiv1 (PQR A) true = 0.
Admitted.
```

Strategy: `Secret = true` forces `Inputs = (1,1)` (singleton fibre), so the
conditional joint equals its product; `cdiv1_is_div` + `div0` on a point-mass.
Explore the conditional-distribution API with `rocq_query Search cdiv1`.

- [ ] **Step 2: State the reduction (`Admitted`).**

```coq
Fact kim_cond_mutual_infoE (A : seq nat) :
  cond_mutual_info (PQR A) = (3%:R / 4%:R) * cdiv1 (PQR A) false.
Admitted.
```

Strategy: `cond_mutual_infoE2` expands to `\sum_(s:bool) PQR2 s * cdiv1 (PQR A) s`;
`big_bool`/`big_ord_recr` to two terms; kill the `true` term with
`cdiv1_secret_true0`; show `PQR2 false = 3/4` (`Pr[Secret=false]=3/4`, the
uniform-input prior, independent of the cut weights).

- [ ] **Step 3: Prove both** via `rocq-mcp` (battery: `rewrite cond_mutual_infoE2`, `big_bool`, `cdiv1_secret_true0`). Replace `Admitted` with the found scripts.

- [ ] **Step 4: Compile.** `make -j1 ...vo`. Expected PASS.

- [ ] **Step 5: Commit.**

```bash
ROCQ_AUDIT_BYPASS=fast git add pgg-smc/instances/kim2025/kim_input_privacy.v
ROCQ_AUDIT_BYPASS=fast git commit -m "kim: cond_mutual_info reduces to (3/4)*cdiv1 false"
```

---

### Task 3: The `D <= chi2` helper

**Files:** Modify `kim_input_privacy.v`.

- [ ] **Step 1: Define `chi2_div` and state `le_div_chi2` (`Admitted`).**

```coq
Definition chi2_div (T : finType) (p q : T -> R) : R :=
  \sum_(v in T) (p v - q v) ^+ 2 / q v.
Fact le_div_chi2 (T : finType) (p q : R.-fdist T) :
  (forall v, 0 < q v) ->
  \sum_(v in T) p v * log (p v / q v) <= chi2_div p q / ln 2%:R.
Admitted.
```

(Adjust the LHS to match infotheo's `div`/`D(_||_)` once located via
`rocq_query Search "div" "fdist"`; the divergence is `\sum p * log (p/q)`.)

- [ ] **Step 2: Prove it.** Pointwise `log x = ln x / ln 2` and `ln_id_cmp : 0<x -> ln x <= x-1`, applied to `x = (p v)/(q v)`, gives `p*log(p/q) <= p*((p/q)-1)/ln2 = ((p^2/q) - p)/ln2`; sum and use `\sum p = 1` so `\sum(p^2/q - p) = \sum (p-q)^2/q = chi2`. `rocq-mcp` battery + `Search ln_id_cmp log ler_sum`.

- [ ] **Step 3: Compile.** Expected PASS.

- [ ] **Step 4: Commit.**

```bash
ROCQ_AUDIT_BYPASS=fast git add pgg-smc/instances/kim2025/kim_input_privacy.v
ROCQ_AUDIT_BYPASS=fast git commit -m "kim: D <= chi2 divergence helper (le_div_chi2)"
```

---

### Task 4: Per-view deviation and positivity

**Files:** Modify `kim_input_privacy.v`. Reuses `den_boer_view_count_eq`.

- [ ] **Step 1: State the conditional view prob + deviation (`Admitted`).**

```coq
(* q_x v = Pr[view = v | Inputs = x] = sum of W_eps over cuts realising v *)
Fact kim_view_le (A : seq nat) (x : bool * bool) (v : (size A).-tuple bool) :
  `| `Pr_(PQR A) [ [set (x,v)] | ...secret... ] - ...n_v/5... | <= 2%:R * `|eps|.
Admitted.
Fact kim_qbar_gt0 (A : seq nat) (v : (size A).-tuple bool) :
  0 < ...qbar v....
Admitted.
```

The `...` placeholders are pinned in Step 2 once the conditional-probability
API (`jfdist_cond`, `\Pr_`, `cpr_eq`) is fixed via `rocq_query`. The content:
`q_x v - n_v/5 = \sum_(k in S_x v) (W_eps k - 1/5)`, bounded by `\sum |W_eps - 1/5| = 2|eps|`;
`|S_x v| = n_v` is `den_boer_view_count_eq` (orbit count, distribution-free);
`qbar v >= 1/5 - |eps| > 0` from `eps_lt_inv5`.

- [ ] **Step 2: Fix the statements against the live API, then prove.** Use
`den_boer_view_count_eq` for the count equality; `kim_weight_distE` for
`W_eps k = 1/5 +/- ...`; triangle inequality `ler_norm_sum`.

- [ ] **Step 3: Compile.** Expected PASS.

- [ ] **Step 4: Commit.**

```bash
ROCQ_AUDIT_BYPASS=fast git add pgg-smc/instances/kim2025/kim_input_privacy.v
ROCQ_AUDIT_BYPASS=fast git commit -m "kim: per-view weight deviation <= 2|eps| and qbar positivity"
```

---

### Task 5: Assemble the bound and prove `kim_input_private`

**Files:** Modify `kim_input_privacy.v`.

- [ ] **Step 1: Finalise `kim_leak_bound` and its properties (`Admitted`).**

```coq
(* kim_leak_bound already stubbed in Task 1; keep or refine the constant. *)
Fact kim_leak_bound0 : kim_leak_bound 0 = 0.
Admitted.
Fact kim_leak_bound_ge0 : 0 <= kim_leak_bound eps.
Admitted.
```

`kim_leak_bound0`: `0^+2 = 0` then `mul0r`. `kim_leak_bound_ge0`: numerator
`>=0`, denominator `5^-1 - |eps| > 0` in the Kim regime (`eps_lt_inv5` plus the
lower bound).

- [ ] **Step 2: Prove `kim_input_private`** by chaining: `kim_cond_mutual_infoE`
(`= (3/4)*cdiv1 false`) → `cdiv1_is_div` rewrites `cdiv1 false` as a sum of
`D(q_x || qbar)` → `le_div_chi2` per `x` → `kim_view_le` + `kim_qbar_gt0` bound
each `chi2` term by `C*eps^2/(5^-1-|eps|)` → arithmetic to `kim_leak_bound eps`.
Replace the Task 1 `Admitted`. If the emergent constant differs from the Task 1
stub, adjust `kim_leak_bound` (and re-check `kim_leak_bound0/_ge0`).

- [ ] **Step 3: Compile.** Expected PASS, no `Admitted` remaining except
`kim_input_private0` (Task 6).

- [ ] **Step 4: Commit.**

```bash
ROCQ_AUDIT_BYPASS=fast git add pgg-smc/instances/kim2025/kim_input_privacy.v
ROCQ_AUDIT_BYPASS=fast git commit -m "kim: prove kim_input_private (I(inputs;view|secret) <= O(eps^2))"
```

---

### Task 6: Unbiased limit + axiom hygiene

**Files:** Modify `kim_input_privacy.v`.

- [ ] **Step 1: State and prove `kim_input_private0` (`Admitted` first).**

```coq
(* At eps = 0 the bound is 0, so the conditional MI is exactly 0. *)
Lemma kim_input_private0 (A : seq nat) (Heps0 : eps = 0) :
  cond_mutual_info (`p_ [% kim_inputs, kim_view A, kim_secret]) = 0.
Admitted.
```

Strategy: `cond_mutual_info_ge0` gives `>= 0`; `kim_input_private` with
`kim_leak_bound0` (under `eps=0`) gives `<= 0`; `le_anti`. Cross-check that the
statement matches `den_boer_input_private`'s shape.

- [ ] **Step 2: Compile + axiom check.** `make -j1 ...vo`; then
`rocq_assumptions name="kim_input_private" file="...kim_input_privacy.v"`.
Expected: only `funext`/`propext`/`constructive_indefinite_description` (the
boolp trio), no project axioms. If a stray axiom appears, that is a defect —
trace and remove.

- [ ] **Step 3: Style review.** Run `/mathcomp-review pgg-smc/instances/kim2025/kim_input_privacy.v` and the `mathcomp-style-auditor`; fix findings (line length, naming, `by`/`exact:`).

- [ ] **Step 4: Final commit.**

```bash
ROCQ_AUDIT_BYPASS=fast git add pgg-smc/instances/kim2025/kim_input_privacy.v
ROCQ_AUDIT_BYPASS=fast git commit -m "kim: unbiased limit kim_input_private0 + axiom-clean"
```

---

## Self-Review

- **Spec coverage:** Task 1 (kim_input_dist, RVs, header, statement) ↔ spec §4-7; Task 2 (reduction, singleton fibre) ↔ §8.1-8.2; Task 3 (le_div_chi2) ↔ §6/§8.5; Task 4 (deviation, qbar) ↔ §8.3-8.4; Task 5 (assemble) ↔ §7/§8.5; Task 6 (eps=0, axioms) ↔ §7/§11. All spec sections mapped.
- **Names:** `kim_input_dist`, `kim_inputs`, `kim_secret`, `kim_view`, `chi2_div`, `kim_leak_bound`, `kim_input_private`, `kim_input_private0`, `le_div_chi2`, `kim_cond_mutual_infoE`, `cdiv1_secret_true0`, `kim_view_le`, `kim_qbar_gt0`, `kim_leak_bound0`, `kim_leak_bound_ge0` — match the audited spec list (with `kim_view_le`).
- **Known soft spots (resolve during execution, report if blocking):** exact infotheo product-fdist constructor and conditional-probability API (`jfdist_cond`/`\Pr_`/`cdiv1` argument order); the precise `kim_leak_bound` constant; whether `den_boer_view_count_eq` is stated over the right `Inputs`/`ViewA` to reuse directly under `kim_input_dist`.
