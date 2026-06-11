# DSDP fiber-bound recomposition — implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: use `superpowers:subagent-driven-development` (recommended) or `superpowers:executing-plans` to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax. Rocq proof bodies marked "delegate" are dispatched to the `rocq-prover` agent (per `feedback_rocq_work_delegation`); the plan fixes the *statement* and *strategy*, the agent discovers the proof. Every task ends green (`rocq_check`/`coqc` exit 0) and is committed before the next starts (`feedback_atomic_tasks`).

**Goal:** Replace the degenerate leaked output `S = −(r2+r3)` with the genuine scalar product `u1·v1+u2·v2+u3·v3`, then discharge the information-theoretic fiber bound to prove `dsdp_alice_secrecy_leak_S : ∀ regular u3, Pr[Alice guesses V2] ≤ 1/m + 2·epsilon_cpa`.

**Architecture:** One DSDP game leaks two channels — ciphertexts (computational, `2·epsilon_cpa`, committed) and the output `S` (information-theoretic, `1/m`). The output `S` is recomposed as a plaintext computed from the input weights (theorem parameters seeded into the game env) and the secret samples, referencing a shared `dsdp_output`. The fiber `1/m` is instantiated from a `finComNzRingType`-generic fiber lemma (route F, no homomorphic-encryption library change), conditioned on `injective (fun v => u3 * v)`.

**Tech Stack:** Rocq + MathComp + Infotheo (`dsdp_entropy`) + SSProve (`Pr`, `pkg_composition`). Build: `coqc -R . infotheo` against `/Users/cheng-huiweng/Projects/coq/_opam`. Design spec: `dumas2017dual/notes/20260610-dsdp-fiber-bound-reflection-spec.md` (corrected 2026-06-11).

**Verify command (all tasks):**
```bash
cd /Users/cheng-huiweng/Projects/coq/infotheo-itp
/Users/cheng-huiweng/Projects/coq/_opam/bin/coqc -R . infotheo \
  -w -notation-overridden -w -ambiguous-paths -w -projection-no-head-constant \
  -w -redundant-canonical-projection -w -notation-incompatible-format \
  -w -notation-incompatible-prefix <FILE.v>
```
or `rocq_check` via the rocq MCP on the edited region (`feedback_rocq_check_is_done`). Pre-commit `rocq-auditor` is mandatory for tasks that add identifiers/proof bodies; cleanup-only tasks use `ROCQ_AUDIT_BYPASS=1` (`feedback_skip_audit_for_cleanup`).

**Files touched (responsibility):**
- `dumas2017dual/dsdp/dsdp_program.v` — the shared `dsdp_output` spec function + `alice_resultE`.
- `dumas2017dual/dsdp/dsdp_entropy.v` — route-F generalization of the ring fiber; `dsdp_g` → `dsdp_output`.
- `dumas2017dual/dsdp/dsdp_game_code.v` — parameter-seeded game env.
- `dumas2017dual/dsdp/dsdp_game_symbolic.v` — trace rebuild (output term + weights-as-parameters).
- `dumas2017dual/dsdp/dsdp_indcpa_security.v` — re-confirm the `2·epsilon_cpa` leg under the rebuilt game.
- `dumas2017dual/dsdp/dsdp_security_indcpa_fiber.v` — denotation lemma, four hypotheses, fiber bound, composition.
- `dumas2017dual/blueprint/src/it_leg_bridge.tex` — Part II green-flip.

---

## Phase 1 — Shared output function (no game dependency)

### Task 1: Define `dsdp_output`

**Files:** Modify `dumas2017dual/dsdp/dsdp_program.v` (add near `alice_result`, ~line 278).

- [ ] **Step 1: Add the definition** (probe-verified, `/tmp/output_probe.v`):

```coq
(* dsdp_output — the DSDP specification function: Alice's protocol output, the
   weighted scalar product of the two input vectors. *)
Definition dsdp_output {R : comNzRingType} (v1 u1 u2 u3 v2 v3 : R) : R :=
  u1 * v1 + u2 * v2 + u3 * v3.
```

- [ ] **Step 2: Verify** the file compiles (verify command on `dsdp_program.v`). Expected: exit 0.
- [ ] **Step 3: Audit + commit**

```bash
git add dumas2017dual/dsdp/dsdp_program.v
git commit -m "dsdp_program: shared dsdp_output spec function"
```

### Task 2: Bridge `alice_result` to `dsdp_output`

**Files:** Modify `dumas2017dual/dsdp/dsdp_program.v` (after the existing `alice_result = u1*v1+u2*v2+u3*v3` correctness lemma, ~line 282).

- [ ] **Step 1: State the bridge lemma** (`E`-suffix, no underscore):

```coq
(* alice_resultE — Alice's reconstruction equals the shared output spec. *)
Lemma alice_resultE : alice_result = dsdp_output v1 u1 u2 u3 v2 v3.
Proof. by rewrite dsdp_computes_dot_product /dsdp_output. Qed.
```

- [ ] **Step 2:** The correctness lemma is `dsdp_computes_dot_product` (`dsdp_program.v`, `alice_result = u1*v1+u2*v2+u3*v3`). The proof above is complete.
- [ ] **Step 3: Verify** (exit 0). **Step 4: Audit + commit** `-m "dsdp_program: alice_resultE bridges reconstruction to dsdp_output"`.

### Task 3: Re-express `dsdp_g` through `dsdp_output` (rename)

**Files:** Modify `dumas2017dual/dsdp/dsdp_entropy.v` (`dsdp_g` at line 295; all internal uses).

- [ ] **Step 1:** Rename `dsdp_g` → `dsdp_output_msg` is NOT wanted; instead define the local `dsdp_g` AS the shared function specialized to `msg`:

```coq
(* dsdp_output specialized to the entropy plaintext 'Z_m; the former dsdp_g. *)
Definition dsdp_output_zm (var : msg * msg) (inp : msg * msg * msg * msg) : msg :=
  let '(v2, v3) := var in let '(v1, u1, u2, u3) := inp in
  dsdp_output v1 u1 u2 u3 v2 v3.
```

- [ ] **Step 2:** Replace every `dsdp_g` occurrence in `dsdp_entropy.v` with `dsdp_output_zm` (grep: `grep -n dsdp_g dumas2017dual/dsdp/dsdp_entropy.v`). Keep `dsdp_fiber_eq_abstract`, `S_determined`, `dsdp_centropy_uniform` proofs working (they unfold `dsdp_g`; now unfold `dsdp_output_zm` then `dsdp_output`).
- [ ] **Step 3: Verify** the whole `dsdp_entropy.v` compiles (it is large; full `coqc`). Expected: exit 0. Delegate proof-repair to `rocq-prover` if unfolds break.
- [ ] **Step 4: Audit + commit** `-m "dsdp_entropy: route dsdp_g through shared dsdp_output (dsdp_output_zm)"`. Naming change is in-scope, not deferred (`feedback_naming_no_defer`).

---

## Phase 2 — Route-F entropy generalization (no game dependency)

### Task 4: Generalize the ring fiber-card to `finComNzRingType` + injective

**Files:** Modify `dumas2017dual/dsdp/dsdp_entropy.v` `Section dsdp_entropy_ring` (line 469): change `Variable R : finComUnitRingType` → `Variable R : finComNzRingType`, and `dsdp_fiber_card_ring` (line 482) hypothesis `u3 \is a GRing.unit` → `injective (fun v : R => u3 * v)`.

- [ ] **Step 1: Replace the card lemma** with the probe-verified proof (`/tmp/inj_route_probe.v`, adapted to the section's `dsdp_fiber_ring`):

```coq
Lemma dsdp_fiber_card_ring (u1 u2 u3 v1 s : R) :
  injective (fun v : R => u3 * v) ->
  #|dsdp_fiber_ring u1 u2 u3 v1 s| = #|R|.
Proof.
move=> Hinj.
have Hbij : bijective (fun v : R => u3 * v) by apply: (inj_card_bij Hinj).
case: Hbij => g Hg1 Hg2.
pose f := fun v2 : R => (v2, g (s - u1 * v1 - u2 * v2)).
have Hf_inj : injective f by move=> a b /=; case.
have Hf_image : [set f v2 | v2 : R] = dsdp_fiber_ring u1 u2 u3 v1 s.
  apply/setP => [[v2 v3]]; rewrite /dsdp_fiber_ring !inE.
  apply/imsetP/eqP.
  - by move=> [v2' _ [H1 H2]]; subst v2 v3; rewrite Hg2 addrC subrK.
  - move=> Heq; exists v2 => //=; congr pair.
    have Hv3 : u3 * v3 = s - u1 * v1 - u2 * v2 by rewrite -Heq addrC addKr.
    by rewrite -Hv3 Hg1.
by rewrite -Hf_image card_imset.
```

(Confirmed: `dsdp_fiber_ring (u1 u2 u3 v1 s) := [set vv | u2*vv.1 + u3*vv.2 == s - u1*v1]` matches the probe's `fiber_nz` field order exactly, so the `addrC subrK` / `addKr` steps transfer verbatim.)

- [ ] **Step 2: Verify** `dsdp_entropy.v` compiles through the changed section. Expected: exit 0.
- [ ] **Step 3: Audit + commit** `-m "dsdp_entropy: fiber-card over finComNzRingType + injective multiplier (route F)"`.

### Task 5: Generalize `Pr_dsdp_sol_uniform_ring` to the injective hypothesis

**Files:** Modify `dumas2017dual/dsdp/dsdp_entropy.v` `Pr_dsdp_sol_uniform_ring` (line 616) and any section hypotheses naming `u3 \is a GRing.unit`.

- [ ] **Step 1:** Replace the unit hypothesis on `u3` throughout the section's downstream lemmas with `injective (fun v : R => u3 * v)`; the body changes from `dsdp_fiber_card_ring`'s unit argument to the injective argument.
- [ ] **Step 2:** Strategy: the only consumer of the unit hypothesis was `dsdp_fiber_card_ring`; thread the injective hypothesis through. Delegate body repair to `rocq-prover`. Verify any existing `finComUnitRingType` caller of `Pr_dsdp_sol_uniform_ring` (`grep -rn Pr_dsdp_sol_uniform_ring dumas2017dual`) derives `injective` from `\is a GRing.unit` via `mulrI` (units are regular).
- [ ] **Step 3: Verify** full `dsdp_entropy.v` (exit 0). **Step 4: Audit + commit** `-m "dsdp_entropy: Pr_dsdp_sol_uniform_ring over injective multiplier"`.

---

## Phase 3 — Parameter-seeded env + game rebuild

### Task 6: Parameter-seeded game env

**Files:** Modify `dumas2017dual/dsdp/dsdp_game_code.v` (`empty_denv` ~line 306; `denote_game`/`denote_game_leak_S` initial-env call sites).

- [ ] **Step 1:** Add a seeded-env constructor that pre-loads weight values into `de_val` at fixed low indices:

```coq
(* seeded_denv — initial denotation env carrying the fixed input weights, so the
   trace can reference them without sampling. *)
Definition seeded_denv (ws : seq (gval AHE)) : denv AHE := MkDenv ws [::].
```

- [ ] **Step 2:** Generalize the game builders that currently call `empty_denv` to take an optional weight seed; the existing games pass `[::]` (= `empty_denv`) so they are unchanged. Strategy: thread a `seed : seq gval` parameter through `denote_game_leak_S` / `real_game_leak_S` / `zero_game_leak_S`. Delegate the threading + validity re-proof (`denote_run_valid`) to `rocq-prover`.
- [ ] **Step 3: Verify** `dsdp_game_code.v` + `dsdp_indcpa_security.v` compile (the existing games with empty seed must be definitionally unchanged so downstream proofs survive). Expected: exit 0.
- [ ] **Step 4: Audit + commit** `-m "dsdp_game_code: parameter-seeded game env (empty seed = prior behavior)"`.

### Task 7: Rebuild the trace — scalar-product output, weights as parameters

**Files:** Modify `dumas2017dual/dsdp/dsdp_game_symbolic.v` (`walk_obs_dsdp_leak_S` ~line 294, `obs_of_procs_dsdp_leak_S` ~line 444, `collect_samples` ~line 373, `dsdp_alice_obs_leak_S` ~line 506).

- [ ] **Step 1:** Change the `AO_recv_output` term from `Dec(agg) − r2 − r3 + u1·v1` to the scalar-product term `HE_add (HE_add (HE_mul u1 v1) (HE_mul u2 v2)) (HE_mul u3 v3)` over the seeded-weight indices and sampled-secret indices. The seed holds `u1,u2,u3,v1` at fixed indices; `v2,v3` are the samples.
- [ ] **Step 2:** Exclude `u1,u2,u3,v1` from `collect_samples` (they are seeded, not sampled): the sample prefix samples only `v2,v3` (`AO_sample_val card_msg`) and `r2,r3` (`AO_sample_val card_msg`; masks). Re-derive `dsdp_alice_obs_leak_S` and recompute `gc_eq`.
- [ ] **Step 3:** Re-prove the `by []` characterization lemmas (`walk_obs_dsdp_leak_S`, `obs_of_procs_dsdp_leak_S`) for the new trace; these close by computation. Delegate to `rocq-prover`; the new `gc_eq` is read off `vm_compute`.
- [ ] **Step 4: Verify** `dsdp_game_symbolic.v` (exit 0). **Step 5: Audit + commit** `-m "dsdp_game_symbolic: leak the scalar-product output; weights seeded not sampled"`.

### Task 8: Re-confirm the `2·epsilon_cpa` leg (R-2eps)

**Files:** `dumas2017dual/dsdp/dsdp_indcpa_security.v` (`dsdp_advantage_derived_leak_S` ~line 427+; `dsdp_obs_hops_leak_S`).

- [ ] **Step 1: Verify** `dsdp_obs_hops_leak_S` still computes to `2` (the output term added no hop). Run `coqc` on `dsdp_indcpa_security.v`.
- [ ] **Step 2:** Confirm `dsdp_advantage_derived_leak_S` (`AdvantageE real zero ≤ 2·epsilon_cpa`) still proves — `S` is now written identically in `real_game_leak_S`/`zero_game_leak_S` (a seeded-weight + sampled-secret plaintext computation, untouched by the hops), so the hop ladder is unchanged. Delegate any repair to `rocq-prover`.
- [ ] **Step 3: Verify** (exit 0). **Step 4: commit** `-m "dsdp_indcpa_security: re-confirm 2*epsilon_cpa under recomposed S"` (no new identifiers → audit-light).

---

## Phase 4 — Denotation lemma + the four hypotheses (fiber file)

### Task 9: `denote_output_termE`

**Files:** `dumas2017dual/dsdp/dsdp_security_indcpa_fiber.v` (in `Section dsdp_guess_distribution`, near `gc_eq`).

- [ ] **Step 1:** State and prove (probe-verified shape, `/tmp/output_probe.v`), with the real indices from Task 7's `gc_eq` and the seeded-weight indices:

```coq
Lemma denote_output_termE (e : denv AHE) :
  as_plain (denote_he pkey_of_party rand0 e output_term)
  = dsdp_output (as_plain (de_val_nth e iv1)) (as_plain (de_val_nth e iu1))
                (as_plain (de_val_nth e iu2)) (as_plain (de_val_nth e iu3))
                (as_plain (de_val_nth e iv2)) (as_plain (de_val_nth e iv3)).
Proof. by rewrite /dsdp_output //=. Qed.
```

- [ ] **Step 2:** Fill `output_term` and `iu1..iv3` from `gc_eq`. The proof is definitional (probe-confirmed) and index-agnostic.
- [ ] **Step 3: Verify** (exit 0; the fiber file is large — use `rocq_check` on the region or full `coqc`). **Step 4: Audit + commit** `-m "fiber: denote_output_termE (leaked S denotes to dsdp_output)"`.

### Task 10: `guess_sample_fdist` + `guess_S_determined`

**Files:** `dumas2017dual/dsdp/dsdp_security_indcpa_fiber.v`.

- [ ] **Step 1:** Define `guess_sample_fdist` over the sampled randomness `(V2,V3,r2,r3)` with the seeded weights as constants, and the RV projections `V2 V3 S guess` (mirroring `dsdp_entropy`'s naming). Statement-only spec; the construction is a `fdist_uniform` product composed with the predictor kernel.
- [ ] **Step 2:** State `guess_S_determined : S = (fun t => dsdp_output_zm (VarRV t) (InputRV t))` (the entropy-side `S_determined` shape) and prove via `denote_output_termE`. Delegate to `rocq-prover`.
- [ ] **Step 3: Verify** (exit 0). **Step 4: Audit + commit** `-m "fiber: guess_sample_fdist + guess_S_determined"`.

### Task 11: The remaining three hypotheses

**Files:** `dumas2017dual/dsdp/dsdp_security_indcpa_fiber.v`.

- [ ] **Step 1:** `guess_V2_uniform : `p_ [%V2,V3] = fdist_uniform card_msg_pair` — `(V2,V3)` are independent uniform samples.
- [ ] **Step 2:** `guess_VarRV_indep_inputs : P |= [%V1,U1,U2,U3] _|_ [%V2,V3]` — trivial since the inputs are constant (seeded weights); strategy: `fdist`-independence of a constant RV.
- [ ] **Step 3:** `guess_indep_V2_given_S : guess ⊥ V2 | S` — the predictor's output is framed off `V2_cell` by `Pr_fst_agree_locs` (committed). Delegate; this is the deepest of the three.
- [ ] **Step 4: Verify** (exit 0). **Step 5: Audit + commit** `-m "fiber: guess_V2_uniform, guess_VarRV_indep_inputs, guess_indep_V2_given_S"`.

---

## Phase 5 — Fiber bound + composition (fiber file)

### Task 12: `guess_fdist_success_le_invm`

**Files:** `dumas2017dual/dsdp/dsdp_security_indcpa_fiber.v`.

- [ ] **Step 1:** State `guess_fdist_success_le_invm : injective (fun v => u3 * v) -> guess_fdist_success <= (card_msg)%:R^-1`.
- [ ] **Step 2:** Instantiate the route-F entropy fiber (`Pr_dsdp_sol_uniform_ring` at `R := plain AHE`, from Task 5) with the four hypotheses (Tasks 10–11), bounding the `(guess,V2)` diagonal by `1/m` via `guess_indep_V2_given_S`. Delegate to `rocq-prover`. Cite `Pr_dsdp_sol_uniform_ring`, `dsdp_fiber_card_ring`.
- [ ] **Step 3: Verify** (exit 0). **Step 4: Audit + commit** `-m "fiber: guess_fdist_success_le_invm (the fiber 1/m)"`.

### Task 13: `guess_sdistr_success_le_invm`

**Files:** `dumas2017dual/dsdp/dsdp_security_indcpa_fiber.v`.

- [ ] **Step 1:** State `guess_sdistr_success_le_invm : injective (fun v => u3 * v) -> guess_sdistr_success <= (card_msg)%:R^-1`.
- [ ] **Step 2:** Prove: `rewrite guess_success_sdistr_eq_fdist` (committed connector), then `exact: guess_fdist_success_le_invm`.
- [ ] **Step 3: Verify** (exit 0). **Step 4: Audit + commit** `-m "fiber: guess_sdistr_success_le_invm via the connector"`.

### Task 14: `guess_advantage_le`

**Files:** `dumas2017dual/dsdp/dsdp_security_indcpa_fiber.v`.

- [ ] **Step 1:** State `guess_advantage_le : `|guess_sdistr_success_real − guess_sdistr_success_zero| <= 2 * epsilon_cpa` (carrying the predictor disjointness hypotheses `predictor_locs_disj`).
- [ ] **Step 2:** Re-associate `guessing_experiment = guessing_challenger ∘ par predictor game` into `(guessing_challenger ∘ predictor) ∘ game` (use committed `guess_resolved_par`/link lemmas), package `guessing_challenger ∘ predictor` as a `dsdp_indcpa_adversary`, then `eapply dsdp_advantage_derived_leak_S` (vanilla `eapply`, not `apply:`, per `feedback_ssprove_apply_vs_eapply`). Delegate to `rocq-prover`.
- [ ] **Step 3: Verify** (exit 0). **Step 4: Audit + commit** `-m "fiber: guess_advantage_le (2*epsilon_cpa between real/zero experiments)"`.

### Task 15: `dsdp_alice_secrecy_leak_S` (final theorem)

**Files:** `dumas2017dual/dsdp/dsdp_security_indcpa_fiber.v`.

- [ ] **Step 1:** State the final theorem, quantified over the weight parameters with the regularity precondition:

```coq
Theorem dsdp_alice_secrecy_leak_S (u1 u2 u3 v1 : plain AHE) :
  injective (fun v : plain AHE => u3 * v) ->
  guess_sdistr_success_real u1 u2 u3 v1 <= (card_msg)%:R^-1 + 2 * epsilon_cpa.
```

- [ ] **Step 2:** Prove by the triangle `Pr(real) ≤ Pr(zero) + |Pr(real) − Pr(zero)|`, then `guess_sdistr_success_le_invm` (Task 13) and `guess_advantage_le` (Task 14). Delegate to `rocq-prover`.
- [ ] **Step 3: Verify** (exit 0). Confirm axiom hygiene: `rocq_assumptions` shows no new custom axiom beyond `epsilon_cpa`/`enc_ind_cpa_real_or_zero`/`guess_lossless` (`feedback_audit_still_mandatory`).
- [ ] **Step 4: Audit + commit** `-m "fiber: dsdp_alice_secrecy_leak_S = 1/m + 2*epsilon_cpa (final)"`.

---

## Phase 6 — Cleanup + blueprint

### Task 16: Remove scaffolding and the superseded theorem

**Files:** Delete `dumas2017dual/dsdp/probe_fiber_reflection.v`, `dumas2017dual/dsdp/scratch_fiber_dev.v`; remove `dsdp_alice_secrecy` (replaced by `dsdp_alice_secrecy_leak_S`, `feedback_aggressive_cleanup_no_backcompat`); drop the three `/tmp/*probe*.v`.

- [ ] **Step 1:** Delete the files; `grep -rn dsdp_alice_secrecy dumas2017dual` and remove the old theorem + any references, updating `_CoqProject` if the deleted files are listed.
- [ ] **Step 2: Verify** the dsdp subtree builds (`make -f Makefile.coq` on the leaves, dependency-ordered per `project_symbolic_to_game_derivation`).
- [ ] **Step 3: Commit** `ROCQ_AUDIT_BYPASS=1` (pure deletion, `feedback_skip_audit_for_cleanup`) `-m "dsdp: remove fiber scaffolding + superseded dsdp_alice_secrecy"`.

### Task 17: Blueprint Part II green-flip

**Files:** `dumas2017dual/blueprint/src/it_leg_bridge.tex`; build via `dumas2017dual/blueprint/make_blueprint.sh`.

- [ ] **Step 1:** Update the Part II nodes to the corrected statements (`dsdp_output`, route-F fiber, weights-as-parameters, the `injective (u3·)` precondition), flip blue→green, remove the option-A hypothesis caveat. Statement bodies follow the terse mathcomp-qbs style (CLAUDE.md statement-comment rule).
- [ ] **Step 2: Verify** the blueprint builds green (`make_blueprint.sh`; `latexmk -halt-on-error` per `feedback_verify_with_project_build_command`); scan agent prose for undefined macros.
- [ ] **Step 3: Commit** `-m "blueprint: Part II green — fiber 1/m via recomposed S (route F)"`.

---

## Self-review notes

- **Spec coverage:** Tasks 1–3 = spec §4.1; Task 4–5 = §5/§8 route F; Task 6–7 = §4.2 + §8 weights-as-parameters; Task 8 = §8 R-2eps; Task 9 = §4.3; Tasks 10–11 = §5 hypotheses; Tasks 12–13 = §5 bound; Tasks 14–15 = §6; Tasks 16–17 = §9/§2. All spec sections mapped.
- **Sequencing dependency:** Phase 1+2 (entropy/spec) are game-independent and can run first/in parallel; Phase 3 (game) feeds Phase 4; Phase 4 feeds Phase 5; Phase 6 last. Bottleneck-first (your chosen order) is preserved: the S-recomposition (Tasks 7,9) is the load-bearing algebra and is front-loaded among the game tasks, with its kernel already probe-verified.
- **Proof-body honesty:** probe-verified bodies (Tasks 1, 4, 9) are given exactly; the rest fix the statement + strategy and delegate the body to `rocq-prover`, because their proofs are not yet known and fabricating them would violate `feedback_test_proof_steps_before_plan`.
- **Open implementation risk:** Task 6 (env-seeding) is the one genuinely new mechanism; if threading a seed through `denote_game_leak_S` proves heavy, fall back to seeding via `GC_let`-prefixed constants in the trace (a `game_code`-level seed) rather than an env-constructor change.

---

## 2026-06-11 progress + de-risk experiments (A, B)

**Tasks 1–9 committed and green** (see prior commits). The single genuinely-new
lemma the de-risk flagged is now **done and committed**.

### `cinde_RV_comp` — landed (commit `1be50da`, `dumas2017dual/lib/extra_proba.v`)

The conditional analogue of infotheo's `inde_RV_comp`:
`P |= X _|_ Y | Z -> P |= f(X,Z) _|_ Y | Z`.

- **Experiment A (compiled standalone):** ~70 lines, standard classical axioms
  only. Proof is a fiber sum over `X` (`creasoning_by_cases`) with the
  `W = f(X,Z)` constraint collapsed to the indicator `f a c == d` by two
  joint-law helpers (`pr_eq_comp_constraint`, `pr_eq_comp_constraint_tail`,
  each a `pr_in_comp'` + singleton-preimage computation).
- **Confirmed genuinely absent from infotheo** (MCP signature search +
  full-tree grep over 153 installed `.v`): only the unconditional
  `inde_RV_comp` exists; the nearest cinde lemmas (`decomposition`,
  `cinde_alt`, `inde_RV2_cinde`, `cinde_rv_comp_removal`) are different
  statements. Not a trivial corollary (cinde does not give `[%X,Z] _|_ Y`).
  General enough to upstream next to `inde_RV_comp`; lives in `extra_proba`
  for now.
- **Naming** vetted against the corpus: `comp` is the house spelling
  (`inde_RV_comp`, `comp_RV`, `` `o ``; 76 `_comp` vs 0 `funcomp`); the `c`
  of `cinde` already carries "conditional", so no `_cond` suffix.

### Experiment B — the open question is resolved; no residual bridge lemma

Reading the real reflection (`dsdp_security_indcpa_fiber.v`):
`guess_joint_fdist` (line 337) is `sdistr_to_fdist` of `guess_joint_code`,
which returns only `(msg_to_fin guess, msg_to_fin v2)` — **S and W are
marginalized away**, so `guess _|_ V2 | S` is not even statable over it. The
richer fdist that retains S and W *is* `guess_sample_fdist` (Task 10).

In that trace-level fdist `guess = call_pred(view, s)` (line 289) — `predictor`
applied to `(view/randomness, S)`, never reading the V2 coordinate — so
`guess` is literally the composed RV `predictor `o [%W, S]` **by construction
of the trace projection**. The plug-in compiles as a one-liner
`exact: cinde_RV_comp` (toy verified). Consequences:

- `Pr_fst_agree_locs` does **not** by itself give the conditional
  independence (it is a `Pr`-marginal frame fact); the missing piece was
  `cinde_RV_comp`, now done.
- There is **no residual bridge lemma** beyond it: the factorization is
  pointwise from the trace, not a marginal-replacement. `Pr_fst_agree_locs`'s
  real jobs are the post-run V2-cell read (`Pr_code_preserves`) and the frame
  used when building the rich fdist.

### Refinements to the remaining tasks

- **Task 11** `guess_indep_V2_given_S` is now `exact: cinde_RV_comp` (with
  `X := W`, `Z := S`, `Y := V2`, `f := predictor`), conditional on Task 10
  delivering `guess_sample_fdist` with `guess` as the trace-level
  `predictor `o [%W, S]`.
- **Task 10** is the real remaining plumbing (the "bridge"): build
  `guess_sample_fdist` over the full sample trace (retaining S, W), with
  `guess_joint_fdist` recovered as its `(guess,V2)`-marginal.
- **Task 12** `bijective msg_of_idx` confirmed sound: it is the
  uniform-sampling faithfulness condition (pushforward of uniform stays
  uniform iff the index map is injective); `#|plain AHE| = card_msg` alone is
  insufficient. Lands at the `Mfin`/`msg_of_idx` carrier boundary.
