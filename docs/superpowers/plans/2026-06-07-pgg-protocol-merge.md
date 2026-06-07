# PGG piSMC Protocol Merge Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make the general piSMC protocol the single source of truth: one canonical `exchange_*` program plus a 4-field `ReconPlug` recovery record, with den Boer, Kim, S_5, and S_5×S_5 each a thin instance, and wreath7 retired.

**Architecture:** Keep the framework monomorphic at `ThresholdScheme 'I_N 'I_N` (Option C). Add a fixed content readout `'I_N -> 'I_N` applied by the dealer (`id` for the position model; the deck face map for den Boer). Carve recovery into `ReconPlug` (scheme + content + monodromy + perm-invariance over the full `pgg_G`), and reduce `CoveringScheme` to `{cs_plug; cs_data; cs_gap}`. den Boer is rebuilt over `'I_5`; an input-commitment dealer prologue is added via new pgg-typed session wrappers. The wire (`pgg_data`) never changes, so the player/verifier session-duality proofs are reused verbatim for every instance.

**Tech Stack:** Rocq (Coq) + MathComp + infotheo + HB; piSMC session types (`sproc`/`senv`); rocq-mcp for interactive proof development; `make -j1` for compilation.

**Source spec:** `docs/superpowers/specs/2026-06-07-pgg-protocol-merge-design.md` (v4). Gate findings and decisions: `pgg-smc/notes/20260607T055033Z-gate-results-and-merge-decisions.md`.

---

## Conventions (read before any task)

**Compilation safety (HARD rules — violating these crashes the 24 GB machine):**
- Compile with `make -j1 <path>.vo` ONLY. Never `-j4`. One `rocqworker` at a time. Never run two compilations concurrently (including across subagents).
- Never `rewrite !lemma` with arithmetic lemmas (`addn1`, `addnA`, `subnK`, ...): exponential nat blowup. Use explicit single rewrites.
- Never use `lia` (not available in this project). Use MathComp nat lemmas (`leq_add2l`, `leq_trans`, `ltnS`, `addnK`, ...).
- Never `move/eqP` on Prop equalities from `ltngtP`/`eqVneq`/`leqP` (already Prop `=`); use directly with `subst`/`rewrite`.

**Logical paths (from `_CoqProject`):** `-R . infotheo`; `-R pgg-smc/reconstruct pgg_reconstruct`; `-R pgg-smc/{lib,protocol,groups,security,instances/*} pgg_smc`.

**Interactive proof loop:** develop every proof with rocq-mcp (`rocq_start` → `rocq_query`/`Search`/`Print` → build with `rocq_check`/`rocq_step_multi` → apply once to the file). Reserve `make -j1 …vo` for the final per-file green check and the per-phase full rebuild. Budget at most 2 full-file `make` runs per task.

**Per-task "test" = compile + axiom bar.** A task is DONE when:
1. `make -j1 <file>.vo` succeeds (no errors; warnings OK).
2. `Print Assumptions <main_lemma_of_task>.` lists no axiom beyond the project's pre-existing set (the `*_group_order_eq`, `*_realised_by_curve`, `*_inverse_galois_realised`, `s5x5_*`, Rayleigh `*_mixing` axioms already in the tree). NO new custom axiom may appear except where a task explicitly authorizes one (none do in this plan).
3. The change is committed.

**Pre-existing axiom inventory (capture once, in Task 1.2).** Establishes the baseline `Print Assumptions` set so later tasks can diff against it.

**Commit discipline:** one commit per task (or per step where noted). Commit only `.v` files you changed (and this plan/spec). `pgg-smc/notes/` is gitignored — never `git add -f` it. Staging `.v` files triggers the pre-commit rocq-audit gate; H-series comment rules apply to every new `Lemma`/`Theorem`/`Definition` (Kind/What/Why/Used-by block), and I-series naming rules forbid `_works`/`_tmp`/`_helper`/kind-suffixes. Write the comment block as you add each entity.

**Branch:** work on `pgg-smc` (current). Do not commit to `master`.

---

## File Structure

Files CREATED:
- `pgg-smc/protocol/pgg_monodromy_profile.v` — relocated `MonodromyProfile` (now `mp_plug : ReconPlug`) + `run_profile` section. (Phase 3)
- `pgg-smc/instances/wreath7/wreath_profile.v` (or fold into an existing instance file) — `wreath_profile` plug, kept until retirement. (Phase 3; transient)
- `pgg-smc/instances/s5/s5_profile.v` and `pgg-smc/instances/abelian/abel_profile.v` — relocated plugs. (Phase 3)
- `pgg-smc/instances/s5x5/s5x5_profile.v` — the new s5x5 plug. (Phase 4)
- `pgg-smc/protocol/pgg_input_commitment.v` — new pgg-typed commit/recv-commit `sproc` wrappers + dealer prologue. (Phase 6)

Files MODIFIED (by phase):
- Phase 2: `reconstruct/pgg_sharing_framework.v` (content readout), `reconstruct/covering_scheme.v` (`ReconPlug` + `CoveringScheme` restructure), `reconstruct/cover_genus0.v`/`cover_genus1.v`/`cover_genus2.v`, `reconstruct/pgg_covering_correctness.v`, `reconstruct/algebraic_rigidity.v`, `reconstruct/pgg_dealer_bridge.v`, `reconstruct/pgg_protocol_landscape.v`, `reconstruct/dropout_witness.v`, and the instance rigidity files (`instances/s5/rigidity_s5_instance.v`, `instances/s5x5/rigidity_s5x5_instance.v`, `instances/kim2025/rigidity_kim_instance.v`, `instances/denboer1989/five_card_security.v`).
- Phase 3: `protocol/card_exchange_pismc.v` (`dealt_hand_content`, content-carrying `exchange_dealer`, remove instance imports).
- Phase 5: `instances/denboer1989/five_card_program.v` (face map + `'I_5` lemmas), new den Boer `'I_5` scheme + plug, delete old genus-0 RS5 `AlgebraicRigidity`.
- Phase 6: `protocol/card_exchange_pismc.v` (dealer continuation), den Boer program.
- Phase 7: delete `instances/wreath7/`.

---

## Phase 1: Green baseline + axiom inventory

### Task 1.1: Confirm the reconstruct chain + instances build green

**Files:** none modified.

- [ ] **Step 1: Rebuild the reconstruct chain (already greened in GATE 1; reconfirm).**

Run: `make -j1 pgg-smc/reconstruct/pgg_sharing_framework.vo pgg-smc/reconstruct/covering_scheme.vo pgg-smc/reconstruct/cover_tradeoff.vo pgg-smc/reconstruct/algebraic_rigidity.vo pgg-smc/reconstruct/pgg_covering_correctness.vo`
Expected: all succeed (warnings only).

- [ ] **Step 2: Build the two stale protocol/bridge files (pull the instance inversion).**

Run: `make -j1 pgg-smc/reconstruct/pgg_dealer_bridge.vo pgg-smc/protocol/card_exchange_pismc.vo`
Expected: success. If failure, STOP and fix the baseline before any refactor (the merge starts from green; do not refactor on red).

- [ ] **Step 3: Build the four retained instances + the wreath profile (current source of `MonodromyProfile`).**

Run: `make -j1 pgg-smc/instances/s5/rigidity_s5_instance.vo pgg-smc/instances/s5x5/rigidity_s5x5_instance.vo pgg-smc/instances/kim2025/rigidity_kim_instance.vo pgg-smc/instances/denboer1989/five_card_security.vo pgg-smc/instances/wreath7/wreath_monodromy_profile.vo`
Expected: success.

- [ ] **Step 4: Commit nothing (baseline only).** Record in the execution log that the baseline is green.

### Task 1.2: Capture the pre-existing axiom baseline

**Files:** Create `pgg-smc/reconstruct/_axiom_baseline.v` (scratch, deleted at end).

- [ ] **Step 1: Write a scratch file that prints assumptions of the key end-to-end lemmas.**

```coq
From pgg_smc Require Import pgg_interface card_exchange_pismc.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    algebraic_rigidity pgg_dealer_bridge.
(* Add Print Assumptions for the lemmas the merge will re-touch: *)
Print Assumptions pgg_hidden_invariant_perm.
Print Assumptions genus0_exact.
```

- [ ] **Step 2: Compile and record the output.**

Run: `make -j1 pgg-smc/reconstruct/_axiom_baseline.vo 2>&1 | tee /tmp/axiom_baseline.txt`
Expected: a list of `Closed under the global context` or a small named-axiom set. Save `/tmp/axiom_baseline.txt`; this is the diff target for every later `Print Assumptions`.

- [ ] **Step 3: Delete the scratch file.**

Run: `rm -f pgg-smc/reconstruct/_axiom_baseline.v pgg-smc/reconstruct/_axiom_baseline.vo pgg-smc/reconstruct/_axiom_baseline.glob`

---

## Phase 2: `ReconPlug` carve-out + `CoveringScheme` restructure + content readout

GATE 1 validated every shape in this phase against the live source. Migration substitutions are taken verbatim from the GATE 1 report.

### Task 2.1: Add the content readout to `Section pgg_protocol_secret`

**Files:** Modify `pgg-smc/reconstruct/pgg_sharing_framework.v:254-308`.

Current `pgg_recon_endpoints` reads positions; `pgg_hidden_invariant_perm`'s `ts_valid`/`G_stable` are stated over `starts`. Generalize by inserting a fixed `content : 'I_N -> 'I_N` and reading content of the shuffled starts. `content = id` recovers the current statements definitionally.

- [ ] **Step 1: Add the content variable and generalize `pgg_recon_endpoints`.**

In `Section pgg_protocol_secret`, after `Variable ts : ThresholdScheme 'I_N 'I_N.` and `Hypothesis HT : ts_T' ts = pi_T' PI.`, add:

```coq
Variable content : 'I_N -> 'I_N.
```

Replace the definition (`:275-276`):

```coq
Definition pgg_recon_endpoints (P : gT) : 'I_N :=
  pgg_recon [tuple content (rho P (tnth starts i)) | i < T].
```

- [ ] **Step 2: Generalize `pgg_hidden_invariant_perm` to the content-mapped shares.**

Replace the lemma (`:284-306`) with (the shares are now `[content (start_j)]`, and `G_stable` reads content after the action):

```coq
(** pgg_hidden_invariant_perm — content-readout generalization of endpoint
    reconstruction. Kind: main. What: a perm-compatible scheme on the
    content-mapped starts, plus G-stable starts, reconstructs the secret from the
    endpoints read through [content]. Why: the merge's correctness engine; with
    [content = id] it is the original position-model statement. Used-by:
    pgg_covering_correct, ar_protocol_correct, dealer_words_correct, the den Boer
    correctness re-export. *)
Lemma pgg_hidden_invariant_perm (H : {group gT}) (s : 'I_N) (P : gT)
    (perm : gT -> {perm 'I_sT})
    (HsubG : H \subset pgg_G M)
    (G_stable : forall g, g \in H ->
       forall i : 'I_sT,
         content (rho g (tnth (cast_tuple (esym (congr1 S HT)) starts) i)) =
         tnth [tuple content (tnth (cast_tuple (esym (congr1 S HT)) starts) j)
              | j < sT] (perm g i)) :
  P \in H ->
  ts_valid ts s [tuple content (tnth (cast_tuple (esym (congr1 S HT)) starts) j) | j < sT] ->
  @ts_recon_perm_invariant gT H _ _ ts perm ->
  pgg_recon_endpoints P = s.
```

Proof strategy (mirror the existing proof at `:294-306`): unfold `pgg_recon_endpoints`/`pgg_recon`; show
`cast_tuple (esym (congr1 S HT)) [tuple content (rho P (tnth starts i)) | i < T]
 = [tuple tnth shares (perm P i) | i < sT]` (where `shares` is the content-mapped tuple) via `eq_from_tnth`, `tnth_cast_tuple`, `tnth_mktuple`, then `rewrite -(G_stable P PG i)` and `congr (content (rho P _))` with `tnth_cast_tuple`; close with `exact: Hperm PG Hvalid`. The only delta from the current proof is the extra `content` wrapper, which `congr` carries.

- [ ] **Step 3: Compile.**

Run: `make -j1 pgg-smc/reconstruct/pgg_sharing_framework.vo`
Expected: success.

- [ ] **Step 4: Commit.**

```bash
git add pgg-smc/reconstruct/pgg_sharing_framework.v
git commit -m "reconstruct: content readout in pgg_protocol_secret (content=id collapses to position model)"
```

### Task 2.2: Define the `ReconPlug` record

**Files:** Modify `pgg-smc/reconstruct/covering_scheme.v` (insert before `Section covering_scheme`, after the `CoveringData` section, ~`:104`).

GATE 1 confirmed this record elaborates with `rp_recon_invariant`'s holes resolving to `@ts_recon_perm_invariant (pgg_gT M) (pgg_G M) 'I_N 'I_N rp_scheme rp_monodromy`.

- [ ] **Step 1: Write the record.**

```coq
(** ReconPlug — the pluggable reconstruction half of an instance. Kind: interface.
    What: a threshold scheme on 'I_N, a fixed content readout, a monodromy->share
    permutation, and perm-invariance of reconstruction over the FULL group pgg_G.
    Why: the program (run_*) and correctness (pgg_hidden_invariant_perm) consume
    this bare record; only the genus/tradeoff narrative needs CoveringScheme.
    Used-by: CoveringScheme, MonodromyProfile, every instance plug. *)
Record ReconPlug (M : MonodromyReprType) := MkReconPlug {
  rp_scheme    : ThresholdScheme 'I_(pgg_N' M).+1 'I_(pgg_N' M).+1 ;
  rp_content   : 'I_(pgg_N' M).+1 -> 'I_(pgg_N' M).+1 ;
  rp_monodromy : pgg_gT M -> {perm 'I_(ts_T' rp_scheme).+1} ;
  rp_recon_invariant :
    @ts_recon_perm_invariant _ (pgg_G M) _ _ rp_scheme rp_monodromy ;
}.

Arguments ReconPlug M : clear implicits.
Arguments MkReconPlug {M}.
```

- [ ] **Step 2: Compile (record-only, no consumers yet).**

Run: `make -j1 pgg-smc/reconstruct/covering_scheme.vo`
Expected: success (the existing `CoveringScheme` below still uses the old shape; this step only adds the record above it). If a name clash with the old `cs_scheme` field is reported, proceed to Task 2.3 in the same edit session and compile once after both.

- [ ] **Step 3: Commit (combine with Task 2.3 if compiled together).**

```bash
git add pgg-smc/reconstruct/covering_scheme.v
git commit -m "reconstruct: add ReconPlug record (scheme+content+monodromy+full-group invariance)"
```

### Task 2.3: Restructure `CoveringScheme` to `{cs_plug; cs_data; cs_gap}`

**Files:** Modify `pgg-smc/reconstruct/covering_scheme.v:108-167`.

Drop `cs_T'`, `cs_scheme_T`, `cs_monodromy`, `cs_recon_symmetry`, `cs_recon_symmetry_sub`, `cs_recon_invariant` (GATE 1: `cs_T'`/`cs_scheme_T` have zero consumers; the others move into the plug / become `pgg_G`).

- [ ] **Step 1: Replace the record.**

```coq
Record CoveringScheme (M : MonodromyReprType) := MkCoveringScheme {
  cs_plug : ReconPlug M ;
  cs_data : CoveringData M ;
  cs_gap  : ts_T (rp_scheme cs_plug) <= ts_k (rp_scheme cs_plug) + 2 * cd_genus cs_data ;
}.

Arguments CoveringScheme M : clear implicits.
Arguments MkCoveringScheme {M}.

Notation cs_scheme cs := (rp_scheme (cs_plug cs)).
```

- [ ] **Step 2: Fix the three consequence lemmas (`:146-165`) to the notation.**

`genus0_exact`, `higher_genus_wider_gap`, `gap_bound` use `cs_scheme cs` and `cs_data cs`; with the `Notation`, `cs_scheme cs` already means `rp_scheme (cs_plug cs)`, so their statements are unchanged. Verify each still typechecks; the proofs (`by rewrite Hg0 muln0 addn0`, etc.) are unchanged.

- [ ] **Step 3: Compile.**

Run: `make -j1 pgg-smc/reconstruct/covering_scheme.vo`
Expected: success.

- [ ] **Step 4: Commit.**

```bash
git add pgg-smc/reconstruct/covering_scheme.v
git commit -m "reconstruct: CoveringScheme = {cs_plug; cs_data; cs_gap}; drop cs_T'/cs_scheme_T/recon-symmetry; Notation cs_scheme"
```

### Task 2.4: Migrate the covering builders `cover_genus0/1/2.v`

**Files:** Modify `reconstruct/cover_genus0.v` (`genus0_covering` `:166-176`, `genus0_covering_witness` `:258-262`), `cover_genus1.v` (`:271-276`, `:481-486`), `cover_genus2.v` (`:274-279`).

These construct `CoveringScheme` records and must produce the new `{cs_plug; cs_data; cs_gap}` shape. Each old literal set `cs_scheme := ts`, `cs_T' := ...`, `cs_scheme_T := erefl`, `cs_monodromy := mono`, `cs_recon_symmetry := pgg_G M`, `cs_recon_symmetry_sub := subxx _`, `cs_recon_invariant := inv`, `cs_gap := gap`.

- [ ] **Step 1: Rewrite each literal.** For `genus0_covering` (the shared path for kim/denboer), build the plug then the cover:

```coq
Definition genus0_covering (* ... existing params ... *) : CoveringScheme M :=
  MkCoveringScheme
    (MkReconPlug ts content_fn mono inv)   (* content_fn = id for genus-0 position model *)
    cdata
    gap.
```

Use `id` for `content_fn` in every genus builder (all current covers are position-model). Preserve the existing `ts`, `mono`, `inv`, `cdata`, `gap` terms; only repackage them. The dropped `cs_T'`/`cs_scheme_T` (`erefl`) terms are deleted.

- [ ] **Step 2: Compile each, in dependency order.**

Run: `make -j1 pgg-smc/reconstruct/cover_genus0.vo`
then `make -j1 pgg-smc/reconstruct/cover_genus1.vo`
then `make -j1 pgg-smc/reconstruct/cover_genus2.vo`
Expected: success.

- [ ] **Step 3: Commit.**

```bash
git add pgg-smc/reconstruct/cover_genus0.v pgg-smc/reconstruct/cover_genus1.v pgg-smc/reconstruct/cover_genus2.v
git commit -m "reconstruct: cover_genus0/1/2 build CoveringScheme via ReconPlug (content=id)"
```

### Task 2.5: Migrate `pgg_covering_correctness.v`

**Files:** Modify `reconstruct/pgg_covering_correctness.v:52-66` (`pgg_covering_correct`).

GATE 1 substitutions: `cs_recon_symmetry cs -> pgg_G M`; `cs_monodromy cs -> rp_monodromy (cs_plug cs)`; `cs_recon_symmetry_sub -> subxx _`; `cs_recon_invariant cs -> rp_recon_invariant (cs_plug cs)`. The engine `pgg_hidden_invariant_perm` already accepts an arbitrary subgroup; instantiate `H := pgg_G M`, `HsubG := subxx _`. Thread `content` from the plug: `rp_content (cs_plug cs)`.

- [ ] **Step 1: Apply the substitutions and pass `rp_content (cs_plug cs)` as the content argument to `pgg_hidden_invariant_perm`.** The `G_stable` and `ts_valid` hypotheses are now stated over the content-mapped starts (Task 2.1); for `content = id` they are the existing terms up to a definitional `map id`. If a `map id`/`tnth ... id` mismatch appears, normalize with `rewrite map_id` or `under eq_mktuple => i rewrite ...`.

- [ ] **Step 2: Compile.** Run: `make -j1 pgg-smc/reconstruct/pgg_covering_correctness.vo`. Expected: success.

- [ ] **Step 3: `Print Assumptions pgg_covering_correct` — diff against `/tmp/axiom_baseline.txt`.** Expected: no new axiom.

- [ ] **Step 4: Commit.**

```bash
git add pgg-smc/reconstruct/pgg_covering_correctness.v
git commit -m "reconstruct: pgg_covering_correct over full pgg_G via ReconPlug accessors"
```

### Task 2.6: Migrate `algebraic_rigidity.v`

**Files:** Modify `reconstruct/algebraic_rigidity.v:403-420` (`ar_protocol_correct` and the surrounding `cs_monodromy`/`cs_recon_symmetry` uses at `:405-420`).

- [ ] **Step 1: Apply GATE 1 substitutions** (`cs_monodromy -> rp_monodromy (cs_plug ...)`, `cs_recon_symmetry -> pgg_G M`, `cs_recon_symmetry_sub -> subxx _`, `cs_recon_invariant -> rp_recon_invariant (cs_plug ...)`), and thread `rp_content (cs_plug ...)` into the `pgg_hidden_invariant_perm` application.

- [ ] **Step 2: Compile.** Run: `make -j1 pgg-smc/reconstruct/algebraic_rigidity.vo`. Expected: success.

- [ ] **Step 3: `Print Assumptions ar_protocol_correct` — diff against baseline.** Expected: no new axiom.

- [ ] **Step 4: Commit.**

```bash
git add pgg-smc/reconstruct/algebraic_rigidity.v
git commit -m "reconstruct: ar_protocol_correct threads ReconPlug accessors + content"
```

### Task 2.7: Migrate `pgg_dealer_bridge.v`

**Files:** Modify `reconstruct/pgg_dealer_bridge.v:42-50` and the body.

- [ ] **Step 1: Change the group and accessors.** Replace `Let G := cs_recon_symmetry (tw_covering (ar_threshold ar))` with `Let G := pgg_G M`. In the `G_stable` hypothesis (`:45-50`), replace `cs_monodromy (tw_covering (ar_threshold ar))` with `rp_monodromy (cs_plug (tw_covering (ar_threshold ar)))`. `HT` (`:44`) keeps using `cs_scheme (...)` (now the notation). The proof bodies (`ar_protocol_correct`, `sw_bound` re-exports) are unchanged once `ar_protocol_correct` (Task 2.6) is migrated.

- [ ] **Step 2: Compile.** Run: `make -j1 pgg-smc/reconstruct/pgg_dealer_bridge.vo`. Expected: success.

- [ ] **Step 3: `Print Assumptions dealer_words_correct` — diff against baseline.** Expected: no new axiom.

- [ ] **Step 4: Commit.**

```bash
git add pgg-smc/reconstruct/pgg_dealer_bridge.v
git commit -m "reconstruct: dealer_bridge over full pgg_G; rp_monodromy accessor"
```

### Task 2.8: Migrate `pgg_protocol_landscape.v` and `dropout_witness.v`

**Files:** Modify `reconstruct/pgg_protocol_landscape.v:319-331` and `reconstruct/dropout_witness.v:123,133`.

GATE 1 located these uses: `cs_monodromy` at `pgg_protocol_landscape.v:323,331` and `dropout_witness.v:123,133`; `cs_recon_symmetry` at `pgg_protocol_landscape.v:319,324,330`.

- [ ] **Step 1: Apply the same substitutions** as Task 2.5 in both files.

- [ ] **Step 2: Compile both.** Run: `make -j1 pgg-smc/reconstruct/pgg_protocol_landscape.vo` then `make -j1 pgg-smc/reconstruct/dropout_witness.vo`. Expected: success.

- [ ] **Step 3: Commit.**

```bash
git add pgg-smc/reconstruct/pgg_protocol_landscape.v pgg-smc/reconstruct/dropout_witness.v
git commit -m "reconstruct: landscape + dropout_witness use ReconPlug accessors over pgg_G"
```

### Task 2.9: Migrate the four instance `CoveringScheme` literals (content=id)

**Files:** Modify `instances/s5/rigidity_s5_instance.v:334-342`, `instances/s5x5/rigidity_s5x5_instance.v:385-395`, `instances/kim2025/rigidity_kim_instance.v:73-74`, `instances/denboer1989/five_card_security.v:287-288`.

kim and den Boer go through `genus0_covering_witness` (already fixed in Task 2.4), so they may need no change beyond confirming compilation. s5 and s5x5 build literals directly.

- [ ] **Step 1: Rewrite the s5 and s5x5 `CoveringScheme` literals** to `MkCoveringScheme (MkReconPlug s*_ts id s*_monodromy s*_perm_compatible) s*_covering_data s*_cs_gap`, dropping the `cs_T'`/`cs_scheme_T`/`cs_recon_symmetry`/`cs_recon_symmetry_sub` fields. Use `id` for content. The existing `*_perm_compatible`, `*_covering_data`, `*_cs_gap` terms are reused verbatim (GATE 1: these survive).

- [ ] **Step 2: Compile each instance.**

Run: `make -j1 pgg-smc/instances/s5/rigidity_s5_instance.vo`
then `make -j1 pgg-smc/instances/s5x5/rigidity_s5x5_instance.vo`
then `make -j1 pgg-smc/instances/kim2025/rigidity_kim_instance.vo`
then `make -j1 pgg-smc/instances/denboer1989/five_card_security.vo`
Expected: success.

- [ ] **Step 3: Commit.**

```bash
git add pgg-smc/instances/s5/rigidity_s5_instance.v pgg-smc/instances/s5x5/rigidity_s5x5_instance.v pgg-smc/instances/kim2025/rigidity_kim_instance.v pgg-smc/instances/denboer1989/five_card_security.v
git commit -m "instances: s5/s5x5/kim/denboer build CoveringScheme via ReconPlug (content=id)"
```

### Task 2.10: Phase-2 green gate (full reconstruct + instances rebuild)

**Files:** none.

- [ ] **Step 1: Rebuild every file touched in Phase 2, in dependency order, `-j1`.** (One `make` target list; `make` serializes prerequisites with `-j1`.)

Run: `make -j1 pgg-smc/reconstruct/pgg_protocol_landscape.vo pgg-smc/reconstruct/dropout_witness.vo pgg-smc/reconstruct/pgg_dealer_bridge.vo pgg-smc/instances/s5/rigidity_s5_instance.vo pgg-smc/instances/s5x5/rigidity_s5x5_instance.vo pgg-smc/instances/kim2025/rigidity_kim_instance.vo pgg-smc/instances/denboer1989/five_card_security.vo`
Expected: all green.

- [ ] **Step 2: Confirm the wreath profile still builds against the OLD `MonodromyProfile`** (it has not moved yet): `make -j1 pgg-smc/instances/wreath7/wreath_monodromy_profile.vo`. Expected: success (it uses `mp_scheme`, untouched in Phase 2).

- [ ] **Step 3: No commit (gate only).** Phase 2 complete: the record refactor is live and every retained instance is green.

---

## Phase 3: Relocate `MonodromyProfile` + add the program content layer

### Task 3.1: Add `dealt_hand_content` and content to `exchange_dealer`

**Files:** Modify `pgg-smc/protocol/card_exchange_pismc.v` (`dealt_hand` and `exchange_dealer` `:210-221`).

The dealer must bake `rp_content` into each dealt column. For `content = id` this is definitionally the current `dealt_hand`, so the player/verifier programs and their duality proofs are untouched (spec §5a).

- [ ] **Step 1: Add the content-parameterized dealt hand.** Near `dealt_hand` (`:454-455` per gate refs):

```coq
(** dealt_hand_content — the dealer's column after the fixed content readout.
    Kind: helper. What: [seq content (rho w (start i)) | w <- W]. Why: bakes the
    plug's face/id readout into the wire so the revealed values are faces, not
    identities, and the wire stays 'I_N. Used-by: exchange_dealer. *)
Definition dealt_hand_content (content : 'I_N -> 'I_N) (W : seq gT) (i : 'I_T) : seq 'I_N :=
  [seq content (rho w (tnth starts i)) | w <- W].

Lemma dealt_hand_content_id (W : seq gT) (i : 'I_T) :
  dealt_hand_content id W i = dealt_hand W i.
Proof. by rewrite /dealt_hand_content /dealt_hand; apply: eq_map => w. Qed.
```

(Adjust `N`/`T`/`starts`/`rho` to the section's local `Let`s; mirror the existing `dealt_hand` definition exactly, inserting `content`.)

- [ ] **Step 2: Parameterize `exchange_dealer` by `content`.** Add a `content : 'I_N -> 'I_N` parameter and replace `dealt_hand ... W j` with `dealt_hand_content content W j` in the `Deal<player j>` payload. Existing call sites pass `id` (Step 4).

- [ ] **Step 3: Re-prove the dealer-side duality lemmas** for the new `exchange_dealer` shape. Because the payload type is still `seq 'I_N` (only the value map changed, not the session structure), the `native_compute`/`are_dual` proofs are structurally identical: re-run them. If a lemma was `by native_compute` it stays `by native_compute`; if it pattern-matched `dealt_hand`, rewrite with `dealt_hand_content_id` first for the `id` instances.

- [ ] **Step 4: Update in-file call sites and demos to pass `id`.** Anywhere `exchange_dealer PI W P_idx` appeared, write `exchange_dealer id PI W P_idx` (or the local arg order). Compile: `make -j1 pgg-smc/protocol/card_exchange_pismc.vo`. Expected: success.

- [ ] **Step 5: `Print Assumptions` on the main dealer duality lemma — diff baseline.** Expected: no new axiom.

- [ ] **Step 6: Commit.**

```bash
git add pgg-smc/protocol/card_exchange_pismc.v
git commit -m "protocol: exchange_dealer bakes a fixed content readout (dealt_hand_content; id = old dealt_hand)"
```

### Task 3.2: Remove the protocol->instance import inversion

**Files:** Modify `pgg-smc/protocol/card_exchange_pismc.v:13-16` (imports) and `:508-553` (Monster/abelian duality demos); create demo files under the instance dirs.

- [ ] **Step 1: Move the Monster/abelian `native_compute` duality demos** (`:508-553`) into `instances/monster/` and `instances/abelian/` files (e.g. append to `rigidity_monster_instance.v` / `rigidity_abelian_instance.v`, or new `*_duality_demo.v`). They import `card_exchange_pismc`, not vice versa.

- [ ] **Step 2: Delete the two import lines** `From pgg_smc Require Import rigidity_monster_instance.` / `rigidity_abelian_instance.` (`:15-16`).

- [ ] **Step 3: Compile the protocol file and the new demo homes.** Run: `make -j1 pgg-smc/protocol/card_exchange_pismc.vo` then the two demo files. Expected: success; `protocol/` now imports no instance.

- [ ] **Step 4: Commit.**

```bash
git add pgg-smc/protocol/card_exchange_pismc.v pgg-smc/instances/monster/ pgg-smc/instances/abelian/
git commit -m "protocol: remove protocol->instance import inversion; demos move to instance dirs"
```

### Task 3.3: Create `protocol/pgg_monodromy_profile.v` with `mp_plug : ReconPlug`

**Files:** Create `pgg-smc/protocol/pgg_monodromy_profile.v`. Source: `instances/wreath7/wreath_monodromy_profile.v:50-121` (the record + `run_profile` section only; NOT the wreath/abel/s5 plugs, NOT the wreath imports).

- [ ] **Step 1: Write the relocated record + run section.** Imports: `pgg_interface`, `card_exchange_pismc`, `pgg_sharing_framework`, `covering_scheme` (for `ReconPlug`), `algebraic_rigidity`. NO wreath/instance imports.

```coq
Record MonodromyProfile (R : realType) := MkMonodromyProfile {
  mp_M        : MonodromyReprWithGeneratorType ;
  mp_PI       : PGGInterface mp_M ;
  mp_security : SecurityWitness R mp_M ;
  mp_plug     : ReconPlug mp_M ;
}.

Section run_profile.
Variable R : realType.
Variable mp : MonodromyProfile R.
Let M := mp_M mp. Let PI := mp_PI mp. Let N := (pgg_N' M).+1.
Let plug := mp_plug mp.
Let players := enum 'I_(pi_T' PI).+1.

Definition run_dealer (W : seq (pgg_gT M)) (P_idx : nat) :=
  exchange_dealer (rp_content plug) PI players W P_idx.
Definition run_party (i : 'I_(pi_T' PI).+1) := exchange_player PI i.
Definition run_verifier := exchange_verifier PI players.
Definition run_recover (collected : (ts_T' (rp_scheme plug)).+1.-tuple 'I_N) : 'I_N :=
  ts_recon (rp_scheme plug) collected.
Definition run_eps : R := sw_bound_eps (mp_security mp).
Definition run_k : nat := ts_k (rp_scheme plug).
Definition run_anonymous := sw_bound (mp_security mp).
Definition run_private := ts_private (rp_scheme plug).
Lemma run_recovers (s : 'I_N) : run_recover (ts_encode (rp_scheme plug) s) = s.
Proof. exact: ts_correct (ts_encode_valid (rp_scheme plug) s). Qed.
End run_profile.
```

(Carry over each definition's H-series comment block from the original file, updating `mp_scheme`->`rp_scheme (mp_plug ...)` and `mp_M`-dependent texts.)

- [ ] **Step 2: Compile.** Run: `make -j1 pgg-smc/protocol/pgg_monodromy_profile.vo`. Expected: success.

- [ ] **Step 3: Commit.**

```bash
git add pgg-smc/protocol/pgg_monodromy_profile.v
git commit -m "protocol: relocate MonodromyProfile + run_* (mp_plug : ReconPlug; run_dealer applies rp_content)"
```

### Task 3.4: Relocate `abel_profile` and `s5_profile` to instance files

**Files:** Create `instances/abelian/abel_profile.v` and `instances/s5/s5_profile.v`. Source: `wreath_monodromy_profile.v:150-179`.

- [ ] **Step 1: Build each plug as a `ReconPlug` then a `MonodromyProfile`.** The old profiles passed a bare `ThresholdScheme` as `mp_scheme`; now wrap it in a `ReconPlug` with `content = id`, the instance monodromy, and the instance perm-invariance lemma. For abel (`sum_mod_scheme 2 1`) and s5 (`sum_mod_scheme 3 4`), reuse the existing `*_perm_compatible` lemma the instance already proves (the same one feeding its `CoveringScheme`).

```coq
(* instances/s5/s5_profile.v *)
From pgg_smc Require Import ... pgg_monodromy_profile rigidity_s5_instance.
Definition s5_plug : ReconPlug (Gen_PGGTypes (path_gen_tuple 3)) :=
  MkReconPlug (@sum_mod_scheme 3 4) id s5_monodromy s5_perm_compatible.
Definition s5_profile (R : realType) : MonodromyProfile R :=
  @MkMonodromyProfile R (Gen_PGGTypes (path_gen_tuple 3)) s5_PI
    (s5_security_witness_schreier R 285) s5_plug.
```

(Move `s5_PI`/`s5_starts_uniq` and the abel analogues from `wreath_monodromy_profile.v` into these files. Use the instance's actual monodromy and perm-invariance lemma names; if the instance does not yet export a `*_perm_compatible` at `pgg_G`, reuse `rp_recon_invariant (cs_plug <instance_covering>)`.)

- [ ] **Step 2: Compile each.** Run: `make -j1 pgg-smc/instances/abelian/abel_profile.vo` then `make -j1 pgg-smc/instances/s5/s5_profile.vo`. Expected: success.

- [ ] **Step 3: Move the `run_k_*`/`*_plug_*` contrast lemmas** (`wreath_monodromy_profile.v:185-227`) that reference abel/s5 into these files (s5/abel parts) and the wreath ones stay in wreath7 for now. Compile.

- [ ] **Step 4: Commit.**

```bash
git add pgg-smc/instances/abelian/abel_profile.v pgg-smc/instances/s5/s5_profile.v
git commit -m "instances: relocate abel_profile/s5_profile as ReconPlug-based MonodromyProfiles"
```

### Task 3.5: Point wreath7's profile at the relocated record (transitional)

**Files:** Modify `instances/wreath7/wreath_monodromy_profile.v`.

- [ ] **Step 1: Delete the local `MonodromyProfile` record + `run_profile` section** (now in `protocol/pgg_monodromy_profile.v`) and `Require Import pgg_monodromy_profile`. Rebuild `wreath_profile` as a `ReconPlug`-based profile (wrap `wreath2_scheme` in a `ReconPlug` with `wreath_monodromy` + `wreath_recon_inv`; note `wreath_recon_inv` holds only over `wcore`, NOT `pgg_G` — so the wreath plug CANNOT satisfy `rp_recon_invariant` over the full group). Since wreath is being retired (Phase 7), keep `wreath_profile` ONLY for its security/`run_k` demos and stub `rp_recon_invariant` is NOT possible; instead retain the wreath profile against the OLD record by keeping a local minimal record copy until Phase 7, OR drop `wreath_profile` now.

- [ ] **Step 2 (decision):** Because the dropped recon-symmetry makes wreath structurally incompatible (GATE 1 kill-shot, out of scope), do NOT force wreath into the new `ReconPlug`. Keep `instances/wreath7/wreath_monodromy_profile.v` building against a LOCAL `MonodromyProfile_wreath` copy for its contrast demos until Phase 7 deletes it. Compile: `make -j1 pgg-smc/instances/wreath7/wreath_monodromy_profile.vo`. Expected: success.

- [ ] **Step 3: Commit.**

```bash
git add pgg-smc/instances/wreath7/wreath_monodromy_profile.v
git commit -m "wreath7: keep contrast demos on a local profile copy pending retirement"
```

### Task 3.6: Phase-3 green gate

- [ ] **Step 1: Rebuild protocol + relocated profiles + instances.** Run: `make -j1 pgg-smc/protocol/pgg_monodromy_profile.vo pgg-smc/instances/s5/s5_profile.vo pgg-smc/instances/abelian/abel_profile.vo`. Expected: green. No commit.

---

## Phase 4: s5x5 parity (spec §11a items 1-6) + `s5x5_profile`

Each item is a lemma/definition the wreath profile had and s5x5 needs. Develop proofs with rocq-mcp; statements below are exact.

### Task 4.1: Non-abelian lemma for S_5 × S_5

**Files:** Modify `instances/s5x5/rigidity_s5x5_instance.v` (or `pgg_s5x5.v`).

- [ ] **Step 1: State and prove.**

```coq
(** s5x5_nonabelian — the s5x5 monodromy group is non-abelian. Kind: main.
    What: ~~ abelian (pgg_G R_s5x5). Why: the structural root of the vanishing
    security character (mixing), the s5x5 analogue of wreath_nonabelian.
    Used-by: s5x5 security character / CombinatorialRigidity. *)
Lemma s5x5_nonabelian : ~~ abelian (pgg_G R_s5x5).
```

Strategy: `S_5 × S_5` is non-abelian because `S_5` is (`/negP`, exhibit two non-commuting transpositions in one factor lifted via the product injection). Use the existing s5 non-abelian fact if present (`Search _ abelian (pgg_G _)` in the s5 instance), and `card`/generator lemmas already in `pgg_s5x5.v`.

- [ ] **Step 2: Compile + `Print Assumptions s5x5_nonabelian` (diff baseline). Commit.**

```bash
git commit -am "s5x5: non-abelian lemma for S_5 x S_5"
```

### Task 4.2: Concrete `s5x5_PI` interface

**Files:** Modify `instances/s5x5/rigidity_s5x5_instance.v`.

- [ ] **Step 1: State the uniqueness witness + interface.**

```coq
Lemma s5x5_starts_uniq : uniq (ord_tuple 10).
Proof. by rewrite val_ord_tuple enum_uniq. Qed.

Definition s5x5_PI : PGGInterface R_s5x5 :=
  @MkPGGI R_s5x5 9 (ord_tuple 10) s5x5_starts_uniq.
```

(Confirm `pgg_N' R_s5x5 = 9` so `'I_10`; if the deck size differs, set the `MkPGGI` index and tuple length to `pgg_N' R_s5x5`.)

- [ ] **Step 2: Compile. Commit.**

```bash
git commit -am "s5x5: concrete PGGInterface (ord_tuple 10 starts)"
```

### Task 4.3: Discharge `G_stable` for s5x5

**Files:** Modify `instances/s5x5/rigidity_s5x5_instance.v`.

- [ ] **Step 1: State the start-stability bridge** matching `pgg_hidden_invariant_perm`'s `G_stable` shape for `content = id`:

```coq
(** s5x5_G_stable — rho acts on the s5x5 starts as the share-slot permutation.
    Kind: main. What: for g in pgg_G R_s5x5, rho g (start i) = start (perm g i).
    Why: the G_stable hypothesis of pgg_hidden_invariant_perm; the cast
    reconciliation between deck-position 'I_10 and share-index 'I_10. Used-by:
    s5x5 end-to-end correctness. *)
Lemma s5x5_G_stable (HT : ts_T' s5x5_ts = pi_T' s5x5_PI) :
  forall g, g \in pgg_G R_s5x5 ->
    forall i, pgg_rho g (tnth (cast_tuple (esym (congr1 S HT)) (pi_starts s5x5_PI)) i)
            = tnth (cast_tuple (esym (congr1 S HT)) (pi_starts s5x5_PI)) (s5x5_monodromy g i).
```

Strategy (spec §11a item 4): `pgg_rho g = g` (identity inclusion, `pgg_interface.v:543`); starts are `ord_tuple 10` so `tnth (ord_tuple _) i = i` after the cast; reduce both sides via `tnth_cast_tuple`, `tnth_ord_tuple`, `cast_ordK`; then `s5x5_monodromy g = g` on slots (define `s5x5_monodromy` so that `perm g i = g i` under the cast). Use `tnth_cast_tuple` (proved at `pgg_sharing_framework.v:246-252`).

- [ ] **Step 2: Compile + axiom diff. Commit.**

```bash
git commit -am "s5x5: discharge G_stable (rho=id, ord_tuple starts, cast reconciliation)"
```

### Task 4.4: End-to-end s5x5 protocol correctness

**Files:** Modify `instances/s5x5/rigidity_s5x5_instance.v`.

- [ ] **Step 1: State the unconditional correctness corollary** (combine Tasks 4.2-4.3 with `pgg_hidden_invariant_perm` and `s5x5_perm_compatible`):

```coq
(** s5x5_protocol_correct — endpoint reconstruction recovers the secret for any
    word in pgg_G. Kind: main. What: pgg_recon_endpoints P = s for P = word_eval w
    in pgg_G, with valid encoded starts. Why: s5x5 reaches den Boer / wreath
    parity on end-to-end correctness. Used-by: s5x5_profile guarantee. *)
Theorem s5x5_protocol_correct (HT : ts_T' s5x5_ts = pi_T' s5x5_PI)
    (s : 'I_10) (P : pgg_gT R_s5x5) :
  P \in pgg_G R_s5x5 ->
  ts_valid s5x5_ts s [tuple id (tnth (cast_tuple (esym (congr1 S HT)) (pi_starts s5x5_PI)) j) | j] ->
  @pgg_recon_endpoints R_s5x5 s5x5_PI s5x5_ts HT id P = s.
```

Strategy: `apply: (pgg_hidden_invariant_perm (H := pgg_G R_s5x5) ... (perm := s5x5_monodromy))`; discharge `HsubG := subxx _`, `G_stable := s5x5_G_stable HT`, and the `ts_recon_perm_invariant` argument with `s5x5_perm_compatible` (the existing `product_sum_mod_perm_compatible` instantiation, `product_threshold.v:452`). Normalize `[tuple id (...) | j]` with `map_id`/`eq_mktuple` to match the perm-invariance statement.

- [ ] **Step 2: Compile + `Print Assumptions s5x5_protocol_correct` (diff baseline; the existing `s5x5_group_order_eq`/`s5x5_inverse_galois_realised`/Rayleigh axioms are allowed, nothing new). Commit.**

```bash
git commit -am "s5x5: end-to-end protocol correctness (unconditional, via pgg_hidden_invariant_perm)"
```

### Task 4.5: `CombinatorialRigidity` instance for s5x5

**Files:** Modify `instances/s5x5/rigidity_s5x5_instance.v`.

- [ ] **Step 1: Build the `CombinatorialRigidity` record** from `s5x5_large_group`, `s5x5_group_order_bound`, `s5x5_covering` (spec §11a item 6). Inspect the record's fields with `Print CombinatorialRigidity` and supply each (fiber + crypto-secure). Reuse the wreath instance (`rigidity_wreath_instance.v`) as the field-by-field template.

- [ ] **Step 2: Reconcile the genus figure (spec §9, §16 LOW).** In `s5x5_covering_data` (`:337`) and `s5x5_cs_gap` (`:363-365`), make `cd_genus` and the gap witness consistent: either set `cd_genus` to the value the gap is actually proved against and adjust the `realised_by_curve` comment, or strengthen the gap proof to the larger genus. Remove the stale genus comment (`:362-364`). Do NOT claim "Bring's genus 8" in any comment unless the field equals 8.

- [ ] **Step 3: Compile + axiom diff. Commit.**

```bash
git commit -am "s5x5: CombinatorialRigidity instance + reconcile operative genus figure"
```

### Task 4.6: `s5x5_profile` plug

**Files:** Create `instances/s5x5/s5x5_profile.v`.

- [ ] **Step 1: Build the plug + profile** (mirrors Task 3.4):

```coq
Definition s5x5_plug : ReconPlug R_s5x5 :=
  MkReconPlug s5x5_ts id s5x5_monodromy s5x5_perm_compatible.
Definition s5x5_profile (R : realType) : MonodromyProfile R :=
  @MkMonodromyProfile R R_s5x5 s5x5_PI s5x5_security s5x5_plug.
```

(Use the s5x5 security witness name as it exists in the instance; if it is `s5x5_security_witness_*`, use that.)

- [ ] **Step 2: Compile. Commit.**

```bash
git add pgg-smc/instances/s5x5/s5x5_profile.v
git commit -m "s5x5: s5x5_profile plug (ReconPlug content=id)"
```

### Task 4.7: Phase-4 green gate

- [ ] **Step 1: Rebuild s5x5 instance + profile.** Run: `make -j1 pgg-smc/instances/s5x5/rigidity_s5x5_instance.vo pgg-smc/instances/s5x5/s5x5_profile.vo`. Expected: green. No commit.

---

## Phase 5: den Boer `'I_5` rebuild

Transport the `bool` scheme to `'I_5` and prove the net-new perm-invariance. Existing `bool` machinery: `fc_arrange` (`five_card_program.v:65`), `fc_three_consec` (`:93`), `fc_correct` (`:105`), `fc_ts_valid/recon/encode` + `fc_ts_private` + `fc_threshold_scheme` (`five_card_pismc.v:110-244`).

### Task 5.1: bool/'I_5 codec and the fixed face map

**Files:** Modify `instances/denboer1989/five_card_program.v` (append a codec section).

- [ ] **Step 1: Define the codec and face map.**

```coq
(** encode_bool / decode_bool — embed bool into {0,1} ⊂ 'I_5 and back. Kind:
    helper. What: encode_bool true = 1, false = 0; decode_bool s = (s == 1).
    Why: lets the bool five-card trick reuse the monomorphic 'I_5 framework.
    Used-by: the 'I_5 den Boer scheme, fc_content. *)
Definition encode_bool (x : bool) : 'I_5 := if x then (inord 1) else (inord 0).
Definition decode_bool (s : 'I_5) : bool := s == inord 1.

Lemma decode_encode_bool (x : bool) : decode_bool (encode_bool x) = x.
Proof. by case: x; rewrite /decode_bool /encode_bool; apply/eqP/idP; rewrite ?inord_val ... Qed.

(** fc_content — the deck's FIXED face map 'I_5 -> 'I_5 (card identity to encoded
    heart/non-heart). Kind: helper. What: secret-INDEPENDENT readout the dealer
    bakes in. Why: GATE 2 correction — the arrangement (secret) lives in encode,
    content is fixed. Used-by: den_boer_plug. *)
Definition fc_face (c : 'I_5) : bool := (* hearts identities -> true *) ... .
Definition fc_content (c : 'I_5) : 'I_5 := encode_bool (fc_face c).
```

(Choose `fc_face` consistent with `fc_arrange`'s heart pattern: the arrangement `fc_arrange a b` is a `seq bool` of faces; model the five card identities `'I_5` with `fc_face` so that the identity permutation realizing `fc_arrange a b` reads back to that face sequence. Develop the exact `fc_face` against `fc_arrange` with rocq-mcp by `Eval compute`-checking `fc_arrange a b` for the four `(a,b)`.)

- [ ] **Step 2: Compile `five_card_program.vo` + `Print Assumptions decode_encode_bool`. Commit.**

```bash
git commit -am "denboer: bool<->'I_5 codec (encode_bool/decode_bool) and fixed face map fc_content"
```

### Task 5.2: The `'I_5` den Boer threshold scheme

**Files:** Create `instances/denboer1989/five_card_scheme_I5.v` (or append to `five_card_pismc.v`).

- [ ] **Step 1: Transport validity/recon/encode to `'I_5`.**

```coq
Definition fcI_valid (s : 'I_5) (shares : 5.-tuple 'I_5) : Prop :=
  fc_three_consec [seq decode_bool x | x <- shares] = decode_bool s.
Definition fcI_recon (shares : 5.-tuple 'I_5) : 'I_5 :=
  encode_bool (fc_three_consec [seq decode_bool x | x <- shares]).
Definition fcI_encode (s : 'I_5) : 5.-tuple 'I_5 :=
  [tuple of [seq encode_bool x | x <- fc_arrange_tup (decode_bool s) (decode_bool s)]].
```

- [ ] **Step 2: Prove the three obligations** (`fcI_correct`, `fcI_private`, `fcI_encode_valid`) by transport. `fcI_correct` from `fc_ts_correct` + `decode_encode_bool`; `fcI_encode_valid` from `fc_ts_encode_valid`; `fcI_private` from `fc_ts_private` by mapping `encode_bool` over the witness tuple and `decode_bool` back (the `C`-agreement transports because `encode_bool` is injective: prove `encode_bool_inj` first). State `encode_bool_inj : injective encode_bool` and use it.

```coq
Lemma encode_bool_inj : injective encode_bool.
Definition fcI_scheme : ThresholdScheme 'I_5 'I_5 :=
  @MkThresholdScheme 'I_5 'I_5 4 1 fcI_valid fcI_recon fcI_encode
    fcI_correct fcI_private fcI_encode_valid.
```

- [ ] **Step 3: Compile + `Print Assumptions fcI_scheme` (no new axiom). Commit.**

```bash
git commit -am "denboer: 'I_5 three-consec threshold scheme (transported from bool via codec)"
```

### Task 5.3: The net-new perm-invariance (three-consec rotation invariance)

**Files:** same file as Task 5.2.

- [ ] **Step 1: Define the cut monodromy and state perm-invariance over `pgg_G FiveCard_M = Z_5`.**

```coq
(** fc_cut_perm — the Z_5 cut as a share-slot permutation. Kind: helper.
    What: g \in Z_5 maps to the cyclic rotation perm on 'I_5 slots. *)
Definition fc_cut_perm (g : pgg_gT FiveCard_M) : {perm 'I_5} := ... .

(** fcI_perm_compatible — three-consec reconstruction is invariant under the Z_5
    cut. Kind: main. What: ts_recon_perm_invariant over pgg_G FiveCard_M for
    fcI_scheme and fc_cut_perm. Why: the NET-NEW lemma the merge requires
    (GATE 2); the rp_recon_invariant field of den_boer_plug. Used-by:
    den_boer_plug, den Boer end-to-end correctness. *)
Lemma fcI_perm_compatible :
  @ts_recon_perm_invariant _ (pgg_G FiveCard_M) _ _ fcI_scheme fc_cut_perm.
```

Strategy: unfold to `fcI_recon [tnth shares (fc_cut_perm g i) | i] = s` given `fcI_valid s shares`. Reduce `[seq decode_bool (tnth shares (fc_cut_perm g i)) | i]` to a `rot`-image of `[seq decode_bool (tnth shares i) | i]` (the cut is a cyclic rotation: relate `fc_cut_perm g` to `rot k` via `tnth`/`nth` and `rot_tnth`-style reindexing). Then three-consec invariance under `rot`: prove the helper

```coq
Lemma fc_three_consec_rot (k : nat) (s : seq bool) : size s = 5 ->
  fc_three_consec (rot k s) = fc_three_consec s.
```

by `rewrite /fc_three_consec`; the `s ++ s` cyclic window `has ... (iota 0 5)` is rotation-stable (a window starting at `i` in `rot k s` is the window at `i+k mod 5` in `s`); prove by the same exhaustive `case: k => [|[|[|[|[|]]]]]` shape as `fc_correct`, or by `nth_rot`/`nth_cat` rewriting. Conclude with `decode_encode_bool` to wrap back into `'I_5`.

- [ ] **Step 2: Compile + `Print Assumptions fcI_perm_compatible` (NO new axiom — this must be axiom-free). Commit.**

```bash
git commit -am "denboer: three-consec rotation invariance => ts_recon_perm_invariant over Z_5"
```

### Task 5.4: The den Boer `ReconPlug` and end-to-end correctness

**Files:** Modify `instances/denboer1989/five_card_security.v` (replace the old genus-0 RS5 `AlgebraicRigidity`).

- [ ] **Step 1: Build the plug.**

```coq
(** den_boer_plug — the den Boer reconstruction plug. Kind: instance.
    What: fcI_scheme + fixed face content + Z_5 cut monodromy + rotation
    invariance. Why: routes the Five Card Trick through the general protocol with
    no genus/CoveringScheme. Used-by: den_boer_profile, den Boer correctness. *)
Definition den_boer_plug : ReconPlug FiveCard_M :=
  MkReconPlug fcI_scheme fc_content fc_cut_perm fcI_perm_compatible.
```

- [ ] **Step 2: State + prove den Boer end-to-end correctness** via `pgg_hidden_invariant_perm` with `H := pgg_G FiveCard_M`, `content := fc_content`, threading `fcI_perm_compatible` and the den Boer `G_stable` (the cut acts on the identity-arrangement starts as the slot rotation; prove analogously to s5x5's `s5x5_G_stable` but with `fc_cut_perm`). The recovered `'I_5` decodes to `a && b` via `decode_bool` and `fc_correct`.

```coq
Theorem den_boer_protocol_correct (a b : bool) (P : pgg_gT FiveCard_M) :
  P \in pgg_G FiveCard_M ->
  (* starts encode the arrangement fc_arrange a b *) ... ->
  decode_bool (pgg_recon_endpoints (M:=FiveCard_M) ... fc_content P) = a && b.
```

- [ ] **Step 3: Delete the old genus-0 RS5 `AlgebraicRigidity`** (`five_card_security.v:325`, `fc_rigidity`/`fc_covering` + `fc_covering_realised` axiom) — GATE 2 confirmed no external consumer. Keep `fc_security_uniform`.

- [ ] **Step 4: Compile + `Print Assumptions den_boer_protocol_correct` (the `fc_covering_realised` axiom should DISAPPEAR; no new axiom). Commit.**

```bash
git commit -am "denboer: den_boer_plug + end-to-end correctness; delete old genus-0 RS5 AlgebraicRigidity"
```

### Task 5.5: den Boer profile + replace the bespoke program

**Files:** Create `instances/denboer1989/den_boer_profile.v`; retire `five_card_pismc.v`'s bespoke program (keep the bool scheme defs if still referenced, else remove).

- [ ] **Step 1: Build the profile.**

```coq
Definition den_boer_profile (R : realType) : MonodromyProfile R :=
  @MkMonodromyProfile R FiveCard_M FiveCard_PI (fc_security_uniform R) den_boer_plug.
```

(Define/confirm `FiveCard_PI : PGGInterface FiveCard_M` with `ord_tuple 5` starts; add `fc_starts_uniq` if absent.)

- [ ] **Step 2: Show the canonical `run_*` program serves den Boer** (the bespoke `fc_alice/fc_bob/fc_dealer/fc_verifier` are replaced by `run_dealer den_boer_profile`/`run_party`/`run_verifier`). Re-prove the den Boer session-duality at the new shape if the bespoke duality lemmas were relied on; the player/verifier wire is unchanged so reuse the generic `exchange_*` duality.

- [ ] **Step 3: Compile. Commit.**

```bash
git add pgg-smc/instances/denboer1989/den_boer_profile.v
git commit -am "denboer: den_boer_profile on the canonical run_* program (retire bespoke five_card_pismc)"
```

### Task 5.6: Phase-5 green gate

- [ ] **Step 1: Rebuild the den Boer chain.** Run: `make -j1 pgg-smc/instances/denboer1989/five_card_program.vo pgg-smc/instances/denboer1989/five_card_security.vo pgg-smc/instances/denboer1989/den_boer_profile.vo`. Expected: green. No commit.

---

## Phase 6: Input-commitment stage (new pgg-typed wrappers)

GATE 2: `FCCommit`/`FCRecvCommit` are typed over `fc_dtype`/`fc_data` and CANNOT be spliced into `pgg_dtype`/`pgg_data`. Build new commit wrappers over the existing `pgg_dtype`/`pgg_data` (committed payload reuses an existing constructor), so the player/verifier wire stays unchanged; only the dealer gains a prologue.

### Task 6.1: New commit / recv-commit `sproc` wrappers

**Files:** Create `pgg-smc/protocol/pgg_input_commitment.v`.

- [ ] **Step 1: Define the commit and recv-commit wrappers over `pgg_dtype`/`pgg_data`.** Model a single input party committing a sheet/card value (reuse `PGG_sheet`):

```coq
(** pgg_commit / pgg_recv_commit — input-party commit and dealer receive, as
    sproc fragments over the EXISTING pgg_dtype/pgg_data. Kind: interface.
    What: the M-party input-commitment prologue's send/recv. Why: GATE 2 — the
    fc_dtype FCCommit cannot be reused; the payload is a PGG_sheet so the wire is
    unchanged. Used-by: exchange_dealer_with_commit. *)
Definition pgg_commit (i : nat) (v : 'I_N) : sproc pgg_dtype pgg_data i := ... .
Definition pgg_recv_commit (from : nat) : sproc pgg_dtype pgg_data dealer_idx := ... .
```

(Mirror the structure of an existing `Observe<...>`/`Send<...>` fragment in `card_exchange_pismc.v`; the payload constructor is `PGG_sheet`.)

- [ ] **Step 2: Prove the duality lemma for the commit/recv pair** (`are_dual`/`native_compute`), mirroring the existing player/verifier duality proofs.

- [ ] **Step 3: Compile + axiom diff. Commit.**

```bash
git add pgg-smc/protocol/pgg_input_commitment.v
git commit -m "protocol: pgg-typed input-commitment wrappers (over existing pgg_data; duality proved)"
```

### Task 6.2: Dealer prologue (`exchange_dealer_with_commit`) + assemble

**Files:** Modify `pgg-smc/protocol/card_exchange_pismc.v` (or `pgg_input_commitment.v`).

- [ ] **Step 1: Expose `exchange_dealer`'s deal body as a continuation** and define the prologue that prepends `M` `pgg_recv_commit` steps, then an `assemble : M.-tuple 'I_N -> (the starts)` to build the secret-bearing layout, then the existing deal body:

```coq
Definition exchange_dealer_with_commit (M : nat) (assemble : M.-tuple 'I_N -> ...)
    (content : 'I_N -> 'I_N) PI W P_idx : sproc pgg_dtype pgg_data dealer_idx := ... .
```

- [ ] **Step 2: Re-prove the full dealer duality** for the new prologue shape (`native_compute`/dependent `senv` threading). This is the merge's HIGH-risk item; develop incrementally with rocq-mcp, keeping the deal-body sub-proof reused.

- [ ] **Step 3: Confirm `M = 0/1` degenerates to the plain `exchange_dealer`** (a lemma `exchange_dealer_with_commit_0 : exchange_dealer_with_commit 0 ... = exchange_dealer ...`), so position-model instances are unaffected.

- [ ] **Step 4: Compile + axiom diff. Commit.**

```bash
git commit -am "protocol: dealer input-commitment prologue + duality re-proof; M=0/1 = plain dealer"
```

### Task 6.3: den Boer M=2 input-commitment instance

**Files:** Modify `instances/denboer1989/den_boer_profile.v`.

- [ ] **Step 1: Instantiate `assemble := fc_arrange`-into-identities** (the `M = 2` assemble mapping `(a, b)` to the den Boer arrangement starts), and show the den Boer program is `exchange_dealer_with_commit 2 assemble fc_content FiveCard_PI ...`.

- [ ] **Step 2: Re-state `den_boer_protocol_correct` through the committed dealer** (the assembled starts feed `pgg_hidden_invariant_perm`; correctness unchanged from Task 5.4 modulo the prologue).

- [ ] **Step 3: Compile + axiom diff. Commit.**

```bash
git commit -am "denboer: M=2 input-commitment (assemble = fc_arrange) on the committed dealer"
```

### Task 6.4: Phase-6 green gate

- [ ] **Step 1: Rebuild protocol + den Boer.** Run: `make -j1 pgg-smc/protocol/pgg_input_commitment.vo pgg-smc/protocol/card_exchange_pismc.vo pgg-smc/instances/denboer1989/den_boer_profile.vo`. Expected: green. No commit.

---

## Phase 7: Retire wreath7

### Task 7.1: Confirm no external dependency on wreath modules

**Files:** none modified.

- [ ] **Step 1: Grep for wreath imports outside `instances/wreath7/`.**

Run: `grep -rn "Require .*wreath\|pgg_wreath\|wreath_" pgg-smc --include=*.v | grep -v "instances/wreath7/"`
Expected: only the `pgg_abelian.v:274` comment hit (per spec §11). If any real `Require` appears, STOP and resolve it (relocate or remove the dependency) before deletion.

### Task 7.2: Delete the wreath7 directory

**Files:** Delete `pgg-smc/instances/wreath7/`.

- [ ] **Step 1: Remove the directory and its `_CoqProject` entry.**

Run: `git rm -r pgg-smc/instances/wreath7/`
Then delete the `-R pgg-smc/instances/wreath7 pgg_smc` line from `_CoqProject` and regenerate the Makefile if the build uses a committed `Makefile.coq` (`rocq makefile -f _CoqProject -o Makefile` or the project's regeneration command).

- [ ] **Step 2: Full project rebuild.**

Run: `make -j1` (the whole project, serialized). Expected: green with wreath7 gone. (This is the only whole-project build in the plan; it may take a while — that is expected.)

- [ ] **Step 3: Commit.**

```bash
git add -A
git commit -m "wreath7: retire (s5x5 at parity, generic profile relocated); remove dir + _CoqProject entry"
```

### Task 7.3: Final whole-tree green + axiom audit

**Files:** none.

- [ ] **Step 1: Whole-project build (already done in 7.2 Step 2); confirm exit 0.**

- [ ] **Step 2: Axiom audit of the merged end-to-end lemmas.** `Print Assumptions` for `s5x5_protocol_correct`, `den_boer_protocol_correct`, `dealer_words_correct`, and `run_recovers`; diff against `/tmp/axiom_baseline.txt`. Expected: no NEW custom axiom; the `fc_covering_realised` axiom is GONE (den Boer dropped it).

- [ ] **Step 3: Run the pre-commit rocq-audit gate locally** on the staged changes (it runs on commit anyway): confirm H-series comment blocks and I-series naming pass for every new entity. Fix any finding.

---

## Self-Review

**Spec coverage (spec §1-§16 → tasks):**
- §3 single protocol + record/plug split → Phase 3 (Task 3.1-3.5), Phase 2 (records).
- §5 ReconPlug + content readout → Task 2.1-2.3, 3.1.
- §5b den Boer 'I_5 rebuild → Phase 5 (Task 5.1-5.5).
- §6 input-commitment (new wrappers) → Phase 6 (Task 6.1-6.3).
- §8 recon-symmetry drop → Task 2.3, 2.5-2.9.
- §9/§12 genus honesty → Task 4.5 Step 2.
- §11 wreath retirement → Phase 4 (parity) + Phase 7 (delete).
- §14 axiom bar + wire-unchanged → Task 1.2 baseline + per-task `Print Assumptions`; §5a relied on by Task 3.1 (`dealt_hand_content_id`).
- §15 phasing → Phases 1-7 in order. §16 risks → flagged in Task 3.1 (duality), 5.3 (net-new lemma), 6.2 (HIGH duality).
No spec requirement is unmapped.

**Placeholder scan:** proof bodies for net-new lemmas (Tasks 2.1 step 2, 4.x, 5.2-5.4, 6.1-6.2) are given as exact statements + named-lemma strategies, not "TBD"; the `...` in skeletons (`fc_face`, `fc_cut_perm`, `pgg_commit`, `assemble`) mark terms the executor derives against the live file with rocq-mcp, each with the deriving method stated. These are genuine development tasks, not hidden placeholders, because the statement, the inputs, and the acceptance (compile + axiom diff) are complete.

**Type consistency:** `rp_scheme`/`rp_content`/`rp_monodromy`/`rp_recon_invariant`, `cs_plug`/`cs_data`/`cs_gap`, `cs_scheme` (notation), `mp_plug`, `run_dealer`/`run_recover`, `fcI_scheme`/`fcI_perm_compatible`, `fc_content`/`encode_bool`/`decode_bool`, `den_boer_plug`/`s5x5_plug`/`s5_plug` are used consistently across tasks. `ReconPlug`'s `rp_scheme` is `ThresholdScheme 'I_(pgg_N' M).+1 ...` matching the GATE-1-validated shape; the genus builders and instance literals all feed `id` content.

---

## Execution Handoff

Plan complete and saved to `docs/superpowers/plans/2026-06-07-pgg-protocol-merge.md`. Two execution options:

1. **Subagent-Driven (recommended)** — dispatch a fresh `rocq-prover` subagent per task, review between tasks, fast iteration. Best fit here: every task ends in a compile + `Print Assumptions` check the reviewer can verify, and the proof-development tasks (Phases 5-6) want a focused agent with rocq-mcp.
2. **Inline Execution** — execute tasks in this session via executing-plans, batch with checkpoints at each phase green gate.

Which approach?
