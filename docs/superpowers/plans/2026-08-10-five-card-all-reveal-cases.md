# Five-Card All-Reveal-Cases Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Land `leak_view_set` (mutual information of every reveal pattern) in `five_card_leakage.v` and restore the wadt2026 paper's "every reveal pattern" claim.

**Architecture:** Everything is already proven in the committed probe `docs/superpowers/probes/2026-08-10-five-card-all-reveals/probe_round2.v` (33 Qed, all 32 master branches real, single Admitted support `leak_k3_gap`). Task 1 proves `leak_k3_gap` by the `leak_k3` template. Task 2 transcribes the probe into the permanent file with declarative comments and H-series tags. Task 3 edits the paper, gated on the `.vo`.

**Tech Stack:** Rocq + MathComp 2.4 + infotheo; rocq-mcp for all checking; `make -j1` for `.vo` persistence; `ROCQ_AUDIT_BYPASS=fast` on every commit (user directive 2026-08-10).

**Spec:** `docs/superpowers/specs/2026-08-10-five-card-all-reveal-cases-design.md` (approved 2026-08-10). Probe source of truth: `probe_round2.v` at commit `aafcc92c`.

---

### Task 1: `leak_k3_gap` in `five_card_leakage.v`

**Files:**
- Modify: `pgg-smc/instances/denboer1989/five_card_leakage.v` (insert after `leak_k3`, i.e. after line 522's `Qed.`, before the `leak_k4` comment block at line 524)

**Fibre ground truth** (spec, machine-audited twice): view fibres over
`(a0, a1, a2) := colours at positions (0, 1, 3)`:
nv: TTT 3, TTF 2, TFT 4, TFF 3, FTT 4, FTF 3, FFT 1, FFF 0.
nt (secret true): TTF 2, TFT 1, FTT 1, FFT 1, rest 0.
nf (secret false): TTT 3, TFT 3, TFF 3, FTT 3, FTF 3, rest 0.
Non-deterministic fibres: TFT and FTT, both (nv, nt, nf) = (4, 1, 3) — exactly the `binent_1_4` pair, as in `leak_k3`.

- [ ] **Step 1: Insert the lemma** (template: `leak_k3`, lines 445-522 of the same file; only the position list, the three count tables, and the `bigD1`/`big1` case split differ)

```coq
(** leak_k3_gap — the gapped three cards {0, 1, 3} leak 6/5 - (9/20) log 3
    bits about a && b, the same value as the consecutive triple {0, 1, 2}.
    @main security: the mutual information between the secret and the colours
    at positions {0, 1, 3}. *)
Lemma leak_k3_gap :
  `I( Secret ; ViewA [:: 0; 1; 3]%N ) = 6%:R / 5%:R - (9%:R / 20%:R) * log 3%:R.
Proof.
rewrite mutual_info_RVE H_secret centropy_RVE'.
have cardV3 : forall a0 a1 a2 : bool,
  #|preim (ViewA [:: 0; 1; 3]%N) (pred1 [tuple of [:: a0; a1; a2]])| =
  (if a0 then (if a1 then (if a2 then 3 else 2) else (if a2 then 4 else 3))
         else (if a1 then (if a2 then 4 else 3) else (if a2 then 1 else 0)))%N.
  move=> a0 a1 a2.
  rewrite -sum1_card (eq_bigl (fun w : Omega =>
     (nth false (arr w) 0 == a0) && (nth false (arr w) 1 == a1)
       && (nth false (arr w) 3 == a2))); last first.
    move=> w /=.
    by rewrite /ViewA inE /= -val_eqE /= !eqseq_cons andbT andbA.
  rewrite big_mkcond /= stepO.
  under eq_bigr=> ab _ do rewrite !big_ord_recl big_ord0 addn0 /=.
  rewrite stepBB !big_bool /=.
  by case: a0; case: a1; case: a2.
have cardJ3 : forall (s a0 a1 a2 : bool),
  #|preim [% Secret, ViewA [:: 0; 1; 3]%N]
      (pred1 (s, [tuple of [:: a0; a1; a2]]))| =
  (if s
   then (if a0 then (if a1 then (if a2 then 0 else 2) else (if a2 then 1 else 0))
               else (if a1 then (if a2 then 1 else 0) else (if a2 then 1 else 0)))
   else (if a0 then (if a1 then (if a2 then 3 else 0) else (if a2 then 3 else 3))
               else (if a1 then (if a2 then 3 else 3) else (if a2 then 0 else 0))))%N.
  move=> s a0 a1 a2.
  rewrite -sum1_card (eq_bigl (fun w : Omega =>
      (let: (a, b, _) := w in (a && b) == s)
        && ((nth false (arr w) 0 == a0) && ((nth false (arr w) 1 == a1)
            && (nth false (arr w) 3 == a2))))); last first.
    move=> w /=; rewrite inE /=.
    rewrite xpair_eqE /Secret /ViewA /=.
    by case: w => [[a b] k] /=; rewrite -val_eqE /= !eqseq_cons andbT.
  rewrite big_mkcond /= stepO.
  under eq_bigr=> ab _ do rewrite !big_ord_recl big_ord0 addn0 /=.
  rewrite stepBB !big_bool /=.
  by case: s; case: a0; case: a1; case: a2.
have hterm : forall (t : (size [:: 0; 1; 3]%N).-tuple bool) (nv nt nf : nat),
   #|preim (ViewA [:: 0; 1; 3]%N) (pred1 t)| = nv ->
   #|preim [% Secret, ViewA [:: 0; 1; 3]%N] (pred1 (true, t))| = nt ->
   #|preim [% Secret, ViewA [:: 0; 1; 3]%N] (pred1 (false, t))| = nf ->
   (0 < nv)%N ->
   pfwd1 (ViewA [:: 0; 1; 3]%N) t * centropy1_RV (ViewA [:: 0; 1; 3]%N) Secret t =
   nv%:R / 20%:R *
   (- (nt%:R / nv%:R) * log (nt%:R / nv%:R)
    - (nf%:R / nv%:R) * log (nf%:R / nv%:R)).
  move=> t nv nt nf Hv Ht Hf Hpos.
  by rewrite count_pr Hv (condent_ratio Hv Ht Hf Hpos).
rewrite (bigD1 [tuple of [:: false; true; true]]) //=.
rewrite (bigD1 [tuple of [:: true; false; true]]) //=.
rewrite big1; last first.
  move=> i; case/tupleP: i => a0 /tupleP[a1 /tupleP[a2 a3]].
  rewrite (tuple0 a3) /=.
  case: a0; case: a1; case: a2 => //=.
  - move=> _; rewrite (hterm [tuple true; true; true] 3 0 3 (cardV3 true true true)
      (cardJ3 true true true true) (cardJ3 false true true true) (ltn0Sn _))
      (binent_det0 (ltn0Sn _)) mulr0 //.
  - move=> _; rewrite (hterm [tuple true; true; false] 2 2 0 (cardV3 true true false)
      (cardJ3 true true true false) (cardJ3 false true true false) (ltn0Sn _))
      (binent_det1 (ltn0Sn _)) mulr0 //.
  - move=> _; rewrite (hterm [tuple true; false; false] 3 0 3 (cardV3 true false false)
      (cardJ3 true true false false) (cardJ3 false true false false) (ltn0Sn _))
      (binent_det0 (ltn0Sn _)) mulr0 //.
  - move=> _; rewrite (hterm [tuple false; true; false] 3 0 3 (cardV3 false true false)
      (cardJ3 true false true false) (cardJ3 false false true false) (ltn0Sn _))
      (binent_det0 (ltn0Sn _)) mulr0 //.
  - move=> _; rewrite (hterm [tuple false; false; true] 1 1 0 (cardV3 false false true)
      (cardJ3 true false false true) (cardJ3 false false false true) (ltn0Sn _))
      (binent_det1 (ltn0Sn _)) mulr0 //.
  - move=> _; rewrite count_pr (cardV3 false false false) /= !mul0r //.
rewrite (hterm [tuple false; true; true] 4 1 3 (cardV3 false true true)
  (cardJ3 true false true true) (cardJ3 false false true true) (ltn0Sn _)).
rewrite (hterm [tuple true; false; true] 4 1 3 (cardV3 true false true)
  (cardJ3 true true false true) (cardJ3 false true false true) (ltn0Sn _)).
rewrite !binent_1_4 addr0.
lra.
Qed.
```

Tactical details (goal ordering inside `big1`, `//=` placement) may need
adjustment against the live goal via `rocq_check`/`rocq_step_multi`; the
STATEMENT and the three count tables are fixed and must not change. The
count tables are the load-bearing content; if a count refuses, the table
transposition is wrong, not the enumeration (spec fibre table is
double-audited).

- [ ] **Step 2: Check the lemma compiles in place**

Run: `mcp__rocq-mcp__rocq_compile_file` on `pgg-smc/instances/denboer1989/five_card_leakage.v`
Expected: success, empty error output.

- [ ] **Step 3: Verify the assumption cone**

Run: `mcp__rocq-mcp__rocq_assumptions` name=`leak_k3_gap` file=`pgg-smc/instances/denboer1989/five_card_leakage.v`
Expected: exactly the boolp trio (`propositional_extensionality`, `functional_extensionality_dep`, `constructive_indefinite_description`), nothing else.

- [ ] **Step 4: Persist the .vo**

Run: `make -j1 pgg-smc/instances/denboer1989/five_card_leakage.vo`
Expected: rebuild succeeds (rocq_compile_file does not persist the .vo; make does).

- [ ] **Step 5: Commit**

```bash
git add pgg-smc/instances/denboer1989/five_card_leakage.v
ROCQ_AUDIT_BYPASS=fast git commit -m "denboer1989: leak_k3_gap — gapped three-card reveal leaks 6/5 - (9/20) log 3, equal to the consecutive triple"
```

---

### Task 2: Transcribe probe_round2.v into `five_card_leakage.v`

**Files:**
- Modify: `pgg-smc/instances/denboer1989/five_card_leakage.v`
  - line 24 (first mathcomp import line): append ` div` → `From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.`
  - line 28: append ` five_card_group` → `From pgg_smc Require Import five_card_program five_card_group.`
  - insert the whole new block after `leak_k5`'s `Qed.` (line 560), before `End five_card_leakage.`
- Source of truth (verbatim proof bodies): `docs/superpowers/probes/2026-08-10-five-card-all-reveals/probe_round2.v`

**Transcription deltas (the ONLY permitted differences from the probe):**
1. DROP probe lines 48-50 (`Local Notation P/Secret/ViewA` pinning) — inside the section these are the section's own constants.
2. DROP probe lines 409-415 (`leak_k3_gap` Admitted) — Task 1 landed the real lemma earlier in the file; `leak_view_set`'s reference resolves to it.
3. KEEP probe lines 52-56 (`Local Notation p0..p4`) at the top of the new block.
4. REWRITE every comment declaratively (one sentence, what the object IS; no probe bookkeeping, no status narration) and ADD exactly one H-series tag per declaration, per the table below.
5. Everything else — statements, proof bodies, order — verbatim from the probe (lines 62-407 and 417-748).

**Comment + tag table** (declaration order = probe order; `@intent` for definitions, `@composes: <target>` for helpers, `@main security` for the theorem-level results):

| Declaration (probe line) | Tag line |
|---|---|
| `ViewT` (62) | `@intent: the partial view at a tuple of positions; component i reads the colour of arr w at position tnth t i.` |
| `ViewS` (67) | `@intent: the partial view at a set of positions, read in ascending enumeration order via enum_tuple.` |
| `adjacent` (72) | `@intent: the two elements of a 2-set lie at cyclic distance 1, i.e. S = {i, sigma i} for some i.` |
| `leak` (79) | `@intent: the closed-form leakage of a reveal pattern, classified by cardinality with the adjacency split at two cards.` |
| `setb5` (95) | `@intent: the subset of 'I_5 whose membership vector is the five given bits.` |
| `mem_setb5` (99) | `@composes: card_setb5` |
| `exists_ord5` (105) | `@composes: adjacentE` |
| `setb5_eq` (122) | `@composes: adjacentE` |
| `adjacentE` (135) | `@composes: leak_view_set` |
| `setb5_onto` (164) | `@composes: leak_view_set` |
| `enum_val5` (174) | `@composes: enum_setb5` |
| `card_val5` (183) | `@composes: card_setb5` |
| `card_setb5` (188) | `@composes: leak_view_set` |
| `enum_setb5` (195) | `@composes: leak_view_set` |
| `leakE0` (202) … `leakE5` (225), all seven | `@composes: leak_view_set` |
| `injective_mutual_info_RV` (234) | `@composes: mutual_info_ViewT_rot` (comment notes upstream candidacy next to infotheo's `injective_joint_entropy`) |
| `rot_tuple_inj` (248) | `@composes: mutual_info_ViewT_rot` |
| `ViewTE` (253) | `@composes: ViewT_rot` |
| `ViewT_rot` (258) | `@composes: mutual_info_ViewT_rot` |
| `mutual_info_ViewT_rot` (266) | `@composes: leak_view_set` |
| `mutual_info_ViewS_ViewT` (274) | `@composes: leak_view_set` |
| `val_fc_sigma_fun` (285) | `@composes: ViewT_sigma` |
| `fc_sigmaKV` (290) | `@composes: cut_sigmaKV` |
| `cut_sigma` (294) | `@intent: the sample-space map advancing the cut by one cyclic shift, identity on the two input bits.` |
| `cut_sigma_inv` (298) | `@intent: the sample-space map retracting the cut by one cyclic shift.` |
| `cut_sigmaK` (301) | `@composes: fdistmap_cut_sigma` |
| `cut_sigmaKV` (304) | `@composes: fdistmap_cut_sigma` |
| `fdistmap_cut_sigma` (309) | `@composes: mutual_info_ViewT_sigma` |
| `ViewT_sigma` (320) | `@composes: mutual_info_ViewT_sigma` |
| `mutual_info_ViewT_sigma` (341) | `@composes: leak_view_set` |
| `map_tnth` (356) | `@composes: ViewT_ViewA` |
| `ViewT_ViewA` (366) | `@composes: leak_view_set` |
| `leak_k0` (381) | `@main security: the empty reveal carries no information about the secret.` |
| `leak_view_set` (417) | `@main security: for every subset of the five positions, the mutual information between the secret and the revealed colours equals the closed form leak; all thirty-two reveal patterns in one statement.` |

- [ ] **Step 1: Apply the two import edits and insert the block** (per the deltas and table above)

- [ ] **Step 2: Check the file compiles**

Run: `mcp__rocq-mcp__rocq_compile_file` on `pgg-smc/instances/denboer1989/five_card_leakage.v`
Expected: success, empty output.

- [ ] **Step 3: Verify the assumption cone of the master theorem**

Run: `mcp__rocq-mcp__rocq_assumptions` name=`leak_view_set` file=`pgg-smc/instances/denboer1989/five_card_leakage.v`
Expected: EXACTLY the boolp trio. `leak_k3_gap` must NOT appear (it is Qed in the same file now). Also run for `injective_mutual_info_RV`: boolp trio only.

- [ ] **Step 4: Persist the .vo and rebuild the reverse-dependency closure, strictly `-j1`**

Run, in order:
```bash
make -j1 pgg-smc/instances/denboer1989/five_card_leakage.vo
make -j1 pgg-smc/instances/denboer1989/denboer_secrecy.vo
make -j1 pgg-smc/instances/denboer1989/denboer_trace.vo
make -j1 pgg-smc/instances/denboer1989/den_boer_encoding.vo
make -j1 pgg-smc/instances/kim2025/kim_secrecy.vo
make -j1 pgg-smc/instances/kim2025/kim_trace.vo
make -j1 pgg-smc/instances/kim2025/kim_input_privacy.vo
make -j1 pgg-smc/security/pgg_cyclic_cut_leakage.vo
```
Expected: every target rebuilds clean (spec verification gate 2). If a
path does not exist under these names, locate the true reverse-dependency
set with `git grep -l "Require.*five_card_leakage"` and rebuild those.

- [ ] **Step 5: Commit**

```bash
git add pgg-smc/instances/denboer1989/five_card_leakage.v
ROCQ_AUDIT_BYPASS=fast git commit -m "denboer1989: leak_view_set — mutual-information leakage of every reveal pattern, all 32 subsets, one theorem

Rotation equivariance via the group file's fc_sigma cyclic shift,
injective view relabeling, one general ViewT/ViewA bridge, and the
closed-form classifier leak with the adjacency split at two cards.
Assumption cone: boolp classical trio only."
```

---

### Task 3: Paper edits (gated on Task 2's clean `.vo` closure)

**Files:**
- Modify: `pgg-smc/paper-wadt2026/main.tex` (three loci; verify current line numbers with grep before editing — content anchors below are authoritative, not the line numbers)

- [ ] **Step 1: Contribution bullet** (lines 138-139). Replace

```
  conjunction output, exact mutual-information leakage values for six
  reveal patterns, executed-trace secrecy for a single corrupted player,
```

with

```
  conjunction output, exact mutual-information leakage values for every
  reveal pattern, executed-trace secrecy for a single corrupted player,
```

- [ ] **Step 2: Five-card section sentence and footnote** (line 592 region). Replace

```
Figure~\ref{fig:fivecard-leakage} quantifies six reveal patterns
exactly.\footnote{\coqin{leak\_k1}, \coqin{leak\_k2\_adj},
\coqin{leak\_k2\_dist2}, \coqin{leak\_k3}, \coqin{leak\_k4},
\coqin{leak\_k5}, and the cap \coqin{H\_secret} in
\path{pgg-smc/instances/denboer1989/five_card_leakage.v}. For example
\coqin{leak\_k2\_adj} $=\tfrac{27}{10}-\tfrac14\log 5-\tfrac{7}{10}\log
7$.}
```

with

```
Figure~\ref{fig:fivecard-leakage} quantifies every reveal pattern
exactly.\footnote{The master theorem \coqin{leak\_view\_set} covers all
thirty-two position subsets in one statement, anchored by \coqin{leak\_k1},
\coqin{leak\_k2\_adj}, \coqin{leak\_k2\_dist2}, \coqin{leak\_k3},
\coqin{leak\_k3\_gap}, \coqin{leak\_k4}, \coqin{leak\_k5}, and the cap
\coqin{H\_secret} in
\path{pgg-smc/instances/denboer1989/five_card_leakage.v}. For example
\coqin{leak\_k2\_adj} $=\tfrac{27}{10}-\tfrac14\log 5-\tfrac{7}{10}\log
7$.}
```

- [ ] **Step 3: Add the equal-three-card-values sentence.** In the same
paragraph, after the sentence ending "…the ramp climbs to the secret's own
entropy $2-\tfrac34\log 3\approx 0.811$." insert:

```
Every three-card reveal leaks the same $\tfrac65-\tfrac{9}{20}\log 3$
bits, so only the two-card case distinguishes the pattern's shape,
adjacent versus distance two.
```

(House rules hold: no em-dashes, no parenthetical asides, no
abbreviations; the figure caption at line 644 stays unchanged.)

- [ ] **Step 4: Build the paper and check the page count**

Run (in `pgg-smc/paper-wadt2026/`): the project's usual build — `latexmk -pdf main.tex` if `latexmk` is available, else `pdflatex main.tex` twice.
Expected: clean build; page count stays 21 (check with `pdfinfo main.pdf | grep Pages` or the last page number in `main.log`).

- [ ] **Step 5: Commit**

```bash
git add pgg-smc/paper-wadt2026/main.tex
ROCQ_AUDIT_BYPASS=fast git commit -m "wadt2026: every-reveal-pattern claim restored, licensed by leak_view_set; equal three-card leakage noted"
```

---

### Task 4: Close out

- [ ] **Step 1: Update auto-memory** — rewrite
`~/.claude/.../memory/project_five_card_leakage.md` (or add a linked memory) to record: `leak_view_set` all-32-subsets master theorem landed, boolp-only; every three-card reveal leaks equally; the idP-opacity bridge pattern; probe/audit trail location.

- [ ] **Step 2: Final report to the user** — commits, verification evidence, paper delta.

---

## Self-review

Spec coverage: Task 1 = spec implementation outline item 2; Task 2 = items 1 and 3 (imports + transcription, tags per outline text); Task 3 = item 4 and the spec's "Paper edits" section verbatim; verification gates 1-3 appear as Task 1 steps 2-4, Task 2 steps 2-4, and the bypass directive on every commit. Placeholder scan: none (the one deliberately flexible point — live line numbers in main.tex — is anchored by content snippets). Type consistency: names in the tag table match the probe inventory one-to-one; `leak_k3_gap`'s statement in Task 1 matches the probe's Admitted form and the spec's formal core.
