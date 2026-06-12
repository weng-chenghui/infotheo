# DSDP fiber leg — item 1 (`guess_cinde_V2`) session budget

Companion to `20260612-dsdp-fiber-item5-closed.md`. Branch
`itp2026-dumas2017dual`. Scopes item 1 (the remaining reflection) into
schedulable sessions with green checkpoints.

## Verdict: split, not contiguous

Every natural stopping point in item 1 is a committable (Qed, no-admit) tree.
The decomposition is 4 standalone lemmas (steps 1–4) + an assembly (step 5);
each sub-lemma has a writable statement. Any unfinished sub-lemma can be
threaded forward as an explicit `Hypothesis` (the `Hcinde`-through-items-6/7
mechanism already proven this session), so stopping mid-item-1 never forces an
`Admitted`. "Contiguous-or-bust" is a false constraint.

## Seams cluster by machinery → 2 nominal sessions

### Session A — reflection-warm (steps 1 + 2)
Shares the `drc_*` lemmas, the GC-term de Bruijn slot analysis, and `Pr_code_*`
peeling with item 2's `Hbody` block (`dsdp_security_indcpa_fiber.v:975–1260`).

- **Step 1 `guess_triple_proj_code`**: adapt `Hbody` to keep 3 coords
  (guess_M, V2_M, V3_M) instead of 2. Smaller than `Hbody`. Commit, Qed.
- **Step 2 `view_indep_secrets`**: the hard core — the run-reflection showing
  the cipher view (`vt.1.1`) is constant in the v2,v3 sample binders. ~item-2
  scale (the load-bearing new work). Statement not yet pinned; Session A's first
  job is to pin it.
- Commit-safe fallback: if step 2 overruns, commit step 1 alone and thread
  step 2's statement as a `Hypothesis`. Tree stays green.

### Session B — algebra/assembly-warm (steps 3 + 4 + 5)
Different toolkit: `Pr_fst_put_invariant` / `predictor_locs_disj` /
`resolve_predictor_valid` / `denote_output_termE` / `cinde_RV_factor`. None of
the reflection machinery is needed.

- **Step 3** predictor-kernel V2-independence (leans on committed
  `Pr_fst_put_invariant` + `predictor_locs_disj`).
- **Step 4** s_read = output (leans on committed `denote_output_termE`).
- **Step 5** the `f·g` factorization into `cinde_RV_factor` → `guess_cinde_V2`,
  then inline it into items 6/7 (drop the `Hcinde` binder). Risk: the
  code-derived `f,g` must typecheck against `cinde_RV_factor`'s shape (the
  "obvious f,g is circular" trap, already flagged). If it stalls, commit 3+4
  and thread.

## Budget

| | nominal | if a core step overruns |
|---|---|---|
| Sessions | 2 | 3 (rarely 4) |
| Wall-clock | ~3–4.5h (A ≈ 1.5–2.5h, B ≈ 1.5–2h) | +~1 micro-session per overrun |
| Green checkpoints | up to 5 (one per sub-lemma) | same — overrun degrades into one more micro-session, never a blown block |

Only step 2 is genuinely big. The default 2-session split is efficient because
each session keeps its machinery hot. Conservative alternative: step 2 as its
own session, with 1 riding in front and 3/4/5 behind.

Scheduling subtlety: once step 2's exact statement is pinned (even before its
proof closes), it becomes a threadable hypothesis — which is what would let
Session B run first to de-risk the `cinde_RV_factor` shape before grinding the
reflection.
