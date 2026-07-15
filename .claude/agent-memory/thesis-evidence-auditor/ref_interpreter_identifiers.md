---
name: ref_interpreter_identifiers
description: Verified Rocq identifiers cited in chapters/interpreter.tex, with file locations, types, and proof status (branch itp2026-dumas2017dual)
metadata:
  type: reference
---

All identifiers below are confirmed present and Qed-closed (no Admitted, no load-bearing Axiom/Parameter) as of 2026-06-01 on branch itp2026-dumas2017dual.

## smc/smc_interpreter.v

| Identifier | Line | Kind | Notes |
|---|---|---|---|
| `step` | 54 | `Definition` | single-party one-tick reducer |
| `interp` | 80 | `Fixpoint` | fuel-bounded full interpreter; fuel param `h` |
| `result_traces` | 142 | `Definition` | |
| `step_complete` | 145 | `Lemma` | 3-way case on rstep constructors; Qed line 164 |
| `rstep_disjoint` | 186 | `Lemma` | identical-or-disjoint disjunction; Qed |
| `rstep` | 117 | `Inductive` | 3 constructors: rinit, rret, rcomm |
| `rsteps` | 126 | `Inductive` | reflexive-transitive closure of rstep |
| `interp_traces` | 310 | `Definition` | packaged tuple form; distinct from `interp` |

## smc/smc_interpreter_sound.v

| Identifier | Line | Kind | Notes |
|---|---|---|---|
| `reduction_spec` | 68 | `Inductive` | 3 constructors: RSinit, RSret, RScomm |
| `index_class` | 216 | `Inductive` | 2 constructors: Inert, Disjoint (NOT "Reducible") |
| `step_sound` | 808 | `Lemma` | soundness of one interpreter round; Qed line 830 |

## du2002/spp_proof.v

| Identifier | Line | Kind | Notes |
|---|---|---|---|
| `scalar_product_uncurry` | 167 | `Definition` | trace-map from 6-tuple to party traces |
| `scalar_product_is_leakage_freeP` | 458 | `Theorem` | two-sided; Qed line 466; split → proof_alice + proof_bob |

**Why:** These are stable citations in chapters/interpreter.tex §3 (lines ~187-209). Skip re-fetching on future audits of this chapter unless the file changes.
