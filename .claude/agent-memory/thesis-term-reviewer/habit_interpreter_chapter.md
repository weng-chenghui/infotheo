---
name: habit-interpreter-chapter
description: Recurring grounding habits observed in chapters/interpreter.tex during the 2026-06-01 review run
metadata:
  type: feedback
---

The interpreter chapter has two recurring grounding weaknesses to flag immediately in future runs:

1. **pi-calculus first use lacks a back-anchor.** The term "pi-calculus" appears at the chapter's
   §1 (motivation) without a `(Chapter~\ref{ch:procalc})` anchor, despite being introduced earlier.
   Check for this on every future review of interpreter.tex or any chapter that follows ch:procalc.

2. **"scope extrusion" is never glossed.** It appears once (§2, no-name-passing sub-paragraph) and
   is absent from the term-map. Any future revision of interpreter.tex must carry an inline gloss.

3. **"sub-distribution semantics" has no map entry.** Used in §4 with only a forward cross-ref.
   If the term-map is updated for ch:ssprove, check whether the entry covers this term.

4. **Code constructors `Inert`, `Disjoint`, `reduction_spec`, `index_class`, `rstep_disjoint`,
   `step_sound`, `step_complete` are all correctly confined to sidenotes** -- this is the right
   pattern for the chapter and should be preserved in future edits.

**Why:** These habits were identified in the 2026-06-01 grounding review of interpreter.tex §3
(soundness-decomposition prose). The sidenote placement of all proof-internal code identifiers
was confirmed correct; no G1 violations were found.

**How to apply:** On any future review of interpreter.tex, immediately check lines 19-21 (pi-calc
back-anchor), line 103 (scope extrusion gloss), and line 252-254 (sub-distribution semantics
gloss). Also verify that `Inert`/`Disjoint`/`reduction_spec` remain confined to sidenotes.
