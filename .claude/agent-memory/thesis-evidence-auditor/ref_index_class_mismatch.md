---
name: ref_index_class_mismatch
description: Prose-vs-formal terminology mismatch in interpreter.tex §3: "reducible" (prose) vs Disjoint constructor (formal); EDIT block evidence-interp-1 fixes it
metadata:
  type: project
---

In `chapters/interpreter.tex` lines 191-196, the inline prose says a party is classified as
"inert" or "reducible." The formal Rocq type `index_class` (smc/smc_interpreter_sound.v:216)
has constructors `Inert` and `Disjoint`. The sidenote in the same sentence correctly cites
`Inert` and `Disjoint`, but the inline prose uses the informal gloss "reducible."

**Why:** The `Disjoint` name reflects rstep_disjoint semantics (non-overlapping indices), not just
reducibility. The mismatch misleads readers tracing the code from the prose.

**How to apply:** When reviewing or editing §3 of interpreter.tex, confirm the inline text uses
"disjoint" (or "Disjoint") as the second class name, not "reducible." EDIT block evidence-interp-1
corrects this. See [[ref_interpreter_identifiers]].
