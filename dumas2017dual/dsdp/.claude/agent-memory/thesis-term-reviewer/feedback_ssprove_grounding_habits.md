---
name: feedback-ssprove-grounding-habits
description: ch:ssprove (ssprove.tex) grounding habits confirmed on full chapter review (lines 1-166)
metadata:
  type: feedback
---

ch:ssprove habitually introduces SSProve package-algebra jargon ("front-end
package", "back-end", "shim") in body prose without a one-clause gloss. These
terms are absent from the glossary and no prior chapter introduces them.

Body parentheticals in §reduction routinely hold raw `\coqin{}` identifiers
(`link_assoc`, `Advantage_link`) that must be rewritten to concept descriptions
per the pen-and-paper rule. The `\coqin{Advantage_triangle}` / `\coqin{Advantage_triangle_chain}`
parentheticals at line 61 are ALLOWED (they label the displayed equation and are
definienda of the paragraph).

The word "linking" is overloaded: it names the package-composition operator $\circ$
in §semantics (line 34) and the proof-level "advantage linking" identity in §reduction
(line 73). Both uses lack disambiguation on first occurrence.

"Relative monad" appears in §semantics (line 41) as a subordinate-clause concept with
no gloss. First and only use; never defined in the thesis.

"State-separating" appears only in the related-work paragraph (line 157) without any
gloss; it is the SSProve design principle name and needs a one-clause explanation.

`\coqin{code_of_send}` is used in §semantics body prose (line 36) as a code identifier,
not as a section subject or definiendum — requires pen-and-paper rewrite.

`\coqin{code}` is re-used in §semantics (line 41) outside the §packages definiendum
context — requires pen-and-paper rewrite at that second occurrence.

All 17 conceptual terms introduced in ch:ssprove are absent from the glossary
(list-of-terms.tex) and the notation stub (notation.tex). This is a systematic gap
covering: package, sequential composition, linking, sub-distribution semantics,
advantage, indistinguishability, game hopping, perfect hop, assumption-bounded hop,
game chain, advantage linking, front-end package, shim, reduction (SSProve sense),
relative monad, state-separating, plus notations AdvantageE and approx_0.

**Why:** The author treats SSProve package vocabulary as shared knowledge, but the
thesis reader may not know the linking model. The glossary was not updated when
ch:ssprove was written.

**How to apply:** On any future run of ssprove.tex, flag all "front-end"/"back-end"/
"shim" uses and all body-prose `\coqin{}` parentheticals immediately. Also check for
"linking" disambiguation and "relative monad" gloss. These are recurring patterns.
