---
name: habit-dsdp-derived-terms
description: dsdp.tex subsec:dsdp:derived re-uses Part~\ref{part:derived} terms (symbolic run, control record, hop, corrupted view) with only a coarse part-level reference and no per-term section anchors — four G4 minor findings
metadata:
  type: feedback
---

In the coda subsection \label{subsec:dsdp:derived} (lines 758-783 of chapters/dsdp.tex),
the body prose imports four key Part~\ref{part:derived} terms without per-term back-anchors:

- "symbolic run" (line 760) -- first ch:dsdp body-prose use; defined in
  ch:derived-overview line 35 and sec:frontend:run. The existing Part~\ref{part:derived}
  reference is present but too coarse (part-level, not section-level).

- "control record" (line 770) -- first ch:dsdp body-prose use; introduced in
  ch:derived-overview lines 46-48. No anchor of any kind.

- "hop" (line 773, "receptions that count as hops") -- first ch:dsdp body-prose use of
  "hop" as a game-code concept; defined in ch:derived-backend sec:backend:syntax
  ("A hop is the one statement the ladder rewrites"). No anchor.

- "corrupted view" (line 777) -- first ch:dsdp body-prose use; introduced in
  ch:derived-overview line 49 and ch:derived-frontend. No anchor.

All four are rated G4 (minor). The sidenotes and captions in the same subsection
correctly keep all \coqin{} identifiers out of body prose (no G1 findings).

**Why:** The case-study chapters (ch:dsdp, ch:spp) are written as if the reader has
already absorbed Part~\ref{part:derived} in full. The coda subsection summarizes the
derivation without re-glossing the Part~\ref{part:derived} vocabulary. For a reader who
arrives via PDF cross-reference, the four terms are undefined.

**How to apply:** On any review of subsec:dsdp:derived (or its analogue in ch:spp),
check lines 758-783 for Part~\ref{part:derived} terms and verify each has a
section-level (not just part-level) back-anchor on its first ch:dsdp body-prose use.

Related: [[habit-derived-overview]] tracks the same terms being used as forward
dependencies in derived-overview.tex.
