---
name: project_scope_patterns
description: Recurring scope-discipline patterns in the aplas2024-poster thesis (chapters/)
metadata:
  type: project
---

## Thesis root
`/Users/cheng-huiweng/Projects/aplas2024-poster/thesis/`

## Recurring pattern: named hop taxonomy in ssprove.tex

The ssprove chapter (Ch 12) introduces a two-type hop taxonomy ("perfect hop" /
"assumption-bounded hop") with \emph{} labels. Only "perfect" survives downstream;
"assumption-bounded" is never reused by name outside its defining paragraph. This
asymmetric named-taxonomy pattern (one term sticks, the other does not) may recur
in other background chapters that introduce binary classifications.

**Why:** The author writes the taxonomy generically in Ch 12 but the downstream
chapters (dsdp, game-swapping) use descriptive prose ("the only paid step", "costs
at most epsilon_cpa") rather than the named label.

**How to apply:** When a Ch 12 / background section introduces a pair of named
terms with \emph{}, immediately probe both names downstream. Expect the concrete
operational term to land but the abstract taxonomic label to be unused.

## Recurring pattern: Coq lemma parentheticals

Unit 1 (ssprove.tex:54-100) names three Coq lemma identifiers in parentheticals
(`link_assoc`, `Advantage_triangle`, `Advantage_triangle_chain`). None of these
identifiers appear downstream (the concept of the triangle inequality appears in
dsdp.tex prose, but the Coq lemma name is never cited again). This is the standard
situating-mention pattern — each is a one-clause parenthetical gloss, not a named
definition block, so SD1's exception applies and they are NOT flagged.

**How to apply:** When a background section cites Coq lemma names in parentheticals
(not sidenotes), treat them as situating mentions and do not flag unless they get
their own display or definition environment.

## Confirmed load-bearing items (never flag)

- `\approx_0` notation (ssprove.tex:49,68): used at dsdp.tex:624,628 and
  game-swapping.tex:340,342 and conclusions.tex:109. Load-bearing.
- `\coqin{Advantage_link}`: used at dsdp.tex:642 (sidenote). Load-bearing.
- `sec:ssprove:reduction` label: \ref'd at dsdp.tex:609. Load-bearing.
- `\emph{perfect}` hop term: concept used by name at dsdp.tex:625,629,632.
  Load-bearing.
- `subsec:dsdp:hops` label: not \ref'd downstream (only in aux). But unit is
  load-bearing by content; label absence is a reference concern, not scope.
- `$\mathsf{charlie}$` shorthand in dsdp.tex:619-649: used 5 times within the unit
  in displayed equations; dropped after the unit. Intra-unit alias, not
  introduced for nothing.
