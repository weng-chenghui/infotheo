---
name: ssprove-chapter-gaps
description: All terms introduced in chapters/ssprove.tex that are absent from the glossary, with codebase refs and ungrounded status
metadata:
  type: project
---

## SSProve chapter (ch:ssprove) — terms absent from glossary

All 17 terms below are first introduced in chapters/ssprove.tex and do not appear in backmatter/list-of-terms.tex.

### Concept terms (no codebase ref needed)
- package: SSProve typed module with import/export interface
- sequential composition: monadic bind primitive
- linking ($\circ$): package composition operator
- sub-distribution semantics: code terms denote sub-distributions
- advantage ($\AdvantageE$): gap |Pr[D(G_0)=1] - Pr[D(G_1)=1]|
- indistinguishability ($\approx_0$): zero-advantage relation
- game hopping: transitioning between games via advantage bounds
- perfect hop: game hop contributing zero advantage
- assumption-bounded hop: game hop bounded by a hardness assumption
- game chain: ordered sequence G_0,...,G_n bounded by triangle inequality
- advantage linking: identity absorbing front-end into adversary
- front-end package: shared package routing adversary queries to chosen back-end
- shim: informal synonym for front-end package
- reduction: formal counterpart of textbook reduction = front-end package absorbed into adversary
- relative monad: code terms form a relative monad of sub-distributions
- state-separating: SSProve design principle (each package owns disjoint memory)

### Code terms (codebase refs grounded)
- raw_code: coq-ssprove/theories/Crypt/package/pkg_core_definition.v:92 (Inductive raw_code)
- code: coq-ssprove/theories/Crypt/package/pkg_core_definition.v:195 (Record code)
- code_of_send: infotheo-itp/smc/pismc_to_ssprove.v:124
- Advantage_triangle: coq-ssprove/theories/Crypt/package/pkg_advantage.v:188
- Advantage_triangle_chain: coq-ssprove/theories/Crypt/package/pkg_advantage.v:203
- Advantage_link: coq-ssprove/theories/Crypt/package/pkg_advantage.v:123
- link_assoc: coq-ssprove/theories/Crypt/package/pkg_composition.v:228

### Notation (defined in macros.tex, not in notation.tex)
- \\AdvantageE: defined in thesis/macros.tex line 25 as \\mathsf{AdvantageE}
- \\game{X}: defined in thesis/macros.tex line 26 as \\mathsf{game\\_X}

## Ungrounded (narrative) terms from ssprove.tex
- sequential composition, indistinguishability, game hopping, perfect/assumption-bounded hop, front-end/back-end package, shim, reduction, state-separating: no single Rocq identifier; glosses derived from prose

**Why:** The ssprove chapter is the scoped review chapter for the active review pass. All gaps here are highest priority for the term reviewer and the glossary-fix phase.
**How to apply:** When the term reviewer asks about any of these 17 terms, cite this file for first-intro location (ch:ssprove) and gap status.
