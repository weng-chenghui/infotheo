---
name: ssprove-grounding-facts
description: Verified grounding anchors for thesis chapters/ssprove.tex — cite keys, macros, formal lemmas, and the EasyCrypt/CertiCrypt mis-cite trap
metadata:
  type: reference
---

Verified-real grounding anchors for `chapters/ssprove.tex` (thesis at
`/Users/cheng-huiweng/Projects/aplas2024-poster/thesis/`). Confirmed during a
STAGE=extend substance pass; re-verify existence before reusing (see "verify
before recommending").

**Citations (references.bib):**
- `HaselwarterEtAl2023` (references.bib:486) — SSProve, TOPLAS 2023, vol 45 no 3.
  The state-separating-proof framework in Coq/MathComp. Substantiates: packages
  with typed import/export interfaces; advantage/indistinguishability (its
  probabilistic relational logic); the shared-Coq-stack related-work claim.
  Paper confirmed via dl.acm.org/doi/10.1145/3594735 (also CSF 2021,
  eprint 2021/397).
- `Blanchet2006` (references.bib:396) — CryptoVerif, IEEE TDSC 2008.

**TRAP: `BartheEtAl2009` is CertiCrypt, NOT EasyCrypt.** references.bib:386 =
"Formal Certification of Code-Based Cryptographic Proofs", POPL 2009 (Barthe,
Gregoire, Zanella Beguelin). The thesis ssprove.tex related-work (lines 149-165)
mis-cites it as "EasyCrypt, built on top of Coq". EasyCrypt is NOT built on Coq.
There is NO genuine EasyCrypt bib entry. Never add `BartheEtAl2009` to ground an
EasyCrypt claim; the missing EasyCrypt citation is an evidence/reference defect.

**Macros:**
- `\AdvantageE` = macros.tex:25 (SSProve advantage operator).
- `\coqin{X}` = shared-macros.sty:40 (mintinline ssr). Route all code idents
  through it; never inline \mathrm/\textsc.

**Verified-real formal lemmas (route via \coqin):** in SSProve, used in
`/Users/cheng-huiweng/Projects/coq/infotheo-itp/dumas2017dual/dsdp/ref/dsdp_security_indcpa.v`
(canonical, NOT *_clone.v):
- `Advantage_triangle` (pkg_advantage) — plain triangle ineq, used :1111.
- `Advantage_triangle_chain` (pkg_advantage) — iterated form, used :1170+.
- `Advantage_link` (pkg_advantage) — front-end re-attribution, used :58154 glob.
- `link_assoc` (pkg_composition) — linking associativity.
- `raw_code` (pkg_core_definition) — effectful programs; `code` is typed wrapper.

**Thesis cross-ref labels (all resolve):** `ch:interpreter`
(chapters/interpreter.tex:1), `ch:gameswap` (game-swapping.tex:1),
`sec:gameswap:reduction` (:142), `sec:gameswap:bridge` (:314),
`sec:ssprove:reduction` (ssprove.tex:54).
