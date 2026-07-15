---
name: map-build-protocol
description: Key build decisions for the term-map: chapter order source, SSProve external repo path, staleness check method, seniority rule
metadata:
  type: feedback
---

## Chapter order source
Read from thesis/main.tex \\input order. The map's chapter_order array is:
introduction, smc, infotheo, procalc, rocq, he, algebra, framework-overview,
interpreter, pismc, phantom, ssprove, hybrid-model, ahe, fiber, entropy-fiber,
gameswap, spp, dsdp, conclusions.

**Why:** main.tex is authoritative; it was reorganized (part:interpreter dissolved, ch:gameswap renamed from game-swapping) so always re-read on rebuild.

## SSProve external repo
SSProve 0.3.1 is installed at:
  /Users/cheng-huiweng/Projects/coq/_opam/.opam-switch/sources/coq-ssprove.0.3.1/theories/Crypt/

Key files:
- pkg_core_definition.v: raw_code (line 92), code (line 195), relative monad (line 389)
- pkg_advantage.v: Advantage_link (line 123), Advantage_triangle (line 188), Advantage_triangle_chain (line 203)
- pkg_composition.v: link_assoc (line 228)
- pkg_interpreter.v: Run (line 138)

**How to apply:** When grepping for SSProve identifiers, check the opam sources path above. The pgg-smc and infotheo-itp repos import from SSProve but do not define its core types.

## Staleness check
Use `find thesis/chapters -name "*.tex" -newer thesis/.thesis-review/term-map.json`. If any file is newer, rebuild. The notation.tex and list-of-terms.tex are also checked.

## Seniority rule
A term's first_intro is the earliest (chapter-order position, then line number) occurrence in the thesis body. For terms in ssprove.tex, the seniority is ch:ssprove unless the same identifier appears earlier (e.g., code_of_send first appears in ssprove.tex line 36, which is ch:ssprove order 12; that is earlier than ch:gameswap).

## pismc_to_ssprove.v location
infotheo-itp/smc/pismc_to_ssprove.v defines code_of_send (line 124) and code_of_proc. These bridge the two program layers.
