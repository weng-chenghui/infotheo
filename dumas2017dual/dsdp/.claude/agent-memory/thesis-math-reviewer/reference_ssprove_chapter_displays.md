---
name: ssprove-chapter-displays
description: Verified-correct state of the math displays in chapters/ssprove.tex (triangle, Advantage_link) against coq-ssprove 0.3.1 pkg_advantage.v — contrast with the broken dsdp.tex triangle
metadata:
  type: reference
---

Reviewed `chapters/ssprove.tex` (the abstract SSProve method chapter, distinct
from the concrete `dsdp.tex` chain). Ground truth: coq-ssprove 0.3.1
`theories/Crypt/package/pkg_advantage.v`.

**Triangle display (ssprove.tex:62-64) is CORRECT.**
`AdvantageE G_0 G_n A <= sum_{i=0}^{n-1} AdvantageE G_i G_{i+1} A`.
- Same adversary `A` on LHS and every summand (matches `Advantage_triangle`
  L188 and `advantage_sum`/`Advantage_triangle_chain` L197-205).
- Index range i=0..n-1 with games G_0..G_n is consistent: summands are
  (G_i,G_{i+1}) ending at (G_{n-1},G_n).
- This is the GOOD version. Contrast [[dsdp-triangle-adversary]] where dsdp.tex
  wrongly writes the LHS adversary as `guess ∘ A` while summands use `A`.

**Advantage_link display (ssprove.tex:82-86, repeated fig caption L115) is CORRECT.**
`AdvantageE (P∘G_0)(P∘G_1) A = AdvantageE G_0 G_1 (A∘P)`.
- Source lemma `Advantage_link` L123-126 is the flip (bare on LHS); equality is
  symmetric, fine. "Read left-to-right absorbs the shim P into the adversary" =
  the wrapped→bare direction. Prose matches the equation direction. See
  [[ssprove-advantage-conventions]].

**Open math-writing findings in this chapter (reported, not codebase issues):**
- M1: symbol `A` first appears in the L63 display with no "for an adversary A"
  binding; only described implicitly later (L89-90). Major.
- M3: `≈₀` introduced (L49) as "the advantage is zero, written ≈₀" — labels a
  scalar statement with a symbol that is actually a binary relation between
  games (used correctly as relation at L67). Minor.
- Precision (L47): "AdvantageE ... bounds the distance" — it IS/measures the
  distance |Pr(A∘G₀)-Pr(A∘G₁)|, not a bound on it. Minor overview-prose nit.
