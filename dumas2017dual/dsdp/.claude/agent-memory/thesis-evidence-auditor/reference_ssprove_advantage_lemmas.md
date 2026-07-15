---
name: reference_ssprove_advantage_lemmas
description: SSProve pkg_advantage.v and pkg_composition.v — formal statements of Advantage_link, Advantage_triangle, Advantage_triangle_chain, link_assoc confirmed
metadata:
  type: reference
---

File: /Users/cheng-huiweng/Projects/coq/_opam/.opam-switch/sources/coq-ssprove.0.3.1/theories/Crypt/package/pkg_advantage.v

**Advantage_link** (line 123):
```
Lemma Advantage_link :
  ∀ G₀ G₁ A P,
    AdvantageE G₀ G₁ (A ∘ P) =
    AdvantageE (P ∘ G₀) (P ∘ G₁) A.
```

**Advantage_triangle** (line 188):
```
Lemma Advantage_triangle :
  ∀ P Q R A,
    AdvantageE P Q A <= AdvantageE P R A + AdvantageE R Q A.
```

**Advantage_triangle_chain** (line 203):
```
Lemma Advantage_triangle_chain :
  ∀ P (l : seq raw_package) Q A,
    AdvantageE P Q A <= advantage_sum P l Q A.
```
where `advantage_sum P [R₀;...;R_{n-1}] Q A` = `∑ᵢ AdvantageE Gᵢ G_{i+1} A` (recursive).

File: /Users/cheng-huiweng/Projects/coq/_opam/.opam-switch/sources/coq-ssprove.0.3.1/theories/Crypt/package/pkg_composition.v

**link_assoc** (line 228):
```
Lemma link_assoc :
  ∀ p1 p2 p3,
    link p1 (link p2 p3) = link (link p1 p2) p3.
```

Note: The thesis displays `Advantage_link` with LHS and RHS swapped vs the formal statement (thesis: `AdvantageE (P∘G₀)(P∘G₁) A = AdvantageE G₀ G₁ (A∘P)`). This is valid since equality is symmetric.
