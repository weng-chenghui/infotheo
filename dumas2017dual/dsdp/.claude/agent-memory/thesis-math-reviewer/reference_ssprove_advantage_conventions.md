---
name: ssprove-advantage-conventions
description: SSProve Advantage_link orientation, link/∘ caller direction, and DSDP adversary-naming map used when reviewing ssprove.tex / dsdp.tex computational chains
metadata:
  type: reference
---

Ground-truth facts for reviewing the computational (SSProve) chapters of this thesis.

**Advantage_link** (coq-ssprove 0.3.1, pkg_advantage.v ~L123):
`AdvantageE G₀ G₁ (A ∘ P) = AdvantageE (P ∘ G₀) (P ∘ G₁) A`.
The thesis writes it flipped (wrapped form on LHS, bare form on RHS); equality is
symmetric so that is fine. "Read left-to-right absorbs the shim P into the adversary"
is the bare-RHS direction in SSProve, the wrapped-to-bare direction as printed in
ssprove.tex:81-85. Consistent.

**link / ∘ caller direction** (pkg_composition.v ~L228, L243):
`p1 ∘ p2 = link p1 p2`, right-associative at level 20. In `X ∘ Y`, X is the OUTER
caller: X imports the exports of Y and calls into it. So `P ∘ G` = front-end P
calling back-end/oracle G; `A ∘ P` = adversary A running reduction P as subroutine.
`link_assoc` RHS is left-associated: `link p1 (link p2 p3) = link (link p1 p2) p3`.

**DSDP adversary-naming map** (ref/dsdp_security_indcpa.v):
- thesis `A` (abstract adversary) = Rocq `predictor` (a predictor_guesser).
- thesis `charlie` = `game_via_oracle_charlie`; `predictor_via_oracle_charlie predictor
  = predictor ∘ pack game_via_oracle_charlie` = the absorbed reduction (thesis `A∘charlie`).
- thesis `guess` = `guessing_challenger` (V_2-aware boolean indicator).
- per-hop lemmas `advantage_hop_real_h1` (L1141) and `advantage_hop_h1_h2` (L1309) and
  the triangle lemma `advantage_game_real_game_enc_zero` (L1386) ALL fix the BARE
  `predictor` as adversary, NOT guess∘predictor.
- `Pr_guess_le` (L1662) is where guessing_challenger enters, with adversary
  `guessing_challenger ∘ par predictor (ID game_iface)` — note the `par … (ID
  game_iface)`, because guessing_challenger also imports id_v2_get from the game.
  So even there the adversary is NOT the simple `guess ∘ A`.
