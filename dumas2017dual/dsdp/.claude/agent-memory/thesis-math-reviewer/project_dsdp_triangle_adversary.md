---
name: dsdp-triangle-adversary
description: Recurring math issue — dsdp.tex triangle display uses guess∘A as adversary while the cited triangle lemma and the feeding per-hop bounds hold for bare A
metadata:
  type: project
---

dsdp.tex:677-679 (subsec:dsdp:triangle) displays
`AdvantageE game_real game_enc_zero (guess ∘ A) ≤ 2 ε_cpa`
attributed by sidenote to `advantage_game_real_game_enc_zero`.

**Why this is a problem:** that lemma concludes for the BARE adversary
`predictor` (= thesis A): `AdvantageE game_real game_enc_zero predictor ≤
epsilon_cpa+epsilon_cpa`. The two per-hop bounds at dsdp.tex:664-667 that the
triangle sums also use bare `A`. A triangle inequality must hold the SAME
adversary fixed across LHS and all summands; writing the LHS with `guess ∘ A`
while the summands use `A` breaks the triangle algebra and mis-cites the lemma.
The `guess` (guessing_challenger) wrapper only enters later, in `Pr_guess_le`,
and there as `guessing_challenger ∘ par predictor (ID game_iface)`, not `guess∘A`.

**How to apply:** when reviewing the dsdp computational chain, check that every
AdvantageE in the triangle/per-hop displays uses the same fixed adversary symbol.
The `guess`-wrapper belongs to the probability-closing step (Pr_guess_le /
guessing_experiment), not the advantage triangle. See
[[ssprove-advantage-conventions]] for the full naming map.
