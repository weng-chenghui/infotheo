# RAAG-Star Search Space Analysis

## Search Space vs Word Length

For a word of length L over T generators (and their inverses where applicable):

| Group | Total words | Distinct σ_P values | Search space growth | Why |
|-------|------------|---------------------|--------------------|----|
| **Free F_T** (infinite, not realizable) | 2T·(2T−1)^{L−1} reduced words | 2T·(2T−1)^{L−1} (all distinct) | Exponential in L | No relations → every reduced word gives a different element |
| **Non-abelian S_{T+1}** (`pgg_nonabelian.v`) | T^L (involutions, so no inverses) | min(T^L, (T+1)!) | Exponential in L, capped at (T+1)! | Generators are involutions (σ²=1) so alphabet is T not 2T; all pairs non-commuting so order matters; but S_{T+1} is finite so saturates |
| **RAAG-star** (proposed, disjoint-support center) | T^L | min(T^L, (T+1)!·2) ≈ same as above | Same as non-abelian | G ≅ S_{m+1} × Z_2; the Z_2 factor is trivial; leaf generators alone already give S_{m+1} growth |
| **Abelian ⟨σ⟩** (`pgg_abelian.v`) | T^L | N (= cycle order) | Constant (independent of L) | σ_P = σ^{sum of exponents}; only the sum mod N matters, giving at most N values |

## Key Observations

1. **Free vs non-abelian**: Both exponential in L, but free has base 2T−1 while non-abelian (involutions) has base T. The free group never saturates; S_{T+1} saturates at (T+1)!

2. **RAAG-star ≈ non-abelian**: The disjoint-support center contributes a factor of 2 (Z_2), so the search space is essentially the same as the non-abelian case. The partial commutativity doesn't reduce the leaf subgroup's search space.

3. **Abelian is dramatically smaller**: O(N) regardless of L, because commutativity collapses the word to a single exponent sum.

## Conclusion

The RAAG-star (with disjoint-support center) doesn't create an interesting middle ground — it's basically the non-abelian case with a trivially commuting appendage. For a genuinely intermediate search space, you'd need commutativity relations **between generators that share support**, which would reduce the effective number of distinct products without collapsing everything to a single exponent. But transpositions can only commute via disjoint support, so achieving that requires non-transposition generators or a fundamentally different construction.

The two existing instances (abelian + non-abelian) already capture the meaningful security dichotomy.
