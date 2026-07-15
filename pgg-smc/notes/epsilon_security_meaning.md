# PGG-SMC: What epsilon = 2(N! - T^L) / N! means for security

*2026-03-07*

## Relation between (k, T)-security and epsilon-security

**(k, T)-security** says: any coalition of k out of T parties learns nothing about the secret beyond what their shares already reveal. The standard MPC definition is simulation-based -- there exists a simulator that can produce the adversary's view without knowing the secret.

**epsilon-statistical security** (what we have) says: the adversary's view is within variational distance epsilon of the ideal (uniform) distribution.

**How they connect in our formalization:**

The `collusion_bound` theorem in `pgg_collusion_bound.v` is actually a (T-1, T)-security statement -- it bounds what T-1 colluding parties learn. Specifically:

- The adversary observes T-1 shares (evaluations at T-1 points)
- `var_dist_lfree_eval` says: for *any* evaluation point `eval_at`, the adversary's marginal view is epsilon-close to uniform
- This is (T-1, T)-security with statistical gap epsilon

**What's missing for general (k, T)-security:**

Right now we only handle k = T-1 (all-but-one corruption). For k < T-1:
- The adversary sees k < T-1 shares
- They have *less* information, so security should be *better* (smaller epsilon)
- But we haven't formalized this -- we'd need to show that observing fewer evaluation points only decreases variational distance

**The gap:** We don't yet have a theorem of the form "for any k-subset of parties, the joint view of those k parties is epsilon_k-close to ideal, where epsilon_k <= epsilon_{T-1}." This would require reasoning about joint distributions of multiple evaluation points, not just one.

**In principle**, (T-1, T)-security with small epsilon implies (k, T)-security for all k <= T-1 with at most the same epsilon (data processing inequality -- less information can't help). But we haven't formalized this implication explicitly.

## Security parameters

| Parameter | Role in epsilon = 2(N! - T^L) / N! |
|-----------|-------------------------------|
| **L** (word length) | Longer L -> more achievable permutations -> smaller epsilon |
| **N** (sheet count) | Larger N -> larger S_N -> harder to saturate -> larger epsilon |
| **Group structure** (commutativity) | Determines the *effective* growth rate of T^L |

## What epsilon measures

The bound `epsilon = 2(N! - T^L) / N!` is the **maximum advantage any adversary gains** over random guessing, regardless of computational power.

Concretely: suppose an adversary sees T-1 out of T shares and wants to guess information about the remaining secret share. In the ideal world, the secret share is uniformly random (the adversary learns nothing). epsilon measures how far the real protocol deviates from this ideal:

- **epsilon = 0**: The adversary's view is identically distributed to the ideal -> **perfect security** (like DSDP)
- **epsilon = 0.01**: For any yes/no question about the secret, the adversary's probability of answering correctly is at most 0.5 + 0.005 above random guessing -> **statistical security**
- **epsilon = 1**: The adversary can perfectly distinguish real from ideal -> **no security**

This is variational distance, the standard metric in cryptography. It directly bounds the success probability of *any* distinguishing strategy: `Pr[A outputs 1 | real] - Pr[A outputs 1 | ideal] <= epsilon/2`.

## The dual role of N (sheet count)

N plays a dual role:

1. **Secret space size**: Larger N -> more possible secret values -> more information can be encoded -> **good**
2. **Group size**: Larger N -> S_N has N! elements -> need more words to cover -> harder to make epsilon small -> **bad**

So there's a **tradeoff**. Doubling N gives you twice the secret space, but the group S_N explodes factorially, making epsilon much worse unless you also increase L or T to compensate.

**The real security question is the ratio**: how fast does T^L grow relative to N!?

- If T and L grow with N such that T^L / N! -> 1, then epsilon -> 0 despite larger N
- If N grows faster than T^L can keep up, epsilon stays large

**Practical implication**: You can't just crank up N for "more security." You need to co-design N, T, L together:
- Fix the desired epsilon (say 2^{-128})
- Choose T generators that span S_N (or a large subgroup)
- Choose L such that T^L ~ N!, i.e., L ~ log(N!) / log(T) ~ N*log(N) / log(T)

So L scales roughly as O(N log N) for fixed T -- the protocol gets longer as the secret space grows.

## How commutativity affects security (it's about uniformity, not reachability)

**How the protocol works**: The dealer picks a random word `W = w_1 w_2 ... w_L` of length L over the T generators. This word evaluates to a permutation `sigma_W = sigma_{w_1} * sigma_{w_2} * ... * sigma_{w_L}` in S_N. The security relies on `sigma_W` being close to uniformly distributed over S_N.

**Where commutativity enters**: Different words can evaluate to the *same* permutation. If `sigma_i * sigma_j = sigma_j * sigma_i`, then the words "ij" and "ji" give the same permutation. This means:

- T^L total words exist (each letter chosen from T generators)
- But only |achievable(L)| <= T^L *distinct* permutations result
- The gap T^L - |achievable(L)| is wasted -- multiple words "pile up" on the same permutation

**The non-uniformity problem**: It's worse than just losing distinct values. When words collide, some permutations get hit *more often* than others. The distribution over S_N becomes lumpy, not uniform. Variational distance measures exactly this lumpiness.

**Concrete example** (T=3 generators, L=2):
- 9 total words: aa, ab, ac, ba, bb, bc, ca, cb, cc
- If a and b commute: "ab" and "ba" give the same sigma -> that permutation has probability 2/9 instead of 1/9
- The distribution is biased toward permutations reachable by commuting pairs

**With full commutativity** (abelian): massive collapse. The word "abcba" = "aabbc" = same permutation. Only the *multiset* of letters matters, not the order. So ~L^T/T! distinct values instead of T^L.

**With no commutativity** (free-like): every distinct word gives a distinct permutation (if L-free). The distribution is uniform over achievable(L). Best case.

So commutativity doesn't change *which* permutations are reachable -- it changes *how uniformly* the random word sampling covers them.

## Effect of group structure on growth rate

Commutativity relations determine how many distinct permutations you actually get from T^L words:

- **No commutativity** (free-like): T^L distinct words -> T^L distinct permutations (if L-free)
- **Full commutativity** (abelian): T^L words but only ~L^T/T! distinct permutations (multinomial collapse)
- **Partial commutativity** (RAAG): growth rate determined by the clique polynomial of the commutation graph, between the two extremes
