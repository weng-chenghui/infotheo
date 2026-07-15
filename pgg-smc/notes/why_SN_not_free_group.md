# PGG-SMC: Why S_N (not free groups) gives perfect security

*2026-03-07*

## The confusion

Originally we thought "ideally" a free group gives perfect security, but what matters for PGG security is **coverage of S_N**, not freeness.

## Why S_N is the target, not free groups

The security metric is `epsilon = 2(N! - |achievable(L)|) / N!`. Perfect security (epsilon = 0) requires `|achievable(L)| = N!`, meaning every permutation in S_N is reachable. That's equivalent to `<<sigma_1,...,sigma_T>> = S_N`.

A free group on T generators has T^L distinct elements at length L -- but it's infinite, and when you map it into S_N via the generators, many distinct free group elements **collide** (map to the same permutation). Freeness gives you injectivity in the abstract group, but you're sampling from S_N, not from the free group.

## The key insight

L-freeness (our condition) is the *useful* finite approximation. It says: up to length L, no collisions happen. So you get T^L distinct permutations. But you only need T^L to reach N! -- after that, additional injectivity is wasted.

## The optimal situation

1. Generators span all of S_N (so every permutation is reachable)
2. L is large enough that T^L >= N! (so the word space saturates S_N)
3. L-freeness holds (so no wasted words up to length L)

Condition 1 is purely group-theoretic (e.g., any transposition + any N-cycle generates S_N). Conditions 2-3 control the rate of convergence.

## Practical consequence

You don't need exotic generators. Two well-chosen permutations (a transposition and an N-cycle) generate all of S_N. The question is just: how large must L be before T^L covers enough of S_N to make epsilon negligible?
