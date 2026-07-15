# Group Instances as Card Game Rules

**Date:** 2026-03-25

## Core Insight

Each physical card operation is a generator, and the allowed operations define the group.
The group instance IS the algebraic specification of the card protocol.

## Correspondence Table

| Card game rule | Generator type | Group family |
|---|---|---|
| Random cut (rotate pile) | n-cycle | Cyclic C_n |
| Cut + flip pile over | cycle + reflection | Dihedral D_n |
| Pile-scramble (full shuffle) | all transpositions | Symmetric S_n |
| Shuffle disjoint sub-piles independently | commuting generators on disjoint support | Direct product / RAAG |
| Riffle shuffle | specific interleaving | Subgroup of S_n (Gilbert-Shannon-Reeds) |
| Swap two specific positions | single transposition | Generated subgroup |

## Two Directions

**Group → Game**: Given a group presentation, what physical card operations does it prescribe? Is there a natural deck manipulation that realizes it?

**Game → Group**: Given a real card game's allowed moves, what group do they generate? What security does that group's action provide?

## Non-trivial Questions

- Not every abstract group has a natural "card game realization" — which ones do?
- Two different rule sets might generate the same group (same security) but feel like different games
- The number of cards N and the group G are independent choices — the action connects them

## What the Group Kind Determines

**Generators** = which physical operations are allowed
- C_n: one rotation (random cut)
- D_n: rotation + reflection (cut + flip the pile)
- S_n: all transpositions (pile-scramble)
- RAAG-star: generators with specified commutativity (independent operations on disjoint card subsets)

**Relations** = physical constraints on how operations compose
- Commutativity: operations on disjoint subsets are independent
- Involutions: flipping twice = identity
- Order relations: n cuts = identity

**Spectral gap** = mixing rate in exchange phase
- This depends on the Cayley graph structure, which is about group kind, not size

## Security Connection

- Regularity (free + transitive action) gives eps=0 (perfect security)
- This is a property of the *action*, not the abstract group
- The same group can act regularly on one set and non-regularly on another
- Existing card-based crypto literature typically fixes the shuffle type per protocol and analyzes security ad hoc
- PGG framework lets you parameterize over the group and get security theorems generically

## Relevance to WADT 2026

This is the algebraic specification story: group presentations specify card protocols,
and algebraic properties of the group action yield security guarantees.
Different algebraic theories (cyclic, dihedral, symmetric, RAAG) correspond to
genuinely different protocol families — a rich study field.
