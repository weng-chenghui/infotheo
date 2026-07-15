# Fiber Framework vs. math-comp Orbit Lemmas

**Date**: 2026-03-24
**Question**: Should pgg-smc's fiber analysis be refactored to use math-comp's orbit/stabilizer infrastructure from `fingroup/action.v`?
**Conclusion**: No. The current fiber framework is strictly more general.

## The Correspondence

| infotheo (pgg-smc) | math-comp (fingroup/action.v) | Relationship |
|---|---|---|
| `fiber f c := [set x \| f x == c]` | `amove to G x y := [set a in G \| to x a == y]` | `amove` = `fiber` restricted to group `G`, when `f = fun a => to x a` |
| `image_set f` | `orbit to G x := to x @: G` | `orbit` = `image_set` when `f` is action evaluation over `G` |
| `centropy_constant_fibers` | `card_orbit_stab` | orbit-stabilizer *guarantees* constant fiber size (a special case of the hypothesis that `centropy_constant_fibers` takes) |
| `fiber_prob`: `P(g) = \|fiber g\| / Tg^L` | (no analogue) | infotheo adds the probability/entropy layer |

## Specialization Chain

```
General fiber (entropy_fiber.v)
    fiber f c = [set x | f x == c]            -- any f : A -> B
        |
        |  specialize f := (fun a => to x a), restrict domain to G
        v
Group-action fiber (action.v)
    amove to G x y = [set a in G | to x a == y]   -- requires group G
        |
        |  orbit-stabilizer theorem
        v
    amove to G x (to x a) = Stab(x) :* a          -- each fiber is a coset
    All fibers have size |Stab(x)| = |G| / |orbit(x)|
        |
        |  this satisfies the hypothesis of:
        v
centropy_constant_fibers:
    (forall c in image, |fiber c| = k) -> H(X|Y) = log(k)
```

## Concrete Instance: Endpoint Evaluation

The map `eval_s(sigma) = sigma(s)` in `pgg_collusion_bound.v`:

- `fiber eval_s a = [set sigma | sigma s == a]` = `amove 'P S_N s a` (definitionally)
- `image_set eval_s = orbit 'P S_N s = setT` (S_N transitive on I_N)
- `|fiber eval_s a| = N'!` = `|'C_{S_N}[s | 'P]|` (stabilizer cardinality)

The `Hcount` proof (line 198 of `pgg_collusion_bound.v`) establishes `#{sigma | sigma(s) = a} = N'!` via `prescribed`. The orbit-stabilizer route would derive this from `amove_act` + `card_rcoset` + transitivity. Same fact, different proof technique.

## Why the Fiber Framework is More General

1. **No group structure required**: `word_eval` fibers (`[set w | word_eval w == g]`) live over the free monoid of words. Words have no inverse, no coset structure. `amove` simply doesn't apply.

2. **Non-uniform fiber sizes**: orbit-stabilizer forces all fibers over the orbit to have the same cardinality. The fiber framework handles variable fiber sizes, needed for `var_dist_fdistmap_balanced` and the general `fiber_prob` lemma.

3. **Non-group index sets**: `schreier_gen_count x y = |{i : I_Tg | sigma_i(x) == y}|` counts over generator *indices*, which carry no algebraic structure.

4. **`prescribed` is more general than orbit-stabilizer**: `prescribed` counts permutations with specified values at *multiple* positions simultaneously. Orbit-stabilizer gives only the single-point case.

## math-comp Orbit Lemmas Available (for reference)

Key definitions and lemmas in `fingroup/action.v`:
- `orbit to A x := to x @: A` (line 196)
- `amove to A x y := [set a in A | to x a == y]` (line 198)
- `astab S to := D :&: [set a | S <= [set x | to x a == x]]` (line 202) — pointwise stabilizer
- `card_orbit_stab` (line 989): `|orbit to G x| * |'C_G[x | to]| = |G|`
- `amove_act` (line 737): `amove to G x (to x a) = 'C_G[x | to] :* a`
- `amove_orbit` (line 744): `amove to G x @: orbit to G x = rcosets 'C_G[x | to] G`
- `orbit_partition` (line 616): orbits partition the acted-on set
- `perm_prime_atrans` (line 2722): transitivity for prime-order cyclic groups (S_N transitivity is NOT in math-comp)

## Decision

No refactoring. The fiber framework's generality is a design feature, not an oversight. The two proofs that *could* use orbit-stabilizer (`ideal_marginal_uniform`, `fdistmap_eval_uniform`) work well with `prescribed` and don't benefit meaningfully from the switch.
