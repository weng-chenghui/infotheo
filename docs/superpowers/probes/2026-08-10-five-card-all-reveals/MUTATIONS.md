# Mutation checks for the five-card all-reveal-cases probes

Date: 2026-08-10.
Spec: `docs/superpowers/specs/2026-08-10-five-card-all-reveal-cases-design.md`.

Every mutation below was run through `rocq_check` / `rocq_step_multi` against
the compiled probe context and **confirmed to fail**. None of the mutated code
is left in any `.v` file; the three probe files hold only the unperturbed,
compiling versions.

Method: start an interactive session on the compiled probe file
(`rocq_start(file=..., theorem=...)`, then `Abort.`), which puts every
definition and helper of that file in scope, then submit the perturbed
statement with the *original, unmodified* proof script.

---

## probe_objects.v

### M1 — `cardV013_FTT` claims 5 instead of the enumerated 4

Perturbation: `... = 5%N` in place of `... = 4%N`, proof script unchanged.

```
Unable to unify "5%N" with
 "(1 + (0 + (0 + (0 + 0))) + (0 + (0 + (0 + (1 + 0)))) +
   (0 + (0 + (0 + (0 + 1))) + (0 + (1 + (0 + (0 + 0))))))%N".
```

The residual goal is the raw 20-outcome enumeration, and it sums to
`1 + 1 + 1 + 1 = 4`. This is the machine confirming the Python fibre table
value `cardV013_FTT = 4` rather than the probe merely restating it.

### M2 — `nth_rot5` shifts the index by one: `(i + k + 1) %% 5`

Perturbation: `nth false s ((i + k + 1) %% 5)%N` in place of
`nth false s ((i + k) %% 5)%N`, proof script unchanged.

With the closing `by` the script reports `No applicable tactic.`. Running the
same case bash without the `by` shows all 25 concrete cases turn into false
claims:

```
Goal 1: (0 < 5)%N -> x0 = x1
Goal 2: (1 < 5)%N -> x1 = x2
Goal 3: (2 < 5)%N -> x2 = x3
Goal 4: (3 < 5)%N -> x3 = x4
Goal 5: (4 < 5)%N -> x4 = x0
... (25 goals total)
```

So the lemma pins the rotation offset exactly; an off-by-one is caught in
every one of the 25 cases, not just some.

### M3 — `fc_adjacent_02` expects `true`

Perturbation: `fc_adjacent [set inord 0; inord 2] = true`, with the witness
`inord 0` and the `fc_adjacent_01` proof shape.

Residual goals after the case bash:

```
Goal 1: Hm : (1 < 5)%N |- (1%N == 2%N) = (1%N == 1 %% 5)
Goal 2: Hm : (2 < 5)%N |- (2%N == 2%N) = (2%N == 1 %% 5)
```

i.e. `false = true` and `true = false`. The distance-2 pair `{0, 2}` is not
`{i, i+1}` for any `i`, exactly as the closed form of `fc_leak` requires.

### M4 — `fc_leak_3gap` returns the adjacent-pair value

Perturbation: the right-hand side of `fc_leak_3gap` replaced by the two-card
adjacent closed form.

```
Unable to unify "27 / 10 - 4^-1 * log 5 - 7 / 10 * log 7" with
 "6 / 5 - 9 / 20 * log 3".
```

`fc_leak` really dispatches on `#|A|`; a 3-set cannot pick up the 2-set value.

---

## probe_shapes.v

### M5 — `set5_branch_04` concludes `[set inord 0; inord 3]`

Perturbation: conclusion `A = [set inord 0; inord 3]` in place of
`A = [set inord 0; inord 4]`, hypotheses and proof script unchanged.

With the closing `by` the script reports `No applicable tactic.`. Running the
same script without the `by` leaves the two discriminating subgoals

```
x = inord 3 :  false = (3%N == 0%N) || (3%N == 3%N)
x = inord 4 :  true  = (4%N == 0%N) || (4%N == 3%N)
```

i.e. `false = true` and `true = false`: position 3 is excluded by hypothesis
`H3` but present in the claimed literal, and position 4 is present by `H4` but
missing from it.

### M6 — `leak_view_nil` claims the empty view leaks 1 bit

Perturbation: `` `I( Secret ; ViewT ([tuple] : 0.-tuple 'I_5) ) = 1 ``, proof
script unchanged.

```
Unable to unify "1" with "0".
goal: 0 = 1
```

The independence argument and the conditional-entropy collapse both go
through unchanged; only the claimed value is wrong, so the failure isolates
the value and not the route.

---

## Summary

| # | File | Perturbation | Outcome |
|---|---|---|---|
| M1 | probe_objects.v | `cardV013_FTT = 5` | fails: enumeration sums to 4 |
| M2 | probe_objects.v | `nth_rot5` offset `i + k + 1` | fails: all 25 cases become `x_j = x_{j+1}` |
| M3 | probe_objects.v | `fc_adjacent_02 = true` | fails: `(1 == 2) = (1 == 1)` |
| M4 | probe_objects.v | `fc_leak_3gap` = 2-adjacent value | fails: unify 27/10-form with 6/5-form |
| M5 | probe_shapes.v | `set5_branch_04` -> `[set 0; 3]` | fails: positions 3 and 4 both contradict |
| M6 | probe_shapes.v | `leak_view_nil = 1` | fails: `0 = 1` |
