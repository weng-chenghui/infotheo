# Output channel S: absolute Pr, not real-or-zero advantage

Date: 2026-06-12

## Question

For S (the output), we don't compare the advantage like the real-or-zero case.
Then how does SSProve handle the probability that the predictor can predict it?

## Answer

SSProve does not use `AdvantageE` for the output channel `S` at all. It uses its
**absolute** probability primitive `pkg_advantage.Pr`, which gives `Pr[ G = true ]`
for one closed game `G` — a single mass, not a difference. The `<= 1/m` bound is then
proved in Infotheo, not in SSProve's relational calculus.

### Mechanism

1. **One game, absolute mass.** Instantiate `G` as the all-zero guessing experiment
   (challenger o predictor o `zero_game`) with success event `guess == V2`. The
   quantity is

   ```
   guess_sdistr_success = mu (pkg_advantage.Pr (guessing_experiment predictor zero_game)) true
                        = Pr[ predictor guesses V2 ]   on the all-zero game.
   ```

   No second game, no `AdvantageE`.

2. **Why not the advantage.** `AdvantageE` only certifies "two games indistinguishable
   up to epsilon"; it structurally cannot pin the *magnitude* of one game's success.
   The output-channel claim is a magnitude (`this single Pr <= 1/m`), so it must go
   through the denotational `Pr` / `Pr_fst` layer directly. This is the documented
   `ssprove_absolute_Pr_gap`: the relational tools cannot hand you an absolute `Pr`,
   so you go under them.

3. **SSProve's actual job is just to expose the number.** It defines the absolute
   success Pr and proves the game's sub-distribution is **lossless** (mass 1), so the
   number is a genuine probability. It does not prove `<= 1/m` itself.

4. **The bound is imported from Infotheo:**
   - connector `guess_success_sdistr_eq_fdist`: the game's sub-distribution is lossless,
     so `sdistr_to_fdist` carries it into an Infotheo `fdist` (same number, now
     `Pr_fdist[ guess = V2 ]`);
   - frame `Pr_fst_agree_locs` (heap-footprint lemmas): the predictor never reads
     `V2_cell`, so its guess factors through `(view, S)` only;
   - fiber bound `Pr_dsdp_sol_uniform_ring` (`dsdp_entropy.v`): conditioned on `S`,
     the secret `V2` ranges uniformly over a fiber of size `m`, hence
     `Pr[ guess = V2 | S ] <= 1/m`.

5. **Recombination by triangle inequality.** The real-vs-zero advantage re-enters
   only for the *cipher* channel; the two channels add by triangle inequality:

   ```
   Pr[A wins | real]  <=  Pr[A wins | zero]   +   | Pr[A wins | real] - Pr[A wins | zero] |
                          \-- absolute, <=1/m --/     \-- relational advantage, <= 2*epsilon_cpa --/
   ```

   - output channel = absolute single-game `Pr`, bounded information-theoretically
     (Infotheo fiber of `S`);
   - cipher channel = relational `AdvantageE` real-vs-zero, bounded by IND-CPA;
   - the triangle inequality lets a magnitude and a difference sum to
     `1/m + 2*epsilon_cpa`.

## Follow-up: the two "parts" are not two probabilities

Q: So it looks like we use the fact that guessing V2 via holding S is part of V2
guessing game probability? Another part is the encrypted received payload.

Almost — but the two "parts" don't add as two probabilities. One is a probability,
the other is a *difference*. That asymmetry is the whole reason for the construction.

**What "guess V2 from S" actually is.** It's not a free-standing term. It's the
adversary's success in the **zero game** — the game where the ciphertexts she receives
are replaced by encryptions of a fixed value (so they carry no information about the
secrets), while the leaked output `S` is kept exactly as in the real protocol. In that
game her only usable information about `V2` is `S`, so the fiber argument gives

```
Pr[ A guesses V2 | zero game ]  <=  1/m.
```

This is an **absolute probability** (the `pkg_advantage.Pr` mass), and it is the
"S channel."

**What the "encrypted received payload" contributes.** It is *not* a second probability
`Pr[guess from ciphertext]`. It enters as the **gap** between the real game and the zero
game — how much the adversary's success could rise because the ciphertexts are *real*
instead of *zero*:

```
| Pr[ A guesses V2 | real ]  -  Pr[ A guesses V2 | zero ] |  <=  2 * epsilon_cpa.
```

That gap is bounded by IND-CPA, because real-vs-zero ciphertexts is the *only* thing
that changed between the two games. This is the "cipher channel," and it is a
difference, not a mass.

**So the real decomposition is:**

```
Pr[ A guesses V2 | real ]
   <=  Pr[ A guesses V2 | zero ]            +   | Pr[real] - Pr[zero] |
       \-- guess from S alone, <= 1/m --/       \-- extra boost from real ciphertexts, <= 2*eps_cpa --/
   <=  1/m + 2*epsilon_cpa.
```

The right mental model is: **`1/m` is the baseline you can achieve from `S` even when
the ciphertexts are made useless; the IND-CPA term caps how much the real ciphertexts
can lift you above that baseline.** It is not `P(guess from S) + P(guess from ciphertext)`.
The ciphertext's role is to bound the *increment*, which is exactly why it has to be a
relational advantage and `S` has to be an absolute `Pr`.

## Follow-up: is this round the sdistr->fdist conversion for `Pr[guess V2 | zero] <= 1/m`?

Q: So then in this round we are doing converting SDist to fdist for
`Pr[ A guesses V2 | zero game ] <= 1/m`?

Close, but separate the two things — the conversion is the *bridge*, not the proof of
`<= 1/m`. In this round you're doing both, but they're distinct steps:

**The sdistr->fdist conversion gives you the *equality of numbers*, not the bound.**
The connector `guess_success_sdistr_eq_fdist` says the SSProve absolute mass equals an
Infotheo probability:

```
mu (pkg_advantage.Pr (guessing_experiment predictor zero_game)) true
   =  Pr_fdist[ guess = V2 ].
```

Same number, different type. That is all the conversion does — it moves the quantity
from SSProve's `sdistr` world into Infotheo's `fdist` world so an Infotheo theorem can
be applied to it. It does **not** by itself say anything is `<= 1/m`.

**The `<= 1/m` is proved entirely on the Infotheo side, after the bridge.** Once you're
in `fdist` land:

1. **Losslessness** — prove the zero-game success sub-distribution has total mass 1;
   this is the *precondition* that makes `sdistr_to_fdist` land in a genuine `fdist`
   (the connector is only valid because the game is lossless).
2. **Frame** (`Pr_fst_agree_locs`) — the predictor reads only `(view, S)`, never
   `V2_cell`, so the guess distribution factors through `(view, S)`.
3. **Fiber bound** (`Pr_dsdp_sol_uniform_ring`, `dsdp_entropy.v`) — conditioned on `S`,
   `V2` is uniform over a fiber of size `m`, hence `Pr_fdist[ guess = V2 | S ] <= 1/m`.

Step 3 is the actual `<= 1/m`, and it's a pre-existing Infotheo fact about the fiber of
`S` — not new to this round.

**So the round's new work is the gluing, not the bound.** Per the merge plan, the fiber
`1/m` is *bridged, not re-proved*: you write the **one connector** (sdistr->fdist) plus
its losslessness obligation and the frame lemma, then hand off to the already-proved
Infotheo fiber theorem. The conversion is what makes `Pr[ guess V2 | zero ] <= 1/m`
*expressible and applicable* in the SSProve setting; the `1/m` itself comes from Infotheo.

## Follow-up: why does the guess factoring through (view, S) matter?

Q: "2. Frame (Pr_fst_agree_locs) — the predictor reads only (view, S), never V2_cell,
so the guess distribution factors through (view, S)." --> Explain why this factoring
via those two matters.

The factoring is what turns "can the predictor guess `V2`?" into the fiber lemma, and it
does so by pinning down exactly what the guess is and isn't allowed to depend on. Two
things have to be true, and `(view, S)` is precisely the pair that makes them true.

**Excluding `V2_cell` kills the trivial attack.** The denotational run executes the
predictor against a heap that *contains the real `V2`* (the game sampled it to compute
`S`). If the predictor's read-set touched `V2_cell`, it would just copy the secret and
guess perfectly — `Pr[guess = V2] = 1`, and `<= 1/m` would be false. `Pr_fst_agree_locs`
is a heap-footprint statement: the predictor's reads are disjoint from `V2_cell`, so any
two heaps that agree on the `(view, S)` locations but differ at `V2_cell` produce the
**same** guess distribution. That is exactly the formal content of "the guess is
independent of `V2` beyond what `(view, S)` reveal." Without it the bound is simply wrong.

**Including `S` is what creates the size-`m` fiber.** `S` is genuinely correlated with
`V2` (it's the leaked scalar-product output, a function of `V2`). You can't pretend the
adversary doesn't see it. Conditioning on `S` is what the fiber lemma
`Pr_dsdp_sol_uniform_ring` is *about*: given the value of `S`, the secret `V2` is uniform
over a fiber of exactly `m` candidates. So `S` is the legitimate information channel, and
it constrains `V2` down to the fiber — but no further.

**Including `view` is what makes the bound about the *real* adversary, not a weaker one.**
In the zero game the predictor also sees the whole transcript (messages, zero-ciphertexts,
its own randomness) — that's `view`. If you bounded "guess from `S` alone," you'd be
proving a theorem about an adversary strictly weaker than the actual one. So you must
factor through `(view, S)`, then separately show `view` adds nothing: conditioned on `S`,
`view` is independent of `V2` (the `view_marginal_indep` step), so the fiber stays size
`m` even after the predictor reads the transcript.

**Why the factoring then closes the proof.** Once `guess = f(view, S)` with `f` not
reading `V2_cell`, the success probability becomes an average over the predictor's actual
inputs:

```
Pr[ guess = V2 ]
  =  E_{(view, S)} [  Pr[ V2 = f(view, S)  |  view, S ]  ]
  <=  E_{(view, S)} [ 1/m ]   =   1/m.
```

The inner term is bounded by `1/m` because `f(view, S)` is a *fixed* value once
`(view, S)` is fixed (it doesn't move with `V2`), and `V2` is uniform over `m` fiber
candidates independent of that fixed value. The factoring is what licenses pulling
`f(view, S)` out as a constant inside the conditional expectation — which is the only way
the uniform-on-a-fiber fact becomes a `1/m` ceiling on the guess. Drop either coordinate
and one of the two steps breaks: drop `V2_cell`-exclusion and the inner term is `1`; drop
`view` and you've bounded the wrong adversary; drop `S` and there's no fiber to be uniform
over.

## Follow-up: the cipher leg was already there; only S forced the absolute Pr

Q: So before this round that we add S, it is already there, but we just didn't use
the final prob, but only use advantage diff?

Yes — that's exactly right, and there's a clean reason it was self-consistent without `S`.

**Before the S round, the whole theorem was relational.** The original
`dsdp_indcpa_secrecy` bounded only the *distinguishing advantage* between the real game
and the zero game — `AdvantageE(real, zero) <= count * eps_cpa`. It never named an
absolute success probability. It only ever spoke in differences. That is a complete,
correct statement on its own: it says "real and zero are eps-close," full stop.

**Why the advantage-only framing was blind to `S`.** Here is the key point. `S` is
leaked identically in *both* the real game and the zero game (the output channel is
unchanged when you swap real ciphertexts for zero ciphertexts). So in the difference

```
| Pr[ guess V2 | real ]  -  Pr[ guess V2 | zero ] |
```

the contribution of `S` **cancels** — it is present on both sides. The advantage
literally cannot see the `S` leak. That is why the pure-IND-CPA theorem was airtight as
an *indistinguishability* claim yet said nothing about how well the adversary can
actually guess `V2`: the thing it measures is invariant under the `S` leak.

**What adding `S` forced.** To capture the `S` leak you have to ask the *absolute*
question "what is `Pr[ guess = V2 ]`?", because that is the only quantity in which `S`
does not cancel. The relational machinery (`AdvantageE`) structurally cannot answer it,
so this round introduces the absolute `pkg_advantage.Pr` mass and the Infotheo fiber
bound `<= 1/m`. Then the two get glued together by the triangle inequality.

So the reading is correct: the cipher/advantage leg was already there and used only the
difference; the new work is bolting on the absolute-probability leg that the difference
was constitutionally unable to express, and `1/m` is precisely the part of the guess
probability that the old advantage-only view had cancelled away.
