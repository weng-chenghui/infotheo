# 2026-05-25 — Two-channel secrecy: fiber counting vs IND-CPA, and which discharges `Pr_guess_enc_zero_le_invm`

## Why this note

While scoping the bridge-completion run we conflated two different leakage
channels and nearly pointed the proof at the wrong tool. This records the
disentangled picture so the next run targets the right argument.

## The two orthogonal leakage channels

Alice (the corrupted party / predictor) could learn about Bob's secret `V_2`
through two completely different channels. They need different tools and live
in different parts of the proof.

### Channel 1 — the output channel (`S`)

Alice is *supposed* to learn the scalar-product output

```
S = U_1·V_1 + U_2·V_2 + U_3·V_3.
```

This is the functionality, not a leak to be removed. Even with unbreakable
encryption, Alice holds `S` and her own `(V_1, U_1, U_2, U_3)`. The **fiber
counting** argument shows the linear equation above has a fiber of `(V_2, V_3)`
solutions of size `m` (provided `U_2`/`U_3` avoid the degenerate `0`/`1` values
ruled out by hypothesis), so `V_2` stays uniform on that fiber and Alice's best
guess is `1/m`. Entropy up to `log m`.

- **Nature:** information-theoretic. Holds regardless of any computational
  assumption. Encryption being unbreakable does not help here, because `S` is
  given to Alice by design.
- **Tool:** `cPr_V2_V3_uniform_on_fiber` (generic residual section
  `dsdp_security_indcpa_residual`), `Pr_dsdp_sol_uniform` (`dsdp_entropy.v`),
  the `alice_view` / `alice_view_joint` machinery.

### Channel 2 — the ciphertext channel

The individual encrypted contributions Alice receives could in principle leak
*more* than `S` alone. The IND-CPA hops (`game_real → game_hybrid_* →
game_enc_zero`) replace the real encrypted contributions with encryptions of
`0`, removing this extra channel at cost `2·epsilon_cpa`.

- **Nature:** computational. This is exactly the IND-CPA assumption on the AHE
  scheme.
- **Tool:** `advantage_game_real_game_enc_zero` (the triangle / `ssprove
  triangle` chain).

## Which channel discharges `Pr_guess_enc_zero_le_invm`

```coq
Hypothesis Pr_guess_enc_zero_le_invm :
  forall (predictor : predictor_guesser),
    distr.mu (pkg_advantage.Pr
                (guess_indicator_pkg predictor game_enc_zero)) true
      <= (card_t_msg%:R)^-1.
```

This is about the **predictor's view in the SSProve game `game_enc_zero`**. The
predictor imports `predictor_iface`, which exposes only `id_game_run` (the
cipher-list oracle) and NOT `id_v2_get`. So the predictor sees only
`[a1; a2; c2; c3]`.

After both swaps those ciphers are `[Enc r2; Enc r3; Enc 0; Enc 0]`
(homomorphically: `Epow (Enc 0) u = Enc 0`, so `a1 = Enc r2`, `a2 = Enc r3`).
That view is a function of `(r2, r3)` and fresh encryption randomness only —
**independent of `V_2`** (and `V_3`, and even `U_2`, `U_3`). It does NOT
contain `S`.

Therefore:

> **`Pr_guess_enc_zero_le_invm` is discharged by the DIRECT independence route**
> (predictor view ⊥ `V_2_cell`, `V_2` uniform ⇒ `Pr[guess = V_2] = 1/m`).
> **No fiber counting.** Fiber counting is Channel 1, the output channel, which
> the `game_enc_zero` predictor view does not even see.

## The pitfall that caused the confusion

It is easy (I did it mid-discussion) to say "Alice learns `S`, `S` depends on
`V_2`, so the `game_enc_zero` view is not `V_2`-independent, so we need fiber
counting." That conflates two different views:

- **Alice's full protocol view** in the real protocol — includes `S` (output
  channel, Channel 1). Needs fiber.
- **The predictor's view in the SSProve `game_enc_zero`** — ciphers only, no
  `S`. Channel 2. Direct independence.

`Pr_guess_enc_zero_le_invm` is about the second. The first is a separate
argument.

## Reconciliation — RESOLVED (read-only investigation, 2026-05-25)

Possibility 1 confirmed by a full trace. Evidence:

1. **The `game_enc_zero` predictor cannot see `S`.** It imports `predictor_iface`
   (`ref/dsdp_security_indcpa.v:1467`), which exposes only `id_game_run` (cipher
   list); `id_v2_get` is structurally excluded. `game_enc_zero` (lines 516–561)
   returns only `[a1;a2;c2;c3]` and never computes `S`. So the predictor view is
   `V_2`-independent → **Channel 2, direct independence.**
2. **The fiber machinery in the IND-CPA file is orphaned.**
   `cPr_V2_V3_uniform_on_fiber` (line 3669) and `…_joint` (line ~4056) are defined
   but **never applied** to discharge any obligation. Nothing consumes
   `fdist_game_enc_zero_joint` toward `Pr_guess_enc_zero_le_invm`.
3. **`Pr_guess_enc_zero_le_invm` is undischarged everywhere** — a bare `Hypothesis`
   in the abstract section and at every concrete instantiation (passed through,
   "tracked separately"). When discharged, it is a Channel-2 SSProve independence
   proof (`id_game_run` output `_|_` `V_2_cell`), not a fiber argument.
4. **The real Channel-1 output argument already lives in `dsdp_entropy.v`** —
   `Pr_dsdp_sol_uniform` (line 237), `dsdp_centropy_uniform` (`H(V2,V3|inputs) =
   log m`, line 294), self-contained at the protocol level, independent of any
   SSProve game.

So the docstring's "routes through `fdist_game_enc_zero_joint` /
`cPr_V2_V3_uniform_on_fiber_joint`" claim was aspirational/over-engineering. The
`alice_view_joint` / bridge / fiber mirror in the IND-CPA files duplicates
`dsdp_entropy.v` and is wired to nothing.

## Decisions taken (2026-05-25)

- **Keep** `dsdp_entropy.v` and all original Channel-1 fiber counting (the
  output-channel argument predating the IND-CPA work).
- **Delete** the duplicated fiber machinery from the IND-CPA series files
  (`alice_view{,_joint}`, both bridges, `cPr_V2_V3_uniform_on_fiber{,_ring,_joint}`,
  `fdist_game_enc_zero_joint` + RV projections, the residual sections, the
  `Dk_a/V_2/V_3/Z_rand` carriers, the Task 10/12/B/D blocks).
- **Fixed** the `Pr_guess_enc_zero_le_invm` docstring to state the direct-independence
  (Channel-2) justification and point here.
- **Next:** discharge `Pr_guess_enc_zero_le_invm` via the SSProve independence proof
  (separate dated plan).

## Implication for the bridge-completion orchestrator run

The run's original target ("complete the bridge → instantiate
`fdist_game_enc_zero_joint`") was Channel-1 machinery and is **not** on the critical
path for `Pr_guess_enc_zero_le_invm`. It is retired. The correct future target is the
Channel-2 direct-independence discharge.

## Related

- `[[20260525-ssprove-infotheo-fdist-bridge]]` — the bridge explainer.
- `[[20260525-bridge-completion-survey]]` — Stage 0 survey for the (now paused)
  bridge-completion run; its alice_view_joint findings belong to Channel 1.
- `[[20260430-dsdp-unpredictability-entropy-audited-plan]]` — origin of the
  Task 12/13/F split and the fiber residual.
