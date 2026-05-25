# 2026-05-25 — Plan: discharge `Pr_guess_enc_zero_le_invm` by direct independence

Scoping plan only. No execution. Follow-up to the two-channel reconciliation
([[20260525-two-channel-secrecy-fiber-vs-indcpa]]) and the fiber-duplication
removal (commit 52e5cfd).

## Goal

Replace the bare section `Hypothesis`

```coq
Hypothesis Pr_guess_enc_zero_le_invm :
  forall (predictor : predictor_guesser),
    distr.mu (pkg_advantage.Pr
                (guess_indicator_pkg predictor game_enc_zero)) true
      <= (card_t_msg%:R)^-1.
```

with a proved `Lemma` of the same statement, via the **Channel-2 direct
independence** argument: in `game_enc_zero` the predictor's view is independent
of `V_2`, and `V_2` is uniform, so the guess matches `V_2` with probability
exactly `1/card_t_msg`.

This is an SSProve-side statement (it is about `pkg_advantage.Pr` of the linked
package), not an Infotheo fdist statement. It does NOT use `dsdp_entropy.v` or
any fiber argument.

## Why it should hold (math)

`guess_indicator_pkg predictor game_enc_zero = boolean_shell ∘ predictor ∘
game_enc_zero`. Run semantics:

1. `game_enc_zero`'s `id_game_run` samples `iV2` (and others), `#put V_2_cell :=
   Some (chmsg_of_msg v2)`, and returns the cipher list `[a1;a2;c2;c3]`. Post
   IND-CPA collapse `c2 = Enc 0`, `c3 = Enc 0`, hence `a1 = Enc r2`, `a2 = Enc
   r3` (homomorphically `Epow (Enc 0) u = Enc 0`). The returned list is a
   function of `(r2, r3)` and encryption randomness only — **independent of the
   `V_2` sample stored in `V_2_cell`**.
2. `predictor` imports `predictor_iface` (only `id_game_run`), so its `guess`
   is a function of the cipher list (plus its own coins) — independent of
   `V_2_cell`.
3. `boolean_shell` calls `predictor` for `guess`, then `id_v2_get` to read
   `V_2_cell`, then returns `guess == v2`. `v2` is the uniform sample, drawn
   independently of `guess`.
4. Therefore `Pr[guess == v2] = Σ_g Pr[guess = g] · Pr[v2 = g] = Σ_g Pr[guess =
   g] · (1/m) = 1/m`.

## Proof skeleton (SSProve)

The crux is formalising "the returned cipher list is independent of the value
written to `V_2_cell`," then averaging. Two candidate routes; route A is
preferred.

### Route A — reorder the V_2 sample to the end, then average (preferred)

1. Rewrite the linked package so the `V_2` sample is drawn **after** the
   predictor produces its guess. Justification: `V_2_cell` is written by
   `id_game_run` but only read by `id_v2_get`, which `boolean_shell` calls after
   `call_pred`. Use SSProve swap/independence rules (`ssprove_swap_*`,
   `r_uniform_*`, the `#put`/`get` commutation lemmas in `pkg_rhl` /
   `pkg_distr`) to move the `V_2` draw past the predictor call. Need: the
   predictor does not read or write `V_2_cell` (true by `predictor_iface` and by
   `boolean_shell` not exposing the cell to it) — this is the load-bearing
   side-condition.
2. Once `v2 ← sample uniform card_t_msg` sits immediately before `ret (guess ==
   v2)` with `guess` already fixed, apply the uniform-equality-probability fact:
   `Pr[ x ← uniform n ;; ret (c == x) ] true = 1/n` for any fixed `c`. Find or
   prove this from `pkg_distr` / mathcomp-analysis uniform mass lemmas.

### Route B — denotational independence (fallback)

Compute `Pr` of the whole linked package as a product distribution and show the
`(guess, v2)` joint factorises, then sum the diagonal. Heavier; only if the
swap-based Route A stalls on the reordering side-conditions.

## SSProve lemma inventory to confirm BEFORE planning execution

Per `feedback_test_proof_steps_before_plan`, verify these exist (names/signatures)
in the installed SSProve before committing to Route A:

- A `#put`/`get`-commutation or "unused cell" rule letting a `sample` move past
  code that neither reads nor writes the cell (look in `pkg_rhl.v`,
  `pkg_distr.v`, `ssprove_swap_*`).
- A uniform-sample equality-probability lemma: `Pr[ x ← uniform n ;; ret (c ==
  x : 'bool) ] true = n%:R^-1` (or buildable from `LosslessOp_uniform` +
  `distr.mu` of `uniform`).
- The reflexivity/`Pr`-congruence machinery to transport `Pr` across the
  swap-equivalence (`eq_rel_perf_ind_eq` style, but here for `Pr` not Advantage —
  may need `Pr_eq` from a `≈₀` equivalence).

If the uniform-equality lemma or the unused-cell swap is absent, that is the
real cost driver; budget a helper-lemma sub-task for each.

## Where it lands

`ref/dsdp_security_indcpa.v`, replacing the `Hypothesis Pr_guess_enc_zero_le_invm`
(currently ~line 1615) with a `Lemma … . Proof. … Qed.`. Then the concrete
instantiations (`ref/dsdp_security_indcpa_concrete.v`, currently re-declaring it
as a `Hypothesis`) can drop their hypothesis and pass the proved lemma —
eliminating the assumption end-to-end and making `dsdp_alice_secrecy` /
`Hunp_ge_bound` unconditional in `epsilon_cpa` + the IT residual.

## Risks / open questions

- **Reordering side-condition.** Route A needs "predictor cannot touch
  `V_2_cell`." This is enforced by `predictor_iface` (no `id_v2_get`) but the
  cell is a raw `Location`; confirm the predictor's `ValidCode` against
  `predictor_iface` actually forbids touching `V_2_cell` (it should, since the
  cell is not in the predictor's import interface, but verify SSProve's location
  discipline makes this a usable hypothesis).
- **`Pr` vs `Advantage` transport.** Most SSProve examples bound `Advantage`;
  here we need an exact `Pr` value. Confirm the `Pr`-level congruence lemmas
  exist (e.g. transporting `Pr` across a `≈₀` perfect equivalence).
- **Scale/OOM.** The linked package is DSDP-sized; recall the `apply:` vs
  `eapply` OOM ([[ssprove-apply-vs-eapply]]). Use `eapply` for any
  perfect-indistinguishability step.

## Related

- [[20260525-two-channel-secrecy-fiber-vs-indcpa]] — why this is Channel-2.
- [[ssprove-apply-vs-eapply]] — OOM-avoidance for the linked package.
- [[20260523-ssprove-package-proof-pattern]] — the decompose/align/witness/close
  pattern for SSProve package proofs.
