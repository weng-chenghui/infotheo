# 2026-05-25 — Scope: the "view-as-input" (1a) refactor that fixes the soundness hole

## Why this refactor exists

`Pr_guess_enc_zero_le_invm : forall predictor, Pr[guess = V_2] <= 1/m` is currently
**false** (soundness hole): `boolean_shell` never calls `id_game_run`, so V_2 is
sampled only if the predictor opts in; a predictor that skips `id_game_run` and
returns the constant `chmsg_of_msg 0` hits the unwritten-cell default and wins
with probability 1. See [[20260525-two-channel-secrecy-fiber-vs-indcpa]] and the
counterexample analysis.

The 1a fix moves V_2 sampling to the challenger: `boolean_shell` calls
`id_game_run` (sampling V_2, obtaining the cipher view), passes the view to the
predictor, then reads V_2. The predictor RECEIVES the view as input and may drop
it (a random guesser does). Matches the intended TeX adversary `A : Y -> Δ(R)`.

**Primary value: restores SOUNDNESS** — after the refactor the `forall` bound is
TRUE (V_2 always a fresh uniform the adversary cannot pre-empt). It remains a
`Hypothesis` (the forall-opaque-adversary proof still needs SSProve absolute-Pr
machinery it lacks), but it is now a sound assumption rather than a false one,
and `random_guess_adv` becomes a meaningful (non-degenerate) tightness witness.

## Interface changes (dsdp_security_indcpa.v)

| Decl | line | Change |
|---|---|---|
| `guesser_export` | 1452 | `id_guess : 'unit -> msg`  →  `id_guess : ciphers -> msg` |
| `predictor_iface` | 1467 | **[interface] (empty)** — see refinement below |
| `predictor_guesser` | 1482 | becomes `package [interface] guesser_export` (closed predictor) |
| `boolean_shell` | 1505 | body: import + call `id_game_run` to get `view`, pass `view` to `id_guess`, then `id_v2_get`, return `guess == v2` |
| `guess_indicator_pkg` | 1553 | definition unchanged (`boolean_shell ∘ predictor ∘ game`); linkage re-wires |

### Refinement vs the raw scope map: `predictor_iface` should become EMPTY

The investigation suggested keeping `predictor_iface = {id_game_run}` unchanged.
That is wrong for the clean fix: if the predictor can still call `id_game_run`,
it can RE-sample V_2 (a second sample after `boolean_shell`'s), reintroducing an
ordering/double-sample hazard. In the view-as-input model the predictor is a
pure `ciphers -> msg` function that imports nothing, so `predictor_iface` must be
`[interface]` (empty). Then only `boolean_shell` samples V_2. Linkage still
closes: `boolean_shell` imports `id_game_run`/`id_v2_get` (from game) + `id_guess`
(from predictor); `∘ game` satisfies the game imports; result is closed.

## Lemmas to re-prove (3)

| Lemma | line | effort | why |
|---|---|---|---|
| `boolean_shell_pack_setm` | ~1710 | trivial | witnesses `boolean_shell.(pack)` as a `setm`; new body → update the witnessed term, re-`reflexivity`/`change` |
| `valid_boolean_shell_link` | ~1788 | MEDIUM (main risk) | `ValidPackage (locs pred) game_iface A_export (boolean_shell ∘ pred)`; new `id_game_run` import must propagate as residual via `valid_code_link_residual`; the earlier session already found this proof finicky |
| `Pr_guess_le` | ~2019 | low | `link_assoc` + `AdvantageE` reasoning is generic in the distinguisher; likely replays, just re-typecheck against new `boolean_shell` |

## UNAFFECTED (the load-bearing good news)

The entire IND-CPA chain is generic in the distinguisher (`predictor : raw_package`)
and never mentions `boolean_shell`:
- game equivalences `game_real_equiv_charlie_real`, `charlie_zero_equiv_game_hybrid_one`,
  `game_hybrid_one_equiv_bob_real`, `bob_zero_equiv_game_hybrid_two`,
  `game_hybrid_two_perfect_game_enc_zero` — game-only.
- `advantage_hop_real_h1`, `advantage_hop_h1_h2`, `advantage_game_real_game_enc_zero`
  — generic distinguisher.
- `game_via_oracle_*`, `oracle_encrypt_*`, `predictor_via_oracle_*`, the games,
  `log_id`, `Hunp`, `bound`, `Hunp_ge_bound`, `dsdp_alice_secrecy` (stmt) — unaffected.

So the OOM-sensitive `eapply eq_rel_perf_ind_eq` / `simplify_eq_rel` /
`ssprove_sync_eq` proofs are NOT touched (they are over games, not `boolean_shell`).

## Downstream

- `dsdp_security_indcpa_concrete.v`: `random_guess_adv` (line 356) body header
  `(_ : 'unit)` → `(view : ciphers)` (view unused); same in the Idealized / Benaloh
  / Paillier specializations. `secrecy_random_guess`, `Hunp_random_guess` statements
  unchanged, proofs should replay.
- `dsdp_security_indcpa_pismc.v`: uses the abstract `boolean_shell t_msg t_cipher`;
  `Pr_eq_of_game_real_eq_pismc`, `dsdp_alice_secrecy_pismc`, `Hunp_ge_bound_pismc`
  take the linkage validity as a hypothesis and transport — should replay.
  (NOTE: concrete/pismc files have the pre-existing load-path build issue; verifying
  their replays needs that resolved first.)

## Critical path

1. `guesser_export` type + `predictor_iface` empty + `predictor_guesser`.
2. `boolean_shell` body (import/call `id_game_run`, pass view).
3. `boolean_shell_pack_setm` (trivial).
4. `valid_boolean_shell_link` (medium — the risk).
5. `Pr_guess_le` (re-typecheck).
6. Build-verify ref/dsdp_security_indcpa.vo.
7. `random_guess_adv` header + concrete replays (needs build-fix to verify).
8. pismc replays (needs build-fix to verify).

## Effort / risk

~12–15 LOC of definition changes + 3 reproofs (one trivial, one medium, one low).
Main risk: `valid_boolean_shell_link`'s residual-import proof under the new
`id_game_run` import. The IND-CPA chain and the OOM-prone equivalence proofs are
untouched. Estimate: a focused half-day for ref/; concrete/pismc replays gated on
the load-path build-fix.

## Related
- [[20260525-two-channel-secrecy-fiber-vs-indcpa]] — the soundness-hole finding.
- [[20260525-pr-guess-enc-zero-direct-independence-plan]] — why the forall proof
  stays assumed (absolute-Pr gap).
