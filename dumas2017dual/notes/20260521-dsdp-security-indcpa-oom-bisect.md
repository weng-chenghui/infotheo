# 2026-05-21 — `dsdp_security_indcpa.v` OOM bisection: `apply: eq_rel_perf_ind_eq.` at line 836

## Problem

`make dumas2017dual/dsdp/ref/dsdp_security_indcpa.vo` consumes unbounded memory
(observed ≥80 GiB before manual kill) and never completes.

## Bisection result

The OOM is triggered by a **single tactic**:

- File: `dumas2017dual/dsdp/ref/dsdp_security_indcpa.v`
- Lemma: `game_real_equiv_charlie_real` (lines 833–846)
- Tactic: `apply: eq_rel_perf_ind_eq.` (line 836)

### Evidence

Bisection probe = `dumas2017dual/dsdp/ref/dsdp_security_indcpa_probe.v`
(unlisted in `_CoqProject`, compiled directly with `rocq c` and identical
warnings to the project Makefile).

| Probe content | Peak RSS | Time | Result |
|---|---|---|---|
| Truncated at line 832 (everything up to but not including the lemma) | 1.78 GiB | 6 s | OK |
| Lemma stated, body = `Admitted.` (no tactics at all) | 1.79 GiB | 7 s | OK |
| Body = `apply: eq_rel_perf_ind_eq. Admitted.` (single tactic) | grew past 6 GiB in 11 s, kept climbing to ~80 GiB | killed | OOM |

Cross-check with the partial build artefacts that triggered this investigation:

- `dsdp_security_indcpa.glob` last reference: `eq_rel_perf_ind_eq` at the line
  containing `apply: eq_rel_perf_ind_eq.`.
- `.dsdp_security_indcpa.aux` only timed the trivial `valid_code_link_residual`
  proof; no later proof was ever recorded.

Both consistent with the bisection: nothing after that `apply` ever runs.

## Why this proof shape exists

The proof body deliberately mirrors SSProve's `IND_CPA_equiv_false` proof in
`SSProve/examples/PRF.v` (line 328). The tactic sequence

```
apply: eq_rel_perf_ind_eq.
simplify_eq_rel m.
- ssprove_swap_rhs 9%N.
  do 10 ssprove_sync_eq=> ?.
  ssprove_sync_eq.
  rewrite chcipher_of_cipherK chmsg_of_msgK.
  apply: rpost_weaken_rule; first exact: rreflexivity_rule.
  by move=> [? ?] [? ?] [-> ->].
- ssprove_sync_eq=> stored.
  by case: stored => [v|]; apply: r_ret.
```

is the **canonical SSProve idiom** for perfect indistinguishability between two
linked packages. Same shape as `Schnorr.v` and `PRF.v` upstream.

## What is unusual

The shape is canonical, the **scale is not**.

| | Upstream PRF.v `IND_CPA_equiv_false` | This proof `game_real_equiv_charlie_real` |
|---|---|---|
| First tactic | `eapply eq_rel_perf_ind_eq` | `apply: eq_rel_perf_ind_eq` |
| `simplify_eq_rel` | yes | yes |
| `ssprove_sync_eq` count | 1 (then case-split on key state) | 11 (`do 10 ssprove_sync_eq=> ?` then one more) |
| Linked packages | `IND_CPA false` vs `MOD_CPA_ff_pkg ∘ EVAL true` (one location, one sample) | `game_real` vs `game_via_oracle_charlie ∘ oracle_real` (DSDP whole protocol, 10 uniform samples + linked IND-CPA oracle) |
| Upstream compiles | yes, fast | OOM at the apply, before any sync runs |

## Mechanism

`eq_rel_perf_ind_eq` (in SSProve's `pkg_rhl.v`):

```coq
Corollary eq_rel_perf_ind_eq :
  forall {L0 L1 E} (p0 p1 : raw_package)
  `{ValidPackage L0 Game_import E p0}
  `{ValidPackage L1 Game_import E p1},
  eq_up_to_inv E (fun '(h0,h1) => h0 = h1) p0 p1 -> p0 ≈₀ p1.
```

The two `ValidPackage` typeclass arguments plus the implicit `L0`/`L1` are
inferred from the goal's fully unfolded packages. With a DSDP-sized
`game_via_oracle_charlie ∘ oracle_real` on the right, unification copies a
huge `raw_package` term twice during `apply`. Nothing later in the proof
(`simplify_eq_rel`, `ssprove_sync_eq`, etc.) ever runs because elaboration of
the apply itself never finishes.

No upstream SSProve issue tracks this exact symptom (the eight open issues are
unrelated: dependency versions, naming, choice_universe, extructures, etc.).
This is therefore "edge by scale, not by misuse."

## Mitigation candidates (tried in order)

### Mitigation 1: Opaque/Strategy on the package definitions — **partial**

Adding `Strategy -10 [game_real game_via_oracle_charlie oracle_real ...]`
before the lemma did not stop the OOM (peak 6.7 GiB at 12 s, same shape as
before). `Strategy` levels below `-∞` do not block delta during unification.

Replacing with `Opaque game_real game_via_oracle_charlie oracle_real ...`
**did** stop the OOM (peak 1.8 GiB at 6 s) but the apply then failed with
`Could not find an instance for ValidPackage L0 Game_import E game_real`,
because typeclass search needs to inspect the package structure. Going
fully opaque blocks both unification and instance search; we'd need to
preregister `ValidPackage` instances first. Did not pursue, since
mitigation 2 proved sufficient.

### Mitigation 2: switch `apply:` to `eapply` — **works**

Replacing the ssreflect `apply: eq_rel_perf_ind_eq.` with the vanilla Coq
`eapply eq_rel_perf_ind_eq.` made the full file compile in **7 s with peak
RSS 1.83 GiB**.

Root cause: ssreflect's `apply:` does an aggressive higher-order
unification pass that delta-unfolds the package bodies during type
inference of the implicit `L0`/`L1`/`E` arguments. Vanilla `eapply` leaves
those as existentials and resolves them lazily after the typeclass
instances are found, so the giant `raw_package` term is never duplicated
in memory.

Sites patched (all 5 occurrences in
`dumas2017dual/dsdp/ref/dsdp_security_indcpa.v`):

- line 836 `game_real_equiv_charlie_real`
- line 868 `charlie_zero_equiv_game_hybrid_one`
- line 900 `game_hybrid_one_equiv_bob_real`
- line 931 `bob_zero_equiv_game_hybrid_two`
- line 964 `game_hybrid_two_perfect_game_enc_zero`

### Mitigations 3, 4 — not needed

Splitting into smaller hops, and wrapping the encoding round-trips in
`nosimpl`, were not attempted: mitigation 2 already produced a 7 s build.

## Resolution

Single-character class fix: `apply: → eapply` at 5 call sites. Confirmed
via `make dumas2017dual/dsdp/ref/dsdp_security_indcpa.vo` (returns "up to
date" because the direct `rocq c` invocation already produced the .vo).

## Operational note for future bisection runs

`rocq c <file>.v` spawns a separate `rocqworker` process. Killing the launcher
PID with `kill -9` does **not** stop the worker, which is why a memory-cap
monitor script let the process climb to ~80 GiB before manual `pkill`. Future
bisection harnesses must `setsid` + `kill -- -PGID`, or `pgrep -P` the parent
and kill children explicitly. Recorded in memory as
`feedback_kill_does_not_propagate_to_rocq.md`.

## Reproduce

```bash
cd /Users/cheng-huiweng/Projects/coq/infotheo-itp

# Baseline (compiles in seconds, ~1.8 GiB):
cp dumas2017dual/dsdp/ref/dsdp_security_indcpa.v \
   dumas2017dual/dsdp/ref/dsdp_security_indcpa_probe.v
# Truncate to line 832 + append `End dsdp_security_indcpa.`

# OOM (kill from a separate terminal):
# Append after line 835 (`Proof.`):
#   apply: eq_rel_perf_ind_eq.
#   Admitted.
#   End dsdp_security_indcpa.

rocq c -q -R . infotheo \
  -w -projection-no-head-constant -w -redundant-canonical-projection \
  -w -notation-overridden -w -ambiguous-paths \
  -w -notation-incompatible-format \
  dumas2017dual/dsdp/ref/dsdp_security_indcpa_probe.v
```

## Files left behind

- `dumas2017dual/dsdp/ref/dsdp_security_indcpa_probe.v` — currently in the safe
  (`Admitted.` only, no `apply`) variant. Delete or repurpose; not in
  `_CoqProject`.
