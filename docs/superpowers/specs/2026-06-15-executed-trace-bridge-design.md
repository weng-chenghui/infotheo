# Executed-trace bridge: operational secrecy for the four PGG instances

Created: 2026-06-15. Revised: 2026-06-15 after an adversarial audit (see Audit record).

The deferred operational layer of the view-secrecy framework. Lifts the view-level secrecy to a
RANDOMIZED `run_interp` trace: a single corrupted player's executed trace carries zero information
about the secret.

## Problem

The view-secrecy theorems (`<inst>_view_secrecy`) state that a sub-threshold coalition's VIEW is
independent of the secret, over the view's probability space, not tied to an executed trace. We
want the operational statement, SPP style:

    <inst>_trace_secrecy : H(Secret | player_trace i) = H(Secret)

where `player_trace i` is a single player's `run_interp` trace lifted to a random variable.

## The randomized run (a crucial clarification)

The shipped runs (`s5_run`, `den_boer_run`, ...) deal a DETERMINISTIC secret: `ts_encode s` for a
fixed `s`, with correctness proved by `*_run_recovers`. The trace bridge does NOT reuse those runs.
It defines a NEW, RANDOMIZED run whose dealt content is the sampler's shares over a randomness
space `P`, so the trace becomes a `{RV P -> tracesT}`. The `*_verifier_endpoints` lemmas are
parametric in the dealer content `g`, so the new run's trace shape is the same `vm_compute` fact at
a player index. The bridged secret is the RANDOM secret of the sampler (`rsh_secret` for additive,
`a&&b` for card), not the old runs' deterministic `s`. Correctness of the randomized run is not
needed for secrecy and is out of scope.

## Feasibility basis (established)

- The generic transport `trace_secrecy_of_view` is PROVEN to `Qed`, axiom-clean (a shape audit
  closed it from `centropy_RV_contraction`, `centropyC`, `leakage_of_view_indep`). The SPP recipe
  applies verbatim and the cancel hypothesis is sufficient.
- Single-player trace shape: probes proved, by `vm_compute; reflexivity` with symbolic dealer
  content `g`, that a player index of `run_interp` is one dealt share/card, for den Boer
  (`[:: PGG_idx 0; PGG_hand [:: g[::va;vb](rho w0 (tnth st 0))]]`), s5 (98ms), and s5x5 (221ms,
  one share of one pile). No explosion. This is the `*_verifier_endpoints` fact at a player index.
- den Boer card-to-colour: probe proved `decode_bool (layout card) = the ViewA colour` and the
  `decode/encode` round-trip; the missing piece is the cut connection (see Finding 1 fix below).

## Scope

All four in-scope instances, implementation staged: generic transport plus one proof-of-concept
instance first (s5 is recommended for the POC, as its cancel is direct; see below), then the rest.

## Architecture

### Generic transport: `pgg-smc/security/pgg_trace_secrecy.v` (PROVEN)

    trace_secrecy_of_view (secret : {RV P -> secretT}) (view : {RV P -> viewT})
        (player_trace : {RV P -> traceT}) (trace_of : viewT -> traceT) (view_of : traceT -> viewT) :
      player_trace = trace_of `o view ->
      cancel trace_of view_of ->
      P |= view _|_ secret ->
      `H( secret | player_trace ) = `H `p_ secret.

Proof (audited, closes): from `player_trace = trace_of `o view` and `cancel trace_of view_of`,
derive `view = view_of `o player_trace`; then `H(secret | player_trace) = H(secret | [%player_trace,
view])` (`centropy_RV_contraction`) `= H(secret | [%view, player_trace])` (`centropyC`) `= H(secret
| view)` (`centropy_RV_contraction` with `player_trace = trace_of `o view`) `= H `p_ secret`
(`leakage_of_view_indep secret view Hindep`; note its RV args are EXPLICIT). The `cancel` is the
mutual determinism that turns the data-processing inequality into the equality.

`viewT`/`traceT` must be chosen so the `cancel` is GLOBAL on the finTypes (no partial-image
hypothesis); each instance picks the view type accordingly (see below).

### den Boer / kim (card family): `<inst>_trace.v`

Randomness space `P = Omega = bool*bool*'I_5` (the existing five-card leakage space; `k : 'I_5` is
the rotation). View type `viewT = bool` (the single-card COLOUR), so the cancel
`decode_bool`/`encode_bool` is global on `bool` (`decode_bool (encode_bool b) = b` for all `b`; the
layout-image restriction is NOT needed and is dropped).

THE CORE WORK (Finding 1 fix): connect the leakage rotation `k` to the run's cut. Define the
randomized run's cut as `w0(k) := fc_sigma ^+ k` (the C_5 generator power realizing rotation `k`;
`fc_sigma ^+ k \in pgg_G` since `pgg_G = <[fc_sigma]>`). Then prove the bridge lemma:

    denboer_player_trace_ok (i) :
      denboer_player_trace i = trace_of `o (ViewA [:: i])
    where trace_of (b : bool) := [:: PGG_idx _; PGG_hand [:: encode_bool b]]

via (a) the `vm_compute` trace-shape at player `i` (probe-confirmed), and (b)
`decode_bool (den_boer_layout (a,b) at (rho (fc_sigma^k) (start_i))) = nth false (rot k (fc_arrange
a b)) i`, the monodromy-rotation correspondence that `den_boer_run_output`/`den_boer_run_recovers`
already exploit (the monodromy `rho (fc_sigma^k)` IS the cyclic rotation by `k`). This replaces the
mislabeled `den_boer_view_count_eq` mitigation. Independence from `leak_k1`. kim reuses all of it
(same C_5 cut, `kim_run_recovers = den_boer_run_recovers`).

### s5 (additive): `s5_trace.v`

Randomness space `P =` the uniform sampler tape `'rV['Z_5]_5` (`unif_randomized_sharing`). View
type `viewT = 'Z_5` (the single share value); the cancel is the direct `PGG_hand` head projection,
global on `'Z_5`, no decode collapse.

THE CORE WORK (Finding 2 fix): define the RANDOMIZED run. The dealer content is a tape-outcome
closure `g_u := fun pos => rsh_share rs (sigma^{-1} pos) u` dealing the sampler's shares (the dealt
value lives in `'I_5`; `'Z_5` and `'I_5` are the same finType, so no real cast, only a notation
reconciliation). The bridged secret is `rsh_secret rs : {RV P -> 'Z_5}` (random), NOT the old run's
deterministic `s : 'I_5`. Then:

    s5_player_trace_ok (i) :
      s5_player_trace i = trace_of `o (s5_view i)
    where s5_view i := the single share at player i's cut-permuted position,
          trace_of (x : 'Z_5) := [:: PGG_idx _; PGG_hand [:: x]]

via the `vm_compute` trace-shape (probe-confirmed). Independence: `s5_view i` is `rsh_share rs j`
for one `j`, which `additive_view_indep` at `C = [set j]` (`|C| = 1 < 5`) shows is independent of
`rsh_secret`. (`additive_view_indep` is over the share; bridge `rsh_share rs j` to `rsh_view rs
[set j]` if needed.)

### s5x5 (additive product): `s5x5_trace.v`

THE MOST CONSTRUCTION (Finding 3 fix). The s5x5 run deals one `s : 'I_10` via `product_scheme`; the
secrecy machinery (`additive_view_indep`, `leakage_product`, `inde_RV_fst`) requires the PRODUCT
distribution `P1 `x P2` and the pair secret `(s1, s2)`. So the randomized s5x5 run is dealt over
`P = P1 `x P2` (two independent sampler tapes), with each pile's content the corresponding
`unif_randomized_sharing` (exactly the two factors of `s5x5_joint_view_secrecy`). A single player
`j`'s trace is one share of pile `(j < 5 ? 1 : 2)`. Its independence from the JOINT secret
`[%s1,s2]` combines `additive_view_indep` (share ⫫ its own pile's secret) with the product
cross-independence `inde_RV_fst`/`inde_RV_snd` (share ⫫ the other pile's secret), i.e. the existing
`leakage_product`/`joint_view_indep` machinery. `s5x5_trace_secrecy i : H([%s1,s2] | player_trace
i) = H([%s1,s2])`.

## Files

| File | Contents | Audit status |
|---|---|---|
| `pgg-smc/security/pgg_trace_secrecy.v` | `trace_secrecy_of_view` | PROVEN by shape audit |
| `pgg-smc/instances/s5/s5_trace.v` | s5 randomized run + `s5_trace_secrecy` (POC) | direct cancel; lift is real work |
| `pgg-smc/instances/denboer1989/denboer_trace.v` | den Boer + `denboer_trace_secrecy` | needs the `k -> fc_sigma^k` bridge |
| `pgg-smc/instances/kim2025/kim_trace.v` | kim + `kim_trace_secrecy` (reuses den Boer) | reuse |
| `pgg-smc/instances/s5x5/s5x5_trace.v` | s5x5 over `P1 `x P2` + `s5x5_trace_secrecy` | most construction |

## Risks and mitigations

1. Card family cut bridge (was the audit blocker). Mitigation: `w0(k) := fc_sigma^+k`, and the
   monodromy-rotation correspondence (already used by `den_boer_run_output`). This is the core
   den Boer lift lemma, not a side mitigation.
2. The randomized run construction (additive): the tape-outcome content closure dealing
   `rsh_share rs`. The `*_verifier_endpoints` lemmas are parametric in `g`, so a `u`-dependent
   content is admissible; the trace-shape specializes it. Real but bounded.
3. s5x5 over `P1 `x P2`: re-deal the two piles over two tapes so `additive_view_indep` and
   `leakage_product` apply. Real construction; reuses the already-built product machinery.
4. The deterministic run's secret is irrelevant: secrecy is proved over the randomized run's random
   secret; no reconciliation with `s : 'I_N` is attempted.

## Verification criteria

- All lemmas `Qed`, no `Admitted`, only standard `boolp` axioms.
- `<inst>_trace_secrecy` for all four instances through the single `trace_secrecy_of_view`.
- `player_trace i` is the actual `run_interp` trace projection of the RANDOMIZED run, and the view
  type makes the `cancel` global (no partial-image hypothesis).

## Non-goals

- No coverage beyond the four in-scope instances.
- No multi-player / combined-trace coalition (single corrupted player only).
- No correctness proof for the randomized run; no change to existing view-secrecy or correctness
  proofs.

## Audit record

Two adversarial agents reviewed the 2026-06-15 draft. The generic transport was proved to `Qed`
(shape audit). Folded-in corrections: the bridge uses a NEW randomized run (not the shipped
deterministic run), with the random sampler secret; the card family needs the explicit
`k -> fc_sigma^k` cut bridge (the `den_boer_view_count_eq` mitigation was mislabeled); s5x5 must be
dealt over `P1 `x P2` for the product machinery to apply; the card cancel is global on `bool`
(colour view), so the layout-image hypothesis is dropped.
