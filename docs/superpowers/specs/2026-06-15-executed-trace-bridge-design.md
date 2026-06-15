# Executed-trace bridge: operational secrecy for the four PGG instances

Date: 2026-06-15

The deferred operational layer of the view-secrecy framework. Lifts the view-level secrecy to
the EXECUTED `run_interp` trace: a single corrupted player's executed trace carries zero
information about the secret.

## Problem

The view-secrecy theorems (`<inst>_view_secrecy`) state that a sub-threshold coalition's VIEW is
independent of the secret, but over the view's natural probability space, not tied to the
protocol's executed trace. We want the operational statement, Mizuki-Shizuya / SPP style:

    <inst>_trace_secrecy : H(Secret | player_trace i) = H(Secret)

where `player_trace i` is the executed `run_interp` trace of a single player `i`, lifted to a
random variable. This connects the abstract privacy to what a corrupted party actually observes.

## Feasibility basis (all four established by probes)

Three throwaway probes (compiled, then deleted) confirmed the run-lift for every instance.

- A single player's `run_interp` trace `vm_compute`s to a function of exactly ONE dealt
  share/card, with symbolic inputs, mirroring the shipped `*_verifier_endpoints` lemmas (which
  already `vm_compute` the verifier trace symbolically). No explosion at a player index.
- den Boer: `nth ... .2 2 = [:: PGG_idx 0; PGG_hand [:: g [::va;vb] (rho w0 (tnth st 0))]]`. The
  trace carries the card POSITION; `decode_bool` of it is the `ViewA` colour, and
  `decode_bool`/`encode_bool` are mutually inverse on the layout image (every dealt card is
  `encode_bool` of a bit), so `leak_k1` suffices and the cancel holds.
- s5: `nth ... .2 2 = [:: PGG_idx 0; PGG_hand [:: g [::] (rho w0 (tnth st 0))]]` (98ms). The share
  is a plain `'Z_5` value, so the cancel is DIRECT (no decode collapse).
- s5x5: same single-share shape (221ms); 12 procs (1 dealer, 1 verifier, 10 players); players
  0..4 carry a pile-1 share, 5..9 a pile-2 share. A single player's trace pins one share of one
  factor.

The SPP precedent is the exact recipe to mirror (`du2002/spp_proof.v`): `scalar_product_uncurry`
(the run as a pure function of inputs), `scalar_product_RV` (the trace lifted to an RV),
`alice_traces_ok` (`trace = f o view`, proved by the interp-shape lemma `smc_scalar_product_traces_ok`),
`alice_traces_entropy` (`H(secret | trace) = H(secret | view)` via `centropy_RV_contraction` and a
`cancel`), and `scalar_product_is_leakage_free`.

## Scope

All four in-scope instances. The implementation is staged: the generic transport plus one
proof-of-concept instance (den Boer or s5) first, the remaining three after.

## Architecture

### Generic transport: `pgg-smc/security/pgg_trace_secrecy.v`

Family-agnostic. Abstracts SPP's `alice_traces_entropy` + `is_leakage_free`. Reuses the existing
`leakage_of_view_indep` (`pgg_leakage_witness.v`) for the final `H(secret|view) = H(secret)` step.

    trace_secrecy_of_view (secret : {RV P -> secretT}) (view : {RV P -> viewT})
        (player_trace : {RV P -> traceT}) (trace_of : viewT -> traceT) (view_of : traceT -> viewT) :
      player_trace = trace_of `o view ->
      cancel trace_of view_of ->
      P |= view _|_ secret ->
      `H( secret | player_trace ) = `H `p_ secret /\ `I( secret ; player_trace ) = 0.

Proof: `H(secret | player_trace) = H(secret | view)` by the SPP `alice_traces_entropy` argument
(`view = view_of `o player_trace` from the cancel, so conditioning on the trace equals conditioning
on `[%view, player_trace]`; then `centropy_RV_contraction` and `centropyC` collapse both sides),
then `= H(secret)` by `leakage_of_view_indep`. The mutual determinism (`cancel`) is what turns the
data-processing inequality into the equality, per the adversarial audit of the original framework.

### Per-instance lift: `<inst>_trace.v`

Each instance file: lift the run to an RV over its randomness space `P`, project to one player,
prove the `vm_compute` shape lemma, supply the view connection and the cancel, conclude via the
transport.

    <inst>_run_RV    : {RV P -> tracesT}        (* run_interp as a function of the randomness *)
    <inst>_player_trace (i) := (fun t => nth [::] t (player_idx i)) `o <inst>_run_RV
    <inst>_player_trace_ok (i) : <inst>_player_trace i = trace_of `o <inst>_view i   (* by vm_compute *)
    <inst>_trace_secrecy (i) : `H( Secret | <inst>_player_trace i ) = `H `p_ Secret.

Family specifics:

- **den Boer / kim** (card family): `P = Omega = bool*bool*'I_5` (the existing five-card
  leakage space). `<inst>_view i = ViewA [:: i]` (the single-card colour). `trace_of card =
  [:: PGG_idx _; PGG_hand [:: encode_bool card]]`, `view_of` reads `decode_bool` of the hand; the
  cancel is `encode_bool`/`decode_bool` mutual inverse ON THE LAYOUT IMAGE (a carried hypothesis,
  since it fails for arbitrary `'I_5`). Independence from `leak_k1`. kim reuses all of this (its
  cut is the same C_5; `kim_run_recovers = den_boer_run_recovers`).
- **s5** (additive): `P =` the uniform sampler tape `'rV['Z_5]_5` (`unif_randomized_sharing`). The
  dealer deals the sampler's `rsh_share rs` as the generic content `g`. `s5_view i = rsh_view rs
  [set j(i)]` (the single share at the player's cut-permuted position). `trace_of share =
  [:: PGG_idx _; PGG_hand [:: share]]`; the cancel is the direct `PGG_hand` head projection, no
  decode collapse. Independence from `additive_view_indep` at `|C| = 1 < 5`.
- **s5x5** (additive product): `P =` the product of the two sampler tapes. A single player `j`'s
  trace is one share of pile `(j < 5 ? 1 : 2)`. Its independence from the JOINT secret `(s1, s2)`
  combines `additive_view_indep` (share ⫫ its own pile's secret) with the product cross-independence
  (share ⫫ the other pile's secret), i.e. the `leakage_product` / `joint_view_indep` machinery.
  `s5x5_trace_secrecy i : H([%s1,s2] | player_trace i) = H([%s1,s2])`.

## Files

| File | Contents |
|---|---|
| `pgg-smc/security/pgg_trace_secrecy.v` | `trace_secrecy_of_view` (generic transport) |
| `pgg-smc/instances/denboer1989/denboer_trace.v` | den Boer lift + `denboer_trace_secrecy` |
| `pgg-smc/instances/kim2025/kim_trace.v` | kim lift + `kim_trace_secrecy` (reuses den Boer) |
| `pgg-smc/instances/s5/s5_trace.v` | s5 lift + `s5_trace_secrecy` |
| `pgg-smc/instances/s5x5/s5x5_trace.v` | s5x5 lift + `s5x5_trace_secrecy` |

## Component boundaries

`pgg_trace_secrecy.v` is generic over any `(secret, view, player_trace, trace_of, view_of)`; it has
no instance specifics and depends only on infotheo plus `pgg_leakage_witness`. Each `<inst>_trace.v`
supplies the lift, the `vm_compute` shape lemma, the view, and the cancel, then calls the transport.

## Risks and mitigations

1. The lift RV construction (run as a function of `P`). Mitigation: the existing `*_verifier_endpoints`
   lemmas already express the run as a function of symbolic inputs; the player projection is the same
   by `vm_compute` (probe-confirmed). The content-randomization (deal `rsh_share` as `g`) reuses the
   generic `dealer_with_input_encoding` content hook.
2. Cut threading for the card family: the leakage space's `k : 'I_5` must map to the run's `w0` cut.
   Mitigation: `den_boer_view_count_eq` already shows the rotation orbit is colour-count preserving,
   so the colour view's law is cut-invariant.
3. The cancel hypothesis. Card family needs `encode_bool`/`decode_bool` mutual inverse on the layout
   image (probe-proven, must appear as a hypothesis). Additive family is direct.
4. s5x5 joint independence: a single player's share ⫫ the joint secret needs the product
   cross-independence (`inde_RV_fst`/`inde_RV_snd`) composed with `additive_view_indep`. Mitigation:
   the `leakage_product` machinery (already built) supplies the cross-independence.
5. `centropy_RV_contraction` shape. The transport conditions on the bundled `[%view, player_trace]`,
   not the one-way `trace = f o view`, exactly as SPP's `alice_traces_entropy` does; the cancel
   supplies the reverse direction.

## Verification criteria

- All lemmas reach `Qed` with no `Admitted`, no custom axiom beyond the standard `boolp` axioms.
- `<inst>_trace_secrecy` holds for all four instances through the single generic
  `trace_secrecy_of_view`.
- The lift is over a genuine randomness space (`Omega` or the sampler tape), and `player_trace i`
  is the actual `run_interp` trace projection, not a re-statement of the abstract view.

## Non-goals

- No coverage beyond the four in-scope instances.
- No multi-player / coalition trace (a single corrupted player only); the combined-trace version
  would compose via `leakage_product`, out of scope here.
- No change to the existing view-secrecy theorems or the correctness `*_run_recovers` proofs.
