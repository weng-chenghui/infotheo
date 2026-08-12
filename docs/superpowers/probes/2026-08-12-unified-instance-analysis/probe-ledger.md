# Probe ledger — unified instance analysis, Phase 0 (S5)

Repo `/Users/cheng-huiweng/Projects/coq/infotheo-pgg`, branch `pgg-smc`,
baseline `5453b93b`. Rocq 9.0.0. No production `.v` file, `_CoqProject`, or
request/response document was modified.

Build command for every file below:

```
sh docs/superpowers/probes/2026-08-12-unified-instance-analysis/rebuild.sh <file>.v
```

Build order matters. `probe_s5_det_plug.v` and `probe_s5_rand_plug.v` are
independent; `probe_s5_adapters.v` requires both; `probe_s5_mutation.v` requires
both plug files; `probe_require_check.v` requires `probe_s5_rand_plug.v`.

## Correction to a brief assumption

The brief stated that probe files cannot require each other.
`probe_require_check.v` refutes this: `From uia_probe Require Import
probe_s5_rand_plug.` resolves once the sibling `.vo` exists, because
`rebuild.sh` already passes `-R docs/superpowers/probes/2026-08-12-unified-instance-analysis uia_probe`.
`probe_s5_adapters.v` and `probe_s5_mutation.v` therefore reuse the landed plug
values instead of restating them, which removes any risk of the adapters probe
drifting from the plug probe.

## Per-file results

| File | Purpose | Exit | Wall time |
|---|---|---|---|
| `probe_s5_det_plug.v` | deterministic correctness plug + ObservedExecution + observers | 0 | 4.8 s |
| `probe_s5_rand_plug.v` | R-free layout, codec, cut-generalized skeleton, randomized plug + ObservedExecution | 0 | 5.1 s |
| `probe_s5_adapters.v` | randomized exact-secrecy adapter, finite-word endpoint adapter, reader bridges | 0 | 6.3 s |
| `probe_s5_mutation.v` | eight Fail-guarded perturbations of the load-bearing claims | 0 | 5.0 s |
| `probe_require_check.v` | probe-directory logical root resolves across probe files | 0 | 3.2 s |

No `Admitted`, no `Abort`, no `Axiom` in any probe file.

## Print Assumptions

`rocq compile` does not echo `Fail` messages, so the mutation rejection texts
were harvested from a rocq-mcp session and recorded verbatim in the source
comments of `probe_s5_mutation.v`.

Three assumption sets appear. `BOOLP` abbreviates the classical trio
`propositional_extensionality`, `functional_extensionality_dep`,
`constructive_indefinite_description`. `ORDER` abbreviates
`rigidity_s5_instance.s5_group_order_eq : #|pgg_G (Gen_PGGTypes (path_gen_tuple 3))| = 120`.

| Theorem | Assumptions |
|---|---|
| `s5_det_observed_recovers` | ORDER |
| `s5_det_correct` | ORDER |
| `s5_det_endpoints` | ORDER |
| `s5_det_terminates` | ORDER |
| `s5_rfree_shareE` | BOOLP |
| `s5_rprocs_cut1` | BOOLP |
| `s5_rand_run_recovers` | ORDER |
| `s5_rand_observed_recovers` | ORDER |
| `s5_rand_correct` | ORDER |
| `s5_sample_content_traceE` | ORDER + BOOLP |
| `s5_sample_trace_secrecy` | ORDER + BOOLP |
| `s5_sample_coalition_viewE` | ORDER + BOOLP |
| `s5_sample_coalition_secrecy` | ORDER + BOOLP |
| `s5_word_cut_distE` | ORDER + BOOLP |
| `s5_word_endpoint_bound` | `s5_rayleigh_Q2_R` + ORDER + BOOLP |
| `s5_word_transfer_conditional` | ORDER + BOOLP |
| `s5_rand_cut_distE` | ORDER + BOOLP |
| `s5_fuel_mutation` | Closed under the global context |
| `s5_obs_mutation` | Closed under the global context |
| `s5_group_mutation` | Closed under the global context |
| `s5_cut_mutation` | Closed under the global context |

`ORDER` reaches every execution-layer statement because the statements mention
`s5_profile`, whose `mp_plug` field is `cs_plug s5_brings_covering`, and the
covering record's genus-gap field is proved from the group order. The run
itself never exercises it. This is the same reason `s5_run.v` names `s5_scheme`
directly instead of `rp_scheme s5_plug`. `s5_rayleigh_Q2_R` touches exactly one
result, the finite-word endpoint bound.

## Mutation results

Every perturbation below is rejected. The rejection text is quoted in full in
the source of `probe_s5_mutation.v`.

| Mutation | Perturbation | Rejection |
|---|---|---|
| 1 | seat/share bridge retargeted at `sum_mod_scheme 3 3` (four shares) | `cannot unify "pi_T' (mp_PI mpS)" and "ts_T' sum_mod_scheme"` |
| 2 | four-element participant list | `cannot unify "[:: Ordinal isT; ...]" and "enum 'I_(pi_T' (mp_PI mpS)).+1"` |
| 3 | fuel 3 instead of 150 in the termination proof | `No applicable tactic.` |
| 4 | static observation drops `pgg_rho` (reads the start, not its cut image) | `Cannot apply lemma s5_rand_endpoints` |
| 5 | reconstruction invariance applied without `w0 \in pgg_G` | `Cannot apply lemma (fun u => s5_recon_perm_invariant (s5_rfree_valid u))` |
| 6 | identity-cut specialization claimed at every cut | `Cannot apply lemma (s5_rprocs_cut1 R u)` |
| 7 | `oe_expected` replaced by the constant `ord0` | `cannot unify "exec_decode s5_rand_plug Hsz = s5_codec (s5_tape_secret u)" and "... = ord0"` |
| 8 | spectral bound cast as a base-distribution premise | type error, carrier `'I_5` against carrier `{perm 'I_5}` |

## Findings recorded during the probes

1. `exec_procs` of a `dealer_secret_plug` over `s5_profile` with
   `ep_players = s5_run.s5_players` and `ep_fuel = 150` is convertible to
   `s5_procs` (`by []`). `exec_input_ids` reduces to `[::]` because
   `ep_input_procs` is the constant empty list, and the map over the concrete
   five-element player list reduces to the five explicit `exchange_player`
   entries of `s5_saprocs`. The same conversion carries the randomized plug to
   `s5_rprocs_cut`.
2. `/=` in the endpoint-equation proof triggers the lazy-eval bomb (rocq-mcp
   timeout on `exec_static_endpoints`). The fix is the pgl27 pattern: name
   `ep_fuel` and `ep_players` reductions as `by []` lemmas and rewrite with
   them, never with `/=`.
3. `rsh_share (unif_randomized_sharing R 3 4) j = s5_rfree_share j` is NOT
   `by []`. The last-index branch is a subtraction of a bigop of random
   variables, so the proof is `boolp.funext` followed by `sumrRVE`. This is why
   `s5_rfree_shareE` and `s5_rprocs_cut1` carry BOOLP while the recovery
   theorems do not.
4. `'Z_5` and `'I_5` are definitionally equal, and `(0%R : 'Z_5) = ord0` holds
   by `by []`. The codec is the identity and both cancellation lemmas are
   `by []`. No carrier bridge is needed between `rsh_view`'s
   `{ffun 'I_5 -> 'Z_5}` and the executed reader's `{ffun 'I_5 -> 'I_5}`.
5. Validity of the randomized layout needs a Z/5-to-nat bridge, recorded as
   `zp5_sum_val`: `(\sum_i (f i : nat)) %% 5 = ((\sum_i f i)%R : 'Z_5) :> nat`,
   proved by `val_Zp_nat`, `GRing.natr_sum` and `natr_Zp`.
6. `lift_max : lift ord_max i = i` is a `:> nat` statement, so
   `widen_ord (leqnSn 4) i = lift ord_max i` needs
   `apply: val_inj; symmetry; exact: lift_max`, not `rewrite lift_max`.
7. `Set Implicit Arguments` demotes the source-explicit binders of
   `s5_rand_run_recovers`, so `exact: (s5_rand_run_recovers u w0 Hw0)` fails and
   `exact: (@s5_rand_run_recovers u w0 Hw0)` succeeds.
8. `sa_arg` and `sa_cut` are primitive projections whose record argument is
   implicit; `sa_arg sa u` is a type error and `sa.(sa_arg) u` is required.
   Rewriting `s5_rprocs_cut1` before reducing `sa_arg`/`sa_cut` to `u` and
   `1%g` makes the rewrite diverge, so the projection reductions must be named
   as `by []` lemmas and rewritten first.
9. `s5_verifier_endpoints` is already generic in the content readout, the start
   tuple and the cut, so the randomized endpoint equation reuses it unchanged
   at `g := tnth (s5_rfree_layout u)`. No new interpreter computation was
   needed. `vm_compute` on the cut-generalized termination lemma takes 0.2 s.

# Probe ledger — unified instance analysis, Phase 0 (S5xS5)

Same repository, branch and baseline as the S_5 section above. No production
`.v` file, `_CoqProject`, or request/response document was modified. The S_5
entries above are unchanged.

Build order for this section: `probe_s5x5_det_plug.v` first, then
`probe_s5x5_rand_plug.v` (which requires `probe_s5_rand_plug.v` and
`probe_s5x5_det_plug.v`), then `probe_s5x5_adapters.v`, then
`probe_s5x5_mutation.v`.

## Per-file results

| File | Purpose | Exit | Wall time |
|---|---|---|---|
| `probe_s5x5_det_plug.v` | deterministic correctness plug + ObservedExecution + observers | 0 | 5.5 s |
| `probe_s5x5_rand_plug.v` | R-free two-pile layout, cut-generalized skeleton, randomized plug, product recovery, ObservedExecution | 0 | 5.9 s |
| `probe_s5x5_adapters.v` | randomized product adapter, per-pile and joint executed readers, finite-word adapter, negative-transfer floors | 0 | 16.9 s |
| `probe_s5x5_mutation.v` | twelve Fail-guarded perturbations plus one positive non-injectivity fact | 0 | 45.6 s |

No `Admitted`, no `Abort`, no `Axiom` in any of the four files.

## Print Assumptions

`BOOLP` abbreviates the classical trio `propositional_extensionality`,
`functional_extensionality_dep`, `constructive_indefinite_description`.
`ORDER` abbreviates
`rigidity_s5x5_instance.s5x5_group_order_eq : #|pgg_G (Gen_PGGTypes s5x5_gen_tuple)| = 14400`.
`RAYLEIGH` abbreviates `s5_mixing.s5_rayleigh_Q2_R`.

| Theorem | Assumptions |
|---|---|
| `s5x5_det_observed_recovers` | ORDER |
| `s5x5_det_correct` | ORDER |
| `s5x5_det_endpoints` | ORDER |
| `s5x5_det_terminates` | ORDER |
| `s5x5_rfree_layoutE` | BOOLP |
| `s5x5_rprocs_cut1` | BOOLP |
| `s5x5_rfree_recon` | Closed under the global context |
| `s5x5_rand_run_recovers` | ORDER |
| `s5x5_rand_observed_recovers` | ORDER |
| `s5x5_rand_correct` | ORDER |
| `s5x5_sample_content_traceE` | ORDER + BOOLP |
| `s5x5_sample_trace_secrecy` | ORDER + BOOLP |
| `s5x5_p1_viewE` | ORDER + BOOLP |
| `s5x5_p2_viewE` | ORDER + BOOLP |
| `s5x5_p1_secrecy` | ORDER + BOOLP |
| `s5x5_p2_secrecy` | ORDER + BOOLP |
| `s5x5_joint_viewE` | ORDER + BOOLP |
| `s5x5_joint_secrecy` | ORDER + BOOLP |
| `s5x5_p1_seat_viewE` | ORDER + BOOLP |
| `s5x5_word_cut_distE` | ORDER + BOOLP |
| `s5x5_word_pile1_bound` | RAYLEIGH + ORDER + BOOLP |
| `s5x5_word_pile2_bound` | RAYLEIGH + ORDER + BOOLP |
| `s5x5_word_seat_bound` | RAYLEIGH + ORDER + BOOLP |
| `s5x5_word_pile1_floor` | RAYLEIGH + ORDER + BOOLP |
| `s5x5_word_pile2_floor` | RAYLEIGH + ORDER + BOOLP |
| `s5x5_word_transfer_conditional` | ORDER + BOOLP |
| `s5x5_rand_cut_distE` | ORDER + BOOLP |
| `s5x5_fuel_mutation` | Closed under the global context |
| `s5x5_obs_mutation` | Closed under the global context |
| `s5x5_group_mutation` | Closed under the global context |
| `s5x5_stab_mutation` | Closed under the global context |
| `s5x5_cut_mutation` | Closed under the global context |
| `s5x5_codec_mutation` | Closed under the global context |
| `s5x5_combine_not_injective` | Closed under the global context |

`ORDER` reaches every execution-layer statement for the same reason as in the
S_5 section: the statements mention `s5x5_profile`, whose `mp_plug` field is
`cs_plug s5x5_covering`, and the covering record's genus-gap field is proved
from the group order. `s5x5_rfree_recon` is stated at `s5x5_scheme` rather than
at `rp_scheme s5x5_plug`, which is why the pure recovery fact is closed under
the global context. `RAYLEIGH` touches exactly the five results that mention a
spectral bound.

## Mutation results

Every perturbation below is rejected; the file compiles, which is what
certifies the rejection. `rocq compile` does not echo the text of a
`Fail`-guarded error and the rocq-mcp session could not load the S_5 x S_5
import closure inside its query timeout, so the messages quoted in the source
of `probe_s5x5_mutation.v` record the expected rejection shape rather than a
harvested transcript. This is stated in that file's header.

| Mutation | Perturbation |
|---|---|
| 1 | seat/share bridge retargeted at `product_scheme (sum_mod_scheme 3 3) (sum_mod_scheme 3 4)` (nine shares) |
| 2 | nine-element participant list |
| 3 | fuel 3 instead of 300 in the termination proof |
| 4 | static observation drops `pgg_rho` (reads the start, not its cut image) |
| 5 | randomized reconstruction claimed without `w0 \in pgg_G` |
| 5b | pile-1 stability applied to a group element instead of a membership proof |
| 6 | identity-cut specialization claimed at every cut |
| 7 | `oe_expected` replaced by `combine_secret (uv.1 ord0 ord0) ord0` |
| 8a | pile-1 secrecy applied to a flat `{set 'I_10}` coalition |
| 8b | ten-seat executed coalition reader cast to the pile view carrier `{ffun 'I_5 -> 'Z_5}` |
| 8c | joint secrecy applied to one flat coalition twice |
| 9a | `split_combineK` applied at pile-2 secret 2 |
| 9b | `s5x5_codecK_partial` claimed at every pile pair |
| 10a | pile-1 spectral bound cast as a base-distribution premise on `{perm 'I_10}` |
| 10b | one-seat `s5x5_spectral_TV_bound` cast as a two-seat joint bound |

`s5x5_combine_not_injective` is a positive fact rather than a guard:
`combine_secret 0 2 = combine_secret 0 0` in `'I_10`, closed by `ord_inj`. It is
the compiled form of the request's instruction not to claim that
`combine_secret` is injective.

## Findings recorded during the S_5 x S_5 probes

1. `exec_procs` of a `dealer_secret_plug` over `s5x5_profile` with
   `ep_players = s5x5_run.s5x5_players` and `ep_fuel = 300` is convertible to
   `s5x5_procs` (`by []`), exactly as for S_5. The same conversion carries the
   randomized plug to `s5x5_rprocs_cut`. The bridge `erefl` typechecks:
   `pi_T' s5x5_PI` and `ts_T' (rp_scheme s5x5_plug)` both reduce to 9.
2. `\val` and `nat_of_ord` are distinct constants for ordinals. They are
   interconvertible, so `exact:`, `:=` and `apply:` bridge them, but `rewrite`
   and `case:` match syntactically and do not. Every ordinal fact in these
   probes is therefore stated twice-consistently: library lemmas written with
   `val` (`s5x5_pile1_stab`, `s5x5_preserves_pile2_proved`, `project_pile1`,
   `embed_p1`) are used through `\val`-shaped bridges, while the interpreter
   layout's `if (i < 5)%N` and `inord i` (both coercion-inserted
   `nat_of_ord`) are used through coercion-shaped bridges obtained by
   `have H : (coercion form) := (val-form proof)`. `ord_inj : injective
   nat_of_ord` is the `nat_of_ord`-side counterpart of `val_inj`.
3. `rewrite tnth_mktuple` is keyed on `tnth`, so it unfolds a constant whose
   body is a `mktuple` (here `s5x5_rfree_layout uv` and `s5_rfree_layout u`).
   A pointwise bridging lemma stated at `tnth (s5x5_rfree_layout uv) p` is
   therefore unusable after `rewrite !tnth_mktuple`. The fix that worked is to
   state the bridge as a tuple equality (`s5x5_pile1_layoutE`) and rewrite with
   it before `eq_from_tnth`.
4. `@combine_splitK` cannot infer its `N1'` and `N2'`: the type of its argument
   is `'I_(N1'.+2 + N2'.+2)` and unifying that with `'I_10` has no unique
   solution. Every use needs `@combine_splitK 3 3 s`. The same holds for
   `pile1_shares`, `pile2_shares`, `project_pile1`, `project_pile2` and
   `split_combineK`.
5. `ts_recon s5x5_scheme t = combine_secret (ts_recon (sum_mod_scheme 3 4)
   (pile1_shares t)) (ts_recon (sum_mod_scheme 3 4) (pile2_shares t))` holds by
   `by []`: it is pure delta and iota through `product_scheme` and
   `product_recon`. This is the entry point of the whole recovery proof.
6. The library pile index `Ordinal (pile1_idx_lt i)` and the probe's `p1_idx i`
   differ in their boundedness proof term, so `tnth t` at the two indices is
   related by `congr (tnth t _); apply: val_inj`, not by conversion at the
   rewrite level.
7. `case: ifP => [_|_]` is a parse error in this Rocq version; `case: ifP => H`
   is accepted. A boolean if-condition is discharged against a hypothesis by
   `case: (ltnP a b) => Hc; last by rewrite (leq_gtF Hc) in H`, which reduces
   the `if` and leaves a `false = true` hypothesis that `done` discriminates.
8. `{RV d -> T}` parses `d` at a level that rejects an application, so
   `{RV s5x5_rand_sampleP R -> T}` is a syntax error and
   `{RV (s5x5_rand_sampleP R) -> T}` is required.
9. `vm_compute` proves termination of the cut-generalized twelve-process run at
   fuel 300 with both the content readout and the cut held abstract, in well
   under a second. No concrete leaf is ever forced.
10. `s5x5_verifier_endpoints` is already generic in the content readout, the
    start tuple and the cut, so the randomized endpoint equation reuses it
    unchanged at `g := tnth (s5x5_rfree_layout uv)`. No new interpreter
    computation was needed.

# Probe ledger — unified instance analysis, Phase 0 (Abelian)

Repo `/Users/cheng-huiweng/Projects/coq/infotheo-pgg`, branch `pgg-smc`,
baseline `5453b93b`. Rocq 9.0.0. No production `.v` file, `_CoqProject`, or
request/response document was modified. The revised `abel_profile` is probed
here under the name `abel_profileP`; the production rename happens in Phase 3.

Build order: `probe_abel_profile.v`, then `probe_abel_plugs.v`, then
`probe_abel_negative.v`, then `probe_abel_sig.v` and `probe_abel_mutation.v`.

## Per-file results

| File | Purpose | Exit | Wall time |
|---|---|---|---|
| `probe_abel_profile.v` | four-seat interface, revised profile, false-bridge record, Klein-group facts | 0 | 5.0 s |
| `probe_abel_plugs.v` | secret-recovery plug, shuffle-analysis plug, two ObservedExecutions, endpoint-vector observer | 0 | 5.2 s |
| `probe_abel_negative.v` | parity invariant, exact full-L1 distance 1, executed transport, two SampleAdapters | 0 | 5.6 s |
| `probe_abel_sig.v` | discharged signatures of the section-bound negative results | 0 | 4.6 s |
| `probe_abel_mutation.v` | seven Fail-guarded perturbations, each preceded by a Check control | 0 | 4.9 s |

No `Admitted`, no `Abort`, no `Axiom` in any abelian probe file.

## Print Assumptions

Axiom-free (`Closed under the global context`):

- `abel_profileP`, `abel_pgg_GE`, `abel_G4_card`, `abel_G_abelian`,
  `abel_old_bridge_absent`
- `abel_det_correct`, `abel_shuffle_correct`, `abel_det_observed`,
  `abel_shuffle_observed`, `abel_reader_inj`, `abel_shuffle_executed_readerE`
- `abel_word_evalE`, `abel_flip_freq`
- `abel_pair_reader_not_injective`

The `boolp` trio (`propositional_extensionality`,
`functional_extensionality_dep`, `constructive_indefinite_description`) and
nothing else:

- `abel_word_group_dist`, `abel_executed_distance`, `abel_word_group_dist0`,
  `abel_adapter_distance`, `abel_executed_observation_distance`,
  `abel_parity_mass_half`, `abel_odd_identity_mass`

`abel_plug` is built from `abel_ts` and `abel_sum_mod_perm_compatible`, not
from a `CoveringScheme` record, so nothing on the abelian path touches
`s5_rayleigh_Q2_R` or any other justified-axiom boundary. Confirmed: every
execution-layer result is closed under the global context, and the only axioms
anywhere are the three `boolp` ones that a `realType` statement always carries.

## Mutation results

| # | Perturbation | Guarded command | Rejected |
|---|---|---|---|
| 1 | landed two-seat interface in the plug position | `Fail Definition abel_old_seat_plug` | yes |
| 2a | identity-content constant claimed to be 1 | `Fail Check (erefl : abel_identity_recon_value = Ordinal 1)` | yes |
| 2b | ObservedExecution with expected value 1 | `Fail Definition abel_bad_shuffle_observed` | yes |
| 3 | exact distance claimed to be 1/2 | `Fail have Hbad ... = 2%:R^-1` | yes |
| 4 | length-zero distance claimed to be 1 | `Fail have Hbad ... rho_from_words 0 ... = 1` | yes |
| 5 | two-endpoint reader used for the transport | `Fail have Hbad ... fdistmap abel_pair_reader ...` | yes |
| 6 | even-length parity class claimed at odd length | `Fail have Hbad ... exact: abel_word_eval_even` | yes |
| 7 | fuel 3 for the six-process run | `Fail have Hbad ... run_interp 3 ...` | yes |

Each guard is preceded by a `Check` of the unperturbed claim, so a `Fail` that
fired for a spelling reason would appear as a red `Check`. All eight controls
print.

Positive mutation witnesses (not `Fail`-guarded, proved outright):

- `abel_pair_reader_not_injective : ~ injective abel_pair_reader` — the
  identity and `abel_s2` have the same first two endpoints.
- `abel_odd_identity_mass : odd L.+1 -> abel_word_dist R L 1 = 0` — the class
  reached at odd length is `{s1, s2}`, not `{1, s1 s2}`.
- `abel_word_group_dist0 : var_dist (rho_from_words 0 abel_sigmas)
  abel_group_uniform = 1 + 1/2` — the length-zero value is computed exactly,
  so the positive-length hypothesis is shown to be load-bearing rather than
  merely unproved.

## Findings recorded during the abelian probes

1. The landed `abel_profile` bridge is false as stated in the request: `pi_T'
   (mp_PI abel_profile) = 1` and `ts_T' (rp_scheme (mp_plug abel_profile)) = 3`
   both hold `by []`, and `erefl` is rejected at that type. Replacing
   `Gen_PGG_2 abel_sigmas` by `@MkPGGI abel_M 3 (ord_tuple 4) abel_starts_uniq`
   makes the bridge `erefl` at 3 = 3, and `profile_k` is unchanged at 4.
2. `uniq (ord_tuple 4)` is `by rewrite val_ord_tuple enum_uniq`. `vm_compute`
   on `#|abel_G4|` times out: a `{set {perm 'I_4}}` cardinality forces the
   24-element permutation enumeration through opaque subtype machinery. The
   working route is `-!setUA !cardsU1 !inE cards1` plus six pointwise
   inequations, each proved by applying the permutations to sheet 0 or sheet 2
   and rewriting `!permE`.
3. `[set a; b; c; d]` is left-associated `setU` of singletons, so `cardsU1` and
   `big_setU1` need `-!setUA` first. After that both fire three times and leave
   `cards1` / `big_set1`.
4. `abelian (pgg_G abel_M)` follows from `abelian_gen` after rewriting the
   generated group to `<<[set s1; s2]>>` and `abel_gen_setE`; the two-element
   case needs `centP` and `abel_gens_commute` in both directions.
5. Fuel 150 finishes the six-process abelian run (dealer, verifier, four seats)
   with the content readout and the cut held abstract, in under half a second
   of `vm_compute`. `exec_procs` of a `dealer_secret_plug` over `abel_profileP`
   is convertible to the explicit six-element process list `by []`, which is
   how the generic endpoint equation is applied to the plug-derived run.
6. `abel_verifier_endpoints` mirrors `s5_verifier_endpoints` verbatim at four
   seats and reduces by `vm_compute; reflexivity`, generically in the content
   readout `g`, the start tuple and the cut.
7. `abel_sum_mod_perm_compatible` has all three of `g`, `s` and `shares`
   implicit (each occurs in the type of a later binder under `Set Implicit
   Arguments`), so it is applied as
   `abel_sum_mod_perm_compatible Hw0 (ts_encode_valid abel_ts s)`.
8. A generic `abel_static_tnth` stated over an arbitrary `ExecutionPlug
   abel_profileP` does not rewrite under `under eq_bigr` unless the plug is
   pinned: `under eq_bigr do rewrite (abel_static_tnth (e := abel_shuffle_plug))`
   works where the unpinned form reports no matching subterm.
9. The identity-content reconstruction constant is `Ordinal 2 : 'I_4`, the
   residue of 0 + 1 + 2 + 3 modulo 4, and it holds for every permutation cut,
   not only for cuts in the group. The reindexing step is
   `rewrite [RHS](reindex_perm w0)` inside a `have`;
   `rewrite -(reindex_inj (@perm_inj _ w0))` fails because the backward pattern
   expects the permutation to occur in the predicate as well as the summand.
10. **The counting lemma was not needed.** The brief suggested proving
    `#|{w : n.-tuple 'I_2 | odd (freq_vec w 0)}| = 2^(n-1)`. The route that
    landed avoids cardinalities entirely: the first-letter flip `abel_flip` is
    an involution whose `abel_flip_freq` inverts the parity, so `reindex_inj`
    turns the even-class mass into the odd-class mass, and `bigID` against
    `FDist.f1` gives `mass + mass = 1`, hence `mass = 1/2` by `mulIf`. This
    replaces a counting argument by a bijection and two bigop rearrangements.
11. `abel_flip_freq` is proved by `cardsD1` at `ord0`: the two membership sets
    agree off `ord0` and their `ord0`-membership bits are complementary, and
    `odd ((~~ b) + m) = ~~ odd (b + m)` closes by `case: b`.
12. Involution powers: `expg_invol : g * g = 1 -> g ^+ n = if odd n then g
    else 1`, proved by induction with `expgS`. Combined with
    `abelian_word_eval` and `big_ord_recl` twice this gives
    `abel_word_evalE`, from which the two parity classes read off directly.
13. `mulr_natl` is `n%:R * x = x *+ n`. Rewriting it backwards on a bare
    `x *+ 2` matched the wrong subterm; pinning the arguments
    (`-(mulr_natl (2%:R^-1 : R) 2)`) fixes it. `4^-1 + 4^-1 = 2^-1` goes
    through `4%:R = 2%:R * 2%:R`, `invfM` and `-mulrDl`.
14. `fdist_uniform_supp_in` and `fdist_uniform_supp_notin` take `R` explicitly
    and the cardinality proof as a leading argument, so they are applied as
    `@fdist_uniform_supp_in R _ _ abel_G4_card_gt0 g Hg`.
15. `bigID` on `\sum_(a : {perm 'I_4})` splits directly into
    `\sum_(i in abel_G4)` and `\sum_(i | i \notin abel_G4)` with no residual
    `true &&`, which is what makes `abel_var_distE` a four-line proof.
16. `var_dist_fdistmap_inj` was copied locally rather than imported from
    `instances/s5x5/s5x5_mixing.v`, so that the abelian probe does not pull in
    the S_5 x S_5 mixing development. Phase 3 should relocate the production
    copy to a shared file; the audit decision to do so is recorded here.
17. `{perm 'I_4}` and `pgg_word abel_M L.+1` both elaborate where a `finType`
    is expected, so the two `SampleAdapter` records need no `[the finType of
    _]` wrapper. `sa_cut_dist (abel_actual_adapter L) = abel_word_dist L` holds
    `by []`, because `rho_from_words` is literally `fdistmap word_eval
    word_uniform`.
18. Section discharge over `Variable R : realType` leaves `R` explicit and
    first on every negative result (`abel_word_dist R L`,
    `abel_group_uniform R`, `abel_word_group_dist R L`), but implicit on
    `var_dist_fdistmap_inj`, whose `R` occurs in the type of a later binder.
    `probe_abel_sig.v` records the printed signatures.
19. `SampleAdapter` is a primitive-projection record, so `sa_cut` carries its
    record argument IMPLICITLY (`Arguments sa_cut [R mp e s] _`) while
    `sa_sampleT` and `sa_sampleP` carry it explicitly. `sa_cut sa u` is a type
    error; the correct spelling is `sa_cut u`. The same demotion hits a probe
    definition whose second binder mentions the first: `abel_sample_reader
    (sa : SampleAdapter R abel_shuffle_plug) (u : sa_sampleT sa)` has `sa`
    implicit and must be written `@abel_sample_reader sa` at use sites.
20. The executed-observation layer is closed by
    `abel_sample_reader_dist : fdistmap (@abel_sample_reader sa) (sa_sampleP sa)
    = fdistmap abel_reader (sa_cut_dist sa)`, one `fdistmap_comp`, and
    `abel_executed_observation_distance`, which reads the distance 1 off the
    two adapters' own sample spaces rather than off the raw pushforwards.

## Phase 0 (facade/manifest graph, section 6.8)

File: `probe_facade_graph.v`. Build: `sh rebuild.sh probe_facade_graph.v`,
exit 0, 4.5 s, first compile. No proofs (vocabulary, record, rows, aliases,
Checks); nothing to run Print Assumptions on beyond the imported probe values.

- The planned typed vocabulary (CompletionLevel, TransferStatus, PggAxiom,
  AssumptionStatus with `AcceptsAxioms of seq PggAxiom`) elaborates with no
  collisions against the full S5 import closure.
- `AnalysisPathRow` elaborates with the dependent sample slot
  `forall R, option (@SampleAdapter R _ (OE.oe_execution apr_observed))`;
  instantiated twice: Observed-level row with `fun _ => None` at
  `s5_det_observed`, AnalysisBridged-level row with
  `fun R => Some (s5_rand_sample R)` at `s5_rand_observed` — the adapter's
  plug unifies with `OE.oe_execution s5_rand_observed` definitionally.
- Facade-skeleton module exposes typed transfer-status aliases; qualified
  bare Checks (the clean-client pattern) all print; the two mutation guards
  hold: an alias ascribed the wrong vocabulary type fails, an absent alias
  fails.
- Import-graph and _CoqProject plan recorded in the file header: status file
  below the facades, facades below the manifest, client single-import; no
  cycle by construction.
