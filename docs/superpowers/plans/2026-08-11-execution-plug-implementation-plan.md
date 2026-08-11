# Implementation plan: ExecutionPlug and SampleAdapter (stages S1-S4)

Date: 2026-08-11

Upstream chain: request → evaluation plan (`3991f21f`) → probe suite
(`490ad687`) → audited response (`cf64d7ae`). This plan turns the audited
response's recommendation into commit-sized tasks. Source code for every task
is a landed probe file — ported and renamed, not rewritten.

## User decisions (2026-08-11, all four collected)

| Decision | Selection |
|---|---|
| Design alternative | 6.2 — separate adapter layer over the untouched `MonodromyProfile` |
| Input-mode distinction | TWO SMART CONSTRUCTORS over one record (see D2 below) |
| Stage scope | S1-S4; both S5 items stay non-goals (word-space joint identity, input-party trace bound) |
| Naming | Audit names as-is: `ExecutionPlug`/`MkExecutionPlug`, fields `ep_*`, derived layer `exec_*`, theorems `exec_run_recovers`/`exec_run_correct`; `SampleAdapter`/`MkSampleAdapter`, fields `sa_*` |

### D2: the smart constructors (the one delta beyond compiled probe code)

Two definitional wrappers over `MkExecutionPlug`, both fixing the mode-relevant
fields; unprobed but purely definitional (no proof content), verified by the
S1 compile itself:

```coq
(* dealer-secret mode: no committing parties, identifiers empty by iota _ 0 *)
Definition dealer_secret_plug R mp inputT bridges players playersE content fuel :=
  @MkExecutionPlug R mp inputT bridges players playersE content
    (fun _ => [::]) fuel.
(* committed-input mode: the committing parties are the argument *)
Definition committed_input_plug R mp inputT bridges players playersE content
    input_procs fuel :=
  @MkExecutionPlug R mp inputT bridges players playersE content
    input_procs fuel.
```

(Signatures schematic; S1 writes them against the real record with the two
bridge fields spelled out.) The record itself stays single — soundness finding
15's stronger type-level mode index was explicitly not selected. S2 MUST
construct `pgl27` via `dealer_secret_plug` and five-card via
`committed_input_plug`, so the public interface exhibits the mode split.

## Stage S1 — the generic module

New file `pgg-smc/protocol/pgg_execution_plug.v` (+ `_CoqProject` entry after
`pgg_monodromy_profile.v`). Content, ported from
`probe_h_adapter_decomposition.v` with renames:

| Probe name | Production name |
|---|---|
| `EPP` / `MkEPP` | `ExecutionPlug` / `MkExecutionPlug` (fields keep `ep_*`) |
| `epp_dealer_id`/`epp_verifier_id`/`epp_seat_id`/`epp_input_id` | `exec_dealer_id`/`exec_verifier_id`/`exec_seat_id`/`exec_input_id` |
| `epp_input_ids`, `epp_dealer`, `epp_saprocs`, `epp_procs`, `epp_run` | `exec_input_ids`, `exec_dealer`, `exec_saprocs`, `exec_procs`, `exec_run` |
| `epp_endpoints`, `epp_seat_endpoint`, `epp_participant_trace`, `epp_input_trace` | `exec_endpoints`, `exec_seat_endpoint`, `exec_participant_trace`, `exec_input_trace` (extractors from `probe_e_traces.v` with the `.+3` offset) |
| `epp_decode`, `epp_seat_share_count` | `exec_decode`, `exec_seat_share_count` |
| `epp_static_endpoints`, `epp_endpoints_size` | `exec_static_endpoints`, `exec_endpoints_size` |
| `Theorem epp_run_recovers` | `Theorem exec_run_recovers` |
| `Theorem epp_end_to_end` | `Theorem exec_run_correct` |
| P-E generic equations (`epp_seat_endpointE`, `epp_coalition_endpointsE`, `epp_coalition_endpoints_seqE`, `epp_coalition_trace`) | `exec_seat_endpointE`, `exec_coalition_endpointsE`, `exec_coalition_endpoints_seqE`, `exec_coalition_trace` |

Plus the two smart constructors (D2). Section names keep the audit-confirmed
`execution_of_profile` / `run_of_static_observation` shapes.

Port hygiene (audit items bound to this stage): strip the probe headers'
status narration (soundness finding 16 / naming F33); fix the deferred
comment-tag findings F29-F32 during the port (no `@composes` pointing at
Definitions — point at `exec_run_recovers`/the first downstream lemma; no
degenerate `@intent: 0.` values; tag lines well-formed); every statement
comment terse-mathematical with a role tag. The dealer/verifier/seat/input id
constants get real `@intent` sentences.

Verification: `make -j1 pgg-smc/protocol/pgg_execution_plug.vo`;
`rocq_assumptions` on `exec_run_recovers`, `exec_run_correct` (boolp trio
only); commit through the gate. One commit.

## Stage S2 — the two instances

New files (existing instance files UNTOUCHED — this is the zero-migration
claim):

- `pgg-smc/instances/pgl27/pgl27_exec.v`: `pgl27_exec_plug : ExecutionPlug (pgl27_profile R)`
  built via `dealer_secret_plug`; port from probe_h's PGL instantiation
  section: `pgl27_exec_procsE` (process equality, `by []`), the three
  discharges (`Hterm`/`Hep`/`Hrecon` from `pgl27_run_terminates`/
  `pgl27_endpoints`/`pgl27_run_recovers` internals, fuel and index pinned),
  and the instantiated `pgl27_exec_recovers` + `pgl27_exec_correct`.
- `pgg-smc/instances/kim2025/five_card_exec.v`: `five_card_exec_plug` at
  arbitrary bias via `committed_input_plug`; port from probe_h's five-card
  section plus probe_d's bias-invariance conversion lemma
  (`five_card_exec_procs_biasE`) and the conjunction-recovery discharge.

Comment discipline: the corrected "8 seats, 8 shares and 8 cards" wording
(naming F27) is the source of truth, not the pre-fold probe text.

Verification per file: `make -j1` on the new `.vo`, assumptions check, gate
commit. Two commits (one per family).

## Stage S3 — trace corollaries

Append to the two S2 files (they are this cycle's instance surface; landed
trace files stay untouched): the instance seat/coalition endpoint corollaries
from `probe_e_traces.v` (`pgl_seat_endpointE`, `pgl_coalition_endpointsE`,
`fc_*` twins → `pgl27_exec_seat_endpointE` etc.), the raw-trace agreement
lemmas (`pgl_player_raw_traceE`/`fc_player_raw_traceE` → `*_exec_raw_traceE`),
and the input-position facts (`fc_input_positions`). The
`trace_secrecy_of_view` hookup is exactly the sub-claim the soundness audit
marked UNPROBED: S3 verifies it by proving ONE corollary — the den Boer
`denboer_trace_secrecy` view argument re-expressed through
`exec_participant_trace` — and if that resists two attempts, the resistance is
recorded and the hookup moves to the S5 non-goals rather than blocking S3.
One commit.

## Stage S4 — the sample layer

New file `pgg-smc/security/pgg_sample_adapter.v`: the `SampleAdapter` record
and the three layers from probe_h (`sa_run`, `sa_seat_view`,
`sa_coalition_view`, `sa_seat_dist`, `sa_coalition_dist`, `sa_cut_dist`,
`sa_static_seat_view`, `sa_seat_viewE`, `sa_seat_distE` — names already
production-form) with `content_obs`/`Hep` as section parameters. Instance
values appended to the S2/S3 instance files: `pgl27_sample` (the `sa_pgl`
port: `pgl27P`, `fst`, `snd`), the den Boer rotation sample (probe_f's
`fc_samp_*` with the `fc_sigma ^+ k` cut), the finite-word sample
(`pglw_*` with `word_eval`), and the two compiled identities
(`pgl_sample_is_witness_prod`, `pglw_cut_dist_word` →
`pgl27_sample_witness_prodE`, `pgl27_word_cut_distE`). No privacy statement of
any kind enters this stage (soundness invariant 4). One commit.

## Cross-stage rules

- Execution: `rocq-prover` subagents at `model: opus`, one at a time, one
  rocqworker; the launch preamble carries the probe file paths as verbatim
  source, the fuel/index pinning discipline, and the lazy-eval rules.
- Every commit passes the audit gate unbypassed; if Stage 2 of the gate fails
  on infrastructure, a real auditor agent supplies the review first.
- Probe files are never edited again (evidence freeze at `cf64d7ae`); the port
  cites them in commit messages.
- After S4: `/rocq:golf` on proof bodies only, then assumptions re-verified.
- Paper wording: only the response section-10 claim (as amended by the audit)
  may be ported to WADT prose, in a separate later cycle.

## Non-goals (unchanged from the response)

The S5 items: the `fdistmap` product identity connecting the word sample space
to the landed `pgl27P_word_gen`, and any bound on the input-party trace
observable. Plus everything in request section 11.

## Gate

Implementation starts on explicit user go. Estimated total: ~1350 lines of
ported Rocq across 5 commits, all de-risked by compiled probes; the only
unprobed items are the two definitional smart constructors (D2) and the S3
`trace_secrecy_of_view` corollary, both with recorded fallbacks.
