# Evaluation response: end-to-end execution from a group profile

Date: 2026-08-11
Request: `docs/superpowers/requests/2026-08-11-monodromy-profile-end-to-end-ROCQ-formalization-request.md`
Plan: `docs/superpowers/plans/2026-08-11-monodromy-profile-end-to-end-evaluation-plan.md`
Probes: `docs/superpowers/probes/2026-08-11-monodromy-profile-end-to-end/` (committed as `490ad687`; every claim below cites a compiled file there)
Mutation ledger: `MUTATIONS.md` in the probe directory (six red mutations, each with the observed error verbatim)

No permanent `.v` file or paper source was changed. The probe suite contains zero
`Admitted`, `Axiom`, `Parameter`, or `Abort`; every cited lemma is `Qed` with
`Print Assumptions` reporting exactly the boolp baseline
(`propositional_extensionality`, `functional_extensionality_dep`,
`constructive_indefinite_description`).

## 1. Verdict: literal target — NO-GO

Compiled evidence: `probe_a_sufficiency.v`. Using only a generic
`mp : MonodromyProfile R` and natural runtime values, the eight constructions of
request 7.1 require a six-entry register of data the profile does not carry:

| # | Datum | Type | Why not in the profile |
|---|---|---|---|
| R1 | content readout | `seq 'I_N -> ('I_N -> 'I_N)` | `rp_content` is a fixed endomorphism, constant in secret and inputs; the secret-dependent readout is untypable without bridge 2 (see section 3, F1) |
| R2 | shuffle word/deck | `seq (pgg_gT M)` | `mp_security` stores a word length and a distribution, never a concrete deck |
| R3 | input processes | `seq (aproc pgg_dtype (pgg_data N))` | no input-mode field exists (request gap 5.4); without them the den Boer run is a 7-process list where 9 are needed |
| R4 | input identifiers | `seq nat` | derivable from R3 (`iota`), but only once R3 exists |
| R5 | word index `P_idx` | `nat` | announced by the dealer, not recorded anywhere |
| R6 | interpreter fuel | `nat` | no field |

Only the participant enumeration and the verifier come free. Split per the
audit (request 7.1 permits "runtime values that a protocol must naturally
receive"): three entries are STRUCTURAL gaps the profile cannot escape — R1
the readout, R3 the input processes, R6 the fuel; two are permitted runtime
values that the final interface indeed treats as run arguments — R2 the deck
and R5 the word index; and R4 is derivable from R3. The literal target fails
on the three structural entries, one of which is a process, not a value, so no
reading of "fill one record" makes the current `MonodromyProfile` sufficient.
The mutation (`probe_a_mutation.v`, red) shows the generic constructions are
carrier-constraining, not vacuously polymorphic.

## 2. Verdict: layered target — GO on clauses 1 and 2; clause 3 not achieved
(typed layer only)

Compiled evidence: `probe_h_adapter_decomposition.v`. Request 2.2 is three
clauses and the verdict is per-clause; do not quote "layered: GO" without this
split.

- "A group profile supplies the algebraic, protocol-role, shuffle, and
  reconstruction data" — HOLDS, untouched: all seven landed `MonodromyProfile`
  constructors compile as they stand (section 8).
- "A reusable execution adapter constructs the piSMC run and traces" — HOLDS,
  machine-checked: the eight-field `EPP` record plus one generic `Qed` theorem
  (`epp_end_to_end`: termination carried through, endpoint count and recovery
  derived) is discharged at both carriers — PGL at `pgl27_profile R` and the
  five-card family at arbitrary bias `eps` under the three Kim constraints —
  from three per-carrier facts each plus the cut-membership side condition
  (`w0 \in pgg_G _`), all closed by landed instance lemmas.
- "A reusable security adapter connects the resulting observations to exact or
  finite-shuffle proof principles" — HOLDS ONLY IN ITS TYPED HALF. The
  four-field `SampleAdapter` and its three layers (per-sample run, view random
  variables, `fdistmap` pushforwards) are compiled at the landed exact and
  finite-word sample spaces (`probe_f_distributions.v`), and the
  static-observation equations are `Qed`; but no variation-distance, entropy,
  or mutual-information result is proved through it. The observations are
  connected to a distribution layer, not yet to a proof principle. That last
  step is scoped as remaining work (section 11, stage S4/S5), not claimed.

## 3. Gap matrix (request section 5 → compiled status)

| Gap | Status after probing | Evidence |
|---|---|---|
| 5.1 no dealer from profile | CONFIRMED; closed by `EPP` (`ep_content`, R2/R4/R5 as run/derived data) through the landed `dealer_with_input_encoding` (`pgg_run.v:45`) | probe_a, probe_c |
| 5.2 no process assembly | CONFIRMED; closed generically: `epp_saprocs` = dealer :: verifier :: seats ++ input processes, erased image, `run_interp` at `ep_fuel` | probe_a F2, probe_c/d |
| 5.3 player/share bridge absent | CONFIRMED, and UNDERCOUNTED: there are TWO bridges. Bridge 1 `pi_T' = ts_T'` (the requested one) and bridge 2 `N = ts_T'.+1` (cards vs shares), discovered by a failed elaboration (F1). Both are `erefl` at both carriers; both refute at mismatches (red mutations b, h). Bridge 1 is the load-bearing field: without it the decoder cannot be STATED (probe_h_mutation fails at a Definition, not a proof) | probe_a F1, probe_b, probe_h_mutation |
| 5.4 input modes not in profile | CONFIRMED; closed by `ep_inputT` + `ep_input_procs` in one record — no sum type, no option, no second constructor. The committed-input instance puts the prologue parties in `ep_input_procs`; the empty-input instance passes `fun _ => [::]`. The two modes stay publicly distinct through the field values, and the record accommodates both without change | probe_c/d |
| 5.5 run is not a distribution | CONFIRMED and now type-enforced: the three layers are distinct definitions, and the pushforward of a raw trace is a compiled `Fail Definition` (`seq` is not a finType) | probe_f |
| 5.6 no generic coalition trace | SPLIT, measured: extraction and assembly generic; endpoint-level view/trace equations generic from one hypothesis `Hep`; the raw-trace-to-content step is irreducibly per-instance (the seat-by-seat `vm_compute` leaf lemmas); the view-to-trace lift via the landed `trace_secrecy_of_view` was NOT exercised by any probe — it is asserted from the landed instance files only (soundness finding 6) and its reuse is scoped to stage S3 verification | probe_e |
| 5.7 security hypotheses not fields | RESOLVED BY EVIDENCE: sample space, prior, arg map, cut map are adapter fields (four); `Hep` and `content_obs` must stay theorem hypotheses (they are the only interpreter contact); `sw_rho_dist` is typed in the permutation carrier and connects only via `fdistmap pgg_rho` (section 6 finding) | probe_f |
| 5.8 instances prove bridges manually | CONFIRMED as duplication, now eliminated generically: the P-C/P-D transports and the P-H discharge table show the same three facts close both carriers; with `ep_players` a field the process equalities are pure conversion | probe_c/d/h |
| 5.9 dependency-cycle risk | NO CYCLE: 119 modules, live graph acyclic; both placements (execution adapter in `protocol/`, sample adapter in `security/`) have zero instance modules in their import closure and no non-instance module imports instances | probe_g_depgraph_output.txt |
| 5.10 session-type and computation risk | MEASURED: elaboration green (probe_c/d); `enum`-based `vm_compute` RED — `enum 'I_8` is vm-stuck (385 KB stuck normal form, leaves matching Qed-opaque `idP`), both direct attempts killed, versus 0.023 s / 0.036 s on the concrete list; compile time green (~6 s per probe file, import-dominated) | probe_g_vmcompute.v timing block |

## 4. Proposed public interface

Names below are probe-local; final names follow repository conventions
(naming audit, section 12). All types are as landed and compiled.

### 4.1 Alternative 6.2 (recommended): execution adapter over the profile

```coq
Record EPP (R : realType) (mp : MonodromyProfile R) := MkEPP {
  ep_inputT         : Type ;
  ep_players_bridge : pi_T' (mp_PI mp) = ts_T' (rp_scheme (mp_plug mp)) ;
  ep_cards_bridge   : (pgg_N' (mp_M mp)).+1 = (ts_T' (rp_scheme (mp_plug mp))).+1 ;
  ep_players        : seq 'I_(pi_T' (mp_PI mp)).+1 ;
  ep_playersE       : ep_players = enum 'I_(pi_T' (mp_PI mp)).+1 ;
  ep_content        : ep_inputT -> seq 'I_(pgg_N' (mp_M mp)).+1
                        -> ('I_(pgg_N' (mp_M mp)).+1 -> 'I_(pgg_N' (mp_M mp)).+1) ;
  ep_input_procs    : ep_inputT
                        -> seq (aproc pgg_dtype (pgg_data (pgg_N' (mp_M mp)).+1)) ;
  ep_fuel           : nat ;
}.
```

Field-by-field provenance: `ep_inputT`/`ep_input_procs` from probe_a F2 (input
processes are load-bearing; their absence deadlocks the committed-input run);
the two bridges from probe_b (both `erefl` at matched carriers, refutable at
mismatched ones); `ep_players`+`ep_playersE` from probe_g (the enum is vm-stuck,
so a new instance cannot prove termination without the concrete list; the
equation recovers the canonical enumeration propositionally — the design
`pgl27_run.v:53-56` documents informally, now measured); `ep_content` uncast
from probe_c (the cast form is provably equal but downgrades the process
equality from conversion to rewrite under a dependent constructor);
`ep_fuel` from probe_a/c (with the pinning discipline of section 10).

Derived generically (no instance work): input identifiers at offset
`(pi_T').+3` (probe_d's as-built correction), dealer via
`dealer_with_input_encoding`, session-typed and erased process lists,
`run_interp` run, process-id constants (`epp_dealer_id`/`epp_verifier_id`/
`epp_seat_id`/`epp_input_id`), verifier endpoints, per-seat endpoint reader,
participant and input-party raw traces, endpoint decoder along bridge 1.

Generic theorems (Qed at generic `mp`, `e`): `epp_run_recovers` from `Hep` and
`Hrecon` only (termination is not a premise of recovery), and `epp_end_to_end`
from all three of `Hterm`/`Hep`/`Hrecon`, carrying the termination fact as a
conjunct (`probe_h_adapter_decomposition.v:292-301` and `:331-337`); the P-E
endpoint equations from `Hep` alone; the P-B round trip `gen_decode_encoded`.

Production names (naming audit, folded): the record ships as `ExecutionPlug` /
`MkExecutionPlug` — its initials give exactly the `ep_` field prefix already in
use (zero field renames), and `Plug` is the repo's head noun for the
instance-supplied half completing a generic construction (`ReconPlug`,
`mp_plug`, `five_card_plug`). The derived layer ships as `exec_*`
(`exec_procs`, `exec_run`, `exec_endpoints`, `exec_decode`, ...), keeping it
out of the `ep_` projection namespace and matching the word-prefix precedent
of `protocol_of_profile`'s `profile_*`. The theorems ship as
`exec_run_recovers` (the landed `_run_recovers` suffix, five instances) and
`exec_run_correct` in place of `epp_end_to_end` (`_correct` is the repo's
identifier for prose "end-to-end": `ar_protocol_correct`,
`dealer_words_correct`; `end_to_end` appears repo-wide only in prose). Probe
files keep the probe-local names.

### 4.2 Security/sample adapter (second layer, `security/` placement)

```coq
Record SampleAdapter (R : realType) (mp : MonodromyProfile R) (e : EPP mp) :=
  MkSampleAdapter {
    sa_sampleT : finType ;
    sa_sampleP : R.-fdist sa_sampleT ;
    sa_arg     : sa_sampleT -> ep_inputT e ;
    sa_cut     : sa_sampleT -> pgg_gT (mp_M mp) ;
  }.
```

With derived layers `sa_run` (per-sample concrete run), `sa_seat_view` /
`sa_coalition_view` (RVs), `sa_seat_dist` / `sa_coalition_dist` / `sa_cut_dist`
(`fdistmap` pushforwards; `fdistmap _ P` is the landed idiom and is proba.v's
`` `p_ `` by definition). `content_obs` and `Hep` remain theorem hypotheses.
All three landed sample spaces fit unchanged: PGL exact (`fst`/`snd` on
`bool * pgg_gT`), den Boer (`u.1` / `fc_sigma ^+ u.2` — the power-map cut costs
one destructing intro pattern), finite-word (`u.1` / `word_eval u.2`).
Precision on what is compiled where (soundness finding 11, closed at audit
fold): probe_f exercises the four slots as SECTION VARIABLES over the
six-field probe-era adapter at all three sample spaces; the RECORD packaging
over the final eight-field adapter is instantiated at the PGL exact space
(`sa_pgl` and `sa_pgl_seat_dist`, appended to probe_h and recompiled green).
Naming audit: `SampleAdapter` / `sa_` / `MkSampleAdapter` confirmed as-is
(the sibling-consistent `SamplePlug` is blocked — `sp_` is taken).

### 4.3 Alternative 6.1: extend or package the record

Compiled comparison (`probe_h_adapter_decomposition.v:772-` and its comment
block): the packaged form `MonodromyProfileX { mpx_core; mpx_exec }`
instantiates at both carriers reusing the landed profile values (`by []`).
A flat 13-field record would change the arity of all five direct constructor
calls and both wrappers, and would force the three run-less instances (s5,
s5x5, abelian) to invent execution data or take option-typed fields. Dominated
by 6.2 on migration cost with no expressiveness gain; the packaged form is
available for free on top of 6.2 if a one-value handle is ever wanted.

### 4.4 Alternative 6.3: no records, explicit arguments

The measured status quo: the register (section 1) is exactly the argument
bundle every construction repeats — six arguments before run arguments, plus
three proof obligations per instance, with no statement-level home for the
bridges. probe_h's discharge table shows the same content organized once.
Dominated by 6.2: same proof work, worse statements, and the paper could not
name a reusable artifact.

## 5. Probe paths, build commands, results

Build command (all probes; one worker):
`sh docs/superpowers/probes/2026-08-11-monodromy-profile-end-to-end/rebuild.sh <file>.v`
which is `rocq compile -q` with the `_CoqProject` `-R` flags (lines 259-264
plus the instance lines 265, 266 and 274). Red files verified by direct
`rocq compile` (the script's grep pipe masks exit codes — measured tooling
fact). Every green file was independently re-verified by the orchestrator:
fresh recompile after deleting the `.vo`, forbidden-command sweep, and — for
the six files that have one — direct red-compile of its mutation.

| File | Result | Key content |
|---|---|---|
| `probe_a_sufficiency.v` (green, 9 Qed) + `probe_a_mutation.v` (red) | literal NO-GO register | six-entry register; F1 bridge-2 discovery via `Fail Definition`; both carriers instantiate; five-card side conditions proved, not hypothesised |
| `probe_b_count_bridge.v` (green) + `probe_b_mutation.v` (red) | both bridges | `erefl` at 7/7/8 and 4/4/5; generic decoder `gen_decode`; round trip `gen_decode_encoded` Qed; `pgl_decodeE`/`db_decodeE` equal the landed `tcast` shapes via `eq_irrelevance` |
| `probe_c_pgl27_exec.v` (green) + `probe_c_mutation.v` (red) | PGL execution | record elaborates; `epp_procs = pgl27_procs` in 3 lines; termination/endpoints/recovery transported; fuel-divergence trap found and pinned |
| `probe_d_fivecard_exec.v` (green) + `probe_d_mutation.v` (red) | five-card execution | `epp_procs = den_boer_procs` at ARBITRARY bias; bias invariance by conversion (`by []`); conjunction recovery `= a && b`; input-id off-by-one caught and corrected |
| `probe_e_traces.v` (green, 25 Qed) + `probe_e_mutation.v` (red) | trace layer | extractors incl. input-party traces; generic endpoint equations from one `Hep`; reusable-vs-instance split measured; index-pinning discipline |
| `probe_f_distributions.v` (green, 23 Qed, 2 `Fail Definition`) | distribution layer | three layers typed; raw traces have no layer 3 (type error); `pgl27P = uniform x sw_rho_dist` by conversion; `sw_rho_dist` carrier verdict; word space fits the same adapter |
| `probe_g_depgraph.py` + output | dependency half | 119 modules acyclic; both placements cycle-free |
| `probe_g_vmcompute.v` (green) | computation half | enum vm-stuck (killed 70 s / prover death) vs 0.023 s / 0.036 s concrete; verdict: concrete-list field required |
| `probe_h_adapter_decomposition.v` (green) + `probe_h_mutation.v` (red) | the layered verdict | final records; `epp_run_recovers`/`epp_end_to_end` Qed generically and at both carriers, zero Admitted; 6.1 comparison; bridge-1 mutation fails at a Definition |

## 6. Module dependency analysis

From `probe_g_depgraph_output.txt` (parses every `Require` line of 119 pgg-smc
modules): the live graph is acyclic; no non-instance module imports an instance
module; the execution adapter's import closure (16 modules: `pgg_run`,
`pgg_monodromy_profile`, `pgg_input_commitment`, `card_exchange_pismc`,
`pgg_interface`, `pgg_session_types`, reconstruct trio, and their closures)
contains no instance module, and likewise the security adapter's (18, adding
`pgg_trace_secrecy`). Placement: execution adapter in `pgg-smc/protocol/`
(after `pgg_run` and `pgg_monodromy_profile`, which do not import each other);
sample adapter in `pgg-smc/security/`. No cycle is possible for either.
Directory-level layering is not strict in the live tree (protocol, security,
reconstruct reference each other across files); module-level acyclicity is the
invariant that holds and the one that matters.

One typed boundary fact for the security layer: `sw_rho_dist (mp_security mp)`
has carrier `{fdist {perm 'I_N}}`, not `{fdist pgg_gT (mp_M mp)}` (compiled
`Fail Definition` in probe_f). The connecting map is `fdistmap (@pgg_rho _)`.
At every current instance the mismatch is invisible (`Gen_PGGTypes` makes the
group be the permutation group by conversion, and at PGL the landed sample
space factorizes as `fdist_uniform x sw_rho_dist` by conversion); it bites for
any future profile whose monodromy is a proper representation. The interface
must either store cut laws in the group carrier and expose the `pgg_rho` image,
or the profile must gain a group-side shuffle law. Recommended: the former —
it needs no profile change.

## 7. Proof obligations at the two carriers

What an instance owes the generic layer (the P-H discharge table, all closed
from landed lemmas at both carriers):

| Obligation | PGL closes with | Five-card closes with |
|---|---|---|
| `Hterm` (termination at `ep_fuel`) | `pgl27_run_terminates` | `den_boer_run_terminates` |
| `Hep` (endpoint equation) | `pgl27_endpoints` | `den_boer_endpoints` |
| `Hrecon` (static decode of observations) | `pgl27_run_recovers` internals + `pgl27_endpoints_size` | `den_boer_run_recovers` + `val_tcast` chain |
| `ep_playersE` | `inj_map val_inj` + `val_enum_ord` | same |
| both bridges | `erefl` | `erefl` |

Both instantiated headlines additionally carry the cut-membership side
condition (`w0 \in pgg_G _`) as a theorem hypothesis — disclosed here, not
only in the Q9 answer.

A NEW instance (no landed lemmas) owes: the three facts above proved directly —
termination by `vm_compute` on its concrete `ep_players` (measured 0.023-0.036 s
at these carrier sizes), the endpoint equation by the `pgl27_verifier_endpoints`
pattern, the static recovery from its scheme's invariance — plus, for the trace
layer, the per-seat content leaf lemmas (the irreducible instance cost, section
9). `Hrecon`'s quantification over the size proof is what keeps the generic
derivation `eq_irrelevance`-free (probe_h finding).

## 8. Migration impact, all existing profiles

Landed `MonodromyProfile` constructors (grep-verified 2026-08-11):

| Constructor site | Under 6.2 | Under flat 6.1 |
|---|---|---|
| `instances/pgl27/pgl27_profile.v:105` | untouched; gains an `EPP` value alongside | arity change |
| `instances/kim2025/five_card_family.v:164` | untouched; gains one eps-generic `EPP` | arity change |
| `instances/s5/s5_profile.v:51` | untouched (no run exists) | must invent execution data or option fields |
| `instances/s5x5/s5x5_profile.v:42` | untouched (no run exists) | same |
| `instances/abelian/abel_profile.v:69` | untouched (no run exists) | same |
| `instances/denboer1989/den_boer_profile.v:76` (wrapper) | untouched | changes with wrapped function |
| `instances/kim2025/rigidity_kim_instance.v:66` (wrapper) | untouched | changes with wrapped function |

Existing mathematical statements are not changed by migration (request Q11):
`pgl_decodeE`/`db_decodeE` prove the generic decoder equals each instance's
landed reconstruction shape, the process equalities are conversions once
`ep_players` is a field, and the seven RUN-LEVEL lemmas transport verbatim
with fuel and index pinned (`pgl27_run_terminates`, `pgl27_endpoints`,
`pgl27_endpoints_size`, `pgl27_run_recovers`; `den_boer_run_terminates`,
`den_boer_endpoints`, `den_boer_run_recovers`). Nothing in the trace, secrecy,
or mixing files was exercised by transport — and under 6.2 nothing is REQUIRED
to transport at all, since the landed files stay untouched. Kim's
`kim_procs := den_boer_procs` is subsumed by the bias-invariance conversion.

Duplicated artifacts a NEW instance no longer writes (the claim-ledger
"end-to-end reuse" row, enumerated): the dealer definition
(`pgl27_dealer_run` / `den_boer_dealer_run` shape); the session-typed and
erased process lists (`pgl27_saprocs`/`pgl27_procs`,
`den_boer_saprocs`/`den_boer_procs`); the endpoint-size lemma
(`pgl27_endpoints_size` shape); the decoder cast (the `tcast` inside
`pgl27_run_recovers`/`run_recover_pgl27`); the input-identifier list; the
player-list-to-enum conversion as a floating lemma (now the field
`ep_playersE`); and the witness-swap alias pair (`kim_procs`,
`kim_player_trace`). What every instance still writes is section 9. Note: `abel_profile` sits in
`instances/abelian/`, which is outside the pgg-smc instance scope
(kim2025/denboer1989/s5/s5x5 per project constraints) but is counted here
because the migration claim quantifies over every landed constructor.

## 9. What remains instance-specific after the extension

1. The adapter field VALUES: input type, concrete player list, content readout,
   input processes, fuel (one small definition each; the bridges and
   `ep_playersE` are one-liners).
2. The three per-carrier facts of section 7 — for new instances, real proof
   work, dominated by the `vm_compute` termination and endpoint runs.
3. The per-seat raw-trace-to-content leaf lemmas (`pgl27_abs_p0..p7`,
   `denboer_abs_p0..p4` pattern): irreducible, because process bodies are
   concrete only at an instance (probe_e verdict).
4. All distribution choices: the secret/input prior (a model parameter
   everywhere), the sample space and its two maps (four adapter fields), the
   dealing mode (fixed-representative vs all-decks), word vs uniform shuffle.
   At PGL exact, the cut factor is the profile's own `sw_rho_dist` by
   conversion; elsewhere it is instance data.
5. Privacy theorems themselves: view equations, mixing bounds, and every
   entropy/variation-distance statement (unchanged by this design; see the
   boundary in section 2).
6. The five-card side conditions at a chosen bias (proved as one-liners at
   `eps = 0` in the probes).

Uncovered observable, flagged not solved: the input-party traces (positions
`(pi_T').+3 + j`) have no landed extractor, bound, or theorem, at the carrier
where the committed bits ARE the secret. The adapter now names them
(`epp_input_trace`); nothing yet bounds them.

## 10. Paper-safe claim (supported by the compiled interface today)

> A group instance supplies one algebraic profile and one small execution
> adapter (an input type, two count equalities, a concrete seat list with its
> enumeration equation, a content readout, its committing processes, and an
> interpreter fuel). From these the framework constructs the complete piSMC
> process list, the interpreter run, the per-participant and per-input-party
> traces, and the verifier endpoints; one generic machine-checked theorem then
> yields the endpoint count and the recovery of the protocol's output — the
> dealt secret at the PGL dealer-secret instance, the committed conjunction at
> the five-card family at every shuffle bias — and carries the instance's
> termination fact through, all from three per-instance facts and the
> cut-membership side condition. A typed sample layer maps profile and adapter
> data to sample spaces, view random variables, and pushforward endpoint-view
> distributions, with the cut law proved identical to the landed word
> distribution at the finite-word instance.

What the paper must NOT say (each violates a compiled boundary): that one
profile alone suffices (section 1); that the framework derives the security
proofs (section 2, third clause); that the generic theorem PROVES termination
(it forwards the instance's termination fact; only endpoint count and recovery
are derived — soundness finding 2); that the framework produces "trace
distributions" (raw traces provably have no distribution layer; the compiled
laws are endpoint-view laws — soundness finding 3); that the sample layer's
view objects are the landed analyses' view objects (only the cut-law identity
`samp_cut_dist = rho_word` is compiled; the view-level connection is stage-S4
work — soundness finding 4); that trace distributions come from the profile
(the prior and sample space are parameters, section 9.4); or that per-position
endpoint facts are coalition or trace privacy (nothing in the probes states or
implies any privacy result).

## 11. Recommendation and scope estimate

RECOMMENDATION: alternative 6.2 — the separate execution-adapter layer, with
the sample adapter as its security-side companion. 6.1 is dominated (section
4.3); 6.3 is dominated (section 4.4). The request's own leaning toward 6.2 is
confirmed by every probe that touched the alternatives.

Implementation stages (each independently compilable, in order; sources are
probe files to be adapted, not rewritten):

| Stage | Content | Source | Size |
|---|---|---|---|
| S1 | `protocol/` execution-adapter module: `EPP` record, derived assembly, process-id constants, decoder, generic theorems (`epp_run_recovers`, `epp_end_to_end`, endpoint equations) | probe_h generic sections + probe_e equations | ~400 lines |
| S2 | PGL + five-card adapter instances with the three discharges each; retire the per-instance duplication (the run files keep their statements, gaining `= generic` corollaries) | probe_c/d/h instantiation sections | ~450 lines |
| S3 | Trace-extractor corollaries at both carriers (seat/coalition/input-party readers, content-leaf hookup) | probe_e instance sections | ~250 lines |
| S4 | `security/` sample-adapter module + the three layers + the static-observation equations; `sw_rho_dist` image lemmas | probe_f + probe_h SampleAdapter section | ~250 lines |
| S5 (open) | The two flagged obligations if wanted: the joint word-space pushforward identity (`fdistmap` product lemma infotheo lacks), and any bound on the input-party trace observable (new artifact, new mathematics) | flagged in probe_f/e | not estimated |

S1 -> S2 is the dependency spine; S3 and S4 are independent of each other after
S2. Naming for all public identifiers to be fixed at S1 review time per the
naming audit (section 12).

## 12. Adversarial audits

Two independent audits were dispatched on this response, the probe suite, and
the repo (plan section 5). Deviation from the plan's agent table, recorded: the
naming remit ran on a general-purpose read-only agent rather than the per-file
style auditor, because the remit is repo-wide precedent verification of a
proposed interface, which a per-file punch-list auditor cannot span.

Both audits returned **GO-WITH-FIXES, no blocker**. Every finding is folded
or dispositioned below; nothing was rejected.

**Soundness audit (compile-capable).** All twelve invariants HOLD (invariant 7
in the weak, value-level sense — finding 15 below; invariant 12 modulo three
narration comments — finding 16). Vacuity: not vacuous — a fresh scratch
recompile builds both carrier instances and discharges every hypothesis from
landed lemmas. Tautology: the bias-invariance statement quantifies genuinely
independent biases, constraint packs, and word lengths. Honest boundary: no
information-theoretic statement exists anywhere in the suite. Sixteen quoted
claims re-verified exactly; the dependency script reproduced byte-identical
output.

Accepted and folded (soundness): 1 per-clause layered verdict (section 2);
2, 3, 4, 9, 17 paper-claim corrections (section 10); 5 register split
(section 1, Q2); 6 the `trace_secrecy_of_view` lift marked UNPROBED (section
3, gap 5.6); 7 `Hterm` attribution (section 4.1); 8 cut-membership side
condition surfaced (sections 2, 7, 10); 10 in-file `Print Assumptions` blocks
appended to probe_a and probe_b, recompiled green; 11 the `SampleAdapter`
record instantiated at the PGL exact space (`sa_pgl`, appended to probe_h,
recompiled green); 12 mutation-count scoping (section 5); 13 misdirected
correction removed (section 3); 14 transport scoping and the enumerated
duplication list (section 8); 19 citation ranges (section 4.1); 20 the
duplicated-artifact list (section 8).

Recorded, deferred to the S1 production port: finding 16 (three
narration-bearing statement comments in probe_b/probe_d/probe_f — probes are
evidence artifacts outside the audit gate; the production port must strip
them). Finding 15 is a USER DECISION at S1 review: the two input modes are
distinct only at the value level (`ep_input_procs = fun _ => [::]` versus
commit parties); a type-level mode predicate is a strengthening option the
evaluation does not presuppose.

**Naming/precedent audit (read-only).** 17/17 anchors verified at live paths
(two MINOR line-range drifts, corrected here); zero name collisions; zero
redundancy with landed records (nearest conceptual relative: `ProtoSpec` in
`declarative/`, not reusable, and it independently confirms the
initials-prefix rule).

Accepted and folded (naming): F19 production record name `ExecutionPlug` /
`MkExecutionPlug` with the `ep_` prefix; F21 derived layer `exec_*`; F23
`exec_run_correct` replacing `end_to_end` in identifiers (all three in section
4.1); F27 the "7 seats, 7 shares" comment corrected to "8 seats, 8 shares" in
probe_h and probe_e, recompiled green; F28 the `@composes` target of
`epp_seat_share_count` corrected to its actual consumer in probe_e; F34 the
`sa_*` field vocabulary in Q10; F1/F2 citation corrections (sections 5, 4.1).

Confirmed as-is: `SampleAdapter`/`sa_`/`MkSampleAdapter` (F20); the X_of_Y
section names (F22); the `_run_recovers`/`_terminates`/`_endpoints`/`E`
suffixes (F24, F25); I001 conformance of every proposed name (F26 — with the
auditor's caution that I001 cannot see `Record` type names or fields, so
F19-F21 need human enforcement at S1 review).

Recorded, deferred to the S1 port: F29-F33 (comment-tag polish in probe
files: two `@composes` targets pointing at Definitions, one malformed tag
line, two degenerate `@intent` values on one-line constants, header status
narration).

Rejected: none.

## 13. Answers to the twelve evaluation questions

1. **Can the literal target be achieved without changing `MonodromyProfile`?**
   No (section 1): six register entries, one of them a process.
2. **What exact extra data is missing?** The register R1-R6, verbatim types in
   section 1. Structurally missing: R1, R3, R6; permitted runtime values: R2,
   R5; derivable from R3: R4.
3. **Extend the record or new layer?** New layer (sections 4, 8, 11): zero
   migration for seven landed constructors versus arity changes everywhere,
   and run-less instances stay legal profiles.
4. **Can one typed adapter cover both input modes?** Yes, compiled: one record,
   `ep_inputT` + `ep_input_procs`, no sum, no option, modes distinct through
   field values (probe_c/d).
5. **Smallest generic process-list builder?** `epp_saprocs` = dealer ::
   verifier :: seat players ++ input processes over the concrete `ep_players`,
   with identifiers `iota (pi_T').+3` — six record fields feed it; it equals
   both landed lists by conversion.
6. **Can termination and fuel be generic?** Fuel is a field, termination an
   obligation. For migrated instances it transports; for new instances it is
   `by vm_compute` on the concrete list (0.023-0.036 s measured), and CANNOT be
   generic: the enum path is vm-stuck (probe_g), and termination is a run fact,
   not a profile fact. The fuel-pinning discipline is mandatory (section 10 of
   the mutation ledger / P-C entry).
7. **Which trace extractors and equations are reusable?** Extraction, coalition
   assembly, endpoint equations: generic (one `Hep`). Raw-to-content leaves:
   per-instance, irreducibly (probe_e, section 9.3).
8. **What turns raw traces into trace distributions?** The four sample-adapter
   fields plus `fdistmap` — and a content readout first, since raw traces have
   no distribution layer (typed, probe_f).
9. **Exact-security hypotheses: adapter or theorem hypotheses?** Sample space,
   prior, arg/cut maps: adapter fields. `Hep`, `content_obs`, group-membership
   side conditions: theorem hypotheses. `sw_rho_dist` reaches the cut law only
   through `fdistmap pgg_rho` (probe_f).
10. **Finite-shuffle hypotheses?** Same split; the word space fits the same
    four fields (`sa_sampleT := bool * L.-tuple 'I_k`, `sa_cut := word_eval`);
    the landed word object is the image one level up, marginal identity proved,
    joint identity scoped to S5.
11. **Migrate without changing mathematical statements?** Yes (section 8):
    decoder equalities, conversion-level process equalities, verbatim
    transports.
12. **What paper claim becomes true?** Section 10, verbatim.

## 14. Completion criteria (request section 13)

1. Separate verdicts: sections 1 and 2. ✓
2. Both carriers compile with one worker: every probe, re-verified fresh. ✓
3. Count-mismatch mutation fails: probe_b_mutation (bridge refuted) and
   probe_h_mutation (decoder unstatable). ✓
4. No import cycle: section 6. ✓
5. Runs / trace functions / trace distributions distinguished: probe_f's three
   layers; the distinction is type-enforced. ✓
6. No permanent Rocq or paper source changed: `git status` clean on both
   throughout; probes and docs only. ✓
7. No probe contains `Axiom`, `Parameter`, `Abort`: swept per file (and none
   contains `Admitted` either). ✓
8. Positive-evidence miniatures end in `Qed` with assumptions checked: every
   cited lemma; boolp baseline only, verified per probe, with in-file
   `Print Assumptions` blocks in every probe after the audit fold. ✓
9. All additional data beyond `MonodromyProfile` named: section 1 register +
   section 4 fields + section 9 residue. ✓
10. Paper claim matches the compiled interface, not the intended design:
    section 10 claims execution and typed distribution layers only; the
    security-principle connection is explicitly excluded. ✓
