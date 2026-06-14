# PGG piSMC Trace Bridge — Design Spec

Date: 2026-06-14
Status: approved direction, pending spec review
Scope: `pgg-smc/` (protocol + four in-scope instances), reusing `dumas2017dual/dsdp/` as the template.

## 1. Goal

Make the shared PGG piSMC program **executable through the interpreter** and **derive protocol
correctness from the executed trace**, for all four in-scope instances (den Boer, Kim, S5, S5×S5),
mirroring DSDP's `interp_traces` → `dsdp_traces_ok` → `dsdp_is_correct`.

Today the PGG programs are only checked for session-type duality (`channels_dual` by `vm_compute`)
and never run; correctness lives in abstract reconstruction lemmas decoupled from the interpreter
(`exchange_verifier`'s own comment: reconstruction "happens outside piSMC"). This closes the
standing "piSMC trace bridge" gap so that the operational semantics become load-bearing for
correctness, exactly as in DSDP.

## 2. Non-goals (explicit)

- **No real cut / permutation is threaded.** The dealer's word stays the identity; correctness is
  word-independent (see §4), so a real permutation would prove nothing extra about correctness.
- **No privacy is derived from the trace.** Privacy is a distributional property over the random
  cut (`den_boer_input_private : cond_mutual_info … = 0`, `five_card_leakage`); a single trace
  cannot capture it. Privacy stays where it is.
- **No perm-value-to-number reduction.** Permutation application does not reduce under `vm_compute`
  (blocked by opaque finType/`reflect` proofs; confirmed by experiment). Trace endpoint values stay
  **symbolic** `rho w (start i)` expressions, exactly as DSDP's trace carries symbolic `enc`/`Emul`.
- **No `|W| > 1` multi-candidate hand**, and **no input encoding for position-model instances**
  (s5/s5x5 have `secretT = 'I_N`, no committed party inputs).

## 3. Background facts (established in repo)

- `pgg_recon_endpoints P := pgg_recon [tuple content (rho P (tnth starts i)) | i < T]`
  (`reconstruct/pgg_sharing_framework.v:284`). Word-independent: `pgg_recon_monodromy_correct`
  (`:293`) and `recon_from_layout_output` (`reconstruct/input_encoding.v:74`) prove it `= secret`
  for **every** `P ∈ pgg_G M`, including the identity.
- The verifier program collects exactly `[content (rho w (tnth starts i)) | i < T]` into its `Init`
  buffer (`protocol/card_exchange_pismc.v:247–256`). So the executed verifier buffer **is** the
  endpoint tuple consumed by `pgg_recon_endpoints`.
- `run_recover collected := ts_recon (rp_scheme plug) collected`
  (`protocol/pgg_monodromy_profile.v:90`) already reconstructs from a collected tuple.
- Input path: the `InputEncoding` record (`reconstruct/input_encoding.v:28`) carries
  `ie_assemble : inputT → layout`, `ie_output : inputT → secretT`, `ie_assemble_valid`, `ie_orbit`.
  It is **separate from** `MonodromyProfile` and is used only by heterogeneous-secret instances
  (den Boer, Kim; `secretT = bool`).
- DSDP template: `dsdp h := interp h dsdp_procs …`; `dsdp_traces := interp_traces 15 dsdp_procs`;
  `dsdp_traces_ok` (structure, via `interp_traces_ok`); `dsdp_is_correct` (closed by `ring`)
  (`dumas2017dual/dsdp/dsdp_correctness.v:145,169,186,201`).

## 4. Feasibility (settled by experiment, 2026-06-14)

Run against the idealized 2-player instance (N=3) through the real `erase_aprocs`/`run_interp`
pipeline:

- `interp`/`run_interp` **reduces the `ForList` dealer to termination**:
  `(run_interp 50 procs).1 = [:: Finish; Finish; Finish; Finish]` proven `by vm_compute`.
- The **trace structure is provable**: `map size (run_interp 50 procs).2 = [:: 1; 4; 2; 2]`
  `by vm_compute` (verifier collected its endpoints).
- **Perm application does NOT reduce** to a number: `nat_of_ord ((1%g) x)` stays a ~114 KB stuck
  term (opaque `reflect`/finType proofs). This is the user's anticipated risk, and it is real for
  *values*; it is why the codebase already carries nat-level `_natB` mirrors. It does **not** block
  the bridge, because (a) control flow reduces regardless of data, and (b) the DSDP pattern keeps
  values symbolic and closes correctness algebraically.

Conclusion: the trace bridge is feasible. `traces_ok` is stated with symbolic endpoints and proved
through control-flow reduction; correctness reads those symbolic endpoints via the word-independent
recon lemma. No perm value is ever forced to a number.

## 5. Architecture

### 5.1 Generic module `protocol/pgg_run.v` (NEW)

Generic over a profile, and (for input-encoded instances) an `InputEncoding`.

- `dealer_with_input_encoding (ie : InputEncoding plug inputT) (decode : seq 'I_N → inputT)
  players P_idx` — the generic input-derived-content dealer; the generalization of
  `den_boer_dealer_layout`. It threads `tnth (ie_assemble ie (decode committed))` as the content
  through `exchange_dealer_with_commit`. The `decode` reader (committed cards → `inputT`,
  currently `den_boer_decode`) is a parameter here; folding it into `InputEncoding` as a field is a
  candidate cleanup but out of scope for this spec. Position-model instances do not use this dealer;
  they use the existing fixed-`rp_content` `run_dealer`.
- `endpoints_of_trace (verifier_trace : seq data) : T.-tuple 'I_N` — reads the `T` `PGG_sheet`
  values out of the verifier's collected buffer (buffer order pinned against the experiment:
  player `T-1` pushed first).
- `recovers_of_endpoints` (generic bridge lemma):
  `endpoints_of_trace verifier_trace = [tuple content (rho P (tnth starts i)) | i < T] →`
  `pgg_recon (endpoints_of_trace verifier_trace) = secret`,
  proved by rewriting with the hypothesis and applying `pgg_recon_monodromy_correct` (at `P = 1`,
  or any `P ∈ pgg_G`).

### 5.2 Per-instance run files (thin), all four instances

For each instance `X ∈ {den_boer, kim, s5, s5x5}`:

- `X_procs : seq (proc data)` — `erase_aprocs` of the aproc list ordered by party id:
  `[dealer; verifier; player₀ … player_{T-1}; (input parties, for five-card)]`.
- `X_traces_ok : (run_interp h X_procs).2 = <expected trace>` — the verifier slice equals the
  symbolic tuple `[:: PGG_sheet (rho w (tnth starts i)) | …]`. Proof: control-flow reduction
  (`vm_compute`, both sides reduce to the same symbolic form) or `rewrite interp_traces_ok` then
  structural, mirroring `dsdp_traces_ok`.
- `X_recovers : pgg_recon (endpoints_of_trace (verifier_trace_of X_procs)) = X_secret` — rewrite via
  `X_traces_ok`, then apply `recovers_of_endpoints`. The DSDP `dsdp_is_correct` analog.

Instance specifics:

| Instance | secretT | dealer | input parties | secret |
|---|---|---|---|---|
| den Boer | `bool` | `dealer_with_input_encoding ie_db` | yes (2 bits) | `a && b` (`ie_output`) |
| Kim | `bool` | `dealer_with_input_encoding ie_kim` | yes | `ie_output` |
| S5 | `'I_5` | fixed-`rp_content` `run_dealer` | no | dealt position |
| S5×S5 | `'I_10` | fixed-`rp_content` `run_dealer` | no | dealt position |

### 5.3 Rename / relocation map

| Current (den-Boer-only / mis-named) | New (general) | Action |
|---|---|---|
| `den_boer_assemble := [:: 1%g]` (trivial WORD) | identity deck, inlined in `pgg_run.v` | DELETE the conflated name |
| `den_boer_dealer_layout` | `dealer_with_input_encoding` (generic) | generalize + relocate to `pgg_run.v`; den Boer instantiates |
| `den_boer_layout` (input→layout) | `den_boer_ie_assemble` (its `InputEncoding` fill) | rename for clarity; keep instance-specific content |
| `den_boer_decode` | `den_boer_ie_decode` | rename; instance-specific |
| `den_boer_dealer_committed`, `den_boer_dealer_layout_ap` | fold into the generic dealer + a per-instance `_ap` | relocate |
| — | `pgg_procs`, `endpoints_of_trace`, `recovers_of_endpoints` | NEW generic |
| — | `<inst>_procs`, `<inst>_traces_ok`, `<inst>_recovers` | NEW per instance |
| `den_boer_*_dual` (session duality) | keep per instance | unchanged |

The trivial-word `den_boer_assemble` is the only true deletion; the input→layout assembler keeps its
home in `InputEncoding` and is merely renamed for clarity, per the audit's recommendation.

## 6. Verification plan & risks

Build order (spike-first, de-risk the larger sizes early):

1. `protocol/pgg_run.v` — generic module; typecheck the signatures.
2. `instances/denboer1989/den_boer_run.v` — first concrete run (N=5, input-encoded). Spike
   `den_boer_traces_ok` to confirm the **commit-prologue** trace shape executes.
3. `instances/s5x5/…_run.v` — largest (N=10), position-model. Spike to confirm structure reduces at
   N=10.
4. `instances/kim2025/…_run.v`, `instances/s5/…_run.v` — fill remaining.

Risks:

- **R1 (structure reduction at N=10).** Control flow reduced cleanly at N=3; explicit player lists
  (not `enum`) keep the `sproc_iter`/`fold_senv` folds reducing. Mitigation: spike s5x5 early.
- **R2 (commit-prologue execution).** The input-party prologue is currently only duality-checked.
  Mitigation: spike its execution in the den Boer run before generalizing.
- **R3 (`endpoints_of_trace` order/off-by-one).** The verifier pushes player `T-1` first.
  Mitigation: pin `endpoints_of_trace` against the observed buffer order from the experiment.

Build discipline: `make -j1` per file (RAM safety). Perm values are never forced to numbers; all
`traces_ok` proofs keep endpoints symbolic.

## 7. Definition of done

- `protocol/pgg_run.v` compiles with the generic dealer, `endpoints_of_trace`, and
  `recovers_of_endpoints`.
- Each of the four instances has `<inst>_procs`, `<inst>_traces_ok`, `<inst>_recovers`, all `Qed`,
  standard axioms only.
- The conflated `den_boer_assemble := [:: 1%g]` is removed; the input→layout assembler lives in
  `InputEncoding` under a clear name.
- No statement of an existing correctness/privacy theorem is weakened; the new `X_recovers` is an
  *additional* operational guarantee, not a replacement.

## 8. Academic claims (reference)

Fact-checked 2026-06-14 against the codebase and the reference papers
(`~/Projects/aplas2024-poster/feb12ITP2026/feb12ITP2026.tex`,
`~/Projects/aplas2024-poster/forteApr22/forteApr22.tex`). Full audit and evidence table in the
companion `2026-06-14-pgg-piSMC-trace-bridge-academic-claims-review.md`. This section records what is
defensible to claim, all **verified true** unless marked otherwise.

### 8.1 Claims you CAN make (verified true)

- **Executable operational semantics.** The PGG piSMC protocols gain a concrete executable semantics
  via the pi-calculus interpreter; they are no longer abstract definitions or session-type-checked
  stubs only.
- **End-to-end operational correctness.** Correctness is derived from executed traces: the verifier's
  dynamically collected buffer matches the input of `pgg_recon_endpoints`
  (`pgg_sharing_framework.v:284`, verifier collection `card_exchange_pismc.v:247`), so the protocol
  computes the intended secret in practice.
- **Verification via symbolic execution.** Correctness is proved even though permutation application
  is computationally opaque/stuck under `vm_compute`; keeping endpoints symbolic proves control-flow
  and structural correctness algebraically (DSDP-style).
- **Generality of the trace bridge.** The `pgg_run.v` architecture uniformly covers heterogeneous
  instances (den Boer, Kim; `secretT = bool`) and position-model instances (S5, S5x5; `secretT = 'I_N`).

### 8.2 Claims you CANNOT make (verified false / out of scope)

- **Privacy from traces — FALSE for piSMC.** Unlike DSDP, this bridge does not lift traces to random
  variables. Privacy stays distributional over the abstract random cut
  (`den_boer_input_private : cond_mutual_info = 0`, `five_card_leakage.v`), decoupled from `interp`.
- **Active/malicious-adversary security — FALSE.** The interpreter models deterministic honest
  execution (`feb12ITP2026.tex:127` "honest parties"; VIEW is passive observation). No active
  deviation is modeled.
- **Modeling the real randomized cut — FALSE.** The dealer's word stays the identity; the trace
  proves only *word-independent* correctness (`pgg_recon_monodromy_correct` holds for all `P`).

### 8.3 Correction to "not deployment-runnable" (the one review imprecision)

The review marked "the interpreter yields a concretely executable program for deployment" as
SUSPICIOUS. The **conclusion is correct** — this work is verification-only and makes no deployment
claim — but the **stated reason is imprecise**: it conflates kernel `vm_compute` reduction with Coq
program **extraction**. `vm_compute` being stuck on a permutation application (blocked by opaque
finType/`reflect` proofs) does **not** imply the protocol cannot extract to runnable OCaml/Rust;
extraction erases opaque proofs, and a perm finfun extracts to a computable function. So: do not
claim a deployment-runnable artifact, but also do not claim it is *unextractable* on
`nat_of_ord`-stuck grounds. Whether extraction yields a runnable artifact is untested and out of
scope for this spec.

### 8.4 DSDP vs piSMC, the distinction to state in any paper (verified true)

DSDP's interpreter traces carry **both** correctness and privacy: `feb12ITP2026.tex:210` builds each
party's view from the collected traces and proves Peer-wise Perfect Privacy
(`H(X_i | View_j) = H(X_i)`, Def. at `feb12ITP2026.tex:1241–1252`), and `forteApr22.tex:61–177`
verifies traces for correctness **and** information leakage freedom. This piSMC bridge carries
**correctness only**; privacy is handled by a separate abstract layer (the random-cut lemmas).
