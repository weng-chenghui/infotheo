# DSDP SSProve simulator formalization — design memo

Date: 2026-07-14
Status: design approved in-session; all four de-risking probes completed and
passing. Next step: implementation plan (writing-plans), then execution.

## Objective

Mechanize the simulator notion and the game/simulator conversion for the DSDP
corrupted-Alice leg, as an SSProve extension (no Infotheo imports anywhere in
the new line), with the final theorems presented in `dsdp_main.v`. This
supports the thesis chapter `security-models.tex`:

| Thesis claim | Mechanized counterpart |
|---|---|
| Simulator `Sim : X_A x Y_A -> Dist(B_A)` (Def `def:smc:simulator`) | `dsdp_simulator_pkg` (package level) + its view law (distr level) |
| eps-privacy `Delta(view law, Sim law) <= eps` (Def `def:smc:epsilon-privacy`) | `dsdp_alice_view_statdist_le` |
| Game advantage bound (Eq `eq:smc:advantage`) | existing `AdvantageE` bounds (unchanged) |
| max advantage = statistical distance (Prop `prop:smc:max-advantage`) | `statdist_test_le` + `statdist_test_max` |
| perfect/eps privacy <=> all-distinguisher bound (§`sec:smc:relating`) | `Simulates_from_endpoint` / `Simulates_reduction` + headline derivations |

The chapter hedge at `security-models.tex:973-975` ("the factorization stays
on paper") becomes updatable after this lands (thesis edit is a separate
follow-up task).

## Decisions (fixed during brainstorming)

1. **Both levels, bridged**: package-level simulator (SSProve-native,
   compositional) plus distr-level statistical distance with the
   max-advantage identity; a bridge connects them.
2. **Corrupted Alice only**: the generic notion is party-agnostic; the DSDP
   instance targets the `leak_S` game pair. Relay simulators are future work.
3. **Approach A, factor-the-endpoint**: existing code is untouched; the
   all-zero endpoint is proven perfectly equivalent to `Sim ∘ Ideal`.
4. **No duplicated security line**: one proof line, extended by one node.
   The existing hop-ladder bound `dsdp_advantage_derived_leak_S` stays the
   axis engine; the simulation headline consumes it via `Advantage_triangle`
   plus the new factorization. No existing conclusion is re-proven; the
   leak_S real-vs-zero statement is never promoted to a headline.
5. **Naming**: SSProve upstream style for all new identifiers (precedent:
   `adv_equiv`, `Advantage_link`, `LosslessOp_*`), each chosen by
   grep-for-precedent; a blocking adversarial naming-audit agent pass runs
   before every commit.
6. **Proof style**: mathcomp/ssreflect per the mathcomp-skills guide
   (80-char lines, `by`/`exact:` closers, bullets, meaningful hypothesis
   names). Exception islands: vanilla `eapply` at `eq_rel_perf_ind`-family
   entry points (ssreflect `apply:` delta-unfolds raw_package bodies and
   OOMs). These sites are listed below and known to the style auditor.

## Architecture

```
smc/ssprove_ext_simulator.v      generic package-level simulation security
smc/ssprove_ext_statdist.v       generic distr-level statistical distance
dumas2017dual/dsdp/simulation/dsdp_simulator.v   DSDP axis: ideal + sim +
                                                 factorization + view law
dumas2017dual/dsdp/dsdp_main.v   headlines (cloned context, full bodies)
```

Probe files (kept, uncommitted, never imported; content is promoted by
copying, per the no-scratch-imports rule):

- `dumas2017dual/dsdp/simulation/probe_p2_zero_slot_reads.v` (P2)
- `dumas2017dual/dsdp/simulation/probe_p3_statdist.v` (P3)
- `dumas2017dual/dsdp/simulation/probe_p5_skeletons.v` (P5)
- `dumas2017dual/dsdp/simulation/probe_p1_factorization_pet.v` (P1)

Compile command for out-of-_CoqProject files (from repo root):

```
rocq c -R . infotheo -w -notation-overridden -w -ambiguous-paths \
  -w -notation-incompatible-format <file.v>
```

The three permanent files enter `_CoqProject` + make when implemented.

## Layer 1 — generic package level (`smc/ssprove_ext_simulator.v`)

Validated by probe P5 (all statements type-check; conversion lemmas already
Qed in the probe).

- `adv_sim_le (E : Interface) (adm : Locations -> raw_package -> Prop)
  (Real Ideal Sim : raw_package) (eps : R) : Prop :=
  forall LA A, ValidPackage LA E A_export A -> adm LA A ->
  AdvantageE Real (Sim ∘ Ideal) A <= eps.`
  The class `adm` is the thesis' restricted distinguisher class `Delta_T`.
- `Simulates_from_endpoint` (game -> simulator): from the endpoint bound
  (forall admissible A, `AdvantageE Real End A <= eps`) and the perfect
  factorization stated as `forall admissible A, AdvantageE End (Sim ∘ Ideal)
  A = 0`, conclude `adv_sim_le`. Engine: `Advantage_triangle` + `addr0`.
  Statement-shape note (P5): the factorization hypothesis is phrased as the
  class-restricted advantage equality, NOT upstream `≈₀`/`adv_equiv`, because
  `adv_equiv` quantifies over all adversaries and cannot carry `adm`.
- `Simulates_reduction` (simulator -> game): `adv_sim_le ... eps ->`
  post-processed comparisons `AdvantageE (T ∘ Real) (T ∘ Sim ∘ Ideal) A
  <= eps`, for classes closed under `A ∘ T` (hypothesis). Engine:
  `rewrite -Advantage_link`; no `link_assoc` needed (`∘` right-associates).

## Layer 2 — generic distr level (`smc/ssprove_ext_statdist.v`)

Validated by probe P3 (all lemmas Qed standalone, standard boolp axioms
only, 303 lines; promotion effort: low).

- `statdist p q := psum (fun t => `|p t - q t|) / 2%:R` over
  `{distr T / R}`, generic `realType`.
- `statdist_ge0`, `statdist_sym`, `statdist_triangle`.
- Acceptance probability: mathcomp-analysis `distr.pr`
  (`pr mu E = psum (fun x => (E x)%:R * mu x)`, notation `\P_[mu] E`).
- `statdist_test_le : psum p = 1 -> psum q = 1 ->
  `|pr p D - pr q D| <= statdist p q`.
  MASS-1 IS REQUIRED: the inequality is false for general subdistributions
  (counterexample in probe). Both view laws are lossless in our use, per the
  existing `LosslessCode` discipline (`ssprove_ext_lossless.v`).
- `statdist_test_max : psum p = 1 -> psum q = 1 ->
  pr p (fun t => q t < p t) - pr q (fun t => q t < p t) = statdist p q`.
  Strongest form: strict optimal test, plain difference, exact attainment.
- Together these mechanize Prop `prop:smc:max-advantage`; no sup-over-tests
  machinery is needed because the optimal test is explicit.
- realsum API notes (from P3, reusable): `psum` is unsigned (sup of finite
  abs-sums); combine via `psumID` + `psumD`, never signed linearity; a
  1-line `psum_split` helper from `psumD` + `eq_psum`; `(D t)%:R` needs a
  named `pred T` to dodge the `%:R` nat-scope trap; `Import GRing.Theory`;
  `ltrgtP`-then-`lra` discharges pointwise boolean-coefficient goals.

## DSDP instantiation (`dumas2017dual/dsdp/simulation/dsdp_simulator.v`)

Grounded in machine-checked P2 facts and P5 skeletons.

P2 facts (all proved by `vm_compute` Examples in the P2 probe):

- All-zero code shape: 4x `GC_sample card_msg` (v2, v3, r2, r3);
  2x `GC_sample card_renc` (ra1, ra2); `GC_put V_2_cell v2`; two
  `GC_enc_hop _ (HE_const 0)` with inline randomness; two `GC_let`
  combines `a_i = (c_i ^ u_i) * Enc(pk_i, r_i, ra_i)`;
  `GC_put_output Sout_cell (u2 v2 + u3 v3 + u1 v1)`;
  `GC_ret [a1; a2; c2; c3]`.
- View provenance: the ciphers view reads seed slots {u2, u3} only, plus
  fresh samples. v2/v3 provably absent from the zero view; provably present
  in the all_real view (the IND-CPA hops are exactly what erases them).
- V2 reaches only `V_2_cell` (read by `id_v2_get`); S only `Sout_cell`
  (read by `id_Sout_get`); puts never reach `GC_ret`.
- `game_iface_leak_S` ops: `id_game_run = (0, 'unit -> chList t_cipher)`,
  `id_v2_get = (2, 'unit -> t_msg)`, `id_Sout_get = (3, 'unit -> t_msg)`.

Components:

- `I_dsdp_ideal` interface: `id_ideal_run = (4, 'unit -> 'unit)` (ident 4:
  0/1/2/3 are taken; 1 is `id_guess` in the guessing layer, so the P2-probe
  suggestion of 1 is superseded), plus the existing `id_v2_get`,
  `id_Sout_get` signatures.
- `dsdp_ideal_pkg` (locations `protocol_state t_msg`): `id_ideal_run`
  samples v2, v3 (uniform card_msg), computes S mirroring the real
  `put_output` expression from the seed weights (`as_plain (de_val_nth
  seed k)`), writes both cells, returns tt. `id_v2_get`/`id_Sout_get` read
  the cells. This is the trusted third party: it holds the honest inputs
  and computes f; `id_Sout_get` is the allowed information a(x); the
  challenge oracle `id_v2_get` is experiment-harness plumbing present in
  both worlds, not part of the view.
- `dsdp_simulator_pkg` (imports `I_dsdp_ideal`, exports `game_iface_leak_S`,
  empty own locations): `id_game_run` calls `id_ideal_run`, samples r2, r3,
  ra1, ra2 and the two hop randomnesses, builds `c_i = Enc(pk_i, 0, _)` and
  the combines `a_i`, returns `[a1; a2; c2; c3]`. Pass-through oracles end
  in `x <- call tt ;; ret x` (P5: bare `call` tails break `pack_valid`
  resolution). Parameter honesty: the simulator's free parameters are
  Alice's data only (u2, u3 seed slots, public keys); v2/v3 never appear in
  its code. The allowed-info-only property is witnessed syntactically.
- Factorization (the axis workhorse): forall admissible A,
  `AdvantageE (zero_game_leak_S ...) (dsdp_simulator_pkg ∘ dsdp_ideal_pkg)
  A = 0`. Proof route validated by P1 (see risk table).
- View law + bridge (P4, pattern already exercised): `view_dump_challenger`
  calls `id_game_run` then `id_Sout_get`, returns the pair;
  `view_law G := Pr_fst (resolve (view_dump_challenger ∘ G) view_op tt)`.
  Resolution lemma `view_dump_resolve_eq` (statement type-checked in P5)
  chains upstream `Pr_Pr_fst` + repo `Pr_fst_map` (`dsdp_convert.v`) +
  `distr.pr_dmargin`, cloning the `guess_resolve_eq` proof pattern from
  `dsdp_guess_fiber.v`. Losslessness of the composed view code via
  `LosslessOp_bind` (`ssprove_ext_lossless.v`) + upstream uniform
  instances.

## Headlines in `dsdp_main.v`

Both in the cloned `dsdp_alice_guess`-style section context, full
multi-step proof bodies consuming axis results (same status as
`dsdp_alice_guess_real_le`); the factorization's heavy proof stays in the
axis file. Header comment gains a "Simulation-based security (simulation
axis)" block naming the engine lemmas.

1. `dsdp_alice_simulation_secure`: forall admissible A,
   `AdvantageE (real_game_leak_S ...) (dsdp_simulator_pkg ∘ dsdp_ideal_pkg)
   A <= 2%:R * epsilon_cpa`.
   Body: `Simulates_from_endpoint` instantiated with
   `dsdp_advantage_derived_leak_S` + the factorization. (P5 verified the
   instantiation fits, including `fseparate` bookkeeping: sim locations are
   empty, so the link's location set reduces to `protocol_state`.)
2. `dsdp_alice_view_statdist_le`: under the lossless hypotheses,
   `statdist (view_law real_game) (view_law (sim ∘ ideal))
   <= 2%:R * epsilon_cpa`.
   Body: `statdist_test_max` gives the optimal test D*; `test_adversary D*`
   is one admissible adversary of headline 1; `view_dump_resolve_eq`
   converts its advantage to the test gap.

Conversion visibility: game -> simulator is headline 1's derivation;
simulator -> game is `Simulates_reduction` (generic) and headline 2
(every test bounded, distance form).

## Probe results summary

| Probe | Question | Result |
|---|---|---|
| P2 | Zero-endpoint view reads allowed info only? | YES, machine-checked; view reads {u2,u3}+fresh only; v2/v3 absent (present in all_real) |
| P1 | PET cost of the factorization proof | VIABLE: entry ms; `simplify_eq_rel` ~125 s / ~6 GB (T1); guard-rewrite collapses goal 195 MB -> 1.4 MB; sync/swap fire |
| P3 | statdist optimal-test lemma provable on realsum? | YES, all Qed standalone; mass-1 required for BOTH lemmas; effort low |
| P5 | Skeletons/interfaces/class-fit type-check? | YES; conversion lemmas already Qed; two Admitted = exactly the planned work |

## Proof-engineering rules for the factorization (from P1)

- Write the composition inline (`sim ∘ ideal`); an opaque `Definition`
  wrapper breaks `ValidPackage` instance resolution at entry.
- Vanilla `eapply eq_rel_perf_ind_eq`, then `simplify_eq_rel m`
  (budget ~2 min / ~6 GB per direction; acceptable, once per proof).
- Immediately reduce the stuck cardinality guards on each run-oracle goal:
  `rewrite eqxx` and `rewrite (negbTE card_renc_neq)` (the section already
  carries `card_renc_neq`), BEFORE any sync/swap.
- `ssprove_sync_eq` for the v2/v3 samples; `ssprove_swap_rhs`/
  `ssprove_swap_lhs` to commute the ideal's early cell writes past the
  simulator's mask/randomness samples (swap inventory: 2 puts x 4-6
  samples, all fired in probe).
- Fallback (validated as unnecessary, kept for safety): prove the
  run-oracle equivalence as a separate lemma with `denote_run` kept
  symbolic, `hop_equiv_*_leak_S` style.
- Monitor rocqworker RSS; kill the process group on runaway, not the
  launcher.

## Task breakdown (atomic; each verified via rocq_check/compile + committed)

1. `smc/ssprove_ext_statdist.v` — promote P3 content; add to `_CoqProject`.
2. `smc/ssprove_ext_simulator.v` — promote P5 Part A; generic conversion
   lemmas proven (already Qed in probe).
3. `dsdp_simulator.v` part 1 — interfaces + ideal + simulator packages
   (promote P5 Part B skeleton with real bodies per P2 facts).
4. `dsdp_simulator.v` part 2 — the factorization proof (P1 recipe).
5. `dsdp_simulator.v` part 3 — view law, resolution lemma, losslessness.
6. `dsdp_main.v` — two headlines + header block.
7. Follow-up (separate): thesis chapter hedge update; probe-file cleanup
   decision (keep as-is for now).

## Gates (every commit, in order)

1. mathcomp-style-auditor on new/touched `.v` files (+ `audit-quick.sh`).
2. Adversarial SSProve naming audit over all new identifiers.
3. rocq-auditor Stage-2 (mandatory precommit).
4. Crypto-vacuity statement check of the headlines against
   Eq `eq:smc:simulation` and Prop `prop:smc:max-advantage`
   (English-statement match, variable tracing, parallel-track test).

## Out of scope

Relay-party (Bob/Charlie) simulators; the record-based non-leak_S game
pair; thesis `.tex` edits; UC/composition beyond this protocol.
