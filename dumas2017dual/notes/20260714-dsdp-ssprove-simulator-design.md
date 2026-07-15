# DSDP SSProve simulator formalization — design memo

Date: 2026-07-14
Status: IMPLEMENTED (2026-07-15). The design below was approved in-session and
de-risked by five probes (P1, P2, P3, P5, P6); it was then executed in full and
both headlines are Qed in `dsdp_main.v`. Landed across seven commits: 2bbc1714
(smc statdist), bea78b5f (smc simulator), b10187b5 (smc lossless_heap),
cc6863fa (ideal/simulator packages), b0dedbac (zero-game factorization),
beb898a4 (security, view law, mass-1 discharge), eef925e5 (dsdp_main headlines).
The adversarial design audit's B1 (statement scope), M1 (mass-1 discharge), M2
(allowed-info witness), M3 (P1 validation scope) findings were resolved by the
re-scopings and decisions marked "audit" in this revision. User decisions locked
(2026-07-14): statement scope = average-case (B1 option i); mass-1 = P6 graceful
degradation (see M1 block); sim_view_body witness adopted; probe files kept
uncommitted. See the Implementation outcome section at the end for what deviated
from the plan sketch.

## Objective

Mechanize the simulator notion and the game/simulator conversion for the DSDP
corrupted-Alice leg, as an SSProve extension (no Infotheo imports anywhere in
the new line), with the final theorems presented in `dsdp_main.v`. This
supports the thesis chapter `security-models.tex`:

| Thesis claim | Mechanized counterpart |
|---|---|
| Simulator `Sim : X_A x Y_A -> Dist(B_A)` (Def `def:smc:simulator`) | `dsdp_simulator_pkg` (package level) + its view law (distr level) |
| eps-privacy `Delta(view law, Sim law) <= eps` (Def `def:smc:epsilon-privacy`) | `dsdp_alice_view_statdist_le` — AVERAGE-CASE analogue, see scope note |
| Game advantage bound (Eq `eq:smc:advantage`) | existing `AdvantageE` bounds (unchanged) |
| max advantage = statistical distance (Prop `prop:smc:max-advantage`) | `statdist_test_le` + `statdist_test_max` (mass-1 laws over a choiceType, generalizing the thesis' finite `Dist(B_A)`) |
| perfect/eps privacy <=> all-distinguisher bound (§`sec:smc:relating`) | `Simulates_from_endpoint` / `Simulates_reduction` + headline derivations |

STATEMENT SCOPE (adversarial-audit finding B1, resolved by re-scoping).
The thesis' eps-privacy quantifies per input x over ALL parties' inputs
(`def:smc:epsilon-privacy`: "for every input x"; the test advantage
`eq:smc:test-advantage` takes max over x). The mechanized headlines fix
Alice's inputs (the seed slots u1, u2, u3, v1) but the honest inputs v2, v3
are SAMPLED IN-GAME, uniformly. Both headlines therefore bound the distance
between mixture laws averaged over uniform (v2, v3) at each fixed corrupted
input — by joint convexity a strictly weaker statement than the thesis'
per-x bound, which they do not imply. Exposing v2 through `id_v2_get`
(headline 1's adversaries may call it) upgrades this to the average over v2
of conditional distances, never the max; v3 is not exposed at all. The
mechanized claims are therefore: average-case eps-privacy at fixed corrupted
input, honest inputs uniform. The thesis follow-up must present them as
such. A per-v2 corollary is recoverable via v2-indicator tests at cost
factor card_msg (bound m * 2 * epsilon_cpa) — recorded as optional future
work, not planned. Fixed-honest-input game variants would require
re-deriving the whole hop ladder and are ruled out by decision 3.

The chapter hedge at `security-models.tex:973-975` ("the factorization stays
on paper") becomes updatable after this lands (thesis edit is a separate
follow-up task, worded per the scope note above). One more honesty note for
that follow-up (audit m5): headline 2's test space `chList t_cipher * t_msg`
is the (received-ciphers, leaked-S) MARGINAL of the thesis view B_A at fixed
corrupted input; B_A also contains x_A and the corrupted party's own
randomness, and `def:smc:simulator`'s extraction condition only holds in the
per-x_A sliced reading.

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
- `dumas2017dual/dsdp/simulation/probe_p6_lossless_heap.v` (P6)

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
  Bridge from an rhl `≈₀` proof to this hypothesis: trivial restriction —
  `dsdp_adm`'s protocol_state conjunct implies `adv_equiv`'s two `fseparate`
  side conditions (sim locations empty, zero_game locations =
  protocol_state); P5 closed both obligations with the class conjunct
  (audit confirmed-sound #4).
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
  (counterexample: p = dunit a, q = dnull gives gap 1 > 1/2 = statdist; the
  probe established the necessity, and the promoted file adds this
  counterexample as an Example — audit m1).
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

P2 facts (all machine-checked as conversion-proof `by []` Examples in the
P2 probe):

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

- `I_dsdp_ideal` interface: `id_ideal_run = (4, 'unit -> 'unit)`, plus the
  existing `id_v2_get`, `id_Sout_get` signatures. Ident note (audit m2):
  ident 1 is `id_guess` in the guesser's EXPORT space and would not
  actually collide here (the ideal's export is consumed by the simulator);
  4 is a safe stylistic choice avoiding any ident reuse, not a necessity.
  P1's probe used a probe-local ident 1.
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
  resolution).
- ALLOWED-INFO WITNESS (audit M2): the package type alone does NOT witness
  allowed-info-only, since `I_dsdp_ideal` includes `id_v2_get` (needed for
  the pass-through re-export) and nothing in the type stops `id_game_run`
  from calling it. Fix adopted: the view-synthesis body is a standalone
  Gallina function abstracted over ONLY the allowed-info oracles,
  `sim_view_body (run_ideal : raw_code 'unit) (get_S : raw_code t_msg) :
  raw_code (chList t_cipher)` (no v2 continuation in its type), and the
  package's `id_game_run` is `sim_view_body (call id_ideal_run tt)
  (call id_Sout_get tt)`. The Gallina type of `sim_view_body` is the
  type-level witness that the fabricated view uses only allowed
  information, matching the thesis' `Sim : X_A x Y_A -> Dist(B_A)` reading.
  P6-CONFIRMED FEASIBLE (Part B, Qed): `sim_view_body : raw_code 'unit ->
  raw_code t_msg -> raw_code (cipher_list t_cipher)` and the package
  ValidPackage-check both work, with two required idioms: (1) a
  `valid_sim_view_body` lemma + `#[local] Hint Extern 2 (ValidCode _ _
  (sim_view_body _ _)) ... : typeclass_instances ssprove_valid_db`, because
  the resolver cannot descend an opaque helper head (`#[export]` is illegal
  on a Hint inside a Section); (2) call arguments in bind-wrapped form
  `x <- c tt ;; ret x`, since a bare `c tt` leaves a beta-redex that
  `valid_opr`'s syntactic hint cannot match.
  (Alternative considered: splitting the package into an allowed-info core
  `par` a v2-forwarder — stronger package-level witness but complicates the
  factorization proof and diverges from P1's timed shape; not adopted.)
  Parameter honesty stands: the simulator's free parameters are Alice's
  data only (u2, u3 seed slots, public keys); v2/v3 never appear.
- Factorization (the axis workhorse): forall admissible A,
  `AdvantageE (zero_game_leak_S ...) (dsdp_simulator_pkg ∘ dsdp_ideal_pkg)
  A = 0`. Proof route validated by P1 (see risk table).
- View law + bridge (pattern already exercised in P5 Part C plus the
  `guess_resolve_eq` precedent; the "P4" label from the probe planning was
  folded into P5): `view_dump_challenger`
  calls `id_game_run` then `id_Sout_get`, returns the pair;
  `view_law G := Pr_fst (resolve (view_dump_challenger ∘ G) view_op tt)`.
  Resolution lemma `view_dump_resolve_eq` (statement type-checked in P5)
  chains upstream `Pr_Pr_fst` + repo `Pr_fst_map` (`dsdp_convert.v`) +
  `distr.pr_dmargin`, cloning the `guess_resolve_eq` proof pattern from
  `dsdp_guess_fiber.v`.
- MASS-1 DISCHARGE DECISION (audit M1, resolved by probe P6): the resolved
  view code contains `#put`/`get`, placing it OUTSIDE the `LosslessOp_bind`
  closure (`ValidCode emptym [interface]` prefix requirement; documented at
  `dsdp_guess_fiber.v:203-210`, where `guess_lossless` is a Hypothesis).
  P6 built the missing machinery and it is PROVEN (11 Qed, 0 Admitted):
  `LosslessHeapCode c := forall h, psum (distr.mu (Pr_code c h)) = 1`
  (JOINT mass, chosen because every upstream `Pr_code_*` equation is stated
  at the joint level), instances ret/sample/get/put/bind/if with NO
  `ValidCode emptym` restriction, the `Pr_fst` bridge, and — the
  load-bearing piece — `denote_run_lossless_heap` by induction on the
  game_code AST (hypotheses: `gc_sample_cards gc`, `card_msg`/`card_renc`
  positivity, `card_renc_neq`), which discharges the stateful game core
  WITHOUT materialising the 100-MB resolved term. One mechanical step
  remains open for full `view_zero_mass1`: a structural reduction lemma for
  `gc_sample_cards` on the concrete `all_zero (game_of_trace_seeded ...)`
  with abstract cardinalities (`vm_compute` cannot fire on abstract-nat
  guards; needs `cbn` + per-sample `eqxx`). PLAN (graceful degradation):
  task 5 promotes the P6 infrastructure and attempts that reduction lemma
  with bounded effort; if it lands, headline 2 is unconditional; if not,
  headline 2 carries mass-1 hypotheses citing `denote_run_lossless_heap`
  (the `guess_lossless` precedent, with the hypotheses' truth now
  machine-supported for the core). Axiom note (P6, checked via Print
  Assumptions): the class depends on the boolp trio plus mathcomp-analysis'
  admitted `interchange_psum` — the SAME dependency upstream
  `Lossless_sample` and the `Pr`/`AdvantageE` stack already carry; no new
  axiom enters. Prop `prop:smc:max-advantage`'s mechanization is
  unconditional (Layer 2).

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
| P2 | Zero-endpoint view reads allowed info only? | YES, machine-checked (conversion-proof `by []` Examples); view reads {u2,u3}+fresh only; v2/v3 absent (present in all_real) |
| P1 | PET cost of the factorization proof | ENTRY + EARLY ALIGNMENT VIABLE: entry ms; `simplify_eq_rel` 124.9 s / ~5.6-5.9 GB on T1 (first goal 97.7 MB); on T0 (zero-vs-zero) 240 s / 11.6 GB with `rewrite eqxx` collapsing 195 MB -> 1.36 MB; 2 syncs + 3 swaps fired. TAIL UNVALIDATED (see proof-engineering rules) |
| P3 | statdist optimal-test lemma provable on realsum? | YES, all Qed standalone; mass-1 required for BOTH lemmas; effort low |
| P5 | Skeletons/interfaces/class-fit type-check? | YES; conversion lemmas already Qed; two Admitted = exactly the planned work |
| P6 | Mass-1 provable outright? sim_view_body feasible? | Class + all instances + `denote_run_lossless_heap` Qed (AST induction, no giant term); one open reduction lemma (`gc_sample_cards` concrete); sim_view_body + package Qed with two documented idioms |

## Proof-engineering rules for the factorization (from P1)

- Write the composition inline (`sim ∘ ideal`); an opaque `Definition`
  wrapper breaks `ValidPackage` instance resolution at entry.
- Vanilla `eapply eq_rel_perf_ind_eq`, then `simplify_eq_rel m`
  (budget ~2 min / ~6 GB per direction; acceptable, once per proof).
- Immediately reduce the stuck cardinality guards on each run-oracle goal:
  `rewrite eqxx` and `rewrite (negbTE card_renc_neq)` (the section already
  carries `card_renc_neq`), BEFORE any sync/swap. Note (audit M3): the
  `card_renc` guard reduction was NOT exercised in P1 (the probe section
  omitted `card_renc_neq`); only `rewrite eqxx` was measured.
- `ssprove_sync_eq` for the v2/v3 samples; `ssprove_swap_rhs`/
  `ssprove_swap_lhs` to commute the ideal's early cell writes past the
  simulator's mask/randomness samples. P1 fired 2 syncs + 3 swaps of the
  estimated 2-puts x 4-6-samples inventory; the remaining swaps, the renc
  sample syncs, the Sout heap-term equality (the denoted term re-embeds the
  whole denotation env at every `de_val_nth` read, vs the ideal's
  hand-written `u2*v2 + u3*v3 + u1*v1`), the closing `r_ret`, and the two
  get-oracle goals are UNVALIDATED — the tail is where ~100 MB goals get
  manipulated (audit M3).
- Fallback (LIVE, not retired): prove the run-oracle equivalence as a
  separate lemma with `denote_run` kept symbolic, `hop_equiv_*_leak_S`
  style. Escalate to it if the Sout-term equality or the tail swaps stall.
- Probe-package divergences that do not transfer: P1's ideal used ident 1
  (plan uses 4; immaterial to PET cost) and its packages diverge from the
  real denotation as listed in the P1 report (regrouped sampling, early
  cell writes — the intentional swap challenge).
- Monitor rocqworker RSS; kill the process group on runaway, not the
  launcher.

## Task breakdown (atomic; each verified via rocq_check/compile + committed)

1. `smc/ssprove_ext_statdist.v` — promote P3 content + the dnull
   counterexample Example (audit m1); add to `_CoqProject`.
2. `smc/ssprove_ext_simulator.v` — promote P5 Part A; generic conversion
   lemmas proven (already Qed in probe).
3. `dsdp_simulator.v` part 1 — interfaces + ideal + simulator packages
   (promote P5 Part B skeleton with real bodies per P2 facts), with the
   `sim_view_body` allowed-info abstraction (audit M2).
4. `dsdp_simulator.v` part 2 — the factorization proof (P1 recipe).
   LARGEST-RISK TASK: the tail is unvalidated (audit M3); escalate to the
   symbolic-`denote_run` fallback lemma if the Sout-term equality or tail
   swaps stall.
5. `dsdp_simulator.v` part 3 — view law, resolution lemma, mass-1 per the
   M1 decision: promote P6's `LosslessHeapCode` infrastructure (likely
   into `smc/ssprove_ext_lossless.v` or a sibling) + attempt the
   `gc_sample_cards` concrete-reduction lemma with bounded effort;
   unconditional headline 2 if it lands, else mass-1 hypotheses citing
   `denote_run_lossless_heap`.
6. `dsdp_main.v` — two headlines + header block, statements worded per the
   B1 scope note (average-case, honest inputs uniform).
7. Follow-up (separate): thesis chapter hedge update worded per the B1
   scope note and the m5 marginal note; probe-file cleanup decision (keep
   as-is for now).

## Gates (every commit, in order)

1. mathcomp-style-auditor on new/touched `.v` files (+ `audit-quick.sh`).
2. Adversarial SSProve naming audit over all new identifiers.
3. rocq-auditor Stage-2 (mandatory precommit).
4. Crypto-vacuity statement check of the headlines against
   Eq `eq:smc:simulation` and Prop `prop:smc:max-advantage`
   (English-statement match, variable tracing, parallel-track test).
   Match criterion per the B1 scope note: the headlines are the
   AVERAGE-CASE analogues (honest inputs uniform, fixed corrupted input);
   a checker demanding the thesis' per-x statement must flag the wording,
   not the design. Vacuity anchors already established by the adversarial
   audit: `dsdp_adm` is inhabited (empty-locations test adversaries;
   `guess_reduction`), and the factorization is falsifiable (a wrong
   simulator, e.g. returning `[::]`, is distinguished with advantage 1 by
   a view-length test in the class).

## Out of scope

Relay-party (Bob/Charlie) simulators; the record-based non-leak_S game
pair; thesis `.tex` edits; UC/composition beyond this protocol.

## Implementation outcome (2026-07-15)

Both headlines are Qed in `dsdp_main.v`, average-case scope as designed:
`dsdp_alice_simulation_secure` (`AdvantageE real (Sim ∘ Ideal) <= 2 * epsilon_cpa`)
and `dsdp_alice_view_statdist_le` (statistical distance `<= 2 * epsilon_cpa`).
The axiom footprint of both is the SSProve library baseline plus `epsilon_cpa`
and `enc_ind_cpa_real_or_zero`, no custom axioms beyond that crypto assumption.

Headline 2 is UNCONDITIONAL. The M1 graceful-degradation fallback (the mass-1
hypotheses) was not needed. `view_real_mass1` and `view_simulated_mass1` are
proven outright via the heap-parametric lossless class, so the statistical
distance bound carries no side condition.

The factorization (`dsdp_simulator_factorization`, epsilon-free) closed on the
DIRECT rhl route. The P1 fallback was not consumed.

Deviations from the plan sketch, recorded:
- `sim_view_body` dropped its unused `get_S` parameter. It takes one parameter,
  runs `run_ideal` only, and the fabricated view provably reads no S.
- Headline 1 inlines the triangle derivation. It does not call
  `adv_sim_le_from_endpoint`, so `dsdp_main.v` does not import
  `smc.ssprove_ext_simulator`. The generic layer stays load-bearing through the
  axis file's `dsdp_adv_sim_le`.
- The ideal's `Sout` operand order matches the denotation's `dsdp_output` order
  (`u1 * v1 + u2 * v2 + u3 * v3`), which spares a ring step.
- View-layer and mass-1 names finalized as `view_pair_challenger`,
  `view_resolved`, `view_resolve_eq`, `sample_cards_msg_renc`, and
  `view_{zero,real,simulated}_mass1`.

Probe files stay uncommitted under
`dumas2017dual/dsdp/simulation/probe_p{1,2,3,5,6}_*.v` (decision 4).

Full-project build check: `make -f Makefile.coq dumas2017dual/dsdp/dsdp_main.vo`
rebuilds the four new files and `dsdp_main.vo` in `_CoqProject` dependency order,
against compiled `.vo` for every upstream dependency, and completes with exit 0.
