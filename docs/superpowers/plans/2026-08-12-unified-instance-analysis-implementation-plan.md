# Implementation plan: unified analysis pipelines (S5, S5xS5, Abelian, repo contract)

Request: `docs/superpowers/requests/2026-08-12-unified-instance-analysis-ROCQ-formalization-request.md`
Response (in progress): `...-response.md` (Phase 0 record).
Probes: `docs/superpowers/probes/2026-08-12-unified-instance-analysis/` — the
plan quotes probe code; the probe files are the verbatim source for every
statement below. Baseline `5453b93b`.

Verdicts feeding this plan: S5 probes GO, S5xS5 probes GO, Abelian probes GO,
facade-graph probe GREEN, soundness audit GO, naming audit GO. Phase 0 is
complete; every task below quotes compiled probe code.

Cross-cutting gotcha (Abelian probe finding, applies to every phase):
`SampleAdapter` is a primitive-projection record — `sa_cut u` never
`sa_cut sa u`, while `sa_sampleT`/`sa_sampleP` take the record explicitly.

Global decisions (from the two audits, all with reasons):

- D1. Module names: `S5Analysis` / `S5x5Analysis` / `AbelianAnalysis` in
  `s5_analysis.v` / `s5x5_analysis.v` / `abelian_analysis.v` (CamelCase +
  Analysis precedent; `s5x5` is the identifier family).
- D2. Facade alias names: deterministic path uses pgl27-parity names
  (`exec_plug`, `observed`, `exec_correct`, `exec_recovers`); randomized path
  prefixed `rand_`; S5x5 observers pile-tagged (`pile1_*`, `pile2_*`,
  `joint_*`). Reason: uniform navigation without erasing path identity.
- D3. Typed vocabulary in NEW `pgg-smc/manifest/pgg_analysis_status.v`, no pgg
  imports, `_CoqProject` after `pgg_observed_execution.v` (line 141); facades
  Require Export it. Reason: facades must expose typed aliases; placing it in
  the manifest would cycle.
- D4. `AssumptionStatus` carries a dedicated axiom-name enum (no string
  imports in facades):
  `Inductive PggAxiom := AxRayleighQ2R | AxS5GroupOrder | AxS5x5GroupOrder.`
  `Inductive AssumptionStatus := KernelClosed | AcceptsAxioms of seq PggAxiom.`
  Reason: the only accepted assumptions in scope are these three; a closed
  enum keeps rows checkable and I001-clean.
- D5. Import discipline: no production file Imports two `*_trace` modules;
  `content_of` and `s5_players` written qualified wherever more than one
  instance cone is loaded.
- D6. `var_dist_fdistmap_inj` is RELOCATED from `s5x5_mixing.v:329` to
  `pgg-smc/security/pgg_collusion_bound.v` (next to `var_dist_triangle`),
  statement unchanged; `s5x5_mixing.v` keeps using it via its existing import.
  Reason: Abelian needs it and must not import s5x5_mixing; one name, one
  definition (adding a same-named copy would shadow inside s5x5_mixing).
- D7. Manifest rows become typed witness records (design below), theorem
  aliases stay in the `Timeout 60 Check` checker. Prose level
  `Security-bridged` migrates to typed `AnalysisBridged`.
- D8. Fuel and player lists: reuse landed constants (S5: 150, S5xS5: 300,
  concrete ordinal lists as reduction caches, each with its `@intent` comment
  per request §11).

Typed vocabulary (T0, exact source):

```coq
Inductive CompletionLevel : Set :=
  | Algebraic | Executable | Observed | Sampled | AnalysisBridged.
Inductive TransferStatus : Set :=
  | NoModelComparison | StaticExecutedOnly | IdealFinite | NegativeTransfer.
Inductive PggAxiom : Set :=
  | AxRayleighQ2R      (* s5_rayleigh_Q2_R, trusted analytical certificate *)
  | AxS5GroupOrder     (* s5_group_order_eq *)
  | AxS5x5GroupOrder.  (* s5x5_group_order_eq *)
Inductive AssumptionStatus : Set :=
  | KernelClosed | AcceptsAxioms of seq PggAxiom.
```

Manifest row record (T4.1, in `pgg_analysis_manifest.v` after the facades are
imported; the OE value carries profile and plug as projections, so the row
stays small and §12.12-compliant — no theorem proofs stored):

```coq
Record AnalysisPathRow := MkAnalysisPathRow {
  apr_observed    : OE.ObservedExecution ;
  apr_sample      : forall R : realType,
                      option (SampleAdapter R (OE.oe_execution apr_observed)) ;
  apr_completion  : CompletionLevel ;
  apr_transfer    : TransferStatus ;
  apr_assumptions : AssumptionStatus ;
}.
```

One `Definition <instance>_row_<path> : AnalysisPathRow` per analysis path
(including re-encoding the five existing PGL27/five-card paths). The source
table comments keep the ten-field prose format; levels in the table must match
the typed fields (checker Checks pin every alias and every row).

## Task list (one atomic commit per task; make -j1; audit gate unbypased)

### T0 — status vocabulary + shared lemma relocation
Files: NEW `pgg-smc/manifest/pgg_analysis_status.v` (vocabulary above, with
@intent comments); `pgg-smc/security/pgg_collusion_bound.v` (add
`var_dist_fdistmap_inj` verbatim from s5x5_mixing.v:329-357, general section);
`pgg-smc/instances/s5x5/s5x5_mixing.v` (delete its local copy; its uses
resolve via the existing pgg_collusion_bound import); `_CoqProject` (+1 line
after pgg_observed_execution.v). Verify: serial rebuild of the
pgg_collusion_bound cone including s5x5_mixing.vo, s5_mixing.vo untouched
warnings-wise.

### T1.1 — s5_exec.v (S5 execution layer)
Source: `probe_s5_det_plug.v`, `probe_s5_rand_plug.v` verbatim, production
names: `s5_exec_plug` (det), `s5_rand_exec_plug`, `s5_observed`,
`s5_rand_observed`, helpers `s5_players_enumE`, `s5_content_obs`,
`s5_rcontent_obs`, `s5_rfree_share/layout/sum/valid`, `s5_rfree_shareE`,
`s5_codec` (identity; cancellation lemmas), `s5_aprocs_cut`, `s5_rprocs_cut`,
`s5_rprocs_cut1` (identity-cut = s5_rprocs), `s5_recon_perm_invariant`,
`zp5_sum_val`, det/rand terminates/endpoints/endpoints_size/recovers.
Constructors verbatim from the probes:
`@dealer_secret_plug mpS 'I_5 erefl s5_run.s5_players s5_players_enumE (fun s _ => tnth (ts_encode s5_scheme s)) 150`
and the `'rV['Z_5]_5` twin with `(fun u _ => tnth (s5_rfree_layout u))`.
`_CoqProject`: insert after `s5_trace.v` (line 233). Comments per §11 (role
tags; player-list cache comment; fuel comment; codec comment).

### T1.2 — s5_models.v (S5 models + executed security)
Source: `probe_s5_adapters.v`. Production content: `s5_rand_sample`
(sampleT `'rV['Z_5]_5`, prior respelled s5P, arg idfun, cut `fun _ => 1%g`),
`s5_word_sample` (prior `secretP `x word_uniform 3 L`, cut word_eval),
reader equalities `s5_sample_content_traceE`, `s5_sample_coalition_viewE`,
executed theorems `s5_exec_trace_secrecy` (@main security),
`s5_exec_coalition_secrecy` (@main security), `s5_word_cut_distE`,
`s5_word_endpoint_bound` (@main bound, conditional AxRayleighQ2R),
`s5_word_base_premise` (the named missing premise) and
`s5_word_transfer_conditional`. No finite-word coalition claim anywhere.

### T1.3 — s5_analysis.v (S5 facade)
Module S5Analysis, seven sections + `bound` sub-block, aliases only; Transfer
section exposes `Definition rand_transfer_status : TransferStatus := StaticExecutedOnly.`
+ its two reader equalities, and
`Definition word_transfer_status : TransferStatus := NoModelComparison.`
+ `word_missing_premise := s5_word_base_premise` naming the absent premise;
`det_transfer_status := NoModelComparison`. Retention checks at end of file.
`_CoqProject` after s5_models.v.

### T2.1 — s5x5_exec.v
Source: `probe_s5x5_det_plug.v`, `probe_s5x5_rand_plug.v`. Names:
`s5x5_exec_plug`, `s5x5_rand_exec_plug`, `s5x5_observed`,
`s5x5_rand_observed`; recovery chain `s5x5_reconE`,
`s5x5_pile1_sharesE/pile2_sharesE`, `s5x5_pile1_layoutE/pile2_layoutE`,
`s5x5_p1_map/p2_map` (+ injectivity), `sum_mod5_recon_reindex`,
`s5x5_rfree_recon` (axiom-free), `s5x5_rand_run_recovers`; oe_expected is the
combine_secret image (comment: 'I_10 image only, combine_secret not
injective — O3). Reuses s5_rfree_* from s5_exec.v (import s5_exec, qualified
where needed per D5). `_CoqProject` after s5x5_trace.v (line 240).

### T2.2 — s5x5_models.v
Source: `probe_s5x5_adapters.v`. `s5x5_rand_sample` (Pprod respelled),
executed readers: content trace, `pile1_seat`, `pile2_seat`,
`pile1_coalition`, `pile2_coalition`, `joint_coalition`, verifier; theorems:
`s5x5_exec_trace_secrecy`, `s5x5_exec_p1_secrecy` / `s5x5_exec_p2_secrecy`
(NEW Pprod statements against JointSecret per O1 — comments state they are
not restatements of s5x5_view_secrecy_concrete), `s5x5_exec_joint_secrecy`;
word adapters + `s5x5_word_cut_distE` + `s5x5_word_pile1_bound/pile2_bound/
seat_bound` (conditional AxRayleighQ2R); floors
`s5x5_word_pile1_floor/pile2_floor` (NegativeTransfer content); positivity
corollary at L >= 17 via a rational sqrt-5 bound (5 < (2236068*10^-6)^2 shape,
landed-2^-40 precedent); `s5x5_word_base_premise` + conditional transfer.

### T2.3 — s5x5_analysis.v
Module S5x5Analysis, seven sections + bound sub-block; transfer aliases:
rand path `StaticExecutedOnly` (per-pile + joint reader equalities), pile
finite-word rows `NoModelComparison` (+ missing premise), two global-uniform
limitation aliases `NegativeTransfer` (floor + reverse-triangle bound +
positivity regime named). Retention checks. `_CoqProject` after s5x5_models.v.

### T3.1 — abel_profile.v revision (four-seat interface)
Source: `probe_abel_profile.v` verbatim. Edit in place: add
`abel_starts_uniq : uniq (ord_tuple 4)`,
`abel_PI : PGGInterface abel_M := @MkPGGI abel_M 3 (ord_tuple 4) abel_starts_uniq`,
redefine `abel_profile := @MkMonodromyProfile abel_M 'I_4 abel_PI abel_plug`
(probe name abel_profileP becomes the production abel_profile), keep
`Gen_PGG_2 abel_sigmas` only in its group-level role (its one profile use was
abel_profile.v:73), update `profile_k_abel` (= 4 by []). Also land the Klein
facts here or in abelian_exec.v: `abel_G4 = [set 1; s1; s2; s1*s2]`,
`abel_pgg_GE : pgg_G abel_M = abel_G4`, `#|abel_G4| = 4`,
`abelian (pgg_G abel_M)`. Consumers to migrate: none beyond profile_k_abel
(near-orphan, verified). Serial rebuild of the abelian cone.

### T3.2 — abelian_exec.v
Source: `probe_abel_plugs.v` verbatim. `abel_players` (4 explicit ordinals +
players_enumE), the generic `abel_verifier_endpoints` (content g, start tuple,
cut w0 all abstract; vm_compute), secret-recovery plug
`@dealer_secret_plug abel_profile 'I_4 erefl abel_players abel_players_enumE
(fun s _ => tnth (ts_encode abel_ts s)) 150` with terminates (nseq 6 Finish),
endpoints, size 4, recovery for every s and every cut in pgg_G; identity-
content shuffle plug (`ep_inputT = unit`, content `fun _ _ => idfun`, fuel
150) with `abel_identity_recon_value := Ordinal 2 : 'I_4` (constant for EVERY
permutation cut) — no arbitrary-secret claim; both OE values
(`abel_det_observed` oe_expected id; `abel_shuffle_observed` oe_expected
`fun _ => abel_identity_recon_value`); `abel_reader sigma = [tuple sigma
(tnth (pi_starts abel_PI) i) | i < 4]` + `abel_reader_inj` (GLOBAL) +
`abel_shuffle_executed_readerE : exec_endpoints abel_shuffle_plug x w0 0 =
val (abel_reader w0)`.

### T3.3 — abelian_models.v + negative theorem
Source: `probe_abel_negative.v` verbatim. `abel_group_uniform :=
fdist_uniform_supp abel_G4` (positivity from card 4); `abel_word_dist R L :=
@rho_from_words R 2 1 L.+1 abel_sigmas`; adapters `abel_ideal_adapter`
(sampleT {perm 'I_4}, cut idfun) and `abel_actual_adapter L` (sampleT
pgg_word abel_M L.+1, prior word_uniform, cut word_eval) on the shuffle plug
+ `abel_actual_cut_dist` (by []); parity chain: `abel_word_evalE`,
`abel_flip` involution + `abel_flip_freq` (cardsD1) + `abel_parity_mass_flip`
(reindex_inj) + `abel_parity_mass_half` (bigID against FDist.f1 + mulIf);
distance theorems verbatim: `abel_word_group_dist` (= 1 for every R, L),
`abel_executed_distance` (through abel_reader, via the relocated
var_dist_fdistmap_inj — D6), `abel_sample_reader_dist` (fdistmap_comp) and
`abel_executed_observation_distance` (= 1 at the adapters' own sample
spaces), plus the length-0 exclusion witness `abel_word_group_dist0`
(= 1 + 2^-1). @main security tag with the label "fixed-length mixing
limitation"; NegativeTransfer chain exposes group form, static form, executed
form and the connecting equalities.

### T3.4 — abelian_analysis.v
Module AbelianAnalysis, seven sections; transfer alias `NegativeTransfer`;
rows' capabilities labelled per §9.8 with the soundness-audit correction
(mixing-limitation label on the limitation row, not the correctness row).

### T4.1 — manifest rows + typed records
`pgg_analysis_manifest.v`: extend Require Export with the three new facades;
add `AnalysisPathRow` + one row per path: PGL27 (2 rows: exact, word),
five-card (3 rows: uniform, single-biased, repeated/centi), S5 (3 rows per
§7.8), S5xS5 (6 rows per §8.7), Abelian (3 rows per §9.8) — statuses:
  - S5: det NoModelComparison/AcceptsAxioms[AxS5GroupOrder]; rand
    StaticExecutedOnly/AcceptsAxioms[AxS5GroupOrder]; word
    NoModelComparison/AcceptsAxioms[AxS5GroupOrder; AxRayleighQ2R]
    ("conditional" appears in each Rayleigh-dependent capability description).
  - S5xS5: det + rand as S5 with AxS5x5GroupOrder; pile word rows
    NoModelComparison + AxRayleighQ2R; two limitation rows NegativeTransfer +
    AxRayleighQ2R (positive regime L >= 17 stated).
  - Abelian: recovery + identity-content rows NoModelComparison; limitation
    row NegativeTransfer; assumption status from probe Print Assumptions
    (expected KernelClosed or boolp-only — confirm from probe ledger).
  - PGL27/five-card: existing capabilities re-labelled with typed statuses
    (PGL27 word path gets IdealFinite — it has the landed transfer theorem;
    five-card exact rows StaticExecutedOnly; repeated/centi row
    NoModelComparison), levels migrate Security-bridged → AnalysisBridged.
Checker: Timeout 60 Check for every new alias + every row + every status
alias. Source-table prose updated; "Absent capabilities" appendix updated to
name each missing premise.

### T4.2 — clean client
`pgg_analysis_client.v`: one representative alias per section per facade (all
five), typed status aliases for empty-math Transfer sections, Fail Checks for
instance internals, namespaces distinct.

### T4.3 — completeness check
NEW `pgg-smc/scripts/profile_facade_check.sh` (modeled on
abstract_metrics.sh): tracked files under pgg-smc/instances, comment-stripped,
finds top-level global `Definition ... : MonodromyProfile` + direct aliases,
excludes Local/Let/facades/probes/docs; classifies against the pinned list
(pgl27 represented, five_card represented, den_boer alias, s5/s5x5/abelian
represented, nothing else). Exit non-zero on drift. Run and record output.

### T5 — verification + report + commits (request §14–15)
Focused serial builds per touched .vo; clean client build; full affected cone
build; rocq-audit on every touched .v; Admitted/Abort scan; Print Assumptions
on every new public theorem (recorded per row); manifest mutation checks
(remove an alias → checker fails; retype → mismatch); timed reduction check
only if a player list or fuel changed (none planned). Complete the response
doc's 23-item completion report. Commits per task through the gate.

## Verification sources (per memory rule)
Every T-task verifies against: the probe files (compiled at baseline), the
landed instance lemmas (unchanged), and the manifest checker (mutation-tested
in T5). No spike-only artifacts: everything load-bearing lands in production
files with facade aliases and typed rows.
