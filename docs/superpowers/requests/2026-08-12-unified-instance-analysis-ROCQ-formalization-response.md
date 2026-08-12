# Formalization response: unified analysis pipelines for all protocol instances

Date: 2026-08-12. STATUS: IN PROGRESS (Phase 0 running).

Request: `docs/superpowers/requests/2026-08-12-unified-instance-analysis-ROCQ-formalization-request.md`
Probes: `docs/superpowers/probes/2026-08-12-unified-instance-analysis/`
Baseline commit: `5453b93bb07b5eee63c331d17a9b95b62802b9d5` (branch `pgg-smc`).

## Phase 0 §6.1 Baseline build

Command (run from the repository root, opam switch `/Users/cheng-huiweng/Projects/coq`):

```text
make -j1 pgg-smc/manifest/pgg_analysis_client.vo \
         pgg-smc/instances/s5/s5_run.vo \
         pgg-smc/instances/s5x5/s5x5_run.vo \
         pgg-smc/instances/abelian/abel_profile.vo \
         pgg-smc/instances/abelian/abelian_word_collapse.vo
```

- Rocq: The Rocq Prover, version 9.0.0 (compiled with OCaml 5.2.1)
- OCaml: 5.2.1
- Exit status: 0
- Elapsed: 2 min 55.36 s wall (164.99 s user, 8.19 s system, 98% cpu)
- Rebuilt within the cone (stale at start, no deletions needed):
  `pgg-smc/reconstruct/rs_privacy.v`, `pgg-smc/reconstruct/rs_massey_bridge.v`,
  `pgg-smc/reconstruct/coord_perm_compatible.v`, `pgg-smc/reconstruct/cover_genus0.v`,
  `pgg-smc/instances/abelian/rigidity_abelian_instance.v`,
  `pgg-smc/instances/abelian/abel_profile.v`,
  `pgg-smc/instances/abelian/abelian_word_collapse.v`
- Warnings: all pre-existing classes only — `deprecated-library-file-since-mathcomp-2.5.0`
  (all_ssreflect), `comment-terminator-in-string` (cover_genus0.v),
  `notation-incompatible-prefix` (`_ <| _` vs `_ <| _ |> _`, abelian files). No new warnings.

## Phase 0 §6.2 Live declaration inventory

Corrected H2 description: S5 and S5xS5 are NOT "Algebraic only". Both have full
deterministic run/termination/endpoint/recovery lemma sets and randomized-tape
trace-secrecy theorems. What they lack is packaging: no `ExecutionPlug`, no
`ObservedExecution`, no `SampleAdapter`, no facade. Abelian additionally has an
incoherent profile interface (below).

### Reference shape (landed at `88ed16a2`)

- `MonodromyProfile` (protocol/pgg_monodromy_profile.v:52): mp_M, mp_secretT,
  mp_PI, mp_plug. `ExecutionPlug mp` (protocol/pgg_execution_plug.v:56):
  ep_inputT, `ep_players_bridge : pi_T' (mp_PI mp) = ts_T' (rp_scheme (mp_plug mp))`,
  ep_players, ep_playersE, ep_content, ep_input_procs, ep_fuel; smart
  constructors `dealer_secret_plug` / `committed_input_plug`.
  `OE.ObservedExecution` (protocol/pgg_observed_execution.v:89): oe_profile,
  oe_execution, oe_P_idx, oe_content_obs, oe_expected, oe_terminates,
  oe_endpoints, oe_static_recon. `SampleAdapter R mp e`
  (security/pgg_sample_adapter.v:114): sa_sampleT, sa_sampleP, sa_arg, sa_cut.
- `PGGInterface M` (protocol/pgg_interface.v:379): pi_T', pi_starts
  (`pi_T'.+1`-tuple, uniq). Seats = `pi_T'.+1`.
- Facades: `Module PGL27Analysis` / `Module FiveCardAnalysis`, seven
  `===== k. <Section> =====` markers, aliases only; five-card section 7 is
  documented-empty. Manifest = prose row tables (10 fixed fields + capability
  table + level justification) + `Timeout 60 Check (alias : spelled_type)`
  checker; client = exactly one `Require Import pgg_analysis_manifest` +
  bare `Check` per section + `Fail Check` encapsulation probes.
- Confirmed absent repo-wide: `CompletionLevel`/`TransferStatus`/
  `AssumptionStatus` as Rocq identifiers; `NoModelComparison`,
  `StaticExecutedOnly`, `IdealFinite`, `NegativeTransfer` occur only in the
  request. Phase 4 must introduce the typed vocabulary.
- Generic transfer theorem exists: `var_dist_fdistmap_transfer`
  (security/pgg_collusion_bound.v:1185), premises `var_dist P Q <= delta` and
  `fdistmap fx Q = fdistmap fy Q`, conclusion bound `delta + delta`.
- `var_dist` (probability/variation_dist.v:33) is full (un-halved) L1.

### S5 (files s5_profile.v, s5_run.v, s5_trace.v, s5_secrecy.v, s5_mixing.v, rigidity_s5_instance.v)

- Profile: `s5_profile := @MkMonodromyProfile s5_M 'I_5 s5_PI s5_plug`;
  `s5_PI = @MkPGGI _ 4 (ord_tuple 5)` (5 seats); scheme `sum_mod_scheme 3 4`
  (ts_T' = ts_k' = 4); `profile_k_s5 = 5`.
- Deterministic path (s5_run.v, no sections, R-free): `s5_players` = 5 explicit
  ordinals (s5_run.v:50), `s5_procs s w0` (dealer with
  `ts_encode s5_scheme s`, cut-parametric), fuel 150,
  `s5_run_terminates` (`= nseq 7 Finish` shape), `s5_endpoints`,
  `s5_endpoints_size`, `s5_run_recovers` (premise `w0 \in pgg_G s5_M`).
- Randomized path (s5_trace.v, Section with `Variable R`): abstract skeleton
  `s5_aprocs_abs (g : 'I_5 -> 'I_5)` with cut HARD-WIRED to `1%g`;
  `s5_rs := @unif_randomized_sharing R 3 4` over tape `'rV['Z_5]_5`
  (coord 0 = secret `'Z_5`, coords 1-4 masks; share 4 = secret - sum masks);
  `s5_rlayout u = [tuple rsh_share s5_rs i u | i < 5]`;
  `s5_rprocs u = s5_aprocs_abs (tnth (s5_rlayout u))`; distribution
  `s5P := fdist_uniform (card_ZN_subproof 3) `^ 5` (a Let — must respell);
  `s5_player_trace i` reads `content_of` at proc index `2+i`;
  `s5_player_trace_E : s5_player_trace i = rsh_share s5_rs i`;
  `s5_trace_secrecy : `H(rsh_secret s5_rs | s5_player_trace i) = `H `p_ ...`
  (conditional entropy ONLY; via `trace_secrecy_of_view`).
  Name collision: `s5_trace.s5_players` duplicates `s5_run.s5_players`.
- Static secrecy: `s5_view_secrecy_concrete (C : {set 'I_5}) (#|C| < 5)`
  gives MI = 0 AND conditional entropy preserved, coalition view carrier
  `{ffun 'I_5 -> 'Z_5}` via `rsh_view`, same tape distribution as `s5P`.
- Mixing (s5_mixing.v, no sections): `s5_alpha_R = 181/200`; the single
  Axiom `s5_rayleigh_Q2_R`; `s5_spectral_convergence_proved/gap (R L s)` bound
  `var_dist (fdistmap (fun sigma => sigma s) (rho_from_words L (path_gen_tuple 3)))
  (uniform 5) <= sqrt 5 * alpha^L` — a SINGLE-POSITION endpoint pushforward of
  the word distribution, not a cut/coalition distance.
- Consumers outside s5/: only s5x5_mixing.v (s5_rayleigh_Q2_R, s5_alpha_R*);
  everything else zero — packaging is additive.

### S5xS5 (s5x5_profile.v, s5x5_run.v, s5x5_trace.v, s5x5_secrecy.v, s5x5_mixing.v, rigidity_s5x5_instance.v, pgg_s5x5.v, s5x5_pile.v)

- Profile: `s5x5_profile` on `@Gen_PGGTypes 7 8 s5x5_gen_tuple` (10 sheets,
  8 adjacent-transposition generators, 4 per pile), secret `'I_10`, scheme
  `product_scheme (sum_mod_scheme 3 4) (sum_mod_scheme 3 4)`
  (ts_T' = 9, ts_k = 5); `profile_k_s5x5 = 5`.
- `combine_secret s1 s2 = (s1 + 5*s2) %% 10`; `split_combineK` PARTIAL
  (hypothesis `s1 + 5*s2 < 10`, i.e. holds only for `s2 < 2`);
  `combine_splitK` total. Randomized recovery must therefore work from the two
  factor sum reconstructions + pile preservation, as the request instructs.
- Deterministic path: `s5x5_players` = 10 explicit ordinals, `s5x5_procs s w0`,
  fuel 300, 12 procs, `s5x5_run_terminates` (`nseq 12 Finish`),
  `s5x5_endpoints`, `s5x5_endpoints_size` (= 10), `s5x5_run_recovers`
  (premise `w0 \in pgg_G`).
- Randomized path: `rs1 = rs2 = @unif_randomized_sharing R 3 4`; product tape
  `uv : 'rV['Z_5]_5 * 'rV['Z_5]_5`, `Pprod := Pone `x Pone` (Pone is a Let);
  codec `embed_p1 = inord (val s)`, `embed_p2 = inord (5 + val s)`,
  `proj_pile c = inord (val c %% 5)` with `cancel_p1/p2`;
  `s5x5_rlayout`, `s5x5_rprocs uv` (identity cut, abstract skeleton);
  `JointSecret uv = (rsh_secret rs1 uv.1, rsh_secret rs2 uv.2) : 'Z_5 * 'Z_5`;
  `s5x5_player_trace j` at proc `2+j`;
  `s5x5_trace_secrecy (j : 'I_10) : `H(JointSecret | s5x5_player_trace j) = `H `p_ JointSecret`.
- Static: `s5x5_view_secrecy_concrete (C1 C2 : {set 'I_5}, #|Ci| < 5)` per-pile
  MI = 0 + centropy; `s5x5_joint_view_secrecy` via `leakage_product` over
  `P `x P` — same product distribution shape as `Pprod`.
- Mixing: `s5_lazy_alpha_R = (1 + s5_alpha_R)/2`; `s5x5_pile1_TV_bound` /
  `s5x5_pile2_TV_bound` (endpoint pushforward vs `fdist_uniform_pile{1,2}`,
  bound `sqrt 5 * lazy_alpha^L`); `s5x5_spectral_TV_bound` (vs uniform 10,
  bound `1 + sqrt 5 * lazy_alpha^L`); PROVED exact floors
  `var_dist_uniform_pile1_uniform10 = 1` (s5x5_mixing.v:871) and pile2 (:901)
  — the NegativeTransfer rows' first factor already exists. All spectral
  results depend on `s5_rayleigh_Q2_R`.
- Pile structure: indices 0-4 / 5-9 of `'I_10`; `widen5to10` / `rshift5to10`;
  `s5x5_pile1_stab` (axiom-free pile preservation);
  `product_sum_mod_perm_compatible` needs only pile-1 preservation.
- Axiom surface beyond Rayleigh (rigidity path only): `s5x5_group_order_eq`,
  `s5x5_inverse_galois_realised`, `s5x5_multi_realised`. The run path is
  deliberately routed around them. Zero consumers outside the directory.

### Abelian (abel_profile.v, abelian_word_collapse.v, rigidity_abelian_instance.v, pgg_abelian.v)

- Generators: `abel_s1 = tperm 0 1`, `abel_s2 = tperm 2 3` in `'S_4` (two
  disjoint transpositions; generated group Klein Z/2 x Z/2, order 4 — order
  fact NOT yet a repo lemma). `abel_ts := @sum_mod_scheme 2 3`
  (ts_T' = 3, 4 shares over 'I_4), `abel_plug` with `rp_content = id`.
- Incoherence CONFIRMED: `mp_PI abel_profile = Gen_PGG_2 abel_sigmas` has
  `pi_T' = 1` (2 seats) while `ts_T' abel_ts = 3`; `ExecutionPlug` requires
  `ep_players_bridge : pi_T' = ts_T'`, i.e. the false `1 = 3`.
- Migration surface is near-orphan: `Gen_PGG_2 abel_sigmas` is used as a
  profile interface ONLY at abel_profile.v:73; `abel_profile` and
  `profile_k_abel` have zero consumers. Four-seat replacement
  `abel_PI := @MkPGGI (Gen_PGGTypes abel_sigmas) 3 (ord_tuple 4) uniq` follows
  the s5/pgl27 pattern verbatim; `abel_HT := erefl`, `abel_G_stable` one-liner.
- Word collapse: `abelian_word_eval` (word_eval = prod of gen^freq),
  `freq_vec_det`, `freq_vec_sum`, `abelian_search_space_bound`
  (<= 'C(L+1,1) = L+1 at Tg = 2 — too weak for the negative target).
- Reachability at fixed length (NOT yet a lemma anywhere): for L >= 1,
  `achievable L` = one parity class of exactly 2 elements
  ({s1, s2} for odd L; {1, s1*s2} for even L >= 2) out of |G| = 4; the uniform
  word distribution pushes to the UNIFORM distribution on that class
  (P(c1 odd) = 1/2). Hence var_dist(actual, uniform-on-G) =
  2*(1/2 - 1/4) + 2*(1/4) = 1 exactly, at every positive length. The complete
  endpoint vector with identity content is globally injective on `{perm 'I_4}`,
  so the distance transports to the executed observer
  (`var_dist_fdistmap_inj` pattern, s5x5_mixing.v:329).
- `weval_inj` is FALSE for L >= 2 (2^L words, 2 achievable elements), so the
  probe must use `security_witness_from_bound`-style statements, never the
  `Hlfree`-carrying constructors. `rho_from_words` itself needs no Hlfree:
  `@rho_from_words R 2 1 L abel_sigmas : R.-fdist {perm 'I_4}`.
- `abel_security_witness_direct_1` (L = 1, eps = 1) via endpoint injectivity;
  consumed by `abel_rigidity` only.

## §18 fresh independent re-audit

### Naming/API/architecture audit: VERDICT GO

Findings adopted into the plan:

1. Module names: `Module S5Analysis` in `s5_analysis.v`, `Module S5x5Analysis`
   in `s5x5_analysis.v` (identifier family is uniformly `s5x5`),
   `Module AbelianAnalysis` in `abelian_analysis.v`. No collisions repo-wide.
2. Dual-plug alias names (request leaves them open): deterministic path keeps
   pgl27-parity names (`exec_plug`, `observed`, `exec_correct`,
   `exec_recovers`); randomized path gets `rand_` prefix (`rand_exec_plug`,
   `rand_observed`, `rand_correct`, `rand_recovers`). S5x5 observer aliases
   carry pile tags (`pile1_seat_endpoint`, `pile2_coalition_view`,
   `joint_view`).
3. Cross-file duplicates (complete): only `s5_players` (s5_run.v:50 vs
   s5_trace.v:44, identical bodies) forces qualification; `content_of` has
   four copies (s5_trace, s5x5_trace, pgl27_trace, denboer_trace) — import
   discipline: no file Imports two `*_trace` modules; `content_of` written
   qualified in any file importing more than its own instance cone.
   §8.1's implied `s5x5_players` collision does not exist (defined once).
4. Typed vocabulary placement: new `pgg-smc/manifest/pgg_analysis_status.v`
   (no pgg imports; `Inductive CompletionLevel/TransferStatus/AssumptionStatus`),
   `_CoqProject` insertion after `pgg_observed_execution.v` (line 141);
   facades `Require Export` it; manifest/client inherit through facades
   (placing it inside the manifest would be an import cycle). All constructor
   names collision-free as identifiers. `AssumptionStatus` needs a
   data-carrying constructor: `KernelClosed | AcceptsAxioms of seq string`
   (or a dedicated axiom-label enum).
5. New files (precedent pgl27_exec/models/analysis): `s5_exec.v`, `s5_models.v`,
   `s5_analysis.v` (after `s5_trace.v`, line 233); `s5x5_exec.v`,
   `s5x5_models.v`, `s5x5_analysis.v` (after line 240); `abel_profile.v`
   edited in place; `abelian_exec.v`, `abelian_models.v`,
   `abelian_analysis.v` (after line 245); manifest Require Export line
   extended with the three new facades.
6. Tag grammar: request §11 matches AUTHORITY.md and configured
   `main_purpose_labels` exactly. Typed status names are I001-exempt
   (CamelCase). Watch: 5-component lowercase lemma names for the
   NegativeTransfer floors need a canonical tail or `Naming:` line.
7. Completeness check: `pgg-smc/scripts/profile_facade_check.sh` modeled on
   `abstract_metrics.sh` (tracked-files universe via git ls-files, comment
   stripping, pinned expected list, `Let`-aware, `*_analysis.v` facade aliases
   excluded, den_boer alias kept). Verified universe: exactly
   {s5, pgl27, five_card, abel, s5x5}_profile + den_boer alias; nothing in
   oc/monster/cyclic/star.
8. Every load-bearing identifier in the request exists at the cited location.
9. Transfer statuses are per PATH: five-card rows 3-4 `StaticExecutedOnly`,
   row 5 (repeated/centi endpoint bounds) `NoModelComparison`. Do not stamp a
   whole facade.
10. The unnumbered `===== bound (endpoint marginal, not security) =====`
    sub-block is part of the facade template for S5/S5x5 conditional endpoint
    bounds. Prose level `Security-bridged` migrates to typed `AnalysisBridged`
    in Phase 4 (a manifest label, not a mathematical rename).

### Soundness audit: VERDICT GO

All six audited claim groups verified by hand against sources; four MINOR
corrections folded in:

1. Abelian §6.7 target VERIFIED: group = Klein four-group; support at length
   n >= 1 is one sign-parity class of 2 elements, pushforward uniform on it;
   full-L1 distance to group-uniform exactly 1 for every n >= 1 (length 0,
   distance 3/2, correctly excluded). The proof needs the parity structure,
   not commutativity alone (adding an identity generator keeps abelianness
   but destroys distance 1) — §9.6's warning is necessary and satisfiable.
   Identity-content recovery constant: recon = (0+1+2+3) mod 4 = 2, i.e.
   `Ordinal 2 : 'I_4`, constant across all of S_4.
2. MINOR (folded): state endpoint-vector injectivity GLOBALLY on
   `{perm 'I_4}` (holds; a permutation is determined by all 4 images);
   `var_dist_fdistmap_inj` requires global injectivity and then gives exact
   equality, which "exact distance 1" needs.
3. MINOR (folded): `var_dist_fdistmap_inj` currently lives in
   `s5x5_mixing.v` inside an R-section; relocate/re-prove in a shared file
   (`pgg_collusion_bound.v`, next to var_dist_triangle) so abelian does not
   import s5x5_mixing.
4. MINOR (folded): §9.8's "second capability" labelling sentence is
   off-by-one — the fixed-length mixing-limitation label belongs to row 3
   (the limitation theorem), row 2 is correctness.
5. S5xS5 NegativeTransfer rows VERIFIED: var_dist_triangle
   (pgg_collusion_bound.v:44) + symmetric_var_dist give
   `>= 1 - sqrt 5 * lazy_alpha^L`; positive regime exactly **L >= 17**
   (sqrt 5 * 0.9525^16 ~ 1.026 > 1 > 0.978 ~ at 17); in-kernel needs a
   rational sqrt-5 bound (same shape as landed 2^-40 proofs). Floors are
   axiom-free; upper bounds conditional on s5_rayleigh_Q2_R.
6. S5 randomized recovery VERIFIED: sum-mod recon telescopes
   (masks + (secret - sum masks)); codec 'Z_5 -> 'I_5 essentially identity;
   `s5_sum_mod_perm_compatible` is Qed axiom-free and covers every cut in
   pgg_G.
7. MINOR (folded): `s5_plug`/`s5x5_plug` are projections of covering records
   whose proofs use `s5_group_order_eq`/`s5x5_group_order_eq`; every value
   routed through the profiles reports the group-order axiom under
   Print Assumptions even on correctness paths. S5/S5xS5 manifest rows will
   carry AcceptsAxioms(...) status, disclosed per §12.18/§12.20; a
   re-bundled standalone plug is excluded by §5.1/§12.2.
8. S5 §7.7 discipline VERIFIED AND SHARPENED: the missing transfer premise
   is `var_dist (rho_from_words L (path_gen_tuple 3)) Q <= delta` on carrier
   `{perm 'I_5}` against a named ideal Q — and for Q = uniform on the group
   it is UNSATISFIABLE for small delta: every length-L word of transpositions
   lies in one sign coset, so var_dist >= 1 for every L. NoModelComparison is
   mathematically forced for this path (same parity mechanism as the Abelian
   target). Record under "nearby claims that remain false".
9. Five-card StaticExecutedOnly alias: pure packaging, no new mathematics.
10. S5xS5 §8.1 warnings are necessary, not cautious: product_valid at the
    combine image genuinely fails for s2 in {2,3,4}; factor-sum recovery
    works because all 8 generators are within-pile transpositions.

## Phase 0 §6.3–6.8 Probes

Probe directory: `docs/superpowers/probes/2026-08-12-unified-instance-analysis/`
(build via its `rebuild.sh`, one worker; ledger in `probe-ledger.md`).
Probe files CAN Require each other through the `uia_probe` logical root once
the sibling `.vo` exists (demonstrated by `probe_require_check.v`).

### S5 probes (§6.3–6.6): GO

Files (all exit 0, zero Admitted/Abort/Axiom, mutation-checked):
`probe_s5_det_plug.v` (4.8 s, assumptions: s5_group_order_eq only),
`probe_s5_rand_plug.v` (5.1 s, + boolp trio on the two R-bridging lemmas),
`probe_s5_adapters.v` (6.3 s, + s5_rayleigh_Q2_R on s5_word_endpoint_bound
only), `probe_s5_mutation.v` (5.0 s), `probe_require_check.v` (3.2 s).

Working constructor terms (verbatim in the probes):
- `s5_det_plug := @dealer_secret_plug mpS 'I_5 erefl s5_run.s5_players
  s5_players_enumE (fun s _ => tnth (ts_encode s5_scheme s)) 150`
- `s5_rand_plug := @dealer_secret_plug mpS 'rV['Z_5]_5 erefl
  s5_run.s5_players s5_players_enumE (fun u _ => tnth (s5_rfree_layout u)) 150`
- Both `OE.MkObservedExecution` values; `s5_rand_observed`'s expected value is
  `fun u => s5_codec (s5_tape_secret u)` with codec = identity
  ('Z_5 and 'I_5 definitionally equal; cancellations by []).
- `s5_rand_sample` (sampleT 'rV['Z_5]_5, prior = respelled s5P, arg idfun,
  cut = fun _ => 1%g); `s5_word_sample` (prior secretP x word_uniform 3 L,
  cut = word_eval).
- Convertibility by []: `exec_procs mpS s5_det_plug s w0 0 = s5_procs s w0`;
  `exec_procs mpS s5_rand_plug u w0 0 = s5_rprocs_cut u w0`;
  `s5_aprocs_cut g 1%g = s5_aprocs_abs g`.

§6.6 answers: (a) YES — respelled s5P accepted verbatim;
`s5_sample_content_traceE` + `s5_sample_trace_secrecy` restate
s5_trace_secrecy at the executed reader. (b) YES — coalition carriers agree
(`{ffun 'I_5 -> 'Z_5}` = `{ffun 'I_5 -> 'I_5}`), seat indexing via
s5_rho1_index, `s5_sample_coalition_viewE`; s5_view_secrecy_concrete reaches
the executed reader for every #|C| < 5. (c) YES —
`s5_word_cut_distE : sa_cut_dist s5_word_sample = rho_from_words L
(path_gen_tuple 3)`; spectral bound discharges at the adapter's own cut
distribution. (d) NO for the coalition reader — missing premise named as
`var_dist (sa_cut_dist s5_word_sample) Q <= delta` at carrier `{perm 'I_5}`;
mutation 8 proves the endpoint bound does not cast into it;
`NoModelComparison` stands.

Discharged obligations to carry into Phase 1: `s5_rfree_shareE` (funext +
sumrRVE; the only boolp-trio source), `zp5_sum_val` (nat/'Z_5 sum bridge),
`s5_rfree_sum` (shares telescope to the tape secret), and
`s5_recon_perm_invariant` (the inline `have` of s5_run_recovers, named).
Packaging fact: everything mentioning s5_profile inherits s5_group_order_eq
through cs_plug (run never exercises it) — assumption status per audit
finding 7.

### S5xS5 probes (§6.3–6.6): GO

Files (all exit 0, zero Admitted/Abort/Axiom): `probe_s5x5_det_plug.v`
(5.5 s, s5x5_group_order_eq only), `probe_s5x5_rand_plug.v` (5.9 s;
s5x5_rfree_recon CLOSED under global context; layout/cut lemmas boolp trio),
`probe_s5x5_adapters.v` (16.9 s; spectral results add s5_rayleigh_Q2_R),
`probe_s5x5_mutation.v` (45.6 s; 15 perturbations rejected).

Working constructors: det plug `@dealer_secret_plug mpX 'I_10 erefl
s5x5_players s5x5_players_enumE (fun s _ => tnth (ts_encode s5x5_scheme s))
300`; rand plug over `('rV['Z_5]_5 * 'rV['Z_5]_5)` with R-free layout;
`erefl` bridge works (pi_T' = ts_T' = 9); `exec_procs ... = s5x5_procs s w0`
by []; rand adapter with respelled Pprod definitionally equal (by []) to the
trace file's; word adapter with `sa_cut_dist = @rho_from_words R 8 7 L
s5x5_gen_tuple` exactly.

Randomized recovery route (no ts_valid, axiom-free `s5x5_rfree_recon`):
(1) `s5x5_reconE` by [] unfolds product recon to combine_secret of pile
recons; (2) pile-share extraction rewritten to probe seat embeddings
(val_inj on boundedness proofs); (3) cut-permuted layout reindexed by
`s5x5_p1_map/p2_map` using s5x5_pile1_stab + s5x5_preserves_pile2_proved and
codec cancellations; (4) `sum_mod5_recon_reindex` (reindex-by-injection
version of the S5 invariance proof) at the per-pile validity from the S5
probe's s5_rfree_valid.

§6.6 answers: (a) YES (Pprod definitional); (b) carrier/indexing YES via
proj_pile codec, but s5x5_view_secrecy_concrete lives over the SINGLE-pile
distribution — executed per-pile rows are new Pprod statements against
JointSecret (obligation O1), compiled as s5x5_p1_secrecy/p2_secrecy;
joint reader matches leakage_product view and s5x5_joint_view_secrecy
restates directly. (c) YES exactly. (d) NO — missing premise
`var_dist (sa_cut_dist s5x5_word_sample) Q <= delta` at `{perm 'I_10}`;
Fail-guard confirms the pile bounds do not cast into it.

NegativeTransfer floors COMPILED: `s5x5_word_pile1_floor`/`pile2_floor`:
`1 - sqrt 5 * lazy^L <= var_dist (endpoint pushforward) (uniform 10)` via
var_dist_triangle + exact pile floors + conditional pile bounds. L >= 17
positivity corollary deferred to Phase 2 (statement recorded in comment).

Carry-forward obligations: O1 (per-pile secrecy = Pprod statement, not a
restatement), O2 (pile-marginal-secret variant unprobed; manifest must name
which secret each row is about), O3 (recovery field is the 'I_10 image only;
combine_secret non-injectivity compiled), O4 (missing base premise), O5
(positivity regime), O6 (s5x5_group_order_eq on every profile-touching
value; only s5x5_rfree_recon is closed), O7 (mutation messages are expected
shapes, not harvested transcripts — compiled rejections certify).

### Abelian probes (§6.3, §6.7): GO

Files (all exit 0, zero Admitted/Abort/Axiom): `probe_abel_profile.v` (5.0 s,
all Closed under the global context), `probe_abel_plugs.v` (5.2 s, all
Closed), `probe_abel_negative.v` (5.7 s, R-carrying results boolp trio only),
`probe_abel_sig.v` (4.6 s), `probe_abel_mutation.v` (4.9 s). `abel_plug` is
axiom-FREE — nothing on the Abelian path touches s5_rayleigh_Q2_R or any
covering record.

Old bridge confirmed false (`Fail` with the pi_T'/ts_T' mismatch harvested);
new interface compiles: `abel_PI := @MkPGGI abel_M 3 (ord_tuple 4)
abel_starts_uniq`, `abel_profileP := @MkMonodromyProfile abel_M 'I_4 abel_PI
abel_plug`, bridge `erefl` (3 = 3), `profile_k abel_profileP = 4` by [].
Klein facts in-kernel: `abel_G4 = [set 1; s1; s2; s1*s2]` equals
`pgg_G abel_M`, cardinality 4, abelian.

Both plugs at fuel 150 (6 procs; vm_compute < 0.5 s with abstract leaves,
S5-pattern generic verifier-endpoints lemma): secret-recovery plug
(`ts_encode abel_ts`, recovery for every s and every cut in pgg_G) and
identity-content shuffle plug (ep_inputT = unit, content idfun; constant
recovery `abel_identity_recon_value = Ordinal 2` — holds for EVERY
permutation cut, not only group cuts). Both OE values compile. Complete
endpoint-vector reader `abel_reader sigma = [tuple sigma (start i) | i]`
GLOBALLY injective.

Negative target: compiled EXACTLY as pinned, and stronger — no parity side
condition:

```coq
abel_word_group_dist : forall (R : realType) (L : nat),
  var_dist (abel_word_dist R L) (abel_group_uniform R) = 1%R
abel_executed_distance : forall (R : realType) (L : nat),
  var_dist (fdistmap abel_reader (abel_word_dist R L))
           (fdistmap abel_reader (abel_group_uniform R)) = 1%R
abel_adapter_distance / abel_executed_observation_distance : (at the two
  SampleAdapters' own sample spaces, = 1%R)
abel_word_group_dist0 : length-0 distance = 1 + 2^-1  (exclusion witness)
```

with `abel_word_dist R L := @rho_from_words R 2 1 L.+1 abel_sigmas` and
`abel_group_uniform := fdist_uniform_supp abel_G4`. The counting lemma was
replaced by a bijection argument: flip-letter-0 involution + reindex_inj +
bigID against FDist.f1 gives class mass 1/2 directly. Label confirmed:
fixed-length mixing limitation (not privacy failure). Both parity classes
handled ({s1,s2} odd; {1,s1s2} even), distance 1 in both.

Carry-overs for Phase 3: rename abel_profileP -> abel_profile + migrate
(near-orphan); var_dist_fdistmap_inj relocation (= plan D6); SampleAdapter is
a primitive-projection record — `sa_cut u` never `sa_cut sa u`, while
sa_sampleT/sa_sampleP take the record explicitly (cost two compiles here,
will bite in Phases 1-2).

### Facade/manifest graph probe (§6.8): GREEN

`probe_facade_graph.v` (exit 0, 4.5 s): typed vocabulary
(CompletionLevel/TransferStatus/PggAxiom/AssumptionStatus) elaborates with no
collisions against the full S5 import closure; `AnalysisPathRow` with the
dependent `forall R, option (SampleAdapter ...)` slot instantiated at both an
Observed-level row (no model) and an AnalysisBridged-level row
(`Some (s5_rand_sample R)`); facade-skeleton module exposes typed
transfer-status aliases reachable by qualified bare Check (the clean-client
pattern); mutation guards hold. Import graph (status -> facades -> manifest ->
client) acyclic by construction; the exact `_CoqProject` insertion plan is in
the probe file header.

## Phase 0 §6.9 Verdicts

| Instance | Verdict | Evidence |
|---|---|---|
| S5 | **GO** | probe_s5_det_plug / rand_plug / adapters / mutation green; both plugs + OEs + adapters compile; executed secrecy bridges via reader equalities; missing transfer premise named |
| S5xS5 | **GO** | probe_s5x5_* green; randomized combine_secret recovery proved WITHOUT ts_valid (axiom-free); pile/joint readers typed; NegativeTransfer floors compiled |
| Abelian | **GO** | probe_abel_* green; four-seat interface + revised profile compile; §6.7 distance = 1 machine-checked at every positive length; axiom-free beyond boolp |

Both §18 re-audits: GO (findings folded above). Phase 0 is complete; the
implementation plan is at
`docs/superpowers/plans/2026-08-12-unified-instance-analysis-implementation-plan.md`.

## Phase 0 §6.9 Verdicts

(pending)
