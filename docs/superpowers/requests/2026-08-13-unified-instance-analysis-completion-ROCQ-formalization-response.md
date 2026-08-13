# Completion response: unified instance analysis contract

Date: 2026-08-13 (amended and completed the same day)

Status: COMPLETE UNDER AMENDMENT. The request as originally pinned was
partially impossible: the work package A executed theorems were false, and
this response's section 3 keeps their compiled refutations. The user
approved amending the request (section 0); under the amended request every
work package is delivered and every amended acceptance criterion passes.
The original section 11 criteria 1-6 are refuted as written and met in
their amended form.

Request: `docs/superpowers/requests/2026-08-13-unified-instance-analysis-completion-ROCQ-formalization-request.md`

## 0. The amendment (user-approved, 2026-08-13)

This response records that the REQUEST WAS CHANGED, by user approval given
in-session after the NO-GO report, for the following reasons:

- The section 4.1/4.2 executed upper bounds, as pinned (observer
  `sa_seat_dist` of the deterministic plugs, ideals the uniform
  distributions, constants `sqrt 5 * alpha^L` and `sqrt 5 * lazy^L`), are
  mathematically FALSE: the deterministic encoder `sum_mod_encode s =
  [0,...,0,s]` collapses the executed content, and compiled counterexamples
  (section 3) refute all four upper-bound shapes, prior-independently.
- The true executed statements the request's machinery supports compare the
  executed reading with the ENCODER-IMAGE ideals: the content a seat reads
  when its dealt position is exactly uniform, mixed over the secret prior.
  The user chose this repair (option 1 of the NO-GO report's menu) over
  randomizing the encoder or delivering floors only.

What the amendment changes in the request, precisely:

1. Section 4.1/4.2 statement shapes: the ideals become the encoder-image
   readings (`s5_ideal_reading`, `s5x5_ideal_pile1_reading`,
   `s5x5_ideal_pile2_reading`, `s5x5_ideal_seat_reading`); the constants
   and the observer are unchanged. The 4.2 item-3 shape
   (`<= 1 + sqrt5*lazy^L` against global uniform) is not reproduced (it is
   refuted); its role passes to the per-seat pile-ideal bound
   `s5x5_exec_seat_bound` and the ceiling `s5x5_exec_seat_uniform_ub`,
   whose leading term is the ideal's own distance, deliberately not a
   constant.
2. Section 3 item 3 now reads: no cut-carrier or full-carrier
   ideal-to-finite theorem is claimed for S5 or S5xS5; the missing
   full-carrier premise remains absent and named; the OBSERVER-LEVEL
   encoder-image transfer IS claimed.
3. Section 4.3's transfer column and its sentence "Do not change these
   paths to IdealFinite": superseded. With the executed transfer theorems
   landed, `NoModelComparison` would be false under the vocabulary's own
   definition; the word rows are `AnalysisBridged / IdealFinite` and the
   limitation rows `AnalysisBridged / NegativeTransfer`.
4. Acceptance criteria 1-6: met in the amended form (section 10).

The amendment decisions were adversarially audited before implementation
(section 7): the IdealFinite label carries binding conditions (this record;
the two-ideal guard prose everywhere; the vocabulary clarification), and
the floors' obstruction is re-sourced to encoder support confinement.

## 1. Commits (section 12 item 1)

- Baseline: `51f8192661440576abd8274d051cf5e366b6ec87`.
- Packages B and C (delivered before the amendment): `e1b11396` (rename),
  `ffebab0b` (model-family vocabulary), `89220316` (ten typed families),
  `9cceb246` (dependent model slot), `0d925262` (legend alignment),
  `ed48250b` (the pre-amendment NO-GO response).
- Amended package A: `b552ef7a` (generic mixture and support lemmas + S5),
  `2dfcb150` (S5xS5), `7c6f7f13` (manifest statuses, check 5, client),
  `9220bedc` (IdealFinite vocabulary clarification), `36def083` (the
  fourth mutation guard and the post-landing audit fix-forwards; the
  guard had been claimed in 7c6f7f13's message but its edit was lost in a
  timed-out shell step, which the compensating review caught).
- Final commit: the commit updating this response.

## 2. Verdicts (section 12 item 2)

| Package | Verdict |
|---|---|
| S5 executed endpoints | GO under the amendment: `s5_exec_endpoint_bound` at the encoder-image ideal; the original uniform-ideal statement refuted (section 3) |
| S5xS5 executed endpoints | GO under the amendment: seven executed theorems plus the ceiling and two unconditional support floors; original items 1-3 refuted |
| Typed manifest | GO: dependent model slot, ten families, all four mutation guards, check 5 satisfied by the eleven executed spelled-type pins |
| Assumption-status correction | GO: `BaselineClassicalOnly` |
| Repository contract | GO: one-import client reaches the model families, the executed theorem family, the ideal readings, the revised typed fields and constructors |

## 3. The refutation of the original package A (kept as the amendment's justification)

The deterministic plugs deal the canonical threshold encoding, and that
encoding is degenerate: `sum_mod_encode s = [0,0,0,0,s]`
(`pgg-smc/reconstruct/pgg_sharing_framework.v:191`), the `ts_encode` of
`s5_scheme = @sum_mod_scheme 3 4`; `product_encode` composes two such
encoders pile-wise. The interpreter-executed seat endpoint is
`tnth (ts_encode scheme s) (rho(cut)(seat))` by the cut-generic seat
equations, with `pgg_rho` the identity inclusion and identity start
tuples. So `sa_seat_dist` is the position distribution pushed through a
non-injective content map, and at `secretP := fdist1 ord0` it equals
`fdist1 ord0` at EVERY word length, at full-L1 distance 8/5 from
`fdist_uniform (card_ord 5)` and from the pile ideals, and 9/5 from
`fdist_uniform (card_ord 10)` — while the claimed right-hand sides fall
below these constants. A session probe (twelve statements, all `Qed`,
zero `Admitted`/`Abort`/`Axiom`, mutation-checked, assumptions the boolp
trio plus only the relevant group-order axiom) compiled:

```coq
Lemma refute_s5_seat_dist (L : nat) (i : 'I_(pi_T' (mp_PI mpS)).+1) :
  @sa_seat_dist R mpS s5_exec_plug (s5_word_sample (fdist1 ord0) L) 0 i
  = fdist1 ord0.

Lemma refute_s5_requested :
  ~ (forall (secretP : R.-fdist 'I_5) (L : nat)
       (i : 'I_(pi_T' (mp_PI mpS)).+1),
       var_dist
         (@sa_seat_dist R mpS s5_exec_plug (s5_word_sample secretP L) 0 i)
         (fdist_uniform (card_ord 5))
       <= Num.sqrt 5%:R * (s5_alpha_R R) ^+ 17).
```

with the S5xS5 analogues (`refute_s5x5_pile1_requested`,
`refute_s5x5_pile2_requested` at distance 8/5 vs `sqrt5*lazy^17`;
`refute_s5x5_seat_requested` at 9/5 vs `1 + sqrt5*lazy^34`). An
independent adversarial audit confirmed every step and strengthened it:
minimal refuting lengths L = 4 (S5), 7 (piles), 22 (global seat), and the
S5 failure is prior-independent (`P(endpoint = ord0) >= 4/5 - delta`; the
uniform prior gives asymptotic distance 32/25), so no quantifier repair
existed inside the original pins. The would-be floors at the uniform
target are true but only by support confinement, which motivated the
amendment's honest re-sourcing rather than delivery under the original
section 4.3 semantics.

## 4. The amended executed theorems (section 12 items 3, 5, 6)

New generic lemmas (`pgg-smc/security/pgg_collusion_bound.v`):
`fdistmap_prod_curryE` (product pushforward as prior-weighted mixture),
`var_dist_fdistmap_prod_mix` (the mixture bound: per-first-coordinate
distance delta transfers to the product pushforwards; the two right
factors may live on different carriers), `var_dist_supp_ge`
(`2 * (1 - #|S|/n.+1) <= var_dist P uniform` when P vanishes off S).

The encoder-image ideals (Models layer, aliased in the facades):

```coq
Definition s5_ideal_reading (secretP : R.-fdist 'I_5) : R.-fdist 'I_5 :=
  fdistmap (fun sq : 'I_5 * 'I_5 => tnth (ts_encode s5_scheme sq.1) sq.2)
    (secretP `x (fdist_uniform (card_ord 5))).
```

with `s5x5_ideal_pile1_reading` / `s5x5_ideal_pile2_reading` (positions
through `widen5to10` / `rshift5to10`) and the per-seat
`s5x5_ideal_seat_reading` (the seat's own pile's ideal).

Old cut-level theorem (kept, reworded as cut-level) and its executed
counterpart (all conditional on `s5_rayleigh_Q2_R`, full-L1, one endpoint
marginal, no privacy or coalition claim; proofs are per-secret DPI onto
the landed spectral bounds plus the mixture lemma):

| Cut-level (kept) | Executed counterpart (new) |
|---|---|
| `s5_word_endpoint_bound` | `s5_exec_endpoint_bound`: `var_dist (sa_seat_dist (s5_word_sample secretP L) 0 i) (s5_ideal_reading secretP) <= sqrt5 * alpha^L` |
| `s5x5_word_pile1_bound` | `s5x5_exec_pile1_bound` (vs the pile-1 ideal, `sqrt5 * lazy^L`) |
| `s5x5_word_pile2_bound` | `s5x5_exec_pile2_bound` (vs the pile-2 ideal) |
| `s5x5_word_seat_bound` | `s5x5_exec_seat_bound` (vs the seat's own pile ideal) and `s5x5_exec_seat_uniform_ub` (ceiling vs global uniform, leading term the ideal's own distance) |
| `s5x5_word_pile1_floor` | `s5x5_exec_pile1_floor`: `1 - sqrt5*lazy^L <= var_dist (executed reading) uniform_I10`, transported by reverse triangle from `s5x5_ideal_pile1_uniform_ge` (the ideal's support confinement, `1 <= var_dist ideal uniform_I10`); plus the unconditional `s5x5_exec_pile1_uniform_ge` (`1 <=` at every L, no certificate) |
| `s5x5_word_pile2_floor` | `s5x5_exec_pile2_floor` + `s5x5_exec_pile2_uniform_ge` |
| `s5x5_word_pile1_floor_gt0` | `s5x5_exec_pile1_floor_gt0` (17 <= L) |
| `s5x5_word_pile2_floor_gt0` | `s5x5_exec_pile2_floor_gt0` (17 <= L) |

Facade aliases added: S5 `ideal_reading`, `exec_endpoint_bound`; S5xS5
`ideal_pile1_reading`, `ideal_pile2_reading`, `ideal_seat_reading`,
`exec_pile1_bound`, `exec_pile2_bound`, `exec_seat_bound`,
`exec_seat_uniform_ub`, `exec_pile1_floor`, `exec_pile2_floor`,
`exec_pile1_floor_gt0`, `exec_pile2_floor_gt0`, `exec_pile1_uniform_ge`,
`exec_pile2_uniform_ge`. Changed aliases: the cut-level word aliases'
comments now say cut-level explicitly (also fixing older facade prose
that called the word-cut reader executed); `word_transfer_status`,
`pile1_word_transfer_status`, `pile2_word_transfer_status` are
`IdealFinite` with the two-ideal guard prose; the limitation statuses'
justifications are re-sourced to the support-confinement transport.
`word_missing_premise` aliases are kept verbatim, and new
`Check`/`Fail Check` pairs in both model files pin that the executed
bounds do not instantiate the cut-carrier base premises.

## 5. The manifest and client after the amendment (section 12 item 4)

Row table (families and assumption statuses unchanged from the
pre-amendment delivery; only rows 8, 11-14 changed status):

| # | Row | Family index at R | Completion | Transfer | Assumptions |
|---|---|---|---|---|---|
| 1 | `pgl27_row_exact` | `unit` | AnalysisBridged | StaticExecutedOnly | BaselineClassicalOnly |
| 2 | `pgl27_row_word` | `R.-fdist bool` | AnalysisBridged | IdealFinite | BaselineClassicalOnly |
| 3 | `five_card_row_uniform` | `unit` | AnalysisBridged | StaticExecutedOnly | BaselineClassicalOnly |
| 4 | `five_card_row_biased` | `unit` | AnalysisBridged | StaticExecutedOnly | BaselineClassicalOnly |
| 5 | `five_card_row_repeated` | `unit` | Sampled | NoModelComparison | BaselineClassicalOnly |
| 6 | `s5_row_det` | empty optional slot | Observed | NoModelComparison | AcceptsAxioms [:: AxS5GroupOrder] |
| 7 | `s5_row_rand` | `unit` | AnalysisBridged | StaticExecutedOnly | AcceptsAxioms [:: AxS5GroupOrder] |
| 8 | `s5_row_word` | `R.-fdist 'I_5 * nat` | AnalysisBridged | IdealFinite | AcceptsAxioms [:: AxS5GroupOrder; AxRayleighQ2R] |
| 9 | `s5x5_row_det` | empty optional slot | Observed | NoModelComparison | AcceptsAxioms [:: AxS5x5GroupOrder] |
| 10 | `s5x5_row_rand` | `unit` | AnalysisBridged | StaticExecutedOnly | AcceptsAxioms [:: AxS5x5GroupOrder] |
| 11 | `s5x5_row_pile1_word` | `R.-fdist 'I_10 * nat` | AnalysisBridged | IdealFinite | AcceptsAxioms [:: AxS5x5GroupOrder; AxRayleighQ2R] |
| 12 | `s5x5_row_pile2_word` | `R.-fdist 'I_10 * nat` | AnalysisBridged | IdealFinite | AcceptsAxioms [:: AxS5x5GroupOrder; AxRayleighQ2R] |
| 13 | `s5x5_row_pile1_limitation` | `R.-fdist 'I_10 * nat` | AnalysisBridged | NegativeTransfer | AcceptsAxioms [:: AxS5x5GroupOrder; AxRayleighQ2R] |
| 14 | `s5x5_row_pile2_limitation` | `R.-fdist 'I_10 * nat` | AnalysisBridged | NegativeTransfer | AcceptsAxioms [:: AxS5x5GroupOrder; AxRayleighQ2R] |
| 15 | `abel_row_recovery` | empty optional slot | Observed | NoModelComparison | BaselineClassicalOnly |
| 16 | `abel_row_identity` | empty optional slot | Observed | NoModelComparison | BaselineClassicalOnly |
| 17 | `abel_row_limitation` | `nat` | AnalysisBridged | NegativeTransfer | BaselineClassicalOnly |

Typed model slot (pre-amendment delivery, unchanged): `apr_model :
AnalysisModelSlot apr_observed apr_completion` makes a `Sampled` or
`AnalysisBridged` row without an `AnalysisModelFamily` witness over its
own observed execution a type error. Manifest checks: per-row `apr_model`
checks, index-exercise checks, the generic execution-projection check, 51
erefl status pins (8 flipped by the amendment, plus 3 facade status
pins), the eleven executed spelled-type checks (request 5.3 check 5), and
five mutation `Fail` commands covering the four requested mutation
classes, the fourth class being the executed alias reverted to the
cut-level type (landed in `36def083` after the compensating review caught
its earlier omission). The manifest's convention banner, the five affected row
tables, the row-17 justification and the absent-capabilities block are
rewritten so the three comparison targets (cut-level pile uniform;
satisfiable encoder-image ideals; unsatisfiable-premise group uniform)
cannot be conflated, and the premise-naming obligation covers the
IdealFinite and NegativeTransfer word rows by name. The still-recorded
fact that the group-uniform cut-carrier premise is UNSATISFIABLE (sign
cosets) is untouched and now guarded on both sides.

Client: exactly one `Require`; additionally reaches the three ideal
readings and all eleven executed aliases.

## 6. Changed files by work package (section 12 item 7)

- Package C: `pgg-smc/manifest/pgg_analysis_status.v`,
  `pgg_analysis_manifest.v` (e1b11396).
- Package B: `pgg_analysis_status.v` (ffebab0b, 9cceb246-adjacent);
  the ten instance/facade files (89220316); `pgg_analysis_manifest.v`,
  `pgg_analysis_client.v` (9cceb246, 0d925262).
- Amended package A: `pgg-smc/security/pgg_collusion_bound.v`,
  `pgg-smc/instances/s5/{s5_models,s5_analysis}.v` (b552ef7a);
  `pgg-smc/instances/s5x5/{s5x5_models,s5x5_analysis}.v` (2dfcb150);
  `pgg-smc/manifest/{pgg_analysis_manifest,pgg_analysis_client}.v`
  (7c6f7f13); `pgg_analysis_status.v` (9220bedc).
- No new production `.v` file; `_CoqProject` unchanged. No paper, slide,
  bibliography or older formalization response touched (the pre-existing
  uncommitted user modification of `pgg-smc/paper-wadt2026/main.tex` was
  never staged). `s5x5_models.v` gained the `mathcomp lra` import for two
  rational side conditions.

## 7. Builds, tests, audits (section 12 items 8, 9)

All builds `opam exec --switch=/Users/cheng-huiweng/Projects/coq -- make
-j1 <targets>`, Rocq 9.0.0 / OCaml 5.2.1, every one exit 0. Amended-round
steps: collusion_bound 5.7 s; s5_models 73 s; s5_analysis 8.3 s;
s5x5_models 6.6-7.0 s per iteration; s5x5_analysis 8.1 s; manifest +
client 10.6 s; facade checker exit 0 (six profiles) and
profile_facade_check_test.py 18/18; final forced client rebuild + full
serial repository build exit 0 (pre-amendment full build: 10 min 17 s;
amended-round full build recorded in the session log). Probe compiles:
refutation probe 5.0 s; model-slot probe 6.8 s; amended-statement probe
5.2 s (fifteen `Qed`, statements byte-identical up to one
parenthesization, three mutation checks failing correctly, one of them
upgraded to a compiled counterexample of the hypothesis-free support
lemma).

Warnings: no new warning class; the pre-existing classes now also appear
on the files that gained protocol-layer imports.

Scans over all touched production files:
`Axiom|Parameter|Admitted|admit|Abort`: none found.

Audits: the pre-commit gate ran on every commit (Stage 1; Stage 2 remains
the S998 no-op), with one Stage-1 rejection each on b552ef7a's and
2dfcb150's first attempts (a five-component name without `Naming:`; probe
comments without H-series role tags), fixed forward before the commits
landed. Compensating direct rocq-auditor dispatches reviewed every
substantive commit; the amendment's label decisions were separately
audited before implementation (conditional GO whose conditions this
response and the landed prose discharge), and the post-landing dispatch
over the four amended commits returned: wording contract COMPLIANT on
every added line (no privacy framing, no ideal conflation, floors sourced
in the encoder), one error-severity accuracy finding (the fourth guard
claimed but not landed) and eight style findings, all fixed forward in
`36def083`.

## 8. Print Assumptions (section 12 item 10)

Per new public theorem and its facade alias (identical lists):

- boolp trio only: `fdistmap_prod_curryE`, `var_dist_fdistmap_prod_mix`,
  `var_dist_supp_ge`, `s5x5_ideal_pile1_uniform_ge`,
  `s5x5_ideal_pile2_uniform_ge`.
- trio + `s5_group_order_eq` + `s5_rayleigh_Q2_R`:
  `s5_exec_endpoint_bound` (and `S5Analysis.exec_endpoint_bound`).
- trio + `s5x5_group_order_eq` + `s5_rayleigh_Q2_R`:
  `s5x5_exec_pile1_bound`, `s5x5_exec_pile2_bound`,
  `s5x5_exec_seat_bound`, `s5x5_exec_seat_uniform_ub`,
  `s5x5_exec_pile1_floor`, `s5x5_exec_pile2_floor`,
  `s5x5_exec_pile1_floor_gt0`, `s5x5_exec_pile2_floor_gt0`.
- trio + `s5x5_group_order_eq` (NO Rayleigh): the unconditional support
  floors `s5x5_exec_pile1_uniform_ge`, `s5x5_exec_pile2_uniform_ge`.

The ideal definitions and model families carry at most the trio plus the
instance group-order axiom, as recorded in section 8 of the pre-amendment
response.

## 9. Boundary confirmations (section 12 items 11-13)

- Item 11: `s5_rayleigh_Q2_R` retained, not eliminated, unfolded,
  reproven or expanded; every dependent theorem is explicitly conditional,
  and the two unconditional support floors are proved without it.
- Item 12, strongest repository-facing claim: every live instance's
  finite-word path now carries an executed, machine-checked transfer: the
  interpreter-executed seat reading of the deterministic S5/S5xS5 plugs is
  within the spectral mixing term of the encoder-image ideal reading, for
  every secret prior, every seat and every word length; and against global
  uniform the S5xS5 executed readings are provably far (at least
  `1 - sqrt5*lazy^L` conditionally, at least 1 unconditionally), a
  limitation of the deterministic encoder's executed reading. The typed
  manifest enforces model witnesses; the assumption vocabulary states its
  true boundary.
- Item 13, nearby claims that remain false, superseding the pre-amendment
  response's item 13 where noted: the ORIGINAL uniform-ideal executed
  upper bounds (refuted, section 3); any privacy, secrecy,
  indistinguishability, coalition or leakage reading of any finite-word
  endpoint result, executed or cut-level; any cut-carrier or full-carrier
  ideal-to-finite transfer for S5/S5xS5 (the group-uniform premise remains
  absent and unsatisfiable); any reading of the encoder-image ideal as
  uniform or secret-independent; and — SUPERSEDED — the pre-amendment
  sentence calling the executed floors mislabeled is replaced: they are
  now honestly delivered as transports of the encoder-image ideal's
  support confinement, with the unconditional constant-one versions landed
  alongside, and the prose sources them in the encoder, never in a
  spectral mixing failure.

## 10. Acceptance ledger (section 11, amended)

1. AMENDED-MET: S5 has `s5_exec_endpoint_bound` at `sa_seat_dist` of
   `s5_word_sample` (against the amended ideal).
2. AMENDED-MET: S5xS5 has executed forms of both pile bounds, the seat
   bound (pile-ideal target plus the global-uniform ceiling), both floors
   and both positive-regime corollaries, plus two unconditional support
   floors.
3. MET: every cut-level theorem is retained and its aliases say cut-level.
4. AMENDED-MET: the S5 word row is `AnalysisBridged / IdealFinite`.
5. AMENDED-MET: both S5xS5 word rows are `AnalysisBridged / IdealFinite`.
6. MET: both S5xS5 limitation rows are `AnalysisBridged /
   NegativeTransfer`.
7. MET: no `Sampled` or `AnalysisBridged` row without a typed family.
8. MET: all five instances' families are typed facade values.
9. MET: the client builds from one `Require` and reaches the new API,
   including the executed theorem family.
10. MET: the six-profile checker and all 18 mutation cases pass.
11. MET: all four manifest mutations fail for the intended type-level
    reason.
12. MET: no boolp-trio-dependent result is called kernel-closed.
13. MET: no new trusted assumption or unfinished proof (`lra` is a
    tactic, not an axiom; `Print Assumptions` confirms).
14. MET: no paper, slide, bibliography or unrelated file changed.
