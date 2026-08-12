# Baseline: pgg-smc measured against Shinagawa 2021 (BEFORE)

Measured 2026-08-12 at HEAD `995e2a39`, branch `pgg-smc`, before the
layered-protocol-packing implementation. Companion request:
`docs/superpowers/requests/2026-08-12-layered-protocol-packing-ROCQ-formalization-request.md`.
The AFTER measurement re-runs the METRIC commands below verbatim and
re-fills the scorecard.

## Identification

Baseline work: Kazumasa Shinagawa, "Card-based Cryptography with Dihedral
Symmetry", New Generation Computing 39, pp. 41-71, 2021.
DOI 10.1007/s00354-020-00117-9. Resolved from the local research KB
(`cite_as: Shinagawa2021`, verified, full-text-read; slice
`~/.claude/research-kb/slices/Shinagawa2021-dihedral-symmetry.md`). This is
the same paper the project's `baseline-transition-analysis` skill derives its
eight moves from, and its Section 2 is literally "A Unified Protocol Model" —
the organizational virtue the request asks to match. Runner-up candidates
(Shinagawa-Nuida DAM 2021 single-shuffle; Miyamoto-Shinagawa 2021
graph-automorphism shuffles) are not organizational/model papers.

## Virtue checklist (grounded in the paper)

| # | Virtue | Grounding in Shinagawa 2021 |
|---|---|---|
| V1 | One unified protocol model, stated once, reused by every construction | Sect. 2 "A Unified Protocol Model"; binary, polygon, dihedral cards are instances of one model |
| V2 | A single current table enumerating constructions with their parameters | Table 1 (p. 43); every protocol's card/shuffle counts findable from its fixed Efficiency block |
| V3 | One fixed per-construction template, identical across constructions | Sects. 4.1-4.8: Functionality -> Protocol -> steps -> Correctness -> Security -> Efficiency |
| V4 | Every theorem stated against the shared model, one uniform security notion | One security notion (visible sequence-trace independence, Mizuki-Shizuya lineage) applied verbatim per protocol |
| V5 | Explicit separation of protocol (syntax/execution) from security analysis | Sect. 2 model has no probability obligations; Correctness and Security are separate consuming paragraphs |
| V6 | Explicit scope and completeness statement; honest triviality/limitation calls | Sect. 2.1 states which decks the model fails on; "The correctness is trivial." said in one sentence |
| V7 | Definition-then-example discipline | Nine numbered Definitions each followed by an Example; 15 Example blocks total |
| V8 | One entry point per construction: headline results collected, one holdable number | Each of 4.1-4.8 self-contained; Table 1 aggregates |

## Metric (reproducible measurement procedures)

Scoring: 0 = absent, 1 = partial, 2 = matches baseline. Commands run from `pgg-smc/`.

- V1: count record types + files/directories a reader opens to learn what "an
  instance" is: `grep -rn "Record SecurityWitness\|Record ReconPlug\|Record ThresholdScheme\|Record PGGInterface\|Record MonodromyProfile" --include='*.v' .`
  2 = all constituents reachable from one file/section; 1 = bundling record
  exists, constituents span >= 2 directories; 0 = no shared record.
- V2: single in-repo manifest listing every in-scope instance with parameters
  and theorems, current: `grep -c pgl27 audit-inventory/THEOREM_INDEX.md`,
  `grep -c pgl27 blueprint/src/content.tex`, `git log -1 --format=%ad --date=short -- <manifest>`.
  2 = one manifest, all 5 in-scope instances, newer than last instance commit;
  1 = manifests stale/incomplete; 0 = none.
- V3: file-role template parity per instance dir; count distinct file-name
  prefixes: `ls instances/<d>/*.v | sed 's|.*/||;s/_.*//' | sort -u | wc -l`.
  2 = one prefix + same role files everywhere; 1 = one instance uniform,
  others drift; 0 = no template.
- V4: headline-theorem name/statement parity:
  `grep -rn "_trace_secrecy" instances/ --include='*.v'` and view-layer greps.
  2 = one naming scheme through framework definitions; 1 = one layer uniform;
  0 = ad-hoc.
- V5: (a) does the instance-defining record carry probability/proof fields
  (read MonodromyProfile fields); (b) directory purity
  (`ls protocol/ | grep -i security`; `ls security/ | grep -E "demo|test|debug"`;
  location of Record SecurityWitness). 2 = program record proof-free +
  witnesses separate + directories match names; 1 = one of the two; 0 = both mixed.
- V6: scope statement + dead-code census: `ls pgg-smc/README* pgg-smc/*.md`;
  `grep -n "instances/\(abelian\|cyclic\|monster\|oc\|star\)" ../_CoqProject | wc -l`.
  2 = scope stated in-repo and build matches; 1 = stated but build disagrees;
  0 = neither.
- V7: framework record headers name current in-scope fillers:
  `for f in protocol/pgg_interface.v reconstruct/covering_scheme.v reconstruct/pgg_sharing_framework.v reconstruct/algebraic_rigidity.v protocol/pgg_monodromy_profile.v; do sed -n 1,60p $f | grep -in "s5\|denboer\|den.boer\|kim\|pgl27\|abel\|example"; done`.
  2 = all 5 headers current; 1 = some stale/out-of-scope; 0 = none.
- V8: entry-point count = minimum .v files opened to collect one instance's
  headline results; facade check: `grep -rln "Require Export" --include='*.v' .`.
  2 = <= 2 files or a facade re-exports the set; 1 = 3-4 files, one dir;
  0 = >= 5 files or story spans instance dirs.

## BEFORE scorecard

| # | Score | Evidence (abbreviated; full evidence in the run log) |
|---|---|---|
| V1 | 1 | MonodromyProfile filled by all five in-scope instances; but constituents span 4 files in 2 directories (PGGInterface protocol/pgg_interface.v:379, SecurityWitness reconstruct/algebraic_rigidity.v:147, ReconPlug reconstruct/covering_scheme.v:117, ThresholdScheme reconstruct/pgg_sharing_framework.v:47) |
| V2 | 1 | THEOREM_INDEX.md stale (2026-04-23, `grep -c pgl27` = 0); blueprint covers 4/5 instances; no in-repo table of (group, N, T, k, eps, L) |
| V3 | 1 | pgl27 is the template (one prefix, full role set); denboer1989 has three prefixes, kim2025 three, s5/s5x5 three each plus scratch files |
| V4 | 1 | trace layer uniform (<inst>_trace_secrecy through the shared keystone); view/correctness layers drift (denboer_indep vs pgl27_view_indep; FiveCardKim_protocol_correct lives in den_boer_profile.v) |
| V5 | 0 | mp_security : SecurityWitness (distribution + eps + proved bound) is a constructor field of MonodromyProfile; ts_private in mp_plug; pgg_uc_security.v in protocol/; debug/test/demo files in security/; witness record in reconstruct/ |
| V6 | 0 | no README/scope note in pgg-smc/; abelian, cyclic, monster, oc, star (10 files) still in _CoqProject |
| V7 | 1 | header blocks present, but example pointers stale: pgg_monodromy_profile.v:22-23 lists retired abel_profile, omits pgl27/five_card; pgg_interface.v:53 motivates via retired groups; algebraic_rigidity.v:40-42 names 5/7 out-of-scope instances |
| V8 | 0 | zero Require Export in pgg-smc/; PGL story needs >= 6 files; five-card story spans two instance dirs with a cross-named theorem |

## TOTAL: 5 / 16

Three largest gaps: V5 (protocol/security entanglement — request stage A),
V6 (no scope statement / retired instances built — manifest + H2 inventory),
V8 (no per-instance entry point — request stage H1 facades + manifest).
