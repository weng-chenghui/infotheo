# 2026-06-12 — Bridge lemma naming audit (MathComp style)

Audit of every identifier listed in Group A and Group B of
`20260612-bridge-lemma-inventory-since-blueprint.md`, against MathComp/ssreflect
naming conventions plus the project's standing rules.

## Authorities used

- **MathComp `CONTRIBUTING.md`** (master) — lemma grammar
  `(condition_)?mainSymbol_suffixes(_condition)?`; suffix table (`E` =
  elimination / rewrite equation, `P` = characteristic property / reflection,
  `_le`/`_lt`/`_ge0`, `inj`, `0`/`1`, `l`/`r` operand tags, `_card`, …);
  `in_`/`mem_` prefixes; type-structures are lowercase-first CamelCase ending in
  `Type`; HB structures / Coq modules are CamelCase. Terms and lemmas are
  lowercase.
  https://github.com/math-comp/math-comp/blob/master/CONTRIBUTING.md
- **Project rocq-auditor catalog** — `.claude/audit/template/rules/AUTHORITY.md`
  (canonical, loaded into every audit), plus rules `F001` (name does not follow
  MathComp grammar; flags `^[a-z][a-z0-9]*(_[a-z0-9]+){2,}`, allowlists
  `in_`/`mem_`/`card_`/`_of_`), `G001` (suffix does not match semantic role).
- **Project standing rules** (memory): strict snake_case for NEW identifiers;
  math-notation RV vars (`V2, V3, U1, Sout`, …) preserve paper/LaTeX form and are
  NOT violations; SSProve-style `*_valid` / `*_equiv_*` are an upstream-class
  exception; no semantic-stripping abbreviations; top-level `Lemma H...` is
  suspect (`H` = local-hypothesis convention).
- Mathlib naming page consulted for cross-check only (not authoritative here):
  https://leanprover-community.github.io/contribute/naming.html

Verdict legend: **match** (follows convention), **partial** (mostly fine, minor
drift), **mismatch** (violates a named rule, rename proposed), **out-of-scope**
(established API / pre-blueprint, do not rename per the inventory note).

---

## Group A — Pre-blueprint reused references (inventory §A, last paragraph)

| Name | Kind | Verdict | Why | Suggestion | Reason |
|---|---|---|---|---|---|
| `gen_cPr_uniform_fiber` | Lemma | out-of-scope | Established API in `entropy_fiber_zpq.v` (2026-03-01), explicitly marked out of scope by the inventory note. | keep | Pre-blueprint; renaming would churn a stable dependency. |
| `dsdp_entropy_ring` | Section | out-of-scope | Pre-blueprint section in `dsdp_entropy.v` (2026-05-14). Snake_case `mainSymbol_condition` (`_ring` = ring-generic tag) is already MathComp-shaped. | keep | Out of scope; also already conformant. |
| `id_game_run` | Definition | out-of-scope | Pre-blueprint oracle id in `dsdp_game_code.v` (2026-05-15). `id_` prefix + role, snake_case. | keep | Out of scope; conformant. |
| `id_v2_get` | Definition | out-of-scope | Pre-blueprint oracle id (`dsdp_game_code.v`). | keep | Out of scope; conformant. |

---

## Group A — Created since the blueprint (inventory §A, merge / side figures)

| Name | Kind | Verdict | Why | Suggestion | Reason |
|---|---|---|---|---|---|
| `guessing_experiment` | Definition | match | Snake_case noun-phrase main symbol; a closed `raw_package`, no suffix needed. | keep | Conformant. |
| `guess_resolve_eq` | Lemma | match | States an equation (`resolve … = …`); `_eq` is the equational suffix. Snake_case. | keep | Suffix matches role (G001). |
| `guess_joint_code` | Definition | match | Snake_case; `guess_joint` main symbol + `_code` carrier tag (a `raw_code`). | keep | Conformant. |
| `guess_success_sdistr_eq_fdist` | Lemma | partial | States `guess_sdistr_success = guess_fdist_success`; `_eq_` is equational, `sdistr`/`fdist` name the two sides (the SSProve subdistr vs Infotheo fdist). `sdistr` is an established type abbreviation (SSProve `SDistr`), not semantic-stripping. Five components stretch F001's length heuristic. | keep | The two sides are load-bearing and the name reads as `sdistr = fdist`; acceptable per the standing rule that long descriptive names beat abbreviations. |
| `guess_joint_fdist` | Definition | match | `guess_joint` + `_fdist` (the bridged Infotheo distribution); snake_case. | keep | Conformant. |
| `guess_joint_fdist_marginal` | Lemma | match | The pair fdist is the `(guess,V2)`-marginal of the rich sample distribution; `_marginal` is a descriptive role tag. Snake_case. | keep | Conformant. |
| `guess_sample_fdist` | Definition | match | `guess_sample` + `_fdist`; the rich sample distribution. Snake_case. | keep | Conformant. |
| `guess_cinde_V2` | Lemma | match | States `… \|= guess_rv _\|_ V2 \| Sout` (conditional independence). `cinde` is the established infotheo name (`cinde_RV`); `V2` is a paper RV var. | keep | Reuses upstream `cinde` token; conformant. |
| `run_heap_agree_predictor` | Lemma | match | Snake_case; the run's heap agrees with the predictor's-footprint frame. Descriptive, no abbreviation. | keep | Conformant. |
| `guess_fdist_success_le` | Lemma | match | Statement is `guess_fdist_success <= card_msg%:R^-1`; `_le` correctly states `<=`. Snake_case. | keep | Suffix matches a genuine `<=` (G001). |
| `guess_sdistr_success_le` | Lemma | match | Statement is `guess_sdistr_success <= card_msg%:R^-1`; `_le` correct. `sdistr` is the established SSProve type token. | keep | Suffix matches role; conformant. |
| `guess_V2_cond_le` | Lemma | match | Statement is `\`Pr[ V2 = a \| Sout = s ] <= card_msg%:R^-1`; `_le` correct, `_cond` = conditioned, `V2` paper RV. | keep | Suffix matches `<=`; conformant. |
| `guess_advantage_eq` | Lemma | match | States `\| … \| = AdvantageE …` (equation); `_eq` correct. Snake_case. | keep | Suffix matches role. |
| `guess_advantage_le` | Lemma | match | States `AdvantageE … <= 2%:R * epsilon_cpa`; `_le` correct. | keep | Suffix matches `<=`. |
| `dsdp_alice_secrecy_leak_S` | Theorem | match | Snake_case; `dsdp_alice_secrecy` main symbol + `_leak_S` condition (the leaked-output variant). `S` is the paper output var. | keep | Conformant; the variant tag is meaningful and grounded. |
| `cinde_diagonal_bound` | Lemma | match | (`lib/extra_proba.v`) States `Pr P [set t \| X t == Y t] <= m%:R^-1`; `cinde` upstream token, `diagonal` = the equality event, `_bound` role. Snake_case. | keep | Conformant; descriptive. |
| `Pr_dsdp_sol_uniform_ring` | Lemma | match | (`dsdp_entropy.v`) States a conditional `\`Pr[…\|…] = #\|R\|^-1`. `Pr_` is the established infotheo probability prefix; `_ring` carrier tag; `dsdp_sol_uniform` describes the uniform-on-solutions content. | keep | Conformant with infotheo `Pr_`-prefix convention. |
| `dsdp_fiber_card_ring` | Lemma | match | (`dsdp_entropy.v`) States `#\|dsdp_fiber_ring …\| = #\|R\|`; `_card` is the cardinality suffix (allowlisted in F001), `_ring` carrier. | keep | Suffix matches role. |
| `dsdp_advantage_derived_leak_S` | Lemma | match | (`dsdp_indcpa_security.v`) `dsdp_advantage` main symbol + `_derived` + `_leak_S` variant; snake_case. | keep | Conformant; variant tag grounded. |
| `id_s_get` | Definition | match | (`dsdp_game_code.v`) `id_` oracle prefix, `_s_get` reads the leaked S; mirrors the pre-blueprint `id_v2_get`. Snake_case. | keep | Conformant; matches the sibling oracle-id family. |
| `real_game_leak_S` | Definition | match | (`dsdp_indcpa_security.v`) Snake_case; `real_game` main symbol + `_leak_S` variant. | keep | Conformant. |
| `zero_game_leak_S` | Definition | match | (`dsdp_indcpa_security.v`) `zero_game` (all-zero endpoint) + `_leak_S`; snake_case. | keep | Conformant. |
| `guessing_challenger` | Definition | match | Snake_case noun phrase; the V_2-aware boolean challenger package. | keep | Conformant. |
| `predictor_guesser` | Definition | match | Snake_case noun phrase; the predictor package `Type`. | keep | Conformant. |

---

## Group B — fdist ↔ SDistr bridge (inventory §B)

| Name | Kind | Verdict | Why | Suggestion | Reason |
|---|---|---|---|---|---|
| `sdistr_to_fdist` | Definition | match | `X_to_Y` conversion (subdistr → fdist); `to` total-conversion form, snake_case. | keep | Conformant conversion name. |
| `sdistr_to_fdistE` | Lemma | match | `sdistr_to_fdist u = distr.mu mu u` — a defining rewrite equation; `E` suffix correct. | keep | `E` matches a rewrite equation (G001). |
| `Pr_sdistr_to_fdist` | Lemma | match | `Pr (sdistr_to_fdist) E = distr.pr mu …`; `Pr_` prefix names the head symbol (infotheo convention). | keep | Conformant. |
| `dmargin_comp` | Lemma | match | `dmargin h (dmargin g mu) = dmargin (h \o g) mu`; `dmargin` head symbol + `_comp` (composition). Snake_case. | keep | Conformant. |
| `dlet_dmargin_eq` | Lemma | match | `dlet g (dmargin f mu) = dlet (… ) mu` — an equation; `_eq` suffix correct, head symbols `dlet`/`dmargin`. | keep | Suffix matches role. |
| `Pr_fst_map` | Lemma | match | `Pr_fst (x ← c ;; ret (f x)) = dmargin f (Pr_fst c)`; `Pr_fst` head + `_map` (pushforward). Snake_case. | keep | Conformant. |
| `Pr_fdistmap_pre` | Lemma | match | `Pr (fdistmap g p) E = Pr p [set a \| g a \in E]` (probability of a preimage); `Pr_fdistmap` head + `_pre` (preimage). | keep | Conformant; descriptive. |
| `fdistmap_bij_unif` | Lemma | match | `fdistmap` head + `bij` (bijection hypothesis) + `unif` (uniform); snake_case. `unif` is the established infotheo/mathcomp shortening (`fdist_uniform`). | keep | Conformant; `unif` is a standard token, not semantic-stripping. |
| `mean1_eq1` | Lemma | match | A mass/mean-equals-1 fact; `mean1` + `_eq1` (`1` = unit suffix). Snake_case. | keep | Suffix matches role. |
| `fin_to_plain` | Definition | match | `X_to_Y` total conversion (`Mfin → plain AHE`); snake_case. | keep | Conformant conversion. |

---

## Group B — heap-frame / footprint (inventory §B)

| Name | Kind | Verdict | Why | Suggestion | Reason |
|---|---|---|---|---|---|
| `Pr_fst_agree_locs` | Lemma | match | `Pr_fst` head + `agree_locs` (agreement on a location set); snake_case, descriptive. | keep | Conformant. |
| `Pr_fst_closed` | Lemma | match | `Pr_fst` head + `_closed` (closed code); snake_case. | keep | Conformant. |
| `Pr_fst_put_invariant` | Lemma | match | `Pr_fst` head + `put_invariant` (invariance under a `#put`); snake_case, descriptive. | keep | Conformant. |
| `eq_in_dlet` | Lemma | match | Mirrors MathComp `eq_in_*` family (`eq_in_map`); pointwise-on-support equality lifted through `dlet`. Snake_case. | keep | Conformant; matches an upstream lemma family. |
| `dlet_const_unit` | Lemma | match | `dlet` head + `const_unit` (constant-unit kernel collapse); snake_case. | keep | Conformant. |
| `dmargin_fst_const` | Lemma | match | `dmargin_fst` head + `_const`; snake_case. | keep | Conformant. |
| `Pr_code_preserves` | Lemma | match | `Pr_code` head + `_preserves` (location preserved by the code); snake_case verb. | keep | Conformant. |

---

## Group B — challenger linking / oracle resolution (inventory §B)

| Name | Kind | Verdict | Why | Suggestion | Reason |
|---|---|---|---|---|---|
| `id_guess` | Definition | match | `id_` oracle-id prefix + `guess`; mirrors `id_game_run`/`id_v2_get`/`id_s_get`. Snake_case. | keep | Conformant with the oracle-id family. |
| `guesser_export` | Definition | match | The predictor's export `Interface`; `guesser` + `_export`. Snake_case. | keep | Conformant. |
| `guess_pair_challenger` | Definition | match | Snake_case noun phrase; the pair-returning challenger package. | keep | Conformant. |
| `guess_op` | Definition | match | `guess` + `_op` (the `opsig`); snake_case, `op` is the established SSProve token. | keep | Conformant. |
| `guess_resolved` | Definition | match | `guess` + `_resolved` (the closed resolved experiment, a `raw_code`); snake_case. | keep | Conformant. |
| `resolve_predictor_valid` | Lemma | match | `resolve_predictor` + `_valid`; `*_valid` is the SSProve upstream-class exception. | keep | Conformant (SSProve `_valid`). |
| `guess_resolved_par` | Lemma | match | States `guess_resolved = ( … resolve (par …) … )`; `_par` names the `par` form on the RHS. Snake_case. | keep | Conformant; descriptive of the RHS head. |
| `resolve_game_run` | Lemma | match | `resolve_game` head + `_run` (the run oracle); snake_case. | keep | Conformant. |
| `resolve_game_sget` | Lemma | partial | `resolve_game` + `_sget`; `sget` (= S get) is a tight join of two tokens but mirrors the oracle-id `id_s_get`. Could read `_s_get` for symmetry. | keep | Acceptable; matches the `id_s_get` oracle it resolves. |
| `resolve_game_v2get` | Lemma | partial | `resolve_game` + `_v2get`; same shape as `_sget`, mirrors `id_v2_get`. | keep | Acceptable; matches the `id_v2_get` oracle it resolves. |
| `guess_resolved_oracles` | Lemma | match | `guess_resolved` + `_oracles` (the four-oracle resolved form); snake_case. | keep | Conformant. |
| `guess_sdistr_success` | Definition | match | `guess` + `sdistr_success` (the subdistr-side true-mass); snake_case, `sdistr` established. | keep | Conformant. |
| `guess_fdist_success` | Definition | match | `guess` + `fdist_success` (the Infotheo-side diagonal mass); snake_case. | keep | Conformant. |

---

## Group B — denotation of the leaked output S (inventory §B)

| Name | Kind | Verdict | Why | Suggestion | Reason |
|---|---|---|---|---|---|
| `drun_sample_msg` | Lemma | **mismatch** | `drun` is a `Let` alias for `denote_run`; the `drun` abbreviation strips meaning (no-semantic-stripping rule). These are the step equations of `denote_run` on each `GC_*` ctor. | rename → `denote_run_sample_msg` | Spell `denote_run`; matches the spelled-out `denote_run_*` lemmas in the same file (`denote_run_distrE`, `denote_run_caps_*`). |
| `drun_sample_renc` | Lemma | **mismatch** | Same `drun` abbreviation. | rename → `denote_run_sample_renc` | Same as above. |
| `drun_put` | Lemma | **mismatch** | Same. | rename → `denote_run_put` | Same. |
| `drun_put_output` | Lemma | **mismatch** | Same. | rename → `denote_run_put_output` | Same. |
| `drun_let` | Lemma | **mismatch** | Same. | rename → `denote_run_let` | Same. |
| `drun_enc_hop` | Lemma | **mismatch** | Same. | rename → `denote_run_enc_hop` | Same. |
| `drun_ret` | Lemma | **mismatch** | Same. | rename → `denote_run_ret` | Same. |
| `gc_eq` | Lemma | partial | States `gc = GC_sample …` (an unfolding equation); `_eq` correct. `gc` is a `Let` alias for the game code; it is a local 2-letter binder, lighter than `drun`. | rename → `game_code_eq` | Optional. `gc` mirrors the constructor prefix `GC_`; acceptable, but spelling improves grep. Lower priority than the `drun_*`/`drc_*` renames. |
| `denote_output_termE` | Lemma | match | A defining/rewrite equation for `denote` on `output_term`; `E` suffix correct, head spelled `denote_output_term`. | keep | `E` matches a rewrite equation; head is spelled out. |
| `denote_run_distrE` | Lemma | match | A rewrite equation pushing `denote_run` through to the distribution; `E` correct, head `denote_run_distr` spelled out. | keep | `E` matches role; conformant. |
| `dsdp_output` | Definition | match | (`dsdp_program.v`) `dsdp` + `_output` (the spec function); snake_case. | keep | Conformant. |
| `alice_resultE` | Lemma | match | (`dsdp_program.v`) `alice_result = dsdp_output …` — a defining equation; `E` suffix correct. | keep | `E` matches a rewrite equation. |
| `denote_game_leak_S` | Definition | match | (`dsdp_game_code.v`) `denote_game` + `_leak_S` variant; head spelled out, snake_case. | keep | Conformant. |
| `denote_game_leak_S_raw` | Definition | match | Same head + `_raw` (the `raw_package` form before the validity wrapper). | keep | Conformant. |
| `denote_game_leak_S_valid` | Lemma | match | `*_valid` is the SSProve upstream-class exception; head spelled out. | keep | Conformant (SSProve `_valid`). |

---

## Group B — the capturing run, rich carrier (inventory §B)

| Name | Kind | Verdict | Why | Suggestion | Reason |
|---|---|---|---|---|---|
| `denote_run_caps_fst` | Lemma | match | `denote_run_caps` head + `_fst` (first-projection faithfulness); head spelled out, snake_case. `caps` = "captures" the rich carrier; borderline but consistently used as the family stem. | keep | Conformant; head spelled out. |
| `denote_run_caps_valid` | Lemma | match | Same head + `_valid` (SSProve exception). | keep | Conformant. |
| `denote_run_caps_preserves` | Lemma | match | Same head + `_preserves` (location preserved). Snake_case verb. | keep | Conformant. |
| `drc_sample_msg` | Lemma | **mismatch** | `drc` is a `Let`/stem alias for `denote_run_caps`; the abbreviation strips meaning, and clashes with the spelled-out `denote_run_caps_*` family in the same file. Step equations on each `GC_*` ctor. | rename → `denote_run_caps_sample_msg` | Spell `denote_run_caps`; aligns with `denote_run_caps_fst`/`_valid`/`_preserves`. |
| `drc_sample_renc` | Lemma | **mismatch** | Same `drc` abbreviation. | rename → `denote_run_caps_sample_renc` | Same. |
| `drc_put` | Lemma | **mismatch** | Same. | rename → `denote_run_caps_put` | Same. |
| `drc_let` | Lemma | **mismatch** | Same. | rename → `denote_run_caps_let` | Same. |
| `drc_hop` | Lemma | **mismatch** | Same. | rename → `denote_run_caps_enc_hop` | Same; spell `enc_hop` to match `drun`'s `GC_enc_hop` step and `denote_run_enc_hop`. |
| `drc_putout` | Lemma | **mismatch** | Same; `putout` also tightens `put_output`. | rename → `denote_run_caps_put_output` | Same; spell `put_output` to match `GC_put_output`. |
| `guess_resolved_caps` | Definition | match | `guess_resolved` + `_caps` (rich-carrier variant); consistent with the `denote_run_caps` family stem, snake_case. | keep | Conformant family stem. |
| `guess_full_code` | Definition | match | `guess_full` + `_code` (the rich observed tuple, a `raw_code`); snake_case. | keep | Conformant. |
| `guess_full_proj_code` | Lemma | match | States the `(guess,V2)`-projection of `guess_full_code = guess_joint_code`; `proj` = projection, `_code` carrier. Snake_case. | keep | Conformant. |
| `guess_triple_proj_code` | Lemma | match | The `(guess,V2,V3)`-projection reflects to the rich-run form; `triple` + `proj` + `_code`. | keep | Conformant. |
| `guess_inner` | Definition | match | `guess_inner` — the rich inner experiment with secrets fixed; snake_case noun. | keep | Conformant. |
| `guess_triple_peel` | Lemma | match | Peels the two outer secret samples off the triple-projection; `triple` + `_peel`. Snake_case, descriptive. | keep | Conformant. |

---

## Group B — the kernel crux, hard reflection (inventory §B)

| Name | Kind | Verdict | Why | Suggestion | Reason |
|---|---|---|---|---|---|
| `view_marginal_indep` | Lemma | match | The cipher-list view marginal is independent of the secrets; `view_marginal` + `_indep`. Snake_case, descriptive. | keep | Conformant. |
| `guess_run_cells` | Lemma | match | Every run heap carries the leaked-output and V_2 cells; `guess_run` + `_cells`. Snake_case. | keep | Conformant. |
| `guess_inner_v2v3_det` | Lemma | match | The `(V2,V3)`-marginal of `guess_inner` is deterministic; `v2v3` are paper RV vars, `_det` = determined. Snake_case. | keep | Conformant; RV-var exception applies to `v2v3`. |
| `guess_inner_kernel_form` | Lemma | match | Rewrites `guess_inner`'s guess-marginal into the `dlet`-of-kernel form; `kernel_form`. Snake_case. | keep | Conformant. |
| `guess_inner_out` | Lemma | match | Equal `dsdp_output` ⇒ equal guess-marginal; `_out` = the output. Snake_case. | keep | Conformant. |
| `Dview` | Let | **mismatch** | CamelCase term (`Let Dview : distr …`). MathComp lowercases terms/definitions; CamelCase is reserved for types / HB structures / modules. Also `D`+`view` glues a one-letter abbreviation onto `view`. | rename → `view_distr` | Lowercase snake_case for a term: `view_distr` (the cipher-list view distribution), parallel to `guess_sample_fdist`. |
| `Kguess` | Definition | **mismatch** | CamelCase term. Same rule as `Dview`: terms are lowercase. `K` (kernel) glued to `guess`. | rename → `guess_kernel` | Lowercase snake_case; `guess_kernel` reads as the output-conditioned guess kernel and matches the `guess_*` family. |
| `guess_inner_kernel_z` | Lemma | match | The guess-marginal of `guess_inner` is the kernel at the leaked output; `kernel` + `_z` (the conditioning output value, here named `z`). Snake_case. | keep | Conformant; `_z` is the argument tag. (If `Kguess` is renamed, the matching `guess_kernel` stem keeps this name coherent.) |
| `guess_triple_pr` | Lemma | match | The `(guess,V2,V3)` joint mass formula; `triple` + `_pr` (probability, established `pr`/`Pr` token). Snake_case. | keep | Conformant. |
| `guess_inner_kernel_form` | (dup. above) | — | Listed once. | — | — |

---

## Group B — random variables + determinism (inventory §B)

| Name | Kind | Verdict | Why | Suggestion | Reason |
|---|---|---|---|---|---|
| `guess_rv` | Definition | match | `guess` + `_rv` (the predictor's guess as a random variable); `rv` is the established infotheo RV token (`const_RV`, `{RV …}`). | keep | Conformant. |
| `V1` | Definition | match | Paper RV var (`V_1`); the math-notation exception. CamelCase-looking but it is a single capital-letter math symbol, not a multi-word term. | keep | Paper-faithful RV name; explicit project exception. |
| `V2` | Definition | match | Paper RV var `V_2`. | keep | Paper-faithful RV name. |
| `V3` | Definition | match | Paper RV var `V_3`. | keep | Paper-faithful RV name. |
| `U1` | Definition | match | Paper RV var `U_1`. | keep | Paper-faithful RV name. |
| `U2` | Definition | match | Paper RV var `U_2`. | keep | Paper-faithful RV name. |
| `U3` | Definition | match | Paper RV var `U_3`. | keep | Paper-faithful RV name. |
| `ir1_rv` | Definition | match | `ir1` (hop input-randomness 1) + `_rv`; snake_case, `rv` token. `ir` mirrors the protocol's hop-randomness naming. | keep | Conformant; consistent with the `_rv` family. |
| `ir2_rv` | Definition | match | `ir2` + `_rv`. | keep | Conformant. |
| `Sout` | Definition | match | Paper output RV `S` (the leaked scalar product), `out` distinguishing it from the type token `S`. Math-notation exception. | keep | Paper-faithful RV name. |
| `Zcond` | Definition | **mismatch** | CamelCase term (`Definition Zcond : {RV …}`). The RV-var exception covers single paper symbols (`V2`, `Sout`); `Zcond` is `Z`+`cond`, a glued two-token CamelCase term, so the lowercase-terms rule applies. | rename → `cond_view` (or `z_cond`) | Lowercase snake_case for the conditioning-view RV. `cond_view` reads clearest; `z_cond` keeps the paper `Z` symbol if that link matters. |
| `guess_S_determined` | Lemma | match | `Sout` equals the scalar-product spec; `guess_S` + `_determined`. `S` paper var. Snake_case. | keep | Conformant. |
| `de_val_nth_pushS` | Lemma | partial | `de_val_nth` head + `_pushS` (the `push_val`-successor step). `pushS` glues `push`+`S` (here `S` = successor, not the output) — mildly opaque against the `Sout` output `S`. | keep (optional → `de_val_nth_push_succ`) | Acceptable as a `push_val` step family; rename only if the `S`=successor / `S`=output clash is judged confusing. |
| `de_val_nth_push0` | Lemma | match | `de_val_nth` + `_push0` (`0` = the base index); snake_case, `0` is a standard suffix. | keep | Conformant. |
| `de_val_nth_pushrand` | Lemma | match | `de_val_nth` + `_pushrand` (`push_rand` transparency); snake_case. | keep | Conformant; mirrors the `push_rand` constructor. |
| `as_plain_Gplain` | Lemma | match | `as_plain (Gplain x) = x` — a defining equation through two head symbols. Borderline missing `E`, but it is the unfold of `as_plain` on the `Gplain` ctor (`mainSymbol_arg` shape). | keep (optional → `as_plain_GplainE`) | Acceptable; add `E` only if matching the `*E` rewrite-equation convention strictly. |
| `dhe_var` | Lemma | **mismatch** | `dhe` is a `Let` alias for `denote_he`; the abbreviation strips meaning. States `dhe e (HE_var n) = de_val_nth e n` (the `denote_he`-on-`HE_var` step). | rename → `denote_he_var` | Spell `denote_he`, matching the spelled-out `denote_*` lemmas; head + `HE_var` ctor arg. |
| `guess_inputs_indep` | Lemma | match | The seeded constant inputs are independent of the secrets; `guess_inputs` + `_indep`. Snake_case. | keep | Conformant. |
| `cpr_eq_drop_indep` | Lemma | match | Drops an independent conditioning RV from a `cpr_eq`; `cpr_eq` head (infotheo conditional-Pr token) + `drop_indep`. Snake_case. | keep | Conformant; reuses the `cpr_eq` infotheo token. |

---

## Group B — entropy-side, 1/m residual (inventory §B)

| Name | Kind | Verdict | Why | Suggestion | Reason |
|---|---|---|---|---|---|
| `cardpp` | Lemma | **mismatch** | `card`+`pp` glues an opaque `pp` ("plaintext pair") with no underscore; semantic-stripping. States `#\|(plain×plain)\| = (…).-1.+1`. MathComp would use `card_` + a spelled main symbol. | rename → `card_plain_pair` | `card_` is allowlisted (F001) and spells the carrier; matches `card_prod`-style naming. |
| `Htail2_abs` | Lemma | **mismatch** | Top-level `Lemma H…` — `H` is the local-hypothesis convention, so a top-level `Htail2_abs` is suspect. Also `_abs` ("abstracted over the predictor code") is a semantic-stripping abbreviation. | rename → `tail_collapse_pred_abstract` (or `Pr_code_tail_collapse`) | Drop the `H` prefix; spell `abs`. The lemma states the post-run tail-collapse of the value-marginal abstracted over the predictor code `pc`. |
| `guess_VarRV_uniform` | Lemma | partial | States `\`p_[% V2, V3] = fdist_uniform cardpp`; `_uniform` role tag fine. `VarRV` is CamelCase glued — but it deliberately mirrors the infotheo `RV`/`VarRV_r` token family (see `Pr_dsdp_sol_uniform_ring`'s `VarRV_r`). | keep | Acceptable: `VarRV` reuses the established infotheo RV-bundle token; renaming would break the parallel with the entropy-side `VarRV_r`. (If `cardpp` is renamed, update the argument.) |
| `guess_VarRV_cond_uniform` | Lemma | partial | Conditional version: `\`Pr[ [%V2,V3]=… \| … ] = #\|plain\|^-1`; `_cond_uniform` role tags correct. Same `VarRV` token note. | keep | Acceptable for the same reason. |
| `guess_V2_cond_Sout` | Lemma | match | `\`Pr[ V2 = a \| Sout = s ] = #\|plain\|^-1`; `V2` paper var, `_cond_Sout` names the conditioning RV. Snake_case. | keep | Conformant. |
| `dsdp_fiber_ring` | Definition | match | (`dsdp_entropy.v`) `dsdp_fiber` + `_ring` carrier; the ring-generic solution set. Snake_case. | keep | Conformant. |

---

## Group B — composition / final assembly (inventory §B)

| Name | Kind | Verdict | Why | Suggestion | Reason |
|---|---|---|---|---|---|
| `real_game` | Let | match | Snake_case; the real endpoint game at the section parameters. | keep | Conformant. |
| `guess_sdistr_success_real` | Definition | match | `guess_sdistr_success` + `_real` variant; snake_case, `sdistr` established. | keep | Conformant. |
| `guess_reduction` | Let | match | `guess` + `_reduction` (the IND-CPA reduction distinguisher); snake_case. | keep | Conformant. |
| `guess_reduction_valid` | Lemma | match | `*_valid` SSProve exception; head spelled out. | keep | Conformant (SSProve `_valid`). |
| `real_game_valid` | Lemma | match | `*_valid` SSProve exception; head spelled out. | keep | Conformant (SSProve `_valid`). |
| `game_valid` | Lemma | match | `*_valid` SSProve exception. | keep | Conformant (SSProve `_valid`). |

---

## Recommended renames

`drun_*` family (spell `denote_run`):

- `drun_sample_msg`  → `denote_run_sample_msg`
- `drun_sample_renc` → `denote_run_sample_renc`
- `drun_put`         → `denote_run_put`
- `drun_put_output`  → `denote_run_put_output`
- `drun_let`         → `denote_run_let`
- `drun_enc_hop`     → `denote_run_enc_hop`
- `drun_ret`         → `denote_run_ret`

`drc_*` family (spell `denote_run_caps`):

- `drc_sample_msg`  → `denote_run_caps_sample_msg`
- `drc_sample_renc` → `denote_run_caps_sample_renc`
- `drc_put`         → `denote_run_caps_put`
- `drc_let`         → `denote_run_caps_let`
- `drc_hop`         → `denote_run_caps_enc_hop`
- `drc_putout`      → `denote_run_caps_put_output`

`dhe` abbreviation (spell `denote_he`):

- `dhe_var` → `denote_he_var`

CamelCase terms (lowercase per MathComp):

- `Dview` → `view_distr`
- `Kguess` → `guess_kernel`
- `Zcond` → `cond_view` (or `z_cond` to keep the paper `Z`)

Semantic-stripping / suspect-prefix:

- `cardpp` → `card_plain_pair`
- `Htail2_abs` → `tail_collapse_pred_abstract` (drop the `H` prefix; spell `abs`)

Optional / lower priority (raise only if the maintainer agrees):

- `gc_eq` → `game_code_eq` (spell the `gc` Let alias)
- `de_val_nth_pushS` → `de_val_nth_push_succ` (avoid `S`=successor vs `S`=output clash)
- `as_plain_Gplain` → `as_plain_GplainE` (strict `E` rewrite-equation suffix)

## Counts

- **match:** 73
- **partial:** 9 (`guess_success_sdistr_eq_fdist`, `resolve_game_sget`,
  `resolve_game_v2get`, `gc_eq`, `de_val_nth_pushS`, `as_plain_Gplain`,
  `guess_VarRV_uniform`, `guess_VarRV_cond_uniform`) — kept; two of these
  (`gc_eq`, `de_val_nth_pushS`, `as_plain_Gplain`) also appear as optional renames
- **mismatch / rename:** 19 required (7 `drun_*`, 6 `drc_*`, `dhe_var`, `Dview`,
  `Kguess`, `Zcond`, `cardpp`, `Htail2_abs`) + 3 optional
- **out-of-scope:** 4 (the Group-A pre-blueprint references)
