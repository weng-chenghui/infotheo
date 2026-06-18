# Kim Mixing-Length L=7 Formalization — Design Spec

- Date: 2026-06-18
- Repo: infotheo-pgg (branch `pgg-smc`)
- Status: design, pre-implementation
- Owner: Chenghui Weng

## 1. Goal

Prove a code-fixed Kim mixing length `L = 7`, at bias deviation `1/100`
(no-cut probability `0.19`), establishing

```
forall s, var_dist (fdistmap (eval s) (real biased-cut deal at eps=1/100, L=7))
                   (fdist_uniform (card_ord 5)) < 2^-40
```

fully in-kernel: no axiom, no external certificate. This closes the final
numeric closeness step that S5 and S5xS5 leave at comment level, and gives Kim
the only fully machine-checked mixing bound among the four instances.

## 2. Why this is non-trivial and worth doing

- Kim is the repeated biased cyclic cut on `C_5` (Kim and Cetinkaya,
  "Confidentiality in a Card-Based Protocol Under Repeated Biased Shuffles",
  arXiv:2511.05111). The paper keeps the bias symbolic; repeated shuffles are
  its object, so the word length `L` (repeated cuts) is exactly the paper's
  quantity.
- `kim_lambda2 = (5/4)*|eps|` is an exact closed-form second eigenvalue
  (`five_card_kim.v:370`), because the circulant weight matrix has closed-form
  spectrum. Contrast S5, whose second eigenvalue is bounded by `alpha=181/200`
  via an external sum-of-squares certificate imported as the axiom
  `s5_rayleigh_Q2_R` (`s5_mixing.v:188`).
- The witness `fc_kim_security_witness L` already proves
  `var_dist <= sqrt 5 * kim_lambda2^L` over the real weight distribution
  (`kim_spectral_convergence`, `:420-423`). What is missing is a concrete `L`
  with `sqrt 5 * kim_lambda2^L < 2^-40`.

## 3. Locked decisions

| # | Decision | Choice |
|---|---|---|
| 1 | Closeness convention | `var_dist < 2^-40` (strict, un-halved L1) |
| 2 | S5 285->286 fix extent | align all to L=286 (the value correct under decision 1): bump the 2 Rocq wirings, the 4 comments, the Python doc comment, and the slide |
| 3 | Deliverable tier | (b) numeric lemma + concrete `SecurityWitness`, exposing `sw_bound_eps < 2^-40` |
| 4 | Bias | `eps_repo = 1/100` (P(no-cut) = `0.19`), `lambda2 = 1/80`, `L = 7` |
| 5 | Single-cut leak | include the paper-faithful `var_dist = 1/50` at `(eps=1/100, L=1)` |
| 6 | File location | extend `instances/kim2025/five_card_kim.v` Section 6 (already fixes the concrete-bias regime) |
| 7 | Proof technique | square both sides: `sqrt5 * (1/80)^7 < 2^-40` reduces to `5*2^80 < 80^14`, nat leaf by `lia`/`zify` (not `vm_compute`) |
| 8 | Slide epistemic footnote | mark den Boer and Kim as in-kernel; S5 and S5xS5 as externally verified (Python SOS certificate plus axiom, which is solid) |
| 9 | Adversarial audit | run after this spec; three targets (math, Rocq typecheck, honesty/non-vacuity) |

## 4. The mathematics (numerically verified)

At `eps_repo = 1/100`: `lambda2 = (5/4)*(1/100) = 1/80`.

Smallest `L` with `sqrt 5 * (1/80)^L < 2^-40` is `7`:

| L | `sqrt5 * (1/80)^L` | vs `2^-40 = 9.09e-13` |
|---|---|---|
| 6 | `8.53e-12` | fails (>=) |
| 7 | `1.07e-13` | holds (<) |

Square-both-sides reduction (both sides non-negative, `(sqrt 5)^2 = 5` exactly):

```
sqrt 5 * (1/80)^7 < 2^-40
  <->  5 * (1/80)^14 < 2^-80
  <->  5 * 2^80 < 80^14
```

with `5*2^80 = 6.04e24 < 80^14 = 4.40e26` (exact: `5*2^80 =
6,044,629,098,073,145,873,530,880`). The `nat` leaf is NOT `vm_compute`-tractable
(mathcomp `nat` is unary, times out > 130s); it is closed by `lia` with `zify`.

Cross-check used during design: under the same strict convention, the smallest
`L` for S5 (`alpha = 181/200`) is `286`, not `285`; at `L=285` the bound is
`9.87e-13 > 2^-40`. Hence decision 2.

## 5. Artifacts (proposed lemma chain)

All in `five_card_kim.v` Section 6 unless noted. Names provisional, subject to
the I001 naming rule.

Prerequisite import (near the import block, lines 14-24):
`Require Import Lia.` and `From mathcomp Require Import zify.` (no scope conflict,
no added axioms; needed for the nat leaf in artifact 2).

1. `kim_lambda2_at_centi : kim_lambda2 (1/100) = 1/80`.
   Propositional, not definitional (`5/4*(1/100)` is not defeq `1/80`); proved by
   `rewrite /kim_lambda2 ger0_norm` then cross-multiply. Parallels `kim_lambda2_at_zero`.
2. `kim_bound_centi : Num.sqrt 5%:R * (kim_lambda2 (1/100)) ^+ 7 < 2%:R ^- 40`.
   Square both sides via `ltr_pXn2r` + `sqr_sqrtr` (`(sqrt 5)^2 = 5`), collapse
   exponents (`exprMn`, `exprVn`), cross-multiply (`ltr_pdivlMr`/`ltr_pdivrMr`),
   bridge to nat (`natrX`, `natrM`, `ltr_nat`); leaf `(5*2^80 < 80^14)%N` by `lia`.
   The only purely-numeric step.
3. `kim_security_witness_centi : SecurityWitness R FiveCardKim_M`
   `:= @fc_kim_security_witness R (1/100) Hlt Hgt Hspec 7`.
   No section instantiation: after `Section kim_security` closes, `eps` and the
   three hypotheses are explicit arguments. Concrete witness over the real deal.
4. `kim_deal_centi_lt : forall s, var_dist (fdistmap (fun sigma => sigma s)
   (sw_rho_dist kim_security_witness_centi)) (fdist_uniform (card_ord 5)) < 2^-40`,
   where `sw_rho_dist = rho_from_words_weighted 3 4 7 fc_kim_sigmas
   (kim_weight_dist Hlt Hgt)` is the real biased deal. Top-level deliverable;
   composes the witness `sw_bound` field with `kim_bound_centi` via `le_lt_trans`.
5. `kim_one_cut_centi : forall s, var_dist (fdistmap (fun sigma => sigma s)
   (rho_from_words_weighted 3 4 1 fc_kim_sigmas (kim_weight_dist Hlt Hgt)))
   (fdist_uniform (card_ord 5)) = 1/50`.
   Paper-faithful single biased cut; from `kim_var_dist_exact` at `L=1`
   (`(8/5)*(1/80) = 1/50`).

## 6. Non-vacuity requirements (load-bearing guards)

The deliverable is `kim_deal_centi_lt` (a `var_dist` security statement over the
real distribution), never a bare nat lemma. A standalone `(5*2^80 < 80^14)%N`
would be a true-but-disconnected fact and is explicitly rejected as the
deliverable. Three guards, each an audit checkpoint:

- G1. The witness `sw_bound` field bounds the real endpoint: `kim_spectral_convergence`
  is stated over `W := kim_weight_dist`, the actual biased fdist on `'I_5`
  (`five_card_kim.v:230,267`), not a placeholder distribution.
- G2. The instance is satisfiable, not vacuously typed: `Hlt (1/100 < 1/5)`,
  `Hgt (-4/5 < 1/100)`, `Hspec (|1/100| < 4/5)` are discharged with real proofs,
  so the witness does not rest on a false premise.
- G3. `lambda2 = 1/80` is computed, not assumed: `kim_lambda2_at_centi` reduces
  the real `kim_lambda2` definition.

`kim_bound_centi`'s nat leaf `5*2^80 < 80^14` is reached only inside proving
`sqrt 5 * (1/80)^7 < 2^-40`, which bounds the witness `sw_bound_eps`, which via
the `sw_bound` field bounds the real `var_dist`.

## 7. Companion edits (outside Rocq)

- S5: align everything to L=286, the value correct under decision 1 (at L=285
  the bound is `var_dist ~9.87e-13 > 2^-40`; at L=286 it is `~8.93e-13 < 2^-40`).
  - Bump the 2 Rocq wirings `s5_security_witness_schreier R 285 -> 286`
    (`s5_profile.v:53`, `rigidity_s5_instance.v:386`). The witness is parametric
    in L, so only `sw_bound_eps` changes (`sqrt5*alpha^286`); no types change and
    no proof breaks. Recompiles `s5_profile.vo`, `rigidity_s5_instance.vo`, and
    their dependents.
  - Update the 4 comments `285 -> 286` (`rigidity_s5_instance.v:13,23,212,214`);
    the `var_dist < 2^-40` claim then holds.
  - Update the doc comment in `s5_spectral_certificate.py` `285 -> 286`. The SOS
    certificate itself is L-independent (it certifies `alpha=181/200`), so only
    the "targeting 40-bit mixing at L=285" line changes.
- Slide `wadtSep17/slides.tex`, page 16 list:
  - Kim line: relabel bias to "bias eps = 1/100 (P(no-cut) = 0.19)" (the paper's
    own eps is this deviation, so 1/100 is kept and the no-cut probability is
    added for clarity); keep `L=7`, `var_dist < 2^-40`.
  - S5 line: `L=285 -> L=286` (the threshold achieving `var_dist < 2^-40`).
  - Add a one-line footnote: den Boer and Kim bounds are machine-checked
    in-kernel; S5 and S5xS5 bounds are verified externally (Python SOS
    certificate plus an imported axiom).

S5 code and comments are now aligned to L=286, so the slide, comments, and wired
instance all state the same correct value.

## 8. Adversarial audit plan (run after this spec, before user review)

Three independent targets:

- A. Math correctness. Independently re-derive `lambda2 = 1/80`, that `L=7` is
  the minimal `L` for `var_dist < 2^-40`, the square-both-sides equivalence, and
  `5*2^80 < 80^14`. Confirm `L=6` fails. Confirm the S5 `285 vs 286` finding.
- B. Rocq typecheck against live code. Validate the proposed lemma shapes
  against the live `five_card_kim.v`: the `kim_lambda2` definition and how `eps`
  and `L` are bound in the target Section (Variable vs explicit argument); the
  `fc_kim_security_witness` signature and the `SecurityWitness` `sw_bound_eps`
  and `sw_bound` field types; that `Hlt/Hgt/Hspec` are dischargeable at `1/100`;
  that no step needs `Admitted`; that `80^14` is `vm_compute`-tractable.
- C. Honesty and non-vacuity. Confirm G1-G3; confirm the deliverable is the
  `var_dist` statement; confirm faithfulness to arXiv:2511.05111 (symbolic bias,
  repeated shuffles, the notation mapping `eps_repo = eps_paper = 1/100` with
  `P(no-cut) = 1/5 - eps = 0.19`, per the paper Assumption 2 eqs 7-8); confirm
  the "in-kernel vs externally verified" slide labeling is accurate.

## 9. Success criteria

- `five_card_kim.vo` compiles; `Print Assumptions kim_deal_centi_lt` shows no
  Kim-specific axiom (only standard/boolp).
- `kim_lambda2_at_centi`, `kim_bound_centi`, `kim_deal_centi_lt`,
  `kim_one_cut_centi` all `Qed`.
- Audit targets A, B, C pass with no unresolved error-severity finding.
- `s5_profile.vo` and `rigidity_s5_instance.vo` recompile cleanly at L=286.
- Slide rebuilds; Kim line, S5 line, and footnote are mutually consistent.

## 10. Risks (status after audit)

- Section plumbing: RESOLVED. No section instantiation; after `Section
  kim_security` closes, `eps` and the three hypotheses are explicit arguments
  (`@fc_kim_security_witness R (1/100) Hlt Hgt Hspec 7`).
- nat leaf: RESOLVED. `(5*2^80 < 80^14)%N` is NOT `vm_compute`-tractable (mathcomp
  `nat` is unary, times out > 130s). Closed by `lia` after `Require Import Lia.`
  and `From mathcomp Require Import zify.` (no scope conflict, no added axioms).
- nat/R bridge lemmas: known good (`ltr_pXn2r`, `sqr_sqrtr`, `exprMn`, `exprVn`,
  `ltr_pdivlMr`, `ltr_pdivrMr`, `natrX`, `natrM`, `ltr_nat`). The Rocq auditor
  assembled the full chain end-to-end (310ms), no `Admitted`, no new axiom.

## 11. Audit outcome

Both adversarial auditors completed; corrections folded into this spec.

- Math + honesty (independent re-derivation + paper fetch): the load-bearing math
  is all correct (`lambda2=1/80`; `L=7` minimal, `L=6` fails; square-both-sides;
  `5*2^80 < 80^14`; S5 285-vs-286; non-vacuity G1-G3; deliverable load-bearing;
  `kim_one_cut = 1/50`). Caught and fixed: the `6.04e24` gloss (was `9.90e24`) and
  the bias mapping (`eps_repo = eps_paper = 1/100`, P(no-cut) = 0.19).
- Rocq typecheck (rocq-mcp, read-only): FEASIBLE-WITH-CHANGES. Built and closed
  every lemma end-to-end. Required change: `vm_compute` -> `lia`/`zify` for the
  nat leaf (folded into decision 7 and sections 5, 10). Confirmed the witness
  signature, hypothesis-discharge tactics, and statement shapes (folded into
  section 5). Estimate: ~30-40 proof lines + 2 import lines, Low-Medium, no
  `Admitted`, no new axiom.
