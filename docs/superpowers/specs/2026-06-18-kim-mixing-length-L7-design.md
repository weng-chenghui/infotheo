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
| 2 | S5 285->286 fix extent | comment-only: fix S5 source comments + slide; leave S5 Rocq wiring at 285 |
| 3 | Deliverable tier | (b) numeric lemma + concrete `SecurityWitness`, exposing `sw_bound_eps < 2^-40` |
| 4 | Bias | `eps_repo = 1/100` (P(no-cut) = `0.19`), `lambda2 = 1/80`, `L = 7` |
| 5 | Single-cut leak | include the paper-faithful `var_dist = 1/50` at `(eps=1/100, L=1)` |
| 6 | File location | extend `instances/kim2025/five_card_kim.v` Section 6 (already fixes the concrete-bias regime) |
| 7 | Proof technique | square both sides: `sqrt5 * (1/80)^7 < 2^-40` reduces to `5*2^80 < 80^14` |
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

with `5*2^80 = 9.90e24 < 80^14 = 4.40e26` (exact nat inequality, `vm_compute`).

Cross-check used during design: under the same strict convention, the smallest
`L` for S5 (`alpha = 181/200`) is `286`, not `285`; at `L=285` the bound is
`9.87e-13 > 2^-40`. Hence decision 2.

## 5. Artifacts (proposed lemma chain)

All in `five_card_kim.v` Section 6 unless noted. Names provisional, subject to
the I001 naming rule.

1. `kim_lambda2_at_centi : kim_lambda2 (eps := 1/100) = 1/80`.
   Reduces the real definition; parallels existing `kim_lambda2_at_zero`.
2. `kim_bound_centi : Num.sqrt 5%:R * (kim_lambda2 (1/100)) ^+ 7 < 2%:R ^- 40`.
   Leaf `5*2^80 < 80^14` via square-both-sides; the only purely-numeric step.
3. `kim_security_witness_centi : SecurityWitness R FiveCardKim_M`
   `:= fc_kim_security_witness <Hlt Hgt Hspec at 1/100> 7`.
   Concrete witness over the real biased deal.
4. `kim_deal_centi_lt : forall s, var_dist (fdistmap (eval s) (real deal at 1/100, L=7))
   (fdist_uniform (card_ord 5)) < 2^-40`.
   Top-level deliverable; composes the witness `sw_bound` field with
   `kim_bound_centi`.
5. `kim_one_cut_centi : forall s, var_dist (fdistmap (eval s) (real deal at 1/100, L=1))
   (fdist_uniform (card_ord 5)) = 1/50`.
   Paper-faithful single biased cut; from `kim_var_dist_exact` at `L=1`.

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

- S5 comments: correct `rigidity_s5_instance.v:23,214` and the
  `s5_spectral_certificate.py` doc line from "L=285 gives var_dist < 2^-40" to
  "L=285 gives var_dist < 2^-39; L=286 gives var_dist < 2^-40". The descriptive
  comment at `:13` (which records the wired witness at 285) stays. The Rocq
  wiring `s5_security_witness_schreier R 285` (`s5_profile.v:53`,
  `rigidity_s5_instance.v:386`) is left unchanged per decision 2.
- Slide `wadtSep17/slides.tex`, page 16 list:
  - Kim line: relabel bias to "P(no-cut) = 0.19 (deviation 1/100)"; keep `L=7`,
    `var_dist < 2^-40`.
  - S5 line: `L=285 -> L=286` (the threshold achieving `var_dist < 2^-40`).
  - Add a one-line footnote: den Boer and Kim bounds are machine-checked
    in-kernel; S5 and S5xS5 bounds are verified externally (Python SOS
    certificate plus an imported axiom).

Open point for user confirmation: the slide S5 line will read `L=286` while the
S5 Rocq instance remains wired at `L=285` (which achieves `var_dist < 2^-39`).
This gap is documented in the corrected comment; flagged here so it is a
conscious choice.

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
  repeated shuffles, the `eps_repo = 1/5 - eps_paper` notation mapping); confirm
  the "in-kernel vs externally verified" slide labeling is accurate.

## 9. Success criteria

- `five_card_kim.vo` compiles; `Print Assumptions kim_deal_centi_lt` shows no
  Kim-specific axiom (only standard/boolp).
- `kim_lambda2_at_centi`, `kim_bound_centi`, `kim_deal_centi_lt`,
  `kim_one_cut_centi` all `Qed`.
- Audit targets A, B, C pass with no unresolved error-severity finding.
- Slide rebuilds; Kim line, S5 line, and footnote are mutually consistent.

## 10. Risks

- Section plumbing: how `eps` and `L` are bound in Section `kim_concrete` may
  require instantiating the section or using the explicit-argument lemma forms
  (`fc_kim_security_bound` takes `eps` as an argument). Audit B resolves.
- nat/R bridge for the squared inequality (`natrX`, `ler_pXn2l`/`ltr_pXn2`,
  `sqr_sqrtr`) is standard but fiddly; budget proof iterations accordingly.
- `80^14 ~ 4.4e26` bignum `vm_compute` cost; expected fine, confirm by a check.
```
