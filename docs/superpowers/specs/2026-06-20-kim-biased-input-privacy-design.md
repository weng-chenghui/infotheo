# Kim biased-cut input privacy — design spec

- Date: 2026-06-20
- Status: approved (brainstorming), ready for implementation plan
- Target: one new file `pgg-smc/instances/kim2025/kim_input_privacy.v`

## 1. Goal

Prove, for the Kim five-card instance under its actual biased cut, that a
partial card view leaks almost nothing about the individual inputs `(a, b)`
beyond the computed output `a && b`:

```
kim_input_private (A) : cond_mutual_info (`p_ [% kim_inputs, kim_view A, kim_secret]) <= kim_leak_bound eps
```

with `kim_leak_bound eps = O(eps^2)` and `kim_leak_bound 0 = 0`, recovering den
Boer's exact zero in the unbiased limit.

## 2. Background: two leakage axes

These are distinct and must not be conflated:

- **View-vs-output** (`I(Secret ; View)`): how much a partial reveal tells about
  the result `a && b`. Done: `five_card_leakage.v` (`leak_k1..leak_k5`),
  reused by `kim_secrecy.v` under the uniform model.
- **Output-to-input** (`I(Inputs ; View | Secret)`): given the result, how much a
  reveal tells about the individual inputs. Done for den Boer:
  `den_boer_encoding.v` `den_boer_input_private` proves it is exactly `0` under
  the uniform cut. This spec extends that axis to Kim's biased cut.

den Boer's exact zero rests on `den_boer_view_count_eq`: two inputs with the
same output are related by a cyclic rotation of the arrangement, and a uniform
cut averages over all rotations equally, so they deal the same view
distribution. Kim's biased weight breaks that symmetry, so the conditional
independence becomes approximate.

## 3. Scope and non-goals

- In scope: Kim only, one file.
- Out of scope: S5 and S5xS5. They are no-input dealt-secret schemes, so
  `I(Inputs ; View | Secret)` has no referent; the matching property
  (sub-threshold view leaks nothing about the secret) is already proved by
  `s5_view_secrecy` / `s5_trace_secrecy` / `s5x5_*`. No pointer comments added.
- Out of scope: a generic continuity (Fannes-type) lemma in infotheo; the bound
  is obtained by an explicit chi-square route instead.

## 4. File header (verbatim)

```coq
(******************************************************************************)
(* Den Boer / Kim Five-Card Trick: input privacy under a biased cut           *)
(*                                                                            *)
(* Bounds, as conditional mutual information in bits, the information a        *)
(* partial reveal of the dealt five-card row carries about the individual     *)
(* inputs (a, b) GIVEN the computed output a && b, when the cyclic cut is      *)
(* Kim's biased W_eps (w_0 = 1/5 - eps; w_k = 1/5 + eps/4, k = 1..4) rather    *)
(* than uniform.                                                              *)
(*                                                                            *)
(* Mechanism. Two inputs with the same output (e.g. (0,1) and (1,0)) differ   *)
(* only by a cyclic rotation of the arrangement. A uniform cut averages over  *)
(* all rotations equally, so the rotation is invisible and equal-output       *)
(* inputs deal the SAME view distribution: input privacy is exact,            *)
(* I(Inputs ; View | Secret) = 0 (den Boer). The biased weight favours some    *)
(* cut positions, reweighting the rotation, so equal-output inputs deal        *)
(* slightly different view distributions, and that gap is the leakage.         *)
(*                                                                            *)
(* Order of magnitude. The per-view probability gap is first order in the     *)
(* bias, O(eps), tracking || W_eps - uniform ||. The leaked information is a   *)
(* KL / chi-square quantity, second order in that gap, so                      *)
(* I(Inputs ; View | Secret) <= kim_leak_bound eps = O(eps^2), with           *)
(* kim_leak_bound 0 = 0, recovering den Boer's exact zero.                     *)
(*                                                                            *)
(* The leakage is carried entirely by the output-0 fibre {(0,0),(0,1),(1,0)}; *)
(* output 1 forces (a, b) = (1,1), leaving nothing to leak.                    *)
(******************************************************************************)
```

## 5. Construction: `kim_input_dist` and the random variables

- `kim_input_dist : R.-fdist Omega` over `Omega = bool * bool * 'I_5`: the
  product of the uniform law on `bool * bool` (fair inputs) and Kim's weight law
  `kim_weight_dist eps` on `'I_5`. Reuses `five_card_kim`'s `kim_weight_dist`
  and its positivity hypotheses.
- Section parameters: `eps : R`, `eps_lt_inv5 : eps < 5^-1`,
  `eps_gt_neg4inv5 : - (4 * 5^-1) < eps` (names reused verbatim from
  `five_card_kim`).
- Random variables over `kim_input_dist`, reusing the den Boer / five-card pure
  functions: `kim_inputs` (pair `(a,b)`), `kim_secret` (`a && b`),
  `kim_view A` (the colours read at positions `A`).

## 6. Definitions

- `chi2_div p q := \sum_v (p v - q v)^2 / q v` (general, reusable; no instance
  prefix).
- `kim_leak_bound eps`: an explicit closed form of shape `C * eps^2 / (5^-1 - `
  `|eps|)`, with `C` a concrete log2 / rational constant pinned during the
  proof. Properties: `kim_leak_bound 0 = 0`, `0 <= kim_leak_bound eps`, finite
  for `|eps| < 1/5` (Kim's positivity regime).

## 7. Theorems

Main results (bare):

- `kim_input_private (A : seq nat) :
    cond_mutual_info (`p_ [% kim_inputs, kim_view A, kim_secret]) <= kim_leak_bound eps`.
- `kim_input_private0 :` at `eps = 0`, the conditional mutual information is `0`
  (cross-checked to agree with `den_boer_input_private`).

Auxiliary (`Local` / `Fact` / `Let`):

- `le_div_chi2 : D(p || q) <= chi2_div p q / ln 2` (from `ln_id_cmp`).
- `kim_cond_mutual_infoE :` `cond_mutual_info = (3/4) * cdiv1 ... false`.
- `cdiv1_secret_true0 :` `cdiv1 ... true = 0`.
- `kim_view_le :` per-view deviation `|q_x v - n_v/5| <= 2 * |eps|`.
- `kim_qbar_gt0 :` `qbar v > 0`.
- `kim_leak_bound0 :` `kim_leak_bound 0 = 0`.
- `kim_leak_bound_ge0 :` `0 <= kim_leak_bound eps`.

## 8. Proof strategy

1. `cond_mutual_infoE2`: `cond_mutual_info = \sum_(s : bool) PQR2 s * cdiv1 s`.
2. Singleton fibre: `cdiv1 true = 0` (`Secret = true` forces `Inputs = (1,1)`),
   so `cond_mutual_info = (3/4) * cdiv1 false`.
3. `cdiv1 false = \sum_x (1/3) * D(q_x || qbar)`, with
   `q_x v = \sum_(k in S_x v) W_eps k`, `qbar = avg_x q_x`.
4. Deviation: each `q_x v` and `qbar v` is within `2 * |eps|` of `n_v / 5`,
   using `den_boer_view_count_eq` for `|S_x v| = n_v` (orbit count, independent
   of `x` in the fibre); and `qbar v >= 1/5 - |eps| > 0`.
5. `le_div_chi2` plus steps 3 and 4 give `cdiv1 false <= C' * eps^2 / (5^-1 - |eps|)`;
   multiply by `3/4` to obtain `kim_leak_bound eps`.

`den_boer_view_count_eq` is pure cardinality (no distribution), so it transfers
to `kim_input_dist` unchanged; it is the reused combinatorial core.

## 9. New names (audited against mathcomp §10-14)

Definitions (snake_case, §13): `kim_input_dist`, `kim_inputs`, `kim_secret`,
`kim_view`, `chi2_div`, `kim_leak_bound`. All conform.

Main lemmas: `kim_input_private`, `kim_input_private0`. Intentional divergence
from `mainSymbol_suffixes`: descriptive, parallel to `den_boer_input_private`,
discoverable; the trailing `0` is the canonical "= 0 / at 0" suffix.

Auxiliary lemmas: `le_div_chi2` (predicate-first `le_`), `kim_cond_mutual_infoE`
(`E` equation suffix), `cdiv1_secret_true0` (`0` suffix), `kim_view_le`
(`le` for a `<=` bound), `kim_qbar_gt0` and `kim_leak_bound_ge0` (canonical
`_gt0` / `_ge0`), `kim_leak_bound0` (`0` suffix). All conform.

Hypotheses: `eps`, `eps_lt_inv5`, `eps_gt_neg4inv5` (meaningful, `_lt_` / `_gt_`
pattern, reused from `five_card_kim`).

All names clear the rocq-audit I-series (no `_lemma/_proof`, no drift tokens, no
five-plus components without a canonical suffix).

## 10. Tooling requirements

- Proving uses the `mathcomp-skills` skill (installed at
  `~/.claude/skills/mathcomp-skills`; prereqs verified: Rocq 9.0.0, mathcomp
  2.5.0, mathcomp-analysis 1.15.0) driven by the `rocq-mcp` 4-phase loop
  (`rocq_start` -> `rocq_query` -> `rocq_check` / `rocq_step_multi` -> apply
  once).
- After the file compiles: run `/mathcomp-review` on it and the
  `mathcomp-style-auditor` for idiom/style, then fix findings.
- Commits skip rocq-audit **Stage 2** (the LLM gate) via
  `ROCQ_AUDIT_BYPASS=fast git commit ...`. Stage 1 regex and the I-series still
  gate; the fast bypass is logged. Do not use the `Rocq-Audit-Skip-Stage2`
  trailer (broken on macOS bash 3.2).

## 11. Verification and axioms

- `make -j1 pgg-smc/instances/kim2025/kim_input_privacy.vo` (and via `rocq-mcp`
  during development).
- `Print Assumptions kim_input_private`: expect only the standard profile
  already present in `den_boer_encoding` / `five_card_leakage` (the boolp
  `funext` / `propext` / `cid` trio), no project axioms.

## 12. Execution order (spike-first)

1. `kim_input_dist` + RV bindings + `Admitted` statement of `kim_input_private`
   compiles.
2. `cond_mutual_infoE2` plumbing + singleton-fibre reduction
   (`= (3/4) * cdiv1 false`).
3. `le_div_chi2` helper.
4. `kim_view_le` deviation (reusing `den_boer_view_count_eq`) and `kim_qbar_gt0`.
5. assemble the bound; pin `kim_leak_bound`.
6. `eps = 0` corollary (`kim_input_private0`) + `Print Assumptions`.
