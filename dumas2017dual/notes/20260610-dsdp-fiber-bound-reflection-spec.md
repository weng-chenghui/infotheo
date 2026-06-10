# DSDP output-channel 1/m by full reflection — design spec (option B)

Date: 2026-06-10. Branch: itp2026-dumas2017dual.
Scope: discharge the information-theoretic fiber bound `Pr[guess = V2] ≤ 1/m` at
the all-zero output-exposing endpoint with **zero new assumptions** (only the
already-committed predictor-losslessness `guess_lossless`), completing the
chain `dsdp_alice_secrecy_leak_S ≤ 1/m + 2·epsilon_cpa`.

Supersedes the option-A fallback (a localized `guess_fdist_success_le_invm`
hypothesis) in `20260610-dsdp-output-channel-derived-implementation-plan.md`.

## 1. Goal and why option B is feasible

The connector (`guess_success_sdistr_eq_fdist`; committed as
`Pr_guess_enc_zero_leak_S_eqE`) already proves
`guess_sdistr_success = guess_fdist_success`, i.e.
`Pr(experiment, zero_S) true = Pr_[guess_joint_fdist] [diagonal]`, moving
the question into infotheo's fdist world. What remained was bounding that
diagonal by `1/m`, which needs the joint's structure (`V2` uniform on the
`m`-point fiber given `S`; `guess ⊥ V2 | S`). The prior analysis
(`ssprove_absolute_Pr_gap`) judged this intractable because SSProve's relational
tools give `AdvantageE`, not an absolute `Pr`, and a cell-read cannot be
commuted past an opaque predictor.

That analysis missed the **absolute-`Pr` footprint route**, now validated by a
compiled probe (`dsdp/probe_fiber_reflection.v`, throwaway):

- `Pr_fst_closed` (PROVEN, ~9 tactic lines, `Qed`): a closed predictor's
  value-marginal is heap-independent, so it cannot read `V2_cell` — by induction
  on `valid_code`, the `opr`/`getr`/`putr` cases vacuous (`fhas_empty`),
  `ret`/`sampler` thread the heap unchanged.
- The integration (`toy_reflect`) advanced through every substantive step:
  reflect a concrete `sample → put → get` program with `Pr_code_sample` /
  `dlet_uniform` / `Pr_code_get`, compose an opaque predictor via
  `Pr_code_bind`, and eliminate its heap-dependence via the footprint lemma.
  Only a cosmetic `dlet`-congruence fold remained.

Design choice settled with the user: the predictor is **general** (may keep its
own state in locations disjoint from the game cells — the strictly stronger
adversary class, matching the committed `predictor_guesser` type). This needs
the general footprint `Pr_fst_agree_locs`; `Pr_fst_closed` is its `L = emptym`
corollary.

## 2. Proof architecture (data flow)

```
 guess_joint_code : raw_code (Mfin × Mfin)             (committed, returns (guess,V2) pair)
        │ Pr_fst
        ▼
 guess_joint_fdist : {fdist Mfin × Mfin}               (committed; the (guess,V2) joint)
        │ reflect the program's INTERNAL samples (Pr_fst_guess_joint_code)
        │ opaque predictor framed out by Pr_fst_agree_locs
        ▼
 guess_sample_fdist : {fdist <samples × guess>}        (NEW; full joint of v2,v3,u2,u3,S,guess)
        │ discharge dsdp_entropy hypotheses:
        │   guess_V2_uniform, guess_VarRV_indep_inputs,
        │   guess_S_determined, guess_indep_V2_given_S
        ▼
 Pr_dsdp_sol_uniform (cited, guess-free) ⇒ each (v2,v3) has prob 1/m; guess ⊥ V2 | S
        ▼
 guess_fdist_success_le_invm : guess_fdist_success = Pr_[guess_joint_fdist][diag] ≤ 1/m   (NEW)
        │ + connector guess_success_sdistr_eq_fdist : guess_sdistr_success = guess_fdist_success
        ▼
 guess_sdistr_success_le_invm : guess_sdistr_success = Pr(exp, zero_S) true ≤ 1/m          (NEW)
        │ + guess_advantage_le (NEW; 2ε between the real/zero experiments,
        │   from dsdp_advantage_derived_leak_S committed)
        ▼
 dsdp_alice_secrecy_leak_S : Pr(exp, real_S) true ≤ 1/m + 2·epsilon_cpa  (NEW, final)
```

## 3. Components — every new identifier (signatures + role)

### 3.0 Naming conventions (locked 2026-06-10)

- **Prefix policy.** Building blocks inside `Section dsdp_guess_distribution`
  are bare `guess_*` — the section name already carries `dsdp`, so the prefix is
  redundant on its locals. Only the final exported result keeps the project
  prefix: `dsdp_alice_secrecy_leak_S`.
- **The connector's two sides are named by distribution TYPE, mirroring the
  bridge `sdistr_to_fdist`.** `guess_sdistr_success` is the mass of the SSProve
  subdistribution (`sdistr` = the `distr`/`SDistr` the game run induces);
  `guess_fdist_success` is the diagonal mass of the Infotheo fdist. Both denote
  the *same* real. `game` is rejected (a game is a program, not a distribution,
  so it would not be parallel to `fdist`); `sdistr` is the SSProve distribution
  type, already the name in `sdistr_to_fdist`.
- **`guess` belongs on both connector sides.** The quantity is the adversary's
  success probability; the guess is the predictor's output, foreign to Infotheo.
  So neither side is "Infotheo content" — the fdist side is only the fdist
  *representation*. The distinctively-Infotheo facts are **guess-free** and keep
  their `dsdp_entropy` names (`Pr_dsdp_sol_uniform`, `dsdp_fiber_card`); they are
  about `V2`'s distribution, cited not renamed.
- **The connector names both representations** (`guess_success_sdistr_eq_fdist`,
  not the terse `…E`), so the bridge is legible from the lemma name.

### 3.1 Generic reflection infrastructure (fiber file, reusable)

- `Pr_fst_agree_locs` — lemma. The value-marginal of valid code depends only on
  the heap restricted to the code's own locations `L`: heaps agreeing on `L`
  give equal `distr.dmargin fst (Pr_code c ·)`. Proof by induction on
  `valid_code` (the `getr`/`putr` cases touch only `L`, so agreement on `L` is
  preserved; `ret`/`sampler` thread the heap; `opr` vacuous for `[interface]`).
  Source comment states the separation-logic FOOTPRINT/frame reading and that
  it is what makes the predictor blind to `V2_cell`. (Generic: no `guess_`
  prefix — not a member of the guess family.)
- `Pr_fst_closed` — lemma (PROVEN). The `L = emptym` corollary of
  `Pr_fst_agree_locs`: `ValidCode emptym [interface] c → ∀ h, distr.dmargin fst
  (Pr_code c h) = Pr_fst c`.
- `Pr_fst_guess_joint_code` — lemma. The explicit reflection of
  `Pr_fst guess_joint_code`: the experiment's internal uniform samples
  (`dlet_uniform`) threaded through the cells (`Pr_code_get`/`_put`) with the
  opaque predictor framed out (`Pr_fst_agree_locs`), equating it to the
  pushforward of `guess_sample_fdist` onto `(guess, V2)`.

### 3.2 The explicit sample distribution and its random variables

- `guess_sample_fdist` — def. The joint fdist of the zero-game's protocol
  scalars and the guess: the scalars `(V2, V3, U2, U3)` are uniform and
  independent (the `denote_run` samples), and `guess` follows the predictor's
  output distribution on the resulting `(view, S)` — i.e. a uniform product on
  the scalars composed with the predictor kernel, NOT a uniform draw on the
  guess. `Pr_fst_guess_joint_code` proves the program realizes it, and its
  `(guess, V2)`-marginal is `guess_joint_fdist`.
- `V2 V3 U2 U3 S guess` (and the constant inputs `V1 U1`) — random variables
  (`Let`/def) over `guess_sample_fdist`, the projections feeding `dsdp_entropy`.
  Names preserve the math symbols, mirroring `dsdp_entropy`'s
  `V1 V2 V3 U1 U2 U3 S`.

### 3.3 The four `dsdp_entropy` hypotheses, discharged over the sample fdist

- `guess_V2_uniform` — lemma. `(V2, V3)` is uniform under `guess_sample_fdist`
  (independent uniform samples).
- `guess_VarRV_indep_inputs` — lemma. `(V2, V3) ⊥ (V1, U1, U2, U3)`. (`VarRV`
  kept to mirror `dsdp_entropy`'s local naming.)
- `guess_S_determined` — lemma. `S` is the constraint function of the variables
  and inputs (`S = u1·v1 + u2·v2 + u3·v3 = dsdp_g`).
- `guess_indep_V2_given_S` — lemma. `guess ⊥ V2 | S` — at the all-zero endpoint
  the view is `V2`-free (enc of 0), so the guess depends on `V2` only through
  `S`; the conditional independence is delivered by `Pr_fst_agree_locs` (the
  predictor's output is framed out from `V2_cell`).

### 3.4 The two success probabilities, the connector, the bound, composition

- `guess_sdistr_success` — def. The SSProve-side success probability: the
  true-mass of the guessing game's output subdistribution,
  `distr.mu (pkg_advantage.Pr (guessing_experiment predictor zero_game_leak_S)) true`.
- `guess_fdist_success` — def. The Infotheo-side success probability: the
  diagonal mass of the bridged fdist,
  `Pr guess_joint_fdist [set gv | gv.1 == gv.2]`. Same real as
  `guess_sdistr_success`.
- `guess_success_sdistr_eq_fdist` — lemma (connector).
  `guess_sdistr_success = guess_fdist_success`. The guessing experiment's
  instance of `sdistr_to_fdist`: pushforward (`Pr_fst_map`) onto the diagonal,
  then `Pr_sdistr_to_fdist`. Heap-free. (Restructures the committed
  `Pr_guess_enc_zero_leak_S_eqE`, introducing the two named sides.)
- `guess_fdist_success_le_invm` — lemma. `guess_fdist_success ≤
  (card_msg)%:R^-1`. Proof: the diagonal of the `(guess, V2)` marginal equals
  `Pr_[guess_sample_fdist] [guess = V2]`; instantiate `dsdp_entropy` at
  `guess_sample_fdist` with §3.3; the guess-free `Pr_dsdp_sol_uniform` gives each
  `(v2,v3)` probability `1/m`, and `guess_indep_V2_given_S` caps the collision
  at `1/m`.
- `guess_sdistr_success_le_invm` — theorem. `guess_sdistr_success ≤
  (card_msg)%:R^-1`. Proof: rewrite by `guess_success_sdistr_eq_fdist`, then
  `guess_fdist_success_le_invm`.
- `guess_advantage_le` — lemma (named, ~10–25 lines; carries the predictor
  disjointness hypotheses). `|Pr(exp, real_S) true − Pr(exp, zero_S) true| ≤
  2·epsilon_cpa`. Proof: re-associate `guessing_experiment = guessing_challenger
  ∘ par predictor game` into `(guessing_challenger ∘ predictor) ∘ game`, package
  `guessing_challenger ∘ predictor` as a `dsdp_indcpa_adversary` (validity
  automatic; disjointness from the three hypotheses + the challenger's `emptym`
  locations), then `exact: dsdp_advantage_derived_leak_S`.
- `dsdp_alice_secrecy_leak_S` — theorem (final, prefixed; replaces
  `dsdp_alice_secrecy`).
  `Pr(guessing_experiment predictor real_game_leak_S) true ≤
  (card_msg)%:R^-1 + 2·epsilon_cpa`. Proof: triangle
  `Pr(real) ≤ Pr(zero) + |Pr(real) − Pr(zero)|`, then
  `guess_sdistr_success_le_invm` and `guess_advantage_le`.

### 3.5 Renames of committed identifiers (fiber file only)

Apply the prefix policy and the success-naming to the committed
`Section dsdp_guess_distribution`:

- `dsdp_guess_core → guess_joint_code` (the `(guess, V2)`-pair program).
- `dsdp_guess_fdist → guess_joint_fdist` (its `(guess, V2)` joint fdist).
- `dsdp_guess_resolved → guess_resolved`, `dsdp_guess_resolve_eq →
  guess_resolve_eq`, `dsdp_guess_lossless → guess_lossless`.
- `Pr_guess_enc_zero_leak_S_eqE → guess_success_sdistr_eq_fdist`, restructured to
  state `guess_sdistr_success = guess_fdist_success` via the two new defs.
- update all internal references; sync the blueprint `\rocq` links and coqdoc
  anchors in the same commit as the code rename (so no link dangles).

## 4. Cited (unchanged) anchors

- infotheo `dsdp_entropy`: `dsdp_g`, `dsdp_fiber_card`, `Pr_dsdp_sol_uniform`,
  the section interface (`P`, `V1..S`, `CondRV`/`VarRV`/`InputRV`, hypotheses
  `VarRV_uniform`/`VarRV_indep_inputs`/`constraint_holds`).
- SSProve nominal: `Pr_code_sample`/`_get`/`_put`/`_bind`, `Pr_fst_sample`/
  `_bind`, `Pr_Pr_fst`, `dlet_uniform`, `distr.dmargin*`.
- committed derived chain: `real_game_leak_S`, `zero_game_leak_S`,
  `dsdp_advantage_derived_leak_S`; the connector and guessing layer.

## 5. Risks and mitigations

- **R1 (main): reflecting the full `denote_run`.** The zero-game's `denote_run`
  unfolds to ~14 straight-line statements carrying the AHE marshalling and
  `he_term` evaluation. Mitigation: reflect the *unfolded* concrete program
  (computed from `gc_dsdp`) statement-by-statement with the proven calculus; the
  `he_term`/marshalling appears only inside `S`'s value, which feeds
  `guess_S_determined` as a closed-form equation, not something to reflect
  probabilistically. Mechanical, no opaque obstruction.
- **R2: connecting the reflected sample distribution to `dsdp_entropy`'s RV
  framework.** Mitigation: `guess_sample_fdist` is an explicit
  `fdist_uniform` over a product index; the four identities are then standard
  marginal/independence facts of a uniform product, plus the closed-form `S`.
- **R3: the `par predictor game` vs `A ∘ game` reconciliation** in
  `guess_advantage_le`. Mitigation: the committed `guess_resolve_eq`
  already resolves the `par` form; the same link/interchange lemmas re-associate
  it to the sequential `(challenger ∘ predictor) ∘ game` that `AdvantageE`
  expects.
- None of R1–R3 is a documented infra gap; all use proven calculus.

## 6. Verification

- Each component verified by `rocq_compile_file` on the fiber file; no
  `Admitted`/`admit`/`Axiom` (the only assumption is the committed
  `guess_lossless`). Final axiom set = the committed chain's (`epsilon_cpa`,
  `enc_ind_cpa_real_or_zero`, standard SSProve/classical), no new custom axiom.
- The throwaway probe `dsdp/probe_fiber_reflection.v` is deleted before the real
  work; the proven `Pr_fst_closed`/`Pr_fst_agree_locs` are ported into the fiber
  file.
- On completion, the blueprint Part II (ch 10–11) nodes flip from blue to green
  and lose the option-A hypothesis caveat.

## 7. Out of scope

- No change to Part I or the `2·epsilon_cpa` machinery.
- No new SSProve general-purpose infra beyond the two footprint lemmas
  (`Pr_fst_agree_locs`, `Pr_fst_closed`), which live in the fiber file.
