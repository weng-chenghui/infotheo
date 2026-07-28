# Reduction-form security statements: removing `epsilon_cpa` and the IND-CPA axiom

Date: 2026-07-28
Branch base: `itp2026-dumas2017dual`
Status: design, not implemented
Supersedes: `20260728-resource-bounded-adversary-class.md`, which an adversarial
review found unsound. See "Why the previous design was abandoned" below.

## Problem

`enc_ind_cpa_real_or_zero` (`homomorphic_encryption/indcpa_ror.v:256`) is an axiom
asserting that a single constant `epsilon_cpa AHE` bounds the IND-CPA advantage of
`reduction : raw_package`, quantified with no restriction beyond well-typedness.

Writing the bound as a constant silently quantifies over the whole adversary class.
`epsilon_cpa AHE` is the supremum of the advantage over every `raw_package`. `Renc` is a
`finType` and `pkey_of_party` is fixed before `reduction` is quantified, so a
`raw_package` can hard-code the public key and decide by finite search over `#|Renc|`
whether `c = Enc(pk, m; r)` holds for some `r`. That distinguisher has advantage close
to 1, so the supremum is close to 1, so every `_ <= 2 * epsilon_cpa AHE` bound and the
composed `1/m + 2 * epsilon_cpa AHE` are numerically empty.

Nothing in the tree constrains `epsilon_cpa` at any concrete scheme. Paillier 1999 and
Benaloh 1994 are built as `AHEncType` instances (`_CoqProject:118-121`) and neither file
mentions `epsilon_cpa`. The only lemma relating the constant to a scheme is
`epsilon_cpa_idealized_ge1` (`homomorphic_encryption/idealized/idealized_indcpa.v:157`),
which concerns the deliberately broken plaintext-returning scheme and concludes
`1 <= epsilon_cpa`.

## Approach

State every computational bound as the advantage of an explicitly constructed reduction
against the IND-CPA oracles, rather than as a multiple of an assumed constant. This is
how the SSProve case studies state their results. Evidence, from
`coq-ssprove.0.3.1/theories/Crypt/examples/`:

- `grep -rE "^(Axiom|Parameter|Conjecture) " *.v` over all twenty example files returns
  nothing.
- `PRF.v:323` defines `prf_epsilon A := Advantage EVAL A`, a function of the adversary,
  not a constant.
- `PRF.v:383` states `Advantage IND_CPA A <= prf_epsilon (A ∘ MOD_CPA_ff_pkg) +
  statistical_gap A + prf_epsilon (A ∘ MOD_CPA_tt_pkg)`, with `ValidPackage` and
  `fseparate` as the only side conditions.
- `PRF.v:325` keeps `statistical_gap` as an unreduced information-theoretic summand
  alongside the reduction terms. This is the same shape as the DSDP `1/m` leg.
- `KEMDEM.v:861` and `StretchPRG.v:169` have the same form.

The reductions this needs already exist in the DSDP proofs. `Advantage_link`
(`SSProve/Crypt/package/pkg_advantage.v:123`) states
`AdvantageE G0 G1 (A ∘ P) = AdvantageE (P ∘ G0) (P ∘ G1) A`, and
`dsdp_indcpa_advantage.v:285` already rewrites with it to produce `A ∘ shim` before
handing that package to the axiom on the next line. The change is to stop consuming the
term and propagate it into the statement.

## Goals

1. Delete `epsilon_cpa` and `enc_ind_cpa_real_or_zero`.
2. Restate the two hop ladders and every downstream bound in terms of the IND-CPA
   advantage of explicit reductions.
3. Rename `adm` / `dsdp_adm`, which name a location-disjointness condition after
   admissibility and carry an unused `raw_package` argument.

## Non-goals

- Formalizing DCR, DDH, or any number-theoretic assumption. The reduction terminates at
  the IND-CPA game, which is where the SSProve case studies also terminate.
- Proving anything about the IND-CPA advantage of Paillier or Benaloh.
- Introducing an adversary class, a resource predicate, or any cost model.
- Touching the information-theoretic leg. `dsdp_alice_guess_V2_zero_le` and its fiber
  chain are unaffected.

## Why the previous design was abandoned

The superseded spec guarded the axiom with an opaque `resource_bounded` predicate. An
adversarial review found:

- A global `Parameter` cannot be instantiated by any downstream mechanism, so the claim
  that the guarded statement subsumes the unguarded one at `fun _ => True` was false.
- The development is non-asymptotic. `epsilon_cpa` is a plain real per scheme with no
  security parameter, so the only meaningful resource class is a fixed budget, and fixed
  budgets are not closed under `link`, `par`, or `ID`. The three proposed closure axioms
  are false for exactly the classes that would make the guarded bound mean anything.
- `dsdp_alice_view_statdist_le` (`dsdp_main.v:903`) has no adversary in its statement.
  Its proof manufactures `Dstar`, the optimal statistical test, and wraps it with
  `test_adversary` (`dsdp_simulator.v:331`). Guarding it would require assuming every
  Boolean function is efficiently computable, which readmits the brute-force
  distinguisher and undoes the exercise.
- `raw_code` continuations are Gallina functions, so the brute-force distinguisher and an
  honest one-bit test are the same package skeleton. No predicate on `raw_package`
  definable without a cost model separates them.

The reduction form makes all of this moot. There is no constant to be forced to 1, so
there is no adversary class to define.

## Design

### The advantage functional

In `homomorphic_encryption/indcpa_ror.v`, after the oracle definitions, replacing the
deleted `Parameter` and `Axiom`:

```coq
Definition indcpa_advantage
    (AHE : AHEncType) (Renc : finType) (card_renc : nat)
    (renc_card : #|Renc| = card_renc) (rand_of_renc : Renc -> rand AHE)
    (t_msg t_cipher : choice_type)
    (msg_of_chmsg : t_msg -> plain AHE)
    (chcipher_of_cipher : cipher AHE -> t_cipher)
    (pkey_of_party : party_id -> pub_key AHE)
    (reduction : raw_package) : R :=
  AdvantageE
    (oracle_encrypt_real AHE Renc card_renc renc_card rand_of_renc
       t_msg t_cipher msg_of_chmsg chcipher_of_cipher pkey_of_party)
    (oracle_encrypt_zero AHE Renc card_renc renc_card rand_of_renc
       t_msg t_cipher chcipher_of_cipher pkey_of_party)
    reduction.
```

This is a definition, not an assumption. It names the quantity the reductions are
measured against, in the same way `PRF.v:323` names `prf_epsilon`.

### The hop lemmas become theorems

`advantage_hop_leak_S` (`indcpa_hopping/dsdp_indcpa_advantage.v:249`) currently
telescopes through two perfect equivalences, rewrites with `Advantage_link`, and applies
the axiom. Removing the last step leaves the reduction term:

```coq
Lemma advantage_hop_leak_S ... :
  AdvantageE
    (denote_game_leak_S ... (zero_hop_prefix i gc))
    (denote_game_leak_S ... (zero_hop_prefix i.+1 gc)) A
  <= indcpa_advantage ... (A ∘ denote_game_shim_leak_S (zero_hop_prefix i gc) i).
```

The proof is the current one with `apply: (enc_ind_cpa_real_or_zero ...)` deleted and
the goal closed by reflexivity of the rewritten term. Same for `advantage_hop`
(`symbolic_game/dsdp_game_code.v:886`), whose axiom application is at `:909`.

### The ladder sums instead of multiplying

`advantage_sum_ladder_le_leak_S` (`:294`) currently concludes
`<= n.+1%:R * epsilon_cpa AHE`. It becomes a sum indexed by rung:

```coq
  <= \sum_(l < n.+1) indcpa_advantage ...
       (A ∘ denote_game_shim_leak_S (zero_hop_prefix (start + l) gc) (start + l)).
```

The telescoping induction is unchanged in structure. Each rung contributes its own term
rather than a copy of a constant, so the `mulrSr / mulrDl / mul1r` collapse steps are
replaced by `big_ord_recr` and `lerD`.

`advantage_le_leak_S` (`:329`) currently concludes
`<= (size (hop_sites gc))%:R * epsilon_cpa AHE` and becomes a sum over `hop_sites gc`.

### Headline shape

`dsdp_experiment_hops` (`dsdp_main.v:118`) computes `count_obs_hops (corrupted_view
dsdp_experiment) = 2` by `Proof. by []. Qed.`, so at the DSDP instance the sum has
exactly two summands and can be displayed as two terms:

```coq
Theorem dsdp_alice_guess_V2_real_le ... :
  guess_sdistr_success_real ...
  <= card_msg%:R^-1
     + indcpa_advantage ... (guess_reduction ∘ shim_0)
     + indcpa_advantage ... (guess_reduction ∘ shim_1).
```

The `1/m` summand is unchanged, and `dsdp_alice_guess_V2_zero_le` keeps a
byte-identical statement. `dsdp_alice_unpredictability_entropy_ge` transports the same
bound through `log_id` (`dsdp_guess_fiber.v:1772`), whose current statement is
parameterized on `eps` and takes the new sum in that slot without modification.

### `dsdp_alice_view_statdist_le` survives unchanged in kind

Its proof (`dsdp_main.v:923-935`) builds `Dstar` and applies
`dsdp_alice_simulation_secure`. Since no hypothesis is added to that theorem, the proof
needs only its bound updated to the reduction sum. This is the case the superseded
design could not handle.

### Deletions

`epsilon_cpa` and `enc_ind_cpa_real_or_zero` (`indcpa_ror.v:241`, `:256`) are deleted,
together with the trailing `Check @enc_ind_cpa_real_or_zero.` at `:279`.

`epsilon_cpa_idealized_ge1` (`idealized_indcpa.v:157`) loses its subject and is deleted.
Its mathematical content survives in `advantage_idealized_eq1` (`:140`), which is
unconditional, axiom-free, and states that the idealized scheme is separated with
advantage exactly 1. The file header comment at `:5` and `:40`, which explains the
per-scheme indexing of `epsilon_cpa`, is rewritten to explain instead why a constant
bound is not used at all.

No project axiom remains after this. The `computational/` directory proposed in the
superseded spec is not created, because its intended contents cease to exist.

### Rename

| Before | After | Type before | Type after |
|---|---|---|---|
| `adm` (`smc/ssprove_ext_simulator.v:36`) | `locs_disjoint` | `Locations -> raw_package -> Prop` | `Locations -> Prop` |
| `dsdp_adm` (`dsdp_simulator.v:225`) | `dsdp_locs_disjoint` | `Locations -> raw_package -> Prop` | `Locations -> Prop` |

Occurrences: `smc/ssprove_ext_simulator.v` 9, `dsdp_simulator.v` 5,
`probe_p5_skeletons.v` 11. The probe file is absent from `_CoqProject` and is updated
only to avoid leaving contradictory vocabulary.

`adv_sim_le_reduction` (`ssprove_ext_simulator.v:82`) takes `AT_adm : adm LAT (A ∘ T)`
and genuinely uses the package argument. Under `dsdp_adm` the body ignores it, so
`adm LAT (A ∘ T)` and `dsdp_locs_disjoint LAT` are interchangeable at the DSDP
instantiation, and the arity drop is sound there. The generic lemma loses the ability to
express a package-dependent side condition. Since `adv_sim_le` has exactly one consumer
(`dsdp_adv_sim_le`, `dsdp_simulator.v:279`), this is recorded and accepted rather than
worked around.

Blueprint references `dsdp_adv_sim_le` (`security.tex:196`), whose name does not change.

## Costs

1. Headline statements grow. `2 * epsilon_cpa AHE` becomes two `indcpa_advantage` terms
   carrying their full parameter lists. The generic ladder lemmas carry a `\sum` rather
   than a product.
2. The ladder induction is rewritten from arithmetic on a constant multiple to `bigop`
   reasoning. Structurally the same induction, different closing tactics.
3. Every place in the blueprint and thesis that writes the bound as `1/m + 2 eps` must be
   restated. The prose claim that these terms are small under a standard assumption moves
   from a formal axiom to a cited sentence, which is what `StretchPRG.v:164` does with
   its `Negligible by assumption.` comment.
4. `idealized_indcpa.v` loses its headline, and the argument for per-scheme indexing
   loses its subject.
5. `adv_sim_le` loses package-dependent side conditions, as recorded above.

Not a cost: no result becomes unreachable. Every current bound is recovered by anyone
who supplies a bound on `indcpa_advantage` for their scheme and adversary class, and the
current statement is the special case where that bound is a constant.

## Phases

Each phase builds clean and is committed before the next begins.

**Phase 1. Rename.** `adm` to `locs_disjoint`, `dsdp_adm` to `dsdp_locs_disjoint`, arity
dropped, `adv_sim_le_reduction` adjusted, probe file updated. Independent of the rest.

**Phase 2. Add `indcpa_advantage`.** Definition only, nothing consumes it. Build green.

**Phase 3. Chain I.** Restate `advantage_hop`, `advantage_sum_ladder_le`,
`advantage_le`, `advantage_gc_dsdp` (`dsdp_game_code.v:886, 930, 973, 1064`) and
`dsdp_indcpa_secrecy` (`dsdp_game_derivation.v:691`) in reduction form. Update
`dsdp_advantage_derived` (`dsdp_indcpa_advantage.v:63`) and
`dsdp_alice_view_advantage_le` (`dsdp_main.v:128`).

**Phase 4. Chain II.** Same for `advantage_hop_leak_S`,
`advantage_sum_ladder_le_leak_S`, `advantage_le_leak_S`,
`dsdp_advantage_derived_leak_S` (`dsdp_indcpa_advantage.v:249, 294, 329, 405`), then
`dsdp_adv_sim_le` (`dsdp_simulator.v:279`) and the five remaining `dsdp_main.v`
headlines at `:726, 756, 789, 850, 903`.

**Phase 5. Delete.** Remove `epsilon_cpa`, `enc_ind_cpa_real_or_zero`, the trailing
`Check`, and `epsilon_cpa_idealized_ge1`. Rewrite the `idealized_indcpa.v` header.
This phase is the one that proves the axiom was never needed, because it cannot compile
until every consumer has been converted.

**Phase 6. Documentation.** Blueprint node bodies and `\rocq{}` coverage, thesis wording,
`Print Assumptions` regression.

Phase ordering rationale: converting consumers before deleting the axiom keeps every
intermediate state compilable. Phase 5 failing to compile is the signal that a consumer
was missed.

## Verification

- Full-tree `make` under the local `~/Projects/coq/_opam` switch, per phase.
- After Phase 5, `Print Assumptions` on each `dsdp_main.v` headline must contain no
  project declaration. The residual entries are upstream and expected:
  `boolp.propositional_extensionality`, `boolp.functional_extensionality_dep`,
  `FunctionalExtensionality.functional_extensionality_dep`,
  `boolp.constructive_indefinite_description`, `SPropBase.ax_proof_irrel`,
  `Axioms.R`, `realsum.__admitted__interchange_psum`. This list is committed as the
  regression allowlist.
- `dumas2017dual/blueprint/check_coverage.py` returns OK.
- `dsdp_alice_guess_V2_zero_le` and `dsdp_simulator_factorization` have byte-identical
  statements before and after.

## Follow-up recorded, not scheduled

`realsum.__admitted__interchange_psum` is an `Admitted` lemma in mathcomp
`experimental_reals` sitting in the trust base of every headline. It is unrelated to
this work and predates it, but it belongs in any honest account of what the development
assumes. Worth its own note.

Connecting `indcpa_advantage` at Paillier to DCR is a separate piece of work. The
interface for it is exactly the `indcpa_advantage` terms this design exposes.
