# Reduction-form security statements: removing `epsilon_cpa` and the IND-CPA axiom

Date: 2026-07-28
Branch base: `itp2026-dumas2017dual`
Status: design, not implemented. Revised after a second adversarial review.
Supersedes: `20260728-resource-bounded-adversary-class.md`.

## Problem

`enc_ind_cpa_real_or_zero` (`homomorphic_encryption/indcpa_ror.v:256`) is an axiom
asserting that one constant `epsilon_cpa AHE` bounds the IND-CPA advantage of
`reduction : raw_package`, quantified with no restriction beyond well-typedness.

Writing the bound as a constant silently quantifies over the whole adversary class.
`epsilon_cpa AHE` is the supremum of the advantage over every `raw_package`. `Renc` is a
`finType` and `pkey_of_party` is fixed before `reduction` is quantified, so a
`raw_package` can hard-code the public key and decide by finite search over `#|Renc|`
whether `c = Enc(pk, m; r)` holds for some `r`. That distinguisher has advantage close
to 1, so the supremum is close to 1, so `_ <= 2 * epsilon_cpa AHE` and the composed
`1/m + 2 * epsilon_cpa AHE` are numerically empty.

Nothing in the tree constrains `epsilon_cpa` at any concrete scheme. Paillier 1999 and
Benaloh 1994 are built as `AHEncType` instances (`_CoqProject:118-121`) and neither file
mentions `epsilon_cpa`. The only lemma relating the constant to a scheme is
`epsilon_cpa_idealized_ge1` (`homomorphic_encryption/idealized/idealized_indcpa.v:157`),
concerning the deliberately broken plaintext-returning scheme, concluding
`1 <= epsilon_cpa`.

## Approach

State every computational bound as the advantage of an explicitly constructed reduction
against the IND-CPA oracles, rather than as a multiple of an assumed constant. This is
how the SSProve case studies state their results. Evidence from
`coq-ssprove.0.3.1/theories/Crypt/examples/`:

- `PRF.v:323` defines `prf_epsilon A := Advantage EVAL A`, a function of the adversary,
  not a constant.
- `PRF.v:388-392` bounds `Advantage IND_CPA A` by
  `prf_epsilon (A ∘ MOD_CPA_ff_pkg) + statistical_gap A + prf_epsilon (A ∘ MOD_CPA_tt_pkg)`,
  with `ValidPackage` and `fseparate` as the only side conditions.
- `PRF.v:325` keeps `statistical_gap` as an unreduced information-theoretic summand
  alongside the reduction terms. Same shape as the DSDP `1/m` leg.
- `KEMDEM.v:861` and `StretchPRG.v:169` have the same form.
- No example states an unproven security assumption. The `Parameter`s that do occur
  (34 across `OVN.v`, `SigmaProtocol.v`, `Schnorr.v`, `RandomOracle.v`, for instance
  `Schnorr.v:41` `Parameter gT : finGroupType.`) are `Module Type` carriers for group
  and message types, not advantage bounds.
- `StretchPRG.v:165` leaves the negligibility reading to a prose comment,
  `Negligible by assumption.`

The reductions already exist in the DSDP proofs. `Advantage_link`
(`SSProve/Crypt/package/pkg_advantage.v:123`) states
`AdvantageE G0 G1 (A ∘ P) = AdvantageE (P ∘ G0) (P ∘ G1) A`, and
`dsdp_indcpa_advantage.v:285` already rewrites with it to produce `A ∘ shim` before
handing that package to the axiom on the next line. The change is to stop consuming the
term and propagate it into the statement.

## Goals

1. Delete `epsilon_cpa` and `enc_ind_cpa_real_or_zero`.
2. Restate the two hop ladders and every downstream bound as the IND-CPA advantage of
   explicit reductions.
3. Delete `dsdp_alice_view_statdist_le` and its now-dead support.
4. Rename `adm` / `dsdp_adm`, which name a location-disjointness condition after
   admissibility and carry an unused `raw_package` argument.

## Non-goals

- Formalizing DCR, DDH, or any number-theoretic assumption. The reduction terminates at
  the IND-CPA game, where the SSProve case studies also terminate.
- Proving anything about the IND-CPA advantage of Paillier or Benaloh.
- Introducing an adversary class, a resource predicate, or any cost model.
- Touching the information-theoretic leg or the Infotheo bridge.

## Why the previous design was abandoned

The superseded spec guarded the axiom with an opaque `resource_bounded` predicate. A
global `Parameter` cannot be instantiated, so its subsumption argument was false. The
development is non-asymptotic, so the only meaningful resource classes are fixed
budgets, which are not closed under `link`, `par`, or `ID`, making the proposed closure
axioms false. And `raw_code` continuations are Gallina functions, so the brute-force
distinguisher and an honest one-bit test are the same package skeleton, which no
predicate on `raw_package` definable without a cost model can separate.

The reduction form makes this moot. There is no constant to be forced to 1, so there is
no adversary class to define.

## Design

### The advantage functional

In `homomorphic_encryption/indcpa_ror.v`, after `End indcpa_ror.` at `:231`, replacing
the deleted `Parameter` and `Axiom`:

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

A definition, not an assumption. It names the quantity the reductions are measured
against, as `PRF.v:323` names `prf_epsilon`.

The argument list matches what the current `apply:` at `dsdp_game_code.v:909` and
`dsdp_indcpa_advantage.v:286` already unifies against: `oracle_real` and `oracle_zero`
(`dsdp_game_code.v:708, 716`) are delta-equal to `oracle_encrypt_real` and
`oracle_encrypt_zero` at exactly these arguments. The oracles take only
`msg_of_chmsg : t_msg -> plain AHE`; the opposite-direction `chmsg_of_msg` is consumed
by `denote_game` and `denote_game_shim`, on the other side of `∘`.

Because `indcpa_advantage` takes `renc_card : #|Renc| = card_renc` and the oracles use
it under `cast_ord`, headline bounds become proof-relevant in that argument. This is
harmless by `eq_irrelevance` on `nat`, but statement-identity checks must compare proof
terms, not just printed forms. Likewise `denote_game_shim_leak_S` is a `package` whose
term embeds its validity proof, so headline right-hand sides now carry validity terms.

### Hop lemmas become axiom-free

`advantage_hop_leak_S` (`dsdp_indcpa_advantage.v:249`) telescopes through two perfect
equivalences, rewrites with `Advantage_link`, then applies the axiom. Deleting that last
step leaves the reduction term:

```coq
Lemma advantage_hop_leak_S ... :
  AdvantageE
    (denote_game_leak_S ... (zero_hop_prefix i gc))
    (denote_game_leak_S ... (zero_hop_prefix i.+1 gc)) A
  <= indcpa_advantage ... (A ∘ denote_game_shim_leak_S (zero_hop_prefix i gc) i).
```

The goal after `rewrite -Advantage_link` is closed by `exact: lexx`, not `reflexivity`,
since the goal is an inequality. Same for `advantage_hop` (`dsdp_game_code.v:886`),
whose axiom application is at `:909`.

### The ladder sums instead of multiplying

`advantage_sum_ladder_le_leak_S` (`:294`) currently concludes
`<= n.+1%:R * epsilon_cpa AHE`. It becomes

```coq
  <= \sum_(l < n.+1) indcpa_advantage ...
       (A ∘ denote_game_shim_leak_S (zero_hop_prefix (start + l) gc) (start + l)).
```

The sum covers sites `start .. start + n`, exactly the `n+1` rungs, so there is no
off-by-one.

The split must use `big_ord_recl`, not `big_ord_recr`. `advantage_sum` peels the head
(`pkg_advantage.v:197-201`), and both ladder proofs apply `IHn` at `start.+1` via
`rewrite -addSnnS` (`dsdp_indcpa_advantage.v:318-320`, `dsdp_game_code.v:944-946`).
`big_ord_recr` peels the last site and would need `IHn` at `start`, which a head-peeling
`advantage_sum` never produces. The realignment step is required because `start + l.+1`
and `start.+1 + l` are not convertible for a variable `start`, and unlike the current
proof the term now sits under a binder:

```coq
rewrite big_ord_recl addn0; congr (_ + _); by apply: eq_bigr => i _; rewrite addSnnS.
```

The base case needs `big_ord1` and `addn0` where the current proof uses
`mulrSr mulrDl mul1r`.

`advantage_le_leak_S` (`:329`) currently concludes
`<= (size (hop_sites gc))%:R * epsilon_cpa AHE`. Since `hop_sites gc = iota 0
(count_hops gc)` (`dsdp_game_code.v:123`), the rungs are a plain `0 .. n-1` range and
the index sets coincide. Write the bound as `\sum_(l < size (hop_sites gc))`, ordinal
indexed. A seq bigop over `hop_sites gc` would not unify with
`advantage_sum_ladder_le`'s conclusion. The empty-ladder branch keeps
`advantage_self_zero` with `mul0r` replaced by `big_ord0` and `lexx`.

### Headline shape

`dsdp_experiment_hops` (`dsdp_main.v:118`) computes `count_obs_hops (corrupted_view
dsdp_experiment) = 2` by `Proof. by []. Qed.`, so at the DSDP instance the sum has two
summands:

```coq
Theorem dsdp_alice_guess_V2_real_le ... :
  guess_sdistr_success_real ...
  <= card_msg%:R^-1
     + indcpa_advantage ... (guess_reduction ∘ shim_0)
     + indcpa_advantage ... (guess_reduction ∘ shim_1).
```

`dsdp_alice_guess_V2_zero_le` keeps a byte-identical statement. The Infotheo bridge is
untouched: `sdistr_to_fdist` (`dsdp/convert/dsdp_convert.v:62`) repackages the same mass
function at the same realType (`Notation R := SSProve.Crypt.Axioms.R`, `:41`), and
`guess_success_sdistr_eq_fdist` (`dsdp_guess_fiber.v:233`) is an equality of reals. The
composition at `dsdp_main.v:769-781` is ordered-field reasoning only, so changing the
shape of the second summand does not touch it.

### `log_id` must be generalized

`log_id` (`dsdp_guess_fiber.v:1772`) states
`- log (m%:R^-1 + 2%:R * eps) = log m%:R - log (1 + 2%:R * m%:R * eps)`. The factor 2 is
baked into the statement, and the new bound is not of that shape. The factor plays no
role in the proof. The generalization compiles against the project switch:

```coq
Lemma log_id_gen (m : nat) (d : R) : (0 < m)%N -> (0 <= d)%R ->
  (- log (m%:R^-1 + d) = log m%:R - log (1 + m%:R * d))%R.
```

Same proof skeleton, with `mulrAC` replaced by `[(m%:R * d)%R]mulrC` before `mulfK`.
`dsdp_alice_unpredictability_entropy_ge` (`dsdp_main.v:789`) becomes
`log card_msg - log (1 + card_msg * (adv_0 + adv_1)) <= Hunp_leak_S`, still approaching
`log card_msg` as the advantages vanish.

Its hypothesis `epsilon_cpa_ge0` (`dsdp_main.v:800`) becomes provable, since
`indcpa_advantage` is a `normr`, so `sumr_ge0` and `normr_ge0` discharge it. Delete the
hypothesis rather than restating it.

### `adv_sim_le` needs an adversary-indexed bound

`adv_sim_le` (`smc/ssprove_ext_simulator.v:42`) binds `eps : R` before the adversary:

```coq
Definition adv_sim_le (Real Ideal Sim : raw_package) (eps : R) : Prop :=
  forall LA A, ValidPackage LA E A_export A -> adm LA A ->
    AdvantageE Real (Sim ∘ Ideal) A <= eps.
```

A reduction bound depends on `A` and cannot be stored in a slot that cannot see it. The
signature becomes `eps : raw_package -> R` with conclusion `<= eps A`, the shape
SSProve's `adv_equiv` already uses (`pkg_advantage.v:86-93`). `adv_sim_le_from_endpoint`
(`:53`) and `adv_sim_le_reduction` (`:73`) adapt, the latter concluding `<= eps (A ∘ T)`.

### Deletions

`epsilon_cpa` and `enc_ind_cpa_real_or_zero` (`indcpa_ror.v:241`, `:256`), together with
the trailing `Check @enc_ind_cpa_real_or_zero.` at `:279`.

`epsilon_cpa_idealized_ge1` (`idealized_indcpa.v:157`) loses its subject. Its own
`Used by: regression guard on the [epsilon_cpa] signature` at `:156` is self-referential,
no `_CoqProject` file consumes it. Delete the lemma but keep the directory:
`advantage_idealized_eq1` (`:143`) states
`AdvantageE idealized_oracle_real idealized_oracle_zero idealized_distinguisher = 1`,
which under the new design is definitionally
`indcpa_advantage idealized_ahe_f2 ... idealized_distinguisher = 1`. Restated in those
terms it becomes the vacuity guard for the new functional, proving `indcpa_advantage` is
not identically zero. The file header at `:5`, `:40`, `:42`, `:75`, `:84` is rewritten to
explain why no constant bound is used at all.

`dsdp_alice_view_statdist_le` (`dsdp_main.v:903`) is deleted. Its statement contains no
adversary, and its proof manufactures `Dstar`, the optimal statistical test
(`smc/ssprove_ext_statdist.v:75`), wrapping it with `test_adversary`
(`dsdp_simulator.v:331`). Under the reduction form the bound would name that test as its
own reduction, and no computational assumption can bound the optimal test. Under the
current `epsilon_cpa` form the headline is already empty for the same reason, so this is
a deletion of something that never held computational content, not a loss.

Consequently dead, to be removed in the same phase after confirming no other consumer:
`smc/ssprove_ext_statdist.v` (its only `Require` is `dsdp_main.v:58`), and
`view_real_mass1` and `view_simulated_mass1`, used only at `dsdp_main.v:924` and `:927`.
`_CoqProject:101` drops the statdist entry. `dumas2017dual/dsdp/simulation/probe_p3_statdist.v`
is absent from `_CoqProject` and is left alone.

No project axiom remains after this. The `computational/` directory proposed in the
superseded spec is not created, because its intended contents cease to exist.

### Rename

| Before | After | Type before | Type after |
|---|---|---|---|
| `adm` (`smc/ssprove_ext_simulator.v:36`) | `locs_disjoint` | `Locations -> raw_package -> Prop` | `Locations -> Prop` |
| `dsdp_adm` (`dsdp_simulator.v:225`) | `dsdp_locs_disjoint` | `Locations -> raw_package -> Prop` | `Locations -> Prop` |

Occurrences: `smc/ssprove_ext_simulator.v` 9, `dsdp_simulator.v` 5,
`probe_p5_skeletons.v` 15 (11 bare `adm` plus 4 `dsdp_adm`). The probe file is absent
from `_CoqProject` and is updated only to avoid leaving contradictory vocabulary.

`adv_sim_le_reduction` (`ssprove_ext_simulator.v:73`, with the `AT_adm` binder at `:78`)
genuinely uses the package argument. Under `dsdp_adm` the body ignores it, so
`adm LAT (A ∘ T)` and `dsdp_locs_disjoint LAT` are interchangeable at the sole
instantiation, and the arity drop is sound there. The generic lemma loses the ability to
express a package-dependent location condition. Since `adv_sim_le` has exactly one
consumer (`dsdp_adv_sim_le`, `dsdp_simulator.v:279`), this is recorded and accepted.

Blueprint references `dsdp_adv_sim_le` (`security.tex:196`), whose name does not change.

## Costs

1. Headline statements grow. `2 * epsilon_cpa AHE` becomes two `indcpa_advantage` terms
   carrying full parameter lists. Generic ladder lemmas carry a `\sum` rather than a
   product, and right-hand sides now embed validity proof terms.
2. The ladder induction moves from arithmetic on a constant multiple to `bigop`
   reasoning, with an `eq_bigr` realignment the current proof does not need.
3. Every blueprint and thesis passage writing the bound as `1/m + 2 eps` is restated.
   The claim that these terms are small under a standard assumption moves from a formal
   axiom to a cited sentence, as `StretchPRG.v:165` does.
4. `idealized_indcpa.v` loses its headline and keeps a rewritten one.
5. `adv_sim_le` loses package-dependent location conditions.
6. One headline is deleted outright.

Not a cost: no result becomes unreachable. Every current bound is recovered by anyone
supplying a bound on `indcpa_advantage` for their scheme and adversary class, and the
current statement is the special case where that bound is a constant.

## Phases

Each phase builds clean and is committed before the next begins, except where noted.

**Phase 1. Rename.** `adm` to `locs_disjoint`, `dsdp_adm` to `dsdp_locs_disjoint`, arity
dropped, `adv_sim_le_reduction` adjusted, probe file updated. Independent of the rest.

**Phase 2. Delete the statdist headline.** Remove `dsdp_alice_view_statdist_le`, its
`Require` at `dsdp_main.v:58`, the header index entry at `:36`, `view_real_mass1` and
`view_simulated_mass1`, `smc/ssprove_ext_statdist.v`, and `_CoqProject:101`. Remove the
blueprint node at `security.tex:224-231` and any `\uses` pointing at
`thm:alice_view_statdist`. Doing this first shrinks the surface every later phase must
convert.

**Phase 3. Add `indcpa_advantage` and generalize `log_id`.** Definition plus
`log_id_gen`, nothing consumes them yet. Build green.

**Phase 4. `adv_sim_le` signature.** `eps : raw_package -> R` in
`smc/ssprove_ext_simulator.v`, with `dsdp_adv_sim_le` passing a constant function so the
phase compiles before the bounds change.

**Phase 5. Chain I.** Restate `advantage_hop`, `advantage_sum_ladder_le`,
`advantage_le`, `advantage_gc_dsdp` (`dsdp_game_code.v:886, 930, 973, 1064`) and
`dsdp_indcpa_secrecy` (`dsdp_game_derivation.v:691`), then `dsdp_advantage_derived`
(`dsdp_indcpa_advantage.v:63`) and `dsdp_alice_view_advantage_le` (`dsdp_main.v:128`).

**Phase 6. Chain II.** Same for `advantage_hop_leak_S`,
`advantage_sum_ladder_le_leak_S`, `advantage_le_leak_S`,
`dsdp_advantage_derived_leak_S` (`dsdp_indcpa_advantage.v:249, 294, 329, 405`), then
`dsdp_adv_sim_le` (`dsdp_simulator.v:279`) and the four remaining `dsdp_main.v`
headlines at `:726, 756, 789, 850`.

**Phase 7. Delete the axiom.** Remove `epsilon_cpa`, `enc_ind_cpa_real_or_zero`, the
trailing `Check`, and `epsilon_cpa_idealized_ge1`, and restate
`advantage_idealized_eq1`. This phase cannot compile until every consumer is converted,
which is what proves the axiom was never needed.

This phase also edits `blueprint/src/content.tex:476-477`, a `\rocq{}` node citing both
deleted declarations. `check_coverage.py` fails the moment the declarations disappear,
so that edit belongs here rather than in Phase 8.

**Phase 8. Documentation sweep.** Stale comments in `idealized_indcpa.v:5, 40, 42, 75,
84`; `indcpa_ror.v:1-24, 233-240, 243-255`; `dsdp_game_code.v:873, 877, 884, 916, 921,
961, 966, 1058`; `dsdp_game_derivation.v:5-6, 209, 686, 689`;
`dsdp_indcpa_advantage.v:1-12, 58, 246, 248, 292, 325, 401, 403`;
`dsdp_simulator.v:275-277`; `dsdp_main.v:1-38, 121-127, 721-724, 750-755, 785-788,
843-849`. Blueprint `\epscpaof` occurrences: `content.tex` 12, `security.tex` 15,
`it_bound_bridge.tex` 1. Thesis wording pass.

Phase ordering rationale: converting consumers before deleting the axiom keeps every
intermediate state compilable. Phase 7 failing to compile signals a missed consumer.

## Verification

- Full-tree `make` under the local `~/Projects/coq/_opam` switch, per phase.
- After Phase 7, `Print Assumptions` on each remaining `dsdp_main.v` headline must
  contain no project declaration. The residual entries are upstream. Generate the
  allowlist by running the command and committing its output rather than asserting it
  in advance. Known members include `boolp.propositional_extensionality`,
  `boolp.functional_extensionality_dep`,
  `FunctionalExtensionality.functional_extensionality_dep`,
  `boolp.constructive_indefinite_description`, `SPropBase.ax_proof_irrel`,
  `Axioms.R` and the `absord` / `unlock_absord` declared alongside it, and
  `realsum.__admitted__interchange_psum`.
- `dumas2017dual/blueprint/check_coverage.py` returns OK after Phase 7.
- `dsdp_alice_guess_V2_zero_le` and `dsdp_simulator_factorization` have unchanged
  statements before and after, compared as proof terms rather than printed forms.

## Follow-up recorded, not scheduled

`realsum.__admitted__interchange_psum` is an `Admitted` lemma in mathcomp
`experimental_reals`, used at `distr.v:516`, sitting in the trust base of every
headline. Unrelated to this work and predating it, but it belongs in any honest account
of what the development assumes. Worth its own note.

Connecting `indcpa_advantage` at Paillier to DCR is separate work. The interface for it
is exactly the `indcpa_advantage` terms this design exposes.
