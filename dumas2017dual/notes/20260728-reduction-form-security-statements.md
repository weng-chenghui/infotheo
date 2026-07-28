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
- `MACCCA.v:440` and `SymmRatchet.v:430` name this quantity at an IND-CPA game pair
  `cpa_epsilon := Advantage CPA_EVAL` and `cpa_epsilon := Advantage CTXT`. That is the
  direct analogue of what this design introduces.
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
Definition indcpa_epsilon
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

Because `indcpa_epsilon` takes `renc_card : #|Renc| = card_renc` and the oracles use
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
  <= indcpa_epsilon ... (A ∘ denote_game_shim_leak_S (zero_hop_prefix i gc) i).
```

The goal after `rewrite -Advantage_link` is closed by `exact: lexx`, not `reflexivity`,
since the goal is an inequality. Same for `advantage_hop` (`dsdp_game_code.v:886`),
whose axiom application is at `:909`.

### The ladder sums instead of multiplying

`advantage_sum_ladder_le_leak_S` (`:294`) currently concludes
`<= n.+1%:R * epsilon_cpa AHE`. It becomes

```coq
  <= \sum_(l < n.+1) indcpa_epsilon ...
       (A ∘ denote_game_shim_leak_S (zero_hop_prefix (start + l) gc) (start + l)).
```

The sum covers sites `start .. start + n`, exactly the `n+1` rungs, so there is no
off-by-one.

The split probably wants `big_ord_recl` rather than `big_ord_recr`, but this must be
probed before it is relied on, because SSProve's own structurally similar ladder proof
uses `big_ord_recr` (`PRFPRG.v:348`, in `hyb_security_based_on_prf`). The argument for
`recl` here: `advantage_sum` peels the head
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
     + indcpa_epsilon ... (guess_reduction ∘ shim_0)
     + indcpa_epsilon ... (guess_reduction ∘ shim_1).
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
role in the proof, and a generalization over a plain `d` compiles against the project
switch, with `mulrAC` replaced by `[(m%:R * d)%R]mulrC` before `mulfK`.

The naming audit rejects keeping this as a named lemma at all. `log_id` squats on the
live `log_id_cmp` / `log_id_eq` / `log_id_diff` family
(`lib/realType_ln.v:239`, `probability/divergence.v:55, 63`) where `id` really is the
identity function, and no suffix chain in the `logK` / `logV` / `logM` / `logDiv` family
(`lib/realType_ln.v:188, 191, 194, 227`) can name the generalized statement, because
unlike every member of that family its suffixes would not determine the right-hand side.
That is evidence the statement is an unfactored composite.

Preferred: delete it and expand at the call site. `addf_div`
(`mathcomp/algebra/ssralg.v:4768`) turns `m%:R^-1 + x` into a single quotient, `divr1`
cleans up, and `logDiv` finishes. Two rewrites where a lemma used to be, and §18 wants
auxiliary results minimized. Fallback if the call site is unreadable: `Local Lemma
log_invD (m : nat) (x : R)`, underscore before the lowercase `inv` per §10, binder `x`
per §14, which assigns `d` to naturals.

`dsdp_alice_unpredictability_entropy_ge` (`dsdp_main.v:789`) becomes
`log card_msg - log (1 + card_msg * (adv_0 + adv_1)) <= Hunp_leak_S`, still approaching
`log card_msg` as the advantages vanish.

Its hypothesis `epsilon_cpa_ge0` (`dsdp_main.v:800`) becomes provable, since
`indcpa_epsilon` is a `normr`, so `sumr_ge0` and `normr_ge0` discharge it. Delete the
hypothesis rather than restating it.

### `advantage_sim_le` needs an adversary-indexed bound

`adv_sim_le` (`smc/ssprove_ext_simulator.v:42`) binds `eps : R` before the adversary:

```coq
Definition adv_sim_le (Real Ideal Sim : raw_package) (eps : R) : Prop :=
  forall LA A, ValidPackage LA E A_export A -> adm LA A ->
    AdvantageE Real (Sim ∘ Ideal) A <= eps.
```

A reduction bound depends on `A` and cannot be stored in a slot that cannot see it. It
becomes `bound : raw_package -> R` with conclusion `<= bound A`, the shape SSProve's
`adv_equiv` already uses (`pkg_advantage.v:86-93`). The three lemmas are renamed off the
overloaded `adv` at the same time, per the naming audit:

```coq
Context (E : Interface) (admissible : Locations -> raw_package -> Prop).

Definition advantage_sim_le (Real Ideal Sim : raw_package)
    (bound : raw_package -> R) : Prop :=
  forall (LA : Locations) (A : raw_package),
    ValidPackage LA E A_export A -> admissible LA A ->
    AdvantageE Real (Sim ∘ Ideal) A <= bound A.
```

`advantage_sim_le_from_endpoint` (`:53`) and `advantage_sim_le_reduction` (`:73`) adapt,
the latter concluding `<= bound (A ∘ T)`.

### Deletions

`epsilon_cpa` and `enc_ind_cpa_real_or_zero` (`indcpa_ror.v:241`, `:256`), together with
the trailing `Check @enc_ind_cpa_real_or_zero.` at `:279`.

`epsilon_cpa_idealized_ge1` (`idealized_indcpa.v:157`) loses its subject. Its own
`Used by: regression guard on the [epsilon_cpa] signature` at `:156` is self-referential,
no `_CoqProject` file consumes it. Delete the lemma but keep the directory:
`advantage_idealized_eq1` (`:143`) states
`AdvantageE idealized_oracle_real idealized_oracle_zero idealized_distinguisher = 1`,
which under the new design is definitionally
`indcpa_epsilon idealized_ahe_f2 ... idealized_distinguisher = 1`. Restated in those
terms it becomes the vacuity guard for the new functional, proving `indcpa_epsilon` is
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

| Before | After | Type change |
|---|---|---|
| `adm` (`smc/ssprove_ext_simulator.v:36`) | `admissible` | none, stays `Locations -> raw_package -> Prop` |
| `dsdp_adm` (`dsdp_simulator.v:225`) | `dsdp_locs_disjoint` | drops to `Locations -> Prop` |
| `adv_sim_le`, `_from_endpoint`, `_reduction` (`:42, 53, 73`) | `advantage_sim_le`, `_from_endpoint`, `_reduction` | `eps : R` becomes `bound : raw_package -> R` |
| `dsdp_adv_sim_le` (`dsdp_simulator.v:279`) | `dsdp_advantage_sim_le` | as above |
| `gc_dsdp`, `hop_sites_gc_dsdp`, `advantage_gc_dsdp` (`dsdp_game_code.v:1029, 1053, 1064`) | `game_code_dsdp`, `hop_sites_game_code_dsdp`, `advantage_game_code_dsdp_le` | none |
| `dsdp_advantage_derived`, `_leak_S` (`dsdp_indcpa_advantage.v:63, 405`) | `dsdp_derived_game_advantage_le`, `_leak_S` | none |
| `dsdp_indcpa_secrecy` (`dsdp_game_derivation.v:691`) | `dsdp_indcpa_secrecy_le` | none |
| `dsdp_alice_simulation_secure` (`dsdp_main.v:850`) | `dsdp_alice_simulation_advantage_le` | none |
| `advantage_idealized_eq1` (`idealized_indcpa.v:143`) | `indcpa_epsilon_idealized_eq1` | restated over `indcpa_epsilon` |

The abstract parameter keeps both its arity and a deliberately unspecific name.
`smc/ssprove_ext_simulator.v:36` is a `Context` parameter, not a definition, so naming it
after its one current instantiation would make a generic file assert a property it does
not know. `advantage_sim_le_reduction` (`:73`, with its binder at `:78`) genuinely uses
the package argument in `admissible LAT (A ∘ T)`. DSDP instantiates with
`fun LA _ => dsdp_locs_disjoint LA`, which puts the ignored argument at the one place
where it is genuinely ignored.

`adm` occurrences: `smc/ssprove_ext_simulator.v` 9, `dsdp_simulator.v` 5,
`probe_p5_skeletons.v` 15 (11 bare `adm` plus 4 `dsdp_adm`). The probe file is absent
from `_CoqProject` and is updated only to avoid leaving contradictory vocabulary.

Blueprint `security.tex:196` cites `dsdp_adv_sim_le` and must be updated in the same
phase as that rename.

## Naming audit

Every identifier this design creates, renames, or whose statement it changes, checked
against `mathcomp-skills/reference.md` §10 (`mainSymbol_suffixes`, underscore rule,
head-of-LHS, avoid overly generic), §11 (abbreviation table), §13 (definitions are
`snake_case`), §14 (binder names), §18 (auxiliary results are `Local` / `Let` / `Fact`),
and against the project rules: strict `snake_case` except paper-form variables, no
semantic-stripping abbreviations, SSProve-extension identifiers follow SSProve house
style where that does not conflict.

A restated lemma is in scope even when its name is unchanged, because a name can stop
describing its statement.

### Created

| Name | Kind | Verdict | Rule |
|---|---|---|---|
| `indcpa_epsilon` | Definition | accept | §13 `snake_case`; matches SSProve's `cpa_epsilon` (`MACCCA.v:440`, `SymmRatchet.v:430`), which names exactly this quantity at exactly this game pair |

An earlier draft proposed `indcpa_advantage` on the grounds that `epsilon` connotes a
constant. That reason does not survive its own evidence. Upstream's `_epsilon` names are
already adversary-indexed, as this spec's own Approach section shows by citing
`PRF.v:323`, so the misreading feared does not occur in the corpus being deviated from.
The draft also kept `eps` for the adversary-indexed bound in `adv_sim_le`, which made
the objection incoherent. Both are resolved: `indcpa_epsilon` here, `bound` there.

An earlier draft also proposed `logVD` for the generalized `log_id`. Rejected. The repo
owns `logK` / `logV` / `logM` / `logDiv` (`lib/realType_ln.v:188, 191, 194, 227`), and in
every member the suffix chain determines the right-hand side, which `logVD` would not.
Next to `logV` it would misparse as a variant about `log` of an inverse. Its argument's
head operation is `+` with the inverse nested, so even on its own scheme the chain reads
outside-in as `DV`. The statement is deleted rather than renamed, per the Design section.

### Renamed

| Before | After | Verdict | Rule |
|---|---|---|---|
| `adm` (abstract `Context` param) | `admissible` | accept | §10; an abstract parameter must not be named after its one instantiation |
| `dsdp_adm` | `dsdp_locs_disjoint` | accept | §13; `locs` is SSProve's own record field (`pkg_core_definition.v:615`), not a coinage; `disjoint` is SSProve's own gloss of `fseparate` (`fmap_extra.v:26`) |
| `adv_sim_le` and its two lemmas | `advantage_sim_le`, `_from_endpoint`, `_reduction` | accept | project abbreviation ban; `adv` is overloaded in-repo, meaning *adversary* in `adv_package` / `adv_valid` / `adv_locations` (`dsdp_game_derivation.v:675-678`) and *advantage* here |
| `dsdp_adv_sim_le` | `dsdp_advantage_sim_le` | accept | as above |
| `eps` binder | `bound` | accept | consistency with the `indcpa_epsilon` decision above |
| `gc_dsdp`, `hop_sites_gc_dsdp`, `advantage_gc_dsdp` | `game_code_dsdp`, `hop_sites_game_code_dsdp`, `advantage_game_code_dsdp_le` | accept | project abbreviation ban; `gc` strips `game_code`. Not `dsdp_game_code`, which collides with the module name. `_le` added per §10 |
| `dsdp_advantage_derived`, `_leak_S` | `dsdp_derived_game_advantage_le`, `_leak_S` | accept | §10; a `<=` statement whose every sibling carries `_le`. `derived` survives, qualifying the auto-derived game per `dsdp_indcpa_advantage.v:56` |
| `dsdp_indcpa_secrecy` | `dsdp_indcpa_secrecy_le` | accept | §10; `<=` statement with no shape suffix |
| `dsdp_alice_simulation_secure` | `dsdp_alice_simulation_advantage_le` | accept | §10; `secure` is a claim word, the statement is `AdvantageE _ _ _ <= _` |
| `advantage_idealized_eq1` | `indcpa_epsilon_idealized_eq1` | accept | §10 head-of-LHS; restating it over `indcpa_epsilon` changes the LHS head |
| `log_id` | deleted | accept | see Created above |

### Restated, name kept

| Name | Verdict | Rule |
|---|---|---|
| `advantage_hop`, `advantage_hop_leak_S` | accept | §10; LHS head and the `hop` shape are unchanged, and the name never claimed a bound shape |
| `advantage_sum_ladder_le`, `_leak_S` | accept | §10 head-of-LHS; the LHS head remains SSProve's `advantage_sum` (`pkg_advantage.v:197`). The right-hand side becoming a `\sum` is a second, different sum, which is a readability cost recorded here rather than a naming error |
| `advantage_le`, `advantage_le_leak_S` | accept | §10 |
| `dsdp_alice_guess_V2_zero_le`, `_real_le` | accept, exception E2 | §10; `_le` standard |
| `dsdp_alice_unpredictability_entropy_ge` | accept | §10; `_ge` standard |
| `dsdp_alice_view_advantage_le`, `dsdp_alice_guess_advantage_le` | accept | §10 |

`dsdp_alice_guess_V2_real_le` does carry one §10 deviation not covered by any exception:
`guess` truncates the statement's head symbol `guess_sdistr_success_real`. Recorded and
tolerated, since spelling it out would make an already long headline unreadable and the
truncation is unambiguous inside the `dsdp_alice_guess` family.

### Binders and local names introduced by this design

`shim_0` and `shim_1` appear in the Headline shape display purely as abbreviations for
`denote_game_shim_leak_S (zero_hop_prefix i gc) i` at `i = 0, 1`. They are display
shorthand for this document and must not become identifiers. Same for `adv_0`, `adv_1`,
which would additionally re-import the overloaded `adv`. Where the sum is written out at
the DSDP instance, the terms are spelled in full.

If the fallback `log_invD` is taken, its binder is `x : R`, not `d : R`. §14 assigns `d`
to naturals and integers, and ring elements to `x, y, z, u, v, w`.

### Exceptions

**E1 was withdrawn.** An earlier draft claimed the subject prefix in `dsdp_alice_*`
deviates from §10's head-symbol-first rule. It does not. §10's "avoid overly generic
names", with PR #1624 preferring `hoelder_conjugate` over `conjugate`, endorses theory
qualifiers, and `dsdp_alice_` is exactly that form. There was nothing to excuse.

**E2. Capitalized `V2` inside a `snake_case` identifier.** Backed by the written project
rule that variables carrying a math-notation name from the source paper keep their paper
form, not by preference. `V2` and `V3` are the protocol's inputs in Dumas 2017 and `S` is
its scalar-product output, so `_leak_S` is the same case. Precedent: `bob_privacy_V3`
(`dsdp_main.v:573`), `charlie_privacy_V2` (`:636`).

**E3 was withdrawn.** See the `indcpa_epsilon` entry above.

### Noticed, out of scope

`advantage_self_zero` (`dsdp_game_code.v:955`) concludes `= 0` and would be `_eq0` in
mathcomp. `Hunp_leak_S` is a capital-prefixed abbreviation. Neither statement is changed
by this design, so neither is renamed here.

## Proof workflow

Every proof obligation in this design is discharged through the Rocq skill stack, not by
hand-editing tactic scripts.

- **`mathcomp-skills`** is consulted before writing any tactic. `templates.md` for a
  goal shape, `phrasebook.md` for an intent, `proof-development.md` for the
  inspect-search-battery-commit loop, `errors.md` for any `coqc` message. The bigop work
  in Phases 5 and 6 specifically wants `reference.md` §34 and §34.7.
- **`rocq:autoprove`** drives the multi-cycle proving for each converted lemma, with its
  hard stop rules. The ladder inductions are the cycles most likely to need it.
- Live iteration uses the rocq-mcp loop rather than repeated `coqc`: warm the imports
  once via `rocq_start preamble=...`, find a winner with `rocq_step_multi` without
  advancing state, commit it with `rocq_check`, extract `proof_tactics`.
- `rocq_assumptions` is run per converted headline, which is also how the Phase 7
  allowlist is generated.
- `rocq-auditor` Stage 2 remains a mandatory pre-commit gate for every phase that adds
  an identifier or a proof body. Phases that are pure deletion or mechanical rename
  (Phases 1, 2, and the deletion half of Phase 7) use `ROCQ_AUDIT_BYPASS=1`.
- The bundled `audit-quick.sh` `PostToolUse` hook fires on each edited `.v` file. Its
  findings are advisory, but the 80-column rule (§1) will bite: `indcpa_epsilon` terms
  carry full parameter lists, so restated statements need deliberate line breaking.

## Costs

1. Headline statements grow. `2 * epsilon_cpa AHE` becomes two `indcpa_epsilon` terms
   carrying full parameter lists. Generic ladder lemmas carry a `\sum` rather than a
   product, and right-hand sides now embed validity proof terms.
2. The ladder induction moves from arithmetic on a constant multiple to `bigop`
   reasoning, with an `eq_bigr` realignment the current proof does not need.
3. Every blueprint and thesis passage writing the bound as `1/m + 2 eps` is restated.
   The claim that these terms are small under a standard assumption moves from a formal
   axiom to a cited sentence, as `StretchPRG.v:165` does.
4. `idealized_indcpa.v` loses its headline and keeps a rewritten one.
5. One headline is deleted outright.
6. Ten identifier families are renamed, several of them cited across `notes/` and one
   (`dsdp_adv_sim_le`) cited by the blueprint.

Not a cost: no result becomes unreachable. Every current bound is recovered by anyone
supplying a bound on `indcpa_epsilon` for their scheme and adversary class, and the
current statement is the special case where that bound is a constant.

## Phases

Each phase builds clean and is committed before the next begins, except where noted.

**Phase 1. Renames, no statement changes.** Every rename in the naming audit's Renamed
table except `advantage_idealized_eq1`, which is tied to Phase 7's restatement, and
`log_id`, whose deletion is Phase 3. So: `adm` to `admissible` (arity unchanged),
`dsdp_adm` to `dsdp_locs_disjoint` (arity dropped, instantiated as
`fun LA _ => dsdp_locs_disjoint LA`), the `adv_sim_le` trio to `advantage_sim_le`, the
`gc_dsdp` trio to `game_code_dsdp`, `dsdp_advantage_derived` and `_leak_S` to
`dsdp_derived_game_advantage_le`, `dsdp_indcpa_secrecy` to `_le`,
`dsdp_alice_simulation_secure` to `dsdp_alice_simulation_advantage_le`, probe file
updated. Blueprint `security.tex:196` cites `dsdp_adv_sim_le` and is edited here. Pure
renaming, so `ROCQ_AUDIT_BYPASS=1`, and `check_coverage.py` must pass before the commit.

**Phase 2. Delete the statdist headline.** Remove `dsdp_alice_view_statdist_le`, its
`Require` at `dsdp_main.v:58`, the header index entry at `:36`, `view_real_mass1` and
`view_simulated_mass1`, `smc/ssprove_ext_statdist.v`, and `_CoqProject:101`. Remove the
blueprint node at `security.tex:224-231` and any `\uses` pointing at
`thm:alice_view_statdist`. Doing this first shrinks the surface every later phase must
convert.

**Phase 3. Add `indcpa_epsilon` and retire `log_id`.** The definition, plus expanding
`log_id`'s single call site into `addf_div` / `divr1` / `logDiv`. If that call site reads
badly, keep `Local Lemma log_invD` instead. Nothing consumes `indcpa_epsilon` yet.

**Phase 4. `advantage_sim_le` signature.** `bound : raw_package -> R` in
`smc/ssprove_ext_simulator.v`, with `dsdp_advantage_sim_le` passing a constant function
so the phase compiles before the bounds change.

Phases 5 onward use the post-Phase-1 names.

**Phase 5. Chain I.** Restate `advantage_hop`, `advantage_sum_ladder_le`,
`advantage_le`, `advantage_game_code_dsdp_le` (`dsdp_game_code.v:886, 930, 973, 1064`)
and `dsdp_indcpa_secrecy_le` (`dsdp_game_derivation.v:691`), then
`dsdp_derived_game_advantage_le` (`dsdp_indcpa_advantage.v:63`) and
`dsdp_alice_view_advantage_le` (`dsdp_main.v:128`).

**Phase 6. Chain II.** Same for `advantage_hop_leak_S`,
`advantage_sum_ladder_le_leak_S`, `advantage_le_leak_S`,
`dsdp_derived_game_advantage_le_leak_S` (`dsdp_indcpa_advantage.v:249, 294, 329, 405`),
then `dsdp_advantage_sim_le` (`dsdp_simulator.v:279`) and the four remaining
`dsdp_main.v` headlines at `:726, 756, 789, 850`.

**Phase 7. Delete the axiom.** Remove `epsilon_cpa`, `enc_ind_cpa_real_or_zero`, the
trailing `Check`, and `epsilon_cpa_idealized_ge1`, and restate `advantage_idealized_eq1`
as `indcpa_epsilon_idealized_eq1`. This phase cannot compile until every consumer is
converted, which is what proves the axiom was never needed.

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

Connecting `indcpa_epsilon` at Paillier to DCR is separate work. The interface for it
is exactly the `indcpa_epsilon` terms this design exposes.
