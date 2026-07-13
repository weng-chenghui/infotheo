# pgl27 boundary closure + realistic-shuffle mixing: design (2026-07-13)

Three-part round: (1) close the three residual claim-matrix cells,
(2) record the claim matrix and the termination boundary in a
committed note, (3) open the one chosen model extension: an in-kernel
mixing bound for the realistic L-word shuffle. Parts 1 and 2 freeze
the exact-shuffle model; part 3 is the only deliberate enlargement,
gated by the boundary rule itself.

## Part 0 — the boundary rule (what makes this terminate)

Issues divide into three types. Type A: unfilled cells of the finite
claim matrix (dealer model x observer model x threshold) of the FIXED
model; closing a cell never creates a cell, so type A converges. Type
B: model extensions (mixing, active adversaries, composition, formal
reveal phase, quantitative leakage, sibling-instance lifts, framework
semantics); every model extends forever, so type B must be gated by
prose claims, not audit pressure. Type C: the trust base (boolp trio,
kernel VM); fixed floor.

The rule, recorded in the closure note of Part 2:

> pgl27 is closed when every prose sentence about it maps either to a
> Qed theorem in a committed file or to an explicitly disclosed
> non-claim in the same document. New work enters only when a new
> prose claim needs it, and each such claim opens its own spec with
> its own finite matrix.

Part 3 (mixing) is exactly such an entry: it licenses the prose claim
"privacy holds under a realistic word-of-generators shuffle", which
the current artifact does not make.

## Part 1 — the three residual Type A cells

All statements live in the existing files; ~50-70 lines total; no new
machinery; no ripple.

| Cell | Statement sketch | Discharge |
|------|------------------|-----------|
| Shuffle-free trace secrecy | `pgl27_deck_trace_secrecy` (+ coalition form): over `uniform_deckP`, the executed trace at the identity cut is the dealt card; `H(secret \| trace) = H(secret)` | run at cut `1%g`; trace = `tnth u.2 i` via `pgl27_abs_p<k>` at `w0 := 1` (`morph1` + `perm1`, no group membership needed); keystone with `pgl27_view_indep_deck` |
| Class-proportional prior | `pgl27_view_indep_deck_prior`: the generic `ttrans_view_indep_deck` instantiated at an arbitrary `secretP : R.-fdist bool`, PLUS the deck-marginal identification lemma: at the class-proportional prior (28/70, 42/70) the dealt-deck marginal is uniform over all valid decks, each deck getting `(#\|class s\|/70) * (1/#\|class s\|) = 1/70`-scaled mass; consumes `orbit_class_split` (audited: the bridge alone does not provide this reading) | direct application + a ~30-line marginal lemma |
| Sub-6 ambiguity | `pgl27_reveal_ambiguous`: for every position set D with `#\|D\| <= 6` there are two valid decks of opposite classes agreeing on D | from `pgl27_six_reveal_ambiguous` at any pair {p, q} disjoint from D (exists since `#\|~:D\| >= 2`); the witness pair agrees off {p,q} hence on D |

Placement: cells 1-2 in `pgl27_trace.v` / `pgl27_secrecy.v`
respectively; cell 3 in `pgl27_recovery.v`. Naming pre-checked: all
at most 4 components.

## Part 2 — the closure note

New file `pgg-smc/notes/20260713-pgl27-claim-boundary.md` (the
`pgg-smc/notes/` `YYYYMMDD-kebab` convention): the full claim matrix with one row per
proven statement (lemma name, file, dealer model, observer model,
threshold, axiom status), the disclosed non-claims (verifier learns
by design; post-reveal out of model; passive adversary; single
execution; exact-uniform shuffle until Part 3 lands), the trust base,
and the boundary rule of Part 0. One docs commit, updated only when a
new claim lands.

## Part 3 — realistic-shuffle mixing (the chosen Type B extension)

### Model and target

The realistic shuffle is a uniform random word of length L over the
inverse-closed generator list
`[tr_perm; tr_perm^-1; sc_perm; sc_perm^-1; inv_perm]` (five
entries; `inv_perm` is an involution). The framework already models
this: `word_weighted`/`rho_from_words_weighted`
(`pgg_weighted_words.v:60-99`) give the L-word shuffle law as an
`R.-fdist {perm 'I_N}` with `fiber_prob_weighted` characterising each
element's probability as its word-fiber weight.

Headline target (group-level, subsumes the single-card bound):

```
pgl27_word_mixing :
  var_dist (rho_from_words_weighted (L := 200) pgl27_sym_sigmas Wuni)
           (`U pgl27_G_pos)
  <= 2^-40
```

with the single-card corollary
`var_dist (endpoint_dist_weighted ... s) (fdist_uniform card8) <= 2^-40`
by pushforward monotonicity, and (stretch) approximate coalition
privacy: the exact `pgl27_view_indep` transfers to the L-word shuffle
with additive slack `<= 2^-40` in the independence products.

### Probe evidence (2026-07-13, this session)

Python, EXACT integer arithmetic on the verified 336-element closure
(numerators over denominator `5^L`): the group walk reaches full-L1
`var_dist < 2^-40` at exactly L = 193 (8.933e-13, a 1.8% margin);
at L = 200 the exact value is 3.176e-13, a 2.9x margin. L = 200 is
frozen. Per-start endpoint walks mix at L* = 185..192 (float probe).

Arithmetic layer (audited, blocking fix): MathComp `nat` is unary —
`5^200` is not representable, so the walk and checker live in BINARY
integers (Stdlib `N` via ssrnat's `nat_of_bin`/`bin_of_nat` with the
`nat_of_add_bin`/`nat_of_mul_bin` morphisms), where `vm_compute` at
465 bits x 336 entries x 200 steps is trivial. A reflection bridge
relates the N-level walk to the nat-level fiber counts pointwise
(induction on L through the shared successor structure; absolute
differences via comparison-guarded subtraction, avoiding truncation).
`lia`/`zify` are NOT planned; if an unavoidable scalar leaf appears,
the landed `five_card_kim.v` precedent (`by lia` on a nat leaf) is
the sanctioned fallback, recorded here as an explicit decision.

### Approaches considered

- **A (chosen): exact in-kernel matrix powering** at the nat level
  over the 336-entry closure list, checker by `vm_compute`, bridged
  to `rho_from_words_weighted` by a fiber-counting induction. No
  spectral theory, no eigenvalue certificate, no axiom.
- B: SchreierCertificate route (`pgg_schreier.v`) with a spectral-gap
  certificate. Rejected: the wreath precedent needed a Rayleigh
  axiom; pgl27's headline is axiom-freeness.
- C: kim's closed-form eigenvalue route. Rejected: it needs the
  uniform-off-diagonal circulant structure kim's 5-state walk has and
  pgl27's Schreier walk does not.

### Structure

Ground layer (new file `pgg-smc/instances/pgl27/pgl27_mixing.v`, all
Local, two-layer technique):

| Piece | Content |
|-------|---------|
| `pgl27_sym_sigmas` | the 5-tuple `[tuple tr_perm; tr_perm^-1; sc_perm; sc_perm^-1; inv_perm]` and `Wuni : R.-fdist 'I_5` the uniform weight (the word law's letter distribution; `W : R.-fdist 'I_Tg` per `pgg_weighted_words.v:42-54`) |
| `gen5` consistency | nat tables for the five letters (reusing `tr_tbl`/`sc_tbl`/`inv_tbl` and the inverse tables `tr_inv_tbl`/`sc_inv_tbl` at `pgl27_group.v:56-57`) + two new table-vs-perm lemmas `val ((tr_perm^-1)%g x) = nth 0 tr_inv_tbl (val x)` and the `sc` analogue (8-case `val_inj` pattern) |
| `elem_bfs` / `elem_table` | fueled BFS producing the 336 `(perm table, witness word)` pairs, closed under the FIVE symmetrized generator tables |
| `succ_table` | per-entry successor indices under the five generators |
| `walk_vec L` | BINARY-N fixed-point distribution vector, denominator `5^L`, iterated via `succ_table` |
| `mixing_ok` | checker in `N`: table uniq + size 336 + each entry's word re-verifies + successor closure + `2^40 * sum_i \|336 * walk_vec 200 i - 5^200\| <= 336 * 5^200` (absolute difference by comparison-guarded subtraction), all discharged `by vm_compute` |

Bridge layer:

1. Closure list = the group: each entry's word gives `word_perm w \in
   pgg_G pgl27_M` (item-1 machinery, extended to the 5-letter
   alphabet; entries built as SYMBOLIC `word_perm` products, never as
   perms-from-tables); conversely the entry set contains 1 and is
   closed under right multiplication by the generators, so it
   contains `<<gens>>` by the products induction — `gen_prodgP`
   (fingroup.v:2094) gives every element of `<<A>>` as a product of
   elements of A itself (no inverses needed in a finite group;
   inverse-closedness of the 5-list is a shuffle-model choice, not a
   proof requirement), closed by `big_ord_recr` recursion against the
   list closure. The audited `group_set`/336^2-`vm_compute` fallback
   is DELETED: set-level perm computation is not viable in this repo.
   Supporting lemma `<<3 gens>> = <<5 gens>>` (one `eqEsubset` via
   `genS`, `gen_subG`, `groupV`) ties the walk's group to
   `pgg_G pgl27_M`. Byproduct: `pgl27_card : #|pgg_G pgl27_M| = 336`
   returns as a THEOREM — deleted as dead in the audit round, now
   load-bearing for the support argument.
2. Fiber counting: `#|fiber_weighted g|` at length L equals
   `nat_of_bin` of `walk_vec L` at g's index, by induction on L
   splitting words at the LAST letter: `word_eval` is a left-to-right
   `\prod` (pgg_interface.v:163), so `big_ord_recr` gives
   `fiber_L(g) = \bigcup_j rcons(fiber_{L-1}(g * gj^-1), j)`,
   disjoint. The N-to-nat reflection rides the same induction via
   `nat_of_add_bin`/`nat_of_mul_bin`. This is the load-bearing novel
   proof (~200-300 lines with the reflection).
3. Assembly: `rho_weighted_is_uniform` (pgg_weighted_words.v:142)
   collapses the uniform-W law to `rho_from_words`, whose
   `fiber_prob` (pgg_collusion_bound.v:575) gives
   `#|fiber g|%:R / (5^L)%:R`; the two `fdist_uniform` cardinality
   witnesses (`card_word_L` vs `card_word_L'`) are reconciled by
   `eq_irrelevance` (known repo pattern). `var_dist` splits by
   `bigID` on `a \in G` + `big1` off-support (`fdist_uniform_supp_notin`
   and empty fibers off the list, both from list = G) + reindex onto
   the 336-entry list; the N inequality from `mixing_ok` closes the
   bound. Dependency order: `pgl27_card` lands in the same commit
   BEFORE the assembly (it supplies `U g = 1/336`). No enumeration of
   the 40320-element perm type ever reaches `vm_compute`.
4. Corollaries: pushforward monotonicity EXISTS —
   `var_dist_fdistmap` (pgg_collusion_bound.v:73); the endpoint
   corollary chains `endpoint_dist_weighted = fdistmap (eval s)`
   (pgg_weighted_words.v:99), the landed `pgl27_point_uniform`
   (pgl27_profile.v:68, a full fdist equality), and
   `var_dist_fdistmap`. The approximate-privacy stretch goal is
   RESTATED per audit: the primary lemma is the joint-law bound
   `var_dist (secretP `x rho_L) (secretP `x (`U HG)) <= 2^-40`
   (the sum factorizes through secretP), with a derived pointwise
   corollary carrying the honest 2*eps constant (triangle through
   the exact law); included if provable in ~80 lines, else deferred
   with a disclosed non-claim.

### Feasibility verdicts

| Piece | Verdict | Evidence |
|-------|---------|----------|
| BFS + successor tables `vm_compute` | proven pattern | landed checkers; table-level only |
| Binary-N walk + checker `vm_compute` | feasible (audited fix) | 465-bit N arithmetic is native to vm_compute; exact Python run pins L=200 with 2.9x margin |
| N-to-nat reflection bridge | feasible | ssrnat `nat_of_bin` morphisms; rides the fiber induction |
| Word-law fdist + fiber lemma | exists | `pgg_weighted_words.v:60-99` + `fiber_prob` (pgg_collusion_bound.v:575) |
| `var_dist` monotonicity | exists | `var_dist_fdistmap` (pgg_collusion_bound.v:73) |
| Closure-list = G argument | feasible, single route | `gen_prodgP` (fingroup.v:2094) + table-level closure; set-level fallback deleted |
| Fiber-counting induction + reflection | feasible, main risk | bounded (~200-300 lines), `big_ord_recr` rcons partition |
| Approximate-privacy transfer (joint-law form) | uncertain | stretch; deferrable without breaking the headline |

Estimated 600-800 lines, 2 prover sessions. `_CoqProject` gains
`pgl27_mixing.v`.

### Verification

- `Print Assumptions pgl27_word_mixing` — closed under the global
  context or boolp-only (reals enter through `var_dist`; boolp
  acceptable, no custom axioms; input source: live repo).
- `Print Assumptions pgl27_card` — closed under the global context.
- Full chain `make -j1` rebuild; audit gate per commit.
- The closure note (Part 2) gains the mixing row and retires the
  "exact-uniform shuffle" disclosure at the single-card level (and at
  the coalition level only if the stretch lands).

## Commit plan

| Commit | Content |
|--------|---------|
| 1 | Part 1: three cells (trace/secrecy/recovery edits) |
| 2 | Part 2: closure note |
| 3 | Part 3 ground + bridge: `pgl27_mixing.v`, `pgl27_card` theorem, `_CoqProject` |
| 4 | Part 3 corollaries + closure-note update |

## Out of scope (disclosed, per the boundary rule)

Active adversaries, composition, formal reveal-phase model,
quantitative MI values at k = 4..6, all-decks lifts for sibling
instances, the framework eps=0 single-card semantics, and the
framework `ts_T`/`pgl_bound` items (verified this session: pgl27
consumes `pgl_bound` only for the field-quotient order lemma, where
the formula is correct).
