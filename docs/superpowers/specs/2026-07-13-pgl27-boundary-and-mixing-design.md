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
| Shuffle-free trace secrecy | `pgl27_deck_trace_secrecy` (+ coalition form): over `uniform_deckP`, the executed trace at the identity cut is the dealt card; `H(secret \| trace) = H(secret)` | run at cut `1%g`; trace = `tnth u.2 i` via `pgl27_abs_p<k>` at `w0 := 1`; keystone with `pgl27_view_indep_deck` |
| Class-proportional prior | `pgl27_view_indep_deck_prior`: the generic `ttrans_view_indep_deck` instantiated at an arbitrary `secretP : R.-fdist bool` (covers the 42/70-28/70 uniform-over-all-valid-decks reading) | direct application; the bridge is already generic in `secretP` |
| Sub-6 ambiguity | `pgl27_reveal_ambiguous`: for every position set D with `#\|D\| <= 6` there are two valid decks of opposite classes agreeing on D | from `pgl27_six_reveal_ambiguous` at any pair {p, q} disjoint from D (exists since `#\|~:D\| >= 2`); the witness pair agrees off {p,q} hence on D |

Placement: cells 1-2 in `pgl27_trace.v` / `pgl27_secrecy.v`
respectively; cell 3 in `pgl27_recovery.v`. Naming pre-checked: all
at most 4 components.

## Part 2 — the closure note

New file `pgg-smc/notes/20260713-pgl27-claim-boundary.md` (the
instance-notes convention): the full claim matrix with one row per
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

Python, exact walk on the verified 336-element closure: the group
walk reaches full-L1 `var_dist < 2^-40` at L* = 193; per-start
endpoint walks at L* = 185..192. L = 200 gives margin. In-kernel
cost: nat fixed-point vectors with denominator `5^200` (~465 bits),
200 steps x 336 states x 5 successors ~ 336k big-nat additions —
same order as the landed `orbit_class_split` and 3-transitivity
checkers.

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
| `pgl27_sym_sigmas` | the 5-tuple `[tuple tr_perm; tr_perm^-1; sc_perm; sc_perm^-1; inv_perm]` and `Wuni` the uniform weight on `'I_5` (the shuffle's word law) |
| `elem_bfs` / `elem_table` | fueled BFS producing the 336 `(perm table, witness word)` pairs, closed under the FIVE symmetrized generator tables (reuses `tr_tbl`/`sc_tbl`/`inv_tbl` + the inverse tables `tr_inv_tbl`/`sc_inv_tbl` already in `pgl27_group.v:57-58`) |
| `succ_table` | per-entry successor indices under the five generators |
| `walk_vec L` | nat fixed-point distribution vector, denominator `5^L`, iterated via `succ_table` |
| `mixing_ok` | checker: table uniq + size 336 + each entry's word re-verifies + successor closure + `2^40 * sum_i abs(336 * walk_vec 200 i - 5^200) <= 336 * 5^200`, all discharged `by vm_compute` |

Bridge layer:

1. Closure list = the group: each entry's word gives `word_perm w \in
   pgg_G pgl27_M` (item-1 machinery, extended to the 5-letter
   alphabet); conversely the entry set contains 1 and is closed under
   right multiplication by the (inverse-closed) generators, so it
   contains `<<gens>>` by the products induction (`gen_prodgP`-style;
   fallback: the `group_set` route with a 336^2-composition
   `vm_compute`). Byproduct: `pgl27_card : #|pgg_G pgl27_M| = 336`
   returns as a THEOREM — deleted as dead in the audit round, now
   load-bearing for the support argument.
2. Fiber counting: `#|fiber_weighted g|` at length L equals
   `walk_vec L` at g's index, by induction on L splitting words at
   the last letter (`fiber_L(g) = \bigcup_j fiber_{L-1}(g * gj^-1)`,
   disjoint, via tuple `rcons` partition). This is the load-bearing
   novel proof (~100-150 lines).
3. Assembly: `fiber_prob_weighted` turns the counts into
   `rho_from_words_weighted` probabilities; `var_dist` splits over
   the closure list (all of G) versus the rest of `{perm 'I_8}`
   (probability 0 on both sides once support is pinned); the nat
   inequality from `mixing_ok` closes the bound.
4. Corollaries: `var_dist` monotonicity under `fdistmap` (add the
   small generic lemma to `pgg_mixing.v` or reuse if present —
   Search first) gives the endpoint bound; the approximate-privacy
   transfer is a stretch goal, included only if the independence
   perturbation lemma is provable in ~50 lines (Search
   `variation_dist`/`proba` first; otherwise deferred with a
   disclosed non-claim, per the boundary rule).

### Feasibility verdicts

| Piece | Verdict | Evidence |
|-------|---------|----------|
| BFS + walk + checker `vm_compute` | proven pattern | probes for items already landed; Python L* run above |
| Word-law fdist + fiber lemma | exists | `pgg_weighted_words.v:60-99` |
| Closure-list = G argument | feasible | inverse-closed gens; two candidate routes named |
| Fiber-counting induction | feasible, main risk | bounded (~150 lines), rcons partition |
| Approximate-privacy transfer | uncertain | stretch; deferrable without breaking the headline |

Estimated 450-600 lines, 1-2 prover sessions. `_CoqProject` gains
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
