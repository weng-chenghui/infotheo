# pgl27 open questions: closure design (2026-07-12)

Design for closing the four items left open by the pgl27 audit round:
the group 3-transitivity axiom, the all-valid-decks dealer, sub-8
recovery, and the reveal-phase model. Feasibility was probed live in
Rocq before this design was written; probe evidence is quoted inline.

## Feasibility verdicts

| # | Item | Verdict | Core evidence |
|---|------|---------|---------------|
| 1 | Prove `pgl27_3transitive` in-kernel | Feasible, probed | Morphism collapse is a one-liner; BFS word closure + checker closes by `vm_compute` in 910 ms; `atrans` intro shape confirmed (probe states 245, 260, 265) |
| 2 | All-valid-decks dealer privacy | Feasible | Bridge keystone `ktuple_encode_uniform` is already representative-generic: it uses only `uniq (encode b)`, so it applies to every valid deck |
| 3 | Sub-8 recovery impossibility | Feasible after REFRAMING | The claim "no 7-position decoder exists" is FALSE: 7 revealed cards determine the 8th (unique missing card), hence the deck, hence the class. The sharp true pair: 7 reveals determine, 6 never do |
| 4 | Reveal-phase prose discipline | Trivial | Header/doc sweep, no proof content |

Execution order: 1, then 3, then 2, then 4. Item 3 consumes the
3-transitivity statement (theorem after item 1). Item 4 runs last so
prose reflects the new results.

## Item 1 — `pgl27_3transitive` in-kernel

### Approaches considered

- **A (chosen): BFS word-witness closure**, the two-layer technique
  that closed `orbit_class_split`. Ground layer: a fueled in-Rocq BFS
  over nat triples produces a `(triple, generator word)` table; a
  nested-`all` checker certifies by `vm_compute` that every distinct
  triple below 8 appears with a word that maps the base triple
  `[:: 0; 1; 2]` to it. Bridge layer: words map to group elements of
  `<<gens>>` by `foldl` product, a val-level induction lemma connects
  the perm product to nat-table composition, and the `atrans` orbit
  proof assembles the witnesses.
- B: Moebius/Bruhat composition formalisation. Rejected; the
  composition identity is a symbolic eight-parameter field identity
  out of reach of `vm_compute` and available tactics, as already
  documented in the file's justification block.
- C: keep the axiom. Rejected; A is probed feasible, and the axiom is
  the single decidable trust anchor of the whole pgl27 chain.

### Probe evidence (2026-07-12, live rocq-mcp session)

Python sanity: all 336 ordered distinct triples are reachable from
(0,1,2) under the three generator tables; maximum word length 8;
total word entries 1815. The group closure has exactly 336 elements.

Rocq probes, in a session importing `pgl27_group`:

1. `(pgg_rho pgl27_M @* pgg_G pgl27_M)%g = pgg_G pgl27_M` closed by
   `by rewrite morphimEdom imset_id.` (27 ms).
2. A fueled BFS (`pbfs`, fuel 12) over `seq nat` triples with word
   accumulation, plus the completeness-and-correctness checker
   (`all` over the 512-triple cube, distinctness-guarded `has`
   lookup re-verifying `papply w [:: 0;1;2] == t`), closed by
   `by vm_compute.` in 910 ms.
3. `rewrite /ntransitive probe_morphim; apply/imsetP; exists [tuple
   ord0; ord1; ord2]` yields exactly the two expected goals:
   base-tuple membership in `3.-dtuple([set: 'I_8])` and
   `3.-dtuple([set: 'I_8]) = orbit ('P * 3) (pgg_G pgl27_M) t0`.

### Structure (all in `pgl27_group.v`, replacing the axiom block)

Same name, same statement; the three consumers
(`pgl27_scheme.v:62`, `pgl27_secrecy.v:71`, `pgl27_profile.v:73`)
recompile unchanged.

| Piece | Content | Discharge |
|-------|---------|-----------|
| `wgenn i` | nat table of generator i (reuse `tr_tbl`/`sc_tbl`/`inv_tbl` via `nth`) | definition |
| `wstep`, `wapply` | apply one table to a nat triple; `foldl` a word | definition |
| `word_bfs` | fueled BFS from `([:: 0;1;2], [::])`, dedup against seen, fuel 12 | definition |
| `word_table` | `word_bfs` output, 336 entries | definition |
| `word_table_ok` | nested `all` over `iota 0 8` cubed: distinct triples have a table entry whose word re-verifies | `by vm_compute` |
| `gen_of : nat -> {perm 'I_8}` | 0, 1, 2 to `tr_perm`, `sc_perm`, `inv_perm`; default a generator | definition |
| `word_perm w` | `foldl (fun a i => (a * gen_of i)%g) 1%g w` | definition |
| `word_perm_mem` | `word_perm w \in pgg_G pgl27_M` | induction; `group1`, `groupM`, `mem_gen` |
| `word_perm_val` | `val (word_perm w x) = wapply w (val x)` pointwise | `foldl` induction, generalized accumulator, `permM` + per-generator val lemmas (mirror `gen0_val`..`gen2_val` of `pgl27_orbit.v`) |
| `triple_word` | for distinct `a b c < 8`: a word `w` with `wapply w [:: 0;1;2] = [:: a; b; c]` | nested `allP`/`mem_iota` read-off, the `gen_class` pattern |
| `pgl27_3transitive` | the axiom's statement, now a Lemma | `morphimEdom imset_id`; `apply/imsetP`; goal 1 by `inE` + computation; goal 2 by `eqEsubset`: orbit side via `orbitP` + `n_act_dtuple` (the `'N([set: 'I_8] | 'P)` condition is trivial by `astabsP`), dtuple side via `tupleP` destructuring ×3, `dtuple_onP` distinctness, `triple_word`, witness `word_perm w`, tuple equality by `eq_from_tnth` + `tnth_map` + `val_inj` + `word_perm_val` |

The file-header comment and the justification block are replaced by a
terse statement description per the statement-comment rule; the BFS
rationale lives in a non-rendered source comment.

Estimated 300-350 lines. Delegated to `rocq-prover` with the probe
transcript, exact line range, and the standard budget block.

### Verification

- `rocq_assumptions pgl27_3transitive` reports closed under the
  global context with no axioms (pure fingroup content; input source:
  live repo, branch `pgg-smc`).
- `make -j1` recompile of the five downstream pgl27 files in
  dependency order (input source: live repo).
- `grep -rn "^Axiom" pgg-smc/instances/pgl27/` returns nothing; the
  whole pgl27 chain is then boolp-only.

## Item 2 — all-valid-decks dealer privacy

### The gap and the key reuse fact

The landed sampler (`pgl27P` in `pgl27_secrecy.v`) draws a uniform
group element applied to the fixed representative `orbit_encode s`.
A reader imagines a dealer that can deal ANY valid deck of class s.
The bridge keystone `ktuple_encode_uniform`
(`transitivity_privacy.v:402`) already proves, for ANY tuple with
`uniq`, that the shuffled coalition k-tuple pushforward is uniform
over distinct k-tuples; the law does not depend on the deck. So the
per-orbit decomposition sketched in the previous round is
unnecessary: per-deck genericity plus a mixture argument suffices.

### Approaches considered

- **A (chosen): deck-and-shuffle kernel model, generic in the
  bridge.** Sample space `bool * (deck * gT)` with law
  `secretP `X (fun s => D_s `x (`U HG))` where
  `D_s := fdist_uniform_supp` over `[set sh | deck_ok sh &&
  (orbit_class sh == s)]`. Sections at fixed deck push to the same
  law by `ktuple_encode_uniform`; a support-restricted mixture lemma
  and a kernel-product independence lemma finish.
- **B (also included, as the headline corollary): shuffle-free
  uniform-class dealer.** Law `secretP `X (fun s => D_s)`, view read
  directly off the dealt deck. Follows from A because the shuffle is
  absorbed: for fixed g the action is a class-preserving bijection of
  the class-s deck set (`deck_stable`, `orbit_class_invariant`), so
  the dealt-deck marginal of model A equals `D_s`. This is the
  statement a skeptic actually wants: uniform over all valid class-s
  decks, independence with no reliance on any representative.
- C: orbit-representative decomposition and averaging (previous
  round's sketch). Subsumed by A + B with less machinery. Rejected.

### New generic lemmas (`transitivity_privacy.v`)

| Lemma | Statement sketch |
|------------------------|------------------|
| `inde_prod_kernel_fst` | over `P `X W`, a variable whose conditional law given the first coordinate is a constant `mu` (hypothesis restricted to `P a != 0`) is independent of the first coordinate; same algebra as `inde_prod_fst` with `fdist_prodE` giving `P ab.1 * W ab.1 ab.2` |
| `fdistmap_prod_const` | if for every `a` in the support of `P`, `fdistmap (f a) (W a) = mu`, then `fdistmap (uncurry f) (P `X W) = mu`; second-coordinate variant obtained via `fdistX` |
| `fdist_uniform_supp_bij` | a bijection stabilising the support pushes `fdist_uniform_supp` to itself (mirrors `bij_uniform`) |
| `ttrans_view_indep_alldecks` | new section generic over `orbit_class`, `deck_ok`, invariance and stability hypotheses (the `redeal`-section shape): in the deck-and-shuffle model every coalition of at most t positions has view independent of the secret |
| `alldecks_shuffle_absorb` | `fdistmap (act) (D_s `x (`U HG)) = D_s` |
| `ttrans_view_indep_uniform_deck` | shuffle-free model independence, transferred along `alldecks_shuffle_absorb` |

Note: `P1 `x P2` vs the kernel notation ``P `X W`` in fdist.v must be
reconciled at plan time; if `` `x `` is the constant-kernel special
case, the new lemmas state everything over `` `X ``.

### Instance layer (`pgl27_secrecy.v`)

`pgl27_class_decks_pos` (positivity of each class-s deck set, from
`orbit_populated`), `pgl27P_alldecks`, `pgl27_view_alldecks`,
`pgl27_view_indep_alldecks`, `pgl27_view_indep_uniform_deck`.
The secret prior stays an abstract `secretP` in the bridge; the
instance uses the uniform prior as today. Estimated 300-350 lines
total across the two files.

Out of scope here: lifting the executed-trace secrecy results of
`pgl27_trace.v` to the all-decks dealer. That is a follow-on once the
view-level statement lands; the audit critique targeted the sampler
of the view-independence results.

### Verification

- `rocq_assumptions pgl27_view_indep_alldecks` and
  `..._uniform_deck`: boolp only (input source: live repo).
- The deck-kernel support is by definition
  `[set sh | deck_ok sh && (orbit_class sh == s)]`, i.e. ALL valid
  class-s decks; checked by reading the statement, no proof needed.

## Item 3 — recovery threshold sharpness (reframed)

### The finding that forces reframing

A valid deck is a uniq 8-tuple over `'I_8`, i.e. a permutation of the
full card set. Seven revealed position-card pairs determine the
eighth card as the unique missing one, hence determine the deck and
the class. So "no sub-8 decoder exists" is false at 7, and prose
implying reveal-all is information-theoretically necessary must be
corrected. The true sharp pair:

- 7 reveals determine the class (positive, new);
- 6 reveals never do, for EVERY choice of the two hidden positions
  (negative, new).

The privacy threshold 3 and the sharp leak at 4 are untouched; the
ramp story becomes: private up to 3, leaky from 4, determined at 7.
The 2026-07-11 spec already flagged the missing "revealing N-1 cards
determines the secret" refinement (line 69); this closes it.

### Approaches for the 6-reveal insufficiency

- **A (chosen): group transfer from the base witness.**
  `orbit_encode false` and `orbit_encode true` agree everywhere
  except positions 3 and 4 (read off the definitions) and have
  opposite classes (`orbit_encodeK`). For arbitrary hidden positions
  p, q: 2-transitivity (`ntransitive_weak` applied to
  `pgl27_3transitive`) yields g with the coordinate action carrying
  the witness pair to decks agreeing off {p, q}; `deck_stable` and
  `orbit_class_invariant` preserve validity and classes.
- B: direct `vm_compute` search over all 28 position pairs with a
  deck-builder. Rejected: more lines, and redundant once item 1 makes
  A axiom-free.

### Deliverables (new file `pgg-smc/instances/pgl27/pgl27_recovery.v`)

| Lemma | Statement |
|-------|-----------|
| `pgl27_seven_reveal_determines` | two valid decks agreeing off one position are equal (missing-card completion) |
| `pgl27_seven_reveal_class` | corollary: their orbit classes agree, so a 7-position decoder exists |
| `pgl27_2transitive` | `ntransitive 2` corollary via `ntransitive_weak` |
| `pgl27_six_reveal_ambiguous` | for every p != q there are two valid decks agreeing off {p, q} with distinct orbit classes |

Estimated 150-200 lines. Prose corrections: `pgl27_scheme.v` header
("reconstruction reads all eight endpoints" stays as a description of
the implemented decoder, with the sharp-threshold sentence added),
the 2026-07-11 spec post-note, and the pgl27 memory entries.

### Verification

- `rocq_assumptions` on all four: no axioms beyond what
  `pgl27_3transitive` carries (none after item 1; input source: live
  repo).
- The base witness agreement off {3, 4} is itself a lemma discharged
  by computation, not prose.

## Item 4 — reveal-phase prose discipline

No formal content. One qualifier sentence, placed in file headers and
docs only (statement comments stay terse per the statement-comment
rule): the secrecy theorems concern the pre-reveal execution; after
the public reveal every player learns the secret by design.

Sweep list:

| Target | Edit |
|--------|------|
| `pgl27_secrecy.v` header | add the mid-execution qualifier |
| `pgl27_trace.v` header | add the qualifier next to the trace-secrecy summary |
| `pgl27_scheme.v` header | qualifier + item-3 sharp-threshold correction |
| `docs/superpowers/specs/2026-07-11-pgl27-orbit-class-design.md` post-note | qualifier + item-3 correction + axiom-status update after item 1 |
| `docs/superpowers/plans/2026-07-11-pgl27-orbit-class.md` post-note | same status updates |
| memory: `project_pgl27_instance_landed.md`, `project_pgl27_audit_findings.md` | axiom now theorem; sharp recovery pair; all-decks dealer closed |

## Commit plan

| Commit | Content | Gate notes |
|--------|---------|------------|
| 1 | `pgl27_group.v`: axiom replaced by theorem + machinery; downstream rebuild | H/I tags on new declarations; `@composes: pgl27_3transitive` chains |
| 2 | `pgl27_recovery.v` new file + `_CoqProject` entry + scheme-header correction | new-file audit |
| 3 | bridge extension + `pgl27_secrecy.v` all-decks statements | H/I tags; `@main security` on the two headline lemmas |
| 4 | prose sweep, spec/plan post-notes, memory updates | docs-only |

Each Rocq commit is delegated to `rocq-prover` with pre-built `.vo`
status, exact line ranges, section contexts, a turn budget, and the
4-phase rocq-mcp workflow reminder, per the project instructions.

## Out of scope

- Trace-level all-decks secrecy (`pgl27_trace.v`), noted above.
- Resurrecting `pgl27_card` (|G| = 336 in-kernel). The BFS closure
  machinery makes it reachable (group closure has exactly 336
  elements, verified in the Python sanity run), but the audit deleted
  it as dead code and nothing consumes it. Recorded here as possible
  future work only.
- Any change to the other four instances.

## Risks

| Risk | Mitigation |
|------|------------|
| `foldl` accumulator induction fiddliness in `word_perm_val` | standard generalized-accumulator induction; probe transcript pins the definitions |
| 3-tuple destructuring / `n_act` coordinate juggling | `tupleP` ×3 + `tnth_map`; intro shape already probed (state 265) |
| infotheo API drift around `fdist_uniform_supp` pushforwards | write `fdist_uniform_supp_bij` by hand mirroring `bij_uniform` |
| `` `x `` vs `` `X `` notation reconciliation | resolved at plan time by reading `fdist.v`; worst case the new lemmas restate the constant case |
| audit Stage-2 token budget across 4 commits | commits are small and focused; bypass only per the documented policy if a cap fires |
