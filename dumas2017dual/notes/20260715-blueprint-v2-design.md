# Blueprint v2: design, audit, and the epsilon_cpa fix

Date: 2026-07-15
Status: code fix DONE (commits 0c59b058, 664e2e49). Blueprint design REVISED
after adversarial audit; D2/D3 refuted and pending re-decision.
Branch: `epsilon-cpa-per-scheme`

## 1. What happened

The task began as "rewrite the blueprint to tell the SMC-DSDP security story".
Three adversarial audits of the first design found a code-level defect that made
the blueprint unwritable as designed: six of the nine corrupted-Alice headlines
were vacuous. The code fix landed first. The blueprint follows.

## 2. The epsilon_cpa defect (FIXED)

`Parameter epsilon_cpa : reals.Real.sort R` was a single constant, while
`enc_ind_cpa_real_or_zero` quantifies `forall (AHE : AHEncType) ... <=
epsilon_cpa`. One constant therefore had to bound every scheme's IND-CPA
advantage at once.

The repository contains a scheme that returns the plaintext
(`idealized_enc pk m r := m`, `idealized_ahe.v:61`), packed as a legal
`AHEncType` (`dsdp_correctness.v:79`). A one-query adversary attains advantage 1
against it, so the axiom forced `1 <= epsilon_cpa`.

Since SSProve's subdistribution structure supplies `AdvantageE _ _ _ <= 1` for
free (the `psum mu <= 1` field of `Structure distr`), every downstream
`_ <= 2 * epsilon_cpa` bound was `>= 2` and therefore implied by a record field.
The derived game-hopping chain concluded less than its own types already gave.

The development was **sound** throughout — the axiom is consistent (`eps = 1`
satisfies it), every proof valid. The bounds were **vacuous**, not wrong.

**Fix** (0c59b058): `epsilon_cpa : AHEncType -> reals.Real.sort R`, threaded
through 63 sites in 6 built files. Mechanical: no lemma needs epsilon uniform
across two schemes. `dsdp_game_derivation.v` has no sections, so its bound is
indexed by the record field: `epsilon_cpa (exp_enc_scheme P)`.

**Guard** (664e2e49): `epsilon_cpa_idealized_ge1 : 1 <= epsilon_cpa
idealized_ahe_f2` in `homomorphic_encryption/idealized/idealized_indcpa.v`.
Re-collapsing `epsilon_cpa` to a constant makes this contradict any bound
under 1, so the build catches the regression.

### Rejected alternative

Axiomatising "the three leakage sites together give at most 1" would either
restate the free `psum mu <= 1` (no effect on the vacuity) or, in the strong
form `2*eps + 1/m <= 1`, **contradict** the existing axiom via the identity
scheme (`1 <= eps` and `eps <= 0.5`), making the axiom set inconsistent. A
too-weak assumption cannot be repaired by axiomatising a strong conclusion. The
legitimate form is a `Hypothesis` over a section `Variable AHE`, discharged at
instantiation — which the indexing is what makes expressible.

## 3. Measured axiom map (`Print Assumptions`, all 15 headlines)

The gate a `grep` cannot be. Run via the LOCAL switch
(`/Users/cheng-huiweng/Projects/coq/_opam/bin/coqc`, OCaml 5.2.1 — the
`~/.opam/infotheo` switch is 4.14.2 and cannot read the project's `.vo`).

| headline | IND-CPA | admitted `interchange_psum` |
|---|---|---|
| `dsdp_centropy_uniform` | - | - |
| `dsdp_centropy_uniform_n` | - | - |
| `US_n_compromised_leaks_secret` | - | - |
| `US_compromised_leaks_V2` | - | - |
| `bob_privacy_V1` | - | - |
| `charlie_privacy_V1` | - | - |
| `bob_privacy_V3` | - | - |
| `charlie_privacy_V2` | - | - |
| `dsdp_alice_view_advantage_le` | YES | YES |
| `dsdp_alice_guess_ideal_le` | **-** | **YES** |
| `dsdp_alice_guess_advantage_le` | YES | YES |
| `dsdp_alice_guess_real_le` | YES | YES |
| `dsdp_alice_unpredictability_ge` | YES | YES |
| `dsdp_alice_simulation_secure` | YES | YES |
| `dsdp_alice_view_statdist_le` | YES | YES |

The eight counting-axis headlines carry only classical axioms (boolp
extensionality trio + indefinite description).

`realsum.__admitted__interchange_psum` (`Proof using Type. Admitted.` upstream,
with the note "lacks proof") reaches **7** headlines, including
`dsdp_alice_guess_ideal_le` — the one leg free of IND-CPA. So the 1/m fiber
bound is unconditional on cryptography while resting on an unproved upstream
Tonelli lemma. The blueprint must not paint it green as a proved library fact.

## 4. Blueprint decisions after audit

**D1 — threat-model spine. SURVIVES.** Parts group by who is corrupted;
chapter = one headline theorem chained to leaves.

**D4 — simulation scope stated, worst-case as a blue node. SURVIVES.** Both
simulation headlines are average-case (`v2`, `v3` sampled uniformly in-game).
The simulator is genuine: `sim_view_body` takes `run_ideal : raw_code 'unit`,
so nothing flows back from the ideal; the view is fabricated from `enc pk 0`.
That is a type-level witness.

**D2 — library leaves + generated hypothesis blocks. REFUTED as written.**
- "In-tree" is undefined: `-R . infotheo` makes the whole repo one namespace, so
  "an Infotheo library fact" and "an in-tree declaration" are the same thing.
  Node count swings 400 / 506 / 616-of-1891 / 1891 depending on where the cut
  falls. The checker cannot be specified until this is written down.
- Generated hypothesis blocks recover **46 of 96** hypotheses. For
  `dsdp_alice_guess_real_le` the generated block reports **none** — missing
  `Hinj`, `guess_lossless`, `card_renc_neq`, all four seed pins. D2's purpose
  was making over-hypothesisation visible; it would have printed a clean bill
  for the most hypothesised theorem. Fix: `About <thm>` off the `.vo` gives
  100% by construction. The glob is the wrong tool for this job.

**D3 — chain-walker, no exclusion list. REFUTED as written.**
- `.glob` does not record all dependencies. Ground truth: a lemma proved by
  `autorewrite` has the dependency in its proof term and **zero** glob refs;
  one proved by `auto` looked correct only because a following `Hint Rewrite`
  command was swallowed by span attribution. Canonical structure inference leaks
  identically. Live in-tree at `dsdp_simulator.v:187,192` and
  `dsdp_guess_fiber.v:1352` (`ssprove_valid`, `Hint Extern`).
- "Nothing to waive" is false: `dsdp_game_code:push_val` — the design's own
  example of a legitimate permanent waiver — **is on a headline chain**, with 83
  plumbing nodes beside it (`GC_enc_hop`, `HE_add`, `Gplain`, …).
- `dsdp_faithful` (`dsdp_game_derivation.v:502`) is on **no** chain. It is the
  lemma proving the derived game models DSDP. Scope-as-closure-of-`dsdp_main`
  puts the protocol-faithfulness link outside the claim — invisible rather than
  listed, worse than the 306-waiver list it replaces.

What survives of D3: no phantom `exact` (the regex checker mints one from
ssreflect tactic brackets at `dsdp_main.v:882,926`); probe files auto-excluded
(verified: none in closure); DIGEST-based staleness detection (DIGEST is the md5
of the `.v`, all 40 closure modules current). Real, but narrower than "the
instrument checks what it claims".

## 5. Corrections the blueprint must carry

- **Part III is not "Malicious Alice".** `US_compromised_leaks_V2` needs
  `U2 = 1`, `U3 = 0` — legal *input choices* for a semi-honest party, no
  protocol deviation. And `Hinj : injective (fun v => w_u3 * v)` on
  `dsdp_alice_guess_ideal_le` / `_real_le` / `_unpredictability_ge` excludes
  exactly `u3 = 0`, where the 1/m bound is **false**, not merely unproven. Parts
  I and III are separated by `u3` invertibility, not by threat model. Re-place
  Part III as Part I's tightness witness, immediately after the 1/m chapter.
- **`dsdp_centropy_uniform` does not condition on Alice's view.** `CondRV :=
  [% V1, U1, U2, U3, S]` is inputs + output. Alice's view (`dsdp_main.v:386`)
  additionally carries `Dk_a`, `R2`, `R3`, and three ciphertexts. The source
  comment at `dsdp_main.v:180` already misstates this and should be fixed.
- **Correctness is absent.** `dsdp_is_correct`, `dsdp_result_correct`,
  `dsdp_algebraic_correctness` are proved and in no chapter. Security without
  correctness is satisfied by a protocol returning a constant.
- **`card_renc_neq` is an interpreter artifact**, not a security condition:
  `denote_run` dispatches sample sorts by cardinality. It excludes schemes whose
  randomness and message spaces have equal size. Belongs in the machinery
  chapter, tagged as such.
- **`u3 ∈ (0, min(p,q))`** in `dsdp_centropy_uniform` is a magnitude restriction
  (CRT decomposition), far stronger than "u3 invertible". For p ≈ q ≈ √m it
  admits ≈ √m of m weights.
- **`predictor_locs_disj` is security-critical**, not hygiene: it keeps
  `V_2_cell` out of the predictor's readable footprint.
- **`dsdp_centropy_uniform_n` has five undischarged hypotheses** and no N-party
  instance. `VarRV` has n+1 components while the entropy is `log(m^n)`.

## 6. Sequencing (from the structure audit; adopted)

1. **Spec A — measure and decide.** Walker as a read-only reporting tool.
   Settle the in-tree/library boundary, the plumbing rule, the root set
   (must include `dsdp_faithful` and the correctness theorems). Deliverable:
   real node counts per chapter. Everything downstream is unsizable until this
   lands.
2. **Spec B — tooling cutover** on the *existing* v1 document, so the ratchet is
   never off. Generate `\uses` edges and hypothesis blocks (via `About`). Derive
   `MODULES` from the walk. Infra bootstrap: `.venv` is gitignored, so `git mv`
   strands the build. New macro layer — `macros/common.tex` defines 20 macros,
   all pipeline notation, and **none** for entropy / statdist / unpredictability,
   which carry 8 of 14 headline chapters.
3. **Spec C — `git mv`, Part 0.** Protocol, views, threat models, correctness.
   Re-frame the 1,172 lines of v1 (12 chapters into 2 is a rewrite, not a copy).
4. **Spec D — Parts I-III.** Sequenced by measured chain size; smallest first to
   validate the template.

Do not `git mv` until Spec B passes on the old document. That ordering keeps the
ratchet on for the whole migration — the property §1 says was lost last time.
