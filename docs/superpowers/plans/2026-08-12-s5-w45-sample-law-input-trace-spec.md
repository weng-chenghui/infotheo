# Spec: sample-distribution identities and the input-party trace bound (S5-1, S5-2, W4, W5)

Date: 2026-08-12, amended same day after the probe fold-backs and both
adversarial audits (fold-back log at the end). User go: 2026-08-12 ("make plan
then complete these two" naming the two S5 non-goals and the two S4 auditor
candidates W4/W5).

Upstream chain: evaluation response `cf64d7ae` section 11 (S5 row) and the
as-built record of `2026-08-11-execution-plug-implementation-plan.md`
(deviation 3, W4/W5). This cycle turns the four recorded future candidates
into landed theorems. Everything extends the four files landed in the
previous cycle; no landed statement is modified.

Compiled evidence: `docs/superpowers/probes/2026-08-12-s5-w45/probe_a_laws.v`
(all claims Qed, boolp trio only, independently re-verified by the soundness
audit via `Print Assumptions` on the built `.vo`), `probe_b_mutation.v`
(Fail-wrapped mutations), and the soundness audit's own compiled
`denboer_witness_is_rotation` (the C9 source).

## Scope (the four items, as amended)

| Item | Content |
|---|---|
| W4 | Word-space coalition `distE` twin at `pgl27_word_sample` |
| W5 | Cut-distribution results, three of them: the pgl27 exact sample's cut distribution IS the witness distribution (a tie, C2); the five-card sample's cut distribution is the uniform-rotation image distribution at every bias (an identification, C3); and the five-card cut distribution equals the den Boer member's witness distribution (a tie, C9 — the audit's positive refutation of the spec's original "no tie" invariant) |
| S5-1 | The `fdistmap` joint identity connecting `pgl27_word_sample` to the landed `pgl27P_word_gen`, via a generic product-map lemma infotheo lacks, landed as the generic `sa_joint_dist` layer plus one instance identity |
| S5-2 | The bound on the input-party trace observable at five-card: the committing parties' own trace rows are empty, so the observable read from them is constant and conditioning on it leaves the secret's entropy unchanged; the committed PAYLOADS travel to the dealer's row only, and that row determines both committed bits. The verifier's row is a second, already-landed determination locus (`den_boer_endpoints`, `leak_k5`); C8 claims payload locus, not exclusive information locus |

## Pinned carriers

- pgl27 side: `Section pgl27_execution` context of `pgl27_exec.v`
  (`R : realType`, `mpP := pgl27_profile R`), word block after the section
  variable `secretP : R.-fdist bool`.
- five-card side: `Section five_card_execution` context of `five_card_exec.v`
  (`R`, bias `eps` with its three side conditions, word length `L`,
  `mpF := five_card_profile ...`), `dbP := P R` with
  `Omega = (bool * bool * 'I_5)%type`, `P R = fdist_uniform card_Omega20`;
  C9 lands standalone after `End five_card_execution` in the
  `five_card_exec_procs_biasE` style.
- generic side: `Section` context of `pgg_sample_adapter.v` (generic imports
  only) for the product-map lemma and the `sa_joint_dist` definition; plain
  finTypes `A B C`, `P : R.-fdist A`, `Q : R.-fdist B`, `g : B -> C`.

## Claim ledger (production names final, per the naming audit)

Every row is GO: probed to `Qed` at the pinned carrier in `probe_a_laws.v`
(probe name in parentheses), zero `Admitted`/`Abort`/`Axiom`, boolp trio
only. C9a was compiled by the soundness audit; C9b is a two-rewrite corollary
of C3 + C9a (the one derivation not probed verbatim; fallback recorded in the
plan).

| # | Production name | Statement | Tag |
|---|---|---|---|
| C1 | `pgl27_word_sample_coalition_distE` (`probe_C1`) | `pgl27_word_sample_coalition_dist C = fdistmap (sa_static_coalition_view pgl27_word_sample pgl27_content_obs C) pgl27_word_sampleP` | `@main architecture:` |
| C2 | `pgl27_sample_cut_distE` (`probe_C2`) | `sa_cut_dist pgl27_sample = pgl27_witness_cut_dist` | `@main architecture:` |
| C3 | `five_card_sample_cut_distE` (`probe_C3`) | `five_card_sample_cut_dist = fdistmap (fun k : 'I_5 => (fc_sigma ^+ k)%g) (fdist_uniform (card_ord 5))`; helpers `five_card_card_bool2` (`probe_card_bool2`, local duplicate of `kim_input_privacy.card_bool2` — deliberate, no new import edge), `five_card_sample_uniform_prodE` (`probe_omega_prodE`), `five_card_sample_snd_uniformE` (`probe_omega_snd_uniform`) | `@main architecture:`; helpers `@composes` up the chain |
| C4 | `fdistmap_prodr` (`probe_fdistmap_prodr`) | `fdistmap (fun ab : A * B => (ab.1, g ab.2)) (P `x Q) = P `x fdistmap g Q` — in `pgg_sample_adapter.v`; `r` = the right factor is acted on (mathcomp `allpairs0l/r`, `cfDprodl/r` precedent) | `@main architecture:` |
| C5 | `pgl27_word_sample_joint_distE` (`probe_C5_sa` restated through the new definition) | `sa_joint_dist (pgl27_word_sample secretP) = pgl27P_word_gen secretP`, where the generic `Definition sa_joint_dist := fdistmap (fun u => (sa_arg u, sa_cut u)) sa_sampleP` completes the layer-3 family in `pgg_sample_adapter.v`. ONE export (the probe's two definitionally-equal forms do not both land) | `sa_joint_dist` `@intent:`; identity `@main architecture:` |
| C6 | `five_card_exec_input_raw_traceE` (`probe_C6`), helper `five_card_exec_traces_size` (`probe_run_traces_size`) | `five_card_exec_input_raw_trace (a, b) w0 j = [::]` for ALL `j : nat` — two reasons, split in the comment: committing parties are pure senders (a `Send` logs nothing to its own row, `smc_interpreter.v` step), and rows past the nine-process run are `[::]` by `nth_default` | `@composes: five_card_exec_input_trace_secrecy`; helper `@composes: five_card_exec_input_raw_traceE` |
| C7 | RV `five_card_exec_input_trace` (`probe_input_view`), export `five_card_exec_input_trace_secrecy` (`probe_C7`) | `` `H( Secret R | five_card_exec_input_trace j ) = `H `p_ (Secret R) `` for all `j : nat`, via `unit_RV`/`inde_unit_RV` + `inde_RV_comp` + `inde_cond_entropy` (no new helper needed — probe fold-back 3) | RV `@intent:`; export `@main architecture:` — NOT `security` (audit F3): the identity is constant-conditioning, and its honest-scope caveats are MANDATORY inside the rendered comment (see invariant 2) |
| C8 | Generic extractor `exec_dealer_trace` (unprobed 3-line mirror of `exec_input_trace`; probe used the equivalent local `probe_exec_dealer_trace`); instance `five_card_exec_dealer_raw_trace` + readout equation `five_card_exec_dealer_raw_traceE` (`probe_C8a`); readout function `five_card_exec_dealer_readout` (`probe_dealer_readout`); RV `five_card_exec_dealer_trace` (`probe_dealer_view`); function identity `five_card_exec_dealer_traceE` (`probe_C8b_fun`); exports `five_card_exec_dealer_pair_centropy0` (`H` of the committed-pair RV `fun w => w.1` given the dealer RV `= 0`, immediate from the function identity + `centropy_RV_comp0`) and `five_card_exec_dealer_trace_centropy0` (`probe_C8b`, `` `H( Secret R | dealer RV ) = 0 ``) | extractor/definitions `@intent:`; equations `@composes` up the chain; the two `centropy0` exports `@main security:` |
| C9 | `den_boer_witness_rotationE` (audit-compiled `denboer_witness_is_rotation`) and corollary `den_boer_sample_cut_witnessE` | (a) `sw_rho_dist (mp_security (den_boer_profile R)) = fdistmap (fun k : 'I_5 => (fc_sigma ^+ k)%g) (fdist_uniform (card_ord 5))`; (b) for every bias pack and word length, `five_card_sample_cut_dist Hlt Hgt Hspec L = sw_rho_dist (mp_security (den_boer_profile R))` — the five-card sample's cut distribution is bias-independent and equals the den Boer member's witness distribution. Proof of (b): rewrite C3 then C9a | (a) `@composes: den_boer_sample_cut_witnessE`; (b) `@main architecture:` |

C8a's row value (probe fold-back 1): the dealer's row is anti-chronological —
head `PGG_idx 0` is the dealer's own `Init` of the deck index (chronologically
last), then party 8's sheet `PGG_sheet (encode_bool b)`, then party 7's
`PGG_sheet (encode_bool a)`. The readout keeps the probe's bespoke
three-entry pattern match (not `sheets_of` + `rev` + `den_boer_decode`,
which would decode to `(b, a)` — audit F7); its `(false, false)` default on
malformed rows coincides with a legitimate committed pair and the comment
must say the readout is meaningful only through
`five_card_exec_dealer_raw_traceE`.

## Construction choices (decided)

1. **C4 and `sa_joint_dist` live in `pgg-smc/security/pgg_sample_adapter.v`**:
   `fdistmap_prodr` in a small section before the record, `sa_joint_dist`
   beside `sa_cut_dist`, completing the layer-3 family. The constant-
   conditioning helper originally floated here is DROPPED (probe fold-back 3):
   `spp_proba.inde_unit_RV` + `pgg_trace_secrecy.inde_RV_comp` +
   `extra_entropy.inde_cond_entropy` already compose, resolved through
   transitive Requires and confirmed by batch compile.
2. **`exec_dealer_trace` is added to `pgg_execution_plug.v`** (mirror of
   `exec_input_trace` at `exec_dealer_id`). This is the ONE unprobed
   construction step (audit F12): the probe proved the same term as a local
   definition, so the risk is parameterization only. Fallback: if it resists,
   the instance file keeps the local form and the generic extractor is
   dropped without touching the rest.
3. **Observables are finType RVs** (`'I_5`, `bool * bool`), never raw
   `seq data` traces (raw traces have no distribution layer — previous
   cycle's soundness finding 3).
4. **Placement**: C4/C5-generic in `pgg_sample_adapter.v`; C1, C2, C5 in
   `pgl27_exec.v`; C3, C6, C7, C8-instance in `five_card_exec.v` inside
   `Section five_card_execution`; C9a/C9b standalone after
   `End five_card_execution` (C9 does not depend on the section's bias
   variables). `exec_dealer_trace` in `pgg_execution_plug.v`.
5. **No landed statement changes.** All additions are additive; the four
   files of the previous cycle keep every existing identifier and statement.
   Editing `pgg_execution_plug.v` and `pgg_sample_adapter.v` invalidates the
   downstream `.vo` cone; the plan rebuilds it with `make -j1` once, before
   the instance stages.
6. **C4 stays single-component** (map on the right factor only). The
   both-components form (audit F13) is rejected: no current or foreseeable
   consumer, and unconsumed API generality was the previous cycle's W3
   lesson.
7. **`five_card_card_bool2` stays local** (naming audit item 9 option b): the
   identical `card_bool2` exists at `kim_input_privacy.v:51`, but importing
   `kim_input_privacy` adds an unprobed import edge (`lra` into the
   dependency cone) for one argument-free certificate; the prefixed local
   name plus a `Naming:` line documenting the collision is cheaper and
   probe-faithful.
8. **`Naming:` lines** are required on nine names (all-lowercase with four or
   more underscore components): `five_card_exec_traces_size`,
   `five_card_exec_input_trace`, `five_card_exec_input_trace_secrecy`,
   `five_card_exec_dealer_raw_trace`, `five_card_exec_dealer_readout`,
   `five_card_exec_dealer_trace`, `five_card_exec_dealer_pair_centropy0`,
   `five_card_exec_dealer_trace_centropy0`, and (as documentation)
   `five_card_card_bool2`. Templates: `five_card_exec.v:166-167` (`_size`),
   `:350-351` (`_raw_trace`), `:420-422` (two-word prefix), `:528-530`
   (`_trace_secrecy`).

## Soundness invariants (as amended)

1. No new axiom or assumed constant; every new result depends on exactly the
   boolp trio (`propositional_extensionality`,
   `functional_extensionality_dep`, `constructive_indefinite_description`).
   Verified on the probe by the soundness audit.
2. Honest scope of C6/C7 — the caveats go INSIDE the rendered `(** … *)`
   comments of both results, not in a source-only comment (audit F3):
   (i) the rows are empty because in THIS interpreter model a `Send` logs
   nothing to the sender's own trace; (ii) the identity is therefore a
   constant-conditioning statement, tagged `@main architecture`, not a
   commitment-privacy result; (iii) a committing party knows its own bit, so
   even a non-empty row would not make C7 a privacy statement about that
   party; (iv) the committed payloads travel to the dealer's row, which C8
   shows determines both bits. C6/C7 land only together with C8.
3. (Rewritten after audit F1's machine refutation.) The five-card witness
   distribution `sw_rho_dist (mp_security mpF)` COINCIDES with the rotation
   image distribution of C3 exactly at the den Boer member (`eps = 0`, any
   `L >= 1`): the Kim alphabet is the five rotations, unbiased weights are
   uniform, and uniform on Z/5 is convolution-stable. C9 lands this
   positively. At `eps <> 0` the two differ; no tie is claimed at general
   bias, and none is needed by any consumer.
4. The five-card sample layer (`five_card_sample_*`, C3, C6, C7, C8) is
   bias-independent: `five_card_sample_cut` is the uniform rotation at every
   `eps`, so these results state the unbiased dealing regime read through a
   plug that may carry any bias (audit F4). C9b records this as a theorem
   rather than a caveat.
5. No new privacy claim beyond the stated conditional-entropy identities:
   C7 is constant-conditioning (architecture), C8 is total determination
   through the dealer row (security, the leakage direction: the VIEW
   determines the secret — `centropy_RV_comp0`, never the converse).
   "Determines both committed bits" is carried by
   `five_card_exec_dealer_pair_centropy0`; the `Secret` form alone would
   only claim the conjunction (audit F8). Mixing bounds, coalition privacy,
   and view distributions are untouched.
6. Quantifier scope: C6 and C7 hold for all `j : nat`, by two different
   arguments split in the comments (audit F10); C1-C5, C9 are universally
   quantified over their stated arguments with no hidden side conditions.
7. Vocabulary: rendered statement comments and spec prose say
   "distribution", never "law" (audit F11); `_dist`/`_distE` identifiers are
   exempt; "word law" compounds become "word shuffle".
8. Cited library objects, each USED at the pinned carrier in the probe:
   `sa_coalition_distE`, `sa_cut_dist` (`pgg_sample_adapter.v`);
   `fdistmap_comp`, `fdistX_prod`, `fdistX2`, `fdist_prod1`, `fdistmapE`,
   `fdist_prodE`, `fdist_ext`, `reindex_onto`, `eq_big` (infotheo
   `probability/`, mathcomp `bigop`); `centropy_RV_comp0`
   (`entropy.v:498`); `unit_RV`/`inde_unit_RV` (`du2002/spp_proba.v:119`),
   `inde_RV_comp` (`pgg_trace_secrecy.v:29`), `inde_cond_entropy`
   (`dumas2017dual/lib/extra_entropy.v:559`); `fdist_uniform`,
   `card_Omega20`, `Secret`, `P` (`five_card_leakage.v`); `content_of`
   (`denboer_trace.v:39`); `encode_bool`/`decode_encode_bool`
   (`den_boer_encoding.v`); `pgg_commit` (`pgg_input_commitment.v:67`);
   `rho_from_words_weighted`/`word_weighted` (`pgg_weighted_words.v:60-65`);
   `pgl27P_word_gen`/`rho_word` (`pgl27_word_privacy.v:68-81`);
   `den_boer_profile` (`den_boer_profile.v:79`), `fc_kim_sigmas`
   (`five_card_kim.v:112`).

## Non-goals

- The verifier's row (position 1) as a theorem target: that full endpoints
  determine the secret is the landed den Boer leakage story
  (`den_boer_endpoints`, `leak_k5`); the Scope table's C8 language names it
  as the second determination locus but states nothing new about it.
- Any witness/rotation relation at `eps <> 0` (see invariant 3).
- The both-components product-map form (construction choice 6).
- The remaining request-section-11 items of the original cycle.
- WADT prose (separate cycle, unchanged).

## Probe record and remaining probe work (P0)

Searches the probe ran before proving (audit F14, recorded here): for C4,
`Search fdistmap fdist_prod` and pattern searches return only
`transitivity_privacy.fdistmap_prod_snd_const`/`..._prod_const` (constant
collapse, wrong shape) — infotheo lacks the lemma, confirming the response's
record. For C3's marginal, searches over `fdist_snd`/`fdist_uniform`/
`fdist_prod` return only `fdist_uniform_eq1`, `bij_uniform`,
`fdistmap_inj_uniform` — no uniform-marginal distribution lemma; the probe
went through the product decomposition instead (cheaper than the spec's
fiber-count fallback). For C7, no constant-conditioning lemma exists, but
the three-lemma chain above composes. Proof traps recorded for the landing:
`xpair_eqE` does not match the `preim`ed pair predicate and `pair_big` does
not match the product-indexed condition — use `eq_big` then
`reindex_onto (fun b => (a, b)) snd`; `comp_RV` never reduces under `/=`,
`rewrite /comp_RV` is required; the C2/C3 chain needs the product rewrite
BEFORE `-fdistX_prod fdistX2 fdist_prod1`.

P0 (before implementation): amend `probe_b_mutation.v` — replace M1 with a
semantic mutation (`= fdistmap g Q `x Pa`, which typechecks and must fail)
(audit F5); add M4 (C7 with `= 0`, must fail since `H(Secret) > 0` under
uniform `P`) and M5 (C8b with `` = `H `p_ (Secret R) ``, must fail) (audit
F6); strengthen the vacuity example to instantiate `probe_C6` at the
`den_boer_eps0_*` witnesses (audit F15). Recompile both probe files (one
rocqworker). Probe files are then frozen for this cycle.

## Fold-back log (2026-08-12)

Probe fold-backs: (1) C8a row gains the leading `PGG_idx 0` — spec's
two-element prediction was wrong, cons order was right; (2) C6/C7 strengthen
to all `j : nat`; (3) the constant-conditioning helper is dropped.

Soundness audit (NO-GO on the original invariant 3; all findings accepted
except F13): F1 invariant 3 rewritten, C9 added as the positive result;
F2 "leakage locus" reworded to payload locus, verifier row named; F3 C7
retagged `@main architecture` with in-comment caveats; F4 new invariant 4
(bias independence), C9b; F5/F6/F15 folded into P0; F7 readout decision and
anti-chronology recorded at C8; F8 pair-form export added; F9 C8a comment
rewording; F10 invariant 6 split; F11 distribution-vocabulary sweep; F12
`exec_dealer_trace` marked unprobed with fallback; F13 REJECTED (no
consumer); F14 search record added above.

Naming audit (GO with renames, all adopted): C5 single export through the
new `sa_joint_dist` (`pgl27_word_sample_joint_distE`); `_input_view` renamed
`five_card_exec_input_trace` (view is the static-observation family);
C8 names split raw/RV per the file convention, determination exports named
`*_centropy0` (`_leak` rejected — `leak` is a defined quantity in
`five_card_leakage.v:673`); `_nil` rejected for C6 (mathcomp `_nil` marks a
nil argument); `card_bool2` duplicate resolved locally (choice 7); C6 tag
downgraded to `@composes`; nine `Naming:` lines mapped to templates
(choice 8).
