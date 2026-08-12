# Spec: sample-law identities and the input-party trace bound (S5-1, S5-2, W4, W5)

Date: 2026-08-12. User go: 2026-08-12 ("make plan then complete these two"
naming the two S5 non-goals and the two S4 auditor candidates W4/W5).

Upstream chain: evaluation response `cf64d7ae` section 11 (S5 row) and the
as-built record of `2026-08-11-execution-plug-implementation-plan.md`
(deviation 3, W4/W5). This cycle turns the four recorded future candidates
into landed theorems. Everything extends the four files landed in the
previous cycle; no landed statement is modified.

## Scope (the four items)

| Item | Content |
|---|---|
| W4 | Word-space coalition `distE` twin at `pgl27_word_sample` |
| W5 | Cut-law ties: the pgl27 exact sample's cut law is the witness distribution; the five-card sample's cut law is the uniform-rotation image law |
| S5-1 | The `fdistmap` joint identity connecting `pgl27_word_sample` to the landed `pgl27P_word_gen`, via a generic product-map lemma infotheo lacks |
| S5-2 | The bound on the input-party trace observable at five-card: the committing parties' own trace rows are empty (they leak nothing), and the leakage locus is the dealer's row, which determines both committed bits |

## Pinned carriers

- pgl27 side: `Section pgl27_execution` context of `pgl27_exec.v`
  (`R : realType`, `mpP := pgl27_profile R`), word block after the section
  variable `secretP : R.-fdist bool`.
- five-card side: `Section five_card_execution` context of `five_card_exec.v`
  (`R`, bias `eps` with its three side conditions, word length `L`,
  `mpF := five_card_profile ...`), `dbP := P R` with
  `Omega = (bool * bool * 'I_5)%type`, `P R = fdist_uniform card_Omega20`.
- generic side: `Section` context of `pgg_sample_adapter.v` (generic imports
  only) for the product-map lemma; plain finTypes `A B C`,
  `P : R.-fdist A`, `Q : R.-fdist B`, `g : B -> C`.

## Claim ledger

Passing criterion for every row: the probe statement compiles to `Qed` at the
pinned carrier with zero `Admitted`/`Abort`/`Axiom`, and the mutation check
fails.

| # | Item | Claim (statement to probe) | Route | Risk |
|---|---|---|---|---|
| C1 | W4 | `pgl27_word_sample_coalition_distE : pgl27_word_sample_coalition_dist C = fdistmap (sa_static_coalition_view pgl27_word_sample pgl27_content_obs C) pgl27_word_sampleP` | `by apply: sa_coalition_distE => u; exact: pgl27_exec_endpoints.` — the exact twin of the landed seat form `pgl27_word_sample_seat_distE` and the exact-sample coalition form | LOW |
| C2 | W5 (witness tie) | `pgl27_sample_cut_distE : @sa_cut_dist R mpP pgl27_exec_plug pgl27_sample = pgl27_witness_cut_dist` | `sa_cut` of `pgl27_sample` is `snd` and `pgl27P R` is definitionally `fdist_uniform card_bool `x sw_rho_dist (mp_security mpP)` (landed `pgl27_sample_witness_prodE`); conclude by the `fdist_snd`-of-product chain used in the landed `pgl27_word_cut_distE` (`-/(fdist_snd _) -fdistX_prod fdistX2 fdist_prod1`) | LOW |
| C3 | W5 (rotation tie) | `five_card_sample_cut_distE : five_card_sample_cut_dist = fdistmap (fun k : 'I_5 => (five_card_group.fc_sigma ^+ k)%g) (fdist_uniform (card_ord 5))` | `five_card_sample_cut = (fun k => fc_sigma ^+ k) \o (fun w => w.2)`; `fdistmap_comp` reduces to the marginal claim `fdistmap (fun w : Omega => w.2) (P R) = fdist_uniform (card_ord 5)` — a uniform law over a product finType pushes to the uniform law on a factor. Probe searches infotheo for an existing uniform-marginal lemma first; fallback is a direct `fdist_ext`/`fdistmapE` fiber count (#fiber = 4, 4/20 = 1/5) | MEDIUM |
| C4 | S5-1 (generic) | `fdistmap_prodr (g : B -> C) : fdistmap (fun ab : A * B => (ab.1, g ab.2)) (P `x Q) = P `x fdistmap g Q` (name provisional, naming audit decides) | Response `cf64d7ae` records infotheo lacks it. Probe searches first (`fdistmap`+`fdist_prod` combinations); fallback proof: `fdist_ext => -[a c]`, both sides via `fdistmapE`/`fdist_prodE`, partition the fiber sum as `secret row x fiber of g` | MEDIUM |
| C5 | S5-1 (instance) | `pgl27_word_sample_joint_genE : fdistmap (fun u : pgl27_word_sampleT => (u.1, pgl27_word_cut u)) pgl27_word_sampleP = pgl27P_word_gen R secretP` (equivalently stated through `sa_arg`/`sa_cut` of `pgl27_word_sample`; probe decides which form elaborates) | C4 at `g := @word_eval pgl27_Msym 200 \o` tuple side, then `rho_from_words_weighted = fdistmap word_eval word_weighted` is definitional (`pgg_weighted_words.v:64`), so the right factor is `rho_word R` and the whole right side is `pgl27P_word_gen R secretP` by its definition `secretP `x rho_word` | MEDIUM-LOW given C4 |
| C6 | S5-2 (row emptiness) | `five_card_exec_input_raw_trace (a, b) w0 j = [::]` for all `j` | The committing parties erase to pure senders: `pgg_commit` is `SSend dealer DT_Sheet (PGG_sheet v) SFinish` (`pgg_input_commitment.v:67-69`) and the interpreter's `step` logs only `Init`/`Recv`/`Ret` payloads to a process's own trace (`smc_interpreter.v:54-76`), so rows 7 and 8 stay `[::]`; rows beyond the process count are `[::]` by `nth` default. Evaluation discipline: the run has symbolic `a b w0` leaves; probe must confirm `vm_compute`/abstract-leaves handling per `reference_interp_trace_abstract_leaves` and never let `done` see the run term | MEDIUM |
| C7 | S5-2 (observable secrecy) | With `five_card_exec_input_view j : {RV dbP -> 'I_5} := fun w => content_of (five_card_exec_input_raw_trace (w.1.1, w.1.2) (fc_sigma ^+ w.2)%g j)` (the `five_card_exec_trace` pattern at input rows): `` `H( Secret R \| five_card_exec_input_view j ) = `H `p_ (Secret R) `` | By C6 the RV is the constant `content_of [::]`. Probe searches infotheo for a constant-conditioning lemma (`H(Y \| const) = H(Y)`); fallback: derive from `centropy_RVE'` with the point mass at the constant, or via independence of a constant RV | MEDIUM |
| C8 | S5-2 (leakage locus) | (a) dealer-row readout: `nth [::] (run_interp 100 (den_boer_procs a b w0 0)).2 0 = [:: PGG_sheet (encode_bool b); PGG_sheet (encode_bool a)]` (payload order to be fixed by the probe — the trace conses, so the later receive heads the list); (b) with `five_card_exec_dealer_view : {RV dbP -> bool * bool}` decoding that row by `den_boer_decode`-style readout composed over the sample point: `five_card_exec_dealer_view = fun w => (w.1.1, w.1.2)` as functions, and `` `H( Secret R \| five_card_exec_dealer_view ) = 0 `` | (a) is a trace-row evaluation like C6 (leaves are `encode_bool a/b`, no permutation leaves in row 0); (b) the function identity uses `decode_encode_bool` (`den_boer_decodeK` pattern), then `Secret R = (fun p => p.1 && p.2) \o five_card_exec_dealer_view` and infotheo's `centropy_RV_comp0` (`entropy.v:498`) closes the entropy claim | MEDIUM |

## Construction choices (decided here, audit may contest)

1. **Location of C4**: `pgg-smc/security/pgg_sample_adapter.v`, a new small
   section before the `SampleAdapter` record. Reason: it is a generic
   sample-law lemma consumed by the instance identity; the file already holds
   the generic law layer and has generic imports only. Not upstream
   `probability/` — this repo's convention keeps project additions under
   `pgg-smc/`.
2. **C8 extractor**: the dealer row is read directly as
   `nth [::] (exec_run ...).2 (exec_dealer_id ...)` unfolded at the instance;
   a generic `exec_dealer_trace` field-style extractor IS added to
   `pgg_execution_plug.v` (three lines, mirror of `exec_input_trace` at
   `exec_dealer_id`). Reason: symmetry of the extractor family; the input and
   participant extractors landed generically, and C8 is the first consumer.
3. **C7/C8 observables are finType RVs** (`'I_5`, `bool * bool`), never raw
   `seq data` traces. Reason: raw traces have no distribution layer
   (soundness finding 3 of the previous cycle); every entropy statement must
   pass through a finType observable, as `five_card_exec_trace` does.
4. **Statement placement**: C1, C2, C5 in `pgl27_exec.v` (word block for C1
   and C5, exact block for C2); C3, C6, C7, C8 in `five_card_exec.v` inside
   `Section five_card_execution`; C4 (and a constant-conditioning helper if
   the probe finds none in infotheo) in `pgg_sample_adapter.v`.
5. **No landed statement changes.** All eight claims are additive; the four
   files of the previous cycle keep every existing identifier and statement.

## Soundness invariants

1. No new axiom or assumed constant; every new result depends on exactly the
   boolp trio (`propositional_extensionality`,
   `functional_extensionality_dep`, `constructive_indefinite_description`).
2. Honest scope of C6/C7 (mandatory prose in the statement comments): the
   input-party rows are empty because in THIS interpreter model a `Send` logs
   nothing to the sender's own trace. C7 is a statement about the executed
   trace observable of the committing parties' rows; it is NOT a
   commitment-privacy result — the committed payloads travel to the dealer's
   row, which C8 shows determines both bits. C7 without C8 would be
   misleading; they land together.
3. No tie is claimed between the five-card witness distribution
   (`five_card_witness_cut_dist = sw_rho_dist (mp_security mpF)`, the Kim
   biased word-shuffle law of `fc_kim_security_witness`) and the den Boer
   rotation cut law of C3. They are laws of different protocol layers (the
   shuffle law vs the sharing tape) and are not equal; the spec's witness tie
   (C2) is at pgl27 exact only, where `pgl27P` is definitionally the product
   with `sw_rho_dist`.
4. No new privacy claim beyond the stated conditional-entropy identities
   (C7 = no leakage through empty rows, C8 = total determination through the
   dealer row). Mixing bounds, coalition privacy, and view laws are untouched.
5. C8(b)'s `= 0` claim uses `centropy_RV_comp0` (`H(f \`o X | X) = 0`,
   infotheo `entropy.v:498`) — the determination direction, not an
   independence claim.
6. Quantifier scope: C6 holds for all `j : nat` (rows past the process count
   are `[::]` by `nth` default); C7 is stated for `j` in the meaningful range
   (as an `'I_2`-indexed or `j < 2` statement — probe decides which
   elaborates cleanly); C1-C5 are universally quantified over their stated
   arguments with no hidden side conditions.
7. Cited library objects: `sa_coalition_distE`, `sa_seat_distE`,
   `sa_cut_dist` (`pgg_sample_adapter.v`); `fdistmap_comp`, `fdistX_prod`,
   `fdistX2`, `fdist_prod1`, `fdistmapE`, `fdist_prodE`, `fdist_ext`
   (infotheo `probability/`); `centropy_RV_comp0`, `centropy_RVE'`
   (infotheo `information_theory/entropy.v`); `fdist_uniform`,
   `card_Omega20`, `Secret`, `P` (`five_card_leakage.v`); `content_of`
   (`denboer_trace.v:39`); `encode_bool`/`decode_encode_bool`
   (`den_boer_encoding.v`); `pgg_commit` (`pgg_input_commitment.v:67`);
   `rho_from_words_weighted`/`word_weighted` (`pgg_weighted_words.v:60-65`);
   `pgl27P_word_gen`/`rho_word` (`pgl27_word_privacy.v:68-81`). Each is used
   at the pinned carrier in the probe, not `Check`ed.

## Non-goals

- The verifier's row (position 1): its endpoint readout and the fact that
  full endpoints determine the secret are the landed den Boer leakage story
  (`den_boer_endpoints`, `leak_k5`); nothing new is stated about it.
- Any bound relating the Kim witness law to the rotation tape (see
  invariant 3).
- The remaining request-section-11 items of the original cycle.
- WADT prose (separate cycle, unchanged).

## Probe plan

One probe file `docs/superpowers/probes/2026-08-12-s5-w45/probe_a_laws.v`
(green) + `probe_b_mutation.v` (red), compiled by a `rocq-prover` agent
(opus, one rocqworker, rocq-mcp workflow). The probe:

- states C1-C8 at the pinned carriers and drives each to `Qed`;
- searches for existing infotheo lemmas before proving C3's marginal, C4,
  and C7's constant-conditioning helper, and records what it found;
- mutation-checks: C4 with `g` on the first component instead (must fail to
  typecheck against the claim), C6 at a participant row `2 + i` (must yield a
  non-empty trace, so the `= [::]` claim must fail), C8 with the payload
  order swapped (must fail);
- runs the tautology probe (`Fail by []`) on C3, C4, C5 and the vacuity
  check that the five-card section hypotheses are satisfiable at `eps = 0`;
- never edits any landed file and never `Require Import`s a probe from a
  permanent file.

Two failed attempts on one row stop-and-isolate per the probe-first skill's
stopping rule; a falsified row returns to this spec as a NO-GO fold-back, not
a silent scope change.
