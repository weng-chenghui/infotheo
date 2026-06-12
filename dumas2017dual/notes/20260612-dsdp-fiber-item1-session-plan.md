# DSDP fiber leg — item 1 (`guess_cinde_V2`) session budget

Companion to `20260612-dsdp-fiber-item5-closed.md`. Branch
`itp2026-dumas2017dual`. Scopes item 1 (the remaining reflection) into
schedulable sessions with green checkpoints.

## Verdict: split, not contiguous

Every natural stopping point in item 1 is a committable (Qed, no-admit) tree.
The decomposition is 4 standalone lemmas (steps 1–4) + an assembly (step 5);
each sub-lemma has a writable statement. Any unfinished sub-lemma can be
threaded forward as an explicit `Hypothesis` (the `Hcinde`-through-items-6/7
mechanism already proven this session), so stopping mid-item-1 never forces an
`Admitted`. "Contiguous-or-bust" is a false constraint.

## Seams cluster by machinery → 2 nominal sessions

### Session A — reflection-warm (steps 1 + 2)
Shares the `drc_*` lemmas, the GC-term de Bruijn slot analysis, and `Pr_code_*`
peeling with item 2's `Hbody` block (`dsdp_security_indcpa_fiber.v:975–1260`).

- **Step 1 `guess_triple_proj_code`**: adapt `Hbody` to keep 3 coords
  (guess_M, V2_M, V3_M) instead of 2. Smaller than `Hbody`. Commit, Qed.
- **Step 2 `view_indep_secrets`**: the hard core — the run-reflection showing
  the cipher view (`vt.1.1`) is constant in the v2,v3 sample binders. ~item-2
  scale (the load-bearing new work). Statement not yet pinned; Session A's first
  job is to pin it.
- Commit-safe fallback: if step 2 overruns, commit step 1 alone and thread
  step 2's statement as a `Hypothesis`. Tree stays green.

### Session B — algebra/assembly-warm (steps 3 + 4 + 5)
Different toolkit: `Pr_fst_put_invariant` / `predictor_locs_disj` /
`resolve_predictor_valid` / `denote_output_termE` / `cinde_RV_factor`. None of
the reflection machinery is needed.

- **Step 3** predictor-kernel V2-independence (leans on committed
  `Pr_fst_put_invariant` + `predictor_locs_disj`).
- **Step 4** s_read = output (leans on committed `denote_output_termE`).
- **Step 5** the `f·g` factorization into `cinde_RV_factor` → `guess_cinde_V2`,
  then inline it into items 6/7 (drop the `Hcinde` binder). Risk: the
  code-derived `f,g` must typecheck against `cinde_RV_factor`'s shape (the
  "obvious f,g is circular" trap, already flagged). If it stalls, commit 3+4
  and thread.

## Budget

| | nominal | if a core step overruns |
|---|---|---|
| Sessions | 2 | 3 (rarely 4) |
| Wall-clock | ~3–4.5h (A ≈ 1.5–2.5h, B ≈ 1.5–2h) | +~1 micro-session per overrun |
| Green checkpoints | up to 5 (one per sub-lemma) | same — overrun degrades into one more micro-session, never a blown block |

Only step 2 is genuinely big. The default 2-session split is efficient because
each session keeps its machinery hot. Conservative alternative: step 2 as its
own session, with 1 riding in front and 3/4/5 behind.

Scheduling subtlety: once step 2's exact statement is pinned (even before its
proof closes), it becomes a threadable hypothesis — which is what would let
Session B run first to de-risk the `cinde_RV_factor` shape before grinding the
reflection.

## Session A — DONE (commits after `6161a8a`)

Full `coqc` of the fiber file: exit 0, `.vo` rebuilt.

- **Step 1 `guess_triple_proj_code`** (Qed): the `(guess, V_2, V_3)`-projection
  of `guess_full_code` reflects to the rich-run form
  `vt ← denote_run_caps 11 8 9 10 7 6 [::] seed gc ;; s ← denote_s_get_body ;;
  guess ← resolve (pack predictor) … (vt.1.1, s) ;; v2 ← denote_v2_get_body ;;
  ret (msg_to_fin guess, msg_to_fin v2, msg_to_fin (chmsg_of_msg vt.1.2.1.2))`.
  Direct adaptation of `guess_full_proj_code` keeping the V_3 coordinate.

- **Step 2 `view_marginal_indep`** (Qed) — renamed from the planned
  `view_indep_secrets`. Refinement found during proof: the view-only run is NOT
  a raw-code equality, because `GC_put`/`GC_put_output` write the secret-dependent
  values into the heap (`V_2_cell` = chmsg(v2), `S_output_cell` = chmsg(output)).
  The correct, provable form is the cipher-list **marginal** (`dmargin fst`):
  `dmargin fst (Pr_code (drun (push m1 (push m0 seed)) gc_rest) h)` is invariant
  under `m0, m1`. The heap writes land in the discarded `snd`. Proof: peel the run
  with the `drun_*` lemmas (`drun_sample_msg/renc`, `drun_put`, `drun_enc_hop`,
  `drun_let`, `drun_put_output`, `drun_ret`) + `Pr_code_sample/put/ret` +
  `dfst_dlet_commut`, descending each sample with `eq_dlet`; at the `GC_ret` leaf
  `SubDistr.distr_ext` + `dmargin_dunit` drops the heaps and `congr (mu (dunit _) w)`
  closes by **convertibility** — the cipher list is definitionally free of the
  secrets (the de Bruijn lookups for `[HE_var 1;0;3;2]` compute past the v2/v3
  slots to the let-combines/hop-ciphers). No plan defect: step 2 is TRUE, just
  distributional rather than raw-code.

  GOTCHAs for Session B: (i) `card_renc_neq` is a section hyp, so `drun_sample_renc`
  takes no explicit arg; passing it mis-fills the `e` slot. (ii) The `!`-batched
  renc peel times out on the big term; peel LHS then RHS with plain `rewrite` once
  only one `GC_sample card_renc` remains, then `eq_dlet`. (iii) `gc_rest` in the
  statement is the literal `gc`-after-two-`GC_sample card_msg`; Session B produces
  it by `gc_eq` + 2 `drc_sample_msg`, and bridges `vt.1.1` to `drun … gc_rest` via
  `denote_run_caps_fst`.

## Session B — remaining (steps 3 + 4 + 5)

Per the seam map above. Consume `view_marginal_indep` (view ⊥ secrets, marginal),
add predictor-kernel V_2-independence (`Pr_fst_put_invariant` + `predictor_locs_disj`;
predictor reads only its own locs, disjoint from `protocol_state`), s_read = output
(`denote_output_termE`), and assemble the `cinde_RV_factor` factorization into
`guess_cinde_V2`, then inline it for the `Hcinde` hypothesis in items 6/7.

## Session B — progress (committed) + two findings

Committed, full `coqc` exit 0:
- **`guess_inner` + `guess_triple_peel`**: the (guess,V2,V3) triple experiment =
  two uniform secret draws then `guess_inner a b` (the run/predictor with secrets
  `a,b` fixed). Mirrors item-2 `HbodyEq` (`gc_eq` + 2 `drc_sample_msg` + `sba`).
  GOTCHA: `guess_full_code` is on the LHS, so `sba` targets `[in X in X = _]`
  (item-2's orientation was flipped).
- **de Bruijn helpers** `de_val_nth_pushS/push0/pushrand`, `as_plain_Gplain`,
  `dhe_var` (all `by []`). `push_val` consumes one successor index, `push_rand`
  is transparent; keep `de_val_nth seed` folded so the seed hypotheses apply.

### Finding 1 — DEFECT FIXED: seed weights unlinked to `w_v1..w_u3`
`Sout` (line ~1005) is `dsdp_output w_v1 w_u1 w_u2 w_u3 V2 V3` with **abstract**
weights, but the run's leaked `S` is computed from the **seed's** weight slots.
With `seed` abstract and unlinked, the cinde is false. User-approved fix added
(`seed_wu1/wu2/wu3/wv1 : as_plain (de_val_nth seed 0..3) = w_u1,w_u2,w_u3,w_v1`).
True once `seed` is instantiated; makes `Sout` = the run's leaked output.

### Finding 2 — RESOLVED: the SSProve program is faithful; `guess_run_cells` DONE
The apparent "cipher-shaped" `S_output` value was a misread of the un-reduced env
display. From `denote_he` (`dsdp_game_code.v:354-356`), `HE_mul`/`HE_add`/`HE_sub`
are **plaintext** ring ops (`Gplain (as_plain a * as_plain b)`), and `HE_dec` is a
`Gplain 0` stub (off the game path) — so `output_term` denotes to a **plaintext
scalar**. Reducing the de Bruijn reads (`de_val_nth_*`) turns the stored value into
`as_plain(de_val seed 0)*as_plain(de_val seed 3) + as_plain(de_val seed 1)*msg a
+ as_plain(de_val seed 2)*msg b`, which the seed hypotheses close to
`dsdp_output`. So the program puts the protocol's leaked S (the plain scalar, =
`D_privA(γ) − r2 − r3 + u1·v1` per the paper; masks r2,r3 sit at slots 4/5 and are
unread) into `S_output_cell`. `guess_run_cells` is **Qed**, full `coqc` exit 0.
Key proof move: after `get_set_heap_eq`, do NOT use `denote_output_termE` (the term
has already computed past it); reduce de Bruijn reads directly with
`!(de_val_nth_pushS, de_val_nth_pushrand, de_val_nth_push0)` then `seed_*` +
`/dsdp_output`. See [[reference_dsdp_protocol_flow]].

### guess_inner_v2v3_det — DONE (Qed, committed)
Full predictor peel proved. `guess_run_cells` extended with a 3rd conjunct
`z.1.1.2.1.2 = msg b` (captured v3, closes by `by []`). Pattern that worked, reusable
for `guess_inner_out`: `dmargin_comp`+`dmarginE`+`dlet_dunit_id`+`eq_in_dlet` → support
fact; peel `Pr_code` of `guess_inner` bind-by-bind with `Pr_code_bind`+`dfst_dlet_commut`
+`distr.dinsupp_dlet`; collapse the deterministic `get` bodies with inline
`have Hxget : Pr_code (denote_X_get_body _) h = dunit (val, h) by rewrite /denote_X_get_body
Pr_code_get <heapfact> Pr_code_ret`; predictor `V_2`-preservation via
`have Hnotin : (V_2_cell t_msg).1 \notin domm (locs predictor) by apply:
(@notin_has_separate _ _ (protocol_state t_msg) (locs predictor) (V_2_cell t_msg));
[exact: fhas_set | exact: fseparateC predictor_locs_disj]` then
`Pr_code_preserves (resolve_predictor_valid _ _) Hnotin Hpred`. CRITICAL SSReflect note:
this section's selector does NOT auto-focus, so use inline `have H : P by tac` (never
`have H : P.` then a separate proof sentence — leaves 2 goals focused) and `split; first by`
/ `; [ | ]` (never `1:{}`/`2:{}`).

### Remaining: guess_inner_out + guess_cinde_V2 (skeletons REMOVED; re-add from here)
Re-add both skeletons after `guess_inner_v2v3_det`; prove then commit.

- **`guess_inner_out`** (a b a' b'): `output(a,b) = output(a',b') ->
  dmargin .1.1 (Pr_fst (guess_inner a b)) = dmargin .1.1 (Pr_fst (guess_inner a' b'))`.
  THE crux. Plan (uses the v2v3_det peel pattern above):
  `rewrite dmargin_comp` on both sides → `dmargin (fun vh => vh.1.1.1) (Pr_code
  (guess_inner _ _) emptym)`. Peel run (`Pr_code_bind` + `dfst_dlet_commut`/the
  dmargin-dlet commute); collapse `s_get` (s = chmsg(output) via `guess_run_cells`'s
  `HS`) and `v2_get` (lossless dunit) with the inline-have pattern, keeping `guess`;
  the inner reduces to `dmargin (msg_to_fin ∘ fst) (Pr_code (resolve predictor …
  (vt.1.1, chmsg(output))) h_run)`. Drop `h_run → emptym` with `Pr_fst_agree_locs`
  (`resolve_predictor_valid` + the `Hnotin`-style `\notin domm (locs predictor)` for
  every protocol cell the run wrote — `V_2_cell`, `S_output_cell`; run touches only
  `protocol_state`), so the predictor sees only `(vt.1.1, output)`. The guess marginal
  is then `dlet (over the run's vt.1.1 marginal) of dmargin(…) (predictor(view,
  chmsg output) emptym)`. Connect the run's vt.1.1 marginal to `drun` via
  `denote_run_caps_fst` (`xy ← denote_run_caps … ;; ret xy.1.1 = drun … gc_rest`),
  then `view_marginal_indep` (card_renc_neq) gives that drun cipher-list marginal is
  the same for `(a,b)` and `(a',b')`. Same output (hyp) + same view marginal ⇒ equal.

- **`guess_cinde_V2`**: `guess_sample_fdist |= guess_rv _|_ V2 | Sout`. Via
  `cinde_RV_factor` with code-derived `f y z` (secret-pair mass for V2=y, Sout=z) and
  `g z x` (the predictor kernel K(z)(x)). Bridge `pfwd1 [%guess_rv,V2,Sout]` to the
  triple via `guess_triple_peel` + the `sdistr_to_fdist`/`fdistmap`/`Pr_fst_map`
  pattern (as in `guess_joint_fdist_marginal`); fiber-sum over V3 with `guess_inner_out`
  giving the output-determined kernel. Then inline for `Hcinde` in items 6/7.

Then item 8 (real-vs-zero composition + final theorem).
