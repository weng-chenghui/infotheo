# Reduction-Form Security Statements Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development
> to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.
>
> Spec: `dumas2017dual/notes/20260728-reduction-form-security-statements.md` (commit 4fc787ad).
> Branch: `20260729-0028-reduction-form-security` (from `itp2026-dumas2017dual`).

**Goal:** Delete `epsilon_cpa` and the `enc_ind_cpa_real_or_zero` axiom; restate every
computational bound as the IND-CPA advantage (`indcpa_epsilon`) of an explicitly
constructed reduction package, SSProve case-study style; delete the statdist headline;
apply the audited renames.

**Architecture:** 8 phases, each a full-tree-buildable atomic commit. Renames first
(Phase 1), dead-surface deletion second (Phase 2), the new functional third (Phase 3),
then signature (4) and the two proof chains (5, 6), axiom deletion last-but-one (7),
documentation sweep last (8). Phase 7 failing to compile signals a missed consumer.

**Tech stack:** Rocq 9.x + mathcomp + SSProve 0.3.1 under the LOCAL opam switch
`/Users/cheng-huiweng/Projects/coq/_opam`. Build: `make -f Makefile` at repo root
(delegates to Makefile.coq). Blueprint gate: `dumas2017dual/blueprint/check_coverage.py`.

---

## Execution protocol (user directives, mandatory)

1. **Per task, dispatch a `rocq-prover` subagent** with the task text below. Monitor its
   progress via `git status` / file mtimes. If ~15 minutes pass with no progress written
   to actual `.v` files, stop the subagent and take over inline using the `rocq:autoprove`
   skill plus `mathcomp-skills` (rocq-mcp loop: `rocq_start` preamble/dev-copy,
   `rocq_step_multi` battery, `rocq_check` commit). Read the subagent's memory first.
2. **After each proved or re-proved lemma**, invoke the `rocq:proof-golfer` subagent on it
   before the task's commit.
3. **Audit gates:** `rocq-auditor` Stage 2 before commits that add identifiers or proof
   bodies (Tasks 3–7). Pure rename/deletion commits (Tasks 1, 2, 8) use
   `ROCQ_AUDIT_BYPASS=1`. **Skip S996 (comment-style) findings entirely** per user.
4. **Every task ends with:** full-tree `make` clean under the local switch +
   `python3 dumas2017dual/blueprint/check_coverage.py` OK + commit. `git commit`
   only — no push.
5. **Stop only for spec/plan defects.** Do not stop for tactic-level difficulty; escalate
   through the autoprove loop instead.

Build command used everywhere below:

```bash
cd /Users/cheng-huiweng/Projects/coq/infotheo-itp
eval $(opam env --switch /Users/cheng-huiweng/Projects/coq --set-switch)
make -j6 2>&1 | tail -20   # expect no Error; .vo count unchanged or per-task delta
python3 dumas2017dual/blueprint/check_coverage.py   # expect OK
```

Consumer map (verified 2026-07-29; legacy/, .scratch/, probe_* files are NOT in
`_CoqProject` and never gate the build — probe files get vocabulary-only updates):

| Identifier | Defined | Built consumers |
|---|---|---|
| `epsilon_cpa`, axiom | `indcpa_ror.v:241,256` | `dsdp_game_code.v`, `dsdp_game_derivation.v`, `dsdp_indcpa_advantage.v`, `dsdp_simulator.v`, `dsdp_main.v`, `idealized_indcpa.v` |
| `adm`, `adv_sim_le` trio | `smc/ssprove_ext_simulator.v:36,42,52,73` | `dsdp_simulator.v` |
| `dsdp_adm`, `dsdp_adv_sim_le` | `dsdp_simulator.v:225,279` | (self) + blueprint `security.tex:196` |
| `gc_dsdp` trio | `dsdp_game_code.v:1029,1053,1064` | (self only) |
| `dsdp_advantage_derived(_leak_S)` | `dsdp_indcpa_advantage.v:63,405` | `dsdp_simulator.v:292`, `dsdp_main.v:738,888` |
| `dsdp_indcpa_secrecy` | `dsdp_game_derivation.v:691` | `dsdp_indcpa_advantage.v:116`, `dsdp_main.v:132` |
| `log_id` | `dsdp_guess_fiber.v:1772` | `dsdp_main.v:820` |
| statdist surface | `smc/ssprove_ext_statdist.v`, `dsdp_simulator.v:512,525` | `dsdp_main.v:58,894–936` only |

---

### Task 1: Renames, no statement changes (spec Phase 1)

**Files:**
- Modify: `smc/ssprove_ext_simulator.v` (whole file, 85 lines)
- Modify: `dumas2017dual/dsdp/simulation/dsdp_simulator.v:222–301` (+ any later `dsdp_adm` use)
- Modify: `dumas2017dual/dsdp/symbolic_game/dsdp_game_code.v:1002–1077` (gc_dsdp trio + comments)
- Modify: `dumas2017dual/dsdp/symbolic_game/dsdp_game_derivation.v:683–694` (name + comment at :688)
- Modify: `dumas2017dual/dsdp/indcpa_hopping/dsdp_indcpa_advantage.v:56–118, 398–441`
- Modify: `dumas2017dual/dsdp/dsdp_main.v:25–36 (header), :121–134, :726–745, :756–782, :843–892`
- Modify: `dumas2017dual/dsdp/simulation/probe_p5_skeletons.v` (vocabulary only, not built)
- Modify: `dumas2017dual/blueprint/src/security.tex:196`

- [ ] **Step 1.1: rename in `smc/ssprove_ext_simulator.v`.** `adm` → `admissible`
  (Context param at :36, all 9 uses incl. binder `AT_adm` → `AT_admissible` at :78 and
  the header/doc comments); `adv_sim_le` → `advantage_sim_le`;
  `adv_sim_le_from_endpoint` → `advantage_sim_le_from_endpoint`;
  `adv_sim_le_reduction` → `advantage_sim_le_reduction`. **No signature change** (that
  is Task 4): `eps : R` stays for now. Watch §1: keep lines ≤ 80 chars after rename.
- [ ] **Step 1.2: `dsdp_simulator.v`.** Rename `dsdp_adm` → `dsdp_locs_disjoint` AND drop
  the unused package argument:

```coq
(* dsdp_locs_disjoint — the adversary-location side condition: LA is disjoint
   from the protocol state and from the real and zero encryption oracle
   location sets. *)
Definition dsdp_locs_disjoint (LA : Locations) : Prop :=
  fseparate LA (protocol_state t_msg) /\
  fseparate LA (locs (oracle_real_pkg renc_card rand_of_renc msg_of_chmsg
                        chcipher_of_cipher pkey_of_party)) /\
  fseparate LA (locs (oracle_zero_pkg renc_card rand_of_renc t_msg
                        chcipher_of_cipher pkey_of_party)).
```

  Rename `dsdp_adv_sim_le` → `dsdp_advantage_sim_le`; in its statement replace the class
  argument `dsdp_adm` with `(fun LA _ => dsdp_locs_disjoint LA)`:

```coq
Lemma dsdp_advantage_sim_le
    (cipher_of_chcipher : t_cipher -> cipher AHE)
    (chcipher_of_cipherK : cancel chcipher_of_cipher cipher_of_chcipher) :
  advantage_sim_le (game_iface_leak_S t_msg t_cipher)
    (fun LA _ => dsdp_locs_disjoint LA)
    (real_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
       pkey_of_party msg_of_idx rand0 seed)
    dsdp_ideal_pkg dsdp_simulator_pkg
    (2%:R * epsilon_cpa AHE).
```

  The proof body is unchanged: the intro pattern
  `move=> LA A A_valid [Hstate [Hore Hoze]]` still destructs the same conjunction after
  beta. Verify with `rocq_compile_file`.
- [ ] **Step 1.3: `dsdp_game_code.v`.** `gc_dsdp` → `game_code_dsdp`,
  `hop_sites_gc_dsdp` → `hop_sites_game_code_dsdp`,
  `advantage_gc_dsdp` → `advantage_game_code_dsdp_le` (definitions :1029/:1053/:1064,
  uses inside those proofs, and the surrounding comments :1002–1028, :1049–1063). Update
  the `advantage_gc_dsdp` mention in `dsdp_game_derivation.v:688`'s comment.
- [ ] **Step 1.4: cross-file renames.** `dsdp_advantage_derived` →
  `dsdp_derived_game_advantage_le` and `dsdp_advantage_derived_leak_S` →
  `dsdp_derived_game_advantage_le_leak_S` (def `dsdp_indcpa_advantage.v:63,405`; uses
  `dsdp_simulator.v:292`, `dsdp_main.v:738,888` and comment mentions).
  `dsdp_indcpa_secrecy` → `dsdp_indcpa_secrecy_le` (def `dsdp_game_derivation.v:691`;
  uses `dsdp_indcpa_advantage.v:116`, `dsdp_main.v:132`, comments).
  `dsdp_alice_simulation_secure` → `dsdp_alice_simulation_advantage_le`
  (`dsdp_main.v:850`, use at :933, header :34).
- [ ] **Step 1.5: probe + blueprint.** In `probe_p5_skeletons.v` rename the 11 bare `adm`
  and 4 `dsdp_adm` occurrences to match (file is not built; text-level edit is enough).
  In `blueprint/src/security.tex:196` change
  `...dsdp_simulator.dsdp_adv_sim_le` → `...dsdp_simulator.dsdp_advantage_sim_le`.
- [ ] **Step 1.6: verify + commit.** Run the build command block (make + check_coverage).
  Then:

```bash
ROCQ_AUDIT_BYPASS=1 git commit -am "reduction-form phase 1: audited renames, no statement changes"
```

### Task 2: Delete the statdist headline (spec Phase 2)

**Files:**
- Modify: `dumas2017dual/dsdp/dsdp_main.v` (delete :894–936, `Require` :58, header :36–37)
- Modify: `dumas2017dual/dsdp/simulation/dsdp_simulator.v` (delete `view_real_mass1` :510–521, `view_simulated_mass1` :522–…)
- Delete: `smc/ssprove_ext_statdist.v`; Modify: `_CoqProject:101`
- Modify: `dumas2017dual/blueprint/src/security.tex:224–232` (delete node) + any `\uses{thm:alice_view_statdist}`

- [ ] **Step 2.1:** delete `Theorem dsdp_alice_view_statdist_le` (dsdp_main.v:894–936,
  including its comment), the header index lines :36–37, and
  `Require Import smc.ssprove_ext_statdist.` (:58).
- [ ] **Step 2.2:** in `dsdp_simulator.v` delete `view_real_mass1` and
  `view_simulated_mass1` (their only consumers were dsdp_main.v:924/:927). First confirm
  with `grep -rn "view_real_mass1\|view_simulated_mass1" --include="*.v" . | grep -v legacy`
  that nothing else consumes them. Keep `view_pair_challenger` / `view_resolved` /
  `test_adversary` / `view_resolve_eq` **only if** still consumed after this deletion;
  if `grep` shows them fully dead, delete them in the same commit (aggressive-cleanup
  rule) and note it in the commit message.
- [ ] **Step 2.3:** `git rm smc/ssprove_ext_statdist.v`; remove line
  `smc/ssprove_ext_statdist.v` from `_CoqProject` (:101).
  (`dumas2017dual/dsdp/simulation/probe_p3_statdist.v` is not in `_CoqProject`; leave it.)
- [ ] **Step 2.4:** blueprint: delete the `thm:alice_view_statdist` node
  (`security.tex:224–232`) and `grep -rn "alice_view_statdist" dumas2017dual/blueprint/src/`
  to remove any `\uses` / `\ref`. Also delete the statdist line from the Part overview
  around `security.tex:188` if it names the deleted theorem.
- [ ] **Step 2.5:** verify + commit:

```bash
# build block, then:
ROCQ_AUDIT_BYPASS=1 git commit -am "reduction-form phase 2: delete the statdist headline and its dead support"
```

### Task 3: Add `indcpa_epsilon`; retire `log_id` (spec Phase 3)

**Files:**
- Modify: `homomorphic_encryption/indcpa_ror.v` (insert after `End indcpa_ror.` :231)
- Modify: `dumas2017dual/dsdp/indcpa_hopping/dsdp_guess_fiber.v:1769–1784` (delete `log_id`)
- Modify: `dumas2017dual/dsdp/dsdp_main.v:806–822` (expand the call site)

- [ ] **Step 3.1:** insert into `indcpa_ror.v`, directly after `End indcpa_ror.`
  (keep `epsilon_cpa` / the Axiom below it untouched until Task 7):

```coq
(** indcpa_epsilon — the IND-CPA real-or-zero advantage of [reduction]: the
    [AdvantageE] of distinguishing [oracle_encrypt_real] from
    [oracle_encrypt_zero]. *)
Definition indcpa_epsilon
    (AHE : AHEncType) (Renc : finType) (index_renc : nat)
    (renc_card : #|Renc| = index_renc) (rand_of_renc : Renc -> rand AHE)
    (t_msg t_cipher : choice_type)
    (msg_of_chmsg : t_msg -> plain AHE)
    (chcipher_of_cipher : cipher AHE -> t_cipher)
    (pkey_of_party : party_id -> pub_key AHE)
    (reduction : raw_package) : R :=
  AdvantageE
    (oracle_encrypt_real AHE Renc index_renc renc_card rand_of_renc
       t_msg t_cipher msg_of_chmsg chcipher_of_cipher pkey_of_party)
    (oracle_encrypt_zero AHE Renc index_renc renc_card rand_of_renc
       t_msg t_cipher chcipher_of_cipher pkey_of_party)
    reduction.
```

  (The file has no `Set Implicit Arguments`; all arguments explicit, matching the Axiom's
  argument list. Binder names follow the file: `index_renc`, not `card_renc`.)
- [ ] **Step 3.2:** delete `Lemma log_id` (+ its comment) from `dsdp_guess_fiber.v`.
- [ ] **Step 3.3:** in `dsdp_main.v`'s `dsdp_alice_unpredictability_entropy_ge` proof,
  replace the line
  `rewrite -(log_id (m := card_msg) (eps := epsilon_cpa AHE) Hcard0 epsilon_cpa_ge0).`
  with the inline expansion (candidate; probe with `rocq_step_multi` against the live
  goal; imports `addf_div` = ssralg, `logDiv` = `lib/realType_ln.v:227`):

```coq
have -> : (log card_msg%:R - log (1 + 2%:R * card_msg%:R * epsilon_cpa AHE)
           = - log (card_msg%:R^-1 + 2%:R * epsilon_cpa AHE) :> R)%R.
  have -> : (card_msg%:R^-1 + 2%:R * epsilon_cpa AHE =
             (1 + 2%:R * card_msg%:R * epsilon_cpa AHE) / card_msg%:R :> R)%R
    by rewrite mulrDl mul1r mulrAC mulfK ?gt_eqF ?ltr0n.
  by rewrite logDiv ?opprB ?ltr0n // ltr_pwDl ?ltr01 // !mulr_ge0 ?ler0n.
```

  If the call site reads badly after golfing, take the spec's fallback instead:
  `Local Lemma log_invD (m : nat) (x : R)` in `dsdp_guess_fiber.v` with binder `x`
  (§14), stating `(0 < m)%N -> 0 <= x -> - log (m%:R^-1 + x) = log m%:R - log (1 + m%:R * x)`.
- [ ] **Step 3.4:** golf the touched proof (`rocq:proof-golfer`), run rocq-auditor
  Stage 2 (skip S996), then verify + commit:

```bash
# build block, then:
git commit -am "reduction-form phase 3: add indcpa_epsilon; retire log_id"
```

### Task 4: `advantage_sim_le` adversary-indexed bound (spec Phase 4)

**Files:**
- Modify: `smc/ssprove_ext_simulator.v:42–83`
- Modify: `dumas2017dual/dsdp/simulation/dsdp_simulator.v` (`dsdp_advantage_sim_le`)

- [ ] **Step 4.1:** restate the trio with `bound : raw_package -> R`:

```coq
(* advantage_sim_le E admissible Real Ideal Sim bound — bounded simulation
   security relative to the admissible-adversary class: every valid,
   admissible adversary A distinguishes the real package from the simulator
   composed with the ideal package with advantage at most bound A. *)
Definition advantage_sim_le (Real Ideal Sim : raw_package)
    (bound : raw_package -> R) : Prop :=
  forall (LA : Locations) (A : raw_package),
    ValidPackage LA E A_export A -> admissible LA A ->
    AdvantageE Real (Sim ∘ Ideal) A <= bound A.

Lemma advantage_sim_le_from_endpoint
    (Real Endpoint Ideal Sim : raw_package) (bound : raw_package -> R)
    (game_le : forall (LA : Locations) (A : raw_package),
       ValidPackage LA E A_export A -> admissible LA A ->
       AdvantageE Real Endpoint A <= bound A)
    (sim_eq0 : forall (LA : Locations) (A : raw_package),
       ValidPackage LA E A_export A -> admissible LA A ->
       AdvantageE Endpoint (Sim ∘ Ideal) A = 0) :
  advantage_sim_le Real Ideal Sim bound.

Lemma advantage_sim_le_reduction
    (Real Ideal Sim : raw_package) (bound : raw_package -> R)
    (sim_le : advantage_sim_le Real Ideal Sim bound)
    (T A : raw_package) (LAT : Locations)
    (AT_valid : ValidPackage LAT E A_export (A ∘ T))
    (AT_admissible : admissible LAT (A ∘ T)) :
  AdvantageE (T ∘ Real) (T ∘ Sim ∘ Ideal) A <= bound (A ∘ T).
```

  All three proof bodies are unchanged (the bound is only ever used at the quantified
  adversary, so `eps` → `bound A` / `bound (A ∘ T)` is a beta-neutral edit).
- [ ] **Step 4.2:** in `dsdp_simulator.v`, `dsdp_advantage_sim_le` passes a constant
  function so this phase compiles before the bounds change (Task 6 replaces it):
  final argument `(2%:R * epsilon_cpa AHE)` → `(fun _ : raw_package => 2%:R * epsilon_cpa AHE)`.
  Proof body unchanged.
- [ ] **Step 4.3:** golf if any body changed, rocq-auditor Stage 2 (skip S996),
  verify + commit:

```bash
git commit -am "reduction-form phase 4: advantage_sim_le takes an adversary-indexed bound"
```

### Task 5: Chain I — non-leak_S ladder to reduction form (spec Phase 5)

**Files:**
- Modify: `dumas2017dual/dsdp/symbolic_game/dsdp_game_code.v:886–995, 1064–1076`
- Modify: `dumas2017dual/dsdp/symbolic_game/dsdp_game_derivation.v:691–708`
- Modify: `dumas2017dual/dsdp/indcpa_hopping/dsdp_indcpa_advantage.v:63–118`
- Modify: `dumas2017dual/dsdp/dsdp_main.v:121–134`

All five restatements below use the section's own variable names. Inside
`Section dsdp_game_code` the section variables are exactly the argument list the old
proofs pass to the axiom (`AHE Renc card_renc renc_card rand_of_renc t_msg t_cipher
msg_of_chmsg chcipher_of_cipher pkey_of_party`). Abbreviate nothing: `shim_0`-style
names are display shorthand of the spec and MUST NOT become identifiers.

- [ ] **Step 5.1: `advantage_hop`** (dsdp_game_code.v:886). New conclusion:

```coq
  AdvantageE (denote_game (zero_hop_prefix i gc))
             (denote_game (zero_hop_prefix i.+1 gc)) A
    <= indcpa_epsilon AHE Renc card_renc renc_card rand_of_renc t_msg t_cipher
         msg_of_chmsg chcipher_of_cipher pkey_of_party
         (A ∘ denote_game_shim (zero_hop_prefix i gc) i).
```

  Proof: identical up to `rewrite -Advantage_link`, then the axiom application becomes
  `exact: lexx.` (both sides are delta-equal: `oracle_real`/`oracle_zero` at
  :708/:716 unfold to `oracle_encrypt_real`/`oracle_encrypt_zero` at exactly these
  arguments, and `indcpa_epsilon` unfolds to `AdvantageE` of those). If `lexx` fails on
  conversion, try `rewrite /indcpa_epsilon; exact: lexx.` then
  `rewrite /indcpa_epsilon /oracle_real /oracle_zero; exact: lexx.`
- [ ] **Step 5.2: `advantage_sum_ladder_le`** (:930). New conclusion:

```coq
  forall (n start : nat),
  advantage_sum (denote_game (zero_hop_prefix start gc))
    [seq (denote_game (zero_hop_prefix l gc) : raw_package) | l <- iota start.+1 n]
    (denote_game (zero_hop_prefix (start + n.+1) gc)) A
    <= \sum_(l < n.+1)
         indcpa_epsilon AHE Renc card_renc renc_card rand_of_renc t_msg t_cipher
           msg_of_chmsg chcipher_of_cipher pkey_of_party
           (A ∘ denote_game_shim (zero_hop_prefix (start + l) gc) (start + l)).
```

  Proof strategy (MUST be probed live with `rocq_step_multi`; the spec flags
  `big_ord_recl` vs `big_ord_recr` as unresolved — upstream `PRFPRG.v:348` uses `recr`):

```coq
elim=> [|n IHn] start.
- cbn [iota map advantage_sum]. rewrite big_ord1 addn0. by apply: advantage_hop.
- cbn [iota map advantage_sum].
  rewrite big_ord_recl addn0 addrC.  (* head summand = site start; check /bump *)
  apply: lerD.
  + apply: le_trans (IHn start.+1) _.   (* endpoint realigns via -addSnnS as before *)
    rewrite -addSnnS.                    (* if needed on the advantage_sum endpoint *)
    by apply: ler_sum => l _; rewrite addSnnS.  (* per-summand start.+1+l = start+l.+1 *)
  + by apply: advantage_hop.
```

  Notes for the prover: (a) `lift ord0 l` computes to `l.+1` through `/bump /= add1n`
  if the summand does not reduce; (b) if `recl` misaligns, switch to `big_ord_recr` and
  restructure with `IHn start` — whichever closes; both realignments (`-addSnnS` on the
  endpoint, `addSnnS` under the binder via `eq_bigr`/`ler_sum`) are available;
  (c) mathcomp-skills `reference.md` §34 (bigops) before writing tactics.
- [ ] **Step 5.3: `advantage_le`** (:973). New conclusion:

```coq
  AdvantageE (denote_game (all_real gc)) (denote_game (all_zero gc)) A
    <= \sum_(l < size (hop_sites gc))
         indcpa_epsilon AHE Renc card_renc renc_card rand_of_renc t_msg t_cipher
           msg_of_chmsg chcipher_of_cipher pkey_of_party
           (A ∘ denote_game_shim (zero_hop_prefix l gc) l).
```

  Proof: keep `rewrite /all_real /all_zero /hop_sites size_iota` + `case Hch:`; empty
  branch `by rewrite advantage_self_zero big_ord0 lexx.` — probe; if `rewrite lexx`
  is ill-formed use `by rewrite advantage_self_zero big_ord0.` with `lexx`/`sumr_ge0`.
  Actually the goal is `AdvantageE G G A <= \sum_(l < 0) …` = `0 <= 0` after both
  rewrites: close with `by rewrite advantage_self_zero big_ord0.`. Non-empty branch:
  `le_trans tri` then `advantage_sum_ladder_le` at `start = 0`, then realign
  `\sum eps(0 + l)` to `\sum eps(l)` via `under eq_bigr do rewrite add0n` (or
  `ler_sum` + `add0n`).
- [ ] **Step 5.4: `advantage_game_code_dsdp_le`** (:1064). New conclusion (spell both
  summands in full):

```coq
  AdvantageE (denote_game (all_real game_code_dsdp))
             (denote_game (all_zero game_code_dsdp)) A
    <= indcpa_epsilon AHE Renc card_renc renc_card rand_of_renc t_msg t_cipher
         msg_of_chmsg chcipher_of_cipher pkey_of_party
         (A ∘ denote_game_shim (zero_hop_prefix 0 game_code_dsdp) 0)
     + indcpa_epsilon AHE Renc card_renc renc_card rand_of_renc t_msg t_cipher
         msg_of_chmsg chcipher_of_cipher pkey_of_party
         (A ∘ denote_game_shim (zero_hop_prefix 1 game_code_dsdp) 1).
```

  Proof: `have H := advantage_le game_code_dsdp A_valid A_disj_state A_disj_ore
  A_disj_oze.` then reduce the ordinal sum at bound `size (hop_sites game_code_dsdp)`
  (= 2 computationally): candidate
  `by move: H; rewrite !big_ord_recl big_ord0 addr0 !add0n.` — expect index arithmetic
  `0`, `lift ord0 ord0 = 1`; probe.
- [ ] **Step 5.5: `dsdp_indcpa_secrecy_le`** (dsdp_game_derivation.v:691). New
  conclusion: the RHS of Step 5.3's `advantage_le` with `P`'s projections substituted
  and the bound rewritten to `count_obs_hops (corrupted_view P)`:

```coq
  AdvantageE (real_game P) (zero_game P) (adv_package Adv)
    <= \sum_(l < count_obs_hops (corrupted_view P))
         indcpa_epsilon (exp_enc_scheme P) (exp_rand_carrier P)
           (exp_card_randomness P) (exp_rand_carrier_card P)
           (exp_rand_of_carrier P) (exp_choice_msg_type P)
           (exp_choice_cipher_type P) (exp_plain_of_choice_msg P)
           (exp_choice_cipher_of_cipher P) (exp_pub_key_of_party P)
           (adv_package Adv
              ∘ denote_game_shim (exp_rand_carrier_card P)
                  (exp_rand_of_carrier P) (exp_choice_msg_of_plain P)
                  (exp_choice_cipher_of_cipher P) (exp_pub_key_of_party P)
                  (exp_msg_of_index P) (exp_fallback_rand P)
                  (zero_hop_prefix l (game_of_trace (corrupted_view P))) l).
```

  IMPORTANT: derive the exact `denote_game_shim` argument list by `Check`-ing it at top
  level first (`rocq_query command="About denote_game_shim."`); the list above follows
  `denote_game`'s pattern at :657 and MUST be corrected against the real signature.
  Record-field accessor spellings (`P.(f)` vs `(f P)`) follow the file's own usage.
  Proof: keep `Hcnt` bridging `count_obs_hops` to `size (hop_sites …)`, rewrite it in
  the sum bound, then `eapply advantage_le` with the same goal-numbered `apply:` list.
- [ ] **Step 5.6: `dsdp_derived_game_advantage_le`** (dsdp_indcpa_advantage.v:63). New
  conclusion: two explicit `indcpa_epsilon` summands (shape of Step 5.4) at
  `game_of_trace (dsdp_alice_obs card_msg card_renc)` with reductions
  `A ∘ denote_game_shim renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
  pkey_of_party msg_of_idx rand0 (zero_hop_prefix 0 (game_of_trace (dsdp_alice_obs
  card_msg card_renc))) 0` (resp. `1`) — again correct the shim argument list against
  `About denote_game_shim`. Proof: keep the `pose P`/`pose Adv` packaging,
  `have H := dsdp_indcpa_secrecy_le Adv`, then expand the 2-element ordinal sum
  (`big_ord_recl`/`big_ord0`) — `move: H; by []` will no longer close it; probe
  the bigop expansion.
- [ ] **Step 5.7: `dsdp_alice_view_advantage_le`** (dsdp_main.v:128). Same two-summand
  conclusion at `dsdp_experiment`'s projections; proof via
  `dsdp_indcpa_secrecy_le Adv` + `dsdp_experiment_hops` + bigop expansion.
- [ ] **Step 5.8:** golf every re-proved lemma (`rocq:proof-golfer`), rocq-auditor
  Stage 2 (skip S996), build block, commit:

```bash
git commit -am "reduction-form phase 5: chain I restated over indcpa_epsilon reductions"
```

### Task 6: Chain II — leak_S ladder + headlines (spec Phase 6)

**Files:**
- Modify: `dumas2017dual/dsdp/indcpa_hopping/dsdp_indcpa_advantage.v:249–289, 294–321, 329–364, 405–441`
- Modify: `dumas2017dual/dsdp/simulation/dsdp_simulator.v` (`dsdp_advantage_sim_le`)
- Modify: `dumas2017dual/dsdp/dsdp_main.v:721–745, 747–782, 784–822, 843–892` (+ header comment lines for these)

- [ ] **Step 6.1:** restate `advantage_hop_leak_S`, `advantage_sum_ladder_le_leak_S`,
  `advantage_le_leak_S` exactly as Steps 5.1–5.3 with the `_leak_S` denotations and
  `denote_game_shim_leak_S` in the reduction terms (the Section
  `dsdp_game_code_leak_S` passes oracles as
  `oracle_real renc_card rand_of_renc msg_of_chmsg chcipher_of_cipher pkey_of_party`
  — the `indcpa_epsilon` arguments are the same section variables). The proofs mirror
  Task 5's; reuse the winning bigop chord found there.
- [ ] **Step 6.2:** `dsdp_derived_game_advantage_le_leak_S` (:405): two-summand
  conclusion with reductions
  `A ∘ denote_game_shim_leak_S … (zero_hop_prefix i G) i` for `i = 0, 1` at
  `G := game_of_trace_seeded dsdp_weight_names (dsdp_alice_obs_leak_S_seeded card_msg
  card_renc)` (check the shim's real argument list). Proof: keep `Hsz`, apply the
  restated `advantage_le_leak_S`, expand the sum.
- [ ] **Step 6.3:** `dsdp_advantage_sim_le` (dsdp_simulator.v): replace the Task-4
  constant bound with the reduction bound:

```coq
    (fun A : raw_package =>
       indcpa_epsilon … (A ∘ denote_game_shim_leak_S … 0)
     + indcpa_epsilon … (A ∘ denote_game_shim_leak_S … 1))
```

  (full argument lists as in Step 6.2). Proof: `advantage_sim_le_from_endpoint` with
  `game_le` discharged by the restated `dsdp_derived_game_advantage_le_leak_S`;
  factorization branch unchanged.
- [ ] **Step 6.4: dsdp_main.v headlines.** With this section's `guess_reduction`
  (let-bound at :701):
  - `dsdp_alice_guess_advantage_le` (:726): conclusion
    `AdvantageE real_game game guess_reduction <= indcpa_epsilon … (guess_reduction ∘
    denote_game_shim_leak_S … 0) + indcpa_epsilon … (guess_reduction ∘ … 1)`;
    proof body: same `eapply dsdp_derived_game_advantage_le_leak_S` chain.
  - `dsdp_alice_guess_V2_real_le` (:756): conclusion
    `guess_sdistr_success_real … <= card_msg%:R^-1 + (indcpa_epsilon … (guess_reduction
    ∘ … 0) + indcpa_epsilon … (guess_reduction ∘ … 1))`; the composition proof at
    :769–782 is ordered-field reasoning only — replace `2%:R * epsilon_cpa AHE` by the
    two-summand term throughout; `lerD2r` / `ler_norm` / `guess_advantage_eq` unchanged.
  - `dsdp_alice_unpredictability_entropy_ge` (:789): DELETE hypothesis
    `epsilon_cpa_ge0`; conclusion

```coq
  (log card_msg%:R
     - log (1 + card_msg%:R
              * (indcpa_epsilon … (guess_reduction ∘ denote_game_shim_leak_S … 0)
               + indcpa_epsilon … (guess_reduction ∘ denote_game_shim_leak_S … 1)))
     <= Hunp_leak_S …)%R
```

    Note the factor 2 disappears (two explicit summands replace `2 * eps`). The
    nonnegativity that `epsilon_cpa_ge0` provided is now provable:
    `indcpa_epsilon` unfolds to `AdvantageE` = a `normr`, so
    `addr_ge0 (normr_ge0 _) (normr_ge0 _)` after `rewrite /indcpa_epsilon /AdvantageE`
    (or SSProve's own nonnegativity lemma — `rocq_query
    command="Search AdvantageE (0 <= _)."` first). Rework the Task-3 inline log
    algebra for the new shape `m%:R^-1 + x` with
    `x := indcpa_epsilon … + indcpa_epsilon …` (no `2%:R *`):
    `x` is abstracted with `set x := (X in _ + X)` before the algebra, so the
    Task-3 chord applies verbatim with `2%:R * epsilon_cpa AHE` replaced by `x`.
  - `dsdp_alice_simulation_advantage_le` (:850): conclusion bound becomes the same
    two-summand term with the quantified `A` as reduction head
    (`A ∘ denote_game_shim_leak_S … i`); proof: triangle + `HY` unchanged, `HX` by the
    restated `dsdp_derived_game_advantage_le_leak_S`, close with `lra` (if `lra` balks
    at the opaque summands, `set e0 := …; set e1 := …` first).
- [ ] **Step 6.5:** golf every re-proved lemma, rocq-auditor Stage 2 (skip S996), build
  block, commit:

```bash
git commit -am "reduction-form phase 6: chain II + headlines restated over indcpa_epsilon"
```

### Task 7: Delete the axiom (spec Phase 7)

**Files:**
- Modify: `homomorphic_encryption/indcpa_ror.v` (delete :233–241 Parameter, :243–270 Axiom, `Check @enc_ind_cpa_real_or_zero.` :279)
- Modify: `homomorphic_encryption/idealized/idealized_indcpa.v:141–161`
- Modify: `dumas2017dual/blueprint/src/content.tex:476–477`

- [ ] **Step 7.1:** delete `Parameter epsilon_cpa`, `Axiom enc_ind_cpa_real_or_zero`,
  and the trailing `Check @enc_ind_cpa_real_or_zero.` with their comments from
  `indcpa_ror.v`.
- [ ] **Step 7.2:** in `idealized_indcpa.v` delete `epsilon_cpa_idealized_ge1`
  (:150–161) and restate `advantage_idealized_eq1` → `indcpa_epsilon_idealized_eq1`:

```coq
(** indcpa_epsilon_idealized_eq1 — the idealized scheme's [indcpa_epsilon] at
    [idealized_distinguisher] equals 1: [indcpa_epsilon] is not identically
    zero. *)
Lemma indcpa_epsilon_idealized_eq1 :
  indcpa_epsilon idealized_ahe_f2 'I_1 1 idealized_renc_card
    idealized_rand_of_renc 'bool 'bool idealized_msg_of_chmsg
    idealized_chcipher_of_cipher idealized_pkey_of_party
    idealized_distinguisher = 1%R.
Proof.
rewrite /indcpa_epsilon -/idealized_oracle_real -/idealized_oracle_zero.
by rewrite /AdvantageE pr_idealized_real pr_idealized_zero subr0 normr1.
Qed.
```

  (Probe: the `-/` folds may be unnecessary or need `rewrite /idealized_oracle_real` in
  the pr_ lemmas' direction instead; `pr_idealized_real`/`pr_idealized_zero` and
  `idealized_oracle_*` definitions stay.)
- [ ] **Step 7.3:** blueprint `content.tex:476–477`: the `\rocq{}` node cites both
  deleted declarations — restate the node to cite
  `infotheo.homomorphic_encryption.indcpa_ror.indcpa_epsilon` and rewrite the node
  body (:478–483) from "assumption bounding every adversary by $\epscpaof{E}$" to the
  definition of the advantage functional (`check_coverage.py` fails on dangling
  citations the moment the declarations disappear, so this edit belongs here).
- [ ] **Step 7.4:** confirm zero remaining references in built code:

```bash
grep -rn "epsilon_cpa\|enc_ind_cpa_real_or_zero" --include="*.v" . \
  | grep -v "legacy/\|\.scratch/\|probe_\|\.claude/\|indcpa_epsilon"
# expect: no output
```

- [ ] **Step 7.5:** golf the restated lemma, rocq-auditor Stage 2 on
  `idealized_indcpa.v` (skip S996; the deletions themselves are bypass-eligible but the
  restatement is not), build block, commit:

```bash
git commit -am "reduction-form phase 7: delete epsilon_cpa and the IND-CPA axiom"
```

### Task 8: Documentation sweep (spec Phase 8)

**Files:**
- Modify comments only: `idealized_indcpa.v:1–7, 37–42, 72–75, 81–84`;
  `indcpa_ror.v:1–24, 48–55`; `dsdp_game_code.v:871–884, 914–928, 959–972, 1056–1063`;
  `dsdp_game_derivation.v:5–6, 209, 683–690`; `dsdp_indcpa_advantage.v:1–12, 52–62,
  120–132, 245–248, 291–293, 323–328, 398–404`; `dsdp_simulator.v:273–278`;
  `dsdp_main.v:1–38, 121–127, 721–724, 747–755, 784–788, 843–849`
- Modify: `dumas2017dual/blueprint/src/content.tex` (12 `\epscpaof`),
  `security.tex` (remaining `\epscpaof`), `it_bound_bridge.tex` (1 + comments)

- [ ] **Step 8.1:** rewrite every stale comment naming `epsilon_cpa`, the axiom, the
  `2 * eps` bound shape, or pre-rename identifiers, to the reduction-form reading.
  Statement comments stay terse-mathematical (project rule): what the object IS, no
  status/meta narration.
- [ ] **Step 8.2:** blueprint prose: replace constant-bound formulas
  (`\le 2\,\epscpaof{E}`, `(n{+}1)\,\epscpaof{E}`, `|\sites(g)|\,\epscpaof{E}`,
  `1/m + 2\,\epscpaof{E}`, `\log(1+2m\,\epscpaof{E})`) with the reduction-form
  statements (advantage of the explicit reduction / sum over hop sites / `1/m +`
  two-reduction sum). Where `\epscpaof` survives as notation, redefine its gloss at
  `content.tex:28–32` as the adversary-indexed advantage function (it already reads
  "is a function $\epscpaof{\cdot}$" — align it with `indcpa_epsilon`). The
  negligibility reading becomes a cited sentence (StretchPRG.v:165 style), not a formal
  hypothesis. Build the blueprint with its own Makefile if present; at minimum
  `check_coverage.py` OK.
- [ ] **Step 8.3:** update `dsdp_main.v:1–38` header index to the final names and bound
  shapes (incl. removing the statdist line if any residue).
- [ ] **Step 8.4:** verify + commit:

```bash
# build block, then:
ROCQ_AUDIT_BYPASS=1 git commit -am "reduction-form phase 8: documentation and blueprint sweep"
```

### Task 9: Final verification

- [ ] **Step 9.1:** full-tree `make` from clean state
  (`make clean && make -j6`) under the local switch — no Error.
- [ ] **Step 9.2:** axiom hygiene: for each remaining `dsdp_main.v` headline
  (`dsdp_centropy_uniform`, `dsdp_centropy_uniform_n`,
  `US_n_compromised_leaks_secret`, `US_compromised_leaks_V2`, `bob_privacy_V1`,
  `charlie_privacy_V1`, `bob_privacy_V3`, `charlie_privacy_V2`,
  `dsdp_alice_view_advantage_le`, `dsdp_alice_guess_V2_zero_le`,
  `dsdp_alice_guess_advantage_le`, `dsdp_alice_guess_V2_real_le`,
  `dsdp_alice_unpredictability_entropy_ge`, `dsdp_alice_simulation_advantage_le`)
  run `rocq_assumptions name=<thm> file=dumas2017dual/dsdp/dsdp_main.v`. Assert: **no
  project declaration** in any output. Expected residual (upstream):
  `boolp.propositional_extensionality`, `boolp.functional_extensionality_dep`,
  `FunctionalExtensionality.functional_extensionality_dep`,
  `boolp.constructive_indefinite_description`, `SPropBase.ax_proof_irrel`, `Axioms.R`,
  `absord` / `unlock_absord`, `realsum.__admitted__interchange_psum`. Write the actual
  output to `dumas2017dual/notes/20260729-headline-assumptions-allowlist.md` and commit
  it (spec: commit the output, do not assert it in advance).
- [ ] **Step 9.3:** statement-identity guard: `git diff itp2026-dumas2017dual --` on
  `dsdp_main.v` and `dsdp_simulator.v` must show **no change** inside the statement of
  `dsdp_alice_guess_V2_zero_le` and `dsdp_simulator_factorization` (proof-term level:
  both still compile against unchanged statements; the diff hunks must not touch their
  statement lines).
- [ ] **Step 9.4:** `python3 dumas2017dual/blueprint/check_coverage.py` → OK.
- [ ] **Step 9.5:** commit the allowlist note:

```bash
git commit -am "reduction-form: headline assumptions allowlist"
```

---

## Self-review notes

- Spec coverage: Phases 1–8 map to Tasks 1–8; Verification section maps to Task 9 and
  the per-task build blocks; naming-audit renames all land in Task 1 except
  `advantage_idealized_eq1` (Task 7, tied to its restatement) and `log_id` (Task 3,
  deletion). Follow-ups (interchange_psum note, Paillier/DCR, thesis wording pass in
  the phd-thesis repo) stay recorded in the spec, not scheduled here.
- The `denote_game_shim(_leak_S)` argument lists in Tasks 5–6 are written from
  `denote_game`'s pattern and MUST be checked against `About` output before restating —
  flagged inline at each use.
- The `big_ord_recl`-vs-`recr` choice is deliberately left to live probing (spec flags
  it); both realignment identities are pre-derived in Step 5.2's notes.
