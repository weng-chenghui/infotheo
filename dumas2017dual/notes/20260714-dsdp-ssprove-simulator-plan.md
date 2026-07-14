# DSDP SSProve Simulator Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking. Rocq proving work is delegated to
> `rocq-prover` subagents per project convention; every prover step follows
> the mathcomp-skills goal-state-first loop (rocq_start → rocq_step_multi →
> rocq_check).

**Goal:** Mechanize the simulator notion and both game↔simulator conversion
directions for corrupted-Alice DSDP as an SSProve extension, ending in two
headline theorems in `dsdp_main.v`.

**Architecture:** Approach A from the spec
(`dumas2017dual/notes/20260714-dsdp-ssprove-simulator-design.md`, commits
f50e8967/5edb8fd7/9ebdf1d2): two generic SSProve-extension files (bounded
simulation security; statistical distance), one DSDP axis file (ideal +
simulator packages, the zero-game factorization, view law, losslessness),
then headline promotion into `dsdp_main.v`. Existing proven code is never
modified. All content promotes validated probe code from
`dumas2017dual/dsdp/simulation/probe_p{1,2,3,5,6}_*.v` — promote by COPYING,
never `Require Import` a probe file.

**Tech Stack:** Rocq (rocq c / make), mathcomp + mathcomp-analysis
(realsum/distr), SSProve 0.3.1 (Package, pkg_rhl, nominal/Pr), repo infra
(`smc/ssprove_ext_lossless.v`, `dsdp_game_code.v`,
`dsdp_indcpa_advantage.v`, `dsdp_convert.v`, `dsdp_guess_fiber.v`).

---

## Shared facts (read once)

**Compile command** (repo root `/Users/cheng-huiweng/Projects/coq/infotheo-itp`,
opam switch `/Users/cheng-huiweng/Projects/coq`), for any single file:

```bash
rocq c -R . infotheo -w -notation-overridden -w -ambiguous-paths \
  -w -notation-incompatible-format <path/to/file.v>
```

Expected: exit 0, only notation-overridden/incompatible-prefix warnings.

**Statement scope (locked decision B1/i):** every new theorem statement and
comment presents AVERAGE-CASE eps-privacy — honest inputs v2, v3 are sampled
in-game (uniform), Alice's inputs are the fixed seed slots. Never word a
statement or comment as the thesis' per-input (`forall x`) claim.

**Proof style:** mathcomp/ssreflect throughout (80-char lines, `by`/`exact:`
closers, bullets, meaningful hypothesis names — mathcomp-skills Reviewer
Checklist). Sole exception: vanilla `eapply` at `eq_rel_perf_ind`-family
entry points (ssreflect `apply:` delta-unfolds raw_package bodies and OOMs).

**Statement comments** follow the terse mathematical style (state what the
object IS; no status markers, no effort notes, no proof strategy in the
rendered comment).

**GATE PROCEDURE** — run before EVERY commit in this plan, on the files the
task touched:

1. `bash /Users/cheng-huiweng/.claude/skills/mathcomp-skills/scripts/audit-quick.sh <files>`
   — fix all mechanical findings.
2. Dispatch one `mathcomp-skills:mathcomp-style-auditor` agent per touched
   `.v` file (read-only); apply its punch list (skip only items on the
   documented `eapply` exception sites and validated-unsound patterns per
   playbook.md).
3. Dispatch an adversarial SSProve naming-audit agent (general-purpose,
   read-only): "For each NEW identifier in <files>, find the closest
   upstream SSProve precedent (grep
   /Users/cheng-huiweng/Projects/coq/_opam/lib/coq/user-contrib/SSProve)
   and judge conformance (e.g. `adv_equiv`, `Advantage_link`,
   `LosslessOp_uniform`, `Lossless_ret`, `Pr_fst`). Reject deviations with a
   proposed rename." Apply renames immediately (naming fixes are not
   deferrable).
4. `git commit` normally (NO `ROCQ_AUDIT_BYPASS`) — the precommit hook runs
   rocq-auditor Stage-2; fix findings before retrying.

**Axiom baseline:** `rocq_assumptions` (or `Print Assumptions` in a /tmp
file) on each task's main result must show ONLY: the boolp trio
(`propositional_extensionality`, `functional_extensionality_dep`,
`constructive_indefinite_description`), `Axioms.R`-related constants,
mathcomp-analysis' admitted `interchange_psum` (inherited by everything
touching `psum`/`dlet`; upstream `Lossless_sample` carries it too), and — on
the game side only — `epsilon_cpa` / `enc_ind_cpa_real_or_zero`
(`homomorphic_encryption/indcpa_ror.v`, the one cryptographic assumption).
Anything else is a blocker.

---

### Task 1: `smc/ssprove_ext_statdist.v` — statistical distance layer

**Files:**
- Create: `smc/ssprove_ext_statdist.v`
- Modify: `_CoqProject` (insert `smc/ssprove_ext_statdist.v` directly after
  the line `smc/ssprove_ext_lossless.v`)
- Source to copy from: `dumas2017dual/dsdp/simulation/probe_p3_statdist.v`
  (303 lines, all Qed)

- [ ] **Step 1: Create the file by promoting the probe.** Copy the ENTIRE
  content of `probe_p3_statdist.v` into `smc/ssprove_ext_statdist.v`.
  Replace the probe's file-header comment with:

```coq
(** SSProve extension: statistical (total-variation) distance on [{distr T}].

    [statdist p q] is half the pointwise absolute-difference mass between
    two subdistributions.  For mass-1 laws, every boolean test's acceptance
    gap is bounded by [statdist] ([statdist_test_le]) and the strict
    optimal test [fun t => q t < p t] attains it exactly
    ([statdist_test_max]): the maximum distinguisher advantage equals the
    statistical distance. *)
```

  Keep every declaration and name as-is (inventory from the probe: the
  `statdist` definition, `statdist_ge0`, `statdist_sym`,
  `statdist_triangle`, `statdist_test_le`, `statdist_test_max`, the
  `psum_split` workhorse and the ~22 supporting lemmas, the `Dstar`
  local). Do NOT reorganize proofs — they are validated verbatim.

- [ ] **Step 2: Add the mass-1 necessity counterexample** (new code, audit
  finding m1) at the end of the file's main section, adapting the concrete
  types to the section's `{R : realType} {T : choiceType}` context
  instantiated at `T := nat`:

```coq
(** [statdist_test_le] requires mass one: with the point mass [dunit 0%N]
    against the null subdistribution, the always-true test opens gap [1]
    while the distance is [1/2]. *)
Example statdist_test_le_needs_mass1 (R : realType) :
  statdist (dunit (0%N : nat) : {distr nat / R}) dnull
    < `|pr (dunit (0%N : nat) : {distr nat / R}) predT - pr dnull predT|.
```

  Prover note: `pr` here is the acceptance-probability primitive the probe
  chose (`distr.pr`, `pr mu E = psum (fun x => (E x)%:R * mu x)`); expect
  the proof from `psum`-of-`dunit`/`dnull` facts (`Search psum dunit`,
  `Search dnull` in `from_state`; the probe file's helper lemmas already
  compute such masses). If the exact statement form fights the scopes, the
  equivalent `1/2 < 1` phrasing after two `have ->:` mass computations is
  acceptable; the Example must remain a genuine strict-inequality witness.

- [ ] **Step 3: Compile.**

```bash
rocq c -R . infotheo -w -notation-overridden -w -ambiguous-paths \
  -w -notation-incompatible-format smc/ssprove_ext_statdist.v
```

  Expected: exit 0 (~3-5 s, matching the probe's 3.18 s).

- [ ] **Step 4: Axiom check** on `statdist_test_max` and the new Example
  against the Axiom baseline (boolp trio + `interchange_psum` family only —
  this file must NOT depend on `epsilon_cpa`).

- [ ] **Step 5: Add to `_CoqProject`** after `smc/ssprove_ext_lossless.v`,
  then confirm the file still compiles under the project namespace (same
  command as Step 3).

- [ ] **Step 6: GATE PROCEDURE + commit.**

```bash
git add smc/ssprove_ext_statdist.v _CoqProject
git commit -m "smc: ssprove_ext_statdist — statistical distance with the
max-advantage identity (statdist_test_le / statdist_test_max, mass-1)"
```

---

### Task 2: `smc/ssprove_ext_simulator.v` — bounded simulation security

**Files:**
- Create: `smc/ssprove_ext_simulator.v`
- Modify: `_CoqProject` (insert after `smc/ssprove_ext_statdist.v`)
- Source: `dumas2017dual/dsdp/simulation/probe_p5_skeletons.v` lines 40-93
  (Part A, all Qed)

- [ ] **Step 1: Create the file.** Import header: copy the probe's header
  (lines 10-38) but DROP the DSDP-specific `Require Import` lines
  (`homomorphic_encryption` through `dsdp_guess_fiber`) — this generic file
  imports only mathcomp, SSProve (`Package pkg_composition Pr`),
  extructures, and needs no repo modules. Keep the
  `Notation R := SSProve.Crypt.Axioms.R.` pin. File-header comment:

```coq
(** SSProve extension: bounded simulation security.

    [adv_sim_le E adm Real Ideal Sim eps] — every valid adversary in the
    admissible class [adm] distinguishes [Real] from [Sim ∘ Ideal] with
    advantage at most [eps].  [Simulates_from_endpoint] converts a
    real-versus-endpoint game bound plus a perfect endpoint factorization
    into bounded simulation security; [Simulates_reduction] transports the
    bound to any common left context [T]. *)
```

  Then the three declarations verbatim from the probe (complete code):

```coq
Section bounded_simulation.

Definition adv_sim_le (E : Interface) (adm : Locations -> raw_package -> Prop)
    (Real Ideal Sim : raw_package) (eps : R) : Prop :=
  forall (LA : Locations) (A : raw_package),
    ValidPackage LA E A_export A -> adm LA A ->
    AdvantageE Real (Sim ∘ Ideal) A <= eps.

Lemma Simulates_from_endpoint
    (E : Interface) (adm : Locations -> raw_package -> Prop)
    (Real Endpoint Ideal Sim : raw_package) (eps : R)
    (Hgame : forall (LA : Locations) (A : raw_package),
       ValidPackage LA E A_export A -> adm LA A ->
       AdvantageE Real Endpoint A <= eps)
    (Hsim : forall (LA : Locations) (A : raw_package),
       ValidPackage LA E A_export A -> adm LA A ->
       AdvantageE Endpoint (Sim ∘ Ideal) A = 0) :
  adv_sim_le E adm Real Ideal Sim eps.
Proof.
move=> LA A A_valid A_adm.
apply: (le_trans (Advantage_triangle Real (Sim ∘ Ideal) Endpoint A)).
rewrite (Hsim LA A A_valid A_adm) addr0.
exact: (Hgame LA A A_valid A_adm).
Qed.

Lemma Simulates_reduction
    (E : Interface) (adm : Locations -> raw_package -> Prop)
    (Real Ideal Sim : raw_package) (eps : R)
    (Hsim : adv_sim_le E adm Real Ideal Sim eps)
    (T A : raw_package) (LAT : Locations)
    (AT_valid : ValidPackage LAT E A_export (A ∘ T))
    (AT_adm : adm LAT (A ∘ T)) :
  AdvantageE (T ∘ Real) (T ∘ Sim ∘ Ideal) A <= eps.
Proof.
rewrite -Advantage_link.
exact: (Hsim LAT (A ∘ T) AT_valid AT_adm).
Qed.

End bounded_simulation.
```

  Add terse statement comments above each declaration (the probe's comments
  are close; strip any meta wording).

- [ ] **Step 2: Compile** (same command shape as Task 1 Step 3, on
  `smc/ssprove_ext_simulator.v`). Expected: exit 0. If `le_trans` is out of
  scope with the trimmed imports, add
  `Import Order.POrderTheory.` (present in the probe header).

- [ ] **Step 3: Axiom check** on both lemmas (boolp trio + Axioms.R only).

- [ ] **Step 4: `_CoqProject` entry + recompile.**

- [ ] **Step 5: GATE PROCEDURE + commit.**

```bash
git add smc/ssprove_ext_simulator.v _CoqProject
git commit -m "smc: ssprove_ext_simulator — bounded simulation security
(adv_sim_le) with endpoint and reduction conversion lemmas"
```

---

### Task 3: `smc/ssprove_ext_lossless_heap.v` — heap-parametric losslessness

**Files:**
- Create: `smc/ssprove_ext_lossless_heap.v`
- Modify: `_CoqProject` (insert after `smc/ssprove_ext_simulator.v`)
- Source: `dumas2017dual/dsdp/simulation/probe_p6_lossless_heap.v` lines
  58-142 (Part A1, all Qed)

- [ ] **Step 1: Create the file** by copying Part A1 verbatim:
  `psum_dlet_const1`, `LosslessHeapCode`, `LosslessHeap_ret`,
  `LosslessHeap_sample`, `LosslessHeap_get`, `LosslessHeap_put`,
  `LosslessHeap_bind`, `LosslessHeap_if`, `LosslessHeap_Pr_fst`. Import
  header: copy the probe's (lines 20-56) but drop the DSDP `Require
  Import` lines (`homomorphic_encryption` through `dsdp_indcpa_advantage`)
  — keep `From mathcomp ... distr` (the `\dlet` notation lives there),
  `From SSProve.Crypt Require Import Package pkg_composition Pr pkg_rhl`,
  and `Require Import smc.ssprove_ext_lossless` (for `LosslessOp`
  compatibility). File-header comment:

```coq
(** SSProve extension: heap-parametric losslessness.

    [LosslessHeapCode c] — the joint output/heap subdistribution
    [Pr_code c h] has total mass one from every starting heap [h].  Closed
    under ret / sample / get / put / bind / if with no
    [ValidCode emptym] restriction, so stateful code is in scope;
    [LosslessHeap_Pr_fst] recovers SSProve's [Pr_fst]-based mass-1 form. *)
```

- [ ] **Step 2: Compile.** Expected: exit 0 (probe: 4.47 s with the DSDP
  imports; this trimmed file should be faster). If `Couplings.psum_SDistr_unit`
  or `summable_mlet` fail to resolve after the import trim, restore
  whichever SSProve module provided them (they are upstream:
  `Search psum SDistr_unit`, `Locate summable_mlet`).

- [ ] **Step 3: Axiom check** on `LosslessHeap_Pr_fst` (boolp trio +
  `interchange_psum` + Axioms.R — the probe confirmed this exact set).

- [ ] **Step 4: `_CoqProject` entry + recompile.**

- [ ] **Step 5: GATE PROCEDURE + commit.**

```bash
git add smc/ssprove_ext_lossless_heap.v _CoqProject
git commit -m "smc: ssprove_ext_lossless_heap — heap-parametric lossless
class closed under get/put/bind, with Pr_fst bridge"
```

---

### Task 4: `dumas2017dual/dsdp/simulation/dsdp_simulator.v` part 1 — packages

**Files:**
- Create: `dumas2017dual/dsdp/simulation/dsdp_simulator.v`
- Modify: `_CoqProject` (insert after
  `dumas2017dual/dsdp/indcpa_hopping/dsdp_guess_fiber.v` — check the exact
  neighbor line; it must come after every module it imports)
- Sources: probe_p6 lines 148-267 (sim_view_body section), probe_p1 lines
  96-130 (real ideal body), probe_p5 lines 99-201 (section context, ids,
  dsdp_adm)

- [ ] **Step 1: Create the file** with the import header of
  `probe_p1_factorization_pet.v` lines 23-59 (it is the union needed later
  for the factorization: includes `pkg_rhl`) PLUS
  `Require Import smc.ssprove_ext_simulator smc.ssprove_ext_lossless_heap.`
  and `Require Import dsdp_convert dsdp_guess_fiber.`
  Open a section cloning `dsdp_main.v` `Section dsdp_alice_guess`
  variables (dsdp_main.v:707-741) — at minimum:

```coq
Section dsdp_simulator.
Variables (AHE : AHEncType) (Renc : finType) (card_renc : nat)
  (renc_card : #|Renc| = card_renc) (rand_of_renc : Renc -> rand AHE)
  (t_msg t_cipher : choice_type)
  (chmsg_of_msg : plain AHE -> t_msg)
  (chcipher_of_cipher : cipher AHE -> t_cipher)
  (pkey_of_party : party_id -> pub_key AHE)
  (card_msg : nat) (msg_of_idx : 'I_card_msg -> plain AHE) (rand0 : rand AHE).
Variable seed : denv AHE.
Variable msg_of_chmsg : t_msg -> plain AHE.
Hypothesis chmsg_of_msgK : cancel chmsg_of_msg msg_of_chmsg.
Hypothesis card_renc_neq : card_renc != card_msg.
Hypothesis card_msg_pos : (0 < card_msg)%N.
Hypothesis card_renc_pos : (0 < card_renc)%N.

Local Notation "'msg'" := t_msg (in custom pack_type at level 2).
Local Notation "'ciphers'" := (cipher_list t_cipher)
  (in custom pack_type at level 2).
```

- [ ] **Step 2: Interface and ideal package** (probe_p6 ids + probe_p1 real
  body, ops renumbered to 4/2/3):

```coq
Definition id_ideal_run : nat := 4%N.

Definition I_dsdp_ideal : Interface :=
  [interface
     #val #[ id_ideal_run ] : 'unit → 'unit ;
     #val #[ id_v2_get    ] : 'unit → msg ;
     #val #[ id_Sout_get  ] : 'unit → msg ].

Definition dsdp_ideal_pkg : package [interface] I_dsdp_ideal :=
  [package (protocol_state t_msg) ;
    #def #[ id_ideal_run ] (_ : 'unit) : 'unit
    {
      x2 ← sample uniform card_msg ;;
      x3 ← sample uniform card_msg ;;
      let v2 := msg_of_idx x2 in
      let v3 := msg_of_idx x3 in
      let u1 := as_plain (de_val_nth seed 0) in
      let u2 := as_plain (de_val_nth seed 1) in
      let u3 := as_plain (de_val_nth seed 2) in
      let v1 := as_plain (de_val_nth seed 3) in
      #put (V_2_cell t_msg) := Some (chmsg_of_msg v2) ;;
      #put (Sout_cell t_msg) :=
        Some (chmsg_of_msg (u2 * v2 + u3 * v3 + u1 * v1)) ;;
      ret tt
    } ;
    #def #[ id_v2_get ] (_ : 'unit) : msg
    {
      stored ← get (V_2_cell t_msg) ;;
      match stored with
      | Some v => ret v
      | None   => ret (chmsg_of_msg (0%R : plain AHE))
      end
    } ;
    #def #[ id_Sout_get ] (_ : 'unit) : msg
    {
      stored ← get (Sout_cell t_msg) ;;
      match stored with
      | Some v => ret v
      | None   => ret (chmsg_of_msg (0%R : plain AHE))
      end
    }
  ].
```

  IMPORTANT: before finalizing the two `#put` values and the `None`
  fallbacks, read `denote_game_leak_S` / `denote_run`
  (`dsdp_game_code.v:521-560` and the `GC_put`/`GC_put_output`
  interpreter cases) and mirror the stored values and cell option-shape
  EXACTLY as the real denotation writes them — any mismatch surfaces in
  Task 5's factorization as an unprovable cell equality. Record what was
  checked in the statement comment of `dsdp_ideal_pkg`.

- [ ] **Step 3: `sim_view_body` + validity + simulator package** — copy
  probe_p6 lines 181-267 with ONE change: DROP the `get_S` parameter and
  its `_ ← get_S ;;` bind (the fabricated view provably reads no S — P2
  provenance; this keeps the code-linked RHS identical to P1's timed shape
  and strengthens the allowed-info witness):

```coq
Definition sim_view_body (run_ideal : raw_code 'unit) :
  raw_code (cipher_list t_cipher) :=
  _ ← run_ideal ;;
  x_r2  ← sample uniform card_msg ;;
  x_r3  ← sample uniform card_msg ;;
  x_ra1 ← sample uniform card_renc ;;
  x_ra2 ← sample uniform card_renc ;;
  x_c2  ← sample uniform card_renc ;;
  x_c3  ← sample uniform card_renc ;;
  let r2  := msg_of_idx x_r2 in
  let r3  := msg_of_idx x_r3 in
  let ra1 := rand_of_renc (@sample_to_renc _ _ renc_card x_ra1) in
  let ra2 := rand_of_renc (@sample_to_renc _ _ renc_card x_ra2) in
  let pk1 := pkey_of_party (nat_to_party_id 1) in
  let pk2 := pkey_of_party (nat_to_party_id 2) in
  let c2c := enc pk1 (0%R : plain AHE)
                 (rand_of_renc (@sample_to_renc _ _ renc_card x_c2)) in
  let c3c := enc pk2 (0%R : plain AHE)
                 (rand_of_renc (@sample_to_renc _ _ renc_card x_c3)) in
  let u2 := as_plain (de_val_nth seed 1) in
  let u3 := as_plain (de_val_nth seed 2) in
  let a1c := Emul (Epow c2c u2) (enc pk1 r2 ra1) in
  let a2c := Emul (Epow c3c u3) (enc pk2 r3 ra2) in
  ret ([:: chcipher_of_cipher a1c; chcipher_of_cipher a2c;
           chcipher_of_cipher c2c; chcipher_of_cipher c3c ]
       : cipher_list t_cipher).

Lemma valid_sim_view_body (L : Locations) (I : Interface)
    (run_ideal : raw_code 'unit)
    (H1 : ValidCode L I run_ideal) :
    ValidCode L I (sim_view_body run_ideal).
Proof.
rewrite /sim_view_body.
apply: valid_bind.
move=> _; ssprove_valid.
Qed.

#[local] Hint Extern 2 (ValidCode ?L ?I (sim_view_body ?r)) =>
  eapply valid_sim_view_body
  : typeclass_instances ssprove_valid_db.

Definition dsdp_simulator_pkg :
  package I_dsdp_ideal (game_iface_leak_S t_msg t_cipher) :=
  [package emptym ;
    #def #[ id_game_run ] (_ : 'unit) : ciphers
    {
      sim_view_body
        (#import {sig #[ id_ideal_run ] : 'unit → 'unit } as call_ideal ;;
         r ← call_ideal Datatypes.tt ;; ret r)
    } ;
    #def #[ id_v2_get ] (_ : 'unit) : msg
    {
      #import {sig #[ id_v2_get ] : 'unit → msg } as call_v2 ;;
      x ← call_v2 Datatypes.tt ;;
      ret x
    } ;
    #def #[ id_Sout_get ] (_ : 'unit) : msg
    {
      #import {sig #[ id_Sout_get ] : 'unit → msg } as call_Sout ;;
      x ← call_Sout Datatypes.tt ;;
      ret x
    }
  ].
```

  Known idioms (P6-validated, keep them): the `Hint Extern` is required
  because the resolver cannot descend the opaque `sim_view_body` head
  (`#[export]` is illegal inside a Section — keep `#[local]` and
  re-evaluate at `End` time whether the hint must be restated); call
  arguments stay in bind-wrapped `x ← c tt ;; ret x` form (a bare `c tt`
  leaves a beta-redex the `valid_opr` hint cannot match).

- [ ] **Step 4: `dsdp_adm`** (probe_p5 lines 196-201, verbatim):

```coq
Definition dsdp_adm (LA : Locations) (A : raw_package) : Prop :=
  fseparate LA (protocol_state t_msg) /\
  fseparate LA (locs (oracle_real_pkg renc_card rand_of_renc msg_of_chmsg
                        chcipher_of_cipher pkey_of_party)) /\
  fseparate LA (locs (oracle_zero_pkg renc_card rand_of_renc t_msg
                        chcipher_of_cipher pkey_of_party)).
```

- [ ] **Step 5: Compile; `_CoqProject`; GATE PROCEDURE + commit.**

```bash
git add dumas2017dual/dsdp/simulation/dsdp_simulator.v _CoqProject
git commit -m "dsdp simulation: ideal functionality and simulator packages
with type-level allowed-info witness (sim_view_body)"
```

---

### Task 5: `dsdp_simulator.v` part 2 — the factorization (LARGEST-RISK TASK)

**Files:**
- Modify: `dumas2017dual/dsdp/simulation/dsdp_simulator.v` (same section)

- [ ] **Step 1: State it Admitted and compile** (statement validated by P5;
  the composition MUST stay inline — an opaque alias breaks `valid_link`
  instance resolution):

```coq
Lemma dsdp_simulator_factorization :
  zero_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
    pkey_of_party msg_of_idx rand0 seed
  ≈₀ dsdp_simulator_pkg ∘ dsdp_ideal_pkg.
Proof.
Admitted.
```

  Compile: exit 0 expected (P5 typechecked this exact shape).

- [ ] **Step 2: Prove it, following the P1 recipe.** Delegate to a
  rocq-prover agent with this exact playbook (per-command budget ~5 min /
  8 GB RSS; kill the rocqworker process GROUP on runaway):

  1. Entry: `eapply eq_rel_perf_ind_eq.` (vanilla eapply; ~15 ms; leaves
     one `eq_up_to_inv` goal, instances auto-resolve).
  2. `simplify_eq_rel m.` — budget ~2 min / ~6 GB, produces three oracle
     goals (run / v2_get / Sout_get).
  3. Run-oracle goal FIRST: `rewrite !eqxx.` then
     `rewrite !(negbTE card_renc_neq).` (possibly interleaved; the four
     `card_msg == card_msg` and two `card_renc == card_msg` dispatch guards
     must all reduce BEFORE any sync — P1 measured the collapse at two
     orders of magnitude).
  4. `ssprove_sync_eq` twice (honest inputs v2, v3 — both sides sample
     them first).
  5. Re-align the ideal's early cell writes with the monolithic game's
     write positions: `ssprove_swap_rhs 0%N`, `ssprove_swap_rhs 1%N`,
     `ssprove_swap_lhs 0%N` fired in P1 at the first mismatch (LHS head =
     mask sample, RHS head = #put); continue interleaving
     `ssprove_sync_eq` (masks r2, r3; randomnesses ra1, ra2; two hop
     samples) with `ssprove_swap_rhs`/`ssprove_swap_lhs`/`ssprove_swap_seq_*`
     until both `#put`s align. The UNVALIDATED TAIL starts here.
  6. Cell-write equalities: the LHS (denoted) Sout value re-embeds the
     denotation env at each `de_val_nth` read; the RHS is the ideal's
     literal `u2 * v2 + u3 * v3 + u1 * v1`. Look for `de_val_nth`/
     `push_val` simplification lemmas in `dsdp_game_code.v`
     (`rocq_query Search de_val_nth`); expect `cbn`/`rewrite` normalization
     to close the value equality. Same for the V_2 write and the final
     `r_ret`.
  7. v2_get / Sout_get oracle goals: both sides reduce to the same
     `get`-and-match code (the simulator pass-through code-links to the
     ideal's get); `ssprove_code_simpl` + `ssprove_sync_eq` +
     `r_ret`/`by []`.

- [ ] **Step 3: FALLBACK TRIGGER.** If step 6 (cell-value equality) or the
  tail swaps stall for more than ~2 focused hours: STOP the direct route.
  Restate the run-oracle equivalence as a standalone lemma over a symbolic
  `gc : game_code` with shape hypotheses (the `hop_equiv_real_leak_S` /
  `hop_equiv_zero_leak_S` pattern, `dsdp_indcpa_advantage.v:198-246`, keeps
  `denote_run` un-unfolded and fast), instantiate at
  `all_zero (game_of_trace_seeded …)`, and rebuild the `≈₀` from per-oracle
  lemmas. If THAT also stalls, mark the task blocked and report to the user
  — do not switch strategy further (strategy-switch rule).

- [ ] **Step 4: Verify Qed + axioms** (`rocq_check` proof_finished is
  sufficient; axiom set per baseline — the factorization leg itself must
  NOT pull in `epsilon_cpa`).

- [ ] **Step 5: GATE PROCEDURE + commit.**

```bash
git add dumas2017dual/dsdp/simulation/dsdp_simulator.v
git commit -m "dsdp simulation: zero-game factorization — the all-zero
endpoint is the simulator composed with the ideal functionality"
```

---

### Task 6: `dsdp_simulator.v` part 3 — simulation security, view law, mass-1

**Files:**
- Modify: `dumas2017dual/dsdp/simulation/dsdp_simulator.v` (same section)

- [ ] **Step 1: `dsdp_simulation_secure`** (probe_p5 lines 207-230 shape;
  complete code, adjusted to this file's context — the factorization
  application takes the adversary's validity + the `protocol_state`
  separation, P5-verified):

```coq
Lemma dsdp_simulation_secure
    (cipher_of_chcipher : t_cipher -> cipher AHE)
    (chcipher_of_cipherK : cancel chcipher_of_cipher cipher_of_chcipher) :
  adv_sim_le (game_iface_leak_S t_msg t_cipher) dsdp_adm
    (real_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
       pkey_of_party msg_of_idx rand0 seed)
    dsdp_ideal_pkg dsdp_simulator_pkg
    (2%:R * epsilon_cpa).
Proof.
apply: (Simulates_from_endpoint
  (Endpoint := zero_game_leak_S renc_card rand_of_renc chmsg_of_msg
     chcipher_of_cipher pkey_of_party msg_of_idx rand0 seed)).
- move=> LA A A_valid [Hstate [Hore Hoze]].
  eapply dsdp_advantage_derived_leak_S.
  + exact: chcipher_of_cipherK.
  + exact: chmsg_of_msgK.
  + exact: A_valid.
  + exact: Hstate.
  + exact: Hore.
  + exact: Hoze.
- move=> LA A A_valid [Hstate _].
  apply: (dsdp_simulator_factorization A_valid Hstate).
  exact: Hstate.
Qed.
```

  (The exact argument plumbing of the second branch depends on how the
  Qed'd factorization's `adv_equiv` unfolds; P5's compiled version is the
  reference. Adjust mechanically, do not restructure.)

- [ ] **Step 2: View-dumper layer** — copy probe_p5 Part C (lines 263-303)
  verbatim: `view_dump_challenger`, `view_op`, `view_dump_resolved`,
  `test_adversary`. Then PROVE `view_dump_resolve_eq` (P5 statement, lines
  308-313, currently Admitted there): clone the `guess_resolve_eq` proof
  pattern (`dsdp_guess_fiber.v` — `rewrite /resolve … mkfmapE …
  coerce_kleisliE`, `resolve_link`, `code_link_bind`), then `Pr_fst_map`
  (`dsdp_convert.v:109`). Statement (complete, from P5):

```coq
Lemma view_dump_resolve_eq (G : raw_package)
    (D : (cipher_list t_cipher * t_msg)%type -> bool) :
  Pr_fst (resolve (test_adversary D ∘ G) RUN Datatypes.tt)
  = distr.dmargin (fun p => (D p : 'bool)) (Pr_fst (view_dump_resolved G)).
```

- [ ] **Step 3: Losslessness** — copy from probe_p6 lines 289-325:
  `gc_sample_cards` (Fixpoint) and `denote_run_lossless_heap` (Qed,
  verbatim — it now cites Task 3's promoted `LosslessHeap_*` names).

- [ ] **Step 4: BOUNDED attempt (≤ 2 focused hours) at the concrete
  reduction** — the one open P6 step:

```coq
Lemma gc_sample_cards_all_zero :
  gc_sample_cards
    (all_zero (game_of_trace_seeded dsdp_weight_names
       (dsdp_alice_obs_leak_S_seeded card_msg card_renc))) = true.
```

  Route: NOT `vm_compute` (stuck on abstract-nat guards, P6-measured);
  instead `cbn [game_of_trace_seeded game_of_trace all_zero
  zero_hop_prefix …]`-style controlled unfolding plus per-sample
  `rewrite eqxx orbT /=` — the code has exactly 4 `card_msg` and 2
  `card_renc` samples (P2). If it lands: prove `view_zero_mass1` (and the
  `real_game` analogue) by the resolve-reduction plumbing
  (`dsdp_guess_fiber.v`'s `resolve game (id_game_run,_) tt = drun seed gc`
  precedent) + `denote_run_lossless_heap` + `LosslessHeap_get/_ret` for the
  Sout tail + `LosslessHeap_Pr_fst`. If it does NOT land within budget:
  delete the attempt and declare the two mass-1 facts as section
  Hypotheses named `view_real_lossless` / `view_zero_lossless` (the
  `guess_lossless` precedent, `dsdp_main.v:721-735`), each with a statement
  comment citing `denote_run_lossless_heap` as the machine-supported core.
  Either outcome is per the locked M1 decision.

- [ ] **Step 5: Compile, axiom check, GATE PROCEDURE + commit.**

```bash
git add dumas2017dual/dsdp/simulation/dsdp_simulator.v
git commit -m "dsdp simulation: bounded simulation security, view law with
resolution lemma, and mass-1 discharge"
```

---

### Task 7: `dsdp_main.v` headlines

**Files:**
- Modify: `dumas2017dual/dsdp/dsdp_main.v` (append a new Section after
  `dsdp_alice_guess`, extend the header comment lines 1-30 and the
  `Require Import` block line 52)

- [ ] **Step 1: Imports + section.** Add `dsdp_simulator` to the Require
  Import line that already pulls `dsdp_indcpa_advantage dsdp_convert
  dsdp_guess_fiber`, and `smc.ssprove_ext_simulator
  smc.ssprove_ext_statdist smc.ssprove_ext_lossless_heap` next to
  `smc.ssprove_ext_lossless`. Open `Section dsdp_alice_simulation` cloning
  the same context as Task 4 Step 1 (full clone per the headline
  convention: apex sections re-declare their variables).

- [ ] **Step 2: Headline 1 — full proof body** (average-case wording in
  the comment; the body inlines the triangle derivation, consuming the two
  axis engines — no thin wrapper):

```coq
(* dsdp_alice_simulation_secure — bounded simulation security of the
   output-exposing corrupted-Alice game: every admissible adversary
   distinguishes the real game from the simulator composed with the ideal
   functionality with advantage at most [2 * epsilon_cpa].  Honest inputs
   are sampled uniformly in-game (average-case reading); Alice's inputs are
   the fixed seed slots.  [3-party] *)
Theorem dsdp_alice_simulation_secure
    (cipher_of_chcipher : t_cipher -> cipher AHE)
    (chcipher_of_cipherK : cancel chcipher_of_cipher cipher_of_chcipher)
    (LA : Locations) (A : raw_package)
    (A_valid : ValidPackage LA (game_iface_leak_S t_msg t_cipher) A_export A)
    (A_disj_state : fseparate LA (protocol_state t_msg))
    (A_disj_ore : fseparate LA
       (locs (oracle_real_pkg renc_card rand_of_renc msg_of_chmsg
                chcipher_of_cipher pkey_of_party)))
    (A_disj_oze : fseparate LA
       (locs (oracle_zero_pkg renc_card rand_of_renc t_msg
                chcipher_of_cipher pkey_of_party))) :
  AdvantageE
    (real_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
       pkey_of_party msg_of_idx rand0 seed)
    (dsdp_simulator_pkg ∘ dsdp_ideal_pkg)
    A <= 2%:R * epsilon_cpa.
Proof.
apply: (le_trans (Advantage_triangle _ _
  (zero_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
     pkey_of_party msg_of_idx rand0 seed) A)).
have Hfact : AdvantageE
    (zero_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
       pkey_of_party msg_of_idx rand0 seed)
    (dsdp_simulator_pkg ∘ dsdp_ideal_pkg) A = 0.
  by apply: (dsdp_simulator_factorization A_valid); exact: A_disj_state.
rewrite Hfact addr0.
by eapply dsdp_advantage_derived_leak_S; eauto.
Qed.
```

  (Exact factorization-application plumbing follows Task 5's Qed'd shape;
  keep the structure — triangle, factorization-is-zero, ladder bound.)

- [ ] **Step 3: Headline 2 — the distance form.** Statement (with the
  Task 6 Step 4 outcome deciding hypotheses vs discharged):

```coq
(* dsdp_alice_view_statdist_le — the statistical distance between the real
   and the simulated (cipher view, S) laws is at most [2 * epsilon_cpa]:
   the optimal test attains the distance ([statdist_test_max]) and is one
   admissible adversary of the simulation bound.  Average-case reading:
   honest inputs uniform in-game.  [3-party] *)
Theorem dsdp_alice_view_statdist_le
    (cipher_of_chcipher : t_cipher -> cipher AHE)
    (chcipher_of_cipherK : cancel chcipher_of_cipher cipher_of_chcipher)
    (Hmass_real : psum (distr.mu (Pr_fst (view_dump_resolved
       (real_game_leak_S renc_card rand_of_renc chmsg_of_msg
          chcipher_of_cipher pkey_of_party msg_of_idx rand0 seed)))) = 1)
    (Hmass_ideal : psum (distr.mu (Pr_fst (view_dump_resolved
       (dsdp_simulator_pkg ∘ dsdp_ideal_pkg)))) = 1) :
  statdist
    (Pr_fst (view_dump_resolved
       (real_game_leak_S renc_card rand_of_renc chmsg_of_msg
          chcipher_of_cipher pkey_of_party msg_of_idx rand0 seed)))
    (Pr_fst (view_dump_resolved (dsdp_simulator_pkg ∘ dsdp_ideal_pkg)))
    <= 2%:R * epsilon_cpa.
```

  (If Task 6 Step 4 discharged the mass-1 facts, cite them instead of
  taking `Hmass_*` hypotheses.) Proof skeleton the prover follows:
  `rewrite -(statdist_test_max Hmass_real Hmass_ideal)` exposes the optimal
  test `D*`; `view_dump_resolve_eq` + `distr.pr_dmargin` + `Pr_Pr_fst`
  rewrite each `pr … D*` into `Pr (test_adversary D* ∘ G) true`; the
  difference is `<=` its absolute value = `AdvantageE … (test_adversary D*)`
  (`ler_norm`), bounded by headline 1 — `test_adversary D*` has `emptym`
  locations, so all three `dsdp_adm` separations hold by
  `fseparate`-with-empty (`Search fseparate emptym`; the same fact P5's
  class-inhabitation check used).

- [ ] **Step 4: Header block.** Extend the `dsdp_main.v` header comment
  (after the corrupted-Alice guessing-triangle block, line 30) with:

```
   Simulation-based security (simulation axis)  [3-party]
     dsdp_alice_simulation_secure : AdvantageE real (Sim ∘ Ideal)
       <= 2 * epsilon_cpa (average-case: honest inputs uniform in-game;
       engine: dsdp_advantage_derived_leak_S + dsdp_simulator_factorization)
     dsdp_alice_view_statdist_le : statdist(real view law, simulated view
       law) <= 2 * epsilon_cpa (optimal-test conversion, statdist_test_max)
```

- [ ] **Step 5: Compile `dsdp_main.v`; axiom check both headlines**
  (baseline + `epsilon_cpa`/`enc_ind_cpa_real_or_zero` expected here).

- [ ] **Step 6: GATE PROCEDURE — plus gate 4 (vacuity/statement check).**
  Dispatch an adversarial statement-audit agent: English-statement match
  against the spec's B1 scope note (statements must read as AVERAGE-CASE;
  a per-input reading is a wording bug), variable tracing
  (`epsilon_cpa`, `card_msg`, seed slots), vacuity anchors (class
  inhabited; factorization falsifiable), and parallel-track check against
  the header inventory. Fix findings, then commit.

```bash
git add dumas2017dual/dsdp/dsdp_main.v
git commit -m "dsdp main: simulation-based security headlines — bounded
simulation security and view-law statistical distance (average-case)"
```

---

### Task 8: Full-build verification + memo close-out

**Files:**
- Modify: `dumas2017dual/notes/20260714-dsdp-ssprove-simulator-design.md`
  (status header only)

- [ ] **Step 1: Full project build** with the real build system (never a
  permissive ad-hoc invocation): regenerate if needed
  (`coq_makefile -f _CoqProject -o Makefile.coq` — only if the repo's
  Makefile expects it; check `ls Makefile*` and mirror how the repo
  currently builds) and run the project's standard `make` target.
  Expected: full build passes including every pre-existing file.

- [ ] **Step 2: Memo status update** — flip the memo's Status header to
  "implemented through dsdp_main.v headlines (commits …)"; record the
  `sim_view_body` one-parameter refinement (get_S dropped: view needs no S,
  P2 provenance) and the Task 6 Step 4 outcome (mass-1 discharged or
  hypothesized). Nothing else in the memo changes.

- [ ] **Step 3: Commit** (docs-only: `ROCQ_AUDIT_BYPASS=1` applies).

```bash
git add dumas2017dual/notes/20260714-dsdp-ssprove-simulator-design.md
ROCQ_AUDIT_BYPASS=1 git commit -m "dsdp notes: simulator design memo —
implementation complete, record sim_view_body refinement and mass-1 outcome"
```

- [ ] **Step 4: Report** the final theorem names, axiom inventories, and
  the mass-1 outcome to the user. The thesis-chapter follow-up (hedge
  rewording per the B1 scope note and the m5 marginal note) is explicitly
  OUT OF SCOPE of this plan — offer it as the next task.

---

## Self-review notes (spec coverage)

- Spec Layer 1 (adv_sim_le + conversions) → Task 2. Layer 2 (statdist +
  max-advantage) → Task 1. Heap-parametric losslessness (M1) → Tasks 3, 6.
  Packages + witness (M2) → Task 4. Factorization + P1 recipe + fallback
  (M3) → Task 5. Headlines + B1 wording + gate 4 → Task 7. Build + memo →
  Task 8. Probe files stay untracked (decision 4) — no task touches them.
- Names used consistently: `adv_sim_le`, `Simulates_from_endpoint`,
  `Simulates_reduction` (Tasks 2→6→7); `statdist`, `statdist_test_le`,
  `statdist_test_max` (Tasks 1→7); `LosslessHeapCode`, `LosslessHeap_*`
  (Tasks 3→6); `id_ideal_run`, `I_dsdp_ideal`, `dsdp_ideal_pkg`,
  `dsdp_simulator_pkg`, `sim_view_body`, `valid_sim_view_body`, `dsdp_adm`
  (Tasks 4→5→6→7); `dsdp_simulator_factorization` (Tasks 5→6→7);
  `view_dump_challenger`, `view_op`, `view_dump_resolved`,
  `test_adversary`, `view_dump_resolve_eq`, `gc_sample_cards`,
  `denote_run_lossless_heap` (Tasks 6→7). Final names remain subject to
  the per-commit naming gate; renames propagate forward at the commit where
  they happen.
- Known deliberate deviation from probes: `sim_view_body` drops the unused
  `get_S` parameter (Task 4 Step 3 rationale; memo updated in Task 8).
