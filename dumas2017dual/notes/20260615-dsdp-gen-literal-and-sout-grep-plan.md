# dsdp_game_gen_literal.v + Sout greppability — Implementation Plan

> STATUS: COMPLETE (2026-06-15). Commit A = `c7ae148` (Sout-stem rename, audit-bypassed mechanical). Commit B = `ff3d154` (new file + gen_literal_zeroE/realE + gc_real_eq, full audit passed with ROCQ_AUDIT_TOKEN_CAP=720000). Full project build green; `Print Assumptions` clean (no Admitted, no new axioms).

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a permanent, abstract mid-point lemma certifying that a hand-written legible SSProve program (with the scalar-product output S visible) equals the auto-derived denotation for both the real and all-zero output-exposing endpoints; and unify every leaked-output identifier onto a single greppable `Sout` stem.

**Architecture:** Two atomic commits. Commit A is a mechanical cross-file rename to the `Sout` stem (4 files). Commit B adds a standalone file `dsdp_game_gen_literal.v` that re-establishes its own `denote_run` reflection scaffolding (no surgery on the fragile fiber file) and proves `gen_literal_zero = denote_run seed gc` and `gen_literal_real = denote_run seed gc_real`.

**Tech Stack:** Rocq/Coq, MathComp, SSProve, Infotheo; verification by `rocq_check` and the project Makefile; audit by rocq-auditor Stage-2.

**Working dir:** `/Users/cheng-huiweng/Projects/coq/infotheo-itp/dumas2017dual/dsdp`

---

## File structure

- **Modify (rename):** `dsdp_game_code.v`, `dsdp_game_symbolic.v`, `dsdp_indcpa_security.v`, `dsdp_security_indcpa_fiber.v` — the `Sout` stem.
- **Create:** `dsdp_game_gen_literal.v` — the legible programs and the two mid-point lemmas.
- **Modify:** `_CoqProject` (add the new file), `dsdp_security_indcpa_fiber.v` (one cross-reference comment at `gc`).
- **Delete:** `scratch_print_gen.v` (subsumed by `gen_literal_real`).

---

## Task 1: Cross-file `Sout`-stem rename (Commit A)

**Files:**
- Modify: `dsdp_game_code.v` (S_output_cell ×12, id_s_get ×10, denote_s_get_body ×5)
- Modify: `dsdp_game_symbolic.v` (S_output_cell ×1)
- Modify: `dsdp_indcpa_security.v` (id_s_get ×7, denote_s_get_body ×2)
- Modify: `dsdp_security_indcpa_fiber.v` (S_output_cell ×13, id_s_get ×11, denote_s_get_body ×16, binder `s` consume/read sites)

- [ ] **Step 1: Rename the three definition identifiers (word-boundary, global).**

These three are unique identifiers; a word-boundary substitution across the four files is safe.

```bash
cd /Users/cheng-huiweng/Projects/coq/infotheo-itp/dumas2017dual/dsdp
for f in dsdp_game_code.v dsdp_game_symbolic.v dsdp_indcpa_security.v dsdp_security_indcpa_fiber.v; do
  perl -pi -e 's/\bS_output_cell\b/Sout_cell/g; s/\bid_s_get\b/id_Sout_get/g; s/\bdenote_s_get_body\b/denote_Sout_get_body/g;' "$f"
done
```

- [ ] **Step 2: Add the `S_cell` convenience alias.**

In `dsdp_game_code.v`, immediately after the `Sout_cell` definition (was `S_output_cell`, now near line 236), add:

```coq
(* S_cell — short alias for [Sout_cell]; keeps `grep S_cell` landing on the
   leaked-output cell. *)
Notation S_cell := Sout_cell.
```

- [ ] **Step 3: Rename the leaked-output value binders `s` -> `Sout_val` in the fiber file.**

Site-by-site (NOT a blind substitution — other local binders such as `sread` must be left alone). Each is a monadic bind `s ← …` (or `denote_Sout_get_body`) and its in-scope uses. Edit these binders and the uses that read them:

- `guessing_challenger` (~line 100-101): `s ← call_s_get tt` and `call_pred (view, s)`.
- `guess_pair_challenger` (~line 402-403): same shape.
- `guess_resolved` / `guess_resolved_par` (~line 599) and `guess_resolved_oracles` (~line 641-642): `s ← …` and `(view, s)`.
- `guess_resolved_caps` (~line 855-858): `s ← denote_Sout_get_body …` and `(vt.1.1, s)`.
- `guess_full_code` destructure (~line 869): `let '(guess, v2, (v1, u1, u2, u3, v2', v3, s), irs) := gv`.
- `guess_full_proj_code` (~line 901-903), `guess_triple_proj_code` (~line 926-929), `guess_inner` (~line 997-1000): `s ← …` and `(vt.1.1, s)`.

Add one anchor comment at the canonical consume site in `guessing_challenger`:

```coq
      guess ← call_pred (view, Sout_val) ;;   (* Sout consumed by the predictor here *)
```

- [ ] **Step 4: Build every affected file.**

Run (from the repo root, with the project opam switch active):

```bash
make dumas2017dual/dsdp/dsdp_security_indcpa_fiber.vo
```

Expected: clean build of `dsdp_game_code.vo`, `dsdp_game_symbolic.vo`, `dsdp_indcpa_security.vo`, `dsdp_security_indcpa_fiber.vo` with no errors. If a stray `s` was renamed wrongly, the error pinpoints it; fix and rebuild.

- [ ] **Step 5: Confirm greppability.**

```bash
cd dumas2017dual/dsdp
grep -c -F Sout dsdp_security_indcpa_fiber.v    # expect: RV + binders + cell + oracle, > 40
grep -n -F Sout_val dsdp_security_indcpa_fiber.v # expect: the consume/read sites incl. the anchor comment
```

- [ ] **Step 6: Commit A (audit bypass — pure mechanical rename).**

```bash
ROCQ_AUDIT_BYPASS=1 git add -A && \
ROCQ_AUDIT_BYPASS=1 git commit -m "dsdp: unify leaked-output identifiers onto the Sout stem (Sout_cell/id_Sout_get/denote_Sout_get_body/Sout_val)"
```

---

## Task 2: `dsdp_game_gen_literal.v` scaffolding

**Files:**
- Create: `dsdp_game_gen_literal.v`
- Modify: `_CoqProject` (add the file so `make` builds it)

- [ ] **Step 1: Create the file header, imports, section, variables, and hypotheses.**

Mirror the fiber section's parameter block and the `scratch_print_gen.v` notations. The seed-weight hypotheses (`seed_wu1/wu2/wu3/wv1`) and `card_renc_neq` are required to reduce the abstract denotation to the readable form.

```coq
(* dsdp_game_gen_literal.v — the LITERAL (hand-spelled) form of the auto-derived
   corrupted-Alice SSProve program.  [gen_literal_zeroE] / [gen_literal_realE]
   certify that the legible programs below are exactly the denotations
   [denote_run seed gc] / [denote_run seed gc_real] the generator emits for the
   output-exposing all-zero / real endpoint games, with the scalar-product output
   S written by name into [Sout_cell]. *)

From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap reals realsum.
Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve.Crypt Require Import Package pkg_composition Pr.
Set Warnings "notation-overridden,ambiguous-paths".
From Stdlib Require Import Utf8.
From extructures Require Import ord fset fmap.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter spp_proba bayes.
Require Import homomorphic_encryption indcpa_ror.
Require Import dsdp_program.
Require Import smc.ssprove_ext_lossless.
Require Import dsdp_game_code dsdp_symbolic dsdp_game_symbolic.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Import GRing.Theory Num.Theory Order.POrderTheory.
Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.

Section dsdp_game_gen_literal.
Variables (AHE : AHEncType) (Renc : finType) (card_renc : nat)
  (renc_card : #|Renc| = card_renc) (rand_of_renc : Renc -> rand AHE)
  (t_msg t_cipher : choice_type)
  (chmsg_of_msg : plain AHE -> t_msg)
  (chcipher_of_cipher : cipher AHE -> t_cipher)
  (pkey_of_party : party_id -> pub_key AHE)
  (card_msg : nat) (msg_of_idx : 'I_card_msg -> plain AHE) (rand0 : rand AHE).
Variable seed : denv AHE.
Hypothesis card_renc_neq : card_renc != card_msg.
Variables (w_v1 w_u1 w_u2 w_u3 : plain AHE).
Hypothesis seed_wu1 : as_plain (de_val_nth seed 0) = w_u1.
Hypothesis seed_wu2 : as_plain (de_val_nth seed 1) = w_u2.
Hypothesis seed_wu3 : as_plain (de_val_nth seed 2) = w_u3.
Hypothesis seed_wv1 : as_plain (de_val_nth seed 3) = w_v1.

Local Notation "'msg'" := t_msg (in custom pack_type at level 2).
Local Notation "'ciphers'" := (cipher_list t_cipher) (in custom pack_type at level 2).

Set Warnings "-notation-overridden".
Notation "u *h w" := (Emul u w) (at level 40).
Notation "u ^h w" := (Epow u w) (at level 40).
Notation "'E<' p ',' s '>(|' m '|)'" :=
  (enc (pkey_of_party p) m (rand_of_renc (sample_to_renc renc_card s)))
  (at level 10, p constr at level 0, s constr at level 0, m constr at level 200,
   format "'E<' p ',' s '>(|'  m  '|)'").
Notation "'m[' i ']'" := (msg_of_idx i) (at level 0).
Notation "'<[' c ']>'" := (chcipher_of_cipher c) (at level 0).
Set Warnings "notation-overridden".
```

- [ ] **Step 2: Add the local `drun`/`dhe` abbreviations, the seeded games, and the reflection scaffolding (copied from the fiber file, standalone — no mutual import).**

```coq
Let drun := denote_run renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
              pkey_of_party msg_of_idx rand0.
Let dhe := denote_he pkey_of_party rand0.

Let gc      := all_zero (game_of_trace_seeded dsdp_weight_names
                 (dsdp_alice_obs_leak_S_seeded card_msg card_renc)).
Let gc_real := all_real (game_of_trace_seeded dsdp_weight_names
                 (dsdp_alice_obs_leak_S_seeded card_msg card_renc)).

(* The seven denote_run per-constructor unfold lemmas, verbatim from the fiber
   file (dsdp_security_indcpa_fiber.v:512-525): denote_run_sample_msg,
   denote_run_sample_renc, denote_run_put, denote_run_put_output, denote_run_let,
   denote_run_enc_hop, denote_run_ret.  Each is `by rewrite /drun /denote_run
   -/denote_run …`. *)
(* gc_eq / gc_real_eq: `by rewrite /gc; vm_compute.` reflections to the explicit AST. *)
(* output_term notation + denote_output_termE: verbatim from fiber:537-550. *)
```

- [ ] **Step 3: Register the file in `_CoqProject`.**

Add `dumas2017dual/dsdp/dsdp_game_gen_literal.v` to `_CoqProject` next to `dsdp_security_indcpa_fiber.v` (before it, since fiber does not depend on it but file order should respect the dependency DAG: after `dsdp_game_symbolic.v`).

- [ ] **Step 4: Build the scaffolding (Admitted-stub the two mid-point lemmas for now).**

Run: `make dumas2017dual/dsdp/dsdp_game_gen_literal.vo`
Expected: builds with `gc_eq`, `gc_real_eq`, the unfold lemmas, and `denote_output_termE` all green; the two `gen_literal_*E` lemmas are `Admitted` placeholders at this step.

---

## Task 3: `gen_literal_zero` + `gen_literal_zeroE`

**Files:**
- Modify: `dsdp_game_gen_literal.v`

- [ ] **Step 1: Read the reduced normal form of `drun seed gc`.**

Use the Rocq MCP. Open the file at a scratch lemma `Goal drun seed gc = drun seed gc.` and step:

```
rewrite {2}/gc gc_eq
  denote_run_sample_msg denote_run_sample_msg denote_run_sample_msg
  denote_run_sample_msg denote_run_sample_renc denote_run_sample_renc
  denote_run_put denote_run_enc_hop denote_run_enc_hop
  denote_run_let denote_run_let denote_run_put_output denote_run_ret.
```

then rewrite the output put with `denote_output_termE` and the four seed hypotheses (`seed_wv1 seed_wu1 seed_wu2 seed_wu3`) and `simpl`. Read the RHS: that is the program to transcribe. (This is the `scratch_print_gen.v` printing recipe; the notations render the combine/hop ciphers and `m[ i ]`.)

- [ ] **Step 2: Transcribe the normal form into `gen_literal_zero`.**

Write `Definition gen_literal_zero : raw_code (cipher_list t_cipher) := …` with the binders in printed order, the `#put Sout_cell := Some (chmsg_of_msg Sout)` step bound by `let Sout := dsdp_output w_v1 w_u1 w_u2 w_u3 m[x] m[x0] in`, and the `ret [:: … ]` of four `<[ … ]>` ciphers. (The all-zero endpoint: both hop payloads are `0`.)

- [ ] **Step 3: Prove `gen_literal_zeroE`.**

```coq
(* gen_literal_zeroE — the legible all-zero output-exposing program is the
   generator's denotation of the seeded all-zero game. *)
Lemma gen_literal_zeroE : gen_literal_zero = drun seed gc.
Proof.
rewrite /gen_literal_zero /gc gc_eq
  !(denote_run_sample_msg, denote_run_sample_renc, denote_run_put,
    denote_run_enc_hop, denote_run_let, denote_run_put_output, denote_run_ret).
(* rewrite the output term to dsdp_output via denote_output_termE + seed hyps *)
by rewrite denote_output_termE seed_wv1 seed_wu1 seed_wu2 seed_wu3.
Qed.
```

Adjust the rewrite multiset to match the actual node order from Step 1 if needed.

- [ ] **Step 4: Verify.**

Run `rocq_check` on `gen_literal_zeroE` (proof_finished: true). Per project convention a green `rocq_check` is sufficient verification.

---

## Task 4: `gen_literal_real` + `gen_literal_realE`

**Files:**
- Modify: `dsdp_game_gen_literal.v`

- [ ] **Step 1: Read the reduced normal form of `drun seed gc_real`.**

Same recipe as Task 3 Step 1 but with `gc_real` / `gc_real_eq`. The only structural difference from the zero case is the two hop payloads: `GC_enc_hop 1 (HE_var …) …` (the real secret) instead of `GC_enc_hop 1 (HE_const 0) …`.

- [ ] **Step 2: Transcribe into `gen_literal_real`.**

Identical to `gen_literal_zero` except the two `E<Bob,…>(| … |)` / `E<Charlie,…>(| … |)` hop ciphers carry the real plaintexts (`m[ … ]`) rather than `0`. The `let Sout := dsdp_output …` step and the `#put Sout_cell` step are identical to the zero program.

- [ ] **Step 3: Prove `gen_literal_realE`.**

```coq
(* gen_literal_realE — the legible real output-exposing program is the
   generator's denotation of the seeded real game. *)
Lemma gen_literal_realE : gen_literal_real = drun seed gc_real.
Proof.
rewrite /gen_literal_real /gc_real gc_real_eq
  !(denote_run_sample_msg, denote_run_sample_renc, denote_run_put,
    denote_run_enc_hop, denote_run_let, denote_run_put_output, denote_run_ret).
by rewrite denote_output_termE seed_wv1 seed_wu1 seed_wu2 seed_wu3.
Qed.
```

- [ ] **Step 4: Verify.**

`rocq_check` on `gen_literal_realE` (proof_finished: true). Close the section (`End dsdp_game_gen_literal.`).

---

## Task 5: Wire-up, cleanup, build, audit, commit (Commit B)

**Files:**
- Modify: `dsdp_security_indcpa_fiber.v` (cross-reference comment)
- Delete: `scratch_print_gen.v`

- [ ] **Step 1: Add the fiber cross-reference comment.**

At `dsdp_security_indcpa_fiber.v` `Let gc := …` (~line 506), add a comment line:

```coq
(* The legible hand-spelled form of [drun seed gc] is certified by
   [gen_literal_zeroE] in dsdp_game_gen_literal.v. *)
```

(No `Require` — keeps the files independent and avoids helper-lemma name clashes.)

- [ ] **Step 2: Delete the superseded scratch file.**

```bash
cd /Users/cheng-huiweng/Projects/coq/infotheo-itp/dumas2017dual/dsdp
git rm scratch_print_gen.v 2>/dev/null || rm -f scratch_print_gen.v
```

Confirm nothing imports it: `grep -rn "scratch_print_gen" --include="*.v" .` (expect no hits) and it is absent from `_CoqProject`.

- [ ] **Step 3: Full project build.**

Run: `make` (from repo root).
Expected: whole project builds, including `dsdp_game_gen_literal.vo`. No new axioms (the lemmas are equalities proved by computation/rewriting).

- [ ] **Step 4: Axiom check on the new lemmas.**

`rocq_assumptions` (or `Print Assumptions gen_literal_zeroE.` / `gen_literal_realE.`): expect only the section variables/hypotheses, no stray axioms.

- [ ] **Step 5: rocq-auditor Stage-2 (mandatory — new identifiers + proof bodies).**

Dispatch the rocq-auditor agent over `dsdp_game_gen_literal.v`. Incorporate any naming/style findings before committing.

- [ ] **Step 6: Commit B.**

```bash
git add dumas2017dual/dsdp/dsdp_game_gen_literal.v _CoqProject \
        dumas2017dual/dsdp/dsdp_security_indcpa_fiber.v
git rm --cached --ignore-unmatch dumas2017dual/dsdp/scratch_print_gen.v
git commit -m "dsdp: add dsdp_game_gen_literal.v — legible mid-point program (S visible) = auto-derived denote_run, for real and zero endpoints; drop superseded scratch_print_gen.v"
```

---

## Self-review

- **Spec coverage:** Component 1 (legible programs + both mid-point lemmas) → Tasks 2-4. Component 2 (`Sout` rename, `S_cell` alias) → Task 1. Verification/commit plan → Steps in each task + Task 5. scratch deletion → Task 5 Step 2. All spec sections mapped.
- **Placeholder scan:** The combine/hop-cipher text in `gen_literal_zero`/`gen_literal_real` is transcribed from the verified reduced normal form (Task 3/4 Step 1), not guessed — this is an interactive transcription with a defined recipe, the same method `scratch_print_gen.v` documents, and `rocq_check` rejects any mismatch. Not a TBD.
- **Type consistency:** `gen_literal_zero`/`gen_literal_real : raw_code (cipher_list t_cipher)`; `gen_literal_zeroE`/`gen_literal_realE` equate them to `drun seed gc` / `drun seed gc_real`; `drun`/`dhe`/`gc`/`gc_real` defined in Task 2; seed hypotheses `seed_wu1/wu2/wu3/wv1` and `card_renc_neq` declared in Task 2 Step 1 and used in Tasks 3-4. Renamed identifiers `Sout_cell`/`id_Sout_get`/`denote_Sout_get_body`/`Sout_val` consistent across Task 1 and the new file.
