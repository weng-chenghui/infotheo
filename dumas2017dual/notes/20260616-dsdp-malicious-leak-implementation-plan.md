# Malicious-leak sound reconstruction — Implementation Plan

> Spec: `20260616-dsdp-malicious-leak-sound-reconstruction.md`. All proof bodies
> below are transplanted verbatim from the de-risk probe
> (`dumas2017dual/dsdp/.scratch/probe_leak_feasibility.v`, compiled clean,
> Rocq 9.0.0, no extra axioms). Probes A/B/C/D all pass.

**Goal:** Replace the mis-filed algebraic `US_n_compromised_leaks_V1` with a
genuine N-party full-leakage theorem `US_n_compromised_leaks_secret`
(`H(VS_0 | View) = 0`) and its 3-party instance `US_compromised_leaks_V2`, both
sound (no encryption assumption), and tag every `dsdp_main.v` headline 3-party /
N-party. Scope the IND-CPA secrecy reductions in a separate memo.

**Architecture:** Pure-Infotheo leak via `centropy_RV_comp0` (`H(f∘X | X) = 0`).
Generic theorem lives in `dsdp_main.v / Section dsdp_malicious_n`; the 3-party
theorem is a formal `n_relay = 1` instance of it in a new section. `malicious_n`
in `dsdp_view_independence.v` is unchanged. No new support lemmas.

**Verify command (each code task):**
`coqc -w -projection-no-head-constant -w -redundant-canonical-projection -w -notation-overridden -w -ambiguous-paths -w -notation-incompatible-format -w -notation-incompatible-prefix -R . infotheo dumas2017dual/dsdp/dsdp_main.v`
(exit 0). dsdp_main.v carries the SSProve import chain, so allow up to 10 min.

---

## Task 0: Commit design + plan docs

- [ ] Commit the spec and this plan (probe stays gitignored in `.scratch`).

```bash
git add dumas2017dual/notes/20260616-dsdp-malicious-leak-sound-reconstruction.md \
        dumas2017dual/notes/20260616-dsdp-malicious-leak-implementation-plan.md
git commit -m "dsdp notes: spec + plan for sound malicious-leak reconstruction"
```

---

## Task 1: Generic N-party leakage theorem

**Files:** Modify `dumas2017dual/dsdp/dsdp_main.v` (`Section dsdp_malicious_n`,
currently lines ~362-394).

- [ ] **Step 1.** In `Section dsdp_malicious_n`, after the existing
  `Local Open Scope fdist_scope.` line, add:

```coq
Local Open Scope entropy_scope.
```

- [ ] **Step 2.** Delete the entire `US_n_compromised_leaks_V1` lemma (its comment
  block + `Lemma … Qed.`).

- [ ] **Step 3.** In its place insert:

```coq
(* US_n_compromised_leaks_secret — a corrupted Alice fixing her query to e_1
   makes relay party 1's input VS_0 a function of her view: the protocol output
   is in the view and equals VS_0, so its conditional entropy collapses to zero.
   N-party generic; the 3-party result is the n_relay = 1 instance. *)
Theorem US_n_compromised_leaks_secret {A : finType}
    (View : {RV P -> A}) (g : A -> msg)
    (US VS : {RV P -> {ffun 'I_n_relay.+1 -> msg}})
    (US_e1 : US = fun _ => @ConstUS_n p_minus_2 q_minus_2 n_relay)
    (output_in_view :
       @Dotp_n_rv R T P p_minus_2 q_minus_2 n_relay US VS = g `o View) :
  `H( (fun t => VS t ord0) | View ) = 0.
Proof.
have disc : @Dotp_n_rv R T P p_minus_2 q_minus_2 n_relay US VS
            = (fun t => VS t ord0).
  rewrite US_e1 /Dotp_n_rv; apply: boolp.funext => t /=.
  exact: dotp_n_e1.
have key : (fun t => VS t ord0) = g `o View by rewrite -disc.
rewrite key; exact: centropy_RV_comp0.
Qed.
```

- [ ] **Step 4.** Verify: run the verify command. Expected exit 0.
- [ ] **Step 5.** Run rocq-auditor on the new theorem (new identifier). Incorporate
  any naming/style findings inline.
- [ ] **Step 6.** Commit:

```bash
git add dumas2017dual/dsdp/dsdp_main.v
git commit -m "dsdp main: replace algebraic US_n_compromised_leaks_V1 with genuine N-party leakage theorem US_n_compromised_leaks_secret (H(VS_0|View)=0, sound via centropy_RV_comp0)"
```

---

## Task 2: Concrete 3-party instance

**Files:** Modify `dumas2017dual/dsdp/dsdp_main.v` (insert a new section
immediately after `End dsdp_malicious_n.`).

- [ ] **Step 1.** Insert:

```coq
Section dsdp_malicious_3party.
(* 3-party instance of US_n_compromised_leaks_secret at n_relay = 1 *)
Local Set Default Goal Selector "1".
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Context {R : realType}.
Variable T : finType.
Variable P : R.-fdist T.
Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Local Notation m := (p * q).
Local Notation msg := 'Z_m.

Variables (V1 V2 V3 U1 U2 U3 R2 R3 : {RV P -> msg}).
Variable Dk_a : {RV P -> Alice.-key Dec msg}.

Let D2 : {RV P -> msg} := V2 \* U2 \+ R2.
Let D3 : {RV P -> msg} := V3 \* U3 \+ R3 \+ D2.
Let S  : {RV P -> msg} := D3 \- R2 \- R3 \+ U1 \* V1.

Let E_alice_d3   : {RV P -> Alice.-enc msg}   := E' Alice `o D3.
Let E_charlie_v3 : {RV P -> Charlie.-enc msg} := E' Charlie `o V3.
Let E_bob_v2     : {RV P -> Bob.-enc msg}     := E' Bob `o V2.

(* Alice's full real view: her key, the output S, her own inputs and masks, and
   the three ciphertext hops. V2 appears only inside S and the Bob hop. *)
Let AliceView :=
  [% Dk_a, S, V1, U1, U2, U3, R2, R3, E_alice_d3, E_charlie_v3, E_bob_v2].

(* US_compromised_leaks_V2 — a malicious Alice fixing her query to e_1
   (U2 = 1, U3 = 0) reads Bob's private input V2 off her view, ciphertext hops
   included; its conditional entropy collapses to zero. 3-party instance. *)
Theorem US_compromised_leaks_V2 :
  U2 = (fun _ => 1) -> U3 = (fun _ => 0) ->
  `H( V2 | AliceView ) = 0.
Proof.
move=> HU2 HU3.
pose VS : {RV P -> {ffun 'I_1.+1 -> msg}} :=
  fun t => [ffun i => if i == ord0 then V2 t else V3 t].
pose US : {RV P -> {ffun 'I_1.+1 -> msg}} :=
  fun t => [ffun i => if i == ord0 then U2 t else U3 t].
pose g := fun o : (Alice.-key Dec msg * msg * msg * msg * msg * msg * msg * msg
                    * Alice.-enc msg * Charlie.-enc msg * Bob.-enc msg) =>
  let '(_, s, _, u1, _, _, _, _, _, _, _) := o in
  let '(_, _, v1, _, _, _, _, _, _, _, _) := o in
  s - v1 * u1.
have HVS0 : (fun t => VS t ord0) = V2.
  by apply: boolp.funext => t; rewrite /VS ffunE eqxx.
have HUS_e1 : US = fun _ => @ConstUS_n p_minus_2 q_minus_2 1.
  rewrite /US /ConstUS_n; apply: boolp.funext => t; apply/ffunP => i.
  by rewrite !ffunE HU2 HU3 /=; case: (i == ord0).
have Hout : @Dotp_n_rv R T P p_minus_2 q_minus_2 1 US VS = g `o AliceView.
  rewrite (_ : @Dotp_n_rv R T P p_minus_2 q_minus_2 1 US VS = (fun t => V2 t)).
    rewrite /g /AliceView /comp_RV /S /D3 /D2.
    by apply: boolp.funext => t /=; rewrite HU2 HU3 /=; ring.
  rewrite HUS_e1 /Dotp_n_rv.
  by apply: boolp.funext => t /=; rewrite dotp_n_e1 /VS ffunE eqxx.
have := US_n_compromised_leaks_secret (View := AliceView) (g := g)
          (US := US) (VS := VS) HUS_e1 Hout.
by rewrite HVS0.
Qed.

End dsdp_malicious_3party.
```

- [ ] **Step 2.** Verify: run the verify command. Expected exit 0.
- [ ] **Step 3.** Run rocq-auditor (new identifiers). Incorporate findings inline.
- [ ] **Step 4.** Commit:

```bash
git add dumas2017dual/dsdp/dsdp_main.v
git commit -m "dsdp main: add 3-party US_compromised_leaks_V2 as a formal n_relay=1 instance of US_n_compromised_leaks_secret (full real view incl. ciphertext hops)"
```

---

## Task 3: 3-party / N-party scope tags

**Files:** Modify `dumas2017dual/dsdp/dsdp_main.v` (file header comment + each
theorem's comment). No new identifiers.

- [ ] **Step 1.** Replace the file header headline list (lines ~9-19) with a
  version that tags each: `(3-party)` for `dsdp_alice_*`, `dsdp_centropy_uniform`,
  `US_compromised_leaks_V2`; `(N-party)` for `dsdp_centropy_uniform_n`,
  `relay_privacy_n`, `US_n_compromised_leaks_secret`. Add one sentence:
  "The file mixes generic N-party results with their 3-party DSDP instances; each
  theorem's comment states its scope."

- [ ] **Step 2.** Append the scope tag to each theorem's leading comment, per the
  table in spec Section 6. Example for `dsdp_alice_view_advantage_le`: end its
  comment with " (3-party: the DSDP corrupted-Alice instance.)".

- [ ] **Step 3.** Verify: run the verify command. Expected exit 0 (comments only).
- [ ] **Step 4.** Commit (audit-bypass, comments only):

```bash
git add dumas2017dual/dsdp/dsdp_main.v
ROCQ_AUDIT_BYPASS=1 git commit -m "dsdp main: tag every headline 3-party / N-party in file + theorem comments"
```

---

## Task 4: Blueprint coverage

**Files:** Modify `dumas2017dual/blueprint/blueprint-exclude.txt`.

- [ ] **Step 1.** Remove the line `dsdp_main:US_n_compromised_leaks_V1`.
- [ ] **Step 2.** Add (in the `dsdp_main:` block, alphabetical):
  `dsdp_main:US_compromised_leaks_V2` and
  `dsdp_main:US_n_compromised_leaks_secret`.
- [ ] **Step 3.** Verify: `python3 dumas2017dual/blueprint/check_coverage.py`.
  Expected: passes (exit 0, no uncovered declarations). The checker reads
  `dsdp_main.glob`, so ensure Tasks 1-2 recompiled it.
- [ ] **Step 4.** Commit (audit-bypass):

```bash
git add dumas2017dual/blueprint/blueprint-exclude.txt
ROCQ_AUDIT_BYPASS=1 git commit -m "dsdp blueprint: drop US_n_compromised_leaks_V1, add the two new leak headlines to coverage baseline"
```

---

## Task 5: IND-CPA secrecy scoping memo

**Files:** Create
`dumas2017dual/notes/20260616-dsdp-indcpa-secrecy-reductions-scope.md`.

- [ ] **Step 1.** Write the memo: the deleted Bob/Charlie semi-honest privacy
  results need game-based IND-CPA corruption reductions (not IT independence),
  modeled on the existing Alice guessing triangle; list the target statements,
  the game/oracle shape to reuse, and the open work. Statement bodies in terse
  declarative style.
- [ ] **Step 2.** Commit:

```bash
git add dumas2017dual/notes/20260616-dsdp-indcpa-secrecy-reductions-scope.md
git commit -m "dsdp notes: scope IND-CPA Bob/Charlie secrecy reductions as future work"
```

---

## Self-review

- Spec coverage: Task 1 (generic), Task 2 (concrete instance + hops), Task 3 (doc
  tags), Task 4 (blueprint drop/add), Task 5 (memo). `malicious_n` unchanged per
  spec Layer 1. All spec deliverables (Section 9 checklist) covered.
- All proof bodies are probe-validated verbatim; no placeholders.
- Identifier consistency: `US_n_compromised_leaks_secret` and
  `US_compromised_leaks_V2` used identically in Tasks 1, 2, 4.
