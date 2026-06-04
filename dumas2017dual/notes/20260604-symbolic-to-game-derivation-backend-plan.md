# Symbolic-to-game derivation — back-end implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: use superpowers:subagent-driven-development, dispatching **rocq-prover** as the per-task subagent (project policy: all `.v` writing/proving goes through rocq-prover). Steps use checkbox (`- [ ]`) syntax.

**Goal:** Build the back end of the symbolic-to-game pipeline — the `game_code`
AST, its denotation into SSProve packages, and a *generic* hybrid-ladder
advantage bound `AdvantageE ⟦real⟧ ⟦all-zero⟧ A ≤ k·epsilon_cpa` — validated on a
hand-built DSDP `game_code` fixture yielding `2·epsilon_cpa`.

**Architecture:** `game_code` is a first-order source AST (later produced by the
symbolic interpreter; here fed by a temporary fixture). `denote_game` lowers it
to an SSProve `package`, reusing all SSProve semantics/advantage machinery and
the project's `enc`/`Emul`/`Epow`. The ladder varies one `GC_enc_hop` site at a
time; one generic `hop_equiv` (`≈₀`) lemma, made tractable by a canonical sample
order, drives the triangle bound. Nothing on the SSProve side is hand-written.

**Tech stack:** Rocq + MathComp + SSProve (`Package`, `pkg_composition`, `Pr`,
`PackageNotation`), the project's `homomorphic_encryption` / `indcpa_ror`
(`AHEncType`, `oracle_encrypt_*`, `epsilon_cpa`, `enc_ind_cpa_real_or_zero`).
Verification via `mcp__rocq-mcp__rocq_compile` / `rocq_check`.

**Source of verified statements:** `.scratch/rocq/symbolic_game_derivation_skeleton.v`
(rocq-prover's elaboration-checked skeleton — all signatures below compiled there
as `Parameter`/`Admitted` stubs). This plan turns those stubs into real
`Definition`s and proofs.

**Coq verification gate (per task):** "fails" = the stub elaborates but the
proof is `Admitted`; "passes" = `rocq_compile` returns `success:true` and the
target lemma's `rocq_check` reports `proof_finished:true` with no `Admitted` and
no new custom axiom beyond `enc_ind_cpa_real_or_zero`.

---

## File structure

- Create: `dumas2017dual/dsdp/dsdp_game_code.v` — the entire back end (one Section
  mirroring `dsdp_security_indcpa.v`'s parameter block, lines ~101–217). Holds
  `he_term`, `game_code`, the structural functions, `denote_game` /
  `denote_game_shim`, `hybrid_ladder`, validity, `hop_equiv`, `advantage_le`,
  and the `gc_dsdp` validation.
- Reference only (do NOT modify): `dumas2017dual/dsdp/ref/dsdp_security_indcpa.v`
  (the hand-written games this back end retires — kept until the pipeline
  reproduces its `2·epsilon_cpa`), `homomorphic_encryption/indcpa_ror.v`.
- `_CoqProject` / build: add `dumas2017dual/dsdp/dsdp_game_code.v` to the build
  list (Task 1).

Interface vocabulary (`game_iface`, `cipher_list`, `id_game_run`, `id_v2_get`,
`V_2_cell`, `protocol_state`) is Section-local in `dsdp_security_indcpa.v` and so
is **re-declared** in the new file (the skeleton did this and it elaborates).
Extracting it into a shared `dsdp_game_iface.v` is deferred until
`dsdp_security_indcpa.v` is retired — noted in Task 12, not done here, to avoid
churning a soon-removed file.

---

### Task 1: Scaffold the file (imports, Section, parameters, interface vocab)

**Files:**
- Create: `dumas2017dual/dsdp/dsdp_game_code.v`
- Modify: `_CoqProject` (add the new file)

- [ ] **Step 1: Create the file with the verified header + parameter block.**
Copy the import header from `dsdp_security_indcpa.v:14–47` (HB, MathComp, the
`Set Warnings` SSProve fence, `extructures`, the `Require Import` list incl.
`homomorphic_encryption indcpa_ror`, `Import PackageNotation`, the scope opens,
`Notation R := SSProve.Crypt.Axioms.R`). Open `Section dsdp_game_code` and
declare the same `Variable`/`Hypothesis` block as `dsdp_security_indcpa.v:105–217`
(`AHE`, `Renc`, `card_renc`, `renc_card`, `rand_of_renc`, `t_msg`, `t_cipher`,
`msg_of_chmsg`, `chmsg_of_msg`, `chcipher_of_cipher`, `cipher_of_chcipher`,
`chcipher_of_cipherK`, `chmsg_of_msgK`, `pkey_of_party`, `card_msg`,
`msg_of_idx`). Then re-declare `cipher_list`, `id_game_run`, `id_v2_get`,
`V_2_cell`, `protocol_state`, `game_iface`, and the `'msg`/`'cipher_t`/`'ciphers'`
pack_type notations exactly as `dsdp_security_indcpa.v:219–309`.

- [ ] **Step 2: Add the file to the build and elaborate.**
Add the path to `_CoqProject`. Run `mcp__rocq-mcp__rocq_compile` on the file.
Expected: `success:true`, only the benign `notation-overridden` /
`notation-incompatible-prefix` warnings (same as the reference file). No errors.

- [ ] **Step 3: Commit.**
```bash
git add dumas2017dual/dsdp/dsdp_game_code.v _CoqProject
git commit -m "dsdp: scaffold dsdp_game_code.v (imports, section, interface vocab)"
```

---

### Task 2: `he_term` and `game_code` inductives

**Files:** Modify `dumas2017dual/dsdp/dsdp_game_code.v`

- [ ] **Step 1: Add the two inductives (concrete — verified in the skeleton).**
```coq
(* Deep embedding of the HE message algebra (single-sorted; Plain/Cipher
   sort-indexing deferred). nat args: HE_var/HE_const pool index; HE_enc/HE_dec
   carry a pubkey id and (for enc) a randomness slot. *)
Inductive he_term : Type :=
| HE_var   : nat -> he_term
| HE_const : nat -> he_term
| HE_enc   : nat -> he_term -> nat -> he_term
| HE_dec   : nat -> he_term -> he_term
| HE_emul  : he_term -> he_term -> he_term
| HE_epow  : he_term -> he_term -> he_term
| HE_add   : he_term -> he_term -> he_term
| HE_sub   : he_term -> he_term -> he_term
| HE_mul   : he_term -> he_term -> he_term.

(* Reified body of the id_game_run oracle. nat args are de Bruijn-style pool
   indices / pubkey ids / randomness slots. GC_enc_hop is the only hoppable
   statement; GC_let carries non-hoppable he_terms (incl. encryptions of masks). *)
Inductive game_code : Type :=
| GC_sample  : nat -> game_code -> game_code
| GC_put     : he_term -> game_code -> game_code
| GC_let     : he_term -> game_code -> game_code
| GC_enc_hop : nat -> he_term -> nat -> game_code -> game_code
| GC_ret     : seq he_term -> game_code.
```

- [ ] **Step 2: Elaborate.** Run `rocq_compile`. Expected: `success:true`.

- [ ] **Step 3: rocq-auditor Stage-2** on the new identifiers (naming: snake_case
defs, `HE_`/`GC_` capitalized constructors — confirm against the audit table in
the design doc §3).

- [ ] **Step 4: Commit.**
```bash
git add dumas2017dual/dsdp/dsdp_game_code.v
git commit -m "dsdp: add he_term and game_code inductives"
```

---

### Task 3: structural functions `hop_sites`, `all_real`, `all_zero`

**Files:** Modify `dumas2017dual/dsdp/dsdp_game_code.v`

**Strategy:** plain structural recursion over `game_code`. `hop_sites` collects
the positions/identifiers of `GC_enc_hop` nodes (decide: index by traversal
order; return `seq nat`). `all_real`/`all_zero` are the identity on structure but
tag the encrypt mode consumed by `denote_game` — represent the mode either by a
boolean field threaded into `denote_game` or by rewriting `GC_enc_hop` payloads;
pick whichever makes `denote_game` (Task 5) cleanest. rocq-prover decides the
representation and confirms termination.

- [ ] **Step 1:** rocq-prover writes `hop_sites`, `all_real`, `all_zero` with
signatures `game_code -> seq nat`, `game_code -> game_code`, `game_code ->
game_code` (verified to elaborate as `Parameter`s in the skeleton).
- [ ] **Step 2: Verify** `rocq_compile` `success:true`; sanity-`Eval` `hop_sites`
on a tiny literal `game_code` (one `GC_enc_hop`) returns a singleton.
- [ ] **Step 3:** rocq-auditor Stage-2.
- [ ] **Step 4: Commit** `git commit -m "dsdp: game_code structural functions (hop_sites, all_real, all_zero)"`.

---

### Task 4: `denote_game` — the lowering (the heart)

**Files:** Modify `dumas2017dual/dsdp/dsdp_game_code.v`

**Verified target signature (skeleton):**
```coq
denote_game : game_code -> package [interface] game_iface
```

**Strategy (delegated to rocq-prover; do NOT pre-write the body):**
- A `raw_code`-level core `denote_run : env -> game_code -> raw_code cipher_list`
  by recursion: `GC_sample n k → x ← sample uniform n ;; denote_run (push x) k`;
  `GC_put e k → #put V_2_cell := ⟦e⟧ ;; denote_run env k`;
  `GC_let e k → let v := ⟦e⟧ in denote_run (push v) k`;
  `GC_enc_hop pk e r k → bind enc(pk, ⟦e⟧-or-0, r) per the all_real/all_zero mode`;
  `GC_ret es → ret [seq ⟦e⟧ | e <- es]`. `⟦·⟧` denotes `he_term` over the env via
  the project's `enc`/`Emul`/`Epow`/`D` (reuse — never redefine).
- Binder discipline: the de Bruijn pool `env` maps `HE_var n` to the n-th bound
  sample/let value. rocq-prover pins the exact env representation (e.g. `seq`
  of denoted values, or a `nat -> value` map) and reports it.
- Wrap into `package [interface] game_iface` by adding the fixed `id_v2_get`
  oracle (reads `V_2_cell`) and `protocol_state` locs, mirroring
  `dsdp_security_indcpa.v:364–372`.

- [ ] **Step 1: Stub elaborates.** Confirm the `Parameter denote_game` signature
still elaborates in-file (it did in the skeleton).
- [ ] **Step 2: rocq-prover writes `denote_run` + `denote_game`.** Iterate with
`rocq_compile` until it elaborates as a real `Definition`/`Fixpoint`. Report the
`env` representation and the encrypt-mode mechanism actually used.
- [ ] **Step 3: Verify** `rocq_compile` `success:true`; `Eval`/`Check`
`denote_game (all_real gc_min)` on a one-sample/one-hop `gc_min` reduces to a
well-formed package term.
- [ ] **Step 4:** rocq-auditor Stage-2 (naming + docstrings for `denote_run`/`denote_game`).
- [ ] **Step 5: Commit** `git commit -m "dsdp: denote_game lowering game_code to SSProve package"`.

---

### Task 5: `denote_game_valid` (generic `ValidPackage`)

**Files:** Modify `dumas2017dual/dsdp/dsdp_game_code.v`

**Verified target (skeleton):**
```coq
Lemma denote_game_valid (gc : game_code) :
  ValidPackage (locs (denote_game gc)) [interface] game_iface (denote_game gc).
```
**Strategy:** generic over `gc` by induction on the `game_code` structure; each
constructor's body is valid code (sample/put/let/enc/ret are all `ValidCode`),
analogous to how the reference games are valid by construction. If a residual-
imports subtlety arises (as in `valid_code_link_residual`,
`dsdp_security_indcpa.v:71`), reuse that lemma rather than reproving it. rocq-prover
discovers the tactic; this is moderate risk (§9 #2).

- [ ] **Step 1:** state the lemma (Admitted), confirm it elaborates.
- [ ] **Step 2:** rocq-prover proves it; verify `rocq_check` `proof_finished:true`.
- [ ] **Step 3:** rocq-auditor Stage-2; **Step 4: Commit**
`git commit -m "dsdp: denote_game produces a ValidPackage (generic)"`.

---

### Task 6: `denote_game_shim` + its validity

**Files:** Modify `dumas2017dual/dsdp/dsdp_game_code.v`

**Verified target (skeleton):**
```coq
denote_game_shim : game_code -> nat ->
  package (oracle_encrypt_iface t_msg t_cipher) game_iface
```
**Strategy:** identical to `denote_game` except the `GC_enc_hop` at the given
`site` index is replaced by an `#import`ed oracle call
(`oracle_enc (party, ⟦e⟧)`), exactly mirroring `game_via_oracle_charlie`
(`dsdp_security_indcpa.v:600–647`). Because of the canonical sample order, the
shim and `denote_game` differ at exactly that one statement. Add the analogous
`ValidPackage` lemma.

- [ ] **Step 1:** stubs elaborate. **Step 2:** rocq-prover writes
`denote_game_shim` + validity; verify. **Step 3:** auditor. **Step 4: Commit**
`git commit -m "dsdp: denote_game_shim (one hop site routed through IND-CPA oracle)"`.

---

### Task 7: `hybrid_ladder` + oracle package aliases

**Files:** Modify `dumas2017dual/dsdp/dsdp_game_code.v`

**Verified targets (skeleton):**
```coq
hybrid_ladder : game_code -> seq raw_package
(* plus the package-form aliases needed for .(locs) premises: *)
oracle_real_pkg : package [interface] (oracle_encrypt_iface t_msg t_cipher)
oracle_zero_pkg : package [interface] (oracle_encrypt_iface t_msg t_cipher)
oracle_real := oracle_real_pkg : raw_package   (* for the ∘ in hop_equiv *)
oracle_zero := oracle_zero_pkg : raw_package
```
(`oracle_real_pkg`/`oracle_zero_pkg` built from
`oracle_encrypt_real_pkg`/`oracle_encrypt_zero_pkg` of `indcpa_ror` — the skeleton
reshape; `.(locs)` lives on `package`, not `raw_package`.)

**Strategy:** `hybrid_ladder gc` = the chain whose i-th game zeroes hop sites
`1..i` and leaves the rest real (`denote_game` of the appropriately-moded `gc`),
as a `seq raw_package`. rocq-prover decides whether the intermediate games are
built via `all_*`-style mode vectors or per-site rewriting (coordinate with
Task 3's mode representation).

- [ ] **Step 1:** stubs elaborate. **Step 2:** rocq-prover writes them; verify
`rocq_compile`. **Step 3:** auditor. **Step 4: Commit**
`git commit -m "dsdp: hybrid_ladder and oracle package aliases"`.

---

### Task 8: PROTOTYPE `hop_equiv` on a minimal `game_code` (§9 risk #1 gate)

**Files:** Modify `dumas2017dual/dsdp/dsdp_game_code.v` (a local `Example`/`Lemma`,
removed or kept as a regression after).

**This is the project's highest-risk step — do it before the generic lemma.**
Build the smallest `game_code` exercising one hop:
`gc_min := GC_sample c (GC_enc_hop pk (HE_var 0) r (GC_ret [HE_var 1]))` (one
sample, one hoppable encryption, return it). Prove the single perfect
equivalence:
```coq
Lemma hop_equiv_min :
  denote_game gc_min ≈₀ denote_game_shim gc_min 0 ∘ oracle_real.
```
**Strategy:** mirror `game_real_equiv_charlie_real` (`dsdp_security_indcpa.v:833`):
`eapply eq_rel_perf_ind_eq` (NOT ssreflect `apply:` — see the OOM note at line
836 and memory `ssprove_apply_vs_eapply`), `simplify_eq_rel`, sync the shared
samples with `ssprove_sync_eq`, and close by `rreflexivity_rule`. The design
claim is that the canonical sample order means **no `ssprove_swap_*` and no
encoding round-trip cancels are needed** — if the prototype proof in fact needs
swaps/cancels, that falsifies the §7 de-risking assumption: STOP, report which
steps were needed, and reassess the canonical-order invariant before scaling
(do not silently switch strategy).

- [ ] **Step 1:** define `gc_min`, state `hop_equiv_min` (Admitted), elaborate.
- [ ] **Step 2:** rocq-prover proves it; verify `rocq_check` `proof_finished:true`.
- [ ] **Step 3: Record the outcome** in the design doc §9 (did the canonical
order hold — no swaps/cancels — or not?).
- [ ] **Step 4: Commit** `git commit -m "dsdp: prototype hop_equiv on minimal game_code (canonical-order gate)"`.

---

### Task 9: generic `hop_equiv`

**Files:** Modify `dumas2017dual/dsdp/dsdp_game_code.v`

**Verified target (skeleton):**
```coq
Lemma hop_equiv (gc : game_code) (site : nat) (* + validity/disjointness premises *) :
  denote_game (* real at site *) gc ≈₀ denote_game_shim gc site ∘ oracle_real.
```
(Plus the symmetric zero-oracle equivalence to `denote_game` with `site` zeroed,
mirroring `charlie_zero_equiv_game_hybrid_one`, `dsdp_security_indcpa.v:1000`.)

**Strategy:** generalize the Task 8 prototype over `gc` and `site` by induction
on the statement prefix before `site`; the post-`site` suffix is identical on
both sides. Proceed only if Task 8 validated the no-swap/no-cancel claim.

- [ ] **Step 1:** state (Admitted), elaborate. **Step 2:** rocq-prover proves;
verify. **Step 3:** auditor. **Step 4: Commit**
`git commit -m "dsdp: generic hop_equiv"`.

---

### Task 10: generic `advantage_le`

**Files:** Modify `dumas2017dual/dsdp/dsdp_game_code.v`

**Verified target (skeleton):**
```coq
Lemma advantage_le (LA : Locations) (A : raw_package) (gc : game_code)
  (* validity + per-game/oracle disjointness premises, mirroring
     advantage_game_real_game_enc_zero at dsdp_security_indcpa.v:1360 *) :
  AdvantageE (denote_game (all_real gc)) (denote_game (all_zero gc)) A
    <= (size (hop_sites gc))%:R * epsilon_cpa.
```
**Strategy:** a driver over SSProve's existing `Advantage_triangle_chain`
(reuse — do not reimplement) across `hybrid_ladder gc`; bound each consecutive
hop by `hop_equiv` + `Advantage_link` + `enc_ind_cpa_real_or_zero` (the IND-CPA
axiom about the real scheme), exactly as `advantage_hop_real_h1`
(`dsdp_security_indcpa.v:1124`) does for one hop, generalized to `k` by
induction on `hop_sites gc`. The `%:R` count comes from the ladder length.

- [ ] **Step 1:** state (Admitted), elaborate. **Step 2:** rocq-prover proves;
verify `rocq_check` `proof_finished:true`. **Step 3:** auditor. **Step 4: Commit**
`git commit -m "dsdp: generic advantage_le (k hops bound by k*epsilon_cpa)"`.

---

### Task 11: DSDP validation — `gc_dsdp` fixture → `2·epsilon_cpa`

**Files:** Modify `dumas2017dual/dsdp/dsdp_game_code.v`

`gc_dsdp` is a **temporary AST fixture** standing in for the symbolic
interpreter's future output (sub-project 2), used to check the back end
end-to-end. The derived SSProve game is `denote_game (all_real gc_dsdp)` — no
hand-written game.

**Fixture (skeleton de Bruijn convention):** samples bind 0–9
(V2,V3,U2,U3,R2,R3,ra1,ra2,rb1,rc1), `GC_put` of the V2 secret, two `GC_enc_hop`
binding 10 (c2),11 (c3), two `GC_let` binding 12 (a1),13 (a2) via
`HE_emul`/`HE_epow`, `GC_ret [HE_var 12; HE_var 13; HE_var 10; HE_var 11]`
(matching `[a1;a2;c2;c3]`, `dsdp_security_indcpa.v:359`).

```coq
Definition gc_dsdp : game_code := (* per the convention above *).

Lemma hop_sites_gc_dsdp : size (hop_sites gc_dsdp) = 2.
(* by reflexivity / computation *)

Lemma advantage_gc_dsdp (LA : Locations) (A : raw_package)
  (* same premises as advantage_le, instantiated at gc_dsdp *) :
  AdvantageE (denote_game (all_real gc_dsdp)) (denote_game (all_zero gc_dsdp)) A
    <= 2%:R * epsilon_cpa.
```
**Strategy:** `advantage_gc_dsdp` = `advantage_le` at `gc_dsdp`, rewriting
`size (hop_sites gc_dsdp)` to `2` via `hop_sites_gc_dsdp`. This reproduces
`advantage_game_real_game_enc_zero`'s `2·epsilon_cpa` from the *derived* game —
the sanity check that the pipeline matches the retired hand proof.

- [ ] **Step 1:** define `gc_dsdp`, state both lemmas (Admitted/by-computation),
elaborate. **Step 2:** rocq-prover proves; verify `hop_sites_gc_dsdp` by
`reflexivity` and `advantage_gc_dsdp` via `advantage_le`. **Step 3:** auditor.
- [ ] **Step 4: Commit** `git commit -m "dsdp: validate back end on gc_dsdp fixture (2*epsilon_cpa)"`.

---

### Task 12: axiom hygiene + close-out

**Files:** Modify `dumas2017dual/dsdp/dsdp_game_code.v` (close `Section`); design doc.

- [ ] **Step 1: Axiom check.** `Print Assumptions advantage_gc_dsdp`. Expected:
only `enc_ind_cpa_real_or_zero` (+ the section parameters and standard MathComp/
SSProve axioms) — **no new custom axiom** introduced by this back end. If any
`Parameter` from the skeleton leaked as an axiom, it must now be a real
`Definition` (Tasks 3–7); fix and re-check.
- [ ] **Step 2:** close `End dsdp_game_code.`; full-file `rocq_compile`
`success:true`.
- [ ] **Step 3: Update the design doc** §9 with the Task-8 canonical-order
outcome and tick the §10 success criteria; note the deferred shared-interface
extraction (`dsdp_game_iface.v`) as a follow-up once `dsdp_security_indcpa.v` is
retired.
- [ ] **Step 4: Final rocq-auditor Stage-2** over the whole file.
- [ ] **Step 5: Commit**
```bash
git add dumas2017dual/dsdp/dsdp_game_code.v dumas2017dual/notes/20260604-symbolic-to-game-derivation-design.md
git commit -m "dsdp: close back-end game-derivation slice (axiom hygiene, doc sync)"
```

---

## Notes for the executor

- **Hard-stop triggers** (surface to the user, do not push through): Task 8
  needs swaps/cancels (falsifies §7); any new custom axiom; rocq-auditor failure;
  rocqworker memory escalation; a strategy switch (count ≥ 1).
- **Out of scope** (later sub-projects): the symbolic interpreter + `Symbolic_AHEnc`
  + `game_of_trace` front end; the IT `1/m` leg; the final `1/m + 2·epsilon_cpa`
  composition theorem; N-party generalization.
