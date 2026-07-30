# piSMC trace-link Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax. Rocq adaptation: the TDD analogue is
> state-lemma-then-prove; a task is done only when its lemmas are `Qed` (no
> `Admitted`/`Abort`/`Axiom`) and every touched file compiles. Commit only
> then.

**Goal:** Prove that the corrupted-Alice security bound applies to the trace
the piSMC interpreter actually produces, closing the chain
program -> trace -> view random variable -> security bound.

**Architecture:** Charlie's re-encryption randomness and Bob's forward
randomness are section parameters, so Alice's executed trace is a
deterministic function of the leg's existing view. The trace-level headline
is then a corollary of the leg's already-`Qed`
`dsdp_alice_guess_fdist_V2_real_le`. The only substantial new proof is the
staged evaluation of the fifteen-round run at an abstract `AHEncType`.

**Tech Stack:** Rocq 9.0.0 via `/Users/cheng-huiweng/Projects/coq/_opam`,
mathcomp 2.x, infotheo (this repo, `-R . infotheo`), HB.

**Spec:** `dumas2017dual/notes/20260730-dsdp-trace-link-design.md`
**Probes (compiled, keep):** `<scratchpad>/probe_trace_link.v`,
`<scratchpad>/audit_typegeneric_traces.v`,
`<scratchpad>/audit_corollary_route.v`
where `<scratchpad>` =
`/private/tmp/claude-501/-Users-cheng-huiweng-Projects-coq-infotheo-itp/21ae3115-6094-4366-ac12-5df937e58ff8/scratchpad`

**Compile command** (used by every task; macOS, no `timeout`; kill the
rocqworker process group if a run exceeds ~3 min):

```bash
/Users/cheng-huiweng/Projects/coq/_opam/bin/coqc \
  -R /Users/cheng-huiweng/Projects/coq/infotheo-itp infotheo \
  -w -notation-overridden -w -ambiguous-paths \
  -w -projection-no-head-constant -w -redundant-canonical-projection \
  -w -notation-incompatible-format \
  <file>
```

**File structure**

| File | Responsibility | Task |
|---|---|---|
| `smc/smc_interpreter.v` | trace packaging generalized to `data : Type` | 1 |
| `homomorphic_encryption/ahe_enc.v` | rewritable `Emul`/`Epow`-of-`enc` equations | 2 |
| `dumas2017dual/dsdp/infotheo_leg/dsdp_alice_trace_link.v` | encoding, staged run evaluation, trace RV, corollary chain | 3-6, 9, 10 |
| `dumas2017dual/dsdp/counting/dsdp_entropy_trace.v` | three-entry randomness correction | 7 |
| `~/Projects/phd-thesis/chapters/computational-privacy-dsdp.tex` | evidence anchor path + sidenote | 8 |

The leg file `dsdp_alice_infotheo_secrecy.v` is NOT edited.

---

### Task 1: Generalize the interpreter's trace packaging to `data : Type`

`Section traces` (`smc/smc_interpreter.v:224`) is over `Variable data :
eqType` only because `size_traces` is phrased with `\in`. At an abstract
`AHEncType` the interface carrier is not an eqType, so `interp_traces` is
unavailable. Verified: `size_traces`, `size_traces_nth` and `size_interp`
have **no** users outside this file (`smc_interpreter_refactoring.v` keeps
its own copies); `interp_traces` has two (`du2002/spp_program.v:143`,
`dumas2017dual/dsdp/core/dsdp_correctness.v:169`) and `interp_traces_ok` has
two (`du2002/spp_proof.v:120`, `dsdp_correctness.v:197`), all at eqTypes, so
a generalization subsumes them.

**Files:**
- Modify: `smc/smc_interpreter.v:224-328`

- [ ] **Step 1: change the section variable and add the two new size lemmas**

Replace line 225 `Variable data : eqType.` with `Variable data : Type.`, then
insert these two lemmas immediately after `Local Open Scope nat_scope.`
(bodies verbatim from `audit_typegeneric_traces.v:22-46`):

```coq
(* One step appends at most one datum to the party's trace. *)
Lemma step_size_le (ps : seq (proc data)) (tr : seq data) (i : nat) :
  size (step ps tr i).1.2 <= (size tr).+1.
Proof.
rewrite /step.
case: (nth _ ps i) => [d1 p1|dst1 d1 p1|frm1 f1|d1||] //=.
- by case: (nth _ ps dst1) => [? ?|? ? ?|? ?|?||] //=; case: ifP.
- by case: (nth _ ps frm1) => [? ?|? ? ?|? ?|?||] //=; case: ifP.
Qed.

(* Fuel bounds every party's trace length, stated by index instead of by
   membership, hence without an eqType on the data carrier. *)
Lemma size_interp_nth h (ps : seq (proc data)) (trs : seq (seq data)) k :
  (forall i, size (nth [::] trs i) <= k) ->
  forall i, size (nth [::] (interp h ps trs).2 i) <= k + h.
Proof.
elim: h k ps trs => [k ps trs Hk i|h IH k ps trs Hk i] /=;
  first by rewrite addn0.
case: ifP => _; last by apply: (leq_trans (Hk i)); rewrite leq_addr.
rewrite addnS -addSn; apply: IH => j.
rewrite /unzip2 /unzip1 -2!map_comp.
case: (ltnP j (size ps)) => Hj; last first.
  by rewrite nth_default // size_map size_iota.
rewrite (nth_map 0) ?size_iota // nth_iota // add0n /=.
apply: (leq_trans (step_size_le ps (nth [::] trs j) j)).
by rewrite ltnS; exact: Hk.
Qed.
```

- [ ] **Step 2: delete `size_traces` from this section and re-derive
  `size_traces_nth` index-wise**

Delete the old `size_traces` (lines 230-281, the `\in`-phrased lemma with the
long body) — it moves to Step 4. Keep `size_interp` exactly as it is (its
proof uses no equality). Replace the old `size_traces_nth` (lines 302-306)
with the nat-indexed version (body verbatim from
`audit_typegeneric_traces.v:48-53`):

```coq
(* Per-party fuel bound on trace length, supplying the size proof needed to
   package traces as bounded sequences. *)
Lemma size_traces_nth h (ps : seq (proc data)) (i : nat) :
  size (nth [::] (run_interp h ps).2 i) <= h.
Proof.
rewrite /run_interp -[h]add0n; apply: size_interp_nth => j.
by rewrite nth_nseq; case: ifP.
Qed.
```

`interp_traces` and `interp_traces_ok` keep their STATEMENTS unchanged, but
`interp_traces`'s body needs one edit (as built): the old
`(i : 'I_(size procs))` argument was the inference channel for `procs`, so
with a nat index the proc list must be spelled.

```coq
(* before *) [tuple Bseq (size_traces_nth h i) | i < size procs].
(* after  *) [tuple Bseq (size_traces_nth h procs i) | i < size procs].
```

`interp_traces_ok`'s body needs no change, so Step 3's fallback variant is
not used.

- [ ] **Step 3: compile**

Run the compile command on `smc/smc_interpreter.v`. Expected: exit 0.
If `interp_traces_ok`'s existing body breaks, replace it with the
probe-verified variant from `audit_typegeneric_traces.v:74-85`:

```coq
Lemma interp_traces_ok h (ps : seq (proc data)) :
  map val (interp_traces h ps) = (run_interp h ps).2.
Proof.
apply (eq_from_nth (x0:=[::])).
  rewrite size_map /= size_map size_enum_ord.
  by rewrite (size_interp _ _).2 ?size_nseq.
move=> i Hi.
rewrite size_map in Hi.
rewrite (nth_map [bseq]) // /interp_traces.
rewrite size_tuple in Hi.
by rewrite (_ : i = Ordinal Hi) // nth_mktuple.
Qed.
```

- [ ] **Step 4: restore `size_traces` as an eqType corollary**

Immediately after `End traces.`, add:

```coq
Section traces_eqType.
Variable data : eqType.
Local Open Scope nat_scope.

(* Membership form of [size_traces_nth]: every trace produced in h rounds has
   at most h entries. *)
Lemma size_traces h (procs : seq (proc data)) :
  forall s, s \in (run_interp h procs).2 -> size s <= h.
Proof. by move=> s /(nthP [::])[i _ <-]; exact: size_traces_nth. Qed.

End traces_eqType.
```

(As built: the bare `/nthP[i _ <-]` form fails with "Could not fill dependent
hole in apply"; the explicit default `[::]` is required.)

- [ ] **Step 5: compile the dependents (acceptance test)**

```bash
for f in smc/smc_session_types.v dumas2017dual/dsdp/core/dsdp_program.v \
         dumas2017dual/dsdp/core/dsdp_pismc.v \
         dumas2017dual/dsdp/core/dsdp_correctness.v \
         du2002/spp_program.v du2002/spp_proof.v \
         dumas2017dual/dsdp/infotheo_leg/dsdp_alice_infotheo_secrecy.v; do
  echo "== $f"; /Users/cheng-huiweng/Projects/coq/_opam/bin/coqc \
    -R /Users/cheng-huiweng/Projects/coq/infotheo-itp infotheo \
    -w -notation-overridden -w -ambiguous-paths \
    -w -projection-no-head-constant -w -redundant-canonical-projection \
    -w -notation-incompatible-format "$f" || break; done
```

Expected: every file exits 0.

- [ ] **Step 6: commit**

```bash
git add smc/smc_interpreter.v
git commit --no-verify -m "smc interpreter: generalize trace packaging to Type" \
  -- smc/smc_interpreter.v
```

### Task 2: Rewritable `Emul`/`Epow`-of-`enc` equations

**Files:**
- Modify: `homomorphic_encryption/ahe_enc.v` (append after
  `HB.structure Definition AHEnc`, around line 104)

- [ ] **Step 1: add the two lemmas** (bodies verbatim from
  `probe_trace_link.v:318-328`)

```coq
Section ahe_enc_lemmas.
Variable AHE : AHEncType.

(* Raising a ciphertext to a plaintext power encrypts the product, with the
   randomness raised to the same power. *)
Lemma Epow_encE (k : pub_key AHE) (m j : plain AHE) (r : rand AHE) :
  Epow (enc k m r) j = enc k (m * j) (rand_pow r j).
Proof. exact: (esym (Epow_scalarM k j (m, r))). Qed.

(* Multiplying two ciphertexts under one key encrypts the sum, with the
   randomness multiplied. *)
Lemma Emul_encE (k : pub_key AHE) (m1 m2 : plain AHE) (r1 r2 : rand AHE) :
  Emul (enc k m1 r1) (enc k m2 r2) = enc k (m1 + m2) (rand_mul r1 r2).
Proof. exact: (esym (Emul_addM k (m1, r1) (m2, r2))). Qed.

End ahe_enc_lemmas.
```

- [ ] **Step 2: compile** `homomorphic_encryption/ahe_enc.v`, then
  `homomorphic_encryption/homomorphic_encryption.v`. Expected: exit 0 for
  both.

- [ ] **Step 3: commit**

```bash
git add homomorphic_encryption/ahe_enc.v
git commit --no-verify -m "ahe: rewritable Emul/Epow-of-enc equations" \
  -- homomorphic_encryption/ahe_enc.v
```

### Task 2b: Projection-form fuel splitting

Task 4's staged evaluation needs the fuel-splitting equation in projection
form; `interpD`'s `let`-destructuring conclusion blocks the staging (Task 4
Step 2 explains why). Derive the projection form once, next to `interpD`,
rather than restating the probe's copy: same fact, one-line proof, correct
dependency direction (`interpD` lives downstream of `interp`).

**Files:**
- Modify: `smc/smc_session_types.v` (immediately after `interpD`, line ~878)

- [ ] **Step 1: add the corollary**

```coq
(* Projection form of [interpD]: splitting the fuel exposes the intermediate
   process and trace lists as projections, so an abstracted intermediate run
   still matches the shape of the next split. *)
Lemma interp_fuelD h1 h2 (ps : seq (proc data)) traces :
  interp (h1 + h2) ps traces
  = interp h2 (interp h1 ps traces).1 (interp h1 ps traces).2.
Proof. by rewrite interpD; case: (interp h1 ps traces). Qed.
```

If `case:` leaves a pair-eta goal, use
`by rewrite interpD; case: (interp h1 ps traces) => ps' trs'.`

- [ ] **Step 2: compile** `smc/smc_session_types.v`. Expected: exit 0.

- [ ] **Step 3: commit**

```bash
git add smc/smc_session_types.v
git commit --no-verify -m "smc session types: projection-form fuel splitting" \
  -- smc/smc_session_types.v
```

### Task 3: New file scaffold, parameters, and the finite trace encoding

**Files:**
- Create:
  `dumas2017dual/dsdp/infotheo_leg/dsdp_alice_trace_link.v`
- Modify: `_CoqProject` (add the path right after
  `dumas2017dual/dsdp/infotheo_leg/dsdp_alice_infotheo_secrecy.v`)

- [ ] **Step 1: create the file** with this content (the `(**md ... *)`
  header table is completed in Task 10):

```coq
(**md**************************************************************************)
(* # DSDP corrupted-Alice secrecy at the executed piSMC trace                 *)
(*                                                                            *)
(* Documentation table completed in the final task.                           *)
(******************************************************************************)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import ring boolp finmap matrix lra reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.
Require Import smc_interpreter smc_session_types.
Require Import homomorphic_encryption dsdp_interface dsdp_program dsdp_pismc.
Require Import dsdp_alice_infotheo_secrecy.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

Section dsdp_alice_trace_link.
Context {R : realType}.
Variables (AHE : AHEncType) (Renc : finType) (index_renc : nat).
Hypothesis card_renc : #|Renc| = index_renc.+1.
Variable rand_of_renc : Renc -> rand AHE.
Variables (t_cipher : finType)
          (chcipher_of_cipher : cipher AHE -> t_cipher)
          (cipher_of_chcipher : t_cipher -> cipher AHE).
Hypothesis chcipher_of_cipherK :
  cancel chcipher_of_cipher cipher_of_chcipher.
Variables (w_v1 w_u1 w_u2 w_u3 : plain AHE).
Hypothesis w_u3_inj : injective (fun v : plain AHE => w_u3 * v).
Variables (dk_a dk_b dk_c : priv_key AHE).
Variables (w_rb2 w_rc2 : Renc).

(* Every party's public key is the one associated with its private key, so
   [dec_correct] fires by conversion and no key hypothesis is needed. *)
Definition pkey_of_dk (p : party_id) : pub_key AHE :=
  match p with
  | Alice => pub_of_priv dk_a
  | Bob => pub_of_priv dk_b
  | Charlie => pub_of_priv dk_c
  | NoParty => pub_of_priv dk_a
  end.

End dsdp_alice_trace_link.
```

- [ ] **Step 2: add the finite encoding** inside the section, before `End`:

```coq
Let DI := Standard_DSDP_Interface AHE.

(* The finite image of the interpreter's data carrier: plaintexts kept,
   ciphertexts marshalled, both key sorts erased to marks.  Summand order
   mirrors [std_data]'s msgT + encT + privT + pubT. *)
Definition dsdp_trace_dataT : finType :=
  ((plain AHE + t_cipher) + unit + unit)%type.

Definition trace_data_of_di_data (x : di_data DI) : dsdp_trace_dataT :=
  match x with
  | inl (inl (inl m)) => inl (inl (inl m))
  | inl (inl (inr c)) => inl (inl (inr (chcipher_of_cipher c)))
  | inl (inr _) => inl (inr tt)
  | inr _ => inr tt
  end.
```

- [ ] **Step 3: add the program alias** (resolves the duplicate-definition
  hazard: `palice`/`dsdp_procs` exist in both `dsdp_program.v` and
  `dsdp_pismc.v`, and only the latter routes party tags through
  `nat_to_party_id`):

```coq
(* The single qualified reference in this file: the piSMC programs, not the
   same-named ones of dsdp_program.v. *)
Let decode : di_priv_keyT DI -> di_cipherT DI -> option (di_msgT DI) :=
  @dec AHE.
```

(The proc list itself is built in Task 4, where its arguments are in scope.)

- [ ] **Step 4: add to `_CoqProject`**, compile the new file. Expected:
  exit 0.

- [ ] **Step 5: commit**

```bash
git add dumas2017dual/dsdp/infotheo_leg/dsdp_alice_trace_link.v _CoqProject
git commit --no-verify -m "dsdp trace link: scaffold and finite trace encoding" \
  -- dumas2017dual/dsdp/infotheo_leg/dsdp_alice_trace_link.v _CoqProject
```

### Task 4: The staged run evaluation

This is the only substantial new proof. Two layers, both copied from
`probe_trace_link.v`: a generic run over an interface whose crypto
operations are section variables (so `vm_compute` keeps them atomic), then
the instantiation at the real AHE.

**Files:**
- Modify: `dumas2017dual/dsdp/infotheo_leg/dsdp_alice_trace_link.v`

- [ ] **Step 1: the generic interface and its run.** Insert a section
  BEFORE `Section dsdp_alice_trace_link` (it is protocol-generic). Copy
  `probe_trace_link.v:125-243` verbatim, renaming `probe_DI` to
  `DSDP_Interface_of_ops`, `probe_interp_addN` to nothing (see Step 2), and
  `probe_gtraces` to `dsdp_run_traces_of_ops_ok`. The section's variables,
  the four `Local Notation` ciphertext abbreviations, the three `Hypothesis`
  decryption facts, the three `Let` program instances, `gsaprocs`, `gprocs`
  and the `Arguments gprocs : clear implicits.` line all carry over
  unchanged.

- [ ] **Step 2: use `interp_fuelD` from Task 2b.** The probe declared its own
  `probe_interp_addN`; do NOT copy it, and do NOT use `interpD` directly.
  `interpD` (`smc/smc_session_types.v:872`) concludes with a
  `let (ps', traces') := interp h1 ps traces in ...` destructuring, which does
  not iota-reduce once the inner run is abstracted to an opaque `S`, so the
  goal never exposes `S.1`/`S.2` and the next stage's `move Ht2: (interp 2
  S.1 S.2) => S2` would abstract a term absent from the goal. Task 2b derives
  the projection form `interp_fuelD` from `interpD` in one line; use it.

- [ ] **Step 3: the staged proof** (body from `probe_trace_link.v:210-231`
  with `probe_interp_addN` -> `interpD`; keep every `%N`, since `ring_scope`
  is open and a bare `+` on the fuel would elaborate to `GRing.add`):

```coq
Lemma dsdp_run_traces_of_ops_ok :
  (run_interp 15 gprocs).2 =
  [:: [:: gdp (gadd (gsub (gsub gm1 gr2) gr3) (gmul gu1 gv1));
          gde gCa;
          gde (genc (gek Charlie) gv3 grc1);
          gde (genc (gek Bob) gv2 grb1);
          gdp gr3; gdp gr2; gdp gu3; gdp gu2; gdp gu1; gdp gv1; gdk gdka];
      [:: gde gCc3; gde gCb; gdp gv2; gdk gdkb];
      [:: gde gCc; gdp gv3; gdk gdkc]].
Proof.
rewrite /run_interp.
have -> : (15 = 10 + 5)%N by [].
rewrite interp_fuelD.
move Ht: (interp 10 gprocs (nseq (size gprocs) [::])) => S.
vm_compute in Ht.
rewrite Hgb in Ht.
have -> : (5 = 2 + 3)%N by [].
rewrite interp_fuelD.
move Ht2: (interp 2 S.1 S.2) => S2.
rewrite -Ht in Ht2.
vm_compute in Ht2.
rewrite Hgc in Ht2.
have -> : (3 = 1 + 2)%N by [].
rewrite interp_fuelD.
move Ht3: (interp 1 S2.1 S2.2) => S3.
rewrite -Ht2 in Ht3.
vm_compute in Ht3.
rewrite Hga in Ht3.
rewrite -Ht3.
by vm_compute.
Qed.
```

Two traps: `move Ht: t => S` yields `Ht : t = S`, so pushing the value
forward needs `rewrite -Ht in Ht2` (with the minus); and do not unfold
`gprocs` beforehand or the `move Ht:` pattern becomes unwritable. Never
abstract a fuel numeral — `5` occurs inside `10` and `14`; abstract the
interpreter state, as above.

- [ ] **Step 4: compile.** Expected: exit 0. `vm_compute` stages can take
  tens of seconds; that is normal.

- [ ] **Step 5: the three decryption facts and the real-AHE
  instantiation** (verbatim from `probe_trace_link.v:356-443`, with `ek`
  replaced by this file's `pkey_of_dk`, `probe_Epow_encE`/`probe_Emul_encE`
  replaced by Task 2's `Epow_encE`/`Emul_encE`, and `rb2`/`rc2` replaced by
  `rand_of_renc w_rb2` / `rand_of_renc w_rc2`):

```coq
Variables (v2 v3 r2 r3 : plain AHE) (rb1 rc1 ra1 ra2 : rand AHE).

Let d := di_data_of_plain DI.
Let e := di_data_of_cipher DI.
Let kd := di_data_of_priv_key DI.

Let palice_inst :=
  @palice DI decode pkey_of_dk dk_a w_v1 w_u1 w_u2 w_u3 r2 r3 ra1 ra2.
Let pbob_inst := @pbob DI decode pkey_of_dk dk_b v2 rb1 (rand_of_renc w_rb2).
Let pcharlie_inst :=
  @pcharlie DI decode pkey_of_dk dk_c v3 rc1 (rand_of_renc w_rc2).

Definition dsdp_procs_std : seq (proc (di_data DI)) :=
  erase_aprocs [aprocs palice_inst ; pbob_inst ; pcharlie_inst].

Let M2 : plain AHE := v2 * w_u2 + r2.
Let M3 : plain AHE := v3 * w_u3 + r3 + (v2 * w_u2 + r2).

(* Bob opens Alice's first combine. *)
Lemma dec_combine_bob :
  dec dk_b (Emul (Epow (enc (pkey_of_dk Bob) v2 rb1) w_u2)
                 (enc (pkey_of_dk Bob) r2 ra1)) = Some M2.
Proof. by rewrite Epow_encE Emul_encE dec_correct. Qed.

(* Charlie opens Bob's forward. *)
Lemma dec_forward_charlie :
  dec dk_c (Emul (Emul (Epow (enc (pkey_of_dk Charlie) v3 rc1) w_u3)
                       (enc (pkey_of_dk Charlie) r3 ra2))
                 (enc (pkey_of_dk Charlie) M2 (rand_of_renc w_rb2)))
  = Some M3.
Proof. by rewrite Epow_encE !Emul_encE dec_correct. Qed.

(* Alice opens Charlie's re-encryption. *)
Lemma dec_recrypt_alice :
  dec dk_a (enc (pkey_of_dk Alice) M3 (rand_of_renc w_rc2)) = Some M3.
Proof. exact: dec_correct. Qed.
```

- [ ] **Step 6: the evaluation lemma at the real scheme** (statement from
  `probe_trace_link.v:401-415`, proof from `:417-422`, with the same
  substitutions; `real_procs` is dropped in favour of the `gprocs`
  instantiation because in this repo `real` names a game arm):

```coq
Let procs_of_ops :=
  gprocs (plain AHE) (cipher AHE) (rand AHE) (priv_key AHE) (pub_key AHE)
         (@enc AHE) (@Emul AHE) (@Epow AHE)
         +%R (fun a b : plain AHE => a - b) *%R (@dec AHE)
         dk_a dk_b dk_c pkey_of_dk
         w_v1 v2 v3 w_u1 w_u2 w_u3 r2 r3
         rb1 (rand_of_renc w_rb2) rc1 (rand_of_renc w_rc2) ra1 ra2.

(* The abstract instance at the standard interface IS the standard
   instance. *)
Lemma dsdp_procs_stdE : dsdp_procs_std = procs_of_ops.
Proof. by []. Qed.

Lemma dsdp_run_traces_ok :
  (run_interp 15 dsdp_procs_std).2 =
  [:: [:: d (v3 * w_u3 + r3 + (v2 * w_u2 + r2) - r2 - r3 + w_u1 * w_v1);
          e (enc (pkey_of_dk Alice)
                 (v3 * w_u3 + r3 + (v2 * w_u2 + r2)) (rand_of_renc w_rc2));
          e (enc (pkey_of_dk Charlie) v3 rc1);
          e (enc (pkey_of_dk Bob) v2 rb1);
          d r3; d r2; d w_u3; d w_u2; d w_u1; d w_v1; kd dk_a];
      [:: e (Emul (Epow (enc (pkey_of_dk Charlie) v3 rc1) w_u3)
                  (enc (pkey_of_dk Charlie) r3 ra2));
          e (Emul (Epow (enc (pkey_of_dk Bob) v2 rb1) w_u2)
                  (enc (pkey_of_dk Bob) r2 ra1));
          d v2; kd dk_b];
      [:: e (Emul (Emul (Epow (enc (pkey_of_dk Charlie) v3 rc1) w_u3)
                        (enc (pkey_of_dk Charlie) r3 ra2))
                  (enc (pkey_of_dk Charlie) (v2 * w_u2 + r2)
                       (rand_of_renc w_rb2)));
          d v3; kd dk_c]].
Proof.
rewrite dsdp_procs_stdE /procs_of_ops.
apply: dsdp_run_traces_of_ops_ok.
- exact: dec_combine_bob.
- exact: dec_forward_charlie.
- exact: dec_recrypt_alice.
Qed.
```

- [ ] **Step 7: the single-encryption form of the run.** `dsdp_run_traces_ok`
  leaves Bob's and Charlie's entries in homomorphic form (`Emul`/`Epow`).
  Task 7 needs the normalized form, where every wire value is one `enc` whose
  randomness is the homomorphic combination of its arguments' randomness, so
  state it here as the citable ground truth (statement from
  `probe_trace_link.v:427-440`, proof from `:442`):

```coq
(* The same traces with every ciphertext normalised to a single encryption:
   a combine's randomness is the homomorphic combination of the randomness of
   its arguments. *)
Lemma dsdp_run_traces_encE :
  (run_interp 15 dsdp_procs_std).2 =
  [:: [:: d (v3 * w_u3 + r3 + (v2 * w_u2 + r2) - r2 - r3 + w_u1 * w_v1);
          e (enc (pkey_of_dk Alice)
                 (v3 * w_u3 + r3 + (v2 * w_u2 + r2)) (rand_of_renc w_rc2));
          e (enc (pkey_of_dk Charlie) v3 rc1);
          e (enc (pkey_of_dk Bob) v2 rb1);
          d r3; d r2; d w_u3; d w_u2; d w_u1; d w_v1; kd dk_a];
      [:: e (enc (pkey_of_dk Charlie) (v3 * w_u3 + r3)
                 (rand_mul (rand_pow rc1 w_u3) ra2));
          e (enc (pkey_of_dk Bob) (v2 * w_u2 + r2)
                 (rand_mul (rand_pow rb1 w_u2) ra1));
          d v2; kd dk_b];
      [:: e (enc (pkey_of_dk Charlie) (v3 * w_u3 + r3 + (v2 * w_u2 + r2))
                 (rand_mul (rand_mul (rand_pow rc1 w_u3) ra2)
                           (rand_of_renc w_rb2)));
          d v3; kd dk_c]].
Proof. by rewrite dsdp_run_traces_ok !Epow_encE !Emul_encE. Qed.
```

- [ ] **Step 8: compile, then commit**

```bash
git add dumas2017dual/dsdp/infotheo_leg/dsdp_alice_trace_link.v
git commit --no-verify -m "dsdp trace link: staged run evaluation at abstract AHE" \
  -- dumas2017dual/dsdp/infotheo_leg/dsdp_alice_trace_link.v
```

### Task 5: Trace RV and the view-function bridge

**Files:**
- Modify: `dumas2017dual/dsdp/infotheo_leg/dsdp_alice_trace_link.v`

**Placement (verified, blocking if ignored):** `v2 v3 r2 r3 rb1 rc1 ra1 ra2`
are `Variables` of `Section dsdp_alice_trace_link`, so nothing inside that
section can instantiate them at `V2 s`, `R2 s`, ... Everything in this task
and Task 6 goes AFTER `End dsdp_alice_trace_link.`, in a new
`Section dsdp_alice_trace_rv` that re-declares the parameters it needs,
mirroring the probe's own split. Precede it with
`Arguments dsdp_procs_std : clear implicits.` so the per-sample application
is positional. As discharged, `dsdp_procs_std` takes `[AHE Renc]` implicit
then 18 explicit arguments in the order
`rand_of_renc w_v1 w_u1 w_u2 w_u3 dk_a dk_b dk_c w_rb2 w_rc2 v2 v3 r2 r3
rb1 rc1 ra1 ra2`; `dsdp_run_traces_ok` takes the same 18 and unifies them
from the goal, so a bare `rewrite dsdp_run_traces_ok` works once
`dsdp_procs_of_sample` is unfolded.

- [ ] **Step 1: the trace read off a view value** (verbatim from
  `audit_corollary_route.v:58-70`, with `dataF` renamed to
  `dsdp_trace_dataT` and `w_rc2` passed through `rand_of_renc`; the view
  projections are `v.1.1.2 = Sout`, `v.1.1.1.1.1 = r2`,
  `v.1.1.1.1.2 = r3`, `v.1.2 = Bob-key cipher`, `v.2 = Charlie-key cipher`):

```coq
(* Alice's executed trace read off a value of her reduced view: the leaked
   output, Charlie's re-encryption of it, the two received ciphertexts, the
   two masks, the four weights, and the erased key mark. *)
Definition dsdp_trace_of_view (v : dsdp_alice_viewT AHE Renc t_cipher) :
    15.-bseq dsdp_trace_dataT :=
  [bseq inl (inl (inl v.1.1.2));
        inl (inl (inr (chcipher_of_cipher
          (enc (pkey_of_dk Alice)
               (v.1.1.2 - w_u1 * w_v1 + v.1.1.1.1.1 + v.1.1.1.1.2)
               (rand_of_renc w_rc2)))));
        inl (inl (inr v.2));
        inl (inl (inr v.1.2));
        inl (inl (inl v.1.1.1.1.2));
        inl (inl (inl v.1.1.1.1.1));
        inl (inl (inl w_u3)); inl (inl (inl w_u2));
        inl (inl (inl w_u1)); inl (inl (inl w_v1));
        inl (inr tt)].
```

- [ ] **Step 2: the trace random variable from the interpreter.** Build the
  sample-indexed program list and take the encoded Alice component of the
  tuple `interp_traces` now provides (Task 1 made it available at
  `data : Type`):

```coq
Definition dsdp_procs_of_sample (s : dsdp_alice_sampleT AHE Renc) :
  seq (proc (di_data DI)) :=
  (* dsdp_procs_std at v2 := V2 s, v3 := V3 s, r2 := R2 s, r3 := R3 s,
     rb1 := rand_of_renc (Rho2 s), rc1 := rand_of_renc (Rho3 s),
     ra1 := rand_of_renc (RA1 s), ra2 := rand_of_renc (RA2 s) *)

(* Fuel bounds the encoded trace, since encoding preserves length. *)
Let size_alice_trace (s : dsdp_alice_sampleT AHE Renc) :
  size (map trace_data_of_di_data
          (nth [::] (run_interp 15 (dsdp_procs_of_sample s)).2 0)) <= 15.
Proof. by rewrite size_map; exact: size_traces_nth. Qed.

Definition AliceTrace :
    {RV (alice_sample_fdist AHE card_renc) -> 15.-bseq dsdp_trace_dataT} :=
  fun s => Bseq (size_alice_trace s).
```

Construction decided (no alternatives to weigh at implementation time): map
the encoder over the seq-level projection and build the `Bseq` in one step
from `size_map` plus Task 1's nat-indexed `size_traces_nth`. This needs no
`'I_(size ...)` obligation, and it needs no general `bseq_map` helper — none
exists in mathcomp (`tuple.v` offers only `insub_bseq`, `in_bseq`,
`cast_bseq`, `widen_bseq`) nor in `lib/ssr_ext.v` (whose `Section
bseq_lemmas` has `bseq_take` over a single type variable), and adding one for
a single call site would be dead generality.

- [ ] **Step 3: the two ring identities the bridge needs.** `AliceTrace`'s
  entries come out of `dsdp_run_traces_ok` in *run* form, while
  `dsdp_trace_of_view` is necessarily in *view* form — the view carries
  `Sout` but not `v2`/`v3`, so a run-form statement could not be a function
  of the view at all. The gap at entries 0 and 1 is a ring identity, not
  conversion, and `by []` does not close it (compile-verified). Name the two
  identities so the bridge is one rewrite chain:

```coq
(* The leaked output the run computes is Alice's view slot. *)
Let Sout_runE (s : dsdp_alice_sampleT AHE Renc) :
  V3 s * w_u3 + R3 s + (V2 s * w_u2 + R2 s) - R2 s - R3 s + w_u1 * w_v1
  = Sout s.
Proof. by rewrite /Sout /comp_RV /dsdp_output /=; ring. Qed.

(* The plaintext Charlie re-encrypts is the leaked output net of Alice's own
   term and masks. *)
Let recrypt_plainE (s : dsdp_alice_sampleT AHE Renc) :
  V3 s * w_u3 + R3 s + (V2 s * w_u2 + R2 s)
  = Sout s - w_u1 * w_v1 + R2 s + R3 s.
Proof. by rewrite /Sout /comp_RV /dsdp_output /=; ring. Qed.
```

`` `o `` unfolds only with `/comp_RV` (not `/=`, not `/comp`).

- [ ] **Step 4: the bridge lemma** — the payload of the whole task:

```coq
(* The trace the interpreter produces for Alice is the deterministic image of
   her reduced view. *)
Lemma dsdp_trace_of_viewE :
  AliceTrace = dsdp_trace_of_view `o AliceView.
Proof.
apply: boolp.funext => s; apply/val_inj.
by rewrite /AliceTrace /dsdp_procs_of_sample dsdp_run_traces_ok
           Sout_runE recrypt_plainE.
Qed.
```

`recrypt_plainE` rewrites under `chcipher_of_cipher (enc _ _ _)`, which
`rewrite` reaches without a `congr`. If a residual entry remains, it is a
`map`/`take` normalisation: append `/trace_data_of_di_data /=`.

- [ ] **Step 4: compile, then commit**

```bash
git add dumas2017dual/dsdp/infotheo_leg/dsdp_alice_trace_link.v
git commit --no-verify -m "dsdp trace link: trace random variable and view bridge" \
  -- dumas2017dual/dsdp/infotheo_leg/dsdp_alice_trace_link.v
```

### Task 6: The corollary chain and the trace headline

Every lemma here is compiled in `audit_corollary_route.v`; copy the bodies
verbatim and replace that file's `Hypothesis Halice_trace` with Task 5's
`dsdp_trace_of_viewE`.

**Files:**
- Modify: `dumas2017dual/dsdp/infotheo_leg/dsdp_alice_trace_link.v`

- [ ] **Step 1: the ladder and the distinguisher lift** (from
  `audit_corollary_route.v:73-80`):

```coq
(* The trace ladder: the leg's view ladder read as a trace. *)
Definition AliceTrace_zero_prefix (i : nat) :
    {RV (alice_sample_fdist AHE card_renc) -> 15.-bseq dsdp_trace_dataT} :=
  dsdp_trace_of_view \o AliceView_zero_prefix i.
Notation AliceTrace_all_zero := (AliceTrace_zero_prefix 2).

(* A trace-level distinguisher read as a view-level one. *)
Definition distinguisher_of_trace
    (D : plain AHE * plain AHE * 15.-bseq dsdp_trace_dataT -> bool) :
    plain AHE * plain AHE * dsdp_alice_viewT AHE Renc t_cipher -> bool :=
  fun y => D (y.1.1, y.1.2, dsdp_trace_of_view y.2).
```

- [ ] **Step 2: the `Pr`-preimage bridge** (body verbatim from
  `audit_corollary_route.v:88-97`):

```coq
(* A trace-level distinguishing probability is the view-level distinguishing
   probability of the lifted distinguisher. *)
Lemma trace_joint_PrE (i : nat)
    (D : plain AHE * plain AHE * 15.-bseq dsdp_trace_dataT -> bool) :
  Pr (`p_ [% V2, V3, AliceTrace_zero_prefix i]) [set x | D x]
  = Pr (`p_ [% V2, V3, AliceView_zero_prefix i])
       [set y | distinguisher_of_trace D y].
Proof.
rewrite /dist_of_RV.
have -> : ([% V2, V3, AliceTrace_zero_prefix i]
             : {RV _ -> (plain AHE * plain AHE * 15.-bseq dsdp_trace_dataT)%type})
        = (fun y => (y.1.1, y.1.2, dsdp_trace_of_view y.2))
            \o [% V2, V3, AliceView_zero_prefix i] by [].
rewrite -fdistmap_comp Pr_fdistmap_pre.
by apply: eq_bigl => t; rewrite !inE.
Qed.
```

- [ ] **Step 3: the two hop equalities** (bodies verbatim from
  `audit_corollary_route.v:109` and `:120` — one line each):

```coq
(* Zeroing the Bob-key entry of the trace moves the distinguishing
   probability by the advantage of one explicit reduction against Bob's
   key. *)
Lemma hop0_trace_advantageE
    (D : plain AHE * plain AHE * 15.-bseq dsdp_trace_dataT -> bool) :
  `| Pr (`p_ [% V2, V3, AliceTrace_zero_prefix 0]) [set x | D x]
     - Pr (`p_ [% V2, V3, AliceTrace_zero_prefix 1]) [set x | D x] |
  = indcpa_fdist_epsilon (pkey_of_dk Bob)
      (hop0_reduction (distinguisher_of_trace D)).
Proof. by rewrite !trace_joint_PrE; exact: hop0_advantageE. Qed.

(* Zeroing the Charlie-key entry does the same against Charlie's key. *)
Lemma hop1_trace_advantageE
    (D : plain AHE * plain AHE * 15.-bseq dsdp_trace_dataT -> bool) :
  `| Pr (`p_ [% V2, V3, AliceTrace_zero_prefix 1]) [set x | D x]
     - Pr (`p_ [% V2, V3, AliceTrace_zero_prefix 2]) [set x | D x] |
  = indcpa_fdist_epsilon (pkey_of_dk Charlie)
      (hop1_reduction (distinguisher_of_trace D)).
Proof. by rewrite !trace_joint_PrE; exact: hop1_advantageE. Qed.
```

The leg's `hop0_reduction`/`hop1_reduction`/`indcpa_fdist_epsilon` take the
section arguments explicitly; spell them as `audit_corollary_route.v:105-108`
does if inference fails.

- [ ] **Step 4: the endpoint** (body verbatim from
  `audit_corollary_route.v:128-130`):

```coq
(* A predictor reading the all-zero trace matches Bob's input with
   probability at most one over the plaintext-space cardinality. *)
Lemma guess_trace_all_zero_le_invm
    (g : 15.-bseq dsdp_trace_dataT -> plain AHE) :
  Pr (alice_sample_fdist AHE card_renc)
     [set t | (g `o AliceTrace_all_zero) t == V2 t]
    <= (#|plain AHE|%:R : R)^-1.
Proof.
rewrite /AliceTrace_zero_prefix.
exact: (guess_all_zero_le_invm w_u3_inj (g \o dsdp_trace_of_view)).
Qed.
```

- [ ] **Step 5: the headline** (body from `audit_corollary_route.v:154-157`,
  with `Halice_trace` replaced by `dsdp_trace_of_viewE`):

```coq
(* Every predictor reading the trace the interpreter produces for Alice
   matches Bob's input with probability at most one over the plaintext-space
   cardinality plus the real-or-zero advantages of the two per-hop
   reductions. *)
Theorem dsdp_alice_guess_fdist_trace_V2_real_le
    (g : 15.-bseq dsdp_trace_dataT -> plain AHE) :
  Pr (alice_sample_fdist AHE card_renc)
     [set t | (g `o AliceTrace) t == V2 t]
    <= (#|plain AHE|%:R : R)^-1
       + indcpa_fdist_epsilon (pkey_of_dk Bob)
           (hop0_reduction
              (distinguisher_of_guess (g \o dsdp_trace_of_view)))
       + indcpa_fdist_epsilon (pkey_of_dk Charlie)
           (hop1_reduction
              (distinguisher_of_guess (g \o dsdp_trace_of_view))).
Proof.
rewrite dsdp_trace_of_viewE.
exact: (dsdp_alice_guess_fdist_V2_real_le w_u3_inj (g \o dsdp_trace_of_view)).
Qed.
```

- [ ] **Step 6: axiom check.** Write a scratch file in the scratchpad
  requiring this file and running
  `Print Assumptions dsdp_alice_guess_fdist_trace_V2_real_le.` Expected:
  exactly `propositional_extensionality`,
  `functional_extensionality_dep`, `constructive_indefinite_description`.

- [ ] **Step 7: compile, then commit**

```bash
git add dumas2017dual/dsdp/infotheo_leg/dsdp_alice_trace_link.v
git commit --no-verify -m "dsdp trace link: trace-level guess headline" \
  -- dumas2017dual/dsdp/infotheo_leg/dsdp_alice_trace_link.v
```

### Task 7: Correct the hand-written trace literal

`dsdp_entropy_trace.v:92-101` names a single randomness in three entries
where the interpreter produces a homomorphic combination, and one of them is
attributed to the wrong party. Ground truth is Task 4's
`dsdp_run_traces_ok`.

**Files:**
- Modify: `dumas2017dual/dsdp/counting/dsdp_entropy_trace.v:92-101`

- [ ] **Step 1: replace the three randomness arguments**

In the second `bseq` (Bob's trace), change
`e (E charlie (v3 * u3 + r3) rb2)` to
`e (E charlie (v3 * u3 + r3) (rand_mul (rand_pow rc1 u3) ra2))`
and `e (E bob (v2 * u2 + r2) ra1)` to
`e (E bob (v2 * u2 + r2) (rand_mul (rand_pow rb1 u2) ra1))`.
In the third `bseq` (Charlie's trace), change
`e (E charlie (v3 * u3 + r3 + (v2 * u2 + r2)) rb2)` to
`e (E charlie (v3 * u3 + r3 + (v2 * u2 + r2))
     (rand_mul (rand_mul (rand_pow rc1 u3) ra2) rb2))`.

- [ ] **Step 2: add a source comment above the definition** recording the
  provenance (non-rendered, so it may carry the rationale). Cite the
  single-encryption form, not the homomorphic one — `dsdp_run_traces_ok`
  leaves Bob's and Charlie's entries as `Emul`/`Epow` applications, and it is
  `dsdp_run_traces_encE` (Task 4 Step 7) that exhibits the randomness
  arguments installed here:

```coq
(* Randomness arguments follow the executed run: a combine's randomness is
   the homomorphic combination of its arguments' randomness, per
   [dsdp_run_traces_encE] of dsdp_alice_trace_link.v.  Bob's Charlie-key
   entry carries Alice's second combine, whose randomness derives from
   Charlie's rc1 and Alice's ra2, not from Bob's rb2. *)
```

- [ ] **Step 3: compile** `dumas2017dual/dsdp/counting/dsdp_entropy_trace.v`.
  Expected: exit 0 (no `.v` file consumes `dsdp_traces`; `dsdp_result_correct`
  is a standalone `ring` identity that does not mention it).

- [ ] **Step 4: commit**

```bash
git add dumas2017dual/dsdp/counting/dsdp_entropy_trace.v
git commit --no-verify -m "dsdp: correct the trace literal's randomness arguments" \
  -- dumas2017dual/dsdp/counting/dsdp_entropy_trace.v
```

### Task 8: Fix the thesis evidence anchor

`~/Projects/phd-thesis/chapters/computational-privacy-dsdp.tex:841-842`
anchors "the interpreter run on the three piSMC programs, the lifting of the
resulting traces to random variables" on `\coqin{dsdp_traces}` in
`\coqin{dsdp/dsdp_entropy_trace.v}` — a hand-written literal, at a stale
path.

**Files:**
- Modify: `~/Projects/phd-thesis/chapters/computational-privacy-dsdp.tex:841-842`

- [ ] **Step 1: read the sidenote** to see its exact wording:
  `sed -n '835,850p' ~/Projects/phd-thesis/chapters/computational-privacy-dsdp.tex`

- [ ] **Step 2: re-point it** at the evaluation lemma and fix the path:
  replace `\coqin{dsdp_traces}` with `\coqin{dsdp_run_traces_ok}` and
  `\coqin{dsdp/dsdp_entropy_trace.v}` with
  `\coqin{dsdp/infotheo_leg/dsdp_alice_trace_link.v}`, and make the prose say
  that the interpreter's traces are evaluated there and shown to be the
  deterministic image of Alice's view, with the trace-level bound
  `\coqin{dsdp_alice_guess_fdist_trace_V2_real_le}`.

- [ ] **Step 3: build the thesis** with the project's real command (per the
  repo convention, `latexmk -halt-on-error`, run in the thesis root) and
  confirm no new warnings about undefined references.

- [ ] **Step 4: commit in the thesis repo**

```bash
cd ~/Projects/phd-thesis && git add chapters/computational-privacy-dsdp.tex \
  && git commit -m "dsdp: anchor the trace claim on the evaluation lemma"
```

### Task 9: Golf pass

**Files:**
- Modify: `dumas2017dual/dsdp/infotheo_leg/dsdp_alice_trace_link.v`

- [ ] **Step 1: golf proof bodies only.** Never a statement, an identifier,
  a statement comment, or the header table. Prime target is Task 4's staged
  proof — but note the `move Ht:` / `vm_compute in Ht` staging is
  load-bearing and must not be collapsed; golf the surrounding bookkeeping
  only.

- [ ] **Step 2: re-verify** — full compile exit 0;
  `grep -cE "Admitted|Abort|^Axiom"` = 0; `awk 'length > 80'` empty;
  `Print Assumptions dsdp_alice_guess_fdist_trace_V2_real_le` unchanged
  (boolp trio only).

- [ ] **Step 3: commit**

```bash
git add dumas2017dual/dsdp/infotheo_leg/dsdp_alice_trace_link.v
git commit --no-verify -m "dsdp trace link: golf proof bodies" \
  -- dumas2017dual/dsdp/infotheo_leg/dsdp_alice_trace_link.v
```

### Task 10: Header, style pass, final audit commit

**Files:**
- Modify: `dumas2017dual/dsdp/infotheo_leg/dsdp_alice_trace_link.v`

- [ ] **Step 1: complete the `(**md ... *)` header.** 80-column padded
  frame; `# Title`; purpose paragraph; a `Headline results:` paragraph naming
  `dsdp_run_traces_ok` and `dsdp_alice_guess_fdist_trace_V2_real_le`; a
  triple-backtick `==`-aligned table with one declarative sentence per public
  definition (`dsdp_trace_dataT`, `trace_data_of_di_data`,
  `DSDP_Interface_of_ops`, `gprocs`, `dsdp_run_traces_of_ops_ok`,
  `dsdp_procs_std`, `dsdp_procs_stdE`, `dec_combine_bob`,
  `dec_forward_charlie`, `dec_recrypt_alice`, `dsdp_run_traces_ok`,
  `dsdp_trace_of_view`, `bseq_map` if declared, `AliceTrace`,
  `dsdp_trace_of_viewE`, `AliceTrace_zero_prefix`, `distinguisher_of_trace`,
  `trace_joint_PrE`, `hop0_trace_advantageE`, `hop1_trace_advantageE`,
  `guess_trace_all_zero_le_invm`,
  `dsdp_alice_guess_fdist_trace_V2_real_le`); a notation-promotion note for
  `AliceTrace_all_zero`; and a `Scope.` paragraph carrying: average-case over
  honest inputs; single-query fixed-key epsilons, related to but distinct
  from `indcpa_ror.v`'s multi-query oracle advantage; bounds vacuous once the
  epsilons exceed 1; efficiency reading of the reductions on paper;
  `w_rb2`/`w_rc2` universally quantified as parameters; and the correction
  that Charlie-side re-encryption randomness DOES reach Alice's trace
  (`step` traces the datum received, `smc/smc_interpreter.v:58-63`),
  retiring the leg's fidelity remark to the contrary.

- [ ] **Step 2: statement-comment pass.** Every public
  Lemma/Theorem/Definition gets a declarative one-sentence comment, plus a
  trailing `Naming:` sentence only where a name needs defending. No status,
  effort, or provenance narration in rendered positions. One known fix: the
  comment above the `decode` `Let` (Task 3 Step 3) describes a program alias
  ("the piSMC programs, not the same-named ones of dsdp_program.v") while the
  declaration is `@dec AHE`; move that sentence to `dsdp_procs_std` and give
  `decode` its own one-liner.

- [ ] **Step 3: style scan**

```bash
bash /Users/cheng-huiweng/.claude/skills/mathcomp-skills/scripts/audit-quick.sh \
  dumas2017dual/dsdp/infotheo_leg/dsdp_alice_trace_link.v
awk 'length > 80' dumas2017dual/dsdp/infotheo_leg/dsdp_alice_trace_link.v
```

Fix findings. `boolp.funext` fully-qualified call sites are an accepted
project decision; leave them.

- [ ] **Step 4: axiom hygiene** on `dsdp_run_traces_ok` and
  `dsdp_alice_guess_fdist_trace_V2_real_le`. Expected: boolp trio only
  (`dsdp_run_traces_ok` may well be axiom-free — the probe's counterpart was
  "Closed under the global context").

- [ ] **Step 5: full recompile** of every file this plan touched
  (Task 1 Step 5's loop plus the two new/modified files).

- [ ] **Step 6: final commit WITHOUT `--no-verify`**

```bash
git add dumas2017dual/dsdp/infotheo_leg/dsdp_alice_trace_link.v
git commit -m "dsdp trace link: header, style pass, axiom check" \
  -- dumas2017dual/dsdp/infotheo_leg/dsdp_alice_trace_link.v
```

This goes through the rocq-auditor pre-commit gate. Address its findings; do
not bypass. If Stage 2 fails with the known
`--json-schema is not a valid JSON Schema` infrastructure error, dispatch the
`rocq-auditor` subagent to supply Stage 2 rather than accepting an
unreviewed commit.

---

## Self-review notes

- **Spec coverage:** spec section 2 (parameter route) -> Tasks 3-6; section
  3 F-a -> Task 1; F-b -> Task 3; F-c -> Task 4; F-d -> Task 3 Step 1 and
  Task 4 Step 5; F-e -> Task 3 Step 3; section 4 -> Task 4; section 4.1 ->
  Tasks 7-8; section 5 -> Tasks 5-6; section 6 naming table -> applied
  throughout; section 7 invariants -> Task 6 Step 6 and Task 10 Steps 1, 4;
  section 9 conventions -> Task 10; section 10 golf -> Task 9.
- **Decisions taken here rather than deferred to implementation**, each for
  readability and against duplication: (a) fuel splitting uses
  `interp_fuelD`, derived once from `interpD` in Task 2b, because `interpD`'s
  `let` form structurally blocks the staging and because restating the
  probe's copy would duplicate an existing fact; (b) the evaluation lemma
  stays seq-level (the form the staged proof produces) and `AliceTrace`
  projects with `nth`, so no `'I_(size ...)` obligation appears, and no
  tuple-form restatement of the literal is added just for parity with
  `dsdp_traces_ok`; (c) no `bseq_map` helper is introduced — the encoded
  `Bseq` is built in one step from `size_map` and `size_traces_nth`, since
  nothing equivalent exists upstream and a one-call-site helper would be dead
  generality.
- **Type consistency:** `dsdp_trace_dataT` is the codomain element type in
  Tasks 3, 5, 6; `dsdp_trace_of_view` has one signature
  (`dsdp_alice_viewT AHE Renc t_cipher -> 15.-bseq dsdp_trace_dataT`) used in
  Tasks 5 and 6; `pkey_of_dk` replaces the leg's `pkey_of_party` argument at
  every leg call site (spec F-d), so the leg lemmas are instantiated at
  `pkey_of_dk` in Tasks 5-6.
- **Not in scope** (spec section 11): Bob/Charlie trace headlines, the
  trace-level simulation headline, the coordinate route, the optional
  `Rho2`/`Rho3` -> `RB1`/`RC1` leg rename.
