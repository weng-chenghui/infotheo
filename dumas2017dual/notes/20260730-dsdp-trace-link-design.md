# Design: closing the piSMC chain for the DSDP infotheo leg

Date: 2026-07-30
Status: probe-corrected, naming-audited, soundness-audited (NO-GO fixes
applied; the audit's cheaper route adopted)
Target file: `dumas2017dual/dsdp/infotheo_leg/dsdp_alice_trace_link.v`
Probes (kept): `<session scratchpad>/probe_trace_link.v` (686 lines, exit 0),
`audit_typegeneric_traces.v`, `audit_corollary_route.v` (both exit 0,
boolp-trio axioms only)

## 1. Goal

Make the corrupted-Alice security bound apply to the trace the piSMC
interpreter actually produces, rather than to a hand-transcribed view. Two
deliverables:

1. A machine-checked evaluation lemma for the DSDP protocol run at an
   abstract `AHEncType` (the idealized-scheme counterpart already exists as
   `dsdp_traces_ok`, `dumas2017dual/dsdp/core/dsdp_correctness.v:186`).
2. A trace-level guess headline: for every predictor reading the encoded
   Alice trace, success is at most `1/#|plain AHE|` plus the real-or-zero
   advantages of two explicitly constructed reductions.

This closes the last dashed line in the chain piSMC program -> trace -> view
random variable -> security bound.

## 2. Architecture: the parameter route

The soundness audit compiled two routes and the cheap one wins decisively.

**Adopted.** Charlie's re-encryption randomness and Bob's forward randomness
are section **parameters** `w_rb2 w_rc2 : Renc`, not sample coordinates. Then
Alice's executed trace is a deterministic function of the leg's existing
view, `AliceTrace = alice_trace_of `o AliceView`, which is exactly the shape
of the repo's own precedent
`alice_traces_ok : alice_traces = alice_traces_from_view `o [%...]`
(`du2002/spp_proof.v:254`). Every trace-level statement is then a corollary
of the leg's already-`Qed` results: the audit's `audit_corollary_route.v`
proves the two hop equalities, the endpoint and the headline in **one line
each** on top of an 8-line `Pr`-preimage bridge, ~75 lines total.

**Rejected (recorded as follow-up).** Making `rb2`/`rc2` sample coordinates
requires an extended sample space, extended-space analogues of about
eighteen leg lemmas (~515 lines to mirror, measured), a generalization of
`enc_slot_resampleE` in the committed leg file, and a re-derivation of the
whole spectator ladder. What those lines buy is one thing: a single
reduction's epsilon for the `rc2`-**averaged** experiment.

**Strength comparison, stated honestly.** The parameter route proves
`forall w_rb2 w_rc2, forall g, Pr[...] <= 1/m + eps0 + eps1` in exact
reduction form — it holds for every choice of re-encryption randomness,
including adversarially chosen, and it implies the averaged bound. The
coordinate route proves the averaged probability with a single epsilon.
Universally quantifying the randomness is the stronger cryptographic
reading, so the cheap route is also the better statement. What the file does
NOT provide is a bound in which `rc2` is itself averaged inside one
reduction; that is the follow-up.

Correction the audit forced (leg spec `20260729` fidelity remark): the claim
that no Charlie-side encryption randomness enters Alice's view is **wrong**.
`step` traces the raw datum received, not the continuation's argument
(`smc/smc_interpreter.v:58-63`), so `enc (ek Alice) M3 rc2` is in the trace
under either route. The new file's `Scope.` paragraph states this.

## 3. Probe-forced construction details

**F-a. `interp_traces` at abstract AHE — resolved by generalizing the
interpreter, not by working around it.** `Section traces`
(`smc/smc_interpreter.v:224-328`) is stated over `Variable data : eqType`
only because `size_traces` is phrased with `\in`; `bseq_of` is `Type`-generic
(`mathcomp/boot/tuple.v:475-477`) and `size_interp` uses no equality. The
audit re-derived the packaging index-wise at `data : Type` in ~45 lines, all
`Qed`, zero axioms, and confirmed that at abstract AHE
`interp_traces 15 procs : 3.-tuple (15.-bseq (di_data DI))` then typechecks.

So the plan generalizes `Section traces` in place: the index-wise size
lemmas become the primitives at `data : Type`, the `\in`-phrased lemma stays
as an eqType corollary, and `interp_traces`/`interp_traces_ok` keep their
names and statements. Existing users (`dsdp_correctness.v`,
`du2002/spp_proof.v`) are unaffected because a generalization subsumes them,
verified by rebuilding the dependents (`smc_session_types`, `dsdp_program`,
`dsdp_pismc`, `dsdp_correctness`, `du2002/spp_proof`, the leg). This deletes
the whole workaround chain: no `nth [::]`, no `seq`-level statement, no
`take`-bound helper in `lib/ssr_ext.v`, and the evaluation lemma becomes the
direct analogue of `dsdp_traces_ok` and `smc_scalar_product_traces_ok`.

**F-b. Encoded trace codomain.** `cipher AHE` is an `nzRingType` and both key
sorts are bare `Type`, so the RV codomain is a finite encoding:

```
Definition dsdp_trace_dataT : finType :=
  ((plain AHE + t_cipher) + unit + unit)%type.
Definition trace_data_of_di_data (x : di_data DI) : dsdp_trace_dataT :=
  (* plain kept; cipher marshalled by chcipher_of_cipher;
     both key sorts erased to unit marks *)
```

The summand order mirrors `std_data`'s `msgT + encT + privT + pubT`
(`dsdp_interface.v:157`); the `pub_key` summand is dead (no proc emits one)
and is kept only for that parity. **Injectivity is required and available**:
the leg already carries `cipher_of_chcipher` and
`chcipher_of_cipherK` (`dsdp_alice_infotheo_secrecy.v:259-263`), so
`can_inj chcipher_of_cipherK` gives injectivity on the ciphertext summand;
the encoder is injective on the plaintext and ciphertext summands and
constant on the key summands, hence injective on the run's image. Without
this the universally quantified predictor class would silently shrink and
the epsilons would be measured in a collapsed ciphertext space — the
statement would sound stronger than it is.

**F-c. Staged evaluation over an abstract-operation interface clone.**
Proving the run at `Standard_DSDP_Interface AHE` directly fails: `rewrite /=`
and `cbn` time out past 180 s, `vm_compute` kills the worker, and
`vm_compute` at the HB instance expands `enc` into a mixin match after which
no `rewrite` matches. Probe-verified construction:

- `DSDP_Interface_of_ops`: interface value with the concrete `di_data` sum
  carrier (so `di_get_cipher` computes) and every crypto operation a section
  `Variable` (so `vm_compute` keeps it atomic). `di_Recv_dec`/`di_Recv_enc`
  are never read by the pismc programs, so the value is convertible to
  `Standard_DSDP_Interface AHE` and the two proc lists are equal `by []`.
- fuel splitting via the **existing** `interpD`
  (`smc/smc_session_types.v:872`, in scope through `dsdp_program`), whose
  conclusion is a `let (ps', traces') := ... in` destructuring. Do not
  restate it. Fuel arithmetic stays in `%N`: `ring_scope` is open, so a bare
  `+` on the fuel elaborates to `GRing.add` and every rewrite misses.
- three `move Ht: <inner run> => S; vm_compute in Ht` stages, split at the
  three stuck decryptions, each discharged by a `dec_correct` rewrite. Never
  abstract a fuel numeral (`5` occurs inside `10`); abstract the state.

**F-d. All three parties decrypt; keys by match; `pkey_of_party` must BE
`ek`.** A single Alice-key hypothesis is not enough — Bob's and Charlie's
`Recv_dec` also block the fixpoint. Defining

```
Let ek (p : party_id) : pub_key AHE :=
  match p with Alice => pub_of_priv dk_a | Bob => pub_of_priv dk_b
             | Charlie => pub_of_priv dk_c | NoParty => pub_of_priv dk_a end.
```

makes `dec_correct` (unconditional, `enc_dec.v:56`) fire by conversion, so no
key hypothesis is needed. **The leg's `pkey_of_party` must be instantiated to
`ek`**: otherwise the run's `enc (ek Bob) v2 rb1` and the view's slot
`chcipher_of_cipher (enc (pkey_of_party Bob) (V2 t) ...)` (leg `:319-322`)
are distinct terms and the evaluation lemma does not typecheck as an
equality. The pismc programs route through `nat_to_party_id`, which reduces,
so statements name `Alice`/`Bob`/`Charlie`, not `party_id` variables.

**F-e. `dsdp_procs` is defined twice.** `dsdp_program.v:123/160/166` and
`dsdp_pismc.v:136/326/330` both define `palice`, `dsdp_saprocs`,
`dsdp_procs`; `nat_to_party_id` occurs 5 times in `dsdp_pismc.v`, 0 in
`dsdp_program.v`. F-d needs the pismc programs while the leg pulls in
`dsdp_program`, so bare names would resolve last-import-wins. One explicitly
qualified alias, then the alias everywhere:

```
Let dsdp_procs_std := dsdp_pismc.dsdp_procs.   (* the only qualified use *)
```

## 4. The computed trace (ground truth)

Probe-verified, with `d/e/kd := di_data_of_plain/cipher/priv_key DI`:

```
interp_traces 15 dsdp_procs_std =
[tuple [bseq d (v3*u3 + r3 + (v2*u2 + r2) - r2 - r3 + u1*v1);
              e (enc (ek Alice) (v3*u3 + r3 + (v2*u2 + r2)) w_rc2);
              e (enc (ek Charlie) v3 rc1);
              e (enc (ek Bob) v2 rb1);
              d r3; d r2; d u3; d u2; d u1; d v1; kd dk_a];
        [bseq e (enc (ek Charlie) (v3*u3 + r3)
                     (rand_mul (rand_pow rc1 u3) ra2));
              e (enc (ek Bob) (v2*u2 + r2)
                     (rand_mul (rand_pow rb1 u2) ra1));
              d v2; kd dk_b];
        [bseq e (enc (ek Charlie) (v3*u3 + r3 + (v2*u2 + r2))
                     (rand_mul (rand_mul (rand_pow rc1 u3) ra2) w_rb2));
              d v3; kd dk_c]]
```

Homomorphic randomness is tracked by `rand_pow`/`rand_mul` through
`Epow_encE`/`Emul_encE`, rewritable restatements of the `isAHEnc` mixin
equations:
`Epow (enc k m r) j = enc k (m * j) (rand_pow r j)`,
`Emul (enc k m1 r1) (enc k m2 r2) = enc k (m1 + m2) (rand_mul r1 r2)`.
Being AHE-generic with no DSDP content, they belong in
`homomorphic_encryption/ahe_enc.v` beside `Emul_addM` (`:91`) and
`Epow_scalarM` (`:96`), as a separate atomic task.

Alice's 11 entries classify as: entry 0 `= Sout` (by `ring`); entry 1 the
`rc2` re-encryption of `M3 = Sout - u1*v1 + r2 + r3`; entries 2 and 3 the two
**secret-bearing** ciphertexts (the complete set, so the two-hop ladder is
right); entries 4-5 mask coordinates; entries 6-10 section constants. Sends
are not traced.

### 4.1 Repo bug found by the evaluation lemma

`dumas2017dual/dsdp/counting/dsdp_entropy_trace.v:92-101` hand-writes the
same trace with three wrong randomness arguments:

| entry | written there | actually produced |
|---|---|---|
| Bob[0] (Charlie key) | `rb2` | `rand_mul (rand_pow rc1 u3) ra2` |
| Bob[1] (Bob key) | `ra1` | `rand_mul (rand_pow rb1 u2) ra1` |
| Charlie[0] | `rb2` | `rand_mul (rand_mul (rand_pow rc1 u3) ra2) rb2` |

Bob[0] is also attributed to the wrong party: `rb2` is Bob's own randomness,
while that wire carries Alice's second combine, whose randomness derives
from Charlie's `rc1` and Alice's `ra2`. The hand-written literal is provable
**under** (not "exactly under" — the probe establishes sufficiency, and
necessity would need injectivity of `enc` in its randomness argument, which
`isAHEnc` does not give) the three identities
`rand_mul (rand_pow rb1 u2) ra1 = ra1`,
`rand_mul (rand_pow rc1 u3) ra2 = rb2`,
`rand_mul (rand_mul (rand_pow rc1 u3) ra2) rb2 = rb2`, none of which follows
from `isAHEnc`, the middle one being false whenever `rb2` is independent. All
plaintexts, all entry orders and the party order are correct.

**Blast radius, corrected.** No `.v` file consumes `dsdp_traces`
(`dsdp_result_correct` at `:106` is a standalone plaintext `ring` identity
that does not mention it), so the code-side fix is free. But the **thesis
does** consume it: `~/Projects/phd-thesis/chapters/computational-privacy-dsdp.tex:841-842`
anchors "the interpreter run on the three piSMC programs, the lifting of the
resulting traces to random variables" on `\coqin{dsdp_traces}` in
`\coqin{dsdp/dsdp_entropy_trace.v}` — a claim about interpreter output
resting on a hand-written literal with three wrong randomness arguments, and
with a stale path (`dsdp/` vs `dsdp/counting/`). Tasks: correct the three
entries, fix the path, and re-point that sidenote at the new evaluation
lemma.

## 5. Trace RV, evaluation lemma, and the corollary chain

```
Definition dsdp_trace_of_view (v : dsdp_alice_viewT) :
  15.-bseq dsdp_trace_dataT
  (* the 11 encoded entries, rebuilt from the view: Sout; the rc2
     re-encryption of Sout - u1*v1 + r2 + r3; the two view ciphertexts;
     r3; r2; the four weights; the erased key mark *)

Definition AliceTrace :
  {RV alice_sample_fdist -> 15.-bseq dsdp_trace_dataT} :=
  fun s => [the encoded Alice component of interp_traces 15
            (dsdp_procs_of_sample s)]

Lemma dsdp_trace_of_viewE :        (* THE evaluation lemma *)
  AliceTrace = dsdp_trace_of_view `o AliceView.

Definition AliceTrace_zero_prefix (i : nat) :=
  dsdp_trace_of_view `o AliceView_zero_prefix i.
Notation AliceTrace_all_zero := (AliceTrace_zero_prefix 2).
```

Because `AliceView` is the leg's notation for `AliceView_zero_prefix 0`,
`AliceTrace_zero_prefix 0` is `dsdp_trace_of_view `o AliceView`
definitionally, so `dsdp_trace_of_viewE` **is** the ladder-to-trace link the
first audit found missing; no separate bridge lemma is needed, and the
sample space is the leg's, unextended.

Corollary chain (audit-compiled, one line each after the bridge):

```
Lemma trace_joint_PrE (D) (i : nat) :
  Pr (`p_ [% V2, V3, AliceTrace_zero_prefix i]) [set x | D x]
  = Pr (`p_ [% V2, V3, AliceView_zero_prefix i])
       [set x | D (x.1.1, x.1.2, dsdp_trace_of_view x.2) ].

Lemma hop0_trace_advantageE (D) : ... = indcpa_fdist_epsilon
  (pkey_of_party Bob) (hop0_reduction (D \o trace_lift)).
Lemma hop1_trace_advantageE (D) : (* Charlie *)
Lemma guess_trace_all_zero_le_invm (g) :
  Pr alice_sample_fdist [set t | (g `o AliceTrace_all_zero) t == V2 t]
    <= (#|plain AHE|%:R)^-1.

Theorem dsdp_alice_guess_fdist_trace_V2_real_le (g) :
  Pr alice_sample_fdist [set t | (g `o AliceTrace) t == V2 t]
    <= (#|plain AHE|%:R)^-1
       + indcpa_fdist_epsilon (pkey_of_party Bob)
           (hop0_reduction (distinguisher_of_guess (g \o dsdp_trace_of_view)))
       + indcpa_fdist_epsilon (pkey_of_party Charlie)
           (hop1_reduction (distinguisher_of_guess (g \o dsdp_trace_of_view))).
```

The endpoint and the headline are `exact:` appeals to the leg's
`guess_all_zero_le_invm` and `dsdp_alice_guess_fdist_V2_real_le` at
`g \o dsdp_trace_of_view`, mirroring the leg's own
`dsdp_alice_guess_fdist_full_le` (`:1435-1449`). No extended sample space, no
extended-space analogues, no edit to the leg's proofs, no spectator
re-derivation: the audit's finding that the `rc2` ciphertext cannot live in
the spectator block (it would determine `Sout` and make the independence
premise provably false) never arises, because the endpoint is inherited
rather than re-proved.

## 6. Naming table (audited)

| Name | Precedent | Note |
|---|---|---|
| `dsdp_trace_dataT` | `dsdp_alice_viewT`, `hop0_ctxT` (leg) | element type; distinct from the existing `dsdp_traceT` notations |
| `trace_data_of_di_data` | `di_data_of_plain/cipher/...` (`dsdp_interface.v:93-96`, rule at `:90`), `pub_of_priv` | total conversion; names the real source type |
| `DSDP_Interface_of_ops` | `Standard_DSDP_Interface` (`:183`), `_of_` rule (`:90`) | Mixed_Snake is the grandfathered upstream-class form |
| `dsdp_procs_std` | — | the single qualified reference to `dsdp_pismc.dsdp_procs`; `real_procs` rejected (`real` = game arm) |
| `dsdp_procs_of_sample` | `_of` family | sample -> programs |
| `AliceTrace`, `AliceTrace_zero_prefix`, `Notation AliceTrace_all_zero` | `AliceView`, `AliceView_zero_prefix`, `AliceView_all_zero` (leg `:340/:344/:345`) | |
| `dsdp_trace_of_view`, `dsdp_trace_of_viewE` | `alice_view_full_of`/`alice_view_fullE`, `alice_spectator_of`/`alice_spectator_ofE` (leg) | conversion + its equation |
| `dsdp_run_traces_ok` (if the tuple form is named) | `dsdp_traces_ok` (`dsdp_correctness.v:186`), `interp_traces_ok`, `alice_traces_ok` | `_ok` = object equals its ground-truth literal |
| `trace_joint_PrE` | leg `guess_event_jointE`, `Pr_fdistmap_pre` | `Pr`-preimage bridge |
| `hop0_trace_advantageE`, `hop1_trace_advantageE` | leg `hop0_advantageE :655` | head noun first, level token in the middle (`guess_fdist_success` convention), never a `trace_` prefix |
| `guess_trace_all_zero_le_invm` | leg `guess_all_zero_le_invm :993` | |
| `dsdp_alice_guess_fdist_trace_V2_real_le` | leg `dsdp_alice_guess_fdist_V2_real_le :1039` | `V2` says what is guessed, `real` marks the ladder end |
| `Epow_encE`, `Emul_encE` (in `ahe_enc.v`) | `Emul_addM :91`, `Epow_scalarM :96`, `EmulE`/`EpowE` (`dsdp_program.v:200/203`) | LHS heads are `Emul`/`Epow` |
| `w_rb2`, `w_rc2` | leg `w_v1 w_u1 w_u2 w_u3` | fixed-parameter `w_` family, not RV caps |

Dropped from the previous draft together with the coordinate route: `RB2`,
`RC2`, `dsdp_alice_trace_sampleT`, `alice_trace_sample_fdist(E)`,
`card_trace_sample`, `hop{0,1}_trace_ctx_prod`, the
`AliceTraceSpectator*`/`alice_trace_spectator_*` family,
`alice_trace_V2_cond_le`, `alice_trace_recrypt_slotE`, `take_size_bound`,
and the `enc_slot_resampleE` generalization.

Also dropped: the leg rename `Rho2`/`Rho3` -> `RB1`/`RC1`. Its motivation was
a clash with the new `RB2`/`RC2` coordinates, which no longer exist. The
underlying mismatch (`Rho2` carries `rb1`) is real but now isolated; it is
recorded as an optional cleanup, not part of this plan.

Flat-namespace rule: the repo has no modules. Two pre-existing duplicate
globals constrain this file — `dsdp_traces` (`dsdp_correctness.v:168` and
`dsdp_entropy_trace.v:92`) and the `dsdp_traceT`/`dsdp_tracesT` notations —
so the new file must not become the first to import both sources.

## 7. Soundness invariants

1. Reduction form preserved: the two trace epsilons are
   `indcpa_fdist_epsilon` of explicitly constructed reductions; no
   hypothesis bounds them.
2. The evaluation lemma is proved, not assumed: no `Hypothesis` describes
   the trace contents. New modeling inputs are `dk_a dk_b dk_c`,
   `w_rb2 w_rc2`, the `ek`-by-match definition, and the instantiation
   `pkey_of_party := ek` (F-d).
3. The headline quantifies over every predictor on the encoded trace, and
   the encoding is injective on the run's image
   (`can_inj chcipher_of_cipherK`; key summands constant).
4. `AliceTrace` is defined from `interp_traces`, and
   `AliceTrace_zero_prefix 0` is definitionally
   `dsdp_trace_of_view `o AliceView`, so `dsdp_trace_of_viewE` links the
   headline to the ladder with nothing smuggled in.
5. `w_u3_inj` remains the only protocol premise; the leg's absent side
   conditions must not reappear.
6. Scope carried over from the leg and restated in the header: average-case
   over honest inputs; single-query fixed-key epsilons, related to but
   distinct from `indcpa_ror.v`'s multi-query oracle advantage; bounds hold
   vacuously once the epsilons exceed 1; the efficiency reading of the
   reductions stays on paper. Added here: `w_rb2`/`w_rc2` are universally
   quantified parameters, and the leg's fidelity remark about Charlie-side
   randomness not reaching Alice's view is corrected (section 2).

## 8. Risks

- The staged `vm_compute` evaluation is probe-verified but brittle against
  changes to the pismc programs or the fuel bound; the plan pins the stage
  boundaries and records why each exists.
- Generalizing `Section traces` touches a widely imported file; the plan
  rebuilds its dependents (`smc_session_types`, `dsdp_program`,
  `dsdp_pismc`, `dsdp_correctness`, `du2002/spp_proof`, the leg) as the
  task's acceptance test.
- Estimated size: `smc_interpreter.v` generalization ~45 lines,
  `ahe_enc.v` ~10 lines, evaluation machinery ~250 lines, corollary chain
  ~75 lines.

## 9. File conventions

Matching the leg's actual preamble
(`dsdp_alice_infotheo_secrecy.v:1-8`, `:176-185`): imports in blocks with
`From HB Require Import structures.` first; `(**md ... *)` header after the
imports carrying `# Title`, a purpose paragraph, a `Headline results:`
paragraph, the `==`-aligned table of every public definition, the `Scope.`
paragraph of section 7.6, and a notation-promotion note for
`AliceTrace_all_zero`; setup in the order `Import Order.TTheory GRing.Theory
Num.Def Num.Theory.`, `Set Implicit Arguments.`, `Unset Strict Implicit.`,
`Import Prenex Implicits.`; the four `Local Open Scope` lines
(`ring_scope` being open is what makes the `%N` fuel discipline
load-bearing); statement comments declarative with a trailing `Naming:`
sentence only where a name needs defending; cardinality facts and glue as
`Let`, headlines bare; `Arguments ... : clear implicits.` after `End` if a
record is declared (`dsdp_interface.v:128-135`); 80 columns, ASCII.

Spec shorthand notice: this document writes `Pr[D on X]` for readability.
The repo has no such notation; every plan step spells it
`Pr (`p_ [% ...]) [set x | D x]` as the leg does.

## 10. Verification process

Probes done and kept. Naming audit and soundness audit done, findings folded
in (the soundness verdict was NO-GO; all six blocking items are resolved
here, four of them dissolved by adopting the parameter route). Next:
writing-plans, then task-by-task implementation with per-task compile and
commit.

Task-level scope beyond the new file: `smc/smc_interpreter.v` (generalize
`Section traces` to `data : Type`, with a dependent rebuild as the acceptance
test), `homomorphic_encryption/ahe_enc.v` (`Epow_encE`, `Emul_encE`),
`dsdp_entropy_trace.v` (the three-entry randomness correction of 4.1), and
`~/Projects/phd-thesis/chapters/computational-privacy-dsdp.tex` (the anchor
path and sidenote re-pointing). Each is its own atomic task. The leg file is
NOT edited.

The plan carries a mandatory `rocq:golf` stage after the last proving task
and before the header/style task: proof bodies only, never a statement, an
identifier, a statement comment, or the header table; re-verified by a full
compile, a zero `Admitted`/`Abort`/`Axiom` grep, and unchanged
`Print Assumptions`. The final commit goes through the rocq-auditor gate
unbypassed.

## 11. Out of scope

- Bob/Charlie trace headlines; trace-level simulation headline.
- The coordinate route (`rb2`/`rc2` as sample coordinates) and the
  `rc2`-averaged single-reduction epsilon it would buy.
- The optional `Rho2`/`Rho3` -> `RB1`/`RC1` leg rename.
- Any PPT/asymptotic internalization.
