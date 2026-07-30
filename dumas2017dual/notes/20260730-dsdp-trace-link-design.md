# Design: closing the piSMC chain for the DSDP infotheo leg

Date: 2026-07-30
Status: probe-corrected draft (pre-audit)
Target file: `dumas2017dual/dsdp/infotheo_leg/dsdp_alice_trace_link.v`
Probe: `<session scratchpad>/probe_trace_link.v` (686 lines, exit 0, zero
axioms in the run-evaluation lemma), items P0-P3 all passing.

## 1. Goal

Make the corrupted-Alice security bound apply to the trace the piSMC
interpreter actually produces, rather than to a hand-transcribed view. Two
deliverables:

1. A machine-checked evaluation lemma for the DSDP protocol run at an
   abstract `AHEncType` (the idealized-scheme counterpart already exists as
   `dsdp_traces_ok`, `dumas2017dual/dsdp/core/dsdp_correctness.v:197`).
2. A trace-level guess headline: for every predictor reading the encoded
   Alice trace, success is at most `1/#|plain AHE|` plus the real-or-zero
   advantages of two explicitly constructed trace-level reductions.

This closes the last dashed line in the chain piSMC program -> trace -> view
random variable -> security bound, and retires the "average-case /
decrypt-on-receive model" caveat about Charlie's re-encryption randomness
(audit finding 15 of the 2026-07-30 leg audit): `RC2` becomes a modelled
sample coordinate.

Scope decision (brainstorming): trace-level headline, reusing the leg's
machinery (option A1 — full-tuple evaluation then projection, mirroring
`dsdp_correctness.v`). Out of scope: Bob/Charlie trace headlines, a
trace-level simulation headline, and replacing the counting axis's traces.

## 2. Probe-forced architecture (the four blocking findings)

**F-a. `interp_traces` is unavailable at abstract AHE.** It lives in
`smc/smc_interpreter.v` `Section traces` over `Variable data : eqType`;
`priv_key`/`pub_key` of `AHEncType` are bare `Type`
(`homomorphic_encryption/he_types.v:44-45`), so `di_data` is not an eqType
and `interp_traces 15 procs` does not typecheck. `dsdp_correctness.v` can
use it only because its idealized instance has `priv_key = pub_key = 'F_m`.

Consequence: the evaluation lemma is stated at the seq level,
`(run_interp 15 procs).2 : seq (seq data)`, and Alice's trace is
`nth [::] _ 0`. The `n.-bseq` wrapper is rebuilt with an explicit bound
(`size (take n s) <= n`), not with `interp_traces` and not with `insub`
(whose `idP` is `Qed`-opaque and does not reduce).

**F-b. The RV codomain must be an encoded trace.** `cipher AHE` is an
`nzRingType`, both key sorts are bare `Type`. `n.-bseq T` and
`m.-tuple (n.-bseq T)` are finTypes when `T` is (`mathcomp/boot/tuple.v:690`,
`:420`), so the fix is a finite encoding of the data carrier:

```
Definition dsdp_trace_dataT : finType :=
  ((plain AHE + t_cipher) + unit + unit)%type.
Definition trace_data_of_data (x : di_data DI) : dsdp_trace_dataT :=
  (* plain kept; cipher marshalled by chcipher_of_cipher;
     both key sorts erased to unit marks *)
```

Only `chcipher_of_cipher` is needed; `cipher_of_chcipher` and its cancel
play no part here. Erasing the key entries loses nothing: Alice's key entry
is the constant `dk_a`.

**F-c. Staged evaluation over an abstract-operation interface clone.**
Proving the run directly at `Standard_DSDP_Interface AHE` fails: `rewrite /=`
and `cbn` time out past 180 s, `vm_compute` kills the worker, and
`vm_compute` at the HB instance expands `enc` into a mixin match after which
no `rewrite` matches. The probe-verified construction:

- an interface instance with the concrete `di_data` sum carrier (so
  `di_get_cipher` computes) but every crypto operation a section `Variable`
  (so `vm_compute` keeps it atomic); `di_Recv_dec`/`di_Recv_enc` are never
  read by the pismc procs, so the clone is convertible to the standard
  instance and `procs = real_procs` holds `by []`;
- a fuel-splitting lemma `interp (m + n)%N ps trs = interp n (interp m ...)`
  (**the `%N` matters**: under `ring_scope` a bare `+` on the fuel elaborates
  to `GRing.add` and every rewrite silently misses);
- three `move Ht: <inner run> => S; vm_compute in Ht` stages, split exactly
  at the three stuck decryptions, each discharged by a `dec_correct` rewrite.
  Never abstract a fuel numeral (`5` occurs inside `10`); abstract the
  interpreter state.

**F-d. All three parties decrypt, and the party tags are constructors.**
A single `ek Alice = pub_of_priv dk_a` hypothesis is not enough — Bob's and
Charlie's `Recv_dec` also block the fixpoint. Defining
`ek p := match p with Alice => pub_of_priv dk_a | Bob => ... end` removes the
need for any key hypothesis, since `dec_correct` then fires by conversion.
The pismc procs route through `nat_to_party_id`, which reduces, so statements
must name `Alice`/`Bob`/`Charlie` rather than `party_id` variables.

## 3. The computed trace (ground truth)

Probe-verified, with `d/e/kd := di_data_of_plain/cipher/priv_key DI`:

```
(run_interp 15 procs).2 =
[:: [:: d (v3*u3 + r3 + (v2*u2 + r2) - r2 - r3 + u1*v1);
        e (enc (ek Alice) (v3*u3 + r3 + (v2*u2 + r2)) rc2);
        e (enc (ek Charlie) v3 rc1);
        e (enc (ek Bob) v2 rb1);
        d r3; d r2; d u3; d u2; d u1; d v1; kd dk_a];
    [:: e (enc (ek Charlie) (v3*u3 + r3)
               (rand_mul (rand_pow rc1 u3) ra2));
        e (enc (ek Bob) (v2*u2 + r2)
               (rand_mul (rand_pow rb1 u2) ra1));
        d v2; kd dk_b];
    [:: e (enc (ek Charlie) (v3*u3 + r3 + (v2*u2 + r2))
               (rand_mul (rand_mul (rand_pow rc1 u3) ra2) rb2));
        d v3; kd dk_c]]
```

Homomorphic randomness is tracked by `rand_pow`/`rand_mul`, from the
`isAHEnc` mixin equations restated in rewritable form:
`Epow (enc k m r) j = enc k (m * j) (rand_pow r j)` and
`Emul (enc k m1 r1) (enc k m2 r2) = enc k (m1 + m2) (rand_mul r1 r2)`.

Two structural facts: **sends are not traced** (Alice's trace holds neither
of her outgoing combines), and Alice's trace does hold
`enc (ek Alice) M3 rc2`, Charlie's re-encryption under her own key, with
`M3 = v3*u3 + r3 + (v2*u2 + r2)`.

### 3.1 Repo bug found by the evaluation lemma

`dumas2017dual/dsdp/counting/dsdp_entropy_trace.v:92-101` hand-writes the
same trace with three wrong randomness arguments:

| entry | written there | actually produced |
|---|---|---|
| Bob[0] (Charlie key) | `rb2` | `rand_mul (rand_pow rc1 u3) ra2` |
| Bob[1] (Bob key) | `ra1` | `rand_mul (rand_pow rb1 u2) ra1` |
| Charlie[0] | `rb2` | `rand_mul (rand_mul (rand_pow rc1 u3) ra2) rb2` |

Bob[0] is also attributed to the wrong party: `rb2` is Bob's own randomness,
while that wire carries Alice's second combine, whose randomness is built
from Charlie's `rc1` and Alice's `ra2`. The probe pins this down: the
hand-written literal is provable exactly under
`rand_mul (rand_pow rb1 u2) ra1 = ra1`,
`rand_mul (rand_pow rc1 u3) ra2 = rb2`,
`rand_mul (rand_mul (rand_pow rc1 u3) ra2) rb2 = rb2`, none of which follows
from `isAHEnc`, and the middle one is false whenever `rb2` is sampled
independently. All plaintexts, all entry orders and the party order are
correct.

Fix (in scope, separate task): correct those three entries in
`dsdp_entropy_trace.v`, citing the evaluation lemma as ground truth. Blast
radius is nil: that `Definition` feeds only `dsdp_result_correct`, a
plaintext-level `ring` identity.

## 4. Sample space, trace RV, and the transport shape

Extended space (probe-verified uniform):

```
Definition dsdp_alice_trace_sampleT : finType :=
  (dsdp_alice_sampleT * (Renc * Renc))%type.        (* new: rb2, rc2 *)
Definition alice_trace_sample_fdist : R.-fdist dsdp_alice_trace_sampleT :=
  alice_sample_fdist `x (fdist_uniform card_renc_pair).
Lemma alice_trace_sample_fdistE :
  alice_trace_sample_fdist = fdist_uniform card_trace_sample.
```

Leg RVs lift by `\o fst`; new coordinates `RB2`, `RC2`. `RC2` is the only
new coordinate Alice's trace reads; `RB2` occurs only in Bob's and Charlie's
traces and is carried so the three-party evaluation lemma is instantiable.

Trace RV (encoded, seq-level projection, explicit bseq bound):

```
Definition AliceTrace : {RV alice_trace_sample_fdist -> 15.-bseq dsdp_trace_dataT}
  := fun s => bseq_take 15 (map trace_data_of_data
                (nth [::] (run_interp 15 (dsdp_procs_of_sample s)).2 0)).
```

**Transport is one-directional (F-e).** The trace and `AliceView` are not a
cancel pair: the trace lacks `RA1`, `RA2` and adds the `rc2` ciphertext. So
the relation to state is

```
Lemma alice_trace_of_viewE :
  AliceTrace = alice_trace_of `o [% AliceView \o fst, RC2].
```

a determination of the trace by (view, fresh randomness), which is all a
guessing bound needs. Do not plan on two-way `cancel` transport.

**Why the hops are re-run rather than averaged.** Reading the bound off the
existing view headline by averaging over `RC2` would make the epsilon a
per-`rc2` average, no longer the advantage of one explicit reduction, which
breaks reduction form. Instead the two hops are re-derived on the extended
space, where each hop is again a single explicit reduction whose context
carries `RB2`, `RC2`.

## 5. Generalizing the leg's machinery

`enc_slot_resampleE` is stated over `alice_sample_fdist` but its proof uses
only `fdistmap_comp`, `fdist_prod_bindE`, `fdistmap_bind`. Probe-verified:
generalizing its binder to `(U : finType) (P : R.-fdist U)` keeps the same
proof body, and existing call sites are unaffected (they instantiate at
`alice_sample_fdist`). This is a one-lemma edit to the committed
`dsdp_alice_infotheo_secrecy.v`, and it is what lets the trace hops reuse the
resampling fact instead of duplicating it.

The protocol-specific facts (`hop0_ctx_prod`, `hop1_ctx_prod`,
`spectator_pre_indep`, the `AliceView_zero_prefix` ladder) stay pinned; their
extended-space analogues are new definitions in the new file. Probe P3 shows
the cost: the context product law over the extended space is the same
`fdist_uniform_prod` + `fdistmap_bij_uniform` proof with one extra `*` layer
in the bijection and two destructuring patterns.

## 6. Trace-level ladder, endpoint, headline

```
Definition AliceTrace_zero_prefix (i : nat) :
  {RV alice_trace_sample_fdist -> 15.-bseq dsdp_trace_dataT}
  (* i = 0 real; 1 zeroes the Bob-key entry; 2 also zeroes the Charlie-key
     entry.  The rc2 entry re-encrypts M3, a function of Sout and the masks,
     and is NOT a hop site: it carries no secret beyond Sout. *)

Lemma trace_hop0_advantageE (D) :
  `| Pr[D on (V2, V3, AliceTrace_zero_prefix 0)]
     - Pr[D on (V2, V3, AliceTrace_zero_prefix 1)] |
  = indcpa_fdist_epsilon (pkey_of_party Bob) (trace_hop0_reduction D).
Lemma trace_hop1_advantageE (D) : (* prefix 1 -> 2, Charlie *)

Lemma guess_trace_all_zero_le_invm (g) :
  Pr alice_trace_sample_fdist
     [set t | (g `o AliceTrace_zero_prefix 2) t == (V2 \o fst) t]
    <= (#|plain AHE|%:R)^-1.

Theorem dsdp_alice_guess_fdist_trace_le (g) :
  Pr alice_trace_sample_fdist
     [set t | (g `o AliceTrace) t == (V2 \o fst) t]
    <= (#|plain AHE|%:R)^-1
       + indcpa_fdist_epsilon (pkey_of_party Bob)
           (trace_hop0_reduction (distinguisher_of_guess g))
       + indcpa_fdist_epsilon (pkey_of_party Charlie)
           (trace_hop1_reduction (distinguisher_of_guess g)).
```

Endpoint route, mirroring the leg: the all-zero trace is a deterministic
function of `[% AliceTraceSpectator, Sout \o fst]` where the spectator block
is masks, combine randomness, `RB2`, `RC2`, both zeroed ciphertexts and the
`rc2` re-encryption of `M3`; that block is independent of `(V2, V3)` given
`Sout` (product independence plus the graphoid ladder `cinde_RV_unit` ->
`weak_union` -> `cpr_prd_unit_RV`), then `cinde_RV_comp` +
`cinde_diagonal_bound` with the extended-space `alice_V2_cond_le`. The fiber
lemma `Pr_dsdp_sol_uniform_ring` is stated over an arbitrary `P`, so it
applies once the extended-space uniformity premises are discharged from
`alice_trace_sample_fdistE`.

Note the `rc2` entry carries `M3 = Sout + r2 + r3 - u1*v1`, a function of
`Sout` and mask coordinates, so it lands in the spectator block without
extra hops — this must be proved, not asserted, as a slot-law equality.

## 7. Naming table (audit target)

| Candidate | Precedent | Note |
|---|---|---|
| `dsdp_run_traces_ok` | `dsdp_traces_ok` (`dsdp_correctness.v:197`), `dsdp_received_hop_ciphertexts_eq` | seq-level, AHE-generic; distinct from the idealized global |
| `interp_addN` | `interp_traces_ok`; `%N` suffix marks nat addition | fuel split; DISCUSS `interp_fuel_addE` |
| `dsdp_trace_dataT` | `smc_scalar_product_party_tracesT`, `di_data` | `T` suffix, finType |
| `trace_data_of_data` | `chcipher_of_cipher`, `party_of_nat` | total conversion; DISCUSS `trace_data_of_di_data` |
| `bseq_take` | `probe_size_take`; mathcomp `take` | general helper; DISCUSS placing it in `lib/` |
| `dsdp_alice_trace_sampleT`, `alice_trace_sample_fdist`(`E`) | `dsdp_alice_sampleT`, `alice_sample_fdist`, `alice_sample_fdistE` | |
| `RB2`, `RC2` | `R2`, `R3`, `RA1`, `RA2` | math-notation RV caps |
| `AliceTrace`, `AliceTrace_zero_prefix` | `AliceView`, `AliceView_zero_prefix`; du2002 `alice_traces` | |
| `alice_trace_of`, `alice_trace_of_viewE` | `alice_view_full_of`, `alice_view_fullE` | function + equation split |
| `trace_hop0_reduction`, `trace_hop1_reduction` | `hop0_reduction`, `hop1_reduction` | |
| `trace_hop0_advantageE`, `trace_hop1_advantageE` | `hop0_advantageE`, `hop1_advantageE` | equalities |
| `AliceTraceSpectator`, `alice_trace_spectator_cinde` | `AliceSpectator`, `alice_spectator_cinde` | |
| `guess_trace_all_zero_le_invm` | `guess_all_zero_le_invm` | |
| `dsdp_alice_guess_fdist_trace_le` | `dsdp_alice_guess_fdist_V2_real_le` | axis + level tokens |
| `Epow_encE`, `Emul_encE` | `Epow_scalarM`, `Emul_addM` (mixin), `E` equation suffix | rewritable restatements; DISCUSS placing them in `homomorphic_encryption/` |

Flat-namespace rule: the repo has no modules, so every global here must not
collide with `dsdp_correctness.v`'s idealized `dsdp_traces`/`dsdp_traces_ok`
or the leg's names.

## 8. Soundness invariants

1. Reduction form preserved: the two trace epsilons are
   `indcpa_fdist_epsilon` of explicitly constructed reductions; no
   hypothesis bounds them.
2. The evaluation lemma is proved, not assumed: no `Hypothesis` describes
   the trace contents; the only new modeling inputs are `dk_a dk_b dk_c` and
   the `ek`-by-match definition (which needs no key hypothesis).
3. The trace-level headline quantifies over every `g` on the encoded trace;
   the encoding must not discard secret-bearing content (keys erased to
   marks are constants; ciphertexts marshalled injectively).
4. No claim that trace and view determine each other; only
   trace = function of (view, `RC2`).
5. `w_u3_inj` remains the only protocol premise; the leg's absent side
   conditions must not reappear.
6. The `rc2` entry's placement in the spectator block is a proved slot law,
   not an assertion.

## 9. Risks

- The staged `vm_compute` evaluation is probe-verified but brittle against
  changes to the pismc programs or the fuel bound; the plan pins the exact
  stage boundaries and records why each exists.
- Extended-space re-proofs of the ladder are mechanical but tuple-shape
  sensitive; keep the nesting of the extended context identical to the
  probe's.
- `dsdp_trace_dataT`'s summand order must mirror `std_data`'s
  (`msgT + encT + privT + pubT`), or `trace_data_of_data` stops computing.
- Estimated size: evaluation machinery ~250 lines, extended-space ladder and
  headline ~350-450 lines.

## 10. File conventions

Same as the leg (spec `20260729-dsdp-infotheo-leg-design.md` section 10):
`(**md ... *)` header with an `==`-aligned table of every public definition,
setup block `Set Implicit Arguments. / Unset Strict Implicit. / Import
Order.TTheory GRing.Theory Num.Def Num.Theory.`, 80 columns, declarative
statement comments with a trailing `Naming:` paragraph, `Arguments ... :
clear implicits.` after any record, pre-commit record-field disjointness
check and rocq-auditor Stage 2.

## 11. Verification process

Probe already done (P0-P3, file kept). Next: Opus soundness audit + Opus
mathcomp naming audit on this spec, findings folded in, then writing-plans,
then task-by-task implementation with per-task compile and commit, final
commit through the audit gate. Every stated lemma `Qed`; `Print Assumptions`
on the trace headline expected to be the boolp trio only.

## 12. Out of scope

- Bob/Charlie trace headlines; trace-level simulation headline.
- Replacing the counting axis's hand-written traces beyond the three-entry
  randomness correction of section 3.1.
- Any PPT/asymptotic internalization.
