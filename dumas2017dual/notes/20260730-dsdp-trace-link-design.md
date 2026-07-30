# Design: closing the piSMC chain for the DSDP infotheo leg

Date: 2026-07-30
Status: probe-corrected, naming-audited draft (soundness audit pending)
Target file: `dumas2017dual/dsdp/infotheo_leg/dsdp_alice_trace_link.v`
Probe: `<session scratchpad>/probe_trace_link.v` (686 lines, exit 0, zero
axioms in the run-evaluation lemma), items P0-P3 all passing.

## 1. Goal

Make the corrupted-Alice security bound apply to the trace the piSMC
interpreter actually produces, rather than to a hand-transcribed view. Two
deliverables:

1. A machine-checked evaluation lemma for the DSDP protocol run at an
   abstract `AHEncType` (the idealized-scheme counterpart already exists as
   `dsdp_traces_ok`, `dumas2017dual/dsdp/core/dsdp_correctness.v:186`).
2. A trace-level guess headline: for every predictor reading the encoded
   Alice trace, success is at most `1/#|plain AHE|` plus the real-or-zero
   advantages of two explicitly constructed trace-level reductions.

This closes the last dashed line in the chain piSMC program -> trace -> view
random variable -> security bound, and retires the decrypt-on-receive caveat
about Charlie's re-encryption randomness (audit finding 15 of the 2026-07-30
leg audit): `RC2` becomes a modelled sample coordinate. The retirement is
recorded in the new file's `Scope.` header paragraph.

Scope decision (brainstorming): trace-level headline, reusing the leg's
machinery (option A1 — full-tuple evaluation then projection, mirroring
`dsdp_correctness.v`). Out of scope: Bob/Charlie trace headlines, a
trace-level simulation headline, and replacing the counting axis's traces.

## 2. Probe-forced architecture (four blocking findings)

**F-a. `interp_traces` is unavailable at abstract AHE.** It lives in
`smc/smc_interpreter.v` `Section traces` over `Variable data : eqType`;
`priv_key`/`pub_key` of `AHEncType` are bare `Type`
(`homomorphic_encryption/he_types.v:44-45`), so `di_data` is not an eqType
and `interp_traces 15 procs` does not typecheck. `dsdp_correctness.v` can
use it only because its idealized instance has `priv_key = pub_key = 'F_m`.

Consequence: the run is named and evaluated at the seq level,

```
Definition dsdp_run_traces : seq (seq (di_data DI)) :=
  (run_interp 15 dsdp_procs_std).2.
```

and Alice's trace is `nth [::] dsdp_run_traces 0`. The `n.-bseq` wrapper is
rebuilt with an explicit bound, not with `interp_traces` and not with `insub`
(whose `idP` is `Qed`-opaque and does not reduce).

**F-b. The RV codomain must be an encoded trace.** `cipher AHE` is an
`nzRingType`, both key sorts are bare `Type`. `n.-bseq T` and
`m.-tuple (n.-bseq T)` are finTypes when `T` is (`mathcomp/boot/tuple.v:690`,
`:420`), so the fix is a finite encoding of the data carrier:

```
Definition dsdp_trace_dataT : finType :=
  ((plain AHE + t_cipher) + unit + unit)%type.
Definition trace_data_of_di_data (x : di_data DI) : dsdp_trace_dataT :=
  (* plain kept; cipher marshalled by chcipher_of_cipher;
     both key sorts erased to unit marks *)
```

The summand order must mirror `std_data`'s `msgT + encT + privT + pubT` or
the encoder stops computing. Only `chcipher_of_cipher` is needed;
`cipher_of_chcipher` and its cancel play no part here. Erasing the key
entries loses nothing: Alice's key entry is the constant `dk_a`.

**F-c. Staged evaluation over an abstract-operation interface clone.**
Proving the run directly at `Standard_DSDP_Interface AHE` fails: `rewrite /=`
and `cbn` time out past 180 s, `vm_compute` kills the worker, and
`vm_compute` at the HB instance expands `enc` into a mixin match after which
no `rewrite` matches. The probe-verified construction:

- `DSDP_Interface_of_ops`: an interface value with the concrete `di_data`
  sum carrier (so `di_get_cipher` computes) but every crypto operation a
  section `Variable` (so `vm_compute` keeps it atomic). `di_Recv_dec` and
  `di_Recv_enc` are never read by the pismc programs, so the value is
  convertible to `Standard_DSDP_Interface AHE` and the two proc lists are
  equal `by []`.
- fuel splitting via the **existing** `interpD`
  (`smc/smc_session_types.v:872`, in scope transitively through
  `dsdp_program`), whose conclusion is a
  `let (ps', traces') := interp h1 ps traces in interp h2 ps' traces'`
  destructuring. Do not restate it (the probe's `probe_interp_addN` was a
  reinvention). Fuel arithmetic must stay in `%N`: `ring_scope` is open in
  this file family, so a bare `+` on the fuel elaborates to `GRing.add` and
  every rewrite silently misses.
- three `move Ht: <inner run> => S; vm_compute in Ht` stages, split exactly
  at the three stuck decryptions, each discharged by a `dec_correct`
  rewrite. Never abstract a fuel numeral (`5` occurs inside `10`); abstract
  the interpreter state.

**F-d. All three parties decrypt, and the party tags are constructors.**
A single `ek Alice = pub_of_priv dk_a` hypothesis is not enough — Bob's and
Charlie's `Recv_dec` also block the fixpoint. Defining
`ek p := match p with Alice => pub_of_priv dk_a | Bob => ... end` removes the
need for any key hypothesis, since `dec_correct` then fires by conversion.
The pismc programs route through `nat_to_party_id`, which reduces, so
statements name `Alice`/`Bob`/`Charlie` rather than `party_id` variables.

## 2b. Resolved hazards (verified 2026-07-30)

**H-1. `dsdp_procs` and friends are defined twice.** `dsdp_program.v:123/160/166`
and `dsdp_pismc.v:136/326/330` both define `palice`, `dsdp_saprocs`,
`dsdp_procs`; `nat_to_party_id` occurs 5 times in `dsdp_pismc.v` and 0 times
in `dsdp_program.v`. F-d needs the pismc programs, while the leg pulls in
`dsdp_program`, so bare names would resolve last-import-wins. Resolution: one
explicitly qualified alias at the top of the section, then use the alias
everywhere.

```
Let dsdp_procs_std := dsdp_pismc.dsdp_procs.   (* the only qualified use *)
```

The name `real_procs` from the probe is dropped: in this repo `real` names
the real-vs-zero game arm (`indcpa_fdist_success_real`, `hop0_real_armE`),
so `real_procs` misreads.

**H-2. `bseq_take` is taken.** `lib/ssr_ext.v:868` already defines
`bseq_take : n.-bseq T -> nat -> n.-bseq T` (truncating an existing bounded
sequence), and its neighbour `leq_take` (`:863`) needs `size s <= n` as a
premise, so neither serves the `seq -> n.-bseq` direction needed here.
Resolution: add one unconditional lemma to `lib/ssr_ext.v`'s
`Section bseq_lemmas`, beside `leq_take`, and build the `Bseq` inline:

```
Lemma take_size_bound (s : seq T) k : size (take k s) <= k.
```

Do not introduce a second `bseq_take`.

**H-3. Randomness index conventions clash.** The leg's `Rho2`/`Rho3` carry
`rb1`/`rc1` (party-number indexing), while the new `RB2`/`RC2` carry
`rb2`/`rc2` (party-letter + protocol index, following `RA1`/`RA2`). A reader
will mis-pair `Rho2` with `RB2`. Resolution, in this plan rather than a later
cleanup: rename the leg's `Rho2`/`Rho3` to `RB1`/`RC1` so the whole
randomness family reads uniformly, and give `RB2` a `Naming:` note recording
the mapping to the protocol's variables.

## 3. The computed trace (ground truth)

Probe-verified, with `d/e/kd := di_data_of_plain/cipher/priv_key DI`:

```
dsdp_run_traces =
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
`isAHEnc` mixin equations restated in rewritable form as `Epow_encE` and
`Emul_encE`:
`Epow (enc k m r) j = enc k (m * j) (rand_pow r j)` and
`Emul (enc k m1 r1) (enc k m2 r2) = enc k (m1 + m2) (rand_mul r1 r2)`.
These are AHE-generic facts about the `isAHEnc` mixin with no DSDP content,
so they belong in `homomorphic_encryption/ahe_enc.v` after
`HB.structure Definition AHEnc`, next to the existing `Emul_addM`
(`:91`) and `Epow_scalarM` (`:96`), as a separate atomic task.

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
`dsdp_entropy_trace.v`, citing `dsdp_run_traces_ok` as ground truth. Blast
radius is nil: that `Definition` feeds only `dsdp_result_correct`, a
plaintext-level `ring` identity.

## 4. Sample space, trace RV, and the transport shape

Extended space (probe-verified uniform):

```
Definition dsdp_alice_trace_sampleT : finType :=
  (dsdp_alice_sampleT * (Renc * Renc))%type.        (* new: rb2, rc2 *)
Definition alice_trace_sample_fdist : R.-fdist dsdp_alice_trace_sampleT :=
  alice_sample_fdist `x (fdist_uniform card_renc_pair).
Let card_trace_sample :
  #|dsdp_alice_trace_sampleT| = #|dsdp_alice_trace_sampleT|.-1.+1.
Lemma alice_trace_sample_fdistE :
  alice_trace_sample_fdist = fdist_uniform card_trace_sample.
```

Leg RVs lift by `\o fst`; new coordinates `RB2`, `RC2`. `RC2` is the only
new coordinate Alice's trace reads; `RB2` occurs only in Bob's and Charlie's
traces and is carried so the three-party evaluation lemma is instantiable.
The leg's globals are discharged over its section variables, so every use
supplies them; the leg's cardinality `Let`s do not export and are
re-declared here.

Trace RV (encoded, seq-level projection, explicit bseq bound):

```
Definition dsdp_procs_of_sample (s : dsdp_alice_trace_sampleT) :
  seq (proc (di_data DI)).
Definition AliceTrace :
  {RV alice_trace_sample_fdist -> 15.-bseq dsdp_trace_dataT} :=
  fun s => Bseq (take_size_bound _ 15)   (* over the encoded Alice trace *)
```

**Transport is one-directional (F-e).** The trace and `AliceView` are not a
cancel pair: the trace lacks `RA1`, `RA2` and adds the `rc2` ciphertext. So
the relation to state is

```
Lemma alice_trace_ofE :
  AliceTrace = alice_trace_of `o [% AliceView \o fst, RC2].
```

a determination of the trace by (view, fresh randomness), which is all a
guessing bound needs. Do not plan on two-way `cancel` transport. Name follows
`alice_spectator_ofE` (leg `:949`), the exact structural precedent
(RV = conversion `` `o `` other RV), not the invented head
`alice_trace_of_view`.

**Why the hops are re-run rather than averaged.** Reading the bound off the
existing view headline by averaging over `RC2` would make the epsilon a
per-`rc2` average, no longer the advantage of one explicit reduction, which
breaks reduction form. Instead the two hops are re-derived on the extended
space, where each hop is again a single explicit reduction whose context
carries `RB2`, `RC2`. (The pending soundness audit is asked to steelman the
averaging route; if a single reduction can absorb `rc2` into its own
context, section 6 shrinks substantially.)

## 5. Generalizing the leg's machinery

`enc_slot_resampleE` is stated over `alice_sample_fdist` but its proof uses
only `fdistmap_comp`, `fdist_prod_bindE`, `fdistmap_bind`. Probe-verified:
generalizing its binder to `(U : finType) (P : R.-fdist U)` keeps the same
proof body, and existing call sites are unaffected (they instantiate at
`alice_sample_fdist`). This is a one-lemma edit to the committed
`dsdp_alice_infotheo_secrecy.v` and a public-API change, so the leg's header
table entry for it must be reworded from the coordinate-specific phrasing to
the generalized statement.

The protocol-specific facts stay pinned; their extended-space analogues are
new, named here rather than left implicit: `hop0_trace_ctx_prod`,
`hop1_trace_ctx_prod`, `alice_trace_spectator_preT`,
`AliceTraceSpectatorPre`, `alice_trace_spectator_of`,
`alice_trace_spectator_ofE`, `alice_trace_spectator_indep`,
`alice_trace_V2_cond_le`. Probe P3 shows the cost: the context product law
over the extended space is the same `fdist_uniform_prod` +
`fdistmap_bij_uniform` proof with one extra `*` layer in the bijection and
two destructuring patterns.

## 6. Trace-level ladder, endpoint, headline

```
Definition AliceTrace_zero_prefix (i : nat) :
  {RV alice_trace_sample_fdist -> 15.-bseq dsdp_trace_dataT}
  (* i = 0 real; 1 zeroes the Bob-key entry; 2 also zeroes the Charlie-key
     entry.  The rc2 entry re-encrypts M3, a function of Sout and the masks,
     and is NOT a hop site: it carries no secret beyond Sout. *)
Notation AliceTrace_all_zero := (AliceTrace_zero_prefix 2).

Lemma alice_traceE : AliceTrace = AliceTrace_zero_prefix 0.
  (* the bridge: without it the headline (stated over AliceTrace) and the hop
     equalities (stated over the ladder) are unconnected *)

Lemma alice_trace_recrypt_slotE : (* the rc2 entry as a function of
     Sout and the mask coordinates -- proved, not asserted *)

Lemma hop0_trace_advantageE (D) :
  `| Pr[D on (V2, V3, AliceTrace_zero_prefix 0)]
     - Pr[D on (V2, V3, AliceTrace_zero_prefix 1)] |
  = indcpa_fdist_epsilon (pkey_of_party Bob) (hop0_trace_reduction D).
Lemma hop1_trace_advantageE (D) : (* prefix 1 -> 2, Charlie *)

Lemma guess_trace_all_zero_le_invm (g) :
  Pr alice_trace_sample_fdist
     [set t | (g `o AliceTrace_all_zero) t == (V2 \o fst) t]
    <= (#|plain AHE|%:R)^-1.

Theorem dsdp_alice_guess_fdist_trace_V2_real_le (g) :
  Pr alice_trace_sample_fdist
     [set t | (g `o AliceTrace) t == (V2 \o fst) t]
    <= (#|plain AHE|%:R)^-1
       + indcpa_fdist_epsilon (pkey_of_party Bob)
           (hop0_trace_reduction (distinguisher_of_guess g))
       + indcpa_fdist_epsilon (pkey_of_party Charlie)
           (hop1_trace_reduction (distinguisher_of_guess g)).
```

The axis/level token sits after the head noun (`hop0` + `trace` + role;
`dsdp_alice_guess` + `fdist` + `trace` + `V2_real_le`), following the repo's
`guess_sdistr_success` / `guess_fdist_success` convention, never as a
`trace_` prefix.

Endpoint route, mirroring the leg: the all-zero trace is a deterministic
function of `[% AliceTraceSpectator, Sout \o fst]` where the spectator block
is masks, combine randomness, `RB2`, `RC2`, both zeroed ciphertexts and the
`rc2` re-encryption of `M3`; that block is independent of `(V2, V3)` given
`Sout` (product independence plus the graphoid ladder `cinde_RV_unit` ->
`weak_union` -> `cpr_prd_unit_RV`), then `cinde_RV_comp` +
`cinde_diagonal_bound` with `alice_trace_V2_cond_le`. The fiber lemma
`Pr_dsdp_sol_uniform_ring` is stated over an arbitrary `P`, so it applies
once the extended-space uniformity premises are discharged from
`alice_trace_sample_fdistE`.

## 7. Naming table (audited)

| Name | Precedent | Note |
|---|---|---|
| `dsdp_run_traces` | `dsdp_traces` (two existing globals — must NOT reuse that name) | seq-level run; gives `_ok` a real head symbol |
| `dsdp_run_traces_ok` | `interp_traces_ok` (`smc_interpreter.v:315`), `dsdp_traces_ok` (`dsdp_correctness.v:186`), `alice_traces_ok`, `alice_view_full_ok` | `_ok` = object equals its ground-truth literal |
| (fuel split) | **reuse `interpD`** (`smc_session_types.v:872`) | do not declare `interp_addN`; `N` means negation, `D` means addition |
| `dsdp_trace_dataT` | `dsdp_alice_viewT`, `hop0_ctxT`, `alice_spectator_preT` | element type; distinct from the existing `dsdp_traceT` notations |
| `trace_data_of_di_data` | `di_data_of_plain/cipher/priv_key/pub_key` (`dsdp_interface.v:93-96`, rule at `:90`), `pub_of_priv` | total conversion; names the real source type |
| `take_size_bound` (in `lib/ssr_ext.v`) | `leq_take` (`ssr_ext.v:863`) | `bseq_take` is TAKEN with a different signature |
| `DSDP_Interface_of_ops` | `DSDP_Interface` (`dsdp_interface.v:80`), `Standard_DSDP_Interface` (`:183`), `_of_` rule (`:90`) | Mixed_Snake is the grandfathered upstream-class form here |
| `dsdp_procs_std` (alias) | — | the single qualified reference to `dsdp_pismc.dsdp_procs`; `real_procs` rejected (`real` = game arm) |
| `dsdp_alice_trace_sampleT`, `alice_trace_sample_fdist`, `alice_trace_sample_fdistE`, `card_trace_sample` (`Let`) | leg `:284`, `:289`, `:435`, `Let card_sample :431` | |
| `RB2`, `RC2` | `RA1`/`RA2` (leg `:306/:308`) = party letter + protocol index | `Naming:` note must record the `Rho2`/`Rho3` clash (H-3) |
| `AliceTrace`, `AliceTrace_zero_prefix`, `Notation AliceTrace_all_zero` | `AliceView`, `AliceView_zero_prefix`, `AliceView_all_zero` (leg `:340/:344/:345`) | |
| `alice_traceE` | leg's `AliceView` is a Notation for prefix 0, so no bridge was needed there | REQUIRED here: `AliceTrace` is an independent Definition |
| `alice_trace_of`, `alice_trace_ofE` | `alice_spectator_of`/`alice_spectator_ofE` (leg `:941/:949`) | not `alice_trace_of_viewE` (invented head, stacked tokens) |
| `hop0_trace_reduction`, `hop1_trace_reduction`, `hop0_trace_advantageE`, `hop1_trace_advantageE` | leg `hop0_reduction :585`, `hop0_advantageE :655`; token-position rule from `guess_fdist_success` | head noun first, level token in the middle |
| `hop0_trace_ctx_prod`, `hop1_trace_ctx_prod` | leg `hop0_ctx_prod :488`, `hop1_ctx_prod :554` | extended-space analogues |
| `AliceTraceSpectator`, `AliceTraceSpectatorPre`, `alice_trace_spectator_preT`, `alice_trace_spectator_of(E)`, `alice_trace_spectator_indep`, `alice_trace_spectator_cinde` | leg `AliceSpectator :935`, `AliceSpectatorPre :738`, `alice_spectator_*` family | |
| `alice_trace_V2_cond_le` | leg `alice_V2_cond_le :903` | |
| `alice_trace_recrypt_slotE` | leg `alice_spectator_law`; `E` for a slot-law equality | the `rc2` entry's law |
| `guess_trace_all_zero_le_invm` | leg `guess_all_zero_le_invm :993` | |
| `dsdp_alice_guess_fdist_trace_V2_real_le` | leg `dsdp_alice_guess_fdist_V2_real_le :1039` | `V2` says what is guessed, `real` marks the ladder end; both kept |
| `dsdp_procs_of_sample` | `_of` family | sample -> programs |
| `Epow_encE`, `Emul_encE` (in `ahe_enc.v`) | `Emul_addM :91`, `Epow_scalarM :96`, `EmulE`/`EpowE` (`dsdp_program.v:200/203`) | LHS heads are `Emul`/`Epow`; AHE-generic, wrong file if kept here |

Flat-namespace rule: the repo has no modules. Two pre-existing duplicate
globals constrain this file — `dsdp_traces` (`dsdp_correctness.v:168` and
`dsdp_entropy_trace.v:92`) and the `dsdp_traceT`/`dsdp_tracesT` notations —
so the new file exports `dsdp_run_traces` and must not become the first file
to import both sources.

## 8. Soundness invariants

1. Reduction form preserved: the two trace epsilons are
   `indcpa_fdist_epsilon` of explicitly constructed reductions; no
   hypothesis bounds them.
2. The evaluation lemma is proved, not assumed: no `Hypothesis` describes
   the trace contents; the only new modeling inputs are `dk_a dk_b dk_c` and
   the `ek`-by-match definition (which needs no key hypothesis).
3. The trace-level headline quantifies over every `g` on the encoded trace;
   the encoding must not discard secret-bearing content (keys erased to
   marks are constants; ciphertext marshalling must not collapse distinct
   ciphertexts — the pending soundness audit rules on whether injectivity of
   `chcipher_of_cipher` must be a hypothesis).
4. No claim that trace and view determine each other; only
   trace = function of (view, `RC2`), plus `alice_traceE` linking the
   headline's `AliceTrace` to the ladder's prefix 0.
5. `w_u3_inj` remains the only protocol premise; the leg's absent side
   conditions must not reappear.
6. The `rc2` entry's placement in the spectator block is a proved slot law
   (`alice_trace_recrypt_slotE`), not an assertion.

## 9. Risks

- The staged `vm_compute` evaluation is probe-verified but brittle against
  changes to the pismc programs or the fuel bound; the plan pins the exact
  stage boundaries and records why each exists.
- Extended-space re-proofs of the ladder are mechanical but tuple-shape
  sensitive; keep the nesting of the extended context identical to the
  probe's.
- Estimated size: evaluation machinery ~250 lines, extended-space ladder and
  headline ~350-450 lines. Kept as its own file (the leg is already 1451
  lines).

## 10. File conventions

Matching the leg's actual preamble
(`dsdp_alice_infotheo_secrecy.v:1-8`, `:176-185`):

- Imports in blocks: `From HB Require Import structures.` first, then the
  `From mathcomp` lines, then project `Require Import` lines (including
  `dsdp_pismc` — see H-1 for the aliasing discipline).
- `(**md ... *)` header after the imports: `# Title`; purpose paragraph;
  a `Headline results:` paragraph naming each headline; the `==`-aligned
  table documenting every public definition; a `Scope.` paragraph carrying
  the caveats (average-case over honest inputs; single-query fixed-key
  epsilons; bounds vacuous once epsilons exceed 1; efficiency reading on
  paper) **and recording that the decrypt-on-receive `rc2` caveat is
  retired by this file**; and a notation-promotion note for
  `AliceTrace_all_zero`.
- Setup in the leg's order: `Import Order.TTheory GRing.Theory Num.Def
  Num.Theory.` then `Set Implicit Arguments.`, `Unset Strict Implicit.`,
  `Import Prenex Implicits.` (the leg does not use `Unset Printing Implicit
  Defensive.`).
- Four scope lines: `Local Open Scope ring_scope. / reals_ext_scope. /
  proba_scope. / fdist_scope.` — `ring_scope` being open is what makes the
  `%N` fuel discipline of F-c load-bearing.
- Statement comments: declarative sentence, plus a trailing `Naming:`
  sentence only where a name needs defending (the leg uses it selectively,
  16 times), never status or effort narration.
- Cardinality facts and glue are `Let`; headlines are bare
  `Theorem`/`Corollary`.
- `Arguments ... : clear implicits.` after `End` if any record is declared
  (precedent `dsdp_interface.v:128-135`; the leg's in-section placement is a
  deviation, not a model).
- 80 columns, ASCII, per-lemma `rocq_check`, pre-commit rocq-auditor
  Stage 2.

## 11. Verification process

Probe done (P0-P3, file kept). Naming audit done and folded in. Soundness
audit pending; its findings are folded before writing-plans. Then
task-by-task implementation with per-task compile and commit.

Task-level scope beyond the new file: `lib/ssr_ext.v` (`take_size_bound`),
`homomorphic_encryption/ahe_enc.v` (`Epow_encE`, `Emul_encE`),
`dsdp_alice_infotheo_secrecy.v` (generalize `enc_slot_resampleE`, rename
`Rho2`/`Rho3` to `RB1`/`RC1`, reword the affected header rows),
`dsdp_entropy_trace.v` (the three-entry randomness correction of 3.1). Each
is its own atomic task.

The plan carries a mandatory `rocq:golf` stage after the last proving task
and before the header/style task: proof bodies only, never a statement, an
identifier, a statement comment, or the header table; re-verified by a full
compile, a zero `Admitted`/`Abort`/`Axiom` grep, and unchanged
`Print Assumptions` on the headline. The final commit goes through the
rocq-auditor gate unbypassed.

## 12. Out of scope

- Bob/Charlie trace headlines; trace-level simulation headline.
- Replacing the counting axis's hand-written traces beyond the three-entry
  randomness correction of section 3.1.
- Any PPT/asymptotic internalization.
