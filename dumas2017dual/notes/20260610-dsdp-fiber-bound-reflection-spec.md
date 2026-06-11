# DSDP output-channel 1/m by full reflection — design spec (option B, corrected)

Date: 2026-06-10, corrected 2026-06-11. Branch: itp2026-dumas2017dual.
Scope: discharge the information-theoretic fiber bound `Pr[guess = V2] ≤ 1/m` at
the all-zero output-exposing endpoint with **no new assumptions** beyond the
already-committed predictor-losslessness `guess_lossless`, completing the chain
`dsdp_alice_secrecy_leak_S ≤ 1/m + 2·epsilon_cpa`.

Supersedes the option-A fallback (a localized `guess_fdist_success_le_invm`
hypothesis) in `20260610-dsdp-output-channel-derived-implementation-plan.md`.

## 0. Correction (2026-06-11): the committed games leak a degenerate S

The committed output-exposing games leak `S = −(r2 + r3)`, **not** the protocol
output `u1·v1 + u2·v2 + u3·v3`. The original step 2/3 (reflect, then read `S` off
the run) rested on the false premise that the game's `S` is the scalar product.

Evidence (all current code):
- **Symbolic trace** (`obs_of_procs_dsdp_leak_S`, `dsdp_game_symbolic.v:444`):
  the output term is `S = Dec(agg) − r2 − r3 + u1·v1`, with the aggregate
  (`HE_var 50`), `u1` (`HE_var 17`), `v1` (`HE_var 16`) occurring **only** inside
  `AO_recv_output`. `obs_value_names` returns `[::]` for `AO_recv_output`, so
  `collect_samples` never samples them and `resolve_term` maps them to the
  out-of-range `HE_var 10`.
- **Denotation** (`dsdp_game_code.v:349`): `HE_dec _ _ → Gplain 0`, and an
  out-of-range `HE_var → Gplain 0`.
- **Env trace** over `gc_eq` (de Bruijn `4 = r3`, `6 = r2`):
  `as_plain S = (0 − r2 − r3) + (0·0) = −(r2 + r3)`.
- **Cross-check** (`dsdp_program.v:282`, `dsdp_correctness.v`): the real output
  is `u1·v1 + u2·v2 + u3·v3`.

Consequence: the committed `guess_S_determined : S = dsdp_g` is false against this
game. The bound `1/m` still holds at the zero endpoint, but only by the trivial
direct-independence route (the whole view is `V2`-free), which this project
explicitly rejected as not security-meaningful
(`project_dsdp_it_leg_ssprove_merge`). The Infotheo fiber leg has nothing to
discharge.

## 1. Root cause, and why modeling decryption cannot fix it

Design-level cause: `S` was defined as a **decryption of the cipher aggregate**,
and the IND-CPA hybrid zeroes those ciphers, so a decryption-derived `S` is
`V2`-free at the all-zero endpoint by construction:

```
zero endpoint: c100 = enc 0,  a1 = enc r2,  a2 = enc r3,
               agg = enc(r2+r3),  Dec agg = r2+r3,
               S = (r2+r3) − r2 − r3 + u1·v1 = u1·v1     (still V2-free)
```

Zeroing the ciphers (Channel 2) necessarily zeroes the `V2`-content of any `S`
decrypted from them (Channel 1). The two channels are independent only if `S` is
modeled independently of the ciphers. A *correct* decryption model does not help
(it still gives `u1·v1` at the zero endpoint) and is not even locally expressible
in Alice's view (`agg` is a value she receives, not one her denotation builds).

## 2. Resolution: recompose S as the plaintext output

Leak `S` as the genuine protocol output `u1·v1 + u2·v2 + u3·v3`, computed from the
input weights and the secret samples and written into `S_output_cell`
independently of the cipher hybrid. The input weights `u1,u2,u3,v1` are **theorem
parameters** (not samples — decision R-u3-regular, §8), seeded into the game env;
only the secrets `v2,v3` and masks `r2,r3` are sampled. Then:
- `S` is written identically in the real and zero games (a plaintext computation,
  untouched by the hops), so the committed `2·epsilon_cpa` cipher leg is
  unaffected.
- At the zero endpoint the ciphers are `V2`-free but `S` carries `v2` through
  `u2·v2`, so conditioning on `S` pins `(v2,v3)` to an `m`-point fiber and the
  fiber `1/m` is genuine.

Provenance contract:
```
cipher channel  = lower(trace)               (single source of truth, committed)
output value S  = protocol correctness       (dsdp_computes_dot_product, cited)
```
The output channel is where **local-view security meets global correctness**:
security reasons over Alice's local trace, which cannot see that her output is the
scalar product; correctness, reasoning over the joint run, supplies it. No
mechanism is duplicated — the output node references the shared spec function
`dsdp_output`, not a re-typed copy.

## 3. What stands unchanged (committed, done; independent of the S value)

- The SSProve→Infotheo bridge `sdistr_to_fdist` + `Pr_sdistr_to_fdist`, and the
  connector `guess_success_sdistr_eq_fdist`
  (`guess_sdistr_success = guess_fdist_success`; heap-free pushforward).
- The generic reflection toolkit: `Pr_fst_map`, `Pr_fst_agree_locs`,
  `Pr_fst_closed`, `eq_in_dlet`, `Pr_code_preserves`.
- The reflection core: `denote_run_distr` + `denote_run_distrE`, the `drun_*`
  unfolds, `gc_eq`.
- Oracle resolution: `guess_resolved_par`, `resolve_game_{run,sget,v2get}`,
  `guess_resolved_oracles`.

## 4. The shared output function and the output-node recomposition (verified)

### 4.1 dsdp_output — the single source of truth for the output value

```coq
Definition dsdp_output {R : comNzRingType} (v1 u1 u2 u3 v2 v3 : R) : R :=
  u1 * v1 + u2 * v2 + u3 * v3.
```
Verified (`/tmp/output_probe.v`, `coqc` exit 0): the class is `comNzRingType`
(`plain : finComNzRingType`; `comRingType` is wrong), and the same function
instantiates at **both** `plain AHE` (game) and `'Z_m` (entropy).

Re-express the existing copies as wrappers (no fourth copy):
- `dsdp_program.v`: `alice_resultE : alice_result = dsdp_output v1 u1 u2 u3 v2 v3`
  (by `dsdp_computes_dot_product`).
- `dsdp_entropy.v`: the former `dsdp_g` renamed `dsdp_output`; `dsdp_outputE`
  relating the tupled and curried forms; downstream uses updated.

### 4.2 Trace re-derivation (`dsdp_game_symbolic.v`)

Per decision R-u3-regular (§8), the input weights `u1,u2,u3,v1` move OUT of the
sample prefix and become theorem parameters seeded into the game's initial env
(the construction generalizes `empty_denv` to a parameter-seeded env). The sample
prefix then samples only `v2,v3` (secrets) and `r2,r3` (masks). Make
`AO_recv_output` (or its lowering) yield the scalar-product term
`HE_add (HE_add (HE_mul u1 v1) (HE_mul u2 v2)) (HE_mul u3 v3)` over the seeded and
sampled indices, replacing the `Dec`-based term. Re-derive
`dsdp_alice_obs_leak_S` and `gc_eq`; the real indices come out of the rebuilt env.
(Designing the env-seeding mechanism is the first writing-plans task.)

### 4.3 denote_output_termE — the reference (verified shape)

```coq
Lemma denote_output_termE (e : denv AHE) :
  as_plain (denote_he pkey_of_party rand0 e output_term)
  = dsdp_output (as_plain (de_val_nth e iv1)) (as_plain (de_val_nth e iu1))
                (as_plain (de_val_nth e iu2)) (as_plain (de_val_nth e iu3))
                (as_plain (de_val_nth e iv2)) (as_plain (de_val_nth e iv3)).
Proof. by rewrite /dsdp_output //=. Qed.
```
Verified definitional (no `ring`); index-agnostic, so the placeholder probe
transfers to the real indices.

## 5. The fiber bound, now genuinely meaningful

With weights as parameters (§4.2), `guess_sample_fdist` is over the sampled
randomness only: `(V2,V3)` uniform secrets (plus masks), with `(V1,U1,U2,U3)` the
constant input RVs. Discharge the four entropy hypotheses over it:
- `guess_V2_uniform` — `(V2,V3)` uniform.
- `guess_VarRV_indep_inputs` — `(V2,V3) ⊥ (V1,U1,U2,U3)`, trivial since the inputs
  are constant.
- `guess_S_determined` — `S = dsdp_output(...)`, now provable via
  `denote_output_termE` and the recomposed game (was false before).
- `guess_indep_V2_given_S` — `guess ⊥ V2 | S`, delivered by `Pr_fst_agree_locs`
  framing the predictor off `V2_cell`.

The fiber instantiation carries the precondition `injective (fun v => u3 * v)` on
the parameter `u3` (decision R-u3-regular).

Then instantiate the entropy fiber for
`guess_fdist_success_le_invm : guess_fdist_success ≤ (card_msg)%:R^-1`, and
`guess_sdistr_success_le_invm` via the connector.

Entropy instantiation (route F, verified): relax the ring-generic fiber
(`dsdp_fiber_card_ring`/`Pr_dsdp_sol_uniform_ring`) from `finComUnitRingType` +
`u3 \is a GRing.unit` to `finComNzRingType` + `injective (fun v => u3 * v)`, then
instantiate at `R := plain AHE`. The card proof replaces `u3^-1` with the
bijective inverse from `inj_card_bij` (injective on a finite type is bijective).
A unit is a regular multiplier, so the generalization subsumes the existing
lemmas. No change to the homomorphic-encryption library; full AHE-genericity
kept. The earlier candidates — strengthening `plain` to `finComUnitRingType`
(library-wide) or specializing to a `'Z_(p*q)` scheme (loses genericity) — are
both unnecessary.

## 6. Composition (unchanged shape)

`guess_advantage_le` (`≤ 2·epsilon_cpa`, from `dsdp_advantage_derived_leak_S`;
re-confirm under the recomposed `S`), then the triangle. The final theorem
quantifies over the input-weight parameters with the regularity precondition:
`dsdp_alice_secrecy_leak_S : forall (u1 u2 u3 v1 : plain AHE),
injective (fun v => u3 * v) -> Pr(guessing_experiment predictor
(real_game_leak_S … u1 u2 u3 v1)) true ≤ (card_msg)%:R^-1 + 2·epsilon_cpa`.

## 7. Cited anchors, naming, notation

Cited unchanged: infotheo `dsdp_entropy` (`dsdp_fiber_card`,
`Pr_dsdp_sol_uniform`/`Pr_dsdp_sol_uniform_ring`, the RV interface);
SSProve nominal (`Pr_code_*`, `Pr_fst_*`, `dlet_uniform`, `distr.dmargin*`);
the committed derived chain (`real_game_leak_S`, `zero_game_leak_S`,
`dsdp_advantage_derived_leak_S`).

Naming: building blocks inside `Section dsdp_guess_distribution` are bare
`guess_*`; only the exported `dsdp_alice_secrecy_leak_S` keeps the project prefix.
`dsdp_g → dsdp_output` (the `g` is the opaque inherited constraint-function
symbol). Equation lemmas use the MathComp `E`-suffix **without** underscore
(`alice_resultE`, `dsdp_outputE`, `denote_output_termE`).

Notation: do **not** reuse `$`/`#` for `as_plain`/`de_val_nth` — both are
established piSMC data-wrapper notations in `pismc_scope` (`$ x := e x`
"encrypted", `# x := priv_key x`), so reusing `$` for `as_plain` inverts its
meaning. If brevity is wanted, pick fresh two-char tokens (the `*h`/`^h`/`E<>`
family) and grep-verify against the fiber file's open scopes at implementation.

## 8. Open items and risks

- **R-trace** (mechanical): the re-derivation in §4.2; the §4.3 proof is
  index-agnostic, so low risk once the trace is rebuilt.
- **R-entropy type-compatibility** (RESOLVED, route F): `plain AHE` is
  `finComNzRingType` and does **not** upgrade to `finComUnitRingType` (probe
  `/tmp/unit_probe2.v`: no free upgrade; `u3 \is a GRing.unit` is not even
  statable). Resolution: generalize `dsdp_fiber_card_ring`/
  `Pr_dsdp_sol_uniform_ring` to `finComNzRingType` + `injective (fun v => u3 * v)`
  (probe `/tmp/inj_route_probe.v`, `fiber_nz_card`, `coqc` exit 0), instantiate at
  `R := plain AHE`. No library change; genericity kept; subsumes the unit version.
- **R-u3-regular** (RESOLVED, decision 2026-06-11): `injective (u3 * ·)` ≡ `u3`
  regular/a unit; uniform `u3` is not always regular, so an unconditional 1/m would
  carry slack `Pr[u3 non-regular]`. **Decision: weights as parameters.** Model the
  input weights `u1,u2,u3,v1` as universally-quantified theorem parameters with
  precondition `injective (fun v => u3 * v)`; sample only `v2,v3` (secrets) and
  `r2,r3` (masks). Yields the clean worst-case `∀ regular u3, Pr ≤ 1/m +
  2·epsilon_cpa`; matches game-based security (adversary commits inputs) and the IT
  framework (InputRV conditioned). Consequence: the §4.2 trace rebuild seeds the
  weights into the game env rather than sampling them (env-seeding is the first
  writing-plans task). Rejected: sample `u3` from regulars (artificial input
  distribution, average-case); accept additive slack (non-clean headline).
- **R-2eps**: re-confirm `dsdp_advantage_derived_leak_S` with `S` written
  identically in real/zero (expected, since `S` no longer routes through the
  hops).
- The resulting `1/m` is the **meaningful fiber bound** (Channel 1 open at the
  zero endpoint), not the trivial direct-independence one.

## 9. Verification status

- `/tmp/output_probe.v` (throwaway, `coqc` exit 0): `dsdp_output` over
  `comNzRingType` at both `plain AHE` and `'Z_m`; `denote_output_termE` closes
  definitionally.
- `/tmp/unit_probe2.v` (throwaway, `coqc` exit 0): confirmed `plain AHE` is not
  `finComUnitRingType` and there is no free upgrade; `'Z_m` is, with the unit
  predicate and `dsdp_fiber_card_ring` usable.
- `/tmp/inj_route_probe.v` (throwaway, `coqc` exit 0): `fiber_nz_card` proved over
  `finComNzRingType` with `injective (u3 * ·)`, no `u3^-1`, no library change.
- No `Admitted`/`admit`/`Axiom` introduced; the only assumption remains the
  committed `guess_lossless`.
