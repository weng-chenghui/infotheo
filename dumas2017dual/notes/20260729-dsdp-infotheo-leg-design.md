# Design: infotheo-native computational leg for DSDP corrupted-Alice

Date: 2026-07-29
Status: draft, pre-audit
Target file: `dumas2017dual/dsdp/infotheo_leg/dsdp_alice_infotheo_secrecy.v` (single file)

## 1. Goal and context

One self-contained `.v` file that restates and proves the corrupted-Alice
computational-security results of the SSProve axis inside piSMC + infotheo
only, with zero SSProve imports. Reduction-form discipline is kept: every
epsilon is the real-or-zero advantage of an explicitly constructed reduction;
no axiom or hypothesis asserts any epsilon small.

Decisions fixed during brainstorming:

- Scope: DSDP-wired (imports the repo's AHE base and DSDP algebra; the
  SSProve axis stays untouched as a parallel track).
- Architecture: explicit product sample space ("B"): all distributional
  facts (uniformity, independence) are theorems of the product construction,
  not `Hypothesis` fields. Alice's own inputs are fixed parameters
  `w_v1 w_u1 w_u2 w_u3` mirroring the guess-fiber design (`const_RV`).
- Headlines: (i) guess bound, (ii) unpredictability corollary,
  (iii) simulator + distinguisher bound. The hybrid-entropy equality stays an
  internal lemma.
- No RSLR / no PPT internalization. Complexity reading lives on paper.

Protocol facts this file encodes (provenance: `dsdp_pismc.v:136-143`,
`dsdp_symbolic_exec.v:236`, `dsdp_entropy.v` `dsdp_constraint`):

- Alice receives exactly two non-decryptable ciphertexts:
  `enc pk_bob v2 _` and `enc pk_charlie v3 _`.
- Alice legitimately learns `S` with `S - u1*v1 = u2*v2 + u3*v3`.
- The 1/m zero-endpoint comes from the one-degree-of-freedom fiber of that
  constraint, requiring `injective (fun v => w_u3 * v)`.

## 2. Section parameters

```
Variables (AHE : AHEncType) (Renc : finType) (rand_of_renc : Renc -> rand AHE).
Variables (t_cipher : finType) (chcipher_of_cipher : cipher AHE -> t_cipher)
          (cipher_of_chcipher : t_cipher -> cipher AHE)
          (chcipher_of_cipherK : cancel chcipher_of_cipher cipher_of_chcipher).
Variable  pkey_of_party : party_id -> pub_key AHE.
Variables (w_v1 w_u1 w_u2 w_u3 : plain AHE).
Hypothesis w_u3_inj : injective (fun v : plain AHE => w_u3 * v).
```

`t_cipher` marshalling mirrors the SSProve axis (`indcpa_ror.v`) because
`cipher AHE` is an `nzRingType`, not a `finType`; infotheo RVs and `fdist`
need a `finType` codomain. `w_u3_inj` is the protocol security condition,
same premise as `dsdp_alice_guess_V2_zero_le`.

## 3. Sample space and view random variables

Free coordinates, each uniform, jointly a product (independence and
uniformity are theorems, not hypotheses):

```
Definition dsdp_alice_sampleT :=
  ((plain AHE * plain AHE)      (* v2, v3 *)
 * (plain AHE * plain AHE)      (* r2, r3   : Alice's mask plaintexts *)
 * (Renc * Renc)                (* rho2, rho3 : hop encryption randomness *)
 * (Renc * Renc)                (* ra1, ra2   : Alice's combine randomness *)
 * (Renc * Renc))%type.         (* rho2', rho3' : simulator's fresh randomness *)
Definition P : R.-fdist dsdp_alice_sampleT := (* product of fdist_uniform *).
```

RVs are coordinate projections in math-notation style (repo precedent
`V1 U1 S` in `dsdp_entropy.v`): `V2 V3 R2 R3 : {RV P -> plain AHE}`,
`Rho2 Rho3 RA1 RA2 Rho2' Rho3' : {RV P -> Renc}`.

Derived RVs:

```
Definition S : {RV P -> plain AHE} := w_u1 * w_v1 + w_u2 *o V2 + w_u3 *o V3.
  (* dsdp_constraint holds definitionally; no constraint hypothesis *)
Definition E2 : {RV P -> t_cipher} :=  (* enc pk_bob V2 (rand_of_renc Rho2) *)
Definition E3 : {RV P -> t_cipher} :=  (* enc pk_charlie V3 (rand_of_renc Rho3) *)
```

Views (`alice_viewT := (plain^2 * Renc^2 * plain * t_cipher * t_cipher)`-shaped
tuple; exact nesting fixed at implementation):

```
Definition AliceView           := [% R2, R3, RA1, RA2, S, E2, E3].
Definition AliceView_enc_zero1 := (* E2 slot replaced by enc pk_bob 0 Rho2 *).
Definition AliceView_enc_zero  := (* both slots zeroed, randomness Rho2' Rho3' *).
```

Naming precedent: `zero_game`/`game_enc_zero`/`all_zero` on the SSProve axis;
`BobView`/`CharlieView` for view RVs.

Fidelity note: Alice's two combine messages and the decrypted final hop are
deterministic functions of `AliceView` components and the fixed inputs. A
remark lemma `alice_view_full_of_reduced` exhibits the full corrupted view as
a deterministic image of `AliceView`; a corollary transfers every headline
bound to the full view. This closes the "you quietly dropped view components"
objection.

## 4. Computational infrastructure

```
Definition fdist_enc (pk : pub_key AHE) (v : plain AHE) : R.-fdist t_cipher :=
  fdistmap (fun r => chcipher_of_cipher (enc pk v (rand_of_renc r)))
           (fdist_uniform card_renc).

Record ror_adversary := {
  adv_context : finType ;                             (* side information *)
  adv_choose  : R.-fdist (plain AHE * adv_context) ;  (* plaintext + context *)
  adv_decide  : adv_context -> t_cipher -> bool }.

Definition ror_success_real (pk) (A : ror_adversary) : R :=
  Pr (adv_choose A `>>= fun ma =>
        fdistmap (adv_decide A ma.2) (fdist_enc pk ma.1)) [set true].
Definition ror_success_zero (pk) (A : ror_adversary) : R :=
  (* same with fdist_enc pk 0 *).
Definition ror_epsilon (pk) (A : ror_adversary) : R :=
  `| ror_success_real pk A - ror_success_zero pk A |.
```

Naming precedents: `fdist_enc` follows the infotheo `fdist_*` constructor
family; `ror_success_real`/`ror_success_zero` follow the
`oracle_encrypt_real`/`oracle_encrypt_zero` pair plus `guess_sdistr_success`;
`ror_epsilon` follows `indcpa_epsilon`; record and fields follow
`dsdp_indcpa_adversary`'s `adv_*` field style. `ror_epsilon` is the
infotheo-native `indcpa_epsilon`: a number attached to a concrete reduction,
never assumed small.

Distinguishers are input-aware, matching Lindell's Definition 4.1 in which
the distinguisher knows the parties' inputs:

```
D : plain AHE * plain AHE * alice_viewT -> bool     (* sees (v2, v3, view) *)
```

Hop reductions (explicit constructions; the only substantive new proofs):

```
Definition hop0_reduction (D) : ror_adversary :=
  (* context = all coordinates except rho2, plus derived values;
     choose = joint law of (V2, context); decide rebuilds the view around
     the challenge ciphertext in the E2 slot and runs D *)
Definition hop1_reduction (D) : ror_adversary := (* E3 slot, context includes
     the already-zeroed E2 sample *)

Lemma hop0_advantage (D) :
  `| Pr[ D on AliceView ] - Pr[ D on AliceView_enc_zero1 ] |
     <= ror_epsilon (pkey_of_party Bob) (hop0_reduction D).
Lemma hop1_advantage (D) : (* zero1 -> zero, pk_charlie, V3 *)
```

Proof shape: both probabilities are the two arms of the same
`fdistbind`/`fdistmap` refactoring of the product measure (equality, stated
as `<=`); coordinate independence is definitional in the product space.

## 5. Information-theoretic leg

Reuses the ring-generic fiber section of `dsdp_entropy.v`
(`dsdp_constraint_ring`, `linear_fiber` lemmas): conditionally on the fixed
inputs and `S`, the pair `(V2, V3)` is uniform on an `m`-element fiber that
projects bijectively to `V2` (by `w_u3_inj`). Spectator coordinates
(`R2, R3, RA1, RA2`, zeroed cipher slots) are peeled off by product
independence; 2-3 small bridging lemmas expected.

Zero endpoint (internal): for every `g : alice_viewT -> plain AHE`,
`Pr[ (g \o AliceView_enc_zero) = V2 ] <= (#|plain AHE|%:R)^-1`.
Candidate name `Pr_guess_enc_zero_le_invm`, precedent
`Pr_guess_fiber_le_invm` (blueprint) and `dsdp_alice_guess_V2_zero_le`.

## 6. Headlines

```
Theorem dsdp_alice_guess_V2_le (g : alice_viewT -> plain AHE) :
  `Pr[ (g `o AliceView) = V2 ]
    <= (#|plain AHE|%:R)^-1
       + ror_epsilon (pkey_of_party Bob)     (hop0_reduction (guess_test g))
       + ror_epsilon (pkey_of_party Charlie) (hop1_reduction (guess_test g)).

Theorem dsdp_alice_unpredictability_ge (g) :
  log (#|plain AHE|%:R) - log (1 + #|plain AHE|%:R * (eps0 g + eps1 g))
    <= - log `Pr[ (g `o AliceView) = V2 ].

Definition alice_simulator (s : plain AHE) : R.-fdist alice_viewT :=
  (* uniform masks x fdist1 s x fdist_enc pk_bob 0 x fdist_enc pk_charlie 0,
     bob_simulator product style *)

Lemma alice_simulator_factorization v s :   (* perfect, hybrid only *)
  `Pr[ AliceView_enc_zero = v | S = s ] = alice_simulator s v.

Theorem dsdp_alice_advantage_sim_le (D) :
  `| Pr[ D on (V2, V3, AliceView) ] - Pr[ D on (V2, V3, AliceView_sim) ] |
    <= ror_epsilon _ (hop0_reduction D) + ror_epsilon _ (hop1_reduction D).
```

`guess_test g` turns a guesser into an input-aware distinguisher
`fun '(v2, _, view) => g view == v2` (precedent: `guess_reduction`).
Headline names mirror `dsdp_alice_guess_V2_real_le`,
`dsdp_alice_unpredictability_entropy_ge`, `dsdp_advantage_sim_le`,
`bob_simulator`, `dsdp_simulator_factorization`; module namespace (new file)
disambiguates from the SSProve-axis originals.

## 7. Naming table (audit target)

| Candidate | Precedent | Notes |
|---|---|---|
| `fdist_enc` | infotheo `fdist_uniform`, `fdist_binary` | constructor family |
| `ror_adversary`, `adv_context/adv_choose/adv_decide` | `dsdp_indcpa_adversary` `adv_*` | |
| `ror_success_real/zero` | `oracle_encrypt_real/zero`, `guess_sdistr_success` | pair, not bool arg |
| `ror_epsilon` | `indcpa_epsilon` | |
| `AliceView`, `AliceView_enc_zero1`, `AliceView_enc_zero` | `BobView`, `game_enc_zero` | RV caps = math notation |
| `hop0_reduction`, `hop1_reduction` | `guess_reduction`, `zero_hop_prefix l` | |
| `hop0_advantage`, `hop1_advantage` | `dsdp_advantage_sim_le` family | or `*_advantage_le` |
| `Pr_guess_enc_zero_le_invm` | `Pr_guess_fiber_le_invm` | internal |
| `guess_test` | — weak precedent, audit | |
| `alice_simulator`, `alice_simulator_factorization` | `bob_simulator`, `dsdp_simulator_factorization` | |
| `dsdp_alice_guess_V2_le` | `dsdp_alice_guess_V2_real_le` | |
| `dsdp_alice_unpredictability_ge` | `dsdp_alice_unpredictability_entropy_ge` | |
| `dsdp_alice_advantage_sim_le` | `dsdp_advantage_sim_le` | |
| `dsdp_alice_sampleT`, `alice_viewT` | `smc_scalar_product_party_tracesT` | `T` suffix |

## 8. Soundness invariants (audit target)

1. No axiom/hypothesis asserts any epsilon small; epsilons are defined
   advantages of explicit reductions (reduction form).
2. No statement asserts a distributional equality between an encryption of a
   secret and anything independent of the secret; perfect equalities are
   claimed only for zeroed views.
3. Real-view claims are inequalities carrying `ror_epsilon` terms; entropy
   equalities are claimed only for zeroed views (internal lemma).
4. The hop lemmas' reductions must be total constructions; no samplability
   assumption beyond the product space itself.
5. `w_u3_inj` is the only protocol-level premise, identical in role to the
   SSProve axis premise.

## 9. Risks

- infotheo product-glue gaps: a local `product coordinate` toolkit section
  may grow; reusable, acceptable.
- Fiber lemmas are stated for abstract `P` + hypotheses; applying them to the
  concrete product `P` requires discharging their hypotheses (cheap here) and
  peeling spectators (small bridging lemmas).
- `alice_simulator`'s exact signature (masks inside the dirac or integrated
  out) is fixed at implementation; headline shapes unaffected.
- ln-algebra for the unpredictability corollary: expected available in
  `realType_ln`; else ~20 lines local.

## 10. Verification and process

- Build with the local opam switch (`~/Projects/coq/_opam`); per-lemma
  `rocq_check`; file added to `_CoqProject`.
- Implementation phases (each compiles before the next): product toolkit ->
  infra -> hop lemmas -> IT leg -> headlines. Atomic commits per phase.
- Pre-implementation audits (this spec): (a) adversarial soundness audit,
  (b) mathcomp naming/style audit against mathcomp-skills reference.md
  §10-§11 and repo precedents. Both Opus. Findings folded back here before
  any code.
- Pre-commit: rocq-auditor Stage 2 as usual.

## 11. Out of scope

- RSLR / any PPT internalization; asymptotic (security-parameter-indexed)
  statements.
- Replacing or modifying the SSProve axis; blueprint updates (follow-up).
- Bob/Charlie legs (already unconditional IT in `dsdp_main.v`).
