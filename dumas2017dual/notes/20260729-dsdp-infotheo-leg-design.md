# Design: infotheo-native computational leg for DSDP corrupted-Alice

Date: 2026-07-29
Status: audited draft (adversarial soundness audit + mathcomp naming audit
applied; see Audit resolution log)
Target file: `dumas2017dual/dsdp/infotheo_leg/dsdp_alice_infotheo_secrecy.v`
(single file)

## 1. Goal and context

One self-contained `.v` file that restates and proves the corrupted-Alice
computational-security results of the SSProve axis inside piSMC + infotheo
only, with zero SSProve imports. Reduction-form discipline is kept: every
epsilon is the real-or-zero advantage of an explicitly constructed reduction;
no axiom or hypothesis asserts any epsilon small.

Scope caveat (mirrors `dsdp_simulator.v:234-235`): all statements are
average-case over the honest inputs `V2, V3`, which are sampled uniformly
inside the experiment; this is the same scope as the SSProve axis. A
per-input variant of the simulation headline (inputs as section parameters,
Dirac `adv_choose`) would be strictly stronger and is recorded as follow-up,
not in this file.

Decisions fixed during brainstorming:

- Scope: DSDP-wired (imports the repo's AHE base and DSDP algebra; the
  SSProve axis stays untouched as a parallel track).
- Architecture: explicit product sample space ("B"): all distributional
  facts (uniformity, independence) are theorems of the product construction,
  not `Hypothesis` fields. Alice's own inputs are fixed parameters
  `w_v1 w_u1 w_u2 w_u3` mirroring the guess-fiber design (`const_RV`).
- Headlines: (i) guess bound, (ii) unpredictability corollary,
  (iii) simulator + distinguisher bound against an explicit ideal-world
  joint. The hybrid conditional-law lemma stays internal.
- No RSLR / no PPT internalization. Complexity reading lives on paper.

Protocol facts this file encodes (provenance: `core/dsdp_pismc.v:134-143`,
`symbolic_game/dsdp_symbolic_exec.v:236`, `counting/dsdp_entropy.v:486`
ring-generic `dsdp_constraint_ring`):

- Alice receives exactly two non-decryptable ciphertexts:
  `enc pk_bob v2 _` and `enc pk_charlie v3 _`.
- Alice legitimately learns `S = dsdp_output w_v1 w_u1 w_u2 w_u3 v2 v3`
  (`core/dsdp_program.v:39-41`), i.e. `u1*v1 + u2*v2 + u3*v3`.
- The 1/m zero-endpoint comes from the one-degree-of-freedom fiber of that
  constraint, requiring `injective (fun v => w_u3 * v)`.
- piSMC model note: `#dk`-receives bind the decrypted plaintext
  (decrypt-on-receive), so the final hop contributes its plaintext, not a
  ciphertext, to Alice's view, and no Charlie-side encryption randomness
  enters the sample space.

## 2. Section parameters

```
Variables (AHE : AHEncType) (Renc : finType) (index_renc : nat).
Hypothesis card_renc : #|Renc| = index_renc.+1.
Variable  rand_of_renc : Renc -> rand AHE.
Variables (t_cipher : finType)
          (chcipher_of_cipher : cipher AHE -> t_cipher)
          (cipher_of_chcipher : t_cipher -> cipher AHE).
Hypothesis chcipher_of_cipherK :
  cancel chcipher_of_cipher cipher_of_chcipher.
Variable  pkey_of_party : party_id -> pub_key AHE.
Variables (w_v1 w_u1 w_u2 w_u3 : plain AHE).
Hypothesis w_u3_inj : injective (fun v : plain AHE => w_u3 * v).
```

`card_renc` in `.+1` form because `fdist_uniform` requires
`#|A| = n.+1` (`probability/fdist.v:421-437`); without it `Renc` could be
empty and the sample space unbuildable. `#|plain AHE| >= 2` is derivable
(`finComNzRingType`), exposed as `Let`s in `card_R_gt0` style
(`counting/dsdp_entropy.v:474-483`). `t_cipher` marshalling mirrors
`indcpa_ror.v` because `cipher AHE` is an `nzRingType`, not a `finType`.
`w_u3_inj` is the protocol security condition, same premise as
`dsdp_alice_guess_V2_zero_le`. The SSProve-axis side conditions
`guess_lossless`, `guess_full_lossless`, `card_renc_neq`, `Hmsg_bij`,
`predictor_locs_disj` have no counterpart here and must not reappear.

## 3. Sample space and view random variables

Free coordinates, each uniform, jointly a product (independence and
uniformity are theorems, not hypotheses):

```
Definition dsdp_alice_sampleT :=
  ((plain AHE * plain AHE)      (* v2, v3 *)
 * (plain AHE * plain AHE)      (* r2, r3 : Alice's mask plaintexts *)
 * (Renc * Renc)                (* rho2, rho3 : hop encryption randomness *)
 * (Renc * Renc))%type.         (* ra1, ra2 : Alice's combine randomness *)
Definition alice_sample_fdist : R.-fdist dsdp_alice_sampleT :=
  (* product of fdist_uniform applied to the .+1 cardinality equations *).
```

No simulator-only randomness coordinates: the all-zero view reuses
`Rho2, Rho3` (audit F6); the resampling content lives in one named lemma
(section 4).

RVs are coordinate projections in math-notation style: `V2 V3 R2 R3 :
{RV alice_sample_fdist -> plain AHE}`, `Rho2 Rho3 RA1 RA2 :
{RV alice_sample_fdist -> Renc}` (`Implicit Types` to keep ascriptions
short). Derived RVs:

```
Definition Sout : {RV alice_sample_fdist -> plain AHE} :=
  uncurry2 (dsdp_output w_v1 w_u1 w_u2 w_u3) `o [% V2, V3].
  (* curried head needs the uncurried composition idiom, probe C2 *)
Definition E_bob_v2     : {RV alice_sample_fdist -> t_cipher} :=
  (* chcipher_of_cipher (enc (pkey_of_party Bob) V2 (rand_of_renc Rho2)) *)
Definition E_charlie_v3 : {RV alice_sample_fdist -> t_cipher} :=
  (* same with Charlie, V3, Rho3 *)
```

`Sout` (not `S`: shadows the `nat` successor; the repo already made this
rename in `dsdp_guess_fiber.v:865`) is `dsdp_output` composed on `[%V2, V3]`,
so `dsdp_constraint_ring` holds definitionally and the equation is pinned to
the SSProve axis' `S`.

Views, as one indexed family mirroring `zero_hop_prefix i`
(`symbolic_game/dsdp_game_code.v:93`):

```
Definition AliceView_zero_prefix (i : nat) :
  {RV alice_sample_fdist -> dsdp_alice_viewT} :=
  (* [% R2, R3, RA1, RA2, Sout, C2 i, C3 i ] where C2/C3 slots carry
     enc of the true plaintext for hops >= i and enc of 0 for hops < i *)
Notation AliceView          := (AliceView_zero_prefix 0).   (* real *)
Notation AliceView_all_zero := (AliceView_zero_prefix 2).   (* endpoint *)
```

(`all_zero` after `dsdp_game_derivation.v:673`; the retired
`game_enc_zero` name lives only in `legacy/` and is not used.)

Fidelity remark (piSMC decrypt-on-receive model, section 1): Alice's two
outgoing combines and the decrypted final hop are deterministic functions of
view components and fixed weights (`palice`, `core/dsdp_pismc.v:134-143`).
A function `alice_view_full_of` and lemma `alice_view_full_ok` exhibit the
full corrupted view as a deterministic image of `AliceView`; a corollary
transfers every headline bound to the full view.

## 4. Computational infrastructure

```
Definition enc_fdist (pk : pub_key AHE) (v : plain AHE) :
    R.-fdist t_cipher :=
  fdistmap (fun r => chcipher_of_cipher (enc pk v (rand_of_renc r)))
           (fdist_uniform card_renc).

Record indcpa_fdist_adversary := {
  adv_context : finType ;                        (* side information *)
  adv_choose  : R.-fdist adv_context ;
  adv_plain   : adv_context -> plain AHE ;       (* challenge plaintext *)
  adv_decide  : adv_context -> t_cipher -> bool }.

Definition indcpa_fdist_success_real (pk) (A : indcpa_fdist_adversary)
    : R :=
  Pr (adv_choose A >>= fun c =>
        fdistmap (adv_decide A c) (enc_fdist pk (adv_plain A c)))
     [set true].
Definition indcpa_fdist_success_zero (pk) (A : indcpa_fdist_adversary)
    : R := (* same with enc_fdist pk 0 *).
Definition indcpa_fdist_epsilon (pk) (A : indcpa_fdist_adversary) : R :=
  `| indcpa_fdist_success_real pk A - indcpa_fdist_success_zero pk A |.
```

The challenge plaintext is a function of the context (`adv_plain`), so a
reduction whose context decouples from its plaintext is unrepresentable
(audit F5). No `priv_key` is in scope, so no reduction can decrypt.
`>>=` is infotheo's fdist bind (`fdist_scope`). Naming: `indcpa_` is the
established stem (`indcpa_epsilon`), `fdist` the axis token
(`guess_fdist_success` vs `guess_sdistr_success`), `_success_real/_zero`
after `oracle_encrypt_real/zero` + `guess_sdistr_success_real`; `ror_*` has
no identifier precedent in the repo. `enc_fdist` follows the domain-fdist
suffix convention (`guess_sample_fdist`, `sdistr_to_fdist`), not the
type-generic `fdist_*` library family. Field prefix `adv_` follows
`dsdp_indcpa_adversary`; its four fields are disjoint from that record's six
(pre-commit gate re-checks this, since projections are global constants and
the repo has no modules).

Distinguishers are input-aware (the distinguisher knows the honest inputs;
average-case scope per section 1):

```
D : plain AHE * plain AHE * dsdp_alice_viewT -> bool   (* (v2, v3, view) *)
```

Resampling lemma (the load-bearing product fact, audit F6; generalized per
probe correction C1 — a fixed plaintext is too weak, since the hop's
challenge plaintext `V2` is itself a context coordinate). For a coordinate
`Rho` read by no component of `Ctx` and a context-reading slot map
`k : ctxT -> Renc -> t_cipher` (a LEMMA binder, not a section `Variable`,
so both arms instantiate it):

```
Lemma enc_slot_resampleE k :
  `p_ [% Ctx, (fun t => k (Ctx t) (Rho t)) : {RV _ -> t_cipher}]
    = (`p_ Ctx) `X (fun a => fdistmap (k a) (`p_ Rho)).
```

(kernel `fdist_prod` `` `X ``, probe-verified provable monadically via
`fdist_prod_bindE`/`fdistmap_bind`/`fdist_prod1`/`fdistmap_comp`; the
`>>=` form is a one-line corollary.) Supporting glue toolkit, probe-verified
absent from infotheo and ~30 lines total: `fdist_prod_bindE`
(`Q `X W = Q >>= fun a => fdistmap (pair a) (W a)`), `fdistmap_bind`
(map-bind swap, via `fdistbindA`), `Pr_fdistmap_bool`
(`Pr (fdistmap D m) [set true] = Pr m [set t | D t]`), `fdist_prod2`
(`(Q1 `x Q2)`2 = Q2`), plus coordinate-law and independence helpers
(`fdist_prod1`, `prod_dist_inde_RV`, `inde_dist_of_RV2`). `eq_fdistbind` /
`eq_fdistmap` do not exist: use `congr` + `boolp.funext`.

Hop reductions and hop equalities (audit F7: equalities, not `<=` — the
same proof, and a mis-typed view can no longer yield a vacuously true
bound):

```
Definition hop0_reduction (D) : indcpa_fdist_adversary :=
  (* context = the full coordinate tuple minus rho2; adv_plain = the v2
     component; adv_decide rebuilds the view around the challenge in the
     E_bob_v2 slot, computes Sout from context, runs D *)
Definition hop1_reduction (D) : indcpa_fdist_adversary :=
  (* context = full tuple minus rho3 plus the zeroed hop-0 cipher sample;
     adv_plain = the v3 component; Sout computed from context *)

Lemma hop0_advantageE (D) :
  `| Pr[ D on (V2, V3, AliceView_zero_prefix 0) ]
     - Pr[ D on (V2, V3, AliceView_zero_prefix 1) ] |
  = indcpa_fdist_epsilon (pkey_of_party Bob) (hop0_reduction D).
Lemma hop1_advantageE (D) : (* prefix 1 -> 2, Charlie, hop1_reduction *)
```

Proof shape: both probabilities are the two arms of the same
`fdistbind`/`fdistmap` refactoring of the product measure via
`enc_slot_resampleE`; `Sout` is recomputed inside `adv_decide` from the
context, which carries `V2` (hop 0) resp. `V2, V3` (hop 1), so the
challenge plaintext and the leak stay jointly distributed (audit F3/F5).

## 5. Information-theoretic leg

Template: the existing zero-endpoint chain of `dsdp_guess_fiber.v`,
re-proved over `alice_sample_fdist` (its originals live in a section over
`guess_sample_fdist` and cannot be imported; ~250 lines of copy-with-P-swap,
audit F11):

- `Pr_dsdp_sol_uniform_ring` (`counting/dsdp_entropy.v:558-577`,
  `finComNzRingType`, conditional LAW, exact fit for `plain AHE`) gives
  `(V2,V3) | (fixed inputs, Sout)` uniform on the fiber;
- marginalize `V3` through the `w_u3_inj` bijection:
  `` `Pr[ V2 = a | Sout = s ] = #|plain AHE|%:R^-1 ``
  (template `guess_V2_cond_Sout`, `dsdp_guess_fiber.v:1443-1490`, zero-mass
  case split per `:1493-1503`);
- `Sout_uniform : `p_ Sout = fdist_uniform card_plain` (from `w_u3_inj`;
  discharges the nonzero-mass guards, audit F9);
- spectator peeling is conditional independence, not ad-hoc bridging:
  `cinde_RV_comp` (`lib/extra_proba.v:465-466`) turns "the spectator block
  is conditionally independent of `V2` given `Sout`" into the same for
  `g `o view`, for every `g`; then
  `cinde_diagonal_bound` (`lib/extra_proba.v:619`) closes:

```
Lemma guess_all_zero_le_invm (g : dsdp_alice_viewT -> plain AHE) :
  Pr alice_sample_fdist [set t | (g `o AliceView_all_zero) t == V2 t]
    <= (#|plain AHE|%:R)^-1.
```

Statement form per probe C3: `` `Pr[ X = a ] `` is `pfwd1` with a value on
the right — there is no RV-versus-RV form — so guess events are stated as
`Pr _ [set t | _ t == _ t]`, exactly what `cinde_diagonal_bound` produces
(cf. `dsdp_guess_fiber.v:226`). No entropy detour: the chain is
conditional-law all the way.

## 6. Headlines

```
Theorem dsdp_alice_guess_fdist_V2_real_le
    (g : dsdp_alice_viewT -> plain AHE) :
  Pr alice_sample_fdist [set t | (g `o AliceView) t == V2 t]
    <= (#|plain AHE|%:R)^-1
       + indcpa_fdist_epsilon (pkey_of_party Bob)
           (hop0_reduction (distinguisher_of_guess g))
       + indcpa_fdist_epsilon (pkey_of_party Charlie)
           (hop1_reduction (distinguisher_of_guess g)).

Theorem dsdp_alice_unpredictability_fdist_ge (g)
    (Hpos : 0 < Pr alice_sample_fdist
                   [set t | (g `o AliceView) t == V2 t]) :
  log (#|plain AHE|%:R) - log (1 + #|plain AHE|%:R * (eps0 g + eps1 g))
    <= - log (Pr alice_sample_fdist
                [set t | (g `o AliceView) t == V2 t]).

Definition dsdp_alice_simulator (s : plain AHE) :
    R.-fdist dsdp_alice_viewT :=
  (* uniform masks x uniform RA-coordinates x fdist1 s
     x enc_fdist pk_bob 0 x enc_fdist pk_charlie 0, bob_simulator style *)

Lemma dsdp_alice_view_cond_sim v v2 v3 :        (* the load-bearing one *)
  `Pr[ AliceView_all_zero = v | [% V2, V3] = (v2, v3) ]
    = dsdp_alice_simulator (dsdp_output w_v1 w_u1 w_u2 w_u3 v2 v3) v.
Corollary dsdp_alice_view_cond_sim_S v s :      (* S-conditioned form *)
  `Pr[ Sout = s ] != 0 ->
  `Pr[ AliceView_all_zero = v | Sout = s ] = dsdp_alice_simulator s v.

Definition alice_ideal_joint :
    R.-fdist (plain AHE * plain AHE * dsdp_alice_viewT) :=
  `p_ [% V2, V3] >>= fun vv =>
     fdistmap (fun v => (vv.1, vv.2, v))
       (dsdp_alice_simulator (dsdp_output w_v1 w_u1 w_u2 w_u3 vv.1 vv.2)).

Theorem dsdp_alice_sim_advantage_fdist_le (D) :
  `| Pr[ D `o [% V2, V3, AliceView] = true ]
     - Pr (fdistmap D alice_ideal_joint) [set true] |
    <= indcpa_fdist_epsilon _ (hop0_reduction D)
       + indcpa_fdist_epsilon _ (hop1_reduction D).
```

The simulator is load-bearing (audit F1): the ideal world is
`alice_ideal_joint`, built from the honest-input law and
`dsdp_alice_simulator` fed the true output — so the simulated view carries
the true `Sout` and no `(V2,V3,S)`-consistency check helps the
distinguisher (audit F10). The `[%V2,V3]`-conditioned factorization is the
one the sim headline consumes; the `S`-conditioned form is a corollary
(audit F2, mirroring `bob_view_cond_sim` vs `bob_view_cond_sim_xy`,
`du2002/spp_simulator.v:173,215`). `Hpos` guards `log 0 = 0` (audit F4,
mirroring `dsdp_main.v:871-874`). `distinguisher_of_guess g` is the
guesser-to-distinguisher conversion `fun '(v2, _, view) => g view == v2`
(total conversion, `X_of_Y` applies; repo `_of_` family).
`dsdp_alice_sim_advantage_fdist_le` does not reuse the `advantage_sim_le`
name because it does not instantiate that predicate
(`smc/ssprove_ext_simulator.v:44`).

## 7. Naming table (audited)

| Chosen | Precedent | Note |
|---|---|---|
| `enc_fdist` | `guess_sample_fdist`, `sdistr_to_fdist` | domain `_fdist` suffix |
| `indcpa_fdist_adversary`; fields `adv_context/adv_choose/adv_plain/adv_decide` | `indcpa_epsilon`; `dsdp_indcpa_adversary` `adv_*` | field-disjointness gate |
| `indcpa_fdist_success_real/_zero` | `guess_sdistr_success_real`, `oracle_encrypt_real/zero` | not `Pr_*` (that is a lemma family) |
| `indcpa_fdist_epsilon` | `indcpa_epsilon` + axis token | |
| `alice_sample_fdist` | `guess_sample_fdist` | not `P` (universal section-Variable name) |
| `dsdp_alice_sampleT`, `dsdp_alice_viewT` | `smc_scalar_product_party_tracesT` | shared prefix |
| `Sout` | `dsdp_guess_fiber.v:865` | `S` shadows nat successor |
| `E_bob_v2`, `E_charlie_v3` | `E_bob_d2`, `E_charlie_vur3` (`dsdp_main.v:407`) | key visible in name |
| `AliceView_zero_prefix i`; notations `AliceView`, `AliceView_all_zero` | `zero_hop_prefix i`, `all_zero` | indexed family; global-scope promotion noted in header |
| `hop0_reduction`, `hop1_reduction` | `guess_reduction` | |
| `hop0_advantageE`, `hop1_advantageE` | `_eq`/`E` equation suffix; `dsdp_main.v:750-755` naming note | equality form supersedes `_le` |
| `enc_slot_resampleE` | equation suffix | DISCUSS at implementation |
| `guess_all_zero_le_invm` | `guess_fdist_success_le`, `all_zero` | not `Pr_guess_enc_zero_le_invm` (retired hypothesis name, H002 bad example) |
| `distinguisher_of_guess` | repo `_of_` total-conversion family | alt `guess_distinguisher` |
| `dsdp_alice_simulator`, `dsdp_alice_view_cond_sim`, `_cond_sim_S` | `bob_simulator`, `bob_view_cond_sim(_xy)`, `dsdp_simulator_factorization` | `dsdp_` prefix avoids SPP near-collision |
| `alice_ideal_joint` | `guess_joint_fdist` | DISCUSS: `dsdp_alice_ideal_joint`? |
| `dsdp_alice_guess_fdist_V2_real_le` | `dsdp_alice_guess_V2_real_le` + axis token after `guess` (`guess_fdist_success`) | token order DISCUSS |
| `dsdp_alice_unpredictability_fdist_ge` | `dsdp_alice_unpredictability_entropy_ge` | |
| `dsdp_alice_sim_advantage_fdist_le` | `dsdp_advantage_sim_le` | reordered: not an `advantage_sim_le` instance |
| `alice_view_full_of` + `alice_view_full_ok` | `bob_ext` + `bob_ext_ok` | function/lemma split |

Flat-namespace rule (no `Module` anywhere in the repo): every headline and
global carries an axis token or `dsdp_alice` prefix so joint imports with
`dsdp_main.v` stay unambiguous; blueprint `\rocq{}` references stay
distinct.

## 8. Soundness invariants (audit-hardened)

1. No axiom/hypothesis asserts any epsilon small; epsilons are defined
   advantages of explicit reductions (reduction form). Bounds may exceed 1;
   the efficiency reading is a paper-level remark (same status as the
   SSProve axis).
2. No statement asserts a distributional equality between an encryption of
   a secret and anything independent of the secret; perfect equalities are
   claimed only for zeroed views.
3. Real-view claims are inequalities carrying `indcpa_fdist_epsilon` terms.
4. Hop reductions are total constructions; `adv_plain` makes
   plaintext/context decoupling unrepresentable; hop lemmas are equalities.
5. `w_u3_inj` is the only protocol-level premise; the SSProve-axis
   side-condition list must not reappear (section 2).
6. Headline (ii) carries `Hpos`; conditional statements carry nonzero-mass
   guards or discharge them via `Sout_uniform`.
7. Thesis-facing caveats recorded here, to be stated rather than papered
   over: the per-hop epsilon is single-query at a fixed key
   (vs `indcpa_ror.v`'s multi-query party-indexed oracle — related, not the
   same number); the adversary is a plain-function record, a weaker footing
   for the paper PPT reading than SSProve's `raw_package`; conversely
   (i)/(ii) quantify over every `g` (min-entropy strength) and the
   side-condition surface shrinks to `w_u3_inj` + marshalling.

## 9. Risks

- The ~250-line P-swap re-proof of the `dsdp_guess_fiber.v:1419-1685`
  chain is mechanical but sensitive to tuple-shape mismatches; keep the
  view tuple nesting identical to the fiber chain's conditioning tuple.
- infotheo product-glue toolkit: confirmed needed and confirmed small
  (probe C8, ~30 lines: the four glue lemmas of section 4 plus coordinate
  law/independence helpers); reusable, acceptable.
- `dsdp_alice_simulator`'s slot layout must match `dsdp_alice_viewT`
  nesting exactly; fixed at implementation together with
  `enc_slot_resampleE`.
- ln-algebra for headline (ii): `1/m + e0 + e1 = (1 + m*(e0+e1))/m`
  exactly; guards via `Hpos` and `normr_ge0`.

## 10. File conventions (added per naming audit)

- Header: `(**md ... *)` block after imports (du2002/smc/probability
  style), 80-column padded frame, triple-backtick `==`-aligned table
  documenting every public definition (~20 entries budgeted).
- Setup block in exact order: `Set Implicit Arguments.` /
  `Unset Strict Implicit.` / `Unset Printing Implicit Defensive.` /
  `Import Order.TTheory GRing.Theory Num.Def Num.Theory.`; `Local Open
  Scope` only.
- 80-column limit incl. statements (4-space continuation indent);
  `Implicit Types` for repeated RV ascriptions.
- Statement comments: declarative first sentence + trailing `Naming:`
  paragraph (model: `dsdp_main.v:750-755`); no status/meta narration in
  rendered positions.
- RV algebra notations (probe C4): infotheo's backticked only-parsing
  family `` `+ ``, `` `* ``, `` `+cst ``, `` `*cst `` etc., `const_RV`,
  `` `o `` (no `*o`, no `\*`/`\+` — those are function-level ops; `\o` only
  for plain functions); fdist bind `>>=` in `fdist_scope`.
- Any auxiliary abstract ring carrying RV arithmetic must be
  `finComNzRingType`, or canonical-structure resolution fails (probe C5);
  `plain AHE` already is one.
- Immediately after the `indcpa_fdist_adversary` record:
  `Arguments adv_choose : clear implicits.` (likewise `adv_plain`,
  `adv_decide`) — `Set Implicit Arguments` otherwise makes the record
  argument implicit and the sketched applications fail (probe C6).
- Applying `Pr_dsdp_sol_uniform_ring`: supply our own
  `#|(R * R)%type : finType| = _.-1.+1` equation and close the
  uniformity premise with `congr fdist_uniform; exact: eq_irrelevance`
  (its exported premise names a section-`Let` subproof); `apply:` leaves
  the three hypotheses as goals in declaration order — use `-` bullets
  (probe C7).
- Pre-commit: record-field disjointness check (`indcpa_fdist_adversary`
  fields vs `dsdp_indcpa_adversary`'s), rocq-auditor Stage 2 as usual.

## 11. Verification and process

- Build with the local opam switch (`~/Projects/coq/_opam`); per-lemma
  `rocq_check`; file added to `_CoqProject`.
- Implementation phases (each compiles before the next): sample space +
  RVs -> infra (`enc_fdist`, adversary record, epsilons,
  `enc_slot_resampleE`) -> hop equalities -> IT leg (P-swap chain) ->
  headlines + simulator. Atomic commits per phase.
- Audits already applied to this spec: adversarial soundness (verdict
  NO-GO -> fixes folded in), mathcomp naming/style (all renames folded
  in). Findings log below.
- Probe-compiled (2026-07-29, kept at
  `<session scratchpad>/probe_infotheo_leg.v`, 43 declarations, exit 0,
  boolp-trio axioms only): P1 signatures, P2 resampling (product + bind +
  context-dependent-slot forms), P3 hop-arm change-of-variables and
  `|real - zero|` equality, P4 `Pr_dsdp_sol_uniform_ring` applicability,
  P5 `cinde_RV_comp` ∘ `cinde_diagonal_bound` chain. Corrections C1-C8
  folded into sections 3, 4, 5, 6, 9, 10.

## 12. Audit resolution log

| Finding | Resolution |
|---|---|
| F1 sim headline lacked the simulator | `alice_ideal_joint` defined; headline (iii) restated against it |
| F2 factorization conditioned only on `S` | `dsdp_alice_view_cond_sim` on `[%V2,V3]` primary; `S` form corollary |
| F3 Lindell claim was average-case | scope caveat in section 1; per-input variant recorded as follow-up |
| F4 (ii) false at `Pr = 0` | `Hpos` added |
| F5 hop context under-specified | `adv_plain : adv_context -> plain` field; contexts pinned in section 4 |
| F6 `Rho2'/Rho3'` unstated swap | coordinates removed; `enc_slot_resampleE` named |
| F7 `<=` hop lemmas vacuously provable | stated as equalities (`E` suffix) |
| F8 `Renc` could be empty | `index_renc` + `.+1` cardinality hypothesis |
| F9 zero-mass conditioning | `Sout_uniform` + guarded corollary |
| F10 sim carries true `Sout` | via `alice_ideal_joint` construction (F1) |
| F11 IT-leg template mis-cited | section 5 names the `dsdp_guess_fiber.v:1419-1685` chain; effort corrected |
| F12 epsilon granularity differs from SSProve | thesis caveats in section 8.7 |
| F13 bounds can exceed 1 | header remark (8.1) |
| F14 fidelity remark model-dependent | decrypt-on-receive note (sections 1, 3) |
| F15 nonexistent notations | sketches corrected (`dsdp_output `o`, `>>=`, no `*o`) |
| Naming audit W1-W12, table | all renames adopted (section 7); false precedents removed |
| C1 fixed-plaintext resample lemma too weak for the hops | generalized to context-reading slot map `k`, lemma binder (section 4) |
| C2 curried `dsdp_output` composition | `uncurry2` idiom (section 3) |
| C3 no RV-vs-RV `` `Pr[ _ = _ ] `` form | guess statements as `Pr _ [set t \| _ t == _ t]` (sections 5, 6) |
| C4 `\*`/`\+` are not RV notations | backticked only-parsing family (section 10) |
| C5 RV arithmetic needs `finComNzRingType` | convention noted (section 10) |
| C6 record projections get implicit record arg | `Arguments ... : clear implicits.` (section 10) |
| C7 exported subproof in fiber lemma's premise | `eq_irrelevance` discharge + bullet discipline (section 10) |
| C8 glue toolkit scope | four named glue lemmas + helpers, ~30 lines (sections 4, 9) |

## 13. Out of scope

- RSLR / any PPT internalization; asymptotic (security-parameter-indexed)
  statements.
- Per-input (fixed `v2, v3`) simulation variant — strictly stronger
  headline (iii); follow-up file.
- Replacing or modifying the SSProve axis; blueprint updates (follow-up).
- Bob/Charlie legs (already unconditional IT in `dsdp_main.v`).
