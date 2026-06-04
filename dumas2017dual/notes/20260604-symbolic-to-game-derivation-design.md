# Symbolic-to-game derivation for DSDP — design

Date: 2026-06-04
Status: design (brainstorming output). Implementation plan to follow via writing-plans + rocq-prover.

## 0. One-paragraph summary

The DSDP protocol is currently written twice by hand: once as a session-typed
piSMC process (`dumas2017dual/dsdp/dsdp_pismc.v`, used for duality / termination
/ correctness) and once as a family of SSProve probabilistic games
(`dumas2017dual/dsdp/ref/dsdp_security_indcpa.v`, used for the computational
game-hopping bound). There is no mechanical link guaranteeing the two encodings
describe the same protocol. The goal is a single source — *enhanced piSMC* —
from which the SSProve game is **derived** by a Coq function, so the two-world
security bound `Pr_guess ≤ 1/m + 2·epsilon_cpa` becomes two harvests of one
artifact. The IT residual `1/m` and the computational `2·epsilon_cpa` are read
off the same derived structure.

This document specifies the **first sub-project: the back end** — the reified
game syntax `game_code`, its denotation into SSProve `raw_code`, and a *generic*
hybrid-ladder advantage theorem `AdvantageE ⟦real⟧ ⟦all-zero⟧ A ≤ k·epsilon_cpa`.
It deliberately does **not** include the symbolic interpreter front end (that is
sub-project 2) nor the information-theoretic leg (sub-project 3).

## 1. Decisions locked during brainstorming

- **Primary goal:** research artifact / paper.
- **Central claim:** two-world hybrid composition — one source compiles to an
  IT leg (`1/m`) and a game-hopping leg (`2·epsilon_cpa`); the language
  guarantees both proofs concern the same protocol.
- **Embedding:** deep embedding, realised as *enhanced piSMC + a derivation
  function*, not a from-scratch third calculus.
- **Reification mechanism:** symbolic execution of the existing interpreter at a
  symbolic AHE instance (`Symbolic_AHEnc`), reusing the interpreter's scheduling
  and loop unrolling. (Front end, sub-project 2.)
- **Builder ↔ proof:** reified game AST + denotation; the advantage chain is
  proved on generated games and the hand-written `game_real … game_enc_zero`
  ladder is retired.
- **First slice:** back end first (this document).

## 2. Terminology

- *Deep embedding* — `he_term` / `game_code` are data with explicit
  constructors, vs. a shallow embedding (host-language functions).
- *Symbolic execution* — running the protocol on symbolic inputs (sub-project 2).
- *Reification* — the value→syntax step, in the proof-by-reflection (Chlipala,
  CPDT) and normalization-by-evaluation (Berger–Schwichtenberg) sense. Prose
  only; no identifier uses the word.

## 3. Naming (MathComp style, locked)

Strict snake_case for definitions, capitalized type-prefixed inductive
constructors (matching `STSend` / `SInit` / `DT_Enc`), `X_of_Y` for conversions.

| Concept | Identifier |
|---|---|
| HE message algebra (deep embedding) | `he_term` (type) |
| its constructors | `HE_var`, `HE_const`, `HE_enc`, `HE_dec`, `HE_emul`, `HE_epow` (+ ring ops) |
| reified SSProve game | `game_code` (type), parallels `proc` |
| game-statement constructors | `GC_sample`, `GC_put`, `GC_let`, `GC_enc_hop`, `GC_ret` (capitalized, prefix `GC_`) |
| denotation | `denote_game : game_code -> raw_code` (parallels `interp` / `erase`) |
| oracle-routed denotation (one hop opened) | `denote_game_shim` |
| hybrid ladder | `hybrid_ladder` |
| per-hop perfect equivalence | `hop_equiv` |
| advantage bound | `advantage_le` (matches the file's `advantage_*`) |
| symbolic AHE instance (sub-project 2) | `Symbolic_AHEnc` / `Symbolic_isAHEnc` (PascalCase sibling of `Idealized_AHEnc`) |

Open: exact `GC_*` prefix (`GC_` vs `G_`) and whether ring ops live in `he_term`
or are shared with an existing arithmetic expression type — resolve by a
prior-art grep at implementation time.

## 4. Scope of this sub-project

In scope:
- `game_code` inductive (statement list with a canonical sample order and an
  explicit hop-site marker).
- `denote_game : game_code -> raw_code`, plus the fixed second-oracle wrapper
  (`id_v2_get`) shared by all games, and a package wrapper with validity.
- `denote_game_shim`: route a chosen hop site through the IND-CPA real-or-zero
  oracle (the `game_via_oracle_*` analogue), generated mechanically.
- `hybrid_ladder : game_code -> seq raw_package` over the k hop sites.
- one generic `hop_equiv` (`≈₀`) lemma and `advantage_le`:
  `AdvantageE (denote_game (all_real gc)) (denote_game (all_zero gc)) A
   ≤ (size (hop_sites gc))%:R * epsilon_cpa`.
- validation: a hand-built `game_code` reproducing DSDP's two-hop structure,
  with `advantage_le` instantiating to `2·epsilon_cpa`.

Out of scope (later sub-projects):
- `he_term` reification via `Symbolic_AHEnc` and the observer-hooked interpreter.
- `game_of_trace` (the corrupted-view projection + hop classification).
- the IT leg (`1/m`) and the entropy harvest.
- the final composition theorem.

## 5. `game_code` design

**Derivation invariant (load-bearing).** No part of any SSProve game is
hand-written. `game_code` is the AST *produced by* the symbolic interpreter
(sub-project 2: run the piSMC source at `Symbolic_AHEnc`); `denote_game` then
lowers it to SSProve `raw_code`/`package`. The single hand-written artifact is
the piSMC source. `game_code` is therefore a compiler *source AST* that lowers
to `raw_code` (the *target IR*); their constructor-level resemblance is the
ordinary AST→IR relationship, not a reinvention — `raw_code` is HOAS (its
`opr`/`getr`/`sampler`/`putr` continuations are opaque functions) and so cannot
itself be scanned or laddered, which is exactly why a first-order derived AST is
needed. All semantics and advantage machinery (`raw_code`, `package`,
`AdvantageE`, `Advantage_triangle_chain`, `Advantage_link`, the oracle packages,
`enc_ind_cpa_real_or_zero`, and the project's `enc`/`Emul`/`Epow`/`D`) are reused
via `denote_game`; nothing semantic is redefined.

A `game_code` models the body of the `id_game_run` oracle (the part that varies
across the hybrid games). The second oracle (`id_v2_get`, identical in every
game) is added uniformly by `denote_game`, so `game_code` need not carry it.

A `game_code` is a straight-line sequence of statements:

- `GC_sample` — draw a fresh uniform value (carries a cardinality index and a
  sort tag: protocol scalar vs encryption randomness), bind to a variable.
- `GC_put` — write the challenge secret into the shared cell (`V_2_cell`
  analogue). Exactly the marker the challenger later scores against.
- `GC_let` — bind a non-hoppable `he_term` expression (homomorphic assembly
  `HE_emul`/`HE_epow`, encryptions of random masks, etc.).
- `GC_enc_hop` — a **hoppable** encryption of a secret under a public key with a
  fresh randomness slot, bound to a variable. This is the only statement the
  ladder rewrites real→zero. (Distinguished from a `GC_let` carrying an
  `HE_enc`: only encryptions of *secret inputs* are hoppable; encryptions of
  random masks stay real, matching the hand-written games where `enc pk_b r2
  ra1` is never swapped.)
- `GC_ret` — return the observable output, a list of cipher-valued `he_term`s
  referencing earlier-bound variables (the leaked ciphertext list).

Key structural invariant: **canonical sample order.** All `GC_sample`s precede
the computation, in one fixed order shared by the all-real game, the all-zero
game, and every shim. This invariant is what removes the per-proof
`ssprove_swap_*` alignment steps the hand-written equivalences need.

`all_real gc` / `all_zero gc`: interpret every `GC_enc_hop` as a real
encryption / a zero encryption respectively. `hop_sites gc`: the list of
`GC_enc_hop` positions.

## 6. `denote_game` design

`denote_game gc : raw_code` maps statements to SSProve operations:
`GC_sample → sample uniform`, `GC_put → #put`, `GC_let → let … in`,
`GC_enc_hop → enc pk m r` (real) or `enc pk 0 r` (zero), `GC_ret → ret`.
`he_term`s denote structurally to `enc`/`Emul`/`Epow`/ring expressions over the
bound SSProve variables.

The package wrapper adds the fixed `id_v2_get` oracle and the shared
`protocol_state` locations, and exports `game_iface`. A `ValidPackage` obligation
is discharged once, parametrically over `gc` (this is real work — SSProve
validity of a generated package — and a named risk, §9).

`denote_game_shim gc site`: identical to `denote_game gc` except the chosen
`GC_enc_hop` is replaced by a call to an imported IND-CPA encryption oracle,
exactly mirroring `game_via_oracle_charlie/bob`. Because of the canonical sample
order, the shim and the inlined game differ *only* at that one statement.

## 7. Generic ladder and advantage bound

For a `game_code` with hop sites `s_1 … s_k`, `hybrid_ladder` is the chain whose
i-th game has sites `s_1 … s_i` zeroed and `s_{i+1} … s_k` real. Consecutive
games differ at exactly one site.

`hop_equiv` (the load-bearing generic lemma): for any `gc` and any single hop
site, the inlined game is `≈₀` to `denote_game_shim gc site` linked with the
real oracle, and the next game is `≈₀` to the same shim linked with the zero
oracle. Because the canonical sample order makes the two sides identical except
at the site, the proof synchronises the shared prefix (`ssprove_sync_eq`) and closes
with *no swaps* — collapsing the six near-identical hand proofs into one generic
lemma. (Outcome: the encode/decode cancels `chcipher_of_cipherK` /
`chmsg_of_msgK` *do* fire, as expected — the oracle returns a `t_cipher` that
round-trips; "no swaps" is the payoff, not "no cancels". Realising the canonical
order required a design correction discovered at the T8 gate — see §9.1.)

`advantage_le`: triangle inequality over `hybrid_ladder`, each consecutive hop
bounded via `hop_equiv` + `Advantage_link` + the IND-CPA axiom
`enc_ind_cpa_real_or_zero` (a fact about the real scheme), giving
`AdvantageE (denote_game (all_real gc)) (denote_game (all_zero gc)) A ≤ k·epsilon_cpa`.

## 8. Validation

`gc_dsdp` is a *temporary AST fixture* standing in for what the symbolic
interpreter (sub-project 2) will emit automatically; it is hand-built only so
the back end can be developed and tested before the front end exists. It is an
AST, not a hand-written SSProve game — the SSProve game is the *derived*
`denote_game (all_real gc_dsdp)`, and the fixture is discarded once the symbolic
run produces `game_code` for real.

Hand-build `gc_dsdp : game_code` with the two `GC_enc_hop` sites (Bob's c_2,
Charlie's c_3) and the homomorphic assembly as `GC_let`s, matching
`dsdp_security_indcpa.v` line 325 onward. Then:
- `advantage_le` at `gc_dsdp` yields `2·epsilon_cpa`, reproducing
  `advantage_game_real_game_enc_zero` — a sanity check, not a dependency (the
  hand-written ladder is being retired).
- optional: `Eval`/`Check` that `denote_game (all_real gc_dsdp)` matches the
  shape of `game_real` (informal confidence, not a proof obligation).

## 9. Risks and open questions

1. **Generic `hop_equiv` — RESOLVED (with a design correction).** The T8 gate
   prototype FAILED on the first attempt: the original design pre-sampled each
   hop's randomness into the `de_rand` pool, but the IND-CPA oracle samples its
   randomness internally at the hop, giving a 2-vs-1 sample-count mismatch (the
   shim carried a dead up-front sample plus the oracle's), which would have
   needed `ssprove_swap` + dead-sample absorption. Fix: `GC_enc_hop` samples its
   randomness *inline* (binder `ir_hop`), coupling 1:1 with the oracle's sample.
   After the fix, `hop_equiv_real` and `hop_equiv_zero` proved generically over
   `(gc, i)` by induction (helpers `denote_run_shim_real_equiv`,
   `denote_run_shim_post_target_zero`, `denote_run_shim_zero_equiv`), with NO
   `ssprove_swap` anywhere — only the expected cancels. The §7 "no swaps" payoff
   holds; the "no cancels" over-claim did not.
2. **`ValidPackage` of generated packages — RESOLVED.** Constructing a `package`
   *value* requires its validity proof, so `denote_run_valid` /
   `denote_game_valid` (and the shim analogues) were proved by induction on
   `game_code` as part of `denote_game` itself; no separate residual lemma was
   needed.
3. **`raw_code` vs `package` — RESOLVED.** `denote_game` targets `package`
   directly (the smart constructor needed the explicit validity certificate
   above); no `raw_code`-core/wrapper split was necessary.
4. **`he_term` sorts — RESOLVED (single-sort sufficed).** A single-sorted
   `he_term` with a 2-case value sum `gval` (`Gplain`/`Gcipher`) plus totality
   defaults lowered cleanly; no `Plain`/`Cipher` sort index was needed. `Key`/
   `Rand` stayed opaque (party-id nats and rand-slot nats).

## 10. Success criteria — ALL MET (back end complete)

- ✓ `game_code`, `denote_game`, `denote_game_shim`, `hybrid_ladder` defined and
  type-checked; `denote_game` is a `ValidPackage` (`denote_game_valid`).
- ✓ `hop_equiv` (`hop_equiv_real`/`hop_equiv_zero`) and `advantage_le` proved
  generically — all `Qed`, no `Admitted`, no new custom axioms beyond the
  existing `enc_ind_cpa_real_or_zero`.
- ✓ `gc_dsdp` validation: `advantage_gc_dsdp` instantiates `advantage_le` to
  `2·epsilon_cpa` (de Bruijn indices verified faithful to `game_real`).
- ✓ Naming passes the MathComp-style audit; the pre-commit rocq-audit hook gates
  every commit (`Naming:` justifications recorded for the SSProve `*_equiv_*`
  upstream-class exception on the ≥5-component helper names).

Deferred (follow-ups, not blocking the back end): extract the shared interface
vocabulary into `dsdp_game_iface.v` once `dsdp_security_indcpa.v` is retired; the
symbolic-interpreter front end (`Symbolic_AHEnc` + `game_of_trace`, sub-project
2); the IT `1/m` leg; the `1/m + 2·epsilon_cpa` composition theorem.
