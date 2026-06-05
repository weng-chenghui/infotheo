# DSDP symbolic-to-game derivation — architecture and the manual-vs-derived comparison

Date: 2026-06-05

Status: implemented. Phase 1 commit `01a9bd4` (standalone interface), Phase 2 commit
`664b16b` (symbolic instance + observer). Plan: `~/.claude/plans/swirling-whistling-kahn.md`.

Files: `dumas2017dual/dsdp/dsdp_interface.v` (the interface + `Standard` instance),
`dsdp_session_types.v` / `dsdp_pismc.v` / `dsdp_program.v` (the protocol procs over the
interface), `dsdp_symbolic.v` (the symbolic instance + the symbolic run), `dsdp_game_code.v`
(the back end), `dsdp_game_symbolic.v` (the derived trace + lowering + faithfulness).

---

## 1. Manual vs auto-generated game: does the derived game have less information?

> Sharp question. The short answer: **for the property that matters (the 2·ε IND-CPA bound), no information is lost — it is fully proven on the auto-generated game.** But the symbolic representation does have three genuine expressiveness limits, and `game_real` simply happens to stay inside them. Let me be precise.
>
> ### Why nothing is lost for *this* game
>
> `denote_game (all_real gc_dsdp)` is not an abstraction of a game — it *is* a real SSProve game. `denote_game` lowers the `game_code` back to actual `raw_code`: `GC_sample → sample uniform`, `GC_enc_hop → enc …`, `GC_let → Emul/Epow`, `GC_ret → ret`. So the denoted combine is literally `Emul (Epow c2 u2) (enc pk_b r2 ra1)` — the *same operations* as `game_real:357`. The `he_term` is only the generation intermediary; after denotation the real `enc`/`Emul`/`Epow` are back. That's why `dsdp_advantage_derived` proves the same `≤ 2·ε` on it. Anything you can prove about `game_real`'s structure (sampling, put, encryptions, combines, leak), you can prove about the derived game, because it has all of them.
>
> ### Where the symbolic representation genuinely carries less — and `game_real` just doesn't use it
>
> The `he_term`/`game_code` AST *cannot faithfully express* three things:
>
> 1. **Decryption.** `he_term` has `HE_dec`, but the back end's `denote_he` maps `HE_dec _ _ → Gplain 0`. There is no secret key in the game denotation, so a decrypted plaintext becomes **0**. Consequence: you could **not** derive-and-prove any game whose *observable output depends on a decrypted value* — e.g. a **correctness** game (output = the dot product `g - r2 - r3 + u1·v1`). The derivation would silently emit `0`. `game_real` is a pure secrecy game and never decrypts (it stops at the ciphertext leak), so this costs nothing *here* — but it is a real wall for other games.
>
> 2. **Randomness arithmetic / the homomorphic law.** `HE_enc` carries randomness as a **nat slot index**, not a `rand AHE` value, and `he_term` has no `rand_mul`/`rand_pow`. So the game_code cannot state facts like `Emul (enc m1 r1) (enc m2 r2) = enc (m1+m2) (r1·r2)`. Consequence: a proof that needs the homomorphic **correctness law** could not be carried out on the derived game. The IND-CPA bound deliberately does **not** use those laws (it rides the IND-CPA oracle), so again no loss here — but it's a genuine limit.
>
> 3. **Single sort.** The denotation collapses `gval` to `Gplain | Gcipher` with `0`-defaults on a mismatch. A game that mixes plaintext and ciphertext in the leaked output beyond the simple DSDP pattern could be mis-modeled. DSDP-Alice leaks only ciphertexts, so it's fine.
>
> ### The one thing that is honestly "less"
>
> Not less *information in the game*, but a missing *link*: there is no theorem `denote_game (all_real gc_dsdp) = game_real`. The new game was shape-verified against `game_real` by hand, not proven equal. So you can't transfer `game_real`'s specific lemmas onto the derived game for free — you re-prove the bound independently (which `dsdp_advantage_derived` does).
>
> ### Bottom line
>
> The auto-generated game is **equi-expressive with `game_real` for the secrecy bound** — the 2·ε result is provable on it with nothing missing. The symbolic layer's expressiveness limits (no real decryption, no randomness algebra, single sort) are real, but they only block *other* kinds of games (correctness, or anything invoking the homomorphic law) — games `game_real` itself doesn't attempt. So the loss is in *what other games you could auto-derive*, not in what you can prove about this one.

---

## 2. Overall architecture

Two halves meet at a reified game AST (`game_code`):

- **Front end** (`dsdp_symbolic.v` + `dsdp_game_symbolic.v`) *produces* the game from the
  one DSDP program by running it at a symbolic instance, then lowers the result to `game_code`.
- **Back end** (`dsdp_game_code.v`) *consumes* `game_code`: it denotes it to a concrete
  SSProve package and proves a generic hybrid-ladder advantage bound, reusing SSProve's
  `enc`/`Emul`/`Epow`/`AdvantageE`/`Advantage_triangle_chain` machinery (nothing semantic is
  re-implemented).

```
        DSDP procs (palice / pbob / pcharlie) : parameterized over DSDP_Interface
              /                                                          \
  Standard_DSDP_Interface AHE  (concrete)              Symbolic_DSDP_Interface  (he_term / nat)
        |                                                               |
  correctness / termination / duality              run palice symbolically (palice_symbolic):
  (existing proofs, preserved)                       erase + sent_payloads
                                                       -> dsdp_observed_combines
                                                       (a1, a2 DERIVED, proved = Send payloads)
                                                                        |
                                       dsdp_alice_obs  =  derived combine terms
                                       (dsdp_game_symbolic.v)   +  explicit security-model config
                                                                    (samples / put / hops / leak)
                                                                        |
                                           game_of_trace   -->   game_code            (REUSE)
                                                                        |
                                 (REUSE back end)  denote_game   -->   SSProve package
                                                   advantage_le
                                                                        |
                                       AdvantageE (real) (all-zero) A   <=   2 * epsilon_cpa
```

The horizontal split at the top is the load-bearing idea: **one set of protocol procs, two
instances of one interface.** The left instance recovers the existing concrete proofs
unchanged; the right instance is what makes the game derivable.

---

## 3. Front-end design

### 3.1 One program, two interpretations

The DSDP protocol is written once, as session-typed piSMC procs `palice`/`pbob`/`pcharlie`
(plus the n-party templates). Before this work they were parameterized by an `AHEncType` and
drew `enc`/`Emul`/`Epow` directly from it, so they could only ever run at a concrete scheme.

They are now parameterized by a standalone `DSDP_Interface` (a plain record of carrier types
and operations, no laws). Two instances:

- `Standard_DSDP_Interface AHE` — the concrete reading. Fields are filled *definitionally* with
  the old operations (`di_encrypt := @enc AHE`, `di_emul := @Emul AHE`, `di_data := std_data`,
  …), so the entire existing proof suite (3-party + n4/n5 duality, termination, `senv_zero`,
  `dsdp_ok`, Benaloh/Paillier, the cross-equality lemmas) re-proves with no change.
- `Symbolic_DSDP_Interface` — the symbolic reading, over `he_term` plaintext/ciphertext carriers
  and `nat` randomness/key carriers, with `di_encrypt := HE_enc`, `di_emul := HE_emul`, etc.

Why an interface and not a symbolic `AHEncType`: a lawful `AHEncType` over `he_term` is
impossible, because `AHEncType` requires `plain : finComNzRingType` and `cipher : nzRingType`,
but a free `he_term` algebra is infinite (not a finType). Generalizing the *protocol's*
interface sidesteps the type-class wall entirely: the law-free `DSDP_Interface` has no
finiteness or ring constraints, so `he_term`/`nat` slot in directly.

### 3.2 The SMC-DSDP interface

`DSDP_Interface` (in `dsdp_interface.v`) is the abstraction boundary between the protocol
procs and the crypto+data layer. It bundles:

- **Carrier types** (bare `Type`s): `di_msgT`, `di_cipherT`, `di_randT`, `di_priv_keyT`,
  `di_pub_keyT`, `di_data`.
- **Data marshalling** (MathComp `X_of_Y` for the total injectors, a verb for the partial
  extractor): `di_data_of_plain`, `di_data_of_cipher`, `di_data_of_priv_key`,
  `di_data_of_pub_key`, and `di_get_cipher : di_data -> option di_cipherT`.
- **Operations** (signatures only, no laws): `di_encrypt`, `di_emul`, `di_epow`, and the
  plaintext ring ops `di_add` / `di_sub` / `di_mul` (needed so the corrupted party's final
  reconstruction typechecks at a non-ring carrier).
- **Specialized receives**: `di_Recv_dec` (receive-and-decrypt) and `di_Recv_enc`
  (receive-ciphertext), each carrying a HOAS continuation over `proc di_data`.

The session wrappers (`DSend`/`DRecv_enc`/`DRecv_dec`/…) and the procs source everything from a
`DI : DSDP_Interface`. Keeping `Standard_DSDP_Interface.di_data` *definitionally* equal to the
old `std_data` sum is an explicit invariant: downstream files (`dsdp_trace_bridge`,
`dsdp_correctness`) pattern-match that concrete shape.

### 3.3 The symbolic run and the derived trace

This is the part that makes the game "auto-generated."

1. **Run the protocol symbolically.** `dsdp_symbolic.v` instantiates Alice's program at
   `Symbolic_DSDP_Interface` with symbolic-variable inputs and erases it to a first-order
   `proc symbolic_data` (`palice_symbolic`).
2. **Force the HOAS and read off the sends.** `sent_payloads` (an 8-line first-order fixpoint
   over `proc`, copied locally to avoid pulling the SSProve stack from `dsdp_trace_bridge.v`)
   drives Alice's process with a *response stream* and collects her `Send` payloads.
   Crucially, the received ciphertexts are fed as **named placeholders** (`HE_var 30`,
   `HE_var 31`), so the computed sends reference `c2`/`c3` by name — matching the name-based
   lowering pass, rather than inlining the received terms.
3. **Derive the combines.** `dsdp_observed_combines := pmap symbolic_get_cipher (sent_payloads
   palice_symbolic …)` computes (proved `by []` in `dsdp_observed_combines_eq`) to
   `[a1; a2]` with `a1 = Emul(Epow c2 u2)(Enc_Bob r2 ra1)`, `a2 = Emul(Epow c3 u3)(Enc_Charlie
   r3 ra2)`. These homomorphic assemblies are **derived from the protocol, not hand-written.**
4. **Assemble the observation trace.** `dsdp_alice_obs` (in `dsdp_game_symbolic.v`) takes its
   two `AO_combine` payloads from `dsdp_observed_combines` and wraps them in the explicit,
   generic *security-model config*: the sample prefix (six `card_msg` scalars, two `card_renc`
   randomnesses), the `AO_put` of the challenge secret, the `AO_recv_hop` classifications, and
   the `AO_leak` set/order. (Per §1: this config is declared, not discovered from the protocol.)
5. **Lower and validate.** `game_of_trace` resolves the named trace to de Bruijn `game_code`;
   `dsdp_faithful : game_of_trace dsdp_alice_obs = gc_dsdp card_renc card_msg` holds by
   computation (axiom-free), and `dsdp_advantage_derived` transports the back-end bound onto the
   derived game.

---

## 4. Backend design

The back end is `dsdp_game_code.v`. It treats `game_code` as a compiler *source AST* and
lowers it to SSProve `raw_code`/`package` (the *target IR*); `raw_code` is HOAS and unscannable,
which is exactly why a first-order `game_code` is needed to ladder over.

### 4.1 Reified game syntax (`he_term` / `game_code`)

`he_term` is the deep-embedded message algebra (`HE_var`/`HE_const`/`HE_enc`/`HE_dec`/`HE_emul`/
`HE_epow` + plaintext ring ops). `game_code` is a straight-line statement list:
`GC_sample` (draw a uniform of a given cardinality), `GC_put` (write the challenge cell),
`GC_let` (bind a non-hoppable homomorphic assembly), `GC_enc_hop` (a *hoppable* encryption of a
secret — the only statement the ladder rewrites real→zero, with its randomness sampled inline),
and `GC_ret` (the leaked cipher list). The load-bearing invariant is a **canonical sample
order** shared by the all-real game, the all-zero game, and every shim.

### 4.2 Denotation into SSProve (`denote_he` / `denote_run` / `denote_game`)

`denote_he : denv -> he_term -> gval` evaluates a term to a plaintext/ciphertext value,
reusing the project's real `enc`/`Emul`/`Epow` (never re-implemented). `denote_run` lowers a
`game_code` body to `raw_code` (each constructor to its SSProve operation), and `denote_game`
wraps it as a `package [interface] game_iface` with the fixed second oracle and a once-and-for-all
`ValidPackage` certificate (`denote_game_valid`). `HE_dec` defaults to `Gplain 0` (no secret key
on the game path) and `gval` is single-sorted — the two expressiveness limits of §1.

### 4.3 Generic hybrid-ladder advantage bound (`denote_game_shim` / `hop_equiv` / `advantage_le`)

`denote_game_shim gc site` routes one chosen `GC_enc_hop` through the IND-CPA real-or-zero
oracle (the `game_via_oracle_*` analogue, generated mechanically). `hybrid_ladder` zeroes the
hop sites one at a time. The generic `hop_equiv_real`/`hop_equiv_zero` prove, for *any* `gc` and
hop site, that the inlined game is `≈₀` to the shim linked with the real/zero oracle. Because of
the canonical sample order (and inline hop randomness, which couples 1:1 with the oracle's
internal sample), these proofs need **no `ssprove_swap`** — only the expected
`chcipher_of_cipherK`/`chmsg_of_msgK` cancels. `advantage_le` then telescopes the ladder via
the triangle inequality and `Advantage_link` + the IND-CPA axiom `enc_ind_cpa_real_or_zero`:

```
AdvantageE (denote_game (all_real gc)) (denote_game (all_zero gc)) A
  <= (size (hop_sites gc))%:R * epsilon_cpa
```

proved once, for any well-formed `game_code`. This collapses what the hand-written
`ref/dsdp_security_indcpa.v` does in ~2500 lines of bespoke game-hopping into one generic lemma.

### 4.4 DSDP instantiation (`gc_dsdp` / `advantage_gc_dsdp` / `dsdp_advantage_derived`)

`gc_dsdp` is the two-hop DSDP-Alice `game_code` (Bob's `c2`, Charlie's `c3`). `advantage_gc_dsdp`
specializes `advantage_le` to `2 * epsilon_cpa` (two hop sites). The front end's
`dsdp_advantage_derived` transports that bound onto the *derived* game via
`rewrite dsdp_faithful; apply: advantage_gc_dsdp`. Axiom hygiene: `dsdp_faithful` is closed
under the global context; `dsdp_advantage_derived` carries only the inherited
`enc_ind_cpa_real_or_zero` / `epsilon_cpa` plus the standard SSProve/classical axioms — no new
custom axioms.

### 4.5 Expressiveness boundary (pointer)

The back end's representation choices (`HE_dec → 0`, single-sort `gval`, slot-indexed randomness
without `rand_mul`/`rand_pow`) are exactly the three limits analyzed in §1. They are harmless for
the IND-CPA secrecy bound but would block deriving correctness games or any proof invoking the
homomorphic correctness law.
