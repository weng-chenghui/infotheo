# Correctness of the piSMC → SSProve game translation: how to define it, how to prove it

Date: 2026-06-06

Context: follow-up to the question of whether the interpreter soundness proof
(`step_sound`, `smc/smc_interpreter_sound.v:808`) underwrites the symbolic-to-game
derivation. It does not (the derivation rests on `erase` + `sent_payloads`, never
on `step`/`interp`/`rsteps`). This note answers the natural next question: what
*would* "correctness of translation from piSMC to SSProve game" mean, and how
would one prove it.

## Grounding fact: two separate probabilistic worlds, never bridged

This codebase runs two probability theories that are never formally connected:

- **infotheo `fdist` world** — Alice's operational view is a random variable;
  `alice_view_joint`, `H(V2,V3 | view)` (`dumas2017dual/dsdp/dsdp_entropy.v:461`).
- **SSProve `SDistr` / `AdvantageE` world** — the game is a `raw_package`;
  advantage reasoning via `eq_rel_perf_ind_eq` (`dumas2017dual/dsdp/dsdp_game_code.v:678`).

The docstring "a stronger SDistr-to-fdist bridge is built later as Task 12"
(`smc/pismc_to_ssprove.v:288`) names this bridge as future work; it is not built.
That gap is exactly what the correctness question circles.

## 1. Fix the two objects and their semantics first

You cannot say "the translation is correct" until both sides are objects with a
meaning, and they live in different categories.

**Source (piSMC).** `palice ‖ pbob ‖ pcharlie` driven by `interp` is
*deterministic* (`interp h dsdp_procs …`, `dumas2017dual/dsdp/dsdp_correctness.v:145`);
it returns `(final_procs, traces)`, the per-party wire logs. Randomness enters
only as the sampled inputs (secrets, masks, encryption randomness). So the
source's "behaviour as a distribution" is the **pushforward** of the input
distribution through "run `interp`, then project the corrupted view." That
pushforward is an infotheo `R.-fdist`, and `dsdp_entropy.v` already builds it
(`alice_view_joint`).

**Target (SSProve game).** `denote_game (all_real (game_of_trace dsdp_alice_obs))`
is a `raw_package`. Its randomness is the `sample uniform card_*` commands; its
meaning is a sub-distribution `SDistr` observed through `Pr` / `AdvantageE`.

Translation correctness therefore relates a pushforward `fdist` (source) to an
`SDistr` (target). The rest is about which relation, and how strong.

## 2. The definition is a ladder, not a single statement

Be explicit about the rung, because the repo proves the bottom two and a skeptic
always means the third.

- **L0 — Well-definedness (compatibility).** "The translator depends on the
  program only through its erasure." `translate_correct_marginal`
  (`smc/pismc_to_ssprove.v:290`): `translate p = code_of_proc (erase p)`, `by []`.
  A property of the *function*, not a relation between *meanings*.

- **L1 — Structural / syntactic faithfulness.** "The derived game AST equals a
  reference AST." `dsdp_faithful` (`dumas2017dual/dsdp/dsdp_game_symbolic.v:242`):
  `game_of_trace dsdp_alice_obs = gc_dsdp`, `by []`. Certifies the front-end
  plumbing (symbolic run → reified syntax). Still no distributions.

- **L2 — Distributional / denotational correctness (THE real one).** "The law of
  the corrupted view under the operational protocol equals the law the denoted
  game returns," modulo marshalling cancels (`chcipher_of_cipherK`,
  `chmsg_of_msgK`):

  ```
  law( project_view ∘ interp (palice‖pbob‖pcharlie) )
        =   Pr/θ( denote_game (game_real ...) )
  ```

  This is what licenses *transport*: it makes an advantage bound on the package
  mean something about the protocol. It is Chapter 21's "honest gap," and it is
  NOT proved.

- **L3 — Observational equivalence / bisimulation.** A step-indexed simulation
  between `rsteps`/`interp` and the package's effectful run, matching every
  observable (oracle calls, abort/`Fail`, ordering), not just the leaked list.
  Explicitly disclaimed (Design Commitment 4, `smc/pismc_to_ssprove.v:18`).
  Overkill for a secrecy bound.

One-line answer to "what is correctness": **L2 — equality (or a coupling) of the
corrupted-view law on the two sides.** L0/L1 are necessary scaffolding but neither
is the semantic statement.

## 3. How you would prove L2

A probabilistic relational-simulation argument with one missing keystone.

**(a) Pin the source law.** Reuse `dsdp_entropy.v`: inputs from `fdist_uniform`,
run `interp`, project Alice's view (`alice_view_joint`). Call its law `mu_op`.

**(b) Pin the target law.** `mu_game :=` `Pr` of
`denote_game (all_real (game_of_trace dsdp_alice_obs))`, pushed onto the same view
type through the cancel lemmas.

**(c) Keystone — `sent_payloads`-vs-`interp` agreement.** The derivation reads
sends *syntactically* via `sent_payloads (erase palice)`
(`dumas2017dual/dsdp/dsdp_symbolic.v:107,160`); the protocol emits sends via
`interp`'s `traces`. Prove they coincide:

  ```
  under the concrete interface, response stream coupled to the peers' actual sends,
     sent_payloads (erase palice) responses
        =   Alice's emitted ciphertexts in (interp ...).traces
  ```

  This bridge does not exist today; it is the load-bearing lemma. It connects the
  syntactic object the front end manipulates to the operational object that has a
  probabilistic meaning. **This is where `step_sound` can re-enter**: if you state
  the source side *declaratively* over `rsteps` rather than computationally over
  `interp`, `step_sound` (`smc/smc_interpreter_sound.v:808`) is exactly the lemma
  that swaps `interp` for `rsteps`. Stated operationally over `interp` and
  discharged by computation, you don't need it. So `step_sound` is optional L2/L3
  infrastructure (natural for the relational phrasing), not a prerequisite.

**(d) `denote_run` as a per-statement simulation.** Each reified statement denotes
to the SSProve command whose effect matches the operational step: sample ↔
`sample uniform`, hop ↔ `enc`, combine ↔ `Emul`/`Epow`, return ↔ leaked list.
Re-read `denote_run` as a simulation relation, one constructor at a time.

**(e) One-to-one randomness coupling via the canonical sample order.** Couple each
operational randomness draw with exactly one `sample uniform`. The canonical
sample order (Chapter 20: fixed de Bruijn positions, identical across real/ideal/
intermediate games) makes this a bijection with no reordering. That is the
technical payoff of fixing the order, and `hop_equiv_real`/`hop_equiv_zero` already
exploit it inside the ladder.

**(f) Assemble in SSProve's relational logic.** Lift (c)–(e) into the
perfect-indistinguishability judgment the back end already uses
(`eq_rel_perf_ind_eq`, `dumas2017dual/dsdp/dsdp_game_code.v:678`), now with the
operational model on one side, to conclude the equality coupling `mu_op = mu_game`.

**(g) Optional — the `SDistr`↔`fdist` bridge (Task 12).** Steps (a)–(f) can be
stated entirely inside SSProve's `SDistr`, which suffices to transport the
advantage bound. The `SDistr`-to-`fdist` bridge (`smc/pismc_to_ssprove.v:288`,
unbuilt) is needed only to additionally connect the computational result to the
information-theoretic `fdist` analysis in `dsdp_entropy.v`, i.e. to make the two
probabilistic worlds talk to each other.

## 4. Why L2 is the right definition

Correctness of a translation is defined by *what transfers across it*. Once
`mu_op = mu_game`, the existing target bound

  ```
  dsdp_advantage_derived : AdvantageE game_real game_zero A ≤ 2·epsilon_cpa
        (dumas2017dual/dsdp/dsdp_game_symbolic.v:262)
  ```

becomes a statement about the actual piSMC protocol: Alice's real operational view
is ≤ 2ε-indistinguishable from the simulated all-zero view, i.e. simulation-based
secrecy of the protocol. Without L2, the advantage bound is a true theorem about a
`raw_package` only *eye-checked* against the protocol (`dsdp_faithful` gives
syntactic equality to a fixture, not behavioural equality to the running
protocol). That eye-check is the L1/L2 distinction in one sentence.

## 5. Honest status in the repo

- **L0 proved** — `translate_correct_marginal` (definitional).
- **L1 proved** — `dsdp_faithful` (syntactic, `by []`).
- **L2 not proved** — Chapter 21's "missing equivalence link." Keystone needed:
  the `sent_payloads`-vs-`interp` agreement lemma (§3c); for the IT connection
  additionally the `SDistr`↔`fdist` bridge (§3g).
- **L3 out of scope** — deliberately disclaimed (Design Commitment 4).

## 6. A better-targeted notion: operational correspondence (probability-free)

Instead of the distributional L2, ask only that the translated game has the same
*operational meaning* as the piSMC program: each protocol step has a matching
game step, computing the same value. This is the L3-flavoured rung, but stated in
a probability-free *structural* form, and it turns out to be the most tractable
real correctness statement and the one that catches interface bugs.

### The three operation maps

Name the operation maps, with the real constructors:

- **σ** = symbolic interface fill (`Symbolic_DSDP_Interface`,
  `dumas2017dual/dsdp/dsdp_symbolic.v:73-75`): op-slot to `he_term` node.
  `encrypt↦HE_enc`, `emul↦HE_emul`, `epow↦HE_epow`, `add/sub/mul↦HE_add/HE_sub/HE_mul`.
- **δ** = denotation back to real ops (`denote_he`,
  `dumas2017dual/dsdp/dsdp_game_code.v:317-330`): `HE_enc↦enc`, `HE_emul↦Emul`,
  `HE_epow↦Epow`, ring↦ring, and `HE_dec↦Gplain 0` (lossy, `:324`).
- **κ** = concrete interface fill (`Standard_DSDP_Interface`): `encrypt↦enc`,
  `emul↦Emul`, `epow↦Epow`, the real ops.

The derived game's operations are **δ∘σ**; the protocol's are **κ**. The notion
of correctness is **δ∘σ = κ**, lifted to a step-by-step correspondence.

### Three things to state right

1. **Weak simulation up to `erase`, not strict 1:1.** `Init` collapses to its
   continuation (`code_of_proc: Init _ k => code_of_proc k`,
   `smc/pismc_to_ssprove.v:247`), mapping to zero game commands; `Recv_dec` is
   folded into its continuation by `erase`. So some protocol steps match nothing.
   The right shape is a stuttering simulation, not a bijection of steps.

2. **Anchor at the CONCRETE interface, not the symbolic one.** Three objects:

   ```
   C = palice @ Standard (real ops, κ)        ← ground truth
   S = palice @ Symbolic (he_term, σ)         ← the symbolic run
   G = denote(game_of_trace(obs(S)))          = δ∘σ
   ```

   G is built *from* S. So a symbolic-interface (σ) bug, e.g. `di_epow := HE_emul`:
   - **C ↔ G catches it**: C sends `Epow(c,u)`; G computes `δ(HE_emul)=Emul`;
     `δ∘σ(epow)=Emul ≠ Epow=κ(epow)`. Correspondence fails. ✓
   - **S ↔ G is blind to it**: "G denotes S" holds by construction of the pipeline
     whether or not σ is buggy. A symbolic-to-game simulation is a tautology;
     garbage in, consistent garbage out.

   The bug-catching statement is therefore **C ↔ G**, equivalently δ∘σ = κ. The
   symbolic interface is only correct *relative to* the concrete ground truth, and
   the only way to test it is against κ.

3. **The decryption step deliberately breaks δ∘σ = κ — and that is not a bug.**
   `δ(HE_dec) = Gplain 0` (`dsdp_game_code.v:324`), whereas κ would `dec` to the
   real plaintext. So a full-process correspondence is *false* for DSDP-Alice. It
   holds only on the **leaked-ciphertext projection** (the terms Alice sends, which
   never pass through `dec`; the plan's explicit truncation drops Alice's final
   `Recv_dec … => Ret`). The single-sort defaults
   `as_plain (Gcipher _) = 0` / `as_cipher (Gplain _) = 0` (`:262,268`) are a
   second deliberate δ∘σ ≠ κ, off the observed path. Payoff: **the hypotheses of
   the correspondence theorem are exactly the three expressiveness limits of
   Chapters 20-21, stated operationally.** Extending the leak set to a decrypted
   value would correctly make the proof fail.

### Why this is the cheap MVP (and resolves the draftability problem)

On the observed projection the correspondence reduces to a per-term equation, no
probability, no relational logic:

```
denote_he (env coupled to the concrete samples) (derived combine term)
   =  the ciphertext the concrete palice sends
```

and the derived terms are already pinned by computation
(`dsdp_observed_combines_eq`, by `reflexivity`,
`dsdp_symbolic.v:154-167`). Randomness is isolated to a per-slot substitution
(`game sample i = concrete input i`); the deterministic *structure* needs no
coupling at all. This is why the notion sidesteps the wall that made L2 hard to
draft: the distributional L2 needed the nonexistent `SDistr`↔`fdist` bridge
because it crossed into probability; the operational/value correspondence never
leaves the deterministic world, so its statement references only existing types
(`denote_he`, the concrete `palice` send, the env). It is genuinely
`/rocq:draft`-able: an equation, not a cross-monad law.

For this notion `step_sound` (`smc/smc_interpreter_sound.v:808`) finally earns its
keep: if C's side is phrased over the reduction relation `rsteps` rather than by
computing `interp`, `step_sound` is the lemma giving a rigorous handle on the
protocol's operational steps. It was optional for the distributional reading; it is
the natural backbone here.

### Honest scope

This buys: the game faithfully computes the protocol's observed wire values, step
for step, falsified by any operation-level interface bug. It does NOT by itself
give the security transport — "equal values under the coupling" still needs a thin
probabilistic cap ("pointwise-equal-under-coupling ⟹ equal law") before the
SSProve advantage bound becomes a statement about the protocol. But that cap is
small, and this correspondence is its reusable, bug-sensitive backbone. In ladder
terms: the spine of L2, extracted as a probability-free, draftable,
interface-bug-catching lemma — the right MVP to build first.

## 7. The lemma skeleton (δ∘σ = κ on the observed projection)

Status: identifiers below are verified to exist in the named files; the section
context (the `AHE`, `decode`, `ek`, `pkey_of_party`, `rand0` variables, and the
env coupling) is part of the obligation and is written out as explicit hypotheses.
Not yet build-elaborated — to be materialised into a scratch `.v` and elaborated
via `/rocq:draft` / rocq-prover before trusting it.

### General notion (protocol-agnostic schema)

For any protocol `P` with corrupted party `X`, derived terms
`obs := pmap di_get_cipher (sent_payloads (erase (P @ Symbolic)) recv_names)`,
and concrete run `P @ Standard` on inputs coupled to an environment `env`:

```
[seq as_cipher (denote_he env t) | t <- obs]
   = pmap di_get_cipher (sent_payloads (erase (P @ Standard)) concrete_recvs)
```

i.e. denoting the symbolically-derived sends (δ∘σ) reproduces the concrete sends
(κ), on the leaked-ciphertext projection, under the env/inputs coupling.

### Concrete DSDP-Alice instance (the `Admitted` skeleton)

```coq
(* The ciphertexts the real Alice program sends.  Run [palice] with the real
   encryption operations on Alice's inputs, then keep the ciphertexts it puts on
   the wire.  [c2 c3] are the ciphertexts Alice receives from Bob and Charlie;
   [g] is the value Charlie returns at the end, which Alice decrypts but never
   re-sends. *)
Definition dsdp_concrete_sends
    (AHE : AHEncType)
    (decode : di_priv_keyT (Standard_DSDP_Interface AHE) ->
              di_cipherT  (Standard_DSDP_Interface AHE) ->
              option (di_msgT (Standard_DSDP_Interface AHE)))
    (ek : party_id -> di_pub_keyT (Standard_DSDP_Interface AHE))
    (dk : priv_key AHE) (v1 u1 u2 u3 r2 r3 : plain AHE) (ra1 ra2 : rand AHE)
    (c2 c3 : cipher AHE) (g : plain AHE) : seq (cipher AHE) :=
  pmap (di_get_cipher (Standard_DSDP_Interface AHE))
    (sent_payloads
       (smc_session_types.erase
          (@palice (Standard_DSDP_Interface AHE) decode ek
             dk v1 u1 u2 u3 r2 r3 ra1 ra2))
       [:: di_data_of_cipher (Standard_DSDP_Interface AHE) c2
         ; di_data_of_cipher (Standard_DSDP_Interface AHE) c3
         ; di_data_of_plain  (Standard_DSDP_Interface AHE) g ]).

(* dsdp_observed_correspondence — the derived game computes the same ciphertexts
   the real Alice program sends.  Take the two combine terms the symbolic run
   produced, evaluate them with the real encryption operations on Alice's real
   inputs (supplied through [env] and the hypotheses below), and the result is
   exactly the ciphertexts the real [palice] puts on the wire.  This equation is
   what certifies the translation: if the symbolic interface or the evaluator
   used the wrong operation (an [Emul] where an [Epow] belongs, say), the two
   sides would differ.  Only the ciphertexts Alice sends are covered.  Her final
   decryption is not: the evaluator sends a decryption to the plaintext zero on
   purpose, so no decrypted value ever appears in a sent term. *)
Lemma dsdp_observed_correspondence
    (AHE : AHEncType)
    (decode : di_priv_keyT (Standard_DSDP_Interface AHE) ->
              di_cipherT  (Standard_DSDP_Interface AHE) ->
              option (di_msgT (Standard_DSDP_Interface AHE)))
    (ek : party_id -> di_pub_keyT (Standard_DSDP_Interface AHE))
    (pkey_of_party : party_id -> pub_key AHE) (rand0 : rand AHE)
    (dk : priv_key AHE) (v1 u1 u2 u3 r2 r3 : plain AHE) (ra1 ra2 : rand AHE)
    (c2 c3 : cipher AHE) (g : plain AHE)
    (env : denv AHE rand0)            (* denote_he's environment, see MkDenv *)
    (* value-pool coupling: de Bruijn names -> concrete values *)
    (Hc2  : de_val_nth env 30 = Gcipher c2)
    (Hc3  : de_val_nth env 31 = Gcipher c3)
    (Hu2  : de_val_nth env 12 = Gplain u2)
    (Hu3  : de_val_nth env 13 = Gplain u3)
    (Hr2  : de_val_nth env 14 = Gplain r2)
    (Hr3  : de_val_nth env 15 = Gplain r3)
    (* randomness-pool coupling: encryption slots -> concrete randomness *)
    (Hra1 : de_rand_nth env 20 = ra1)
    (Hra2 : de_rand_nth env 21 = ra2)
    (* party-tag alignment: HE_enc's nat tag denotes to the protocol's pubkey *)
    (Hpk_bob     : pkey_of_party (nat_to_party_id 1) = ek bob_idx)
    (Hpk_charlie : pkey_of_party (nat_to_party_id 2) = ek charlie_idx) :
  [seq as_cipher (denote_he env t) | t <- dsdp_observed_combines]
    = dsdp_concrete_sends AHE decode ek dk v1 u1 u2 u3 r2 r3 ra1 ra2 c2 c3 g.
Proof.
Admitted.
```

The intended proof is by `denote_he` reduction on the two closed terms
`a1_observed`/`a2_observed` (`dsdp_symbolic.v:164-167`), rewriting by the coupling
hypotheses, against `dsdp_concrete_sends` reduced by computation — both sides
land on `[:: Emul (Epow c2 u2) (enc (ek bob_idx) r2 ra1)
            ;  Emul (Epow c3 u3) (enc (ek charlie_idx) r3 ra2) ]`.
No probability, no relational logic.

### Open design points the skeleton makes explicit

- `denv`'s exact parameterisation (`MkDenv` carries `de_val : seq gval` and
  `de_rand : seq (rand AHE)`, with `de_rand_nth` defaulting to `rand0`); the
  `env`-coupling hypotheses above stand in for "build the env from the concrete
  samples." A cleaner phrasing replaces the eight `de_*_nth` hypotheses with a
  single `env := env_of_inputs …` definition and proves the equations.
- The concrete `decode`/`ek`/`pkey_of_party` come from `palice`'s section context
  (`dsdp_pismc.v:22,107`); the two `Hpk_*` alignment hypotheses are where the
  HE_enc party tags (1 = Bob, 2 = Charlie, `dsdp_symbolic.v:92`) meet the
  protocol's key schedule.
- To add the security cap (lift to L2), follow with the thin lemma
  "pointwise-equal-under-the-sample-coupling ⟹ equal law," landing the result in
  SSProve `SDistr` so `dsdp_advantage_derived` transports onto the protocol.

## 8. Next deliverable

Materialise §7 into a scratch `.v` against the real opam switch, elaborate the
skeleton (resolve `denv`'s parameter list and the `env_of_inputs` phrasing), and
confirm both sides reduce as claimed — sizing the obligation before committing to
the proof. Then, separately, the L2 distributional cap (§3g) and, if the
information-theoretic connection is wanted, the `SDistr`↔`fdist` bridge.
