# Option A feasibility probes: can the derivation reliably produce the output game?

Date: 2026-07-16
Status: SUPERSEDED by adversarial audit (2026-07-16). Do not run P1-P7 as written.
See "Audit outcome" below.
Related: 20260715-blueprint-v2-design.md (the derivation gap, §"routes")

## Audit outcome (2026-07-16) — two FATALs, spec not run

Two adversarial audits (logic + technical), both verified against code:

1. **FATAL — wrong fallback baseline.** The seeded trace
   `dsdp_alice_obs_leak_S_seeded` writes its output directly in fiber form
   `u1*v1 + u2*v2 + u3*v3` (no `HE_dec`, no placeholder). `denote_output_termE`
   denotes it to `dsdp_output` **definitionally** (no bridge). The security
   result `dsdp_alice_guess_ideal_le` (guess <= 1/m) is **Qed today** on it. So a
   bridge-death does NOT fall to "Option B, no code" -- the seeded trace is an
   already-proved, bridge-free baseline that dominates. The decision tree's top
   row was wrong.
2. **FATAL — wrong protocol topology.** The chain is Alice -> Bob -> Charlie ->
   Alice, not Alice -> Charlie. `pbob` does the homomorphic combine and forwards
   to Charlie (`dsdp_pismc.v:117-124`); `pcharlie` receives from Bob
   (`dsdp_pismc.v:127-133`). Deriving `g` needs TWO responders run in sequence,
   not "run pcharlie on Alice's outputs". P5/P7's "small connector" was
   calibrated on a topology that does not exist. (Positive: `g` IS under Alice's
   key, so `dec_alice(g)` cancels; route 1 is not dead for the key reason.)

Also confirmed: P4's "trivial" v1/u1 fix over-captures name 50 (`term_value_names`
descends into `HE_dec`); P3 is near-certain FAIL (the fiber layer is hard-wired
to the seeded tree by `gc_eq`'s `vm_compute`); the feasibility bar is too
syntactic to catch a well-formed-but-wrong `g`; P1's leaf list names
`dsdp_is_correct`, which is the Idealized (identity-encryption) instance and
useless as the abstract bridge's leaf.

**Reframing the audits force:** the security bound is already proved (seeded
trace). Route 1 buys only a provenance claim (output derived + certified
faithful), and is now understood as a LARGE build (two-responder symbolic
execution + new dec-form S-determination + a homomorphic-decryption bridge whose
leaves are not ready + re-proving the fiber layer). The real decision is not
"is route 1 feasible" but "does the thesis's derivation claim require the output
channel to be derived, or is a scoped 'ciphertext channel derived; output value
supplied in fiber form' honest enough". Pending user decision.

---

## Original spec below (retained for the probe designs; premises now corrected above)


## The decision this probe set informs

**Option A** = make the derivation mechanism reliably generate the
output-exposing SSProve game, with the protocol-correctness step as a
machine-checked link. **Route 1** (chosen): the mechanism must itself produce the
aggregate `g` Charlie returns, symbolically, rather than accept a hand-supplied
placeholder.

The probes decide **build Option A (route 1), or fall back**, with evidence: is
it feasible, roughly how big, and where are the hard spots. The probes build
nothing in the repo. All experiment code lives in the scratchpad and is
discarded.

## Established facts (verified this session, not assumed)

1. The derived output trace `dsdp_alice_obs_leak_S` references three value names
   that are neither sampled nor bound: `16` (v1), `17` (u1), `50` (the
   aggregate). Confirmed by Compute: referenced-but-unbound = `[50; 17; 16]`.
2. `16`, `17` are unbound only because `obs_value_names` (dsdp_game_derivation.v:366)
   has no `AO_recv_output` case. Adding it makes `collect_samples` sample them.
   Trivial.
3. `50` is a hand-supplied placeholder: `dsdp_recv_responses` (dsdp_symbolic_exec.v:147)
   binds Charlie's returned aggregate to `SD_cipher (HE_var 50)`. It is a
   received value, not a fresh draw, so it cannot be sampled.
4. Symbolic execution builds `he_term` syntax trees (`di_encrypt := fun pk m r =>
   HE_enc pk m r`, etc.); it never runs Benaloh/Paillier. The concrete scheme
   enters only at denotation, usually as an abstract `Variable AHE : AHEncType`.
5. Symbolic decrypt does not cancel encrypt: `symbolic_Recv_dec`
   (dsdp_symbolic_exec.v:58) yields `HE_dec sk c` and stops. `HE_dec sk (HE_enc
   sk m r) = m` is decryption correctness of the concrete scheme, invoked at
   denotation, not a syntactic rewrite.
6. `sent_payloads` (dsdp_symbolic_exec.v:108) is a generic proc interpreter: it
   runs any party's program against a response stream, multi-round. The machinery
   to run a responder exists; the wiring that feeds Alice's outputs into Charlie
   and Charlie's aggregate back into Alice does not.
7. The fiber argument (`dsdp_guess_fiber`, `Pr_dsdp_sol_uniform_ring`) consumes
   the output in the form `S = u1*v1 + u2*v2 + u3*v3`. The derived walk produces
   `S = dec_alice(g) - r2 - r3 + u1*v1`. Bridging the two is protocol correctness.

**Consequence:** both routes need the same correctness bridge at denotation.
Route 1 additionally needs the mechanism to produce `g`, which runs no crypto
(just a bigger syntax tree) and does not remove the bridge.

## Approach: hybrid, bridge-first then integration spike

**Phase 1 = kill-switch (Approach 1, bridge-first).** The correctness bridge is
the shared necessary condition for BOTH routes. If it cannot be stated or
skeleton-proved, Option A is dead and so is the route-2 fallback, discovered for
the least effort. Probes P1-P3.

**Phase 2 = integration spike (Approach 3), only if Phase 1 passes.** Route 1's
biggest risk is not any single piece (the interpreter exists; the bridge either
reduces or does not) but whether derived-`g`, the walk, the bridge, and the fiber
argument compose without one disturbing another. A thin end-to-end skeleton with
`Admitted` leaves tests exactly that. Probes P4-P7, assembled as one spike.

**Feasibility bar.** A probe passes only if its skeleton compiles with `Admitted`
confined to named correctness leaves that are known-true, in-tree facts. No
`Admitted` at a structural or integration joint. A skeleton that Admits a joint
has proved nothing.

## Phase 1 — the correctness bridge (kill-switch)

### P1 — State the bridge lemma
- **Asks:** can the "derived output game equals the fiber-form output game"
  claim even be phrased, at the denotation level, over an abstract `AHE`?
- **Run:** in a scratch file, over `Variable AHE : AHEncType`, write the
  statement `denote(derived_S_term) = denote(fiber_S_term)` (or the game-level
  `AdvantageE ... = 0`). Confirm it type-checks. Enumerate the exact correctness
  facts its hypotheses would need.
- **Pass:** statement type-checks; every hypothesis it needs is a fact that
  exists in-tree (`dsdp_is_correct`, the `EncDec` decryption law, the AHE
  homomorphic laws).
- **Fail:** the claim cannot be phrased at the game level, or it needs a fact
  that does not exist or is not true.
- **Specific risk to surface:** `g` is a homomorphically-combined ciphertext, so
  `dec_alice(g)` needs the AHE *homomorphic* correctness (decrypt of a combined
  ciphertext = the combined plaintext), which is stronger than plain dec-enc
  cancellation. P1 must name whether that law is available in-tree.

### P2 — Skeleton-prove the bridge
- **Asks:** does the bridge reduce cleanly to `dsdp_is_correct` + ring algebra,
  or hit a wall?
- **Run:** prove the P1 statement with the STRUCTURE fully connected and
  `Admitted` only at the leaf correctness facts. This is where "does `dec_alice(g)`
  actually equal `u2*v2 + u3*v3 + r2 + r3`, so the masks cancel to the scalar
  product" gets tested.
- **Pass:** skeleton compiles; remaining `Admitted`s are exactly the known
  correctness leaves, each a real provable fact.
- **Fail:** the reduction leaves a gap that is NOT a known correctness fact (masks
  do not cancel; key mismatch means `dec_alice(g)` is not the aggregate; the
  homomorphic law needed is absent or false).

### P3 — Composition with the fiber argument
- **Asks:** if the certified derived game replaces the seeded game, does the
  existing fiber chain (`dsdp_alice_guess_ideal_le` -> `guess_fiber` ->
  `Pr_dsdp_sol_uniform_ring`) still apply, or is it coupled to the seeded trace's
  exact shape? (Which of the two is unknown until inspected; this probe decides
  it.)
- **Run:** inspect what `dsdp_guess_fiber` consumes (`guess_sample_fdist`,
  `guess_S_determined`, `Sout`): does it reach the output only through its VALUE,
  or does it pattern-match the seeded game structure?
- **Pass:** the fiber argument reaches the output only through its value, which the
  bridge preserves; the swap is transparent.
- **Fail:** the fiber layer is coupled to the seeded syntax and must be re-proved.

**Phase 1 gate:**
- P1 or P2 fail -> Option A infeasible (bridge impossible); route 2 also dead ->
  recommend Option B.
- P3 fail -> bridge exists but integration into the fiber layer is expensive ->
  size it before deciding.

## Phase 2 — integration spike (only if Phase 1 passes)

Assembled as ONE scratch file that runs derive-`g` -> walk -> bridge (`Admitted`)
-> fiber (`Admitted`) and must type-check end to end. P4-P7 are its steps.

### P4 — Bind v1/u1 (the trivial fix), spike step 0
- **Run:** add the `AO_recv_output` case to `obs_value_names` / `obs_rnd_names`;
  recompute referenced-but-unbound.
- **Pass:** drops `16`, `17`, leaving only `50`. (Half-verified already.)

### P5 — Produce `g` by running the responder
- **Unverified premise to establish first:** which of Alice's outputs Charlie
  actually receives (a1 or a2), and whether `pcharlie_sym` has a
  receive-then-send structure after its head Send at all. Read `pcharlie` before
  constructing the stream; do not assume "Charlie receives a2".
- **Asks:** does `sent_payloads pcharlie_sym <Charlie's actual response stream>`
  yield Charlie's later Send (the aggregate)?
- **Run:** Compute. Construct Charlie's response stream from the established
  premise, run `sent_payloads`, inspect the non-head Send.
- **Pass:** a non-head Send appears and is a well-formed `he_term` aggregate tree.
- **Fail:** the proc has no post-receive Send in the model (Charlie does not
  respond in Alice's-view scope), or the interpreter cannot be driven past the
  head.

### P6 — Wire `g` into Alice's stream and re-derive
- **Asks:** replace `dsdp_recv_responses`' `HE_var 50` with the P5-produced `g`,
  re-run Alice's walk: does the output term reference only bound names, and does
  its tree match the shape the P1/P2 bridge consumes?
- **Run:** Compute the walk with the new stream; check referenced-but-unbound is
  empty; check the output tree has the `dec_alice(HE_enc alice ...)` structure the
  bridge collapses.
- **Pass:** no dangling names; output tree matches the bridge's input shape.
- **Fail:** `g`'s tree does not decrypt-cancel (key mismatch), or `g` introduces
  fresh unbound refs.

### P7 — Cross-party wiring cost
- **Asks:** how much NEW code assembles Charlie's response stream from Alice's
  outputs and threads `g` back? A small connector, or a general multi-round
  network driver?
- **Run:** from P5/P6, count the new definitions needed to thread a1/a2 ->
  Charlie -> `g` -> Alice. Assess whether it fits the existing derivation file or
  needs a new subsystem.
- **Pass:** small connector (~1-2 definitions), fits the existing structure.
- **Fail:** needs a general multi-round driver (a large new subsystem).

**Spike verdict:** the assembled scratch file type-checks end to end, with
`Admitted` only at the bridge and fiber correctness leaves.

## Decision tree

| Probe outcome | Verdict |
|---|---|
| P1 or P2 fail | Option A infeasible; route 2 also dead -> **Option B** |
| P1/P2 pass, P3 fail | bridge OK, fiber re-proof needed -> size, likely A but bigger |
| Phase 1 pass, P5 fail | mechanism cannot produce `g` -> route 1 dead; offer route 2 or B |
| Phase 1 pass, P6 fail (key mismatch / new dangling) | derived `g` does not collapse to the fiber form -> route 1 needs the model reworked; offer route 2 or B |
| Phase 1 pass, P5/P6 pass, P7 small | **Option A route 1 feasible, small** -> build plan |
| Phase 1 pass, P7 = big driver | route 1 feasible but large -> user decides A-large / route 2 / B |

## Execution

- Run inline (rocq-mcp / scratch files + the local switch coqc at
  `/Users/cheng-huiweng/Projects/coq/_opam/bin/coqc`, OCaml 5.2.1; no `timeout`
  on macOS). Inline probes have settled every question fast this session;
  delegated provers have tended to spin.
- Everything in the scratchpad. Nothing touches the repo.
- Effort for the probing itself: small. These are Compute + skeleton proofs, not
  full proofs. A focused session.

## Non-goals

- Not building Option A. Not changing the repo. Not writing the blueprint. Not
  fully proving the bridge. The deliverable is a verdict with evidence, plus
  throwaway scratch code.
