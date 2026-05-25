# 2026-05-25 — SSProve `distr R` ↔ Infotheo `R.-fdist` bridge in the IND-CPA chain

## Question

Does the IND-CPA related code in `dumas2017dual/dsdp/ref/dsdp_security_indcpa.v`
have a place that needs a bridge between Infotheo's `fdist` (full distribution)
and SSProve's `distr R _` / SDistr (sub-distribution)?

## Short answer

Yes. The bridge exists in this file already (Task 12 of the plan). The
IND-CPA chain itself (`Pr_guess_le`, `advantage_game_real_game_enc_zero`,
`Hunp_ge_bound`) works entirely SSProve-side. The bridge is needed to
**discharge the section hypothesis `Pr_guess_enc_zero_le_invm`**, which is
the only remaining IT-flavoured step. Its discharge runs in Infotheo land
(`cPr_eq` over a joint fdist), and the bridge converts the SSProve
denotation of `game_enc_zero` into the Infotheo fdist that residual
analysis consumes.

The bridge construction is done. What is missing is the concrete
application at the consumer site (Task 13/14).

## Where the bridge sits

Lines 2500–2640 of `ref/dsdp_security_indcpa.v`, under the section header
`Task 12: SDistr-to-fdist bridge for alice_view`. Four named pieces:

| Identifier | Type | Role |
|---|---|---|
| `bridge_psum_to_bigop` (2520) | `\sum_(v : alice_view) (distr.mu mu) v = psum (distr.mu mu)` | Reconciles MathComp's bigop with SSProve's `psum` over a `finType` carrier |
| `bridge_enc_zero_to_fdist` (2550) | `(mu : distr R alice_view) → psum = 1 → R.-fdist alice_view` | Constructor: takes a sub-distribution and a mass-1 proof, returns an Infotheo `fdist` |
| `bridge_enc_zero_to_fdistE` (2570) | `bridge_enc_zero_to_fdist Hmass v = distr.mu mu v` | Elementwise equation so downstream proofs can evaluate the bridged fdist |
| `bridge_total_mass` (2592) | `mass = 1 → \sum (distr.mu mu) v = 1` | Exported `FDist.make` obligation |

So the SDistr → fdist construction itself is done.

## Where the bridge is needed in the IND-CPA chain

Exactly one place: the **discharge of `Pr_guess_enc_zero_le_invm`**, the
section hypothesis used by `Pr_guess_le`.

```coq
Hypothesis Pr_guess_enc_zero_le_invm :
  forall (predictor : predictor_guesser),
    distr.mu (pkg_advantage.Pr
                (guess_indicator_pkg predictor game_enc_zero)) true
      <= (card_t_msg%:R)^-1.
```

This is an SSProve-side statement (`distr.mu (Pr …) true`). The discharge
is an information-theoretic fact: in `game_enc_zero` the ciphers are
independent of V_2, so V_2 stays uniform on the fiber, so the conditional
probability collapses to `1/m`. The natural framework for that argument is
Infotheo's `cPr_eq` / fdist machinery, which lives over
`R.-fdist alice_view_joint`, not over `distr R _`.

The docstrings make this explicit:

- 1603–1604: *"The discharge at concrete instantiation (T6) routes through
  the bridged joint fdist `fdist_game_enc_zero_joint` and the residual
  uniformity `cPr_V2_V3_uniform_on_fiber_joint`."*
- 2536–2543: *"This is the central piece of plumbing that lets the IT
  residual analysis (Task 13) run against an infotheo `{fdist alice_view}`
  while the upstream IND-CPA hops (Tasks 06–08) work over SSProve's
  `distr R alice_view`."*

So `Pr_guess_le` / `Hunp_ge_bound` are entirely SSProve-side. The bridge
is what lets the one remaining IT hypothesis be proven in Infotheo land
and ported back.

## What is not yet wired

The fdist on the Infotheo side is currently abstract:

```coq
(* line 3118 *)
Variable fdist_game_enc_zero_joint : R.-fdist alice_view_joint.
```

i.e. "assume someone hands us this fdist." The residual section then
defines `V_2`, `V_3`, `U_3`, `S`, etc. as
`{RV fdist_game_enc_zero_joint -> _}` and proves
`cPr_V2_V3_uniform_on_fiber_joint`.

The bridge's job is to construct this `Variable` concretely from
`Pr_fst (game_enc_zero code)` plus a `LosslessCode (game_enc_zero code)`
proof (which provides `psum = 1` and feeds `bridge_enc_zero_to_fdist`'s
mass hypothesis). That construction — the application of the bridge — has
not landed in this file yet.

`bridge_enc_zero_to_fdist`'s docstring spells out the deferral:
*"The function is parametric in `mu` and its mass-1 hypothesis: the
`Pr_fst game_enc_zero`-specific instance is the consumer's obligation
(Task 13 will supply it via `LosslessCode` resolution on the resolved
`game_enc_zero` code)."*

## Present state, three layers

1. **Bridge construction (Task 12)**: done. Lines 2500–2640.
2. **Abstract fdist consumer (residual section)**: done. Lines 3087–3290
   use the `Variable fdist_game_enc_zero_joint` and prove the residual
   uniformity facts against it.
3. **Concrete application (Task 13/14)**: not yet done. Need a
   `LosslessCode (game_enc_zero code)` proof, then feed
   `Pr_fst (game_enc_zero code)` and that lossless proof to
   `bridge_enc_zero_to_fdist`, then identify the result with
   `fdist_game_enc_zero_joint`.

## Short answer for a peer

> Yes, we need that bridge, and the constructor is already there
> (`bridge_enc_zero_to_fdist` in Task 12). It sits between SSProve's
> `distr R alice_view` and Infotheo's `{fdist alice_view}`. It is needed
> to discharge the IT-side hypothesis `Pr_guess_enc_zero_le_invm` — the
> only remaining Infotheo-flavoured step in the IND-CPA chain — by
> routing the SSProve denotation of `game_enc_zero` through the bridge
> to land on an Infotheo joint fdist where the residual uniformity
> argument can run. The bridge is built. What is missing is the concrete
> application at the consumer site (Task 13/14: produce a
> `LosslessCode (game_enc_zero code)` proof and feed it to
> `bridge_enc_zero_to_fdist` to instantiate the currently-abstract
> `fdist_game_enc_zero_joint`).

## Related

- `[[20260430-dsdp-unpredictability-entropy-audited-plan]]` — the plan
  this Task 12 / Task 13 split comes from.
- `[[20260515-chain-status-after-W3]]` — chain status after the W2/W3
  transport lemmas; predates the rename of `entropy` → `Hunp`.
- `[[20260523-ssprove-package-proof-pattern]]` — the SSProve proof pattern
  used elsewhere in this file.
