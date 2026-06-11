# 2026-06-11 — Two-channel secrecy (UPGRADED): `S` now flows through the guessing game; `1/m` by the fiber, not direct independence

## Status

**Upgraded version of [[20260525-two-channel-secrecy-fiber-vs-indcpa]].** That
2026-05-25 memo concluded the `1/m` bound is discharged by **direct
independence** (the `game_enc_zero` predictor imports only `id_game_run`, sees
ciphers only, never `S`; the fiber machinery is "orphaned, delete it"). This
session **reversed that decision**: the direct-independence `1/m` is the trivial
/ vacuous one (the project explicitly wanted the security-meaningful fiber `1/m`,
not the one where the view is already `V2`-free). To make the meaningful `1/m`
real we:

1. added an `id_s_get` oracle so the predictor **does** receive `S`, and
2. recomposed the leaked `S` as the **genuine scalar product**
   `S = u1·v1 + u2·v2 + u3·v3` (it was previously a degenerate `−(r2+r3)`),

so the `1/m` now comes from the **fiber** (`Pr_dsdp_sol_uniform_ring`), not from
direct independence. Lines 49–136 of the 2026-05-25 memo (the "no fiber, direct
independence, delete the fiber" conclusion) are **superseded** by this note.

## What changed, in one table

| | 2026-05-25 (old) | 2026-06-11 (this session) |
|---|---|---|
| predictor view | ciphers `[a1;a2;c2;c3]` only | **`(ciphers, S)`** |
| `S` reaches predictor? | no (no `id_s_get`) | **yes**, via `id_s_get` |
| `S` value | degenerate `−(r2+r3)` | **`u1·v1+u2·v2+u3·v3`** (genuine) |
| `1/m` argument | direct independence (view ⊥ `V2`) | **fiber counting on `S`** |
| at all-zero endpoint | view already `V2`-free → trivial | ciphers `V2`-free, **`S` carries `V2` via `u2·v2`** → fiber |
| tool | (none meaningful) | `Pr_dsdp_sol_uniform_ring`, `dsdp_entropy.v` |

## Diagram 1 — the guessing experiment, WITH `S` (the upgrade)

The old guessing game handed the predictor only `view`. The upgrade inserts
step (2): the challenger now also calls `id_s_get` and passes `(view, S)` to the
predictor. Matches the live `guessing_challenger` body
(`dsdp_security_indcpa_fiber.v`): `view ← call_run ;; s ← call_s_get ;;
guess ← call_pred (view, s) ;; v2 ← call_v2 ;; ret (guess == v2)`.

```
  CHALLENGER (boolean)      ONE GAME (zero_game_leak_S)     PREDICTOR (= adversary A)
  ════════════════════      ═══════════════════════════     ════════════════════════
        │                            │                             │
  (1)   │── id_game_run ────────────►│  sample v2,v3,r2,r3         │
        │                            │  run protocol once          │
        │◄── view=[a1;a2;c2;c3] ──────│  (ciphers = Enc 0 here)     │
        │                            │  + write S to S_output_cell │
        │                            │                             │
  (2)   │── id_s_get ───────────────►│       ◄── THE UPGRADE        │
        │◄── S = u1v1+u2v2+u3v3 ──────│  (genuine scalar product)   │
        │                            │                             │
  (3)   │── call_pred (view, S) ────────────────────────────────►│ sees BOTH
        │◄──────────── guess g ───────────────────────────────────│ view AND S
        │                            │                             │ (blind to V2_cell)
        │                            │                             │
  (4)   │── id_v2_get ──────────────►│  (challenger-only: scoring) │
        │◄──── v2 = V2 ───────────────│                             │
        │                            │                             │
  (5)   │  return (g == v2) : bool
        ▼
   win ⟺ g = V2.

  The predictor is fed (view, S). id_v2_get is the only oracle it never sees
  (challenger uses it solely to score guess == V2). Same adversary, repackaged
  as challenger ∘ predictor, is the IND-CPA distinguisher for the 2·ε_cpa leg.
```

## Diagram 2 — one game, two channels (packaging vs channels)

A "channel" is not a package; it is one component of the single game's output
bundle — a conduit through which `V2` can leak. Two oracles project the one
bundle into the two channels.

```
  ┌──────────────────────────────────────────────────────────────────────────┐
  │ ONE GAME, ONE raw_code, ONE output bundle:                                 │
  │     ┌───────────────────────┐                                             │
  │     │ ciphers [a1;a2;c2;c3]  │ ── id_game_run ──►  CHANNEL 2 (cipher)      │
  │     │ scalar  S  in S_cell   │ ── id_s_get   ──►  CHANNEL 1 (output)       │
  │     └───────────────────────┘                                             │
  └──────────────────────────────────────────────────────────────────────────┘

  ┌─ CHANNEL 1 — OUTPUT (S) ───────────┐   ┌─ CHANNEL 2 — CIPHER ──────────────┐
  │ S = u1·v1 + u2·v2 + u3·v3           │   │ encrypted contributions           │
  │ Alice is SUPPOSED to learn S        │   │ [a1;a2;c2;c3] she receives        │
  │ (functionality, not removable).     │   │ (could leak MORE than S alone).   │
  │                                     │   │                                   │
  │ Tool:  fiber counting               │   │ Tool:  IND-CPA hybrid hops        │
  │   Pr_dsdp_sol_uniform_ring          │   │   real → … → all-zero,            │
  │   (dsdp_entropy.v, route F)         │   │   dsdp_advantage_derived_leak_S   │
  │ Nature: INFORMATION-THEORETIC       │   │ Nature: COMPUTATIONAL             │
  │ Bound:  ≤ 1/m                       │   │ Bound:  ≤ 2·ε_cpa                 │
  │ S is the LOAD-BEARING carrier here  │   │ S is COMMON CONTEXT here (cancels)│
  └─────────────────────────────────────┘   └────────────────────────────────────┘
                    │                                     │
                    └──────────────┬──────────────────────┘
                                   ▼
                       triangle inequality
                Pr[A wins | real]  ≤  1/m + 2·ε_cpa,   ∀ A

  THE HINGE: at the all-zero endpoint the ciphers are Enc(0), so CHANNEL 2 is
  CLOSED — it carries no V2. Only CHANNEL 1 stays open, and S's fiber of size m
  caps the residual at 1/m. The 2·ε_cpa is the cost of having closed channel 2.

  Same experiment, same four oracles, predictor fed (view, S). The two "paths"
  are the two BOUNDING ARGUMENTS over the one experiment: S is common context
  for the 2·ε_cpa argument and the load-bearing carrier for the 1/m argument.
  No package is a channel.
```

## One line

One game, one `raw_code`, one output bundle; `id_game_run`→ciphers (channel 2,
IND-CPA, `2·ε_cpa`), `id_s_get`→`S` (channel 1, fiber, `1/m`); the predictor is
fed `(view, S)`; the two bounds join by the triangle inequality. The upgrade
over 2026-05-25 is that `S` now genuinely flows through the guessing game and
the `1/m` is the **fiber** bound, not the trivial direct-independence one.
