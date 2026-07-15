# How far are we from having AG-based reconstruction instead of sum-mod-N and Shamir?

## What's built (bottom-up)

| Layer | File | Status |
|-------|------|--------|
| Linear code from generator matrix | `ag_code.v` | Done (Goppa bound axiomatized) |
| Massey secret sharing from code | `massey.v` | Done (fully proved) |
| AG code → ThresholdScheme + gap | `ag_massey_bridge.v` | Done (`ts_T ≤ ts_k + 2g` proved) |
| Transport F ↔ 'I_N | `rs_massey_bridge.v` | Done (reused) |
| Code-level compatibility bridge | `code_compatibility.v` | Done (`share_compatible → ts_compatible`) |
| Genus-1 CoveringScheme | `cover_genus1.v` | Done (code-level axioms) |
| Higher-genus CoveringScheme | `cover_genus1.v` | Done (same pattern) |

## What plugs in where

The protocol correctness theorem (`pgg_secret_invariant` in `pgg_sharing_framework.v`) is **already parametric** in `ThresholdScheme`. It doesn't care whether the scheme comes from sum-mod-N, RS/Shamir, or AG codes. So the AG path already works end-to-end:

```
ag_code ev  →  ag_massey  →  ag_genus_scheme  →  CoveringScheme  →  pgg_secret_invariant
              (massey.v)    (transport to 'I_N)   (cover_genus1.v)   (protocol correctness)
```

## What's still axiomatized

1. **`ts_compatible`** (Issue #39) — monodromy preserves reconstruction. `code_compatibility.v` reformulates this as `share_compatible` (code-level), but both genus-0 and genus-1 still axiomatize it. This is the **only scheme-level axiom remaining**.

2. **`goppa_wt`** — Goppa weight bound from Riemann-Roch. Code-level axiom, needs algebraic geometry to prove.

3. **`ag_priv_surj`** — privacy surjectivity from dual distance. Code-level axiom. (For RS/genus-0, this is **proved** via Lagrange interpolation in `lagrange.v` + `rs_privacy.v`.)

4. **`genus0_pgl`** — Aut(P^1) ≅ PGL(2,F_q), used only in `cover_tradeoff.v`.

## Distance from "fully AG-based"

**Short answer: We're there for the abstract pipeline.** The AG path produces a `CoveringScheme` that feeds into `pgg_secret_invariant` and `security_threshold_tradeoff` — exactly the same interface as sum-mod-N/Shamir.

**What "fully AG-based" would additionally mean:**
- Proving `goppa_wt` from Riemann-Roch (deep algebraic geometry — likely out of scope)
- Proving `ag_priv_surj` from dual code theory (doable but substantial)
- Proving `share_compatible` for specific curves (needs curve automorphism theory)

**Task 4 (deferred)** would let `cover_genus0.v` and `cover_genus1.v` state the compatibility hypothesis as `share_compatible` instead of `ts_compatible` — a cosmetic improvement since they're equivalent for Massey schemes, but makes the axiom boundary more transparent.

The sum-mod-N scheme (`pgg_sum_mod.v`) is orthogonal — it's a **different** concrete instance of `ThresholdScheme` used for the basic single-component protocol. It coexists with the AG path rather than being replaced by it.
