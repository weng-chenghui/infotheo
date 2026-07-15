# Hypotheses & Lemmas Needed to Formalize the BGW–Shamir IT-Secure Protocol

**Companion to:** `20260428-3party-it-secure-scalar-product-bgw.md` (the protocol design).

**Reference baseline:** `dumas2017dual/dsdp/dsdp_security.v` (the existing Coq/Rocq formalization of DSDP's information-theoretic security analysis).

This note maps out what would change if we re-targeted `dsdp_security.v` from DSDP (Paillier-PHE-based, computationally secure with entropic-security wrap) to the BGW–Shamir 3-party scalar product (perfectly IT-secure, semi-honest, $t = 1$). The audit's verdict was that the BGW–Shamir protocol is correct and IT-secure; the question here is *what would the proof skeleton look like*.

## High-level structural change

| Aspect | DSDP (current) | BGW–Shamir (proposed) |
|---|---|---|
| Field | $\mathbb{Z}/pq\mathbb{Z}$ (composite, for Benaloh) | $\mathbb{F}_p$ (prime field, $p > 3$) |
| Hiding primitive | Public-key homomorphic encryption ($E_{\mathrm{pubP}}$, $D_{\mathrm{privP}}$) | Shamir share masking by uniform $r_s$ |
| Encryption hypotheses | `E_enc_unif`, `E_enc_inde` (axiomatic) | **Eliminated** — replaced by *provable* lemmas about Shamir shares |
| Constraint statement | `constraint_holds` (hypothesis) | `S_def` (definition, by construction) |
| Composite-modulus hypotheses | `prime_p`, `prime_q`, `coprime_pq`, `U3_coprime_m`, `U3_pos`, `U3_lt_minpq` | Dropped entirely (single prime $p$ suffices) |
| Security flavor | Entropic security, $H(V_2 \mid \text{AliceView}) = \log m$ | Same: $H(V_2 \mid \text{AliceView}) = \log p$, but with **provable independence**, no entropic-security wrapper needed |

## Setup section

| Item | DSDP signature | BGW–Shamir signature | Why |
|---|---|---|---|
| Field params | `Variables (p_minus_2 q_minus_2 : nat); Hypothesis prime_p ...; prime_q ...; coprime_pq ...` | `Variable p_minus_4 : nat; Local Notation p := p_minus_4.+4; Hypothesis prime_p : prime p` | Need $p > 3$ so evaluation points $1, 2, 3$ are non-zero and distinct mod $p$ for Lagrange interpolation. |
| Message type | `Local Notation msg := 'Z_(p*q)` | `Local Notation msg := 'Z_p` (or `'F_p`) | Prime field, no need for CRT decomposition. |
| Eval points | (n/a — DSDP doesn't use Shamir) | `Definition x_A : msg := 1. Definition x_B : msg := 2. Definition x_C : msg := 3.` | Fixed points for parties; non-zero for share uniformity, distinct for reconstruction. |

## Random variables

| Item | DSDP | BGW–Shamir | Why |
|---|---|---|---|
| Inputs | `U1, U2, U3, V1, V2, V3` | same | Same protocol functionality. |
| Decryption keys | `Dk_a, Dk_b, Dk_c : {RV P -> Party.-key Dec msg}` | **dropped** | No encryption keys in BGW. |
| Masking randomness | `R2, R3 : {RV P -> msg}` (only two masks in DSDP) | `r_{u1}, r_{u2}, r_{u3}, r_{v1}, r_{v2}, r_{v3}, s_A, s_B, s_C : {RV P -> msg}` | One sharing-randomness per shared input (6) plus one re-share-randomness per party (3). |
| Derived RV: $S$ | `S = D3 - R2 - R3 + U1*V1` (defined) | `S := U1*V1 + U2*V2 + U3*V3` (defined directly) | BGW computes the inner product symbolically; constraint holds by construction. |
| Derived RV: shares | (n/a) | `Definition share (s r x : {RV P -> msg}) : {RV P -> msg} := s \+ r \* x_const` | Each transmitted share. |

## Hypotheses to keep (with exact analogues)

| DSDP hypothesis | BGW–Shamir analogue | Purpose |
|---|---|---|
| `pV1_unif`, `pV2_unif`, `pV3_unif : `\``p_ V_i = fdist_uniform card_msg` | same | Inputs are uniform — needed so $H(V_i) = \log p$ at the entropy step. |
| `VarRV_uniform : `\``p_ [% V2, V3] = fdist_uniform card_msg_pair` | same | Joint uniformity of secrets-being-protected. |
| `VarRV_indep_inputs : P |= [% V1, U1, U2, U3] _|_ [% V2, V3]` | same | Alice's local inputs are statistically independent of Bob's and Charlie's secrets. Standard MPC modeling assumption. |

## Hypotheses to drop

| DSDP hypothesis | Why droppable |
|---|---|
| `E_enc_unif : forall ... `\``p_X = fdist_uniform (card_enc_for' p card_A)` | No encryption in BGW. |
| `E_enc_inde : forall ... P |= X _|_ Y` (the unsound axiom flagged in `f085e59`) | No encryption in BGW; hiding is via *provable* Shamir uniformity. **This eliminates the most concerning axiom in the current development.** |
| `constraint_holds : forall t, dsdp_constraint (CondRV t) (VarRV t)` | $S = \sum u_i v_i$ is BGW's *definition* of $S$, not a separate constraint to assume. |
| `U3_coprime_m`, `U3_pos`, `U3_lt_minpq` | Composite-modulus invertibility hack; not needed in $\mathbb{F}_p$. |
| `cinde_V2V3`, `cinde_V2`, `V3_determined` | DSDP-specific reductions for getting from `AliceView` to `CondRV`; BGW's view structure is different (see new lemmas below). |

## New lemmas needed (Shamir-side infrastructure)

These would live in a new file, e.g. `bgw_shamir.v`, and replace DSDP's encryption module.

| Lemma | Signature (sketch) | What it shows | Why we need it |
|---|---|---|---|
| `share_unif` | `forall (s r : {RV P -> msg}) (x : msg), x != 0 -> P |= r _|_ s -> `\``p_ r = fdist_uniform card_msg -> `\``p_ (s \+ r \* const_RV x) = fdist_uniform card_msg` | A single Shamir share at a non-zero point is uniformly distributed when the masking randomness is uniform and independent. | Direct OTP property — replaces the role of `E_enc_unif`. **Provable** from `lemma_3_5'` already in `smc_proba.v`. |
| `share_indep_secret` | `forall s r x, x != 0 -> P |= r _|_ s -> `\``p_ r = fdist_uniform card_msg -> P |= (s \+ r \* const_RV x) _|_ s` | A single share alone is independent of the secret. | Replaces `E_enc_inde`, but here it is **provable**, not axiomatic. |
| `lagrange_2pt_recover` | `forall (s r : msg) (x1 x2 : msg), x1 != x2 -> x1 != 0 -> x2 != 0 -> let f y := s + r * y in s = lambda1 x1 x2 * f x1 + lambda2 x1 x2 * f x2` (with explicit $\lambda$'s) | Two shares reconstruct the secret via Lagrange. | Used implicitly when reasoning that 2 shares "would" reconstruct — but no party ever has 2 shares of an honest party's secret in our threat model, so this lemma is needed only for the audit narrative, not the main proof. |
| `lagrange_3pt_deg2` | `forall (a b c : msg), let f y := a*y^2 + b*y + c in 3 * f 1 - 3 * f 2 + 1 * f 3 = c` (with $p > 3$) | Lagrange coefficients $(3, -3, 1)$ for interpolation at $x = 0$ from $\{1, 2, 3\}$ correctly recover the constant term $f(0) = c$ for any degree-$\leq 2$ polynomial. | Round-2 degree-reduction correctness. |
| `degree_reduction_correct` | `forall (T_A T_B T_C s_A s_B s_C : {RV P -> msg}), (forall t, 3*T_A t - 3*T_B t + T_C t = S t) -> let h_A := 3*(T_A) - 3*(T_B \+ s_B \* x_A) + (T_C \+ s_C \* x_A) in ...` (analogous for $h_B, h_C$) `, ... let h y := S \+ R_combined \* y in forall P, h_P = h x_P` | The Lagrange combination of fresh degree-1 reshares of $T_A, T_B, T_C$ produces a *fresh* degree-1 sharing of $S$. | Round-2 main correctness lemma. |
| `share_indep_when_one_held` | `forall s r, P |= r _|_ s -> `\``p_ r = fdist_uniform card_msg -> P |= (s \+ r \* const_RV x_A) _|_ (s \+ r \* const_RV x_B)` ❌ — this is **false** in general (two shares of the same poly are correlated through $s$ and $r$). The correct phrasing is conditional: shares are jointly independent of $s$ if the adversary holds at most $t = 1$ of them. | (corrected) Shows IT-security threshold. | Cornerstone of "Alice sees one share ⇒ learns nothing about $v_2$." |
| `view_uniform_below_threshold` | `forall (X Y : {RV P -> _}) (s : {RV P -> msg}), [list of independence conditions] -> P |= [% X, Y] _|_ s` (where $X, Y$ enumerate Alice's $\leq t$ shares) | The whole adversary view is independent of any single secret. | Composes `share_indep_secret` over all of Alice's incoming shares using the existing `inde_RV_comp` and `mixing_rule` from `smc_proba.v`. |

## Hypotheses still needed (independence of fresh randomness from inputs and from each other)

These are the *modeling* assumptions about the protocol's randomness — analogous to DSDP's `R2_indep_VU2_V3` etc., but more numerous because BGW has more masks.

| Hypothesis | Signature | Purpose |
|---|---|---|
| `pr_*_unif` (×9) | `forall r in {r_u1, r_u2, r_u3, r_v1, r_v2, r_v3, s_A, s_B, s_C}, `\``p_ r = fdist_uniform card_msg` | Each masking randomness is uniformly drawn. |
| `randomness_mut_indep` | `P |= [% r_u1, ..., s_C] _|_ unit_RV P` (or pairwise mutual independence stated in graphoid form) | All sharing/reshare randomness is mutually independent. Practically: each party draws its own randomness independently. |
| `randomness_indep_inputs` | `P |= [% all 9 randoms] _|_ [% U1, U2, U3, V1, V2, V3]` | Randomness is drawn independently of the secrets being shared. Standard. |

In DSDP these correspond to `R2_indep_VU2_V3`, `R3_indep_VU3_V1`, etc. — the same flavor, just more of them.

## What the View definitions look like

### Alice's view

```coq
Let alice_round1_in : {RV P -> msg * msg} :=
  [% V2 \+ r_v2 \* const x_A,    (* [v2]_A *)
     V3 \+ r_v3 \* const x_A].   (* [v3]_A *)

Let alice_round2_in : {RV P -> msg * msg} :=
  [% T_B \+ s_B \* const x_A,    (* g_B(1) *)
     T_C \+ s_C \* const x_A].   (* g_C(1) *)

Let alice_round3_in : {RV P -> msg * msg} :=
  [% S_share_B,                  (* [S]_B *)
     S_share_C].                 (* [S]_C *)

Let AliceView : {RV P -> _} :=
  [% V1, U1, U2, U3,             (* her own inputs *)
     alice_round1_in,
     alice_round2_in,
     alice_round3_in,
     S].                         (* the protocol output *)
```

Note: **no encryption keys in the view** — that's an entire dimension of complexity gone.

### Bob's view (and Charlie's, symmetric)

```coq
Let BobView : {RV P -> _} :=
  [% V2,                         (* his own input *)
     [u1]_B, [u2]_B, [u3]_B, [v1]_B,  (* round 1 from Alice *)
     [v3]_B,                     (* round 1 from Charlie *)
     g_A(2), g_C(2)].            (* round 2 reshares *)
```

Bob never receives any $[S]_*$, so his view stops at Round 2. (Reconstruction is at Alice only.)

## Main theorems (parallel to DSDP)

| DSDP theorem | BGW–Shamir analogue |
|---|---|
| `dsdp_constraint_centropy_eqlogm : `\``H(VarRV \| CondRV) = log (m%:R : R)` | `bgw_constraint_centropy_eqlogp : `\``H([% V2, V3] \| [% V1, U1, U2, U3, S]) = log (p%:R : R)` |
| `dsdp_entropic_security : `\``H(V2 \| AliceView) = log m /\ `\``H(V2 \| AliceView) > 0` | `bgw_alice_privacy_V2 : `\``H(V2 \| AliceView) = log p /\ `\``H(V2 \| AliceView) > 0` |
| `bob_privacy_V1, bob_privacy_V3, charlie_privacy_V1, charlie_privacy_V2` | `bgw_bob_privacy_*`, `bgw_charlie_privacy_*` (same shape, different views) |
| `US_compromised_leaks_V2` (malicious case where Alice sets $u = (1, 0)$) | **Same theorem applies if the threat model is extended to malicious** — but in the strict semi-honest, $t = 1$ model BGW does not need this. Could be added as an analogue, parallel to DSDP's existing analysis. |

## What this saves vs. DSDP's current proof

| Saving | Mechanism |
|---|---|
| Eliminate the unsound `E_enc_inde` axiom | Replaced by *provable* `share_indep_secret`. |
| Eliminate `E_enc_unif` axiom | Replaced by *provable* `share_unif` (direct application of `lemma_3_5'`). |
| Eliminate composite-modulus apparatus (`coprime_pq`, `U3_coprime_m`, `U3_pos`, `U3_lt_minpq`, CRT-based fiber argument in `linear_fiber_zpq.v`) | Prime field, $\mathbb{F}_p$ is itself a field, multiplicative inverses always exist for non-zero elements, no fiber decomposition needed. |
| Eliminate `constraint_holds` hypothesis | Constraint is built into the definition $S := \sum u_i v_i$. |
| Eliminate `V3_determined` hypothesis | The view-to-constraint reduction looks different in BGW; $V_3$ is recoverable from $(V_1, U_1, U_2, U_3, S, V_2)$ exactly as in DSDP, so this hypothesis carries over identically — *not* saved. |

## What this costs vs. DSDP's current proof

| Cost | Mechanism |
|---|---|
| 9 uniformity hypotheses for randomness instead of DSDP's 2 (R2, R3) | More masks because BGW shares all six inputs and re-shares all three local products. |
| New degree-reduction correctness lemma | DSDP doesn't have an analogue because it uses encryption, not polynomials. |
| New round-3 reconstruction lemma | DSDP's reconstruction is a single decryption; BGW's is a 3-point Lagrange interpolation. |
| Larger view structure | More shares to track than DSDP's three encrypted blobs. |

## Summary

The BGW–Shamir formalization would be **structurally simpler** than DSDP:

- 0 encryption axioms (vs. 2 in DSDP, one of which is acknowledged as unsound).
- 1 prime $p$ instead of composite $pq$ with CRT machinery.
- All hiding properties **provable** from `lemma_3_5'` (already in `smc_proba.v`) plus elementary linear algebra (Lagrange interpolation).

The price is more random variables (9 masks instead of 2) and a larger transcript per party, but each per-share argument is a uniform application of the same OTP lemma.

The key insight: DSDP's complexity in `dsdp_security.v` is largely an artifact of needing to *axiomatize* what encryption does (`E_enc_unif`, `E_enc_inde`) because Paillier's IT-property is non-existent — these axioms are stand-ins for entropic-security claims that aren't actually true of Paillier in the standard sense. Replacing the protocol with one that has a real IT-secure primitive (Shamir + uniform mask) collapses those axioms into provable lemmas, removing the need to *trust* the encryption abstraction.
