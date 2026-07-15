# 3-Party IT-Secure Scalar Product over an Arbitrary Commutative Ring (Replicated Secret Sharing)

**Companion to:** `20260428-3party-it-secure-scalar-product-bgw.md` (Shamir-over-field version) and `20260427-its-homomorphic-encryption-survey.md`.

**Reference baseline:** `dumas2017dual/dsdp/dsdp_security.v` (the existing DSDP IT-security formalization).

**Why this exists.** The BGW–Shamir protocol relies on field-style invertibility: Lagrange reconstruction divides by point-pair differences, and one-share uniformity needs the evaluation point to be a unit. In a generic ring (e.g., $\mathbb{Z}/2^k$), neither holds. Practical 3-party honest-majority MPC libraries (ABY3, MOTION, MP-SPDZ in 3PC mode) therefore use **2-out-of-3 replicated secret sharing (RSS)**, originally due to Araki–Furukawa–Lindell–Nof–Ohara (CCS 2016). RSS works over **any commutative ring** because it has no polynomials and no division.

This note specifies the protocol and lays out the hypotheses/lemmas that a Coq/Rocq formalization (along the shape of `dsdp_security.v`) would require.

## Setup

- Commutative ring $R$ with $|R| = n \geq 2$. **No primality, no coprimality, no field structure required.** Concrete examples: $\mathbb{F}_p$, $\mathbb{Z}/(pq)$, $\mathbb{Z}/2^k$, any product ring.
- 3 parties: Alice ($P_1$), Bob ($P_2$), Charlie ($P_3$). Indices cyclic mod 3 with $i+1$ wrap (so $P_1 \to P_2 \to P_3 \to P_1$).
- Inputs: Alice has $u_1, u_2, u_3, v_1 \in R$; Bob has $v_2$; Charlie has $v_3$.
- Goal: Alice learns $S = u_1 v_1 + u_2 v_2 + u_3 v_3$, no party learns anything beyond input + output.
- Threat model: semi-honest, at most one corrupted party.
- Channels: pairwise IT-secure authenticated private channels.

## Notation

| Symbol | Meaning |
|---|---|
| $s$ | a secret (e.g., $v_2$) |
| $\langle s \rangle$ | RSS sharing of $s$: a triple $(s_1, s_2, s_3) \in R^3$ with $s = s_1 + s_2 + s_3$ |
| $[s]_{P_i} := (s_i, s_{i+1})$ | $P_i$'s **pair** of pieces. Each party holds two of three. |
| $r_{s,1}, r_{s,2}$ | the sharer's fresh uniform randomness; $s_1 := r_{s,1}, s_2 := r_{s,2}, s_3 := s - r_{s,1} - r_{s,2}$ |
| $z_i$ | $P_i$'s additive share of a product, computed locally |
| $\alpha_i$ | $P_i$'s zero-sharing mask, $\sum \alpha_i = 0$ |
| $\rho_i$ | $P_i$'s fresh uniform random for zero-sharing chain |
| $z'_i := z_i + \alpha_i$ | $P_i$'s re-randomized additive share of $S$ |

In particular, $[v_2]_{Alice} = (v_{2,1}, v_{2,2}) = (r_{v_2,1}, r_{v_2,2})$ — **two uniformly random ring elements**, independent of $v_2$.

## Protocol

```
       Alice (P1)              Bob (P2)              Charlie (P3)
        ==========             ========              ============
inputs: u1, u2, u3, v1            v2                      v3
            |                      |                      |
================ Round 1 - input sharing + zero-sharing setup =========
            |                      |                      |
   Alice for each x in {u1,u2,u3,v1}:
     pick r_{x,1}, r_{x,2} uniform in R
     compute (x_1, x_2, x_3) = (r_{x,1}, r_{x,2}, x - r_{x,1} - r_{x,2})
   Bob: same for v2.  Charlie: same for v3.
            |                      |                      |
            |--- (u_*,2,u_*,3 ; v1,2,v1,3) ----->|        |
            |--- (u_*,3,u_*,1 ; v1,3,v1,1) ------------------------>|
            |<-- (v2,1, v2,2) ----|                      |
            |                      |--- (v2,3, v2,1) -->|
            |<------------ (v3,1, v3,2) ----------------|
            |                      |<--- (v3,2, v3,3) --|
            |                      |                      |
   (zero-sharing chain, in same round)
   Alice picks rho_1; Bob picks rho_2; Charlie picks rho_3 uniform in R
            |---- rho_1 --------->|                      |
            |                      |---- rho_2 -------->|
            |<------------------------- rho_3 ----------|
            |                      |                      |
   After Round 1, Pi holds:
     - RSS pair [x]_Pi for every shared input x
     - own rho_i  AND received rho_{i-1}  (so it can compute alpha_i)
            |                      |                      |
================ Local (no comms) ====================================
            |                      |                      |
   Each Pi computes:
     alpha_i := rho_{i-1} - rho_i           (so sum_i alpha_i = 0)
     z_i^(j) := u_{j,i} v_{j,i} + u_{j,i} v_{j,i+1} + u_{j,i+1} v_{j,i}    for j=1,2,3
     z_i := z_i^(1) + z_i^(2) + z_i^(3)     (additive share of S)
     z'_i := z_i + alpha_i                  (re-randomized share of S)
            |                      |                      |
================ Round 2 - reconstruction at Alice ===================
            |                      |                      |
            |<--- z'_2 -----------|                      |
            |<------------------------- z'_3 -----------|
            |                      |                      |
   Alice:  S = z'_1 + z'_2 + z'_3
            = (z_1 + z_2 + z_3) + (alpha_1 + alpha_2 + alpha_3)
            = u1 v1 + u2 v2 + u3 v3 + 0   = S    <- output
```

## Round / message accounting

| Resource | Count | Notes |
|---|---|---|
| Rounds | **2** | Round 1: input sharing + zero-sharing chain. Round 2: reconstruction. |
| Logical arrows | **8** | Round 1: 6 (every directed pairwise edge). Round 2: 2 ($P_2, P_3 \to P_1$). |
| Ring-element transmissions | **29** | Round 1 = 27 (Alice→Bob: 4 RSS pairs + $\rho_1$ = 9; Alice→Charlie: 4 RSS pairs = 8; Bob→Alice: 2; Bob→Charlie: 2 + $\rho_2$ = 3; Charlie→Alice: 2 + $\rho_3$ = 3; Charlie→Bob: 2). Round 2 = 2. |

Compared with BGW–Shamir on a field (3 rounds, 14 arrows, 20 elements): RSS uses **fewer rounds and fewer arrows but more ring elements per arrow**, because each share is a *pair* and each input is shared with both other parties.

## Why the protocol is correct

**Multiplication identity.** For $x, y \in R$ shared as $\langle x \rangle, \langle y \rangle$:

$$\sum_{i=1}^{3} \big(x_i y_i + x_i y_{i+1} + x_{i+1} y_i\big) \;=\; \sum_{i,j=1}^{3} x_i y_j \;=\; \Big(\sum_i x_i\Big)\Big(\sum_j y_j\Big) \;=\; xy.$$

Each of the 9 cross terms $x_i y_j$ appears exactly once across the three local sums. Pure ring algebra; no field structure used.

**Sum of products.** Linearity:

$$\sum_i z_i^{(j)} = u_j v_j \quad\Rightarrow\quad \sum_i z_i = \sum_i \sum_j z_i^{(j)} = \sum_j u_j v_j = S.$$

**Zero-sharing.** $\alpha_i = \rho_{i-1} - \rho_i$, so $\sum_i \alpha_i = (\rho_3 - \rho_1) + (\rho_1 - \rho_2) + (\rho_2 - \rho_3) = 0$.

**Reconstruction.** $\sum_i z'_i = \sum_i (z_i + \alpha_i) = S + 0 = S$.

## Why the protocol is information-theoretically secure

The core fact: **for $r$ uniform over $R$ and any $a \in R$, the value $a + r$ is uniform over $R$**. This is the OTP property and holds in *any* abelian group, in particular any commutative ring's additive group — **no field structure required**.

### View of corrupted Alice

Alice's incoming messages and their distributions:

| Message | Form | Distribution from Alice's view |
|---|---|---|
| $[v_2]_{Alice} = (r_{v_2,1}, r_{v_2,2})$ | two of Bob's uniform randoms | uniform on $R^2$, independent of $v_2$ |
| $[v_3]_{Alice} = (r_{v_3,1}, r_{v_3,2})$ | two of Charlie's uniform randoms | uniform on $R^2$, independent of $v_3$ |
| $\rho_3$ | Charlie's zero-sharing random | uniform on $R$, independent of all secrets |
| $z'_2 = z_2 + \alpha_2$, where $\alpha_2 = \rho_1 - \rho_2$ | masked by $\alpha_2$ | $\alpha_2$ contains $\rho_2$ which Alice does not have ⇒ uniform; so $z'_2$ uniform |
| $z'_3 = z_3 + \alpha_3$, where $\alpha_3 = \rho_2 - \rho_3$ | masked by $\alpha_3$ | same: $\rho_2$ unknown to Alice ⇒ $\alpha_3$ uniform; $z'_3$ uniform |
| Joint $(z'_2, z'_3)$ | sum-constrained: $z'_2 + z'_3 + z'_1 = S$ | uniform on the affine line $\{(a, b) : a + b = S - z_1\}$ |

Alice's full view can be perfectly simulated from $(u_1, u_2, u_3, v_1, S)$ plus fresh uniform randomness:

1. Sample uniform pair $(\hat r_{v_2,1}, \hat r_{v_2,2})$ as the simulated $[v_2]_{Alice}$.
2. Sample uniform pair $(\hat r_{v_3,1}, \hat r_{v_3,2})$ as the simulated $[v_3]_{Alice}$.
3. Sample uniform $\hat\rho_3$ as the simulated message from Charlie's zero-sharing.
4. Sample uniform $\hat z'_2$ and set $\hat z'_3 := S - \hat z_1 - \hat z'_2$, where $\hat z_1$ is the local computation Alice would perform on her simulated inputs.

Distribution of the simulated view is identical to the real view. **Statistical distance zero.** This is the standard simulation-based IT-security proof; no asymptotic argument or computational assumption.

### View of corrupted Bob (or Charlie)

Bob's incoming messages:

| Message | Distribution from Bob's view |
|---|---|
| $[u_j]_{Bob} = (u_{j,2}, u_{j,3})$ for $j = 1,2,3$ | uniform on $R^2$, independent of $u_j$ |
| $[v_1]_{Bob} = (v_{1,2}, v_{1,3})$ | uniform, independent of $v_1$ |
| $[v_3]_{Bob} = (v_{3,2}, v_{3,3})$ | uniform, independent of $v_3$ |
| $\rho_1$ from Alice | uniform |

Bob never sees any $z'_i$ in this protocol (reconstruction is at Alice only). His view is uniform conditioned on his own input $v_2$. Simulator: sample everything uniform from $v_2$ alone. Charlie symmetric.

### Why this is genuinely IT, not just computational

There is **no encryption** anywhere in the protocol. Every hiding step is an additive mask by uniform randomness over $R$'s additive group. An unbounded adversary cannot do better than guessing — there is no key to brute-force, no hardness assumption to break, no Lagrange division to invert. Privacy follows from the OTP property of additive shares, valid in any commutative ring.

### Note on $\mathbb{Z}/2^k$ (no 2-torsion bug)

A natural worry: $z'_2 - z'_3$ contains $\alpha_2 - \alpha_3 = \rho_1 - 2\rho_2 + \rho_3$, and over $\mathbb{Z}/2^k$ multiplication by $2$ is a zero divisor, so $2\rho_2$ is uniform only on the even residues. Doesn't this leak the LSB of $z_2 - z_3$ to Alice?

**It doesn't, because Alice never gets two independent degrees of freedom in $(z'_2, z'_3)$.** The reconstruction identity $z'_1 + z'_2 + z'_3 = S$ pins $z'_2 + z'_3 = S - z'_1$ to a value that is part of Alice's intended output. So $(z'_2, z'_3)$ lives on a 1-dimensional affine line. The single free coordinate — say $z'_2$ — is masked by $-\rho_2$ alone (a single uniform draw, not $-2\rho_2$), and one uniform draw is sufficient to make $z'_2$ uniform over $R$ regardless of ring structure. The factor of 2 in the difference is redundant; the protocol is IT-secure over $\mathbb{Z}/2^k$, $\mathbb{F}_p$, and any other commutative ring.

## Comparison with prior protocols

| Property | DSDP (Paillier) | BGW–Shamir (field) | **RSS (this note)** |
|---|---|---|---|
| Rounds | 4 | 3 | **2** |
| Logical messages | 5 | 14 | 8 |
| Ring elements transmitted | ~5 ciphertexts | 20 field elements | 29 ring elements |
| Algebraic structure | $\mathbb{Z}/(pq)$ + Paillier hardness | field, or ring with eval-points-as-units | **any commutative ring** |
| Security | Computational (DCR) | IT-secure (perfect, $t=1$ semi-honest) | **IT-secure** (perfect, $t=1$ semi-honest) |
| Works over $\mathbb{Z}/2^k$? | n/a | ❌ | ✅ |

---

# Formalization plan: hypotheses & lemmas needed

**Reference:** mirrors the structure of `20260428-bgw-shamir-formalization-hypotheses.md` and the existing `dsdp_security.v`. Aim: a Coq/Rocq development that proves the same shape of theorems — `H(V_2 \mid \text{AliceView}) = \log n$, `BobView _|_ V_1`, etc. — with the absolute minimum of axioms and no field-specific machinery.

## High-level structural change vs. Shamir-over-field

| Aspect | Shamir BGW (field) | **RSS (this protocol)** |
|---|---|---|
| Field/Ring | $\mathbb{F}_p$ ($p > 3$ prime) | arbitrary commutative ring of size $n \geq 2$ |
| Hiding primitive | $f_s(x) = s + r_s \cdot x$, single share | $(s_1, s_2, s_3 = s - s_1 - s_2)$, pair held |
| Lagrange interpolation | required (`lagrange_3pt_deg2`) | **eliminated** |
| Degree-reduction lemma | required (`degree_reduction_correct`) | **eliminated** |
| Zero-sharing | not used | required (`zero_sharing_correct`, new) |
| Multiplication identity | local product gives degree-2; needs reduce | local product gives 9 cross-terms summing to $xy$; no degree concept |

## Setup section (Coq sketch)

| Item | Shamir signature | RSS signature | Why |
|---|---|---|---|
| Ring params | `Variable p_minus_4 : nat; Hypothesis prime_p; Hypothesis p_gt3` | `Variable n_minus_2 : nat; Local Notation n := n_minus_2.+2.` | RSS only needs $n \geq 2$; no primality, no eval-point conditions. |
| Message type | `'Z_p` | `'Z_n` | $\mathbb{Z}/n\mathbb{Z}$ for any $n$. |
| Eval points | `x_A := 1, x_B := 2, x_C := 3 : msg` | (n/a — no evaluation points in RSS) | RSS uses index $i \in \{1,2,3\}$ to label *which piece* a party holds, not as a ring element. |

## Random variables

| Item | Shamir BGW | RSS | Why |
|---|---|---|---|
| Inputs | `U1, U2, U3, V1, V2, V3` | same | identical functionality |
| Sharing randomness | 6 (one per input) | **12** (two per input: each input split with two random pieces) | RSS uses additive 3-piece sharing, two of which are random |
| Re-share / zero-share randomness | 3 ($s_A, s_B, s_C$ for degree reduction) | **3** ($\rho_1, \rho_2, \rho_3$ for zero-sharing chain) | analogous role, different mechanism |
| Total auxiliary randomness | **9** | **15** | RSS pays for ring-genericity in mask count |

## Hypotheses to keep (with exact RSS analogues)

| Shamir-BGW hypothesis | RSS analogue | Purpose |
|---|---|---|
| `pV1_unif`, `pV2_unif`, `pV3_unif` | same (input uniformity) | gives $H(V_i) = \log n$ |
| `VarRV_uniform : `\``p_ [% V2, V3] = fdist_uniform` | same | joint uniformity of secrets to be protected |
| `VarRV_indep_inputs : P |= [% V1, U1, U2, U3] _|_ [% V2, V3]` | same | input independence (modeling assumption) |

## Hypotheses to drop (relative to DSDP)

| DSDP / Shamir hypothesis | Why droppable for RSS |
|---|---|
| `E_enc_unif`, `E_enc_inde` (DSDP encryption axioms) | No encryption in RSS; replaced by *provable* `RSS_pair_unif` |
| `prime_p`, `prime_q`, `coprime_pq` (DSDP) | RSS works over any commutative ring |
| `U3_coprime_m`, `U3_pos`, `U3_lt_minpq` (DSDP CRT machinery) | RSS doesn't depend on multiplicative invertibility of any input |
| `lagrange_3pt_deg2`, `degree_reduction_correct` (Shamir) | No Lagrange in RSS |
| `p > 3` field-size constraint (Shamir) | RSS only needs $n \geq 2$ |

## New lemmas needed (RSS-side infrastructure)

These would live in a new file, e.g. `rss.v`, replacing both DSDP's encryption module and Shamir's polynomial module.

| Lemma | Signature (sketch) | What it shows | Why we need it |
|---|---|---|---|
| `additive_mask_unif` | `forall (s r : {RV P -> msg}), P |= r _|_ s -> `\``p_ r = fdist_uniform card_msg -> `\``p_ (s \+ r) = fdist_uniform card_msg` | $s + r$ is uniform when $r$ is uniform and independent of $s$ | The single OTP fact RSS rests on. **Provable** from `lemma_3_5'` already in `smc_proba.v`. |
| `additive_mask_indep_secret` | `forall s r, P |= r _|_ s -> `\``p_ r = fdist_uniform -> P |= (s \+ r) _|_ s` | $s + r$ alone is independent of $s$ | direct consequence of `additive_mask_unif`; replaces both `E_enc_inde` and Shamir's `share_indep_secret` |
| `RSS_pair_unif` | `forall (s r1 r2 : {RV P -> msg}), [r1, r2 indep, indep of s, both uniform] -> let s3 := s \- r1 \- r2 in `\``p_ [%r2, s3] = fdist_uniform card_msg_pair /\ `\``p_ [%s3, r1] = fdist_uniform card_msg_pair` | Each of the three pairs $(s_1,s_2), (s_2,s_3), (s_3,s_1)$ is uniform on $R^2$ | The IT-privacy guarantee for a single party's RSS pair. **Provable** by elementary linear-algebra-over-rings reasoning. |
| `RSS_pair_indep_secret` | `forall s r1 r2, ... -> P |= [% appropriate_pair] _|_ s` | Each held pair is independent of the secret | The sharper form needed for the simulator argument |
| `mult_cross_terms_sum` | `forall (x y : 'I_3 -> msg), let z i := x i * y i + x i * y (cyclic_succ i) + x (cyclic_succ i) * y i in `\``\sum_i z i = (`\``\sum_i x i) * (`\``\sum_i y i)` | The 9-term identity $\sum_i (x_iy_i + x_iy_{i+1} + x_{i+1}y_i) = xy$ | Multiplication correctness; pure ring algebra |
| `zero_sharing_sum` | `forall (rho : 'I_3 -> msg), let alpha i := rho (cyclic_pred i) \- rho i in `\``\sum_i alpha i = 0` | $\alpha_i := \rho_{i-1} - \rho_i$ telescopes to 0 | Zero-sharing correctness |
| `zero_sharing_alpha_unif` | `forall (rho1 rho2 rho3 : {RV P -> msg}), [pairwise indep, each uniform] -> let alpha2 := rho1 \- rho2 in P |= alpha2 _|_ [% rho1, rho3] /\ `\``p_ alpha2 = fdist_uniform card_msg` (and symmetric for $\alpha_3$) | Each $\alpha_i$ that the adversary doesn't compute is uniform conditional on the keys the adversary holds | Privacy of the re-randomization. (Replaces the vague `zero_sharing_indep` from earlier draft.) |
| `z'_uniform_given_alice_view` | `forall (z2 alpha2 : {RV P -> msg}), P |= alpha2 _|_ [% Alice_other_view, z2] -> `\``p_ alpha2 = fdist_uniform card_msg -> `\``p_ ((z2 \+ alpha2) \| Alice_other_view) = fdist_uniform card_msg` | $z'_2 = z_2 + \alpha_2$ is uniform conditional on Alice's other view, by direct application of `lemma_3_5'` with $X = z_2$, $Z = \alpha_2$ | **The cornerstone IT-security step.** Replaces the per-message uniformity claim in the simulator argument. |
| `view_simulator_alice` | (large statement) `AliceView` can be sampled from $(u_*, v_1, S)$ + fresh uniform randomness with statistical distance 0 | Composite simulator-based IT-security | The headline theorem in simulation-based form |

## Modeling hypotheses still needed

These are the standard MPC modeling assumptions, parametric in the RV count.

| Hypothesis | Signature | Purpose |
|---|---|---|
| `pr_*_unif` (×15) | `\``p_ r = fdist_uniform card_msg` for each of the 12 sharing randoms + 3 zero-sharing randoms | Each masking value is uniformly drawn |
| `randomness_mut_indep` | `P |= [% all 15 randoms] _|_ unit_RV P` (encoded as pairwise / graphoid-style mutual independence) | Honest parties draw their masks independently |
| `randomness_indep_inputs` | `P |= [% all 15 randoms] _|_ [% U1,U2,U3,V1,V2,V3]` | Mask draws are independent of inputs (standard) |

In DSDP these correspond to `R2_indep_VU2_V3`, `R3_indep_VU3_V1`, etc. — same flavor, more of them.

## View definitions

```coq
(* RSS-pair shorthand: (s_i, s_{i+1}) where s_3 := s - r1 - r2 *)
Definition rss_pair_alice (s r1 r2 : {RV P -> msg}) : {RV P -> msg * msg} :=
  [% r1, r2].   (* (s_1, s_2) *)
Definition rss_pair_bob   (s r1 r2 : {RV P -> msg}) : {RV P -> msg * msg} :=
  [% r2, s \- r1 \- r2].   (* (s_2, s_3) *)
Definition rss_pair_charlie (s r1 r2 : {RV P -> msg}) : {RV P -> msg * msg} :=
  [% s \- r1 \- r2, r1].   (* (s_3, s_1) *)

(* Alice's view *)
Let AliceView : {RV P -> _} :=
  [% V1, U1, U2, U3,
     (* Round 1 — Alice's pairs of every shared input (her own + received) *)
     rss_pair_alice U1 r_u1_1 r_u1_2,
     rss_pair_alice U2 r_u2_1 r_u2_2,
     rss_pair_alice U3 r_u3_1 r_u3_2,
     rss_pair_alice V1 r_v1_1 r_v1_2,
     rss_pair_alice V2 r_v2_1 r_v2_2,    (* received from Bob *)
     rss_pair_alice V3 r_v3_1 r_v3_2,    (* received from Charlie *)
     (* Round 1 — zero-sharing: own rho_1 + received rho_3 *)
     rho_1, rho_3,
     (* Round 2 — re-randomized partial sums from Bob and Charlie *)
     z'_2, z'_3,
     S].

(* Bob's and Charlie's views: symmetric, no z' messages *)
```

**No encryption keys, no encrypted blobs**: that entire dimension of complexity in `dsdp_security.v` is gone.

## Main theorems (parallel to DSDP / Shamir BGW)

| DSDP / Shamir theorem | RSS analogue |
|---|---|
| `dsdp_constraint_centropy_eqlogm` / `bgw_constraint_centropy_eqlogp` | `rss_constraint_centropy_eqlogn : `\``H([% V2, V3] \| [% V1, U1, U2, U3, S]) = log (n%:R : R)` |
| `dsdp_entropic_security` / `bgw_alice_privacy_V2` | `rss_alice_privacy_V2 : `\``H(V2 \| AliceView) = log n /\ ... > 0` |
| `bob_privacy_V1`, `bob_privacy_V3` | `rss_bob_privacy_V1`, `rss_bob_privacy_V3` |
| `charlie_privacy_V1`, `charlie_privacy_V2` | `rss_charlie_privacy_V1`, `rss_charlie_privacy_V2` |
| `US_compromised_leaks_V2` (DSDP malicious case) | not needed in semi-honest; could be added if desired |

## What this saves vs. DSDP

| Saving | Mechanism |
|---|---|
| Eliminate `E_enc_inde` axiom (the unsound one) | Replaced by *provable* `additive_mask_indep_secret` |
| Eliminate `E_enc_unif` axiom | Replaced by *provable* `additive_mask_unif` |
| Eliminate composite-modulus apparatus (`coprime_pq`, `U3_coprime_m`, `U3_pos`, `U3_lt_minpq`, CRT in `linear_fiber_zpq.v`) | RSS works over any commutative ring; no fiber decomposition |
| Eliminate `constraint_holds` hypothesis | $S$ is defined by the protocol |
| **Additionally vs. Shamir**: eliminate `lagrange_3pt_deg2`, `degree_reduction_correct`, $p > 3$ constraint | RSS has no Lagrange and no degree concept |

## What this costs vs. Shamir

| Cost | Mechanism |
|---|---|
| 15 mask hypotheses instead of 9 | RSS shares each input with 2 random pieces (vs. 1 polynomial coefficient) |
| Larger view per party (pairs, not single shares) | RSS holds 2 pieces per shared value |
| New zero-sharing infrastructure | Replaces Shamir's degree-reduction step |

## Summary

| | Axioms required | Field/ring constraint | Eliminates Lagrange? |
|---|---|---|---|
| DSDP `dsdp_security.v` (current) | 2 unsound encryption axioms + composite-modulus structure | $\mathbb{Z}/(pq)$ with $p, q$ prime | n/a |
| Shamir-BGW formalization (proposed in companion note) | 0 encryption axioms; field structure; Lagrange machinery | $\mathbb{F}_p$ or $\mathbb{Z}/(pq)$ with $p, q \geq 3$ | no |
| **RSS formalization (this note)** | **0 encryption axioms; no Lagrange machinery; only OTP-additive lemma** | **any commutative ring** | **yes** |

The headline win: **RSS over a generic ring eliminates *both* the encryption axioms in DSDP *and* the Lagrange-interpolation machinery in Shamir.** The only proof-relevant primitive is the OTP property of additive masks, which is already captured by `lemma_3_5'` in `smc_proba.v`. The cost is more random variables to track, but each is handled by uniform application of the same elementary lemma.

This makes RSS the leanest target for a formal IT-security proof of 3-party scalar product over arbitrary rings — strictly better than both DSDP's current axiomatic approach and the Shamir-over-field alternative.
