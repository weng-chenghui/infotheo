# 3-Party IT-Secure Scalar Product (BGW with Shamir, $(k,n) = (2,3)$ / $t=1$)

**Context:** companion to `20260427-its-homomorphic-encryption-survey.md`. Establishes that the same functionality DSDP computes — the 3-party scalar product $S = u_1 v_1 + u_2 v_2 + u_3 v_3$ with privacy of $v_2, v_3$ from Alice — *is* achievable with information-theoretic security, but at the cost of a different message graph than DSDP's 5-message Paillier-based chain.

## Setup

- Field $\mathbb{F}_p$ for prime $p > 3$.
- 3 parties: Alice (P1), Bob (P2), Charlie (P3).
- Inputs: Alice has $u_1, u_2, u_3, v_1$; Bob has $v_2$; Charlie has $v_3$.
- Goal: Alice learns $S = u_1 v_1 + u_2 v_2 + u_3 v_3$, no party learns anything beyond their own input and the protocol output (Alice's output is $S$; Bob's and Charlie's output is $\bot$).
- Threat model: semi-honest, at most one corrupted party.
- Channels: pairwise IT-secure authenticated private channels (standard MPC assumption).

## Convention note: $(k, n)$ vs $t$

Two conventions describe the same scheme:

| Convention | Parameters | Meaning |
|---|---|---|
| Shamir's original | $(k, n) = (2, 3)$ | $n$ = total shares, $k$ = minimum to reconstruct |
| MPC literature | $n$ parties, $t = 1$ | $n$ = total, $t$ = max corruptions tolerated |

Translation: $k = t + 1$. Both say *"any 1 share is uniformly random; any 2 shares reconstruct."*

For honest-majority MPC with multiplication: $n \geq 2t + 1 = 2k - 1$. For us: $n = 3$, $t = 1$, $k = 2$ — tight.

## Primitive

Shamir secret sharing with degree-1 polynomials over $\mathbb{F}_p$. Evaluation points: $x_A = 1, x_B = 2, x_C = 3$.

To share secret $s$: pick fresh uniform $r_s \in \mathbb{F}_p$, set $f_s(x) = s + r_s \cdot x$. Party $P$'s share is $[s]_P = f_s(x_P)$.

## Notation

| Symbol | Meaning |
|---|---|
| $s$ | a secret (e.g., $v_2$) |
| $r_s$ | fresh uniform random element of $\mathbb{F}_p$, drawn by the sharer; kept secret |
| $f_s(x) = s + r_s \cdot x$ | sharing polynomial |
| $x_P$ | $P$'s evaluation point: $x_A = 1, x_B = 2, x_C = 3$ |
| $[s]_P$ | $:= f_s(x_P) = s + r_s \cdot x_P$ — one field element, uniform in $\mathbb{F}_p$ |
| $T_P$ | $P$'s degree-2 share of $S$ after local product |
| $g_P(x) = T_P + s_P \cdot x$ | fresh degree-1 polynomial $P$ uses to re-share $T_P$ |
| $\lambda_A, \lambda_B, \lambda_C = 3, -3, 1$ | Lagrange coefficients for interpolation to $x = 0$ from $\{1, 2, 3\}$ |
| $\mu_A, \mu_B, \mu_C = 3, -3, 1$ | same coefficients, used at final reconstruction |

In particular, $[v_2]_A = v_2 + r_{v_2}$ is **one masked field element**, not the secret $v_2$.

## Protocol

```
       Alice (P1)              Bob (P2)             Charlie (P3)
        ==========             ========             ============
inputs: u1, u2, u3, v1            v2                     v3
            |                      |                      |
========== Round 1 - input sharing =============================
            |                      |                      |
            |-- [u1,u2,u3,v1]_B -->|                      |
            |-- [u1,u2,u3,v1]_C ------------------------->|
            |<----- [v2]_A --------|                      |
            |                      |---- [v2]_C --------->|
            |<-------------------------- [v3]_A ----------|
            |                      |<---- [v3]_B ---------|
            |                      |                      |
   each P now holds  [u1]_P, [u2]_P, [u3]_P, [v1]_P, [v2]_P, [v3]_P
            |                      |                      |
========== Round 2 - local product + degree reduction ==========
            |                      |                      |
   each P computes locally (no comms):
       T_P  =  sum_i [u_i]_P * [v_i]_P    <- degree-2 share of S
            |                      |                      |
   each P fresh-shares its T_P via a degree-1 poly g_P(x) = T_P + s_P * x:
            |                      |                      |
            |---- g_A(2) --------->|                      |
            |---- g_A(3) ------------------------------->|
            |<---- g_B(1) ---------|                      |
            |                      |---- g_B(3) -------->|
            |<------------------------------ g_C(1) ------|
            |                      |<---- g_C(2) ---------|
            |                      |                      |
   each P computes locally:
       [S]_P = lambda_A * g_A(x_P) + lambda_B * g_B(x_P) + lambda_C * g_C(x_P)
              <- fresh degree-1 share of S, lambda_i are Lagrange coeffs at 0
            |                      |                      |
========== Round 3 - reconstruction at Alice ===================
            |                      |                      |
            |<----- [S]_B ---------|                      |
            |<-------------------------- [S]_C -----------|
            |                      |                      |
   Alice:  S = mu_A * [S]_A + mu_B * [S]_B + mu_C * [S]_C
             = u1*v1 + u2*v2 + u3*v3   <- output
```

## Lagrange coefficients

For interpolation to $x = 0$ from points $\{1, 2, 3\}$:

$$\lambda_A = \frac{(0-2)(0-3)}{(1-2)(1-3)} = 3, \quad \lambda_B = \frac{(0-1)(0-3)}{(2-1)(2-3)} = -3, \quad \lambda_C = \frac{(0-1)(0-2)}{(3-1)(3-2)} = 1.$$

Same coefficients $\mu_A, \mu_B, \mu_C = 3, -3, 1$ for the final reconstruction (same point set). Requires $p > 3$ so $2, 3$ are non-zero and invertible.

## Why the protocol is correct

**Round 2 degree reduction.** Define $f(x) = \sum_i f_{u_i}(x) \cdot f_{v_i}(x)$, a polynomial of degree $\leq 2$ with $f(0) = S$. Each party $P$ holds $T_P = f(x_P)$. By Lagrange interpolation from points $\{1, 2, 3\}$:

$$f(0) = \lambda_A T_A + \lambda_B T_B + \lambda_C T_C = S.$$

Define $h(x) = \lambda_A g_A(x) + \lambda_B g_B(x) + \lambda_C g_C(x)$. Each $g_P$ is degree 1, so $h$ is degree $\leq 1$. Evaluating at 0:

$$h(0) = \lambda_A g_A(0) + \lambda_B g_B(0) + \lambda_C g_C(0) = \lambda_A T_A + \lambda_B T_B + \lambda_C T_C = S.$$

So $h$ is a valid degree-1 sharing of $S$, and $[S]_P = h(x_P)$ for each $P$.

**Round 3 reconstruction.** Alice has 3 evaluations of degree-1 $h$, interpolates to $h(0) = S$. Output correct.

## Why the protocol is information-theoretically secure

The core fact: for a degree-1 polynomial $f(x) = s + r \cdot x$ with $r$ uniform in $\mathbb{F}_p$, **any single evaluation $f(x_P)$ at a non-zero point $x_P$ is uniformly distributed in $\mathbb{F}_p$, independent of $s$.** This is the Shamir IT-security guarantee — no computational assumption involved.

### View of corrupted Alice

Alice's incoming messages and what they look like:

| Message | Form | Distribution |
|---|---|---|
| $[v_2]_A = v_2 + r_{v_2}$ | one share of $v_2$ | uniform on $\mathbb{F}_p$ |
| $[v_3]_A = v_3 + r_{v_3}$ | one share of $v_3$ | uniform on $\mathbb{F}_p$ |
| $g_B(1) = T_B + s_B$ | one share of Bob's $T_B$ | uniform via fresh $s_B$ |
| $g_C(1) = T_C + s_C$ | one share of Charlie's $T_C$ | uniform via fresh $s_C$ |
| $[S]_B = h(2)$ | one share of $S$ | jointly with $[S]_A, [S]_C$ determines $S$ |
| $[S]_C = h(3)$ | one share of $S$ | jointly with $[S]_A, [S]_B$ determines $S$ |

The first four are independent uniform field elements — they carry zero information about $v_2, v_3, T_B, T_C$ individually. The last two are determined by $S$ together with Alice's own $[S]_A$, so they carry exactly $S$ worth of information beyond Alice's own state.

Therefore Alice's full view can be perfectly simulated from $(u_1, u_2, u_3, v_1, S)$ plus fresh uniform randomness — the standard real/ideal indistinguishability for IT-security, with **statistical distance zero**.

### View of corrupted Bob (or Charlie)

Bob's incoming messages:

| Message | Distribution |
|---|---|
| $[u_1]_B, [u_2]_B, [u_3]_B, [v_1]_B$ | each a single Shamir share, uniform |
| $[v_3]_B$ | uniform |
| $g_A(2)$ | uniform via fresh $s_A$ |
| $g_C(2)$ | uniform via fresh $s_C$ |

Bob never receives any $[S]_P$, so reconstruction-side information never reaches him. His view is uniform random conditioned on his own input $v_2$. Simulator can produce his view from $v_2$ alone. Charlie symmetric.

### Why this is genuinely IT, not just computational

There is no encryption anywhere in the protocol. Every "hiding" is via Shamir share masking: a single share at $x_P \neq 0$ is uniformly distributed over $\mathbb{F}_p$ as $r_s$ ranges uniformly over $\mathbb{F}_p$. An unbounded adversary cannot do better than guessing — there is no key to brute-force, no hardness assumption to break. Privacy is from Shannon-style randomness, not from computational hardness.

## Round and message accounting

| Resource | Count | Notes |
|---|---|---|
| Rounds | **3** | Round 1: input share. Round 2: reshare for degree reduction. Round 3: reconstruction. |
| Logical messages (arrows) | **14** | Round 1: 6 arrows. Round 2: 6 arrows. Round 3: 2 arrows. |
| Field-element transmissions | **20** | Round 1: 12 (Alice sends 4 shares × 2 destinations + Bob/Charlie 1 each × 2). Round 2: 6. Round 3: 2. |

Counting convention matters. DSDP's "5 messages" follows the logical-arrow convention (e.g., $\alpha_2, \alpha_3$ travel together as one $A \to B$ arrow). Apples-to-apples comparison gives BGW = 14 arrows vs DSDP = 5 arrows.

## Comparison with DSDP

| Property | DSDP (Paillier) | BGW–Shamir (this protocol) |
|---|---|---|
| Rounds | 4 | 3 |
| Logical messages | 5 | 14 |
| Edges used | $A\!\leftrightarrow\!B,\ A\!\leftrightarrow\!C,\ B\!\to\!C$ | complete graph each round |
| Security | Computational (DCR) | **Information-theoretic** (perfect, $t=1$ semi-honest) |
| Setup | Each party has a PKE keypair | Pairwise IT-secure channels |
| Adversary computing power | Polynomial-time | Unbounded |

## Caveats

1. **Semi-honest only.** Against an active (malicious) adversary, $n = 3, t = 1$ does *not* extend — robust reconstruction needs $n \geq 3t + 1 = 4$, and verifiable secret sharing must be layered on top.

2. **$n = 3, t = 1$ is tight** for honest-majority multiplication: $n = 2t + 1$ with equality. No room for additional faulty parties; if even one party drops out, degree-2 reconstruction fails.

3. **Channel assumption.** Pairwise IT-secure channels are *assumed*, not constructed within the protocol. In practice they require either physical secrecy or pre-shared one-time-pad keys; QKD also suffices. Without IT-secure channels, the overall protocol's security degrades to whatever the channel guarantees.

4. **Field size.** $p > 3$ is required for the Lagrange coefficients to be invertible (i.e., for points $1, 2, 3$ to be distinct and non-zero). Practical implementations use a large prime to avoid statistical leakage from small field collisions.

## Take-away

The Paillier-based DSDP and this BGW–Shamir protocol compute the same function but live in different design points:

- **DSDP optimizes message count** (5 arrows, asymmetric chain) at the cost of relying on a public-key hardness assumption (DCR for Paillier).
- **BGW–Shamir optimizes the security model** (information-theoretic, no computational assumptions) at the cost of more messages and a complete-graph communication pattern in each round.

The structural reason DSDP is so lean is that Alice can *unilaterally* perform homomorphic scalar multiplication $c_2^{u_2} \cdot E_{\mathrm{pubB}}(r_2)$ using only Bob's *public* key. No IT-secure primitive offers that capability — public-key encryption is fundamentally not IT-secure (any unbounded adversary holding the public key can decrypt). So the IT-secure version pays for cross-party multiplications with extra rounds and pairwise edges, which is exactly the cost difference observed.
