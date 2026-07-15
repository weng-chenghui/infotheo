# Why PKE cannot achieve information-theoretic security

Date: 2026-04-30

## The core impossibility argument

### 1. Diffie–Hellman (1976) — the original observation
In *New Directions in Cryptography*, Diffie and Hellman pointed out the impossibility in the very paper that introduced PKE:

> "We note that neither public key cryptosystems nor one-way authentication systems can be unconditionally secure because the public information always determines the secret information uniquely among the members of a finite set. With unlimited computation, the problem could therefore be solved by a straightforward search."

This is the brute-force argument: the public key `pk` determines the secret key `sk` (and hence the plaintext) uniquely; an unbounded adversary just enumerates.

### 2. Maurer (CRYPTO '99) — *Information-Theoretic Cryptography*
Maurer proves a stronger statement using conditional entropy / mutual information bounds: if Alice and Bob share no initial secret and communicate only over a public channel accessible to Eve, they cannot generate an information-theoretically secure shared key. As a corollary: **no unconditionally-secure public-key cryptosystem or public-key distribution protocol can exist.**

### 3. Panny (2019), "Guess what?! On the impossibility of unconditionally secure public-key encryption" (eprint 2019/1228)
Panny gives a self-contained, modern proof that closes the "decryption-error gap" left open by the simple Diffie–Hellman brute force (which assumes deterministic, error-free decryption). The argument:

- **Lemma 1:** For any (possibly randomized) distinguisher `O` on ciphertexts of `m ∈ {0,1}`, `Adv(O) ≤ Σ_c max{0, p₁(c) − p₀(c)}` where `pₘ(c) = Pr[Enc_pk(m) = c]`.
- **Lemma 2:** The adversary `A_pk` that, given only `pk`, computes `p₀(c)` and `p₁(c)` by exhaustively iterating over the randomness of `Enc_pk` and outputs the maximum-likelihood guess, **achieves the upper bound of Lemma 1**. Therefore `Dec_sk` cannot do strictly better than `A_pk`.

Conclusion: if honest decryption succeeds with probability > 1/2, then the unbounded MLE adversary using only `pk` also succeeds with probability > 1/2. The only way to make `A_pk` useless is to make `Dec_sk` equally useless — defeating communication itself (Shannon 1948).

### 4. Shannon (1949) — the symmetric-key analogue
The classic *Communication Theory of Secrecy Systems* result `H(K) ≥ H(M)` (Shannon's bound) is the symmetric-key counterpart: perfect secrecy requires keys at least as long as the message. Dodis revisits this in *Shannon Impossibility, Revisited* (ICITS 2012). This isn't a PKE-specific impossibility but is the foundational information-theoretic constraint that PKE inherits and cannot escape without computational assumptions.

## Practical takeaway for RSSDP / IT-MPC work

The Panny / Maurer / Diffie–Hellman line says: any scheme where one party broadcasts a public key and the other encrypts to it over a public channel is **provably** computationally secure at best. This is one of the standard arguments for why information-theoretic MPC (BGW, RSS-based DSDP) requires either pre-shared correlated randomness, private channels, or honest-majority assumptions — you cannot bootstrap IT security purely from public-channel public keys.

## Sources

- Panny, "Guess what?! On the impossibility of unconditionally secure public-key encryption" (eprint 2019/1228) — <https://eprint.iacr.org/2019/1228.pdf>
- Diffie & Hellman, "New Directions in Cryptography," IEEE TIT 1976 — <https://ee.stanford.edu/~hellman/publications/24.pdf>
- Maurer, "Information-Theoretic Cryptography," CRYPTO '99 — <https://link.springer.com/content/pdf/10.1007/3-540-48405-1_4.pdf>
- Dodis, "Shannon Impossibility, Revisited," ICITS 2012 — <https://cs.nyu.edu/~dodis/ps/one-time-pad.pdf>
- Information-theoretic security — Wikipedia — <https://en.wikipedia.org/wiki/Information-theoretic_security>
- Cornell CS687 Lecture 2: Information-Theoretic Security — <https://www.cs.cornell.edu/courses/cs687/2006fa/lectures/lecture2.pdf>
