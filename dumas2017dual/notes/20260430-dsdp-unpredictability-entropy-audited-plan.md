# Audited plan: Reformulate DSDP security via unpredictability entropy

Date: 2026-04-30
Status: Audited (verdict: Sound-with-fixes by information-theory expert subagent), pending review and decision
Source: `/Users/cheng-huiweng/.claude/plans/one-correction-bob-owns-eventual-bonbon.md`

## TL;DR

No PKE scheme can be information-theoretically secure, which is why E_enc_inde has concrete counterexamples in-model. Given only the public key, an unbounded adversary can compute the likelihoods `Pr[Enc(pk, m) = c]` for any candidate message m and observed ciphertext c by exhaustively iterating over the encryption randomness, and outputting the maximum-likelihood guess matches or exceeds the success probability of honest decryption [1]. As long as honest decryption succeeds with probability greater than 1/2, this attack does too, so an encrypted RV cannot be Shannon-independent of its plaintext.

Replace E_enc_inde with the standard IND-CPA hypothesis [2], and from it derive a ciphertext-replacement lemma. Then prove the security theorem by chaining the lemma three times, swapping each Enc(secret) in the corrupted-Alice view for Enc(0) at cost eps_cpa per swap.

Standard IND-CPA security for a public-key encryption scheme is defined by the following game. The challenger sends a public key to the adversary, who submits two equal-length messages m_0 and m_1. The challenger picks a random bit b, returns the ciphertext Enc(pk, m_b), and the adversary outputs a guess b'. The scheme is IND-CPA secure if for every efficient adversary the probability of guessing b correctly is at most 1/2 plus a negligible function in the security parameter.

The ciphertext-replacement lemma states that for any joint distribution over a view V and a message random variable M, the pair (V, Enc(pk, M)) is eps_cpa-indistinguishable [3] from (V, Enc(pk, 0)) against efficient adversaries. This form is what the protocol needs because the encrypted value is correlated with the view rather than a message the reduction can sample independently. The lemma follows from standard IND-CPA via a one-step reduction: any distinguisher between the two distributions can be turned into an IND-CPA adversary by internally simulating the protocol to generate (V, M) and submitting M and 0 as the two challenge messages.

After the swap each ciphertext encrypts the constant 0 instead of a secret-dependent value, so it is a deterministic function of pk and the fresh per-call encryption randomness r alone. Since pk is fixed at protocol setup and r is sampled independently of all secret inputs, the post-swap encryption RVs are independent of V2 and V3 in the strict Shannon sense.

The eps_cpa cost is not a defect in this independence. After the swap the encryption RVs really are perfectly Shannon-independent of V2 and V3, because the encrypted message is a constant. What carries the eps_cpa is the transition between two probability distributions, the real one where encryptions carry secrets and the hybrid one where they carry zero. IND-CPA is exactly the assumption that lets us treat those two as interchangeable up to that cost, and `eps_cpa` is paid once per ciphertext at the boundary. Inside the hybrid distribution the rest of the proof is fully Shannon-flavored, feeding the existing lemmas with honest independence and no further computational price.

The lemmas in dsdp_entropy.v that currently consume E_enc_inde, such as alice_view_to_cond, take exactly this encryption-independence as their hypothesis. On the hybrid view they apply with honest input instead of the unsound axiom. The remaining lemmas in dsdp_entropy.v make no reference to encryption RVs and are unaffected.

The path to the Hunp conclusion goes through uniformity directly, bypassing Shannon entropy. `Pr_dsdp_sol_uniform` at line 237 of `dsdp_entropy.v` already proves that the conditional distribution of V2 given the non-encrypted part of the view is uniform on m elements. The new lemma `Hmin_cond_of_uniform` formalizes the uniform-to-Hmin step: a uniform conditional distribution on m elements gives `Hmin_cond X Y = log m`. Then `Hunp ≥ Hmin` holds by definition since a bounded predictor never outperforms an unbounded one, so the chain runs from `Pr_dsdp_sol_uniform` to the Hunp bound in two short steps. Shannon `dsdp_centropy_uniform` plays no role on the critical path.

The final theorems become Hunp(V2 | AliceView) ≥ log m − 2·eps_cpa and the corresponding statements for Bob and Charlie, replacing Shannon equality with conditional unpredictability entropy [4] bounds. Conditional unpredictability entropy, written Hunp, is the negative log of the maximum probability [5] that any efficient adversary in a fixed class C can guess the secret given the view. So the bound directly says no such adversary guesses V2 better than 1/m + 2·eps_cpa. (Bob and Charlie cases incur 1·eps_cpa and 0·eps_cpa respectively per the path-(b) decision recorded in the closed-form section, with Charlie's two theorems holding unconditionally.)

### TL;DR references

[1] Panny, "Guess what?! On the impossibility of unconditionally secure public-key encryption", IACR ePrint 2019/1228, 2019. Closes the decryption-error gap left by the original Diffie–Hellman 1976 brute-force argument by showing that even for randomized encryption with non-zero decryption error, the maximum-likelihood adversary using only the public key matches or exceeds honest decryption's success probability.

[2] Shoup, "Sequences of Games: A Tool for Taming Complexity in Security Proofs", IACR ePrint 2004/332, 2004. The canonical reference for the game-based hybrid technique. Models security proofs as sequences of indistinguishable games connected by IND-CPA-style transitions, exactly the structure used here, with no appeal to the simulation paradigm. The IND-CPA definition itself goes back to Goldwasser–Micali, "Probabilistic Encryption", J. Comput. Syst. Sci. 1984, and is treated in any modern textbook such as Katz–Lindell, *Introduction to Modern Cryptography*, 3rd ed., 2020, Ch. 11.

[3] Goldreich, "Foundations of Cryptography, Vol. I", Cambridge University Press 2001, Ch. 3, §3.2. Standard textbook definition of ε-computational indistinguishability as `|Pr[D(X)=1] − Pr[D(Y)=1]| ≤ ε` for every distinguisher D in the admitted adversary class.

[4] Hsiao, Lu, Reyzin, "Conditional Computational Entropy, or Toward Separating Pseudoentropy from Compressibility", Eurocrypt 2007, LNCS 4515, pp. 169–186. Introduces conditional unpredictability entropy in Section 5, Definition 7.

[5] Reyzin, "Some Notions of Entropy for Cryptography", ICITS 2011, LNCS 6673, pp. 138–142. Survey; states unpredictability entropy as the logarithm of the maximum predicting probability over a bounded predictor class, equivalently the conditional min-entropy formula `−log max_{A ∈ C} Pr[A(Y) = X]`.

### Two-distribution architecture (peer follow-up)

This subsection has its own reference list (R1–R7 below) to keep the message self-contained.

There are two distributions in my proposed solution. I'm still checking if my understanding is correct from my search results. But the architecture looks right [R1, R2, R3]:

  1. Real distribution. Ciphertexts are `Enc(pubkey, secret; r)`. Given the `privkey`, the ciphertext fully determines plaintext secret, so `I(Enc(pubkey, V2); V2) = H(V2)` — no Shannon independence. This is why the unsound `E_enc_inde` failed since it claims there is independence.
  2. Hybrid distribution. Ciphertexts are `Enc(pk, 0; r)` with fresh `r`. Here the ciphertext is a function of `(pk, r)` alone, `r` is independent of `(V2, V3)`, so `I(Enc(pubkey, 0); V2) = 0` — strict Shannon independence does hold, in this distribution.

These two distributions differ by `eps_cpa` in computational distance [R4] (per swap), not in Shannon / TV distance.
IND-CPA is a computational hypothesis: an unbounded adversary can distinguish them perfectly.

So even though strictly information-theoretically, real `(view, Enc(secret))` and hybrid `(view, Enc(0))` are not close, and the encryption RVs in the real protocol are not Shannon-independent of `V2, V3`, because we assume IND-CPA first (restrict the adversary's power to make those two distributions cannot be distinguished), the pure information-theoretic lemmas still work under the assumption.
So we never claim Shannon independence in the real distribution. But:

- In the hybrid: apply Shannon-style reasoning. Use `Pr_dsdp_sol_uniform` plus `Hmin_cond_of_uniform` to get `Hmin_cond V2 view_hybrid = log m`, then `Hunp >= Hmin` [R5, R6] to lift to `Hunp_C V2 view_hybrid >= log m`.

- Cross from hybrid to real: pay `eps_cpa` per ciphertext swap via the ciphertext-replacement lemma [R7], which is a statement about `Hunp` (a computational quantity), not about Shannon entropy.

#### References for the two-distribution subsection

[R1] Lindell and Pinkas, "A Proof of Security of Yao's Protocol for Two-Party Computation", J. Cryptology 22 (2009), 161–188. https://eprint.iacr.org/2004/175.pdf
The canonical worked example of the two-distribution proof pattern. A sequence of hybrid simulators replaces garbled-circuit ciphertexts encrypting "inactive" wire labels with encryptions of a fixed dummy value, with each replacement charged to a double-encryption / IND-CPA-style assumption. After all replacements the residual view depends only on uniform random labels and is concluded by a statistical / information-theoretic argument. Caveat: the IT step there is over uniform random wire labels rather than over Shannon entropy of secret inputs, so it supports the architecture but not specifically a `Hunp(V|view)` conclusion.

[R2] Goldreich, "Foundations of Cryptography Vol. II: Basic Applications", Cambridge University Press, 2004, sec. 5.2 (semantic security) and sec. 7.3 (GMW semi-honest construction and proof).
Textbook treatment of the same shape: the GMW semi-honest security proof uses ciphertext-replacement hybrids justified by the security of the underlying encryption / OT, then concludes by indistinguishability of the residual view.

[R3] Cramer, Damgård, Nielsen, "Secure Multiparty Computation and Secret Sharing", Cambridge University Press, 2015, Chapter 7 ("Cryptographic MPC Protocols").
Reference textbook for the standard reduction in HE-/PKE-based MPC: the cryptographic protocol is reduced to an information-theoretic ideal-world view via IND-CPA-style hybrids on the encryption layer. Chapter 6 covers the IT side that the hybrid eventually meets.

[R4] Goldreich, "Foundations of Cryptography Vol. I: Basic Tools", Cambridge University Press, 2001, sec. 3.2.
Standard textbook definition of eps-computational indistinguishability: `|Pr[D(X)=1] − Pr[D(Y)=1]| ≤ eps` for every distinguisher D in the admitted adversary class.

[R5] Hsiao, Lu, Reyzin, "Conditional Computational Entropy, or Toward Separating Pseudoentropy from Compressibility", Eurocrypt 2007, LNCS 4515, pp. 169–186.
Introduces conditional unpredictability entropy in Section 5, Definition 7. The bound `Hunp_C(X | Y) ≥ Hmin_cond(X | Y)` holds by construction because a bounded predictor in class C can never outperform an unbounded one.

[R6] Reyzin, "Some Notions of Entropy for Cryptography", ICITS 2011, LNCS 6673, pp. 138–142. Survey.
States unpredictability entropy as the negative log of the maximum predicting probability over a bounded predictor class, equivalently `−log max_{A ∈ C} Pr[A(Y) = X]`.

[R7] Bellare and Rogaway, "Code-Based Game-Playing Proofs and the Security of Triple Encryption", Eurocrypt 2006, LNCS 4004, pp. 409–426. https://eprint.iacr.org/2004/331.pdf
Formal game-hop framework that justifies charging `eps_cpa` per ciphertext-replacement step as a clean syntactic transition between adjacent games.

### Survey: canonical papers that assume IND-CPA and what they build on top

Reference table of how prior work in MPC and related areas takes IND-CPA (or a closely related encryption-side hardness assumption) as a hypothesis on a primitive and then derives a protocol-level security theorem from it. Each row instantiates the same architecture used in this plan: an encryption-layer hypothesis, followed by a hybrid argument that reduces protocol-level security to the encryption advantage. The "after" column is always a *protocol-level* theorem whose proof chains game hops, each charged to the encryption assumption. Entries marked with `[†]` use a custom or stronger-than-IND-CPA notion in place of plain IND-CPA; the architecture is the same but the per-hop loss is named after that notion. Entries below were verified by downloading and reading each paper.

| # | Paper citation | How IND-CPA is assumed (on what) | Work built on the hypothesis |
|---|---|---|---|
| 1 | Lindell and Pinkas, "A Proof of Security of Yao's Protocol for Two-Party Computation", J. Cryptology 22(2):161–188, 2009. https://eprint.iacr.org/2004/175.pdf | IND-CPA on the symmetric encryption used to encrypt wire labels inside each garbled gate, plus an *elusive range* and an *efficiently verifiable range* (Definition 2). The protocol uses double encryption `Ek0(Ek1(m))`; Lemma 4 reduces the chosen-double-encryption experiment to standard IND-CPA. | Theorem 7: Yao's garbled-circuit protocol securely computes any deterministic same-output 2-party functionality against static semi-honest adversaries (probabilistic / different-output cases follow as corollaries). The hybrid argument goes `H_0, H_1, …, H_{|C|}`, replacing **one gate at a time** with a fake gate; indistinguishability of neighboring hybrids reduces to chosen double encryption, hence to IND-CPA. |
| 2 | Freedman, Nissim, Pinkas, "Efficient Private Matching and Set Intersection", EUROCRYPT 2004, LNCS 3027, pp. 1–19. | Semantic security (= IND-CPA) of an additively homomorphic public-key scheme, instantiated with Paillier. | Two-party private matching and private set intersection in the semi-honest model. The receiver encrypts its set as the coefficients of a polynomial whose roots are its elements; the sender homomorphically evaluates the polynomial on its own elements. Lemma 2 reduces client privacy to semantic security: the simulator replaces the real coefficient encryptions with encryptions of zero, indistinguishability follows from IND-CPA. (The originally cited Lindell–Pinkas CRYPTO 2000 / J. Cryptology 2002 paper is *not* an IND-CPA-based protocol; it uses Yao + OT, and the PSI / OPE attribution properly belongs to FNP04.) |
| 3 | Cramer, Damgård, Nielsen, "Multiparty Computation from Threshold Homomorphic Encryption", EUROCRYPT 2001. https://www.iacr.org/archive/eurocrypt2001/20450279.pdf | Semantic security (= IND-CPA) of a threshold homomorphic public-key scheme (Paillier-like). The shared decryption key is held in shares by the parties. | A general n-party MPC protocol secure against an active adversary corrupting any minority (`t < n/2`), with `O(nk·\|C\|)` communication. All input-privacy steps reduce to IND-CPA of the threshold scheme; active security is enforced by ZK proofs of plaintext knowledge. |
| 4 | Damgård, Pastro, Smart, Zakarias (SPDZ), "Multiparty Computation from Somewhat Homomorphic Encryption", CRYPTO 2012. https://eprint.iacr.org/2011/535.pdf | IND-CPA on a Brakerski–Vaikuntanathan-style ring-LWE somewhat homomorphic encryption scheme used in the offline preprocessing phase (the paper extends BV, CRYPTO 2011 [ref 7], not BGV). IND-CPA reduces to the polynomial-LWE (PLWE) hardness assumption; no circular-security or KDM assumption is needed. | The SPDZ preprocessing / online split: the offline phase generates authenticated Beaver triples by encrypting shares under SHE; the online phase is statistically secure / information-theoretic given the preprocessed material (Theorem 1). The full protocol is statically UC-secure against active adversaries with dishonest majority (`n−1` of `n`). |
| 5 | Asharov, Jain, López-Alt, Tromer, Vaikuntanathan, Wichs, "Multiparty Computation with Low Communication, Computation and Interaction via Threshold FHE", EUROCRYPT 2012, LNCS 7237, pp. 483–501. | IND-CPA of a *threshold* FHE scheme (single shared FHE public key with the secret key additively shared across parties), built from the BGV / BV LWE-based FHE schemes under standard **LWE** (not Ring-LWE). Distinct from the multi-key FHE setting of Row 6. | A 3-broadcast-round UC-secure MPC protocol for arbitrary functions with dishonest majority (any `t ≤ N`). The basic protocol is UC-secure against *semi-malicious* adversaries (Theorem 5.2), then compiled to fully malicious security via UC NIZKs. Inputs are encrypted once under the shared TFHE key, the function is evaluated homomorphically, and parties run a distributed decryption. Privacy of inputs reduces to IND-CPA of the TFHE scheme. |
| 6 | López-Alt, Tromer, Vaikuntanathan, "On-the-Fly Multiparty Computation on the Cloud via Multikey Fully Homomorphic Encryption", STOC 2012. https://eprint.iacr.org/2013/094.pdf `[†]` | Three assumptions stacked, not plain NTRU IND-CPA: (i) Ring-LWE; (ii) a non-standard "decisional small polynomial ratio"-style assumption that the modified-NTRU public key `h = 2gf^{-1} mod q` is computationally indistinguishable from uniform at FHE parameters where the standard Stehlé–Steinfeld RLWE proof of NTRU IND-CPA does *not* apply; (iii) weak circular security for bootstrapping. | "On-the-fly" cloud MPC: clients independently encrypt under their own keys, the server homomorphically evaluates over heterogeneous ciphertexts via multi-key FHE, and a final distributed-decryption MPC round recovers the output (Section 1.3). Confidentiality of each client's input reduces to semantic security of the multi-key FHE construction (under the three assumptions above). |
| 7 | Bogetoft, Christensen, Damgård, Geisler, Jakobsen, Krøigaard, Nielsen (Janus), Nielsen (Jesper Buus), Nielsen (Kurt), Pagter, Schwartzbach, Toft, "Secure Multiparty Computation Goes Live", FC 2009. | IND-CPA of a Paillier-style threshold homomorphic public-key scheme (the "preferred" implementation of the auction's online comparisons; an alternative based on Shamir secret sharing was also fielded). | The first large-scale production deployment of MPC: the Danish sugar-beet auction, run as a 3-server protocol among representatives of the producers, the buyer, and the research consortium. Bidder privacy of the online comparison reduces to IND-CPA of the threshold homomorphic scheme. (The originally cited Damgård–Geisler–Krøigaard–Nielsen "Asynchronous MPC" PKC 2009 / VIFF paper is *not* IND-CPA-based; VIFF is built on Shamir secret sharing with perfect security under `t < n/3`.) |
| 8 | Bellare, Hoang, Rogaway, "Foundations of Garbled Circuits", CCS 2012. https://eprint.iacr.org/2012/265.pdf `[†]` | Security of a custom *dual-key cipher* (DKC) primitive (deterministic, nonadaptive known-plaintext, nonce-tweaked, leaks the LSB of one key, forbids encryption cycles), **not** standard IND-CPA. The paper explicitly contrasts DKC with the IND-CPA + elusive-range scheme of Lindell–Pinkas (Row 1). DKC is in turn instantiated from a PRF or from fixed-key AES. | A clean abstraction of garbling schemes with formal definitions (privacy `prv`, obliviousness `obv`, authenticity `aut`) and the relations between them. Theorem 10: DKC security implies the `prv.ind` privacy notion for `Garble1`, which yields secure 2PC and KDM-secure encryption (re-establishing Applebaum's projection-KDM-implies-bounded-KDM with order-of-magnitude efficiency gains). The `obv` and `aut` notions, motivated by Gennaro–Gentry–Parno verifiable outsourcing, are defined and a `Garble2` construction is given, but no end-to-end VC protocol. |
| 9 | Damgård, Geisler, Krøigaard, "Homomorphic Encryption and Secure Comparison", IJACT 1(1):22–31, 2008 (conference version: "Efficient and Secure Comparison for On-Line Auctions", ACISP 2007, LNCS 4586, pp. 416–430). `[†]` | Semantic security (= IND-CPA) of the bespoke DGK cryptosystem `Epk(m, r) = g^m h^r mod n`, which holds under a custom subgroup-indistinguishability conjecture on RSA moduli (Conjecture 1: given `(n, g, h, u)` with `n = pq`, distinguishing a uniform element of `⟨g⟩` from a uniform element of `⟨h⟩` is computationally infeasible). Not Paillier's DCRA and not standard QR; a published correction (IJACT 1(4), 2009) adjusts the cryptosystem definition while preserving the same conjecture. | A two-party secure-comparison subprotocol on encrypted `ℓ`-bit integers, with on-line auctions as the headline application; privacy of the compared values reduces to IND-CPA of DGK. The protocol is reusable as a black-box gadget inside larger MPC protocols. |
| 10 | Chen, Laine, Rindal, "Fast Private Set Intersection from Homomorphic Encryption", CCS 2017. https://eprint.iacr.org/2017/299.pdf | IND-CPA of a leveled FHE scheme (Section 2.3). Instantiated with the Fan–Vercauteren scheme [FV12] via SEAL v2.1 (Section 6.1); the "BFV" name is later community shorthand. Sender-privacy additionally needs circuit privacy of the FHE. | An efficient *unbalanced* PSI (`Nx ≫ Ny`): the receiver holds the smaller set `Y`, encrypts and sends it to the sender, who homomorphically evaluates the membership polynomial `r_i · Π_{x ∈ X}(y_i − x)` (zero iff `y_i ∈ X`, uniform random `Z_t` element otherwise) and replies with the masked ciphertexts. Receiver privacy reduces directly to IND-CPA of the FHE (Theorem 2 / Section 5.1). |

Common pattern across all rows: the encryption-side assumption (IND-CPA, or DKC / NTRU-pseudorandomness for the `[†]`-marked rows) is the *only* thing standing between an adversary's real-world view of ciphertexts and a simulator's ideal-world view of ciphertexts of zero (or arbitrary fixed messages). Whatever protocol-level guarantee the paper claims (semi-honest 2PC, UC active MPC, PSI, secure comparison, deployed auction), the proof is a chain of game hops, each step charged to the encryption advantage. This plan adopts the same architecture: charge `eps_cpa` per ciphertext at the boundary, then conduct the residual reasoning information-theoretically over the post-swap hybrid distribution.

Audit caveats from the verification pass:
- Row 1: hybrid replaces **gates**, not wires; "efficiently verifiable range" is required alongside elusive range.
- Row 2: replaced the originally cited Lindell–Pinkas paper with FNP04 because LP00 uses Yao + OT, not Paillier IND-CPA.
- Row 4: SHE is BV-style (not BGV-style), reduced to PLWE.
- Row 5: distinguished from Row 6 — *threshold* FHE (single shared key) vs. *multi-key* FHE (independent keys); LWE not Ring-LWE; semi-malicious basic, malicious via NIZKs.
- Row 6: requires a non-standard pseudorandomness assumption beyond plain NTRU IND-CPA, plus circular security.
- Row 7: replaced the originally cited VIFF paper (Shamir-based, perfectly secure, no IND-CPA) with Bogetoft et al. FC 2009, which actually uses Paillier-style threshold encryption in production.
- Row 8: BHR12's primitive is a *dual-key cipher*, not standard IND-CPA; "verifiable computation" was overstated and downgraded to verifiable-outsourcing definitions.
- Row 9: DGK does not use Paillier or QR; it relies on a custom RSA-subgroup conjecture.
- Row 10: paper writes "FV", not "BFV"; sender-privacy additionally needs circuit privacy.

### IT residual after the IND-CPA hop

Every row above has *some* information-theoretic step after the IND-CPA reduction. The strength and explicitness vary. The "post-swap residual" is the distribution that remains after replacing real ciphertexts with encryptions of zero (or the simulator-side equivalent).

| # | Paper (short) | IT residual after IND-CPA hop | Strength of IT step |
|---|---|---|---|
| 1 | Lindell-Pinkas, Yao 2009 | Simulated garbled circuit reveals only the active wire labels, which are uniform random strings | Uniform-random-labels (perfect IT) |
| 2 | Freedman-Nissim-Pinkas, EUROCRYPT 2004 | After encrypting zero coefficients, sender's reply `r_i · P(y_i)` is uniform on `Z_q` for non-matches | Uniform random masking (perfect IT) |
| 3 | Cramer-Damgård-Nielsen, EUROCRYPT 2001 | Residual view is Shamir-style threshold shares with honest majority `t < n/2` | **Strong** — Shamir secret-sharing IT-secure |
| 4 | SPDZ, CRYPTO 2012 | Online phase is **unconditionally secure** given preprocessed Beaver triples (Theorem 1: statistical UC security) | **Strongest** — explicit "online phase is information-theoretic" |
| 5 | Asharov et al., EUROCRYPT 2012 | Distributed decryption uses noise-flooding for statistical indistinguishability | Statistical (smudging) |
| 6 | López-Alt et al., STOC 2012 | Distributed decryption uses noise-flooding | Statistical (smudging) |
| 7 | Bogetoft et al., FC 2009 | After threshold decryption the comparison reduces to a 3-server secret-sharing reconstruction | **Strong** — Shamir / threshold sharing IT-secure |
| 8 | Bellare-Hoang-Rogaway, CCS 2012 | Simulator outputs uniform random labels for inactive wires; identical-distribution residual | Uniform-random-labels (perfect IT) |
| 9 | Damgård-Geisler-Krøigaard, IJACT 2008 | Comparison-bit reveal uses uniform random masks over the message group | Uniform random masking (perfect IT) |
| 10 | Chen-Laine-Rindal, CCS 2017 | Sender's masked ciphertexts contain `r_i · Π(y_i − x)`, uniform on `Z_t` for non-matches (random-masking lemma + circuit privacy) | Uniform random masking (statistical) |

Closest precedents to the DSDP plan's architecture (IND-CPA hop → genuinely IT residual that one can name with an entropy quantity):

- **SPDZ (Row 4)** is the strongest precedent: the abstract literally states the online phase is unconditionally secure, with IND-CPA on SHE absorbed entirely in the offline phase.
- **CDN01 (Row 3)** and **Bogetoft (Row 7)** both pass through Shamir-style secret sharing, whose IT security is well-known.

None of these papers state the post-swap residual as a Shannon / min-entropy / `Hunp` bound. They use simulator-indistinguishability or "uniform random" arguments instead. So the DSDP plan's framing — IND-CPA hop followed by an *entropy-quantified* IT bound (`Hunp ≥ log m − q·eps_cpa` with `q ∈ {2, 1, 0}` for Alice / Bob / Charlie corruption under path (b)) — is a new presentation of the same two-distribution architecture, with the residual reasoning lifted from "uniform random" or "indistinguishable" into the language of conditional unpredictability entropy.

## Context

The Rocq proof in `dumas2017dual/dsdp/dsdp_security.v` currently relies on an unsound axiom

```coq
Hypothesis E_enc_inde :
  forall (A B : finType) (p : party_id)
         (X : {RV P -> p.-enc A}) (Y : {RV P -> B}),
  P |= X _|_ Y.
```

(line 135-137) which claims any random variable taking values in a ciphertext type is information-theoretically independent of any other random variable. This is mathematically false: `Enc(pk, V)` is fully determined by `V` given `sk`, so `(Enc(pk,V), V)` has full mutual information. More fundamentally, no PKE scheme can be unconditionally secure (Diffie–Hellman 1976; Maurer CRYPTO '99; Panny eprint 2019/1228), so any IT-style independence axiom about ciphertexts admits concrete counterexamples in-model.

The three top-level security theorems (`dsdp_entropic_security` for corrupted Alice at line 260; `bob_privacy_*` at lines 803/839; `charlie_privacy_*` at lines 1505/1544) all conclude `H(V_target | AdversaryView) = log m`. With the unsound axiom retired, that exact Shannon equality cannot be recovered: `H` is an unbounded-computation quantity and the encryption fully leaks information to an unbounded adversary.

**Goal.** Replace `E_enc_inde` with a sound, standard cryptographic assumption (IND-CPA), and reformulate the security conclusion in the most information-theoretic available framework that admits PKE-based protocols. Concretely, switch the conclusion from Shannon conditional entropy to **conditional unpredictability entropy** (Hsiao–Lu–Reyzin, Eurocrypt 2007), preserving the IT spirit (closed-form negative-log-of-probability quantity with a clean chain rule) while sound under standard cryptographic assumptions.

The corrupted-Alice case is the running example: V2 is owned by Bob, V3 by Charlie. Security claim: "no efficient adversary corrupting Alice can guess V2 (or V3) from `AliceView` better than uniform random." Bob-corrupted and Charlie-corrupted cases are structurally identical.

RSSDP (`weng2026/rssdp/`) is information-theoretically secure under the standard SMC model and stays unchanged.

## Why unpredictability entropy

Among computational entropy notions:
- **HILL pseudoentropy** does not satisfy a chain rule (Krenn–Pietrzak–Wadia, TCC 2013).
- **Yao / metric pseudoentropy** are compression-based, less IT-flavored.
- **Simulation-based security** is operational, not entropic.
- **Unpredictability entropy** `H^unp_C(X | Y) = -log max_{A ∈ C} Pr[A(Y) = X]` is the negative log of the best guessing probability over an adversary class `C`. The *quantity* is information-theoretic (min-entropy in form); only the quantifier is computational. **It satisfies a chain rule** (HLR07 Thm 3.4) and maps directly to the SMC privacy claim.

## Audit-driven corrections to the original sketch

Six soundness/tightness issues were identified by the information-theory expert audit (verdict: **Sound-with-fixes**) and are addressed below:

1. **Random-variable-form IND-CPA (not constant-message).** The hybrid swap targets `Enc(D3)` where `D3` is a random variable correlated with the rest of `AliceView`. Standard fixed-message IND-CPA does not directly justify this; we need real-or-random IND-CPA over correlated message random variables.

2. **Adversary class closure conditions.** The chain rule and hybrid reduction require the adversary class `C` (a per-view-codomain Markov-kernel membership predicate, `Parameter C : forall (Y : finType), (Y -> fdist R) -> Prop`) to be closed under (a) bounded enumeration, (b) composition with samplers for joint random variables, (c) input fixing. These are stated as `Hypothesis`es `C_enum`, `C_sample`, `C_fix_input` in `computational_entropy.v` (Phase 1).

3. **Independent-extension bridge lemma.** Existing Shannon lemmas (`alice_view_to_cond`, `dsdp_constraint_centropy_eqlogm`) are stated about the *original* view, not the zero-encryption hybrid (which has fresh encryption randomness). Need `cond_entropy_indep_extension`: `H(X | Y) = H(X | Y, Z)` when `Z _|_ (X, Y)`, to factor out fresh encryption coins.

4. **Uniformity is the critical-path fact, not Shannon entropy.** `Pr_dsdp_sol_uniform` (`dsdp_entropy.v:237`) proves genuine uniformity of the conditional distribution at `1/m` on the solution set. `dsdp_centropy_uniform` (`dsdp_entropy.v:294`) is a Shannon-entropy *consequence* of this uniformity, not a separate fact, and is not directly usable for `Hmin`. For the Hunp argument we go to `Hmin_cond` from the same uniformity via a new `Hmin_cond_of_uniform` lemma in Phase 1, bypassing the Shannon detour. `Hunp ≥ Hmin` then gives the final bound.

5. **Marginal not joint.** Rather than `Hunp(V2, V3 | view) ≥ log(m²)` (which is not automatic — joint unpredictability is not the sum of marginals without an additional chain-rule step), state two separate theorems: `Hunp(V2 | view) ≥ log m - q·eps_cpa` and `Hunp(V3 | view) ≥ log m - q·eps_cpa`, where `q` is the per-corruption ciphertext count (see closed-form section).

6. **Tighter eps accounting (revised in the closed-form section).** The original sketch used `eps_total = 3·eps_cpa + δ_chain`. After the math-audit pass, `δ_chain` was eliminated entirely: the proof goes through `Pr_dsdp_sol_uniform → Hmin_cond_of_uniform → Hunp ≥ Hmin`, never invoking a chain rule for unpredictability entropy. The bound deduction is `q · eps_cpa` with `q ∈ {2, 1, 0}` for Alice / Bob / Charlie corruption under path (b) (matching the *cross-key* ciphertext count after own-key plaintext rewrites), as documented at each theorem statement in the closed-form section.

The audit also recommended a guessing-probability-only framing as a simpler alternative; this plan keeps the Hunp framing because the user explicitly requested the most information-theoretic option, and the entropy form composes with the existing Shannon machinery in `dsdp_entropy.v`. The primitive guessing-probability statement remains derivable as a corollary.

## Closed-form theorem statements (target)

Per peer recommendation: the theorem statements (unlike lemmas) carry their full context inline, so each one reads as a closed formula independent of the surrounding section. Writing them down now, before any deeper implementation work, fixes the target the five-phase plan is implementing. The notation block and Theorems below were verified against `dsdp_security.v` and revised after a math-audit pass (Fixes 1–11 below).

### Notation block (used by all six theorems below)

- `(Ω, Σ, P)` is a discrete probability space.
- `(R, +, ·, 0_R, 1_R)` is a finite commutative ring with `m := #|R| ≥ 2`. `R^× := { u ∈ R | ∃ v ∈ R, u · v = 1_R }` is its multiplicative unit group.
- `𝓡_enc` is the (finite) encryption-randomness space of the scheme.
- `(KeyGen, Enc, Dec)` is a public-key encryption scheme with plaintext space `R`, ciphertext space `𝒞`, and randomness space `𝓡_enc`. The public-key registry `(pk_a, pk_b, pk_c)` is fixed at protocol setup, with corresponding decryption keys `(Dk_a, Dk_b, Dk_c)`. Correctness `Dec(Dk_p, Enc(pk_p, m; r)) = m` is assumed but not invoked in the theorem statements.
- `𝒲` ranges over arbitrary finite "auxiliary view" types; it is a metavariable in the IND-CPA hypothesis below.
- `C` is the class of bounded adversaries against which we measure secrecy. For each finite type `𝒴`, `C` contains Markov kernels `A : 𝒴 → Δ(R)`, where `Δ(R)` denotes the set of probability distributions on `R`. When `A` observes view value `y`, the kernel `A(y)` is the probability distribution from which `A` samples its guess, so the kernel formalism captures randomized predictors whose internal randomness is independent of the rest of the experiment. When we write `A ∈ C` against a view `Y : Ω → 𝒴` with target `X : Ω → R`, we restrict to the kernel-typed entry matching `codom(Y)`. The success probability is `Pr[A(Y) = X] := E_ω [ A(Y(ω))({X(ω)}) ]`, which for each sample ω takes the distribution `A(Y(ω))` on `R`, evaluates it at the singleton `{X(ω)}` to get the mass `A` places on the true target, and averages those masses over ω. `C` is closed under (a) bounded enumeration, (b) composition with samplers for joint random variables, and (c) input fixing, the closure conditions of Hsiao–Lu–Reyzin, Eurocrypt 2007, Definition 7.
- `H_unp^C(X | Y) := −log sup_{A ∈ C} Pr[A(Y) = X]` is conditional unpredictability entropy (Hsiao–Lu–Reyzin, Eurocrypt 2007, Def. 7).
- `ε_cpa ∈ [0, 1]` is the IND-CPA advantage bound. The scheme satisfies `(C, ε_cpa)`-IND-CPA in real-or-random form: for every finite type `𝒲`, every joint random variable `(W, M) : Ω → 𝒲 × R`, every party key `pk ∈ {pk_a, pk_b, pk_c}`, and every fresh encryption randomness `r : Ω → 𝓡_enc` uniform on `𝓡_enc` and independent of `(W, M)`,
  `(W, Enc(pk, M; r))  ≈_{C, ε_cpa}  (W, Enc(pk, 0_R; r'))`
  where `r' : Ω → 𝓡_enc` is a fresh independent uniform draw and `≈_{C, ε_cpa}` denotes `ε_cpa`-indistinguishability against `C` (i.e. for every `A ∈ C`, `|Pr[A(LHS) = 1] − Pr[A(RHS) = 1]| ≤ ε_cpa`).

### Theorem 1 (DSDP secrecy of V_2 against corrupted Alice, closed form)

**Hypotheses.**

1. *Inputs.* `V_1, V_2, V_3 : Ω → R` are jointly independent. `V_2` and `V_3` are individually uniform on `R`. (`V_1` may have arbitrary distribution.)
2. *Protocol-internal randomness.* `U_1, U_2, U_3, R_2, R_3 : Ω → R` are mutually independent, jointly independent of `(V_1, V_2, V_3)`, with `U_1, U_2` uniform on `R`, `R_2, R_3` uniform on `R`, and `U_3 ∈ R^×` almost surely.
3. *Protocol-defined intermediates (algebraic identities of honest DSDP execution).* The following random variables are defined pointwise on `Ω`:
   - `D_2 := V_2 · U_2 + R_2`
   - `D_3 := V_3 · U_3 + R_3 + D_2 = V_3 · U_3 + V_2 · U_2 + R_2 + R_3`
   - `S   := D_3 + U_1 · V_1 − R_2 − R_3 = U_1 · V_1 + U_2 · V_2 + U_3 · V_3` (the publicly opened sum at the reveal step).
4. *Encryption randomness.* `r_a, r_b, r_c : Ω → 𝓡_enc` are mutually independent, each uniform on `𝓡_enc`, and jointly independent of `(V_1, V_2, V_3, U_1, U_2, U_3, R_2, R_3)`.
5. *Adversary view.*
   `AliceView := (Dk_a, S, V_1, U_1, U_2, U_3, R_2, R_3, Enc(pk_a, D_3; r_a), Enc(pk_c, V_3; r_c), Enc(pk_b, V_2; r_b))`.

**Conclusion.**

`H_unp^C(V_2 | AliceView) ≥ log m − 2 · ε_cpa.`

*Path-(b) proof remark.* Rewrite the own-key ciphertext `Enc(pk_a, D_3; r_a)` as the plaintext `D_3` via `Hunp_dec_replace` (Phase 1, using `Dk_a ∈ AliceView` and decryption correctness); then apply IND-CPA RoR twice to swap the cross-key encryptions `Enc(pk_c, V_3; r_c)` and `Enc(pk_b, V_2; r_b)` for `Enc(pk_c, 0)` and `Enc(pk_b, 0)`, losing `1 · ε_cpa` per swap. The residual reduces to the existing `Pr_dsdp_sol_uniform` after observing that `D_3 = (S − U_1 · V_1) + R_2 + R_3` is a deterministic function of `(S, V_1, U_1, R_2, R_3)`.

**Corollary A (entropy-derived form, follows from the conclusion by the definition of `H_unp`).** For every `A ∈ C`,
`Pr[A(AliceView) = V_2] ≤ (1/m) · 2^{2 · ε_cpa}.`
For small `ε_cpa` this is `≈ 1/m + (2 · ε_cpa · ln 2) / m`, which is *strictly weaker* than the additive form below.

**Corollary B (additive form, proved directly by probability hops, not via `H_unp`).** Under the same hypotheses, for every `A ∈ C`,
`Pr[A(AliceView) = V_2] ≤ 1/m + 2 · ε_cpa.`
Proof: each cross-key ciphertext swap in the hybrid argument is an `ε_cpa`-indistinguishability hop on the additive guessing probability; after two swaps the residual hybrid has `Pr[A(view) = V_2] = 1/m` exactly (uniform conditional). Sum the additive losses.

### Theorem 2 (DSDP secrecy of V_3 against corrupted Alice)

Same hypotheses 1–5 as Theorem 1, **with the addition of `U_2 ∈ R^×` almost surely** in hypothesis 2 (the V_3 marginal of the residual conditional is uniform on `m` only under the symmetric unit-mask hypothesis on `U_2`; the existing `Pr_dsdp_sol_uniform` discharges V_2 under `U_3 ∈ R^×`, but the V_3 marginal needs `U_2 ∈ R^×`, hence the Phase 1 companion lemma `Pr_dsdp_sol_uniform_V3`). Conclusion:
`H_unp^C(V_3 | AliceView) ≥ log m − 2 · ε_cpa.`

*Path-(b) proof remark.* Same rewrite-then-swap pattern as Theorem 1, with `Pr_dsdp_sol_uniform_V3` taking the role of `Pr_dsdp_sol_uniform` in the residual.

The same two corollary forms (A multiplicative `(1/m) · 2^{2 · ε_cpa}`, B additive `1/m + 2 · ε_cpa`) follow.

### Theorems 3–6 (Bob-corrupted and Charlie-corrupted cases)

The DSDP protocol is *not* perfectly role-symmetric: the corrupted-party views as defined in `dsdp_security.v` differ in size. The closed-form views, with explicit ciphertext counts, are:

- `BobView     := (Dk_b, V_2, Enc(pk_c, V_3 · U_3 + R_3; r'_c), Enc(pk_b, D_2; r'_b))`
  (4 components, **2 ciphertexts**: one under `pk_c`, one under `pk_b`.)
- `CharlieView := (Dk_c, V_3, Enc(pk_c, D_3; r''_c))`
  (3 components, **1 ciphertext**, under `pk_c`.)

Here `r'_b, r'_c, r''_c : Ω → 𝓡_enc` are fresh independent uniform draws, jointly independent of `(V_1, V_2, V_3, U_1, U_2, U_3, R_2, R_3)`.

**Theorem 3 (V_1 against corrupted Bob).** Hypotheses 1–4 of Theorem 1, additionally requiring `V_1` uniform on `R`. **No unit-mask hypothesis is required.** Conclusion:
`H_unp^C(V_1 | BobView) ≥ log m − 1 · ε_cpa.`
*Path-(b) proof remark.* Rewrite `Enc(pk_b, D_2; r'_b)` as the plaintext `D_2 = V_2 · U_2 + R_2` via `Hunp_dec_replace` (using `Dk_b ∈ BobView`); swap the cross-key ciphertext `Enc(pk_c, V_3 · U_3 + R_3; r'_c)` for `Enc(pk_c, 0)` under IND-CPA RoR (lose `1 · ε_cpa`); conclude by independence of `V_1` from `(V_2, D_2)`, since `D_2` does not involve `V_1`.

**Theorem 4 (V_3 against corrupted Bob).** Same hypotheses as Theorem 3 with `V_3` uniform (already in Theorem 1). **No unit-mask hypothesis is required.** Conclusion:
`H_unp^C(V_3 | BobView) ≥ log m − 1 · ε_cpa.`
*Path-(b) proof remark.* Same rewrite-then-swap pattern as Theorem 3; conclude by independence of `V_3` from `(V_2, D_2)`, since `D_2` does not involve `V_3` or `U_3`.

**Theorem 5 (V_1 against corrupted Charlie, unconditional).** Hypotheses 1–4 of Theorem 1, additionally requiring `V_1` uniform on `R`. **No unit-mask hypothesis and no IND-CPA hop are required.** Conclusion:
`H_unp^C(V_1 | CharlieView) ≥ log m.`
*Path-(b) proof remark.* Rewrite `Enc(pk_c, D_3; r''_c)` as the plaintext `D_3` via `Hunp_dec_replace` (using `Dk_c ∈ CharlieView`); no swap needed; conclude by independence of `V_1` from `(V_3, D_3)`, since `D_3` does not involve `V_1`.

**Theorem 6 (V_2 against corrupted Charlie, unconditional).** Same hypotheses as Theorem 5 with `V_2` uniform (already in Theorem 1). **No unit-mask hypothesis and no IND-CPA hop are required.** Conclusion:
`H_unp^C(V_2 | CharlieView) ≥ log m.`
*Path-(b) proof remark.* Rewrite `Enc(pk_c, D_3; r''_c)` as the plaintext `D_3` via `Hunp_dec_replace`; conclude `V_2 | (V_3, D_3)` uniform on `R` by `Hmin_cond_uniform_with_additive_pad` (Phase 1). Reason: `R_2 + R_3` is uniform on `R` (sum of two independent uniforms over a finite abelian group) and jointly independent of `(V_2, V_3, U_2, U_3)`. So for every joint value of `(V_2, V_3, U_2, U_3)`, `Pr[D_3 = c | V_2, V_3, U_2, U_3] = Pr[R_2 + R_3 = c − V_2 · U_2 − V_3 · U_3] = 1/m`, which is constant in `(V_2, U_2, U_3)`. Therefore conditioning on `D_3` does not bias the prior on `V_2`. No unit-mask is required.

Both corollary forms (A multiplicative, B additive) carry over for each theorem, with the deduction `q · ε_cpa` matching the *cross-key* ciphertext count `q ∈ {2, 1, 0}` for Alice / Bob / Charlie corruption respectively, after rewriting own-key ciphertexts as their plaintexts. For Charlie's two theorems (`q = 0`) both Corollary A and Corollary B collapse to the exact bound `Pr[A(Y) = X] ≤ 1/m`.

### Reading guide

- Each of the six theorems is a closed formula: every free symbol is bound either by the notation block above or by the local hypothesis list. The intermediates `D_2`, `D_3`, `S` and the views `AliceView`, `BobView`, `CharlieView` are defined inline in terms of the input random variables, not imported as section variables from `dsdp_security.v`.
- The deduction in the bound is `q · ε_cpa`, where `q` is the number of *cross-key* ciphertexts in the corrupted party's view (2 for Alice, 1 for Bob, 0 for Charlie) after rewriting own-key ciphertexts as their decrypted plaintexts under path (b); see the Path (b) decision below. No `δ_chain` term appears because the proof never invokes a chain rule for unpredictability entropy; uniformity of the residual conditional distribution combined with `H_unp ≥ H_min` discharges the IT step directly.
- **Corollary A vs. Corollary B.** From `H_unp^C(X | Y) ≥ log m − q · ε_cpa` one derives only the multiplicative bound `Pr[A(Y) = X] ≤ (1/m) · 2^{q · ε_cpa}` (Corollary A). The cleaner additive bound `Pr[A(Y) = X] ≤ 1/m + q · ε_cpa` (Corollary B) is *not* a consequence of the entropy bound; it must be proved separately by hop-by-hop additive accounting on the guessing probability. Both are recorded because the implementation in Phases 4 and 5 produces both forms, and downstream callers may want either.
- These six theorems are the targets that Phases 4 and 5 of the implementation plan below must produce as `Theorem` (not `Lemma`) entries in `dsdp_security.v`, with all hypothesis blocks materialized as Coq `forall`-binders rather than section-level `Hypothesis`.

### Path (b) decision recorded

**Decision.** The formalization commits to *path (b)*: the encryption hypothesis stays at plain IND-CPA RoR, and own-key ciphertexts (those encrypted under the corrupted party's own public key) are rewritten as their decrypted plaintexts before any IND-CPA hop is applied. The cross-key ciphertexts that remain (under non-corrupted-party keys) are then swapped under standard IND-CPA RoR.

**Per-theorem cross-key ciphertext counts** (these are the `q` values appearing in the conclusion `H_unp ≥ log m − q · ε_cpa` of each theorem):

- Alice corrupted: `q = 2` (the ciphertexts `Enc(pk_c, V_3; r_c)` and `Enc(pk_b, V_2; r_b)`).
- Bob corrupted: `q = 1` (the ciphertext `Enc(pk_c, V_3 · U_3 + R_3; r'_c)`).
- Charlie corrupted: `q = 0`. **Both Charlie theorems are unconditional**, holding with no IND-CPA hop at all.

**The load-bearing rewrite lemma.** `Hunp_dec_replace` (Phase 1, in `computational_entropy.v`):

`H_unp^C(X | (W, Enc(pk_p, M; r))) ≥ H_unp^C(X | (W, M))`

whenever `Dk_p ∈ W` and decryption correctness holds. The lemma is stated as an inequality `≥`, not an equality. Justification: any predictor against `(W, M)` can be converted to a predictor against `(W, Enc(pk_p, M; r))` with the *same* success probability by post-composing with `Dec(Dk_p, ·)`; this is the `C_sample` closure axiom applied to the deterministic `Dec` sampler. The reverse inequality would require the adversary class to be additionally closed under fresh-randomness `Enc` composition, which is not needed for the proof; we do not introduce it.

**Why path (b) is preferred over path (a).** Path (a) would strengthen the encryption hypothesis to a KDM-secure or circular-secure variant that admits own-key swaps with a uniform `q ∈ {3, 2, 1}` accounting. That hypothesis is non-standard and is not currently formalized in infotheo, so committing to it would require new axiomatic infrastructure. Path (b) keeps the hypothesis at plain IND-CPA RoR (which is the standard textbook notion and reduces to PLWE / DDH / DCRA in the usual instantiations) and absorbs the own-key plaintext into the IT residual analysis. The IT residual under path (b) goes through cleanly: for Alice the existing `Pr_dsdp_sol_uniform` carries the V_2 marginal directly, for Bob the residual is V_target ⫫ (V_2, D_2), for Charlie the additive uniformity of `R_2 + R_3` makes the conditional distribution of `V_2` uniform without any unit-mask hypothesis.

## Approach (5 phases)

### Phase 1 — Foundation (new files in `information_theory/`)

Add two thin layers to infotheo:

1. **`min_entropy.v`** — pure information-theoretic min-entropy:
   - `Definition pmax (P : fdist A) := \rmax_a P a.`
   - `Definition Hmin (P : fdist A) := -log (pmax P).`
   - `Definition Hmin_cond (PXY : fdist (X*Y)) : R := ...`
   - Lemmas: `Hmin_le_entropy` (min-entropy ≤ Shannon), `Hmin_uniform = log #|A|`, monotonicity.
   - **`Hmin_cond_of_uniform`**: if the conditional distribution of `X` given `Y` is uniform on `m` elements for every value of `Y`, then `Hmin_cond X Y = log m`. One-line consequence of the `Hmin` definition. Used in Phase 4 to derive min-entropy directly from `Pr_dsdp_sol_uniform`, bypassing the Shannon `dsdp_centropy_uniform` detour.
   - **`cond_entropy_indep_extension`**: `Z _|_ [%X, Y] -> H(X | [%Y, Z]) = H(X | Y)` (for both Shannon and min-entropy).
     Used to factor out fresh encryption randomness in Phase 4.
   - Reuse: `centropy`, `entropy` from `information_theory/entropy.v`; `inde_RV` from `dumas2017dual/lib/extra_entropy.v`.

2. **`computational_entropy.v`** — adversary class as a per-view-codomain Markov-kernel membership predicate, and unpredictability entropy.

   The class `C` is a `Parameter` indexed by view-codomain finite type `Y`, whose elements are Markov kernels `Y -> fdist R`. There is no separate `advantage` predicate (the success probability is computed directly from the kernel, not tracked separately).

   ```coq
   Section ComputationalEntropy.
   Variable R : finComRingType.    (* the message space, as in the closed-form Setup *)

   Parameter C : forall (Y : finType), (Y -> fdist R) -> Prop.

   (* Closure conditions of Hsiao-Lu-Reyzin Eurocrypt 2007 Definition 7. *)
   Hypothesis C_enum :
     forall (Y B : finType) (A : Y * B -> fdist R),
     C _ A -> forall (b : B), C _ (fun y => A (y, b)).
   Hypothesis C_sample :
     forall (Y W : finType) (A : Y -> fdist R) (sampler : W -> fdist Y),
     C _ A -> exists A' : W -> fdist R,
              C _ A' /\
              forall w, A' w = fdist_bind (sampler w) A.
   Hypothesis C_fix_input :
     forall (Y Y' : finType) (A : Y * Y' -> fdist R) (y0 : Y'),
     C _ A -> C _ (fun y => A (y, y0)).
   ```

   Success probability and unpredictability entropy:

   ```coq
   Definition succ_prob {Y : finType}
     (A : Y -> fdist R) (Yrv : {RV P -> Y}) (X : {RV P -> R}) : R :=
     `E (fun ω => A (Yrv ω) (X ω)).
     (* For each ω, A(Yrv ω) is a distribution on R; evaluate it at X(ω)
        to get the mass A places on the true target; average over ω.
        Equivalent to E_ω [ A(Yrv(ω))({X(ω)}) ]. *)

   Definition Hunp {Y : finType}
     (Yrv : {RV P -> Y}) (X : {RV P -> R}) : R :=
     - log (sup_{ A : Y -> fdist R | C _ A } succ_prob A Yrv X).
   ```

   Note: `Hunp` does not take `C` as an explicit argument because `C` is a `Parameter` of the section; it is universally quantified at the top of the file rather than per-call. This matches HLR's convention.

   Lemmas (proved against the abstract `C` plus the three closure hypotheses):

   - `Hunp_chain_rule`: `Hunp Yrv (RV_pair Yrv Zrv) X ≥ Hunp Yrv X - log #|codom Zrv|`, with the `C_enum` closure justifying the chain-rule reduction (HLR07 Thm 3.4).
   - `Hunp_ge_Hmin`: `Hunp Yrv X ≥ Hmin_cond X Yrv`. Bounded predictors never outperform unbounded ones, since the unbounded predictor that picks the argmax of the conditional distribution is a Markov kernel into Δ(R) and is in any reasonable C, but more directly: the sup over `C`-membership is a sup over a sub-class of all kernels, so it is at most the sup over all kernels, which is `pmax = exp(-Hmin_cond)`.
   - `Hunp_uniform_lower`: if the conditional distribution of `X` given `Yrv` is uniform on a set of `m` values for each value of `Yrv`, then `Hunp Yrv X ≥ log m`. Direct consequence of `Hmin_cond_of_uniform` and `Hunp_ge_Hmin`.
   - `Hunp_dec_replace` (path-(b) own-key plaintext rewrite): for any party `p`, any random variables `X : {RV P -> R}` and `W : {RV P -> 𝒲}` with `Dk_p ∈ W`, any `M : {RV P -> R}`, and any encryption randomness `r : {RV P -> 𝓡_enc}`,
     `Hunp (RV_pair W (E' p M r)) X ≥ Hunp (RV_pair W M) X`,
     where the inequality is justified by `C_sample` applied to the deterministic `Dec(Dk_p, ·)` sampler. Stated as `≥`, not `=` (audit fix).

   This is the abstract Option-2 commitment from the message-thread discussion: `C`'s exact concrete model is left as a parameter; the theorems are universally quantified over any `C` satisfying `C_enum`, `C_sample`, `C_fix_input`. `Print Assumptions` will list these three closure hypotheses plus `C` itself as standing parameters of each theorem, not as oracle-trusted axioms about the universe. Discharging them to a concrete model (e.g. all total functions, or a circuit class) is downstream of this plan.

### Phase 2 — IND-CPA replacement of the unsound axiom

In `homomorphic_encryption/homomorphic_encryption.v`:

- **Remove** axiom `E_enc_inde`.
- **Add** an abstract real-or-random IND-CPA hypothesis (audit fix #1):
  ```coq
  Hypothesis IND_CPA_RoR :
    forall (A : finType) (p : party_id) (V : finType)
           (M : {RV P -> A}) (view : {RV P -> V}),
    indist_eps eps_cpa
      (RV_pair view (E' p `o M))
      (RV_pair view (E' p `o cst_RV (0 : A))).
  ```
  This says: under any joint distribution `(view, M)`, encrypting the actual `M` is `eps_cpa`-indistinguishable from encrypting zero. The reduction to standard IND-CPA holds whenever the reduction can sample `(view, M)` — which is granted by the `C_sample` closure axiom from Phase 1.
- **Rewrite** `E_enc_ce_contract` as `E_enc_ce_contract_eps` using `Hunp` and concluding `Hunp C Z [%X, E] ≥ Hunp C Z X - eps_cpa`.

### Phase 3 — Hybrid (ciphertext-replacement) lemma

In `computational_entropy.v`:

- **Lemma `ciphertext_replacement`** (relies on `IND_CPA_RoR` + `C_sample`):
  ```
  Hunp C V_target (RV_pair view (E' p `o secret_RV))
  ≥ Hunp C V_target (RV_pair view (E' p `o cst_RV 0))
  - eps_cpa.
  ```
  Proof: any predictor against the LHS gives a distinguisher between the two distributions, contradicting `IND_CPA_RoR` if the gap exceeds `eps_cpa`.
- **Lemma `ciphertext_replacement_iter`**: iterating gives `≥ Hunp(...) - q · eps_cpa` for `q` ciphertexts under independent keys. The three Alice-view encryptions are under three distinct party keys (Alice's `pk_a`, Charlie's `pk_c`, Bob's `pk_b`), so this applies.

### Phase 4 — Restate and re-prove the three security theorems

In `dsdp_security.v`:

Replace each Shannon conclusion with **two marginal Hunp theorems** (audit fix #5). For corrupted Alice:

```coq
Theorem dsdp_unp_security_alice_V2 :
  Hunp V2 AliceView ≥ log (m%:R : R) - 2 * eps_cpa.

Theorem dsdp_unp_security_alice_V3 :
  Hunp V3 AliceView ≥ log (m%:R : R) - 2 * eps_cpa.
```

(Bob and Charlie cases use `1 * eps_cpa` and `0 * eps_cpa` respectively per the path-(b) decision; see the Path (b) decision recorded above. The `δ_chain` term was dropped per the closed-form section's reading guide: the proof never invokes a chain rule for unpredictability entropy, so no class-shrinkage term arises.)

**Proof skeleton** (same shape for both):
0. Apply `Hunp_dec_replace` (Phase 1) using `Dk_a ∈ AliceInputsView` to rewrite the own-key ciphertext `Enc(pk_a, D_3; r_a)` as the plaintext `D_3`. AliceView becomes information-theoretically equivalent to `(Dk_a, S, V1, U1, U2, U3, R2, R3, D_3, Enc(pk_c, V_3; r_c), Enc(pk_b, V_2; r_b))`.
1. Apply `ciphertext_replacement_iter` to swap the two cross-key encryptions `E_charlie_v3` and `E_bob_v2` for `Enc(0)` under fresh independent randomness. Lose `2 · eps_cpa`.
2. The hybrid view is `(V1, U1, U2, U3, R2, R3, S, D_3, Enc(pk_c, 0; r_c), Enc(pk_b, 0; r_b))`. The encryption randomness `(r_c, r_b)` is fresh and independent of `(V2, V3, AliceInputsView)`.
3. Apply `cond_entropy_indep_extension` (Phase 1) to factor out `(r_c, r_b)` — the conditional entropy / min-entropy is unchanged by conditioning on independent fresh randomness.
4. The remaining view is `(V1, U1, U2, U3, R2, R3, S, D_3)`. Since `D_3 = (S − U_1·V_1) + R_2 + R_3` is a deterministic function of `(S, V_1, U_1, R_2, R_3)`, conditioning on `D_3` adds no information; the view collapses to `(V1, U1, U2, U3, R2, R3, S)`. This is precisely the `CondRV ∪ {R2, R3}` shape that the existing `alice_view_to_cond` / `dsdp_centropy_uniform` chain handles.
5. By `Pr_dsdp_sol_uniform` (`dsdp_entropy.v:237`) for V_2 (under `U_3 ∈ R^×`), or `Pr_dsdp_sol_uniform_V3` for V_3 (under `U_2 ∈ R^×`), the conditional distribution `V_target | (V1, U1, U2, U3, S)` is uniform on `m` values. By `Hmin_cond_of_uniform` (Phase 1), this gives `Hmin_cond V_target (V1, U1, U2, U3, S) = log m`. Note: the existing Shannon `dsdp_centropy_uniform` is a consequence of the same uniformity and is not on the critical path.
6. Apply `Hunp_ge_Hmin`: `Hunp C V_target hybrid_view ≥ log m`.
7. Combine with steps 0–3: `Hunp C V_target AliceView ≥ log m - 2 · eps_cpa`. No `δ_chain` term arises because the argument never invokes a chain rule for unpredictability entropy.

**Hypothesis cleanup**: `cinde_V2V3` and `cinde_V2` (lines 178-182) — these stay as Shannon independence hypotheses. They quantify over `[Dk_a, R2, R3]` which contain no encryption RVs in the post-hybrid view. `VarRV_uniform`, `VarRV_indep_inputs`, `constraint_holds`, `U3_coprime_m`, `V3_determined` all retain.

### Phase 5 — Bob-corrupted and Charlie-corrupted parallels

The `bob_security_independence` (line 454) and `charlie_security_independence` (line 875) sections re-use `E_enc_inde` transitively. Apply the identical Phase 4 transformation, with the per-corruption ε accounting from the closed-form section (one `ε_cpa` per *cross-key* ciphertext after path-(b) own-key plaintext rewrites):
- `bob_privacy_V1` / `bob_privacy_V3` → `Hunp V_target BobView ≥ log m - 1 * eps_cpa`.
- `charlie_privacy_V1` / `charlie_privacy_V2` → `Hunp V_target CharlieView ≥ log m` (no `ε_cpa` term — unconditional).

Per the Path (b) decision, Charlie's theorems are unconditional and Bob's incur `1 * eps_cpa`. Proof step 0 of Phase 4 (the `Hunp_dec_replace` own-key plaintext rewrite) applies in both Bob and Charlie cases and reduces the swap count by one in each.

## Critical files to modify

| File | Action |
|---|---|
| `information_theory/min_entropy.v` | **NEW** — `Hmin`, `Hmin_cond`, `cond_entropy_indep_extension`, `Hmin_cond_uniform_with_additive_pad` (additive-pad uniformity used by Charlie's V_2 case). |
| `information_theory/computational_entropy.v` | **NEW** — `Parameter C : forall (Y : finType), (Y -> fdist R) -> Prop` with three closure `Hypothesis`es (`C_enum`, `C_sample`, `C_fix_input`), `succ_prob`, `Hunp`, `Hunp_chain_rule`, `Hunp_ge_Hmin`, `Hunp_uniform_lower`, `ciphertext_replacement`, `ciphertext_replacement_iter`, `Hunp_dec_replace` (path-(b) own-key plaintext rewrite, stated as inequality `≥`). |
| `homomorphic_encryption/homomorphic_encryption.v` | Remove `E_enc_inde`; add `IND_CPA_RoR`; rewrite `E_enc_ce_contract` as `_eps` version. |
| `dumas2017dual/dsdp/dsdp_security.v` | Replace `H(_ \| _) = log m` with `Hunp ≥ log m - q * eps_cpa` per the closed-form section, where `q ∈ {2, 1, 0}` matches the *cross-key* ciphertext count after path-(b) rewrites (Alice / Bob / Charlie). Six theorems total. |
| `dumas2017dual/dsdp/dsdp_entropy.v` | Add `Pr_dsdp_sol_uniform_V3` (V_3-marginal companion of `Pr_dsdp_sol_uniform`, required by Theorem 2 under path (b) when `U_2 ∈ R^×`). Existing Shannon lemmas keep their statements; reused on the post-hybrid view via `cond_entropy_indep_extension`. |

## Reused existing infrastructure

- `centropy_RV`, `entropy`, `entropy_max` from `information_theory/entropy.v` — Phase 1 min-entropy bounds.
- `inde_cond_entropy` from `dumas2017dual/lib/extra_entropy.v:559` — applies on hybrid post-extension.
- `Pr_dsdp_sol_uniform` from `dsdp_entropy.v:237` — **critical-path uniformity lemma**; feeds `Hmin_cond_of_uniform` post-hybrid.
- `dsdp_centropy_uniform` from `dsdp_entropy.v:294` — Shannon-entropy consequence of the same uniformity. Not on the critical path for the Hunp bound.
- `V3_determined_centropy_v2`, `alice_view_to_cond` — Shannon-shape lemmas reused on the hybrid view.
- `centropy1_uniform_over_set` — already used by the existing proof; stays.

## Verification

1. `make information_theory/min_entropy.vo information_theory/computational_entropy.vo` compiles cleanly with no `Admitted`.
2. The new `Hunp_chain_rule`, `Hunp_uniform_lower`, `cond_entropy_indep_extension` are pure IT facts (closed under the closure axioms) — fully proved.
3. `IND_CPA_RoR`, `C`, and the three closure conditions (`C_enum`, `C_sample`, `C_fix_input`) remain as `Hypothesis`/`Parameter` declarations — these are the standard cryptographic-framework assumptions parameterizing the theorem, not hidden falsehoods. **`E_enc_inde` is gone.**
4. `make dumas2017dual/dsdp/dsdp_security.vo` compiles cleanly with the six reformulated theorems.
5. `Print Assumptions` lists per theorem (asymmetric under path (b)):
   - `dsdp_unp_security_alice_V2` (Theorem 1) lists `IND_CPA_RoR`, `C`, the three closure hypotheses (`C_enum`, `C_sample`, `C_fix_input`), the protocol's IT hypotheses including `U3_coprime_m`, and standard math axioms. **No `E_enc_inde`.**
   - `dsdp_unp_security_alice_V3` (Theorem 2) additionally lists `U2_coprime_m` (the V_3-marginal companion). Both unit-mask hypotheses are required.
   - The four Bob/Charlie theorems (3–6) drop their respective unit-mask hypotheses entirely; their `Print Assumptions` lists do not include any `U_*_coprime_m`.
6. RSSDP build is unaffected: `make weng2026/rssdp/...` still passes.
7. As a sanity check: derive Corollary A `forall (A : codom AliceView -> fdist R), C _ A -> succ_prob A AliceView V2 ≤ (1/m) * 2^(2 * eps_cpa)` directly from `dsdp_unp_security_alice_V2` (multiplicative form, immediate from the `Hunp` definition). The additive Corollary B `succ_prob A AliceView V2 ≤ 1/m + 2 * eps_cpa` is *not* a consequence of the entropy bound; if needed, prove it as a separate theorem by hop-by-hop additive accounting on the guessing probability. See the closed-form section's reading guide.

## Effort estimate

- Phase 1: ~400 lines (definitions, closure axioms, foundational lemmas including `cond_entropy_indep_extension`).
- Phase 2: ~80 lines (axiom swap; RoR-form IND-CPA).
- Phase 3: ~200 lines (`ciphertext_replacement`, iterated form).
- Phase 4: ~150 lines per theorem × 2 marginals = ~300 lines for Alice-corrupted case.
- Phase 5: similar scale × 2 = ~600 lines for Bob/Charlie cases.

Total: ~1500 LoC, no new dependencies. Larger than the initial estimate due to RoR-form IND-CPA, closure axioms, and the marginal split.

## Outstanding open questions before implementation

1. *Resolved.* The adversary class `C` is parameterized abstractly via `Parameter C : forall (Y : finType), (Y -> fdist R) -> Prop` plus three closure `Hypothesis`es (`C_enum`, `C_sample`, `C_fix_input`), as documented in Phase 1's `computational_entropy.v` block. No concrete model is instantiated in this plan. Total-functions and circuit-class instantiations are downstream, and would discharge `C` plus its three closure hypotheses into a definition with proved lemmas. *Note: the unbounded "all functions" model fails the IND-CPA RoR hypothesis (an unbounded predictor can decrypt by exhaustive search), so `C` must be a strictly proper sub-class of all kernels for the formalization to be consistent.*
2. Does the user prefer the entropy-form `Hunp ≥ log m - eps` conclusion (this plan), or the audit-recommended pure-probability form `Pr[A guess = V2] ≤ 1/m + eps`? The latter is ~half the LoC and avoids new entropy infrastructure.
3. Whether the protocol's existing `cinde_V2V3` and `cinde_V2` hypotheses (which themselves implicitly involve encryption-derived RVs through `S`) need re-examination — they are listed as "stay as Shannon hypotheses," but `S = D3 - R2 - R3 + U1 * V1` and `D3` involves encrypted intermediaries; verify they are sound under the post-hybrid view.

## References (linked from companion notes)

- `20260430-pke-impossibility-it-security.md` — why `E_enc_inde` is unsound (Diffie–Hellman, Maurer, Panny).
- Hsiao, Lu, Reyzin (Eurocrypt 2007). "Conditional Computational Entropy, or Toward Separating Pseudoentropy from Compressibility." — chain rule for unpredictability entropy (Thm 3.4).
- Krenn, Pietrzak, Wadia (TCC 2013). "A Counterexample to the Chain Rule for Conditional HILL Entropy" — why HILL is the wrong notion.
- Pietrzak, Skórski (Latincrypt 2015). "The Chain Rule for HILL Pseudoentropy, Revisited."
- Pinto, "Comparing Notions of Computational Entropy" (journal version) — landscape of computational entropy notions.
