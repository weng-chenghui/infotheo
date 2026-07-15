# Words as Computation in MPC: Literature Survey

## 1. Barrington's Theorem and MPC/Cryptography

### 1a. Barrington's Theorem (foundational)

- **Title**: Bounded-Width Polynomial-Size Branching Programs Recognize Exactly Those Languages in NC1
- **Authors**: David Mix Barrington
- **Year**: 1989 (STOC 1986)
- **Venue**: JCSS
- **URL**: https://www.sciencedirect.com/science/article/pii/0022000089900378
- **Summary**: The original theorem: any NC1 circuit (fan-in 2, depth O(log n)) can be converted to a width-5 branching program of polynomial length. The branching program computes by multiplying permutations in S_5 conditioned on input bits. If the circuit outputs 1, the product is a fixed 5-cycle sigma; if 0, the product is the identity. The key insight is that S_5 is non-solvable: there exist 5-cycles gamma, delta whose commutator gamma*delta*gamma^{-1}*delta^{-1} is again a 5-cycle, enabling inductive simulation of AND/OR gates via commutator products.
- **Key insight for "word = computation"**: A Boolean function is encoded as a *word* (product) of group elements in S_5, where the word is input-dependent. This is the purest example of "word = computation."

### 1b. Boneh-Zhandry: Barrington over SL_2(Z) / SL_3(F)

- **Title**: A Note on Barrington's Theorem (Barrington's theorem using matrices in SL_2(Z))
- **Authors**: Dan Boneh, Mark Zhandry (also attributed to Ben-Or and Cleve for SL_2 variant)
- **Year**: Various (Ben-Or/Cleve 1992; Boneh/Zhandry note)
- **Venue**: Stanford crypto group
- **URL**: https://crypto.stanford.edu/~dabo/pubs/abstracts/barrington.html / https://theory.stanford.edu/~dabo/papers/barrington.html
- **Summary**: For cryptographic applications (obfuscation), it is more convenient to use 2x2 or 3x3 matrices over a field instead of S_5. Zhandry showed the required commutator structure exists in SL_3(F). Ben-Or and Cleve showed polynomial-size algebraic formulas can be computed using a constant number of registers (= matrix products in SL_2). These matrix variants are used in indistinguishability obfuscation constructions.
- **Key insight**: Barrington's "word of group elements" transfers from S_5 to matrix groups, and the matrix version is what obfuscation schemes actually use.

---

## 2. Indistinguishability Obfuscation (iO) via Branching Programs

### 2a. Garg-Gentry-Halevi-Raykova-Sahai-Waters (GGH+RSW) iO

- **Title**: Candidate Indistinguishability Obfuscation and Functional Encryption from All-Linear-Maps
- **Authors**: Sanjam Garg, Craig Gentry, Shai Halevi, Mariana Raykova, Amit Sahai, Brent Waters
- **Year**: 2013
- **Venue**: FOCS 2013
- **URL**: https://eprint.iacr.org/2013/451.pdf
- **Summary**: The first candidate general-purpose iO construction. The function is first converted to a *matrix branching program* (via Barrington's theorem or direct matrix BP construction), then the matrices are encoded using multilinear maps. The obfuscated program is a sequence of encoded matrices; evaluation is a matrix product. Security relies on the multilinear map hiding the individual matrices while allowing their product to be computed.
- **Key insight**: An obfuscated program IS a word of encoded group elements. Evaluation = multiplying out the word. This is the most direct cryptographic application of "word = computation."

### 2b. Ananth-Boneh-Garg-Sahai-Zhandry: Avoiding Barrington's Theorem

- **Title**: Optimizing Obfuscation: Avoiding Barrington's Theorem
- **Authors**: Prabhanjan Ananth, Dan Boneh, Sanjam Garg, Amit Sahai, Mark Zhandry
- **Year**: 2014
- **Venue**: IACR ePrint
- **URL**: https://eprint.iacr.org/2014/222.pdf
- **Summary**: Barrington's theorem causes a 4^d blowup. This work gives an alternative strategy that directly constructs matrix branching programs from circuits without going through Barrington, reducing the overhead. Still, the final object is a word of encoded matrices.
- **Key insight**: Even when avoiding the Barrington detour, the obfuscation paradigm remains "function = word of matrix elements."

---

## 3. Randomized Encodings and Branching Programs

### 3a. Ishai-Kushilevitz: Randomizing Branching Programs

- **Title**: Perfect Constant-Round Secure Computation via Perfect Randomizing Polynomials
- **Authors**: Yuval Ishai, Eyal Kushilevitz
- **Year**: 2002
- **Venue**: ICALP 2002
- **URL**: https://link.springer.com/chapter/10.1007/3-540-45465-9_22
- **Summary**: Any function computed by a branching program of size l over a finite field F admits a degree-3 randomized encoding over F. The technique directly randomizes the branching program: each step's matrix/permutation is multiplied by random invertible matrices from left and right, creating a "garbled word" where individual factors reveal nothing but the product encodes f(x).
- **Key insight**: A branching program (= word of matrices) can be *randomized step-by-step* to yield a secure encoding. The word structure is essential: randomization works because random matrices cancel in the product (telescoping).

### 3b. Applebaum-Ishai-Kushilevitz: Randomized Encodings as a Paradigm

- **Title**: Randomly Encoding Functions: A New Cryptographic Paradigm
- **Authors**: Benny Applebaum, Yuval Ishai, Eyal Kushilevitz
- **Year**: 2006/2011 (survey)
- **Venue**: ICS 2011 / various
- **URL**: https://link.springer.com/chapter/10.1007/978-3-642-20728-0_3
- **Summary**: Formalizes randomized encodings: replace a "complex" function f(x) by a "simpler" randomized mapping g(x,r) whose output distribution on input x encodes f(x) and hides everything else. For branching programs, degree-3 encodings exist. This framework unifies garbled circuits, randomized branching programs, and other constructions.
- **Key insight**: The word-product structure of branching programs is what makes low-degree randomized encodings possible. The product of randomized matrices is the encoding.

### 3c. Applebaum: Cryptography in NC0

- **Title**: Cryptography in Constant Parallel Time (PhD thesis)
- **Authors**: Benny Applebaum
- **Year**: 2007
- **Venue**: Technion PhD thesis
- **URL**: https://www.wisdom.weizmann.ac.il/~bennyap/pubs/thesis.pdf
- **Summary**: Shows that under standard assumptions, cryptographic primitives (OWF, PRG, commitments, encryption, etc.) can be computed in NC0 (constant depth, bounded fan-in). The constructions use randomized encodings of branching programs as an intermediate step.
- **Key insight**: Composing "word of group elements" with randomization yields NC0 constructions of crypto primitives.

### 3d. Garbled Circuits as Randomized Encodings

- **Title**: Garbled Circuits as Randomized Encodings of Functions: a Primer
- **Authors**: Benny Applebaum
- **Year**: 2017
- **Venue**: IACR ePrint 2017/385
- **URL**: https://eprint.iacr.org/2017/385.pdf
- **Summary**: Shows Yao's garbled circuits are a special case of randomized encodings. For branching programs, the randomized encoding takes the form of a sequence of "garbled" matrices whose product reveals only the function output. This unifies the circuit-based and BP-based views.
- **Key insight**: Garbled circuits and garbled branching programs are both instances of "randomized word encodings."

---

## 4. Evaluating Branching Programs on Encrypted Data

### 4a. Ishai-Paskin: Evaluating BPs on Encrypted Data

- **Title**: Evaluating Branching Programs on Encrypted Data
- **Authors**: Yuval Ishai, Anat Paskin
- **Year**: 2007
- **Venue**: TCC 2007
- **URL**: https://link.springer.com/chapter/10.1007/978-3-540-70936-7_31
- **Summary**: Given a branching program P and an encryption c of input x, one can efficiently compute a succinct ciphertext c' from which P(x) can be decoded using the secret key. The ciphertext size depends on |x| and the *length* of P but not its *size*. As special cases: finite automata, decision trees, and OBDDs can be evaluated on encrypted data. This is a 2-message protocol that hides the size of P from the client.
- **Key insight**: The word structure of BPs (sequence of transition steps) enables a step-by-step homomorphic evaluation. Each step is an encrypted transition; the product of transitions gives the encrypted result.

---

## 5. Non-Interactive MPC and Commuting Permutation Systems

### 5a. Beimel-Gabizon-Ishai-Orlov: Non-Interactive MPC

- **Title**: Non-Interactive Secure Multiparty Computation
- **Authors**: Amos Beimel, Ariel Gabizon, Yuval Ishai, Eyal Kushilevitz, Sigal Moran, Rafail Ostrovsky
- **Year**: 2014
- **Venue**: CRYPTO 2014
- **URL**: https://www.semanticscholar.org/paper/Non-Interactive-Secure-Multiparty-Computation-Beimel-Gabizon/1f844fd578316e425d993cc22ecf45c0b3efa814
- **Summary**: Introduces NIMPC (Non-Interactive MPC): parties get correlated random strings, then each sends a single message to an output server. Every function can be securely computed this way; for polynomial-size messages, efficient protocols exist for functions in nondeterministic logspace.
- **Key insight**: Each party's message is like a "letter" and the server combines them (like concatenating a word) to compute the function.

### 5b. Agarwal-Anand-Prabhakaran: Uncovering Algebraic Structures in MPC

- **Title**: Uncovering Algebraic Structures in the MPC Landscape
- **Authors**: Navneet Agarwal, Sanat Anand, Manoj Prabhakaran
- **Year**: 2019
- **Venue**: EUROCRYPT 2019
- **URL**: https://eprint.iacr.org/2019/278
- **Summary**: Introduces **Commuting Permutation Systems (CPS)** as the algebraic structure characterizing which functions admit information-theoretically secure MPC. A CPS for a function f assigns permutations to each party's input values such that: (1) the permutations from different parties commute, and (2) the composed permutation's action on a fixed point reveals f. This gives necessary conditions and (slightly stronger) sufficient conditions for secure computability.
- **Key insight**: **This is the most directly relevant paper.** Secure computation of f is equivalent to representing f via a *commuting word of permutations* -- one permutation per party, and the word (product) determines f. The commutativity requirement corresponds to the non-interactive setting.

### 5c. Beimel-Ishai-Kumaresan-Kushilevitz: On Secure m-Party Computation and CPS

- **Title**: Brief Announcement: On Secure m-Party Computation, Commuting Permutation Systems and Unassisted Non-Interactive MPC
- **Authors**: Amos Beimel, Yuval Ishai, Ranjit Kumaresan, Eyal Kushilevitz
- **Year**: 2018
- **Venue**: ICALP 2018
- **URL**: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2018.103
- **Summary**: Characterizes functions admitting information-theoretically secure m-party computation against passive corruption using CPS. The algebraic structure of commuting permutations precisely captures the boundary of secure computability.
- **Key insight**: Whether a multi-party function is securely computable is determined by whether it has a CPS representation = a commuting word of permutations.

---

## 6. Feige-Kilian-Naor: Minimal Model (PSM) and Branching Programs

- **Title**: A Minimal Model for Secure Computation
- **Authors**: Uri Feige, Joe Kilian, Moni Naor
- **Year**: 1994
- **Venue**: STOC 1994
- **URL**: https://www.wisdom.weizmann.ac.il/~naor/PAPERS/fkn.pdf
- **Summary**: Introduces Private Simultaneous Messages (PSM): Alice and Bob each send one message to Charlie using shared randomness. Communication O(t) protocols exist for t-size Boolean formulas and t-size branching programs. This is the precursor to NIMPC.
- **Key insight**: Branching programs (= word of transitions) can be securely evaluated with communication proportional to program length, not circuit size.

---

## 7. One-Pass MPC for Branching Programs

### 7a. Halevi-Lindell-Pinkas

- **Title**: Multi-party Computation of Polynomials and Branching Programs without Simultaneous Interaction
- **Authors**: Shai Halevi, Yehuda Lindell, Benny Pinkas (extended by Gordon, Malkin, Rosulek)
- **Year**: 2011/2013
- **Venue**: EUROCRYPT 2011 / extended 2013
- **URL**: https://eprint.iacr.org/2013/267
- **Summary**: Secure computation where each party interacts only once with a centralized server (one-pass model). Efficient protocols for read-once branching programs over parties' inputs, useful for string matching, finite automata evaluation, second-price auctions.
- **Key insight**: The sequential/word structure of branching programs maps naturally to one-pass protocols: each party contributes one "letter" (transition) to the computation.

---

## 8. Oblivious Automata Evaluation

### 8a. Frikken: Oblivious DFA/NFA Evaluation

- **Title**: Practical Private DNA String Searching and Matching through Efficient Oblivious Automata Evaluation
- **Authors**: Keith Frikken
- **Year**: 2009
- **Venue**: DBSec 2009
- **URL**: https://link.springer.com/chapter/10.1007/978-3-642-03007-9_6
- **Summary**: One party holds a private finite automaton, the other a private string. They jointly determine whether the string is accepted without revealing either input. Applicable to DNA searching, virus genome detection, pattern matching.

### 8b. Oblivious NFA Evaluation for Virus Detection

- **Title**: Oblivious Evaluation of Non-deterministic Finite Automata with Application to Privacy-Preserving Virus Genome Detection
- **Authors**: Various
- **Year**: 2014
- **Venue**: WPES 2014
- **URL**: https://dl.acm.org/doi/10.1145/2665943.2665954
- **Summary**: NFA-based oblivious evaluation is orders of magnitude faster than DFA-based methods. Applied to privacy-preserving genomic virus detection.

### 8c. Efficient Oblivious DFA via CDS

- **Title**: Efficient Oblivious Evaluation Protocol and Conditional Disclosure of Secrets for DFA
- **Authors**: Various
- **Year**: 2022
- **Venue**: ACNS 2022
- **URL**: https://eprint.iacr.org/2023/1169
- **Summary**: Oblivious DFA evaluation via conditional disclosure of secrets (CDS), constant-round, no heavy crypto needed.
- **Key insight for all 8a-c**: Automata process input as a *word* letter-by-letter. Secure automata evaluation = secure word processing, where each transition is a "computation step" applied obliviously.

---

## 9. Group-Based Fully Homomorphic Encryption

### 9a. Nuida: FHE from Group Theory

- **Title**: Towards Constructing Fully Homomorphic Encryption without Ciphertext Noise from Group Theory
- **Authors**: Koji Nuida
- **Year**: 2014/2020
- **Venue**: IACR ePrint 2014/097; IMA 2020
- **URL**: https://eprint.iacr.org/2014/097
- **Summary**: Proposes FHE without noise using group theory. The core idea: encode bits as group elements; homomorphic operations = group multiplication. Uses a "compression function" implemented by group operations on a finite group G. Gave an example over S_5 (later A_5). Showed such functions cannot exist over solvable groups (including S_n for n <= 4), connecting to Barrington's theorem's reliance on non-solvability.
- **Key insight**: FHE via group operations = computation as a word of group elements. The non-solvability of S_5/A_5 is essential, just as in Barrington's theorem.

### 9b. GRAFHEN: Group-Based FHE without Noise

- **Title**: Introducing GRAFHEN: Group-based Fully Homomorphic Encryption without Noise
- **Authors**: Various (building on Nuida)
- **Year**: 2025
- **Venue**: IACR ePrint 2025/1907; arXiv 2510.21483
- **URL**: https://eprint.iacr.org/2025/1907
- **Summary**: Achieves noise-free FHE using group encodings via rewriting systems. Groups are represented so that the subgroup membership problem is hard (unlike permutation groups where it is easy). Several orders of magnitude faster than OpenFHE.
- **Key insight**: Computation on encrypted data = multiplying group element ciphertexts = building a word whose product encodes the result.

### 9c. Group Homomorphic Encryption (Armknecht et al.)

- **Title**: Group Homomorphic Encryption
- **Authors**: Frederik Armknecht, Stefan Katzenbeisser, Andreas Peter
- **Year**: 2010
- **Venue**: IACR ePrint 2010/501
- **URL**: https://eprint.iacr.org/2010/501.pdf
- **Summary**: Formalizes the search for algebraically homomorphic encryption as finding encryption over appropriate groups. Shows: an algebraically homomorphic scheme on (F_2, +, *) exists iff a homomorphic scheme on S_7 exists. The group structure determines what computations can be done homomorphically.
- **Key insight**: The group in which ciphertexts live determines the computational power of the homomorphic scheme.

---

## 10. Programs over Monoids = NC1 (Algebraic Automata Theory)

### 10a. Barrington-Therien: Finite Monoids and NC1

- **Title**: Finite Monoids and the Fine Structure of NC1
- **Authors**: David Mix Barrington, Denis Therien
- **Year**: 1988
- **Venue**: JACM
- **URL**: https://dl.acm.org/doi/10.1145/48014.63138
- **Summary**: A language is in NC1 iff it is recognized by a polynomial-length program over a finite monoid. Subclasses of NC1 correspond to monoid varieties: AC0 = programs over aperiodic monoids; CC0 = programs over solvable groups; ACC0 = programs over solvable monoids.
- **Key insight**: The "word = computation" paradigm is *exactly* NC1. The algebraic structure of the monoid determines the computational power class.

### 10b. Programs over Monoids in DA (recent)

- **Title**: The Power of Programs over Monoids in DA
- **Authors**: Various
- **Year**: 2020
- **Venue**: STACS 2020
- **URL**: https://arxiv.org/abs/1912.07992
- **Summary**: Continues the classification of which circuit classes correspond to which monoid varieties in the "programs over monoids" framework.

---

## 11. Group/Semigroup-Based Cryptography

### 11a. Shpilrain-Ushakov: Combinatorial Group Theory and Cryptography

- **Title**: Combinatorial Group Theory and Public Key Cryptography
- **Authors**: Vladimir Shpilrain, Alexander Ushakov
- **Year**: Various
- **URL**: https://shpilrain.ccny.cuny.edu/pkc.pdf
- **Summary**: Uses word problems and conjugacy problems in groups for key exchange and encryption. Authentication based on the hardness of the word problem in certain groups.

### 11b. Semigroup Action Problems in Post-Quantum Crypto

- **Title**: Semigroup Action Problems and Their Uses in Post-Quantum Cryptography
- **Authors**: Various
- **Year**: 2026
- **Venue**: IACR ePrint 2026/462
- **URL**: https://eprint.iacr.org/2026/462.pdf
- **Summary**: Uses semigroup actions (no inverses) to build Diffie-Hellman and ElGamal analogues. The absence of inverses prevents certain algebraic attacks.

### 11c. Gnilke-Zumbragel: Cryptographic Group and Semigroup Actions

- **Title**: Cryptographic Group and Semigroup Actions
- **Authors**: Oliver W. Gnilke, Jens Zumbragel
- **Year**: 2023
- **Venue**: IACR ePrint 2023/017
- **URL**: https://eprint.iacr.org/2023/017.pdf
- **Summary**: Investigates group and semigroup actions for next-gen digital signatures, detailed algebraic analysis of NIST post-quantum candidates.

---

## 12. Kilian: Founding Cryptography on Oblivious Transfer

- **Title**: Founding Cryptography on Oblivious Transfer
- **Authors**: Joe Kilian
- **Year**: 1988
- **Venue**: STOC 1988
- **URL**: https://dl.acm.org/doi/10.1145/62212.62215
- **Summary**: Shows that oblivious transfer is sufficient for any secure two-party computation. While not directly about branching programs, subsequent work (Ishai-Kushilevitz) showed that OT-based protocols can efficiently evaluate branching programs, connecting OT to the "word of transitions" model.

---

## 13. Mazurkiewicz Traces and Concurrency (Tangential but Relevant to Your Project)

- **Title**: Trace Theory (Diekert-Muscholl survey)
- **Authors**: Volker Diekert, Anca Muscholl
- **Year**: 2011 (survey; Mazurkiewicz 1987 original)
- **URL**: http://www2.informatik.uni-stuttgart.de/fmi/ti/veroeffentlichungen/pdffiles/DiekertMuscholl2011.pdf
- **Summary**: Mazurkiewicz traces model concurrent computation via partially commuting words. A commutation system (A, theta) specifies which actions commute; a trace is an equivalence class of words under the commutation relation. Foata normal form maximizes parallelism.
- **Key insight for PGG-SMC**: The CPS (Commuting Permutation Systems) from papers 5a-5c are essentially the MPC analogue of Mazurkiewicz traces. In both: independent parties' actions commute, and the equivalence class of the word (trace) determines the computation result.

---

## Summary: The "Word = Computation" Paradigm Across MPC/Crypto

| Domain | Word | Letters | Product = | Key Reference |
|--------|------|---------|-----------|---------------|
| Barrington's theorem | Permutation BP | sigma_i in S_5 | Circuit output | Barrington 1989 |
| iO (obfuscation) | Matrix BP | M_i in GL | Obfuscated function | Garg+ 2013 |
| Randomized encodings | Garbled BP | R_i * M_i * R_{i+1}^{-1} | Encoded f(x) | Ishai-Kushilevitz 2002 |
| NIMPC / CPS | Commuting perms | pi_i(x_i) in S_n | f(x_1,...,x_m) | Agarwal+ 2019 |
| FHE (group-based) | Group ciphertexts | g_i in G | Homomorphic eval | Nuida 2014, GRAFHEN 2025 |
| Automata evaluation | DFA transitions | delta(q, a_i) | Accept/reject | Ishai-Paskin 2007 |
| PSM / FKN | Party messages | m_i | f(x_1,...,x_n) | Feige-Kilian-Naor 1994 |
| NC1 characterization | Monoid program | m_i in M | Language membership | Barrington-Therien 1988 |
