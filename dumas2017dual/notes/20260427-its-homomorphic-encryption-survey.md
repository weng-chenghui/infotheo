# Information-Theoretically Secure Homomorphic Encryption — Web Survey

**Date:** 2026-04-27
**Question:** Does any homomorphic algorithm provide information-theoretic security (not just computational)? If not, is there a fundamental impossibility?

## Bottom line

- **Classical FHE with information-theoretic (perfect / unconditional) security is fundamentally impossible** in the standard non-interactive setting. Negative results:
  - Yu, Pérez-Delgado, Fitzsimons 2014 (PRA 90:050303(R)) — perfect ITS-QHE forces encoding size to scale with the size of the computation; in particular, universal computation needs exponential overhead.
  - Newman, Shi 2018 (QIC 18(11&12):927–948) — strengthens the inefficiency bound for ITS-QHE implementing the full set of classical reversible functions; gives a code-theoretic obstruction (no binary QECC implements a universal reversible gate set transversally).
  - Hu, Ouyang, Tomamichel 2023 (Quantum 7:976) — even for Clifford-only schemes, *data privacy + circuit privacy + correctness* cannot be simultaneously achieved.
  - Armknecht, Katzenbeisser, Peter 2013 (DCC 67(2):209–232) — structural impossibility / characterization results for group-homomorphic public-key encryption (computational setting; included for context).
- **Quantum schemes that achieve some form of information-theoretic security exist**, but only with one or more of: (a) restricted gate set, (b) accessible-information bound rather than perfect IT-security, (c) exponential overhead, (d) trade-offs against compactness or circuit privacy.
  - Tan, Kettlewell, Ouyang, Chen, Fitzsimons 2016 (Sci. Rep. 6:33467) — private-key bosonic QHE supporting the group $G_C$ of operations on spatial modes (containing BosonSampling, beam-splitters, phase-shifters). Security guarantee is a Holevo-style bound on accessible information, not perfect IT-security; gap between encoded and adversary-accessible information grows asymptotically as a constant fraction of the message length with polynomial overhead.
  - Ouyang, Tan, Fitzsimons 2018 (PRA 98:042334) — code-based private-key QHE; security is information-theoretic in the standard sense, but the scheme is restricted to circuits with a bounded number of non-Clifford gates determined by the underlying QECC.
- **Homomorphic secret sharing (HSS)** is a sibling notion that *can* be perfectly secure, but only for trivial function classes; Boyle–Gilboa–Ishai–Lin–Tessaro (ITCS 2018) prove additive HSS for any non-trivial function (even AND of two bits) implies non-interactive key exchange, so non-trivial HSS cannot be information-theoretic.

## Audited bibliography table

| # | Authors | Year | Title (short) | Venue | Provides IT-security? | Key caveat |
|---|---------|------|---------------|-------|------------------------|-----------|
| 1 | Tan, Kettlewell, Ouyang, Chen, Fitzsimons | 2016 | A quantum approach to homomorphic encryption | *Sci. Rep.* 6:33467 | Partial — Holevo / accessible-information bound, not perfect IT | Restricted to bosonic-mode operations in group $G_C$; contains BosonSampling, not universal |
| 2 | Ouyang, Tan, Fitzsimons | 2018 | Quantum homomorphic encryption from quantum codes | *Phys. Rev. A* 98:042334 | Yes (private-key, quantum, code-based) | Restricted to circuits with bounded # of non-Clifford gates determined by code distance |
| 3 | Newman, Shi | 2018 | Limitations on transversal computation through QHE | *QIC* 18(11&12):927–948 | Constructs ITS-QHE | Negative result: any ITS-QHE for full classical reversible computation is highly inefficient (exponential) |
| 4 | Yu, Pérez-Delgado, Fitzsimons | 2014 | Limitations on information-theoretically-secure QHE | *Phys. Rev. A* 90:050303(R) | — (negative) | Perfect ITS ⇒ encoding size scales with computation; exponential for universal |
| 5 | Hu, Ouyang, Tomamichel | 2023 | Privacy & correctness trade-offs for ITS-QHE | *Quantum* 7:976 | Conditional | Data privacy + circuit privacy + correctness cannot all hold simultaneously, even for Clifford circuits |
| 6 | Boyle, Gilboa, Ishai, Lin, Tessaro | 2018 | Foundations of Homomorphic Secret Sharing | ITCS 2018, LIPIcs 94, 21:1–21:21 | Mostly no | Non-trivial additive HSS implies NIKE ⇒ cannot be information-theoretic |
| 7 | Armknecht, Katzenbeisser, Peter | 2013 | Group homomorphic encryption: characterizations, impossibility results, applications | *DCC* 67(2):209–232 | — (negative) | Structural impossibilities for group-homomorphic schemes (computational setting) |

## Citation audit notes

- **#1 Tan et al. 2016**: ground truth obtained from the official PDF (DOI 10.1038/srep33467). Authors confirmed in order: Si-Hui Tan, Joshua A. Kettlewell, Yingkai Ouyang, Lin Chen, Joseph F. Fitzsimons. The paper's actual security claim is a bound on accessible information (Holevo $\chi \le \log_2 m!$), and the gate restriction is to the group $G_C$ of permutation-invariant operators on the spatial modes of $m$ bosons — NOT "constant number of non-Clifford gates." That latter description belongs to paper #2 (and to the Broadbent–Jeffery 2015 scheme).
- **#2 Ouyang–Tan–Fitzsimons 2018**: the Sci. Rep. paper itself cites this work (ref. 28) for a "stronger security definition based on trace distance." Confirms PRA 98:042334 / arXiv:1508.00938.
- **#4 Yu–Pérez-Delgado–Fitzsimons 2014**: cited in the Sci. Rep. paper (ref. 25) as the no-go theorem behind the impossibility of perfect ITS for universal computation.
- All other entries verified via journal landing pages / DBLP.

## Corrected BibTeX

```bibtex
@article{Tan2016quantumHE,
  title   = {A quantum approach to homomorphic encryption},
  author  = {Tan, Si-Hui and Kettlewell, Joshua A. and Ouyang, Yingkai and Chen, Lin and Fitzsimons, Joseph F.},
  journal = {Scientific Reports},
  volume  = {6},
  pages   = {33467},
  year    = {2016},
  doi     = {10.1038/srep33467},
  note    = {arXiv:1411.5254}
}

@article{Ouyang2018QHEcodes,
  title   = {Quantum homomorphic encryption from quantum codes},
  author  = {Ouyang, Yingkai and Tan, Si-Hui and Fitzsimons, Joseph F.},
  journal = {Physical Review A},
  volume  = {98},
  number  = {4},
  pages   = {042334},
  year    = {2018},
  doi     = {10.1103/PhysRevA.98.042334},
  note    = {arXiv:1508.00938}
}

@article{NewmanShi2018transversal,
  title   = {Limitations on Transversal Computation through Quantum Homomorphic Encryption},
  author  = {Newman, Michael and Shi, Yaoyun},
  journal = {Quantum Information and Computation},
  volume  = {18},
  number  = {11--12},
  pages   = {927--948},
  year    = {2018},
  note    = {arXiv:1704.07798}
}

@article{Yu2014limitsITSQHE,
  title   = {Limitations on information-theoretically-secure quantum homomorphic encryption},
  author  = {Yu, Li and P{\'e}rez-Delgado, Carlos A. and Fitzsimons, Joseph F.},
  journal = {Physical Review A},
  volume  = {90},
  number  = {5},
  pages   = {050303(R)},
  year    = {2014},
  doi     = {10.1103/PhysRevA.90.050303},
  note    = {arXiv:1406.2456}
}

@article{Hu2023privacycorrectness,
  title   = {Privacy and correctness trade-offs for information-theoretically secure quantum homomorphic encryption},
  author  = {Hu, Yanglin and Ouyang, Yingkai and Tomamichel, Marco},
  journal = {Quantum},
  volume  = {7},
  pages   = {976},
  year    = {2023},
  doi     = {10.22331/q-2023-04-13-976}
}

@inproceedings{BoyleGilboaIshai2018HSSfoundations,
  title     = {Foundations of Homomorphic Secret Sharing},
  author    = {Boyle, Elette and Gilboa, Niv and Ishai, Yuval and Lin, Huijia and Tessaro, Stefano},
  booktitle = {9th Innovations in Theoretical Computer Science Conference (ITCS 2018)},
  series    = {LIPIcs},
  volume    = {94},
  pages     = {21:1--21:21},
  year      = {2018},
  doi       = {10.4230/LIPIcs.ITCS.2018.21}
}

@article{Armknecht2013groupHE,
  title   = {Group homomorphic encryption: characterizations, impossibility results, and applications},
  author  = {Armknecht, Frederik and Katzenbeisser, Stefan and Peter, Andreas},
  journal = {Designs, Codes and Cryptography},
  volume  = {67},
  number  = {2},
  pages   = {209--232},
  year    = {2013},
  doi     = {10.1007/s10623-011-9601-2}
}
```

## Sources verified

- https://www.nature.com/articles/srep33467 (PDF, ground truth)
- https://arxiv.org/abs/1411.5254
- https://arxiv.org/abs/1508.00938
- https://arxiv.org/abs/1704.07798
- https://arxiv.org/abs/1406.2456
- https://quantum-journal.org/papers/q-2023-04-13-976/
- https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITCS.2018.21
- https://dblp.org/rec/journals/dcc/ArmknechtKP13.html
