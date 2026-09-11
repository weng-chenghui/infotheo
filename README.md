<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# A Rocq formalization of information theory and linear error correcting codes

## About this artifact

This repository is a fork of [Infotheo](https://github.com/affeldt-aist/infotheo),
a Rocq library for discrete probabilities, information theory, and linear
error-correcting codes (LGPL-2.1-or-later). Everything below the line
"Infotheo is a Rocq library ..." is Infotheo's own README, kept for its build
notes and bibliography. The formalization submitted with the paper lives in
the files listed in this section; every other file is unmodified Infotheo.

For this artifact all Rocq sources sit in a single flat directory, so every
file has a short unique path. `_CoqProject` maps the directory to the logical
root `infotheo`, so every `From infotheo Require Import ...` line works
unchanged.

### Files written for this work

Secure multiparty computation (interpreter, session types, security models):

- `smc_interpreter.v`, `smc_interpreter_sound.v`, `smc_session_types.v`,
  `pismc.v`, `graded_resource.v`
- `finstoch.v`, `statdist.v`, `privacy_model.v`, `party_structure.v`,
  `entropy_link.v`, `unpredictability.v`, `examples_f3.v`, `spp_bridge.v`

Homomorphic encryption (additive schemes, Paillier, Benaloh, residuosity games):

- `key_type.v`, `he_types.v`, `enc_dec.v`, `ahe_enc.v`, `ahe_monoid.v`,
  `homomorphic_encryption.v`, `residuosity_game.v`, `idealized_ahe.v`
- `paillier_enc.v`, `paillier_ahe.v`, `paillier_fdist_instance.v`
- `benaloh_enc.v`, `benaloh_ahe.v`

Computational security (negligible functions, IND-CPA games, hopping):

- `negligible.v`, `indcpa_game.v`, `indcpa_scheme_sequence.v`,
  `idealized_indcpa_scheme.v`, `epshop.v`, `epshop_sequence.v`
- `paillier_indcpa_scheme.v`, `benaloh_indcpa_scheme.v`

The DSDP protocol (dual scalar-product protocol of Dumas et al., 2017):

- Protocol and interpreter: `dsdp_interface.v`, `dsdp_session_types.v`,
  `dsdp_program.v`, `dsdp_pismc.v`, `dsdp_pismc_idealized.v`,
  `dsdp_correctness.v`
- Information-theoretic counting: `dsdp_entropy_trace.v`,
  `dsdp_random_inputs.v`, `dsdp_entropy.v`, `dsdp_relay_secrecy.v`,
  `dsdp_malicious_dotp.v`
- Game hopping for Alice: `dsdp_instance.v`, `dsdp_alice_hop_secrecy.v`,
  `dsdp_alice_trace_link.v`, `dsdp_alice_instances.v`, `dsdp_alice_main.v`
- Fiber counting and linear algebra: `entropy_fiber.v`,
  `entropy_fiber_zpq.v`, `linear_fiber_zpq.v`, `rouche_capelli.v`,
  `extra_algebra.v`, `extra_proba.v`, `extra_entropy.v`

The scalar-product protocol of Du and Zhan, 2002 (the earlier case study the
DSDP development builds on):

- `spp_tactics.v`, `spp_proba.v`, `spp_entropy.v`, `spp_interface.v`,
  `spp_program.v`, `spp_pismc.v`, `spp_proof.v`, `spp_simulator.v`,
  `spp_session_types.v`

### Infotheo files extended by this work

These upstream files received new lemmas (conditional independence,
conditional entropy, random-variable transport); the rest of each file is
Infotheo's.

- `proba.v`, `fdist.v`, `fdist_extra.v` (new), `jfdist_cond.v`,
  `entropy.v`, `realType_ln.v`, `robustmean.v`

### Files cited in the paper

The paper cites Rocq identifiers by file. The table maps each file name used
in the paper to the file in this directory.

| Name in the paper | File in this directory |
|---|---|
| `smc_interpreter.v` | `smc_interpreter.v` |
| `smc_interpreter_sound.v` | `smc_interpreter_sound.v` |
| `smc_session_types.v` | `smc_session_types.v` |
| `he_types.v` | `he_types.v` |
| `enc_dec.v` | `enc_dec.v` |
| `paillier_enc.v` | `paillier_enc.v` |
| `benaloh_enc.v` | `benaloh_enc.v` |
| `indcpa_game.v` | `indcpa_game.v` |
| `dsdp_interface.v` | `dsdp_interface.v` |
| `dsdp_pismc.v` | `dsdp_pismc.v` |
| `dsdp_entropy.v` | `dsdp_entropy.v` |
| `dsdp_relay_secrecy.v` | `dsdp_relay_secrecy.v` |
| `dsdp_alice_hop_secrecy.v` | `dsdp_alice_hop_secrecy.v` |
| `dsdp_alice_trace_link.v` | `dsdp_alice_trace_link.v` |
| `dsdp_alice_main.v` | `dsdp_alice_main.v` |

Identifiers the paper cites without naming a file are found with
`grep -n "Lemma <name>\|Definition <name>" *.v` in this directory.

### Building with Docker

The image installs the Rocq toolchain and the MathComp dependencies at build
time. Running the container compiles the whole development, Infotheo and the
files above, with `make`.

```shell
docker build -t infotheo-artifact .
docker run infotheo-artifact
```

The build stage installs the dependencies pinned in `rocq-infotheo.opam`
(Rocq 9.0.0, MathComp 2.5.0, MathComp Analysis 1.15.0, Hierarchy Builder 1.10.1,
CoqInterval 4.11.3, robot 0.3.1; every version is pinned exactly)
and takes well over an hour on a laptop. The run stage compiles every file in
`_CoqProject`. A successful run ends with `make` exiting with status 0 and no
`Error` line in the output. To keep the compiled files, mount a volume or run
the container with a shell:

```shell
docker run -it infotheo-artifact sh
opam exec -- make -j"$(nproc)"
```

To build without Docker, follow "Without Docker (using opam)" below with the
same opam file.

---


[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/affeldt-aist/infotheo/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/affeldt-aist/infotheo/actions/workflows/docker-action.yml




## Artifact Verification

### With Docker

Build the image and verify the artifact:

```shell
docker build -t infotheo-artifact .
docker run infotheo-artifact
```

### Without Docker (using opam)

Install [opam](https://opam.ocaml.org/doc/Install.html) (version 2.x) if you
do not already have it, then run:

```shell
opam switch create infotheo ocaml-base-compiler.4.14.2
eval $(opam env --switch=infotheo)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install --deps-only -y ./rocq-infotheo.opam
make
```

---

Infotheo is a Rocq library for reasoning about discrete probabilities,
information theory, and linear error-correcting codes.

## Meta

- Author(s):
  - Anonymous
- License: [LGPL-2.1-or-later](LICENSE)
- Additional dependencies:
  - [MathComp ssreflect](https://math-comp.github.io)
  - [MathComp fingroup](https://math-comp.github.io)
  - [MathComp algebra](https://math-comp.github.io)
  - [MathComp solvable](https://math-comp.github.io)
  - [MathComp field](https://math-comp.github.io)
  - [MathComp analysis](https://github.com/math-comp/analysis)
  - [MathComp analysis reals standard library](https://github.com/math-comp/analysis)
  - [Hierarchy Builder](https://github.com/math-comp/hierarchy-builder)
  - [Hierarchy Builder](https://github.com/math-comp/hierarchy-builder)
  - [MathComp algebra tactics](https://github.com/math-comp/algebra-tactics)
  - [CoqInterval](https://gitlab.inria.fr/coqinterval)
- Rocq/Coq namespace: `infotheo`
- Related publication(s):
  - [An Approach to Formalize Information-Theoretic Security of Multiparty Computation Protocols](https://link.springer.com/chapter/10.1007/978-3-031-95497-9_11) doi:[10.1007/978-3-031-95497-9_11](https://doi.org/10.1007/978-3-031-95497-9_11)
  - [Robust Mean Estimation by All Means (short paper)](https://drops.dagstuhl.de/storage/00lipics/lipics-vol309-itp2024/LIPIcs.ITP.2024.39/LIPIcs.ITP.2024.39.pdf) doi:[10.4230/LIPIcs.ITP.2024.39](https://doi.org/10.4230/LIPIcs.ITP.2024.39)
  - [Trimming Data Sets: a Verified Algorithm for Robust Mean Estimation](https://dl.acm.org/doi/abs/10.1145/3479394.3479412) doi:[10.1145/3479394.3479412](https://doi.org/10.1145/3479394.3479412)
  - [Formal Adventures in Convex and Conical Spaces](https://arxiv.org/abs/2004.12713) doi:[10.1007/978-3-030-53518-6_2](https://doi.org/10.1007/978-3-030-53518-6_2)
  - [A Library for Formalization of Linear Error-Correcting Codes](https://link.springer.com/article/10.1007/s10817-019-09538-8) doi:[10.1007/s10817-019-09538-8](https://doi.org/10.1007/s10817-019-09538-8)
  - [Reasoning with Conditional Probabilities and Joint Distributions in Coq](https://www.jstage.jst.go.jp/article/jssst/37/3/37_3_79/_article/-char/en) doi:[10.11309/jssst.37.3_79](https://doi.org/10.11309/jssst.37.3_79)
  - Examples of formal proofs about data compression, doi:[10.23919/ISITA.2018.8664276](https://doi.org/10.23919/ISITA.2018.8664276)
  - Formalization of Reed-Solomon codes and progress report on formalization of LDPC codes
  - Formalization of error-correcting codes---from Hamming to modern coding theory, doi:[10.1007/978-3-319-22102-1_2](https://doi.org/10.1007/978-3-319-22102-1_2)
  - [Formalization of Shannon’s Theorems](https://link.springer.com/article/10.1007%2Fs10817-013-9298-1) doi:[10.1007/s10817-013-9298-1](https://doi.org/10.1007/s10817-013-9298-1)

## Building and installation instructions

The easiest way to install the latest released version of A Rocq formalization of
information theory and linear error correcting codes
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-infotheo
```

To instead build and install manually, do (using GNU `make`):

``` shell
git clone https://github.com/affeldt-aist/infotheo.git
cd infotheo
make   # or make -j <number-of-cores-on-your-machine>
make -C extraction tests
make install
```

## Acknowledgments

Removed for anonymous review.

## Documentation

Each file is documented in its header.

Changes are (lightly) documented in [changelog.txt](changelog.txt).

## Installation with Windows 10 & 11

Installation of infotheo on Windows is less simple.
See [this page](https://github.com/affeldt-aist/mathcomp-install/blob/master/install-windows-en.org)
for instructions to install MathComp on Windows 10 & 11
(or this page for instructions in Japanese).


Once MathComp is installed (with opam), do
`opam install coq-infotheo` or `git clone git@github.com:affeldt-aist/infotheo.git; opam install .`
