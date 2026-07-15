# Installation

## With Docker

Build the image and verify the artifact:

```shell
docker build -t infotheo-artifact .
docker run infotheo-artifact
```

## Without Docker (using opam)

Install [opam](https://opam.ocaml.org/doc/Install.html) (version 2.x) if you
do not already have it, then run:

```shell
opam switch create infotheo ocaml-base-compiler.4.14.2
eval $(opam env --switch=infotheo)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install --deps-only -y ./coq-infotheo.opam
make
```
