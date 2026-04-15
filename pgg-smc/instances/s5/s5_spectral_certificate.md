# S₅ Schreier Spectral Certificate

This directory contains the hybrid verification artefacts for the S₅
adjacent-transposition Schreier walk's spectral bound.

## What is certified

For the 5×5 transition matrix Q of the random walk on `'I_5` generated
by uniform sampling of the four adjacent transpositions `(0,1), (1,2),
(2,3), (3,4)`, the certificate asserts:

> **Rayleigh bound.** For all rational 5-vectors v with
> `v_0 + v_1 + v_2 + v_3 + v_4 = 0`,
> `<v, Q² v>  ≤  α² · <v, v>`,  where `α = 181/200`.

Equivalently, the 5×5 symmetric matrix `M := α²·I - Q²` is positive
semidefinite on the mean-zero hyperplane, which pins down `‖Q v‖₂ ≤
α · ‖v‖₂` for every mean-zero v and hence `‖Q^L v‖₂ ≤ α^L · ‖v‖₂`.
Combined with the Cauchy–Schwarz bridge from L² to total-variation
distance (proved in Rocq as `cV_l1_le_sqrtN_norm2`), this gives the
conclusion consumed by `SecurityWitness`:

> `var_dist(Q^L δ_s, uniform) ≤ √5 · α^L`

In particular, at `L = 285` the bound is below `2⁻³⁸`, and at `L = 893`
below `2⁻¹²⁸`.

## Why a certificate instead of a Rocq proof

The Rayleigh bound is a universally quantified statement over rational
5-vectors. Structurally it is a polynomial identity (a sum-of-squares
decomposition), provable by `ring` or `field` in Rocq *in principle*.
In practice, the LDL^T coefficients have numerators with up to 18
decimal digits, and Rocq's tactic-level `rat` arithmetic (`ring`,
`field`, even `native_compute`) does not handle products of such
coefficients in sub-five-minute time. We empirically measured this
(see the note in `rigidity_s5_instance.v`).

The certificate decouples the two parts of the proof:

- **Structure** (what Rocq proves): every step of the chain
  Rayleigh-bound ⇒ operator-norm bound ⇒ variation-distance bound ⇒
  `SecurityWitness`, via the general mixing lemma `symm_ds_TV_bound`
  in `pgg-smc/security/pgg_mixing.v`.
- **Numerical content** (what this certificate attests): the specific
  LDL^T decomposition that witnesses positive semidefiniteness of
  `M = α²·I - Q²` on the mean-zero hyperplane.

## Contents of the certificate

Running `python3 s5_spectral_certificate.py` prints:

```
# alpha   = 181/200
# alpha^2 = 32761/40000
#
# LDL^T pivots (all strictly positive):
#   D_0 = 25261/20000
#   D_1 = 1379189363/2020880000
#   D_2 = 6421569868331/13791893630000
#   D_3 = 503998902795641/205490235786592000
#
# Lower-triangular L (unit diagonal):
#   L_10 = -37761/50522
#   L_20 = 2500/25261
#   L_21 = -1592651242/1379189363
#   L_30 = 1250/25261
#   L_31 = 347012500/1379189363
#   L_32 = -41481611773743/25686279473324
```

The script also verifies the reconstruction `L D Lᵀ = S` over the
rationals and the positivity of every pivot; both checks are integrated
into the script's assertions.

## How Rocq uses the certificate

The `Hypothesis` block in `rigidity_s5_instance.v` imports the Rayleigh
bound. `s5_mixing.v` names this hypothesis `s5_rayleigh_Qsq`, then
derives the full variation-distance bound via `symm_ds_TV_bound`. No
rational constant from the certificate is referenced symbolically by
the Rocq proof — the proof only consumes the *conclusion* of the
certificate. This keeps the trust interface minimal: a reviewer needs
to check only that the Python script's verdict matches the Hypothesis's
claim.

## Reproducibility

The script is deterministic, self-contained (no external SymPy
dependency; uses only Python's built-in `fractions`), and committed to
the repository. Any reviewer can regenerate the certificate values by
running:

```
python3 pgg-smc/instances/s5/s5_spectral_certificate.py
```

If the printed values disagree with those embedded in the `Hypothesis`
block's documentary comment in `rigidity_s5_instance.v`, the repository
is in an inconsistent state and should not be trusted until
reconciled.

## Scope

This certificate covers only the S₅ adjacent-transposition instance at
α = 181/200. Other instances (Kim, den Boer, S₅×S₅) do not use external
certificates: Kim and den Boer are fully proved in Rocq; S₅×S₅'s
spectral-side `Hypothesis` is out of scope for the current development
because the underlying walk is reducible (see audit notes in the main
project plan).
