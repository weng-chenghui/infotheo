# Wreath Z_7 wr S_2 versus S_5: records parity

A side-by-side of the wreath instance against the S_5 instance, recording which
S_5 artifacts the wreath also has. The conclusion: after the spectral-mixing and
crypto-rigidity work, the wreath matches S_5 on the security, spectral, and
rigidity-record sides. Two S_5 artifacts remain absent from the wreath for
principled reasons, and one record-type choice differs by design.

References: `rigidity_s5_instance.v`, `s5_mixing.v`, `s5_nogo.v` for S_5;
`wreath_mixing.v`, `rigidity_wreath_instance.v`, `wreath_crypto_rigidity.v`,
`wreath_recovery.v`, `wreath_security.v` for the wreath.

## Security and spectral side

| S_5 | Wreath | Status |
|---|---|---|
| `s5_security_witness_1` (fiber, L=1, eps 6/5) | `wreath_security_witness` (endpoint-injective, L=1, eps 11/7) | parity |
| `s5_alpha_R`, `s5_gap_R` and their `_ge0`/`_le1`/`_lt1`/`_pos` bounds | `wreath_alpha_R`, `wreath_gap_R` and the same bounds | parity |
| `s5_rayleigh_Qsq_R` (axiom) | `wreath_rayleigh_Qsq_R` (axiom) | parity |
| `s5_spectral_convergence_proved`, `s5_spectral_convergence_gap` | `wreath_spectral_convergence_proved`, `wreath_spectral_convergence_gap` | parity |
| `s5_asymptotic` (SecurityAsymptotic, floor 0) | `wreath_asymptotic`, `wreath_asymptotic_eps_inf_zero` | parity |
| `s5_security_witness_schreier` | `wreath_security_witness_schreier`, `wreath_security_witness_asymptotic` | parity |
| `s5_spectral_certificate.py`, `.md` | `wreath_spectral_certificate.py`, `.md` | parity |
| symmetry from generator involutivity, `path_gen_tuple_3_invol` | symmetry from multiset inverse-closure, `wreath_schreier_symm` with `wreath_gens_inv_closed` | analogue |

The symmetry row is the one place the wreath required strictly more than S_5. The
S_5 generators are involutions, so the Schreier transition is symmetric for free.
The wreath cuts are 7-cycles, so symmetry holds only after adjoining the inverse
generators, and `wreath_schreier_symm` proves it from inverse-closure rather than
involutivity. The certified mixing coefficient is `alpha = 17/20`, gap `3/20`,
wider than the S_5 gap `19/200`.

## Rigidity records

| S_5 | Wreath | Status |
|---|---|---|
| `s5_rigidity` (fiber security witness) | `wreath_rigidity` (fiber security witness) | parity |
| `s5_rigidity_cryptographically_secure` (spectral witness, L=285) | `wreath_rigidity_cryptographically_secure` (spectral witness, L=285) | parity |
| `s5_covering`, `s5_brings_covering` (genus 4) | `wreath_covering`, `wreath_covering_sym` (genus 4) | parity |
| `s5_complexity` (search space at most the group) | `wreath_complexity` | parity |
| `s5_group_order_eq` (axiom) | `card_wreath` (axiom) | parity |
| `s5_ts_recon_correct`, `s5_hurwitz`, `s5_tradeoff` | `wreath_protocol_correct`, `wreath_hurwitz`, `wreath_order_inequality_and_gap` | analogue |

`wreath_rigidity_cryptographically_secure` upgrades the rigidity record's security
certificate from the weak L=1 fiber bound to the vanishing spectral asymptotic,
exactly as the S_5 crypto-secure record does. Because the wreath spectral witness
lives on the inverse-closed presentation `M_wreath_sym`, the covering moves there
too. The covering, genus, reconstruction-invariance, and order inequality all
transfer from `M_wreath` verbatim, since `M_wreath_sym` is the same group on the
same 14-card deck with the same scheme. The record's axioms are
`wreath_rayleigh_Qsq_R` and `card_wreath` plus the standard classical axioms, the
exact mirror of the S_5 record's `s5_rayleigh_Qsq_R` and `s5_group_order_eq`.

## Items S_5 has that the wreath does not

1. **In-Rocq sum-of-squares witness data** (`s5_sos_lower_triangular`,
   `s5_sos_diagonal`, `s5_sos_diagonal_nonneg`). The S_5 version is a 4-dimensional
   echo with small entries such as 1 and 1/2. The wreath LDL factorisation is
   13-dimensional with very large rationals, for instance a smallest pivot of
   67469422196491 over 9483622022441480. Echoing roughly 91 such rationals into
   Rocq adds no proof value, since neither instance discharges its Rayleigh axiom
   from this data. The wreath certificate keeps the factorisation in Python only.

2. **The right-angled Artin word-counting chain** (`s5_search_chain`, the bound
   `search_space` at most `n_traces` at most a power of the generator count). The
   trace count `n_traces` is defined for a right-angled Artin group. Z_7 wr S_2 is
   not one: `cut1` has order 7, so the group has torsion, whereas right-angled
   Artin groups are torsion-free. The generic group bound `wreath_complexity` is
   the part that ports.

## A record-type choice that differs by design

S_5 packages its certification as `AlgebraicRigidity`, whose genus-zero PGL
obligation is discharged vacuously because the S_5 covering has genus 4. The
wreath packages its certification as `CombinatorialRigidity`, whose explicit field
`cr_genus_gt0` records the positive genus, and whose `cr_large_group_with_gap` is
the positive dual of the S_5 no-go. These are different record types over the same
underlying certification.

## Genus and the S_5 no-go

The deepest asymmetry is about genus, and it is the reason the two instances sit on
opposite sides of the same dividing line.

The S_5 wired-gap no-go `s5_wired_gap_impossible` proves that no S_5-invariant
secret-encoding algebraic-geometry code exists in the threshold-gap regime. Its
genus is not zero. The gap hypotheses run through `gap_dim_window`, which forces
`0 < g`, and at the AG-Massey relation length 6 they pin the code genus to
`g` in the set {1, 2} with code dimension `k` in {3, 4}. The no-go then shows that
even at this positive genus no S_5-invariant secret module of the required
dimension exists. So the S_5 algebraic-geometry realisation fails to exist for
`g > 0`: positive genus is necessary for a strict gap, yet the representation
theory of S_5 leaves no invariant code there.

The wreath is the positive dual. At genus 4, which is also `g > 0`,
`cr_large_group_with_gap` realises exactly the large-group-with-gap configuration
that the S_5 no-go forbids for the S_5 representation. The wreath escapes the no-go
because its reconstruction uses the abelian-core sum-mod scheme rather than an
S_5-invariant algebraic-geometry code, so the representation-theoretic obstruction
that kills the S_5 case does not apply. Both instances live in the `g > 0` world.
S_5 shows it is a dead end for its own group, and the wreath shows it is reachable
for the wreath group.
