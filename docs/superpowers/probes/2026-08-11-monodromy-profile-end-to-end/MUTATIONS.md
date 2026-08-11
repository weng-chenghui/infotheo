# Mutation ledger

Every probe's perturbed twin, its expected failure, and the observed error.
A probe that would compile anyway proves nothing; these are the failures that
license trusting the green files.

## P-A: `probe_a_mutation.v` — carrier mismatch on the content readout

Perturbation: the PGL instantiation of the generic constructions, with the
content readout swapped for den Boer's `den_boer_layout`-based readout while the
carrier stays `pgl27_profile R`.

Expected: elaboration rejects the cross-carrier readout.

Observed (verified 2026-08-11 by direct `rocq compile`, exit 1, no `.vo`):

```
File ".../probe_a_mutation.v", line 96, characters 58-67:
Error:
In environment
R : realType
w0 : pgg_gT pgl27_M
mpP := pgl27_profile R : MonodromyProfile R
committed : seq 'I_(pgg_N' (mp_M mpP)).+1
The term "committed" has type "seq 'I_(pgg_N' (mp_M mpP)).+1"
while it is expected to have type "seq 'I_(pgg_N' FiveCardKim_M).+1".
```

Interpretation: the generic definitions are carrier-constraining, not vacuously
polymorphic; the mismatch fires on the readout's ARGUMENT (the committed-card
list), one elaboration step before the readout body is applied.

## P-B: `probe_b_mutation.v` — bridge 1 across two carriers

Perturbation: bridge 1 (players vs shares) demanded between the PGL(2,7)
interface (8 seats) and the five-card scheme (5 shares), discharged by `erefl`.

Expected: `erefl` rejected; if it were accepted the bridge would carry no
information and the casts of `probe_b_count_bridge.v` would be vacuous.

Observed (verified 2026-08-11 by direct `rocq compile`, exit 1, no `.vo`):

```
File ".../probe_b_mutation.v", line 23, characters 69-74:
Error:
The term "erefl" has type "pi_T' pgl27_PI = pi_T' pgl27_PI"
while it is expected to have type "pi_T' pgl27_PI = ts_T' fcI_scheme"
(cannot unify "pi_T' pgl27_PI" and "ts_T' fcI_scheme").
```

Interpretation: the count bridges are informative hypotheses — they hold by
computation at matched carriers (both `erefl` in the green file) and are
refutable at mismatched ones, so the mismatch mutation demanded by request 7.4
fails exactly at the bridge, not downstream.

## P-C: `probe_c_mutation.v` — adapter fuel against a landed run

Perturbation: the PGL(2,7) execution adapter of `probe_c_pgl27_exec.v` with
`ep_fuel := 1` in place of `pgl27_fuel = 220`, all other fields unchanged, then
the same transport of `pgl27_run_terminates`.

Expected: the process equality `epp_procs = pgl27_procs` still holds, since the
process list does not mention the fuel, and the termination transport is
rejected.

Observed (verified 2026-08-11 by direct `rocq compile`, exit 1, no `.vo`):

```
File ".../probe_c_mutation.v", line 137, characters 52-57:
Error:
In environment
R : realType
mpP := pgl27_profile R : MonodromyProfile R
s : bool
w0 : pgg_gT pgl27_M
The term "erefl" has type "ep_fuel mut_epp = ep_fuel mut_epp"
while it is expected to have type "ep_fuel mut_epp = pgl27_fuel"
(cannot unify "ep_fuel mut_epp" and "pgl27_fuel").
```

Interpretation: the adapter's fuel is load-bearing for the run facts and inert
for the process list, which is the split the green file relies on. The
transport is staged through the fuel equation `ep_fuel mut_epp = pgl27_fuel`
because the direct step `exact: pgl27_run_terminates` does not fail at a
mismatched fuel: conversion unfolds `run_interp 1` and `run_interp 220` on the
ten-process list and does not return, measured at over 180 s under rocq-mcp
against 36 ms for the matched-fuel transport. A red mutation must therefore
make the fuel mismatch a statement-level equation, and any later probe
transporting a landed run fact must pin the fuel before applying the landed
lemma.

## P-D: `probe_d_mutation.v` — input parties dropped

Perturbation: the five-card adapter of `probe_d_fivecard_exec.v` with
`ep_input_procs := fun _ => [::]` (the two committing parties removed), all
other fields and the whole proof script unchanged.

Expected: the process-list equality against `den_boer_procs` fails fast on the
structural 7-vs-9 mismatch, without evaluating any process body.

Observed (verified 2026-08-11 by direct `rocq compile`, exit 1, no `.vo`):

```
File ".../probe_d_mutation.v", line 149, characters 0-30:
Error: No applicable tactic.
```

Line 149 is `by rewrite fc_epp_bad_playersE.`, the step that closes the green
file. Timing: 31 ms (fast fail held; nothing touched `run_interp`). Dropping
the parties breaks two places at once — the list loses its two-element tail
and the dealer's prologue receives `iota _ 0 = [::]` instead of `[:: 7; 8]` —
both cons/nil constructor clashes. This is P-A finding F2 (input processes are
load-bearing) at the type level.

## As-built correction (P-D finding, applied to P-C): input-identifier offset

`probe_c_pgl27_exec.v`'s generic `epp_input_ids` started at
`(pi_T' (mp_PI mp)).+2`; seats occupy identifiers 2 through `(pi_T' _).+2`, so
the first free identifier is `(pi_T' _).+3`. At the five-card carrier the
`.+2` offset yields `[:: 6; 7]` where the landed dealer passes `[:: 7; 8]`,
making the process equality FALSE (machine-checked in
`probe_d_fivecard_exec.v`: `fc_input_ids_offsetE` vs `fc_epp_input_idsE`).
P-C's copy was corrected to `.+3` on 2026-08-11 and recompiled green,
machine-checking that PGL is insensitive (empty input list, `iota _ 0 = [::]`
at every offset). Both probe files now carry the identical generic section.

## P-E: `probe_e_mutation.v` — the endpoint reader at the dealer's index

Perturbation: the generic endpoint reader of `probe_e_traces.v` with the
verifier's process index 1 replaced by `mut_verifier_index = 0`, the dealer's
index, all other fields and the PGL(2,7) adapter unchanged.

Expected: the process equality `epp_procs = pgl27_procs` still holds, since the
process list does not mention which trace is read afterwards, and the transport
of `pgl27_endpoints` is rejected at the index.

Observed (verified 2026-08-11 by direct `rocq compile`, exit 1, no `.vo`):

```
File ".../probe_e_mutation.v", line 169, characters 38-43:
Error:
In environment
R : realType
mpP := pgl27_profile R : MonodromyProfile R
s : bool
w0 : pgg_gT pgl27_M
The term "erefl" has type "mut_verifier_index = mut_verifier_index"
while it is expected to have type "mut_verifier_index = 1"
(cannot unify "mut_verifier_index" and "1").
```

Interpretation: the process index is load-bearing for the endpoint facts and
inert for the process list, the same split P-C found for the fuel. The
transport is staged through the index equation for the same reason: at a
mismatched index a direct `exact: pgl27_endpoints` puts conversion in front of
two `nth` applications over the same unevaluated `run_interp` term, which is
the P-C divergence shape. Index pinning by `erefl` refutes the substitution in
milliseconds (the 4.6 s wall time is import loading), so every later probe
projecting a run trace must pin its process index the way P-C pins the fuel.

## P-H: `probe_h_mutation.v` — the count bridge dropped from the record

Perturbation: the final adapter record of `probe_h_adapter_decomposition.v`
with the field `ep_players_bridge` deleted, every other field kept, and the
endpoint decoder `epp_decode` attempted over it.

Expected: the headline is underivable because its decoder does not exist. The
failure is at the DEFINITION, not at a proof: the endpoint tuple has one entry
per seat, `run_recover` takes one entry per share, and with the bridge gone
there is no equation to cast along.

Observed (verified 2026-08-11 by direct `rocq compile`, exit 1, no `.vo`,
line 80 characters 15-38):

```
Error:
In environment
R : realType
mp : MonodromyProfile R
e : EPPnb mp
ep : seq 'I_(pgg_N' (mp_M mp)).+1
Hsz : size ep = (pi_T' (mp_PI mp)).+1
The term "tcast Hsz (in_tuple ep)" has type
 "((pi_T' (mp_PI mp)).+1).-tuple 'I_(pgg_N' (mp_M mp)).+1"
while it is expected to have type
 "((ts_T' (rp_scheme (mp_plug ?mp))).+1).-tuple 'I_(pgg_N' (mp_M ?mp)).+1".
```

Interpretation: the seat/share bridge is the load-bearing field of the whole
adapter. It is not a convenience for a proof step; without it the decoder, and
therefore `epp_run_recovers`, `epp_end_to_end` and both instantiated
headlines, cannot even be stated. The card/share bridge `ep_cards_bridge` is
the weaker of the two: it types the plug-derived content readout
(`epp_content_from_plug`) but not the decoder, so deleting it leaves the
headline standing. This is soundness invariant 6 (participant count and share
count connected by a checked type-level fact) realised at the earliest failing
point.
