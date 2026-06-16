# Sound reconstruction of the malicious-adversary leak (post E_enc_inde removal)

Date: 2026-06-16
Scope: `dumas2017dual/dsdp/` (counting axis + `dsdp_main.v`), blueprint, one notes memo.

## 1. Problem

Commit `d3098a9` deleted the unsound `E_enc_inde` cluster. `E_enc_inde` was the
hypothesis

```
forall (A B : finType) (p : party_id) (X : {RV P -> p.-enc A}) (Y : {RV P -> B}),
  P |= X _|_ Y.
```

"AHE encryption hides perfectly" expressed as information-theoretic independence.
This is unsound: a ciphertext is a deterministic function of its plaintext, key,
and randomness, so it is not IT-independent of arbitrary variables.

The deletion removed two kinds of result that depended on it:

- The **attack** result `US_compromised_leaks_V2`: a malicious Alice fixing
  `US = (1,0)` makes `H(V2 | AliceView) <> H(p_V2)`.
- The **secrecy** results `bob_privacy_V1/V3`, `charlie_privacy_V1/V2`: an honest
  party "learns nothing", `H(V_i | View) = log m`.

This memo reconstructs the **attack** result on a sound footing. The secrecy
results are scoped separately (Section 7) because they genuinely need IND-CPA.

## 2. Key insight: the leak needs no encryption assumption

The malicious leak does not need IND-CPA, and never needed `E_enc_inde` either.
IND-CPA bounds secrecy from above; the leak is a from-below fact driven by the
plaintext output, which the adversary is entitled to receive.

The old proof used `E_enc_inde` only to *strip* the ciphertext components out of
the conditioning so that a contraction lemma would fit. That was an artifact of
the proof shape, not of the statement. Soundly:

- When `US = e_1`, the dot-product output `S = VS_0` (relay party 1's input) by
  pure algebra (`dotp_n_e1`, already present and sound in `malicious_n`).
- `S` is a component of the adversary's view, so `VS_0 = g \o View` for a
  projection `g`, hence `H(VS_0 | View) = 0` by the existing infotheo lemma
  `centropy_RV_comp0 : H(f \o X | X) = 0` (`information_theory/entropy.v:498`).
- Extra ciphertext components in the view only lower conditional entropy
  further, so they are harmless; no independence claim is required.

`H(VS_0 | View) = 0` is the **strong full-leakage** statement (zero residual
uncertainty: the adversary's posterior on the secret is a point mass). The old
`<>` form was strictly weaker. The equivalent mutual-information reading is
`I(VS_0 ; View) = log m` (all `log m` bits leak); we headline the residual-zero
form per the design decision, leaving `I = log m` as the `I = H - 0` corollary.

## 3. The full-leakage engine

`centropy_RV_comp0 (f : A -> B) : H( f \o X | X ) = 0`.

Given the adversary's view `View : {RV P -> A}` and a recovery function
`g : A -> msg` with `VS_0 = g \o View`, this lemma yields `H(VS_0 | View) = 0`
directly, regardless of any other components of `View`.

## 4. Design — layers and headlines

### Layer 1 — algebraic disclosure (support, unchanged)

`malicious_n` in `dsdp_view_independence.v` keeps `dotp_n_e1 : dotp_n ConstUS_n v
= v ord0`. This is the named algebraic fact ("`e_1 . v = v_1`"). No new support
lemma is added.

`US_n_compromised_leaks_V1` is **deleted** from `dsdp_main.v`. It was an RV-level
restatement of `dotp_n_e1` with no leakage content (no view, no entropy), and is
needed only as a one-line step inside the generic theorem below, where it is
inlined over `dotp_n_e1`.

### Layer 2 — generic N-party full-leakage headline

In `dsdp_main.v`, `Section dsdp_malicious_n` (cloned context of `malicious_n`):

```
(* US_n_compromised_leaks_secret -- a corrupted Alice fixing US = e_1 makes
   relay party 1's input VS_0 a function of her view (the protocol output S is
   in the view and equals VS_0), collapsing its conditional entropy to zero. *)
Theorem US_n_compromised_leaks_secret {A : finType}
    (View : {RV P -> A}) (g : A -> msg)
    (US VS : {RV P -> {ffun 'I_n_relay.+1 -> msg}})
    (US_e1 : US = fun _ => ConstUS_n)
    (output_in_view : Dotp_n_rv US VS = g \o View) :
  `H( (fun t => VS t ord0) | View ) = 0.
```

Proof sketch: `rewrite US_e1` in `output_in_view`; `Dotp_n_rv (fun _ =>
ConstUS_n) VS = (fun t => VS t ord0)` by `funext` + `dotp_n_e1`; substituting
gives `(fun t => VS t ord0) = g \o View`; close with `centropy_RV_comp0`.

The hypothesis `output_in_view` ("the adversary sees the protocol output") is the
honest content that makes this a leakage theorem rather than an algebraic
identity.

### Layer 3 — concrete 3-party instance

In `dsdp_main.v`, a new cloned-context section. The concrete Alice view is built
from fresh section-variable RVs (the deleted `dsdp_random_inputs` record is not
resurrected), and **includes the three ciphertext hops** so the leak is shown to
survive the full real view that the old proof could only handle by unsoundly
stripping the ciphertexts. The relay query components `U2, U3` are the entries of
Alice's query vector, so "Alice fixes `US = e_1`" is the pair `U2 = 1`, `U3 = 0`:

```
Variables (V1 V2 V3 U1 U2 U3 R2 R3 : {RV P -> msg}) (Dk_a : {RV P -> Alice.-key Dec msg}).
Let D2  := V2 \* U2 \+ R2.
Let D3  := V3 \* U3 \+ R3 \+ D2.
Let S   := D3 \- R2 \- R3 \+ U1 \* V1.            (* output = U2*V2 + U3*V3 + U1*V1 *)
Let AliceView := [% Dk_a, S, V1, U1, U2, U3, R2, R3,
                    E' Alice `o D3, E' Charlie `o V3, E' Bob `o V2].

(* US_compromised_leaks_V2 -- a malicious Alice fixing her query to e_1
   (U2 = 1, U3 = 0) reads Bob's private input V2 off her view; its conditional
   entropy collapses to zero. *)
Theorem US_compromised_leaks_V2 :
  U2 = (fun _ => 1) -> U3 = (fun _ => 0) ->
  `H( V2 | AliceView ) = 0.
```

Recovery: under `U2 = 1`, `U3 = 0` the output is `S = V2 + U1*V1`, so
`V2 = S - U1*V1 = g \o AliceView` with `g(view) = S - U1*V1` (Alice's own
`U1, V1` plus the output `S`); close with `centropy_RV_comp0`.

Reuse of the N-party lemma: this is the `n_relay = 1` instance of
`US_n_compromised_leaks_secret`, obtained by wrapping `(V2, V3)` and `(U2, U3)` as
`'I_2`-indexed ffuns `VS`, `US`, so `US = fun _ => ConstUS_n` encodes
`U2 = 1, U3 = 0` and `Dotp_n_rv US VS = U2*V2 + U3*V3 = S - U1*V1 = g \o
AliceView` discharges `output_in_view`. This is the concrete payoff of "can the
generalized N-party lemmas be used": the 3-party headline is a one-shot
specialization at `n_relay = 1`. Both this instance route and the direct
`centropy_RV_comp0` proof (same recovery `g`) are probe-validated (Section 8);
the instance route is preferred because it exhibits the n-party reuse, with the
direct proof as an equally-checked alternative.

## 5. File placement and blueprint

- `dsdp_view_independence.v` / `malicious_n`: unchanged (keeps `dotp_n_e1`).
- `dsdp_main.v` / `dsdp_malicious_n`: delete `US_n_compromised_leaks_V1`, add
  `US_n_compromised_leaks_secret`; add the concrete-instance section with
  `US_compromised_leaks_V2`.
- Blueprint coverage (strict 1:1): drop `US_n_compromised_leaks_V1`; add
  `US_n_compromised_leaks_secret` and `US_compromised_leaks_V2`. Reintroduced
  3-party algebra (the `S = Dotp_n_rv US VS + U1*V1` identity, if factored as a
  named lemma) goes in `dsdp_view_independence.v` as support.

## 6. 3-party vs N-party annotations in `dsdp_main.v`

Add a per-theorem scope tag to the file header and each theorem comment:

| Headline | Scope |
| --- | --- |
| `dsdp_alice_view_advantage_le` | 3-party (DSDP corrupted-Alice instance) |
| `dsdp_alice_guess_ideal_le` | 3-party |
| `dsdp_alice_guess_advantage_le` | 3-party |
| `dsdp_alice_guess_real_le` | 3-party |
| `dsdp_alice_unpredictability_ge` | 3-party |
| `dsdp_centropy_uniform` | 3-party |
| `dsdp_centropy_uniform_n` | N-party |
| `relay_privacy_n` | N-party (generic relay) |
| `US_n_compromised_leaks_secret` | N-party (generic) |
| `US_compromised_leaks_V2` | 3-party (instance of the above at n_relay = 1) |

The Alice IND-CPA headlines are 3-party because `dsdp_experiment` instantiates
`palice_sym` (the 3-party corrupted-Alice program) and the guessing seed carries
four values (`w_u1, w_u2, w_u3, w_v1`). The file header should state that the
file mixes generic N-party results with their 3-party DSDP instances, and tag
each.

## 7. Out of scope: IND-CPA secrecy reductions (separate memo)

The deleted Bob/Charlie semi-honest "learns nothing" results
(`bob_privacy_*`, `charlie_privacy_*`) genuinely need IND-CPA: an honest party's
view contains ciphertexts of the secrets, and IT conditional entropy does leak
through deterministic encryption, so `H(V_i | View) = log m` is false in the IT
world. The sound route is game-based corruption reductions modeled on the
existing Alice guessing triangle (`indcpa_hopping` axis). A scoping memo
`20260616-dsdp-indcpa-secrecy-reductions-scope.md` records this as future work.

## 8. Testing and de-risking

De-risk probe (`dumas2017dual/dsdp/.scratch/probe_leak_feasibility.v`, compiled
clean against the real switch, Rocq 9.0.0, no axioms beyond the ambient
`boolp` ones):

- **Probe A** — the generic `US_n_compromised_leaks_secret` body
  (`dotp_n_e1` lift, rewrite chain, `centropy_RV_comp0`) compiles as written.
- **Probe B** — the concrete 3-party `AliceView` with all three ciphertext hops
  type-checks (`p.-enc msg` is a finType, RV-codomain-legal); `V2 = g \o
  AliceView` discharges by `funext` + `ring` under `U2 = 1, U3 = 0`; closed by
  `centropy_RV_comp0`. The direct-proof route for Layer 3 is confirmed.
- **Probe C** — wrapping `(V2, V3)`, `(U2, U3)` as `'I_2` ffuns: `USwrap = fun _
  => ConstUS_n` and `Dotp_n_rv USwrap VSwrap = V2` both compile. The
  clean-instance route for Layer 3 is confirmed, so the 3-party headline can be a
  genuine specialization of the generic theorem (not merely the fallback).

Confirmed library facts: `comp_RV` notation is `` f `o X ``; `centropy_RV_comp0 :
`H( f `o X | X ) = 0` (`information_theory/entropy.v:498`); `party_id := Alice |
Bob | Charlie | NoParty`; `Alice.-key Dec msg` is the decryption-key type.

Each new lemma is verified with `rocq_check` (`proof_finished: true`). Deletions
and doc-comment edits carry no new identifiers and are audit-bypassable; the two
new theorems require the standard pre-commit audit.

## 9. Deliverables checklist

1. Delete `US_n_compromised_leaks_V1` from `dsdp_main.v`.
2. Add `US_n_compromised_leaks_secret` (generic N-party) to `dsdp_main.v`.
3. Add `US_compromised_leaks_V2` (3-party instance) to `dsdp_main.v`, with the
   concrete section-variable Alice view including ciphertext hops.
4. Update blueprint coverage (drop one, add two).
5. Add 3-party / N-party scope tags to the file header and every theorem comment.
6. Write `20260616-dsdp-indcpa-secrecy-reductions-scope.md`.
