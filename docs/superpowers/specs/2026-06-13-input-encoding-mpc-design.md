# Input-encoding mechanism for input-dependent layouts (pgg-smc MPC)

- Date: 2026-06-13
- Status: design approved in brainstorming. Core `InputEncoding` record shape validated by `coqc` against the live `ReconPlug`.
- Scope chosen: the general `InputEncoding` interface, its den Boer instance, input privacy, and the operational `sproc` realization (Approach B).

## 1. Problem

The pgg-smc framework runs a monodromy/threshold protocol whose recovered secret lives in a fixed starting layout (`pi_starts`), with the cut/word as anonymizing randomness. For the den Boer instance the committed input bits are received but discarded:

```
den_boer_assemble (committed : seq 'I_5) := [:: 1%g]   (* ignores `committed` *)
```

The layout is the fixed `ord_tuple 5`, whose decoded face row is one heart, so `fcI_recon` returns the constant `false` under every cut. The protocol therefore computes a constant, not `a && b`. Its own comment is explicit: "the committed value does not enter the reconstruction."

Inputs cannot be routed through the word. Reconstruction is invariant under the monodromy group (`rp_recon_invariant`), so any group element fed through `assemble` is invisible to the output. Inputs must instead determine the **layout**, for which there is currently no interface (`pi_starts` is a fixed field, `content = id`).

The actual five-card-trick semantics, `fc_three_consec (fc_shuffle k (fc_arrange a b)) = a && b` (`fc_correct`), live only in `five_card_program.v` and the standalone leakage model `five_card_leakage.v`. They are not wired into the running protocol.

## 2. Goal

A general mechanism by which the parties' committed inputs determine the starting layout, so the protocol computes

```
f(inputs) = ts_recon (layout(inputs))
```

with two guarantees:

- **functional correctness**: the running program recovers `f(inputs)` for every cut;
- **perfect input privacy**: a coalition observing the protocol learns nothing about the inputs beyond `f(inputs)`.

Conceptually, `layout(inputs)` together with the existing cut is a **perfect randomized encoding of `f`** (Ishai and Kushilevitz, "Randomizing Polynomials", FOCS 2000; Applebaum, Ishai, Kushilevitz). The two guarantees are exactly its decoding correctness and its (perfect) privacy.

The mechanism must be general, parameterized by the existing `ReconPlug`, with den Boer as one instance.

## 3. The interface: `InputEncoding`

`InputEncoding` is the deterministic encoder over an existing plug. The record below has been typechecked against the live `ReconPlug` with `coqc` (the field types `ts_T' (rp_scheme plug)`, `'I_(pgg_N' M).+1`, `rp_monodromy plug g`, `pgg_G M` all elaborate).

```coq
Record InputEncoding (M : MonodromyReprType) (secretT : Type)
    (plug : ReconPlug M secretT) (inputT : Type) := MkInputEncoding {
  ie_assemble : inputT -> (ts_T' (rp_scheme plug)).+1.-tuple 'I_(pgg_N' M).+1 ;
  ie_fun      : inputT -> secretT ;
  ie_assemble_valid : forall x,
      ts_valid (rp_scheme plug) (ie_fun x) (ie_assemble x) ;
  ie_orbit : forall x x', ie_fun x = ie_fun x' ->
      exists g : pgg_gT M, g \in pgg_G M /\
        ie_assemble x' =
          [tuple tnth (ie_assemble x) (rp_monodromy plug g i)
                | i < (ts_T' (rp_scheme plug)).+1] ;
}.
```

The two laws are the entire per-instance obligation:

- `ie_assemble_valid` (correctness / decodability): the assembled layout is a valid sharing of `ie_fun x`.
- `ie_orbit` (privacy / simulator): inputs with equal output land in one cut-orbit of layouts.

### Payoff theorems (generic, proven once)

```coq
(* output recovers f x for EVERY cut g0 — functional correctness, cut-anonymous *)
Lemma ie_output_correct (ie : InputEncoding plug inputT) x (g0 : pgg_gT M) :
  g0 \in pgg_G M ->
  ts_recon (rp_scheme plug)
    [tuple tnth (ie_assemble ie x) (rp_monodromy plug g0 i)
          | i < (ts_T' (rp_scheme plug)).+1] = ie_fun ie x.
(* proof: rp_recon_invariant (cut-invariance) + ts_correct (ie_assemble_valid) *)

(* perfect input privacy: under the uniform cut, the view reveals nothing about
   the inputs beyond the output. Stated over the uniform distribution on
   inputT * pgg_gT M (so the generic theorem requires inputT : finType), with
   generic random variables derived from the encoding:
     ie_in        := first projection (the inputs)
     ie_out       := ie_fun o ie_in (the output)
     ie_view ie C := the coalition slice at C of the cut-permuted layout *)
Lemma ie_input_private (ie : InputEncoding plug inputT) (C : {set 'I_(ts_T' (rp_scheme plug)).+1}) :
  `I( ie_in ; ie_view ie C | ie_out ie ) = 0.
(* proof: ie_orbit => equal-output inputs give equal-in-distribution views under
   the uniform cut => conditional mutual information is 0 *)
```

`ie_input_private` is a perfect-randomized-encoding privacy statement: the view distribution is a function of the output alone.

For den Boer (`inputT = bool * bool`, cut group `pgg_gT FiveCardKim_M` of order 5), the generic random variables `ie_in` / `ie_view C` / `ie_out` are the `Inputs` / `ViewA C` / `Secret` of `five_card_leakage.v`. The view identification is through the injective `encode_bool` (`ie_view` carries `'I_5` share values, `ViewA` carries the decoded faces), and injectivity preserves mutual information, so the generic statement specializes to `I( Inputs ; ViewA C | Secret ) = 0` on the leakage `Omega`.

## 4. Decoupling from the existing pipeline

The existing properties are unchanged and inherited through a single seam:

```
inputs --InputEncoding--> layout (valid sharing of f x) --existing pipeline--> { cut-anonymous, threshold-private, recovers f x }
                              \___ ie_assemble_valid is the only coupling ___/
```

- Anonymity (`sw_bound`) is a property of the cut distribution: for every position the cut is near-uniform. Independent of the layout.
- Threshold privacy (`ts_private`) is a property of the scheme: any sub-threshold coalition is indistinguishable across secrets, for any valid shares.
- Recon correctness and monodromy-invariance (`ts_correct`, `rp_recon_invariant`) are properties of the scheme and monodromy.

None mention `assemble`. They all quantify over valid layouts, so the assembled layout inherits them once `ie_assemble_valid` holds. No existing record or proof changes.

## 5. Den Boer instance

```coq
(* obligation 1: the layout decodes to AND  (= fc_correct at cut 0) *)
Lemma den_boer_assemble_valid (ab : bool * bool) :
  fcI_valid (ab.1 && ab.2)
    [tuple of [seq encode_bool x | x <- fc_arrange ab.1 ab.2]].

(* obligation 2: equal AND  =>  the layouts differ by a cyclic cut (the s=0 orbit) *)
Lemma den_boer_orbit (ab ab' : bool * bool) :
  ab.1 && ab.2 = ab'.1 && ab'.2 ->
  exists k : 'I_5, [seq encode_bool x | x <- fc_arrange ab'.1 ab'.2]
                 = rot k [seq encode_bool x | x <- fc_arrange ab.1 ab.2].

Definition den_boer_encoding : InputEncoding five_card_plug (bool * bool) :=
  MkInputEncoding
    (fun ab => [tuple of [seq encode_bool x | x <- fc_arrange ab.1 ab.2]])
    (fun ab => ab.1 && ab.2)
    den_boer_assemble_valid den_boer_orbit.
```

The per-party encoders and the public constant factor `fc_arrange` as:

| owner | positions | encoder |
|---|---|---|
| party A | `{0,1}` | `enc_A : bool -> 2.-tuple 'I_5 := map encode_bool (negate (fc_encode a))` |
| public | `{2}` | constant `encode_bool heart = inord 1` |
| party B | `{3,4}` | `enc_B : bool -> 2.-tuple 'I_5 := map encode_bool (fc_encode b)` |

so `ie_assemble (a,b) = map encode_bool (fc_arrange a b)`.

The orbit obligation rests on a concrete fact: the three `s=0` layouts are cyclic rotations of one another (clubs non-adjacent), while the `s=1` layout is the adjacent-clubs orbit. Explicitly:

```
(0,0) = T F T F T   clubs {1,3}     (0,1) = T F T T F   clubs {1,4}
(1,0) = F T T F T   clubs {0,3}     (1,1) = F T T T F   clubs {0,4}  (3 consec hearts -> s=1)
```

`(0,1)` rotated by 3 is `(0,0)`; `(1,0)` rotated by 2 is `(0,0)`. So under the uniform cut all three `s=0` inputs give `Uniform(non-adjacent-club orbit)`, identically distributed, hence perfect input privacy.

## 6. Operational realization (Approach B)

The live dealer must deal the input-derived layout, not the fixed `pi_starts`. This is a localized change to the den Boer committed dealer plus a layout-parameterized dealer program.

- New dealer program `exchange_dealer_from_layout (layout : sT.-tuple shareT) ...` dealing `content (rho w (tnth layout i))`, paralleling `exchange_dealer_from_words` and `exchange_dealer_with_commit`.
- The committed dealer receives the bits at ids 7, 8, computes `ie_assemble (a,b)`, and runs `exchange_dealer_from_layout (ie_assemble (a,b))`, replacing `den_boer_assemble`'s constant. Recovery reads the same layout.
- End-to-end output theorem: `den_boer_run_output (a,b) = a && b`, which is `ie_output_correct` instantiated at `den_boer_encoding`.
- Session-type duality re-established for `exchange_dealer_from_layout` (the dealing loop structure is unchanged, so the duality proof mirrors `exchange_dealer`; this is the principal implementation risk).

## 7. Probability space

Inputs and randomness share one space:

```
Omega = inputT * pgg_gT M = bool * bool * 'I_5
```

This is exactly the `Omega` of `five_card_leakage.v`: the leakage model's sample space already is the (inputs, cut) space, with `Secret = a && b` the output and `ViewA C` the coalition view. Therefore:

- input privacy is `I( Inputs ; ViewA C | Secret ) = 0`;
- output leakage is `I( Secret ; ViewA C ) = leak_k`;

both on the same uniform `P` over `Omega`, reusing `condent_ratio` and the per-view count lemmas already committed in `five_card_leakage.v`.

## 8. Deliverables (claims about the running program)

| Claim | Source |
|---|---|
| `den_boer_run_output (a,b) = a && b` | `ie_output_correct` + Approach B dealer/recovery |
| perfect input privacy `I(Inputs; ViewA C | Secret) = 0`, every `C` | `ie_input_private` (`den_boer_orbit` + uniform cut) |
| anonymity `eps = 0`, threshold privacy `ts_private` | inherited via `ie_assemble_valid`, unchanged |
| quantitative output leakage `I(Secret; ViewA C) = leak_k` | the entropy bridge in `five_card_leakage.v` |

## 9. Names (audited to codebase/MathComp convention)

| Identifier | Note |
|---|---|
| `InputEncoding`, `MkInputEncoding` | CamelCase record + `Mk<Name>` constructor, like `ReconPlug`/`MkReconPlug` |
| `inputT` | type carrier, a parameter with `T` suffix, like `ReconPlug M secretT` |
| `ie_assemble`, `ie_fun` | descriptive fields, `ie_` prefix (`ts_`/`rp_`/`cs_` style); `ie_fun` over the terse `ie_f` |
| `ie_assemble_valid` | Prop field named `_valid`, mirrors `ts_encode_valid` |
| `ie_orbit` | condition-named field, like `cd_hurwitz` |
| `ie_output_correct`, `ie_input_private` | `_correct` / `_private` suffixes, like `ts_correct` / `ts_private` |
| `den_boer_encoding`, `den_boer_assemble_valid`, `den_boer_orbit`, `den_boer_run_output` | full `den_boer_` instance prefix (never `db_`) |
| `exchange_dealer_from_layout` | `exchange_dealer_<variant>`, like `exchange_dealer_from_words` |
| `Inputs` (RV) | bare CamelCase like `Secret`/`ViewA`, no `RV` suffix; reuse existing `Secret` (output) and `ViewA` (view) |

All forms satisfy the project's I001 naming rule (at most four underscore components, canonical suffixes, no drift tokens).

## 10. Risks and open implementation questions

- Session-type duality for `exchange_dealer_from_layout` (the `vm_compute` duality checks): the main risk; to be resolved in the implementation plan with rocq-prover.
- Exact action direction of `rp_monodromy plug g` in `ie_orbit` and `ie_output_correct` against `rp_recon_invariant`'s convention (reindex versus inverse-reindex).
- Tuple and cast plumbing between `sT.-tuple shareT`, the interface tuples, and `pgg_recon_endpoints`.
- `ie_input_private` requires defining `Inputs : {RV P -> bool * bool}` on `Omega` and a small lemma that equal-in-distribution views give zero conditional mutual information; check infotheo for an existing form before proving it.

## 11. Files

| File | Content |
|---|---|
| `pgg-smc/reconstruct/input_encoding.v` | `InputEncoding` record, `ie_output_correct`, `ie_input_private` (generic) |
| `pgg-smc/instances/denboer1989/den_boer_encoding.v` | `den_boer_encoding` instance, `den_boer_assemble_valid`, `den_boer_orbit`, `Inputs` RV, the den Boer input-privacy theorem on `Omega` |
| `pgg-smc/protocol/card_exchange_pismc.v` | `exchange_dealer_from_layout` + session types |
| `pgg-smc/instances/denboer1989/den_boer_profile.v` | committed dealer rewrite, `den_boer_run_output` |
| `pgg-smc/instances/denboer1989/five_card_leakage.v` | the `ViewA`/`Secret` bridge already present; reused by input privacy |

## 12. De-risking findings (2026-06-13 rocq-mcp spike)

Definitional probes (E1-E5) against the live code settled the one load-bearing
question (generic vs den-Boer-specific output theorem) and corrected the
operational dealer form in Section 6.

**Verified facts.**

- `ts_recon_perm_invariant ts perm := forall g s shares, g \in G -> ts_valid ts s shares -> ts_recon ts [tuple tnth shares (perm g i) | i] = s`. The only recon invariance in the codebase is the **position-reindex** form, not a value-action form.
- `five_card_plug = {| rp_scheme := fcI_scheme; rp_content := fc_content; rp_monodromy := pgg_rho; rp_recon_invariant := fcI_perm_compatible_kim |}`, with `fc_content = id` and `fcI_perm_compatible_kim : ts_recon_perm_invariant fcI_scheme pgg_rho`.
- `pi_starts FiveCardKim_PI` is the identity tuple `[0,1,2,3,4]` (`ord_tuple 5`).
- `ie_output_correct den_boer_encoding ab` already has the type `ts_recon (rp_scheme five_card_plug) [tuple tnth (ie_assemble den_boer_encoding ab) (rp_monodromy five_card_plug P i) | i] = ie_fun den_boer_encoding ab`.

**Verdict.** The run-output theorem is GENERIC over any `InputEncoding plug
inputT` and equals `ie_output_correct` when the layout-recovery is the
reindex form. `den_boer_run_output (a,b) = a && b` is that theorem at
`den_boer_encoding`. No bridging or equivariance lemma is missing.

**Correction to Section 6.** The operational dealer/recovery must use the
**reindex** form, not value-action. `pgg_recon_endpoints` uses
`content (rho P (tnth starts i))`, which is recon-invariant ONLY because
`starts` is the identity (`tnth ord_tuple i = i` makes value-action and
reindex coincide). On a non-identity input layout they diverge and only the
reindex form recovers `ie_fun`. So:

- the layout-recovery is `recon_from_layout plug layout P := ts_recon (rp_scheme plug) [tuple tnth layout (rp_monodromy plug P i) | i]`, and `recon_from_layout plug (ie_assemble ie x) P = ie_fun ie x` is `exact: ie_output_correct`;
- `exchange_dealer_from_layout` deals the reindexed hand `content (tnth layout (rho w i))` ("arrange the layout, then cut by rotating positions"), NOT `content (rho w (tnth layout i))`.

**Scope decisions carried in.** The output theorem is stated generically
(`recon_from_layout_output`); `a && b` is only the den Boer instance
(`den_boer_run_output`). Session-type duality for the new dealer was planned as
deferrable but landed proven: the layout-content dealer keeps the
`den_boer_dealer_committed` session type, so all four duality lemmas discharge by
the same `vm_compute`. The realization (`pgg-smc/instances/denboer1989/den_boer_run.v`)
is `Qed` throughout, zero new axioms.
