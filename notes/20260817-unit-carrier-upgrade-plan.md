# Plan: unit-carrier upgrade (execution of the audited spec)

Spec: notes/20260817-unit-carrier-upgrade-design.md (all 11 ledger rows GO;
soundness audit GO; naming audit GO). Every construction choice below is
decided here, with its reason. Code blocks are verbatim from the compiled
C6 copy (session scratchpad `wt-unit-carrier/`) as amended by the two
build-verified audit deviations.

Probe inventory (kept, never Require'd from permanent files):
`.scratch/probe_unit_carrier_instances.v`, `.scratch/probe_unit_hyp_shape.v`,
`.scratch/probe_unit_counting_transport.v`, plus the built copy at the
session scratchpad `wt-unit-carrier/` and audit checkers under
`audit-soundness/`.

Environment: build from the repo root so `eval $(opam env)` selects the
directory-local switch (Rocq 9.0.0, mathcomp 2.5.0). From anywhere else use
`eval $(opam env --switch=/Users/cheng-huiweng/Projects/coq --set-switch)`.

## Decided construction choices

1. Let term is `mulrI w_u3_unit` — compiled verbatim in probe and closure
   build; `can_inj (mulKr w_u3_unit)` also works but is longer. Reason:
   `mulrI` has `Arguments [R x] _ [x1 x2] _`, so the application is already
   the injectivity proof, and definitional eta bridges `*%R w_u3` to the
   stated lambda.
2. The lambda annotation `v : plain AHE` stays — it is the probed C3 form;
   the type ascription on the Let is load-bearing (naming audit §24.5).
3. trace_link.v gets NO Let — dead there (naming audit, rebuild-verified);
   only the Hypothesis and the :613 argument rename.
4. Hypothesis name `w_u3_unit` — MathComp `_unit` suffix precedent
   (row_ebase_unit family) + the file's `w_` parameter row; `w_u3_is_unit`
   and `Uw_u3` rejected with precedent (spec Naming section).
5. dsdp_entropy.v:421 comment is corrected to say finComNzRingType (the code
   is right; the comment is wrong). The _ring section itself stays at
   finComNzRingType so it keeps serving both carriers via coercion (C5).
6. Paper wording uses "invertible", matching main.tex:1358-1363's existing
   vocabulary. No em-dash, no semicolon (author rules).

## Task 1 — infotheo-itp, single atomic commit (code + .v comments)

All in /Users/cheng-huiweng/Projects/coq/infotheo-itp on branch
itp2026-dumas2017dual. One commit: the six files below compile only
together.

a. homomorphic_encryption/he_types.v
   :12  `(*     - plain : finComNzRingType   (message/plaintext space)                 *)`
   ->   `(*     - plain : finComUnitRingType (message/plaintext space)                 *)`
   :38  `  plain : finComNzRingType ;    (* message/plaintext space *)`
   ->   `  plain : finComUnitRingType ;  (* message/plaintext space *)`

b. homomorphic_encryption/idealized/idealized_ahe.v
   :41  `Variable msgT : finComNzRingType.` -> `Variable msgT : finComUnitRingType.`

c. dumas2017dual/dsdp/fdist_hopping/dsdp_alice_fdist_secrecy.v:209 — replace
   `Hypothesis w_u3_inj : injective (fun v : plain AHE => w_u3 * v).` with:
   ```coq
   (* Naming: [w_u3_unit] reads "w_u3 is a unit" (cf. mathcomp
      [row_ebase_unit]); the derived [w_u3_inj] keeps the former hypothesis
      name so proof bodies are unchanged. *)
   Hypothesis w_u3_unit : w_u3 \is a GRing.unit.
   Let w_u3_inj : injective (fun v : plain AHE => w_u3 * v) := mulrI w_u3_unit.
   ```

d. dumas2017dual/dsdp/fdist_hopping/dsdp_alice_trace_link.v
   :490 `Hypothesis w_u3_inj : injective (fun v : plain AHE => w_u3 * v).`
   ->   `Hypothesis w_u3_unit : w_u3 \is a GRing.unit.`   (no Let: dead here)
   :613 `pkey_of_dk w_v1 w_u1 w_u2 w_u3_inj` -> `pkey_of_dk w_v1 w_u1 w_u2 w_u3_unit`

e. dumas2017dual/dsdp/counting/dsdp_entropy.v:421 — comment word
   `finComUnitRingType` -> `finComNzRingType` (align comment with code).

f. dumas2017dual/dsdp/symbolic_game/dsdp_game_derivation.v:22 — comment word
   `finComNzRingType` -> `finComUnitRingType` (the wall is now stronger; the
   surrounding argument survives a fortiori).

Verification before commit (all reproduced twice already: C6 build + audit):
- `make -j8` exit 0; rebuilt set is the he_types closure (28 files).
- `Print Assumptions` on `dsdp_alice_guess_fdist_trace_V2_real_le` and
  `dsdp_alice_trace_sim_advantage_fdist_le`: exactly the three boolp
  classical axioms.
- grep Admitted/Axiom/Abort over the two fdist_hopping files: zero.
- mathcomp-style-auditor pass on each changed .v (house rule; the copy's
  secrecy.v is already audited, re-run on the final text).
- Commit through the audit gate unbypassed (gate takes 2-3 min, stage2 off).

## Task 2 — CPP paper, sep10CPP2027/main.tex (after Task 1 lands)

Six loci (line numbers pre-edit; audit-enumerated):
- :1991-1993 prose+footnote: "assumes that multiplication by the third
  weight is injective" -> "assumes that the third weight is invertible";
  footnote `\coqin{w_u3_inj}` -> `\coqin{w_u3_unit}`.
- :2214 "the injectivity hypothesis" -> "the invertibility hypothesis".
- :2304-2307 (ver.2 section): same prose change; footnote
  "under Hypothesis \coqin{w_u3_inj}" -> "under Hypothesis \coqin{w_u3_unit}".
- :2354 (ver.2 summary): "the injectivity hypothesis" -> "the invertibility
  hypothesis".
- :830-831 HETypes prose: finComNzRingType gloss -> finComUnitRingType,
  "finite, commutative, non-trivial ring" -> gloss that names computable
  unit inverses (exact sentence drafted at execution under /thesis-prose).
- :843 minted record listing: `plain : finComNzRingType ;` ->
  `plain : finComUnitRingType ;`.
Then `make` (paper builds, references clean).

## Task 3 — thesis, thesis/chapters/ahe-hierarchy.tex (after Task 1 lands)

- :58 record listing carrier word, :65 prose "carries a
  \coqin{finComNzRingType} structure" -> finComUnitRingType with adjusted
  gloss. Same wording discipline as Task 2. Thesis build per its Makefile.

## Fallback

If landing Task 1 hits anything the C6 build did not (it should not; the
copy build is the same toolchain), fall back to spec option 1: keep the
carrier, state `Hypothesis w_u3_unit : exists v, w_u3 * v = 1` — probed GO
2026-08-17 in session scratch (probe_unit_inj.v).
