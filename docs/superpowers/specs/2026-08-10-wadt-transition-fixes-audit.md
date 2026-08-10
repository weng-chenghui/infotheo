# Adversarial audit of 2026-08-10-wadt-transition-fixes-design.md

Auditor: Opus subagent (read-only, static reads and greps, no compilation),
2026-08-10. Spec revision audited: `8325785d`. Paper revision: `e39751e1`.
Verbatim report follows; the spec amendments it forced are recorded in the
design doc's "Audit resolution" section.

---

## BLOCKERS

### A1 — E21: the worked example is wrong on three independent axes, and its stated fallback is also wrong

**Spec item:** E21 (and its "VERIFY before landing" note).

**Evidence — the action direction is `D(g i)`, not `D(g^{-1} i)`.**

`pgg-smc/protocol/card_exchange_pismc.v:200-202`

```coq
Definition dealt_hand_content (content : 'I_N -> 'I_N) (W : seq gT) (i : 'I_T)
    : seq 'I_N :=
  [seq content (rho w (tnth starts i)) | w <- W].
```

Confirmed at four more sites: `pgl27_run.v:152-156` (`pgl27_endpoints`),
`pgl27_trace.v:326-328` (`pgl27_player_trace_E`), `pgl27_secrecy.v:70-72`
(`pgl27_view`), and generically `reconstruct/transitivity_privacy.v:447-449`.
`pgg_rho` is the identity morphism for this instance
(`pgg_interface.v:535-545`; `pgl27_group.v:295-297`). `g^{-1}` appears only on
the dual set-of-positions side, `pgl27_orbit.v:294-295`:
`heart_set (D o g) = (g^-1) @: heart_set D`.

**Evidence — the data.** `pgl27_orbit.v:347-355`:
`D_0 = orbit_encode false = [0;1;2;3;4;5;6;7]`,
`D_1 = orbit_encode true = [0;1;2;4;3;5;6;7]`. Infinity is index 7
(`pgl27_group.v:6-7`, `:113`). Translation is generator 0,
`tr_tbl = [:: 1; 2; 3; 4; 5; 6; 0; 7]` (`pgl27_group.v:51`), certified
`tr_perm =1 moebius 1 1 0 1` (`:136`), the 7-cycle `(0 1 2 3 4 5 6)` fixing 7.

**Three errors:**

1. Values. Seat `i` observes `tnth D_0 (tr_perm i)`; for the identity tuple
   this is `tr_perm i`. Coalition `{0,1,2}` observes **(1, 2, 3)**. The
   spec's primary answer (6,0,1) is the inverse convention and is wrong.
2. "Each card moves one position forward" is false under the correct
   convention: the card at position `p` ends at `p-1`. The spec's fallback
   only swaps the number triple, leaving a false sentence.
3. The three-transitivity sentence points the map the wrong way: the needed
   shuffle `h` maps the coalition's positions to the value-holding
   positions. `D_1(1)=1, D_1(2)=2, D_1(4)=3`, so `h(0)=1, h(1)=2, h(2)=4`;
   the relevant positions of `D_1` are `(1,2,4)`, not `(6,0,1)`.

Under the erroneous convention the example is also degenerate (s=1 with the
same translation gives (6,0,1) again). Under the correct convention it is
genuinely informative: s=1 under the same translation gives (1,2,4), which
differs, and privacy is restored only by a different shuffle.

**Fix.** Corrected example body (adopted into the spec). Also: the
positions figure is Figure 6 (`fig:encoding`), not Figure 5; its drawn
arrangements match `orbit_encode` exactly.

**Latent hazard:** `main.tex:195` writes "$\rho(g)D$", which reads as a left
action but the formalization computes the pullback `D o rho(g)`. Land E21
only together with a convention sentence near line 195.

---

### A2 — E5: the roadmap inverts which sections use kernel enumeration

`vm_compute`/`by compute` counts: `five_card_leakage.v` 0, `five_card_kim.v`
0, `five_card_family.v` 0, `pgl27_group.v` 5, `pgl27_orbit.v` 11,
`pgl27_mixing.v` 3. The five-card leakage closed forms are analytic
(`five_card_leakage.v:317-319`, closed by case analysis at `:465`); the Kim
mixing bound ends in `by lia` (`five_card_kim.v:613-626`). The PGL
three-transitivity certificate is `by vm_compute` (`pgl27_group.v:218-219`).
E5 as drafted contradicted `main.tex:826-827` and `:1030-1034`.

**Fix.** Five-card: "deck small enough for direct case analysis"; PGL:
"deck enumeration no longer suffices and three-transitivity carries the
privacy proofs".

---

### A3 — E11: the stated line range garbles the splice and deletes the all-decks dealer

Replacing lines 234-236 orphans "This fixed-representative" on line 233 and
deletes the all-decks dealer definition and the uniform-prior statement,
which are load-bearing at `main.tex:945-949` and `:952-966`. Also the paper
writes "fixed representative dealer" unhyphenated at `:989`, `:1103`,
`:1134`.

**Fix.** In-sentence rewrite only; preserve lines 234-236 from "An
all-decks" onward verbatim; use the unhyphenated form.

---

### A4 — E1: "Every security proof in this paper consumes the same kinds of data" is false of two of the three generic theorems it introduces

Generic trace lifting (`main.tex:502-508`; `pgg_trace_secrecy.v:38-55`) and
data processing (`:517-520`) consume none of the four listed data; Theorem 1
consumes t-transitivity directly (`:481-483`). E1 also listed four data
where the record has five fields, and said "shuffle distribution" where the
record carries the endpoint bound.

**Fix.** Restate over instances, five data, "shuffle-security bound", and
add "while the generic theorems take their hypotheses directly".

---

## MAJOR

### A5 — Location column mixes "replace this range" with "edit a phrase inside this range"

E5, E7, E8, E10, E11, E14, E19 destroy adjacent text under a literal
line-range replace (orphaned sentence fragments, silently deleted
sentences). **Fix:** exact old string and exact new string for every edit.
E10's replacement is additionally a garden-path sentence; use "I call this
the word-shuffle model." appended.

### A6 — E16: the "actual table entry" does not exist in the source

`word_table` (`pgl27_group.v:205-206`) is computed inside `vm_compute`
during one `Qed` and never materialized. The base triple is `[:: 0; 1; 2]`
(`:213`). `(1,3,5)` is reachable by exhaustiveness but no literal entry
exists; hand-evaluation gives the length-3 word `[:: 1; 1; 0]`, derived,
not machine-checked. **Fix:** restate around the base triple, or
machine-verify a concrete entry first. Placement belongs immediately after
"The kernel checks the resulting finite table." (`:827`).

### A7 — E19: the stated symmetrization reason is nowhere recorded

All comments in `pgl27_mixing.v` are descriptive. The only recorded
rationale is negative
(`2026-07-13-pgl27-boundary-and-mixing-design.md:143-145`:
inverse-closedness is a shuffle-model choice, not a proof requirement). The
spectral rationale lives on a path `pgl27_mixing.v` does not import.
Counter-pressure: inverse-closedness IS mechanically load-bearing —
`inv_letter` (`pgl27_mixing.v:150`) closes the BFS predecessor step and the
fiber recursion over the alphabet (`:154`, `:596`, `:634-660`).
`pgl27_gen5_eq` (`:454-456`) supports the same-group sentence. **Fix:**
state the fiber-recursion closure reason.

### A8 — E3 drops "all" and turns a true hedge into a false claim

`pgl27_view_leak_k4` (`pgl27_secrecy.v:184-195`) does compute a positive
leakage for one four-position coalition; without "all"/"every" the
replacement claims none is computed. Also split the fused first sentence.

### A9 — Gates arithmetic: reason and inference land exactly on their thresholds

Confirmed baseline 6720 words, TOTAL 10 = 14.88/10k. Projected after edits:
purpose 1, reason 7, inference 8, instance 5, example 1, adversative 1,
TOTAL 23 = 32.9/10k. But reason lands exactly on 7 vs gate >=7 and
inference exactly on 8 vs gate >=8, and every truth fix (A2, A7, A12/A13)
threatens one of those events. Neutral signposting cleared by ~0.3 only.
The orientation regex is case-sensitive on "In", so a lowercase "in this
paper" scores zero. **Fix:** carry headroom or lower the two gates and
disclose.

### A10 — The acceptance protocol names instruments that do not exist

No per-section script and no I/we-neutral signposting variant exist in the
skill's `scripts/`. Three gates had no committed instrument. **Fix:**
commit the instruments next to the spec or restate the gates.

---

## MINOR

- **A11** — E12 names "orbit class" 57 lines after first use (`:709`); E10
  names "word-shuffle model" after abstract/roadmap uses; E13 after `:142`.
  E7, E8, E9, E14 are well placed.
- **A12** — Stuffing check: E18 is E14's definition instantiated at g=1
  (true but empty; a human editor cuts it). E12 as placed reads as a stub.
  Runner-up: E15 duplicates `main.tex:690`.
- **A13** — E15's mechanism claim checks out
  (`five_card_family.v:180-183`, `five_card_eps0_eq0`). Keep; consider
  trimming `:690` instead.
- **A14** — E4's "idealized" mislabels the implementable word distribution;
  say "compares a prior with a shuffle distribution rather than a
  distribution over executed runs".
- **A15** — After E2, "these choices" at `:411` resolves weakly; use "these
  components". E1's ending repeated "one record" against `:304`.
- **A16** — llncs.cls predefines numbered `example` (`llncs.cls:1174`);
  `\label` on it is safe (the no-label rule covers only the starred
  `\spnewtheorem*` environments). The spec's `\spnewtheorem` fallback would
  ERROR ("Command \example already defined"); strike it. Net word change
  before the [H] Figure 4 is about +40; recompile per commit.
- **A17** — Inserted text passes the prose rules (no em-dash, no semicolon,
  no parenthetical asides, no "law", no new abbreviations). E21 used an
  imperative, not "I"; either accept the impersonal register for the math
  example explicitly or recast. E9's "what I call" risks misattribution if
  "biased cut" is Kim and Cetinkaya's term; check before landing.

---

## Verified clean

- **E17**: all five instances consume `trace_secrecy_of_view`
  (`denboer_trace.v:217`, `kim_trace.v:49`, `s5_trace.v:191`,
  `s5x5_trace.v:341,347`, `pgl27_trace.v:403,440,569,610,693,731`). The
  fallback wording is unnecessary.
- **E6**: Table `tab:source-index` sits at the end of Section 7 and covers
  Sections 5-7; "this section and the two that follow" is correct.

## Verdict

Safe as written: E6, E9 (with the attribution check), E13, E17. Safe after
mechanical range fix: E7, E8, E10, E14, E20. Spec amendment required: E1,
E2, E3, E4, E5, E11, E12, E15, E16, E18, E19, E21.
