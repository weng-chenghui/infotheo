# Design: explicit mid-point program (`dsdp_game_gen_literal.v`) + `Sout` greppability

Date: 2026-06-15
Status: approved design, ready for implementation plan

## Problem

The SSProve corrupted-Alice game is now fully auto-derived: the program in play is
`denote_run … gc` with `gc := all_zero (game_of_trace_seeded …)`. Nobody can read that
program directly. `gc_eq` (`dsdp_security_indcpa_fiber.v:531`) reflects the **AST** to a
readable `game_code`, but nothing reflects the **denotation** (the actual `raw_code`,
including the `#put S_output_cell := … S …` step) to a hand-written program. So the
scalar-product output S, the object the secrecy theorem is about, is invisible at the
program level.

Separately, in `dsdp_security_indcpa_fiber.v` the leaked output is consumed by the
adversary through a bare lowercase binder `s` (`guess ← … (view, s)`), which does not
grep. The durable names are `S_output_cell`, `Sout` (the RV), `id_s_get`,
`denote_s_get_body`, none sharing one stem.

## Goals

1. A permanent, abstract, mid-point lemma certifying that a hand-written, human-legible
   SSProve program (with S visible) equals the auto-derived denotation, for both the
   real and the all-zero output-exposing endpoints. Modeled on `gen_printedE` in
   `scratch_print_gen.v`.
2. One identifier stem `Sout` shared across every artifact of the leaked output, so
   `grep -F Sout` lands on the produce, read, and consume sites.

## Non-goals

- No change to the secrecy bound, the analysis chain, or any probability lemma.
- No surgery hoisting `gc` / `gc_eq` / unfold lemmas out of the fiber file (rejected:
  high-risk churn through fragile big proofs, no benefit to the goal).
- Clone files (`dsdp_security_indcpa_clone.v` etc.) keep their independent cell copies.

## Component 1 — `dsdp_game_gen_literal.v`

New build-target file, standalone, upstream of `dsdp_security_indcpa_fiber.v` and
downstream of `dsdp_game_code` / `dsdp_game_symbolic` / `dsdp_program`. Parallels the
`dsdp_game_code.v` / `dsdp_game_symbolic.v` family.

### Setup

- Section with the same marshalling variables as the fiber section (`AHE`, `Renc`,
  `card_renc`, `renc_card`, `rand_of_renc`, `t_msg`, `t_cipher`, `chmsg_of_msg`,
  `chcipher_of_cipher`, `pkey_of_party`, `card_msg`, `msg_of_idx`, `rand0`, the `seed`
  weights), and the hypothesis `card_renc != card_msg` (the unfold lemmas need it).
- Section-local rendering notations reused from `scratch_print_gen.v`: `u *h w`,
  `u ^h w`, `E<p,s>(| m |)`, `m[ i ]`, `<[ c ]>`.
- Locally re-established reflection scaffolding (standalone, not hoisted): the
  `game_code` AST and the `denote_run` per-constructor unfold lemmas
  (`denote_run_sample_msg/sample_renc/put/put_output/let/enc_hop/ret`) in the shape the
  fiber file already uses, plus the seeded zero game `gc` and a local `gc_eq`. These are
  the same `denote_run` computation rules; duplicating the seven small unfold lemmas
  and one `vm_compute` reflection is acceptable and avoids fiber-file surgery.

### Programs (seeded, abstract `card_msg` / `card_renc`)

Both endpoints use the seeded shape that matches the fiber's `gc` and `real_game`:
4 `sample uniform card_msg`, 2 `sample uniform card_renc`, the V_2 put, two hops, two
homomorphic combines, the S put, and the leak of four ciphertexts. (Not the 6-sample
unseeded demo shape of `scratch_print_gen.v`; the weights v1, u1, u2, u3 come from the
seed.)

S is bound by name so it appears literally in the source and ties to the correctness
spec `dsdp_output`. The binder is `Sout`, not `S` (which is `nat.+1`).

```
Definition gen_literal_zero : raw_code (cipher_list t_cipher) :=
  x  ← sample uniform card_msg ;;   (* v2, the challenge secret *)
  x0 ← sample uniform card_msg ;;   (* v3 *)
  x1 ← sample uniform card_msg ;;   (* r2 *)
  x2 ← sample uniform card_msg ;;   (* r3 *)
  x5 ← sample uniform card_renc ;;
  x6 ← sample uniform card_renc ;;
  #put V_2_cell t_msg := Some (chmsg_of_msg m[x]) ;;
  ir  ← sample uniform card_renc ;;
  ir0 ← sample uniform card_renc ;;
  let Sout := dsdp_output w_v1 w_u1 w_u2 w_u3 m[x] m[x0] in
  #put Sout_cell t_msg := Some (chmsg_of_msg Sout) ;;
  ret [:: <[ (E<Bob,    ir >(| 0 |) ^h …) *h E<Bob,    x5>(| … |) ]>
        ; <[ (E<Charlie, ir0>(| 0 |) ^h …) *h E<Charlie, x6>(| … |) ]>
        ; <[ E<Bob,    ir >(| 0 |) ]>
        ; <[ E<Charlie, ir0>(| 0 |) ]> ].

Definition gen_literal_real : raw_code (cipher_list t_cipher) := (* same, hops carry the real payloads, not 0 *) …
```

The exact binder-to-meaning mapping and the combine/exponent terms are transcribed from
the reduced normal form at implementation time (the `scratch_print_gen.v` recipe:
`rewrite … ; simpl ; cbv [de_rand_nth …] ; simpl`), so the source is verified, not
guessed.

### Mid-point lemmas

```
(* gen_literal_zeroE — the legible all-zero output-exposing program is exactly the
   auto-derived denotation of the seeded all-zero game. *)
Lemma gen_literal_zeroE : gen_literal_zero = denote_run … gc.

(* gen_literal_realE — the legible real output-exposing program is exactly the
   auto-derived denotation of the seeded real game. *)
Lemma gen_literal_realE : gen_literal_real = denote_run … gc_real.
```

Proof: the `denote_run_*` unfold-lemma rewriting chain (the shape `view_marginal_indep`
uses), terminating in the hand-written form. Not `by []` (abstract cardinalities prevent
the dispatch guards from reducing without the unfold lemmas and `card_renc != card_msg`).

### Fiber cross-reference

One comment line at the fiber's `gc` / `gc_eq` pointing to `gen_literal_zeroE` for the
readable form. The fiber file `Require`s `dsdp_game_gen_literal` for the pointer; no
proof in the fiber file changes.

## Component 2 — `Sout`-stem rename

Every artifact of the leaked output carries the literal substring `Sout`, so
`grep -F Sout` finds the whole flow.

| current | new | files (occurrences) |
|---|---|---|
| `S_output_cell` | `Sout_cell` (+ `Notation S_cell := Sout_cell`) | game_code (12), fiber (13), game_symbolic (1) |
| `id_s_get` | `id_Sout_get` | fiber (11), indcpa_security (7), game_code (10) |
| `denote_s_get_body` | `denote_Sout_get_body` | fiber (16), game_code (5), indcpa_security (2) |
| bare binder `s` (leaked value) | `Sout_val` | fiber: consume sites 101, 403, 599, 642, 858, 903, 929; destructure 869; and the matching `s ← …` read sites |

- RV `Sout` unchanged (already on-stem).
- The binder rename is scoped to the leaked-output value binders only. It is done by
  reading each site, not a blind global substitution: other local `s` binders (e.g.
  `sread`) are left alone, and correctness is confirmed by the build.
- `Notation S_cell := Sout_cell` is a convenience alias so `grep S_cell` also works;
  produce/read sites reference the cell, consume sites reference `Sout_val`, analysis
  sites reference the RV `Sout`. `grep -F Sout` covers all three.
- Clone / scratch / probe files are not touched.

## Verification and commits (atomic)

- **Commit A — rename only.** Mechanical cross-file `Sout` rename (Component 2). Build
  every affected file with the project Makefile; `ROCQ_AUDIT_BYPASS=1` (pure rename,
  nothing for the audit to check).
- **Commit B — new file + lemmas.** Add `dsdp_game_gen_literal.v`, the two mid-point
  lemmas, the `_CoqProject` entry, the fiber cross-reference comment, and delete
  `scratch_print_gen.v` (subsumed by `gen_literal_real`). `rocq_check` green on the new
  lemmas, full `make`, then the mandatory rocq-auditor Stage-2 (new identifiers and
  proof bodies).

## Risks

- **Binder rename over-reach.** A blind substitution of `s` would corrupt unrelated
  binders. Mitigation: site-by-site edit guided by the enumerated line list, build-verified.
- **Abstract reflection of the literal programs.** The combine/exponent terms and binder
  order must be transcribed from the actual reduced normal form, not assumed. Mitigation:
  use the `scratch_print_gen.v` printing recipe and let `rocq_check` reject any mismatch.
- **Cross-file rename build breakage.** 77 occurrences across four files. Mitigation:
  Commit A builds the whole dependent set before Commit B starts.

## Source map

- `scratch_print_gen.v` — the reference (`gen`, `gen_printed`, `gen_printedE`); real game, no S; to be deleted.
- `dsdp_security_indcpa_fiber.v:506,531,534,545` — `gc`, `gc_eq`, `output_term`, `denote_output_termE`.
- `dsdp_security_indcpa_fiber.v:512-525` — the `denote_run_*` unfold lemmas (shape to mirror).
- `dsdp_security_indcpa_fiber.v:949` — `view_marginal_indep` (proof shape for the reflection chain).
- `dsdp_game_code.v:230,236,440,499` — `V_2_cell`, `S_output_cell`, `denote_v2_get_body`, `denote_s_get_body`.
- `dsdp_program.v:41` — `dsdp_output` (the S spec).
