# MathComp and Infotheo style authority

This file is loaded into the `rocq-auditor` system prompt on every invocation.
It is the canonical reference that every rule cites via its `authority` field.
Keep it terse; rationale and long-form examples belong in each rule's Markdown.

## Source

- MathComp `CONTRIBUTING.md` (master): https://github.com/math-comp/math-comp/blob/master/CONTRIBUTING.md
- Infotheo repository conventions (local peer-feedback log at `.claude/audit/justifications/`).

## Lemma naming grammar

Pattern: `(condition_)?mainSymbol_suffixes(_condition)?`

- **Main symbol** is usually the head symbol of the right-hand side of an equation, or the head symbol of a theorem.
- **Suffixes** refine shape or operand. Add an underscore before a suffix that begins with a one-letter lowercase identifier.
- **Membership** uses `in_` for predicate-unfolding (`in_cons`) and `mem_` for other membership (`mem_head`).

## Standard suffixes

| Suffix | Meaning |
|---|---|
| A | associativity |
| AC | right commutativity |
| ACA | self-interchange / inner commutativity |
| b | boolean argument |
| C | commutativity; or predicate/set complement; or constant |
| CA | left commutativity |
| D | predicate/set difference; or addition |
| E | elimination / equational rewrite |
| F, f | boolean false; or finite type |
| g | group argument |
| I | left/right injectivity; or set intersection |
| l | left-hand of an operation |
| L | left-hand of a relation |
| LR | moving operator from LHS to RHS |
| N, n | boolean negation; or natural-number argument; or ring negation |
| P | characteristic property or reflection lemma |
| r | right-hand operation; or ring argument |
| R | right-hand of a relation |
| RL | moving operator from RHS to LHS |
| T, t | boolean truth; or total set |
| U | predicate/set union |
| W | weakening |
| 0 | ring/nat zero or empty set |
| 1 | ring/nat/group one |
| B | subtraction |
| M | multiplication |
| Mn | ring nat multiplication |
| V | multiplicative inverse |
| X, Xn, Xz | exponentiation (Xn: nat, Xz: int) |
| Z | left module scaling |
| z | int argument |
| p | positive number |
| n | negative number |
| w | non-strict / weak monotony |
| wp | non-negative number |
| wn | non-positive number |

## Proof style

- Structure proofs as forward blocks using `have`; limit the scope of errors.
- Lines must end with a period; semicolons combine tactics within a line only.
- Lines that close a goal start with a terminator (`by` or `exact`).
- Do not use `Focus` or braces `{ ... }` for goal management; use bullets (`-`, `+`, `*`) or indentation.
- Avoid long chains of optional rewrites; prefer `rewrite conditional_rule ?simplify_side_condition // next_rule`.
- Line length must not exceed 80 columns.

## Spacing

- `move=>` and `move:` carry no space between `move` and `=>` or `:`.
- `apply/` and `apply:` carry no space between `apply` and `/` or `:`.
- `rewrite /definition` carries one space between `rewrite` and the slash-prefixed unfold.

## Indentation

- Two subgoals: first indented two spaces, second unindented. Use `last first` to put the smallest / least meaningful goal first.
- More than two: bullets at levels 1, 2, 3 (`-`, `+`, `*`).
- One main-flow goal among secondaries: remove the bullet from the main line and unindent; indent secondaries with bullets.

## Tactics to prefer

- `have H : T := term` or `have H := term` for forward reasoning. Not `pose proof term as H`.
- `congr f` or an explicit congruence lemma. Not `f_equal`.
- `case: (eqVneq X Y) => h` for equal-or-not splits. Not `have [/eqP h|h] := boolP (X == Y)`.
- `done`, `trivial`, `exact`, or a named tactic at the end. Not bare `auto`, `tauto`, or `intuition`.
- `have` for a named forward step. Not `assert (...)`.
- `rewrite !inE` for bounded-match rewrites; never `rewrite !` on arithmetic lemmas such as `addn1`, `addnA`, `subnK`.

## Banned and risky constructs

- `Focus N`, `{ ... }` for goal grouping.
- `rewrite !` applied to lemmas that can rewrite unboundedly (arithmetic, commutativity).
- `Admitted.` and `Abort.` in code paths intended to compile.
- `lia` (not available in this project; use MathComp nat lemmas).

## Comment style for lemmas, theorems, and nontrivial definitions

Every `Lemma`, `Theorem`, `Fact`, `Corollary`, `Proposition`, and every
non-`Local`, multi-line `Definition` / `Fixpoint` must carry an
immediately-preceding comment. The style is **short prose**, NOT a
stacked-slot template.

Rules:

- 1-8 lines maximum for `Lemma` / `Theorem` / `Fact` / `Corollary` /
  `Proposition`. 1-15 lines for non-`Local` multi-line `Definition` /
  `Fixpoint`. 1-25 lines for `Hypothesis` / `Variable` (Section
  parameters often carry rich narrative — proof chains, intent that
  downstream proofs depend on).
- Free prose. Do NOT stack `Kind:` / `Why:` / `Used by:` slot lines
  as a template — a single inline mention is fine; two or more on
  separate lines is rejected by rule H002 (TEMPLATE_SLOTS).
- State the entity's conceptual role or the proof's key trick. Do
  NOT restate the type signature in prose (H002 TYPE_RESTATEMENT).
- Inline math notation (`#|T|`, `1/m`, `'I_n`) is preferred over
  identifier brackets (`[T]`, `[card_msg]`).
- No cross-references to plan files (`~/.claude/plans/...md`),
  plan-task tokens (`T4`, `U2`, `W3`), or absolute line numbers
  (`(line 130)`, `[file.v:142]`). These go stale on refactor and are
  rejected by H002 (STALE_CROSSREF).
- When several entities share a family role (e.g., type-bridge
  bijections, cardinality positivity, `Defined.`-ended record
  builders), one comment for the family is sufficient.
- Honest uncertainty markers are acceptable ("Not sure why X
  doesn't work").

### Purposive framing first

A prose-style comment that passes the mechanical checks can still
land low on clarity if it describes the local proof mechanism
instead of the entity's purpose in the larger system. Lead with one
of:

- **ROLE** — what this entity does in the architecture and what
  other entities depend on it.
- **RATIONALE** — why this design choice exists; what constraint
  or invariant it discharges.
- **ALTERNATIVE** — what other choices are compatible with the
  type and why this one was selected; in what regime an
  alternative would be preferable.

Reserve proof-tactic mechanics (which lemma the proof reduces to,
which obligations collapse, which side-conditions unify) for a
second sentence — and only when the mechanics themselves carry
architectural meaning (e.g., `emptym` location set enabling
`fseparate0m` is itself a design choice; "the proof is by induction
on n" usually is not).

Three-tier example: `chmsg_of_msgK : cancel chmsg_of_msg msg_of_chmsg`

Mechanism-only (avoid — rejected by H002 MECHANISM_ONLY when zero
architecture nouns appear):
```coq
(* Cancellation bijection for the message-side type bridge.
   The proof reduces directly to enum_rankK. *)
```

Purposive (preferred — passes all five H002 detectors):
```coq
(* Bijection to build type bridge between AHE and SSProve. *)
```

Purposive + architecturally-informative mechanism (also preferred —
the mechanism carries architectural meaning):
```coq
(* Bijection bridging the AHE-side `plain AHE` Type and the
   SSProve-side `t_msg` choice_type code. Used by every
   encryption-oracle proof to round-trip messages through the
   SSProve type-code layer. *)
```

### Acceptable examples (prose-style, conceptual focus)

```coq
(* Bijection to build type bridge between AHE and SSProve. *)
Lemma chmsg_of_msgK :
  cancel chmsg_of_msg msg_of_chmsg.
Proof. exact: enum_rankK. Qed.
```

```coq
(* For every predictor in the considered class, the probability that
   the predictor correctly guesses V_2 from the leaked-ciphertext
   game is at most 1 / card_t_msg.
   (distr.mu is the probability mass function of a sub-distribution;
    SSProve uses sub-distribution since its relative monad of
    sub-distributions on choice_type.) *)
Hypothesis Pr_guess_enc_zero_le_invm :
  forall (predictor : predictor_guesser t_msg t_cipher), ...
```

```coq
(* A stateless and oracle-free adversary: the predictor ignores all
   the leaked ciphertexts the game provides. When asked for its
   guess, it samples a fresh uniformly random plaintext and submits
   that as its guess at V_2. Used for realizing the lower-bound
   side of the secrecy theorem. *)
Definition random_guess_adv : predictor_guesser t_msg t_cipher := ...
```

### Unacceptable examples (over-templated, stale-crossref, type-restatement)

```coq
(** chcipher_of_cipherK - cancel law for the ciphertext-side
    bijection.  Routes through [eq_rect] cancellation on the
    [cipher_finType_eq] cast plus [enum_rankK].
    Kind: cancellation.
    Why: discharges [chcipher_of_cipherK] (line 130).
    Used by: T1 V_2-aware rebuild. *)
```

Reasons rejected by H002:

- TEMPLATE_SLOTS: `Kind:` / `Why:` / `Used by:` stacked on separate
  lines (the "Naming:" line, when present alone, is not counted —
  see the naming section below).
- STALE_CROSSREF: the plan-task token `T1` and the absolute line
  number `(line 130)` are tied to a specific plan revision and go
  stale the moment the file is refactored.
- TYPE_RESTATEMENT: the first sentence "cancel law for the
  ciphertext-side bijection" merely paraphrases the lemma's stated
  type `cancel chcipher_of_cipher cipher_of_chcipher`, adding no
  information the reader cannot already see.
- OVER_LENGTH: 7 lines for a `Lemma` whose budget is 5.

## Naming conformance or justification

Any Lemma, Theorem, Fact, Corollary, Proposition, Definition, Fixpoint,
CoFixpoint, Let, Hypothesis, Variable, or nested `let x := ...` binding
whose name breaks MathComp grammar must carry a `Naming:` line in the
preceding comment (or an inline `(* Naming: ... *)` comment for local
`let` bindings). Non-conformance signals:

- redundant kind-suffixes `_lemma`, `_theorem`, `_fact`, `_corollary`,
  `_proposition`, `_proof`, `_thm`
- generic drift tokens `_works`, `_test`, `_tmp`, `_old`, `_new`,
  `_foo`, `_bar`, `_baz`, `_placeholder`, `_helper`, `_xxx`, `_hack`
- five or more underscore-separated lowercase components without a
  canonical MathComp suffix at the tail

`Naming:` is intentionally EXCLUDED from H002's stacked-slot detector,
because it is the prescribed justification slot for F001/G001 findings.
A prose-style comment that includes one inline `Naming:` line remains
valid; only the stacked `Kind:` / `Why:` / `Used by:` template is
rejected.

Example of a valid justification (prose + single `Naming:` line):

```coq
(* Alias of ord_pos_ge0 kept for external test compatibility.
   Naming: intentional; mirrors the upstream Python module. *)
Lemma my_proof_works : forall n : nat, 0 < n.+1.
Proof. exact: ord_pos_ge0. Qed.
```

For a nested `let`:

```coq
(* tmp_x is a throwaway binder, scoped to two lines.
   Naming: throwaway. *)
Lemma main_result : ...
Proof.
  ...
  let tmp_x := I in
  exact: tmp_x.
Qed.
```

## Infotheo-specific conventions

- `ring_scope` is locally opened in several files (for example `dumas2017dual/dsdp/dsdp_progress.v`). Use `%N` for nat operations inside a `ring_scope` block.
- When unfolding a `rank` or `pose` function, unfold first, then substitute extracted equalities. For example `rewrite /rank Hi0 -Hjeq /=` rather than `rewrite -Hjeq /rank`.
- Use `Show.` to inspect goals before a speculative tactic.
- Use `apply ` and `exact ` with a space rather than a colon when debugging; the error messages are clearer.
