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

`Naming:` is the prescribed justification slot for F001/G001 findings.
A comment that includes one inline `Naming:` line remains valid.

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
