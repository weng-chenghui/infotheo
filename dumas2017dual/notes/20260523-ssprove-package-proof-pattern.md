# 2026-05-23 — SSProve package proof pattern: decompose, align, witness, close

## The reference proof

```coq
Lemma valid_boolean_shell_link
    (pred : predictor_guesser) :
  ValidPackage (locs pred) game_iface A_export (boolean_shell ∘ pred).
Proof.
case: boolean_shell.(pack_valid) => he1 hi1.
split.
- move=> o.
  rewrite he1 /link.
  split.
  + move=> [f Hf].
    exists (fun x => code_link (f x) pred).
    by rewrite //= mapmE Hf.
  + rewrite //= mapmE.
    change (setm emptym _ _) with (boolean_shell.(pack)).
    move=> [f Hf].
    change (setm emptym _ _) with (boolean_shell.(pack)) in Hf.
    case Eb: (boolean_shell.(pack) o.1) => [[S [T g]]|].
    * rewrite Eb /= in Hf.
      by move: Hf => [= ? ?]; subst; exists g.
    * by rewrite Eb /= in Hf.
- move=> n F x.
  rewrite /fhas /link mapmE.
  change (setm emptym _ _) with (boolean_shell.(pack)).
  case Eb: (boolean_shell.(pack) n) => [[S' [T' f']]|]; last by [].
  move=> /= [= ?]; subst F => /=.
  eapply (@valid_code_link_residual _ (locs pred)
            (unionm game_iface guesser_export) game_iface guesser_export).
  + have /= Hbs_valid := hi1 n (existT _ S' (existT _ T' f')) x Eb.
    eapply valid_injectLocations; [| exact: Hbs_valid].
    exact: fsub0map.
  + eapply valid_package_inject_import; last exact: pred.(pack_valid).
    fmap_solve.
Qed.
```

## The pattern, in one phrase

**Decompose → align → witness → close**, with type-equality extraction
sitting between "decompose" and "witness" whenever a dependent pair shows
up.

For this particular proof the pattern instantiates as follows.

### 1. Decompose

Decompose the goal until it is small enough to look at one piece at a
time.

- `split` on `ValidPackage` to get the two field obligations.
- `split` on the inner `↔` of `valid_exports` to get two implications.
- `move=> [f Hf]` to destructure existentials.
- `case Eb:` on `boolean_shell.(pack) o.1` to fork on whether the
  lookup hits an entry.

### 2. Align

Align the goal with a lemma or hypothesis.  This is the step that does
the actual work: almost every line of the proof is a translation from
one form into another so that a stored fact about the original package
becomes applicable.

- `rewrite he1` substitutes the exports of `boolean_shell` for
  `A_export` so we can compare the two `setm`s directly.
- `rewrite //= mapmE` converts the `mapm` plumbing inside the linked
  package into an `omap` on the original's lookup, which is what the
  case analysis needs.
- `change (setm emptym _ _) with (boolean_shell.(pack))` (backed by
  `boolean_shell_pack_setm`) renames the unfolded form so that
  `Eb : boolean_shell.(pack) o.1 = …` lines up.
- `eapply valid_code_link_residual` reduces the body-validity question
  to two smaller validity claims that match the shapes of `hi1` and
  `pred.(pack_valid)` respectively.

### 3. Extract type equalities

When an existential carries a dependent pair (the
`existT S (existT T f)` triples are the recurring offender), peel the
outer `existT`s and substitute.

- `move: Hf => [= ? ?]; subst` peels `Some` then the two `existT`s,
  learns `S = chsrc o` and `T = chtgt o`, and rewrites them everywhere.
  After this, the witness's outer types match the goal's expected types
  and the remaining content can be supplied.

### 4. Witness

Supply the witness for the existential, when there is one to supply.

- `exists g`, `exists (fun x => code_link (f x) pred)`, etc.  (Either
  `exists` or `eexists` works when the witness is fully spelled out;
  this proof uses the former.)

### 5. Close

Close with a hypothesis in context via the ssreflect `by` terminator.
`by` delegates to `done`, which is itself a curated bundle that tries
`reflexivity`, `assumption` / `eassumption`, `discriminate`,
`contradiction`, and `split` (on a conjunction), among others.

- `by` after `exists g` closes via `assumption` matching `Eb` in
  context.
- `by rewrite Eb /= in Hf` closes the `None` case: the rewrite reduces
  `Hf` to `None = Some _`, and `done` then dispatches to `discriminate`.

## Why the type-equality step exists

The function-table entries are dependent triples
`(src_type ; tgt_type ; body)`, and proofs about them constantly bump
into the need to unify the *outer types* before talking about the
*inner body*.  The `[=]` injection pattern plus `subst` is the standard
SSProve idiom for that bump.  It corresponds to the universe-management
gymnastics that one normally writes informally as "and these source and
target types must agree, which is forced by the equation we just
inspected".

## What the lemmas and hypotheses are actually doing

| concern | tool |
|---|---|
| linking does not change export structure | `he1` (boolean_shell's own `valid_exports`), `mapmE`, `boolean_shell_pack_setm` |
| body well-formedness of original package | `hi1` (boolean_shell's own `valid_imports`) |
| location widening | `valid_injectLocations` + `fsub0map` |
| import widening | `valid_package_inject_import` + `fmap_solve` |
| partial link residual | `valid_code_link_residual` (defined at the top of this file) |
| pred's own validity | `pred.(pack_valid)` |

## Takeaway

The high-level shape really is: **crack the obligation into smaller
obligations, rename / fold / inject until each one matches the shape of
a hypothesis or named lemma, then close**.

The proof's "creative" content is concentrated in two places.  First,
the choice of lemmas to align against — `valid_code_link_residual` is
the bespoke one specific to this file; everything else is upstream
SSProve.  Second, noticing that the encoding round-trip
(`chcipher_of_cipherK`) makes the body-validity step go through without
a more elaborate detour.  Everything else is bookkeeping.

This pattern — decompose, align, inject types, witness, close — is the
workhorse pattern for SSProve package-system proofs generally.  Once
you have done a handful of them, the only real variability between
proofs is which named lemma sits at the "align" step, and the rest is
muscle memory.

## What "align" means

By "align" I mean: **reshape the goal until it has the literal syntactic
form that some named lemma's conclusion (or some hypothesis in context)
is talking about**.  The logical content of the goal does not change.
What changes is how it is *spelled out* — which head symbol is on the
outside, how parentheses fall, which definition is unfolded, which
existential variables are named — so that you can now point to a stored
fact and say "this is what I want, you have already proved it".

### Why alignment is a distinct step

In informal mathematics you write things like

> By Lemma X, we conclude Y.

and the reader's eye fills in the small reshaping that makes Lemma X's
conclusion match Y.  In a proof assistant the reshaping is not
automatic.  Each lemma's conclusion is one *specific* syntactic shape,
and the goal you have at a given moment is *another*, possibly very
similar but not identical shape.  To use the lemma, you must first
manipulate the goal so the two shapes coincide.  That manipulation is
what I called "alignment".

So in a typical proof step you have three logical phases:

1. **Decompose** — break a big goal into pieces (`split`, `case:`,
   `intro`).
2. **Align** — reshape each piece so it matches a known fact.
3. **Discharge** — point at the known fact (`exact:`, `apply:`,
   `assumption`, `by`).

Decomposition reveals the right pieces, alignment makes each piece look
like something you already have a name for, and discharge closes it.
The middle step is the one I named "align".

### What "align" looks like concretely

Alignment moves from `valid_boolean_shell_link`, each labelled by the
shape it was producing:

| tactic | what it reshapes |
|---|---|
| `rewrite he1` | replaces `A_export` with `boolean_shell`'s exports field — now the goal compares two `setm`s directly |
| `rewrite //= mapmE` | turns the linked package's `mapm φ m k` lookup into `omap φ (m k)`, exposing the original `m k` so case analysis can attack it |
| `change (setm emptym _ _) with (boolean_shell.(pack))` | renames an unfolded singleton table to its named form so `Eb : boolean_shell.(pack) o.1 = …` becomes literally applicable |
| `case Eb: (boolean_shell.(pack) o.1) => […\|…]` | produces one subgoal per branch where the lookup is *literally* `Some …` or `None`, and — the load-bearing feature — *introduces the equation `Eb` into context* so that subsequent `rewrite Eb` can substitute the concrete value into both the goal and `Hf` |
| `rewrite Eb /= in Hf` | substitutes the case witness into the equation in `Hf`, so `Hf`'s shape now contains the same concrete `Some` that the goal mentions |
| `eapply valid_code_link_residual` | rewrites the goal "this body is valid in this import set" into two simpler goals whose shapes match `hi1` and `pred.(pack_valid)` directly |

In every case, the goal *after* the tactic is logically equivalent to
the goal *before*, but it now looks like the conclusion of some named
lemma, the right-hand side of some existing equation, or some hypothesis
in context.  After alignment, the discharge step is trivial — usually
`exact:`, `assumption`, or `by`.

### Tactics that count as alignment

The recurring building blocks:

- **Rewriting** (`rewrite L`, `rewrite -L`, `rewrite [pat]L`) — replace
  one form with another via an equality lemma.
- **Folding / unfolding** (`change A with B`, `unfold f`) — rename a
  term using its definition.
- **Reduction** (`simpl`, `cbn`, `//=`) — beta/iota/delta reduction to
  expose computation.
- **Specialization** (`apply: lemma with (x := …)`) — fix a quantified
  variable to a specific value before applying.
- **Reordering / commutation** (`rewrite addrA`, `ssprove_swap_rhs`) —
  rearrange independent operations into a different syntactic order.
- **Case-driven equation substitution** (`case Eb: … => …` followed by
  `rewrite Eb`) — introduce a new equation that lets a known fact apply.
- **Apply with subgoals** (`apply: lemma`) — turn the goal into the
  lemma's premises, which become the new sub-goals to align further.

All of these are alignment moves.  None of them solve the goal by
themselves; each shifts the goal into a form that some other step can
solve.

### The mental model

Think of the proof state as a *jigsaw piece*.  The available lemmas and
hypotheses are *slots* with specific shapes.  Your job is to rotate,
flip, and reshape the jigsaw piece until it fits one of the slots.
Once it fits, you slot it in and that piece of the proof is done.
*Align* is the rotate-and-reshape phase; *discharge* is the slotting
in.

So when I wrote "align the goal with a lemma or hypothesis", I meant
exactly: **reshape the goal — without changing what it asserts — so
that it now textually matches some stored fact, after which a one-tactic
discharge closes it**.  In `valid_boolean_shell_link` every line in the
proof body except the structural `split`, the case-splits, the
witnesses, and the final `by`s is an alignment move.

## `apply` / `eapply` are dual-purpose

`apply` and `eapply` are not pure discharge tactics — they are
*dual-purpose*: they can either discharge or align, depending on
whether the lemma's premises are already satisfied at the moment of
application.

### The two modes

**Discharge mode.**  When the lemma being applied has no premises (or
all its premises are trivially closed by the surrounding context —
typeclass resolution, evar instantiation), the apply finishes the
current subgoal in one shot.

```coq
apply: rreflexivity_rule.
   (* no subgoals — closed *)
```

**Alignment mode.**  When the lemma has premises that are not already
satisfied, the apply *replaces* the current goal with those premises as
new subgoals.  The original goal is reshaped into a list of smaller,
more specific obligations.

```coq
eapply valid_code_link_residual.
   (* two new subgoals: one ValidCode obligation per side *)
```

The proof state after the apply is logically equivalent to the proof
state before (the lemma `premises → conclusion` is sound, so proving
the premises suffices to conclude what was needed).  But the goal
*shape* has changed — sometimes drastically.  That is exactly the
"reshape the goal" behaviour of alignment.

### Where it sits in this proof

Both modes appear in `valid_boolean_shell_link`:

| call | mode | effect |
|---|---|---|
| `apply: rreflexivity_rule` *(used elsewhere in this file, not in `valid_boolean_shell_link` — included as a contrast)* | discharge | closes the relational triple in one step |
| `exact: fsub0map` | discharge | closes the `fsubmap emptym _` subgoal |
| `exact: Hbs_valid` | discharge | closes via a hypothesis already in context |
| `eapply valid_code_link_residual` | alignment | turns one validity goal into two simpler ones |
| `eapply valid_injectLocations; [\| exact: Hbs_valid]` | alignment + discharge | apply produces 2 subgoals, the dispatcher closes the second immediately |
| `eapply valid_package_inject_import; last exact: pred.(pack_valid)` | alignment + discharge | apply produces 2 subgoals, `last exact:` closes the last |

The bottom two rows are particularly telling: a single `eapply … ; [...]`
chain can simultaneously reshape the goal *and* discharge some of the
resulting subgoals.  So in practice these `eapply` calls are doing
alignment work, with the dispatcher syntax discharging the easy halves
in the same line.

### Refined taxonomy

The clean way to categorise tactics is by what they do to the *number*
and *shape* of subgoals:

- **Pure decomposition** — multiplies the number of subgoals from one
  piece into several, by structural inversion: `split`, `case`,
  `destruct`.
- **Pure alignment** — changes the shape of a subgoal without changing
  its count: `rewrite`, `change`, `unfold`, `simpl`, `cbn`.
- **Mixed alignment / decomposition** — replaces one subgoal with
  several, by appealing to a lemma: `apply`, `eapply` when the lemma
  has premises.
- **Pure discharge** — closes a subgoal in one step, replacing one
  with zero: `exact:`, `assumption`, `by`, `done`, `apply` when the
  lemma has no open premises.
- **Intro / witnessing** — consumes connective structure to expose
  hypotheses or fill existentials: `intro` / `move=>`, `exists`,
  `eexists`.

`apply` / `eapply` straddle "mixed alignment / decomposition" and
"discharge", with the distinguishing factor being whether any premises
survive after unification.  The vast majority of `apply`s in SSProve
package-system proofs are in alignment mode, precisely because every
package-validity lemma comes with side-condition premises that
themselves need to be discharged.
