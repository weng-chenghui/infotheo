# 2026-05-21 — Delta-unfolding (Coq/Rocq reduction primer)

Delta-unfolding (or delta-reduction) is one of the basic reduction rules of
the Calculus of Inductive Constructions, the type theory underlying
Coq/Rocq.  It is the act of replacing a defined constant with the body it
is bound to.

For example, given:

```coq
Definition foo := fun x : nat => x + 1.
```

the term `foo 3` reduces by delta to `(fun x : nat => x + 1) 3` (then by
beta to `3 + 1`, then by iota / arithmetic to `4`).  The "delta" step is
specifically the `foo  ⇝  fun x => x + 1` substitution.

The other reductions you usually see paired with it:

- **beta** — apply a lambda: `(fun x => t) u  ⇝  t[x := u]`
- **iota** — compute a `match` / fixpoint on a constructor:
  `match S k with S n => f n | 0 => g end  ⇝  f k`
- **zeta** — substitute a `let`: `let x := u in t  ⇝  t[x := u]`
- **eta** — `(fun x => f x)  ⇝  f` (when allowed)
