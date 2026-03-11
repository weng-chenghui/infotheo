# Prove a Rocq/Coq lemma

Prove the lemma described by the user. Follow this strategy strictly.

Consult memory files for known pitfalls and patterns:
- `ordinal_bigop_techniques.md` — ordinal equality, tperm, bigop manipulation
- `rewrite_pitfalls.md` — dependent types, notations, division, rewrite-bang/rewrite-question blowups, `'Z_(p*q)`
- `coq_debugging.md` — `//` weakness, scope inference, name shadowing, signatures
- `sumn_fixpoint_pitfalls.md` — `sumn` eager reduction, `Arguments simpl never`, higher-order unification failures, `congr` vs `congr1`

## Arguments

$ARGUMENTS

## Setup

- Compiler: `/Users/cheng-huiweng/Projects/coq/_opam/bin/coqc`
- Include flag: `-R /Users/cheng-huiweng/Projects/coq/infotheo infotheo`
- Debug directory: `/tmp/coq_debug/`

### Debug scripts (create once, reuse freely)

At the start of a session, create helper scripts in `/tmp/coq_debug/` so the user only needs to grant Bash permission once. **Never write inline temp files that require separate permission each time.** Use the `Write` tool (not `cat` heredoc via Bash) to create these scripts, so the user doesn't need to re-permit each file creation.

Required scripts:
- **`check.sh`** — Takes a Coq command string, prepends the file up to a given section boundary, compiles, and prints results. For `Check`, `About`, `Search` queries.
- **`goal.sh`** — Takes a line number and optional extra tactic, extracts the file up to that line, appends `Show. Abort.` + section closers, compiles, and prints the goal state.
- **`compile.sh`** — Compiles the actual file with `make` and filters noise.

Example `goal.sh`:
```bash
#!/bin/bash
cd /path/to/project
head -"$1" path/to/file.v > /tmp/coq_debug/test.v
[ -n "$2" ] && echo "$2" >> /tmp/coq_debug/test.v
echo "Show." >> /tmp/coq_debug/test.v
echo "Abort." >> /tmp/coq_debug/test.v
echo "End section_name." >> /tmp/coq_debug/test.v
coqc -R . infotheo /tmp/coq_debug/test.v 2>&1 | grep -v "Warning\|^File\|incomp\|overrid\|ambigu\|^New\|^\[" | sed '/^$/d'
```

## Strategy

### 1. Read the target file

- Read the file containing the lemma. Do NOT read imported files yet — only read specific dependencies later when you need a definition's type or body.

### 2. See the goal and unfold definitions

Use `goal.sh`:

- Run `goal.sh <line_number>` to see the goal at a given proof point.
- Run `goal.sh <line_number> "rewrite /def1 /def2 /=."` to see the goal after unfolding.

### 3. Check and search for lemmas

Use `check.sh`:

- Use `Check @lemma_name.` for candidate lemmas.
- Use `Search (pattern).` or `Search "keyword".` when the goal almost matches but differs in one subterm.
- Batch multiple queries into one call.

### 4. Build the proof

- Add 2-3 tactics at a time, use `goal.sh` to verify progress.
- After writing the full proof attempt, use `compile.sh`. If it fails, bisect to find the failing tactic.

### 5. Apply to the real file

- Once the proof compiles via the debug scripts, edit the actual source file.
- Run `compile.sh` to confirm.

## Rules

- **Do NOT compile the full file to test individual tactics. Always use `goal.sh`.** Full-file compilation takes ~5 min; `goal.sh` takes seconds to a minute.
- Use `apply`/`exact` (not ssreflect `:` variants) during debugging — they give clearer errors. Use ssreflect style (`exact:`, `apply:`) in the final proof only.
- Never guess a proof without seeing the goal via `Show.` first.
- If a compilation fails with a type mismatch or stale-signature error, check that imported `.vo` files are newer than their `.v` sources. Recompile stale dependencies bottom-up with `coqc -R . infotheo <file>.v` from the project root.
- **Think before compile:** Before each `goal.sh` call, write 1-2 sentences explaining what you expect the tactic to do and why. This forces deliberation over guessing.

### Batch-testing multiple tactics

When uncertain between tactics, test them all in one `goal.sh` call instead of compiling separately for each:

```bash
goal.sh 2364 "try (by apply: lemma1). try (by apply: lemma2). idtac \"neither\"."
```

For more structured batch testing, create a `goal_multi.sh` script:

```bash
#!/bin/bash
# goal_multi.sh <line> "tactic1" "tactic2" "tactic3" ...
# Tests multiple tactics against the same goal, reports OK/FAIL for each.
LINE=$1; shift
cd /path/to/project
head -"$LINE" path/to/file.v > /tmp/coq_debug/base.v
for tactic in "$@"; do
  cp /tmp/coq_debug/base.v /tmp/coq_debug/test.v
  echo "$tactic" >> /tmp/coq_debug/test.v
  echo "Show. Abort." >> /tmp/coq_debug/test.v
  echo "End section_name." >> /tmp/coq_debug/test.v
  if coqc -R . infotheo /tmp/coq_debug/test.v >/dev/null 2>&1; then
    echo "OK: $tactic"
  else
    echo "FAIL: $tactic"
  fi
done
```

This tests N tactics in one invocation instead of N separate compilations.
