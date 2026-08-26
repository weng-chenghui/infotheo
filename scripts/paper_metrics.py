#!/usr/bin/env python3
"""Generate the formalization metrics table for the CPP 2027 paper.

Produces every number in that table from the working tree in one pass, so the
table can be refreshed before submission and any drift between the paper and
the sources is reported rather than silently absorbed.

Sizes are specification and proof lines reported by ``coqwc``, summed per row.
Comments and blank lines are therefore excluded, which is what the paper's
caption claims.

A declaration counts as a result iff it is a ``Lemma``, ``Theorem``, or
``Corollary`` in the file scope below, including ``Local`` and attribute
prefixed forms.  A result is *main* iff the paper cites it by name in a
``\\coqin{}``, and *technical* otherwise.  The paper is the authority for that
split, so its source path is a required argument.

All three counts are counts of declarations, so that main and technical
partition the total.  A name carried by two declarations, such as the
``enc_mul_dist`` of Benaloh and the one of Paillier, is therefore two results
even though the paper cites the name once.

Usage:

    python3 scripts/paper_metrics.py --paper ../../publications/sep10CPP2027/main.tex
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

# ── File scope ─────────────────────────────────────────────────────────────
#
# One entry per table row.  A path ending in "/" is a directory whose .v files
# are taken recursively; anything else is an exact file.  Rows must partition
# the scope: a file claimed by two rows is an error, and so is a file under a
# claimed directory that no row wants and DELIBERATELY_OUT_OF_SCOPE does not
# name.

ROWS: dict[str, list[str]] = {
    "Interpreter soundness": [
        "smc/smc_interpreter.v",
        "smc/smc_interpreter_sound.v",
    ],
    "Session types": [
        "smc/smc_session_types.v",
    ],
    r"\pismc{} DSL": [
        "smc/pismc.v",
        "dumas2017dual/dsdp/core/dsdp_pismc.v",
    ],
    "AHE hierarchy": [
        "homomorphic_encryption/",
    ],
    "Information-theoretic security proofs": [
        "dumas2017dual/entropy_fiber/",
        "dumas2017dual/lib/",
        "dumas2017dual/dsdp/fdist_hopping/indcpa_game.v",
    ],
    r"\dsdp{} protocol and its security proofs": [
        "dumas2017dual/dsdp/",
    ],
}

# Directories the rows claim recursively, so that a file added under one of
# them is noticed instead of dropped.
CLAIMED_TREES = [
    "smc/",
    "homomorphic_encryption/",
    "dumas2017dual/",
]

# Files under a claimed tree that the paper does not count, with the reason.
DELIBERATELY_OUT_OF_SCOPE: dict[str, str] = {
    "smc/graded_resource.v": "graded monad resources, not presented in this paper",
    "smc/smc_interpreter_mkBind.v": "draft, absent from _CoqProject",
    "smc/smc_party_indep.v": "draft, absent from _CoqProject",
    "smc/znto_lemmas.v": "draft, absent from _CoqProject",
}

# Whole subtrees under a claimed tree that the paper does not count.
OUT_OF_SCOPE_TREES: dict[str, str] = {
    "smc/security_models/": "scoped to the thesis chapter, uncited here",
    "dumas2017dual/blueprint/": "not Rocq source",
}

DECLARATION = re.compile(
    r"^[ \t]*(?:Local[ \t]+|Global[ \t]+|Program[ \t]+|#\[[^\]]*\][ \t]+)*"
    r"(Lemma|Theorem|Corollary)[ \t]+([A-Za-z_][A-Za-z0-9_']*)",
    re.MULTILINE,
)

CITATION = re.compile(r"\\coqin\{([^}]*)\}")


def expand(patterns: list[str]) -> list[Path]:
    """Resolve one row's patterns to a sorted list of .v files."""
    out: set[Path] = set()
    for pat in patterns:
        if pat.endswith("/"):
            for p in sorted((REPO_ROOT / pat).rglob("*.v")):
                rel = p.relative_to(REPO_ROOT).as_posix()
                if rel in DELIBERATELY_OUT_OF_SCOPE:
                    continue
                if any(rel.startswith(t) for t in OUT_OF_SCOPE_TREES):
                    continue
                out.add(p)
        else:
            p = REPO_ROOT / pat
            if not p.is_file():
                sys.exit(f"error: {pat} does not exist")
            out.add(p)
    return sorted(out)


def resolve_rows() -> dict[str, list[Path]]:
    """Assign each file to exactly one row, later rows yielding claimed files."""
    rows: dict[str, list[Path]] = {}
    taken: dict[Path, str] = {}
    # Rows with explicit file lists win over rows that claim a whole tree, so
    # that dsdp_pismc.v lands in the DSL row and indcpa_game.v in the library
    # row rather than in the protocol row that contains their directories.
    order = sorted(ROWS, key=lambda r: any(p.endswith("/") for p in ROWS[r]))
    for name in order:
        files = []
        for f in expand(ROWS[name]):
            if f in taken:
                continue
            taken[f] = name
            files.append(f)
        rows[name] = files
    return {name: rows[name] for name in ROWS}


def check_coverage(rows: dict[str, list[Path]]) -> list[str]:
    """Report .v files under a claimed tree that no row counts."""
    counted = {f for files in rows.values() for f in files}
    unassigned = []
    for tree in CLAIMED_TREES:
        for p in sorted((REPO_ROOT / tree).rglob("*.v")):
            rel = p.relative_to(REPO_ROOT).as_posix()
            if p in counted:
                continue
            if rel in DELIBERATELY_OUT_OF_SCOPE:
                continue
            if any(rel.startswith(t) for t in OUT_OF_SCOPE_TREES):
                continue
            unassigned.append(rel)
    return unassigned


def coqwc(files: list[Path]) -> tuple[int, int, int]:
    """Return (spec, proof, comments) summed over files, via coqwc."""
    if not files:
        return (0, 0, 0)
    args = ["coqwc"] + [str(f) for f in files]
    try:
        out = subprocess.run(args, capture_output=True, text=True, check=True).stdout
    except FileNotFoundError:
        sys.exit("error: coqwc not on PATH (run: eval $(opam env))")
    except subprocess.CalledProcessError as e:
        sys.exit(f"error: coqwc failed\n{e.stderr}")
    # coqwc prints a total line only for more than one file.
    last = out.strip().splitlines()[-1].split()
    return (int(last[0]), int(last[1]), int(last[2]))


def declarations(files: list[Path]) -> list[tuple[str, str, str]]:
    """Return (file, kind, name) for every Lemma/Theorem/Corollary."""
    found = []
    for f in files:
        rel = f.relative_to(REPO_ROOT).as_posix()
        text = f.read_text(encoding="utf-8", errors="replace")
        for m in DECLARATION.finditer(text):
            found.append((rel, m.group(1), m.group(2)))
    return found


def cited_names(paper: Path) -> set[str]:
    """Identifiers the paper names in \\coqin{}, excluding file paths.

    Most citations are definitions, types, constructors, or inline code rather
    than lemmas, so the caller filters against the declarations it wants.
    """
    text = paper.read_text(encoding="utf-8", errors="replace")
    text = strip_comments(text)
    text = rejoin_split_citations(text)
    names = set()
    for m in CITATION.finditer(text):
        token = m.group(1).strip()
        if not token or "/" in token or token.endswith(".v"):
            continue
        names.add(token)
    return names


COMMENT = re.compile(r"(?<!\\)%.*$", re.MULTILINE)

# A long identifier is broken across a line as \coqin{head_}\allowbreak\coqin{tail},
# which must be read back as the single name it prints.
SPLIT_CITATION = re.compile(r"\\coqin\{([^}]*)\}\s*\\allowbreak\s*\\coqin\{([^}]*)\}")


def strip_comments(text: str) -> str:
    """Drop LaTeX comments, so commented-out citations do not count."""
    return COMMENT.sub("", text)


def rejoin_split_citations(text: str) -> str:
    r"""Glue \coqin{} pairs that a line break split into halves of one name."""
    while True:
        joined = SPLIT_CITATION.sub(lambda m: "\\coqin{" + m.group(1) + m.group(2) + "}", text)
        if joined == text:
            return text
        text = joined


def vocabulary(files: list[Path]) -> set[str]:
    """Every identifier-shaped token appearing anywhere in the scope sources."""
    word = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
    seen: set[str] = set()
    for f in files:
        seen.update(word.findall(f.read_text(encoding="utf-8", errors="replace")))
    return seen


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--paper", required=True, type=Path,
                    help="path to the paper's main.tex, which defines the main/technical split")
    ap.add_argument("--latex", action="store_true", help="print the table body only")
    args = ap.parse_args()

    if not args.paper.is_file():
        sys.exit(f"error: paper not found: {args.paper}")

    rows = resolve_rows()

    unassigned = check_coverage(rows)
    if unassigned:
        print("warning: .v files under a counted tree that no row claims:", file=sys.stderr)
        for rel in unassigned:
            print(f"  {rel}", file=sys.stderr)
        print("  add them to a row or to DELIBERATELY_OUT_OF_SCOPE\n", file=sys.stderr)

    sizes = {name: coqwc(files) for name, files in rows.items()}
    all_files = [f for files in rows.values() for f in files]
    decls = declarations(all_files)

    declared = {name for _, _, name in decls}
    cited = cited_names(args.paper)
    main_names = cited & declared

    # A citation that names no token anywhere in the scope sources is stale:
    # the identifier was renamed or removed and the paper still points at it.
    # Citations that resolve to a definition or constructor are ordinary.
    identifier = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
    vocab = vocabulary(all_files)
    stale = {n for n in cited if identifier.match(n) and n not in vocab}

    total_loc = sum(s + p for s, p, _ in sizes.values())
    n_total = len(decls)
    n_main = sum(1 for _, _, name in decls if name in main_names)
    n_technical = n_total - n_main

    if args.latex:
        emit_latex(sizes, total_loc, n_main, n_technical, n_total)
        return

    print(f"{len(all_files)} files in scope\n")
    print(f"{'Row':44s} {'spec':>6s} {'proof':>6s} {'size':>7s}")
    for name, files in rows.items():
        spec, proof, _ = sizes[name]
        print(f"{name:44s} {spec:>6d} {proof:>6d} {spec + proof:>7d}")
    print(f"{'TOTAL':44s} {'':>6s} {'':>6s} {total_loc:>7d}\n")

    kinds: dict[str, int] = {}
    for _, kind, _ in decls:
        kinds[kind] = kinds.get(kind, 0) + 1
    print(f"Main lemmas and theorems   {n_main:>4d}  "
          f"({len(main_names)} distinct names)")
    print(f"Technical lemmas           {n_technical:>4d}")
    print(f"Total lemmas and theorems  {n_total:>4d}  "
          f"({', '.join(f'{k} {v}' for k, v in sorted(kinds.items()))})\n")

    print("Main results, as cited by the paper:")
    for name in sorted(main_names):
        print(f"  {name}")

    if stale:
        print("\nwarning: the paper cites identifiers that appear nowhere in the sources",
              file=sys.stderr)
        for name in sorted(stale):
            print(f"  {name}", file=sys.stderr)

    print()
    emit_latex(sizes, total_loc, n_main, n_technical, n_total)


def emit_latex(sizes, total_loc, n_main, n_technical, n_total) -> None:
    print(r"    \hline")
    print(r"    Component & Size \\")
    print(r"    \hline")
    for name, (spec, proof, _) in sizes.items():
        print(f"    {name} & \\textbf{{{spec + proof:,}}} loc \\\\")
    print(r"    \hline")
    print(f"    Total lines of \\coq{{}} source & \\textbf{{{total_loc:,}}} loc \\\\")
    print(f"    Main lemmas and theorems & \\textbf{{{n_main}}} \\\\")
    print(f"    Technical lemmas & \\textbf{{{n_technical}}} \\\\")
    print(f"    Total lemmas and theorems & \\textbf{{{n_total}}} \\\\")
    print(r"    \hline")


if __name__ == "__main__":
    main()
