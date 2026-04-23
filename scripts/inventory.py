#!/usr/bin/env python3
"""Emit pgg-smc/audit-inventory/{theorem_index.tsv,THEOREM_INDEX.md}.

Reads the static scope list at pgg-smc/audit-inventory/scope.txt, calls
`file_manifest.build_manifest` (from the rocq-audit engine) on each
in-scope file, and writes a TSV plus a Markdown rendering of every
theorem-kind declaration found. Columns are lifted directly from the
manifest entity; nothing reinterprets what "theorem" means.

Run with the audit engine's venv so `build_manifest` has the same
interpreter the rest of the pipeline uses:

  .claude/audit/venv/bin/python3 scripts/inventory.py
"""
from __future__ import annotations

import pathlib
import sys
from collections import defaultdict

REPO = pathlib.Path(__file__).resolve().parent.parent
AUDIT_BIN = REPO / ".claude" / "audit" / "bin"
sys.path.insert(0, str(AUDIT_BIN))

from file_manifest import build_manifest  # type: ignore

SCOPE_FILE = REPO / "pgg-smc" / "audit-inventory" / "scope.txt"
TSV_OUT = REPO / "pgg-smc" / "audit-inventory" / "theorem_index.tsv"
MD_OUT = REPO / "pgg-smc" / "audit-inventory" / "THEOREM_INDEX.md"
THEOREM_KINDS = {"Theorem", "Lemma", "Fact", "Corollary", "Proposition"}
TRUNC_COMMENT = 200
TRUNC_HEADER = 200


def parse_scope() -> list[str]:
    lines = SCOPE_FILE.read_text().splitlines()
    out: list[str] = []
    for raw in lines:
        stripped = raw.strip()
        if not stripped or stripped.startswith("#"):
            continue
        path = stripped.split("#", 1)[0].strip()
        if path:
            out.append(path)
    return out


def cell(text: str, cap: int) -> str:
    one = " ".join(text.split())
    if len(one) > cap:
        one = one[: cap - 1] + "…"
    return one


def comment_lines(text: str) -> set[int]:
    """1-based line numbers that fall inside `(* ... *)` comments (any depth)."""
    inside: set[int] = set()
    depth = 0
    line = 1
    i = 0
    while i < len(text):
        ch = text[i]
        two = text[i : i + 2]
        if two == "(*":
            depth += 1
            if depth == 1:
                inside.add(line)
            i += 2
            continue
        if two == "*)" and depth > 0:
            if depth == 1:
                inside.add(line)
            depth -= 1
            i += 2
            continue
        if depth > 0:
            inside.add(line)
        if ch == "\n":
            line += 1
        i += 1
    return inside


def main() -> int:
    rels = parse_scope()
    rows = []
    phantoms: list[tuple[str, int, str]] = []
    for rel in rels:
        src = (REPO / "pgg-smc" / rel).read_text()
        file_lines = src.splitlines()
        in_comment = comment_lines(src)
        manifest = build_manifest(
            file_path=str(REPO / "pgg-smc" / rel),
            repo_root=str(REPO),
            entity_names=None,
            line_range=None,
            fallback_name=None,
        )
        for e in manifest["entities"]:
            if e["kind"] not in THEOREM_KINDS:
                continue
            ls = e["line_start"]
            line_text = file_lines[ls - 1] if ls <= len(file_lines) else ""
            if ls in in_comment or not line_text.lstrip().startswith(e["kind"] + " "):
                phantoms.append((rel, ls, e["name"]))
                continue
            rows.append(
                {
                    "file": rel,
                    "line": e["line_start"],
                    "kind": e["kind"],
                    "name": e["name"],
                    "tells_us": cell(e.get("preceding_comment") or "", TRUNC_COMMENT),
                    "statement": cell(e.get("header") or "", TRUNC_HEADER),
                }
            )

    rows.sort(key=lambda r: (r["file"], r["line"]))

    with TSV_OUT.open("w") as f:
        f.write("file\tline\tkind\tname\ttells_us\tstatement\n")
        for r in rows:
            safe = [str(r[k]).replace("\t", " ") for k in ("file", "line", "kind", "name", "tells_us", "statement")]
            f.write("\t".join(safe) + "\n")

    by_dir: dict[str, dict[str, list[dict]]] = defaultdict(lambda: defaultdict(list))
    for r in rows:
        parts = r["file"].split("/", 1)
        d = parts[0]
        by_dir[d][r["file"]].append(r)

    with MD_OUT.open("w") as f:
        f.write(f"# pgg-smc theorem index\n\n")
        f.write(f"{len(rows)} declarations across {len(rels)} in-scope files.\n\n")
        for d in sorted(by_dir):
            dir_total = sum(len(v) for v in by_dir[d].values())
            f.write(f"## `{d}/` ({dir_total} decls)\n\n")
            for rel in sorted(by_dir[d]):
                entries = by_dir[d][rel]
                f.write(f"### `{rel}` ({len(entries)})\n\n")
                f.write("| Line | Kind | Name | Tells us / Statement |\n")
                f.write("|---:|---|---|---|\n")
                for e in entries:
                    tells = e["tells_us"] or e["statement"]
                    tells_md = tells.replace("|", "\\|")
                    f.write(f"| {e['line']} | {e['kind']} | `{e['name']}` | {tells_md} |\n")
                f.write("\n")

    print(f"{len(rows)} rows -> {TSV_OUT.relative_to(REPO)}")
    print(f"          -> {MD_OUT.relative_to(REPO)}")
    if phantoms:
        print(f"note: skipped {len(phantoms)} phantom entities whose declaration line is inside a comment:")
        for rel, line, name in phantoms:
            print(f"  {rel}:{line}  {name}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
