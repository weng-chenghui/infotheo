#!/usr/bin/env python3
"""Build a Tier 0 manifest from a single .v file.

Pure module: no disk writes, no AUDIT_CENTRAL access. Callers own
serialization. This is the shared implementation used by both
`lint-rules.py` (fixture-parity linter) and `audit-file.sh`
(single-file CLI audit).

The entity walk matches every top-level declaration kind the rule
catalog cares about, including the kinds `lint-rules.py`'s legacy
walker at line 92 omitted (CoFixpoint, Let, Variable, Variables,
Hypothesis, Hypotheses). File-mode therefore sees the same kinds the
commit-time Stage 1 sees.

Commit-time divergence (documented, intentional): commit-mode Stage 1
gates I001 on `touched_lines` membership against the staged diff
hunks; file-mode synthesizes `touched_lines` for the entire entity
span, so file-mode can report I001 findings commit-mode would silence
when the bad name lies outside the staged hunk. Operators calling
audit-file.sh have explicitly asked for the whole entity, so this is
the correct semantics for file-mode.
"""
from __future__ import annotations

import fnmatch
import re
from pathlib import Path
from typing import Iterable


DECL_RE = re.compile(
    r"^\s*("
    r"Lemma|Theorem|Fact|Corollary|Proposition|Definition|Fixpoint|"
    r"CoFixpoint|Let|Variable|Variables|Hypothesis|Hypotheses"
    r")\s+([A-Za-z_][A-Za-z0-9_']*)"
)

_DECORATOR_RE = re.compile(
    r"^\s*(#\[|Local\b|Global\b|Export\b|Arguments\b|Hint\b|Canonical\b|Coercion\b)"
)
_STOP_RE = re.compile(
    r"^\s*(Section|Module|End|Require|Import|Open\s+Scope|Close\s+Scope)\b"
)


def _find_preceding_comment(lines: list[str], idx: int) -> tuple[bool, str]:
    """Walk upward from `idx - 1` to find a preceding `(* ... *)` block.

    Tolerates up to two blank lines and skips decorator-like lines
    (`#[...]`, `Local`, `Global`, `Arguments`, etc.). Stops at
    structural keywords (`Section`, `Module`, `Require`, ...).
    """
    j = idx - 1
    blanks = 0
    while j >= 0:
        line = lines[j]
        s = line.strip()
        if s == "":
            blanks += 1
            if blanks > 2:
                return False, ""
            j -= 1
            continue
        if _DECORATOR_RE.match(line):
            blanks = 0
            j -= 1
            continue
        if _STOP_RE.match(line):
            return False, ""
        if "*)" in line:
            k = j
            depth = 0
            buf: list[str] = []
            while k >= 0:
                buf.append(lines[k])
                depth += lines[k].count("*)") - lines[k].count("(*")
                if depth <= 0:
                    break
                k -= 1
            return True, "\n".join(reversed(buf))
        return False, ""
    return False, ""


def _entity_dict(
    rel_path: str,
    kind: str,
    name: str,
    line_start_1based: int,
    line_end_exclusive: int,
    header: str,
    body: str,
    preceding_comment: str,
    preceding_comment_present: bool,
) -> dict:
    return {
        "file": rel_path,
        "kind": kind,
        "name": name,
        "line_start": line_start_1based,
        "line_end": line_end_exclusive,
        "header": header,
        "body": body,
        "touched_lines": list(range(line_start_1based, line_end_exclusive + 1)),
        "preceding_comment": preceding_comment if preceding_comment_present else "",
        "preceding_comment_present": preceding_comment_present,
        "touched_header": True,
    }


def _matches_any(name: str, patterns: Iterable[str]) -> bool:
    return any(fnmatch.fnmatchcase(name, p) for p in patterns)


def _ranges_intersect(a_start: int, a_end: int, b_start: int, b_end: int) -> bool:
    return a_start <= b_end and b_start <= a_end


def build_manifest(
    file_path: str | Path,
    repo_root: str | Path,
    content: str | None = None,
    entity_names: list[str] | None = None,
    line_range: tuple[int, int] | None = None,
    fallback_name: str | None = None,
) -> dict:
    """Return a Tier 0 manifest for `file_path` relative to `repo_root`.

    The return shape matches `audit.sh`'s tier0 JSON:
      {
        "touched_files": [<rel_path>],
        "entities":      [<entity dict>, ...],
        "unanchored_hunks": [],
      }

    Each entity carries `file`, `kind`, `name`, `line_start`,
    `line_end`, `header`, `body`, `touched_lines`,
    `preceding_comment`, `preceding_comment_present`,
    `touched_header`.

    Filtering:
      - `entity_names` is a list of `fnmatch` glob patterns. An
        entity is kept when its `name` matches any pattern. Empty
        list means "no filter" (same as None).
      - `line_range` is `(start, end)`, 1-based inclusive. An entity
        is kept when its `[line_start, line_end]` intersects
        `[start, end]`.
      - At most one of the two may be non-None; a ValueError is
        raised if both are given.

    Fallback: when no declarations are found AND no selector is
    active AND `fallback_name` is given, returns one synthetic
    whole-file entity named `fallback_name`. When `fallback_name`
    is None, returns `entities=[]`. `lint-rules.py` passes
    `fallback_name`; `audit-file.sh` does not.
    """
    if entity_names is not None and line_range is not None:
        raise ValueError("entity_names and line_range are mutually exclusive")

    repo_root_p = Path(repo_root).resolve()
    file_p = Path(file_path)
    if not file_p.is_absolute():
        file_p = (repo_root_p / file_p).resolve()
    else:
        file_p = file_p.resolve()
    try:
        rel_path = str(file_p.relative_to(repo_root_p))
    except ValueError as e:
        raise ValueError(f"{file_p} is not inside {repo_root_p}") from e

    if content is None:
        content = file_p.read_text()
    lines = content.splitlines()

    decl_indices: list[tuple[int, re.Match]] = []
    for idx, ln in enumerate(lines):
        m = DECL_RE.match(ln)
        if m:
            decl_indices.append((idx, m))

    entities: list[dict] = []
    for pos, (idx, m) in enumerate(decl_indices):
        next_idx = (
            decl_indices[pos + 1][0]
            if pos + 1 < len(decl_indices)
            else len(lines)
        )
        pc_present, pc_text = _find_preceding_comment(lines, idx)
        body_span = "\n".join(lines[idx:next_idx])
        entities.append(_entity_dict(
            rel_path=rel_path,
            kind=m.group(1),
            name=m.group(2),
            line_start_1based=idx + 1,
            line_end_exclusive=next_idx,
            header=lines[idx].rstrip(),
            body=body_span,
            preceding_comment=pc_text,
            preceding_comment_present=pc_present,
        ))

    selector_active = bool(entity_names) or (line_range is not None)

    if entity_names:
        entities = [e for e in entities if _matches_any(e["name"], entity_names)]
    elif line_range is not None:
        lo, hi = line_range
        entities = [
            e for e in entities
            if _ranges_intersect(e["line_start"], e["line_end"], lo, hi)
        ]

    if not entities and not selector_active and fallback_name is not None:
        entities = [_entity_dict(
            rel_path=rel_path,
            kind="Lemma",
            name=fallback_name,
            line_start_1based=1,
            line_end_exclusive=max(len(lines), 1),
            header=lines[0] if lines else "",
            body=content,
            preceding_comment="",
            preceding_comment_present=False,
        )]
        # Fallback replicates the legacy whole-file entity shape from
        # lint-rules.py:151-166 exactly; that walker used
        # range(1, len(lines) + 1) for touched_lines, which differs
        # from the real-entity formula by one when len(lines) == 0.
        # Preserve the legacy exactly:
        entities[0]["touched_lines"] = list(range(1, len(lines) + 1))

    return {
        "touched_files": [rel_path],
        "entities": entities,
        "unanchored_hunks": [],
    }


def _cli() -> int:
    """Tiny CLI for ad-hoc inspection. Writes the manifest JSON to stdout."""
    import argparse
    import json
    import sys

    ap = argparse.ArgumentParser(description="Build a Tier 0 manifest from a .v file.")
    ap.add_argument("--file", required=True)
    ap.add_argument("--repo-root", default=None,
                    help="defaults to the directory containing .claude/audit/")
    ap.add_argument("--entity", default=None,
                    help="comma-separated glob patterns")
    ap.add_argument("--lines", default=None,
                    help="START-END")
    ap.add_argument("--fallback-name", default=None)
    args = ap.parse_args()

    repo_root = args.repo_root
    if repo_root is None:
        here = Path(__file__).resolve()
        repo_root = here.parent.parent.parent.parent  # bin/ -> audit/ -> .claude/ -> repo
    entity_names = None
    if args.entity:
        entity_names = [s for s in args.entity.split(",") if s]
    line_range = None
    if args.lines:
        try:
            a, b = args.lines.split("-", 1)
            lo, hi = int(a), int(b)
            if lo < 1 or hi < lo:
                print(f"file_manifest: invalid --lines {args.lines}", file=sys.stderr)
                return 1
            line_range = (lo, hi)
        except ValueError:
            print(f"file_manifest: invalid --lines {args.lines}", file=sys.stderr)
            return 1
    try:
        manifest = build_manifest(
            file_path=args.file,
            repo_root=repo_root,
            entity_names=entity_names,
            line_range=line_range,
            fallback_name=args.fallback_name,
        )
    except ValueError as e:
        print(f"file_manifest: {e}", file=sys.stderr)
        return 1
    print(json.dumps(manifest, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    import sys
    sys.exit(_cli())
