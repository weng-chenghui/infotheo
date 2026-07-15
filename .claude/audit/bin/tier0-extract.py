#!/usr/bin/env python3
"""Tier 0 extraction.

Reads the staged diff, collects touched `.v` files, and expands each touched
line to its enclosing lemma or definition. Emits a JSON manifest on stdout.

Manifest shape:
{
  "touched_files": [path, ...],
  "entities": [
    {
      "file": path,
      "kind": "Lemma" | "Theorem" | "Fact" | "Corollary" | "Definition" | "Fixpoint" | "Inductive" | "Record" | "Variable" | "Hypothesis" | "unknown",
      "name": str,
      "line_start": int,
      "line_end": int,
      "header": str,      # first line of the declaration
      "body": str,        # full multi-line body
      "touched_lines": [int, ...]
    },
    ...
  ],
  "unanchored_hunks": [
    {"file": path, "line_start": int, "line_end": int, "lines": [str, ...]}
  ]
}
"""
from __future__ import annotations
import json
import os
import re
import subprocess
import sys
import fnmatch
from pathlib import Path

# Load config for excluded_paths.
ROOT = Path(os.environ.get("REPO_ROOT", ".")).resolve()
AUDIT_DIR = Path(os.environ.get("AUDIT_DIR", ROOT / ".claude" / "audit")).resolve()

def load_config():
    import yaml
    cfg_path = AUDIT_DIR / "config.yaml"
    if cfg_path.exists():
        with open(cfg_path) as f:
            return yaml.safe_load(f) or {}
    return {}

CFG = load_config()
EXCLUDED = CFG.get("excluded_paths", []) or []


def is_excluded(rel_path: str) -> bool:
    for pat in EXCLUDED:
        if fnmatch.fnmatch(rel_path, pat):
            return True
    return False


def run(cmd: list[str]) -> str:
    try:
        return subprocess.check_output(cmd, cwd=ROOT, text=True, stderr=subprocess.DEVNULL)
    except subprocess.CalledProcessError:
        return ""


# Parse `git diff --cached -U0` to get touched line ranges per file.
def diff_hunks() -> dict[str, list[tuple[int, int]]]:
    out = run(["git", "diff", "--cached", "-U0", "--no-color"])
    result: dict[str, list[tuple[int, int]]] = {}
    cur_file = None
    header_re = re.compile(r"^@@ -\d+(?:,\d+)? \+(\d+)(?:,(\d+))? @@")
    for line in out.splitlines():
        if line.startswith("+++ b/"):
            cur_file = line[6:]
            if is_excluded(cur_file) or not cur_file.endswith(".v"):
                cur_file = None
            else:
                result.setdefault(cur_file, [])
        elif line.startswith("+++ "):
            cur_file = None
        elif cur_file is not None:
            m = header_re.match(line)
            if m:
                start = int(m.group(1))
                length = int(m.group(2)) if m.group(2) else 1
                if length == 0:
                    continue   # pure deletion, no post-image lines
                result[cur_file].append((start, start + length - 1))
    return result


# Read a staged file content, falling back to the worktree if it is staged-only.
def staged_file_content(rel_path: str) -> str:
    out = run(["git", "show", f":{rel_path}"])
    return out


# Identify enclosing Rocq top-level declarations.
DECL_KIND_RE = re.compile(
    r"^\s*(Lemma|Theorem|Fact|Corollary|Proposition|Remark|Definition|Fixpoint|CoFixpoint|Inductive|CoInductive|Record|Class|Instance|Variable|Variables|Hypothesis|Hypotheses|Axiom|Parameter|Notation)\b"
)

# Decorator / attribute lines that should be skipped when associating a
# comment with a declaration.
DECL_DECORATOR_RE = re.compile(
    r"^\s*(#\[[^\]]*\]|Local\b|Global\b|Export\b|Arguments\b|Hint\b|Canonical\b|Coercion\b)"
)

# Boundary lines that break comment-declaration association.
DECL_BOUNDARY_RE = re.compile(
    r"^\s*(Section|Module|End|Require|Import|Export|Open\s+Scope|Close\s+Scope|Declare\s+Scope)\b"
)
DECL_NAME_RE = re.compile(
    r"^\s*(?:Lemma|Theorem|Fact|Corollary|Proposition|Remark|Definition|Fixpoint|CoFixpoint|Inductive|CoInductive|Record|Class|Instance|Variable|Variables|Hypothesis|Hypotheses|Axiom|Parameter|Notation)\s+(?:Local\s+|Global\s+|Export\s+|Section\s+)?([A-Za-z_][A-Za-z0-9_']*)"
)
TERMINATOR_RE = re.compile(r"(^|[ \t;])(Qed|Defined|Admitted|Abort)\s*\.")


def find_preceding_comment(lines: list[str], decl_line_0based: int,
                           max_blank_lines: int = 2) -> tuple[str, bool]:
    """Walk upward from the declaration line looking for a `(* ... *)`
    block. Skip blank lines (bounded) and decorator lines (`#[local]`,
    `Arguments`, `Hint`, `Canonical`, `Coercion`, `Local`, `Global`,
    `Export`). Stop without success on a boundary line (`Section`,
    `Module`, `End`, `Require`, `Import`, `Open Scope`, etc.) or at the
    start of the file.

    Returns (comment_text, present). comment_text is the joined block
    text when present, empty otherwise.
    """
    i = decl_line_0based - 1
    blank_run = 0
    while i >= 0:
        line = lines[i]
        stripped = line.strip()
        if stripped == "":
            blank_run += 1
            if blank_run > max_blank_lines:
                return "", False
            i -= 1
            continue
        if DECL_DECORATOR_RE.match(line):
            blank_run = 0
            i -= 1
            continue
        if DECL_BOUNDARY_RE.match(line):
            return "", False
        if "*)" in line:
            # Walk upward to find the matching opening `(*` (simple
            # approximation that does not handle nested comments beyond a
            # depth counter).
            end_line = i
            j = i
            depth = 0
            buf: list[str] = []
            while j >= 0:
                buf.append(lines[j])
                for _ in range(lines[j].count("*)")):
                    depth += 1
                for _ in range(lines[j].count("(*")):
                    depth -= 1
                if depth == 0:
                    break
                j -= 1
            return "\n".join(reversed(buf)), True
        # Non-blank, non-decorator, non-boundary, non-comment line: no
        # preceding comment.
        return "", False
    return "", False


def find_entities(rel_path: str, content: str, touched: list[tuple[int, int]]) -> list[dict]:
    """Walk the file line by line; emit one entity per decl whose range
    intersects any touched hunk."""
    lines = content.splitlines()
    entities: list[dict] = []
    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        m = DECL_KIND_RE.match(line)
        if not m:
            i += 1
            continue
        kind = m.group(1)
        name_m = DECL_NAME_RE.match(line)
        name = name_m.group(1) if name_m else "(anonymous)"
        start = i + 1   # 1-based
        # Find end: next Qed/Defined/Admitted/Abort for proofs, or next blank
        # line followed by another top-level decl for Definition/Notation/etc.
        end = start
        j = i + 1
        while j < n:
            if TERMINATOR_RE.search(lines[j]):
                end = j + 1
                j += 1
                break
            if DECL_KIND_RE.match(lines[j]) and kind in ("Definition", "Notation", "Variable", "Variables", "Hypothesis", "Hypotheses", "Axiom", "Parameter", "Record", "Inductive", "CoInductive", "Class"):
                # For non-proof kinds, end at the line just before the next decl.
                end = j
                break
            if kind in ("Definition", "Notation", "Variable", "Variables", "Hypothesis", "Hypotheses", "Axiom", "Parameter") and lines[j].rstrip().endswith("."):
                end = j + 1
                j += 1
                break
            j += 1
        else:
            end = n
        # Determine whether any touched hunk falls in [start, end].
        touched_lines: list[int] = []
        for (ts, te) in touched:
            for x in range(max(ts, start), min(te, end) + 1):
                touched_lines.append(x)
        if touched_lines:
            pc_text, pc_present = find_preceding_comment(lines, i)
            entities.append({
                "file": rel_path,
                "kind": kind,
                "name": name,
                "line_start": start,
                "line_end": end,
                "header": line.rstrip(),
                "body": "\n".join(lines[start - 1:end]),
                "touched_lines": sorted(set(touched_lines)),
                "preceding_comment": pc_text,
                "preceding_comment_present": pc_present,
                "touched_header": start in touched_lines,
            })
        i = max(j, i + 1)
    return entities


def find_unanchored(rel_path: str, touched: list[tuple[int, int]], entities: list[dict]) -> list[dict]:
    """Hunks whose lines don't fall inside any entity body. Useful for
    file-header changes or orphan tactics."""
    anchored: set[int] = set()
    for e in entities:
        if e["file"] == rel_path:
            for x in range(e["line_start"], e["line_end"] + 1):
                anchored.add(x)
    out: list[dict] = []
    content_lines = staged_file_content(rel_path).splitlines()
    for (ts, te) in touched:
        orphan_start = None
        orphan_end = None
        for x in range(ts, te + 1):
            if x not in anchored:
                if orphan_start is None:
                    orphan_start = x
                orphan_end = x
            else:
                if orphan_start is not None:
                    out.append({
                        "file": rel_path,
                        "line_start": orphan_start,
                        "line_end": orphan_end,
                        "lines": content_lines[orphan_start - 1:orphan_end],
                    })
                    orphan_start = orphan_end = None
        if orphan_start is not None:
            out.append({
                "file": rel_path,
                "line_start": orphan_start,
                "line_end": orphan_end,
                "lines": content_lines[orphan_start - 1:orphan_end],
            })
    return out


def main() -> int:
    hunks = diff_hunks()
    manifest = {
        "touched_files": sorted(hunks.keys()),
        "entities": [],
        "unanchored_hunks": [],
    }
    for rel_path, touched in hunks.items():
        content = staged_file_content(rel_path)
        entities = find_entities(rel_path, content, touched)
        manifest["entities"].extend(entities)
        manifest["unanchored_hunks"].extend(find_unanchored(rel_path, touched, entities))
    json.dump(manifest, sys.stdout, indent=2, ensure_ascii=False)
    print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
