#!/usr/bin/env python3
"""Mechanical structural assertions for H002 fix_sketch payloads.

Takes a JSON file containing rocq-auditor findings (the output of an
audit-file.sh run, or equivalent) and a reference .v file containing
the user's hand-written prose-style comments. Runs four structural
checks on each fix_sketch:

  1. LINE_BUDGET — comment is ≤ 5 lines (Lemma/Theorem/Fact/
     Corollary/Proposition) or ≤ 10 lines (non-Local multi-line
     Definition/Fixpoint).

  2. TEMPLATE_SLOTS — comment contains < 2 stacked-slot lines of
     `Kind:`/`Why:`/`Used by:`. `Naming:` is excluded.

  3. STALE_CROSSREF — comment cites no plan files
     (`~/.claude/plans/...md`), no plan-task tokens in task context
     (`per/implements/closes/Task ... <TUVW><N>` or `<TUVW><N>:`),
     and no absolute line numbers.

  4. NO_BRACKETS — comment uses inline math notation
     (`#|T|`, `1/m`) rather than `[identifier]` bracketing.

Conceptual-match similarity against the reference file is computed
and reported as ADVISORY output; it does NOT affect exit code.

Exit 0 iff every fix_sketch passes all four structural checks.
Exit 1 if any structural check fails.

Usage:
  compare-comment-styles.py --suggestions audit.json \\
                            --user-reference user_file.v \\
                            [--output report.txt]
"""

import argparse
import json
import re
import sys
from pathlib import Path

LEMMA_LINE_BUDGET = 8
HYPOTHESIS_LINE_BUDGET = 25  # Hypothesis/Variable may carry rich
                              # conceptual narrative — Section parameters
                              # often state proof chains and intent that
                              # downstream proofs depend on.
DEFINITION_LINE_BUDGET = 15

LEMMA_KINDS = {"Lemma", "Theorem", "Fact", "Corollary", "Proposition"}
HYPOTHESIS_KINDS = {"Hypothesis", "Variable"}
DEFINITION_KINDS = {"Definition", "Fixpoint"}

# Pattern for stacked slot lines. Each slot must start at the beginning
# of a stripped comment line (after any `*` continuation prefix).
SLOT_LINE_RE = re.compile(
    r"^\s*(?:\*\s*)?(Kind|Why|Used by)\s*:",
    re.MULTILINE,
)

PLAN_FILE_RE = re.compile(r"~/\.claude/plans/[^\s\)\]]+\.md")
ABS_LINE_RE = re.compile(r"\(line\s+\d+\)|[A-Za-z_]+\.v:\d+")

# Plan-task token in task context: token followed by `:` OR a
# context word ("per"/"implements"/"closes"/"Task"/"task") appears
# within ~40 chars before the token. The window is intentionally
# slack to catch "Closes the T4 task in ..." while still avoiding
# matches like "V2" in unrelated prose.
TASK_LETTERS = "TUVW"
TASK_CONTEXT_RE = re.compile(
    rf"\b[{TASK_LETTERS}]\d+\b(?=:)"
    rf"|(?:\b(?:per|implements|closes|Task|task)\b[\s\w,]{{0,40}}?)\b[{TASK_LETTERS}]\d+\b",
    re.IGNORECASE,
)

# Identifier bracketing pattern: [identifier_with_underscores]
# Conservative: only flag when the bracketed content is a valid
# identifier-ish token (letters/digits/underscores, starts with a
# letter), to avoid false-positives on math notation like [1, n] or
# [a; b].
BRACKET_RE = re.compile(r"\[(?:[A-Za-z][A-Za-z_0-9]*(?:\.[A-Za-z][A-Za-z_0-9]*)*)\]")

# Purposive-framing heuristic (advisory only — never gating).
# Mirrors H002's MECHANISM_ONLY detector: fires when the first 200
# chars contain a mechanism stop-phrase AND fewer than 2 architecture
# nouns.
MECHANISM_STOP_PHRASES = (
    "proof reduces", "reduces to", "reduces directly", "by induction",
    "by case", "case analysis", "directly to", "obligation",
    "obligations", "unifies", "side-condition", "side condition",
    "tactic", "cancellation bijection", "routes through",
    "discharges", "unfolds", "lifts to", "by reflexivity",
    "trivially follows", "by simpl", "by exact", "by destruct",
)

ARCHITECTURE_NOUNS = (
    "bridge", "bridging", "adversary", "predictor", "witness",
    "package", "interface", "carrier", "scheme", "chain", "game",
    "framework", "protocol", "system", "instance", "role",
    "module", "pipeline", "anchor", "guess", "space", "leaked",
    "residual", "AHE", "SSProve", "MathComp", "IND-CPA",
    "V_2", "V_3", "secrecy",
)


def has_purposive_framing(comment_body: str) -> tuple[bool, str]:
    """Return (passed, reason). Advisory only — never gates exit code.

    Fires (returns (False, reason)) only when the first 200 chars
    contain a mechanism stop-phrase AND fewer than 2 architecture
    nouns. Mirrors the H002 MECHANISM_ONLY detector.
    """
    head = comment_body[:200].lower()
    has_mech = any(p in head for p in MECHANISM_STOP_PHRASES)
    arch_count = sum(1 for n in ARCHITECTURE_NOUNS if n.lower() in head)
    if has_mech and arch_count < 2:
        mech_hit = next(p for p in MECHANISM_STOP_PHRASES if p in head)
        return False, (
            f"mechanism-anchored on '{mech_hit}'; "
            f"only {arch_count} architecture noun(s) in first 200 chars"
        )
    return True, ""


def strip_comment_delimiters(text: str) -> str:
    """Drop the outer `(* ... *)` or `(** ... *)` delimiters; return inner."""
    s = text.strip()
    if s.startswith("(**"):
        s = s[3:]
    elif s.startswith("(*"):
        s = s[2:]
    if s.endswith("*)"):
        s = s[:-2]
    return s.strip()


def count_non_blank_lines(comment_body: str) -> int:
    return sum(1 for line in comment_body.splitlines() if line.strip())


def count_stacked_slots(comment_body: str) -> int:
    return len(SLOT_LINE_RE.findall(comment_body))


def find_stale_crossrefs(comment_body: str) -> list[str]:
    """Return list of stale-crossref strings found."""
    hits = []
    hits.extend(PLAN_FILE_RE.findall(comment_body))
    hits.extend(ABS_LINE_RE.findall(comment_body))
    hits.extend(TASK_CONTEXT_RE.findall(comment_body))
    return hits


def find_identifier_brackets(comment_body: str) -> list[str]:
    return BRACKET_RE.findall(comment_body)


def check_one_finding(finding: dict) -> tuple[bool, list[str], list[str]]:
    """Return (gating_passed, gating_failures, advisory_notes).

    Gating failures affect exit code. Advisory notes (purposive framing)
    are reported but never affect exit code.
    """
    fix_sketch = finding.get("fix_sketch", "")
    if not fix_sketch:
        return True, [], []

    entity_kind = finding.get("entity_kind") or ""  # not always present
    body = strip_comment_delimiters(fix_sketch)
    failures = []
    advisories = []

    # LINE_BUDGET (gating)
    n_lines = count_non_blank_lines(body)
    if entity_kind in DEFINITION_KINDS:
        budget = DEFINITION_LINE_BUDGET
    elif entity_kind in HYPOTHESIS_KINDS:
        budget = HYPOTHESIS_LINE_BUDGET
    else:
        budget = LEMMA_LINE_BUDGET
    if n_lines > budget:
        failures.append(f"LINE_BUDGET: {n_lines} non-blank lines (budget {budget})")

    # TEMPLATE_SLOTS (gating)
    n_slots = count_stacked_slots(body)
    if n_slots >= 2:
        failures.append(f"TEMPLATE_SLOTS: {n_slots} stacked Kind:/Why:/Used by: lines")

    # STALE_CROSSREF (gating)
    crossrefs = find_stale_crossrefs(body)
    if crossrefs:
        failures.append(f"STALE_CROSSREF: found {crossrefs}")

    # NO_BRACKETS (gating)
    brackets = find_identifier_brackets(body)
    if brackets:
        failures.append(f"NO_BRACKETS: identifier-bracket(s) {brackets}")

    # PURPOSIVE_FRAMING (advisory only — never gating)
    purposive_ok, reason = has_purposive_framing(body)
    if not purposive_ok:
        advisories.append(f"purposive: FAIL ({reason})")
    else:
        advisories.append("purposive: PASS")

    return (len(failures) == 0), failures, advisories


def conceptual_similarity(fix_sketch: str, user_file_text: str) -> float:
    """Compute Jaccard token-overlap between fix_sketch body and the
    closest matching comment in user_file_text. Advisory only."""
    sketch_body = strip_comment_delimiters(fix_sketch)
    sketch_tokens = set(re.findall(r"[A-Za-z]+", sketch_body.lower()))
    if not sketch_tokens:
        return 0.0
    # Find best-matching comment in the user file
    user_comments = re.findall(r"\(\*[^*]*(?:\*(?!\))[^*]*)*\*\)", user_file_text)
    best = 0.0
    for c in user_comments:
        c_body = strip_comment_delimiters(c)
        c_tokens = set(re.findall(r"[A-Za-z]+", c_body.lower()))
        if not c_tokens:
            continue
        intersection = len(sketch_tokens & c_tokens)
        union = len(sketch_tokens | c_tokens)
        score = intersection / union if union else 0.0
        if score > best:
            best = score
    return best


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--suggestions", required=True,
                    help="JSON file from audit-file.sh (or equivalent)")
    ap.add_argument("--user-reference",
                    help=".v file with user's hand-written comments (advisory)")
    ap.add_argument("--output",
                    help="Write report to this path instead of stdout")
    args = ap.parse_args()

    suggestions = json.loads(Path(args.suggestions).read_text())
    findings = suggestions.get("findings", [])
    user_text = (
        Path(args.user_reference).read_text() if args.user_reference else ""
    )

    lines = []
    total = 0
    failed = 0

    for f in findings:
        if f.get("rule_id") not in ("H001", "H002"):
            continue
        if not f.get("fix_sketch"):
            continue
        total += 1
        passed, failures, advisories = check_one_finding(f)
        if not passed:
            failed += 1
        name = f.get("lemma_name", f.get("file", "<unknown>"))
        status = "PASS" if passed else "FAIL"
        lines.append(f"[{status}] {name} (rule {f.get('rule_id')})")
        if failures:
            for msg in failures:
                lines.append(f"    - {msg}")
        for note in advisories:
            lines.append(f"    [advisory] {note}")
        if user_text and f.get("fix_sketch"):
            sim = conceptual_similarity(f["fix_sketch"], user_text)
            lines.append(f"    [advisory] conceptual-match Jaccard: {sim:.2f}")

    lines.append("")
    lines.append(f"Summary: {total - failed} passed / {failed} failed / {total} total")
    if failed > 0:
        lines.append("Result: FAIL (one or more fix_sketch values violate structural checks)")
    else:
        lines.append("Result: PASS (all fix_sketch values satisfy structural checks)")

    output = "\n".join(lines)
    if args.output:
        Path(args.output).write_text(output + "\n")
    else:
        print(output)

    return 0 if failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
