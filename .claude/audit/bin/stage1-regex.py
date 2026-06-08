#!/usr/bin/env python3
"""Stage 1 regex audit.

Loads enabled rules whose `stage_mode` includes Stage 1, applies each rule's
`fast_pattern` to the staged content of every touched entity, and emits a JSON
findings list on stdout.

Input: path to the Tier 0 manifest as argv[1].
Output: JSON object on stdout.
{
  "findings": [
    {
      "rule_id": str,
      "file": str,
      "line_start": int,
      "line_end": int,
      "lemma_name": str | null,
      "severity": "error"|"warning"|"info",
      "evidence_quote": str,
      "stage": "stage1"
    }, ...
  ]
}
"""
from __future__ import annotations
import json
import os
import re
import sys
import fnmatch
from pathlib import Path

import yaml

ROOT = Path(os.environ.get("REPO_ROOT", ".")).resolve()
AUDIT_DIR = Path(os.environ.get("AUDIT_DIR", ROOT / ".claude" / "audit")).resolve()

# Banned regex features in fast_pattern: lookaround, backreferences, possessive quantifiers.
BANNED_REGEX_FEATURES = [
    (re.compile(r"\(\?="), "positive lookahead"),
    (re.compile(r"\(\?!"), "negative lookahead"),
    (re.compile(r"\(\?<="), "positive lookbehind"),
    (re.compile(r"\(\?<!"), "negative lookbehind"),
    (re.compile(r"\\[1-9]"), "backreference"),
]


def strip_line_comments(text: str) -> str:
    """Remove Rocq block comments `(* ... *)` and preserve line count.

    Nested block comments are flattened conservatively. Strings are not
    tracked; false negatives inside strings are acceptable for Stage 1.
    """
    out = []
    i = 0
    depth = 0
    n = len(text)
    while i < n:
        if depth == 0 and i + 1 < n and text[i] == "(" and text[i + 1] == "*":
            depth = 1
            out.append("  ")
            i += 2
            continue
        if depth > 0:
            if i + 1 < n and text[i] == "(" and text[i + 1] == "*":
                depth += 1
                out.append("  ")
                i += 2
                continue
            if i + 1 < n and text[i] == "*" and text[i + 1] == ")":
                depth -= 1
                out.append("  ")
                i += 2
                continue
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def _rules_dir() -> Path:
    if (AUDIT_DIR / "rules").exists():
        return AUDIT_DIR / "rules"
    if (AUDIT_DIR / "template" / "rules").exists():
        return AUDIT_DIR / "template" / "rules"
    return AUDIT_DIR / "rules"


def load_rules() -> list[dict]:
    rules_dir = _rules_dir()
    rules = []
    for p in sorted(rules_dir.glob("*.yaml")):
        with open(p) as f:
            r = yaml.safe_load(f)
        if not r:
            continue
        r["_path"] = str(p)
        rules.append(r)
    return rules


def load_config() -> dict:
    cfg_path = AUDIT_DIR / "config.yaml"
    if not cfg_path.exists() and (AUDIT_DIR / "template" / "config.yaml").exists():
        cfg_path = AUDIT_DIR / "template" / "config.yaml"
    if cfg_path.exists():
        with open(cfg_path) as f:
            return yaml.safe_load(f) or {}
    return {}


# ---- H-series comment tag contract ----------------------------------------

_TAG_KEYWORD_RE = re.compile(r"@(intent|composes|main)\b", re.IGNORECASE)
_INTENT_RE = re.compile(r"@intent\s*:\s*(.+)", re.IGNORECASE | re.DOTALL)
_COMPOSES_RE = re.compile(r"@composes\s*:\s*([^\n*]+)", re.IGNORECASE)
_MAIN_RE = re.compile(
    r"@main\s+([A-Za-z][A-Za-z0-9_]*(?:\s*,\s*[A-Za-z][A-Za-z0-9_]*)*)\s*:\s*(.+)",
    re.IGNORECASE | re.DOTALL)
_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
_DEGEN_WORDS = {"todo", "fixme", "wip", "xxx", "???"}


def _strip_comment_delims(pc: str) -> str:
    s = pc
    for d in ("(**", "(*", "*)"):
        s = s.replace(d, " ")
    return s


def _content_floor_ok(text: str, identifier: str) -> bool:
    """Reused for both the @-tag value (anti-gaming) and the substantive
    legacy-comment test. Mirrors the old H001.yaml:18-27 metric."""
    t = (text or "").strip()
    if t.lower() in _DEGEN_WORDS:
        return False
    if t == identifier:
        return False
    if len(re.sub(r"\s+", "", t)) < 10:
        return False
    alpha_tokens = re.findall(r"[^\W\d_]{3,}", t, re.UNICODE)
    return len(alpha_tokens) >= 2


def _comment_role_tag(entity: dict) -> dict | None:
    """Return the single role tag found in the preceding comment, or None.
    {"kind": "intent"|"composes"|"main", "value": str,
     "labels": [str]|None, "targets": [str]|None, "multi": bool}"""
    body = _strip_comment_delims(entity.get("preceding_comment", "") or "")
    kws = [k.lower() for k in _TAG_KEYWORD_RE.findall(body)]
    if not kws:
        return None
    kind = kws[0]
    tag: dict = {"kind": kind, "multi": len(set(kws)) > 1, "labels": None, "targets": None, "value": ""}
    if kind == "intent":
        mm = _INTENT_RE.search(body)
        tag["value"] = mm.group(1).strip() if mm else ""
    elif kind == "composes":
        mm = _COMPOSES_RE.search(body)
        raw = mm.group(1).strip() if mm else ""
        tag["value"] = raw
        tag["targets"] = _IDENT_RE.findall(raw)
    elif kind == "main":
        mm = _MAIN_RE.search(body)
        if mm:
            tag["labels"] = [s.strip().lower() for s in mm.group(1).split(",")]
            tag["value"] = mm.group(2).strip()
        else:
            tag["labels"] = []
            tag["value"] = ""
    return tag


def _main_purpose_labels(cfg: dict) -> set[str]:
    return {str(s).lower() for s in (cfg.get("main_purpose_labels") or [])}


def _entity_touched(entity: dict) -> bool:
    """In commit mode an entity is in scope when any of its body lines or its
    header line changed. file_manifest sets touched_header=True for all."""
    return bool(entity.get("touched_lines")) or entity.get("touched_header", False)


def _composes_target_exists(name: str) -> bool:
    """Bounded git grep for an exact top-level declaration of `name`.
    The decl-keyword anchor excludes `Used by:` comment mentions."""
    import subprocess
    pat = (r"^[[:space:]]*(Lemma|Theorem|Fact|Corollary|Proposition|Definition|Fixpoint)"
           r"[[:space:]]+" + re.escape(name) + r"([^A-Za-z0-9_']|$)")
    try:
        r = subprocess.run(["git", "grep", "-lE", pat, "--", "*.v"],
                           cwd=str(ROOT), capture_output=True, text=True, timeout=20)
    except Exception:
        return True  # abstain: never raise a false dangling error on tool failure
    return r.returncode == 0 and bool(r.stdout.strip())


H_SERIES_DECL_KINDS = {"Lemma", "Theorem", "Fact", "Corollary", "Proposition"}
H_SERIES_WIDER_KINDS = {"Definition", "Fixpoint"}


def h_series_applies(entity: dict) -> bool:
    """Narrow scoping for H-series rules. Always include Lemma/Theorem/Fact/
    Corollary/Proposition. Include Definition/Fixpoint only when body spans
    >=2 lines, is not Local, and RHS is not a single literal or identifier."""
    kind = entity.get("kind", "")
    if kind in H_SERIES_DECL_KINDS:
        return True
    if kind not in H_SERIES_WIDER_KINDS:
        return False
    body = entity.get("body", "")
    header = entity.get("header", "")
    if re.match(r"^\s*Local\b", header) or re.match(r"^\s*#\[local\]", header):
        return False
    # Count non-blank body lines, excluding the header.
    body_lines = [ln for ln in body.splitlines()[1:] if ln.strip()]
    if len(body_lines) < 1:
        return False
    # RHS after the `:=` on the header: is it a single token?
    m = re.search(r":=\s*(.+?)\s*\.?\s*$", header)
    if m and re.match(r"^[A-Za-z0-9_'.]+$", m.group(1).strip()):
        return False
    return True


def validate_fast_pattern(rule: dict) -> tuple[bool, str]:
    fp = rule.get("fast_pattern") or {}
    pat = fp.get("pattern")
    if not isinstance(pat, str):
        return False, "missing fast_pattern.pattern"
    for rx, label in BANNED_REGEX_FEATURES:
        if rx.search(pat):
            return False, f"banned regex feature: {label}"
    try:
        re.compile(pat)
    except re.error as e:
        return False, f"invalid regex: {e}"
    return True, ""


def apply_fast_check(rule: dict, manifest: dict, strict_comment_coverage: bool, cfg: dict = None) -> list[dict]:
    """Named entity-level checks that cannot be expressed as single-line
    regex. Dispatched by `fast_check.kind`."""
    if cfg is None:
        cfg = {}
    fc = rule.get("fast_check") or {}
    kind = fc.get("kind")
    findings: list[dict] = []
    sev = fc.get("severity_override", rule.get("severity", "warning"))

    if kind == "missing_preceding_comment":
        for entity in manifest.get("entities", []):
            if not h_series_applies(entity):
                continue
            if not strict_comment_coverage and not entity.get("touched_header", False):
                continue
            if entity.get("preceding_comment_present", False):
                continue
            findings.append({
                "rule_id": rule["id"],
                "file": entity["file"],
                "line_start": entity["line_start"],
                "line_end": entity["line_start"],
                "lemma_name": entity.get("name"),
                "severity": sev,
                "evidence_quote": entity.get("header", "").strip(),
                "stage": "stage1",
            })
    elif kind == "comment_tag_absence":
        for entity in manifest.get("entities", []):
            if not h_series_applies(entity):
                continue
            if not strict_comment_coverage and not _entity_touched(entity):
                continue
            tag = _comment_role_tag(entity)
            if tag is not None:
                continue  # validity handled by H002
            name = entity.get("name", "")
            present = entity.get("preceding_comment_present", False)
            if not present:
                sev_use, why = "error", "no preceding comment and no role tag"
            elif entity.get("touched_header", False):
                sev_use, why = "error", "declaration changed; a role tag is required"
            elif _content_floor_ok(_strip_comment_delims(entity.get("preceding_comment", "")), name):
                sev_use, why = "warning", "legacy comment grandfathered; add a role tag"
            else:
                sev_use, why = "error", "degenerate comment and no role tag"
            findings.append({
                "rule_id": rule["id"], "file": entity["file"],
                "line_start": entity["line_start"], "line_end": entity["line_start"],
                "lemma_name": name, "severity": sev_use,
                "evidence_quote": entity.get("header", "").strip(),
                "stage": "stage1", "reason": why,
            })
    elif kind == "comment_tag_validity":
        labels = _main_purpose_labels(cfg)
        for entity in manifest.get("entities", []):
            if not h_series_applies(entity):
                continue
            if not strict_comment_coverage and not _entity_touched(entity):
                continue
            tag = _comment_role_tag(entity)
            if tag is None:
                continue  # absence handled by H001
            name = entity.get("name", "")
            kindk = entity.get("kind", "")
            problems = []
            if tag.get("multi"):
                problems.append("more than one role tag")
            is_def = kindk in ("Definition", "Fixpoint")
            if is_def and tag["kind"] != "intent":
                problems.append("definitions use @intent, not @" + tag["kind"])
            if not is_def and tag["kind"] == "intent":
                problems.append("lemmas use @main or @composes, not @intent")
            if tag["kind"] in ("intent", "main") and not _content_floor_ok(tag["value"], name):
                problems.append("empty or degenerate tag value")
            if tag["kind"] == "main":
                for lab in (tag.get("labels") or []):
                    if lab not in labels:
                        problems.append(f"@main label '{lab}' not in main_purpose_labels")
                if not tag.get("labels"):
                    problems.append("@main missing a label")
            if tag["kind"] == "composes":
                targets = tag.get("targets") or []
                if not targets:
                    problems.append("@composes names no target")
                for tgt in targets:
                    if not _composes_target_exists(tgt):
                        problems.append(f"@composes target '{tgt}' has no declaration in the repo")
            if problems:
                findings.append({
                    "rule_id": rule["id"], "file": entity["file"],
                    "line_start": entity["line_start"], "line_end": entity["line_start"],
                    "lemma_name": name, "severity": rule.get("severity", "error"),
                    "evidence_quote": (entity.get("preceding_comment", "") or "").strip()[:200],
                    "stage": "stage1", "reason": "; ".join(problems),
                })
    elif kind == "comment_composes_reachability":
        # Build the @composes edge graph over the manifest's entities. Mark
        # @main nodes. A helper is flagged when NO node reachable from it
        # (including via other in-manifest helpers) is @main AND every edge it
        # follows stays inside the manifest (a target outside the manifest is
        # treated as "unknown" -> not flagged, disclosed limitation).
        by_name = {}
        is_main = {}
        edges = {}
        for entity in manifest.get("entities", []):
            tag = _comment_role_tag(entity)
            nm = entity.get("name", "")
            by_name[nm] = entity
            is_main[nm] = bool(tag and tag["kind"] == "main")
            edges[nm] = list(tag["targets"]) if (tag and tag["kind"] == "composes") else []
        for entity in manifest.get("entities", []):
            if not strict_comment_coverage and not _entity_touched(entity):
                continue
            tag = _comment_role_tag(entity)
            if not tag or tag["kind"] != "composes":
                continue
            nm = entity.get("name", "")
            # BFS within the manifest.
            seen, stack, reached_main, left_manifest = set(), list(edges[nm]), False, False
            while stack:
                t = stack.pop()
                if t in seen:
                    continue
                seen.add(t)
                if t not in by_name:
                    left_manifest = True
                    continue
                if is_main.get(t):
                    reached_main = True
                    break
                stack.extend(edges.get(t, []))
            if not reached_main and not left_manifest:
                findings.append({
                    "rule_id": rule["id"], "file": entity["file"],
                    "line_start": entity["line_start"], "line_end": entity["line_start"],
                    "lemma_name": nm, "severity": "warning",
                    "evidence_quote": entity.get("header", "").strip(),
                    "stage": "stage1",
                    "reason": "@composes chain dead-ends without reaching a @main lemma",
                })
    elif kind == "naming_conformance_or_justify":
        findings.extend(_check_naming_conformance_or_justify(rule, manifest, sev))
    return findings


# ---- I001: naming conformance or justify ---------------------------------

# Canonical MathComp suffixes that tail-rescue an otherwise long name.
_MC_CANONICAL_SUFFIXES = [
    "_A", "_AC", "_ACA", "_C", "_CA", "_K", "_D", "_I", "_V",
    "_X", "_Xn", "_Xz", "_Mn", "_Z",
    "_P", "_E", "_W",
    "_ge0", "_le0", "_eq0", "_gt0", "_lt0", "_neq0",
    "_card", "_inj", "_surj", "_bij", "_subset", "_le1", "_ge1",
    "_id", "_idP", "_iff", "_Pn",
]

# Forbidden "kind-suffixes" that duplicate the declaration kind.
_REDUNDANT_SUFFIXES = [
    "_lemma", "_theorem", "_fact", "_corollary", "_proposition",
    "_proof", "_thm",
]

# Generic drift tokens that a MathComp-style name would not carry.
_DRIFT_TOKENS = [
    "_works", "_test", "_tmp", "_old", "_new",
    "_foo", "_bar", "_baz",
    "_placeholder", "_helper", "_helper1", "_helper2",
    "_xxx", "_hack",
]

_NAMING_TAG_RE = re.compile(r"(?mi)^[\s*(]*Naming\s*:\s*\S")


def _ends_with_any(name: str, suffixes: list[str]) -> str | None:
    for s in sorted(suffixes, key=len, reverse=True):
        if name.endswith(s):
            return s
    return None


def _contains_any(name: str, tokens: list[str]) -> str | None:
    for t in tokens:
        if t in name:
            return t
    return None


def _name_non_conforming_reason(name: str) -> str | None:
    """Return a short reason string when the name is non-conforming, else None."""
    # Rule 1: redundant kind-suffix.
    m = _ends_with_any(name, _REDUNDANT_SUFFIXES)
    if m:
        return f"redundant suffix `{m}` duplicates the declaration kind"
    # Rule 2: generic drift token.
    m = _contains_any(name, _DRIFT_TOKENS)
    if m:
        return f"generic drift token `{m.strip('_')}` in the name"
    # Rule 3: five or more components and no canonical tail suffix.
    if name.islower() and name.count("_") >= 4:
        if _ends_with_any(name, _MC_CANONICAL_SUFFIXES) is None:
            return "five or more underscore-separated components without a canonical MathComp suffix"
    return None


def _preceding_has_naming_tag(entity: dict) -> bool:
    pc = entity.get("preceding_comment", "") or ""
    return bool(_NAMING_TAG_RE.search(pc))


def _body_has_naming_tag_for(entity: dict, target_name: str) -> bool:
    """Check the entity's preceding comment for a Naming: line that mentions
    the given inner-binding name (used for local `let` justifications)."""
    pc = entity.get("preceding_comment", "") or ""
    for line in pc.splitlines():
        if _NAMING_TAG_RE.match(line):
            if target_name in line:
                return True
    return False


# Captures `let NAME :=` inside proof bodies and term bodies. Also matches
# `Let NAME :=` when it appears at the line start.
_LET_RE = re.compile(r"(?m)(?:^|[ \t;(])let[ \t]+([A-Za-z_][A-Za-z0-9_']*)[ \t]*:=")
_MODULE_LET_RE = re.compile(r"(?m)^[ \t]*Let[ \t]+([A-Za-z_][A-Za-z0-9_']*)\b")
_VAR_HYP_RE = re.compile(r"(?m)^[ \t]*(?:Variable|Variables|Hypothesis|Hypotheses)[ \t]+([A-Za-z_][A-Za-z0-9_']*)")


def _scan_nested_names(entity: dict) -> list[tuple[str, int, str]]:
    """Return (name, line_number, evidence_quote) for every nested binding
    inside the entity body that I001 should inspect."""
    body = entity.get("body", "")
    base = entity.get("line_start", 1)
    out: list[tuple[str, int, str]] = []
    body_lines = body.splitlines()

    def line_of_offset(off: int) -> int:
        prefix = body[:off]
        return base + prefix.count("\n")

    for m in _LET_RE.finditer(body):
        ln = line_of_offset(m.start(1))
        quote = body_lines[ln - base].strip() if 0 <= ln - base < len(body_lines) else m.group(0)
        out.append((m.group(1), ln, quote))
    for m in _MODULE_LET_RE.finditer(body):
        ln = line_of_offset(m.start(1))
        quote = body_lines[ln - base].strip() if 0 <= ln - base < len(body_lines) else m.group(0)
        out.append((m.group(1), ln, quote))
    for m in _VAR_HYP_RE.finditer(body):
        ln = line_of_offset(m.start(1))
        quote = body_lines[ln - base].strip() if 0 <= ln - base < len(body_lines) else m.group(0)
        out.append((m.group(1), ln, quote))
    return out


_I001_TOP_KINDS = {
    "Lemma", "Theorem", "Fact", "Corollary", "Proposition",
    "Definition", "Fixpoint", "CoFixpoint",
    "Hypothesis", "Hypotheses", "Variable", "Variables",
}


def _check_naming_conformance_or_justify(rule: dict, manifest: dict, sev: str) -> list[dict]:
    findings: list[dict] = []
    for entity in manifest.get("entities", []):
        kind = entity.get("kind", "")
        name = entity.get("name", "")
        # Top-level name check.
        if kind in _I001_TOP_KINDS and name:
            reason = _name_non_conforming_reason(name)
            if reason is not None and not _preceding_has_naming_tag(entity):
                findings.append({
                    "rule_id": rule["id"],
                    "file": entity["file"],
                    "line_start": entity["line_start"],
                    "line_end": entity["line_start"],
                    "lemma_name": name,
                    "severity": sev,
                    "evidence_quote": entity.get("header", "").strip(),
                    "stage": "stage1",
                    "reason": reason,
                })
        # Nested Variable / Hypothesis / let bindings inside the body.
        for nested_name, line_no, quote in _scan_nested_names(entity):
            if nested_name == name:
                continue  # don't double-count the entity itself
            reason = _name_non_conforming_reason(nested_name)
            if reason is None:
                continue
            # Inline comment justification on the same line?
            inline_ok = bool(re.search(r"\(\*[^*]*Naming\s*:\s*\S", quote, re.IGNORECASE))
            tagged_in_parent = _body_has_naming_tag_for(entity, nested_name)
            if inline_ok or tagged_in_parent:
                continue
            findings.append({
                "rule_id": rule["id"],
                "file": entity["file"],
                "line_start": line_no,
                "line_end": line_no,
                "lemma_name": name,
                "severity": sev,
                "evidence_quote": quote,
                "stage": "stage1",
                "reason": f"inner binding `{nested_name}`: {reason}",
            })
    return findings


def exceptions_match(rule: dict, quote: str, lemma_name: str | None) -> bool:
    """Return True when quote or lemma_name matches any exception regex."""
    for ex in rule.get("exceptions", []) or []:
        try:
            rx = re.compile(ex)
        except re.error:
            continue
        if rx.search(quote):
            return True
        if lemma_name and rx.search(lemma_name):
            return True
    return False


def apply_rule_to_entity(rule: dict, entity: dict) -> list[dict]:
    fp = rule["fast_pattern"]
    pattern = fp["pattern"]
    flags = re.MULTILINE
    pat = re.compile(pattern, flags)
    text = entity["body"]
    if fp.get("ignore_in_comments", True):
        text = strip_line_comments(text)
    findings = []
    file_glob = fp.get("file_glob", "*.v")
    if not fnmatch.fnmatch(entity["file"], file_glob):
        return findings
    # Only fire for matches that overlap a touched line.
    touched = set(entity["touched_lines"])
    base_line = entity["line_start"]
    # Walk matches, convert offset to absolute line number.
    pos = 0
    lines = text.split("\n")
    # Build line-offset map.
    line_offsets = [0]
    for ln in lines[:-1]:
        line_offsets.append(line_offsets[-1] + len(ln) + 1)
    for m in pat.finditer(text):
        start_off = m.start()
        # Binary search for the line.
        lo, hi = 0, len(line_offsets) - 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if line_offsets[mid] <= start_off:
                lo = mid
            else:
                hi = mid - 1
        rel_line = lo + 1
        abs_line = base_line + rel_line - 1
        if abs_line not in touched:
            continue
        quote = lines[rel_line - 1].strip() if rel_line - 1 < len(lines) else m.group(0)
        # F001-style rules extract the candidate identifier from the line
        # and apply the exceptions allowlist to it. Use the lemma name from
        # the declaration if present, else the first identifier after the
        # decl keyword.
        candidate_name = entity.get("name")
        id_m = re.match(r"\s*(?:Lemma|Theorem|Fact|Corollary|Proposition|Definition|Fixpoint)\s+([A-Za-z_][A-Za-z0-9_']*)", quote)
        if id_m:
            candidate_name = id_m.group(1)
        if exceptions_match(rule, quote, candidate_name):
            continue
        sev = fp.get("severity_override", rule.get("severity", "warning"))
        findings.append({
            "rule_id": rule["id"],
            "file": entity["file"],
            "line_start": abs_line,
            "line_end": abs_line,
            "lemma_name": entity.get("name"),
            "severity": sev,
            "evidence_quote": quote,
            "stage": "stage1",
        })
    return findings


def apply_rule_to_unanchored(rule: dict, hunk: dict) -> list[dict]:
    fp = rule["fast_pattern"]
    pattern = fp["pattern"]
    file_glob = fp.get("file_glob", "*.v")
    if not fnmatch.fnmatch(hunk["file"], file_glob):
        return []
    pat = re.compile(pattern, re.MULTILINE)
    text = "\n".join(hunk["lines"])
    if fp.get("ignore_in_comments", True):
        text = strip_line_comments(text)
    findings = []
    for idx, ln in enumerate(text.splitlines()):
        if pat.search(ln):
            abs_line = hunk["line_start"] + idx
            id_m = re.match(r"\s*(?:Lemma|Theorem|Fact|Corollary|Proposition|Definition|Fixpoint)\s+([A-Za-z_][A-Za-z0-9_']*)", ln)
            candidate_name = id_m.group(1) if id_m else None
            if exceptions_match(rule, ln, candidate_name):
                continue
            sev = fp.get("severity_override", rule.get("severity", "warning"))
            findings.append({
                "rule_id": rule["id"],
                "file": hunk["file"],
                "line_start": abs_line,
                "line_end": abs_line,
                "lemma_name": None,
                "severity": sev,
                "evidence_quote": ln.strip(),
                "stage": "stage1",
            })
    return findings


def main() -> int:
    if len(sys.argv) < 2:
        print("usage: stage1-regex.py <tier0.json>", file=sys.stderr)
        return 1
    with open(sys.argv[1]) as f:
        manifest = json.load(f)
    rules = load_rules()
    cfg = load_config()
    strict_comment = bool(cfg.get("strict_comment_coverage", False))
    findings: list[dict] = []
    errors: list[str] = []
    for rule in rules:
        if not rule.get("enabled", True):
            continue
        stage_mode = rule.get("stage_mode")
        if stage_mode not in ("stage1_only", "both"):
            continue
        if rule.get("fast_check"):
            findings.extend(apply_fast_check(rule, manifest, strict_comment, cfg))
            continue
        ok, msg = validate_fast_pattern(rule)
        if not ok:
            errors.append(f"rule {rule.get('id','?')}: {msg}")
            continue
        for entity in manifest.get("entities", []):
            findings.extend(apply_rule_to_entity(rule, entity))
        for hunk in manifest.get("unanchored_hunks", []):
            findings.extend(apply_rule_to_unanchored(rule, hunk))
    # Deduplicate identical findings.
    seen = set()
    dedup = []
    for f in findings:
        key = (f["rule_id"], f["file"], f["line_start"], f["line_end"], f["evidence_quote"])
        if key in seen:
            continue
        seen.add(key)
        dedup.append(f)
    out = {"findings": dedup, "errors": errors}
    json.dump(out, sys.stdout, indent=2, ensure_ascii=False)
    print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
