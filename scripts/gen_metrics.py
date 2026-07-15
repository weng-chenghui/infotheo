#!/usr/bin/env python3
"""Generate formalization metrics table from git diff and rocq-stats."""

import re
import subprocess
import sys
from html.parser import HTMLParser
from pathlib import Path
from collections import defaultdict

# ── Configuration ──────────────────────────────────────────────────────────

REPO_ROOT = Path(__file__).resolve().parent.parent
STATS_HTML = Path.home() / "Projects/coq/rocq-stats/rocq-stats/dsdp/stats.html"

EXCLUDED_FILES = {
    "du2002/spp_tactics.v",
    "du2002/spp_entropy.v",
    "du2002/spp_proba.v",
    "du2002/spp_proof.v",
    "smc/smc_interpreter_mkBind.v",
    "smc/graded_resource.v",
    "smc/smc_party_indep.v",
    "smc/znto_lemmas.v",
}

# Files that count in total but are not in any category row
# (diff additions only, since these exist in master)
EXTRA_TOTAL_FILES = {
    "probability/proba.v",
    "information_theory/entropy.v",
}

# Category definitions: row_name -> list of file patterns
# Patterns ending with / are directory prefixes; others are exact matches.
CATEGORIES = {
    "Interpreter soundness (smc_interpreter.v)": [
        "smc/smc_interpreter.v",
    ],
    "Session types (smc_session_types.v)": [
        "smc/smc_session_types.v",
        "dumas2017dual/dsdp/dsdp_session_types.v",
        "du2002/spp_session_types.v",
    ],
    "piSMC DSL (*_pismc.v)": [
        "smc/pismc.v",
        "dumas2017dual/dsdp/dsdp_pismc.v",
        "du2002/spp_pismc.v",
        "du2002/spp_program.v",
    ],
    "Language interface and implementation": [
        "dumas2017dual/dsdp/dsdp_interface.v",
        "du2002/spp_interface.v",
    ],
    "AHE hierarchy (homomorphic_encryption/)": [
        "homomorphic_encryption/",
    ],
    "Entropic security proofs": [
        "dumas2017dual/entropy_fiber/",
        "dumas2017dual/lib/",
        "dumas2017dual/dsdp/dsdp_entropy.v",
        "dumas2017dual/dsdp/dsdp_entropy_trace.v",
    ],
    "DSDP protocol and security proofs": [
        "dumas2017dual/dsdp/dsdp_correctness.v",
        "dumas2017dual/dsdp/dsdp_security.v",
        "dumas2017dual/dsdp/dsdp_program.v",
        "dumas2017dual/dsdp/dsdp_syntax.v",
        "dumas2017dual/dsdp/dsdp_syntax_demo.v",
    ],
}

# Directories whose .v files are in scope for the total
TOTAL_SCOPE_DIRS = ["smc/", "dumas2017dual/", "homomorphic_encryption/"]
# Only these du2002/ files are included
INCLUDED_DU2002 = {
    "du2002/spp_pismc.v",
    "du2002/spp_program.v",
    "du2002/spp_session_types.v",
    "du2002/spp_interface.v",
}


# ── Step 1: Parse diff for LoC ─────────────────────────────────────────────

def parse_diff_loc(diff_path: str) -> dict[str, int]:
    """Parse a unified diff and return {filepath: added_line_count}."""
    counts = defaultdict(int)
    current_file = None
    with open(diff_path) as f:
        for line in f:
            if line.startswith("diff --git"):
                # Extract b/ path
                m = re.search(r' b/(.+)$', line)
                current_file = m.group(1) if m else None
            elif line.startswith("+") and not line.startswith("+++"):
                if current_file and current_file.endswith(".v"):
                    counts[current_file] += 1
    return dict(counts)


# ── Step 2: Parse stats.html for lemma counts ──────────────────────────────

class StatsHTMLParser(HTMLParser):
    """Extract lemma entries from stats.html."""

    def __init__(self):
        super().__init__()
        self.lemmas = []  # list of (file, name, kind) where kind is "main" or "helper"
        self._current_file = None
        self._current_section_kind = None  # "main" or "helper"
        self._in_badge = False
        self._badge_text = ""
        self._in_lemma_name = False
        self._lemma_name = ""

    def handle_starttag(self, tag, attrs):
        attrs_dict = dict(attrs)
        if tag == "div":
            cls = attrs_dict.get("class", "")
            data_file = attrs_dict.get("data-file", "")
            if "file-section" in cls and data_file:
                self._current_file = data_file
                if "main-section" in cls:
                    self._current_section_kind = "main"
                elif "helper-section" in cls:
                    self._current_section_kind = "helper"
        if tag == "span":
            cls = attrs_dict.get("class", "")
            if cls.startswith("badge badge-"):
                self._in_badge = True
                self._badge_text = ""
        if tag == "a":
            cls = attrs_dict.get("class", "")
            if cls == "lemma-name":
                self._in_lemma_name = True
                self._lemma_name = ""

    def handle_data(self, data):
        if self._in_badge:
            self._badge_text += data
        if self._in_lemma_name:
            self._lemma_name += data

    def handle_endtag(self, tag):
        if tag == "span" and self._in_badge:
            self._in_badge = False
        if tag == "a" and self._in_lemma_name:
            self._in_lemma_name = False
            if self._lemma_name and self._current_file:
                self.lemmas.append((
                    self._current_file,
                    self._lemma_name.strip(),
                    self._current_section_kind or "helper",
                ))


def parse_stats_html(path: Path) -> list[tuple[str, str, str]]:
    """Return list of (file, lemma_name, 'main'|'helper')."""
    parser = StatsHTMLParser()
    parser.feed(path.read_text())
    return parser.lemmas


# ── Step 3: Count lemmas from diff for files not in stats ──────────────────

def count_lemmas_from_diff(diff_path: str, target_files: set[str]) -> list[tuple[str, str, str]]:
    """Count Lemma/Theorem/Corollary definitions from added lines in the diff
    for files in target_files. Returns (file, name, 'helper')."""
    results = []
    current_file = None
    pattern = re.compile(r'^\+\s*(?:Lemma|Theorem|Corollary)\s+(\w+)')
    with open(diff_path) as f:
        for line in f:
            if line.startswith("diff --git"):
                m = re.search(r' b/(.+)$', line)
                current_file = m.group(1) if m else None
            elif current_file in target_files and line.startswith("+"):
                m2 = pattern.match(line)
                if m2:
                    results.append((current_file, m2.group(1), "helper"))
    return results


# ── Step 4: Categorize files ───────────────────────────────────────────────

def file_matches_pattern(filepath: str, pattern: str) -> bool:
    if pattern.endswith("/"):
        return filepath.startswith(pattern) and filepath.endswith(".v")
    return filepath == pattern


def categorize_file(filepath: str) -> str | None:
    """Return category name or None if uncategorized."""
    for cat, patterns in CATEGORIES.items():
        for pat in patterns:
            if file_matches_pattern(filepath, pat):
                return cat
    return None


def is_in_total_scope(filepath: str) -> bool:
    """Check if file is in total scope."""
    if filepath in EXCLUDED_FILES:
        return False
    if filepath in EXTRA_TOTAL_FILES:
        return True
    for d in TOTAL_SCOPE_DIRS:
        if filepath.startswith(d) and filepath.endswith(".v"):
            return True
    if filepath in INCLUDED_DU2002:
        return True
    return False


# ── Main ───────────────────────────────────────────────────────────────────

def main():
    diff_path = "/tmp/dumas2017dual_diff.patch"

    # Check if diff exists, generate if not
    if not Path(diff_path).exists():
        subprocess.run(
            ["git", "diff", "master...dumas2017dual"],
            stdout=open(diff_path, "w"),
            cwd=REPO_ROOT,
        )

    # Step 1: Parse diff LoC
    loc_per_file = parse_diff_loc(diff_path)

    # Step 2: Parse stats.html
    stats_lemmas = parse_stats_html(STATS_HTML)
    stats_files = {l[0] for l in stats_lemmas}

    # Step 3: Count lemmas from diff for files not in stats
    # Included smc/ and du2002/ files not covered by stats.html
    files_needing_diff_lemma_count = set()
    for f in loc_per_file:
        if f.endswith(".v") and f not in EXCLUDED_FILES and f not in stats_files:
            if is_in_total_scope(f):
                files_needing_diff_lemma_count.add(f)

    diff_lemmas = count_lemmas_from_diff(diff_path, files_needing_diff_lemma_count)

    # Combine all lemmas
    all_lemmas = stats_lemmas + diff_lemmas

    # ── LoC per category ────────────────────────────────────────────────
    print("=" * 70)
    print("FORMALIZATION METRICS")
    print("=" * 70)
    print()

    print("─── Lines of Code per Category ───")
    print()

    total_loc = 0
    cat_loc = defaultdict(int)
    cat_files = defaultdict(list)
    uncategorized_files = []

    for filepath, count in sorted(loc_per_file.items()):
        if not is_in_total_scope(filepath):
            continue
        total_loc += count
        cat = categorize_file(filepath)
        if cat:
            cat_loc[cat] += count
            cat_files[cat].append((filepath, count))
        else:
            uncategorized_files.append((filepath, count))

    for cat_name in CATEGORIES:
        loc = cat_loc[cat_name]
        print(f"  {cat_name:50s} {loc:>6d} loc")
        for f, c in cat_files[cat_name]:
            print(f"    {f:55s} {c:>5d}")
    print()

    if uncategorized_files:
        uncategorized_total = sum(c for _, c in uncategorized_files)
        print(f"  {'(uncategorized, in total only)':50s} {uncategorized_total:>6d} loc")
        for f, c in uncategorized_files:
            print(f"    {f:55s} {c:>5d}")
        print()

    print(f"  {'TOTAL new/modified lines of Coq code':50s} {total_loc:>6d} loc")
    print()

    # ── Lemma counts ────────────────────────────────────────────────────
    print("─── Lemma / Theorem Counts ───")
    print()

    # Only count lemmas from files in scope
    main_count = 0
    helper_count = 0
    main_lemmas_by_file = defaultdict(list)
    helper_lemmas_by_file = defaultdict(list)

    for filepath, name, kind in all_lemmas:
        if not is_in_total_scope(filepath):
            continue
        if kind == "main":
            main_count += 1
            main_lemmas_by_file[filepath].append(name)
        else:
            helper_count += 1
            helper_lemmas_by_file[filepath].append(name)

    total_lemma_count = main_count + helper_count

    print(f"  Main lemmas and theorems:    {main_count:>4d}")
    print(f"  Technical lemmas:            {helper_count:>4d}")
    print(f"  Total lemmas and theorems:   {total_lemma_count:>4d}")
    print()

    # ── Verification ────────────────────────────────────────────────────
    print("─── Verification: stats.html cross-check ───")
    print()

    stats_main = sum(1 for _, _, k in stats_lemmas if k == "main")
    stats_helper = sum(1 for _, _, k in stats_lemmas if k == "helper")
    print(f"  stats.html main results:  {stats_main} (expected 41)")
    print(f"  stats.html helper lemmas: {stats_helper} (expected 229)")
    print(f"  stats.html total:         {stats_main + stats_helper} (expected 270)")
    print()

    # Lemmas from diff (files not in stats.html)
    if diff_lemmas:
        print("─── Lemmas from diff (not in stats.html) ───")
        print()
        for filepath, name, kind in diff_lemmas:
            print(f"  {filepath:50s} {name}")
        print(f"  Total: {len(diff_lemmas)}")
        print()

    # ── Per-file detail ─────────────────────────────────────────────────
    print("─── Per-file breakdown (main lemmas) ───")
    print()
    for filepath in sorted(main_lemmas_by_file):
        names = main_lemmas_by_file[filepath]
        print(f"  {filepath} ({len(names)} main)")
        for n in names:
            print(f"    - {n}")
    print()

    print("─── Per-file breakdown (helper lemmas) ───")
    print()
    for filepath in sorted(helper_lemmas_by_file):
        names = helper_lemmas_by_file[filepath]
        print(f"  {filepath} ({len(names)} helper)")

    # ── LaTeX output ────────────────────────────────────────────────────
    print()
    print("=" * 70)
    print("LATEX TABLE (copy-paste ready)")
    print("=" * 70)
    print()
    rows = []
    for cat_name in CATEGORIES:
        rows.append((cat_name, cat_loc[cat_name]))

    print(r"\begin{table}[t]")
    print(r"  \centering")
    print(r"  \caption{Formalization metrics.}")
    print(r"  \label{tab:metrics}")
    print(r"  \begin{tabular}{l r}")
    print(r"    \hline")
    print(r"    Component & Size \\")
    print(r"    \hline")
    for name, loc in rows:
        print(f"    {name} & \\textbf{{{loc:,}}} loc \\\\")
    print(r"    \hline")
    print(f"    Total new/modified lines of Coq code & \\textbf{{{total_loc:,}}} loc \\\\")
    print(f"    Main lemmas and theorems & \\textbf{{{main_count}}} \\\\")
    print(f"    Technical lemmas & \\textbf{{{helper_count}}} \\\\")
    print(f"    Total lemmas and theorems & \\textbf{{{total_lemma_count}}} \\\\")
    print(r"    \hline")
    print(r"  \end{tabular}")
    print(r"\end{table}")


if __name__ == "__main__":
    main()
