#!/usr/bin/env python3
"""Per-section motivational-move density for the WADT paper.

Committed instrument for the acceptance gates of
2026-08-10-wadt-transition-fixes-design.md (audit finding A10).

std  = the nine connective families of the baseline-transition-analysis
       skill's count_connectives.py, matched with the same case-sensitive
       regexes.
ext  = the vocabulary-artifact supplement measured across the whole panel
       on 2026-08-10: clause-connector ", so " and the contrast family
       instead / by contrast / in contrast / whereas / unlike.

Usage: python3 wadt_per_section.py [path/to/main.tex]
"""
import os
import re
import sys

DEFAULT = os.path.join(os.path.dirname(__file__), os.pardir, os.pardir,
                       os.pardir, os.pardir, "pgg-smc", "paper-wadt2026",
                       "main.tex")

STD_FAMILIES = [
    ("orientation", r"\bIn this (section|paper|article|chapter)\b"),
    ("purpose", r"\b(in order to|so that we|so as to)\b"),
    ("reason", r"\b(because|since)\b"),
    ("inference", r"\b(Thus|thus|Therefore|therefore|Hence|hence)\b"),
    ("instance", r"\b[Ff]or (example|instance)\b"),
    ("gloss", r"\b(Roughly speaking|roughly speaking|Informally|informally|"
              r"Intuitively|intuitively)\b"),
    ("aside", r"\b[Ww]e (note|can observe|observe|sometimes|remark)\b"),
    ("example", r"(\bExample\s+\d|\\begin\{example\})"),
    ("adversative", r"\b(Although|although|However|however)\b"),
]
EXT_FAMILIES = [
    ("comma-so", r",\s+so\s"),
    ("contrast", r"\b(instead|[Bb]y contrast|[Ii]n contrast|whereas|"
                 r"[Uu]nlike)\b"),
]

STRIP_ENVS = ("tikzpicture", "lstlisting", "tabular", "verbatim",
              "figure*", "algorithmic")


def clean(tex):
    t = re.sub(r"(?m)^\s*%.*$", " ", tex)
    for env in STRIP_ENVS:
        t = re.sub(r"\\begin\{%s\}.*?\\end\{%s\}" % (env, env), " ", t,
                   flags=re.S)
    return t


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else DEFAULT
    raw = open(path, encoding="utf-8", errors="replace").read()
    parts = re.split(r"(\\section\*?\{[^}]*\})", raw)
    sections = []
    if parts[0].strip():
        sections.append(("preamble+abstract", parts[0]))
    for i in range(1, len(parts), 2):
        title = re.sub(r"\\section\*?\{([^}]*)\}", r"\1", parts[i])
        sections.append((title, parts[i + 1] if i + 1 < len(parts) else ""))

    print(f"{'section':<46}{'words':>6}{'std':>5}{'ext':>5}{'all/10k':>9}")
    print("-" * 71)
    tw = ts = te = 0
    for title, body in sections:
        txt = clean(body)
        w = len(re.findall(r"[A-Za-z']+", txt))
        if not w:
            continue
        std = sum(len(re.findall(p, txt)) for _, p in STD_FAMILIES)
        ext = sum(len(re.findall(p, txt)) for _, p in EXT_FAMILIES)
        tw, ts, te = tw + w, ts + std, te + ext
        print(f"{title[:46]:<46}{w:>6}{std:>5}{ext:>5}"
              f"{(std + ext) / w * 1e4:>9.1f}")
    print("-" * 71)
    print(f"{'TOTAL':<46}{tw:>6}{ts:>5}{te:>5}{(ts + te) / tw * 1e4:>9.1f}")
    print(f"\nstd TOTAL per 10k: {ts / tw * 1e4:.1f}")


if __name__ == "__main__":
    main()
