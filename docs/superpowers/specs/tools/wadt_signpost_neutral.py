#!/usr/bin/env python3
"""I/we-neutral signposting rate, applied uniformly to a paper panel.

Committed instrument for the acceptance gates of
2026-08-10-wadt-transition-fixes-design.md (audit finding A10).

The stock fact_density.py SIGNPOST regex counts only "we define/write/
denote/call/set/say that/put". The WADT paper is single-author and uses
"I" for authorial acts (project decision of 2026-08-10), so this variant
adds the corresponding I-forms. The SAME extended pattern runs over every
panel member; peers use "we", so the extension cannot flatter the target.

Usage:
  python3 wadt_signpost_neutral.py paper1.pdf|.tex[=Label] paper2 ...
"""
import os
import re
import shutil
import subprocess
import sys
import tempfile

SIGNPOST_NEUTRAL = r"""(?x)\b(
   [Ww]e\s+(define|write|denote|call|set|say\s+that|put)
 | I\s+(define|write|denote|call|set|say\s+that|put)
 | what\s+I\s+call
 | is\s+defined\s+(as|by) | are\s+defined\s+(as|by)
 | is\s+called | are\s+called
 | is\s+denoted | denoted\s+by
 | [Dd]efinition\s+\d
 | [Ll]et\s+\$?[A-Za-z\\][^.]{0,30}?\s+be\s+(a|an|the)\s
)\b"""

STRIP_ENVS = ("tikzpicture", "lstlisting", "tabular", "verbatim",
              "figure*", "algorithmic")


def load(path):
    ext = os.path.splitext(path)[1].lower()
    if ext == ".pdf":
        if not shutil.which("pdftotext"):
            sys.exit("pdftotext not found")
        out = os.path.join(tempfile.mkdtemp(), "x.txt")
        subprocess.run(["pdftotext", path, out], check=True,
                       capture_output=True)
        return open(out, encoding="utf-8", errors="replace").read()
    t = open(path, encoding="utf-8", errors="replace").read()
    if ext == ".tex":
        for marker in ("\\begin{abstract}", "\\begin{document}"):
            i = t.find(marker)
            if i != -1:
                t = t[i:]
                break
        t = re.sub(r"(?m)^\s*%.*$", " ", t)
        for env in STRIP_ENVS:
            t = re.sub(r"\\begin\{%s\}.*?\\end\{%s\}" % (env, env), " ", t,
                       flags=re.S)
    return t


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    print(f"{'paper':<28}{'words':>7}{'events':>8}{'per10k':>8}")
    print("-" * 51)
    for arg in sys.argv[1:]:
        path, _, label = arg.partition("=")
        label = label or os.path.basename(path)
        text = load(path)
        w = len(re.findall(r"[A-Za-z']+", text))
        n = len(re.findall(SIGNPOST_NEUTRAL, text))
        print(f"{label[:28]:<28}{w:>7}{n:>8}{n / w * 1e4:>8.1f}")


if __name__ == "__main__":
    main()
