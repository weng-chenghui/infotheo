#!/usr/bin/env python3
"""Blueprint coverage checker for the DSDP derivation chain.

Scope is the set of .v files listed in make_blueprint.sh's MODULES array (the
exact set the blueprint documents). The checker hard-fails when:

  * a declared identifier in a scoped module has no \\rocq{} node and is not in
    blueprint-exclude.txt  (an *uncovered* declaration), or
  * a \\rocq{} ref points into a scoped module at an identifier that module does
    not declare  (a *dangling* ref).

It prints `code=N blueprint=M excl=K` and exits 1 on any failure, 0 otherwise.
Section parameters (Variable/Hypothesis/Context/Let) are never blueprint nodes
and are auto-excluded. Run via `make dsdp-blueprint-coverage`.
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))          # dumas2017dual/blueprint
REPO = os.path.abspath(os.path.join(HERE, "..", ".."))     # repo root (-R . infotheo)
MAKE_BLUEPRINT = os.path.join(HERE, "make_blueprint.sh")
EXCLUDE_FILE = os.path.join(HERE, "blueprint-exclude.txt")
SRC_DIR = os.path.join(HERE, "src")

# Declaration keywords whose name we require a blueprint node for.
DECL_KW = (
    "Theorem|Lemma|Corollary|Proposition|Fact|Remark|Example|"
    "Definition|Fixpoint|CoFixpoint|Record|Inductive|Variant|Instance|Axiom"
)
DECL_RE = re.compile(
    r"(?m)^[ \t]*(?:#\[[^\]]*\][ \t\n]*)?"
    r"(?:(?:Local|Global|Program|Polymorphic|Monomorphic|Private|Export)[ \t]+)*"
    r"(?:" + DECL_KW + r")[ \t\n]+([A-Za-z_][A-Za-z0-9_']*)"
)
# Inductive/Variant constructor heads: a `| Name ...` line whose head is not a
# match-arm (no `=>` before the next colon/newline). Blueprint nodes may point
# at constructors, so they count as declared.
CTOR_RE = re.compile(r"(?m)^[ \t]*\|[ \t]*([A-Za-z_][A-Za-z0-9_']*)\b(?![^\n:]*=>)")
ROCQ_RE = re.compile(r"\\rocq\{(infotheo\.[A-Za-z0-9_.]+)\}")


def strip_comments(text):
    """Remove Coq (* ... *) comments, honoring nesting."""
    out, depth, i, n = [], 0, 0, len(text)
    while i < n:
        two = text[i:i + 2]
        if two == "(*":
            depth += 1
            i += 2
        elif two == "*)" and depth > 0:
            depth -= 1
            i += 2
        elif depth == 0:
            out.append(text[i])
            i += 1
        else:
            i += 1
    return "".join(out)


def module_logical_name(relpath):
    """dumas2017dual/dsdp/foo/bar.v -> infotheo.dumas2017dual.dsdp.foo.bar"""
    noext = relpath[:-2] if relpath.endswith(".v") else relpath
    return "infotheo." + noext.replace("/", ".")


def read_modules():
    """Parse the MODULES=( ... ) array from make_blueprint.sh."""
    with open(MAKE_BLUEPRINT) as f:
        body = f.read()
    m = re.search(r"MODULES=\((.*?)\)", body, re.S)
    if not m:
        sys.exit("check_coverage: could not find MODULES=( ... ) in make_blueprint.sh")
    mods = []
    for line in m.group(1).splitlines():
        line = line.split("#", 1)[0].strip()
        if line.endswith(".v"):
            mods.append(line)
    return mods


def read_exclude():
    """Lines are bare `ident` (exclude everywhere) or `module_basename:ident`."""
    glob, permod = set(), set()
    if os.path.exists(EXCLUDE_FILE):
        with open(EXCLUDE_FILE) as f:
            for line in f:
                line = line.split("#", 1)[0].strip()
                if not line:
                    continue
                if ":" in line:
                    permod.add(line)
                else:
                    glob.add(line)
    return glob, permod


def main():
    modules = read_modules()
    glob_excl, permod_excl = read_exclude()

    # declared[logical_name] = { ident: basename }
    declared = {}
    basename_of = {}
    for rel in modules:
        path = os.path.join(REPO, rel)
        if not os.path.exists(path):
            sys.exit("check_coverage: scoped module missing on disk: %s" % rel)
        with open(path) as f:
            src = strip_comments(f.read())
        idents = set(DECL_RE.findall(src)) | set(CTOR_RE.findall(src))
        lname = module_logical_name(rel)
        declared[lname] = idents
        basename_of[lname] = os.path.basename(rel)[:-2]

    # blueprint refs into scoped modules: covered[lname] = {ident}; dangling list
    covered = {l: set() for l in declared}
    dangling = []
    total_refs = 0
    for fn in sorted(os.listdir(SRC_DIR)):
        if not fn.endswith(".tex"):
            continue
        with open(os.path.join(SRC_DIR, fn)) as f:
            for full in ROCQ_RE.findall(f.read()):
                lname, _, ident = full.rpartition(".")
                if lname not in declared:
                    continue                         # ref outside scope: not ours
                total_refs += 1
                if ident in declared[lname]:
                    covered[lname].add(ident)
                else:
                    dangling.append((fn, full))

    # uncovered: declared, not covered, not excluded
    uncovered = []
    n_excl = 0
    for lname, idents in declared.items():
        base = basename_of[lname]
        for ident in sorted(idents):
            if ident in covered[lname]:
                continue
            if ident in glob_excl or ("%s:%s" % (base, ident)) in permod_excl:
                n_excl += 1
                continue
            uncovered.append("%s.%s" % (base, ident))

    n_code = sum(len(v) for v in declared.values())
    n_bp = sum(len(v) for v in covered.values())
    ok = not uncovered and not dangling

    if dangling:
        print("DANGLING (\\rocq ref to a non-existent declaration):")
        for fn, full in sorted(set(dangling)):
            print("  %s : \\rocq{%s}" % (fn, full))
    if uncovered:
        print("UNCOVERED (declared, no \\rocq node, not excluded):")
        for u in sorted(uncovered):
            print("  %s" % u)
    print("%s code=%d blueprint=%d excl=%d (refs into scope=%d)"
          % ("OK" if ok else "FAIL", n_code, n_bp, n_excl, total_refs))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
