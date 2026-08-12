#!/usr/bin/env bash
# Check that every in-scope MonodromyProfile of the repository is represented
# by a complete analysis facade, or is a deliberate alias of one that is.
#
# Universe: tracked .v files under pgg-smc/instances (git ls-files), so
# untracked scratch files, backups and generated files are out by
# construction, and nothing under docs/ is ever read.
#
# Comment-stripping recipe: Python re.sub on (* ... *) with DOTALL, as in
# abstract_metrics.sh, so a profile name mentioned in a comment is never
# counted as a declaration.
#
# Counted declarations, at the top level of a file:
#   - a global Definition whose declared type is MonodromyProfile
#   - a global Definition whose body is one of those profile names, with or
#     without a type ascription (a direct alias)
# Skipped: Local declarations and Let declarations, which are section-local
# abbreviations rather than public profiles, and the facade files
# *_analysis.v, whose profile aliases are the representation itself.
#
# Expected classification, one line per profile:
#   pgl27_profile      represented by PGL27Analysis
#   five_card_profile  represented by FiveCardAnalysis
#   den_boer_profile   deliberate alias of five_card_profile, exposed as
#                      FiveCardAnalysis.den_boer_profile with its own model
#                      rows in the analysis manifest
#   s5_profile         represented by S5Analysis
#   s5x5_profile       represented by S5x5Analysis
#   abel_profile       represented by AbelianAnalysis
#
# Representation is not taken on trust: for each profile the check reads the
# facade file and requires an alias of that profile inside it.
#
# Exit codes:
#   0  the declarations found are exactly the expected ones and every one of
#      them is represented
#   1  an expected profile is unrepresented: its declaration or its facade
#      alias is missing
#   2  an unknown profile declaration was found, or pgg-smc was not found
set -euo pipefail

PGG_SMC="$(cd "$(dirname "$0")/.." && pwd)"
REPO="$(cd "$PGG_SMC/.." && pwd)"
if [ ! -d "$PGG_SMC/instances" ]; then
  echo "ERROR: pgg-smc/instances not found at $PGG_SMC/instances" >&2
  exit 2
fi

cd "$REPO"

IN_SCOPE_LIST=$(git ls-files 'pgg-smc/instances' | grep '\.v$' | sort)

IN_SCOPE_LIST="$IN_SCOPE_LIST" python3 <<'PY'
import os, pathlib, re, sys

files = [f for f in os.environ['IN_SCOPE_LIST'].splitlines() if f]

# name -> (classification, facade file, facade module)
EXPECTED = {
  'pgl27_profile':     ('represented', 'pgg-smc/instances/pgl27/pgl27_analysis.v',
                        'PGL27Analysis'),
  'five_card_profile': ('represented', 'pgg-smc/instances/kim2025/five_card_analysis.v',
                        'FiveCardAnalysis'),
  'den_boer_profile':  ('alias of five_card_profile',
                        'pgg-smc/instances/kim2025/five_card_analysis.v',
                        'FiveCardAnalysis'),
  's5_profile':        ('represented', 'pgg-smc/instances/s5/s5_analysis.v',
                        'S5Analysis'),
  's5x5_profile':      ('represented', 'pgg-smc/instances/s5x5/s5x5_analysis.v',
                        'S5x5Analysis'),
  'abel_profile':      ('represented', 'pgg-smc/instances/abelian/abelian_analysis.v',
                        'AbelianAnalysis'),
}

def strip_comments(src):
    return re.sub(r'\(\*.*?\*\)', '', src, flags=re.DOTALL)

TYPED = re.compile(
    r'^(?P<local>Local\s+|Global\s+)?(?P<kind>Definition|Let)\s+(?P<name>\w+)'
    r'[^:=]*:\s*MonodromyProfile\s*:=\s*(?P<body>[\w.]+)?', re.M)
UNTYPED = re.compile(
    r'^(?P<local>Local\s+|Global\s+)?(?P<kind>Definition|Let)\s+(?P<name>\w+)'
    r'\s*:=\s*(?P<body>[\w.]+)\s*\.', re.M)

found = {}          # name -> (file, body or None)
skipped = []        # (file, name, reason)

for f in files:
    base = os.path.basename(f)
    src = strip_comments(pathlib.Path(f).read_text())
    hits = {}
    for m in TYPED.finditer(src):
        hits[m.group('name')] = (m.group('local'), m.group('kind'),
                                 m.group('body'))
    for m in UNTYPED.finditer(src):
        body = m.group('body').split('.')[-1]
        if body in EXPECTED and m.group('name') not in hits:
            hits[m.group('name')] = (m.group('local'), m.group('kind'), body)
    for name, (local, kind, body) in sorted(hits.items()):
        if base.endswith('_analysis.v'):
            skipped.append((f, name, 'facade alias'))
        elif kind == 'Let':
            skipped.append((f, name, 'section-local Let'))
        elif local and local.strip() == 'Local':
            skipped.append((f, name, 'Local declaration'))
        else:
            found[name] = (f, body)

unknown = sorted(set(found) - set(EXPECTED))
missing = sorted(set(EXPECTED) - set(found))

print('profile declarations found (%d):' % len(found))
for name in sorted(found):
    f, body = found[name]
    kind = EXPECTED.get(name, ('UNKNOWN', '', ''))[0]
    print('  %-18s %-52s %s' % (name, f, kind))

if skipped:
    print()
    print('skipped (%d):' % len(skipped))
    for f, name, why in sorted(skipped):
        print('  %-18s %-52s %s' % (name, f, why))

# Representation evidence: the facade must alias the profile.
unrepresented = []
print()
print('facade evidence:')
for name in sorted(EXPECTED):
    kind, facade, module = EXPECTED[name]
    if name in missing:
        unrepresented.append((name, 'no declaration found'))
        print('  %-18s %-52s MISSING DECLARATION' % (name, facade))
        continue
    if not os.path.exists(facade):
        unrepresented.append((name, 'facade file %s absent' % facade))
        print('  %-18s %-52s MISSING FACADE' % (name, facade))
        continue
    fsrc = strip_comments(pathlib.Path(facade).read_text())
    if re.search(r'^Definition\s+\w+\s*:=\s*(?:[\w.]+\.)?%s\b' % re.escape(name),
                 fsrc, re.M):
        print('  %-18s %-52s %s' % (name, facade, module))
    else:
        unrepresented.append((name, 'facade %s has no alias of %s'
                              % (facade, name)))
        print('  %-18s %-52s NO ALIAS' % (name, facade))

status = 0
if unknown:
    print()
    for name in unknown:
        f, _ = found[name]
        print('UNKNOWN: %s declared in %s is not in the expected list' % (name, f),
              file=sys.stderr)
    status = 2
if unrepresented:
    print()
    for name, why in unrepresented:
        print('UNREPRESENTED: %s: %s' % (name, why), file=sys.stderr)
    if status == 0:
        status = 1

print()
if status == 0:
    print('OK: %d profiles, all represented by a facade or a deliberate alias'
          % len(EXPECTED))
sys.exit(status)
PY
