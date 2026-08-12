#!/usr/bin/env bash
# Check that every in-scope MonodromyProfile of the repository is represented
# by a complete analysis facade, or is a deliberate alias of one that is.
#
# Universe: tracked .v files under pgg-smc/instances (git ls-files), so
# backups and generated files are out by construction and nothing under docs/
# is ever read. Two guards keep that universe honest: an untracked .v under
# pgg-smc/instances that declares a profile is an error rather than a silent
# pass, and so is a profile declared in a tracked pgg-smc file outside
# instances, other than the file that declares the record itself.
#
# Comments are removed by a depth-counting scanner rather than a regular
# expression, so nested comments and string literals are handled the way the
# Rocq lexer handles them and a commented-out declaration is never counted.
#
# Counted declarations, at depth zero of a file, that is outside every Module
# and Section:
#   - a global Definition whose declared type is MonodromyProfile, with or
#     without binders and with or without the Program prefix
#   - a global Definition whose body is one of those profile names, with or
#     without a type ascription (a direct alias)
# Skipped: Let declarations and Local declarations, whether written Local or
# #[local], which are section-local abbreviations rather than public profiles,
# and the aliases of the five facade files, which are the representation
# itself. Any other declaration inside a Module or a Section is reported: it
# is reachable only under a qualified name, or takes section variables after
# discharge, so it is not a top-level profile.
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
# Neither half of a line is taken on trust. The alias line is checked against
# the body of the declaration, so den_boer_profile must really be defined as
# five_card_profile, and a profile listed as represented must not be an
# undocumented alias of another one. The facade line is checked against the
# facade file, and the alias must sit between Module <module>. and its End,
# so an alias left behind as dead code outside the module does not count.
#
# Exit codes:
#   0  the declarations found are exactly the expected ones, each has the
#      expected body, and each is aliased inside its facade module
#   1  an expected profile is unrepresented: its declaration, its documented
#      body or its facade alias is missing
#   2  an unknown, duplicated, nested or untracked profile declaration was
#      found, a tracked file was unreadable, or pgg-smc was not found
set -euo pipefail

PGG_SMC="$(cd "$(dirname "$0")/.." && pwd)"
REPO="$(cd "$PGG_SMC/.." && pwd)"
if [ ! -d "$PGG_SMC/instances" ]; then
  echo "ERROR: pgg-smc/instances not found at $PGG_SMC/instances" >&2
  exit 2
fi

cd "$REPO"

IN_SCOPE_LIST=$(git ls-files 'pgg-smc/instances' | { grep '\.v$' || true; } | sort)
UNTRACKED_LIST=$(git ls-files --others --exclude-standard 'pgg-smc/instances' \
  | { grep '\.v$' || true; } | sort)
OUT_OF_SCOPE_LIST=$(git ls-files 'pgg-smc' | { grep '\.v$' || true; } \
  | { grep -v '^pgg-smc/instances/' || true; } | sort)

if [ -z "$IN_SCOPE_LIST" ]; then
  echo "ERROR: no tracked .v files under pgg-smc/instances" >&2
  exit 2
fi

IN_SCOPE_LIST="$IN_SCOPE_LIST" UNTRACKED_LIST="$UNTRACKED_LIST" \
OUT_OF_SCOPE_LIST="$OUT_OF_SCOPE_LIST" python3 <<'PY'
import os, pathlib, re, sys

def env_list(name):
    return [f for f in os.environ.get(name, '').splitlines() if f]

files = env_list('IN_SCOPE_LIST')
untracked = env_list('UNTRACKED_LIST')
out_of_scope = env_list('OUT_OF_SCOPE_LIST')

# The file that declares the record itself may name MonodromyProfile freely.
RECORD_FILE = 'pgg-smc/protocol/pgg_monodromy_profile.v'

# profile name -> (documented body, facade file, facade module)
# A documented body of None means the profile is expected to be built from the
# constructor rather than to be an alias of another expected profile.
EXPECTED = {
  'pgl27_profile':     (None, 'pgg-smc/instances/pgl27/pgl27_analysis.v',
                        'PGL27Analysis'),
  'five_card_profile': (None, 'pgg-smc/instances/kim2025/five_card_analysis.v',
                        'FiveCardAnalysis'),
  'den_boer_profile':  ('five_card_profile',
                        'pgg-smc/instances/kim2025/five_card_analysis.v',
                        'FiveCardAnalysis'),
  's5_profile':        (None, 'pgg-smc/instances/s5/s5_analysis.v',
                        'S5Analysis'),
  's5x5_profile':      (None, 'pgg-smc/instances/s5x5/s5x5_analysis.v',
                        'S5x5Analysis'),
  'abel_profile':      (None, 'pgg-smc/instances/abelian/abelian_analysis.v',
                        'AbelianAnalysis'),
}
FACADES = {facade for _, facade, _ in EXPECTED.values()}

def strip_comments(src):
    """Blank out (* ... *) the way the Rocq lexer reads it: comments nest, a
    string literal inside a comment does not terminate it, and a "(*" inside a
    string literal at code level does not open one. Newlines are preserved so
    that line numbers and line-anchored patterns still hold."""
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if depth == 0:
            if src.startswith('(*', i):
                depth, i = 1, i + 2
                out.append('  ')
            elif src[i] == '"':
                j = i + 1
                while j < n:
                    if src[j] == '"':
                        if j + 1 < n and src[j + 1] == '"':
                            j += 2
                            continue
                        j += 1
                        break
                    j += 1
                out.append(src[i:j])
                i = j
            else:
                out.append(src[i])
                i += 1
        else:
            if src.startswith('(*', i):
                depth, i = depth + 1, i + 2
                out.append('  ')
            elif src.startswith('*)', i):
                depth, i = depth - 1, i + 2
                out.append('  ')
            elif src[i] == '"':
                j = i + 1
                while j < n and src[j] != '"':
                    j += 1
                out.append(' ' * (min(j + 1, n) - i))
                i = j + 1
            else:
                out.append('\n' if src[i] == '\n' else ' ')
                i += 1
    return ''.join(out)

# A binder run may contain parenthesised and braced binders and qualified
# names, but never a command-terminating dot, so a declaration cannot steal a
# type from the next command.
BINDER = r'(?:[^:=(){}.]|\.(?!\s|$)|\([^()]*\)|\{[^{}]*\})*'
ATTR = r'(?:\#\[\s*(?P<attr>[^\]]*)\]\s*)?'
HEAD = (r'^' + ATTR + r'(?P<local>Local\s+|Global\s+)?(?:Program\s+)?'
        r'(?P<kind>Definition|Let)\s+(?P<name>\w+)')
TYPED = re.compile(HEAD + BINDER + r':\s*MonodromyProfile\s*:=\s*(?P<body>@?[\w.]*)',
                   re.M)
ALIAS = re.compile(HEAD + r'\s*:=\s*\(?\s*(?P<body>[\w.]+)'
                   r'(?:\s*:\s*MonodromyProfile\s*)?\)?\s*\.', re.M)
OPENER = re.compile(r'^(?:Module|Section)\s+\w+(?![^\n]*:=)', re.M)
CLOSER = re.compile(r'^End\s+\w+', re.M)

def depth_map(src):
    """line number (1-based) -> nesting depth of Modules and Sections."""
    depths, depth = {}, 0
    for i, line in enumerate(src.splitlines(), 1):
        if CLOSER.match(line):
            depth -= 1
        depths[i] = depth
        if OPENER.match(line):
            depth += 1
    return depths

def read(path):
    try:
        return strip_comments(pathlib.Path(path).read_text())
    except OSError as e:
        print('ERROR: cannot read %s: %s' % (path, e), file=sys.stderr)
        sys.exit(2)

def declarations(src):
    """(name, kind, local, body, line) for every profile declaration."""
    hits = {}
    for rx, typed in ((TYPED, True), (ALIAS, False)):
        for m in rx.finditer(src):
            name, body = m.group('name'), (m.group('body') or '')
            body = body.lstrip('@').rstrip('.').split('.')[-1]
            if not typed and body not in EXPECTED:
                continue
            if name in hits and not typed:
                continue
            local = bool(m.group('local') and m.group('local').strip() == 'Local')
            local = local or bool(m.group('attr') and 'local' in m.group('attr'))
            hits[name] = (m.group('kind'), local, body,
                          src[:m.start()].count('\n') + 1)
    return hits

found = {}        # name -> (file, body)
duplicates = []   # (name, file)
nested = []       # (file, name, line)
skipped = []      # (file, name, reason)

for f in files:
    src = read(f)
    depths = depth_map(src)
    for name, (kind, local, body, line) in sorted(declarations(src).items()):
        if kind == 'Let':
            skipped.append((f, name, 'section-local Let'))
        elif local:
            skipped.append((f, name, 'Local declaration'))
        elif f in FACADES and body in EXPECTED:
            skipped.append((f, name, 'facade alias of ' + body))
        elif depths.get(line, 0) > 0:
            nested.append((f, name, line))
        elif name in found:
            duplicates.append((name, f))
        else:
            found[name] = (f, body)

unknown = sorted(set(found) - set(EXPECTED))
missing = sorted(set(EXPECTED) - set(found))

print('profile declarations found (%d):' % len(found))
for name in sorted(found):
    f, body = found[name]
    doc = EXPECTED.get(name, ('UNKNOWN',))[0] if name in EXPECTED else None
    kind = ('alias of ' + doc) if doc else (
        'UNKNOWN' if name not in EXPECTED else 'represented')
    print('  %-18s %-52s %s' % (name, f, kind))

if skipped:
    print()
    print('skipped (%d):' % len(skipped))
    for f, name, why in sorted(skipped):
        print('  %-18s %-52s %s' % (name, f, why))

unrepresented = []
print()
print('facade evidence:')
for name in sorted(EXPECTED):
    doc, facade, module = EXPECTED[name]
    if name in missing:
        unrepresented.append((name, 'no declaration found'))
        print('  %-18s %-52s MISSING DECLARATION' % (name, facade))
        continue
    body = found[name][1]
    if doc is None and body in EXPECTED and body != name:
        unrepresented.append((name, 'undocumented alias of %s' % body))
        print('  %-18s %-52s UNDOCUMENTED ALIAS' % (name, facade))
        continue
    if doc is not None and body != doc:
        unrepresented.append((name, 'body is %s, documented as %s' % (body, doc)))
        print('  %-18s %-52s WRONG BODY' % (name, facade))
        continue
    if facade not in files:
        unrepresented.append((name, 'facade %s is not a tracked file' % facade))
        print('  %-18s %-52s FACADE NOT TRACKED' % (name, facade))
        continue
    fsrc = read(facade)
    body_rx = re.compile(r'^Definition\s+(?P<alias>\w+)\s*:=\s*(?:[\w.]+\.)?%s\b'
                         % re.escape(name), re.M)
    span = re.search(r'^Module\s+%s\s*\.(?P<body>.*?)^End\s+%s\s*\.'
                     % (re.escape(module), re.escape(module)),
                     fsrc, re.M | re.S)
    alias = body_rx.search(span.group('body')) if span else None
    if alias:
        print('  %-18s %-52s %s.%s'
              % (name, facade, module, alias.group('alias')))
    elif span is None:
        unrepresented.append((name, 'facade %s has no Module %s'
                              % (facade, module)))
        print('  %-18s %-52s NO MODULE %s' % (name, facade, module))
    else:
        unrepresented.append((name, 'Module %s has no alias of %s'
                              % (module, name)))
        print('  %-18s %-52s NO ALIAS' % (name, facade))

# Universe guards: a profile declared in an untracked instance file, or in a
# tracked pgg-smc file outside instances, is outside the classification above.
stray = []
for f in untracked:
    if declarations(read(f)):
        stray.append((f, 'untracked file declares a profile'))
for f in out_of_scope:
    if f == RECORD_FILE:
        continue
    if any(TYPED.finditer(read(f))):
        stray.append((f, 'profile declared outside pgg-smc/instances'))

status = 0
if unknown or duplicates or nested or stray:
    print()
    for name in unknown:
        print('UNKNOWN: %s declared in %s is not in the expected list'
              % (name, found[name][0]), file=sys.stderr)
    for name, f in duplicates:
        print('DUPLICATE: %s is declared again in %s' % (name, f), file=sys.stderr)
    for f, name, line in nested:
        print('NESTED: %s at %s:%d is inside a Module or Section'
              % (name, f, line), file=sys.stderr)
    for f, why in stray:
        print('STRAY: %s: %s' % (f, why), file=sys.stderr)
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
