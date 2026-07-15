#!/usr/bin/env bash
# Generate browsable HTML documentation for pgg-smc/ using rocqnavi.
#
# Produces cross-referenced HTML with proof folding, type tooltips,
# and an embedded file dependency graph.
#
# Usage:
#   ./scripts/gen_rocqnavi.sh              # generate docs for pgg-smc/
#   ./scripts/gen_rocqnavi.sh --all        # generate docs for entire project
#   ./scripts/gen_rocqnavi.sh --open       # generate and open in browser
#
# Prerequisites:
#   opam install rocq-navi      # browsable HTML doc generator
#   brew install graphviz        # for dependency graph rendering
#
# Output: scripts/html/index.html

set -euo pipefail
cd "$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"

# --- Parse arguments ---
SCOPE="pgg-smc"
OPEN_BROWSER=false
while [[ $# -gt 0 ]]; do
  case "$1" in
    --all)   SCOPE="all"; shift ;;
    --open)  OPEN_BROWSER=true; shift ;;
    *)       echo "Unknown option: $1"; exit 1 ;;
  esac
done

# --- Check tools ---
for cmd in rocqnavi dot; do
  if ! command -v "$cmd" &>/dev/null; then
    echo "Error: '$cmd' not found. Install with:"
    [[ "$cmd" == "rocqnavi" ]] && echo "  opam install rocq-navi"
    [[ "$cmd" == "dot" ]]      && echo "  brew install graphviz"
    exit 1
  fi
done

OUTDIR="scripts/html"
mkdir -p "$OUTDIR"

# --- Step 1: Generate file dependency graph (.d → .dot) ---
echo "==> Generating file dependency graph..."

# Regenerate .Makefile.d to ensure it's current
rocq dep -f _CoqProject 2>/dev/null > .Makefile.d

# Filter .Makefile.d to only pgg-smc files and convert to DOT format
DEP_DOT="$OUTDIR/file_dep.dot"
{
  echo "digraph file_dependencies {"
  echo '  rankdir=BT;'
  echo '  node [shape=box, style=filled, fillcolor="#E8E8E8", fontsize=10];'

  # Color nodes by subdirectory
  echo '  subgraph cluster_legend {'
  echo '    label="Legend"; style=dashed;'
  echo '    _lib [label="lib", fillcolor="#B3E5FC"];'
  echo '    _protocol [label="protocol", fillcolor="#C8E6C9"];'
  echo '    _groups [label="groups", fillcolor="#FFE0B2"];'
  echo '    _security [label="security", fillcolor="#FFCDD2"];'
  echo '    _reconstruct [label="reconstruct", fillcolor="#D1C4E9"];'
  echo '  }'

  # Parse .Makefile.d: extract .vo dependencies between pgg-smc files
  grep -E '^pgg-smc/.*\.vo ' .Makefile.d | grep -v '\.vos' | while IFS= read -r line; do
    # Target: everything before the first ':'
    target=$(echo "$line" | cut -d: -f1 | awk '{print $1}' | sed 's/\.vo$//')
    # Dependencies: .vo files after ':'
    deps=$(echo "$line" | cut -d: -f2- | tr ' ' '\n' | { grep '\.vo$' || true; } | sed 's/\.vo$//')

    target_base=$(basename "$target")

    # Determine color by subdirectory
    case "$target" in
      pgg-smc/lib/*)         color="#B3E5FC" ;;
      pgg-smc/protocol/*)    color="#C8E6C9" ;;
      pgg-smc/groups/*)      color="#FFE0B2" ;;
      pgg-smc/security/*)    color="#FFCDD2" ;;
      pgg-smc/reconstruct/*) color="#D1C4E9" ;;
      *)                     color="#E8E8E8" ;;
    esac

    # Node declaration
    node_id=$(echo "$target" | tr '/-' '__')
    echo "  ${node_id} [label=\"${target_base}\", fillcolor=\"${color}\"];"

    # Edges (only to other pgg-smc files)
    for dep in $deps; do
      case "$dep" in
        pgg-smc/*)
          dep_id=$(echo "$dep" | tr '/-' '__')
          echo "  ${node_id} -> ${dep_id};"
          ;;
      esac
    done
  done

  echo "}"
} > "$DEP_DOT"

echo "    Generated $DEP_DOT ($(grep -c '^  pgg' "$DEP_DOT" 2>/dev/null || echo 0) nodes)"

# --- Step 2: Collect .glob and .v files ---
echo "==> Collecting source files..."

case "$SCOPE" in
  pgg-smc)
    FILE_PATTERN="pgg-smc/"
    TITLE="PGG-SMC Documentation"
    ;;
  all)
    FILE_PATTERN=""
    TITLE="Infotheo Documentation"
    ;;
esac

# Build file list: .glob and .v files
FILELIST=$(find pgg-smc/ -not -path '*/.*' \( -name "*.v" -o -name "*.glob" \) 2>/dev/null | sort)
if [[ "$SCOPE" == "all" ]]; then
  FILELIST=$(find . -not -path '*/.*' -not -path './scripts/*' \( -name "*.v" -o -name "*.glob" \) 2>/dev/null | sort)
fi

NFILES=$(echo "$FILELIST" | grep -c '\.v$' || true)
echo "    Found $NFILES .v files"

# --- Step 3: Run rocqnavi ---
echo "==> Running rocqnavi..."

# shellcheck disable=SC2086
echo "$FILELIST" | xargs rocqnavi \
  -title "$TITLE" \
  -d "$OUTDIR" \
  -Q pgg-smc/lib pgg_smc \
  -Q pgg-smc/protocol pgg_smc \
  -Q pgg-smc/groups pgg_smc \
  -Q pgg-smc/security pgg_smc \
  -Q pgg-smc/reconstruct pgg_reconstruct \
  -file-graph "$DEP_DOT" \
  -short-names

echo "==> Done: $OUTDIR/index.html"
echo "    open $OUTDIR/index.html"

if $OPEN_BROWSER; then
  open "$OUTDIR/index.html"
fi
