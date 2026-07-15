#!/usr/bin/env bash
# Generate dependency graph (DOT → SVG) for the pgg-smc directory.
#
# Usage:
#   ./scripts/gen_depgraph.sh              # full graph (all objects)
#   ./scripts/gen_depgraph.sh --no-defs    # only Prop objects (Axiom/Theorem/Lemma)
#   ./scripts/gen_depgraph.sh --module reconstruct   # only pgg_reconstruct
#   ./scripts/gen_depgraph.sh --module all            # all pgg-smc modules (default)
#
# Prerequisites: coq-dpdgraph (opam install coq-dpdgraph), graphviz (brew install graphviz)
# Output: scripts/depgraph.svg (and intermediate .dpd / .dot files)

set -euo pipefail
cd "$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"

# --- Parse arguments ---
DPD2DOT_FLAGS="-rm-trans"
MODULE_SCOPE="all"
while [[ $# -gt 0 ]]; do
  case "$1" in
    --no-defs)    DPD2DOT_FLAGS="$DPD2DOT_FLAGS -without-defs"; shift ;;
    --with-defs)  shift ;;  # default
    --module)     MODULE_SCOPE="$2"; shift 2 ;;
    *)            echo "Unknown option: $1"; exit 1 ;;
  esac
done

# --- Check tools ---
for cmd in dpd2dot dot rocq; do
  if ! command -v "$cmd" &>/dev/null; then
    echo "Error: '$cmd' not found. Install with:"
    [[ "$cmd" == "dpd2dot" ]] && echo "  opam install coq-dpdgraph"
    [[ "$cmd" == "dot" ]]     && echo "  brew install graphviz"
    [[ "$cmd" == "rocq" ]]    && echo "  opam install rocq"
    exit 1
  fi
done

OUTDIR="scripts"
DPD_FILE="$PWD/$OUTDIR/depgraph.dpd"
DOT_FILE="$OUTDIR/depgraph.dot"
SVG_FILE="$OUTDIR/depgraph.svg"

# --- Build per-file module list from _CoqProject ---
# Each .v file becomes a Require and a FileDependGraph entry.
# dpdgraph needs individual file modules, not directory prefixes.
build_module_list() {
  local dir_pattern="$1"
  grep -E "^${dir_pattern}" _CoqProject | while read -r vfile; do
    # e.g. pgg-smc/reconstruct/cover_tradeoff.v → pgg_reconstruct.cover_tradeoff
    local base
    base=$(basename "$vfile" .v)
    case "$vfile" in
      pgg-smc/reconstruct/*) echo "pgg_reconstruct.$base" ;;
      pgg-smc/lib/*)         echo "pgg_smc.$base" ;;
      pgg-smc/protocol/*)    echo "pgg_smc.$base" ;;
      pgg-smc/groups/*)      echo "pgg_smc.$base" ;;
      pgg-smc/security/*)    echo "pgg_smc.$base" ;;
    esac
  done
}

case "$MODULE_SCOPE" in
  reconstruct) MODULES=$(build_module_list "pgg-smc/reconstruct/") ;;
  protocol)    MODULES=$(build_module_list "pgg-smc/protocol/") ;;
  groups)      MODULES=$(build_module_list "pgg-smc/groups/") ;;
  security)    MODULES=$(build_module_list "pgg-smc/security/") ;;
  all)         MODULES=$(build_module_list "pgg-smc/") ;;
  *)           echo "Unknown module scope: $MODULE_SCOPE"; exit 1 ;;
esac

# --- Build Require lines (no Import/Export per dpdgraph docs) ---
REQUIRE_LINES=""
for mod in $MODULES; do
  REQUIRE_LINES="${REQUIRE_LINES}Require ${mod}.
"
done

# Module list as space-separated for Print FileDependGraph
MODULES_INLINE=$(echo "$MODULES" | tr '\n' ' ')

# --- Generate .v file that extracts dependencies ---
# Place in project root so -R flags resolve correctly
EXTRACT_V="$PWD/_depgraph_extract.v"
trap "rm -f '$EXTRACT_V'" EXIT

cat > "$EXTRACT_V" <<COQEOF
Require dpdgraph.dpdgraph.
${REQUIRE_LINES}
Set DependGraph File "${DPD_FILE}".
Print FileDependGraph ${MODULES_INLINE}.
COQEOF

echo "==> Extracting dependencies..."
echo "    Scope: $MODULE_SCOPE ($(echo "$MODULES" | wc -l | tr -d ' ') files)"
echo "    Output: $SVG_FILE"

# Compile the extraction script
rocq compile -R . infotheo \
  -R pgg-smc/lib pgg_smc \
  -R pgg-smc/protocol pgg_smc \
  -R pgg-smc/groups pgg_smc \
  -R pgg-smc/security pgg_smc \
  -R pgg-smc/reconstruct pgg_reconstruct \
  "$EXTRACT_V"

if [[ ! -f "$DPD_FILE" ]]; then
  echo "Error: $DPD_FILE was not generated"
  exit 1
fi

# --- Convert .dpd → .dot ---
echo "==> Converting .dpd → .dot"
dpd2dot $DPD2DOT_FLAGS -graphname depgraph -o "$DOT_FILE" "$DPD_FILE"

# --- Render .dot → .svg ---
echo "==> Rendering .dot → .svg"
dot -Tsvg "$DOT_FILE" -o "$SVG_FILE"

NENTRIES=$(wc -l < "$DPD_FILE" | tr -d ' ')
echo "==> Done: $SVG_FILE ($NENTRIES dependency entries)"
echo "    open $SVG_FILE"
