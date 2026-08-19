#!/usr/bin/env bash
# Build both papers and fail loudly on any LaTeX error.
#
# Why this exists: Session 313 wrote an undefined macro (\genProd) into
# tools/dead_ends.tsv, which gen_dead_ends.py propagated into
# paper/dead_ends_table.tex.  paper/main.tex stopped compiling and nobody
# noticed for a whole session, because the verification loop ran
# check_lean_refs.py (which checks references, not compilation).
# Run this whenever paper/ or tools/dead_ends.tsv changes.
#
# Usage:  bash tools/check_paper_builds.sh
# Exit:   0 = both papers built; 1 = at least one failed.

set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
status=0

build_one () {
  local dir="$1" label="$2"
  echo "=== $label ($dir) ==="
  ( cd "$ROOT/$dir" || exit 1
    # Two passes: the first resolves labels, the second the cross-references.
    lualatex -interaction=nonstopmode -halt-on-error main.tex >/dev/null 2>&1
    if ! lualatex -interaction=nonstopmode -halt-on-error main.tex >/dev/null 2>&1; then
      echo "  BUILD FAILED — first errors:"
      grep -A3 -m3 "^!" main.log | sed 's/^/    /'
      exit 1
    fi
    pages=$(grep -oE "Output written on main\.pdf \([0-9]+ pages" main.log | grep -oE "[0-9]+" | head -1)
    echo "  ok — ${pages:-?} pages"
    # Undefined references/citations are not fatal to lualatex but are defects.
    if grep -q "LaTeX Warning: Reference .* undefined\|LaTeX Warning: Citation .* undefined" main.log; then
      echo "  WARNING: undefined references or citations:"
      grep -oE "LaTeX Warning: (Reference|Citation) [^ ]+ undefined" main.log | sort -u | sed 's/^/    /' | head -10
      exit 2
    fi
  )
  local rc=$?
  [ $rc -ne 0 ] && status=1
  return 0
}

build_one "paper"       "long paper"
build_one "paper/short" "short paper"

if [ $status -eq 0 ]; then echo "Both papers build cleanly."; else echo "PAPER BUILD CHECK FAILED."; fi
exit $status
