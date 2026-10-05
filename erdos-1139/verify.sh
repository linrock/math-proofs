#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"

if [[ $# -gt 1 ]] || [[ $# -eq 1 && "$1" != "--no-sandbox" ]]; then
  echo "Usage: ./verify.sh [--no-sandbox]" >&2
  exit 2
fi

mkdir -p .verification
while IFS= read -r -d '' lean_file; do
  first_line="$(head -n 1 "$lean_file")"
  if [[ "$first_line" != "module" ]]; then
    echo "FAIL: $lean_file must begin with the module header keyword" >&2
    exit 1
  fi
  line_count="$(wc -l < "$lean_file")"
  if (( line_count > 10000 )); then
    echo "FAIL: $lean_file exceeds 10,000 lines ($line_count)" >&2
    exit 1
  fi
done < <(find *.lean Proofs -type f -name '*.lean' -print0)
if command -v jq >/dev/null 2>&1; then
  jq -e 'any(.sources[]; .relationship == "formalizes" or .relationship == "adapts" or .relationship == "independently-proves")' formalization.yaml >/dev/null || {
    echo "FAIL: formalization.yaml sources need a formalizes, adapts, or independently-proves relationship" >&2
    exit 1
  }
fi
echo "PASS: Palomar preliminary module-header, line-count, and sources checks"

compiler_version="$(lake env lean --version)"
printf '%s\n' "$compiler_version" | tee .verification/toolchain.log
case "$compiler_version" in
  *"version 4.35.0-rc2,"*) ;;
  *) echo "Expected the pinned Lean 4.35.0-rc2 compiler" >&2; exit 1 ;;
esac
mathlib_revision="$(git -C .lake/packages/mathlib rev-parse HEAD)"
if [[ "$mathlib_revision" != "065356127b1dc0016f66b7283ce0ce2c4055aa55" ]]; then
  echo "Mathlib revision does not match the pinned proof" >&2
  exit 1
fi

echo "Building Statement, Solution, AxiomAudit, and Challenge..."
if ! lake build Statement Solution AxiomAudit Challenge > .verification/build.log 2>&1; then
  cat .verification/build.log >&2
  exit 1
fi

lake env lean -j1 -M8192 -E hasSorry -Dformat.width=1000000 \
  --setup=.lake/build/ir/AxiomAudit.setup.json AxiomAudit.lean \
  > .verification/axioms.log 2>&1
awk '
  /depends on axioms:/ {
    reports++
    sub(/^.*depends on axioms: /, "")
    gsub(/[[:space:]\[\]]/, "")
    n = split($0, axioms, ",")
    for (i = 1; i <= n; i++)
      if (axioms[i] != "propext" && axioms[i] != "Classical.choice" &&
          axioms[i] != "Quot.sound") bad = 1
  }
  END { if (reports != 10 || bad) exit 1 }
' .verification/axioms.log
awk '/depends on axioms:/ { print }' .verification/axioms.log
echo "PASS: package build and saved-source axiom audit"

if [[ "${1:-}" == "--no-sandbox" ]]; then
  lake env lake comparator --config comparator.json --inadvisably-no-sandbox \
    2>&1 | tee .verification/comparator.log
fi
