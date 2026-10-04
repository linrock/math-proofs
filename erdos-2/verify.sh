#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
if [[ $# -gt 1 ]] || [[ $# -eq 1 && "$1" != "--no-sandbox" ]]; then
  echo "Usage: ./verify.sh [--no-sandbox]" >&2
  exit 2
fi

mkdir -p .verification
for lean_file in *.lean Proofs/*.lean Proofs/Architect/*.lean Proofs/PrimeNumberTheoremAnd/*.lean Proofs/PrimeNumberTheoremAnd/IEANTN/*.lean; do
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
done
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

# Build in import order, with one project compiler active at a time.
# Provision Mathlib's official build cache with `lake exe cache get` first.
proof_modules=(
  Architect.Basic Architect.Command Architect.CollectUsed Architect.Content
  Architect.Attribute Architect.Tactic Architect.Output Architect.Load Architect
  PrimeNumberTheoremAnd.EulerMaclaurin PrimeNumberTheoremAnd.IEANTN.Mertens
  FiberUpdate2 ProductUpdate2 FiniteWeight2 SieveStep2 ProgressionArithmetic2
  CoveringModel2 CongruenceGeometry2 ProgressionUpdate2 FractionRectangle2
  MomentBound2 RectangleMoment2 RectangleCoefficient2 NaturalDivisorModel2
  EulerMoment2 AnalyticTail2 DivisorEulerBound2 LateMoment2 SieveStage2
  UniformResidue2 FiniteLcm2 SieveBase2 StripPrime2 MertensUpper2 SmoothTail2
  TailChoice2 SieveRecursion2 ResidueLift2 FiniteIndexAdapter2 CoveringSystem2
  StatementAdapter2 NoncoverageCapstone2 Statement Challenge Solution AxiomAudit
)
for proof_module in "${proof_modules[@]}"; do
  echo "Building $proof_module"
  if ! lake build "+$proof_module" > ".verification/$proof_module.log" 2>&1; then
    cat ".verification/$proof_module.log" >&2
    exit 1
  fi
done

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
  END { if (reports != 6 || bad) exit 1 }
' .verification/axioms.log
awk '/depends on axioms:/ { print }' .verification/axioms.log
echo "PASS: package build and saved-source axiom audit"

if [[ "${1:-}" == "--no-sandbox" ]]; then
  lake env lake comparator --config comparator.json --inadvisably-no-sandbox \
    2>&1 | tee .verification/comparator.log
fi
