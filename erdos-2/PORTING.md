# Lean 4.35.0-rc2 port

The current package targets `leanprover/lean4:v4.35.0-rc2`, compiler commit
`11acb17ec6b07a8f9e9173e6845197929540936b`, and canonical Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. This is a separately checked
successor to the completed Lean 4.33.1 package.

## Preserved baseline

The complete original release, including source files, pinned dependencies,
verification records, licenses, and its original `SHA256SUMS`, is retained in
`verification/lean4331-baseline.tar.gz`. The archive hash and old verification
receipt hash are in `verification/lean4331-baseline.json`. Original research
sources, historical canonical verifiers, and their evidence remain unchanged.
The old compiled project artifacts are retained in an ignored version-specific
local directory and are not used by the rc2 build.

## Scope and compatibility

The mathematical result remains the same qualitative negative answer to the
original minimum-modulus problem. The exact ideal statement is in the proved
`Solution.lean`. The separately defined target is retained in `Statement.lean`.
`Challenge.lean` is a Mathlib-only numerical benchmark for Palomar, with its
intentional statement placeholder outside the completed proof import graph.
No numerical cutoff is extracted.

Compatibility changes are confined to five product-bound helper names across
`EulerMoment2`, `AnalyticTail2` and `MertensUpper2`. Mathlib now gives its
zero-sensitive bounds the `₀` suffix. The existing nonnegativity and comparison
hypotheses are retained, and no theorem statement or import changes.
`source-manifest.json` records both baseline and current digests. All eleven
provider modules and the covering-system utility remain byte for byte unchanged.

## Reuse checkpoint

Inspected the indexed exact original capstone, numerical adapter, and frozen
31-module source closure. The first falsifying control, unchanged
`CoveringSystem2`, compiled under the rc2 package. Loogle's pinned lean435
`quick_batch` used ordinary `all` order for `Finset.sum_ite`,
`Finset.card_univ_sdiff`, and `Finset.lcm_ne_zero_iff`. The cardinality and lcm
queries returned their exact established Mathlib declarations; the sum query
was capped and was not treated as exhaustive. Existing saved applications are
compiled directly in the new context before considering replacement helpers.
The first sieve modules and all 11 providers compile without source edits;
no new mathematical lemma or import has been needed for those modules.

The rc2 Loogle lookup for `Finset.prod_le_prod₀` identified its exact defining
module `Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset`. Its existing
two hypotheses close the Euler moment application in Lean-Beam. The subset
lookup similarly identified `Finset.prod_le_prod_of_subset_of_one_le₀`, retaining
the original nonnegativity domain and subset comparison. These are API
compatibility edits rather than additional mathematical assumptions.

## rc2 checks

All 42 vendored modules, three completed proof interfaces, and the separate
benchmark were freshly compiled with the pinned rc2 compiler. The four saved-source
endpoint/fidelity reports use only `propext`, `Classical.choice` and `Quot.sound`.
The final audit binds all 44 project imports to package-owned rc2 artifacts and
excludes Challenge. Comparator found the independently stated numerical
signatures equal, and NanoDa and the default Lean kernel both accepted the
solution. The local macOS Comparator run used `--inadvisably-no-sandbox`;
it is not a Palomar registry submission or review. Exact evidence and the final
canonical replay are recorded in `VERIFICATION.json` and `verification/`.
