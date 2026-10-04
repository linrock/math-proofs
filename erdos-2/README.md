# Erdős #2: the minimum modulus of a distinct covering system is bounded

This package targets Lean 4.35.0-rc2 and formalizes the negative answer to Erdős
problem #2: the smallest modulus of a finite covering system with distinct
positive moduli cannot be arbitrarily large. One absolute natural bound works
for every such system and every choice of signed integer residues. No explicit
numerical bound is extracted.

This is a formalization of known mathematics. [Hough](https://annals.math.princeton.edu/2015/181-1/p06)
proved the negative answer. The proof here follows the probability sieve of
[Balister, Bollobás, Morris, Sahasrabudhe and Tiba](https://arxiv.org/html/1811.03547),
using a fixed half-cap update and qualitative summable tails. It does not claim
a new mathematical solution or discovery priority.

## Statements and proof entrypoints

[Solution.lean](Solution.lean) exposes three unconditional results:

| Declaration in `Erdos2.Standalone` | Meaning |
| --- | --- |
| `erdos_2` | The literal Formal Conjectures ideal statement, with answer `False`. |
| `minimum_modulus_bound` | Every finite indexed covering by distinct positive moduli has a modulus at most one uniform bound. |
| `finite_noncoverage_bound` | Any finite set of moduli all above one uniform bound leaves an integer uncovered, for every assigned residue function. |

The exact original endpoint is

```lean
False ↔
  ∀ B : ℕ, ∃ c : StrictCoveringSystem ℤ, ∀ i, ∃ m : ℕ,
    c.moduli i = Ideal.span {(m : ℤ)} ∧ B < m
```

The [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/2.lean)
uses `answer(False)`, which elaborates to the same proposition. Its utility
defines `StrictCoveringSystem`: a finite collection of cosets of distinct
nonzero proper ideals covering the whole ring. The unchanged attributed
definition source is included in [CoveringSystem2.lean](Proofs/CoveringSystem2.lean).

[Statement.lean](Statement.lean) records the exact target as the proposition
definition `Erdos2.Challenge.statement`. It imports the covering definition
source and its Mathlib dependencies, with no unproved theorem or intentional
placeholder. Solution states its theorem independently.
[AxiomAudit.lean](AxiomAudit.lean) proves statement fidelity, then checks the
public endpoint statements and their transitive axioms. Only `propext`,
`Classical.choice` and `Quot.sound` are accepted.

[Challenge.lean](Challenge.lean) is a separate Mathlib-only numerical benchmark.
It repeats the raw `Erdos2.Standalone.minimum_modulus_bound` signature from
Solution, with one intentional benchmark `sorry`.
[comparator.json](comparator.json) selects this numerical theorem and enables
NanoDa for local validation. Solution, Statement and AxiomAudit exclude
Challenge from their completed proof import graph.

## Proof and source boundary

The proof constructs a normalized weight on a finite residue space modulo a
positive common multiple. Small-prime moduli have uniformly small reciprocal
mass once their minimum is large. At each later prime, the capped fiber update
preserves the earlier mass and bounds the new loss by a second moment. The
moment factors into a finite Euler product, bounded by a sixth power of the
reciprocal prime product. The resulting tail, bounded by a constant times
`log(p)^6 / (p - 1)^2`, is summable. The final covered mass is less than one,
yielding an uncovered residue and then an uncovered signed integer.

The [Proofs](Proofs) directory contains 31 local modules from the
verified research proof, two narrow Mertens/Euler–Maclaurin provider modules,
and nine vendored Architect modules. Their module graph and source digests
were checked against the original frozen closure. The numerical and ideal
adapters preserve arbitrary finite index types, arbitrary prime powers,
distinctness, positivity and signed integer coverage. Modulus one and the
empty-family edge are retained by the numerical interface.

[source-manifest.json](source-manifest.json) records exact source provenance.
Its original research paths are provenance records rather than build
dependencies. [THIRD_PARTY.md](THIRD_PARTY.md) records the retained source
licences; the repository MIT licence does not replace upstream terms.

## Build and verification

The Lean 4.35.0-rc2 port passed fresh source builds for all 46 modules: 45
completed proof modules and interfaces, plus the separate benchmark. The
saved-source audit passed four transitive-axiom reports using only the three
foundations listed above; its setup binds 44 owned imports to the package's
built modules. It reuses canonical compiled Mathlib dependencies and builds
every vendored project module; it does not rebuild Mathlib from source.

The numerical Comparator check matched the independent statements, and both
NanoDa and Lean's default kernel accepted Solution. This was a local macOS
run with Comparator's sandbox explicitly disabled, not a Palomar server
acceptance. [VERIFICATION.json](VERIFICATION.json) records the checks and
[verification/comparator.log](verification/comparator.log) retains their output.
The canonical `./verify.sh` replay and normal Lake build passed. The finalized
release digests also pass their integrity check. See [BUILD.md](BUILD.md) for
the pinned commands.

The preceding Lean 4.33.1 package passed its source build and endpoint audit.
Its complete preserved release and the current compatibility work are recorded
in [PORTING.md](PORTING.md). [formalization.yaml](formalization.yaml)
records the source-based provenance and benchmark scope.
