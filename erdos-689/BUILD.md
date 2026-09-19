# Build and verification for Erdős 689

This selected Lake project contains 175 source modules in `Proofs/`.
`source-manifest.json` records their origin and exact source hashes. Some
origin paths refer to the original research checkout and are historical
provenance labels, not files in this repository. No compiled proof objects or
machine-local dependency paths are included.

The exact toolchain is `leanprover/lean4:v4.33.1`. Mathlib is pinned to
`0df444a360eaa60ab8c11dca51a86af692955474` together with its complete dependency manifest.
Keep these pins when reproducing the build.

From the `erdos-689/` directory, fetch the pinned dependencies and build the
Challenge, Solution, and endpoint axiom audit:

```sh
lake exe cache get
lake build Challenge Solution AxiomAudit
lake env lean AxiomAudit.lean
```

The dependency cache speeds up compilation. It does not verify the local
proof. The first source build can take substantial memory and time,
especially for `Proofs/GoldbachChainMaster.lean`. Do not copy the research
machine's `.olean` files into this project as a substitute for a source build.

`Challenge.lean` contains the intentionally unproved problem statement.
`Solution.lean` does not import it. `AxiomAudit.lean` prints the transitive
axioms of `Erdos689.Palomar.eventual_double_cover`. Inspect that output and
confirm it contains only `propext`, `Classical.choice`, and `Quot.sound`.
The final command prints the audit even when Lake reuses an existing build.

Palomar's official Comparator and NanoDa checks use the selected declaration
and [comparator.json](comparator.json). A local Lake build and axiom printout
do not constitute an official Palomar result.

For the current repository layout, submit the full public commit SHA with
project directory `erdos-689` and Comparator configuration
`erdos-689/comparator.json`. The metadata defaults to
`erdos-689/formalization.yaml`. The license stays at the repository root.
See [Palomar's submission instructions](https://palomar-registry.org/how-to-submit).

The [repository-root MIT license](../LICENSE) matches `project.license: MIT`
in [formalization.yaml](formalization.yaml). Before submission, confirm the
listed authors and responsible maintainer, then repeat the checks on the exact
public commit submitted to Palomar.
