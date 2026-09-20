# Build and audit Erdős #973

This Lake project pins `leanprover/lean4:v4.33.1` and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474` in `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json`. Do not run `lake update` for this
submission candidate.

In this directory, after provisioning the pinned toolchain and dependencies,
run:

```sh
lake exe cache get
lake build Challenge Solution AxiomAudit
lake env lean AxiomAudit.lean
```

The Mathlib cache is a dependency build aid. The Lake build compiles all 11
`Proofs/` modules and the three endpoint modules. `Solution` and `Proofs`
are compiled with `-E hasSorry`. Challenge alone contains the intentional
statement placeholders. `AxiomAudit.lean` prints the transitive axioms of
both selected Solution theorems. The expected axioms are only `propext`,
`Classical.choice`, and `Quot.sound`.

The 11 proof modules are byte-for-byte copies of the canonical research
sources listed and SHA-256 pinned in `source-manifest.json`. Their original
research checkout is not required to build this project. No `.lake` outputs
or machine-local dependency paths are committed. The official Palomar
Comparator/NanoDa check and registry decision are separate from these local
Lean commands.
See [Palomar's contributor guide](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
for its separate submission and verification requirements.
