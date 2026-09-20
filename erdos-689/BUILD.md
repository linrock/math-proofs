# Build and verification for Erdős 689

The exact toolchain is `leanprover/lean4:v4.33.1`. Mathlib is pinned to
`0df444a360eaa60ab8c11dca51a86af692955474` together with its complete
dependency manifest.

From the `erdos-689/` directory, fetch the pinned dependencies and build the
Challenge, Solution, and endpoint axiom audit:

```sh
lake exe cache get
lake build Challenge Solution AxiomAudit
lake env lean AxiomAudit.lean
```

`lake exe cache get` fetches cached dependency builds. Compiling the project
may require substantial time and memory.

`Challenge.lean` contains the intentionally unproved problem statement.
`Solution.lean` does not import it. `AxiomAudit.lean` prints the transitive
axioms of `Erdos689.Palomar.eventual_double_cover`. The expected output is:

```text
'Erdos689.Palomar.eventual_double_cover' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

The final command prints the audit even when Lake reuses an existing build.
Warnings about `sorry` in `Challenge.lean` and two unused lemmas in
`Proofs/PrimeNumberTheoremAnd/Wiener.lean` are expected. The completed proof
does not depend on those placeholders. Its axiom output must not contain
`sorryAx`.

## Verification status

The project built successfully from source using pinned dependency caches,
and its endpoint axiom audit passed. Comparator confirmed the Challenge/Solution
statement correspondence and permitted axioms. Both Lean and NanoDa accepted the
exported proof. That check reused existing project build outputs.

The local checks used Lean 4.33.1 compatibility adaptations to Comparator and
lean4export, with unmodified NanoDa, and ran without Linux isolation.
Palomar's hosted verification and editorial review remain pending.
