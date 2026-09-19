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

`lake exe cache get` only downloads dependencies. `lake build` checks the
local sources and may require substantial time and memory.

`Challenge.lean` contains the intentionally unproved problem statement.
`Solution.lean` does not import it. `AxiomAudit.lean` prints the transitive
axioms of `Erdos689.Palomar.eventual_double_cover`. Inspect that output and
confirm it contains only `propext`, `Classical.choice`, and `Quot.sound`.
The final command prints the audit even when Lake reuses an existing build.

## Local verification record

On 2026-08-27, the commands above completed successfully in an existing local
checkout. The endpoint audit printed:

```text
'Erdos689.Palomar.eventual_double_cover' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

The build produced warnings from the intentionally unproved statement in
`Challenge.lean` and two admitted declarations in
`Proofs/PrimeNumberTheoremAnd/Wiener.lean`. The audited endpoint does not
transitively depend on those admitted declarations: `sorryAx` is absent from
the axiom output above.

This was an in-place local run, not a clean-clone reproduction, verification
of an immutable public commit, or an official Palomar Comparator/NanoDa
result. Repeat all checks on the exact public commit submitted to Palomar.

For Palomar, submit the exact public commit SHA with project directory
`erdos-689` and Comparator configuration `erdos-689/comparator.json`. See the
[submission instructions](https://palomar-registry.org/how-to-submit).
