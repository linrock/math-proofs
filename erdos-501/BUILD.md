# Building and Verifying `erdos-501`

## Toolchain

- Lean: `leanprover/lean4:v4.35.0-rc2`
- Mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`

## Build and Audit Commands

```bash
lake exe cache get
lake build Challenge Solution AxiomAudit
./verify.sh
```

`./verify.sh` builds the package, replays the axiom audit for the three exported theorems, and,
when `jq` is available, checks that `formalization.yaml` records a source with a `formalizes`,
`adapts`, or `independently-proves` relationship. It does not run Comparator; the Comparator
checks are reported separately.

To run Comparator under its built-in sandbox:

```bash
lake env lake comparator --config comparator.json
```

This check requires a host that permits unprivileged mount namespaces. If the host does not
provide them, the sandboxed Comparator check cannot run there.
