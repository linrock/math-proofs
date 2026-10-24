# Building and Verifying `erdos-1122`

## Toolchain

- Lean: `leanprover/lean4:v4.35.0-rc2`
- Mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`

## Build and Audit Commands

```bash
lake build Challenge Solution AxiomAudit Statement
./verify.sh
```

`./verify.sh` builds the package, replays the axiom audit, and, when `jq` is available, checks
that `formalization.yaml` records a source with a `formalizes`, `adapts`, or
`independently-proves` relationship. It does not run Comparator; the Comparator checks are
reported separately.

To run Comparator under its built-in `bwrap` sandbox, which is the trustworthy mode:

```bash
lake env lake comparator --config comparator.json
```

The sandbox needs a host that permits unprivileged mount namespaces. On a host that forbids them,
Comparator reports `bwrap: Can't mount proc` and stops. `./verify.sh --no-sandbox` passes
`--inadvisably-no-sandbox` for local diagnosis; its output is not a trustworthy Comparator result
and should not be treated as verification evidence.
