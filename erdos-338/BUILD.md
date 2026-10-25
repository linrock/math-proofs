# Building and Verifying `erdos-338`

## Toolchain

- Lean: `leanprover/lean4:v4.35.0-rc2`
- Mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`

## Build and Audit Commands

```bash
lake exe cache get
lake build Challenge Solution AxiomAudit
./verify.sh
```

`./verify.sh` builds the package, replays the axiom audit, and checks that every exported theorem
depends only on `propext`, `Classical.choice`, and `Quot.sound`. It also checks that
`formalization.yaml` records a source with a `formalizes`, `adapts`, or `independently-proves`
relationship.

To run Comparator locally:

```bash
lake env lake comparator --config comparator.json
```
