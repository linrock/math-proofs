# Build and verification

This is a standalone Lean 4 package pinned to Lean 4.35.0-rc2 and Mathlib
revision `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Requirements

- Lean 4.35.0-rc2, as recorded in `lean-toolchain`.
- Lake, included with Lean.
- Git, used by `verify.sh` to confirm the pinned Mathlib revision.

The first build downloads the pinned Mathlib dependency. Run the following from
this directory:

```bash
lake exe cache get
lake build
```

## Full package check

```bash
./verify.sh
```

The script checks that every Lean source begins with `module`, checks file
lengths and the manifest source entry, verifies the toolchain and Mathlib
revision, builds `Solution`, `Challenge`, and `AxiomAudit`, and confirms the
transitive axioms of the exported theorem. It writes build and axiom logs to
`.verification/`.

To build and also run Comparator locally, use:

```bash
./verify.sh --no-sandbox
```

Comparator reports from this mode are diagnostic only because the sandbox is
disabled. A trustworthy Comparator run requires the default sandboxed mode.

## Targets

The Lake package has four libraries:

| Library | Sources | Purpose |
| --- | --- | --- |
| `Proofs` | `Proofs/Erdos787Base.lean`, `Proofs/Erdos787Proofs.lean` | Definitions and the complete proof. |
| `Challenge` | `Challenge.lean` | The target statement with `sorry`. |
| `Solution` | `Solution.lean` | The proved target statement. |
| `AxiomAudit` | `AxiomAudit.lean` | Transitive axiom report for the exported theorem. |

Build a single library with `lake build Solution`, for example.
