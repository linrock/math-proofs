# Build and audit Erdős #2

Run the following commands from this directory. Elan selects the exact
compiler from [lean-toolchain](lean-toolchain): Lean `v4.35.0-rc2`, compiler commit
`11acb17ec6b07a8f9e9173e6845197929540936b`. The canonical Mathlib commit is
`065356127b1dc0016f66b7283ce0ce2c4055aa55`, pinned by
[lakefile.toml](lakefile.toml) and [lake-manifest.json](lake-manifest.json).
The manifest also pins Mathlib's transitive dependencies, including Batteries
used by Architect. Ordinary replay does not require `lake update`.

```sh
lake exe cache get
./verify.sh
```

The first command downloads canonical compiled Mathlib dependencies. A cold
checkout needs network access and several GiB for the dependency sources and
cache. It does not replace the project's own proof compilation.

The sequential [verify.sh](verify.sh) route first checks the saved source
digests, then compiles nine Architect modules in import order, two narrow
Mertens/Euler–Maclaurin modules, all 31 local proof modules, and the interfaces
`Statement`, `Solution` and `AxiomAudit`. These 45 completed modules use
`-j1 -M8192 -E hasSorry`. It also builds the separate numerical `Challenge`
benchmark with `-j1 -M8192`, allowing its one intentional `sorry`. The memory
setting is a per-process Lean limit. The check builds every vendored
proof-bearing source rather than depending on the original repository's
compiled research artifacts.

The Lake project's default targets are `Challenge`, `Solution` and
`AxiomAudit`. A normal project build and an explicit endpoint audit can also
be run as follows:

```sh
lake build Statement Solution AxiomAudit Challenge
lake env lean -j1 -M8192 -E hasSorry -Dformat.width=1000000 \
  --setup=.lake/build/ir/AxiomAudit.setup.json AxiomAudit.lean
```

The explicit audit prints the three public declarations and four transitive
axiom reports, including statement fidelity. The verifier accepts only
`propext`, `Classical.choice` and `Quot.sound`. The original
theorem must have the exact `False ↔` ideal formulation without an additional
mathematical premise. Statement is a proposition definition and contains no
intentional proof hole. Challenge is a numerical benchmark excluded from
Solution, Statement and AxiomAudit imports. The setup file binds the explicit
audit's 44 owned imports to this package's built project modules.

[comparator.json](comparator.json) compares the independently stated numerical
theorem in Challenge and Solution, permitting only the same three foundational
axioms and enabling NanoDa. The stock Lean 4.35.0-rc2 toolchain bundles
`lake comparator`, `leanexport`, `leanchecker` and `nanoda_bin`. The default
sandbox uses Linux bubblewrap (`bwrap`):

```sh
lake env lake comparator --config comparator.json
```

The recorded local macOS comparison explicitly disabled that sandbox:

```sh
lake env lake comparator --config comparator.json --inadvisably-no-sandbox
```

The package source/audit check and this comparison have separate verification
records. The local unsandboxed comparison is not a Palomar server acceptance.

## Verification record

The current Lean 4.35.0-rc2 port passed 46 fresh source builds: the 11 vendored
provider modules, 31 local proof modules, three completed interfaces and one
separate benchmark. The saved-source audit passed all four endpoint/fidelity
reports with only `propext`, `Classical.choice` and `Quot.sound`, and its setup
records 44 owned import bindings. Comparator matched the selected numerical
statement; NanoDa and Lean's default kernel both accepted the solution in the
local unsandboxed macOS run above.

The canonical `./verify.sh` replay and normal `lake build` both passed. Final
release digests pass `shasum -a 256 -c SHA256SUMS` after the documentation and
replay records are finalized. [VERIFICATION.json](VERIFICATION.json) distinguishes
the fresh source builds, canonical proof replay and local comparison, and links
their logs. [PORTING.md](PORTING.md) records the preserved Lean 4.33.1 baseline
and the port. The builds reuse canonical compiled Mathlib dependencies; they
do not rebuild Mathlib from source. The result remains qualitative, with no
explicit numerical cutoff. Source revisions and licence boundaries are in
[source-manifest.json](source-manifest.json) and [THIRD_PARTY.md](THIRD_PARTY.md).
