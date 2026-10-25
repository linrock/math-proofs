# Erdős Problem 423 (`erdos-423`)

A standalone Lean 4 (`leanprover/lean4:v4.35.0-rc2`) package for Hofstadter's
consecutive-block-sum sequence: a(1) = 1, a(2) = 2, and each later term is the least larger
integer representable as a sum of at least two consecutive earlier terms
([OEIS A005243](https://oeis.org/A005243)).

## Scope

Upstream records five solved variants of this open problem. The package proves two of them: the
excess a(n) - n of any such sequence is unbounded, and the sequence omits infinitely many
positive integers. Both follow the 2026 arguments of Bolan and Tang. It also re-proves a third
variant, that the excess is nondecreasing; that statement already has an independent Lean proof
in [`anatoliiohorodnyk/lean-fc-proofs`](https://github.com/anatoliiohorodnyk/lean-fc-proofs)
and is not claimed as new here.

Beyond the variants the package proves uniqueness of the zero-anchored sequence, exact
omitted-value counting, global block-sum closure, and prefix-difference bounds. A completed-square
Ramanujan--Nagell obstruction refutes eventual linear stabilization and gives an explicit iterated
excess tower. Stage reductions convert control of that tower into conditional statements about the
remaining finite-bound variants and the main asymptotic question, so the tower-control hypotheses
are not discharged and those reductions are not unconditional proofs. The Erdős--Graham main
conjecture a(n) = n + o(n) remains open, so this package covers solved variants of an open problem.

## Verification

```bash
./verify.sh
```

Run `./verify.sh` from this directory. The package has 24 exported theorems, exact
solution--challenge matches, no `sorry` in its proof modules, and only the standard foundational
axioms (`propext`, `Classical.choice`, and `Quot.sound`).

See [BUILD.md](BUILD.md) for build details and [THIRD_PARTY.md](THIRD_PARTY.md) for attribution.
