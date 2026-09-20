# Math proofs

Standalone [Lean 4](https://lean-lang.org/) proofs of [Erdős problems](https://www.erdosproblems.com/), packaged
as pinned [Lake](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/) projects for [Palomar](https://palomar-registry.org/) submission.
Each project has a statement-only `Challenge.lean`, a proved `Solution.lean`,
an `AxiomAudit.lean`, and build instructions.

## Problems

- [Erdős 689: Double covering with prime residues](erdos-689/README.md):
  **Yes.** For every sufficiently large `n`, one residue class per prime
  `p ≤ n` can be chosen so every integer
  `1 ≤ m ≤ n` lies in at least two of them.
- [Erdős 973: Power sums on or beyond the unit circle](erdos-973/README.md):
  **No.** For every `C > 1`, once `n` is large enough, any `n` complex
  numbers with `|z_i| ≥ 1` have some order
  `2 ≤ k ≤ n+1` with `|∑_i z_i^k| > C^-n`. This holds even without the
  original `z₁ = 1` condition.

## License

MIT
