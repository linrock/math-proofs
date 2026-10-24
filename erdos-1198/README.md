# Erdős Problem 1198: Hindman's monochromatic finite-sums theorem

This package proves the Hindman finite-sums variant of Erdős Problem 1198 in Lean 4. For every
two-colouring of the natural numbers, it produces a strictly increasing sequence
$a_0 < a_1 < a_2 < \cdots$ of positive integers and one colour such that every nonempty finite
sum $\sum_{i \in T} a_i$ has that colour. Equivalently, it proves

```lean
theorem Erdos1198.erdos_1198.variants.hindman :
    ∀ c : ℕ → Fin 2, ∃ a : ℕ → ℕ, StrictMono a ∧ 0 < a 0 ∧ ∃ col : Fin 2,
      ∀ T : Finset ℕ, T.Nonempty → c (∑ i ∈ T, a i) = col
```

The proof applies the partition-regular form of Hindman's theorem to the constant stream of ones.
This yields a stream $b$ with $0 < b_i$ whose nonempty finite sums all have one colour. Consecutive
blocks of $b$ are chosen so that each block sum is larger than the previous one. The block sums form
the required sequence $a$, and a finite sum of block sums is a single finite sum of distinct terms
of $b$.

The main declaration of Erdős Problem 1198 asks for the corresponding statement about sums of
products and is refuted by Smith's counterexample. This package does **not** formalize that
counterexample: the upstream declaration `Erdos1198.erdos_1198` remains a `sorry`. Only the
Hindman variant is proved here.

The mathematical result is due to Neil Hindman, [*Finite sums from sequences within cells of a
partition of N*](https://doi.org/10.1016/0097-3165(74)90023-5), Journal of Combinatorial Theory,
Series A 17 (1974), 1-11. The strong partition-regular theorem used in the argument is the Mathlib
theorem `Hindman.FS_partition_regular`, contributed by David Wärn. The statement is aligned with
the declaration `erdos_1198.variants.hindman` in
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/c094b979118b89adb77cf5f8d923ac9dd2e51b1d/FormalConjectures/ErdosProblems/1198.lean),
at commit `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`.

## Proof structure

- `Erdos1198.reduce` obtains a positive stream whose finite-sum set is monochromatic.
- `Erdos1198.BlockExtraction.block_extraction` partitions that stream into consecutive blocks
  and proves the block sums are strictly increasing.
- `Erdos1198.block_union_sum` identifies a sum of block sums with a finite sum in the original
  stream.
- `Erdos1198.erdos_1198.variants.hindman` assembles these steps and proves positivity, strict
  monotonicity, and the common colour.

## Build and verification

The package is pinned to Lean `4.35.0-rc2` (`leanprover/lean4:v4.35.0-rc2`) and Mathlib revision
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

```bash
./verify.sh
```

This checks the module headers and line limits, builds `Solution`, `AxiomAudit`, and `Challenge`,
replays the axiom audit, and runs the Comparator with its sandbox enabled. The proof uses only the
standard axioms `propext`, `Classical.choice`, and `Quot.sound`. Running `./verify.sh --no-sandbox`
performs the same checks but runs the Comparator without its sandbox, so its verdict is recorded as
not trustworthy; use it only on a machine where the sandbox cannot start.

See [BUILD.md](BUILD.md) for the build details and [THIRD_PARTY.md](THIRD_PARTY.md) for attribution.
