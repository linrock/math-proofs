# Erdős 33: additive complements to the squares

A Lean 4 formalization of the open problem asking for the smallest limsup |A ∩ [1, N]| / √N over additive complements A of the squares, where every natural number is a + n². Erdős observed that the value is finite and that \(1\) is a strict lower bound. Moser's weighted-representation bound and the Moser–Abel identity, applied to a Cilleruelo step-function computation at \(R = 60\), give the sharper bound \(5/4\). The same method at \(R = 150\) and \(R = 500\) yields \(63/50\) and \(127/100\), while van Doorn's shifted-block construction with Fibonacci widths gives the upper bound \(2\varphi^{5/2}\). The exact value of the infimum remains open.

See [Erdős problem #33](https://www.erdosproblems.com/33) for background and literature.

## Scope and main results

The package proves both solved variants of Erdős problem 33: the strict lower bound above \(1\), and van Doorn's \(2\varphi^{5/2}\) upper bound. It also proves the rational lower bounds \(5/4 = 1.25\), \(63/50 = 1.26\), and \(127/100 = 1.27\) on the infimum, each a finite-resolution instance of Cilleruelo's step-function method with the step sums \(S(60) = 2879\), \(S(150) = 17815\), and \(S(500) = 196830\) computed in the kernel. These three bounds quantify over every additive complement and narrow the interval containing the infimum without closing the main value question.

None of the rational bounds is the strongest known result. Cilleruelo (1993), Habsieger (1995), and Balasubramanian–Ramana (2001) independently proved the asymptotic lower bound \(4/\pi \approx 1.2732\), which exceeds \(127/100\). The package's contribution on the lower-bound side is a self-contained kernel-checked derivation, not an improvement on the literature.

The upstream `AdditiveBasisCondition` asks that *every* natural number be of the form `a + n²`. Its docstring records that this was changed from "every large integer" on the grounds that the two conditions are equivalent and that the original paper used the every-integer formulation. The package neither verifies that historical claim nor formalizes the equivalence between the two conventions.

[Solution.lean](Solution.lean) exports 8 unconditional theorems in `Erdos33` (matched by [Challenge.lean](Challenge.lean) and [comparator.json](comparator.json)) across 2 self-contained proof modules in [Proofs/](Proofs), using only the standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`):

| Theorem in `Solution.lean` | Mathematical statement |
| --- | --- |
| `Erdos33.erdos_33_variants_one_mem_lowerBounds` | **Formal Conjectures Erdős 33 `variants.one_mem_lowerBounds`.** Proves \(1 < \inf_A \limsup \lvert A \cap [1, N]\rvert/\sqrt{N}\). |
| `Erdos33.erdos_33_variants_vanDoorn` | **Formal Conjectures Erdős 33 `variants.vanDoorn`.** Proves \(\inf_A \limsup \lvert A \cap [1, N]\rvert/\sqrt{N} \le 2\varphi^{5/2}\). |
| `Erdos33.Core.five_fourths_le_iInf_limsup` | **Step-function lower bound at \(R = 60\): \(5/4 = 1.25\).** Proves \(5/4 \le \inf_A \limsup \lvert A \cap [1, N]\rvert/\sqrt{N}\) via \(S(60) = 2879\); audited in `AxiomAudit.lean` under the module namespace `Erdos33.Core`, since `Solution.lean` re-exports the upstream variants rather than this auxiliary bound. |
| `Erdos33.sixty_three_fiftieths_le_iInf_limsup` | **Step-function lower bound at \(R = 150\): \(63/50 = 1.26\).** Proves \(63/50 \le \inf_A \limsup \lvert A \cap [1, N]\rvert/\sqrt{N}\) via \(S(150) = 17815\). |
| `Erdos33.exists_ge_sixty_three_fiftieths_normalizedPrefixRatio` | **Subsequential \(63/50\) bound for every square additive complement.** Proves \(\forall M, \exists N \ge M, 63/50 \le \lvert A \cap [1, N]\rvert/\sqrt{N}\). |
| `Erdos33.additiveBasisCondition_vanDoornUnion` | **van Doorn block-union complement theorem.** Proves `AdditiveBasisCondition (vanDoornUnion M)` for any \(M_j \ge 1\). |
| `Erdos33.two_mul_sum_fibBlockWidth_div_sqrt_start_le` | **Fibonacci block-ratio bound.** Proves \(2 \sum_{j=0}^{K} F_{j+2} / \sqrt{B_K} \le 2\varphi^{5/2}\) for all \(K \ge 1\). |
| `Erdos33.one_hundred_twenty_seven_over_one_hundred_le_iInf_limsup` | **Step-function lower bound at \(R = 500\): \(127/100 = 1.27\).** Proves \(127/100 \le \inf_A \limsup \lvert A \cap [1, N]\rvert/\sqrt{N}\) via \(S(500) = 196830\). |
| `Erdos33.exists_ge_one_hundred_twenty_seven_over_one_hundred_normalizedPrefixRatio` | **Subsequential \(127/100\) bound for every square additive complement.** Proves \(\forall M, \exists N \ge M, 127/100 \le \lvert A \cap [1, N]\rvert/\sqrt{N}\). |

[Statement.lean](Statement.lean) records the benchmark statement without placeholders, and [AxiomAudit.lean](AxiomAudit.lean) verifies statement fidelity, non-vacuity witnesses, and the transitive axioms of every exported endpoint.

## Proof modules

- [SquareComplementBounds33.lean](Proofs/SquareComplementBounds33.lean): Formalizes square additive complements, Moser's weighted-representation bound and the Moser–Abel identity, the \(R = 60, 150, 500\) step sums, the rational bounds \(5/4\), \(63/50\) and \(127/100\), van Doorn's block construction, and the reduction from block-scale ratios to the infimum.
- [FibonacciVanDoorn33.lean](Proofs/FibonacciVanDoorn33.lean): Instantiates the Fibonacci width sequence \(M_j = F_{j+2}\), proves the Cassini-ratio estimate and the block ratio bound \(2\sum_{j=0}^{K} F_{j+2}/\sqrt{B_K} \le 2\varphi^{5/2}\), and concludes van Doorn's upper bound.

## Build and verification

See [BUILD.md](BUILD.md) for reproduction commands and [THIRD_PARTY.md](THIRD_PARTY.md) for source attribution and license information. Running `./verify.sh --no-sandbox` builds all targets from source, audits transitive axioms, and runs `lake comparator` so both `nanoda_bin` and Lean's default kernel check `Solution` against `Challenge`.
