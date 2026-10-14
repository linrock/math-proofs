# Erdős Problem 939 (`erdos-939`)

Standalone Lean 4 (`leanprover/lean4:v4.35.0-rc2`) formalization package for [Erdős Problem 939](https://www.erdosproblems.com/939) on coprime sums of $r$-powerful numbers (`Erdos939Sums r`).

## Scope

The headline conjecture `erdos_939` is **open** and is not proved here. This package proves the solved variants listed in the Formal Conjectures statement file, together with supporting results, and reduces the open problem exactly to the case $r = 4$.

- **Open barrier ($r = 4$).** `erdos_939_iff_four_nonempty` and `erdos_939_iff_exists_coprime_four_full_pair` show that the conjecture holds if and only if there are positive coprime $4$-powerful integers $a, b$ whose sum $a + b$ is $4$-powerful. Such a triple would need $abc$ quality above $4/3$. No such triple is known, and none is excluded unconditionally.
- **Conditional results.** `erdos939Sums_four_finite_of_abc_seven_sixths_bound`, `erdos939Sums_five_finite_of_abc_five_fourths_threshold` and `not_erdos_939_of_four_full_radical_obstruction` are conditional: each assumes an explicit $abc$-type bound or radical hypothesis stated in the theorem. They are not unconditional finiteness results.
- **Unconditional results.** Everything else below is proved without extra hypotheses.

## Formal Conjectures variants

The Formal Conjectures file `FormalConjectures/ErdosProblems/939.lean` contains these declarations, and this package proves a matching statement for each of `erdos_939_variants_*` in `Challenge.lean` and `Solution.lean`:

| Variant | Status upstream at time of packaging |
| --- | --- |
| `finite` (`answer(False)`), `infinite_of_six_le`, `triples`, `seven`, `eight` | `sorry` without a linked proof |
| `examples`, `euler` | already proved inline upstream |
| `erdos_939` | open (`answer(sorry)`) |

## Main verified results (`Erdos939.Palomar`)

- **Existence and infinitude for $r \ge 5$.**
  - `erdos_939_variants_finite`, `erdos_939_variants_infinite_of_six_le`, `erdos_939_variants_seven`, `erdos_939_variants_eight`, `cambieFiveSet_mem_erdos939Sums_five`.
  - The $r = 5, 7, 8$ witnesses are due to Stijn Cambie. The $r \ge 6$ construction is due to Liam Price.
- **Coprime $3$-powerful triples.**
  - `erdos_939_variants_triples`, `erdos_939_variants_triples_infinite`, `cohn_noncube_triples_infinite`, `cohn_noncube_generalSums_three_two_infinite`, `erdos_939_generalSums_three_two_infinite`.
  - These formalize the families of Nitaj (1995) and Cohn (1998).
- **Euler's conjecture.** `erdos_939_variants_euler` and `landerParkinFiveSet_mem_erdos939GeneralSums_five_four` certify the Lander–Parkin fifth-power counterexample.
- **Structure and $abc$ quality.**
  - `r_full_iff_exists_squarefree_cores`, `rad_pow_r_lt_sum_pow_pred_of_mem_erdos939Sums`, `abc_quality_real_bound_of_mem_erdos939Sums`, `rad_pow_four_le_and_lt_cube_of_mem_erdos939Sums_four`.
  - Walsh's quadratic-twist criteria: `walsh_twist_pair_mem_erdos939GeneralSums_three_two`, `walsh_parametric_cube_scaling_coprime_iff`.

## Layout

- `Challenge.lean`, `Statement.lean`, `Solution.lean`: the statements and their proofs (each challenge theorem has a matching solution theorem).
- `AxiomAudit.lean`: `#print axioms` audit of every solution theorem.
- `Proofs/Blueprint939.lean`, `Proofs/AbcQualityAndCohnRecurrence939.lean`, `Proofs/PowerfulSumsAndNitaj939.lean`: supporting development.

## Build and verification

See [BUILD.md](BUILD.md) for build commands and [THIRD_PARTY.md](THIRD_PARTY.md) for attribution and license information. Verification artifacts are in `.verification/`.
