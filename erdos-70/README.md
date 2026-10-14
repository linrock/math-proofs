# Erdős 70: continuum triple partitions (omega_one ZFC refutation and omega_three)

This package formalizes the unconditional ZFC refutation of the uncountable variant `erdos_70.variants.omega_one` ($\mathfrak{c}.\mathrm{ord} \not\to (\omega_1, 4)^3_2$ via a Sierpiński real-peak coloring) and the positive resolution of `erdos_70.variants.omega_three` ($\mathfrak{c}.\mathrm{ord} \to (\omega, 3)^3_2$) for Erdős problem 70.

See [Erdős problem #70](https://www.erdosproblems.com/70) for background and literature.

## Scope and main results

Refutes `erdos_70.variants.omega_one` (`not_ordinalCardinalRamsey3_continuum_aleph1_four` and `erdos_70_omega_one_refuted`) and proves `erdos_70.variants.omega_three` (`ordinalCardinalRamsey3_continuum_omega_three` and `erdos_70_omega_three_solved`). The countable-ordinal conjecture `erdos_70` and `omega_times_two_four` remain open.

[Solution.lean](Solution.lean) exports 4 unconditional theorems in `Erdos70.Palomar` (matched by [Challenge.lean](Challenge.lean) and [comparator.json](comparator.json)) proved in [Proofs/ContinuumTriplePartitions70.lean](Proofs/ContinuumTriplePartitions70.lean), using only the standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`):

| Theorem in `Solution.lean` | Mathematical statement |
| --- | --- |
| `Erdos70.Palomar.not_ordinalCardinalRamsey3_continuum_aleph1_four` | **ZFC refutation at n = 4.** Proves `¬ OrdinalCardinalRamsey3 (𝔠).ord (Cardinal.aleph 1).ord 4`. |
| `Erdos70.Palomar.erdos_70_omega_one_refuted` | **Formal Conjectures Erdős 70 omega_one variant.** Proves `False ↔ ∀ n ≥ 2, OrdinalCardinalRamsey3 (𝔠).ord (Cardinal.aleph 1).ord n`. |
| `Erdos70.Palomar.ordinalCardinalRamsey3_continuum_omega_three` | **Continuum (ω, 3) partition theorem.** Proves `OrdinalCardinalRamsey3 (𝔠).ord ω 3`. |
| `Erdos70.Palomar.erdos_70_omega_three_solved` | **Formal Conjectures Erdős 70 omega_three variant.** Proves `True ↔ OrdinalCardinalRamsey3 (𝔠).ord ω 3`. |

[Statement.lean](Statement.lean) records the benchmark statement without placeholders, and [AxiomAudit.lean](AxiomAudit.lean) verifies statement fidelity, non-vacuity witnesses, and the transitive axioms of every exported endpoint.

## Build and verification

See [BUILD.md](BUILD.md) for reproduction commands and [THIRD_PARTY.md](THIRD_PARTY.md) for source attribution and license information.
