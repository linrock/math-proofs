module

/-
Copyright 2025 The Formal Conjectures Authors.
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License") for the
attributed Formal Conjectures definitions and statement forms, and the MIT
License for the local proof development.

Adaptation notice: Linmiao Xu adapted the Erdős 2 statements and proved all
public endpoints in Lean 4.35.0-rc2 in 2026. This module does not import or
reference `Challenge`.
-/

public import NoncoverageCapstone2


@[expose] public section

/-!
# Proved endpoints for Erdős Problem 2

This module exports the four proved targets declared in `Challenge.lean`:
- `Erdos2.Standalone.erdos_2`: the literal Formal Conjectures ideal statement
  (`False ↔ ∀ B : ℕ, ∃ c : StrictCoveringSystem ℤ, ...`),
- `Erdos2.Standalone.not_arbitrarilyLarge_ideal_coverings`: the direct negation
  of arbitrarily large minimum moduli in strict ideal covering systems,
- `Erdos2.Standalone.minimum_modulus_bound`: the uniform numerical bound on the
  least modulus of any finite covering of `ℤ` by distinct positive moduli, and
- `Erdos2.Standalone.finite_noncoverage_bound`: the uniform noncoverage bound
  for finite sets of moduli all exceeding `B`.

The proof formalizes the recursive probability sieve of Balister, Bollobás,
Morris, Sahasrabudhe, and Tiba (arXiv:1811.03547) with all analytic inputs
(including Mertens' third theorem and smooth-number Euler products) proved in
the source graph and pinned Mathlib dependency.
-/

namespace Erdos2.Standalone

/-- The literal Formal Conjectures statement for Erdős Problem 2, with
`answer(False)` elaborated as `False`. -/
theorem erdos_2 :
    False ↔
      ∀ B : ℕ, ∃ c : StrictCoveringSystem ℤ, ∀ i, ∃ m : ℕ,
        c.moduli i = Ideal.span {(m : ℤ)} ∧ B < m := by
  exact Erdos2.Noncoverage.erdos_2

/-- Direct disproof of arbitrarily large minimum moduli in strict ideal
covering systems of `ℤ`. -/
theorem not_arbitrarilyLarge_ideal_coverings :
    ¬ ∀ B : ℕ, ∃ c : StrictCoveringSystem ℤ, ∀ i, ∃ m : ℕ,
        c.moduli i = Ideal.span {(m : ℤ)} ∧ B < m := by
  exact Erdos2Statement.not_arbitrarilyLarge_of_uniformNumericalBound
    Erdos2.Noncoverage.uniformNumericalBound

/-- Every finite covering by distinct positive natural moduli contains a
modulus bounded by one universal constant. Residues may be signed integers. -/
theorem minimum_modulus_bound :
    ∃ B : ℕ, ∀ {ι : Type} [Fintype ι] (m : ι → ℕ) (r : ι → ℤ),
      Function.Injective m → (∀ i, 0 < m i) →
      (∀ z : ℤ, ∃ i, Int.ModEq (m i : ℤ) (r i) z) →
      ∃ i, m i ≤ B := by
  exact Erdos2.Noncoverage.uniformNumericalBound

/-- Distinct sufficiently large moduli cannot cover all integers, regardless
of the chosen residues. -/
theorem finite_noncoverage_bound :
    ∃ B : ℕ, ∀ D : Finset ℕ, (∀ d ∈ D, B < d) → ∀ r : ℕ → ℤ,
      ∃ z : ℤ, ∀ d ∈ D, ¬ Int.ModEq (d : ℤ) (r d) z := by
  exact Erdos2.Noncoverage.finiteSetNoncoveringBound

end Erdos2.Standalone
