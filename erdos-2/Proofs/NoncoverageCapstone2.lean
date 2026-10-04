module

public import SieveRecursion2
public import FiniteLcm2
public import ResidueLift2
public import FiniteIndexAdapter2
public import StatementAdapter2


@[expose] public section

/-!
# Final finite noncoverage and original-statement consumers for Erdős #2

Combines the uniform budget selection (`uniform_budget_selection`), the
largest-prime recursive probability sieve (`exists_sieve_weight`), the residue
lift (`integer_lift_of_avoiding_reductions`), and the finite-index and ideal
statement adapters to prove `finiteSetNoncoveringBound`,
`uniformNumericalBound`, and `erdos_2`.
-/

open scoped BigOperators

namespace Erdos2.Noncoverage

/-- The smooth and late budgets use constants independent of every finite
modulus set and its arbitrary signed residue function. -/
theorem finiteSetNoncoveringBound : FiniteIndex.FiniteSetNoncoveringBound := by
  classical
  obtain ⟨C, hC, A, _hA, M, _hM, hprod, hlate, hinitial⟩ :=
    Analytic.uniform_budget_selection
  refine ⟨M, ?_⟩
  intro D hD r
  have hDpos : ∀ d ∈ D, 0 < d := by
    intro d hd
    exact lt_of_le_of_lt (Nat.zero_le M) (hD d hd)
  obtain ⟨N, hN, hdiv⟩ := FiniteLcm.exists_positive_common_multiple D hDpos
  have _ : NeZero N := ⟨hN.ne'⟩
  have hprod' : ∀ p : ℕ, 2 ≤ p → ∀ s : Finset ℕ,
      (∀ q ∈ s, q.Prime ∧ q < p) →
        (∏ q ∈ s, EulerMoment.factorBound (q : ℝ)) ≤
          C * Real.log (p : ℝ) ^ 6 := by
    intro p hp s hs
    simpa only [EulerMoment.factorBound, Analytic.deltaHalfFactor] using
      hprod p hp s hs
  obtain ⟨w, _hw, hmass⟩ :=
    SieveRecursion.exists_sieve_weight N D r C A hC.le hprod'
  have hsmooth :
      (∑ d ∈ D.filter (fun d => ∀ q ∈ d.primeFactors, q ≤ A),
        1 / (d : ℝ)) < (1 : ℝ) / 4 := by
    apply hinitial
    · intro d hd
      exact (Finset.mem_filter.mp hd).2
    · intro d hd
      exact (hD d (Finset.mem_filter.mp hd).1).le
  have htail :
      (∑ p ∈ N.primeFactors.filter (fun p => A < p),
        Analytic.latePrimeCost C p) < (1 : ℝ) / 4 := by
    apply hlate
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hhalf :
      FiniteWeight.mass w.value (CoveringModel.coveredSet D r N) <
        (1 : ℝ) / 2 := by
    linarith
  obtain ⟨x, hx⟩ := FiniteWeight.exists_outside_of_mass_lt_one w.value
    (CoveringModel.coveredSet D r N) w.normalized
    (lt_trans hhalf (by norm_num))
  have havoid : ∀ d : {d : ℕ // d ∈ D},
      ZMod.castHom (hdiv d.val d.property) (ZMod d.val) x ≠
        (r d.val : ZMod d.val) := by
    intro d heq
    apply hx
    exact (CoveringModel.mem_coveredSet D r N x).mpr
      ⟨d.val, d.property, hdiv d.val d.property, heq⟩
  obtain ⟨z, hz⟩ := ResidueLift.integer_lift_of_avoiding_reductions
    (fun d : {d : ℕ // d ∈ D} => d.val)
    (fun d : {d : ℕ // d ∈ D} => r d.val)
    (fun d => hdiv d.val d.property) x havoid
  exact ⟨z, fun d hd => hz ⟨d, hd⟩⟩

/-- Exact arbitrary-finite-index numerical endpoint consumed by the original
ideal formulation. Modulus one and empty index types remain in its domain. -/
theorem uniformNumericalBound : Erdos2Statement.UniformNumericalBound := by
  exact FiniteIndex.uniformNumericalBound_of_finiteSetNoncovering
    finiteSetNoncoveringBound

/-- Literal proposition of Formal Conjectures #2, with `answer(False)`
represented by its elaborated proposition `False`. -/
theorem erdos_2 :
    False ↔
      ∀ B : ℕ, ∃ c : StrictCoveringSystem ℤ, ∀ i, ∃ m : ℕ,
        c.moduli i = Ideal.span {(m : ℤ)} ∧ B < m := by
  exact Erdos2Statement.formalConjectures_statement_of_uniformNumericalBound
    uniformNumericalBound

end Erdos2.Noncoverage
