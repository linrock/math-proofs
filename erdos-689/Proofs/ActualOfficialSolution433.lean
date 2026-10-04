module

public import ActualMajorArcFinalCoupling433

@[expose] public section


open Filter Finset
open scoped Topology

namespace Erdos689

/-- The verbatim proposition on the right-hand side of the upstream
formal-conjectures statement for Erdős problem #689. -/
theorem erdos_689_original_statement :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ a : ℕ → ℕ,
      ∀ m ∈ Finset.Icc 1 n,
        2 ≤ ((Finset.Icc 1 n).filter
          fun p => p.Prime ∧ a p ≡ m [MOD p]).card := by
  exact officialStatement_unconditional

#print axioms Erdos689.officialStatement_unconditional
#print axioms Erdos689.erdos_689_original_statement

end Erdos689
