import Mathlib

/-!
# Erdős #689: the exact eventual double-covering statement

This statement surface imports only Mathlib. The interval is closed at both
ends, the selected moduli are distinct primes at most the same endpoint, and
one residue is chosen for each prime. No explicit threshold is asserted.

The proof hole is intentional: Comparator must compare this declaration with
the independently compiled, fully proved declaration in `Solution`.
-/

open Filter
open scoped Topology

namespace Erdos689.Palomar

/-- Every sufficiently large initial interval admits one selected residue
class per available prime that covers every target at least twice. -/
theorem eventual_double_cover :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ a : ℕ → ℕ,
      ∀ m ∈ Finset.Icc 1 n,
        2 ≤ ((Finset.Icc 1 n).filter
          fun p => p.Prime ∧ a p ≡ m [MOD p]).card := by
  sorry

end Erdos689.Palomar
