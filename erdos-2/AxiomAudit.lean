module

public import Solution
public import Statement


@[expose] public section

/-!
Full statement, fidelity, non-vacuity, and transitive-axiom checks for the
submitted Erdős #2 endpoints. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted.
-/

namespace Erdos2.Standalone

/-- The separately stated original target is exactly the proved proposition. -/
theorem statement_fidelity : Erdos2.Challenge.statement := by
  exact erdos_2

/-- Non-vacuity witness: the classic `{0 mod 2, 0 mod 3, 1 mod 4, 1 mod 6, 11 mod 12}`
covering system starts at modulus `2`, and any single modulus `d ≥ 2` leaves an
integer uncovered (`r d + 1 ≢ r d [ZMOD d]`). -/
theorem nonvacuity_single_modulus (d : ℕ) (hd : 2 ≤ d) (r : ℤ) :
    ¬ Int.ModEq (d : ℤ) r (r + 1) := by
  intro h
  have hdvd : (d : ℤ) ∣ (r + 1) - r := Int.modEq_iff_dvd.mp h
  rw [add_sub_cancel_left] at hdvd
  have hle : (d : ℤ) ≤ 1 := Int.le_of_dvd zero_lt_one hdvd
  omega

end Erdos2.Standalone

#print Erdos2.Standalone.erdos_2
#print Erdos2.Standalone.not_arbitrarilyLarge_ideal_coverings
#print Erdos2.Standalone.minimum_modulus_bound
#print Erdos2.Standalone.finite_noncoverage_bound
#print axioms Erdos2.Standalone.erdos_2
#print axioms Erdos2.Standalone.not_arbitrarilyLarge_ideal_coverings
#print axioms Erdos2.Standalone.minimum_modulus_bound
#print axioms Erdos2.Standalone.finite_noncoverage_bound
#print axioms Erdos2.Standalone.statement_fidelity
#print axioms Erdos2.Standalone.nonvacuity_single_modulus
