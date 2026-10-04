module

public import AnalyticBridge
public import ErdosProblems.Erdos730.PNTAP

@[expose] public section


/-!
# An unconditional prime-number theorem in fixed arithmetic progressions

The separately pinned Lean 4.33.1 research environment imports Will Blair's
fixed-modulus prime-counting bridge and the attributed PrimeNumberTheoremAnd
proof.  The exact closed-interval formulation required by Erdős #689 follows
for every positive fixed modulus and every reduced residue.

The prime-pattern lower bounds, uniform switched-set estimates, degree bounds,
and final scalar construction remain unproved.  This module does not solve
Erdős #689 and is deliberately separate from its canonical Lean 4.32 verifier.
-/

open Filter
open scoped Topology

namespace Erdos689

/-- Prime counting on `[0,n]` agrees exactly with counting on `[1,n]`. -/
theorem primeAPCount_eq_closed_filter (q r n : ℕ) :
    Erdos730.FullDensity.primeAPCount q r n =
      ((Finset.Icc 1 n).filter fun p =>
        p.Prime ∧ p % q = r % q).card := by
  unfold Erdos730.FullDensity.primeAPCount
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc,
    Nat.lt_succ_iff]
  constructor
  · rintro ⟨hbound, hprime, hresidue⟩
    exact ⟨⟨hprime.one_le, hbound⟩, hprime, hresidue⟩
  · rintro ⟨⟨_, hbound⟩, hprime, hresidue⟩
    exact ⟨hbound, hprime, hresidue⟩

/-- The exact fixed-progression analytic hypothesis of #689 is a theorem. -/
theorem prime_number_theorem_arithmetic_progressions :
    PrimeNumberTheoremAP := by
  intro q r hq hcoprime
  have hresidue : Nat.Coprime (r % q) q := by
    rw [Nat.Coprime] at hcoprime ⊢
    rw [Nat.gcd_comm] at hcoprime
    rwa [Nat.gcd_rec] at hcoprime
  have hpnt :=
    (Erdos730.FullDensity.pntAPInputAtModulus q hq).2
      (r % q) (Nat.mod_lt r hq) hresidue
  simpa [primeAPCount_eq_closed_filter, Nat.mod_mod, one_div] using hpnt

end Erdos689

#print axioms WeakPNT_AP
#print axioms chebyshev_asymptotic_pnt
#print axioms Erdos730.FullDensity.pntAPInputAtModulus
#print axioms Erdos689.primeAPCount_eq_closed_filter
#print axioms Erdos689.prime_number_theorem_arithmetic_progressions
