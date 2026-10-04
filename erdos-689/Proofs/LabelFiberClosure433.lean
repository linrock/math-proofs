module

public import LabelFiberSieve433

@[expose] public section


/-!
# Removing artificial seed and coefficient assumptions from label fibers

A fixed-label fiber need not have coprime coefficients when the prime label
itself belongs to the support.  Once the actual label is coprime to the
support coefficient, every nonempty fiber forces coefficient coprimality
and supplies its own canonical residue seed.
-/

open Finset
open scoped BigOperators

namespace Erdos689

/-- A genuine fixed-label solution with a label coprime to its right
coefficient automatically forces the left coefficient to be invertible. -/
theorem labelFiber_coefficient_coprime_of_label_coprime
    (a d z q r : ℕ)
    (hz : Nat.Coprime z (2 * d))
    (hsolution : 2 * d * r = a * q + z) :
    Nat.Coprime a (2 * d) := by
  apply Nat.coprime_of_dvd
  intro p hp hpa hpcoefficient
  have hpsum : p ∣ a * q + z := by
    rw [← hsolution]
    exact dvd_mul_of_dvd_left hpcoefficient r
  have hpproduct : p ∣ a * q := dvd_mul_of_dvd_left hpa q
  have hpz : p ∣ z := (Nat.dvd_add_iff_right hpproduct).mpr hpsum
  have hpcoprime : Nat.Coprime p z :=
    hz.symm.coprime_dvd_left hpcoefficient
  exact (hp.coprime_iff_not_dvd.mp hpcoprime) hpz

/-- Every actual solution canonically generates a residue seed below `2*d`;
the seed's second coordinate is its exact natural quotient. -/
theorem labelFiber_exists_canonical_seed_of_solution
    (a d z q r : ℕ)
    (hd : 0 < d)
    (hsolution : 2 * d * r = a * q + z) :
    ∃ q₀ r₀ : ℕ,
      q₀ = q % (2 * d) ∧ q₀ < 2 * d ∧
        2 * d * r₀ = a * q₀ + z := by
  have hcoefficient : 0 < 2 * d := by omega
  have hdivisible : 2 * d ∣ a * q + z := by
    rw [← hsolution]
    exact dvd_mul_right _ _
  have hresidue :
      (a * (q % (2 * d)) + z) % (2 * d) =
        (a * q + z) % (2 * d) := by
    simp [Nat.add_mod, Nat.mul_mod]
  have hcanonical : 2 * d ∣ a * (q % (2 * d)) + z := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    rw [hresidue]
    exact Nat.dvd_iff_mod_eq_zero.mp hdivisible
  refine ⟨q % (2 * d), (a * (q % (2 * d)) + z) / (2 * d),
    rfl, Nat.mod_lt _ hcoefficient, ?_⟩
  exact Nat.mul_div_cancel' hcanonical

/-- A nonempty actual switched label fiber supplies both missing inputs of
the optimized fixed-label sieve: coefficient coprimality and a seed. -/
theorem labelFiber_exists_coprime_canonical_seed
    (S : Finset ℕ) (b : ℕ → ℕ) (n z a d : ℕ)
    (hd : 0 < d)
    (hz : Nat.Coprime z (2 * d))
    (hnonempty : (labelFiberSwitchedPrimeParameters S b n z a d).Nonempty) :
    Nat.Coprime a (2 * d) ∧
      ∃ q₀ r₀ : ℕ, q₀ < 2 * d ∧
        2 * d * r₀ = a * q₀ + z := by
  obtain ⟨q, hq⟩ := hnonempty
  obtain ⟨_, _, ⟨r, _, _, hsolution⟩, _, _⟩ :=
    (mem_labelFiberSwitchedPrimeParameters_iff S b n z a d q).mp hq
  refine ⟨labelFiber_coefficient_coprime_of_label_coprime
    a d z q r hz hsolution, ?_⟩
  obtain ⟨q₀, r₀, _, hq₀, hseed⟩ :=
    labelFiber_exists_canonical_seed_of_solution a d z q r hd hsolution
  exact ⟨q₀, r₀, hq₀, hseed⟩

#print axioms Erdos689.labelFiber_coefficient_coprime_of_label_coprime
#print axioms Erdos689.labelFiber_exists_canonical_seed_of_solution
#print axioms Erdos689.labelFiber_exists_coprime_canonical_seed

end Erdos689
