module

public import Mathlib


@[expose] public section

/-!
# Positive finite LCM and prime-support bounds

Shows that any finite set of positive natural moduli has a positive common
multiple `D.lcm id` and records prime-factor monotonicity under divisibility.
-/

namespace Erdos2.FiniteLcm

theorem positive_lcm (D : Finset ℕ) (hD : ∀ d ∈ D, 0 < d) :
    0 < D.lcm id := by
  apply Nat.pos_of_ne_zero
  exact Finset.lcm_ne_zero_iff.mpr (fun d hd => (hD d hd).ne')

theorem dvd_lcm_of_mem {D : Finset ℕ} {d : ℕ} (hd : d ∈ D) :
    d ∣ D.lcm id := Finset.dvd_lcm hd

theorem subset_lcm_divisors (D : Finset ℕ) (hD : ∀ d ∈ D, 0 < d) :
    D ⊆ (D.lcm id).divisors := by
  intro d hd
  exact Nat.mem_divisors.mpr ⟨dvd_lcm_of_mem hd, (positive_lcm D hD).ne'⟩

theorem exists_positive_common_multiple (D : Finset ℕ)
    (hD : ∀ d ∈ D, 0 < d) :
    ∃ Q : ℕ, 0 < Q ∧ (∀ d ∈ D, d ∣ Q) :=
  ⟨D.lcm id, positive_lcm D hD, fun _ hd => dvd_lcm_of_mem hd⟩

theorem empty_lcm : (∅ : Finset ℕ).lcm id = 1 := Finset.lcm_empty

theorem primeFactors_le_of_dvd {N d A : ℕ} (hN : N ≠ 0) (hd : d ∣ N)
    (hA : ∀ q ∈ N.primeFactors, q ≤ A) :
    ∀ q ∈ d.primeFactors, q ≤ A :=
  fun q hq => hA q (Nat.primeFactors_mono hd hN hq)

theorem positive_exponent_of_not_dvd {d Q m p j : ℕ}
    (hm : m ∣ Q) (hd : d = m * p ^ j) (hnot : ¬d ∣ Q) : 0 < j := by
  by_contra hj
  have hj0 : j = 0 := by omega
  apply hnot
  simpa [hd, hj0] using hm

end Erdos2.FiniteLcm
