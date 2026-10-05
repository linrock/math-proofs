module

public import Mathlib

@[expose] public section


/-!
# Unconditional finite structural facts for Erdős problem 689

Every result in this file is proved in Lean.  None of the analytic prime-counting
inputs used by the accompanying mathematical manuscript is asserted here.
-/

open scoped BigOperators

namespace Erdos689

/-- The exact closed-interval set of covering prime moduli. -/
def coveredPrimes (n : ℕ) (a : ℕ → ℕ) (m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun p => p.Prime ∧ a p ≡ m [MOD p]

/-- Coverage multiplicity, counting distinct primes only once. -/
def coverage (n : ℕ) (a : ℕ → ℕ) (m : ℕ) : ℕ :=
  (coveredPrimes n a m).card

/-- Replace the residue assigned to one prime. -/
def switch (a : ℕ → ℕ) (p r : ℕ) : ℕ → ℕ :=
  Function.update a p r

/-- An auxiliary support already gives two hits to all relevant multiples. -/
def robustSupport (n p : ℕ) (H : ℕ → ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → m ≤ n → p ∣ m → 2 ≤ H m

/-- An already-covered old residue class can afford to lose its prime. -/
def safePrime (n : ℕ) (a : ℕ → ℕ) (p : ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → m ≤ n → a p ≡ m [MOD p] → 3 ≤ coverage n a m

/-- Membership uses the closed interval, actual primality, and actual congruence. -/
theorem mem_coveredPrimes_iff {n m p : ℕ} {a : ℕ → ℕ} :
    p ∈ coveredPrimes n a m ↔
      1 ≤ p ∧ p ≤ n ∧ p.Prime ∧ a p ≡ m [MOD p] := by
  simp [coveredPrimes, and_assoc]

/-- The right endpoint is included whenever the interval is nonempty. -/
theorem right_endpoint_mem {n : ℕ} (hn : 1 ≤ n) :
    n ∈ Finset.Icc 1 n := by
  simp [hn]

/-- Universal coverage on the official interval includes its right endpoint. -/
theorem coverage_includes_right_endpoint {n : ℕ} {a : ℕ → ℕ}
    (hn : 1 ≤ n)
    (h : ∀ m ∈ Finset.Icc 1 n, 2 ≤ coverage n a m) :
    2 ≤ coverage n a n := by
  exact h n (right_endpoint_mem hn)

/-- Bounded-multiple robustness implies the divisor-based safety criterion. -/
theorem robust_of_multiple_hits {n p J : ℕ} {H : ℕ → ℕ}
    (hcutoff : n < (J + 1) * p)
    (hhits : ∀ j : ℕ, 1 ≤ j → j ≤ J → 2 ≤ H (j * p)) :
    robustSupport n p H := by
  intro m hm hn hdiv
  obtain ⟨j, hj⟩ := hdiv
  have hmj : m = j * p := by simpa [Nat.mul_comm] using hj
  have hjpos : 1 ≤ j := by
    by_contra h
    have hz : j = 0 := by omega
    simp [hmj, hz] at hm
  have hjbound : j ≤ J := by
    by_contra h
    have hlarge : J + 1 ≤ j := by omega
    have hmul : (J + 1) * p ≤ j * p :=
      Nat.mul_le_mul_right p hlarge
    omega
  simpa [hmj] using hhits j hjpos hjbound

/-- No robust prime divides a target with fewer than two auxiliary hits. -/
theorem robust_not_dvd_deficient {n p m : ℕ} {H : ℕ → ℕ}
    (hrobust : robustSupport n p H) (hm : 1 ≤ m) (hmn : m ≤ n)
    (hdeficient : H m < 2) : ¬ p ∣ m := by
  intro hdiv
  have := hrobust m hm hmn hdiv
  omega

/-- The residue chosen to repair a deficient target is necessarily nonzero. -/
theorem robust_target_residue_nonzero {n p m : ℕ} {H : ℕ → ℕ}
    (hrobust : robustSupport n p H) (hm : 1 ≤ m) (hmn : m ≤ n)
    (hdeficient : H m < 2) : m % p ≠ 0 := by
  intro hz
  exact robust_not_dvd_deficient hrobust hm hmn hdeficient
    (Nat.dvd_of_mod_eq_zero hz)

/-- The repair residue is an honest strictly positive residue below its prime. -/
theorem robust_target_residue_bounds {n p m : ℕ} {H : ℕ → ℕ}
    (hp : 0 < p) (hrobust : robustSupport n p H)
    (hm : 1 ≤ m) (hmn : m ≤ n) (hdeficient : H m < 2) :
    0 < m % p ∧ m % p < p := by
  constructor
  · exact Nat.pos_of_ne_zero
      (robust_target_residue_nonzero hrobust hm hmn hdeficient)
  · exact Nat.mod_lt m hp

/-- A prime assigned residue zero hits precisely its divisible targets. -/
theorem zero_class_hit_iff_dvd {a : ℕ → ℕ} {p m : ℕ} (ha : a p = 0) :
    (a p ≡ m [MOD p]) ↔ p ∣ m := by
  rw [ha]
  constructor
  · intro h
    exact Nat.modEq_zero_iff_dvd.mp h.symm
  · intro h
    exact (Nat.modEq_zero_iff_dvd.mpr h).symm

/-- Switching one modulus changes no other membership. -/
theorem coveredPrimes_erase_switch (n m p r : ℕ) (a : ℕ → ℕ) :
    (coveredPrimes n (switch a p r) m).erase p =
      (coveredPrimes n a m).erase p := by
  classical
  ext q
  simp only [Finset.mem_erase]
  constructor
  · rintro ⟨hqp, hcovered⟩
    refine ⟨hqp, ?_⟩
    rw [mem_coveredPrimes_iff] at hcovered ⊢
    simpa [switch, Function.update_of_ne hqp] using hcovered
  · rintro ⟨hqp, hcovered⟩
    refine ⟨hqp, ?_⟩
    rw [mem_coveredPrimes_iff] at hcovered ⊢
    simpa [switch, Function.update_of_ne hqp] using hcovered

/-- Every old covered prime other than the switched prime stays covered. -/
theorem old_erase_subset_new (n m p r : ℕ) (a : ℕ → ℕ) :
    (coveredPrimes n a m).erase p ⊆ coveredPrimes n (switch a p r) m := by
  intro q hq
  have hnew : q ∈ (coveredPrimes n (switch a p r) m).erase p := by
    rw [coveredPrimes_erase_switch]
    exact hq
  exact Finset.mem_of_mem_erase hnew

/-- A reassignment can destroy at most one old hit at any target. -/
theorem collateral_loss_at_most_one (n m p r : ℕ) (a : ℕ → ℕ) :
    coverage n a m ≤ coverage n (switch a p r) m + 1 := by
  classical
  let old := coveredPrimes n a m
  let new := coveredPrimes n (switch a p r) m
  have hsub : (old.erase p).card ≤ new.card :=
    Finset.card_le_card (old_erase_subset_new n m p r a)
  have hold : old.card ≤ (old.erase p).card + 1 := by
    by_cases hp : p ∈ old
    · have hc := Finset.card_erase_add_one hp
      omega
    · rw [Finset.erase_eq_self.mpr hp]
      omega
  change old.card ≤ new.card + 1
  omega

/-- If the old class missed a target, its coverage cannot decrease. -/
theorem no_collateral_loss_of_old_nonhit {n m p r : ℕ} {a : ℕ → ℕ}
    (hold : ¬ a p ≡ m [MOD p]) :
    coverage n a m ≤ coverage n (switch a p r) m := by
  classical
  have hnotmem : p ∉ coveredPrimes n a m := by
    intro hp
    exact hold (mem_coveredPrimes_iff.mp hp).2.2.2
  have herase : (coveredPrimes n a m).erase p = coveredPrimes n a m :=
    Finset.erase_eq_self.mpr hnotmem
  have hsub := old_erase_subset_new n m p r a
  rw [herase] at hsub
  exact Finset.card_le_card hsub

/-- Replacing a missed class by a class hitting the target adds exactly one hit. -/
theorem switching_gain_exactly_one {n m p r : ℕ} {a : ℕ → ℕ}
    (hp : p.Prime) (hpn : p ≤ n)
    (hold : ¬ a p ≡ m [MOD p]) (hnew : r ≡ m [MOD p]) :
    coverage n (switch a p r) m = coverage n a m + 1 := by
  classical
  have holdnot : p ∉ coveredPrimes n a m := by
    intro h
    exact hold (mem_coveredPrimes_iff.mp h).2.2.2
  have hnewmem : p ∈ coveredPrimes n (switch a p r) m := by
    apply mem_coveredPrimes_iff.mpr
    refine ⟨hp.one_le, hpn, hp, ?_⟩
    simpa [switch] using hnew
  have hcard := Finset.card_erase_add_one hnewmem
  rw [coveredPrimes_erase_switch, Finset.erase_eq_self.mpr holdnot] at hcard
  exact hcard.symm

/-- Safe switching cannot create a new target deficient below two hits. -/
theorem safe_switch_preserves_double {n m p r : ℕ} {a : ℕ → ℕ}
    (hsafe : safePrime n a p) (hm : 1 ≤ m) (hmn : m ≤ n)
    (hold : 2 ≤ coverage n a m) :
    2 ≤ coverage n (switch a p r) m := by
  by_cases hhit : a p ≡ m [MOD p]
  · have hmargin := hsafe m hm hmn hhit
    have hloss := collateral_loss_at_most_one n m p r a
    omega
  · exact Nat.le_trans hold (no_collateral_loss_of_old_nonhit hhit)

/-- Two immutable auxiliary hits plus the old zero-class hit imply safe switching. -/
theorem robust_zero_class_is_safe {n p : ℕ} {a : ℕ → ℕ} {H : ℕ → ℕ}
    (ha : a p = 0) (hrobust : robustSupport n p H)
    (hsupport : ∀ m : ℕ, 1 ≤ m → m ≤ n → p ∣ m →
      H m + 1 ≤ coverage n a m) :
    safePrime n a p := by
  intro m hm hmn hhit
  have hdiv : p ∣ m := (zero_class_hit_iff_dvd ha).mp hhit
  have htwo := hrobust m hm hmn hdiv
  have hplus := hsupport m hm hmn hdiv
  omega

/-- A robust zero class repairs a deficient target by exactly one hit. -/
theorem robust_reassignment_repairs_target {n p m : ℕ} {a : ℕ → ℕ}
    {H : ℕ → ℕ} (hp : p.Prime) (hpn : p ≤ n) (ha : a p = 0)
    (hrobust : robustSupport n p H) (hm : 1 ≤ m) (hmn : m ≤ n)
    (hdeficient : H m < 2) :
    coverage n (switch a p (m % p)) m = coverage n a m + 1 := by
  apply switching_gain_exactly_one hp hpn
  · intro hhit
    exact robust_not_dvd_deficient hrobust hm hmn hdeficient
      ((zero_class_hit_iff_dvd ha).mp hhit)
  · exact Nat.mod_modEq m p

/-- The two half-targets in a hyperedge determine the same repair residue. -/
theorem paired_targets_same_residue {A B P : ℕ} (h : B = A + P) :
    2 * A ≡ 2 * B [MOD P] := by
  simp [Nat.ModEq, h, Nat.mul_add, Nat.add_mod]

/-- An odd and an even half-target cannot represent the same target. -/
theorem odd_even_half_targets_distinct {A B : ℕ}
    (hodd : A % 2 = 1) (heven : B % 2 = 0) : A ≠ B := by
  intro h
  subst B
  omega

/-- Distinct half-targets give distinct doubled targets. -/
theorem doubled_targets_distinct {A B : ℕ} (h : A ≠ B) :
    2 * A ≠ 2 * B := by
  intro heq
  exact h (by omega)

/-- Correct collateral bookkeeping uses an inequality, not an equality. -/
theorem cleanup_ledger {D R k remaining : ℕ}
    (hkR : k ≤ R) (hkD : 2 * k ≤ D)
    (hremaining : remaining ≤ D - 2 * k)
    (hsurplus : D ≤ R + k) :
    remaining ≤ R - k := by
  omega

/-- A strict ledger surplus leaves a genuinely unused repair prime. -/
theorem cleanup_ledger_strict {D R k remaining : ℕ}
    (hkR : k ≤ R) (hkD : 2 * k ≤ D)
    (hremaining : remaining ≤ D - 2 * k)
    (hsurplus : D < R + k) :
    remaining < R - k := by
  omega

/-- Exact switched-prime selector cancellation for the first vertex classes. -/
theorem selector_factor_identity (s : ℝ) (hs : s ≠ 1) :
    s * (s - 3) / (s - 1) ^ 2 + 1 / (s - 1) =
      1 - 2 / (s - 1) ^ 2 := by
  field_simp
  ring

/-- Exact switched-prime cancellation when the fixed vertex is divisible. -/
theorem divisible_selector_factor_identity (s : ℝ) (hs : s ≠ 1) :
    s * (s - 2) / (s - 1) ^ 2 = 1 - 1 / (s - 1) ^ 2 := by
  field_simp
  ring

/-- The exceptional-prime deletion factor is uniformly at most five thirds. -/
theorem exceptional_deletion_factor_bound {q : ℝ} (hq : 5 ≤ q) :
    1 + 2 / (q - 2) ≤ 5 / 3 := by
  have hpos : 0 < q - 2 := by linarith
  have hfrac : 2 / (q - 2) ≤ (2 : ℝ) / 3 := by
    apply (div_le_iff₀ hpos).mpr
    nlinarith
  linarith

/-- The outside-prime Euler factor used in the degree estimate is bounded. -/
theorem exceptional_euler_factor_bound {q : ℝ} (hq : 5 ≤ q) :
    q / (q - 1) ≤ 5 / 4 := by
  have hpos : 0 < q - 1 := by linarith
  apply (div_le_iff₀ hpos).mpr
  linarith

/-- The advertised leading Selberg degree constant is exact rational arithmetic. -/
theorem leading_degree_constant :
    (2048 : ℚ) * (3 / 2) * (5 / 4) = 3840 := by
  norm_num

/-- Doubling the leading constant absorbs sufficiently small asymptotic errors. -/
theorem degree_constant_slack : (3840 : ℕ) < 7680 := by
  norm_num

/-- The parameter product in the final ledger has the stated exact expansion. -/
theorem parameter_product_identity (t : ℝ) :
    (1 - t / 10) * (1 + 9 * t / 10) = 1 + 4 * t / 5 - 9 * t ^ 2 / 100 := by
  ring

/-- Every positive parameter below one yields strict rational surplus. -/
theorem parameter_product_surplus {t : ℝ} (ht : 0 < t) (htone : t < 1) :
    1 < (1 - t / 10) * (1 + 9 * t / 10) := by
  rw [parameter_product_identity]
  nlinarith [mul_pos ht (by linarith : 0 < 80 - 9 * t)]

/-- The precise strict inequalities from the manuscript imply usable surplus. -/
theorem final_parameter_surplus {δ τ t : ℝ}
    (ht : 0 < t) (htone : t < 1)
    (hτ : τ < t / 10) (hδ : 1 - t / 10 < δ) :
    1 < δ * (1 - τ + t) := by
  have hbase : 0 < 1 - t / 10 := by linarith
  have hfactor : 0 < 1 - τ + t := by linarith
  have himprove : 1 + 9 * t / 10 < 1 - τ + t := by linarith
  have hfirst : (1 - t / 10) * (1 + 9 * t / 10) <
      (1 - t / 10) * (1 - τ + t) := by
    exact mul_lt_mul_of_pos_left himprove hbase
  have hsecond : (1 - t / 10) * (1 - τ + t) < δ * (1 - τ + t) := by
    exact mul_lt_mul_of_pos_right hδ hfactor
  exact (parameter_product_surplus ht htone).trans (hfirst.trans hsecond)

end Erdos689

