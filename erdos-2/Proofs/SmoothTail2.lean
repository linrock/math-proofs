module

public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Tactic


@[expose] public section

/-!
# Uniform finite-tail bounds for smooth-number reciprocal sums

Applies Mathlib's Euler product theorem for smooth numbers to prove that the
reciprocals of $A$-smooth numbers are summable, and extracts a uniform threshold
$M$ above which any finite set of $A$-smooth moduli has reciprocal sum less
than $\varepsilon$.
-/

open scoped BigOperators

namespace Erdos2.SmoothTail

/-- Completely multiplicative reciprocal weights; zero is totalized to zero. -/
noncomputable def reciprocalHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' m n := by simp [mul_inv_rev, mul_comm]

@[simp] theorem reciprocalHom_apply (n : ℕ) :
    reciprocalHom n = (n : ℝ)⁻¹ := rfl

theorem reciprocalHom_prime_norm_lt_one {p : ℕ} (hp : p.Prime) :
    ‖reciprocalHom p‖ < 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [reciprocalHom_apply, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact inv_lt_one_of_one_lt₀ hp1

/-- Reciprocal weights are summable on every fixed smooth-number set.
This theorem makes no assertion that the unrestricted harmonic series converges. -/
theorem summable_smooth_reciprocals (N : ℕ) :
    Summable (fun m : N.smoothNumbers => (m.val : ℝ)⁻¹) := by
  have h :=
    (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
      reciprocalHom_prime_norm_lt_one N).1
  exact h.of_norm

/-- One natural cutoff controls every finite reciprocal tail with fixed
smoothness bound. Neither the cutoff nor the estimate depends on the finite set. -/
theorem uniform_finite_smooth_tail (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ D : Finset ℕ,
      (∀ n ∈ D, n ∈ N.smoothNumbers) →
      (∀ n ∈ D, M ≤ n) →
      ∑ n ∈ D, (n : ℝ)⁻¹ < ε := by
  classical
  obtain ⟨s, hs⟩ :=
    (summable_iff_vanishing_norm.mp (summable_smooth_reciprocals N)) ε hε
  refine ⟨s.sup Subtype.val + 1, by omega, ?_⟩
  intro D hDs hDM
  let T : Finset N.smoothNumbers := D.subtype (fun n => n ∈ N.smoothNumbers)
  have hdis : Disjoint T s := by
    apply Finset.disjoint_left.mpr
    intro m hmT hms
    have hmD : m.val ∈ D := Finset.mem_subtype.mp hmT
    have hlow := hDM m.val hmD
    have hupp : m.val ≤ s.sup Subtype.val := Finset.le_sup hms
    omega
  have htail := hs T hdis
  have hnonneg : 0 ≤ ∑ m ∈ T, (m.val : ℝ)⁻¹ := by
    apply Finset.sum_nonneg
    intro m hm
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at htail
  have hsum : (∑ m ∈ T, (m.val : ℝ)⁻¹) = ∑ n ∈ D, (n : ℝ)⁻¹ := by
    exact Finset.sum_subtype_of_mem (s := D) (p := fun n => n ∈ N.smoothNumbers)
      (fun n : ℕ => (n : ℝ)⁻¹) hDs
  rwa [hsum] at htail

/-- Inclusive prime-factor formulation used for the initial sieve event.
The positive cutoff itself excludes zero moduli. -/
theorem uniform_finite_primeFactors_tail (A : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ D : Finset ℕ,
      (∀ n ∈ D, ∀ p ∈ n.primeFactors, p ≤ A) →
      (∀ n ∈ D, M ≤ n) →
      ∑ n ∈ D, 1 / (n : ℝ) < ε := by
  obtain ⟨M, hM, htail⟩ := uniform_finite_smooth_tail (A + 1) hε
  refine ⟨M, hM, ?_⟩
  intro D hD hDM
  have hDs : ∀ n ∈ D, n ∈ (A + 1).smoothNumbers := by
    intro n hn
    have hn0 : n ≠ 0 := by have := hDM n hn; omega
    apply Nat.mem_smoothNumbers_of_primeFactors_subset hn0
    intro p hp
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hD n hn p hp))
  simpa only [one_div] using htail D hDs hDM

end Erdos2.SmoothTail
