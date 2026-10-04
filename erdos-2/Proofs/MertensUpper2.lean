module

public import Mathlib
public import PrimeNumberTheoremAnd.IEANTN.Mertens


@[expose] public section

/-!
# Uniform logarithmic upper bound for finite Euler products via Mertens' third theorem

Uses Mertens' third theorem (`Mertens.prod_one_minus_div_prime_eq` and
`Mertens.E₃.abs_le`) to show that $\prod_{q \le p} q/(q - 1) \le C \log p$ for
all $p \ge 2$, and deduces a uniform $O((\log p)^6)$ bound for the sixth-power
Euler product over any finite set of primes $q < p$.
-/

open scoped BigOperators
open Filter Asymptotics Topology

namespace Erdos2.Analytic

noncomputable def inverseEuler (p : ℕ) : ℝ :=
  ∏ q ∈ (Finset.Ioc 0 p).filter Nat.Prime, ((q : ℝ) / ((q : ℝ) - 1))

theorem inverseEuler_eq_inverse_closed_product (p : ℕ) :
    inverseEuler p = (∏ q ∈ (Finset.Ioc 0 p).filter Nat.Prime,
      (1 - 1 / (q : ℝ)))⁻¹ := by
  rw [inverseEuler, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro q hq
  have hprime : Nat.Prime q := (Finset.mem_filter.mp hq).2
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hprime.ne_zero
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hprime.two_le
  have hq1 : (q : ℝ) - 1 ≠ 0 := by linarith
  field_simp

theorem inverseEuler_uniform_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, 2 ≤ p →
      inverseEuler p ≤ C * Real.log (p : ℝ) := by
  obtain ⟨K, hK⟩ := Mertens.E₃.abs_le
  let B : ℝ := max K 0 / Real.log 2
  let C : ℝ := Real.exp Real.eulerMascheroniConstant * Real.exp B
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) < p := by linarith
  have hpPos : (0 : ℝ) < p := by linarith
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hlog2p : Real.log (2 : ℝ) ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by norm_num) hp2
  have herr : |Mertens.E₃ (p : ℝ)| ≤ B := by
    calc
      _ ≤ K / Real.log (p : ℝ) := hK _ hp2
      _ ≤ max K 0 / Real.log (p : ℝ) :=
        div_le_div_of_nonneg_right (le_max_left _ _) hlogp.le
      _ ≤ _ := div_le_div_of_nonneg_left (le_max_right _ _) hlog2 hlog2p
  have hexp : Real.exp (-Mertens.E₃ (p : ℝ)) ≤ Real.exp B :=
    Real.exp_le_exp.mpr (by linarith [(abs_le.mp herr).1])
  have hclosed := Mertens.prod_one_minus_div_prime_eq hp1
  simp only [Nat.floor_natCast] at hclosed
  rw [inverseEuler_eq_inverse_closed_product, hclosed]
  have heq : (Real.exp (-Real.eulerMascheroniConstant) *
      Real.exp (Mertens.E₃ (p : ℝ)) / Real.log (p : ℝ))⁻¹ =
      Real.exp Real.eulerMascheroniConstant * Real.exp (-Mertens.E₃ (p : ℝ)) *
        Real.log (p : ℝ) := by
    rw [Real.exp_neg, Real.exp_neg]
    field_simp
  rw [heq]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le) hlogp.le

theorem finitePrimeProduct_uniform_log_bound (f : ℕ → ℝ)
    (hf : ∀ q : ℕ, Nat.Prime q →
      0 ≤ f q ∧ f q ≤ ((q : ℝ) / ((q : ℝ) - 1)) ^ 6) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, 2 ≤ p →
      ∀ s : Finset ℕ, (∀ q ∈ s, Nat.Prime q ∧ q < p) →
        (∏ q ∈ s, f q) ≤ C * Real.log (p : ℝ) ^ 6 := by
  obtain ⟨K, hK, hEuler⟩ := inverseEuler_uniform_log_bound
  refine ⟨K ^ 6, pow_pos hK _, ?_⟩
  intro p hp s hs
  let t : Finset ℕ := (Finset.Ioc 0 p).filter Nat.Prime
  have hst : s ⊆ t := by
    intro q hqs
    have h := hs q hqs
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨h.1.pos, h.2.le⟩, h.1⟩
  have hq2 (q : ℕ) (hqt : q ∈ t) : (2 : ℝ) ≤ q := by
    exact_mod_cast (Finset.mem_filter.mp hqt).2.two_le
  have hqpos (q : ℕ) (hqt : q ∈ t) :
      0 ≤ (q : ℝ) / ((q : ℝ) - 1) :=
    div_nonneg (Nat.cast_nonneg q) (by linarith [hq2 q hqt])
  have hsubset :
      (∏ q ∈ s, ((q : ℝ) / ((q : ℝ) - 1)) ^ 6) ≤
      (∏ q ∈ t, ((q : ℝ) / ((q : ℝ) - 1)) ^ 6) := by
    apply Finset.prod_le_prod_of_subset_of_one_le₀ hst
    · intro q hqs
      exact pow_nonneg (hqpos q (hst hqs)) _
    · intro q hqt _
      have hOne : 1 ≤ (q : ℝ) / ((q : ℝ) - 1) := by
        apply (le_div_iff₀ (by linarith [hq2 q hqt])).mpr
        linarith
      exact one_le_pow₀ hOne
  have hEulerNonneg : 0 ≤ inverseEuler p := by
    exact Finset.prod_nonneg fun q hqt => hqpos q hqt
  calc
    _ ≤ ∏ q ∈ s, (((q : ℝ) / ((q : ℝ) - 1)) ^ 6) :=
      Finset.prod_le_prod₀ (fun q hqs => (hf q (hs q hqs).1).1)
        (fun q hqs => (hf q (hs q hqs).1).2)
    _ ≤ ∏ q ∈ t, (((q : ℝ) / ((q : ℝ) - 1)) ^ 6) := hsubset
    _ = inverseEuler p ^ 6 := by rw [Finset.prod_pow]; rfl
    _ ≤ (K * Real.log (p : ℝ)) ^ 6 :=
      pow_le_pow_left₀ hEulerNonneg (hEuler p hp) 6
    _ = _ := mul_pow _ _ _

theorem uniform_finite_tail_of_summable (f : ℕ → ℝ)
    (hf : Summable f) (hpos : ∀ n : ℕ, 0 ≤ f n)
    (ε : ℝ) (hε : 0 < ε) (B : ℕ) :
    ∃ A : ℕ, B ≤ A ∧ ∀ s : Finset ℕ,
      (∀ n ∈ s, A ≤ n) → (∑ n ∈ s, f n) < ε := by
  have hsmall : ∀ᶠ A : ℕ in atTop, (∑' n : ℕ, f (n + A)) < ε :=
    (tendsto_sum_nat_add f).eventually_lt_const hε
  obtain ⟨A₀, hA₀⟩ := eventually_atTop.mp hsmall
  let A : ℕ := max A₀ B
  refine ⟨A, le_max_right _ _, ?_⟩
  intro s hs
  have hinj : ∀ n ∈ s, ∀ m ∈ s, n - A = m - A → n = m := by
    intro n hn m hm hnm
    have hna := hs n hn
    have hma := hs m hm
    omega
  have heq : (∑ n ∈ s.image (fun n => n - A), f (n + A)) =
      (∑ n ∈ s, f n) := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Nat.sub_add_cancel (hs n hn)]
  have hshift : Summable (fun n : ℕ => f (n + A)) :=
    (summable_nat_add_iff A).mpr hf
  rw [← heq]
  exact lt_of_le_of_lt
    (hshift.sum_le_tsum _ (fun n _ => hpos (n + A)))
    (hA₀ A (le_max_left _ _))

end Erdos2.Analytic
