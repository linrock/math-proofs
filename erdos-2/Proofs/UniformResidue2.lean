module

public import ProductUpdate2
public import FiniteWeight2
public import CongruenceGeometry2
public import Mathlib


@[expose] public section

/-!
# Uniform probability weight on `ZMod N` and union mass bounds

Defines the uniform probability weight `uniform N` on `ZMod N`, proves that
each congruence class modulo $d \mid N$ has mass $1/d \le 2^{\omega(d)}/d$, and
bounds the uniform mass of a union of congruence classes by $\sum_i 1/d_i$.
-/

open scoped BigOperators

namespace Erdos2.UniformResidue

noncomputable def uniform (N : ℕ) [NeZero N] :
    ProductProbability.ProbabilityWeight (ZMod N) where
  value _ := 1 / (N : ℝ)
  nonneg _ := by positivity
  normalized := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ZMod.card]
    exact mul_one_div_cancel (by exact_mod_cast (NeZero.ne N))

@[simp] theorem uniform_value (N : ℕ) [NeZero N] (x : ZMod N) :
    (uniform N).value x = 1 / (N : ℝ) := rfl

theorem uniform_mass_eq_card_div {N : ℕ} [NeZero N] (S : Finset (ZMod N)) :
    FiniteWeight.mass (uniform N).value S = (S.card : ℝ) / (N : ℝ) := by
  unfold FiniteWeight.mass
  simp only [uniform_value, Finset.sum_const, nsmul_eq_mul]
  ring

theorem uniform_progression_mass {N d : ℕ} [NeZero N]
    (hd : d ∣ N) (a : ℤ) :
    FiniteWeight.mass (uniform N).value
      (Finset.univ.filter (fun x : ZMod N =>
        ZMod.castHom hd (ZMod d) x = (a : ZMod d))) = 1 / (d : ℝ) := by
  have _ : NeZero d := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne N) hd⟩
  rw [uniform_mass_eq_card_div]
  exact CongruenceGeometry.reduction_uniform_fraction hd (a : ZMod d)

theorem uniform_progression_bound {N d : ℕ} [NeZero N]
    (hd : d ∣ N) (a : ℤ) :
    FiniteWeight.mass (uniform N).value
      (Finset.univ.filter (fun x : ZMod N =>
        ZMod.castHom hd (ZMod d) x = (a : ZMod d))) ≤
      (2 : ℝ) ^ d.primeFactors.card / (d : ℝ) := by
  rw [uniform_progression_mass]
  exact div_le_div_of_nonneg_right (one_le_pow₀ (by norm_num)) (by positivity)

theorem uniform_union_mass_le {ι : Type*} {N : ℕ} [NeZero N]
    (s : Finset ι) (d : ι → ℕ) (a : ι → ℤ) (hdiv : ∀ i, d i ∣ N) :
    FiniteWeight.mass (uniform N).value
      (s.biUnion (fun i => Finset.univ.filter (fun x : ZMod N =>
        ZMod.castHom (hdiv i) (ZMod (d i)) x = (a i : ZMod (d i))))) ≤
      ∑ i ∈ s, 1 / (d i : ℝ) := by
  classical
  let C : ι → Finset (ZMod N) := fun i =>
    Finset.univ.filter (fun x : ZMod N =>
      ZMod.castHom (hdiv i) (ZMod (d i)) x = (a i : ZMod (d i)))
  change FiniteWeight.mass (uniform N).value (s.biUnion C) ≤ _
  rw [uniform_mass_eq_card_div]
  have hc : (s.biUnion C).card ≤ ∑ i ∈ s, (C i).card := Finset.card_biUnion_le
  calc
    ((s.biUnion C).card : ℝ) / (N : ℝ) ≤
        ((∑ i ∈ s, (C i).card : ℕ) : ℝ) / (N : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hc
    _ = ∑ i ∈ s, ((C i).card : ℝ) / (N : ℝ) := by
      rw [Nat.cast_sum, Finset.sum_div]
    _ = ∑ i ∈ s, 1 / (d i : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (uniform_mass_eq_card_div (C i)).symm.trans
        (uniform_progression_mass (hdiv i) (a i))

end Erdos2.UniformResidue
