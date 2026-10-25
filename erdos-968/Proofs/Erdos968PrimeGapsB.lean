module

/-
Copyright 2025-2026 The Formal Conjectures Authors.
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

public import Mathlib
public import Erdos968PrimeGapsA

@[expose] public section

section File_OpenAIPrimeGaps_ContourSums

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

noncomputable def fourierCoordinateSum (ι : Type*) [Fintype ι] : EuclideanSpace ℝ ι →L[ℝ] ℝ :=
  ∑ i, EuclideanSpace.proj i

@[simp] theorem fourierCoordinateSum_apply {ι : Type*} [Fintype ι] (v : EuclideanSpace ℝ ι) :
    fourierCoordinateSum ι v = ∑ i, v i := by simp [fourierCoordinateSum]

noncomputable def divisorLogVector {ι : Type*} (L : ℝ) (d : ι → ℕ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => Real.log (d i)/L)

@[simp] theorem divisorLogVector_apply {ι : Type*} (L : ℝ) (d : ι → ℕ) (i : ι) :
    divisorLogVector L d i = Real.log (d i)/L := rfl

noncomputable def fourierContour {ι : Type*} (L : ℝ) (u : EuclideanSpace ℝ ι) (i : ι) : ℂ :=
  (1+Complex.I*(u i : ℂ))/(L:ℂ)

@[simp] theorem fourierContour_re {ι : Type*} (L : ℝ) (u : EuclideanSpace ℝ ι) (i : ι) :
    (fourierContour L u i).re = L⁻¹ := by
  simp [fourierContour, Complex.div_ofReal_re]

theorem tupleFourierCoefficient_norm_eq_of_re {ι : Type*} [Fintype ι] (δ : ℕ) (d : ι → ℕ)
    (z w : ι → ℂ) (h : ∀ i, (z i).re=(w i).re) :
    ‖tupleFourierCoefficient δ d z‖ = ‖tupleFourierCoefficient δ d w‖ := by
  simp only [tupleFourierCoefficient, norm_mul, Complex.norm_exp, Complex.neg_re,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, h]

theorem tupleFourierCoefficient_contour_norm {ι : Type*} [Fintype ι] (δ : ℕ) (d : ι → ℕ)
    (L : ℝ) (u : EuclideanSpace ℝ ι) :
    ‖tupleFourierCoefficient δ d (fourierContour L u)‖ =
      ‖tupleFourierCoefficient δ d (fun _ => (L⁻¹:ℝ))‖ := by
  apply tupleFourierCoefficient_norm_eq_of_re
  intro i
  simp

theorem continuous_tupleFourierCoefficient_contour {ι : Type*} [Fintype ι]
    (δ : ℕ) (d : ι → ℕ) (L : ℝ) :
    Continuous (fun u : EuclideanSpace ℝ ι => tupleFourierCoefficient δ d (fourierContour L u)) := by
  unfold tupleFourierCoefficient fourierContour
  fun_prop

theorem contour_sum_log_eq {ι : Type*} [Fintype ι] (L : ℝ) (d : ι → ℕ)
    (u : EuclideanSpace ℝ ι) :
    (∑ i, (Real.log (d i):ℂ)*fourierContour L u i) =
      (fourierCoordinateSum ι (divisorLogVector L d) : ℂ) +
        Complex.I*(inner ℝ u (divisorLogVector L d) : ℂ) := by
  simp only [fourierCoordinateSum_apply, Complex.ofReal_sum, PiLp.inner_apply,
    Real.inner_apply, divisorLogVector_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [fourierContour, Complex.ofReal_mul, Complex.ofReal_inv, div_eq_mul_inv]
  ring

theorem integral_sourceFourier_tupleCoefficient {ι : Type*} [Fintype ι]
    (δ : ℕ) (d : ι → ℕ) (L : ℝ) (F : EuclideanSpace ℝ ι → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    (∫ u : EuclideanSpace ℝ ι, sourceFourier (fourierCoordinateSum ι) F hF hFs u *
      tupleFourierCoefficient δ d (fourierContour L u)) =
    tuplePrimeDensity δ d * (∏ i, (ArithmeticFunction.moebius (d i):ℂ)) *
      F (divisorLogVector L d) := by
  simp only [tupleFourierCoefficient, contour_sum_log_eq, neg_add_rev]
  rw [← sourceFourier_inversion (fourierCoordinateSum ι) F hF hFs (divisorLogVector L d),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [sub_eq_add_neg]
  ring_nf

theorem integrable_sourceFourier_tupleCoefficient {ι : Type*} [Fintype ι]
    (δ : ℕ) (d : ι → ℕ) (L : ℝ) (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    Integrable (fun u => Φ u * tupleFourierCoefficient δ d (fourierContour L u)) := by
  apply Φ.integrable.mul_bdd (continuous_tupleFourierCoefficient_contour δ d L).aestronglyMeasurable
  filter_upwards [] with u
  exact (tupleFourierCoefficient_contour_norm δ d L u).le

noncomputable def analyticDensity {ι : Type*} [Fintype ι] (δ : ℕ)
    (A : ℕ → Finset (Finset ι)) (L : ℝ) (F : EuclideanSpace ℝ ι → ℂ) : ℂ :=
  ∑' d : AllowedDivisorTuple A,
    tuplePrimeDensity δ d.val * (∏ i, (ArithmeticFunction.moebius (d.val i):ℂ)) *
      F (divisorLogVector L d.val)

theorem analyticDensity_eq_integral {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) {L : ℝ} (hL : 0<L)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R)
    (F : EuclideanSpace ℝ ι → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    analyticDensity δ A L F =
      ∫ u : EuclideanSpace ℝ ι, sourceFourier (fourierCoordinateSum ι) F hF hFs u *
        ∑' d : AllowedDivisorTuple A, tupleFourierCoefficient δ d.val (fourierContour L u) := by
  let : Countable (AllowedDivisorTuple A) := by unfold AllowedDivisorTuple; infer_instance
  let Φ := sourceFourier (fourierCoordinateSum ι) F hF hFs
  have hs := tupleFourier_summable_norm hδ A (fun _ => (L⁻¹:ℝ)) (inv_pos.mpr hL)
    hA hR (fun _ => le_rfl)
  have hint (d : AllowedDivisorTuple A) :
      Integrable (fun u => Φ u * tupleFourierCoefficient δ d.val (fourierContour L u)) :=
    integrable_sourceFourier_tupleCoefficient δ d.val L Φ
  have hsum : Summable (fun d : AllowedDivisorTuple A =>
      ∫ u : EuclideanSpace ℝ ι, ‖Φ u*tupleFourierCoefficient δ d.val (fourierContour L u)‖) := by
    simp_rw [norm_mul, tupleFourierCoefficient_contour_norm, integral_mul_const]
    exact hs.mul_left _
  have he := (hasSum_integral_of_summable_integral_norm hint hsum).tsum_eq
  simp only [integral_sourceFourier_tupleCoefficient, Φ] at he
  rw [analyticDensity, he]
  apply integral_congr_ae
  filter_upwards [] with u
  exact tsum_mul_left

theorem allowed_residue_iff {ι : Type*} [Fintype ι] (d b : ι → ℕ) :
    (∀ p : Nat.Primes, (tuplePrimeSubset d p).Nonempty →
      tuplePrimeSubset d p∈residueFamily (fun i => (b i:ℤ)) p) ↔ localCompatible d b := by
  constructor
  · intro h p hp _ i j hi hj
    have hm := h ⟨p,hp⟩ ⟨i,by simp [tuplePrimeSubset,hi]⟩
    rw [residueFamily, mem_fiberSubsetFamily_image] at hm
    have he := hm.2 i (by simp [tuplePrimeSubset,hi]) j (by simp [tuplePrimeSubset,hj])
    change b i % p = b j % p
    exact_mod_cast he
  · intro h p hp
    rw [residueFamily, mem_fiberSubsetFamily_image]
    refine ⟨hp,?_⟩
    intro i hi j hj
    have hi' : p.val∣d i := by simpa [tuplePrimeSubset] using hi
    have hj' : p.val∣d j := by simpa [tuplePrimeSubset] using hj
    have hq : p.val∣tupleModulus d := hi'.trans (Finset.dvd_lcm (Finset.mem_univ i))
    have he : b i % p.val=b j % p.val := h p.val p.property hq i j hi' hj'
    exact_mod_cast he

theorem allowed_marked_residue_iff {ι : Type*} [Fintype ι] (d b : ι → ℕ) (a : ℕ) :
    (∀ p : Nat.Primes, (tuplePrimeSubset d p).Nonempty →
      tuplePrimeSubset d p∈markedResidueFamily (fun i => (b i:ℤ)) p a) ↔
      markedLocalCompatible d b a := by
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · apply (allowed_residue_iff d b).mp
      intro p hp
      have hm := (mem_markedResidueFamily _ _ _ _).mp (h p hp)
      rw [residueFamily,mem_fiberSubsetFamily_image]
      exact ⟨hm.1,hm.2.1⟩
    · intro p hp _ i hi he
      have hm := (mem_markedResidueFamily _ _ _ _).mp
        (h ⟨p,hp⟩ ⟨i,by simp [tuplePrimeSubset,hi]⟩)
      apply hm.2.2 i (by simp [tuplePrimeSubset,hi])
      change b i % p=a % p at he
      exact_mod_cast he
  · rintro ⟨h,hmark⟩ p hp
    rw [mem_markedResidueFamily]
    have hu := (allowed_residue_iff d b).mpr h p hp
    rw [residueFamily,mem_fiberSubsetFamily_image] at hu
    refine ⟨hu.1,hu.2,?_⟩
    intro i hi he
    have hi' : p.val∣d i := by simpa [tuplePrimeSubset] using hi
    apply hmark p.val p.property (hi'.trans (Finset.dvd_lcm (Finset.mem_univ i))) i hi'
    change b i % p.val=a % p.val
    exact_mod_cast he

theorem analyticDensity_eq_unmarked_tsum {n : ℕ} (X : ℕ)
    (F : (Fin n → ℝ) → ℝ) (b : Fin n → ℕ) :
    analyticDensity 0 (residueFamily (fun i => (b i:ℤ))) (Real.log X)
      (fun v => (F v.ofLp:ℂ)) =
      ∑' d : Fin n → ℕ, ((divisorCoefficient X F d * tupleDensity d b : ℝ):ℂ) := by
  let P := fun d : Fin n → ℕ => (∀ i, Squarefree (d i)) ∧
    ∀ p : Nat.Primes, (tuplePrimeSubset d p).Nonempty →
      tuplePrimeSubset d p∈residueFamily (fun i => (b i:ℤ)) p
  change (∑' d : {d // P d}, tuplePrimeDensity 0 d.val *
    (∏ i, (ArithmeticFunction.moebius (d.val i):ℂ)) *
      (F (divisorLogVector (Real.log X) d.val).ofLp:ℂ)) = _
  refine (tsum_subtype {d | P d} (fun d => tuplePrimeDensity 0 d *
    (∏ i, (ArithmeticFunction.moebius (d i):ℂ)) *
      (F (divisorLogVector (Real.log X) d).ofLp:ℂ))).trans ?_
  apply tsum_congr
  intro d
  by_cases hd : P d
  · rw [Set.indicator_of_mem (show d ∈ {d | P d} from hd), tuplePrimeDensity_zero hd.1]
    have hc := (tupleCompatible_iff_localCompatible hd.1).mpr ((allowed_residue_iff d b).mp hd.2)
    simp only [divisorCoefficient,tupleDensity,ite_eq_left hc,Complex.ofReal_mul,
      Complex.ofReal_prod,Complex.ofReal_intCast,Complex.ofReal_inv,Complex.ofReal_natCast]
    change (tupleModulus d : ℂ)⁻¹ * (∏ i, (ArithmeticFunction.moebius (d i):ℂ)) *
      (F (logCoordinates X d):ℂ) = _
    ring
  · rw [Set.indicator_of_notMem (show d ∉ {d | P d} from hd)]
    have hv : divisorCoefficient X F d * tupleDensity d b = 0 := by
      by_contra hv
      have hf := (divisorCoefficient_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).1
      have hc : tupleCompatible d b := by
        by_contra hc
        exact (mul_ne_zero_iff.mp hv).2 (by simp [tupleDensity,hc])
      exact hd ⟨hf,(allowed_residue_iff d b).mpr
        ((tupleCompatible_iff_localCompatible hf).mp hc)⟩
    rw [hv,Complex.ofReal_zero]

theorem analyticDensity_eq_marked_tsum {n : ℕ} (X : ℕ)
    (F : (Fin n → ℝ) → ℝ) (b : Fin n → ℕ) (a : ℕ) :
    analyticDensity 1 (fun p => markedResidueFamily (fun i => (b i:ℤ)) p a) (Real.log X)
      (fun v => (F v.ofLp:ℂ)) =
      ∑' d : Fin n → ℕ, ((divisorCoefficient X F d * markedTupleDensity d b a : ℝ):ℂ) := by
  let P := fun d : Fin n → ℕ => (∀ i, Squarefree (d i)) ∧
    ∀ p : Nat.Primes, (tuplePrimeSubset d p).Nonempty →
      tuplePrimeSubset d p∈markedResidueFamily (fun i => (b i:ℤ)) p a
  change (∑' d : {d // P d}, tuplePrimeDensity 1 d.val *
    (∏ i, (ArithmeticFunction.moebius (d.val i):ℂ)) *
      (F (divisorLogVector (Real.log X) d.val).ofLp:ℂ)) = _
  refine (tsum_subtype {d | P d} (fun d => tuplePrimeDensity 1 d *
    (∏ i, (ArithmeticFunction.moebius (d i):ℂ)) *
      (F (divisorLogVector (Real.log X) d).ofLp:ℂ))).trans ?_
  apply tsum_congr
  intro d
  by_cases hd : P d
  · rw [Set.indicator_of_mem (show d ∈ {d | P d} from hd), tuplePrimeDensity_one hd.1]
    have hc := (markedTupleCompatible_iff_local hd.1).mpr ((allowed_marked_residue_iff d b a).mp hd.2)
    simp only [divisorCoefficient,markedTupleDensity,ite_eq_left hc,Complex.ofReal_mul,
      Complex.ofReal_prod,Complex.ofReal_intCast,Complex.ofReal_inv,Complex.ofReal_natCast]
    change ((tupleModulus d).totient : ℂ)⁻¹ * (∏ i, (ArithmeticFunction.moebius (d i):ℂ)) *
      (F (logCoordinates X d):ℂ) = _
    ring
  · rw [Set.indicator_of_notMem (show d ∉ {d | P d} from hd)]
    have hv : divisorCoefficient X F d * markedTupleDensity d b a = 0 := by
      by_contra hv
      have hf := (divisorCoefficient_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).1
      have hc : markedTupleCompatible d b a := by
        by_contra hc
        exact (mul_ne_zero_iff.mp hv).2 (by simp [markedTupleDensity,hc])
      exact hd ⟨hf,(allowed_marked_residue_iff d b a).mpr
        ((markedTupleCompatible_iff_local hf).mp hc)⟩
    rw [hv,Complex.ofReal_zero]

theorem divisorCoefficient_support {n X : ℕ} (hX : 2≤X)
    {F : (Fin n → ℝ) → ℝ} {rho : ℝ} (hbudget : HasBudget F rho)
    {d : Fin n → ℕ} (hd : divisorCoefficient X F d≠0) :
    d ∈ positiveProductTuples n ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊ := by
  obtain ⟨hsq,hF⟩ := divisorCoefficient_ne_zero_iff.mp hd
  have hp : ∀ i, 0<d i := fun i => Nat.pos_of_ne_zero (hsq i).ne_zero
  refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_,?_⟩
  · intro i
    exact Finset.mem_Icc.mpr ⟨hp i,divisor_coordinate_bound hX hbudget hp hF i⟩
  · exact (Nat.le_floor_iff (Real.exp_pos _).le).mpr (divisor_product_bound hX hbudget hp hF)

theorem analyticDensity_eq_unmarkedDensitySum {n X : ℕ} (hX : 2≤X)
    {F : (Fin n → ℝ) → ℝ} {rho : ℝ} (hbudget : HasBudget F rho) (b : Fin n → ℕ) :
    analyticDensity 0 (residueFamily (fun i => (b i:ℤ))) (Real.log X)
      (fun v => (F v.ofLp:ℂ)) = (unmarkedDensitySum X F rho b : ℂ) := by
  rw [analyticDensity_eq_unmarked_tsum,unmarkedDensitySum,Complex.ofReal_sum]
  apply tsum_eq_sum
  intro d hd
  have hc : divisorCoefficient X F d=0 := by
    by_contra hc
    exact hd (divisorCoefficient_support hX hbudget hc)
  simp only [hc,zero_mul,Complex.ofReal_zero]

theorem analyticDensity_eq_markedDensitySum {n X : ℕ} (hX : 2≤X)
    {F : (Fin n → ℝ) → ℝ} {rho : ℝ} (hbudget : HasBudget F rho) (b : Fin n → ℕ) (a : ℕ) :
    analyticDensity 1 (fun p => markedResidueFamily (fun i => (b i:ℤ)) p a) (Real.log X)
      (fun v => (F v.ofLp:ℂ)) = (markedDensitySum X F rho b a : ℂ) := by
  rw [analyticDensity_eq_marked_tsum,markedDensitySum,Complex.ofReal_sum]
  apply tsum_eq_sum
  intro d hd
  have hc : divisorCoefficient X F d=0 := by
    by_contra hc
    exact hd (Finset.mem_filter.mpr ⟨divisorCoefficient_support hX hbudget hc,
      (divisorCoefficient_ne_zero_iff.mp hc).1⟩)
  simp only [hc,zero_mul,Complex.ofReal_zero]

theorem schwartz_integral_tail_bound {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (K : EuclideanSpace ℝ ι → ℂ)
    {R B : ℝ} (hR : 0<R) (hB : 0≤B) (hKm : AEStronglyMeasurable K volume)
    (hK : ∀ u, ‖K u‖≤B) (k : ℕ) :
    ‖∫ u in {u | R<‖u‖}, Φ u*K u‖ ≤
      (B/R^k) * ∫ u, ‖u‖^k*‖Φ u‖ := by
  let S : Set (EuclideanSpace ℝ ι) := {u | R<‖u‖}
  have hS : MeasurableSet S := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hp : Integrable (fun u => Φ u*K u) :=
    Φ.integrable.mul_bdd hKm (Filter.Eventually.of_forall hK)
  have ht : Integrable (fun u : EuclideanSpace ℝ ι => ‖u‖^k*‖Φ u‖) :=
    SchwartzMap.integrable_pow_mul volume Φ k
  have hm : ∀ᵐ u ∂volume.restrict S,
      ‖Φ u*K u‖ ≤ (B/R^k)*(‖u‖^k*‖Φ u‖) := by
    filter_upwards [ae_restrict_mem hS] with u hu
    have hpow : R^k≤‖u‖^k := pow_le_pow_left₀ hR.le hu.le k
    rw [norm_mul]
    have hpower : 1≤‖u‖^k/R^k := (one_le_div (pow_pos hR k)).mpr hpow
    calc
      ‖Φ u‖*‖K u‖ ≤ ‖Φ u‖*B := mul_le_mul_of_nonneg_left (hK u) (norm_nonneg _)
      _ ≤ (‖Φ u‖*B)*(‖u‖^k/R^k) := le_mul_of_one_le_right (by positivity) hpower
      _ = (B/R^k)*(‖u‖^k*‖Φ u‖) := by ring
  calc
    _ ≤ ∫ u in S, ‖Φ u*K u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in S, (B/R^k)*(‖u‖^k*‖Φ u‖) :=
      integral_mono_ae hp.integrableOn.norm ((ht.const_mul _).integrableOn) hm
    _ ≤ ∫ u, (B/R^k)*(‖u‖^k*‖Φ u‖) :=
      setIntegral_le_integral (ht.const_mul _) (by filter_upwards [] with u; positivity)
    _ = _ := integral_const_mul _ _

theorem continuous_tupleFourier_tsum {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) {L : ℝ} (hL : 0<L)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) :
    Continuous (fun u : EuclideanSpace ℝ ι =>
      ∑' d : AllowedDivisorTuple A, tupleFourierCoefficient δ d.val (fourierContour L u)) := by
  refine continuous_tsum (fun d => continuous_tupleFourierCoefficient_contour δ d.val L)
    (tupleFourier_summable_norm hδ A (fun _ => (L⁻¹:ℝ)) (inv_pos.mpr hL) hA hR
      (fun _ => by simp)) ?_
  intro d u
  exact (tupleFourierCoefficient_contour_norm δ d.val L u).le

theorem tupleFourier_tsum_norm_bound {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) {L : ℝ} (hL : 0<L)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) (u : EuclideanSpace ℝ ι) :
    ‖∑' d : AllowedDivisorTuple A, tupleFourierCoefficient δ d.val (fourierContour L u)‖ ≤
    Real.exp ((2*R)*Real.log (riemannZeta ((1+L⁻¹:ℝ):ℂ)).re) := by
  exact (norm_tsum_le_tsum_norm (tupleFourier_summable_norm hδ A _ (inv_pos.mpr hL)
    hA hR (by intro i; simp))).trans
    (tupleFourier_norm_tsum_le hδ A _ (inv_pos.mpr hL) hA hR (by intro i; simp))

theorem tupleFourier_schwartz_tail {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) {L U : ℝ} (hL : 0<L) (hU : 0<U)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R)
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (k : ℕ) :
    ‖∫ u in {u | U<‖u‖}, Φ u *
      (∑' d : AllowedDivisorTuple A, tupleFourierCoefficient δ d.val (fourierContour L u))‖ ≤
      (Real.exp ((2*R)*Real.log (riemannZeta ((1+L⁻¹:ℝ):ℂ)).re)/U^k) *
        ∫ u, ‖u‖^k*‖Φ u‖ := by
  apply schwartz_integral_tail_bound Φ _ hU (Real.exp_pos _).le
    (continuous_tupleFourier_tsum hδ A hL hA hR).aestronglyMeasurable
    (tupleFourier_tsum_norm_bound hδ A hL hA hR)

theorem zeta_contour_majorant_polynomial :
    ∃ L₀>0, ∀ L : ℝ, L₀≤L → ∀ R : ℕ,
      Real.exp ((2*R)*Real.log (riemannZeta ((1+L⁻¹:ℝ):ℂ)).re) ≤ ((3/2)*L)^(2*R) := by
  obtain ⟨c,hc,ε,hε,hpole⟩ := zeta_pole_two_sided
  refine ⟨1+ε⁻¹,by positivity,fun L hL R => ?_⟩
  have hL0 : 0<L := lt_of_lt_of_le (by positivity) hL
  have heL : L⁻¹<ε := (inv_lt_comm₀ hL0 hε).mpr (by linarith)
  have hnorm : ‖(L⁻¹:ℂ)‖=L⁻¹ := by
    rw [show (L⁻¹:ℂ)=((L⁻¹:ℝ):ℂ) by simp,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hL0)]
  have hb := (hpole (L⁻¹:ℂ) (inv_ne_zero (by exact_mod_cast hL0.ne')) (by rw [hnorm]; exact heL)).2.2
  rw [norm_mul,hnorm] at hb
  have hz : (riemannZeta ((1+L⁻¹:ℝ):ℂ)).re ≤ (3/2)*L := by
    have hcast : ((1+L⁻¹:ℝ):ℂ)=1+(L⁻¹:ℂ) := by simp
    rw [hcast]
    apply (Complex.re_le_norm _).trans
    calc
      _ = L * (L⁻¹ * ‖riemannZeta (1+(L⁻¹:ℂ))‖) := by field_simp
      _ ≤ L*(3/2) := mul_le_mul_of_nonneg_left hb hL0.le
      _ = _ := by ring
  have hzpos : 0<(riemannZeta ((1+L⁻¹:ℝ):ℂ)).re :=
    riemannZeta_re_pos_of_one_lt (by linarith [inv_pos.mpr hL0])
  calc
    _ = (riemannZeta ((1+L⁻¹:ℝ):ℂ)).re^(2*R) := by
      rw [show (2:ℝ)*R=((2*R:ℕ):ℝ) by norm_cast,Real.exp_nat_mul,Real.exp_log hzpos]
    _ ≤ _ := pow_le_pow_left₀ hzpos.le hz _

theorem tupleFourier_sqrt_tail_power_saving {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (R N : ℕ) :
    ∃ L₀>0, ∀ L : ℝ, L₀≤L → ∀ δ : ℕ, δ≤1 →
      ∀ A : ℕ → Finset (Finset ι),
      (∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty) →
      (∀ p : Nat.Primes, (A p).card≤R) →
      ‖∫ u in {u | Real.sqrt L<‖u‖}, Φ u *
        (∑' d : AllowedDivisorTuple A, tupleFourierCoefficient δ d.val (fourierContour L u))‖ ≤
        ((3/2:ℝ)^(2*R) * ∫ u, ‖u‖^(2*(2*R+N))*‖Φ u‖) / L^N := by
  obtain ⟨L₀,hL₀,hz⟩ := zeta_contour_majorant_polynomial
  refine ⟨L₀,hL₀,fun L hL δ hδ A hA hR => ?_⟩
  have hL0 : 0<L := hL₀.trans_le hL
  have hI : 0≤∫ u, ‖u‖^(2*(2*R+N))*‖Φ u‖ :=
    integral_nonneg (fun _ => by positivity)
  have hs : (Real.sqrt L)^(2*(2*R+N))=L^(2*R+N) := by
    rw [pow_mul,Real.sq_sqrt hL0.le]
  calc
    _ ≤ (Real.exp ((2*R)*Real.log (riemannZeta ((1+L⁻¹:ℝ):ℂ)).re)/
        (Real.sqrt L)^(2*(2*R+N))) * ∫ u, ‖u‖^(2*(2*R+N))*‖Φ u‖ :=
      tupleFourier_schwartz_tail hδ A hL0 (Real.sqrt_pos.mpr hL0) hA hR Φ _
    _ ≤ (((3/2)*L)^(2*R)/(Real.sqrt L)^(2*(2*R+N))) *
        ∫ u, ‖u‖^(2*(2*R+N))*‖Φ u‖ := by
      gcongr
      exact hz L hL R
    _ = _ := by
      rw [hs,mul_pow,pow_add]
      field_simp

theorem nonemptySubsets_singleton {ι : Type*} (i : ι) :
    nonemptySubsets {i} = {{i}} := by
  classical
  ext S
  simp [nonemptySubsets,Finset.subset_singleton_iff]
  aesop

theorem nonemptySubsets_pair {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i≠j) :
    nonemptySubsets {i,j} = {{i},{j},{i,j}} := by
  classical
  ext S
  simp only [nonemptySubsets, Finset.mem_erase, Finset.mem_powerset,
    Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨hne,he⟩
    have h : S=∅ ∨ S={i} ∨ S={j} ∨ S={i,j} := by
      have hp := Finset.mem_powerset.mpr he
      simp [Finset.powerset_insert] at hp
      aesop
    exact h.resolve_left (hne)
  · rintro (rfl|rfl|rfl) <;> simp

theorem fiberKernel_singleton {ι : Type*} (i : ι) (w : ι → ℂ) :
    fiberKernel {i} w = w i := by
  simp [fiberKernel,nonemptySubsets_singleton]

theorem fiberKernel_pair {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i≠j) (w : ι → ℂ) :
    fiberKernel {i,j} w = w i*w j/(w i+w j) := by
  rw [fiberKernel,nonemptySubsets_pair hij]
  have h1 : ({j} : Finset ι)≠{i,j} := by simp [Finset.ext_iff,hij]
  have h2 : ({i} : Finset ι)≠{j} := by simp [hij]
  have h3 : ({i} : Finset ι)≠{i,j} := by simp [Finset.ext_iff,hij.symm]
  simp [h1,h2,h3,hij,div_eq_mul_inv]
  ring

theorem integral_exp_neg_complex_Ioi {w : ℂ} (hw : 0<w.re) :
    (∫ y : ℝ in Ioi 0, Complex.exp (-w*(y:ℂ))) = w⁻¹ := by
  simpa using integral_exp_mul_complex_Ioi (a := -w) (by simpa using hw) 0

theorem fiberKernel_pair_laplace {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i≠j)
    (u : ι → ℝ) :
    fiberKernel {i,j} (fun i => frequencyW (u i)) =
    frequencyW (u i)*frequencyW (u j) *
      ∫ y : ℝ in Ioi 0, Complex.exp (-(frequencyW (u i)+frequencyW (u j))*(y:ℂ)) := by
  rw [fiberKernel_pair hij,integral_exp_neg_complex_Ioi (by simp [frequencyW])]
  rfl

@[simp] theorem primeReciprocalPrefix_eq (y : ℕ) :
    primeReciprocalPrefix y = ∑ p∈Nat.primesLE y, (1:ℝ)/p := by
  simp only [primeReciprocalPrefix,primePrefix,one_div]
  exact Finset.sum_subtype_of_mem (fun p : ℕ => (p:ℝ)⁻¹) (fun p hp => (Nat.mem_primesLE.mp hp).2)

theorem genericEulerConstant_mono : Monotone genericEulerConstant := by
  intro m n hmn
  unfold genericEulerConstant
  gcongr
  norm_num

theorem primeReciprocalPrefix_nonneg (y : ℕ) : 0≤primeReciprocalPrefix y := by
  unfold primeReciprocalPrefix
  exact Finset.sum_nonneg (fun _ _ => by positivity)

theorem exp_sub_one_le_two_mul {x : ℝ} (hx : 0≤x) (hx1 : x≤1) :
    Real.exp x-1≤2*x := by
  have h := Real.norm_exp_sub_one_sub_id_le (x:=x) (by simpa only [Real.norm_eq_abs,abs_of_nonneg hx] using hx1)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hx] at h
  have hh := (abs_le.mp h).2
  nlinarith [mul_nonneg hx (sub_nonneg.mpr hx1)]

noncomputable def uniformEulerError (R : ℕ) (s : ℝ) (y : ℕ) : ℝ :=
  Real.exp (4*R*primeReciprocalPrefix y)*
    (Real.exp (2*R)*6*R*Real.log y*(y:ℝ)^(-s)*primeReciprocalPrefix y+
      2*(Real.exp (genericEulerConstant R/(y:ℝ))-1))

theorem eulerGlobal_uniform_error {ι : Type*} [Fintype ι] {δ : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι))
    (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) {y R : ℕ} (hy : 2≤y)
    (hA : ∀ p : Nat.Primes, (A p).card≤R) (hB : B.card≤R)
    (hgen : ∀ p : Nat.Primes, y<(p:ℕ) → A p=B) {s : ℝ}
    (hzsmall : ∑ i, ‖z i‖ ≤ (y:ℝ)^(-s)) :
    ‖eulerGlobal δ A B z-eulerGlobal δ A B (fun _ => 0)‖ ≤ uniformEulerError R s y := by
  apply (eulerGlobal_comparison hδ A B z hz hy hA hB hgen).trans
  unfold uniformEulerError
  have hlog : 0≤Real.log (y:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤y))
  have hr := primeReciprocalPrefix_nonneg y
  have hK := genericEulerConstant_mono hB
  gcongr

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_ContourSums

section File_OpenAIPrimeGaps_FourierDerivatives

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

theorem tendsto_log_rpow_div_nat_rpow (a : ℝ) {s : ℝ} (hs : 0<s) :
    Tendsto (fun y : ℕ => (Real.log (y:ℝ))^a/(y:ℝ)^s) atTop (𝓝 0) :=
  (isLittleO_log_rpow_rpow_atTop a hs).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))

theorem uniformEulerError_tendsto (R : ℕ) {s : ℝ} (hs : 0<s) :
    Tendsto (uniformEulerError R s) atTop (𝓝 0) := by
  let c : ℝ := Real.exp 1
  let a : ℝ := 4*R*c
  let M : ℝ := Real.exp a
  let K : ℝ := genericEulerConstant R
  let E₁ : ℕ → ℝ := fun y => (M*Real.exp (2*R)*6*R*c)*
    ((Real.log (y:ℝ))^(a+2)/(y:ℝ)^s)
  let E₂ : ℕ → ℝ := fun y => (4*M*K)*((Real.log (y:ℝ))^a/(y:ℝ))
  have h₁ : Tendsto E₁ atTop (𝓝 0) := by
    simpa only [mul_zero,E₁] using (tendsto_log_rpow_div_nat_rpow (a+2) hs).const_mul _
  have h₂ : Tendsto E₂ atTop (𝓝 0) := by
    simpa only [mul_zero,Real.rpow_one,E₂] using
      (tendsto_log_rpow_div_nat_rpow a (s:=1) zero_lt_one).const_mul (4*M*K)
  have he : ∀ᶠ y : ℕ in atTop, 0≤uniformEulerError R s y ∧
      uniformEulerError R s y ≤ E₁ y+E₂ y := by
    have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
    filter_upwards [eventually_prime_reciprocal_bound, ht.eventually_ge_atTop 1,
      (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (max K 1)] with y hr hl hy
    change 1 ≤ Real.log (y:ℝ) at hl
    have hy0 : (0:ℝ)<y := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hy)
    have hK0 : 0≤K := genericEulerConstant_nonneg R
    have hKy : K/(y:ℝ)≤1 := (div_le_one hy0).mpr ((le_max_left _ _).trans hy)
    have hp0 := primeReciprocalPrefix_nonneg y
    have hr' : primeReciprocalPrefix y ≤ c*(1+Real.log (Real.log y)) := by
      simpa only [primeReciprocalPrefix_eq,c] using hr
    have hr'' : primeReciprocalPrefix y ≤ c*Real.log y := by
      apply hr'.trans
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      linarith [Real.log_le_sub_one_of_pos (show 0<Real.log (y:ℝ) by linarith)]
    have hp : Real.exp (4*R*primeReciprocalPrefix y) ≤ M*(Real.log (y:ℝ))^a := by
      calc
        _ ≤ Real.exp (4*R*(c*(1+Real.log (Real.log y)))) := by gcongr
        _ = _ := by
          rw [Real.rpow_def_of_pos (show 0<Real.log (y:ℝ) by linarith)]
          dsimp only [M,a]
          rw [← Real.exp_add]
          congr 1
          ring
    have hex : Real.exp (K/(y:ℝ))-1 ≤ 2*(K/(y:ℝ)) :=
      exp_sub_one_le_two_mul (by positivity) hKy
    have hnonneg : 0≤Real.exp (K/(y:ℝ))-1 := sub_nonneg.mpr (Real.one_le_exp (by positivity))
    constructor
    · unfold uniformEulerError
      exact mul_nonneg (Real.exp_pos _).le (add_nonneg (by positivity) (mul_nonneg (by norm_num) hnonneg))
    · calc
        _ ≤ (M*(Real.log (y:ℝ))^a)*
              (Real.exp (2*R)*6*R*Real.log y*(y:ℝ)^(-s)*(c*Real.log y)+4*K/(y:ℝ)) := by
            unfold uniformEulerError
            apply mul_le_mul hp ?_ (add_nonneg (by positivity) (mul_nonneg (by norm_num) hnonneg))
              (by positivity)
            gcongr
            calc
              _ ≤ 2*(2*(K/(y:ℝ))) := mul_le_mul_of_nonneg_left hex (by norm_num)
              _ = _ := by ring
        _ = E₁ y+E₂ y := by
          dsimp only [E₁,E₂]
          rw [Real.rpow_neg hy0.le,Real.rpow_add (show 0<Real.log (y:ℝ) by linarith),Real.rpow_two]
          ring
  apply squeeze_zero'
  · exact he.mono (fun _ => And.left)
  · exact he.mono (fun _ => And.right)
  · simpa only [add_zero] using h₁.add h₂

section FourierDerivative

open scoped FourierTransform SchwartzMap ContDiff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

open LineDeriv

theorem radianFourier_lineDeriv (G : SchwartzMap V ℂ) (m u : V) :
    radianFourier (∂_{m} G) u = -Complex.I*(inner ℝ u m:ℂ)*radianFourier G u := by
  have hg : (inner ℝ · m).HasTemperateGrowth := by fun_prop
  simp only [radianFourier,SchwartzMap.fourierInv_lineDerivOp_eq,
    smul_apply,SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply,
    frequencyDilation_apply,SchwartzMap.smulLeftCLM_apply hg,real_inner_smul_left,
    smul_eq_mul,Complex.real_smul]
  push_cast
  field_simp

theorem radianFourier_add (G H : SchwartzMap V ℂ) (u : V) :
    radianFourier (G+H) u = radianFourier G u+radianFourier H u := by
  simp only [radianFourier, FourierTransform.fourierInv_add, map_add, smul_add, add_apply]

theorem radianFourier_const_mul (c : ℂ) (G : SchwartzMap V ℂ) (u : V) :
    radianFourier (c • G) u = c*radianFourier G u := by
  simp only [radianFourier, FourierTransform.fourierInv_smul, map_smul, smul_apply,Complex.real_smul,smul_eq_mul]
  ring

noncomputable def laplaceLineDeriv (ℓ : V →L[ℝ] ℝ) (m : V) (G : SchwartzMap V ℂ) :
    SchwartzMap V ℂ := (ℓ m : ℂ) • G + (-1:ℂ) • (∂_{m} G)

theorem radianFourier_laplaceLineDeriv (ℓ : V →L[ℝ] ℝ) (m : V)
    (G : SchwartzMap V ℂ) (u : V) :
    radianFourier (laplaceLineDeriv ℓ m G) u =
      ((ℓ m : ℂ)+Complex.I*(inner ℝ u m:ℂ))*radianFourier G u := by
  rw [laplaceLineDeriv, radianFourier_add, radianFourier_const_mul,
    radianFourier_const_mul, radianFourier_lineDeriv]
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem laplaceLineDeriv_apply (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (m v : V) :
    laplaceLineDeriv ℓ m (laplaceSchwartz ℓ F hF hFs) v =
      Complex.exp (ℓ v : ℂ)*(-fderiv ℝ F v m) := by
  have hlin := Complex.ofRealCLM.hasFDerivAt.comp v ℓ.hasFDerivAt
  have he := hlin.cexp
  have hf := he.mul ((hFs.differentiable (by simp)).differentiableAt.hasFDerivAt (x := v))
  simp only [laplaceLineDeriv, add_apply, smul_apply, smul_eq_mul,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, laplaceSchwartz_apply]
  change (ℓ m:ℂ)*(Complex.exp (ℓ v:ℂ)*F v) +
    -1*(fderiv ℝ (fun v => Complex.exp (ℓ v:ℂ)*F v) v m) = _
  have hd := congrArg (fun A : V →L[ℝ] ℂ => A m) hf.fderiv
  simp only [Function.comp_apply, add_apply,
    smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, smul_eq_mul] at hd
  change (fderiv ℝ (fun x => Complex.exp (ℓ x:ℂ)*F x) v) m =
    Complex.exp (ℓ v:ℂ)*fderiv ℝ F v m + F v*(Complex.exp (ℓ v:ℂ)*(ℓ m:ℂ)) at hd
  rw [hd]
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem contDiff_signedLineDeriv (F : V → ℂ) (hFs : ContDiff ℝ ∞ F) (m : V) :
    ContDiff ℝ ∞ (fun v => -fderiv ℝ F v m) := by
  exact (hFs.fderiv_right (by simp)).clm_apply contDiff_const |>.neg

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem laplaceLineDeriv_laplaceSchwartz (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (m : V) :
    laplaceLineDeriv ℓ m (laplaceSchwartz ℓ F hF hFs) =
      laplaceSchwartz ℓ (fun v => -fderiv ℝ F v m) (hF.fderiv_apply ℝ m |>.neg)
        (contDiff_signedLineDeriv F hFs m) := by
  ext v
  exact laplaceLineDeriv_apply ℓ F hF hFs m v

theorem sourceFourier_signedLineDeriv (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (m u : V) :
    sourceFourier ℓ (fun v => -fderiv ℝ F v m) (hF.fderiv_apply ℝ m |>.neg)
        (contDiff_signedLineDeriv F hFs m) u =
      ((ℓ m:ℂ)+Complex.I*(inner ℝ u m:ℂ))*sourceFourier ℓ F hF hFs u := by
  unfold sourceFourier
  rw [← laplaceLineDeriv_laplaceSchwartz, radianFourier_laplaceLineDeriv]

noncomputable def signedDirections (ms : List V) (F : V → ℂ) : V → ℂ :=
  ms.foldr (fun m H v => -fderiv ℝ H v m) F

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem signedDirections_compact (ms : List V) (F : V → ℂ) (hF : HasCompactSupport F) :
    HasCompactSupport (signedDirections ms F) := by
  induction ms with
  | nil => exact hF
  | cons m ms ih => exact (ih.fderiv_apply ℝ m).neg

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem signedDirections_smooth (ms : List V) (F : V → ℂ) (hFs : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (signedDirections ms F) := by
  induction ms with
  | nil => exact hFs
  | cons m ms ih => exact contDiff_signedLineDeriv _ ih m

theorem sourceFourier_signedDirections (ℓ : V →L[ℝ] ℝ) (ms : List V) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (u : V) :
    sourceFourier ℓ (signedDirections ms F) (signedDirections_compact ms F hF)
        (signedDirections_smooth ms F hFs) u =
      (ms.map (fun m => ((ℓ m:ℂ)+Complex.I*(inner ℝ u m:ℂ)))).prod *
        sourceFourier ℓ F hF hFs u := by
  induction ms with
  | nil => simp [signedDirections]
  | cons m ms ih =>
    change sourceFourier ℓ (fun v => -fderiv ℝ (signedDirections ms F) v m) _ _ u = _
    rw [sourceFourier_signedLineDeriv ℓ (signedDirections ms F)
      (signedDirections_compact ms F hF) (signedDirections_smooth ms F hFs),ih]
    simp only [List.map_cons,List.prod_cons,mul_assoc]

theorem sourceFourier_derivative_inversion (ℓ : V →L[ℝ] ℝ) (ms : List V) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (v : V) :
    (∫ u : V, sourceFourier ℓ F hF hFs u *
      (ms.map (fun m => ((ℓ m:ℂ)+Complex.I*(inner ℝ u m:ℂ)))).prod *
      Complex.exp (-(ℓ v:ℂ)-Complex.I*(inner ℝ u v:ℂ))) = signedDirections ms F v := by
  rw [← sourceFourier_inversion ℓ (signedDirections ms F)
    (signedDirections_compact ms F hF) (signedDirections_smooth ms F hFs) v]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [sourceFourier_signedDirections,mul_comm (sourceFourier ℓ F hF hFs u)]

end FourierDerivative

noncomputable def familyKernel {ι : Type*} (B : Finset (Finset ι)) (w : ι → ℂ) : ℂ :=
  ∏ S∈B, (∑ i∈S, w i)^(-((-1:ℤ)^S.card))

noncomputable def normalizedZetaProduct {ι : Type*} (B : Finset (Finset ι)) (z : ι → ℂ) : ℂ :=
  ∏ S∈B, ((∑ i∈S, z i)*riemannZeta (1+∑ i∈S, z i))^((-1:ℤ)^S.card)

theorem familyKernel_fibers {ι α : Type*} [Fintype ι] (b : ι → α)
    (R : Finset α) (w : ι → ℂ) :
    familyKernel (fiberSubsetFamily b R) w =
      ∏ r∈R, fiberKernel (Finset.univ.filter fun i => b i=r) w := by
  classical
  unfold familyKernel fiberSubsetFamily fiberKernel
  rw [Finset.prod_biUnion]
  intro r _ s _ hrs
  exact disjoint_nonemptySubsets_fibers b hrs

theorem familyKernel_homogeneous {ι : Type*} (B : Finset (Finset ι))
    (w : ι → ℂ) {c : ℂ} (hc : c≠0) {t : ℕ}
    (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ)) :
    familyKernel B (fun i => c*w i) = c^t*familyKernel B w := by
  classical
  unfold familyKernel
  simp_rw [← Finset.mul_sum,mul_zpow]
  rw [Finset.prod_mul_distrib,prod_const_zpow _ _ hc,Finset.sum_neg_distrib,ht,
    neg_neg,zpow_natCast]

theorem eulerZetaProduct_factorization {ι : Type*} (B : Finset (Finset ι)) (z : ι → ℂ)
    (hz : ∀ S∈B, ∑ i∈S, z i≠0) :
    eulerZetaProduct B z=familyKernel B z*normalizedZetaProduct B z := by
  classical
  unfold eulerZetaProduct familyKernel normalizedZetaProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro S hS
  rw [mul_zpow,← mul_assoc,← zpow_add₀ (hz S hS),neg_add_cancel,zpow_zero,one_mul]

theorem familyKernel_norm_polynomial {ι : Type*} [Fintype ι]
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) (u : ι → ℝ)
    {U : ℝ} (hU : 0≤U) (hu : ∀ i, |u i|≤U) :
    ‖familyKernel B (fun i => frequencyW (u i))‖ ≤
      ((max (Fintype.card ι) 1:ℕ)*(1+U):ℝ)^B.card := by
  have hbase : (1:ℝ)≤(max (Fintype.card ι) 1:ℕ)*(1+U) := by
    have h : (1:ℝ)≤(max (Fintype.card ι) 1:ℕ) := by exact_mod_cast le_max_right _ _
    nlinarith
  rw [familyKernel,norm_prod]
  calc
    _ ≤ ∏ _S∈B, ((max (Fintype.card ι) 1:ℕ)*(1+U):ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro S hS
      rcases neg_one_pow_eq_or ℤ S.card with h | h
      · rw [h,zpow_neg_one,norm_inv]
        exact (inv_le_one_of_one_le₀ (frequencySum_norm_lower (hB S hS) u)).trans hbase
      · rw [h,neg_neg,zpow_one]
        apply (frequencySum_norm_upper S u (fun i _ => hu i)).trans
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast (Finset.card_le_univ S).trans (le_max_left _ _)
    _ = _ := by simp

theorem normalizedZetaProduct_error {ι : Type*} (B : Finset (Finset ι)) (z : ι → ℂ)
    {c ε : ℝ} (hc : 0<c) (hε : 0≤ε)
    (hz : ∀ S∈B,
      ‖(∑ i∈S, z i)*riemannZeta (1+∑ i∈S, z i)-1‖≤c*ε ∧
      1/2≤‖(∑ i∈S, z i)*riemannZeta (1+∑ i∈S, z i)‖ ∧
      ‖(∑ i∈S, z i)*riemannZeta (1+∑ i∈S, z i)‖≤3/2) :
    ‖normalizedZetaProduct B z-1‖ ≤ 2^B.card*(B.card*(2*c*ε)) := by
  apply norm_prod_sub_one_le _ _ (by norm_num : (1:ℝ)≤2)
  · intro S hS
    rcases neg_one_pow_eq_or ℤ S.card with h | h
    · rw [h,zpow_one]
      linarith [(hz S hS).2.2]
    · rw [h,zpow_neg_one,norm_inv]
      exact (inv_le_comm₀ (by linarith [(hz S hS).2.1] :
        0<‖(∑ i∈S, z i)*riemannZeta (1+∑ i∈S, z i)‖) (by norm_num)).mpr
        (by simpa only [one_div] using (hz S hS).2.1)
  · intro S hS
    rcases neg_one_pow_eq_or ℤ S.card with h | h
    · rw [h,zpow_one]
      nlinarith [(hz S hS).1]
    · rw [h,zpow_neg_one]
      exact (norm_inv_sub_one_le (hz S hS).2.1).trans (by nlinarith [(hz S hS).1])

theorem eulerZeta_norm_contour_error :
    ∃ c>0, ∃ ε>0, ∀ {ι : Type*} [Fintype ι] (B : Finset (Finset ι)),
      (∀ S∈B, S.Nonempty) → ∀ u : ι → ℝ, ∀ {L U : ℝ}, 0<L → 0≤U →
      (∀ i, |u i|≤U) → (Fintype.card ι:ℝ)*(1+U)/L<ε →
      ‖normalizedZetaProduct B (fun i => frequencyW (u i)/(L:ℂ))-1‖ ≤
        2^B.card*(B.card*(2*c*((Fintype.card ι:ℝ)*(1+U)/L))) := by
  obtain ⟨c,hc,ε,hε,hpole⟩ := zeta_pole_two_sided
  refine ⟨c,hc,ε,hε,?_⟩
  intro ι _ B hB u L U hL hU hu hsmall
  apply normalizedZetaProduct_error B _ hc (by positivity)
  intro S hS
  have hsum : (∑ i∈S, frequencyW (u i)/(L:ℂ)) =
      (∑ i∈S, frequencyW (u i))/(L:ℂ) := (Finset.sum_div _ _ _).symm
  have hnz : (∑ i∈S, frequencyW (u i)/(L:ℂ))≠0 := by
    rw [hsum]
    exact div_ne_zero (frequencySum_ne_zero (hB S hS) u) (by exact_mod_cast hL.ne')
  have hn : ‖∑ i∈S, frequencyW (u i)/(L:ℂ)‖ ≤ (Fintype.card ι:ℝ)*(1+U)/L := by
    rw [hsum,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
    apply div_le_div_of_nonneg_right _ hL.le
    apply (frequencySum_norm_upper S u (fun i _ => hu i)).trans
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ S) (by positivity)
  have hp := hpole _ hnz (hn.trans_lt hsmall)
  exact ⟨hp.1.trans (mul_le_mul_of_nonneg_left hn hc.le), hp.2⟩

theorem eulerZetaProduct_scaled_factorization {ι : Type*}
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) (u : ι → ℝ)
    {t : ℕ} (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ)) {L : ℝ} (hL : 0<L) :
    (L:ℂ)^t*eulerZetaProduct B (fun i => frequencyW (u i)/(L:ℂ)) =
      familyKernel B (fun i => frequencyW (u i))*
        normalizedZetaProduct B (fun i => frequencyW (u i)/(L:ℂ)) := by
  have hLc : (L:ℂ)≠0 := by exact_mod_cast hL.ne'
  have hnz : ∀ S∈B, ∑ i∈S, frequencyW (u i)/(L:ℂ)≠0 := by
    intro S hS
    rw [← Finset.sum_div]
    exact div_ne_zero (frequencySum_ne_zero (hB S hS) u) hLc
  have hk : familyKernel B (fun i => frequencyW (u i)/(L:ℂ)) =
      (L:ℂ)⁻¹^t*familyKernel B (fun i => frequencyW (u i)) := by
    simpa only [div_eq_mul_inv,mul_comm] using
      familyKernel_homogeneous B (fun i => frequencyW (u i)) (inv_ne_zero hLc) ht
  rw [eulerZetaProduct_factorization _ _ hnz,hk,inv_pow,← mul_assoc,← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero t hLc),one_mul]

theorem eulerZetaProduct_scaled_error {ι : Type*} (B : Finset (Finset ι))
    (hB : ∀ S∈B, S.Nonempty) (u : ι → ℝ) {t : ℕ}
    (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ)) {L : ℝ} (hL : 0<L) {E : ℝ}
    (hE : ‖normalizedZetaProduct B (fun i => frequencyW (u i)/(L:ℂ))-1‖≤E) :
    ‖(L:ℂ)^t*eulerZetaProduct B (fun i => frequencyW (u i)/(L:ℂ))-
      familyKernel B (fun i => frequencyW (u i))‖ ≤
        ‖familyKernel B (fun i => frequencyW (u i))‖*E := by
  rw [eulerZetaProduct_scaled_factorization B hB u ht hL,← mul_sub_one,norm_mul]
  exact mul_le_mul_of_nonneg_left hE (norm_nonneg _)

noncomputable def eulerGlobalMajorant (R y : ℕ) : ℝ :=
  Real.exp (4*R*primeReciprocalPrefix y+genericEulerConstant R/(y:ℝ))

theorem norm_eulerGlobal_le {ι : Type*} {δ : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι))
    (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) {y R : ℕ} (hy : 0<y)
    (hA : ∀ p : Nat.Primes, (A p).card≤R) (hB : B.card≤R)
    (hgen : ∀ p : Nat.Primes, y<(p:ℕ) → A p=B) :
    ‖eulerGlobal δ A B z‖ ≤ eulerGlobalMajorant R y := by
  have hf := eulerH_summable_error hδ A B z hz hy hgen
  have ht := norm_tprod_sub_one_le_exp (hf.subtype (fun p => p∉primePrefix y))
  have htail := eulerH_tail_sum hδ A B z hz hy hgen
  have hpref : ‖∏ p∈primePrefix y, eulerH p δ (A p) B z‖ ≤
      Real.exp (4*R*primeReciprocalPrefix y) := by
    rw [norm_prod]
    calc
      _ ≤ ∏ p∈primePrefix y, Real.exp (4*R*(p:ℝ)⁻¹) := by
        apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro p _
        apply (norm_eulerH_le p.property.two_le hδ (A p) B z hz).trans
        apply Real.exp_le_exp.mpr
        have haR : ((A p).card:ℝ)≤R := by exact_mod_cast hA p
        have hbR : (B.card:ℝ)≤R := by exact_mod_cast hB
        have hp0 : 0≤(p:ℝ)⁻¹ := by positivity
        nlinarith
      _ = _ := by rw [← Real.exp_sum]; congr 1; simp [primeReciprocalPrefix,Finset.mul_sum]
  have hn : ‖∏' p : {p : Nat.Primes // p∉primePrefix y}, eulerH p.val δ (A p.val) B z‖ ≤
      Real.exp (genericEulerConstant R/(y:ℝ)) := by
    have hh := norm_le_norm_sub_add (∏' p : {p : Nat.Primes // p∉primePrefix y},
      eulerH p.val δ (A p.val) B z) 1
    rw [norm_one] at hh
    have he : Real.exp (∑' p : {p : Nat.Primes // p∉primePrefix y},
      ‖eulerH p.val δ (A p.val) B z-1‖) ≤ Real.exp (genericEulerConstant R/(y:ℝ)) := by
      apply Real.exp_le_exp.mpr
      apply htail.trans
      exact div_le_div_of_nonneg_right (genericEulerConstant_mono hB) (by positivity)
    linarith
  unfold eulerGlobal
  rw [tprod_eq_prod_mul_tail (primePrefix y) hf,norm_mul]
  apply (mul_le_mul hpref hn (norm_nonneg _) (Real.exp_pos _).le).trans_eq
  exact (Real.exp_add _ _).symm

theorem tupleFourier_scaled_factorization {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι))
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R)
    (hB : ∀ S∈B, S.Nonempty) {y : ℕ} (hy : 0<y)
    (hgen : ∀ p : Nat.Primes, y<(p:ℕ) → A p=B)
    (u : ι → ℝ) {t : ℕ} (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ))
    {L : ℝ} (hL : 0<L) :
    (L:ℂ)^t*(∑' d : AllowedDivisorTuple A,
      tupleFourierCoefficient δ d.val (fun i => frequencyW (u i)/(L:ℂ))) =
      eulerGlobal δ A B (fun i => frequencyW (u i)/(L:ℂ))*
      familyKernel B (fun i => frequencyW (u i))*
      normalizedZetaProduct B (fun i => frequencyW (u i)/(L:ℂ)) := by
  have hz (i : ι) : (frequencyW (u i)/(L:ℂ)).re = 1/L := by
    simp [frequencyW,Complex.div_re]
  have hn (i : ι) : 0≤(frequencyW (u i)/(L:ℂ)).re := by rw [hz]; positivity
  have hH := multipliable_of_summable_norm_sub_one
    (eulerH_summable_error hδ A B _ hn hy hgen)
  rw [tupleFourier_eq_H_zeta hδ A B _ (by positivity : 0<1/L) hA hR
    (fun i => (hz i).ge) hB hH.hasProd]
  have he := eulerZetaProduct_scaled_factorization B hB u ht hL
  change (L:ℂ)^t*(eulerGlobal δ A B _*_) = _
  calc
    _ = eulerGlobal δ A B _*((L:ℂ)^t*eulerZetaProduct B _) := by ring
    _ = _ := by rw [he]; ring

theorem norm_mul_mul_sub_le {H H₀ K N : ℂ} {E M Z : ℝ}
    (hE : ‖H-H₀‖≤E) (hM : ‖H₀‖≤M) (hZ : ‖N-1‖≤Z) :
    ‖H*K*N-H₀*K‖ ≤ ‖K‖*(E*(1+Z)+M*Z) := by
  have he0 : 0≤E := (norm_nonneg _).trans hE
  have hM0 : 0≤M := (norm_nonneg _).trans hM
  have hN : ‖N‖≤1+Z := by
    have := norm_le_norm_sub_add N 1
    rw [norm_one] at this
    linarith
  calc
    _ = ‖K*((H-H₀)*N+H₀*(N-1))‖ := by congr 1; ring
    _ ≤ ‖K‖*(‖H-H₀‖*‖N‖+‖H₀‖*‖N-1‖) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (by
        simpa only [norm_mul] using (norm_add_le ((H-H₀)*N) (H₀*(N-1)))) (norm_nonneg _)
    _ ≤ _ := by gcongr

theorem tupleFourier_scaled_core_error :
    ∃ c>0, ∃ ε>0, ∀ {ι : Type*} [Fintype ι] {δ R : ℕ}, δ≤1 →
      ∀ (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι)),
      (∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty) →
      (∀ p : Nat.Primes, (A p).card≤R) →
      (∀ S∈B, S.Nonempty) → B.card≤R → ∀ {y : ℕ}, 2≤y →
      (∀ p : Nat.Primes, y<(p:ℕ) → A p=B) →
      ∀ (u : ι → ℝ) {t : ℕ}, (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ) →
      ∀ {L U s : ℝ}, 0<L → 0≤U → (∀ i, |u i|≤U) →
      (Fintype.card ι:ℝ)*(1+U)/L<ε →
      (∑ i, ‖frequencyW (u i)/(L:ℂ)‖)≤(y:ℝ)^(-s) →
      ‖(L:ℂ)^t*(∑' d : AllowedDivisorTuple A,
        tupleFourierCoefficient δ d.val (fun i => frequencyW (u i)/(L:ℂ))) -
        eulerGlobal δ A B (fun _ => 0)*familyKernel B (fun i => frequencyW (u i))‖ ≤
      ‖familyKernel B (fun i => frequencyW (u i))‖*
        (uniformEulerError R s y*(1+2^B.card*(B.card*(2*c*((Fintype.card ι:ℝ)*(1+U)/L))))+
         eulerGlobalMajorant R y*(2^B.card*(B.card*(2*c*((Fintype.card ι:ℝ)*(1+U)/L))))) := by
  obtain ⟨c,hc,ε,hε,hpole⟩ := eulerZeta_norm_contour_error
  refine ⟨c,hc,ε,hε,?_⟩
  intro ι _ δ R hδ A B hA hR hB hBR y hy hgen u t ht L U s hL hU hu hsmall hzsmall
  rw [tupleFourier_scaled_factorization hδ A B hA hR hB (by omega) hgen u ht hL]
  apply norm_mul_mul_sub_le
  · exact eulerGlobal_uniform_error hδ A B _
      (fun i => by simp [frequencyW,Complex.div_re]; positivity) hy hR hBR hgen hzsmall
  · exact norm_eulerGlobal_le hδ A B _ (by simp) (by omega) hR hBR hgen
  · exact hpole B hB u hL hU hu hsmall

noncomputable def contourKernel {ι : Type*} (B : Finset (Finset ι))
    (u : EuclideanSpace ℝ ι) : ℂ := familyKernel B (fun i => frequencyW (u i))

theorem continuous_contourKernel {ι : Type*} [Fintype ι]
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) : Continuous (contourKernel B) := by
  unfold contourKernel familyKernel
  apply continuous_finsetProd
  intro S hS
  apply Continuous.zpow₀
  · apply continuous_finsetSum
    intro i _
    unfold frequencyW
    fun_prop
  · intro u
    exact Or.inl (frequencySum_ne_zero (hB S hS) (fun i => u i))

theorem contourKernel_norm_polynomial {ι : Type*} [Fintype ι]
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) (u : EuclideanSpace ℝ ι) :
    ‖contourKernel B u‖ ≤ ((max (Fintype.card ι) 1:ℕ):ℝ)^B.card*
      2^(B.card-1)*(1+‖u‖^B.card) := by
  apply (familyKernel_norm_polynomial B hB (fun i => u i) (norm_nonneg _)
    (fun i => by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u i)).trans
  rw [mul_pow,mul_assoc]
  gcongr
  simpa only [one_pow] using add_pow_le (by norm_num : (0:ℝ)≤1) (norm_nonneg u) B.card

theorem schwartz_integrable_polynomial_majorant {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (k : ℕ) :
    Integrable (fun u => ‖Φ u‖*(1+‖u‖^k)) := by
  have hi := Φ.integrable.norm.add (SchwartzMap.integrable_pow_mul volume Φ k)
  apply hi.congr
  filter_upwards [] with u
  dsimp; ring

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_FourierDerivatives

section File_OpenAIPrimeGaps_ContourIntegrals

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

theorem integrable_schwartz_contourKernel {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) :
    Integrable (fun u => Φ u*contourKernel B u) := by
  have hm := (schwartz_integrable_polynomial_majorant Φ B.card).const_mul
    (((max (Fintype.card ι) 1:ℕ):ℝ)^B.card*2^(B.card-1))
  apply hm.mono' ((Φ.continuous.mul (continuous_contourKernel B hB)).aestronglyMeasurable)
  filter_upwards [] with u
  simp only [Pi.mul_apply]
  rw [norm_mul]
  calc
    _ ≤ ‖Φ u‖*(((max (Fintype.card ι) 1:ℕ):ℝ)^B.card*2^(B.card-1)*(1+‖u‖^B.card)) :=
      mul_le_mul_of_nonneg_left (contourKernel_norm_polynomial B hB u) (norm_nonneg _)
    _ = _ := by ring

noncomputable def kernelConstant {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (B : Finset (Finset ι)) : ℂ :=
  ∫ u, Φ u*contourKernel B u

noncomputable def kernelAbsoluteConstant {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (B : Finset (Finset ι)) : ℝ :=
  ∫ u, ‖Φ u*contourKernel B u‖

theorem kernelAbsoluteConstant_nonneg {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (B : Finset (Finset ι)) :
    0≤kernelAbsoluteConstant Φ B := integral_nonneg fun _ => norm_nonneg _

theorem kernel_integral_on_error {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty)
    (S : Set (EuclideanSpace ℝ ι)) (hS : MeasurableSet S)
    (f : EuclideanSpace ℝ ι → ℂ) (hf : IntegrableOn (fun u => Φ u*f u) S)
    (H : ℂ) {E : ℝ} (hE : 0≤E)
    (he : ∀ u∈S, ‖f u-H*contourKernel B u‖≤‖contourKernel B u‖*E) :
    ‖(∫ u in S, Φ u*f u)-H*(∫ u in S, Φ u*contourKernel B u)‖ ≤
      kernelAbsoluteConstant Φ B*E := by
  have hi := integrable_schwartz_contourKernel Φ B hB
  have hH : IntegrableOn (fun u => Φ u*(H*contourKernel B u)) S := by
    simpa only [mul_left_comm] using (hi.const_mul H).integrableOn (s:=S)
  have hiH : H*(∫ u in S, Φ u*contourKernel B u) =
      ∫ u in S, Φ u*(H*contourKernel B u) := by
    rw [← integral_const_mul]
    congr 1; ext u; ring
  rw [hiH,← integral_sub hf hH]
  calc
    _ ≤ ∫ u in S, ‖Φ u*f u-Φ u*(H*contourKernel B u)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in S, ‖Φ u*contourKernel B u‖*E := by
      apply integral_mono_ae (hf.sub hH).norm (hi.norm.mul_const E).integrableOn
      filter_upwards [ae_restrict_mem hS] with u hu
      simp only [Pi.sub_apply]
      rw [← mul_sub,norm_mul,norm_mul]
      nlinarith [mul_le_mul_of_nonneg_left (he u hu) (norm_nonneg (Φ u))]
    _ ≤ ∫ u, ‖Φ u*contourKernel B u‖*E :=
      setIntegral_le_integral (hi.norm.mul_const E) (by filter_upwards [] with u; positivity)
    _ = kernelAbsoluteConstant Φ B*E := by rw [integral_mul_const]; rfl

theorem eulerGlobalMajorant_div_rpow_tendsto (R : ℕ) {s : ℝ} (hs : 0<s) :
    Tendsto (fun y : ℕ => eulerGlobalMajorant R y/(y:ℝ)^s) atTop (𝓝 0) := by
  let c : ℝ := Real.exp 1
  let a : ℝ := 4*R*c
  let M : ℝ := Real.exp (a+genericEulerConstant R)
  have hlim := (tendsto_log_rpow_div_nat_rpow a hs).const_mul M
  apply squeeze_zero' _ _ (by simpa only [mul_zero] using hlim)
  · filter_upwards [] with y
    unfold eulerGlobalMajorant
    positivity
  · have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
    filter_upwards [eventually_prime_reciprocal_bound,
      ht.eventually_ge_atTop 1,
      (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop 1] with y hr hl hy
    change 1≤Real.log (y:ℝ) at hl
    have hly : 0<Real.log (y:ℝ) := by linarith
    have hr' : primeReciprocalPrefix y ≤ c*(1+Real.log (Real.log y)) := by
      simpa only [primeReciprocalPrefix_eq,c] using hr
    have hK : genericEulerConstant R/(y:ℝ)≤genericEulerConstant R :=
      div_le_self (genericEulerConstant_nonneg R) hy
    have hb : eulerGlobalMajorant R y ≤ M*(Real.log (y:ℝ))^a := by
      calc
        _ ≤ Real.exp (4*R*(c*(1+Real.log (Real.log y)))+genericEulerConstant R) := by
          unfold eulerGlobalMajorant
          gcongr
        _ = _ := by
          rw [Real.rpow_def_of_pos hly]
          dsimp only [M,a]
          rw [← Real.exp_add]
          congr 1
          ring
    calc
      _ ≤ (M*(Real.log (y:ℝ))^a)/(y:ℝ)^s :=
        div_le_div_of_nonneg_right hb (Real.rpow_nonneg (by positivity) _)
      _ = M*((Real.log (y:ℝ))^a/(y:ℝ)^s) := by ring

noncomputable def uniformCoreError (R : ℕ) (c s : ℝ) (y : ℕ) : ℝ :=
  uniformEulerError R s y*(1+(2^R*(R*(2*c)))*(y:ℝ)^(-s))+
    eulerGlobalMajorant R y*(2^R*(R*(2*c)))*(y:ℝ)^(-s)

theorem uniformCoreError_tendsto (R : ℕ) (c : ℝ) {s : ℝ} (hs : 0<s) :
    Tendsto (uniformCoreError R c s) atTop (𝓝 0) := by
  have hy : Tendsto (fun y : ℕ => (y:ℝ)^(-s)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hs).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have h₁ := (uniformEulerError_tendsto R hs).mul
    ((tendsto_const_nhds (x:=(1:ℝ))).add (hy.const_mul (2^R*(R*(2*c)))))
  have h₂ := (eulerGlobalMajorant_div_rpow_tendsto R hs).mul_const (2^R*(R*(2*c)))
  have he : (fun y : ℕ => eulerGlobalMajorant R y/(y:ℝ)^s*(2^R*(R*(2*c)))) =
      (fun y : ℕ => eulerGlobalMajorant R y*(2^R*(R*(2*c)))*(y:ℝ)^(-s)) := by
    ext y
    rw [Real.rpow_neg (by positivity : (0:ℝ)≤y)]
    ring
  rw [he] at h₂
  unfold uniformCoreError
  simpa only [zero_mul,mul_zero,add_zero,zero_add] using h₁.add h₂

theorem integrable_pow_mul_schwartz_contourKernel {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) (k : ℕ) :
    Integrable (fun u => ‖u‖^k*‖Φ u*contourKernel B u‖) := by
  have hi := ((SchwartzMap.integrable_pow_mul volume Φ k).add
    (SchwartzMap.integrable_pow_mul volume Φ (k+B.card))).const_mul
    (((max (Fintype.card ι) 1:ℕ):ℝ)^B.card*2^(B.card-1))
  apply hi.mono' ((continuous_norm.pow k).mul
    ((Φ.continuous.mul (continuous_contourKernel B hB)).norm)).aestronglyMeasurable
  filter_upwards [] with u
  simp only [Pi.mul_apply,Pi.pow_apply,Pi.add_apply]
  rw [Real.norm_of_nonneg (by positivity),norm_mul]
  calc
    _ ≤ ‖u‖^k*(‖Φ u‖*((((max (Fintype.card ι) 1:ℕ):ℝ)^B.card*
      2^(B.card-1))*(1+‖u‖^B.card))) := by
      gcongr; exact contourKernel_norm_polynomial B hB u
    _ = _ := by rw [pow_add]; ring

theorem norm_integral_norm_tail_le {V : Type*} [NormedAddCommGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (f : V → ℂ)
    (hf : Integrable f μ) (k : ℕ) (hk : Integrable (fun u => ‖u‖^k*‖f u‖) μ)
    {U : ℝ} (hU : 0<U) :
    ‖∫ u in {u | U<‖u‖}, f u ∂μ‖ ≤ (∫ u, ‖u‖^k*‖f u‖ ∂μ)/U^k := by
  let S : Set V := {u | U<‖u‖}
  have hS : MeasurableSet S := measurableSet_lt measurable_const continuous_norm.measurable
  have hbound : ∀ᵐ u ∂μ.restrict S, ‖f u‖≤(U^k)⁻¹*(‖u‖^k*‖f u‖) := by
    filter_upwards [ae_restrict_mem hS] with u hu
    have hp : U^k≤‖u‖^k := pow_le_pow_left₀ hU.le hu.le k
    have hdiv : 1≤(U^k)⁻¹*‖u‖^k := by
      rw [← div_eq_inv_mul]
      exact (one_le_div (pow_pos hU k)).mpr hp
    calc
      _ ≤ ((U^k)⁻¹*‖u‖^k)*‖f u‖ := by nlinarith [norm_nonneg (f u)]
      _ = _ := by ring
  calc
    _ ≤ ∫ u in S, ‖f u‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in S, (U^k)⁻¹*(‖u‖^k*‖f u‖) ∂μ :=
      integral_mono_ae hf.integrableOn.norm ((hk.const_mul _).integrableOn) hbound
    _ ≤ ∫ u, (U^k)⁻¹*(‖u‖^k*‖f u‖) ∂μ :=
      setIntegral_le_integral (hk.const_mul _) (by filter_upwards [] with u; positivity)
    _ = _ := by rw [integral_const_mul]; ring

theorem kernel_integral_tail_bound {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) (k : ℕ)
    {U : ℝ} (hU : 0<U) :
    ‖∫ u in {u | U<‖u‖}, Φ u*contourKernel B u‖ ≤
      (∫ u, ‖u‖^k*‖Φ u*contourKernel B u‖)/U^k :=
  norm_integral_norm_tail_le volume _ (integrable_schwartz_contourKernel Φ B hB) k
    (integrable_pow_mul_schwartz_contourKernel Φ B hB k) hU

theorem BombieriVinogradov_quantitative_PNT (hBV : BombieriVinogradov) :
    ∀ A : ℝ, 0<A → ∃ M>0, ∀ᶠ X : ℕ in atTop,
      |(∑ n∈Finset.Ioc 0 X, ArithmeticFunction.vonMangoldt n)-(X:ℝ)| ≤
        M*(X:ℝ)*(Real.log X)^(-A) := by
  intro A hA
  obtain ⟨b,hb,M,hM,x₀,hx₀,hbound⟩ := hBV A hA
  refine ⟨M,hM,?_⟩
  have hx := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop x₀
  have hQ := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (eventually_rpow_le_BV_range (rho:=0) (by norm_num) b)
  filter_upwards [hx,hQ] with X hX hXQ
  have hQ1 : 1≤⌊(X:ℝ)^(1/2:ℝ)*(Real.log X)^(-b)⌋₊ := by
    apply Nat.le_floor
    simpa only [Real.rpow_zero,Nat.cast_one] using hXQ
  have hle : (endpointError X 1:ℝ) ≤
      ∑ q ∈ Finset.Icc 1 ⌊(X:ℝ)^(1/2:ℝ)*(Real.log X)^(-b)⌋₊, (endpointError X q:ℝ) := by
    exact Finset.single_le_sum (fun q _ => NNReal.coe_nonneg _)
      (Finset.mem_Icc.mpr ⟨le_rfl,hQ1⟩)
  have hclass := endpointClassError_le X (q:=1) (c:=0) (by norm_num) (by norm_num)
  have heq : residuePrefix ArithmeticFunction.vonMangoldt X 1 0 =
      ∑ n∈Finset.Ioc 0 X, ArithmeticFunction.vonMangoldt n := by
    simp [residuePrefix,residueSlice,Nat.mod_one]
  rw [heq,Nat.totient_one,Nat.cast_one,div_one] at hclass
  exact hclass.trans (hle.trans (hbound X hX))

theorem uniformEulerError_nonneg (R : ℕ) (s : ℝ) {y : ℕ} (hy : 1≤y) :
    0≤uniformEulerError R s y := by
  have hl : 0≤Real.log (y:ℝ) := Real.log_nonneg (by exact_mod_cast hy)
  have hp := primeReciprocalPrefix_nonneg y
  have he : 0≤Real.exp (genericEulerConstant R/(y:ℝ))-1 :=
    sub_nonneg.mpr (Real.one_le_exp (by
      exact div_nonneg (genericEulerConstant_nonneg R) (by positivity)))
  unfold uniformEulerError
  positivity

theorem uniformCoreError_nonneg (R : ℕ) {c : ℝ} (hc : 0≤c) (s : ℝ)
    {y : ℕ} (hy : 1≤y) : 0≤uniformCoreError R c s y := by
  have he := uniformEulerError_nonneg R s hy
  have hm : 0≤eulerGlobalMajorant R y := (Real.exp_pos _).le
  unfold uniformCoreError
  positivity

theorem frequencyW_div_norm_sum_le {ι : Type*} [Fintype ι] (u : ι → ℝ)
    {L U : ℝ} (hL : 0<L) (hu : ∀ i, |u i|≤U) :
    (∑ i, ‖frequencyW (u i)/(L:ℂ)‖) ≤ (Fintype.card ι:ℝ)*(1+U)/L := by
  calc
    _ ≤ ∑ _i : ι, (1+U)/L := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
      apply div_le_div_of_nonneg_right _ hL.le
      exact (frequencyW_norm (u i)).trans (by linarith [hu i])
    _ = _ := by simp; ring

theorem tupleFourier_scaled_uniform_core_error :
    ∃ c>0, ∃ ε>0, ∀ {ι : Type*} [Fintype ι] {δ R : ℕ}, δ≤1 →
      ∀ (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι)),
      (∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty) →
      (∀ p : Nat.Primes, (A p).card≤R) →
      (∀ S∈B, S.Nonempty) → B.card≤R → ∀ {y : ℕ}, 2≤y →
      (∀ p : Nat.Primes, y<(p:ℕ) → A p=B) →
      ∀ (u : ι → ℝ) {t : ℕ}, (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ) →
      ∀ {L U s : ℝ}, 0<L → 0≤U → (∀ i, |u i|≤U) →
      (Fintype.card ι:ℝ)*(1+U)/L<ε →
      (Fintype.card ι:ℝ)*(1+U)/L≤(y:ℝ)^(-s) →
      ‖(L:ℂ)^t*(∑' d : AllowedDivisorTuple A,
        tupleFourierCoefficient δ d.val (fun i => frequencyW (u i)/(L:ℂ))) -
        eulerGlobal δ A B (fun _ => 0)*familyKernel B (fun i => frequencyW (u i))‖ ≤
      ‖familyKernel B (fun i => frequencyW (u i))‖*uniformCoreError R c s y := by
  obtain ⟨c,hc,ε,hε,hcore⟩ := tupleFourier_scaled_core_error
  refine ⟨c,hc,ε,hε,?_⟩
  intro ι _ δ R hδ A B hA hR hB hBR y hy hgen u t ht L U s hL hU hu hsmall hzsmall
  apply (hcore hδ A B hA hR hB hBR hy hgen u ht hL hU hu hsmall
    ((frequencyW_div_norm_sum_le u hL hu).trans hzsmall)).trans
  have hE := uniformEulerError_nonneg R s (show 1≤y by omega)
  have hCB : (B.card:ℝ)≤R := by exact_mod_cast hBR
  have h2 : (2:ℝ)^B.card≤2^R := pow_le_pow_right₀ (by norm_num) hBR
  have hζ : 2^B.card*(B.card*(2*c*((Fintype.card ι:ℝ)*(1+U)/L))) ≤
      (2^R*(R*(2*c)))*(y:ℝ)^(-s) := by
    calc
      _ ≤ 2^R*(R*(2*c*(y:ℝ)^(-s))) := by gcongr
      _ = _ := by ring
  unfold uniformCoreError
  have hM : 0≤eulerGlobalMajorant R y := (Real.exp_pos _).le
  have hmul := mul_le_mul_of_nonneg_left hζ hM
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (add_le_add_right hζ 1) hE
  · calc
      _ ≤ eulerGlobalMajorant R y*((2^R*(R*(2*c)))*(y:ℝ)^(-s)) := hmul
      _ = _ := by ring

theorem integrable_schwartz_tupleFourier {ι : Type*} [Fintype ι] {δ R : ℕ}
    (hδ : δ≤1) (A : ℕ → Finset (Finset ι)) {L : ℝ} (hL : 0<L)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R)
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    Integrable (fun u => Φ u * (∑' d : AllowedDivisorTuple A,
      tupleFourierCoefficient δ d.val (fourierContour L u))) := by
  exact Φ.integrable.mul_bdd
    (continuous_tupleFourier_tsum hδ A hL hA hR).aestronglyMeasurable
    (Filter.Eventually.of_forall (tupleFourier_tsum_norm_bound hδ A hL hA hR))

theorem integral_core_tail_error {V : Type*} [MeasurableSpace V]
    (μ : Measure V) (f g : V → ℂ) (hf : Integrable f μ) (hg : Integrable g μ)
    (S : Set V) (hS : MeasurableSet S) (H : ℂ) {E : ℝ}
    (he : ‖(∫ u in S, f u ∂μ)-H*(∫ u in S, g u ∂μ)‖≤E) :
    ‖(∫ u, f u ∂μ)-H*(∫ u, g u ∂μ)‖ ≤
      E + ‖∫ u in Sᶜ, f u ∂μ‖ + ‖H‖*‖∫ u in Sᶜ, g u ∂μ‖ := by
  rw [← integral_add_compl hS hf,← integral_add_compl hS hg]
  calc
    _ = ‖((∫ u in S, f u ∂μ)-H*(∫ u in S, g u ∂μ)) +
      ((∫ u in Sᶜ, f u ∂μ)-H*(∫ u in Sᶜ, g u ∂μ))‖ := by congr 1; ring
    _ ≤ ‖(∫ u in S, f u ∂μ)-H*(∫ u in S, g u ∂μ)‖ +
      ‖(∫ u in Sᶜ, f u ∂μ)-H*(∫ u in Sᶜ, g u ∂μ)‖ := norm_add_le _ _
    _ ≤ E + (‖∫ u in Sᶜ, f u ∂μ‖ + ‖H‖*‖∫ u in Sᶜ, g u ∂μ‖) := by
      apply add_le_add he
      simpa only [norm_mul] using norm_sub_le (∫ u in Sᶜ, f u ∂μ)
        (H*(∫ u in Sᶜ, g u ∂μ))
    _ = _ := by ring

theorem tupleFourier_integral_uniform_error :
    ∃ c>0, ∃ ε>0, ∀ {ι : Type*} [Fintype ι] {δ R : ℕ}, δ≤1 →
      ∀ (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι)),
      (∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty) →
      (∀ p : Nat.Primes, (A p).card≤R) →
      (∀ S∈B, S.Nonempty) → B.card≤R → ∀ {y : ℕ}, 2≤y →
      (∀ p : Nat.Primes, y<(p:ℕ) → A p=B) →
      ∀ (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) {t : ℕ},
      (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ) →
      ∀ {L U s : ℝ}, 0<L → 0<U →
      (Fintype.card ι:ℝ)*(1+U)/L<ε →
      (Fintype.card ι:ℝ)*(1+U)/L≤(y:ℝ)^(-s) → ∀ k₁ k₂ : ℕ,
      ‖(L:ℂ)^t*(∫ u, Φ u*(∑' d : AllowedDivisorTuple A,
        tupleFourierCoefficient δ d.val (fourierContour L u))) -
        eulerGlobal δ A B (fun _ => 0)*kernelConstant Φ B‖ ≤
      kernelAbsoluteConstant Φ B*uniformCoreError R c s y +
      L^t*(Real.exp ((2*R)*Real.log (riemannZeta ((1+L⁻¹:ℝ):ℂ)).re)/U^k₁)*
        (∫ u, ‖u‖^k₁*‖Φ u‖) +
      eulerGlobalMajorant R y*(∫ u, ‖u‖^k₂*‖Φ u*contourKernel B u‖)/U^k₂ := by
  obtain ⟨c,hc,ε,hε,hcore⟩ := tupleFourier_scaled_uniform_core_error
  refine ⟨c,hc,ε,hε,?_⟩
  intro ι _ δ R hδ A B hA hR hB hBR y hy hgen Φ t ht L U s hL hU hsmall hysmall k₁ k₂
  let T := fun u : EuclideanSpace ℝ ι => ∑' d : AllowedDivisorTuple A,
    tupleFourierCoefficient δ d.val (fourierContour L u)
  let S : Set (EuclideanSpace ℝ ι) := {u | ‖u‖≤U}
  have hS : MeasurableSet S := measurableSet_le continuous_norm.measurable measurable_const
  have hSc : Sᶜ={u | U<‖u‖} := by ext u; simp [S]
  have hT : Integrable (fun u => Φ u*T u) := integrable_schwartz_tupleFourier hδ A hL hA hR Φ
  have hcT : Integrable (fun u => Φ u*((L:ℂ)^t*T u)) := by
    simpa only [mul_left_comm] using hT.const_mul ((L:ℂ)^t)
  have hK := integrable_schwartz_contourKernel Φ B hB
  have hpoint : ∀ u∈S, ‖(L:ℂ)^t*T u-eulerGlobal δ A B (fun _ => 0)*
      contourKernel B u‖≤‖contourKernel B u‖*uniformCoreError R c s y := by
    intro u hu
    have hui : ∀ i, |u i|≤U := by
      intro i
      have hh : |u i|≤‖u‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u i
      exact hh.trans hu
    exact hcore hδ A B hA hR hB hBR hy hgen (fun i => u i) ht hL hU.le hui hsmall hysmall
  have he := kernel_integral_on_error Φ B hB S hS (fun u => (L:ℂ)^t*T u)
    hcT.integrableOn (eulerGlobal δ A B (fun _ => 0))
    (uniformCoreError_nonneg R hc.le s (y:=y) (by omega)) hpoint
  have hall := integral_core_tail_error volume (fun u => Φ u*((L:ℂ)^t*T u))
    (fun u => Φ u*contourKernel B u) hcT hK S hS
    (eulerGlobal δ A B (fun _ => 0)) he
  have hid : ∀ D : Set (EuclideanSpace ℝ ι),
      (∫ u in D, Φ u*((L:ℂ)^t*T u)) = (L:ℂ)^t*∫ u in D, Φ u*T u := by
    intro D
    rw [← integral_const_mul]
    congr 1; ext u; ring
  have hidall : (∫ u, Φ u*((L:ℂ)^t*T u))=(L:ℂ)^t*∫ u, Φ u*T u := by
    rw [← integral_const_mul]
    congr 1; ext u; ring
  rw [hidall,hid,hSc] at hall
  apply hall.trans
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  apply add_le_add
  · apply add_le_add_right
    have hb := tupleFourier_schwartz_tail hδ A hL hU hA hR Φ k₁
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb (pow_nonneg hL.le t)
  · have hH := norm_eulerGlobal_le hδ A B (fun _ => (0:ℂ)) (by intro i; simp)
      (y:=y) (by omega) hR hBR hgen
    have hb := kernel_integral_tail_bound Φ B hB k₂ hU
    calc
      _ ≤ eulerGlobalMajorant R y*((∫ u, ‖u‖^k₂*‖Φ u*contourKernel B u‖)/U^k₂) :=
        mul_le_mul hH hb (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by ring

noncomputable def densityCutoff (b : ℕ) (L : ℝ) : ℕ := ⌊L^b⌋₊

noncomputable def densityCoreExponent (b : ℕ) : ℝ := (4*(b:ℝ))⁻¹

theorem densityCoreExponent_pos {b : ℕ} (hb : 0<b) : 0<densityCoreExponent b := by
  unfold densityCoreExponent
  positivity

theorem densityCutoff_tendsto {b : ℕ} (hb : 0<b) :
    Tendsto (densityCutoff b) atTop atTop :=
  tendsto_nat_floor_atTop.comp (tendsto_pow_atTop (by omega : b≠0))

theorem sqrt_core_rate (C : ℝ) {L : ℝ} (hL : 0<L) :
    C*(1+Real.sqrt L)/L = C*(L^(-1:ℝ)+L^(-(1/2):ℝ)) := by
  have hp : L^(1/2:ℝ)/L = L^(-(1/2):ℝ) := by
    calc
      _ = L^(1/2:ℝ)/L^(1:ℝ) := by rw [Real.rpow_one]
      _ = L^((1/2:ℝ)-1) := (Real.rpow_sub hL _ _).symm
      _ = _ := by norm_num
  rw [Real.sqrt_eq_rpow,Real.rpow_neg_one,← hp]
  ring

theorem sqrt_core_rate_tendsto (C : ℝ) :
    Tendsto (fun L : ℝ => C*(1+Real.sqrt L)/L) atTop (𝓝 0) := by
  have h₁ := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1)
  have h₂ := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)
  have hh := (h₁.add h₂).const_mul C
  simp only [add_zero,mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  exact (sqrt_core_rate C hL).symm

theorem sqrt_core_quarter_rate (C : ℝ) {L : ℝ} (hL : 0<L) :
    (C*(1+Real.sqrt L)/L)/(L^(-(1/4):ℝ)) =
      C*(L^(-(3/4):ℝ)+L^(-(1/4):ℝ)) := by
  rw [sqrt_core_rate C hL,mul_div_assoc,add_div,← Real.rpow_sub hL,← Real.rpow_sub hL]
  norm_num

theorem eventually_sqrt_core_le_quarter (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, C*(1+Real.sqrt L)/L≤L^(-(1/4):ℝ) := by
  have h₁ := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<3/4)
  have h₂ := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)
  have hh := (h₁.add h₂).const_mul C
  simp only [add_zero,mul_zero] at hh
  filter_upwards [hh.eventually_lt_const zero_lt_one,eventually_gt_atTop (0:ℝ)] with L h hL
  apply (div_le_one (Real.rpow_pos_of_pos hL _)).mp
  rw [sqrt_core_quarter_rate C hL]
  exact h.le

theorem densityCutoff_neg_rpow {b : ℕ} (hb : 0<b) {L : ℝ} (hL : 1≤L) :
    L^(-(1/4):ℝ) ≤ (densityCutoff b L:ℝ)^(-densityCoreExponent b) := by
  have hLb : 1≤L^b := one_le_pow₀ hL
  have hy : 0<(densityCutoff b L:ℝ) := by
    have : 1≤densityCutoff b L := (Nat.one_le_floor_iff _).mpr hLb
    exact_mod_cast (show 0<densityCutoff b L by omega)
  have hyle : (densityCutoff b L:ℝ)≤L^b := Nat.floor_le (by positivity)
  have hb0 : (b:ℝ)≠0 := by exact_mod_cast hb.ne'
  have hexp : (b:ℝ)*(-densityCoreExponent b)=-(1/4:ℝ) := by
    unfold densityCoreExponent
    field_simp
  calc
    _ = L^((b:ℝ)*(-densityCoreExponent b)) := by rw [hexp]
    _ = (L^b)^(-densityCoreExponent b) := by
      rw [Real.rpow_mul (by linarith),Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos hy hyle (by
      have := densityCoreExponent_pos hb; linarith)

theorem eventually_density_core_scale {b : ℕ} (hb : 0<b) (C : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, 0<L ∧ 2≤densityCutoff b L ∧
      C*(1+Real.sqrt L)/L<ε ∧
      C*(1+Real.sqrt L)/L≤(densityCutoff b L:ℝ)^(-densityCoreExponent b) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (densityCutoff_tendsto hb).eventually (eventually_ge_atTop 2),
    (sqrt_core_rate_tendsto C).eventually_lt_const hε,
    eventually_sqrt_core_le_quarter C] with L hL hy hεL hbound
  exact ⟨by linarith,hy,hεL,hbound.trans (densityCutoff_neg_rpow hb hL)⟩

theorem eventually_nat_rate_le_index (a : ℕ → ℝ)
    (ha : Tendsto (fun y : ℕ => a y/(y:ℝ)) atTop (𝓝 0)) :
    ∀ᶠ y : ℕ in atTop, a y≤y := by
  filter_upwards [ha.eventually_lt_const zero_lt_one,eventually_ge_atTop 1] with y h hy
  exact ((div_le_one (by exact_mod_cast hy : 0<(y:ℝ))).mp h.le)

theorem eventually_rate_densityCutoff_le_pow (a : ℕ → ℝ)
    (ha : Tendsto (fun y : ℕ => a y/(y:ℝ)) atTop (𝓝 0))
    {b : ℕ} (hb : 0<b) :
    ∀ᶠ L : ℝ in atTop, a (densityCutoff b L)≤L^b := by
  filter_upwards [(densityCutoff_tendsto hb).eventually (eventually_nat_rate_le_index a ha),
    eventually_ge_atTop (0:ℝ)] with L h hL
  exact h.trans (Nat.floor_le (pow_nonneg hL b))

theorem sqrt_pow_even {L : ℝ} (hL : 0≤L) (n : ℕ) :
    (Real.sqrt L)^(2*n) = L^n := by rw [pow_mul,Real.sq_sqrt hL]

theorem scaled_polynomial_tail {L Z I : ℝ} (hL : 0<L) (hI : 0≤I) (R t : ℕ)
    (hZ : Z≤((3/2:ℝ)*L)^(2*R)) :
    L^t*(Z/(Real.sqrt L)^(2*(2*R+t+1)))*I≤((3/2:ℝ)^(2*R)*I)/L := by
  rw [sqrt_pow_even hL.le]
  calc
    _ ≤ L^t*((((3/2:ℝ)*L)^(2*R))/L^(2*R+t+1))*I := by gcongr
    _ = _ := by rw [mul_pow,pow_add,pow_add,pow_one]; field_simp

theorem kernel_polynomial_tail {L Z I : ℝ} (hL : 0<L) (hI : 0≤I) (b : ℕ)
    (hZ : Z≤L^b) :
    Z*I/(Real.sqrt L)^(2*(b+1))≤I/L := by
  rw [sqrt_pow_even hL.le]
  calc
    _ ≤ L^b*I/L^(b+1) := by gcongr
    _ = _ := by rw [pow_succ]; field_simp

theorem tupleFourier_integral_uniform_asymptotic {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (B : Finset (Finset ι))
    (hB : ∀ S∈B, S.Nonempty) (R t b : ℕ) (hBR : B.card≤R) (hb : 0<b)
    (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ)) :
    ∃ E : ℝ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ L : ℝ in atTop, ∀ δ : ℕ, δ≤1 → ∀ A : ℕ → Finset (Finset ι),
      (∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty) →
      (∀ p : Nat.Primes, (A p).card≤R) →
      (∀ p : Nat.Primes, densityCutoff b L<(p:ℕ) → A p=B) →
      ‖(L:ℂ)^t*(∫ u, Φ u*(∑' d : AllowedDivisorTuple A,
        tupleFourierCoefficient δ d.val (fourierContour L u))) -
        eulerGlobal δ A B (fun _ => 0)*kernelConstant Φ B‖ ≤ E L := by
  obtain ⟨c,hc,ε,hε,hformula⟩ := tupleFourier_integral_uniform_error
  obtain ⟨L₀,hL₀,hz⟩ := zeta_contour_majorant_polynomial
  let I₁ : ℝ := (3/2:ℝ)^(2*R)*(∫ u, ‖u‖^(2*(2*R+t+1))*‖Φ u‖)
  let I₂ : ℝ := ∫ u, ‖u‖^(2*(b+1))*‖Φ u*contourKernel B u‖
  let E : ℝ → ℝ := fun L => kernelAbsoluteConstant Φ B*
    uniformCoreError R c (densityCoreExponent b) (densityCutoff b L) + I₁/L + I₂/L
  refine ⟨E,?_,?_⟩
  · have hcore := ((uniformCoreError_tendsto R c (densityCoreExponent_pos hb)).comp
      (densityCutoff_tendsto hb)).const_mul (kernelAbsoluteConstant Φ B)
    have h₁ : Tendsto (fun L : ℝ => I₁/L) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have h₂ : Tendsto (fun L : ℝ => I₂/L) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    simpa only [mul_zero,add_zero,Function.comp_def,E] using (hcore.add h₁).add h₂
  · have hM : Tendsto (fun y : ℕ => eulerGlobalMajorant R y/(y:ℝ)) atTop (𝓝 0) := by
      simpa only [Real.rpow_one] using eulerGlobalMajorant_div_rpow_tendsto R zero_lt_one
    filter_upwards [eventually_density_core_scale hb (Fintype.card ι:ℝ) hε,
      eventually_rate_densityCutoff_le_pow (eulerGlobalMajorant R) hM hb,
      eventually_ge_atTop L₀] with L hscale hmajor hLL₀
    intro δ hδ A hA hR hgen
    obtain ⟨hL,hy,hsmall,hysmall⟩ := hscale
    have hbound := hformula hδ A B hA hR hB hBR hy hgen Φ ht hL
      (Real.sqrt_pos.mpr hL) hsmall hysmall (2*(2*R+t+1)) (2*(b+1))
    apply hbound.trans
    apply add_le_add
    · apply add_le_add_right
      exact scaled_polynomial_tail hL (integral_nonneg (fun _ => by positivity)) R t (hz L hLL₀ R)
    · exact kernel_polynomial_tail hL (integral_nonneg (fun _ => by positivity)) b hmajor

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_ContourIntegrals

section File_OpenAIPrimeGaps_LaplaceTransform

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

section FourierLaplace

open scoped FourierTransform SchwartzMap ContDiff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def laplaceFrequency (ℓ : V →L[ℝ] ℝ) (m u : V) : ℂ :=
  (ℓ m:ℂ)+Complex.I*(inner ℝ u m:ℂ)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp] theorem laplaceFrequency_re (ℓ : V →L[ℝ] ℝ) (m u : V) :
    (laplaceFrequency ℓ m u).re = ℓ m := by simp [laplaceFrequency]

noncomputable def rayVector {α : Type*} [Fintype α] (m : α → V) (y : α → ℝ) : V :=
  ∑ i, y i • m i

noncomputable def positiveOrthantMeasure (α : Type*) [Fintype α] : Measure (α → ℝ) :=
  Measure.pi (fun _ : α => volume.restrict (Ioi 0))

instance {α : Type*} [Fintype α] : SigmaFinite (positiveOrthantMeasure α) := by
  unfold positiveOrthantMeasure
  infer_instance

theorem positiveOrthantMeasure_eq_restrict (α : Type*) [Fintype α] :
    positiveOrthantMeasure α = volume.restrict (Set.pi univ (fun _ : α => Ioi (0:ℝ))) := by
  rw [volume_pi,Measure.restrict_pi_pi]
  rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem product_laplace_exp_eq {α : Type*} [Fintype α] (ℓ : V →L[ℝ] ℝ)
    (m : α → V) (u : V) (y : α → ℝ) :
    (∏ i, Complex.exp (-laplaceFrequency ℓ (m i) u * (y i:ℂ))) =
      Complex.exp (-(ℓ (rayVector m y):ℂ)-Complex.I*(inner ℝ u (rayVector m y):ℂ)) := by
  rw [← Complex.exp_sum]
  congr 1
  simp only [rayVector,map_sum,map_smul,smul_eq_mul,inner_sum,inner_smul_right,
    Complex.ofReal_sum,Complex.ofReal_mul]
  rw [← Finset.sum_neg_distrib,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold laplaceFrequency
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem norm_product_laplace_exp {α : Type*} [Fintype α] (ℓ : V →L[ℝ] ℝ)
    (m : α → V) (u : V) (y : α → ℝ) :
    ‖∏ i, Complex.exp (-laplaceFrequency ℓ (m i) u * (y i:ℂ))‖ =
      ∏ i, Real.exp (-ℓ (m i) * y i) := by
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp [Complex.norm_exp,laplaceFrequency]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem integrable_product_laplace_exp {α : Type*} [Fintype α]
    (ℓ : V →L[ℝ] ℝ) (m : α → V) (hm : ∀ i, 0<ℓ (m i)) (u : V) :
    Integrable (fun y => ∏ i, Complex.exp (-laplaceFrequency ℓ (m i) u * (y i:ℂ)))
      (positiveOrthantMeasure α) := by
  exact Integrable.fintype_prod (f := fun i (y : ℝ) => Complex.exp (-laplaceFrequency ℓ (m i) u * (y:ℂ)))
    (μ := fun _ => volume.restrict (Ioi 0))
    (fun i => integrableOn_exp_mul_complex_Ioi (by simp [hm i]) 0)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem integral_product_laplace_exp {α : Type*} [Fintype α]
    (ℓ : V →L[ℝ] ℝ) (m : α → V) (hm : ∀ i, 0<ℓ (m i)) (u : V) :
    (∫ y, ∏ i, Complex.exp (-laplaceFrequency ℓ (m i) u * (y i:ℂ))
      ∂positiveOrthantMeasure α) = ∏ i, (laplaceFrequency ℓ (m i) u)⁻¹ := by
  rw [positiveOrthantMeasure,integral_fintype_prod_eq_prod
    (fun i (y : ℝ) => Complex.exp (-laplaceFrequency ℓ (m i) u * (y:ℂ)))]
  apply Finset.prod_congr rfl
  intro i _
  simpa using integral_exp_mul_complex_Ioi (a:=-laplaceFrequency ℓ (m i) u)
    (by simp [hm i]) 0

theorem schwartz_product_laplace_integrable {α : Type*} [Fintype α]
    (Ψ : SchwartzMap V ℂ) (ℓ : V →L[ℝ] ℝ) (m : α → V) (hm : ∀ i, 0<ℓ (m i)) :
    Integrable (fun z : V × (α → ℝ) => Ψ z.1 *
      ∏ i, Complex.exp (-laplaceFrequency ℓ (m i) z.1 * (z.2 i:ℂ)))
      (volume.prod (positiveOrthantMeasure α)) := by
  have he : Integrable (fun y : α → ℝ => ∏ i, Real.exp (-ℓ (m i)*y i))
      (positiveOrthantMeasure α) := by
    exact Integrable.fintype_prod (f := fun i y => Real.exp (-ℓ (m i)*y))
      (μ := fun _ => volume.restrict (Ioi 0))
      (fun i => integrableOn_exp_mul_Ioi (by linarith [hm i]) 0)
  have hb := (Ψ.integrable (μ := volume)).norm.mul_prod he
  apply hb.mono'
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul (Ψ.continuous.comp continuous_fst)
    apply continuous_finsetProd
    intro i _
    unfold laplaceFrequency
    fun_prop
  · filter_upwards [] with z
    rw [norm_mul,norm_product_laplace_exp]

theorem schwartz_product_laplace_interchange {α : Type*} [Fintype α]
    (Ψ : SchwartzMap V ℂ) (ℓ : V →L[ℝ] ℝ) (m : α → V) (hm : ∀ i, 0<ℓ (m i)) :
    (∫ u : V, Ψ u*(∏ i, (laplaceFrequency ℓ (m i) u)⁻¹)) =
      ∫ y, (∫ u : V, Ψ u *
        Complex.exp (-(ℓ (rayVector m y):ℂ)-Complex.I*(inner ℝ u (rayVector m y):ℂ)))
        ∂positiveOrthantMeasure α := by
  calc
    _ = ∫ u : V, ∫ y, Ψ u*(∏ i, Complex.exp (-laplaceFrequency ℓ (m i) u * (y i:ℂ)))
        ∂positiveOrthantMeasure α := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [integral_const_mul,integral_product_laplace_exp ℓ m hm]
    _ = ∫ y, (∫ u : V, Ψ u*(∏ i, Complex.exp (-laplaceFrequency ℓ (m i) u * (y i:ℂ))))
        ∂positiveOrthantMeasure α :=
      integral_integral_swap (schwartz_product_laplace_integrable Ψ ℓ m hm)
    _ = _ := by simp only [product_laplace_exp_eq]

theorem sourceFourier_product_laplace {α : Type*} [Fintype α]
    (ℓ : V →L[ℝ] ℝ) (F : V → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (m : α → V) (hm : ∀ i, 0<ℓ (m i)) :
    (∫ u : V, sourceFourier ℓ F hF hFs u*(∏ i, (laplaceFrequency ℓ (m i) u)⁻¹)) =
      ∫ y, F (rayVector m y) ∂positiveOrthantMeasure α := by
  rw [schwartz_product_laplace_interchange _ ℓ m hm]
  simp only [sourceFourier_inversion]

theorem sourceFourier_derivative_laplace {α : Type*} [Fintype α]
    (ℓ : V →L[ℝ] ℝ) (ms : List V) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (m : α → V) (hm : ∀ i, 0<ℓ (m i)) :
    (∫ u : V, sourceFourier ℓ F hF hFs u *
      (ms.map (fun m => laplaceFrequency ℓ m u)).prod *
      (∏ i, (laplaceFrequency ℓ (m i) u)⁻¹)) =
      ∫ y, signedDirections ms F (rayVector m y) ∂positiveOrthantMeasure α := by
  rw [← sourceFourier_product_laplace ℓ (signedDirections ms F)
    (signedDirections_compact ms F hF) (signedDirections_smooth ms F hFs) m hm]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [sourceFourier_signedDirections ℓ ms F hF hFs u]
  simp only [laplaceFrequency,mul_comm (sourceFourier ℓ F hF hFs u)]

end FourierLaplace

theorem fiberKernel_card_le_two {ι : Type*} (S : Finset ι) (hS : S.card≤2) (w : ι → ℂ) :
    fiberKernel S w = (∏ i∈S, w i)*if S.card=2 then (∑ i∈S, w i)⁻¹ else 1 := by
  classical
  have hc : S.card=0 ∨ S.card=1 ∨ S.card=2 := by omega
  rcases hc with hc|hc|hc
  · have hs : S=∅ := Finset.card_eq_zero.mp hc
    subst S
    simp [fiberKernel,nonemptySubsets]
  · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp hc
    simp [fiberKernel_singleton]
  · obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hc
    simp [fiberKernel_pair hij,hij,div_eq_mul_inv]

theorem familyKernel_small_fibers {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) (hR : ∀ i, b i∈R)
    (hcard : ∀ r∈R, (Finset.univ.filter fun i => b i=r).card≤2) (w : ι → ℂ) :
    familyKernel (fiberSubsetFamily b R) w =
      (∏ i, w i)*(∏ r∈R.filter (fun r => (Finset.univ.filter fun i => b i=r).card=2),
        (∑ i∈Finset.univ.filter (fun i => b i=r), w i)⁻¹) := by
  classical
  rw [familyKernel_fibers]
  calc
    _ = ∏ r∈R, (∏ i∈Finset.univ.filter (fun i => b i=r), w i)*
        (if (Finset.univ.filter (fun i => b i=r)).card=2 then
          (∑ i∈Finset.univ.filter (fun i => b i=r), w i)⁻¹ else 1) := by
      apply Finset.prod_congr rfl
      intro r hr
      exact fiberKernel_card_le_two _ (hcard r hr) w
    _ = _ := by
      rw [Finset.prod_mul_distrib,Finset.prod_fiberwise_of_maps_to (fun i _ => hR i)]
      congr 1
      exact (Finset.prod_filter ..).symm

section SmallFiberCoefficient

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def coordinateDirectionList (ι : Type*) [Fintype ι] :
    List (EuclideanSpace ℝ ι) := by
  classical
  exact Finset.univ.toList.map (fun i => EuclideanSpace.single i (1:ℝ))

noncomputable def doubleFibers {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) : Finset α := by
  classical
  exact R.filter (fun r => (Finset.univ.filter (fun i => b i=r)).card=2)

noncomputable def fiberRay {ι α : Type*} [Fintype ι]
    (b : ι → α) (r : α) : EuclideanSpace ℝ ι := by
  classical
  exact ∑ i∈Finset.univ.filter (fun i => b i=r), EuclideanSpace.single i (1:ℝ)

@[simp] theorem laplaceFrequency_coordinate {ι : Type*} [Fintype ι]
    (i : ι) (u : EuclideanSpace ℝ ι) :
    laplaceFrequency (fourierCoordinateSum ι) (EuclideanSpace.single i (1:ℝ)) u =
      frequencyW (u i) := by
  classical
  simp [laplaceFrequency,frequencyW,fourierCoordinateSum_apply,EuclideanSpace.inner_single_right]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem laplaceFrequency_sum {α : Type*} (ℓ : V →L[ℝ] ℝ) (S : Finset α)
    (m : α → V) (u : V) :
    laplaceFrequency ℓ (∑ i∈S, m i) u = ∑ i∈S, laplaceFrequency ℓ (m i) u := by
  simp [laplaceFrequency,map_sum,inner_sum,Complex.ofReal_sum,Finset.mul_sum,Finset.sum_add_distrib]

@[simp] theorem laplaceFrequency_fiberRay {ι α : Type*} [Fintype ι]
    (b : ι → α) (r : α) (u : EuclideanSpace ℝ ι) :
    laplaceFrequency (fourierCoordinateSum ι) (fiberRay b r) u =
      ∑ i∈Finset.univ.filter (fun i => b i=r), frequencyW (u i) := by
  classical
  simp [fiberRay,laplaceFrequency_sum]

@[simp] theorem coordinateDirectionList_multiplier {ι : Type*} [Fintype ι]
    (u : EuclideanSpace ℝ ι) :
    ((coordinateDirectionList ι).map (fun m => laplaceFrequency (fourierCoordinateSum ι) m u)).prod =
      ∏ i, frequencyW (u i) := by
  classical
  simp [coordinateDirectionList,List.map_map,Function.comp_def]

theorem fiberRay_positive {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) (r : doubleFibers b R) :
    0 < fourierCoordinateSum ι (fiberRay b r.val) := by
  classical
  have hr : (Finset.univ.filter (fun i => b i=r.val)).card=2 :=
    (Finset.mem_filter.mp r.property).2
  have h := congrArg Complex.re (laplaceFrequency_fiberRay b r.val (0 : EuclideanSpace ℝ ι))
  simp only [laplaceFrequency_re,Complex.re_sum,frequencyW_re,Finset.sum_const] at h
  rw [h,hr]
  norm_num

theorem small_fiber_kernelConstant {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) (hR : ∀ i, b i∈R)
    (hcard : ∀ r∈R, (Finset.univ.filter fun i => b i=r).card≤2)
    (F : EuclideanSpace ℝ ι → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    kernelConstant (sourceFourier (fourierCoordinateSum ι) F hF hFs) (fiberSubsetFamily b R) =
      ∫ y, signedDirections (coordinateDirectionList ι) F
        (rayVector (fun r : doubleFibers b R => fiberRay b r.val) y)
          ∂positiveOrthantMeasure (doubleFibers b R) := by
  classical
  rw [← sourceFourier_derivative_laplace (fourierCoordinateSum ι) (coordinateDirectionList ι)
    F hF hFs (fun r : doubleFibers b R => fiberRay b r.val) (fiberRay_positive b R)]
  unfold kernelConstant
  apply integral_congr_ae
  filter_upwards [] with u
  rw [contourKernel,familyKernel_small_fibers b R hR hcard,coordinateDirectionList_multiplier]
  simp only [laplaceFrequency_fiberRay]
  have hp := Finset.prod_coe_sort (s := doubleFibers b R)
    (f := fun r : α => (∑ i∈Finset.univ.filter (fun i => b i=r), frequencyW (u i))⁻¹)
  rw [hp,mul_assoc]
  rfl

end SmallFiberCoefficient

theorem shiftFamily_nonempty {ι : Type*} [Fintype ι] (b : ι → ℤ) :
    ∀ S∈shiftFamily b, S.Nonempty := by
  intro S hS
  exact ((mem_fiberSubsetFamily b (Finset.univ.image b) S).mp hS).1

theorem residueFamily_nonempty {ι : Type*} [Fintype ι] (b : ι → ℤ) (p : ℕ) :
    ∀ S∈residueFamily b p, S.Nonempty := by
  intro S hS
  exact ((mem_fiberSubsetFamily _ _ S).mp hS).1

theorem markedResidueFamily_nonempty {ι : Type*} [Fintype ι] (b : ι → ℤ) (p : ℕ) (a : ℤ) :
    ∀ S∈markedResidueFamily b p a, S.Nonempty := by
  intro S hS
  exact ((mem_markedResidueFamily b p a S).mp hS).1

theorem shiftFamily_sign_sum {ι : Type*} [Fintype ι] (b : ι → ℤ) :
    (∑ S∈shiftFamily b, (-1:ℤ)^S.card) = -((Finset.univ.image b).card:ℤ) := by
  apply fiberSubsetFamily_sign_sum
  intro r hr
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hr
  exact ⟨i,hi⟩

theorem unmarked_analyticDensity_uniform_asymptotic {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) (t β : ℕ) (hβ : 0<β)
    (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ)) :
    ∃ E : ℝ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ L : ℝ in atTop, ∀ b : ι → ℤ, shiftFamily b=B → ∀ D : ℕ,
      (∀ i, (b i).natAbs≤D) → 2*D≤densityCutoff β L →
      ‖(L:ℂ)^t*analyticDensity 0 (residueFamily b) L F -
        (singularSeries (Finset.univ.image b):ℂ)*
          kernelConstant (sourceFourier (fourierCoordinateSum ι) F hF hFs) B‖ ≤ E L := by
  obtain ⟨E,hE,hbound⟩ := tupleFourier_integral_uniform_asymptotic
    (sourceFourier (fourierCoordinateSum ι) F hF hFs) B hB
    (2^Fintype.card ι) t β (subsetFamily_card_le B) hβ ht
  refine ⟨E,hE,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with L hbound hL
  intro b hb D hD hDL
  have hA := fun p : Nat.Primes => residueFamily_nonempty b p
  have hR := fun p : Nat.Primes => subsetFamily_card_le (residueFamily b p)
  have hgen : ∀ p : Nat.Primes, densityCutoff β L<(p:ℕ) → residueFamily b p=B := by
    intro p hp
    exact (residueFamily_generic_of_bound b hD (hDL.trans_lt hp)).trans hb
  have h := hbound 0 (by omega) (residueFamily b) hA hR hgen
  rw [← analyticDensity_eq_integral (by omega) (residueFamily b) hL hA hR F hF hFs] at h
  rw [← hb,unmarked_eulerGlobal_zero] at h
  simpa only [hb] using h

theorem marked_analyticDensity_uniform_asymptotic {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) (t β : ℕ) (hβ : 0<β)
    (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ)) :
    ∃ E : ℝ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ L : ℝ in atTop, ∀ b : ι → ℤ, shiftFamily b=B → ∀ a : ℤ,
      (∀ i, b i≠a) → ∀ D : ℕ, (∀ i, (b i).natAbs≤D) → a.natAbs≤D →
      2*D≤densityCutoff β L →
      ‖(L:ℂ)^t*analyticDensity 1 (fun p => markedResidueFamily b p a) L F -
        (singularSeries (insert a (Finset.univ.image b)):ℂ)*
          kernelConstant (sourceFourier (fourierCoordinateSum ι) F hF hFs) B‖ ≤ E L := by
  obtain ⟨E,hE,hbound⟩ := tupleFourier_integral_uniform_asymptotic
    (sourceFourier (fourierCoordinateSum ι) F hF hFs) B hB
    (2^Fintype.card ι) t β (subsetFamily_card_le B) hβ ht
  refine ⟨E,hE,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with L hbound hL
  intro b hb a ha D hD haD hDL
  have hA := fun p : Nat.Primes => markedResidueFamily_nonempty b p a
  have hR := fun p : Nat.Primes => subsetFamily_card_le (markedResidueFamily b p a)
  have hgen : ∀ p : Nat.Primes, densityCutoff β L<(p:ℕ) → markedResidueFamily b p a=B := by
    intro p hp
    exact (markedResidueFamily_generic_of_bound b a ha hD haD (hDL.trans_lt hp)).trans hb
  have h := hbound 1 (by omega) (fun p => markedResidueFamily b p a) hA hR hgen
  rw [← analyticDensity_eq_integral (by omega) (fun p => markedResidueFamily b p a)
    hL hA hR F hF hFs] at h
  rw [← hb,marked_eulerGlobal_zero b a ha] at h
  simpa only [hb] using h

theorem unmarked_average_uniform_asymptotic {n : ℕ}
    (F : (Fin (n+1) → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i, 0≤v i) → |F v|≤M)
    (B : Finset (Finset (Fin (n+1)))) (hB : ∀ S∈B, S.Nonempty)
    (t β : ℕ) (hβ : 0<β) (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ)) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ X : ℕ in atTop, ∀ b : Fin (n+1) → ℕ,
      shiftFamily (fun i => (b i:ℤ))=B → ∀ D : ℕ,
      (∀ i, b i≤D) → 2*D≤densityCutoff β (Real.log X) →
      ‖(Real.log X:ℂ)^t*(average X (fun m => divisorSum X F m b):ℂ) -
        (singularSeries (Finset.univ.image fun i => (b i:ℤ)):ℂ)*
          kernelConstant (sourceFourier (fourierCoordinateSum (Fin (n+1)))
            (fun v => (F v.ofLp:ℂ)) hF hFs) B‖ ≤ E X := by
  obtain ⟨E,hE,hEbound⟩ := unmarked_analyticDensity_uniform_asymptotic
    (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)) hF hFs B hB t β hβ ht
  let err : ℝ → ℝ := fun L => (2*M*(1+rho)^n)*L^(n+t)*Real.exp (-(1-rho)*L)
  have herr : Tendsto err atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (n+t:ℕ) (1-rho) (by linarith)).const_mul (2*M*(1+rho)^n)
    simpa only [Real.rpow_natCast,mul_zero,mul_assoc,err] using h
  have hlog : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨fun X => err (Real.log X)+E (Real.log X),?_,?_⟩
  · simpa only [Function.comp_def,add_zero] using (herr.comp hlog).add (hE.comp hlog)
  filter_upwards [hlog.eventually hEbound,eventually_ge_atTop 2,
    hlog.eventually (eventually_ge_atTop (1:ℝ))] with X hEX hX hL
  intro b hb D hD hDL
  have hb' : ∀ i, ((b i:ℤ)).natAbs≤D := by simpa only [Int.natAbs_natCast] using hD
  have hden := hEX (fun i => (b i:ℤ)) hb D hb' hDL
  rw [analyticDensity_eq_unmarkedDensitySum hX hbudget b] at hden
  have hcomp : ‖(Real.log X:ℂ)^t*(average X (fun m => divisorSum X F m b):ℂ)-
      (Real.log X:ℂ)^t*(unmarkedDensitySum X F rho b:ℂ)‖ ≤ err (Real.log X) := by
    rw [← mul_sub,← Complex.ofReal_sub,norm_mul,norm_pow,Complex.norm_real,
      Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤Real.log X)]
    have hh := mul_le_mul_of_nonneg_left
      (unmarked_arithmetic_error_exponential hX hL hrho hbudget hM hbound b)
      (pow_nonneg (by linarith : 0≤Real.log X) t)
    convert hh using 1
    all_goals first | rfl | (simp only [err,pow_add]; ring)
  apply le_trans ?_ (add_le_add hcomp hden)
  simpa only [dist_eq_norm] using (dist_triangle
    ((Real.log X:ℂ)^t*(average X (fun m => divisorSum X F m b):ℂ))
    ((Real.log X:ℂ)^t*(unmarkedDensitySum X F rho b:ℂ)) _)

theorem marked_average_uniform_asymptotic (hBV : BombieriVinogradov) {n : ℕ}
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrhohalf : rho<1/2) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i, 0≤v i) → |F v|≤M)
    (B : Finset (Finset (Fin n))) (hB : ∀ S∈B, S.Nonempty)
    (t β : ℕ) (hβ : 0<β) (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ))
    (H : ℕ → ℕ) {D₀ B₀ : ℝ} (hD₀ : 0<D₀)
    (hH : ∀ᶠ X : ℕ in atTop, (H X:ℝ)≤D₀*(Real.log (X:ℝ))^B₀) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ X : ℕ in atTop, ∀ b : Fin n → ℕ,
      shiftFamily (fun i => (b i:ℤ))=B → ∀ a : ℕ, a≤H X →
      (∀ i, b i≠a) → ∀ D : ℕ, (∀ i, b i≤D) → a≤D →
      2*D≤densityCutoff β (Real.log X) →
      ‖(Real.log X:ℂ)^t*(average X (fun m => divisorSum X F m b*theta (m+a)):ℂ) -
        (singularSeries (insert (a:ℤ) (Finset.univ.image fun i => (b i:ℤ))):ℂ)*
          kernelConstant (sourceFourier (fourierCoordinateSum (Fin n))
            (fun v => (F v.ofLp:ℂ)) hF hFs) B‖ ≤ E X := by
  obtain ⟨E,hE,hEbound⟩ := marked_analyticDensity_uniform_asymptotic
    (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)) hF hFs B hB t β hβ ht
  let err : ℕ → ℝ := fun X => M*(weightedErrorSum (2^n) X (H X) (powerModulus rho X)/X)*
    (Real.log (X:ℝ))^t
  have herr : Tendsto err atTop (𝓝 0) := by
    have h := (weightedErrorSum_log_decay hBV (2^n) H hrho hrhohalf hD₀ hH t).const_mul M
    simpa only [mul_zero,mul_assoc,err] using h
  have hlog : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨fun X => err X+E (Real.log X),?_,?_⟩
  · simpa only [Function.comp_def,add_zero] using herr.add (hE.comp hlog)
  filter_upwards [hlog.eventually hEbound,eventually_ge_atTop 2] with X hEX hX
  intro b hb a haH ha D hD haD hDL
  have hb' : ∀ i, ((b i:ℤ)).natAbs≤D := by simpa only [Int.natAbs_natCast] using hD
  have ha' : ∀ i, (b i:ℤ)≠(a:ℤ) := fun i he => ha i (by exact_mod_cast he)
  have hden := hEX (fun i => (b i:ℤ)) hb a ha' D hb'
    (by simpa only [Int.natAbs_natCast] using haD) hDL
  rw [analyticDensity_eq_markedDensitySum hX hbudget b a] at hden
  have hXR : (0:ℝ)<X := by exact_mod_cast (by omega : 0<X)
  have hY : ⌊Real.exp (rho*Real.log (X:ℝ))⌋₊ = powerModulus rho X := by
    unfold powerModulus
    rw [Real.rpow_def_of_pos hXR,mul_comm rho]
  have he := marked_arithmetic_error hX haH (by linarith : rho≤1) hbudget hM hbound b
  rw [hY] at he
  have he' : |average X (fun m => divisorSum X F m b*theta (m+a))-
      markedDensitySum X F rho b a| ≤
      M/X*weightedErrorSum (2^n) X (H X) (powerModulus rho X) := by
    simpa only [weightedErrorSum,Nat.cast_pow] using he
  have hcomp : ‖(Real.log X:ℂ)^t*(average X (fun m => divisorSum X F m b*theta (m+a)):ℂ)-
      (Real.log X:ℂ)^t*(markedDensitySum X F rho b a:ℂ)‖ ≤ err X := by
    rw [← mul_sub,← Complex.ofReal_sub,norm_mul,norm_pow,Complex.norm_real,
      Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (log_pos_of_two_le hX).le]
    have hh := mul_le_mul_of_nonneg_left he' (pow_nonneg (log_pos_of_two_le hX).le t)
    convert hh using 1
    all_goals first | rfl | (simp only [err]; ring)
  apply le_trans ?_ (add_le_add hcomp hden)
  simpa only [dist_eq_norm] using (dist_triangle
    ((Real.log X:ℂ)^t*(average X (fun m => divisorSum X F m b*theta (m+a)):ℂ))
    ((Real.log X:ℂ)^t*(markedDensitySum X F rho b a:ℂ)) _)

open Topology

open scoped Convolution ContDiff Pointwise

noncomputable def negativeCube {ι : Type*} [Fintype ι] (T : ℝ) : Set (EuclideanSpace ℝ ι) :=
  {x | ∀ i, -T≤x i ∧ x i≤0}

theorem negativeCube_compact {ι : Type*} [Fintype ι] (T : ℝ) :
    IsCompact (negativeCube (ι:=ι) T) := by
  have h := (isCompact_univ_pi (fun _ : ι => isCompact_Icc (a := -T) (b := (0:ℝ)))).image
    (PiLp.homeomorph 2 (fun _ : ι => ℝ)).symm.continuous
  convert h using 1
  ext x
  constructor
  · intro hx
    refine ⟨x.ofLp, ?_, ?_⟩
    · simpa only [negativeCube, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_Icc] using hx
    · rfl
  · rintro ⟨y, hy, rfl⟩
    change ∀ i, -T≤y i ∧ y i≤0
    simpa only [Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_Icc] using hy

noncomputable def cubeIndicator {ι : Type*} [Fintype ι] (T : ℝ) : EuclideanSpace ℝ ι → ℝ :=
  (negativeCube T).indicator (fun _ => 1)

theorem cubeIndicator_compact {ι : Type*} [Fintype ι] (T : ℝ) :
    HasCompactSupport (cubeIndicator (ι:=ι) T) := by
  apply (negativeCube_compact T).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (negativeCube_compact T).isClosed
  exact Set.support_indicator_subset

theorem cubeIndicator_integrable {ι : Type*} [Fintype ι] (T : ℝ) :
    Integrable (cubeIndicator (ι:=ι) T) := by
  apply (integrable_indicator_iff (negativeCube_compact T).measurableSet).mpr
  exact continuous_const.continuousOn.integrableOn_compact (negativeCube_compact T)

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_LaplaceTransform

section File_OpenAIPrimeGaps_CumulativeProfiles

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

noncomputable def cumulativeExtension {ι : Type*} [Fintype ι]
    (T : ℝ) (f : EuclideanSpace ℝ ι → ℝ) : EuclideanSpace ℝ ι → ℝ :=
  cubeIndicator T ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] f

theorem cumulativeExtension_compact {ι : Type*} [Fintype ι]
    (T : ℝ) (f : EuclideanSpace ℝ ι → ℝ) (hf : HasCompactSupport f) :
    HasCompactSupport (cumulativeExtension T f) :=
  HasCompactSupport.convolution (ContinuousLinearMap.mul ℝ ℝ) (cubeIndicator_compact T) hf

theorem cumulativeExtension_smooth {ι : Type*} [Fintype ι]
    (T : ℝ) (f : EuclideanSpace ℝ ι → ℝ) (hf : HasCompactSupport f)
    (hfs : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (cumulativeExtension T f) :=
  hf.contDiff_convolution_right _ (cubeIndicator_integrable T).locallyIntegrable hfs

noncomputable def cumulativeTail {ι : Type*} [Fintype ι]
    (f : EuclideanSpace ℝ ι → ℝ) (v : EuclideanSpace ℝ ι) : ℝ :=
  ∫ y in {y | ∀ i, v i≤y i}, f y

theorem cumulativeExtension_tail {ι : Type*} [Fintype ι]
    (T : ℝ) (f : EuclideanSpace ℝ ι → ℝ)
    (hf : ∀ y, f y≠0 → ∀ i, y i≤T)
    (v : EuclideanSpace ℝ ι) (hv : ∀ i, 0≤v i) :
    cumulativeExtension T f v = cumulativeTail f v := by
  have hs : MeasurableSet {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i} := by
    rw [Set.ofPred_forall]
    exact (isClosed_iInter fun i => isClosed_le (continuous_const (y := v i)) (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i)).measurableSet
  unfold cumulativeExtension cumulativeTail
  rw [convolution_def]
  change (∫ t, cubeIndicator T t * f (v-t)) = _
  rw [← integral_sub_left_eq_self (fun t => cubeIndicator T t * f (v-t)) volume v]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [sub_sub_cancel]
  by_cases hfy : f y=0
  · simp [Set.indicator,hfy]
  · by_cases hy : ∀ i, v i≤y i
    · rw [Set.indicator_of_mem (s := {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i}) hy]
      have hcube : v-y∈negativeCube T := by
        intro i
        change -T≤v i-y i ∧ v i-y i≤0
        constructor <;> linarith [hf y hfy i,hv i,hy i]
      simp [cubeIndicator,Set.indicator_of_mem hcube]
    · rw [Set.indicator_of_notMem (s := {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i}) hy]
      have hcube : v-y∉negativeCube T := by
        intro h
        apply hy
        intro i
        have := (h i).2
        change v i-y i≤0 at this
        linarith
      simp [cubeIndicator,Set.indicator_of_notMem hcube]

theorem cumulativeTail_budget {ι : Type*} [Fintype ι]
    (tau : ℝ) (f : EuclideanSpace ℝ ι → ℝ)
    (hf : ∀ y, (∀ i, 0≤y i) → tau≤∑ i, y i → f y=0)
    (v : EuclideanSpace ℝ ι) (hv : ∀ i, 0≤v i) (hs : tau≤∑ i, v i) :
    cumulativeTail f v=0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  apply hf y (fun i => (hv i).trans (hy i))
  exact hs.trans (Finset.sum_le_sum fun i _ => hy i)

section GeneralDirections

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

noncomputable def signedDirectionalList (ms : List V) (F : V → ℂ) : V → ℂ :=
  ms.foldr (fun m H v => -fderiv ℝ H v m) F

theorem signedDirectionalList_smooth (ms : List V) (F : V → ℂ)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (signedDirectionalList ms F) := by
  induction ms with
  | nil => exact hF
  | cons m ms ih =>
    exact (ih.fderiv_right (by simp)).clm_apply contDiff_const |>.neg

theorem signedDirectionalList_compact (ms : List V) (F : V → ℂ)
    (hF : HasCompactSupport F) : HasCompactSupport (signedDirectionalList ms F) := by
  induction ms with
  | nil => exact hF
  | cons m ms ih => exact (ih.fderiv_apply ℝ m).neg

theorem signedDirectionalList_affine (ms : List V) (F : W → ℂ)
    (hF : ContDiff ℝ ∞ F) (A : V →L[ℝ] W) (c : W) :
    signedDirectionalList ms (fun v => F (c+A v)) =
      fun v => signedDirectionalList (ms.map A) F (c+A v) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    have hd := signedDirectionalList_smooth (ms.map A) F hF
    have hA (v : V) : HasFDerivAt (fun v => c+A v) A v := by
      simpa using (A.hasFDerivAt (x := v)).const_add c
    ext v
    change -fderiv ℝ (signedDirectionalList ms (fun v => F (c+A v))) v m = _
    rw [ih]
    have he := ((hd.differentiable (by simp) (c+A v)).hasFDerivAt.comp v (hA v)).fderiv
    simp only [Function.comp_def] at he
    rw [he]
    rfl

theorem signedDirectionalList_tsupport (ms : List V) (F : V → ℂ) :
    tsupport (signedDirectionalList ms F) ⊆ tsupport F := by
  induction ms with
  | nil => exact Set.Subset.rfl
  | cons m ms ih =>
    change tsupport (fun v => - fderiv ℝ (signedDirectionalList ms F) v m) ⊆ _
    change tsupport (-(fun v => fderiv ℝ (signedDirectionalList ms F) v m)) ⊆ _
    rw [tsupport_neg]
    exact (tsupport_fderiv_apply_subset ℝ m).trans ih

end GeneralDirections

noncomputable def finTailEmbed (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin (n+1) → ℝ) :=
  let A : (Fin n → ℝ) →ₗ[ℝ] (Fin (n+1) → ℝ) :=
    { toFun := fun x => Fin.cons 0 x
      map_add' := by intros; ext i; cases i using Fin.cases <;> simp
      map_smul' := by intros; ext i; cases i using Fin.cases <;> simp }
  A.toContinuousLinearMap

@[simp] theorem finTailEmbed_apply (n : ℕ) (x : Fin n → ℝ) :
    finTailEmbed n x = Fin.cons 0 x := rfl

noncomputable def finDirections (n : ℕ) : List (Fin n → ℝ) :=
  (List.finRange n).map (fun i => Pi.single i 1)

theorem finTailEmbed_single (n : ℕ) (i : Fin n) :
    finTailEmbed n (Pi.single i 1) = Pi.single i.succ 1 := by
  ext j
  cases j using Fin.cases with
  | zero => simp
  | succ j => simp [Pi.single_apply,Fin.succ_inj]

theorem finDirections_succ (n : ℕ) :
    finDirections (n+1) = Pi.single 0 1 :: (finDirections n).map (finTailEmbed n) := by
  simp only [finDirections,List.finRange_succ,List.map_cons,List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact (finTailEmbed_single n i).symm

theorem fin_cons_affine {n : ℕ} (a : ℝ) (x : Fin n → ℝ) :
    Fin.cons a x = Pi.single 0 a + finTailEmbed n x := by
  ext i
  cases i using Fin.cases <;> simp

theorem fin_cons_closedEmbedding (n : ℕ) (a : ℝ) :
    IsClosedEmbedding (fun x : Fin n → ℝ => (Fin.cons a x : Fin (n+1) → ℝ)) := by
  have h : Function.Injective (finTailEmbed n) := by
    intro x y hxy
    ext i
    have := congrFun hxy i.succ
    simpa using this
  have he := LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr h)
  have hc := (Homeomorph.addLeft (Pi.single 0 a : Fin (n+1) → ℝ)).isClosedEmbedding.comp he
  convert hc using 1
  funext x
  exact fin_cons_affine a x

theorem fin_cons_head_closedEmbedding (n : ℕ) (y : Fin n → ℝ) :
    IsClosedEmbedding (fun a : ℝ => (Fin.cons a y : Fin (n+1) → ℝ)) := by
  have he : IsClosedEmbedding (fun a : ℝ => a • (Pi.single 0 1 : Fin (n+1) → ℝ)) :=
    isClosedEmbedding_smul_left (by intro h; have := congrFun h 0; simp at this)
  have hc := (Homeomorph.addRight (Fin.cons 0 y : Fin (n+1) → ℝ)).isClosedEmbedding.comp he
  convert hc using 1
  ext a i
  cases i using Fin.cases <;> simp

noncomputable def piTailMeasure {n : ℕ} (v : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i => volume.restrict (Ioi (v i)))

instance {n : ℕ} (v : Fin n → ℝ) : SigmaFinite (piTailMeasure v) := by
  unfold piTailMeasure
  infer_instance

instance {n : ℕ} (v : Fin n → ℝ) : IsFiniteMeasureOnCompacts (piTailMeasure v) := by
  unfold piTailMeasure
  infer_instance

theorem piTail_integral_cons {n : ℕ} (v : Fin (n+1) → ℝ)
    (f : (Fin (n+1) → ℝ) → ℂ) (hf : Integrable f (piTailMeasure v)) :
    (∫ x, f x ∂piTailMeasure v) =
      ∫ y, (∫ a in Ioi (v 0), f (Fin.cons a y)) ∂piTailMeasure (fun i => v i.succ) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
  have hm := measurePreserving_piFinSuccAbove
    (fun i : Fin (n+1) => volume.restrict (Ioi (v i))) 0
  have he : ∀ p : ℝ × (Fin n → ℝ), e.symm p = Fin.cons p.1 p.2 := by
    intro p
    simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]
  dsimp only [e] at he
  have hprod : Integrable (fun p : ℝ × (Fin n → ℝ) => f (Fin.cons p.1 p.2))
      ((volume.restrict (Ioi (v 0))).prod (piTailMeasure (fun i => v i.succ))) := by
    have hh := (hm.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hf
    simpa only [Fin.zero_succAbove,he,Function.comp_def,piTailMeasure] using hh
  calc
    _ = ∫ p : ℝ × (Fin n → ℝ), f (Fin.cons p.1 p.2)
        ∂((volume.restrict (Ioi (v 0))).prod (piTailMeasure (fun i => v i.succ))) := by
      have hh := hm.symm.integral_comp' f
      simpa only [Fin.zero_succAbove,he,piTailMeasure] using hh.symm
    _ = _ := integral_prod_symm _ hprod

theorem fin_cons_head_affine {n : ℕ} (a : ℝ) (y : Fin n → ℝ) :
    Fin.cons a y = a • (Pi.single 0 1 : Fin (n+1) → ℝ) + Fin.cons 0 y := by
  ext i
  cases i using Fin.cases <;> simp

theorem fin_cons_hasDerivAt {n : ℕ} (y : Fin n → ℝ) (a : ℝ) :
    HasDerivAt (fun a => (Fin.cons a y : Fin (n+1) → ℝ)) (Pi.single 0 1) a := by
  have he : (fun a : ℝ => (Fin.cons a y : Fin (n+1) → ℝ)) =
      fun a => a • (Pi.single 0 1 : Fin (n+1) → ℝ) + Fin.cons 0 y :=
    funext (fun a => fin_cons_head_affine a y)
  rw [he]
  simpa using ((hasDerivAt_id a).smul_const (Pi.single 0 1 : Fin (n+1) → ℝ)).add_const
    (Fin.cons 0 y)

theorem fin_cons_head_smooth {n : ℕ} (y : Fin n → ℝ) :
    ContDiff ℝ ∞ (fun a => (Fin.cons a y : Fin (n+1) → ℝ)) := by
  have he : (fun a : ℝ => (Fin.cons a y : Fin (n+1) → ℝ)) =
      fun a => a • (Pi.single 0 1 : Fin (n+1) → ℝ) + Fin.cons 0 y :=
    funext (fun a => fin_cons_head_affine a y)
  rw [he]
  fun_prop

theorem fin_cons_tail_smooth {n : ℕ} (a : ℝ) :
    ContDiff ℝ ∞ (fun y : Fin n → ℝ => (Fin.cons a y : Fin (n+1) → ℝ)) := by
  simp_rw [fin_cons_affine]
  fun_prop

theorem piTail_signedDirections_FTC (n : ℕ) (F : (Fin n → ℝ) → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (v : Fin n → ℝ) :
    (∫ x, signedDirectionalList (finDirections n) F x ∂piTailMeasure v) = F v := by
  induction n with
  | zero =>
    simp only [finDirections,List.finRange_zero,List.map_nil,signedDirectionalList,List.foldr_nil]
    unfold piTailMeasure
    rw [Measure.pi_of_empty (x := v)]
    exact integral_dirac F v
  | succ n ih =>
    rw [finDirections_succ]
    let ms := (finDirections n).map (finTailEmbed n)
    let H := signedDirectionalList ms F
    have hHc : HasCompactSupport H := signedDirectionalList_compact ms F hF
    have hHs : ContDiff ℝ ∞ H := signedDirectionalList_smooth ms F hFs
    have hfull : Integrable (signedDirectionalList (Pi.single 0 1 :: ms) F) (piTailMeasure v) :=
      (signedDirectionalList_smooth _ F hFs).continuous.integrable_of_hasCompactSupport
        (signedDirectionalList_compact _ F hF)
    rw [piTail_integral_cons v _ hfull]
    have hinner (y : Fin n → ℝ) :
        (∫ a in Ioi (v 0), signedDirectionalList (Pi.single 0 1 :: ms) F (Fin.cons a y)) =
          H (Fin.cons (v 0) y) := by
      have hc : HasCompactSupport (fun a : ℝ => H (Fin.cons a y)) :=
        hHc.comp_isClosedEmbedding (fin_cons_head_closedEmbedding n y)
      have hs : ContDiff ℝ ∞ (fun a : ℝ => H (Fin.cons a y)) :=
        hHs.comp (fin_cons_head_smooth y)
      have hd (a : ℝ) : deriv (fun a : ℝ => H (Fin.cons a y)) a =
          fderiv ℝ H (Fin.cons a y) (Pi.single 0 1) := by
        exact ((hHs.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt a
          (fin_cons_hasDerivAt y a)).deriv
      have he : (fun a : ℝ => signedDirectionalList (Pi.single 0 1 :: ms) F (Fin.cons a y)) =
          fun a => -deriv (fun a : ℝ => H (Fin.cons a y)) a := by
        funext a
        rw [hd]
        rfl
      rw [he,integral_neg,HasCompactSupport.integral_Ioi_deriv_eq (hs.of_le (by simp)) hc,neg_neg]
    simp_rw [hinner]
    let G : (Fin n → ℝ) → ℂ := fun y => F (Fin.cons (v 0) y)
    have hGc : HasCompactSupport G := hF.comp_isClosedEmbedding (fin_cons_closedEmbedding n (v 0))
    have hGs : ContDiff ℝ ∞ G := hFs.comp (fin_cons_tail_smooth (v 0))
    have hg : (fun y : Fin n → ℝ => H (Fin.cons (v 0) y)) = signedDirectionalList (finDirections n) G := by
      have he := signedDirectionalList_affine (finDirections n) F hFs (finTailEmbed n)
        (Pi.single 0 (v 0))
      simpa only [← fin_cons_affine] using he.symm
    rw [hg,ih G hGc hGs (fun i => v i.succ)]
    dsimp only [G]
    congr 1
    ext i
    cases i using Fin.cases <;> rfl

noncomputable def complexCumulativeExtension {ι : Type*} [Fintype ι]
    (T : ℝ) (F : EuclideanSpace ℝ ι → ℂ) : EuclideanSpace ℝ ι → ℂ :=
  cubeIndicator T ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] F

theorem complexCumulativeExtension_compact {ι : Type*} [Fintype ι]
    (T : ℝ) (F : EuclideanSpace ℝ ι → ℂ) (hF : HasCompactSupport F) :
    HasCompactSupport (complexCumulativeExtension T F) :=
  HasCompactSupport.convolution (ContinuousLinearMap.lsmul ℝ ℝ) (cubeIndicator_compact T) hF

theorem complexCumulativeExtension_smooth {ι : Type*} [Fintype ι]
    (T : ℝ) (F : EuclideanSpace ℝ ι → ℂ) (hF : HasCompactSupport F)
    (hFs : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (complexCumulativeExtension T F) :=
  hF.contDiff_convolution_right _ (cubeIndicator_integrable T).locallyIntegrable hFs

theorem complexCumulativeExtension_tail {ι : Type*} [Fintype ι]
    (T : ℝ) (F : EuclideanSpace ℝ ι → ℂ)
    (hF : ∀ y, F y≠0 → ∀ i, y i≤T)
    (v : EuclideanSpace ℝ ι) (hv : ∀ i, 0≤v i) :
    complexCumulativeExtension T F v = ∫ y in {y | ∀ i, v i≤y i}, F y := by
  have hs : MeasurableSet {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i} := by
    rw [Set.ofPred_forall]
    exact (isClosed_iInter fun i => isClosed_le (continuous_const (y := v i))
      (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i)).measurableSet
  unfold complexCumulativeExtension
  rw [convolution_def]
  change (∫ t, cubeIndicator T t • F (v-t)) = _
  rw [← integral_sub_left_eq_self (fun t => cubeIndicator T t • F (v-t)) volume v]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [sub_sub_cancel]
  by_cases hFy : F y=0
  · simp [Set.indicator,hFy]
  · by_cases hy : ∀ i, v i≤y i
    · rw [Set.indicator_of_mem (s := {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i}) hy]
      have hcube : v-y∈negativeCube T := by
        intro i
        change -T≤v i-y i ∧ v i-y i≤0
        constructor <;> linarith [hF y hFy i,hv i,hy i]
      simp [cubeIndicator,Set.indicator_of_mem hcube]
    · rw [Set.indicator_of_notMem (s := {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i}) hy]
      have hcube : v-y∉negativeCube T := by
        intro h
        apply hy
        intro i
        have := (h i).2
        change v i-y i≤0 at this
        linarith
      simp [cubeIndicator,Set.indicator_of_notMem hcube]

theorem signedDirections_cumulative {ι : Type*} [Fintype ι]
    (T : ℝ) (ms : List (EuclideanSpace ℝ ι)) (F : EuclideanSpace ℝ ι → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    signedDirections ms (complexCumulativeExtension T F) =
      complexCumulativeExtension T (signedDirections ms F) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    ext v
    change -fderiv ℝ (signedDirections ms (complexCumulativeExtension T F)) v m = _
    rw [ih]
    have hc := signedDirections_compact ms F hF
    have hs := signedDirections_smooth ms F hFs
    unfold complexCumulativeExtension
    rw [(hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
      (cubeIndicator_integrable T).locallyIntegrable (hs.of_le (by simp)) v).fderiv]
    rw [convolution_precompR_apply _ (cubeIndicator_integrable T).locallyIntegrable
      (hc.fderiv ℝ) (hs.continuous_fderiv (by simp))]
    simp only [convolution_def,ContinuousLinearMap.lsmul_apply,
      signedDirections,List.foldr_cons,smul_neg,integral_neg]

noncomputable def euclideanFinDirections (n : ℕ) : List (EuclideanSpace ℝ (Fin n)) :=
  (finDirections n).map (EuclideanSpace.equiv (Fin n) ℝ).symm

theorem euclideanTail_signedDirections_FTC (n : ℕ) (F : EuclideanSpace ℝ (Fin n) → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (v : EuclideanSpace ℝ (Fin n)) :
    (∫ x in {x | ∀ i, v i≤x i}, signedDirections (euclideanFinDirections n) F x) = F v := by
  let e := (EuclideanSpace.equiv (Fin n) ℝ).symm
  have hc : HasCompactSupport (fun x => F (e x)) :=
    hF.comp_isClosedEmbedding e.toHomeomorph.isClosedEmbedding
  have hs : ContDiff ℝ ∞ (fun x => F (e x)) := hFs.comp e.contDiff
  have hFTC := piTail_signedDirections_FTC n (fun x => F (e x)) hc hs v.ofLp
  have ha := signedDirectionalList_affine (finDirections n) F hFs e.toContinuousLinearMap 0
  simp only [zero_add] at ha
  have htail : piTailMeasure v.ofLp = volume.restrict (Ici v.ofLp) := by
    unfold piTailMeasure
    rw [← Measure.restrict_pi_pi]
    exact Measure.restrict_congr_set (Measure.univ_pi_Ioi_ae_eq_Ici (μ := fun _ => volume))
  change signedDirectionalList (finDirections n) (fun x => F (e x)) =
    fun x => signedDirections (euclideanFinDirections n) F (e x) at ha
  rw [htail,ha] at hFTC
  have he := (PiLp.volume_preserving_toLp (Fin n)).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
    (signedDirections (euclideanFinDirections n) F) {x | ∀ i, v i≤x i}
  convert he.symm.trans hFTC using 1
  exact congrArg F (by simp [e])

@[simp] theorem euclideanFinDirections_multiplier (n : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    ((euclideanFinDirections n).map
      (fun m => laplaceFrequency (fourierCoordinateSum (Fin n)) m u)).prod =
      ∏ i, frequencyW (u i) := by
  simp only [euclideanFinDirections,finDirections,List.map_map]
  change ((List.finRange n).map (fun i =>
    laplaceFrequency (fourierCoordinateSum (Fin n)) (EuclideanSpace.single i (1:ℝ)) u)).prod = _
  rw [← Fin.prod_univ_def]
  apply Finset.prod_congr rfl
  intro i _
  convert laplaceFrequency_coordinate i u using 1
  congr 2
  exact Subsingleton.elim _ _

theorem signedDirections_coordinate_eq_fin (n : ℕ) (F : EuclideanSpace ℝ (Fin n) → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    signedDirections (coordinateDirectionList (Fin n)) F =
      signedDirections (euclideanFinDirections n) F := by
  ext v
  rw [← sourceFourier_derivative_inversion (fourierCoordinateSum (Fin n))
    (coordinateDirectionList (Fin n)) F hF hFs v,
    ← sourceFourier_derivative_inversion (fourierCoordinateSum (Fin n))
    (euclideanFinDirections n) F hF hFs v]
  apply integral_congr_ae
  filter_upwards [] with u
  change sourceFourier _ F hF hFs u *
    ((coordinateDirectionList (Fin n)).map (fun m => laplaceFrequency _ m u)).prod * _ =
    sourceFourier _ F hF hFs u *
    ((euclideanFinDirections n).map (fun m => laplaceFrequency _ m u)).prod * _
  rw [coordinateDirectionList_multiplier,euclideanFinDirections_multiplier]

theorem complexCumulativeExtension_signed_full (n : ℕ) (T : ℝ)
    (F : EuclideanSpace ℝ (Fin n) → ℂ) (hF : HasCompactSupport F)
    (hFs : ContDiff ℝ ∞ F) (hT : ∀ y∈tsupport F, ∀ i, y i≤T)
    (v : EuclideanSpace ℝ (Fin n)) (hv : ∀ i, 0≤v i) :
    signedDirections (coordinateDirectionList (Fin n)) (complexCumulativeExtension T F) v =
      F v := by
  rw [signedDirections_coordinate_eq_fin n _ (complexCumulativeExtension_compact T F hF)
    (complexCumulativeExtension_smooth T F hF hFs),signedDirections_cumulative T _ F hF hFs]
  rw [complexCumulativeExtension_tail T _ _ v hv]
  · exact euclideanTail_signedDirections_FTC n F hF hFs v
  · intro y hy i
    exact hT y (signedDirectionalList_tsupport (euclideanFinDirections n) F
      (subset_tsupport _ hy)) i

theorem complexCumulativeExtension_ofReal {ι : Type*} [Fintype ι]
    (T : ℝ) (f : EuclideanSpace ℝ ι → ℝ) :
    complexCumulativeExtension T (fun y => (f y:ℂ)) =
      fun v => (cumulativeExtension T f v:ℂ) := by
  ext v
  simp only [complexCumulativeExtension,cumulativeExtension,convolution_def,
    ContinuousLinearMap.lsmul_apply,ContinuousLinearMap.mul_apply',
    Complex.real_smul,← Complex.ofReal_mul,integral_complex_ofReal]

noncomputable def cumulativeProfile {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun v => cumulativeExtension tau (fun y => f y.ofLp) (WithLp.toLp 2 v)

theorem cumulativeProfile_compact {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) : HasCompactSupport (cumulativeProfile tau f) := by
  have hfc : HasCompactSupport (fun y : EuclideanSpace ℝ (Fin n) => f y.ofLp) :=
    hf.comp_isClosedEmbedding (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isClosedEmbedding
  exact (cumulativeExtension_compact tau _ hfc).comp_isClosedEmbedding
    (EuclideanSpace.equiv (Fin n) ℝ).symm.toHomeomorph.isClosedEmbedding

theorem cumulativeProfile_smooth {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (cumulativeProfile tau f) := by
  have hfc : HasCompactSupport (fun y : EuclideanSpace ℝ (Fin n) => f y.ofLp) :=
    hf.comp_isClosedEmbedding (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isClosedEmbedding
  have hF : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => f y.ofLp) :=
    hfs.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff
  exact (cumulativeExtension_smooth tau _ hfc hF).comp
    (EuclideanSpace.equiv (Fin n) ℝ).symm.contDiff

theorem profile_coordinate_upper {n : ℕ} {tau : ℝ} {f : (Fin n → ℝ) → ℝ}
    (hf : tsupport f ⊆ positiveSimplex n tau) (y : Fin n → ℝ) (hy : y∈tsupport f)
    (i : Fin n) : y i≤tau := by
  have hh := hf hy
  exact (Finset.single_le_sum (fun j _ => (hh.1 j).le) (Finset.mem_univ i)).trans hh.2.le

theorem cumulativeProfile_tail {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : tsupport f ⊆ positiveSimplex n tau) (v : Fin n → ℝ) (hv : ∀ i, 0≤v i) :
    cumulativeProfile tau f v = ∫ y in Ici v, f y := by
  unfold cumulativeProfile
  rw [cumulativeExtension_tail tau _ _ _ hv]
  · unfold cumulativeTail
    have hm := (PiLp.volume_preserving_ofLp (Fin n)).setIntegral_preimage_emb
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding f (Ici v)
    exact hm
  · intro y hy i
    exact profile_coordinate_upper hf y.ofLp (subset_tsupport f hy) i

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_CumulativeProfiles

section File_OpenAIPrimeGaps_TensorProfiles

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem cumulativeProfile_budget {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : tsupport f ⊆ positiveSimplex n tau) : HasBudget (cumulativeProfile tau f) tau := by
  intro v hv hsum
  rw [cumulativeProfile_tail tau f hf v hv]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  by_contra hne
  have hh := hf (subset_tsupport f hne)
  have he : tau≤coordinateSum y :=
    hsum.le.trans (Finset.sum_le_sum (fun i _ => hy i))
  exact (not_lt_of_ge he) hh.2

theorem cumulativeProfile_signed_full {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ positiveSimplex n tau)
    (v : EuclideanSpace ℝ (Fin n)) (hv : ∀ i, 0≤v i) :
    signedDirections (coordinateDirectionList (Fin n))
      (fun y : EuclideanSpace ℝ (Fin n) => (cumulativeProfile tau f y.ofLp:ℂ)) v =
      (f v.ofLp:ℂ) := by
  have hfc : HasCompactSupport (fun y : EuclideanSpace ℝ (Fin n) => (f y.ofLp:ℂ)) :=
    (hf.comp_isClosedEmbedding (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isClosedEmbedding).comp_left
      Complex.ofReal_zero
  have hF : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => (f y.ofLp:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hfs.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff)
  have hT : ∀ y∈tsupport (fun y : EuclideanSpace ℝ (Fin n) => (f y.ofLp:ℂ)),
      ∀ i, y i≤tau := by
    intro y hy i
    have hsub := tsupport_comp_subset (g := (Complex.ofReal : ℝ → ℂ)) Complex.ofReal_zero
      (fun y : EuclideanSpace ℝ (Fin n) => f y.ofLp)
    have hp := tsupport_comp_subset_preimage f (EuclideanSpace.equiv (Fin n) ℝ).continuous
    exact profile_coordinate_upper hsupp y.ofLp (hp (hsub hy)) i
  have hh := complexCumulativeExtension_signed_full n tau _ hfc hF hT v hv
  rw [complexCumulativeExtension_ofReal] at hh
  convert hh using 1
  congr 2

noncomputable def appendMeasurableEquiv (n m : ℕ) :
    ((Fin n → ℝ) × (Fin m → ℝ)) ≃ᵐ (Fin (n+m) → ℝ) :=
  (Fin.appendHomeomorph n m).toMeasurableEquiv

@[simp] theorem appendMeasurableEquiv_apply (n m : ℕ) (p : (Fin n → ℝ) × (Fin m → ℝ)) :
    appendMeasurableEquiv n m p = Fin.append p.1 p.2 := rfl

theorem appendMeasurableEquiv_measurePreserving (n m : ℕ) :
    MeasurePreserving (appendMeasurableEquiv n m) := by
  let e := (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (n+m) => ℝ) finSumFinEquiv)
  have he : appendMeasurableEquiv n m=e := by
    ext p i
    change Fin.append p.1 p.2 i = e p i
    cases i using Fin.addCases with
    | left i => simp [e,MeasurableEquiv.coe_piCongrLeft,
        MeasurableEquiv.coe_sumPiEquivProdPi_symm,Equiv.piCongrLeft]
    | right i => simp [e,MeasurableEquiv.coe_piCongrLeft,
        MeasurableEquiv.coe_sumPiEquivProdPi_symm,Equiv.piCongrLeft]
  rw [he]
  exact (volume_measurePreserving_piCongrLeft (fun _ : Fin (n+m) => ℝ) finSumFinEquiv).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ Fin m => ℝ))

noncomputable def tensorProfile {n m : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin m → ℝ) → ℝ) (v : Fin (n+m) → ℝ) : ℝ :=
  f (fun i => v (i.castAdd m)) * g (fun i => v (i.natAdd n))

@[simp] theorem tensorProfile_append {n m : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin m → ℝ) → ℝ) (v : Fin n → ℝ) (w : Fin m → ℝ) :
    tensorProfile f g (Fin.append v w)=f v*g w := by
  simp [tensorProfile]

theorem tensorProfile_compact {n m : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin m → ℝ) → ℝ) (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    HasCompactSupport (tensorProfile f g) := by
  have hk : IsCompact ((tsupport f) ×ˢ (tsupport g)) := hf.isCompact.prod hg.isCompact
  have hh : HasCompactSupport (fun p : (Fin n → ℝ) × (Fin m → ℝ) => f p.1*g p.2) := by
    apply hk.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hk.isClosed
    intro p hp
    have hm := mul_ne_zero_iff.mp hp
    exact ⟨subset_tsupport f hm.1,subset_tsupport g hm.2⟩
  exact hh.comp_isClosedEmbedding (Fin.appendHomeomorph n m).symm.isClosedEmbedding

theorem tensorProfile_smooth {n m : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin m → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (tensorProfile f g) := by
  unfold tensorProfile
  exact (hf.comp (contDiff_pi.mpr (fun i => contDiff_apply ℝ ℝ (i.castAdd m)))).mul
    (hg.comp (contDiff_pi.mpr (fun i => contDiff_apply ℝ ℝ (i.natAdd n))))

theorem tensorProfile_tsupport {n m : ℕ} {a b : ℝ}
    (f : (Fin n → ℝ) → ℝ) (g : (Fin m → ℝ) → ℝ)
    (hf : tsupport f ⊆ positiveSimplex n a) (hg : tsupport g ⊆ positiveSimplex m b) :
    tsupport (tensorProfile f g) ⊆ positiveSimplex (n+m) (a+b) := by
  intro v hv
  have hleft : (fun i : Fin n => v (i.castAdd m)) ∈ tsupport f := by
    exact tsupport_comp_subset_preimage (f := fun x : Fin (n+m) → ℝ =>
      fun i : Fin n => x (i.castAdd m)) f
      (continuous_pi (fun i => continuous_apply _)) (tsupport_mul_subset_left hv)
  have hright : (fun i : Fin m => v (i.natAdd n)) ∈ tsupport g := by
    exact tsupport_comp_subset_preimage (f := fun x : Fin (n+m) → ℝ =>
      fun i : Fin m => x (i.natAdd n)) g
      (continuous_pi (fun i => continuous_apply _)) (tsupport_mul_subset_right hv)
  refine ⟨?_,?_⟩
  · intro i
    cases i using Fin.addCases with
    | left i => exact (hf hleft).1 i
    | right i => exact (hg hright).1 i
  · change (∑ i, v i)<a+b
    rw [Fin.sum_univ_add]
    exact add_lt_add (hf hleft).2 (hg hright).2

theorem tensorProfile_tail {n m : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin m → ℝ) → ℝ) (v : Fin n → ℝ) (w : Fin m → ℝ) :
    (∫ y in Ici (Fin.append v w), tensorProfile f g y) =
      (∫ y in Ici v, f y)*(∫ y in Ici w, g y) := by
  have hd : (appendMeasurableEquiv n m) ⁻¹' Ici (Fin.append v w) = (Ici v) ×ˢ (Ici w) := by
    ext p
    change (∀ i, Fin.append v w i≤Fin.append p.1 p.2 i) ↔ _
    constructor
    · intro h
      exact ⟨fun i => by simpa using h (i.castAdd m),fun i => by simpa using h (i.natAdd n)⟩
    · rintro ⟨h1,h2⟩ i
      cases i using Fin.addCases with
      | left i => simpa using h1 i
      | right i => simpa using h2 i
  have hm := (appendMeasurableEquiv_measurePreserving n m).setIntegral_preimage_emb
    (appendMeasurableEquiv n m).measurableEmbedding (tensorProfile f g) (Ici (Fin.append v w))
  rw [hd] at hm
  rw [← hm]
  simp only [appendMeasurableEquiv_apply,tensorProfile_append]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact integral_prod_mul f g

theorem cumulativeProfile_tensor {n m : ℕ} {a b : ℝ}
    (f : (Fin n → ℝ) → ℝ) (g : (Fin m → ℝ) → ℝ)
    (hf : tsupport f ⊆ positiveSimplex n a) (hg : tsupport g ⊆ positiveSimplex m b)
    (v : Fin n → ℝ) (w : Fin m → ℝ) (hv : ∀ i, 0≤v i) (hw : ∀ i, 0≤w i) :
    cumulativeProfile (a+b) (tensorProfile f g) (Fin.append v w) =
      cumulativeProfile a f v*cumulativeProfile b g w := by
  rw [cumulativeProfile_tail (a+b) _ (tensorProfile_tsupport f g hf hg),
    cumulativeProfile_tail a f hf _ hv,cumulativeProfile_tail b g hg _ hw,tensorProfile_tail]
  intro i
  cases i using Fin.addCases with
  | left i => simpa using hv i
  | right i => simpa using hw i

@[simp] theorem logCoordinates_append (X : ℕ) {n m : ℕ}
    (d : Fin n → ℕ) (e : Fin m → ℕ) :
    logCoordinates X (Fin.append d e)=Fin.append (logCoordinates X d) (logCoordinates X e) := by
  ext i
  cases i using Fin.addCases <;> simp [logCoordinates]

@[simp] theorem divisorCoefficient_tensor (X : ℕ) {n m : ℕ}
    (F : (Fin n → ℝ) → ℝ) (G : (Fin m → ℝ) → ℝ) (d : Fin n → ℕ) (e : Fin m → ℕ) :
    divisorCoefficient X (tensorProfile F G) (Fin.append d e)=
      divisorCoefficient X F d*divisorCoefficient X G e := by
  simp only [divisorCoefficient,logCoordinates_append,tensorProfile_append,Fin.prod_univ_add,
    Fin.append_left,Fin.append_right]
  ring

theorem divisorSum_tensor (X M : ℕ) {n m : ℕ}
    (F : (Fin n → ℝ) → ℝ) (G : (Fin m → ℝ) → ℝ) (b : Fin n → ℕ) (c : Fin m → ℕ) :
    divisorSum X (tensorProfile F G) M (Fin.append b c)=
      divisorSum X F M b*divisorSum X G M c := by
  classical
  unfold divisorSum
  rw [Finset.sum_mul_sum, ←Finset.sum_product']
  symm
  apply Finset.sum_equiv (Fin.appendEquiv n m)
  · intro p
    simp only [Finset.mem_product,Fintype.mem_piFinset,Fin.appendEquiv_apply]
    constructor
    · rintro ⟨h1,h2⟩ i
      cases i using Fin.addCases with
      | left i => simpa using h1 i
      | right i => simpa using h2 i
    · intro h
      exact ⟨fun i => by simpa using h (i.castAdd m),fun i => by simpa using h (i.natAdd n)⟩
  · intro p _
    exact (divisorCoefficient_tensor X F G p.1 p.2).symm

theorem divisorSum_congr_orthant {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ℕ} (hX : 2≤X) (M : ℕ) (b : ι → ℕ) (F G : (ι → ℝ) → ℝ)
    (hFG : ∀ v, (∀ i, 0≤v i) → F v=G v) : divisorSum X F M b=divisorSum X G M b := by
  apply Finset.sum_congr rfl
  intro d hd
  unfold divisorCoefficient
  congr 1
  apply hFG
  apply logCoordinates_nonneg hX
  intro i
  exact Nat.pos_of_mem_divisors ((Fintype.mem_piFinset.mp hd) i)

theorem divisorSum_cumulative_tensor {n m : ℕ} {a b : ℝ}
    (f : (Fin n → ℝ) → ℝ) (g : (Fin m → ℝ) → ℝ)
    (hf : tsupport f ⊆ positiveSimplex n a) (hg : tsupport g ⊆ positiveSimplex m b)
    {X : ℕ} (hX : 2≤X) (M : ℕ) (s : Fin n → ℕ) (t : Fin m → ℕ) :
    divisorSum X (cumulativeProfile (a+b) (tensorProfile f g)) M (Fin.append s t)=
      divisorSum X (cumulativeProfile a f) M s*divisorSum X (cumulativeProfile b g) M t := by
  rw [←divisorSum_tensor]
  apply divisorSum_congr_orthant hX
  intro v hv
  let v1 : Fin n → ℝ := fun i => v (i.castAdd m)
  let v2 : Fin m → ℝ := fun i => v (i.natAdd n)
  have he : v=Fin.append v1 v2 := by ext i; cases i using Fin.addCases <;> simp [v1,v2]
  rw [he,tensorProfile_append]
  exact cumulativeProfile_tensor f g hf hg v1 v2 (fun i => hv _) (fun i => hv _)

@[simp] theorem logCoordinates_snoc (X : ℕ) {n : ℕ} (d : Fin n → ℕ) (e : ℕ) :
    logCoordinates X (Fin.snoc d e) = Fin.snoc (logCoordinates X d) (Real.log e/Real.log X) := by
  ext i
  cases i using Fin.lastCases <;> simp [logCoordinates]

theorem divisorCoefficient_snoc_one (X : ℕ) {n : ℕ}
    (F : (Fin (n+1) → ℝ) → ℝ) (d : Fin n → ℕ) :
    divisorCoefficient X F (Fin.snoc d 1)=
      divisorCoefficient X (fun v => F (Fin.snoc v 0)) d := by
  simp [divisorCoefficient,logCoordinates_snoc,Fin.prod_univ_castSucc]

theorem divisorCoefficient_snoc_prime_zero {X M a n : ℕ} (hX : 2≤X) (hM : X<M+a)
    (F : (Fin (n+1) → ℝ) → ℝ) {rho : ℝ} (hrho : rho<1) (hb : HasBudget F rho)
    (d : Fin n → ℕ) (hd : ∀ i, 0<d i) : divisorCoefficient X F (Fin.snoc d (M+a))=0 := by
  have hp : 0<M+a := by omega
  have hcoord := logCoordinates_nonneg hX (d := Fin.snoc d (M+a)) (by
    intro i; cases i using Fin.lastCases <;> simp [hp,hd])
  have hs : rho<∑ i,logCoordinates X (Fin.snoc d (M+a)) i := by
    apply hrho.trans
    apply lt_of_lt_of_le _ (Finset.single_le_sum (fun i _ => hcoord i) (Finset.mem_univ (Fin.last n)))
    simp only [logCoordinates,Fin.snoc_last]
    apply (lt_div_iff₀ (log_pos_of_two_le hX)).mpr
    simpa only [one_mul] using Real.log_lt_log (by exact_mod_cast (by omega : 0<X))
      (by exact_mod_cast hM)
  rw [divisorCoefficient,hb _ hcoord hs,mul_zero]

theorem divisorSum_snoc (X M : ℕ) {n : ℕ} (F : (Fin (n+1) → ℝ) → ℝ)
    (b : Fin n → ℕ) (a : ℕ) :
    divisorSum X F M (Fin.snoc b a)=
      ∑ r∈(M+a).divisors, ∑ d∈Fintype.piFinset (fun i => (M+b i).divisors),
        divisorCoefficient X F (Fin.snoc d r) := by
  classical
  unfold divisorSum
  rw [←Finset.sum_product']
  symm
  apply Finset.sum_equiv (Fin.snocEquiv (fun _ : Fin (n+1) => ℕ))
  · intro p
    simp only [Finset.mem_product,Fintype.mem_piFinset,Fin.snocEquiv]
    constructor
    · rintro ⟨h1,h2⟩ i
      cases i using Fin.lastCases with
      | last => simpa using h1
      | cast i => simpa using h2 i
    · intro h
      exact ⟨by simpa using h (Fin.last n),fun i => by simpa using h i.castSucc⟩
  · intro p _
    rfl

theorem divisorSum_prime_delete {X M a n : ℕ} (hX : 2≤X) (hM : X<M+a)
    (hp : Nat.Prime (M+a)) (F : (Fin (n+1) → ℝ) → ℝ)
    {rho : ℝ} (hrho : rho<1) (hb : HasBudget F rho) (b : Fin n → ℕ) :
    divisorSum X F M (Fin.snoc b a)=divisorSum X (fun v => F (Fin.snoc v 0)) M b := by
  rw [divisorSum_snoc,hp.divisors]
  rw [Finset.sum_insert (by simpa using hp.ne_one.symm),Finset.sum_singleton]
  have hz : (∑ d∈Fintype.piFinset (fun i => (M+b i).divisors),
      divisorCoefficient X F (Fin.snoc d (M+a)))=0 := by
    apply Finset.sum_eq_zero
    intro d hd
    exact divisorCoefficient_snoc_prime_zero hX hM F hrho hb d
      (fun i => Nat.pos_of_mem_divisors ((Fintype.mem_piFinset.mp hd) i))
  rw [hz,add_zero]
  apply Finset.sum_congr rfl
  intro d _
  exact divisorCoefficient_snoc_one X F d

@[simp] theorem fiberRay_apply {ι α : Type*} [Fintype ι]
    (b : ι → α) (r : α) (i : ι) : fiberRay b r i=if b i=r then 1 else 0 := by
  classical
  simp [fiberRay,WithLp.ofLp_sum,Finset.sum_apply]

theorem rayVector_fiber_nonneg {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) (y : doubleFibers b R → ℝ) (hy : ∀ r, 0≤y r) (i : ι) :
    0≤rayVector (fun r : doubleFibers b R => fiberRay b r.val) y i := by
  classical
  simp only [rayVector,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,fiberRay_apply]
  exact Finset.sum_nonneg (fun r _ => mul_nonneg (hy r) (by split_ifs <;> norm_num))

theorem rayVector_singleton_zero {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) (i : ι)
    (hi : (Finset.univ.filter fun j => b j=b i).card=1)
    (y : doubleFibers b R → ℝ) :
    rayVector (fun r : doubleFibers b R => fiberRay b r.val) y i=0 := by
  classical
  simp only [rayVector,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,fiberRay_apply]
  apply Finset.sum_eq_zero
  intro r _
  have hr : b i≠r.val := by
    intro he
    have hh := (Finset.mem_filter.mp r.property).2
    rw [←he,hi] at hh
    norm_num at hh
  simp [hr]

theorem cumulativeProfile_kernel_small_fibers {n : ℕ} {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ positiveSimplex n tau)
    {α : Type*} (b : Fin n → α) (R : Finset α) (hR : ∀ i,b i∈R)
    (hcard : ∀ r∈R, (Finset.univ.filter fun i => b i=r).card≤2)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (cumulativeProfile tau f v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (cumulativeProfile tau f v.ofLp:ℂ))) :
    kernelConstant (sourceFourier (fourierCoordinateSum (Fin n))
      (fun v => (cumulativeProfile tau f v.ofLp:ℂ)) hF hFs) (fiberSubsetFamily b R) =
      ∫ y, (f (rayVector (fun r : doubleFibers b R => fiberRay b r.val) y).ofLp:ℂ)
        ∂positiveOrthantMeasure (doubleFibers b R) := by
  rw [small_fiber_kernelConstant b R hR hcard]
  apply integral_congr_ae
  rw [positiveOrthantMeasure_eq_restrict]
  filter_upwards [ae_restrict_mem (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioi))] with y hy
  exact cumulativeProfile_signed_full tau f hf hfs hsupp _
    (rayVector_fiber_nonneg b R y (fun r => (hy r (Set.mem_univ r)).le))

theorem cumulativeProfile_kernel_singleton_zero {n : ℕ} {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ positiveSimplex n tau)
    {α : Type*} (b : Fin n → α) (R : Finset α) (hR : ∀ i,b i∈R)
    (hcard : ∀ r∈R, (Finset.univ.filter fun i => b i=r).card≤2)
    (i : Fin n) (hi : (Finset.univ.filter fun j => b j=b i).card=1)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (cumulativeProfile tau f v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (cumulativeProfile tau f v.ofLp:ℂ))) :
    kernelConstant (sourceFourier (fourierCoordinateSum (Fin n))
      (fun v => (cumulativeProfile tau f v.ofLp:ℂ)) hF hFs) (fiberSubsetFamily b R)=0 := by
  rw [cumulativeProfile_kernel_small_fibers f hf hfs hsupp b R hR hcard]
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  have hz : f (rayVector (fun r : doubleFibers b R => fiberRay b r.val) y).ofLp=0 := by
    by_contra hne
    have hh := (hsupp (subset_tsupport f hne)).1 i
    have he := rayVector_singleton_zero b R i hi y
    change 0<rayVector (fun r : doubleFibers b R => fiberRay b r.val) y i at hh
    rw [he] at hh
    exact lt_irrefl _ hh
  simp [hz]

@[simp] theorem append_self_addNat {n : ℕ} {α : Type*} (y z : Fin n → α) (i : Fin n) :
    Fin.append y z (i.addNat n)=z i := by
  rw [←Fin.natAdd_eq_addNat,Fin.append_right]

def duplicateLabels (n : ℕ) : Fin (n+n) → Fin n := Fin.append id id

theorem duplicateLabels_fiber_sum {n : ℕ} (r : Fin n) {K : Type*} [AddCommMonoid K]
    (w : Fin (n+n) → K) :
    (∑ i∈Finset.univ.filter (fun i => duplicateLabels n i=r), w i)=w (r.castAdd n)+w (r.natAdd n) := by
  classical
  rw [Finset.sum_filter,Fin.sum_univ_add]
  simp [duplicateLabels]

@[simp] theorem duplicateLabels_fiber_card {n : ℕ} (r : Fin n) :
    (Finset.univ.filter fun i => duplicateLabels n i=r).card=2 := by
  simpa using duplicateLabels_fiber_sum r (fun _ => (1:ℕ))

theorem duplicateLabels_classical_fiber {n : ℕ} (r : Fin n) :
    @Finset.filter (Fin (n+n)) (fun i => duplicateLabels n i=r)
      (fun _ => Classical.propDecidable _) Finset.univ =
      Finset.univ.filter (fun i => duplicateLabels n i=r) := by
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]

theorem duplicateLabels_kernel (n : ℕ) (w : Fin (n+n) → ℂ) :
    familyKernel (fiberSubsetFamily (duplicateLabels n) Finset.univ) w =
      (∏ i,w i)*(∏ i : Fin n,(w (i.castAdd n)+w (i.natAdd n))⁻¹) := by
  rw [familyKernel_small_fibers (duplicateLabels n) Finset.univ (fun i => Finset.mem_univ _) (by
    intro r _
    rw [duplicateLabels_classical_fiber,duplicateLabels_fiber_card])]
  simp only [duplicateLabels_classical_fiber,duplicateLabels_fiber_card,Finset.filter_true,
    duplicateLabels_fiber_sum]

noncomputable def duplicateRay {n : ℕ} (i : Fin n) : EuclideanSpace ℝ (Fin (n+n)) :=
  EuclideanSpace.single (i.castAdd n) 1+EuclideanSpace.single (i.natAdd n) 1

theorem duplicateRay_frequency {n : ℕ} (i : Fin n) (u : EuclideanSpace ℝ (Fin (n+n))) :
    laplaceFrequency (fourierCoordinateSum (Fin (n+n))) (duplicateRay i) u =
      frequencyW (u (i.castAdd n))+frequencyW (u (i.natAdd n)) := by
  unfold duplicateRay
  simp only [laplaceFrequency,map_add,inner_add_right,Complex.ofReal_add,
    fourierCoordinateSum_apply]
  simp [frequencyW,EuclideanSpace.inner_single_right]
  ring

theorem duplicateRay_positive {n : ℕ} (i : Fin n) :
    0<fourierCoordinateSum (Fin (n+n)) (duplicateRay i) := by
  have h := congrArg Complex.re (duplicateRay_frequency i 0)
  simp only [laplaceFrequency_re,Complex.add_re,frequencyW_re] at h
  rw [h]
  norm_num

theorem castAdd_ne_addNat_self {n : ℕ} (i j : Fin n) : i.castAdd n ≠ j.addNat n := by
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_castAdd,Fin.val_addNat] at hval
  omega

theorem addNat_ne_castAdd_self {n : ℕ} (i j : Fin n) : i.addNat n ≠ j.castAdd n :=
  (castAdd_ne_addNat_self j i).symm

theorem rayVector_duplicate {n : ℕ} (y : Fin n → ℝ) :
    (rayVector duplicateRay y).ofLp=Fin.append y y := by
  classical
  ext i
  cases i using Fin.addCases with
  | left i => simp [rayVector,duplicateRay,WithLp.ofLp_sum,Finset.sum_apply,
      smul_eq_mul,Pi.single_apply,Finset.sum_add_distrib,castAdd_ne_addNat_self]
  | right i => simp [rayVector,duplicateRay,WithLp.ofLp_sum,Finset.sum_apply,
      smul_eq_mul,Pi.single_apply,Finset.sum_add_distrib,addNat_ne_castAdd_self]

theorem duplicate_kernelConstant {n : ℕ}
    (F : EuclideanSpace ℝ (Fin (n+n)) → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    kernelConstant (sourceFourier (fourierCoordinateSum (Fin (n+n))) F hF hFs)
      (fiberSubsetFamily (duplicateLabels n) Finset.univ) =
      ∫ y, signedDirections (coordinateDirectionList (Fin (n+n))) F (rayVector duplicateRay y)
        ∂positiveOrthantMeasure (Fin n) := by
  rw [←sourceFourier_derivative_laplace (fourierCoordinateSum (Fin (n+n)))
    (coordinateDirectionList (Fin (n+n))) F hF hFs duplicateRay duplicateRay_positive]
  unfold kernelConstant
  apply integral_congr_ae
  filter_upwards [] with u
  rw [contourKernel,duplicateLabels_kernel,coordinateDirectionList_multiplier]
  simp only [duplicateRay_frequency,mul_assoc]

theorem cumulative_tensor_diagonal_kernel {n : ℕ} {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ positiveSimplex n tau)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
      (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
      (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ))) :
    kernelConstant (sourceFourier (fourierCoordinateSum (Fin (n+n)))
      (fun v => (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ)) hF hFs)
      (fiberSubsetFamily (duplicateLabels n) Finset.univ) = (l2Mass f:ℂ) := by
  rw [duplicate_kernelConstant]
  have he : (∫ y, signedDirections (coordinateDirectionList (Fin (n+n)))
      (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
        (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ)) (rayVector duplicateRay y)
      ∂positiveOrthantMeasure (Fin n)) =
      ∫ y, (f y^2:ℂ) ∂positiveOrthantMeasure (Fin n) := by
    apply integral_congr_ae
    rw [positiveOrthantMeasure_eq_restrict]
    filter_upwards [ae_restrict_mem (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioi))] with y hy
    rw [cumulativeProfile_signed_full (tau+tau) (tensorProfile f f)
      (tensorProfile_compact f f hf hf) (tensorProfile_smooth f f hfs hfs)
      (tensorProfile_tsupport f f hsupp hsupp)]
    · rw [rayVector_duplicate,tensorProfile_append,pow_two]
      simp only [Complex.ofReal_mul]
    · intro i
      rw [rayVector_duplicate]
      cases i using Fin.addCases with
      | left i => simpa using (hy i (Set.mem_univ i)).le
      | right i => simpa using (hy i (Set.mem_univ i)).le
  rw [he]
  simp_rw [←Complex.ofReal_pow]
  rw [integral_complex_ofReal,positiveOrthantMeasure_eq_restrict]
  congr 1
  unfold l2Mass
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hfz : f y=0 := by
    by_contra hne
    exact hy (fun i _ => (hsupp (subset_tsupport f hne)).1 i)
  simp [hfz]

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_TensorProfiles

section File_OpenAIPrimeGaps_EqualityPatterns

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem index_density_from_weight_estimates {C : ℝ} (hC : 0<C)
    (W : ℕ → ℕ → ℝ) (a K b M : ℝ)
    (ha : 0<a) (hK : 0<K) (hM : 0<M) (hb : b<a^2/K)
    (hw : ∀ᶠ X : ℕ in atTop, ∀ m ∈ Finset.Ioc X (2*X), 0≤W X m)
    (hfirst : ∀ᶠ X : ℕ in atTop,
      a≤average X (fun m => W X m*detector X (Finset.Ioc 0 (blockLength (C+1) X)) m))
    (hdetect : ∀ᶠ X : ℕ in atTop,
      average X (fun m => W X m*detector X (Finset.Ioc 0 (blockLength (C+1) X)) m^2)≤K)
    (hsuppress : ∀ᶠ X : ℕ in atTop,
      average X (fun m => W X m*detector X
        (Finset.Ioc (blockLength (C+1) X) (2*blockLength (C+1) X)) m)≤b)
    (hsecond : ∀ᶠ X : ℕ in atTop, average X (fun m => W X m^2)≤M) :
    ∃ c : ℝ, 0<c ∧ ∃ N₀ : ℕ, ∀ N≥N₀, c*(N:ℝ)≤((largeGapIndices C N).card:ℝ) := by
  let delta := (a^2/K-b)^2/M
  have hd : 0<delta := div_pos (sq_pos_of_pos (sub_pos.mpr hb)) hM
  let A := 6*(Real.log 4+1)
  have hA : 0<A := by dsimp [A]; positivity
  have hL : 0<C+1 := by linarith
  refine ⟨delta/(A*(C+1)),div_pos hd (mul_pos hA hL),?_⟩
  apply eventually_atTop.mp
  have hstarts : ∀ᶠ X : ℕ in atTop,
      delta*(X:ℝ)≤((goodStarts X (blockLength (C+1) X)).card:ℝ) := by
    filter_upwards [eventually_ge_atTop 2,hw,hfirst,hdetect,hsuppress,hsecond]
      with X hX hW hF hD hS hQ
    exact goodStarts_bound_of_moments hX (W X) a K b M ha hK hM hb hW hF hD hS hQ
  filter_upwards [eventually_scale_comparison,eventually_ge_atTop 1,
    tendsto_indexScale.eventually (eventually_blockLength_le (C+1) hL),
    tendsto_indexScale.eventually (eventually_blockLength_threshold C hC),
    tendsto_indexScale.eventually hstarts] with N hcompare hN hblock hthreshold hcount
  apply index_bound_of_goodStarts hd hL hA hcompare.1 (by omega)
  · have hdiv := Nat.div_mul_le_self (prime N) 3
    change (prime N/3)*3≤prime N at hdiv
    change 2*indexScale N+blockLength (C+1) (indexScale N)≤prime N
    change (indexScale N)*3≤prime N at hdiv
    omega
  · intro p hp
    have hmem := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
    exact hthreshold p (by omega) (by omega)
  · exact hcompare.2
  · exact hcount

def PatternMaps {ι : Type*} (r : Setoid ι) (α : Type*) :=
  {b : ι → α // Setoid.ker b = r}

noncomputable def patternLift {ι α : Type*} {r : Setoid ι} (b : PatternMaps r α) :
    Quotient r → α :=
  Quotient.lift b.val (by
    intro i j hij
    rw [←b.property] at hij
    exact hij)

@[simp] theorem patternLift_mk {ι α : Type*} {r : Setoid ι} (b : PatternMaps r α) (i : ι) :
    patternLift b (Quotient.mk r i)=b.val i := rfl

theorem patternLift_injective {ι α : Type*} {r : Setoid ι} (b : PatternMaps r α) :
    Function.Injective (patternLift b) := by
  intro x y
  induction x using Quotient.inductionOn with | h i =>
    induction y using Quotient.inductionOn with | h j =>
      intro h
      apply Quotient.sound
      rw [←b.property]
      exact h

theorem patternLift_map_injective {ι α : Type*} {r : Setoid ι} :
    Function.Injective (@patternLift ι α r) := by
  intro a b hab
  apply Subtype.ext
  funext i
  exact congrFun hab (Quotient.mk r i)

noncomputable def patternClass {ι α : Type*} [Fintype ι] [Fintype α]
    (r : Setoid ι) : Finset (ι → α) := Finset.univ.filter (fun b => Setoid.ker b=r)

@[simp] theorem mem_patternClass {ι α : Type*} [Fintype ι] [Fintype α]
    (r : Setoid ι) (b : ι → α) : b∈patternClass r ↔ Setoid.ker b=r := by
  simp [patternClass]

theorem patternClass_card_le {ι α : Type*} [Fintype ι] [Fintype α] (r : Setoid ι) :
    (patternClass (α:=α) r).card ≤ Fintype.card α ^ Fintype.card (Quotient r) := by
  classical
  let e : {b // b∈patternClass (α:=α) r} → (Quotient r → α) :=
    fun b => patternLift ⟨b.val,(mem_patternClass r b.val).mp b.property⟩
  have he : Function.Injective e := by
    intro a b h
    apply Subtype.ext
    funext i
    exact congrFun h (Quotient.mk r i)
  have h := Fintype.card_le_of_injective e he
  simpa only [Fintype.card_coe,Fintype.card_fun] using h

theorem patternClass_pairwise_disjoint {ι α : Type*} [Fintype ι] [Fintype α]
    {r s : Setoid ι} (hrs : r≠s) :
    Disjoint (patternClass (α:=α) r) (patternClass (α:=α) s) := by
  classical
  apply Finset.disjoint_left.mpr
  intro b hr hs
  exact hrs ((mem_patternClass r b).mp hr |>.symm.trans ((mem_patternClass s b).mp hs))

noncomputable instance finiteSetoidFintype (ι : Type*) [Fintype ι] : Fintype (Setoid ι) :=
  Fintype.ofInjective (fun r : Setoid ι => r.r) (fun _ _ h => Setoid.ext (by intro i j; exact Iff.of_eq (congrFun (congrFun h i) j)))

theorem sum_patterns {ι α K : Type*} [Fintype ι] [Fintype α] [AddCommMonoid K]
    (f : (ι → α) → K) :
    (∑ r : Setoid ι, ∑ b∈patternClass (α:=α) r, f b)=∑ b : ι → α, f b := by
  classical
  simp only [patternClass]
  exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _

theorem fiberSubsetFamily_image_eq_of_kernel {ι α β : Type*} [Fintype ι]
    (a : ι → α) (b : ι → β) (hab : ∀ i j, a i=a j ↔ b i=b j) :
    fiberSubsetFamily a (Finset.univ.image a)=fiberSubsetFamily b (Finset.univ.image b) := by
  classical
  ext S
  simp only [mem_fiberSubsetFamily_image]
  constructor <;> rintro ⟨hS,h⟩
  · exact ⟨hS,fun i hi j hj => (hab i j).mp (h i hi j hj)⟩
  · exact ⟨hS,fun i hi j hj => (hab i j).mpr (h i hi j hj)⟩

theorem append_fiber_card {m n : ℕ} {α : Type*} (a : Fin m → α) (b : Fin n → α) (r : α) :
    (Finset.univ.filter fun i => Fin.append a b i=r).card=
      (Finset.univ.filter fun i => a i=r).card+(Finset.univ.filter fun i => b i=r).card := by
  classical
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter,Fin.sum_univ_add,Fin.append_left,Fin.append_right]

theorem append_fiber_card_le_two {m n : ℕ} {α : Type*}
    (a : Fin m → α) (b : Fin n → α) (ha : Function.Injective a) (hb : Function.Injective b) (r : α) :
    (Finset.univ.filter fun i => Fin.append a b i=r).card≤2 := by
  classical
  rw [append_fiber_card]
  have h1 : (Finset.univ.filter fun i => a i=r).card≤1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact ha ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
  have h2 : (Finset.univ.filter fun i => b i=r).card≤1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact hb ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
  omega

theorem append_left_singleton {m n : ℕ} {α : Type*}
    (a : Fin m → α) (b : Fin n → α) (ha : Function.Injective a)
    (i : Fin m) (hi : a i∉Set.range b) :
    (Finset.univ.filter fun j => Fin.append a b j=Fin.append a b (i.castAdd n)).card=1 := by
  classical
  have he : (Finset.univ.filter fun j => Fin.append a b j=Fin.append a b (i.castAdd n))=
      {i.castAdd n} := by
    ext j
    cases j using Fin.addCases with
    | left j => simp [ha.eq_iff]
    | right j =>
      have hn : b j≠a i := fun h => hi ⟨j,h⟩
      have hne : Fin.natAdd m j≠i.castAdd n := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
        omega
      simp [hn,hne]
  rw [he,Finset.card_singleton]

theorem append_right_singleton {m n : ℕ} {α : Type*}
    (a : Fin m → α) (b : Fin n → α) (hb : Function.Injective b)
    (i : Fin n) (hi : b i∉Set.range a) :
    (Finset.univ.filter fun j => Fin.append a b j=Fin.append a b (i.natAdd m)).card=1 := by
  classical
  have he : (Finset.univ.filter fun j => Fin.append a b j=Fin.append a b (i.natAdd m))=
      {i.natAdd m} := by
    ext j
    cases j using Fin.addCases with
    | left j =>
      have hn : a j≠b i := fun h => hi ⟨j,h⟩
      have hne : j.castAdd n≠Fin.natAdd m i := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
        omega
      simp [hn,hne]
    | right j => simp [hb.eq_iff]
  rw [he,Finset.card_singleton]

theorem cumulative_tensor_unmatched_kernel_zero {m n : ℕ} {tau : ℝ}
    (f : (Fin m → ℝ) → ℝ) (g : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f ⊆ positiveSimplex m tau) (hsg : tsupport g ⊆ positiveSimplex n tau)
    {α : Type*} (a : Fin m → α) (b : Fin n → α)
    (ha : Function.Injective a) (hb : Function.Injective b) (hab : Set.range a≠Set.range b)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (m+n)) =>
      (cumulativeProfile (tau+tau) (tensorProfile f g) v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (m+n)) =>
      (cumulativeProfile (tau+tau) (tensorProfile f g) v.ofLp:ℂ))) :
    kernelConstant (sourceFourier (fourierCoordinateSum (Fin (m+n)))
      (fun v => (cumulativeProfile (tau+tau) (tensorProfile f g) v.ofLp:ℂ)) hF hFs)
      (fiberSubsetFamily (Fin.append a b) (Finset.univ.image (Fin.append a b)))=0 := by
  classical
  have hh : ∃ i : Fin (m+n),
      (Finset.univ.filter fun j => Fin.append a b j=Fin.append a b i).card=1 := by
    by_cases hsub : Set.range a⊆Set.range b
    · have hnot : ¬Set.range b⊆Set.range a := fun h => hab (Set.Subset.antisymm hsub h)
      obtain ⟨v,⟨i,rfl⟩,hi⟩ := Set.not_subset.mp hnot
      exact ⟨i.natAdd m,append_right_singleton a b hb i hi⟩
    · obtain ⟨v,⟨i,rfl⟩,hi⟩ := Set.not_subset.mp hsub
      exact ⟨i.castAdd n,append_left_singleton a b ha i hi⟩
  obtain ⟨i,hi⟩ := hh
  exact cumulativeProfile_kernel_singleton_zero (tensorProfile f g)
    (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs)
    (tensorProfile_tsupport f g hsf hsg) (Fin.append a b) _
    (fun i => Finset.mem_image_of_mem _ (Finset.mem_univ _))
    (fun r _ => append_fiber_card_le_two a b ha hb r) i hi hF hFs

theorem duplicateLabels_image (n : ℕ) : Finset.univ.image (duplicateLabels n)=Finset.univ := by
  classical
  ext i
  simp only [Finset.mem_image,Finset.mem_univ,true_and,iff_true]
  exact ⟨i.castAdd n,by simp [duplicateLabels]⟩

theorem duplicate_shiftFamily {n : ℕ} (a : Fin n → ℤ) (ha : Function.Injective a) :
    shiftFamily (Fin.append a a)=fiberSubsetFamily (duplicateLabels n) Finset.univ := by
  have he : Fin.append a a=(fun i => a (duplicateLabels n i)) := by
    funext i
    cases i using Fin.addCases <;> simp [duplicateLabels]
  classical
  conv_rhs => rw [←duplicateLabels_image n]
  ext S
  simp only [shiftFamily,mem_fiberSubsetFamily_image]
  constructor <;> rintro ⟨hS,h⟩
  · refine ⟨hS, fun i hi j hj => ?_⟩
    apply ha
    simpa only [he] using h i hi j hj
  · refine ⟨hS, fun i hi j hj => ?_⟩
    rw [he]
    exact congrArg a (h i hi j hj)

noncomputable def patternEmbedding {ι α : Type*} {r : Setoid ι} (b : PatternMaps r α) :
    Quotient r ↪ α := ⟨patternLift b,patternLift_injective b⟩

noncomputable def embeddingPattern {ι α : Type*} (r : Setoid ι) (e : Quotient r ↪ α) :
    PatternMaps r α := ⟨fun i => e (Quotient.mk r i),by
  apply Setoid.ext
  intro i j
  change e (Quotient.mk r i)=e (Quotient.mk r j) ↔ r i j
  rw [e.injective.eq_iff,Quotient.eq]⟩

noncomputable def patternEquivEmbedding {ι α : Type*} (r : Setoid ι) :
    PatternMaps r α ≃ (Quotient r ↪ α) where
  toFun := patternEmbedding
  invFun := embeddingPattern r
  left_inv b := by apply Subtype.ext; rfl
  right_inv e := by
    apply Function.Embedding.ext
    intro x
    induction x using Quotient.inductionOn with | h i => rfl

noncomputable def patternClassEquiv {ι α : Type*} [Fintype ι] [Fintype α] (r : Setoid ι) :
    {b // b∈patternClass (α:=α) r} ≃ (Quotient r ↪ α) :=
  (Equiv.subtypeEquivRight (fun b => mem_patternClass r b)).trans (patternEquivEmbedding r)

theorem patternClass_sum_norm_le {ι α : Type*} [Fintype ι] [Fintype α]
    (r : Setoid ι) (f : (ι → α) → ℂ) {E : ℝ} (hE : 0≤E)
    (hf : ∀ b∈patternClass r, ‖f b‖≤E) :
    ‖∑ b∈patternClass r, f b‖≤(Fintype.card α:ℝ)^Fintype.card (Quotient r)*E := by
  classical
  calc
    _ ≤ ∑ _b∈patternClass (α:=α) r, E := norm_sum_le_of_le _ hf
    _ = ((patternClass (α:=α) r).card:ℝ)*E := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast patternClass_card_le (α:=α) r) hE

theorem patternClass_scaled_sum_norm_le {ι α : Type*} [Fintype ι] [Fintype α]
    (r : Setoid ι) (f g : (ι → α) → ℂ) {L E : ℝ} (hL : 0<L) (hE : 0≤E)
    (hf : ∀ b∈patternClass r, ‖(L:ℂ)^Fintype.card (Quotient r)*f b-g b‖≤E) :
    ‖(∑ b∈patternClass r, f b)-(∑ b∈patternClass r, g b)/(L:ℂ)^Fintype.card (Quotient r)‖≤
      ((Fintype.card α:ℝ)/L)^Fintype.card (Quotient r)*E := by
  classical
  have h := patternClass_sum_norm_le r (fun b => (L:ℂ)^Fintype.card (Quotient r)*f b-g b) hE hf
  rw [Finset.sum_sub_distrib,←Finset.mul_sum] at h
  have hLc : (L:ℂ)≠0 := by exact_mod_cast ne_of_gt hL
  have he : (∑ b∈patternClass r, f b)-(∑ b∈patternClass r, g b)/(L:ℂ)^Fintype.card (Quotient r) =
      ((L:ℂ)^Fintype.card (Quotient r)*(∑ b∈patternClass r, f b)-∑ b∈patternClass r, g b)/
      (L:ℂ)^Fintype.card (Quotient r) := by
    field_simp [hLc]
  rw [he,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  apply (div_le_iff₀ (pow_pos hL _)).mpr
  apply le_trans h
  apply le_of_eq
  rw [div_pow]
  field_simp

theorem pattern_errors_tendsto_zero {ι : Type*} [Fintype ι]
    (r : Setoid ι) (H : ℕ → ℕ) (L E : ℕ → ℝ) (lam : ℝ)
    (f g : (X : ℕ) → (ι → Fin (H X)) → ℂ)
    (hL : ∀ᶠ X in atTop, 0<L X)
    (hHL : Tendsto (fun X => (H X:ℝ)/L X) atTop (𝓝 lam))
    (hE : Tendsto E atTop (𝓝 0))
    (herr : ∀ᶠ X in atTop, ∀ b∈patternClass r,
      ‖(L X:ℂ)^Fintype.card (Quotient r)*f X b-g X b‖≤E X) :
    Tendsto (fun X => (∑ b∈patternClass r, f X b)-
      (∑ b∈patternClass r, g X b)/(L X:ℂ)^Fintype.card (Quotient r)) atTop (𝓝 0) := by
  have hb : ∀ᶠ X in atTop,
      ‖(∑ b∈patternClass r, f X b)-(∑ b∈patternClass r, g X b)/
        (L X:ℂ)^Fintype.card (Quotient r)‖≤
      ((H X:ℝ)/L X)^Fintype.card (Quotient r)*|E X| := by
    filter_upwards [hL,herr] with X hLX hX
    simpa only [Fintype.card_fin] using patternClass_scaled_sum_norm_le r (f X) (g X)
      hLX (abs_nonneg (E X)) (fun b hb => (hX b hb).trans (le_abs_self _))
  apply squeeze_zero_norm' hb
  simpa only [abs_zero,mul_zero] using (hHL.pow (Fintype.card (Quotient r))).mul hE.abs

theorem all_pattern_errors_tendsto_zero {ι : Type*} [Fintype ι]
    (H : ℕ → ℕ) (L : ℕ → ℝ) (lam : ℝ)
    (E : Setoid ι → ℕ → ℝ) (f g : (X : ℕ) → (ι → Fin (H X)) → ℂ)
    (hL : ∀ᶠ X in atTop, 0<L X)
    (hHL : Tendsto (fun X => (H X:ℝ)/L X) atTop (𝓝 lam))
    (hE : ∀ r, Tendsto (E r) atTop (𝓝 0))
    (herr : ∀ r, ∀ᶠ X in atTop, ∀ b∈patternClass r,
      ‖(L X:ℂ)^Fintype.card (Quotient r)*f X b-g X b‖≤E r X) :
    Tendsto (fun X => ∑ r : Setoid ι, ((∑ b∈patternClass r, f X b)-
      (∑ b∈patternClass r, g X b)/(L X:ℂ)^Fintype.card (Quotient r))) atTop (𝓝 0) := by
  have h := tendsto_finsetSum Finset.univ (fun r _ =>
    pattern_errors_tendsto_zero r H L (E r) lam f g hL hHL (hE r) (herr r))
  simpa only [Finset.sum_const_zero] using h

theorem blockLength_ratio_tendsto {lam : ℝ} (hlam : 0≤lam) :
    Tendsto (fun X : ℕ => (blockLength lam X:ℝ)/Real.log X) atTop (𝓝 lam) := by
  have hlog : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv := tendsto_inv_atTop_zero.comp hlog
  have hlo : Tendsto (fun X : ℕ => lam-(Real.log (X:ℝ))⁻¹) atTop (𝓝 lam) := by
    simpa using tendsto_const_nhds.sub hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 2] with X hX
    have hL := log_pos_of_two_le hX
    apply (le_div_iff₀ hL).mpr
    have hh := (Nat.lt_floor_add_one (lam*Real.log (X:ℝ))).le
    dsimp [blockLength]
    have he : (lam-(Real.log (X:ℝ))⁻¹)*Real.log X=lam*Real.log X-1 := by
      field_simp
    rw [he]
    linarith
  · filter_upwards [eventually_ge_atTop 2] with X hX
    exact (div_le_iff₀ (log_pos_of_two_le hX)).mpr (blockLength_le_mul_log hlam hX)

theorem blockLength_tendsto {lam : ℝ} (hlam : 0<lam) :
    Tendsto (blockLength lam) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hlam)

theorem blockLength_densityCutoff_eventually {lam : ℝ} (hlam : 0≤lam) (K : ℕ) :
    ∀ᶠ X : ℕ in atTop, K*blockLength lam X≤densityCutoff 2 (Real.log X) := by
  have hlog : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2,hlog.eventually_ge_atTop ((K:ℝ)*lam)] with X hX hL
  apply (Nat.le_floor_iff (by positivity : 0≤(Real.log (X:ℝ))^2)).mpr
  push_cast
  have hh := blockLength_le_mul_log hlam hX
  nlinarith [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg K),
    mul_le_mul_of_nonneg_right hL (log_pos_of_two_le hX).le]

theorem uniform_singularBoxMean_tendsto (s : ℕ) {K : ℕ} (hK : 0<K)
    (H : ℕ → ℕ) (a : ℕ → Fin s → ℤ) (hH : Tendsto H atTop atTop)
    (hdiam : ∀ᶠ X : ℕ in atTop, boxDiameterBound (h:=H X) (a X) (K*H X)) :
    Tendsto (fun X => singularBoxMean (h:=H X) (a X)) atTop (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨h₀,hh₀⟩ := singularBoxMean_uniform s hK hε
  filter_upwards [hH.eventually_ge_atTop h₀,hdiam] with X hX hd
  exact (by simpa only [Real.dist_eq] using hh₀ (H X) hX (a X) hd)

theorem constant_boxDiameterBound {s h : ℕ} (a : ℤ) :
    boxDiameterBound (s:=s) (h:=h) (fun _ => a) h := by
  intro n i j
  dsimp [boxTuple]
  rw [add_sub_add_left_eq_sub]
  have hi := (n i).isLt
  have hj := (n j).isLt
  omega

theorem quotient_ker_card {ι α : Type*} [Fintype ι] [DecidableEq α] (b : ι → α) :
    Fintype.card (Quotient (Setoid.ker b))=(Finset.univ.image b).card := by
  classical
  let f : Quotient (Setoid.ker b) → {a // a∈Finset.univ.image b} := fun x =>
    ⟨Setoid.kerLift b x, by
      induction x using Quotient.inductionOn with | h i => exact Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
  have hi : Function.Injective f := by
    intro x y h
    apply Setoid.kerLift_injective b
    exact congrArg Subtype.val h
  have hs : Function.Surjective f := by
    rintro ⟨v,hv⟩
    obtain ⟨i,_,he⟩ := Finset.mem_image.mp hv
    refine ⟨Quotient.mk _ i,?_⟩
    exact Subtype.ext he
  simpa only [Fintype.card_coe] using Fintype.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)

noncomputable def numericPattern {ι : Type*} [Fintype ι] (r : Setoid ι) : ι → ℕ :=
  fun i => (Fintype.equivFin (Quotient r) (Quotient.mk r i)).val

theorem numericPattern_ker {ι : Type*} [Fintype ι] (r : Setoid ι) :
    Setoid.ker (numericPattern r)=r := by
  apply Setoid.ext
  intro i j
  change (Fintype.equivFin (Quotient r) (Quotient.mk r i)).val=
    (Fintype.equivFin (Quotient r) (Quotient.mk r j)).val ↔ r i j
  rw [Fin.val_inj,(Fintype.equivFin (Quotient r)).injective.eq_iff,Quotient.eq]

theorem constant_boxTuple_injective_iff {s h : ℕ} (a : ℤ) (n : Fin s → Fin h) :
    Function.Injective (boxTuple (fun _ => a) n) ↔ Function.Injective n := by
  constructor
  · intro hn i j he
    apply hn
    simp [boxTuple,he]
  · intro hn i j he
    apply hn
    have hv : (n i:ℕ)=(n j:ℕ) := by
      exact_mod_cast (add_left_cancel he : (n i:ℤ)=(n j:ℤ))
    exact Fin.ext hv

noncomputable def patternTupleEquiv {ι : Type*} [Fintype ι] (r : Setoid ι) (h : ℕ) (a : ℤ) :
    {b // b∈patternClass (α:=Fin h) r} ≃
    {n // n∈distinctBox (s:=Fintype.card (Quotient r)) (h:=h) (fun _ => a)} :=
  (patternClassEquiv r).trans
    ((Equiv.embeddingCongr (Fintype.equivFin (Quotient r)) (Equiv.refl (Fin h))).trans
      ((Equiv.subtypeInjectiveEquivEmbedding _ _).symm.trans
        (Equiv.subtypeEquivRight (fun n => by
          simp only [distinctBox,Finset.mem_filter,Finset.mem_univ,true_and,
            constant_boxTuple_injective_iff]))))

@[simp] theorem patternTupleEquiv_apply {ι : Type*} [Fintype ι] (r : Setoid ι) (h : ℕ) (a : ℤ)
    (b : {b // b∈patternClass (α:=Fin h) r}) (j : Fin (Fintype.card (Quotient r))) :
    (patternTupleEquiv r h a b).val j=
      patternLift ⟨b.val,(mem_patternClass r b.val).mp b.property⟩
        ((Fintype.equivFin (Quotient r)).symm j) := rfl

theorem patternTupleEquiv_image {ι : Type*} [Fintype ι] (r : Setoid ι) (h : ℕ) (a : ℤ)
    (b : {b // b∈patternClass (α:=Fin h) r}) :
    (Finset.univ.image fun i => a+(b.val i:ℕ))=
      Finset.univ.image (boxTuple (fun _ => a) (patternTupleEquiv r h a b).val) := by
  classical
  ext v
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,rfl⟩
    refine ⟨Fintype.equivFin (Quotient r) (Quotient.mk r i),?_⟩
    simp only [boxTuple,patternTupleEquiv_apply,Equiv.symm_apply_apply]
    rfl
  · rintro ⟨j,rfl⟩
    obtain ⟨i,hi⟩ := Quotient.mk_surjective ((Fintype.equivFin (Quotient r)).symm j)
    refine ⟨i,?_⟩
    simp only [boxTuple,patternTupleEquiv_apply,←hi]
    rfl

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_EqualityPatterns

section File_OpenAIPrimeGaps_Detectors

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem pattern_singular_sum {ι : Type*} [Fintype ι] (r : Setoid ι) (h : ℕ) (a : ℤ) :
    (∑ b∈patternClass (α:=Fin h) r,
      singularSeries (Finset.univ.image fun i => a+(b i:ℕ))) =
    ∑ n∈distinctBox (s:=Fintype.card (Quotient r)) (h:=h) (fun _ => a),
      singularSeries (Finset.univ.image (boxTuple (fun _ => a) n)) := by
  classical
  conv_lhs => rw [←Finset.sum_coe_sort]
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Fintype.sum_equiv (patternTupleEquiv r h a)
  intro b
  rw [patternTupleEquiv_image r h a b]

theorem ker_comp_injective {ι α β : Type*} (b : ι → α) (f : α → β) (hf : Function.Injective f) :
    Setoid.ker (f∘b)=Setoid.ker b := by
  apply Setoid.ext
  intro i j
  exact hf.eq_iff

theorem numericPattern_int_ker {ι : Type*} [Fintype ι] (r : Setoid ι) :
    Setoid.ker (fun i => (numericPattern r i:ℤ))=r := by
  have h := ker_comp_injective (numericPattern r) (fun n : ℕ => (n:ℤ)) (by intro m n hm; exact_mod_cast (show (m:ℤ)=(n:ℤ) from hm))
  exact h.trans (numericPattern_ker r)

theorem shiftFamily_eq_of_ker {ι : Type*} [Fintype ι] (b c : ι → ℤ)
    (h : Setoid.ker b=Setoid.ker c) : shiftFamily b=shiftFamily c := by
  classical
  ext S
  simp only [shiftFamily,mem_fiberSubsetFamily_image]
  have hc (i j : ι) : b i=b j ↔ c i=c j := by
    change (Setoid.ker b) i j ↔ (Setoid.ker c) i j
    rw [h]
  constructor <;> rintro ⟨hS,he⟩
  · exact ⟨hS,fun i hi j hj => (hc i j).mp (he i hi j hj)⟩
  · exact ⟨hS,fun i hi j hj => (hc i j).mpr (he i hi j hj)⟩

noncomputable def equalityPatternFamily {ι : Type*} [Fintype ι] (r : Setoid ι) :
    Finset (Finset ι) := shiftFamily (fun i => (numericPattern r i:ℤ))

theorem equalityPatternFamily_sign_sum {ι : Type*} [Fintype ι] (r : Setoid ι) :
    (∑ S∈equalityPatternFamily r,(-1:ℤ)^S.card)=-(Fintype.card (Quotient r):ℤ) := by
  classical
  rw [equalityPatternFamily,shiftFamily_sign_sum]
  have he : (Finset.univ.image fun i => (numericPattern r i:ℤ))=
      Finset.univ.image (fun j : Fin (Fintype.card (Quotient r)) => (j.val:ℤ)) := by
    ext v
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨Fintype.equivFin (Quotient r) (Quotient.mk r i),rfl⟩
    · rintro ⟨j,rfl⟩
      obtain ⟨i,hi⟩ := Quotient.mk_surjective ((Fintype.equivFin (Quotient r)).symm j)
      refine ⟨i,?_⟩
      simp only [numericPattern,hi,Equiv.apply_symm_apply]
  rw [he,Finset.card_image_of_injective]
  · simp only [Finset.card_univ,Fintype.card_fin]
  · intro i j hij
    apply Fin.ext
    exact_mod_cast (show (i.val:ℤ)=(j.val:ℤ) from hij)

theorem translated_shiftFamily {ι : Type*} [Fintype ι] {h : ℕ}
    (r : Setoid ι) (a : ℕ) (b : ι → Fin h) (hb : b∈patternClass r) :
    shiftFamily (fun i => ((a+(b i).val:ℕ):ℤ))=equalityPatternFamily r := by
  apply shiftFamily_eq_of_ker
  rw [numericPattern_int_ker]
  have hi : Function.Injective (fun x : Fin h => ((a+x.val:ℕ):ℤ)) := by
    intro i j hij
    apply Fin.ext
    have hh : a+i.val=a+j.val := by exact_mod_cast (show ((a+i.val:ℕ):ℤ)=((a+j.val:ℕ):ℤ) from hij)
    exact Nat.add_left_cancel hh
  exact (ker_comp_injective b _ hi).trans ((mem_patternClass r b).mp hb)

theorem divisorSum_fin_zero (X M : ℕ) (F : (Fin 0 → ℝ) → ℝ) (b : Fin 0 → ℕ) :
    divisorSum X F M b=F 0 := by
  classical
  have h : Fintype.piFinset (fun i => (M+b i).divisors)={(0 : Fin 0 → ℕ)} := by
    ext d
    simp [funext_iff]
  rw [divisorSum,h,Finset.sum_singleton]
  simp only [divisorCoefficient,Fin.prod_univ_zero,one_mul]
  congr 1
  ext i
  exact Fin.elim0 i

theorem divisorSum_singleton_at_prime {X M b : ℕ} (hX : 2≤X) (hM : X<M+b)
    (hp : Nat.Prime (M+b)) (G : (Fin 1 → ℝ) → ℝ) {rho : ℝ}
    (hrho : rho<1) (hbudget : HasBudget G rho) :
    divisorSum X G M (fun _ => b)=G 0 := by
  have ht : (fun _ : Fin 1 => b)=Fin.snoc (0 : Fin 0 → ℕ) b := by ext i; fin_cases i; rfl
  rw [ht,divisorSum_prime_delete hX hM hp G hrho hbudget,divisorSum_fin_zero]
  congr 1

theorem theta_div_log_le_upper {X M b Y : ℕ} (hX : 2≤X) (hY : M+b≤Y) (hYP : 1≤Y) :
    theta (M+b)/Real.log X≤Real.log Y/Real.log X := by
  apply div_le_div_of_nonneg_right _ (log_pos_of_two_le hX).le
  by_cases hp : Nat.Prime (M+b)
  · rw [theta,ite_eq_left hp]
    exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hY)
  · rw [theta,ite_eq_right hp]
    exact Real.log_nonneg (by exact_mod_cast hYP)

theorem singleton_divisor_majorant {X M b Y : ℕ} (hX : 2≤X) (hM : X<M+b)
    (hY : M+b≤Y) (hYP : 1≤Y) (G : (Fin 1 → ℝ) → ℝ) {rho : ℝ}
    (hrho : rho<1) (hbudget : HasBudget G rho) (hG : G 0=1) :
    theta (M+b)/Real.log X≤(Real.log Y/Real.log X)*divisorSum X G M (fun _ => b)^2 := by
  by_cases hp : Nat.Prime (M+b)
  · rw [divisorSum_singleton_at_prime hX hM hp G hrho hbudget,hG,one_pow,mul_one]
    exact theta_div_log_le_upper hX hY hYP
  · rw [theta,ite_eq_right hp,zero_div]
    exact mul_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast hYP))
      (log_pos_of_two_le hX).le) (sq_nonneg _)

theorem sum_square_diagonal_offdiag {α : Type*} [DecidableEq α]
    (B : Finset α) (f : α → ℝ) :
    (∑ b∈B,f b)^2=(∑ b∈B,f b^2)+∑ b∈B,∑ c∈B.erase b,f b*f c := by
  rw [pow_two,Finset.sum_mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [←Finset.sum_erase_add B (fun c => f b*f c) hb]
  ring

theorem detector_square_majorant {X M Y : ℕ} (hX : 2≤X) (hYP : 1≤Y)
    (B : Finset ℕ) (hM : ∀ b∈B, X<M+b) (hY : ∀ b∈B, M+b≤Y)
    (G : (Fin 1 → ℝ) → ℝ) {rho : ℝ}
    (hrho : rho<1) (hbudget : HasBudget G rho) (hG : G 0=1) :
    detector X B M^2≤(Real.log Y/Real.log X)*detector X B M+
      (Real.log Y/Real.log X)^2*∑ b∈B,∑ c∈B.erase b,
        divisorSum X G M (fun _ => b)^2*divisorSum X G M (fun _ => c)^2 := by
  classical
  let t := fun b => theta (M+b)/Real.log X
  let q := Real.log Y/Real.log X
  let D := fun b => divisorSum X G M (fun _ => b)
  have ht (b : ℕ) : 0≤t b := div_nonneg (theta_nonneg _) (log_pos_of_two_le hX).le
  have hq : 0≤q := div_nonneg (Real.log_nonneg (by exact_mod_cast hYP)) (log_pos_of_two_le hX).le
  have he : detector X B M=∑ b∈B,t b := by rw [detector,Finset.sum_div]
  have hupper (b : ℕ) (hb : b∈B) : t b≤q := theta_div_log_le_upper hX (hY b hb) hYP
  have hmajor (b : ℕ) (hb : b∈B) : t b≤q*(D b)^2 :=
    singleton_divisor_majorant hX (hM b hb) (hY b hb) hYP G hrho hbudget hG
  rw [he,sum_square_diagonal_offdiag,Finset.mul_sum,Finset.mul_sum]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro b hb
    simpa only [pow_two] using mul_le_mul_of_nonneg_right (hupper b hb) (ht b)
  · apply Finset.sum_le_sum
    intro b hb
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c hc
    have hcB := Finset.mem_of_mem_erase hc
    have hh := mul_le_mul (hmajor b hb) (hmajor c hcB) (ht c)
      (mul_nonneg hq (sq_nonneg (D b)))
    dsimp [q,D] at hh
    nlinarith

noncomputable def patternBoxShifts {n s h : ℕ} (p : Fin n → Fin s)
    (a : Fin s → ℕ) (u : Fin s → Fin h) : Fin n → ℕ :=
  fun i => a (p i)+(u (p i):ℕ)

theorem patternBoxShifts_family {n s h : ℕ} (p : Fin n → Fin s)
    (a : Fin s → ℕ) (u : Fin s → Fin h)
    (hu : u∈distinctBox (fun j => (a j:ℤ))) :
    shiftFamily (fun i => (patternBoxShifts p a u i:ℤ))=
      shiftFamily (fun i => ((p i).val:ℤ)) := by
  apply shiftFamily_eq_of_ker
  apply Setoid.ext
  intro i j
  have hi := (Finset.mem_filter.mp hu).2
  change ((patternBoxShifts p a u i:ℤ)=(patternBoxShifts p a u j:ℤ)) ↔
    ((p i).val:ℤ)=((p j).val:ℤ)
  have he (i : Fin n) : (patternBoxShifts p a u i:ℤ)=boxTuple (fun j => (a j:ℤ)) u (p i) := by
    simp only [patternBoxShifts,boxTuple,Nat.cast_add]
  rw [he,he,hi.eq_iff]
  constructor
  · intro h; rw [h]
  · intro h; apply Fin.ext; exact_mod_cast h

theorem patternBoxShifts_image {n s h : ℕ} (p : Fin n → Fin s)
    (hp : Function.Surjective p) (a : Fin s → ℕ) (u : Fin s → Fin h) :
    (Finset.univ.image fun i => (patternBoxShifts p a u i:ℤ))=
      Finset.univ.image (boxTuple (fun j => (a j:ℤ)) u) := by
  classical
  ext x
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨p i,by simp only [boxTuple,patternBoxShifts,Nat.cast_add]⟩
  · rintro ⟨j,rfl⟩
    obtain ⟨i,rfl⟩ := hp j
    exact ⟨i,by simp only [boxTuple,patternBoxShifts,Nat.cast_add]⟩

theorem surjective_shiftFamily_sign_sum {n s : ℕ} (p : Fin n → Fin s)
    (hp : Function.Surjective p) :
    (∑ S∈shiftFamily (fun i => ((p i).val:ℤ)),(-1:ℤ)^S.card)=-(s:ℤ) := by
  classical
  rw [shiftFamily_sign_sum]
  have he : (Finset.univ.image fun i => ((p i).val:ℤ))=
      Finset.univ.image (fun j : Fin s => (j.val:ℤ)) := by
    ext x
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩; exact ⟨p i,rfl⟩
    · rintro ⟨j,rfl⟩; obtain ⟨i,rfl⟩ := hp j; exact ⟨i,rfl⟩
  rw [he,Finset.card_image_of_injective]
  · simp only [Finset.card_univ,Fintype.card_fin]
  · intro i j hij; apply Fin.ext; exact_mod_cast (show (i.val:ℤ)=(j.val:ℤ) from hij)

theorem box_sum_scaled_norm_le {s h : ℕ} (a : Fin s → ℤ)
    (f g : (Fin s → Fin h) → ℂ) {L E : ℝ} (hL : 0<L) (hE : 0≤E)
    (herr : ∀ u∈distinctBox a, ‖(L:ℂ)^s*f u-g u‖≤E) :
    ‖(∑ u∈distinctBox a,f u)-(∑ u∈distinctBox a,g u)/(L:ℂ)^s‖≤((h:ℝ)/L)^s*E := by
  classical
  have hb : ‖∑ u∈distinctBox a,((L:ℂ)^s*f u-g u)‖≤(h:ℝ)^s*E := by
    calc
      _ ≤ ∑ _u∈distinctBox (h:=h) a,E := norm_sum_le_of_le _ herr
      _ = ((distinctBox (h:=h) a).card:ℝ)*E := by simp
      _ ≤ (h:ℝ)^s*E := by
        apply mul_le_mul_of_nonneg_right _ hE
        have hc := Finset.card_le_card (show distinctBox (h:=h) a⊆Finset.univ from Finset.subset_univ _)
        simpa only [Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow] using
          (show ((distinctBox (h:=h) a).card:ℝ)≤(Fintype.card (Fin s → Fin h):ℝ) from by exact_mod_cast hc)
  rw [Finset.sum_sub_distrib,←Finset.mul_sum] at hb
  have hLc : (L:ℂ)≠0 := by exact_mod_cast ne_of_gt hL
  have he : (∑ u∈distinctBox a,f u)-(∑ u∈distinctBox a,g u)/(L:ℂ)^s=
      ((L:ℂ)^s*(∑ u∈distinctBox a,f u)-∑ u∈distinctBox a,g u)/(L:ℂ)^s := by
    field_simp [hLc]
  rw [he,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  apply (div_le_iff₀ (pow_pos hL _)).mpr
  apply le_trans hb
  apply le_of_eq
  rw [div_pow]
  field_simp

theorem box_sum_errors_tendsto_zero (s : ℕ) (H : ℕ → ℕ) (a : ℕ → Fin s → ℤ)
    (L E : ℕ → ℝ) (lam : ℝ)
    (f g : (X : ℕ) → (Fin s → Fin (H X)) → ℂ)
    (hL : ∀ᶠ X in atTop,0<L X)
    (hHL : Tendsto (fun X => (H X:ℝ)/L X) atTop (𝓝 lam))
    (hE : Tendsto E atTop (𝓝 0))
    (herr : ∀ᶠ X in atTop, ∀ u∈distinctBox (a X),‖(L X:ℂ)^s*f X u-g X u‖≤E X) :
    Tendsto (fun X => (∑ u∈distinctBox (a X),f X u)-
      (∑ u∈distinctBox (a X),g X u)/(L X:ℂ)^s) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a:=fun X => ((H X:ℝ)/L X)^s*|E X|)
  · filter_upwards [hL,herr] with X hLX hX
    exact box_sum_scaled_norm_le (a X) (f X) (g X) hLX (abs_nonneg _) (fun u hu =>
      (hX u hu).trans (le_abs_self _))
  · simpa only [abs_zero,mul_zero] using (hHL.pow s).mul hE.abs

theorem natural_boxDiameterBound {s h K : ℕ} (a : Fin s → ℕ) (ha : ∀ j,a j≤K*h) :
    boxDiameterBound (h:=h) (fun j => (a j:ℤ)) ((K+1)*h) := by
  intro u i j
  dsimp [boxTuple]
  have hi := (u i).isLt
  have hj := (u j).isLt
  have hai := ha i
  have haj := ha j
  have hk : K*h+h=(K+1)*h := by ring
  omega

theorem unmarked_box_pattern_limit {n s K : ℕ} {lam : ℝ} (hlam : 0<lam)
    (p : Fin (n+1) → Fin s) (hp : Function.Surjective p)
    (a : ℕ → Fin s → ℕ)
    (ha : ∀ᶠ X : ℕ in atTop, ∀ j,a X j≤K*blockLength lam X)
    (F : (Fin (n+1) → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M) :
    Tendsto (fun X : ℕ => ∑ u∈distinctBox (h:=blockLength lam X) (fun j => (a X j:ℤ)),
      (average X (fun m => divisorSum X F m (patternBoxShifts p (a X) u)):ℂ)) atTop
      (𝓝 ((lam:ℂ)^s*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin (n+1)))
          (fun v => (F v.ofLp:ℂ)) hF hFs) (shiftFamily (fun i => ((p i).val:ℤ))))) := by
  classical
  let B := shiftFamily (fun i => ((p i).val:ℤ))
  let c := kernelConstant (sourceFourier (fourierCoordinateSum (Fin (n+1)))
    (fun v => (F v.ofLp:ℂ)) hF hFs) B
  let H := blockLength lam
  let az := fun X j => (a X j:ℤ)
  let f := fun X (u : Fin s → Fin (H X)) =>
    (average X (fun m => divisorSum X F m (patternBoxShifts p (a X) u)):ℂ)
  let g := fun X (u : Fin s → Fin (H X)) =>
    (singularSeries (Finset.univ.image (boxTuple (az X) u)):ℂ)*c
  obtain ⟨E,hE,herr⟩ := unmarked_average_uniform_asymptotic F rho hrho hrho1 hbudget
    hF hFs M hM hbound B (shiftFamily_nonempty _) s 2 (by omega)
    (surjective_shiftFamily_sign_sum p hp)
  have herror : ∀ᶠ X in atTop, ∀ u∈distinctBox (az X),
      ‖(Real.log X:ℂ)^s*f X u-g X u‖≤E X := by
    filter_upwards [herr,ha,blockLength_densityCutoff_eventually hlam.le (2*(K+1))]
      with X hX haX hcut
    intro u hu
    have hb (i : Fin (n+1)) : patternBoxShifts p (a X) u i≤(K+1)*H X := by
      have hi := (u (p i)).isLt
      have hh := haX (p i)
      dsimp [H] at hi
      dsimp [patternBoxShifts,H]
      rw [Nat.add_mul,one_mul]
      omega
    have hz := hX (patternBoxShifts p (a X) u) (patternBoxShifts_family p (a X) u hu)
       ((K+1)*H X) hb (by simpa only [Nat.mul_assoc] using hcut)
    rw [patternBoxShifts_image p hp] at hz
    exact hz
  have hL : ∀ᶠ X : ℕ in atTop,0<Real.log X := by
    filter_upwards [eventually_ge_atTop 2] with X hX
    exact log_pos_of_two_le hX
  have hHL := blockLength_ratio_tendsto hlam.le
  have he := box_sum_errors_tendsto_zero s H az (fun X => Real.log X) E lam f g hL hHL hE herror
  have hmean : Tendsto (fun X => singularBoxMean (h:=H X) (az X)) atTop (𝓝 1) := by
    apply uniform_singularBoxMean_tendsto s (K:=K+1) (by omega) H az (blockLength_tendsto hlam)
    filter_upwards [ha] with X hX
    exact natural_boxDiameterBound (a X) hX
  have hmain : Tendsto (fun X => (∑ u∈distinctBox (az X),g X u)/(Real.log X:ℂ)^s)
      atTop (𝓝 ((lam:ℂ)^s*c)) := by
    have hh := ((Complex.continuous_ofReal.continuousAt.tendsto.comp hHL).pow s).mul
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hmean)
    have hh' := hh.mul_const c
    simp only [Complex.ofReal_one,mul_one] at hh'
    apply hh'.congr'
    filter_upwards [hL,(blockLength_tendsto hlam).eventually_ge_atTop 1] with X hLX hHX
    have hHC : ((H X:ℕ):ℂ)≠0 := by exact_mod_cast (show H X≠0 by dsimp [H]; omega)
    have hLC : (Real.log X:ℂ)≠0 := by exact_mod_cast ne_of_gt hLX
    change (((H X:ℝ)/(Real.log X):ℝ):ℂ)^s * (singularBoxMean (h:=H X) (az X):ℂ)*c =
      (∑ u∈distinctBox (az X),g X u)/(Real.log X:ℂ)^s
    simp only [g,←Finset.sum_mul,←Complex.ofReal_sum,singularBoxMean,
      Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast]
    rw [div_pow]
    field_simp
  have h := he.add hmain
  simp only [sub_add_cancel,zero_add] at h
  exact h

theorem average_mono {X : ℕ} (f g : ℕ → ℝ)
    (h : ∀ m∈Finset.Ioc X (2*X),f m≤g m) : average X f≤average X g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg X)

theorem average_add (X : ℕ) (f g : ℕ → ℝ) :
    average X (fun m => f m+g m)=average X f+average X g := by
  rw [average,Finset.sum_add_distrib,add_div]
  rfl

theorem average_const_mul (X : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    average X (fun m => c*f m)=c*average X f := by
  simp only [average,←Finset.mul_sum,mul_div_assoc]

theorem average_finset_sum {α : Type*} (X : ℕ) (S : Finset α) (f : α → ℕ → ℝ) :
    average X (fun m => ∑ i∈S,f i m)=∑ i∈S,average X (f i) := by
  unfold average
  rw [Finset.sum_comm,Finset.sum_div]

theorem weighted_detector_square_majorant {X Y : ℕ} (hX : 2≤X) (hYP : 1≤Y)
    (B : Finset ℕ) (hM : ∀ m ∈ Finset.Ioc X (2*X), ∀ b ∈ B, X < m+b)
    (hY : ∀ m ∈ Finset.Ioc X (2*X), ∀ b ∈ B, m+b ≤ Y)
    (W : ℕ → ℝ) (hW : ∀ m∈Finset.Ioc X (2*X),0≤W m)
    (G : (Fin 1 → ℝ) → ℝ) {rho : ℝ}
    (hrho : rho<1) (hbudget : HasBudget G rho) (hG : G 0=1) :
    average X (fun m => W m*detector X B m^2)≤
      (Real.log Y/Real.log X)*average X (fun m => W m*detector X B m)+
      (Real.log Y/Real.log X)^2*∑ b∈B,∑ c∈B.erase b,
        average X (fun m => W m*divisorSum X G m (fun _ => b)^2*
          divisorSum X G m (fun _ => c)^2) := by
  classical
  have hh := average_mono (X:=X) (fun m => W m*detector X B m^2)
    (fun m => W m*((Real.log Y/Real.log X)*detector X B m+
      (Real.log Y/Real.log X)^2*∑ b∈B,∑ c∈B.erase b,
        divisorSum X G m (fun _ => b)^2*divisorSum X G m (fun _ => c)^2)) (by
      intro m hm
      exact mul_le_mul_of_nonneg_left (detector_square_majorant hX hYP B
        (hM m hm) (hY m hm) G hrho hbudget hG) (hW m hm))
  have he : (fun m => W m*((Real.log Y/Real.log X)*detector X B m+
      (Real.log Y/Real.log X)^2*∑ b∈B,∑ c∈B.erase b,
        divisorSum X G m (fun _ => b)^2*divisorSum X G m (fun _ => c)^2))=
      (fun m => (Real.log Y/Real.log X)*(W m*detector X B m)+
        (Real.log Y/Real.log X)^2*(∑ b∈B,∑ c∈B.erase b,
          W m*divisorSum X G m (fun _ => b)^2*divisorSum X G m (fun _ => c)^2)) := by
    funext m
    have hs : (∑ b∈B,∑ c∈B.erase b,
        W m*divisorSum X G m (fun _ => b)^2*divisorSum X G m (fun _ => c)^2)=
        W m*(∑ b∈B,∑ c∈B.erase b,
          divisorSum X G m (fun _ => b)^2*divisorSum X G m (fun _ => c)^2) := by
      simp only [Finset.mul_sum,mul_assoc]
    rw [hs]
    ring
  rw [he,average_add,average_const_mul,average_const_mul,
    average_finset_sum] at hh
  simpa only [average_finset_sum] using hh

theorem detector_log_ratio_tendsto {lam : ℝ} (hlam : 0≤lam) :
    Tendsto (fun X : ℕ => Real.log (2*X+2*blockLength lam X)/Real.log X) atTop (𝓝 1) := by
  have hlog : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun X : ℕ => (Real.log (X:ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlog
  have hH : Tendsto (fun X : ℕ => (blockLength lam X:ℝ)/(X:ℝ)) atTop (𝓝 0) := by
    have hlogratio : Tendsto (fun X : ℕ => Real.log (X:ℝ)/(X:ℝ)) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
    apply squeeze_zero' (Eventually.of_forall (fun X => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    · filter_upwards [eventually_ge_atTop 2] with X hX
      exact div_le_div_of_nonneg_right (blockLength_le_mul_log hlam hX) (Nat.cast_nonneg X)
    · simpa only [mul_div_assoc,mul_zero] using hlogratio.const_mul lam
  have harg : Tendsto (fun X : ℕ => 2+2*(blockLength lam X:ℝ)/(X:ℝ)) atTop (𝓝 2) := by
    simpa only [mul_zero,add_zero,mul_div_assoc] using tendsto_const_nhds.add (hH.const_mul 2)
  have hh := ((Real.continuousAt_log (by norm_num : (2:ℝ)≠0)).tendsto.comp harg).mul hinv
  have hh' := (tendsto_const_nhds (x := (1:ℝ))).add hh
  simp only [mul_zero,add_zero] at hh'
  apply hh'.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  have hXP : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hL := log_pos_of_two_le hX
  have hA : 0<2+2*(blockLength lam X:ℝ)/(X:ℝ) := by positivity
  have he : (2*(X:ℝ)+2*blockLength lam X)=(X:ℝ)*(2+2*(blockLength lam X:ℝ)/(X:ℝ)) := by
    field_simp
  simp only [Function.comp_apply]
  rw [he,Real.log_mul hXP.ne' hA.ne',add_div,div_self hL.ne']
  rfl

theorem exists_normalized_singleton_profile {tau : ℝ} (htau : 0<tau) :
    ∃ f : (Fin 1 → ℝ) → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f⊆positiveSimplex 1 tau ∧ (∀ v,0≤f v) ∧ (∫ v,f v)=1 := by
  have hopen : IsOpen (positiveSimplex 1 tau) := by
    have he : positiveSimplex 1 tau=(fun v : Fin 1 → ℝ => v 0) ⁻¹' Ioo 0 tau := by
      ext v
      simp [positiveSimplex,coordinateSum,Fin.forall_fin_one]
    rw [he]
    exact isOpen_Ioo.preimage (continuous_apply 0)
  have hmem : (fun _ : Fin 1 => tau/2)∈positiveSimplex 1 tau := by
    simp only [positiveSimplex,Set.mem_ofPred_eq,coordinateSum,Fin.sum_univ_one]
    constructor
    · intro i; positivity
    · linarith
  obtain ⟨f,hs,hc,hf,h01,h1⟩ := exists_contDiff_tsupport_subset (n:=(⊤:ℕ∞)) (hopen.mem_nhds hmem)
  have hn : ∀ v,0≤f v := fun v => (h01 (Set.mem_range_self v)).1
  let A := ∫ v,f v
  have hA : 0<A := integral_pos_of_integrable_nonneg_nonzero hf.continuous
    (hf.continuous.integrable_of_hasCompactSupport hc) hn (by rw [h1]; norm_num)
  let g := fun v => f v/A
  have hgc : HasCompactSupport g := hc.comp_left (g:=fun x : ℝ => x/A) (by simp)
  have hgs : tsupport g⊆positiveSimplex 1 tau :=
    (tsupport_comp_subset (g:=fun x : ℝ => x/A) (by simp) f).trans hs
  refine ⟨g,hf.div_const A,hgc,hgs,fun v => div_nonneg (hn v) hA.le,?_⟩
  rw [show g=(fun v => f v/A) from rfl,integral_div]
  exact div_self hA.ne'

theorem exists_detector_profile {tau : ℝ} (htau : 0<tau) :
    ∃ f : (Fin 1 → ℝ) → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f⊆positiveSimplex 1 tau ∧
      HasBudget (cumulativeProfile tau f) tau ∧
      ContDiff ℝ ∞ (cumulativeProfile tau f) ∧
      HasCompactSupport (cumulativeProfile tau f) ∧
      cumulativeProfile tau f 0=1 := by
  obtain ⟨f,hf,hc,hs,_hn,h1⟩ := exists_normalized_singleton_profile htau
  refine ⟨f,hf,hc,hs,cumulativeProfile_budget tau f hs,
    cumulativeProfile_smooth tau f hc hf,cumulativeProfile_compact tau f hc,?_⟩
  rw [cumulativeProfile_tail tau f hs 0 (fun _ => le_rfl)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,h1]
  intro v hv
  by_contra hne
  apply hv
  intro i
  exact (hs (subset_tsupport f hne)).1 i |>.le

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_Detectors

section File_OpenAIPrimeGaps_PatternMoments

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem box_series_scaled_tendsto {s K : ℕ} {lam : ℝ} (hlam : 0<lam)
    (a : ℕ → Fin s → ℕ)
    (ha : ∀ᶠ X : ℕ in atTop, ∀ j,a X j≤K*blockLength lam X) (c : ℂ) :
    Tendsto (fun X : ℕ =>
      (∑ u∈distinctBox (h:=blockLength lam X) (fun j => (a X j:ℤ)),
        (singularSeries (Finset.univ.image (boxTuple (fun j => (a X j:ℤ)) u)):ℂ)*c)/
        (Real.log X:ℂ)^s) atTop (𝓝 ((lam:ℂ)^s*c)) := by
  classical
  let H := blockLength lam
  let az := fun X j => (a X j:ℤ)
  have hL : ∀ᶠ X : ℕ in atTop,0<Real.log X := by
    filter_upwards [eventually_ge_atTop 2] with X hX
    exact log_pos_of_two_le hX
  have hHL := blockLength_ratio_tendsto hlam.le
  have hmean : Tendsto (fun X => singularBoxMean (h:=H X) (az X)) atTop (𝓝 1) := by
    apply uniform_singularBoxMean_tendsto s (K:=K+1) (by omega) H az (blockLength_tendsto hlam)
    filter_upwards [ha] with X hX
    exact natural_boxDiameterBound (a X) hX
  have hh := ((Complex.continuous_ofReal.continuousAt.tendsto.comp hHL).pow s).mul
    (Complex.continuous_ofReal.continuousAt.tendsto.comp hmean)
  have hh' := hh.mul_const c
  simp only [Complex.ofReal_one,mul_one] at hh'
  apply hh'.congr'
  filter_upwards [hL,(blockLength_tendsto hlam).eventually_ge_atTop 1] with X hLX hHX
  have hHC : ((H X:ℕ):ℂ)≠0 := by exact_mod_cast (show H X≠0 by dsimp [H]; omega)
  have hLC : (Real.log X:ℂ)≠0 := by exact_mod_cast ne_of_gt hLX
  change (((H X:ℝ)/(Real.log X):ℝ):ℂ)^s * (singularBoxMean (h:=H X) (az X):ℂ)*c = _
  simp only [←Finset.sum_mul,←Complex.ofReal_sum,singularBoxMean,
    Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast]
  dsimp only [az,H]
  dsimp only [H] at hHC
  rw [div_pow]
  field_simp [hHC]

theorem distinctBox_init {s h : ℕ} (a : Fin (s+1) → ℕ) (u : Fin (s+1) → Fin h)
    (hu : u∈distinctBox (fun j => (a j:ℤ))) :
    (fun j : Fin s => u j.castSucc)∈distinctBox (fun j : Fin s => (a j.castSucc:ℤ)) := by
  classical
  simp only [distinctBox,Finset.mem_filter,Finset.mem_univ,true_and] at hu ⊢
  exact hu.comp (Fin.castSucc_injective s)

theorem patternBoxShifts_ne_mark {n s h : ℕ} (p : Fin n → Fin s)
    (a : Fin (s+1) → ℕ) (u : Fin (s+1) → Fin h)
    (hu : u∈distinctBox (fun j => (a j:ℤ))) (i : Fin n) :
    patternBoxShifts p (fun j => a j.castSucc) (fun j => u j.castSucc) i≠
      a (Fin.last s)+(u (Fin.last s):ℕ) := by
  intro he
  have hj : boxTuple (fun j => (a j:ℤ)) u (p i).castSucc=
      boxTuple (fun j => (a j:ℤ)) u (Fin.last s) := by
    dsimp only [patternBoxShifts] at he
    dsimp only [boxTuple]
    exact_mod_cast he
  have hi := (Finset.mem_filter.mp hu).2 hj
  exact Fin.castSucc_ne_last (p i) hi

theorem marked_patternBoxShifts_image {n s h : ℕ} (p : Fin n → Fin s)
    (hp : Function.Surjective p) (a : Fin (s+1) → ℕ) (u : Fin (s+1) → Fin h) :
    insert ((a (Fin.last s)+(u (Fin.last s):ℕ):ℕ):ℤ)
      (Finset.univ.image fun i => (patternBoxShifts p (fun j => a j.castSucc)
        (fun j => u j.castSucc) i:ℤ))=
      Finset.univ.image (boxTuple (fun j => (a j:ℤ)) u) := by
  classical
  rw [patternBoxShifts_image p hp]
  ext x
  simp only [Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro (rfl | ⟨j,rfl⟩)
    · exact ⟨Fin.last s,by simp only [boxTuple,Nat.cast_add]⟩
    · exact ⟨j.castSucc,rfl⟩
  · rintro ⟨j,rfl⟩
    cases j using Fin.lastCases with
    | last => left; simp only [boxTuple,Nat.cast_add]
    | cast j => exact Or.inr ⟨j,rfl⟩

theorem marked_box_pattern_limit (hBV : BombieriVinogradov) {n s K : ℕ}
    {lam : ℝ} (hlam : 0<lam) (p : Fin n → Fin s) (hp : Function.Surjective p)
    (a : ℕ → Fin (s+1) → ℕ)
    (ha : ∀ᶠ X : ℕ in atTop, ∀ j,a X j≤K*blockLength lam X)
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrhohalf : rho<1/2) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M) :
    Tendsto (fun X : ℕ => ∑ u∈distinctBox (h:=blockLength lam X) (fun j => (a X j:ℤ)),
      (average X (fun m => divisorSum X F m
        (patternBoxShifts p (fun j => a X j.castSucc) (fun j => u j.castSucc))*
        theta (m+(a X (Fin.last s)+(u (Fin.last s):ℕ)))):ℂ)/(Real.log X:ℂ)) atTop
      (𝓝 ((lam:ℂ)^(s+1)*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin n))
          (fun v => (F v.ofLp:ℂ)) hF hFs) (shiftFamily (fun i => ((p i).val:ℤ))))) := by
  classical
  let B := shiftFamily (fun i => ((p i).val:ℤ))
  let c := kernelConstant (sourceFourier (fourierCoordinateSum (Fin n))
    (fun v => (F v.ofLp:ℂ)) hF hFs) B
  let H := blockLength lam
  let az := fun X j => (a X j:ℤ)
  let f := fun X (u : Fin (s+1) → Fin (H X)) =>
    (average X (fun m => divisorSum X F m
      (patternBoxShifts p (fun j => a X j.castSucc) (fun j => u j.castSucc))*
      theta (m+(a X (Fin.last s)+(u (Fin.last s):ℕ)))):ℂ)/(Real.log X:ℂ)
  let g := fun X (u : Fin (s+1) → Fin (H X)) =>
    (singularSeries (Finset.univ.image (boxTuple (az X) u)):ℂ)*c
  have hD : (0:ℝ)<(K+1:ℕ)*lam := mul_pos (by positivity) hlam
  have hH : ∀ᶠ X : ℕ in atTop, (((K+1)*H X:ℕ):ℝ)≤((K+1:ℕ):ℝ)*lam*(Real.log X)^(1:ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with X hX
    simpa only [Nat.cast_mul,Real.rpow_one,mul_assoc] using
      mul_le_mul_of_nonneg_left (blockLength_le_mul_log hlam.le hX) (Nat.cast_nonneg (K+1))
  obtain ⟨E,hE,herr⟩ := marked_average_uniform_asymptotic hBV F rho hrho hrhohalf hbudget
    hF hFs M hM hbound B (shiftFamily_nonempty _) s 2 (by omega)
    (surjective_shiftFamily_sign_sum p hp) (fun X => (K+1)*H X) hD hH
  have hL : ∀ᶠ X : ℕ in atTop,0<Real.log X := by
    filter_upwards [eventually_ge_atTop 2] with X hX
    exact log_pos_of_two_le hX
  have herror : ∀ᶠ X in atTop, ∀ u∈distinctBox (az X),
      ‖(Real.log X:ℂ)^(s+1)*f X u-g X u‖≤E X := by
    filter_upwards [herr,ha,hL,blockLength_densityCutoff_eventually hlam.le (2*(K+1))]
      with X hX haX hLX hcut
    intro u hu
    have hb (j : Fin (s+1)) : a X j+(u j:ℕ)≤(K+1)*H X := by
      have hi := (u j).isLt
      have hh := haX j
      dsimp [H] at hi
      dsimp [H]
      rw [Nat.add_mul,one_mul]
      omega
    have hz := hX (patternBoxShifts p (fun j => a X j.castSucc) (fun j => u j.castSucc))
      (patternBoxShifts_family p _ _ (distinctBox_init (a X) u hu))
      (a X (Fin.last s)+(u (Fin.last s):ℕ)) (hb (Fin.last s))
      (patternBoxShifts_ne_mark p (a X) u hu) ((K+1)*H X)
      (fun i => hb (p i).castSucc) (hb (Fin.last s))
      (by simpa only [Nat.mul_assoc] using hcut)
    rw [marked_patternBoxShifts_image p hp] at hz
    have hLC : (Real.log X:ℂ)≠0 := by exact_mod_cast ne_of_gt hLX
    convert hz using 1
    dsimp [f,g,c,az]
    congr 1
    rw [pow_succ]
    field_simp
  have he := box_sum_errors_tendsto_zero (s+1) H az (fun X => Real.log X) E lam f g
    hL (blockLength_ratio_tendsto hlam.le) hE herror
  have hmain : Tendsto (fun X => (∑ u∈distinctBox (az X),g X u)/(Real.log X:ℂ)^(s+1))
      atTop (𝓝 ((lam:ℂ)^(s+1)*c)) := by
    simpa only [g,az,H,←Finset.sum_mul] using box_series_scaled_tendsto hlam a ha c
  have hh := he.add hmain
  simp only [sub_add_cancel,zero_add] at hh
  exact hh

noncomputable def patternLabels {ι : Type*} [Fintype ι] (r : Setoid ι) :
    ι → Fin (Fintype.card (Quotient r)) :=
  fun i => Fintype.equivFin (Quotient r) (Quotient.mk r i)

theorem patternLabels_surjective {ι : Type*} [Fintype ι] (r : Setoid ι) :
    Function.Surjective (patternLabels r) := by
  intro j
  obtain ⟨i,hi⟩ := Quotient.mk_surjective ((Fintype.equivFin (Quotient r)).symm j)
  refine ⟨i,?_⟩
  simp only [patternLabels,hi,Equiv.apply_symm_apply]

theorem patternTupleEquiv_labels {n : ℕ} (r : Setoid (Fin n)) (h a : ℕ)
    (b : {b // b∈patternClass (α:=Fin h) r}) :
    patternBoxShifts (patternLabels r) (fun _ => a)
      (patternTupleEquiv r h a b).val=(fun i => a+(b.val i:ℕ)) := by
  funext i
  simp only [patternBoxShifts,patternLabels,patternTupleEquiv_apply,Equiv.symm_apply_apply]
  rfl

theorem pattern_sum_average_eq_box {n : ℕ} (r : Setoid (Fin n)) (h a X : ℕ)
    (F : (Fin n → ℝ) → ℝ) :
    (∑ b∈patternClass (α:=Fin h) r,
      (average X (fun m => divisorSum X F m (fun i => a+(b i:ℕ))):ℂ))=
    ∑ u∈distinctBox (s:=Fintype.card (Quotient r)) (h:=h) (fun _ => (a:ℤ)),
      (average X (fun m => divisorSum X F m (patternBoxShifts (patternLabels r) (fun _ => a) u)):ℂ) := by
  classical
  conv_lhs => rw [←Finset.sum_coe_sort]
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Fintype.sum_equiv (patternTupleEquiv r h a)
  intro b
  rw [patternTupleEquiv_labels]

theorem unmarked_pattern_limit {n K : ℕ} {lam : ℝ} (hlam : 0<lam)
    (r : Setoid (Fin (n+1))) (a : ℕ → ℕ)
    (ha : ∀ᶠ X : ℕ in atTop,a X≤K*blockLength lam X)
    (F : (Fin (n+1) → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M) :
    Tendsto (fun X : ℕ => ∑ b∈patternClass (α:=Fin (blockLength lam X)) r,
      (average X (fun m => divisorSum X F m (fun i => a X+(b i:ℕ))):ℂ)) atTop
      (𝓝 ((lam:ℂ)^Fintype.card (Quotient r)*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin (n+1)))
          (fun v => (F v.ofLp:ℂ)) hF hFs)
        (shiftFamily (fun i => (numericPattern r i:ℤ))))) := by
  have hh := unmarked_box_pattern_limit hlam (patternLabels r) (patternLabels_surjective r)
    (fun X _ => a X) (ha.mono (fun _ h _ => h)) F rho hrho hrho1 hbudget hF hFs M hM hbound
  have he : (fun X : ℕ => ∑ b∈patternClass (α:=Fin (blockLength lam X)) r,
      (average X (fun m => divisorSum X F m (fun i => a X+(b i:ℕ))):ℂ))=
      (fun X : ℕ => ∑ u∈distinctBox (h:=blockLength lam X) (fun _ => (a X:ℤ)),
        (average X (fun m => divisorSum X F m (patternBoxShifts (patternLabels r) (fun _ => a X) u)):ℂ)) := by
    funext X
    exact pattern_sum_average_eq_box r _ _ _ F
  rw [he]
  exact hh

theorem unmarked_labeled_expansion_limit {n K : ℕ} {lam : ℝ} (hlam : 0<lam)
    (a : ℕ → ℕ) (ha : ∀ᶠ X : ℕ in atTop,a X≤K*blockLength lam X)
    (F : (Fin (n+1) → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M)
    (k : Setoid (Fin (n+1)) → ℂ) :
    Tendsto (fun X : ℕ => ∑ b : Fin (n+1) → Fin (blockLength lam X),
      k (Setoid.ker b)*(average X (fun m => divisorSum X F m (fun i => a X+(b i:ℕ))):ℂ)) atTop
      (𝓝 (∑ r : Setoid (Fin (n+1)),k r*((lam:ℂ)^Fintype.card (Quotient r)*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin (n+1)))
          (fun v => (F v.ofLp:ℂ)) hF hFs)
        (shiftFamily (fun i => (numericPattern r i:ℤ)))))) := by
  classical
  have hh := tendsto_finsetSum Finset.univ (fun r _ =>
    (unmarked_pattern_limit hlam r a ha F rho hrho hrho1 hbudget hF hFs M hM hbound).const_mul (k r))
  apply hh.congr'
  exact Eventually.of_forall (fun X => by
    dsimp only
    calc
      (∑ r : Setoid (Fin (n+1)), k r*∑ b∈patternClass (α:=Fin (blockLength lam X)) r,
        (average X (fun m => divisorSum X F m (fun i => a X+(b i:ℕ))):ℂ)) =
        ∑ r : Setoid (Fin (n+1)), ∑ b∈patternClass (α:=Fin (blockLength lam X)) r,
          k (Setoid.ker b)*(average X (fun m => divisorSum X F m (fun i => a X+(b i:ℕ))):ℂ) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        rw [(mem_patternClass r b).mp hb]
      _ = _ := sum_patterns _
    apply Finset.sum_congr (by ext b; simp)
    intro b _
    rfl)

def permutedLabels {n : ℕ} (e : Equiv.Perm (Fin n)) : Fin (n+n) → Fin n := Fin.append id e

theorem permutedLabels_fiber_sum {n : ℕ} (e : Equiv.Perm (Fin n)) (r : Fin n) {K : Type*} [AddCommMonoid K]
    (w : Fin (n+n) → K) :
    (∑ i∈Finset.univ.filter (fun i => permutedLabels e i=r), w i)=w (r.castAdd n)+w ((e.symm r).natAdd n) := by
  classical
  rw [Finset.sum_filter,Fin.sum_univ_add]
  simp [permutedLabels,←Equiv.eq_symm_apply]

@[simp] theorem permutedLabels_fiber_card {n : ℕ} (e : Equiv.Perm (Fin n)) (r : Fin n) :
    (Finset.univ.filter fun i => permutedLabels e i=r).card=2 := by
  simpa using permutedLabels_fiber_sum e r (fun _ => (1:ℕ))

theorem permutedLabels_classical_fiber {n : ℕ} (e : Equiv.Perm (Fin n)) (r : Fin n) :
    @Finset.filter (Fin (n+n)) (fun i => permutedLabels e i=r)
      (fun _ => Classical.propDecidable _) Finset.univ =
      Finset.univ.filter (fun i => permutedLabels e i=r) := by
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]

theorem permutedLabels_kernel {n : ℕ} (e : Equiv.Perm (Fin n)) (w : Fin (n+n) → ℂ) :
    familyKernel (fiberSubsetFamily (permutedLabels e) Finset.univ) w =
      (∏ i,w i)*(∏ i : Fin n,(w (i.castAdd n)+w ((e.symm i).natAdd n))⁻¹) := by
  rw [familyKernel_small_fibers (permutedLabels e) Finset.univ (fun i => Finset.mem_univ _) (by
    intro r _
    rw [permutedLabels_classical_fiber,permutedLabels_fiber_card])]
  simp only [permutedLabels_classical_fiber,permutedLabels_fiber_card,Finset.filter_true,
    permutedLabels_fiber_sum]

noncomputable def permutedRay {n : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) : EuclideanSpace ℝ (Fin (n+n)) :=
  EuclideanSpace.single (i.castAdd n) 1+EuclideanSpace.single ((e.symm i).natAdd n) 1

theorem permutedRay_frequency {n : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) (u : EuclideanSpace ℝ (Fin (n+n))) :
    laplaceFrequency (fourierCoordinateSum (Fin (n+n))) (permutedRay e i) u =
      frequencyW (u (i.castAdd n))+frequencyW (u ((e.symm i).natAdd n)) := by
  unfold permutedRay
  simp only [laplaceFrequency,map_add,inner_add_right,Complex.ofReal_add,
    fourierCoordinateSum_apply]
  simp [frequencyW,EuclideanSpace.inner_single_right]
  ring

theorem permutedRay_positive {n : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) :
    0<fourierCoordinateSum (Fin (n+n)) (permutedRay e i) := by
  have h := congrArg Complex.re (permutedRay_frequency e i 0)
  simp only [laplaceFrequency_re,Complex.add_re,frequencyW_re] at h
  rw [h]
  norm_num

theorem rayVector_permuted {n : ℕ} (e : Equiv.Perm (Fin n)) (y : Fin n → ℝ) :
    (rayVector (permutedRay e) y).ofLp=Fin.append y (y ∘ e) := by
  classical
  ext i
  cases i using Fin.addCases with
  | left i => simp [rayVector,permutedRay,WithLp.ofLp_sum,Finset.sum_apply,
      smul_eq_mul,Pi.single_apply,Finset.sum_add_distrib,castAdd_ne_addNat_self]
  | right i =>
    have he (x : Fin n) : i=e.symm x ↔ x=e i := by
      constructor
      · intro h; rw [h]; simp
      · intro h; rw [h]; simp
    simp [rayVector,permutedRay,WithLp.ofLp_sum,Finset.sum_apply,
      smul_eq_mul,Pi.single_apply,Finset.sum_add_distrib,addNat_ne_castAdd_self,he]

theorem permuted_kernelConstant {n : ℕ} (e : Equiv.Perm (Fin n))
    (F : EuclideanSpace ℝ (Fin (n+n)) → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    kernelConstant (sourceFourier (fourierCoordinateSum (Fin (n+n))) F hF hFs)
      (fiberSubsetFamily (permutedLabels e) Finset.univ) =
      ∫ y, signedDirections (coordinateDirectionList (Fin (n+n))) F (rayVector (permutedRay e) y)
        ∂positiveOrthantMeasure (Fin n) := by
  rw [←sourceFourier_derivative_laplace (fourierCoordinateSum (Fin (n+n)))
    (coordinateDirectionList (Fin (n+n))) F hF hFs (permutedRay e) (permutedRay_positive e)]
  unfold kernelConstant
  apply integral_congr_ae
  filter_upwards [] with u
  rw [contourKernel,permutedLabels_kernel,coordinateDirectionList_multiplier]
  simp only [permutedRay_frequency,mul_assoc]

theorem cumulative_tensor_permuted_kernel {n : ℕ} (e : Equiv.Perm (Fin n)) {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ positiveSimplex n tau) (hsym : SymmetricFunction f)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
      (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
      (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ))) :
    kernelConstant (sourceFourier (fourierCoordinateSum (Fin (n+n)))
      (fun v => (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ)) hF hFs)
      (fiberSubsetFamily (permutedLabels e) Finset.univ) = (l2Mass f:ℂ) := by
  rw [permuted_kernelConstant]
  have he : (∫ y, signedDirections (coordinateDirectionList (Fin (n+n)))
      (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
        (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ)) (rayVector (permutedRay e) y)
      ∂positiveOrthantMeasure (Fin n)) =
      ∫ y, (f y^2:ℂ) ∂positiveOrthantMeasure (Fin n) := by
    apply integral_congr_ae
    rw [positiveOrthantMeasure_eq_restrict]
    filter_upwards [ae_restrict_mem (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioi))] with y hy
    rw [cumulativeProfile_signed_full (tau+tau) (tensorProfile f f)
      (tensorProfile_compact f f hf hf) (tensorProfile_smooth f f hfs hfs)
      (tensorProfile_tsupport f f hsupp hsupp)]
    · rw [rayVector_permuted,tensorProfile_append,hsym,pow_two]
      simp only [Complex.ofReal_mul]
    · intro i
      rw [rayVector_permuted]
      cases i using Fin.addCases with
      | left i => simpa using (hy i (Set.mem_univ i)).le
      | right i => simpa using (hy (e i) (Set.mem_univ (e i))).le
  rw [he]
  simp_rw [←Complex.ofReal_pow]
  rw [integral_complex_ofReal,positiveOrthantMeasure_eq_restrict]
  congr 1
  unfold l2Mass
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hfz : f y=0 := by
    by_contra hne
    exact hy (fun i _ => (hsupp (subset_tsupport f hne)).1 i)
  simp [hfz]

def functionPerm {ι α : Type*} (e : Equiv.Perm ι) : (ι → α) ≃ (ι → α) where
  toFun f := f ∘ e
  invFun f := f ∘ e.symm
  left_inv f := by funext i; simp
  right_inv f := by funext i; simp

theorem divisorCoefficient_perm {n X : ℕ} (F : (Fin n → ℝ) → ℝ)
    (hF : SymmetricFunction F) (e : Equiv.Perm (Fin n)) (d : Fin n → ℕ) :
    divisorCoefficient X F (d ∘ e)=divisorCoefficient X F d := by
  unfold divisorCoefficient
  have he : logCoordinates X (d ∘ e)=(logCoordinates X d) ∘ e := rfl
  rw [he,hF]
  congr 1
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

theorem divisorSum_perm {n X m : ℕ} (F : (Fin n → ℝ) → ℝ)
    (hF : SymmetricFunction F) (e : Equiv.Perm (Fin n)) (b : Fin n → ℕ) :
    divisorSum X F m (b ∘ e)=divisorSum X F m b := by
  classical
  unfold divisorSum
  symm
  apply Finset.sum_equiv (functionPerm e)
  · intro d
    simp only [Fintype.mem_piFinset,functionPerm,Equiv.coe_fn_mk,Function.comp_apply]
    exact e.surjective.forall
  · intro d _
    exact (divisorCoefficient_perm F hF e d).symm

theorem injective_same_range_perm {n : ℕ} {α : Type*}
    (a b : Fin n → α) (hb : Function.Injective b)
    (hab : Set.range a=Set.range b) : ∃ e : Equiv.Perm (Fin n), b=a ∘ e := by
  classical
  have hs : ∀ i,∃ j,a j=b i := by
    intro i
    have : b i ∈ Set.range a := hab.symm ▸ Set.mem_range_self i
    exact this
  choose e he using hs
  have hei : Function.Injective e := by
    intro i j hij
    apply hb
    rw [←he i,←he j,hij]
  exact ⟨Equiv.ofBijective e ⟨hei,Finite.surjective_of_injective hei⟩,by funext i; exact (he i).symm⟩

noncomputable def weightedBlock {n : ℕ} (X h a : ℕ)
    (F : (Fin n → ℝ) → ℝ) (k : Setoid (Fin n) → ℝ) (m : ℕ) : ℝ :=
  ∑ b : Fin n → Fin h, k (Setoid.ker b)*divisorSum X F m (fun i => a+(b i:ℕ))

noncomputable def tensorCoefficient {n p : ℕ}
    (k : Setoid (Fin n) → ℝ) (l : Setoid (Fin p) → ℝ) : Setoid (Fin (n+p)) → ℝ :=
  fun r => k (Setoid.comap (Fin.castAdd p) r)*l (Setoid.comap (Fin.natAdd n) r)

@[simp] theorem append_ker_left {n p : ℕ} {α : Type*}
    (b : Fin n → α) (c : Fin p → α) :
    Setoid.comap (Fin.castAdd p) (Setoid.ker (Fin.append b c))=Setoid.ker b := by
  apply Setoid.ext
  intro i j
  change Fin.append b c (i.castAdd p)=Fin.append b c (j.castAdd p) ↔ b i=b j
  simp only [Fin.append_left]

@[simp] theorem append_ker_right {n p : ℕ} {α : Type*}
    (b : Fin n → α) (c : Fin p → α) :
    Setoid.comap (Fin.natAdd n) (Setoid.ker (Fin.append b c))=Setoid.ker c := by
  apply Setoid.ext
  intro i j
  change Fin.append b c (i.natAdd n)=Fin.append b c (j.natAdd n) ↔ c i=c j
  simp only [Fin.append_right]

theorem weightedBlock_mul {n p : ℕ} (X h a m : ℕ)
    (F : (Fin n → ℝ) → ℝ) (G : (Fin p → ℝ) → ℝ)
    (k : Setoid (Fin n) → ℝ) (l : Setoid (Fin p) → ℝ) :
    weightedBlock X h a F k m * weightedBlock X h a G l m =
    weightedBlock X h a (tensorProfile F G) (tensorCoefficient k l) m := by
  classical
  unfold weightedBlock
  rw [Finset.sum_mul_sum,←Finset.sum_product']
  apply Finset.sum_equiv (Fin.appendEquiv n p)
  · intro bc; simp
  intro bc _
  rw [show (Fin.appendEquiv n p) bc=Fin.append bc.1 bc.2 from rfl]
  simp only [tensorCoefficient,append_ker_left,append_ker_right]
  have he : (fun i => a+((Fin.append bc.1 bc.2 i :Fin h):ℕ))=
      Fin.append (fun i => a+(bc.1 i:ℕ)) (fun i => a+(bc.2 i:ℕ)) := by
    funext i
    cases i using Fin.addCases <;> simp
  rw [he,divisorSum_tensor]
  ring

theorem average_weightedBlock (X h a : ℕ) {n : ℕ}
    (F : (Fin n → ℝ) → ℝ) (k : Setoid (Fin n) → ℝ) :
    average X (weightedBlock X h a F k)=
    ∑ b : Fin n → Fin h, k (Setoid.ker b)*average X (fun m => divisorSum X F m (fun i => a+(b i:ℕ))) := by
  unfold weightedBlock
  rw [average_finset_sum]
  simp only [average_const_mul]

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_PatternMoments

section File_OpenAIPrimeGaps_WeightMoments

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem weightedBlock_average_limit {n K : ℕ} {lam : ℝ} (hlam : 0<lam)
    (a : ℕ → ℕ) (ha : ∀ᶠ X : ℕ in atTop,a X≤K*blockLength lam X)
    (F : (Fin (n+1) → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M)
    (k : Setoid (Fin (n+1)) → ℝ) :
    Tendsto (fun X : ℕ => (average X (weightedBlock X (blockLength lam X) (a X) F k):ℂ)) atTop
      (𝓝 (∑ r : Setoid (Fin (n+1)),(k r:ℂ)*((lam:ℂ)^Fintype.card (Quotient r)*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin (n+1)))
          (fun v => (F v.ofLp:ℂ)) hF hFs)
        (shiftFamily (fun i => (numericPattern r i:ℤ)))))) := by
  simpa only [average_weightedBlock,Complex.ofReal_sum,Complex.ofReal_mul] using
    unmarked_labeled_expansion_limit hlam a ha F rho hrho hrho1 hbudget hF hFs M hM hbound
      (fun r => (k r:ℂ))

theorem average_const {X : ℕ} (hX : X≠0) (c : ℝ) : average X (fun _ => c)=c := by
  unfold average
  simp only [Finset.sum_const,Nat.card_Ioc,nsmul_eq_mul]
  rw [show 2*X-X=X by omega]
  simp [hX]

@[simp] theorem weightedBlock_zero (X h a m : ℕ)
    (F : (Fin 0 → ℝ) → ℝ) (k : Setoid (Fin 0) → ℝ) :
    weightedBlock X h a F k m=k ⊥*F 0 := by
  unfold weightedBlock
  simp only [divisorSum_fin_zero]
  have he (b : Fin 0 → Fin h) : Setoid.ker b=⊥ := by
    apply Setoid.ext
    intro i
    exact Fin.elim0 i
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,pow_zero,one_nsmul]

theorem weightedBlock_average_converges {n K : ℕ} {lam : ℝ} (hlam : 0<lam)
    (a : ℕ → ℕ) (ha : ∀ᶠ X : ℕ in atTop,a X≤K*blockLength lam X)
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (k : Setoid (Fin n) → ℝ) :
    ∃ c : ℝ,Tendsto (fun X : ℕ => average X (weightedBlock X (blockLength lam X) (a X) F k))
      atTop (𝓝 c) := by
  cases n with
  | zero =>
    refine ⟨k ⊥*F 0,?_⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with X hX
    have he : weightedBlock X (blockLength lam X) (a X) F k=(fun _ => k ⊥*F 0) :=
      funext (fun m => weightedBlock_zero X _ _ m F k)
    rw [he,average_const (by omega : X≠0)]
  | succ n =>
    have hc : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)) :=
      (hF.comp_isClosedEmbedding (EuclideanSpace.equiv (Fin (n+1)) ℝ).toHomeomorph.isClosedEmbedding).comp_left
        Complex.ofReal_zero
    have hs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (hFs.comp (EuclideanSpace.equiv (Fin (n+1)) ℝ).contDiff)
    obtain ⟨M,hM⟩ := hFs.continuous.bounded_above_of_compact_support hF
    have hM0 : 0≤M := (norm_nonneg (F 0)).trans (hM 0)
    have hh := weightedBlock_average_limit hlam a ha F rho hrho hrho1 hbudget hc hs M hM0
      (fun v _ => by simpa only [Real.norm_eq_abs] using hM v) k
    exact ⟨_,Complex.continuous_re.continuousAt.tendsto.comp hh⟩

theorem HasBudget.tensor {n p : ℕ} {F : (Fin n → ℝ) → ℝ} {G : (Fin p → ℝ) → ℝ}
    {a b : ℝ} (hF : HasBudget F a) (hG : HasBudget G b) :
    HasBudget (tensorProfile F G) (a+b) := by
  intro v hv hsum
  unfold tensorProfile
  rw [Fin.sum_univ_add] at hsum
  by_cases hf : a<∑ i : Fin n,v (i.castAdd p)
  · rw [hF _ (fun i => hv (i.castAdd p)) hf,zero_mul]
  · rw [hG _ (fun i => hv (i.natAdd n)) (by linarith),mul_zero]

theorem weightedBlock_fourth_converges {n K : ℕ} {lam : ℝ} (hlam : 0<lam)
    (a : ℕ → ℕ) (ha : ∀ᶠ X : ℕ in atTop,a X≤K*blockLength lam X)
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho4 : 4*rho<1) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (k : Setoid (Fin n) → ℝ) :
    ∃ c : ℝ,Tendsto (fun X : ℕ => average X
      (fun m => weightedBlock X (blockLength lam X) (a X) F k m^4)) atTop (𝓝 c) := by
  let F2 := tensorProfile F F
  let k2 := tensorCoefficient k k
  have hc2 := tensorProfile_compact F F hF hF
  have hs2 := tensorProfile_smooth F F hFs hFs
  obtain ⟨c,hc⟩ := weightedBlock_average_converges hlam a ha (tensorProfile F2 F2)
    ((rho+rho)+(rho+rho)) (by positivity) (by linarith)
    ((hbudget.tensor hbudget).tensor (hbudget.tensor hbudget))
    (tensorProfile_compact F2 F2 hc2 hc2) (tensorProfile_smooth F2 F2 hs2 hs2)
    (tensorCoefficient k2 k2)
  refine ⟨c,?_⟩
  convert hc using 1
  ext X
  congr 1
  funext m
  rw [←weightedBlock_mul,←weightedBlock_mul]
  ring

theorem fourth_power_sum_le {α : Type*} (S : Finset α) (f : α → ℝ) :
    (∑ i∈S,f i)^4≤(S.card:ℝ)^3*∑ i∈S,f i^4 := by
  have h1 := sq_sum_le_card_mul_sum_sq (s:=S) (f:=f)
  have h2 := sq_sum_le_card_mul_sum_sq (s:=S) (f:=fun i => f i^2)
  have h3 := mul_self_le_mul_self (sq_nonneg (∑ i∈S,f i)) h1
  have h4 := mul_le_mul_of_nonneg_left h2 (sq_nonneg (S.card:ℝ))
  simp only [←pow_mul] at h3 h4
  nlinarith only [h3,h4]

noncomputable def subsetCoefficient (n : ℕ) (r : Setoid (Fin n)) : ℝ :=
  if r=⊥ then (n.factorial:ℝ)⁻¹ else 0

noncomputable def orderedWeight (tau lam : ℝ) (k : ℕ)
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (X m : ℕ) : ℝ :=
  ∑ j : Fin (k+1), weightedBlock X (blockLength lam X) (blockLength lam X+1)
    (cumulativeProfile tau (f j)) (subsetCoefficient j) m

theorem blockOffset_eventually {lam : ℝ} (hlam : 0<lam) :
    ∀ᶠ X : ℕ in atTop,blockLength lam X+1≤2*blockLength lam X := by
  filter_upwards [(blockLength_tendsto hlam).eventually_ge_atTop 1] with X hX
  omega

theorem finite_sum_fourth_bound {α : Type*} [Fintype α]
    (f : α → ℕ → ℕ → ℝ)
    (h : ∀ j,∃ c : ℝ,Tendsto (fun X => average X (fun m => f j X m^4)) atTop (𝓝 c)) :
    ∃ M : ℝ,0<M ∧ ∀ᶠ X : ℕ in atTop,
      average X (fun m => (∑ j,f j X m)^4)≤M := by
  classical
  choose c hc using h
  let C := (Fintype.card α:ℝ)^3*∑ j,c j
  have ht : Tendsto (fun X => (Fintype.card α:ℝ)^3*∑ j,average X (fun m => f j X m^4))
      atTop (𝓝 C) := (tendsto_finsetSum Finset.univ (fun j _ => hc j)).const_mul _
  refine ⟨|C|+1,by positivity,?_⟩
  filter_upwards [(tendsto_order.mp ht).2 (|C|+1) (by linarith [le_abs_self C])] with X hX
  apply le_trans ?_ hX.le
  calc
    _ ≤ average X (fun m => (Fintype.card α:ℝ)^3*∑ j,f j X m^4) :=
      average_mono _ _ (fun m _ => by
        simpa only [Finset.card_univ] using
          (fourth_power_sum_le Finset.univ (fun j => f j X m)))
    _ = _ := by rw [average_const_mul,average_finset_sum]

theorem orderedWeight_fourth_bound {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (htau4 : 4*tau<1) (hlam : 0<lam) :
    ∃ M : ℝ,0<M ∧ ∀ᶠ X : ℕ in atTop,
      average X (fun m => orderedWeight tau lam k f X m^4)≤M := by
  apply finite_sum_fourth_bound
  intro j
  have hfj := hf.2.1 j (by omega : (j:ℕ)≤k)
  exact weightedBlock_fourth_converges hlam (fun X => blockLength lam X+1)
    (blockOffset_eventually hlam) (cumulativeProfile tau (f j)) tau htau htau4
    (cumulativeProfile_budget tau (f j) hfj.2.2.1)
    (cumulativeProfile_compact tau (f j) hfj.2.1)
    (cumulativeProfile_smooth tau (f j) hfj.2.1 hfj.1) (subsetCoefficient j)

noncomputable def matchedPattern {n : ℕ} (e : Equiv.Perm (Fin n)) : Setoid (Fin (n+n)) :=
  Setoid.ker (permutedLabels e)

@[simp] theorem matchedPattern_left {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Setoid.comap (Fin.castAdd n) (matchedPattern e)=⊥ := by
  apply Setoid.ext
  intro i j
  change permutedLabels e (i.castAdd n)=permutedLabels e (j.castAdd n) ↔ i=j
  simp [permutedLabels]

@[simp] theorem matchedPattern_right {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Setoid.comap (Fin.natAdd n) (matchedPattern e)=⊥ := by
  apply Setoid.ext
  intro i j
  change permutedLabels e (i.natAdd n)=permutedLabels e (j.natAdd n) ↔ i=j
  simp [permutedLabels]

theorem matchedPattern_injective {n : ℕ} : Function.Injective (@matchedPattern n) := by
  intro e f hef
  apply Equiv.ext
  intro i
  have he : (matchedPattern e) ((e i).castAdd n) (i.natAdd n) := by
    change permutedLabels e ((e i).castAdd n)=permutedLabels e (i.natAdd n)
    simp [permutedLabels]
  rw [hef] at he
  change permutedLabels f ((e i).castAdd n)=permutedLabels f (i.natAdd n) at he
  simpa [permutedLabels] using he

theorem matchedPattern_quotient_card {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Fintype.card (Quotient (matchedPattern e))=n := by
  have hs : Function.Surjective (permutedLabels e) := by
    intro j
    exact ⟨j.castAdd n,by simp [permutedLabels]⟩
  have eqv : Quotient (matchedPattern e) ≃ Fin n :=
    Setoid.quotientKerEquivOfSurjective (permutedLabels e) hs
  exact (Fintype.card_congr eqv).trans (Fintype.card_fin n)

theorem ker_eq_bot_iff_injective {α β : Type*} (f : α → β) :
    Setoid.ker f=⊥ ↔ Function.Injective f := by
  constructor
  · intro h x y hxy
    change (Setoid.ker f) x y at hxy
    rw [h] at hxy
    exact hxy
  · intro h
    apply Setoid.ext
    intro x y
    exact h.eq_iff

theorem numericPattern_left_injective {m n : ℕ} (r : Setoid (Fin (m+n)))
    (h : Setoid.comap (Fin.castAdd n) r=⊥) :
    Function.Injective (fun i : Fin m => numericPattern r (i.castAdd n)) := by
  apply (ker_eq_bot_iff_injective _).mp
  have he : Setoid.ker (fun i : Fin m => numericPattern r (i.castAdd n))=
      Setoid.comap (Fin.castAdd n) (Setoid.ker (numericPattern r)) := rfl
  rw [he,numericPattern_ker,h]

theorem numericPattern_right_injective {m n : ℕ} (r : Setoid (Fin (m+n)))
    (h : Setoid.comap (Fin.natAdd m) r=⊥) :
    Function.Injective (fun i : Fin n => numericPattern r (i.natAdd m)) := by
  apply (ker_eq_bot_iff_injective _).mp
  have he : Setoid.ker (fun i : Fin n => numericPattern r (i.natAdd m))=
      Setoid.comap (Fin.natAdd m) (Setoid.ker (numericPattern r)) := rfl
  rw [he,numericPattern_ker,h]

theorem injective_ranges_card {m n : ℕ} {α : Type*} (a : Fin m → α) (b : Fin n → α)
    (ha : Function.Injective a) (hb : Function.Injective b) (hab : Set.range a=Set.range b) : m=n := by
  have e : Fin m ≃ Fin n := (Equiv.ofInjective a ha).trans
    ((Set.equivOfEq hab).trans (Equiv.ofInjective b hb).symm)
  simpa using Fintype.card_congr e

theorem matching_pattern_eq {n : ℕ} (r : Setoid (Fin (n+n)))
    (hleft : Setoid.comap (Fin.castAdd n) r=⊥)
    (hright : Setoid.comap (Fin.natAdd n) r=⊥)
    (hrange : Set.range (fun i : Fin n => numericPattern r (i.castAdd n))=
      Set.range (fun i : Fin n => numericPattern r (i.natAdd n))) :
    ∃ e : Equiv.Perm (Fin n),r=matchedPattern e := by
  let a := fun i : Fin n => numericPattern r (i.castAdd n)
  let b := fun i : Fin n => numericPattern r (i.natAdd n)
  have ha : Function.Injective a := numericPattern_left_injective r hleft
  have hb : Function.Injective b := numericPattern_right_injective r hright
  obtain ⟨e,he⟩ := injective_same_range_perm a b hb hrange
  refine ⟨e,?_⟩
  rw [←numericPattern_ker r]
  have hf : numericPattern r=a ∘ permutedLabels e := by
    funext i
    cases i using Fin.addCases with
    | left i => simp [a,permutedLabels]
    | right i => simpa [b,permutedLabels] using congrFun he i
  rw [hf,ker_comp_injective _ _ ha]
  rfl

theorem matchedPattern_family {n : ℕ} (e : Equiv.Perm (Fin n)) :
    equalityPatternFamily (matchedPattern e)=fiberSubsetFamily (permutedLabels e) Finset.univ := by
  classical
  have hi : Finset.univ.image (permutedLabels e)=Finset.univ := by
    ext j
    simp only [Finset.mem_image,Finset.mem_univ,true_and,iff_true]
    exact ⟨j.castAdd n,by simp [permutedLabels]⟩
  rw [←hi]
  unfold equalityPatternFamily shiftFamily
  ext S
  simp only [mem_fiberSubsetFamily_image]
  have he (i j : Fin (n+n)) :
      (numericPattern (matchedPattern e) i:ℤ)=(numericPattern (matchedPattern e) j:ℤ) ↔
        permutedLabels e i=permutedLabels e j := by
    change (Setoid.ker (fun x => (numericPattern (matchedPattern e) x:ℤ))) i j ↔
      (matchedPattern e) i j
    rw [numericPattern_int_ker]
  simp_rw [he]

theorem sum_matched_patterns {n : ℕ} (c : ℂ) (A : Setoid (Fin (n+n)) → ℂ)
    (hzero : ∀ r,r∉Set.range (@matchedPattern n) → A r=0)
    (hvalue : ∀ e : Equiv.Perm (Fin n),A (matchedPattern e)=c) :
    (∑ r,A r)=(n.factorial:ℂ)*c := by
  classical
  calc
    _ = ∑ r∈Finset.univ.image (@matchedPattern n),A r := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro r _ hr
      apply hzero r
      rintro ⟨e,rfl⟩
      exact hr (Finset.mem_image_of_mem _ (Finset.mem_univ e))
    _ = ∑ e : Equiv.Perm (Fin n),A (matchedPattern e) :=
      Finset.sum_image (fun _ _ _ _ h => matchedPattern_injective h)
    _ = _ := by simp [hvalue,Fintype.card_perm]

theorem realEuclidean_compact {n : ℕ} (F : (Fin n → ℝ) → ℝ) (hF : HasCompactSupport F) :
    HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)) :=
  (hF.comp_isClosedEmbedding (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isClosedEmbedding).comp_left
    Complex.ofReal_zero

theorem realEuclidean_smooth {n : ℕ} (F : (Fin n → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (hF.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff)

noncomputable def cumulativePatternKernel {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hs : ContDiff ℝ ∞ f) (r : Setoid (Fin n)) : ℂ :=
  kernelConstant (sourceFourier (fourierCoordinateSum (Fin n))
    (fun v => (cumulativeProfile tau f v.ofLp:ℂ))
    (realEuclidean_compact _ (cumulativeProfile_compact tau f hf))
    (realEuclidean_smooth _ (cumulativeProfile_smooth tau f hf hs))) (equalityPatternFamily r)

theorem cumulative_pair_unmatched {m n : ℕ} {tau : ℝ}
    (f : (Fin m → ℝ) → ℝ) (g : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex m tau) (hsg : tsupport g⊆positiveSimplex n tau)
    (r : Setoid (Fin (m+n)))
    (hl : Setoid.comap (Fin.castAdd n) r=⊥) (hr : Setoid.comap (Fin.natAdd m) r=⊥)
    (hne : Set.range (fun i : Fin m => numericPattern r (i.castAdd n))≠
      Set.range (fun i : Fin n => numericPattern r (i.natAdd m))) :
    cumulativePatternKernel (tau+tau) (tensorProfile f g)
      (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs) r=0 := by
  let a := fun i : Fin m => numericPattern r (i.castAdd n)
  let b := fun i : Fin n => numericPattern r (i.natAdd m)
  have ha := numericPattern_left_injective r hl
  have hb := numericPattern_right_injective r hr
  have he : Fin.append a b=numericPattern r := by
    funext i
    cases i using Fin.addCases <;> simp [a,b]
  have hfamily : equalityPatternFamily r=
      fiberSubsetFamily (Fin.append a b) (Finset.univ.image (Fin.append a b)) := by
    unfold equalityPatternFamily shiftFamily
    ext S
    simp only [mem_fiberSubsetFamily_image,he,Int.natCast_inj]
  unfold cumulativePatternKernel
  rw [hfamily]
  convert cumulative_tensor_unmatched_kernel_zero f g hf hg hfs hgs hsf hsg a b ha hb hne
    (realEuclidean_compact _ (cumulativeProfile_compact _ _ (tensorProfile_compact f g hf hg)))
    (realEuclidean_smooth _ (cumulativeProfile_smooth _ _
      (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs))) using 1
  congr 2
  ext x
  simp

theorem cumulative_pair_matched {n : ℕ} {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsym : SymmetricFunction f)
    (e : Equiv.Perm (Fin n)) :
    cumulativePatternKernel (tau+tau) (tensorProfile f f)
      (tensorProfile_compact f f hf hf) (tensorProfile_smooth f f hfs hfs) (matchedPattern e)=
      (l2Mass f:ℂ) := by
  unfold cumulativePatternKernel
  rw [matchedPattern_family]
  exact cumulative_tensor_permuted_kernel e f hf hfs hsf hsym _ _

theorem cumulative_square_pattern_sum {n : ℕ} {tau : ℝ} (lam : ℝ)
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsym : SymmetricFunction f) :
    (∑ r : Setoid (Fin (n+n)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient n) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*cumulativePatternKernel (tau+tau) (tensorProfile f f)
          (tensorProfile_compact f f hf hf) (tensorProfile_smooth f f hfs hfs) r))=
      (alpha lam n*l2Mass f:ℂ) := by
  classical
  let A := fun r : Setoid (Fin (n+n)) =>
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient n) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*cumulativePatternKernel (tau+tau) (tensorProfile f f)
          (tensorProfile_compact f f hf hf) (tensorProfile_smooth f f hfs hfs) r)
  have hz : ∀ r,r∉Set.range (@matchedPattern n) → A r=0 := by
    intro r hr
    by_cases hl : Setoid.comap (Fin.castAdd n) r=⊥
    · by_cases hr' : Setoid.comap (Fin.natAdd n) r=⊥
      · have hne : Set.range (fun i : Fin n => numericPattern r (i.castAdd n))≠
            Set.range (fun i : Fin n => numericPattern r (i.natAdd n)) := by
          intro he
          obtain ⟨e,rfl⟩ := matching_pattern_eq r hl hr' he
          exact hr ⟨e,rfl⟩
        simp only [A,cumulative_pair_unmatched f f hf hf hfs hfs hsf hsf r hl hr' hne,mul_zero]
      · simp only [A,tensorCoefficient,subsetCoefficient,ite_eq_right hr',mul_zero,Complex.ofReal_zero,zero_mul]
    · simp only [A,tensorCoefficient,subsetCoefficient,ite_eq_right hl,zero_mul,Complex.ofReal_zero]
  have hv : ∀ e : Equiv.Perm (Fin n), A (matchedPattern e)=
      ((n.factorial:ℂ)⁻¹)^2*((lam:ℂ)^n*(l2Mass f:ℂ)) := by
    intro e
    simp only [A,tensorCoefficient,matchedPattern_left,matchedPattern_right,subsetCoefficient,
      ↓reduceIte,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_natCast,
      matchedPattern_quotient_card,cumulative_pair_matched f hf hfs hsf hsym e,pow_two]
  have hh := sum_matched_patterns _ A hz hv
  change (∑ r,A r)=_
  rw [hh]
  have hn : (n.factorial:ℂ)≠0 := by exact_mod_cast n.factorial_ne_zero
  simp only [alpha,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast]
  field_simp

theorem cumulative_cross_pattern_sum {m n : ℕ} (hmn : m≠n) {tau : ℝ} (lam : ℝ)
    (f : (Fin m → ℝ) → ℝ) (g : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex m tau) (hsg : tsupport g⊆positiveSimplex n tau) :
    (∑ r : Setoid (Fin (m+n)),
      (tensorCoefficient (subsetCoefficient m) (subsetCoefficient n) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*cumulativePatternKernel (tau+tau) (tensorProfile f g)
          (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs) r))=0 := by
  apply Finset.sum_eq_zero
  intro r _
  by_cases hl : Setoid.comap (Fin.castAdd n) r=⊥
  · by_cases hr : Setoid.comap (Fin.natAdd m) r=⊥
    · have hne : Set.range (fun i : Fin m => numericPattern r (i.castAdd n))≠
          Set.range (fun i : Fin n => numericPattern r (i.natAdd m)) := by
        intro he
        exact hmn (injective_ranges_card _ _ (numericPattern_left_injective r hl)
          (numericPattern_right_injective r hr) he)
      rw [cumulative_pair_unmatched f g hf hg hfs hgs hsf hsg r hl hr hne,mul_zero,mul_zero]
    · simp only [tensorCoefficient,subsetCoefficient,ite_eq_right hr,mul_zero,Complex.ofReal_zero,zero_mul]
  · simp only [tensorCoefficient,subsetCoefficient,ite_eq_right hl,zero_mul,Complex.ofReal_zero]

theorem weightedBlock_congr_orthant {n X : ℕ} (hX : 2≤X) (h a m : ℕ)
    (F G : (Fin n → ℝ) → ℝ) (k : Setoid (Fin n) → ℝ)
    (hFG : ∀ v,(∀ i,0≤v i) → F v=G v) :
    weightedBlock X h a F k m=weightedBlock X h a G k m := by
  apply Finset.sum_congr rfl
  intro b _
  rw [divisorSum_congr_orthant hX m _ F G hFG]

theorem weightedBlock_cumulative_mul {n p X : ℕ} (hX : 2≤X) (h a m : ℕ) {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : tsupport f⊆positiveSimplex n tau) (hg : tsupport g⊆positiveSimplex p tau)
    (k : Setoid (Fin n) → ℝ) (l : Setoid (Fin p) → ℝ) :
    weightedBlock X h a (cumulativeProfile tau f) k m*
      weightedBlock X h a (cumulativeProfile tau g) l m=
    weightedBlock X h a (cumulativeProfile (tau+tau) (tensorProfile f g)) (tensorCoefficient k l) m := by
  rw [weightedBlock_mul]
  apply weightedBlock_congr_orthant hX
  intro v hv
  let v1 := fun i : Fin n => v (i.castAdd p)
  let v2 := fun i : Fin p => v (i.natAdd n)
  have he : v=Fin.append v1 v2 := by
    funext i
    cases i using Fin.addCases <;> simp [v1,v2]
  rw [he,tensorProfile_append]
  exact (cumulativeProfile_tensor f g hf hg v1 v2 (fun i => hv _) (fun i => hv _)).symm

theorem weightedBlock_positive_limit {n K : ℕ} (hn : 0<n) {lam : ℝ} (hlam : 0<lam)
    (a : ℕ → ℕ) (ha : ∀ᶠ X : ℕ in atTop,a X≤K*blockLength lam X)
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (k : Setoid (Fin n) → ℝ) :
    Tendsto (fun X : ℕ => (average X (weightedBlock X (blockLength lam X) (a X) F k):ℂ)) atTop
      (𝓝 (∑ r : Setoid (Fin n),(k r:ℂ)*((lam:ℂ)^Fintype.card (Quotient r)*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin n))
          (fun v => (F v.ofLp:ℂ)) (realEuclidean_compact F hF) (realEuclidean_smooth F hFs))
        (equalityPatternFamily r)))) := by
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨M,hM⟩ := hFs.continuous.bounded_above_of_compact_support hF
    exact weightedBlock_average_limit hlam a ha F rho hrho hrho1 hbudget
      (realEuclidean_compact F hF) (realEuclidean_smooth F hFs) M
      ((norm_nonneg (F 0)).trans (hM 0)) (fun v _ => by simpa only [Real.norm_eq_abs] using hM v) k

theorem cumulative_pair_limit {n p K : ℕ} (hnp : 0<n+p) {tau lam : ℝ}
    (htau : 0≤tau) (htau2 : 2*tau<1) (hlam : 0<lam)
    (a : ℕ → ℕ) (ha : ∀ᶠ X : ℕ in atTop,a X≤K*blockLength lam X)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsg : tsupport g⊆positiveSimplex p tau) :
    Tendsto (fun X : ℕ => (average X (fun m =>
      weightedBlock X (blockLength lam X) (a X) (cumulativeProfile tau f) (subsetCoefficient n) m*
      weightedBlock X (blockLength lam X) (a X) (cumulativeProfile tau g) (subsetCoefficient p) m):ℂ))
      atTop (𝓝 (∑ r : Setoid (Fin (n+p)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*cumulativePatternKernel (tau+tau) (tensorProfile f g)
          (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs) r))) := by
  have hh := weightedBlock_positive_limit hnp hlam a ha
    (cumulativeProfile (tau+tau) (tensorProfile f g)) (tau+tau) (by positivity) (by linarith)
    (cumulativeProfile_budget _ _ (tensorProfile_tsupport f g hsf hsg))
    (cumulativeProfile_compact _ _ (tensorProfile_compact f g hf hg))
    (cumulativeProfile_smooth _ _ (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs))
    (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p))
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  congr 2
  funext m
  exact (weightedBlock_cumulative_mul hX _ _ m f g hsf hsg _ _).symm

@[simp] theorem cumulativeProfile_fin_zero {tau : ℝ} (f : (Fin 0 → ℝ) → ℝ)
    (hsf : tsupport f⊆positiveSimplex 0 tau) (v : Fin 0 → ℝ) :
    cumulativeProfile tau f v=f 0 := by
  rw [cumulativeProfile_tail tau f hsf v (fun i => Fin.elim0 i)]
  rw [Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ)]
  have he : Ici v=(Set.univ : Set (Fin 0 → ℝ)) := by
    ext x
    simp only [Set.mem_Ici,Set.mem_univ,iff_true]
    exact fun i => Fin.elim0 i
  rw [he,setIntegral_univ]
  exact integral_dirac f 0

@[simp] theorem l2Mass_fin_zero (f : (Fin 0 → ℝ) → ℝ) : l2Mass f=f 0^2 := by
  unfold l2Mass
  have he : (fun x => f x^2)=(fun _ : Fin 0 → ℝ => f 0^2) := by
    funext x
    rw [Subsingleton.elim x 0]
  rw [he,Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ)]
  simp

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_WeightMoments

section File_OpenAIPrimeGaps_ProfileSymmetry

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem cumulative_square_limit {n K : ℕ} {tau lam : ℝ}
    (htau : 0≤tau) (htau2 : 2*tau<1) (hlam : 0<lam)
    (a : ℕ → ℕ) (ha : ∀ᶠ X : ℕ in atTop,a X≤K*blockLength lam X)
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsym : SymmetricFunction f) :
    Tendsto (fun X : ℕ => average X (fun m =>
      weightedBlock X (blockLength lam X) (a X) (cumulativeProfile tau f) (subsetCoefficient n) m^2))
      atTop (𝓝 (alpha lam n*l2Mass f)) := by
  cases Nat.eq_zero_or_pos n with
  | inl hn =>
    subst n
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with X hX
    simp only [weightedBlock_zero,cumulativeProfile_fin_zero f hsf,
      subsetCoefficient,↓reduceIte,Nat.factorial_zero,Nat.cast_one,inv_one,one_mul]
    rw [average_const (by omega : X≠0),l2Mass_fin_zero]
    simp [alpha]
  | inr hn =>
    have hh := cumulative_pair_limit (by omega : 0<n+n) htau htau2 hlam a ha
      f f hf hf hfs hfs hsf hsf
    rw [cumulative_square_pattern_sum lam f hf hfs hsf hsym] at hh
    have hh' := Complex.continuous_re.continuousAt.tendsto.comp hh
    simpa [Function.comp_def,Complex.mul_re,←pow_two] using hh'

theorem cumulative_cross_limit {n p K : ℕ} (hnp : n≠p) {tau lam : ℝ}
    (htau : 0≤tau) (htau2 : 2*tau<1) (hlam : 0<lam)
    (a : ℕ → ℕ) (ha : ∀ᶠ X : ℕ in atTop,a X≤K*blockLength lam X)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsg : tsupport g⊆positiveSimplex p tau) :
    Tendsto (fun X : ℕ => average X (fun m =>
      weightedBlock X (blockLength lam X) (a X) (cumulativeProfile tau f) (subsetCoefficient n) m*
      weightedBlock X (blockLength lam X) (a X) (cumulativeProfile tau g) (subsetCoefficient p) m))
      atTop (𝓝 0) := by
  have hh := cumulative_pair_limit (by omega : 0<n+p) htau htau2 hlam a ha
    f g hf hg hfs hgs hsf hsg
  rw [cumulative_cross_pattern_sum hnp lam f g hf hg hfs hgs hsf hsg] at hh
  exact Complex.continuous_re.continuousAt.tendsto.comp hh

theorem orderedWeight_second_limit {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (htau2 : 2*tau<1) (hlam : 0<lam) :
    Tendsto (fun X : ℕ => average X (fun m => orderedWeight tau lam k f X m^2))
      atTop (𝓝 (familyW lam k f)) := by
  classical
  let H := fun (j : Fin (k+1)) X m => weightedBlock X (blockLength lam X) (blockLength lam X+1)
       (cumulativeProfile tau (f j)) (subsetCoefficient j) m
  have hp (i j : Fin (k+1)) :
      Tendsto (fun X : ℕ => average X (fun m => H i X m*H j X m)) atTop
        (𝓝 (if i=j then alpha lam i*l2Mass (f i) else 0)) := by
    have hfi := hf.2.1 i (by omega : (i:ℕ)≤k)
    have hfj := hf.2.1 j (by omega : (j:ℕ)≤k)
    by_cases hij : i=j
    · subst j
      simp only [↓reduceIte]
      simpa only [H,pow_two] using cumulative_square_limit htau htau2 hlam
        (fun X => blockLength lam X+1) (blockOffset_eventually hlam)
        (f i) hfi.2.1 hfi.1 hfi.2.2.1 hfi.2.2.2
    · simp only [ite_eq_right hij]
      have hne : (i:ℕ)≠(j:ℕ) := fun h => hij (Fin.ext h)
      exact cumulative_cross_limit hne htau htau2 hlam
        (fun X => blockLength lam X+1) (blockOffset_eventually hlam)
        (f i) (f j) hfi.2.1 hfj.2.1 hfi.1 hfj.1 hfi.2.2.1 hfj.2.2.1
  have hs := tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_finsetSum Finset.univ fun j _ => hp i j
  have he (X : ℕ) : average X (fun m => orderedWeight tau lam k f X m^2)=
      ∑ i : Fin (k+1),∑ j : Fin (k+1),average X (fun m => H i X m*H j X m) := by
    unfold orderedWeight
    simp only [pow_two,Finset.sum_mul_sum,average_finset_sum]
    rfl
  simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte] at hs
  have hv : (∑ i : Fin (k+1),alpha lam i*l2Mass (f i))=familyW lam k f := by
    exact Fin.sum_univ_eq_sum_range (fun j : ℕ => alpha lam j*l2Mass (f j)) (k+1)
  rw [hv] at hs
  exact hs.congr' (Eventually.of_forall fun X => (he X).symm)

theorem cumulativeProfile_perm_orthant {n : ℕ} {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hsupp : tsupport f⊆positiveSimplex n tau)
    (hsym : SymmetricFunction f) (e : Equiv.Perm (Fin n))
    (v : Fin n → ℝ) (hv : ∀ i,0≤v i) :
    cumulativeProfile tau f (v ∘ e)=cumulativeProfile tau f v := by
  change cumulativeProfile tau f (fun i => v (e i))=cumulativeProfile tau f v
  rw [cumulativeProfile_tail tau f hsupp _ (fun i => hv (e i)),
    cumulativeProfile_tail tau f hsupp _ hv]
  let q := MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e.symm
  have hq : MeasurePreserving q volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) e.symm
  have hq_apply (x : Fin n → ℝ) : q x=x ∘ e := by
    funext i
    simp [q,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]
  have he : q ⁻¹' {x : Fin n → ℝ | ∀ i,v (e i)≤x i}={x : Fin n → ℝ | ∀ i,v i≤x i} := by
    ext x
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,hq_apply,Function.comp_apply]
    constructor
    · intro h i
      simpa using h (e.symm i)
    · intro h i
      exact h (e i)
  have hh := hq.integral_comp' (fun x => ({x : Fin n → ℝ | ∀ i,v (e i)≤x i}).indicator f x)
  have hefun : (fun x => ({x : Fin n → ℝ | ∀ i,v (e i)≤x i}).indicator f (q x))=
      ({x : Fin n → ℝ | ∀ i,v i≤x i}).indicator f := by
    funext x
    have hx : (∀ i,v (e i)≤q x i) ↔ ∀ i,v i≤x i := by
      simpa only [Set.mem_preimage,Set.mem_ofPred_eq] using
        (Set.ext_iff.mp he x)
    have hm : q x∈{x : Fin n → ℝ | ∀ i,v (e i)≤x i} ↔ x∈{x : Fin n → ℝ | ∀ i,v i≤x i} := hx
    by_cases hvx : x∈{x : Fin n → ℝ | ∀ i,v i≤x i}
    · rw [Set.indicator_of_mem (hm.mpr hvx),Set.indicator_of_mem hvx,hq_apply,hsym]
    · rw [Set.indicator_of_notMem (fun h => hvx (hm.mp h)),Set.indicator_of_notMem hvx]
  rw [hefun,integral_indicator (by measurability), integral_indicator (by measurability)] at hh
  exact hh.symm

theorem divisorSum_perm_orthant {n X m : ℕ} (hX : 2≤X)
    (F : (Fin n → ℝ) → ℝ)
    (hF : ∀ (e : Equiv.Perm (Fin n)) v,(∀ i,0≤v i) → F (v ∘ e)=F v)
    (e : Equiv.Perm (Fin n)) (b : Fin n → ℕ) :
    divisorSum X F m (b ∘ e)=divisorSum X F m b := by
  classical
  unfold divisorSum
  symm
  apply Finset.sum_equiv (functionPerm e)
  · intro d
    simp only [Fintype.mem_piFinset,functionPerm,Equiv.coe_fn_mk,Function.comp_apply]
    exact e.surjective.forall
  · intro d hd
    change divisorCoefficient X F d=divisorCoefficient X F (d ∘ e)
    unfold divisorCoefficient
    have hp : ∀ i,0<d i := fun i => Nat.pos_of_mem_divisors ((Fintype.mem_piFinset.mp hd) i)
    have he : logCoordinates X (d ∘ e)=(logCoordinates X d) ∘ e := rfl
    rw [he,hF e _ (logCoordinates_nonneg hX hp)]
    congr 1
    exact (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm

noncomputable def subsetEnumeration {h n : ℕ}
    (S : {S : Finset (Fin h) // S.card=n}) : Fin n ↪ Fin h :=
  S.1.orderEmbOfFin S.2 |>.toEmbedding

theorem subsetEnumeration_image {h n : ℕ} (S : {S : Finset (Fin h) // S.card=n}) :
    Finset.univ.image (subsetEnumeration S)=S.1 := by
  classical
  ext x
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,rfl⟩
    exact (S.1.orderIsoOfFin S.2 i).2
  · intro hx
    refine ⟨(S.1.orderIsoOfFin S.2).symm ⟨x,hx⟩,?_⟩
    change ((S.1.orderIsoOfFin S.2) ((S.1.orderIsoOfFin S.2).symm ⟨x,hx⟩)).val=x
    simp

noncomputable def enumeratePerm {h n : ℕ}
    (t : {S : Finset (Fin h) // S.card=n} × Equiv.Perm (Fin n)) :
    {b : Fin n → Fin h // Function.Injective b} :=
  ⟨subsetEnumeration t.1 ∘ t.2,(subsetEnumeration t.1).injective.comp t.2.injective⟩

theorem enumeratePerm_image {h n : ℕ}
    (t : {S : Finset (Fin h) // S.card=n} × Equiv.Perm (Fin n)) :
    Finset.univ.image (enumeratePerm t).val=t.1.1 := by
  classical
  rw [←subsetEnumeration_image t.1]
  ext x
  simp only [Finset.mem_image,Finset.mem_univ,true_and,enumeratePerm,Function.comp_apply]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨t.2 i,hi⟩
  · rintro ⟨i,hi⟩
    exact ⟨t.2.symm i,by simpa using hi⟩

theorem enumeratePerm_bijective (h n : ℕ) :
    Function.Bijective (enumeratePerm (h:=h) (n:=n)) := by
  classical
  constructor
  · rintro ⟨S,e⟩ ⟨T,d⟩ he
    have hST : S=T := by
      apply Subtype.ext
      rw [←enumeratePerm_image (S,e),←enumeratePerm_image (T,d),he]
    subst T
    have hed : e=d := by
      apply Equiv.ext
      intro i
      apply (subsetEnumeration S).injective
      exact congrFun (congrArg Subtype.val he) i
    subst d
    rfl
  · intro b
    let S : {S : Finset (Fin h) // S.card=n} :=
      ⟨Finset.univ.image b.val,by rw [Finset.card_image_of_injective _ b.2]; simp⟩
    have he : Set.range (subsetEnumeration S)=Set.range b.val := by
      ext x
      have hh := Finset.ext_iff.mp (subsetEnumeration_image S) x
      simpa only [Finset.mem_image,Finset.mem_univ,true_and,S,Set.mem_range] using hh
    obtain ⟨e,he⟩ := injective_same_range_perm (subsetEnumeration S) b.val b.2 he
    exact ⟨(S,e),Subtype.ext he.symm⟩

noncomputable def unorderedBlock {n : ℕ} (X h a : ℕ)
    (F : (Fin n → ℝ) → ℝ) (m : ℕ) : ℝ :=
  ∑ S : {S : Finset (Fin h) // S.card=n},
    divisorSum X F m (fun i => a+(subsetEnumeration S i:ℕ))

theorem weightedBlock_eq_unordered {n X h a m : ℕ} (hX : 2≤X)
    (F : (Fin n → ℝ) → ℝ)
    (hsym : ∀ (e : Equiv.Perm (Fin n)) v,(∀ i,0≤v i) → F (v ∘ e)=F v) :
    weightedBlock X h a F (subsetCoefficient n) m=unorderedBlock X h a F m := by
  classical
  unfold weightedBlock
  have he : (∑ b : Fin n → Fin h, subsetCoefficient n (Setoid.ker b)*
      divisorSum X F m (fun i => a+(b i:ℕ)))=
      ∑ b : {b : Fin n → Fin h // Function.Injective b},
        (n.factorial:ℝ)⁻¹*divisorSum X F m (fun i => a+(b.val i:ℕ)) := by
    simp only [subsetCoefficient,Setoid.ker_eq_bot_iff,ite_mul,zero_mul]
    rw [←Finset.sum_filter]
    exact Finset.sum_subtype (p:=fun b : Fin n → Fin h => Function.Injective b)
      (Finset.univ.filter fun b : Fin n → Fin h => Function.Injective b) (by simp) _
  rw [he]
  rw [←Fintype.sum_equiv (Equiv.ofBijective enumeratePerm (enumeratePerm_bijective h n))
    (fun t => (n.factorial:ℝ)⁻¹*divisorSum X F m (fun i => a+((enumeratePerm t).val i:ℕ)))
    _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  unfold unorderedBlock
  apply Finset.sum_congr rfl
  intro S _
  have hd (e : Equiv.Perm (Fin n)) :
      divisorSum X F m (fun i => a+((enumeratePerm (S,e)).val i:ℕ))=
      divisorSum X F m (fun i => a+(subsetEnumeration S i:ℕ)) :=
    divisorSum_perm_orthant hX F hsym e (fun i => a+(subsetEnumeration S i:ℕ))
  simp only [hd,Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul]
  have hn : (n.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

noncomputable def unorderedWeight (tau lam : ℝ) (k : ℕ)
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (X m : ℕ) : ℝ :=
  ∑ j : Fin (k+1), unorderedBlock X (blockLength lam X) (blockLength lam X+1)
    (cumulativeProfile tau (f j)) m

theorem orderedWeight_eq_unordered {tau lam : ℝ} {k X : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (hX : 2≤X) (m : ℕ) : orderedWeight tau lam k f X m=unorderedWeight tau lam k f X m := by
  unfold orderedWeight unorderedWeight
  apply Finset.sum_congr rfl
  intro j _
  have hfj := hf.2.1 j (by omega : (j:ℕ)≤k)
  exact weightedBlock_eq_unordered hX _ (cumulativeProfile_perm_orthant _ hfj.2.2.1 hfj.2.2.2)

theorem unorderedWeight_second_limit {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (htau2 : 2*tau<1) (hlam : 0<lam) :
    Tendsto (fun X : ℕ => average X (fun m => unorderedWeight tau lam k f X m^2))
      atTop (𝓝 (familyW lam k f)) := by
  apply (orderedWeight_second_limit f hf htau htau2 hlam).congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  congr 1
  funext m
  rw [orderedWeight_eq_unordered f hf hX m]

theorem unorderedWeight_fourth_bound {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (htau4 : 4*tau<1) (hlam : 0<lam) :
    ∃ M : ℝ,0<M ∧ ∀ᶠ X : ℕ in atTop,
      average X (fun m => unorderedWeight tau lam k f X m^4)≤M := by
  obtain ⟨M,hM,h⟩ := orderedWeight_fourth_bound f hf htau htau4 hlam
  refine ⟨M,hM,?_⟩
  filter_upwards [h,eventually_ge_atTop 2] with X hX hX2
  simpa only [orderedWeight_eq_unordered f hf hX2] using hX

noncomputable def separatedOffsets (s h : ℕ) : Fin (s+1) → ℕ :=
  Fin.snoc (fun _ => h+1) 1

theorem separatedBox_mem {s h : ℕ} (u : Fin s → Fin h) (c : Fin h) :
    Fin.snoc u c∈distinctBox (fun j => (separatedOffsets s h j:ℤ)) ↔
      u∈distinctBox (fun _ : Fin s => ((h+1:ℕ):ℤ)) := by
  classical
  simp only [distinctBox,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro hu i j hij
    have he : boxTuple (fun j => (separatedOffsets s h j:ℤ)) (Fin.snoc u c) i.castSucc=
        boxTuple (fun j => (separatedOffsets s h j:ℤ)) (Fin.snoc u c) j.castSucc := by
      simpa [boxTuple,separatedOffsets] using hij
    exact Fin.castSucc_injective s (hu he)
  · intro hu i j hij
    cases i using Fin.lastCases with
    | last =>
      cases j using Fin.lastCases with
      | last => rfl
      | cast j =>
        have hj := (u j).isLt
        have hc := c.isLt
        simp only [boxTuple,separatedOffsets,Fin.snoc_last,Fin.snoc_castSucc,Nat.cast_one,Nat.cast_add] at hij
        omega
    | cast i =>
      cases j using Fin.lastCases with
      | last =>
        have hi := (u i).isLt
        have hc := c.isLt
        simp only [boxTuple,separatedOffsets,Fin.snoc_last,Fin.snoc_castSucc,Nat.cast_one,Nat.cast_add] at hij
        omega
      | cast j =>
        congr 1
        apply hu
        simpa [boxTuple,separatedOffsets] using hij

noncomputable def separatedBoxEquiv (s h : ℕ) :
    ({u // u∈distinctBox (s:=s) (h:=h) (fun _ => ((h+1:ℕ):ℤ))} × Fin h) ≃
    {u // u∈distinctBox (s:=s+1) (h:=h) (fun j => (separatedOffsets s h j:ℤ))} where
  toFun t := ⟨Fin.snoc t.1.1 t.2,(separatedBox_mem t.1.1 t.2).mpr t.1.2⟩
  invFun v := (⟨Fin.init v.1,by
      have hv : Fin.snoc (Fin.init v.1) (v.1 (Fin.last s))=v.1 := Fin.snoc_init_self v.1
      exact (separatedBox_mem _ _).mp (hv.symm ▸ v.2)⟩,v.1 (Fin.last s))
  left_inv t := by
    apply Prod.ext
    · apply Subtype.ext
      funext i
      simp [Fin.init]
    · simp
  right_inv v := by
    apply Subtype.ext
    exact Fin.snoc_init_self v.1

theorem separated_double_sum {s h : ℕ} (F : (Fin (s+1) → Fin h) → ℂ) :
    (∑ u∈distinctBox (s:=s) (h:=h) (fun _ => ((h+1:ℕ):ℤ)),∑ c : Fin h,F (Fin.snoc u c))=
      ∑ v∈distinctBox (s:=s+1) (h:=h) (fun j => (separatedOffsets s h j:ℤ)),F v := by
  classical
  conv_lhs => rw [←Finset.sum_coe_sort]
  conv_rhs => rw [←Finset.sum_coe_sort]
  calc
    _ = ∑ t : {u // u∈distinctBox (s:=s) (h:=h) (fun _ => ((h+1:ℕ):ℤ))} × Fin h,
      F (Fin.snoc t.1.val t.2) := (Fintype.sum_prod_type _).symm
    _ = _ := Fintype.sum_equiv (separatedBoxEquiv s h) _ _ (fun _ => rfl)

theorem pattern_marked_sum_eq_box {n : ℕ} (r : Setoid (Fin n)) (h X : ℕ)
    (F : (Fin n → ℝ) → ℝ) :
    (∑ b∈patternClass (α:=Fin h) r,∑ c : Fin h,
      (average X (fun m => divisorSum X F m (fun i => h+1+(b i:ℕ))*theta (m+(1+(c:ℕ)))):ℂ)/(Real.log X:ℂ))=
    ∑ v∈distinctBox (s:=Fintype.card (Quotient r)+1) (h:=h)
      (fun j => (separatedOffsets (Fintype.card (Quotient r)) h j:ℤ)),
      (average X (fun m => divisorSum X F m
        (patternBoxShifts (patternLabels r) (fun j => separatedOffsets _ h j.castSucc)
          (fun j => v j.castSucc))*
        theta (m+(separatedOffsets (Fintype.card (Quotient r)) h (Fin.last (Fintype.card (Quotient r)))+(v (Fin.last _):ℕ)))):ℂ)/(Real.log X:ℂ) := by
  classical
  rw [←separated_double_sum]
  simp only [separatedOffsets,Fin.snoc_castSucc,Fin.snoc_last]
  conv_lhs => rw [←Finset.sum_coe_sort]
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Fintype.sum_equiv (patternTupleEquiv r h ((h+1:ℕ):ℤ))
  intro b
  have he := patternTupleEquiv_labels r h (h+1) b
  simp only [he]

theorem separatedOffsets_eventually {lam : ℝ} (hlam : 0<lam) (s : ℕ) :
    ∀ᶠ X : ℕ in atTop,∀ j,separatedOffsets s (blockLength lam X) j≤2*blockLength lam X := by
  filter_upwards [blockOffset_eventually hlam] with X hX j
  cases j using Fin.lastCases with
  | last => simp only [separatedOffsets,Fin.snoc_last]; omega
  | cast j => simpa only [separatedOffsets,Fin.snoc_castSucc] using hX

theorem marked_pattern_limit (hBV : BombieriVinogradov) {n : ℕ}
    {lam : ℝ} (hlam : 0<lam) (r : Setoid (Fin n))
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrhohalf : rho<1/2) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M) :
    Tendsto (fun X : ℕ => ∑ b∈patternClass (α:=Fin (blockLength lam X)) r,∑ c : Fin (blockLength lam X),
      (average X (fun m => divisorSum X F m (fun i => blockLength lam X+1+(b i:ℕ))*
        theta (m+(1+(c:ℕ)))):ℂ)/(Real.log X:ℂ)) atTop
      (𝓝 ((lam:ℂ)^(Fintype.card (Quotient r)+1)*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin n))
          (fun v => (F v.ofLp:ℂ)) hF hFs)
        (shiftFamily (fun i => (numericPattern r i:ℤ))))) := by
  have hh := marked_box_pattern_limit hBV hlam (patternLabels r) (patternLabels_surjective r)
    (fun X => separatedOffsets _ (blockLength lam X)) (separatedOffsets_eventually hlam _)
    F rho hrho hrhohalf hbudget hF hFs M hM hbound
  apply hh.congr'
  exact Eventually.of_forall fun X => (pattern_marked_sum_eq_box r _ X F).symm

noncomputable def orderedDetector (X h m : ℕ) : ℝ :=
  (∑ c : Fin h,theta (m+(1+(c:ℕ))))/Real.log X

theorem average_div (X : ℕ) (f : ℕ → ℝ) (a : ℝ) :
    average X (fun m => f m/a)=average X f/a := by
  simpa only [div_eq_mul_inv,mul_comm] using average_const_mul X a⁻¹ f

theorem markedBlock_average_expansion {n X h : ℕ}
    (F : (Fin n → ℝ) → ℝ) (k : Setoid (Fin n) → ℝ) :
    (average X (fun m => weightedBlock X h (h+1) F k m*orderedDetector X h m):ℂ)=
      ∑ b : Fin n → Fin h,(k (Setoid.ker b):ℂ)*∑ c : Fin h,
        (average X (fun m => divisorSum X F m (fun i => h+1+(b i:ℕ))*theta (m+(1+(c:ℕ)))):ℂ)/(Real.log X:ℂ) := by
  classical
  have he (m : ℕ) : weightedBlock X h (h+1) F k m*orderedDetector X h m=
      ∑ b : Fin n → Fin h,∑ c : Fin h,
        k (Setoid.ker b)*(divisorSum X F m (fun i => h+1+(b i:ℕ))*theta (m+(1+(c:ℕ))))/Real.log X := by
    unfold weightedBlock orderedDetector
    rw [←mul_div_assoc,Finset.sum_mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro c _
    rw [mul_assoc]
  simp only [he,average_finset_sum,average_div,average_const_mul,
    Complex.ofReal_sum,Complex.ofReal_div,Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Finset.mul_sum,mul_div_assoc]

theorem markedBlock_average_limit (hBV : BombieriVinogradov) {n : ℕ}
    {lam : ℝ} (hlam : 0<lam)
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrhohalf : rho<1/2) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (k : Setoid (Fin n) → ℝ) :
    Tendsto (fun X : ℕ => (average X (fun m =>
      weightedBlock X (blockLength lam X) (blockLength lam X+1) F k m*
        orderedDetector X (blockLength lam X) m):ℂ)) atTop
      (𝓝 (∑ r : Setoid (Fin n),(k r:ℂ)*((lam:ℂ)^(Fintype.card (Quotient r)+1)*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin n))
          (fun v => (F v.ofLp:ℂ)) (realEuclidean_compact F hF) (realEuclidean_smooth F hFs))
        (equalityPatternFamily r)))) := by
  classical
  obtain ⟨M,hM⟩ := hFs.continuous.bounded_above_of_compact_support hF
  have hh := tendsto_finsetSum Finset.univ (fun r _ =>
    (marked_pattern_limit hBV hlam r F rho hrho hrhohalf hbudget
      (realEuclidean_compact F hF) (realEuclidean_smooth F hFs) M
      ((norm_nonneg (F 0)).trans (hM 0)) (fun v _ => by simpa only [Real.norm_eq_abs] using hM v)).const_mul (k r:ℂ))
  apply hh.congr'
  exact Eventually.of_forall (fun X => by
    dsimp only
    rw [markedBlock_average_expansion]
    calc
      (∑ r : Setoid (Fin n), (k r:ℂ)*∑ b∈patternClass (α:=Fin (blockLength lam X)) r,
        ∑ c : Fin (blockLength lam X),
        (average X (fun m => divisorSum X F m (fun i => blockLength lam X+1+(b i:ℕ))*
          theta (m+(1+(c:ℕ)))):ℂ)/(Real.log X:ℂ)) =
        ∑ r : Setoid (Fin n),∑ b∈patternClass (α:=Fin (blockLength lam X)) r,
          (k (Setoid.ker b):ℂ)*∑ c : Fin (blockLength lam X),
            (average X (fun m => divisorSum X F m (fun i => blockLength lam X+1+(b i:ℕ))*
              theta (m+(1+(c:ℕ)))):ℂ)/(Real.log X:ℂ) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        rw [(mem_patternClass r b).mp hb]
      _ = _ := sum_patterns _
    apply Finset.sum_congr (by ext b; simp)
    intro b _
    rfl)

theorem marked_cumulative_pair_limit (hBV : BombieriVinogradov) {n p : ℕ} {tau lam : ℝ}
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsg : tsupport g⊆positiveSimplex p tau) :
    Tendsto (fun X : ℕ => (average X (fun m =>
      weightedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau f) (subsetCoefficient n) m*
      weightedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau g) (subsetCoefficient p) m*
      orderedDetector X (blockLength lam X) m):ℂ))
      atTop (𝓝 ((lam:ℂ)*∑ r : Setoid (Fin (n+p)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*cumulativePatternKernel (tau+tau) (tensorProfile f g)
          (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs) r))) := by
  have hh := markedBlock_average_limit hBV hlam
    (cumulativeProfile (tau+tau) (tensorProfile f g)) (tau+tau) (by positivity) (by linarith)
    (cumulativeProfile_budget _ _ (tensorProfile_tsupport f g hsf hsg))
    (cumulativeProfile_compact _ _ (tensorProfile_compact f g hf hg))
    (cumulativeProfile_smooth _ _ (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs))
    (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p))
  have he : (∑ r : Setoid (Fin (n+p)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^(Fintype.card (Quotient r)+1)*cumulativePatternKernel (tau+tau) (tensorProfile f g)
          (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs) r))=
      (lam:ℂ)*∑ r : Setoid (Fin (n+p)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*cumulativePatternKernel (tau+tau) (tensorProfile f g)
          (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs) r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [pow_succ]
    ring
  change Tendsto _ _ (𝓝 (∑ r : Setoid (Fin (n+p)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^(Fintype.card (Quotient r)+1)*cumulativePatternKernel (tau+tau) (tensorProfile f g)
          (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs) r))) at hh
  rw [he] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  congr 2
  funext m
  rw [weightedBlock_cumulative_mul hX _ _ m f g hsf hsg _ _]

theorem marked_cumulative_square_limit (hBV : BombieriVinogradov) {n : ℕ} {tau lam : ℝ}
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsym : SymmetricFunction f) :
    Tendsto (fun X : ℕ => average X (fun m =>
      weightedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau f) (subsetCoefficient n) m^2*
      orderedDetector X (blockLength lam X) m))
      atTop (𝓝 (lam*alpha lam n*l2Mass f)) := by
  have hh := marked_cumulative_pair_limit hBV htau htau2 hlam f f hf hf hfs hfs hsf hsf
  rw [cumulative_square_pattern_sum lam f hf hfs hsf hsym] at hh
  have hh' := Complex.continuous_re.continuousAt.tendsto.comp hh
  simpa [Function.comp_def,Complex.mul_re,←pow_two,mul_assoc] using hh'

theorem marked_cumulative_cross_limit (hBV : BombieriVinogradov) {n p : ℕ} (hnp : n≠p) {tau lam : ℝ}
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsg : tsupport g⊆positiveSimplex p tau) :
    Tendsto (fun X : ℕ => average X (fun m =>
      weightedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau f) (subsetCoefficient n) m*
      weightedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau g) (subsetCoefficient p) m*
      orderedDetector X (blockLength lam X) m))
      atTop (𝓝 0) := by
  have hh := marked_cumulative_pair_limit hBV htau htau2 hlam f g hf hg hfs hgs hsf hsg
  rw [cumulative_cross_pattern_sum hnp lam f g hf hg hfs hgs hsf hsg,mul_zero] at hh
  exact Complex.continuous_re.continuousAt.tendsto.comp hh

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_ProfileSymmetry

section File_OpenAIPrimeGaps_MarkedMoments

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem orderedWeight_marked_limit (hBV : BombieriVinogradov) {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam) :
    Tendsto (fun X : ℕ => average X (fun m => orderedWeight tau lam k f X m^2*
      orderedDetector X (blockLength lam X) m))
      atTop (𝓝 (lam*familyW lam k f)) := by
  classical
  let H := fun (j : Fin (k+1)) X m => weightedBlock X (blockLength lam X) (blockLength lam X+1)
       (cumulativeProfile tau (f j)) (subsetCoefficient j) m
  have hp (i j : Fin (k+1)) :
      Tendsto (fun X : ℕ => average X (fun m => H i X m*H j X m*orderedDetector X (blockLength lam X) m)) atTop
        (𝓝 (if i=j then lam*alpha lam i*l2Mass (f i) else 0)) := by
    have hfi := hf.2.1 i (by omega : (i:ℕ)≤k)
    have hfj := hf.2.1 j (by omega : (j:ℕ)≤k)
    by_cases hij : i=j
    · subst j
      simp only [↓reduceIte]
      simpa only [H,pow_two] using marked_cumulative_square_limit hBV htau htau2 hlam
        (f i) hfi.2.1 hfi.1 hfi.2.2.1 hfi.2.2.2
    · simp only [ite_eq_right hij]
      have hne : (i:ℕ)≠(j:ℕ) := fun h => hij (Fin.ext h)
      exact marked_cumulative_cross_limit hBV hne htau htau2 hlam
        (f i) (f j) hfi.2.1 hfj.2.1 hfi.1 hfj.1 hfi.2.2.1 hfj.2.2.1
  have hs := tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_finsetSum Finset.univ fun j _ => hp i j
  have he (X : ℕ) : average X (fun m => orderedWeight tau lam k f X m^2*orderedDetector X (blockLength lam X) m)=
      ∑ i : Fin (k+1),∑ j : Fin (k+1),average X (fun m => H i X m*H j X m*orderedDetector X (blockLength lam X) m) := by
    unfold orderedWeight
    simp only [pow_two,Finset.sum_mul,Finset.mul_sum,average_finset_sum]
    rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte] at hs
  have hv : (∑ i : Fin (k+1),lam*alpha lam i*l2Mass (f i))=lam*familyW lam k f := by
    simp only [mul_assoc,←Finset.mul_sum]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun j : ℕ => alpha lam j*l2Mass (f j)) (k+1)
  rw [hv] at hs
  exact hs.congr' (Eventually.of_forall fun X => (he X).symm)

theorem deleteCoordinate_smooth {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (deleteCoordinate f) := by
  let K := (fun v : Fin (n+1) → ℝ => -v (Fin.last n)) '' tsupport f
  have hK : IsCompact K := hf.isCompact.image (continuous_apply _ |>.neg)
  let g : (Fin n → ℝ) → ℝ → ℝ := fun t u => f (Fin.snoc t (-u))
  have hgs : ∀ t u,t∈(Set.univ : Set (Fin n → ℝ)) → u∉K → g t u=0 := by
    intro t u _ hu
    by_contra hn
    apply hu
    refine ⟨Fin.snoc t (-u),subset_tsupport f hn,?_⟩
    simp
  have hsm : ContDiff ℝ ∞ (fun p : (Fin n → ℝ) × ℝ => (Fin.snoc p.1 (-p.2) : Fin (n+1) → ℝ)) := by
    apply contDiff_pi.mpr
    intro i
    cases i using Fin.lastCases with
    | last => simpa using contDiff_snd.neg
    | cast i => simpa [Function.comp_def] using (contDiff_apply ℝ ℝ i).comp contDiff_fst
  have hh := MeasureTheory.contDiffOn_convolution_right_with_param
    (μ:=volume) (ContinuousLinearMap.mul ℝ ℝ) isOpen_univ hK hgs
    (f:=fun _ : ℝ => (1:ℝ)) (continuous_const.locallyIntegrable) (hfs.comp hsm).contDiffOn
  have hg : ContDiff ℝ ∞ (fun p : (Fin n → ℝ) × ℝ =>
      ((fun _ : ℝ => (1:ℝ)) ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] g p.1) p.2) := by
    rwa [Set.univ_prod_univ,contDiffOn_univ] at hh
  have H := hg.comp (contDiff_id.prodMk (contDiff_const (c:=(0:ℝ))))
  change ContDiff ℝ ∞ (fun x => ∫ t : ℝ, f (Fin.snoc x t))
  simpa only [Function.comp_def,convolution_def,ContinuousLinearMap.mul_apply',one_mul,
    zero_sub,g,neg_neg,deleteCoordinate,id_eq] using H

theorem deleteCoordinate_tsupport_subset {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : HasCompactSupport f) :
    tsupport (deleteCoordinate f) ⊆
      (fun v : Fin (n+1) → ℝ => fun i : Fin n => v i.castSucc) '' tsupport f := by
  have hk := hf.isCompact.image (continuous_pi (fun i : Fin n => continuous_apply i.castSucc))
  apply closure_minimal _ hk.isClosed
  intro t ht
  by_contra hn
  apply ht
  unfold deleteCoordinate
  apply integral_eq_zero_of_ae
  filter_upwards [] with u
  by_contra hfu
  exact hn ⟨Fin.snoc t u,subset_tsupport f hfu,by ext i; simp⟩

theorem deleteCoordinate_compact {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : HasCompactSupport f) : HasCompactSupport (deleteCoordinate f) := by
  exact (hf.isCompact.image (continuous_pi (fun i : Fin n => continuous_apply i.castSucc))).of_isClosed_subset
    (isClosed_tsupport _) (deleteCoordinate_tsupport_subset f hf)

theorem deleteCoordinate_interior_support {n : ℕ} {tau : ℝ}
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : HasCompactSupport f)
    (hs : tsupport f⊆positiveSimplex (n+1) tau) :
    tsupport (deleteCoordinate f) ⊆positiveSimplex n tau := by
  intro t ht
  obtain ⟨v,hv,rfl⟩ := deleteCoordinate_tsupport_subset f hf ht
  have hv' := hs hv
  refine ⟨fun i => hv'.1 i.castSucc,?_⟩
  have hh : coordinateSum v=coordinateSum (fun i : Fin n => v i.castSucc)+v (Fin.last n) := by
    exact Fin.sum_univ_castSucc (fun i => v i)
  have hp := hv'.1 (Fin.last n)
  linarith [hv'.2]

noncomputable def fixLastPerm {n : ℕ} (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr e (Equiv.refl (Fin 1))).trans finSumFinEquiv)

@[simp] theorem fixLastPerm_castSucc {n : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) :
    fixLastPerm e i.castSucc=(e i).castSucc := by
  change finSumFinEquiv ((Equiv.sumCongr e (Equiv.refl (Fin 1)))
    (finSumFinEquiv.symm (Fin.castAdd 1 i)))=Fin.castAdd 1 (e i)
  simp

@[simp] theorem fixLastPerm_last {n : ℕ} (e : Equiv.Perm (Fin n)) :
    fixLastPerm e (Fin.last n)=Fin.last n := by
  change finSumFinEquiv ((Equiv.sumCongr e (Equiv.refl (Fin 1)))
    (finSumFinEquiv.symm (Fin.natAdd n (0 : Fin 1))))=Fin.natAdd n (0 : Fin 1)
  simp

theorem deleteCoordinate_symmetric {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ)
    (hs : SymmetricFunction f) : SymmetricFunction (deleteCoordinate f) := by
  intro e t
  unfold deleteCoordinate
  apply integral_congr_ae
  filter_upwards [] with u
  have he : Fin.snoc (t ∘ e) u=(Fin.snoc t u : Fin (n+1) → ℝ) ∘ fixLastPerm e := by
    ext i
    cases i using Fin.lastCases <;> simp
  rw [he,hs]

theorem pi_restrict_Ici {n : ℕ} (v : Fin n → ℝ) :
    Measure.pi (fun i => volume.restrict (Ici (v i)))=volume.restrict (Ici v) := by
  rw [←Measure.restrict_pi_pi]
  congr 1
  ext x
  simp

theorem integral_Ici_snoc {n : ℕ} (v : Fin (n+1) → ℝ)
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : IntegrableOn f (Ici v)) :
    (∫ x in Ici v,f x)=∫ y in Ici (fun i : Fin n => v i.castSucc),
      ∫ a in Ici (v (Fin.last n)),f (Fin.snoc y a) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) (Fin.last n)
  have hm := measurePreserving_piFinSuccAbove
    (fun i : Fin (n+1) => volume.restrict (Ici (v i))) (Fin.last n)
  have he : ∀ p : ℝ × (Fin n → ℝ), e.symm p=Fin.snoc p.2 p.1 := by
    intro p
    simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]
  have hfi : Integrable f (Measure.pi (fun i => volume.restrict (Ici (v i)))) := by
    rw [pi_restrict_Ici]
    exact hf
  have hh := hm.symm.integral_comp' f
  have hi := (hm.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hfi
  dsimp only [e] at he
  simp only [Fin.succAbove_last_apply,he,Function.comp_def,pi_restrict_Ici] at hh hi
  rw [←hh]
  exact integral_prod_symm _ hi

theorem cumulativeProfile_delete_tail {n : ℕ} {tau : ℝ}
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : HasCompactSupport f)
    (hfs : ContDiff ℝ ∞ f) (hs : tsupport f⊆positiveSimplex (n+1) tau)
    (v : Fin n → ℝ) (hv : ∀ i,0≤v i) :
    cumulativeProfile tau f (Fin.snoc v 0)=cumulativeProfile tau (deleteCoordinate f) v := by
  have hs' := deleteCoordinate_interior_support f hf hs
  rw [cumulativeProfile_tail tau f hs,cumulativeProfile_tail tau _ hs' _ hv]
  · rw [integral_Ici_snoc _ _ (hfs.continuous.integrable_of_hasCompactSupport hf).integrableOn]
    simp only [Fin.snoc_castSucc,Fin.snoc_last]
    apply setIntegral_congr_fun measurableSet_Ici
    intro t _
    exact (deleteCoordinate_eq_orthant_integral (fun _ h => (hs (subset_tsupport f h)).1) t).symm
  · intro i
    cases i using Fin.lastCases <;> simp [hv]

noncomputable def deletedFamily (f : (j : ℕ) → (Fin j → ℝ) → ℝ)
    (j : ℕ) (t : Fin j → ℝ) : ℝ := f j t+deleteCoordinate (f (j+1)) t

theorem AdmissibleFamily.all_properties {tau : ℝ} {k : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f) (j : ℕ) :
    ContDiff ℝ ∞ (f j) ∧ HasCompactSupport (f j) ∧
    tsupport (f j)⊆positiveSimplex j tau ∧ SymmetricFunction (f j) := by
  by_cases hj : j≤k
  · exact hf.2.1 j hj
  · rw [hf.2.2 j (by omega)]
    refine ⟨contDiff_const,HasCompactSupport.zero,by simp,?_⟩
    intro e v
    rfl

theorem deletedFamily_admissible {tau : ℝ} {k : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f) :
    AdmissibleFamily tau k (deletedFamily f) := by
  refine ⟨hf.1,?_,?_⟩
  · intro j _
    obtain ⟨hjs,hjc,hjt,hjy⟩ := hf.all_properties j
    obtain ⟨hns,hnc,hnt,hny⟩ := hf.all_properties (j+1)
    refine ⟨hjs.add (deleteCoordinate_smooth _ hnc hns),
      hjc.add (deleteCoordinate_compact _ hnc),?_,?_⟩
    · exact (tsupport_add (f j) (deleteCoordinate (f (j+1)))).trans
        (Set.union_subset hjt (deleteCoordinate_interior_support _ hnc hnt))
    · intro e v
      exact congrArg₂ (·+·) (hjy e v) (deleteCoordinate_symmetric _ hny e v)
  · intro j hj
    have h1 := hf.2.2 j hj
    have h2 := hf.2.2 (j+1) (by omega)
    ext t
    simp [deletedFamily,h1,h2]

theorem cumulativeProfile_deletedFamily {tau : ℝ} {k : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f)
    (j : ℕ) (v : Fin j → ℝ) (hv : ∀ i,0≤v i) :
    cumulativeProfile tau (deletedFamily f j) v=
      cumulativeProfile tau (f j) v+cumulativeProfile tau (f (j+1)) (Fin.snoc v 0) := by
  obtain ⟨hjs,hjc,hjt,hjy⟩ := hf.all_properties j
  obtain ⟨hns,hnc,hnt,hny⟩ := hf.all_properties (j+1)
  have hg := (deletedFamily_admissible hf).all_properties j
  rw [cumulativeProfile_delete_tail _ hnc hns hnt v hv,
    cumulativeProfile_tail tau _ hg.2.2.1 _ hv,cumulativeProfile_tail tau _ hjt _ hv,
    cumulativeProfile_tail tau _ (deleteCoordinate_interior_support _ hnc hnt) _ hv]
  exact integral_add (hjs.continuous.integrable_of_hasCompactSupport hjc).integrableOn
    ((deleteCoordinate_smooth _ hnc hns).continuous.integrable_of_hasCompactSupport
      (deleteCoordinate_compact _ hnc)).integrableOn

theorem divisorSum_add {n : ℕ} (X M : ℕ) (F G : (Fin n → ℝ) → ℝ) (b : Fin n → ℕ) :
    divisorSum X (F+G) M b=divisorSum X F M b+divisorSum X G M b := by
  simp only [divisorSum,divisorCoefficient,Pi.add_apply,mul_add,Finset.sum_add_distrib]

theorem divisorSum_internal_family_delete {tau : ℝ} {k X M a : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f)
    (htau : tau<1) (hX : 2≤X) (hM : X<M+a) (hp : Nat.Prime (M+a))
    (j : ℕ) (b : Fin j → ℕ) :
    divisorSum X (cumulativeProfile tau (f j)) M b+
      divisorSum X (cumulativeProfile tau (f (j+1))) M (Fin.snoc b a)=
      divisorSum X (cumulativeProfile tau (deletedFamily f j)) M b := by
  have hn := hf.all_properties (j+1)
  rw [divisorSum_prime_delete hX hM hp _ htau (cumulativeProfile_budget tau _ hn.2.2.1)]
  rw [←divisorSum_add]
  apply divisorSum_congr_orthant hX
  intro v hv
  exact (cumulativeProfile_deletedFamily hf j v hv).symm

theorem orderedDetector_eq_detector (X h m : ℕ) :
    orderedDetector X h m=detector X (Finset.Ioc 0 h) m := by
  unfold orderedDetector detector
  congr 1
  have he : Finset.Ioc 0 h=Finset.Ico 1 (h+1) := by
    ext i
    simp only [Finset.mem_Ioc,Finset.mem_Ico]
    omega
  rw [he,Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_right]
  exact Fin.sum_univ_eq_sum_range (fun c : ℕ => theta (m+(1+c))) h

theorem unorderedWeight_external_marked_limit (hBV : BombieriVinogradov) {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam) :
    Tendsto (fun X : ℕ => average X (fun m => unorderedWeight tau lam k f X m^2*
      detector X (Finset.Ioc 0 (blockLength lam X)) m))
      atTop (𝓝 (lam*familyW lam k f)) := by
  apply (orderedWeight_marked_limit hBV f hf htau htau2 hlam).congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  simp only [orderedWeight_eq_unordered f hf hX,orderedDetector_eq_detector]

noncomputable def setDivisor (F : (j : ℕ) → (Fin j → ℝ) → ℝ)
    (X M h a : ℕ) (S : Finset (Fin h)) : ℝ :=
  divisorSum X (F S.card) M (fun i => a+(subsetEnumeration ⟨S,rfl⟩ i:ℕ))

theorem subsetEnumeration_range {h n : ℕ} (S : {S : Finset (Fin h) // S.card=n}) :
    Set.range (subsetEnumeration S)=(S.val : Set (Fin h)) := by
  ext x
  have hh := Finset.ext_iff.mp (subsetEnumeration_image S) x
  simpa only [Set.mem_range,Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_coe] using hh

theorem setDivisor_eq_enumeration {X M h a n : ℕ} (hX : 2≤X)
    (F : (j : ℕ) → (Fin j → ℝ) → ℝ)
    (hF : ∀ j (e : Equiv.Perm (Fin j)) v,(∀ i,0≤v i) → F j (v ∘ e)=F j v)
    (S : Finset (Fin h)) (hn : S.card=n) (b : Fin n → Fin h)
    (hb : Function.Injective b) (hr : Set.range b=(S:Set (Fin h))) :
    setDivisor F X M h a S=divisorSum X (F n) M (fun i => a+(b i:ℕ)) := by
  subst n
  obtain ⟨e,he⟩ := injective_same_range_perm (subsetEnumeration ⟨S,rfl⟩) b hb
    ((subsetEnumeration_range ⟨S,rfl⟩).trans hr.symm)
  rw [he]
  exact (divisorSum_perm_orthant hX (F S.card) (hF S.card) e
    (fun i => a+(subsetEnumeration ⟨S,rfl⟩ i:ℕ))).symm

theorem snoc_subsetEnumeration_injective {h : ℕ} (S : Finset (Fin h)) {c : Fin h} (hc : c∉S) :
    Function.Injective (Fin.snoc (subsetEnumeration ⟨S,rfl⟩) c) := by
  intro i j hij
  cases i using Fin.lastCases with
  | last =>
    cases j using Fin.lastCases with
    | last => rfl
    | cast j =>
      simp only [Fin.snoc_last,Fin.snoc_castSucc] at hij
      have hj : subsetEnumeration ⟨S,rfl⟩ j∈S := by
        have hh : subsetEnumeration ⟨S,rfl⟩ j∈Set.range (subsetEnumeration ⟨S,rfl⟩) := ⟨j,rfl⟩
        rwa [subsetEnumeration_range] at hh
      exact False.elim (hc (hij.symm ▸ hj))
  | cast i =>
    cases j using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last,Fin.snoc_castSucc] at hij
      have hi : subsetEnumeration ⟨S,rfl⟩ i∈S := by
        have hh : subsetEnumeration ⟨S,rfl⟩ i∈Set.range (subsetEnumeration ⟨S,rfl⟩) := ⟨i,rfl⟩
        rwa [subsetEnumeration_range] at hh
      exact False.elim (hc (hij ▸ hi))
    | cast j =>
      simp only [Fin.snoc_castSucc] at hij
      exact congrArg Fin.castSucc ((subsetEnumeration ⟨S,rfl⟩).injective hij)

theorem snoc_subsetEnumeration_range {h : ℕ} (S : Finset (Fin h)) (c : Fin h) :
    Set.range (Fin.snoc (subsetEnumeration ⟨S,rfl⟩) c)=↑(insert c S : Finset (Fin h)) := by
  ext x
  simp only [Set.mem_range,Finset.mem_coe,Finset.mem_insert]
  constructor
  · rintro ⟨i,rfl⟩
    cases i using Fin.lastCases with
    | last => simp
    | cast i =>
      right
      simp only [Fin.snoc_castSucc]
      have hh : subsetEnumeration ⟨S,rfl⟩ i∈Set.range (subsetEnumeration ⟨S,rfl⟩) := ⟨i,rfl⟩
      rwa [subsetEnumeration_range] at hh
  · rintro (rfl | hx)
    · exact ⟨Fin.last _,by simp⟩
    · have hx' : x∈Set.range (subsetEnumeration ⟨S,rfl⟩) := by rwa [subsetEnumeration_range]
      obtain ⟨i,rfl⟩ := hx'
      exact ⟨i.castSucc,by simp⟩

theorem setDivisor_insert_eq_snoc {X M h a : ℕ} (hX : 2≤X)
    (F : (j : ℕ) → (Fin j → ℝ) → ℝ)
    (hF : ∀ j (e : Equiv.Perm (Fin j)) v,(∀ i,0≤v i) → F j (v ∘ e)=F j v)
    (S : Finset (Fin h)) {c : Fin h} (hc : c∉S) :
    setDivisor F X M h a (insert c S)=
      divisorSum X (F (S.card+1)) M
        (Fin.snoc (fun i => a+(subsetEnumeration ⟨S,rfl⟩ i:ℕ)) (a+(c:ℕ))) := by
  rw [setDivisor_eq_enumeration hX F hF _ (Finset.card_insert_of_notMem hc)
    _ (snoc_subsetEnumeration_injective S hc) (snoc_subsetEnumeration_range S c)]
  congr 1
  funext i
  cases i using Fin.lastCases <;> simp

noncomputable def finiteSubsetWeight (tau : ℝ) (f : (j : ℕ) → (Fin j → ℝ) → ℝ)
    (X M h a : ℕ) (B : Finset (Fin h)) : ℝ :=
  ∑ S∈B.powerset,setDivisor (fun j => cumulativeProfile tau (f j)) X M h a S

theorem finiteSubsetWeight_prime_delete {tau : ℝ} {k X M h a : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f)
    (htau : tau<1) (hX : 2≤X) (c : Fin h) (hM : X<M+(a+(c:ℕ)))
    (hp : Nat.Prime (M+(a+(c:ℕ)))) :
    finiteSubsetWeight tau f X M h a Finset.univ=
      finiteSubsetWeight tau (deletedFamily f) X M h a (Finset.univ.erase c) := by
  classical
  have hsym : ∀ j (e : Equiv.Perm (Fin j)) v,(∀ i,0≤v i) →
      cumulativeProfile tau (f j) (v ∘ e)=cumulativeProfile tau (f j) v := by
    intro j
    have hj := hf.all_properties j
    exact cumulativeProfile_perm_orthant _ hj.2.2.1 hj.2.2.2
  have he : (Finset.univ : Finset (Fin h))=insert c (Finset.univ.erase c) := by simp
  unfold finiteSubsetWeight
  conv_lhs => rw [he,Finset.sum_powerset_insert (Finset.notMem_erase c Finset.univ),←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  have hc : c∉S := fun h => Finset.notMem_erase c Finset.univ ((Finset.mem_powerset.mp hS) h)
  rw [setDivisor_insert_eq_snoc hX _ hsym S hc]
  exact divisorSum_internal_family_delete hf htau hX hM hp S.card _

theorem setDivisor_fixed_card {X M h a n : ℕ}
    (F : (j : ℕ) → (Fin j → ℝ) → ℝ) (S : Finset (Fin h)) (hn : S.card=n) :
    setDivisor F X M h a S=
      divisorSum X (F n) M (fun i => a+(subsetEnumeration ⟨S,hn⟩ i:ℕ)) := by
  subst n
  rfl

theorem setDivisor_level_sum (X M h a n : ℕ)
    (F : (j : ℕ) → (Fin j → ℝ) → ℝ) :
    (∑ S ∈ Finset.powersetCard n (Finset.univ : Finset (Fin h)),setDivisor F X M h a S)=
      unorderedBlock X h a (F n) M := by
  classical
  rw [Finset.sum_subtype (p:=fun S : Finset (Fin h) => S.card=n)
    (Finset.powersetCard n Finset.univ) (by intro S; simp)]
  unfold unorderedBlock
  apply Finset.sum_congr rfl
  intro S _
  exact setDivisor_fixed_card F S.val S.property

@[simp] theorem cumulativeProfile_zero (tau : ℝ) (n : ℕ) :
    cumulativeProfile tau (0 : (Fin n → ℝ) → ℝ)=0 := by
  ext v
  simp [cumulativeProfile,cumulativeExtension,convolution_def]

@[simp] theorem divisorSum_zero (X M : ℕ) {n : ℕ} (b : Fin n → ℕ) :
    divisorSum X (0 : (Fin n → ℝ) → ℝ) M b=0 := by
  simp [divisorSum,divisorCoefficient]

@[simp] theorem unorderedBlock_zero (X h a M n : ℕ) :
    unorderedBlock X h a (0 : (Fin n → ℝ) → ℝ) M=0 := by
  simp [unorderedBlock]

theorem finiteSubsetWeight_eq_unordered_levels {tau : ℝ} {k X M h a : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f) (hk : k≤h) :
    finiteSubsetWeight tau f X M h a Finset.univ=
      ∑ j : Fin (k+1),unorderedBlock X h a (cumulativeProfile tau (f j)) M := by
  unfold finiteSubsetWeight
  rw [Finset.sum_powerset]
  simp only [Finset.card_univ,Fintype.card_fin,setDivisor_level_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => unorderedBlock X h a (cumulativeProfile tau (f j)) M) (k+1)]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega : k+1≤h+1))
  intro j _ hj
  have hjk : k<j := by simp only [Finset.mem_range,not_lt] at hj; omega
  rw [hf.2.2 j hjk,cumulativeProfile_zero,unorderedBlock_zero]

theorem unorderedWeight_eq_finiteSubsetWeight {tau lam : ℝ} {k X M : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f)
    (hk : k≤blockLength lam X) :
    unorderedWeight tau lam k f X M=
      finiteSubsetWeight tau f X M (blockLength lam X) (blockLength lam X+1) Finset.univ := by
  exact (finiteSubsetWeight_eq_unordered_levels hf hk).symm

noncomputable def restrictedUnorderedBlock {n : ℕ} (X h a : ℕ)
    (F : (Fin n → ℝ) → ℝ) (B : Finset (Fin h)) (m : ℕ) : ℝ :=
  ∑ S : {S : Finset (Fin h) // S.card=n},
    if S.val⊆B then divisorSum X F m (fun i => a+(subsetEnumeration S i:ℕ)) else 0

noncomputable def restrictedBlock {n : ℕ} (X h a : ℕ)
    (F : (Fin n → ℝ) → ℝ) (A : Setoid (Fin n) → ℝ) (B : Finset (Fin h)) (m : ℕ) : ℝ :=
  ∑ b : Fin n → Fin h,A (Setoid.ker b)*
    (if ∀ i,b i∈B then divisorSum X F m (fun i => a+(b i:ℕ)) else 0)

theorem enumeratePerm_subset_iff {h n : ℕ}
    (S : {S : Finset (Fin h) // S.card=n}) (e : Equiv.Perm (Fin n)) (B : Finset (Fin h)) :
    (∀ i,(enumeratePerm (S,e)).val i∈B) ↔ S.val⊆B := by
  constructor
  · intro hi x hx
    rw [←enumeratePerm_image (S,e)] at hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact hi i
  · intro hS i
    apply hS
    rw [←enumeratePerm_image (S,e)]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

theorem restrictedBlock_eq_unordered {n X h a m : ℕ} (hX : 2≤X)
    (F : (Fin n → ℝ) → ℝ) (B : Finset (Fin h))
    (hsym : ∀ (e : Equiv.Perm (Fin n)) v,(∀ i,0≤v i) → F (v ∘ e)=F v) :
    restrictedBlock X h a F (subsetCoefficient n) B m=restrictedUnorderedBlock X h a F B m := by
  classical
  unfold restrictedBlock
  have he : (∑ b : Fin n → Fin h,subsetCoefficient n (Setoid.ker b)*
      (if ∀ i,b i∈B then divisorSum X F m (fun i => a+(b i:ℕ)) else 0))=
      ∑ b : {b : Fin n → Fin h // Function.Injective b},
        (n.factorial:ℝ)⁻¹*(if ∀ i,b.val i∈B then divisorSum X F m (fun i => a+(b.val i:ℕ)) else 0) := by
    simp only [subsetCoefficient,Setoid.ker_eq_bot_iff,ite_mul,zero_mul]
    rw [←Finset.sum_filter]
    exact Finset.sum_subtype (p:=fun b : Fin n → Fin h => Function.Injective b)
      (Finset.univ.filter fun b : Fin n → Fin h => Function.Injective b) (by simp) _
  rw [he]
  rw [←Fintype.sum_equiv (Equiv.ofBijective enumeratePerm (enumeratePerm_bijective h n))
    (fun t => (n.factorial:ℝ)⁻¹*(if ∀ i,(enumeratePerm t).val i∈B then
      divisorSum X F m (fun i => a+((enumeratePerm t).val i:ℕ)) else 0)) _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  unfold restrictedUnorderedBlock
  apply Finset.sum_congr rfl
  intro S _
  have hd (e : Equiv.Perm (Fin n)) :
      divisorSum X F m (fun i => a+((enumeratePerm (S,e)).val i:ℕ))=
      divisorSum X F m (fun i => a+(subsetEnumeration S i:ℕ)) :=
    divisorSum_perm_orthant hX F hsym e (fun i => a+(subsetEnumeration S i:ℕ))
  simp only [hd,enumeratePerm_subset_iff,Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul]
  have hn : (n.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [←mul_assoc, mul_inv_cancel₀ hn,one_mul]

theorem setDivisor_subset_level_sum (X M h a n : ℕ)
    (F : (j : ℕ) → (Fin j → ℝ) → ℝ) (B : Finset (Fin h)) :
    (∑ S ∈ Finset.powersetCard n (Finset.univ : Finset (Fin h)),
      if S⊆B then setDivisor F X M h a S else 0)=
      restrictedUnorderedBlock X h a (F n) B M := by
  classical
  rw [Finset.sum_subtype (p:=fun S : Finset (Fin h) => S.card=n)
    (Finset.powersetCard n Finset.univ) (by intro S; simp)]
  unfold restrictedUnorderedBlock
  apply Finset.sum_congr rfl
  intro S _
  rw [setDivisor_fixed_card F S.val S.property]

@[simp] theorem restrictedUnorderedBlock_zero (X h a M n : ℕ) (B : Finset (Fin h)) :
    restrictedUnorderedBlock X h a (0 : (Fin n → ℝ) → ℝ) B M=0 := by
  simp [restrictedUnorderedBlock]

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_MarkedMoments

section File_OpenAIPrimeGaps_RestrictedWeights

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem finiteSubsetWeight_eq_restricted_levels {tau : ℝ} {k X M h a : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f) (hk : k≤h)
    (B : Finset (Fin h)) :
    finiteSubsetWeight tau f X M h a B=
      ∑ j : Fin (k+1),restrictedUnorderedBlock X h a (cumulativeProfile tau (f j)) B M := by
  classical
  unfold finiteSubsetWeight
  have he : B.powerset=(Finset.univ.powerset : Finset (Finset (Fin h))).filter (fun S => S⊆B) := by
    ext S
    simp
  rw [he,Finset.sum_filter,Finset.sum_powerset]
  simp only [Finset.card_univ,Fintype.card_fin,setDivisor_subset_level_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => restrictedUnorderedBlock X h a (cumulativeProfile tau (f j)) B M) (k+1)]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega : k+1≤h+1))
  intro j _ hj
  have hjk : k<j := by simp only [Finset.mem_range,not_lt] at hj; omega
  rw [hf.2.2 j hjk,cumulativeProfile_zero,restrictedUnorderedBlock_zero]

noncomputable def restrictedWeight (tau lam : ℝ) (k : ℕ)
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (X m : ℕ) (c : Fin (blockLength lam X)) : ℝ :=
  ∑ j : Fin (k+1),restrictedBlock X (blockLength lam X) (blockLength lam X+1)
    (cumulativeProfile tau (f j)) (subsetCoefficient j) (Finset.univ.erase c) m

theorem restrictedWeight_eq_finiteSubsetWeight {tau lam : ℝ} {k X m : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f)
    (hX : 2≤X) (hk : k≤blockLength lam X) (c : Fin (blockLength lam X)) :
    restrictedWeight tau lam k f X m c=
      finiteSubsetWeight tau f X m (blockLength lam X) (blockLength lam X+1) (Finset.univ.erase c) := by
  rw [finiteSubsetWeight_eq_restricted_levels hf hk]
  unfold restrictedWeight
  apply Finset.sum_congr rfl
  intro j _
  have hj := hf.all_properties j
  exact restrictedBlock_eq_unordered hX _ _ (cumulativeProfile_perm_orthant _ hj.2.2.1 hj.2.2.2)

theorem unorderedWeight_prime_delete {tau lam : ℝ} {k X m : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f)
    (htau : tau<1) (hX : 2≤X) (hk : k≤blockLength lam X) (hm : X < m)
    (c : Fin (blockLength lam X)) (hp : Nat.Prime (m+(blockLength lam X+1+(c:ℕ)))) :
    unorderedWeight tau lam k f X m=restrictedWeight tau lam k (deletedFamily f) X m c := by
  rw [unorderedWeight_eq_finiteSubsetWeight hf hk,
    restrictedWeight_eq_finiteSubsetWeight (deletedFamily_admissible hf) hX hk]
  exact finiteSubsetWeight_prime_delete hf htau hX c (by omega) hp

theorem coincident_double_sum {s h : ℕ} (a : ℤ) (F : (Fin (s+1) → Fin h) → ℂ) :
    (∑ u∈distinctBox (s:=s) (h:=h) (fun _ => a),∑ c : Fin h,
       if ∀ j,u j≠c then F (Fin.snoc u c) else 0)=
      ∑ v∈distinctBox (s:=s+1) (h:=h) (fun _ => a),F v := by
  classical
  simp only [distinctBox,Finset.sum_filter,constant_boxTuple_injective_iff]
  have he (u : Fin s → Fin h) :
      (if Function.Injective u then ∑ c : Fin h,if ∀ j,u j≠c then F (Fin.snoc u c) else 0 else 0)=
        ∑ c : Fin h,if Function.Injective u ∧ c∉Set.range u then F (Fin.snoc u c) else 0 := by
    by_cases hu : Function.Injective u <;> simp [hu,Set.mem_range]
  simp only [he]
  rw [Finset.sum_comm]
  calc
    _ = ∑ t : Fin h × (Fin s → Fin h),
        if Function.Injective t.2 ∧ t.1∉Set.range t.2 then F (Fin.snoc t.2 t.1) else 0 :=
      (Fintype.sum_prod_type _).symm
    _ = _ := by
      apply Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (s+1) => Fin h))
      intro t
      change (if Function.Injective t.2 ∧ t.1∉Set.range t.2 then F (Fin.snoc t.2 t.1) else 0)=
        (if Function.Injective (Fin.snoc t.2 t.1) then F (Fin.snoc t.2 t.1) else 0)
      exact if_congr Fin.snoc_injective_iff.symm rfl rfl

theorem patternTupleEquiv_avoid {n h : ℕ} (r : Setoid (Fin n)) (a : ℕ)
    (b : {b // b∈patternClass (α:=Fin h) r}) (c : Fin h) :
    (∀ i,b.val i≠c) ↔ ∀ j,(patternTupleEquiv r h a b).val j≠c := by
  constructor
  · intro hb j
    obtain ⟨i,hi⟩ := (patternLabels_surjective r) j
    have he := congrFun (patternTupleEquiv_labels r h a b) i
    simp only [patternBoxShifts,hi] at he
    have hv : (patternTupleEquiv r h a b).val j=b.val i := by
      apply Fin.ext
      omega
    simpa only [hv] using hb i
  · intro hb i
    have he := congrFun (patternTupleEquiv_labels r h a b) i
    simp only [patternBoxShifts] at he
    have hv : (patternTupleEquiv r h a b).val (patternLabels r i)=b.val i := by
      apply Fin.ext
      omega
    simpa only [hv] using hb (patternLabels r i)

theorem pattern_restricted_marked_sum_eq_box {n : ℕ} (r : Setoid (Fin n)) (h X : ℕ)
    (F : (Fin n → ℝ) → ℝ) :
    (∑ b∈patternClass (α:=Fin h) r,∑ c : Fin h,if ∀ i,b i≠c then
      (average X (fun m => divisorSum X F m (fun i => h+1+(b i:ℕ))*theta (m+(h+1+(c:ℕ)))):ℂ)/(Real.log X:ℂ)
      else 0)=
    ∑ v∈distinctBox (s:=Fintype.card (Quotient r)+1) (h:=h) (fun _ => ((h+1:ℕ):ℤ)),
      (average X (fun m => divisorSum X F m
        (patternBoxShifts (patternLabels r) (fun _ => h+1) (fun j => v j.castSucc))*
        theta (m+(h+1+(v (Fin.last _):ℕ)))):ℂ)/(Real.log X:ℂ) := by
  classical
  rw [←coincident_double_sum]
  simp only [Fin.snoc_castSucc,Fin.snoc_last]
  conv_lhs => rw [←Finset.sum_coe_sort]
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Fintype.sum_equiv (patternTupleEquiv r h ((h+1:ℕ):ℤ))
  intro b
  rw [patternTupleEquiv_labels r h (h+1) b]
  apply Finset.sum_congr rfl
  intro c _
  simp only [←patternTupleEquiv_avoid r (h+1) b c]

theorem restricted_marked_pattern_limit (hBV : BombieriVinogradov) {n : ℕ}
    {lam : ℝ} (hlam : 0<lam) (r : Setoid (Fin n))
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrhohalf : rho<1/2) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M) :
    Tendsto (fun X : ℕ => ∑ b∈patternClass (α:=Fin (blockLength lam X)) r,∑ c : Fin (blockLength lam X),
      if ∀ i,b i≠c then (average X (fun m => divisorSum X F m (fun i => blockLength lam X+1+(b i:ℕ))*
        theta (m+(blockLength lam X+1+(c:ℕ)))):ℂ)/(Real.log X:ℂ) else 0) atTop
      (𝓝 ((lam:ℂ)^(Fintype.card (Quotient r)+1)*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin n))
          (fun v => (F v.ofLp:ℂ)) hF hFs)
        (shiftFamily (fun i => (numericPattern r i:ℤ))))) := by
  have ha : ∀ᶠ X : ℕ in atTop,∀ _j : Fin (Fintype.card (Quotient r)+1),
      blockLength lam X+1≤2*blockLength lam X := by
    filter_upwards [blockOffset_eventually hlam] with X hX j
    exact hX
  have hh := marked_box_pattern_limit hBV hlam (patternLabels r) (patternLabels_surjective r)
    (fun X _ => blockLength lam X+1) ha F rho hrho hrhohalf hbudget hF hFs M hM hbound
  apply hh.congr'
  exact Eventually.of_forall fun X => (pattern_restricted_marked_sum_eq_box r _ X F).symm

noncomputable def internalMarked (X h : ℕ) (H : ℕ → Fin h → ℝ) : ℝ :=
  average X (fun m => ∑ c : Fin h,H m c*theta (m+(h+1+(c:ℕ)))/Real.log X)

theorem restrictedBlock_marked_expansion {n X h : ℕ}
    (F : (Fin n → ℝ) → ℝ) (k : Setoid (Fin n) → ℝ) :
    (internalMarked X h (fun m c => restrictedBlock X h (h+1) F k (Finset.univ.erase c) m):ℂ)=
      ∑ b : Fin n → Fin h,(k (Setoid.ker b):ℂ)*∑ c : Fin h,if ∀ i,b i≠c then
        (average X (fun m => divisorSum X F m (fun i => h+1+(b i:ℕ))*theta (m+(h+1+(c:ℕ)))):ℂ)/(Real.log X:ℂ)
        else 0 := by
  classical
  unfold internalMarked restrictedBlock
  simp only [Finset.mem_erase,Finset.mem_univ,and_true,Finset.sum_mul,Finset.sum_div,
    average_finset_sum,Complex.ofReal_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hb : ∀ i,b i≠c
  · simp only [ite_eq_left hb]
    simp only [←mul_div_assoc,average_div]
    simp only [mul_assoc,average_const_mul,Complex.ofReal_div,Complex.ofReal_mul]
  · simp only [ite_eq_right hb,mul_zero,zero_mul,zero_div]
    simp [average]

theorem restrictedBlock_marked_limit (hBV : BombieriVinogradov) {n : ℕ}
    {lam : ℝ} (hlam : 0<lam)
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrhohalf : rho<1/2) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (k : Setoid (Fin n) → ℝ) :
    Tendsto (fun X : ℕ => (internalMarked X (blockLength lam X) (fun m c =>
      restrictedBlock X (blockLength lam X) (blockLength lam X+1) F k (Finset.univ.erase c) m):ℂ)) atTop
      (𝓝 (∑ r : Setoid (Fin n),(k r:ℂ)*((lam:ℂ)^(Fintype.card (Quotient r)+1)*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin n))
          (fun v => (F v.ofLp:ℂ)) (realEuclidean_compact F hF) (realEuclidean_smooth F hFs))
        (equalityPatternFamily r)))) := by
  classical
  obtain ⟨M,hM⟩ := hFs.continuous.bounded_above_of_compact_support hF
  have hh := tendsto_finsetSum Finset.univ (fun r _ =>
    (restricted_marked_pattern_limit hBV hlam r F rho hrho hrhohalf hbudget
      (realEuclidean_compact F hF) (realEuclidean_smooth F hFs) M
      ((norm_nonneg (F 0)).trans (hM 0)) (fun v _ => by simpa only [Real.norm_eq_abs] using hM v)).const_mul (k r:ℂ))
  apply hh.congr'
  exact Eventually.of_forall (fun X => by
    dsimp only
    rw [restrictedBlock_marked_expansion]
    calc
      (∑ r : Setoid (Fin n), (k r:ℂ)*∑ b∈patternClass (α:=Fin (blockLength lam X)) r,
        ∑ c : Fin (blockLength lam X),if ∀ i,b i≠c then
        (average X (fun m => divisorSum X F m (fun i => blockLength lam X+1+(b i:ℕ))*
          theta (m+(blockLength lam X+1+(c:ℕ)))):ℂ)/(Real.log X:ℂ) else 0) =
        ∑ r : Setoid (Fin n),∑ b∈patternClass (α:=Fin (blockLength lam X)) r,
          (k (Setoid.ker b):ℂ)*∑ c : Fin (blockLength lam X),if ∀ i,b i≠c then
            (average X (fun m => divisorSum X F m (fun i => blockLength lam X+1+(b i:ℕ))*
              theta (m+(blockLength lam X+1+(c:ℕ)))):ℂ)/(Real.log X:ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        rw [(mem_patternClass r b).mp hb]
      _ = _ := sum_patterns _
    apply Finset.sum_congr (by ext b; simp)
    intro b _
    rfl)

theorem restrictedBlock_mul {n p : ℕ} (X h a m : ℕ)
    (F : (Fin n → ℝ) → ℝ) (G : (Fin p → ℝ) → ℝ)
    (k : Setoid (Fin n) → ℝ) (l : Setoid (Fin p) → ℝ) (B : Finset (Fin h)) :
    restrictedBlock X h a F k B m*restrictedBlock X h a G l B m=
      restrictedBlock X h a (tensorProfile F G) (tensorCoefficient k l) B m := by
  classical
  unfold restrictedBlock
  rw [Finset.sum_mul_sum,←Finset.sum_product']
  apply Finset.sum_equiv (Fin.appendEquiv n p)
  · intro bc; simp
  intro bc _
  rw [show (Fin.appendEquiv n p) bc=Fin.append bc.1 bc.2 from rfl]
  simp only [tensorCoefficient,append_ker_left,append_ker_right]
  have he : (fun i => a+((Fin.append bc.1 bc.2 i :Fin h):ℕ))=
      Fin.append (fun i => a+(bc.1 i:ℕ)) (fun i => a+(bc.2 i:ℕ)) := by
    funext i
    cases i using Fin.addCases <;> simp
  rw [he,divisorSum_tensor]
  have hc : (∀ i,Fin.append bc.1 bc.2 i∈B) ↔ (∀ i,bc.1 i∈B) ∧ (∀ j,bc.2 j∈B) := by
    simp only [Fin.forall_fin_add,Fin.append_left,Fin.append_right]
  simp only [hc]
  split_ifs <;> simp_all
  all_goals ring

theorem restrictedBlock_congr_orthant {n X : ℕ} (hX : 2≤X) (h a m : ℕ)
    (F G : (Fin n → ℝ) → ℝ) (k : Setoid (Fin n) → ℝ) (B : Finset (Fin h))
    (hFG : ∀ v,(∀ i,0≤v i) → F v=G v) :
    restrictedBlock X h a F k B m=restrictedBlock X h a G k B m := by
  apply Finset.sum_congr rfl
  intro b _
  rw [divisorSum_congr_orthant hX m _ F G hFG]

theorem restrictedBlock_cumulative_mul {n p X : ℕ} (hX : 2≤X) (h a m : ℕ) {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : tsupport f⊆positiveSimplex n tau) (hg : tsupport g⊆positiveSimplex p tau)
    (k : Setoid (Fin n) → ℝ) (l : Setoid (Fin p) → ℝ) (B : Finset (Fin h)) :
    restrictedBlock X h a (cumulativeProfile tau f) k B m*
      restrictedBlock X h a (cumulativeProfile tau g) l B m=
    restrictedBlock X h a (cumulativeProfile (tau+tau) (tensorProfile f g)) (tensorCoefficient k l) B m := by
  rw [restrictedBlock_mul]
  apply restrictedBlock_congr_orthant hX
  intro v hv
  let v1 := fun i : Fin n => v (i.castAdd p)
  let v2 := fun i : Fin p => v (i.natAdd n)
  have he : v=Fin.append v1 v2 := by
    funext i
    cases i using Fin.addCases <;> simp [v1,v2]
  rw [he,tensorProfile_append]
  exact (cumulativeProfile_tensor f g hf hg v1 v2 (fun i => hv _) (fun i => hv _)).symm

theorem internalMarked_congr {X h : ℕ} {H G : ℕ → Fin h → ℝ}
    (he : ∀ m c,H m c=G m c) : internalMarked X h H=internalMarked X h G := by
  unfold internalMarked
  congr 1
  funext m
  exact Finset.sum_congr rfl fun c _ => by rw [he]

theorem internalMarked_finset_sum {α : Type*} (X h : ℕ) (S : Finset α)
    (H : α → ℕ → Fin h → ℝ) :
    internalMarked X h (fun m c => ∑ i∈S,H i m c)=∑ i∈S,internalMarked X h (H i) := by
  unfold internalMarked
  simp only [Finset.sum_mul,Finset.sum_div,average_finset_sum]
  rw [Finset.sum_comm]

theorem restricted_cumulative_pair_limit (hBV : BombieriVinogradov) {n p : ℕ} {tau lam : ℝ}
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsg : tsupport g⊆positiveSimplex p tau) :
    Tendsto (fun X : ℕ => (internalMarked X (blockLength lam X) (fun m c =>
      restrictedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau f) (subsetCoefficient n) (Finset.univ.erase c) m*
      restrictedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau g) (subsetCoefficient p) (Finset.univ.erase c) m):ℂ))
      atTop (𝓝 ((lam:ℂ)*∑ r : Setoid (Fin (n+p)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*cumulativePatternKernel (tau+tau) (tensorProfile f g)
          (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs) r))) := by
  have hh := restrictedBlock_marked_limit hBV hlam
    (cumulativeProfile (tau+tau) (tensorProfile f g)) (tau+tau) (by positivity) (by linarith)
    (cumulativeProfile_budget _ _ (tensorProfile_tsupport f g hsf hsg))
    (cumulativeProfile_compact _ _ (tensorProfile_compact f g hf hg))
    (cumulativeProfile_smooth _ _ (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs))
    (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p))
  have he : (∑ r : Setoid (Fin (n+p)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^(Fintype.card (Quotient r)+1)*cumulativePatternKernel (tau+tau) (tensorProfile f g)
          (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs) r))=
      (lam:ℂ)*∑ r : Setoid (Fin (n+p)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*cumulativePatternKernel (tau+tau) (tensorProfile f g)
          (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs) r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [pow_succ]
    ring
  change Tendsto _ _ (𝓝 (∑ r : Setoid (Fin (n+p)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^(Fintype.card (Quotient r)+1)*cumulativePatternKernel (tau+tau) (tensorProfile f g)
          (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs) r))) at hh
  rw [he] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  apply congrArg (fun z : ℝ => (z:ℂ))
  symm
  apply internalMarked_congr
  intro m c
  exact restrictedBlock_cumulative_mul hX _ _ m f g hsf hsg _ _ _

theorem restricted_cumulative_square_limit (hBV : BombieriVinogradov) {n : ℕ} {tau lam : ℝ}
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsym : SymmetricFunction f) :
    Tendsto (fun X : ℕ => internalMarked X (blockLength lam X) (fun m c =>
      restrictedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau f) (subsetCoefficient n) (Finset.univ.erase c) m^2))
      atTop (𝓝 (lam*alpha lam n*l2Mass f)) := by
  have hh := restricted_cumulative_pair_limit hBV htau htau2 hlam f f hf hf hfs hfs hsf hsf
  rw [cumulative_square_pattern_sum lam f hf hfs hsf hsym] at hh
  have hh' := Complex.continuous_re.continuousAt.tendsto.comp hh
  simpa [Function.comp_def,Complex.mul_re,←pow_two,mul_assoc] using hh'

theorem restricted_cumulative_cross_limit (hBV : BombieriVinogradov) {n p : ℕ} (hnp : n≠p) {tau lam : ℝ}
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsg : tsupport g⊆positiveSimplex p tau) :
    Tendsto (fun X : ℕ => internalMarked X (blockLength lam X) (fun m c =>
      restrictedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau f) (subsetCoefficient n) (Finset.univ.erase c) m*
      restrictedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau g) (subsetCoefficient p) (Finset.univ.erase c) m))
      atTop (𝓝 0) := by
  have hh := restricted_cumulative_pair_limit hBV htau htau2 hlam f g hf hg hfs hgs hsf hsg
  rw [cumulative_cross_pattern_sum hnp lam f g hf hg hfs hgs hsf hsg,mul_zero] at hh
  exact Complex.continuous_re.continuousAt.tendsto.comp hh

theorem restrictedWeight_marked_limit (hBV : BombieriVinogradov) {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam) :
    Tendsto (fun X : ℕ => internalMarked X (blockLength lam X) (fun m c => restrictedWeight tau lam k f X m c^2))
      atTop (𝓝 (lam*familyW lam k f)) := by
  classical
  let H := fun (j : Fin (k+1)) X m (c : Fin (blockLength lam X)) =>
    restrictedBlock X (blockLength lam X) (blockLength lam X+1)
      (cumulativeProfile tau (f j)) (subsetCoefficient j) (Finset.univ.erase c) m
  have hp (i j : Fin (k+1)) :
      Tendsto (fun X : ℕ => internalMarked X (blockLength lam X) (fun m c => H i X m c*H j X m c)) atTop
        (𝓝 (if i=j then lam*alpha lam i*l2Mass (f i) else 0)) := by
    have hfi := hf.2.1 i (by omega : (i:ℕ)≤k)
    have hfj := hf.2.1 j (by omega : (j:ℕ)≤k)
    by_cases hij : i=j
    · subst j
      simp only [↓reduceIte]
      simpa only [H,pow_two] using restricted_cumulative_square_limit hBV htau htau2 hlam
        (f i) hfi.2.1 hfi.1 hfi.2.2.1 hfi.2.2.2
    · simp only [ite_eq_right hij]
      have hne : (i:ℕ)≠(j:ℕ) := fun h => hij (Fin.ext h)
      exact restricted_cumulative_cross_limit hBV hne htau htau2 hlam
        (f i) (f j) hfi.2.1 hfj.2.1 hfi.1 hfj.1 hfi.2.2.1 hfj.2.2.1
  have hs := tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_finsetSum Finset.univ fun j _ => hp i j
  have he (X : ℕ) : internalMarked X (blockLength lam X) (fun m c => restrictedWeight tau lam k f X m c^2)=
      ∑ i : Fin (k+1),∑ j : Fin (k+1),internalMarked X (blockLength lam X) (fun m c => H i X m c*H j X m c) := by
    simp only [restrictedWeight,pow_two,Finset.sum_mul,Finset.mul_sum,internalMarked_finset_sum]
    rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte] at hs
  have hv : (∑ i : Fin (k+1),lam*alpha lam i*l2Mass (f i))=lam*familyW lam k f := by
    simp only [mul_assoc,←Finset.mul_sum]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun j : ℕ => alpha lam j*l2Mass (f j)) (k+1)
  rw [hv] at hs
  exact hs.congr' (Eventually.of_forall fun X => (he X).symm)

theorem detector_I_eq (X h m : ℕ) :
    detector X (Finset.Ioc h (2*h)) m=
      (∑ c : Fin h,theta (m+(h+1+(c:ℕ))))/Real.log X := by
  unfold detector
  congr 1
  have he : Finset.Ioc h (2*h)=Finset.Ico (h+1) (h+1+h) := by
    ext i
    simp only [Finset.mem_Ioc,Finset.mem_Ico]
    omega
  rw [he,Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  symm
  exact Fin.sum_univ_eq_sum_range (fun c : ℕ => theta (m+(h+1+c))) h

theorem unorderedWeight_internal_delete_average {tau lam : ℝ} {k X : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : tau<1) (hX : 2≤X) (hk : k≤blockLength lam X) :
    average X (fun m => unorderedWeight tau lam k f X m^2*
      detector X (Finset.Ioc (blockLength lam X) (2*blockLength lam X)) m)=
      internalMarked X (blockLength lam X) (fun m c => restrictedWeight tau lam k (deletedFamily f) X m c^2) := by
  classical
  unfold internalMarked average
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  simp only [detector_I_eq,←mul_div_assoc,Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hp : Nat.Prime (m+(blockLength lam X+1+(c:ℕ)))
  · rw [unorderedWeight_prime_delete hf htau hX hk (Finset.mem_Ioc.mp hm).1 c hp]
  · simp [theta,hp]

theorem unorderedWeight_internal_marked_limit (hBV : BombieriVinogradov) {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam) :
    Tendsto (fun X : ℕ => average X (fun m => unorderedWeight tau lam k f X m^2*
      detector X (Finset.Ioc (blockLength lam X) (2*blockLength lam X)) m))
      atTop (𝓝 (familyV lam k f)) := by
  have hh := restrictedWeight_marked_limit hBV (deletedFamily f) (deletedFamily_admissible hf)
    htau htau2 hlam
  change Tendsto _ _ (𝓝 (familyV lam k f)) at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2,(blockLength_tendsto hlam).eventually_ge_atTop k] with X hX hk
  exact (unorderedWeight_internal_delete_average f hf (by linarith) hX hk).symm

theorem cumulative_tensor_permuted_kernel_invariant {n : ℕ} (e : Equiv.Perm (Fin n)) {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ positiveSimplex n tau) (hsym : ∀ y, f (y ∘ e)=f y)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
      (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
      (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ))) :
    kernelConstant (sourceFourier (fourierCoordinateSum (Fin (n+n)))
      (fun v => (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ)) hF hFs)
      (fiberSubsetFamily (permutedLabels e) Finset.univ) = (l2Mass f:ℂ) := by
  rw [permuted_kernelConstant]
  have he : (∫ y, signedDirections (coordinateDirectionList (Fin (n+n)))
      (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
        (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ)) (rayVector (permutedRay e) y)
      ∂positiveOrthantMeasure (Fin n)) =
      ∫ y, (f y^2:ℂ) ∂positiveOrthantMeasure (Fin n) := by
    apply integral_congr_ae
    rw [positiveOrthantMeasure_eq_restrict]
    filter_upwards [ae_restrict_mem (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioi))] with y hy
    rw [cumulativeProfile_signed_full (tau+tau) (tensorProfile f f)
      (tensorProfile_compact f f hf hf) (tensorProfile_smooth f f hfs hfs)
      (tensorProfile_tsupport f f hsupp hsupp)]
    · rw [rayVector_permuted,tensorProfile_append,hsym,pow_two]
      simp only [Complex.ofReal_mul]
    · intro i
      rw [rayVector_permuted]
      cases i using Fin.addCases with
      | left i => simpa using (hy i (Set.mem_univ i)).le
      | right i => simpa using (hy (e i) (Set.mem_univ (e i))).le
  rw [he]
  simp_rw [←Complex.ofReal_pow]
  rw [integral_complex_ofReal,positiveOrthantMeasure_eq_restrict]
  congr 1
  unfold l2Mass
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hfz : f y=0 := by
    by_contra hne
    exact hy (fun i _ => (hsupp (subset_tsupport f hne)).1 i)
  simp [hfz]

theorem l2Mass_tensor {n d : ℕ} (f : (Fin n → ℝ) → ℝ) (g : (Fin d → ℝ) → ℝ) :
    l2Mass (tensorProfile f g)=l2Mass f*l2Mass g := by
  unfold l2Mass
  rw [←(appendMeasurableEquiv_measurePreserving n d).integral_comp
    (appendMeasurableEquiv n d).measurableEmbedding]
  simp only [appendMeasurableEquiv_apply,tensorProfile_append,mul_pow]
  rw [Measure.volume_eq_prod]
  exact integral_prod_mul (fun x => f x^2) (fun y => g y^2)

noncomputable def extendPerm {n : ℕ} (e : Equiv.Perm (Fin n)) (d : ℕ) : Equiv.Perm (Fin (n+d)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr e (Equiv.refl (Fin d))).trans finSumFinEquiv)

@[simp] theorem extendPerm_left {n d : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) :
    extendPerm e d (i.castAdd d)=(e i).castAdd d := by
  simp [extendPerm]

@[simp] theorem extendPerm_right {n d : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin d) :
    extendPerm e d (i.natAdd n)=i.natAdd n := by
  simp [extendPerm]

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_RestrictedWeights

section File_OpenAIPrimeGaps_PairedDetectors

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem tensorProfile_extendPerm {n d : ℕ} (e : Equiv.Perm (Fin n))
    (f : (Fin n → ℝ) → ℝ) (g : (Fin d → ℝ) → ℝ)
    (hf : ∀ y,f (y ∘ e)=f y) (v : Fin (n+d) → ℝ) :
    tensorProfile f g (v ∘ extendPerm e d)=tensorProfile f g v := by
  simp only [tensorProfile,Function.comp_apply,extendPerm_left,extendPerm_right]
  congr 1
  exact hf (fun i => v (i.castAdd d))

noncomputable def extendLabels {n : ℕ} {α : Type*} (a : Fin n → α) (d : ℕ) :
    Fin (n+d) → α ⊕ Fin d := Fin.append (Sum.inl ∘ a) Sum.inr

@[simp] theorem extendLabels_left {n d : ℕ} {α : Type*} (a : Fin n → α) (i : Fin n) :
    extendLabels a d (i.castAdd d)=Sum.inl (a i) := by simp [extendLabels]

@[simp] theorem extendLabels_right {n d : ℕ} {α : Type*} (a : Fin n → α) (i : Fin d) :
    extendLabels a d (i.natAdd n)=Sum.inr i := by simp [extendLabels]

theorem extendLabels_injective {n : ℕ} {α : Type*} (a : Fin n → α) (d : ℕ)
    (ha : Function.Injective a) : Function.Injective (extendLabels a d) := by
  intro i j h
  cases i using Fin.addCases <;> cases j using Fin.addCases <;>
    simp only [extendLabels_left,extendLabels_right,Sum.inl.injEq,Sum.inr.injEq,
      Sum.inl_ne_inr,Sum.inr_ne_inl] at h
  · exact congrArg (Fin.castAdd d) (ha h)
  · exact congrArg (Fin.natAdd n) h

theorem extendLabels_range_ne {n p : ℕ} {α : Type*} (a : Fin n → α) (b : Fin p → α)
    (d : ℕ) (hab : Set.range a≠Set.range b) :
    Set.range (extendLabels a d)≠Set.range (extendLabels b d) := by
  intro he
  apply hab
  ext x
  have hh : ∀ {n : ℕ} (a : Fin n → α), Sum.inl x∈Set.range (extendLabels a d) ↔ x∈Set.range a := by
    intro n a
    constructor
    · rintro ⟨i,hi⟩
      cases i using Fin.addCases with
      | left i => exact ⟨i,by simpa using hi⟩
      | right i => simp at hi
    · rintro ⟨i,rfl⟩; exact ⟨i.castAdd d,by simp⟩
  rw [←hh a,←hh b,he]

noncomputable def extraPairLabels {n p : ℕ} (r : Setoid (Fin (n+p))) (d : ℕ) :
    Fin ((n+d)+(p+d)) → ℕ ⊕ Fin d :=
  Fin.append (extendLabels (fun i : Fin n => numericPattern r (i.castAdd p)) d)
    (extendLabels (fun i : Fin p => numericPattern r (i.natAdd n)) d)

noncomputable def extraPairFamily {n p : ℕ} (r : Setoid (Fin (n+p))) (d : ℕ) :
    Finset (Finset (Fin ((n+d)+(p+d)))) := by
  classical
  exact fiberSubsetFamily (extraPairLabels r d) (Finset.univ.image (extraPairLabels r d))

theorem castAdd_ne_natAdd {n d : ℕ} (i : Fin n) (j : Fin d) : i.castAdd d≠j.natAdd n := by
  intro h
  have hh := congrArg Fin.val h
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hh
  have hi := i.isLt
  omega

theorem natAdd_ne_castAdd {n d : ℕ} (i : Fin d) (j : Fin n) : i.natAdd n≠j.castAdd d :=
  (castAdd_ne_natAdd j i).symm

theorem extraPairFamily_matched {n d : ℕ} (e : Equiv.Perm (Fin n)) :
    extraPairFamily (n:=n) (p:=n) (matchedPattern e) d=
      fiberSubsetFamily (permutedLabels (extendPerm e d)) Finset.univ := by
  classical
  have he := fiberSubsetFamily_image_eq_of_kernel (extraPairLabels (n:=n) (p:=n) (matchedPattern e) d)
    (permutedLabels (extendPerm e d))
  have hh : ∀ i j, extraPairLabels (n:=n) (p:=n) (matchedPattern e) d i=extraPairLabels (n:=n) (p:=n) (matchedPattern e) d j ↔
      permutedLabels (extendPerm e d) i=permutedLabels (extendPerm e d) j := by
    intro i j
    have hr (i j : Fin (n+n)) : numericPattern (matchedPattern e) i=numericPattern (matchedPattern e) j ↔
        permutedLabels e i=permutedLabels e j := by
      change (Setoid.ker (numericPattern (matchedPattern e))) i j ↔ _
      rw [numericPattern_ker]
      rfl
    cases i using Fin.addCases <;> cases j using Fin.addCases <;>
      simp only [extraPairLabels,Fin.append_left,Fin.append_right,permutedLabels] <;>
      rename_i i j <;> cases i using Fin.addCases <;> cases j using Fin.addCases <;>
      simp only [extendLabels_left,extendLabels_right,extendPerm_left,extendPerm_right,
        Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,Fin.castAdd_inj,Fin.natAdd_inj,
        hr,permutedLabels,Fin.append_left,Fin.append_right,Function.id_def,Equiv.apply_eq_iff_eq,
        castAdd_ne_natAdd,natAdd_ne_castAdd]
  have he' : extraPairFamily (matchedPattern e) d=
      fiberSubsetFamily (permutedLabels (extendPerm e d))
        (Finset.univ.image (permutedLabels (extendPerm e d))) := by
    ext S
    simpa only [extraPairFamily,mem_fiberSubsetFamily_image] using Finset.ext_iff.mp (he hh) S
  rw [he']
  congr 1
  ext i
  simp only [Finset.mem_image,Finset.mem_univ,true_and,iff_true]
  exact ⟨i.castAdd (n+d),by simp [permutedLabels]⟩

noncomputable def extraPairProfile {n p d : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin p → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ) :
    (Fin ((n+d)+(p+d)) → ℝ) → ℝ := tensorProfile (tensorProfile f w) (tensorProfile g w)

theorem extraPairProfile_compact {n p d : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin p → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) (hw : HasCompactSupport w) :
    HasCompactSupport (extraPairProfile f g w) :=
  tensorProfile_compact _ _ (tensorProfile_compact f w hf hw) (tensorProfile_compact g w hg hw)

theorem extraPairProfile_smooth {n p d : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin p → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (extraPairProfile f g w) :=
  tensorProfile_smooth _ _ (tensorProfile_smooth f w hf hw) (tensorProfile_smooth g w hg hw)

noncomputable def extraPairKernel {n p d : ℕ} (tau sigma : ℝ)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) (hw : HasCompactSupport w)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g) (hws : ContDiff ℝ ∞ w)
    (r : Setoid (Fin (n+p))) : ℂ :=
  kernelConstant (sourceFourier (fourierCoordinateSum (Fin ((n+d)+(p+d))))
    (fun v => (cumulativeProfile ((tau+sigma)+(tau+sigma)) (extraPairProfile f g w) v.ofLp:ℂ))
    (realEuclidean_compact _ (cumulativeProfile_compact _ _ (extraPairProfile_compact f g w hf hg hw)))
    (realEuclidean_smooth _ (cumulativeProfile_smooth _ _
      (extraPairProfile_compact f g w hf hg hw) (extraPairProfile_smooth f g w hfs hgs hws))))
      (extraPairFamily r d)

theorem extraPairKernel_unmatched {n p d : ℕ} {tau sigma : ℝ}
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) (hw : HasCompactSupport w)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g) (hws : ContDiff ℝ ∞ w)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsg : tsupport g⊆positiveSimplex p tau)
    (hsw : tsupport w⊆positiveSimplex d sigma)
    (r : Setoid (Fin (n+p)))
    (hl : Setoid.comap (Fin.castAdd p) r=⊥) (hr : Setoid.comap (Fin.natAdd n) r=⊥)
    (hne : Set.range (fun i : Fin n => numericPattern r (i.castAdd p))≠
      Set.range (fun i : Fin p => numericPattern r (i.natAdd n))) :
    extraPairKernel tau sigma f g w hf hg hw hfs hgs hws r=0 := by
  unfold extraPairKernel
  convert cumulative_tensor_unmatched_kernel_zero (tensorProfile f w) (tensorProfile g w)
    (tensorProfile_compact f w hf hw) (tensorProfile_compact g w hg hw)
    (tensorProfile_smooth f w hfs hws) (tensorProfile_smooth g w hgs hws)
    (tensorProfile_tsupport f w hsf hsw) (tensorProfile_tsupport g w hsg hsw)
    (extendLabels _ d) (extendLabels _ d)
    (extendLabels_injective _ d (numericPattern_left_injective r hl))
    (extendLabels_injective _ d (numericPattern_right_injective r hr))
    (extendLabels_range_ne _ _ d hne)
    (realEuclidean_compact _ (cumulativeProfile_compact _ _ (extraPairProfile_compact f g w hf hg hw)))
    (realEuclidean_smooth _ (cumulativeProfile_smooth _ _ (extraPairProfile_compact f g w hf hg hw)
      (extraPairProfile_smooth f g w hfs hgs hws))) using 1
  congr 2
  ext x
  simp only [extraPairFamily,extraPairLabels,mem_fiberSubsetFamily_image]

theorem extraPairKernel_matched {n d : ℕ} {tau sigma : ℝ}
    (f : (Fin n → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hw : HasCompactSupport w)
    (hfs : ContDiff ℝ ∞ f) (hws : ContDiff ℝ ∞ w)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsw : tsupport w⊆positiveSimplex d sigma)
    (hsym : SymmetricFunction f) (e : Equiv.Perm (Fin n)) :
    extraPairKernel tau sigma f f w hf hf hw hfs hfs hws (matchedPattern e)=
      (l2Mass f*l2Mass w:ℂ) := by
  unfold extraPairKernel
  rw [extraPairFamily_matched]
  have hh := cumulative_tensor_permuted_kernel_invariant (extendPerm e d) (tensorProfile f w)
    (tensorProfile_compact f w hf hw) (tensorProfile_smooth f w hfs hws)
    (tensorProfile_tsupport f w hsf hsw) (tensorProfile_extendPerm e f w (fun y => hsym e y))
    (realEuclidean_compact _ (cumulativeProfile_compact _ _ (extraPairProfile_compact f f w hf hf hw)))
    (realEuclidean_smooth _ (cumulativeProfile_smooth _ _ (extraPairProfile_compact f f w hf hf hw)
      (extraPairProfile_smooth f f w hfs hfs hws)))
  rw [l2Mass_tensor,Complex.ofReal_mul] at hh
  convert hh using 1
  rfl

noncomputable def splitOffsets (s d h : ℕ) : Fin (s+d) → ℕ :=
  Fin.append (fun _ => h+1) (fun _ => 1)

theorem splitBox_mem {s d h : ℕ} (u : Fin s → Fin h) (v : Fin d → Fin h) :
    Fin.append u v∈distinctBox (fun j => (splitOffsets s d h j:ℤ)) ↔
      u∈distinctBox (fun _ => ((h+1:ℕ):ℤ)) ∧ v∈distinctBox (fun _ => (1:ℤ)) := by
  classical
  simp only [distinctBox,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro hu
    constructor
    · intro i j hij
      have he : boxTuple (fun k => (splitOffsets s d h k:ℤ)) (Fin.append u v) (i.castAdd d)=
          boxTuple (fun k => (splitOffsets s d h k:ℤ)) (Fin.append u v) (j.castAdd d) := by
        simpa [boxTuple,splitOffsets] using hij
      exact Fin.castAdd_inj.mp (hu he)
    · intro i j hij
      have he : boxTuple (fun k => (splitOffsets s d h k:ℤ)) (Fin.append u v) (i.natAdd s)=
          boxTuple (fun k => (splitOffsets s d h k:ℤ)) (Fin.append u v) (j.natAdd s) := by
        simpa [boxTuple,splitOffsets] using hij
      have he' := congrArg Fin.val (hu he)
      simp only [Fin.val_natAdd] at he'
      exact Fin.ext (Nat.add_left_cancel he')
  · rintro ⟨hu,hv⟩ i j hij
    cases i using Fin.addCases with
    | left i =>
      cases j using Fin.addCases with
      | left j =>
        congr 1
        apply hu
        simpa [boxTuple,splitOffsets] using hij
      | right j =>
        have hi := (u i).isLt
        have hj := (v j).isLt
        simp only [boxTuple,splitOffsets,Fin.append_left,Fin.append_right,Nat.cast_add,Nat.cast_one] at hij
        omega
    | right i =>
      cases j using Fin.addCases with
      | left j =>
        have hi := (v i).isLt
        have hj := (u j).isLt
        simp only [boxTuple,splitOffsets,Fin.append_left,Fin.append_right,Nat.cast_add,Nat.cast_one] at hij
        omega
      | right j =>
        congr 1
        apply hv
        simpa [boxTuple,splitOffsets] using hij

noncomputable def splitBoxEquiv (s d h : ℕ) :
    ({u // u∈distinctBox (s:=s) (h:=h) (fun _ => ((h+1:ℕ):ℤ))} ×
      {v // v∈distinctBox (s:=d) (h:=h) (fun _ => (1:ℤ))}) ≃
    {u // u∈distinctBox (s:=s+d) (h:=h) (fun j => (splitOffsets s d h j:ℤ))} where
  toFun t := ⟨Fin.append t.1.1 t.2.1,(splitBox_mem t.1.1 t.2.1).mpr ⟨t.1.2,t.2.2⟩⟩
  invFun v := by
    let v1 := fun i : Fin s => v.1 (i.castAdd d)
    let v2 := fun i : Fin d => v.1 (i.natAdd s)
    have he : Fin.append v1 v2=v.1 := by
      funext i
      cases i using Fin.addCases <;> simp [v1,v2]
    have hv : v1∈distinctBox (fun _ => ((h+1:ℕ):ℤ)) ∧ v2∈distinctBox (fun _ => (1:ℤ)) :=
      (splitBox_mem v1 v2).mp (he.symm ▸ v.2)
    exact (⟨v1,hv.1⟩,⟨v2,hv.2⟩)
  left_inv t := by
    apply Prod.ext <;> apply Subtype.ext <;> funext i <;> simp
  right_inv v := by
    apply Subtype.ext
    funext i
    cases i using Fin.addCases <;> simp

theorem split_double_sum {s d h : ℕ} {K : Type*} [AddCommMonoid K]
    (F : (Fin (s+d) → Fin h) → K) :
    (∑ u∈distinctBox (s:=s) (h:=h) (fun _ => ((h+1:ℕ):ℤ)),
      ∑ v∈distinctBox (s:=d) (h:=h) (fun _ => (1:ℤ)),F (Fin.append u v))=
      ∑ w∈distinctBox (s:=s+d) (h:=h) (fun j => (splitOffsets s d h j:ℤ)),F w := by
  classical
  conv_lhs => rw [←Finset.sum_coe_sort]; arg 2; ext u; rw [←Finset.sum_coe_sort]
  conv_rhs => rw [←Finset.sum_coe_sort]
  calc
    _ = ∑ t : {u // u∈distinctBox (s:=s) (h:=h) (fun _ => ((h+1:ℕ):ℤ))} ×
      {v // v∈distinctBox (s:=d) (h:=h) (fun _ => (1:ℤ))},F (Fin.append t.1.val t.2.val) :=
        (Fintype.sum_prod_type _).symm
    _ = _ := Fintype.sum_equiv (splitBoxEquiv s d h) _ _ (fun _ => rfl)

theorem splitOffsets_eventually {lam : ℝ} (hlam : 0<lam) (s d : ℕ) :
    ∀ᶠ X : ℕ in atTop,∀ j,splitOffsets s d (blockLength lam X) j≤2*blockLength lam X := by
  filter_upwards [blockOffset_eventually hlam] with X hX j
  cases j using Fin.addCases with
  | left j => simpa only [splitOffsets,Fin.append_left] using hX
  | right j => simp only [splitOffsets,Fin.append_right]; omega

noncomputable def extraBoxLabels {n p : ℕ} (r : Setoid (Fin (n+p))) (d : ℕ) :
    Fin ((n+d)+(p+d)) → Fin (Fintype.card (Quotient r)+d) :=
  Fin.append
    (Fin.append (fun i : Fin n => (patternLabels r (i.castAdd p)).castAdd d) (Fin.natAdd _))
    (Fin.append (fun i : Fin p => (patternLabels r (i.natAdd n)).castAdd d) (Fin.natAdd _))

theorem extraBoxLabels_surjective {n p : ℕ} (r : Setoid (Fin (n+p))) (d : ℕ) :
    Function.Surjective (extraBoxLabels r d) := by
  intro i
  cases i using Fin.addCases with
  | left i =>
    obtain ⟨j,hj⟩ := patternLabels_surjective r i
    cases j using Fin.addCases with
    | left j => exact ⟨(j.castAdd d).castAdd (p+d),by simp [extraBoxLabels,hj]⟩
    | right j => exact ⟨(j.castAdd d).natAdd (n+d),by simp [extraBoxLabels,hj]⟩
  | right i => exact ⟨(i.natAdd n).castAdd (p+d),by simp [extraBoxLabels]⟩

noncomputable def extraShifts {n p d h : ℕ} (b : Fin (n+p) → Fin h) (c : Fin d → Fin h) :
    Fin ((n+d)+(p+d)) → ℕ :=
  Fin.append
    (Fin.append (fun i : Fin n => h+1+(b (i.castAdd p):ℕ)) (fun i => 1+(c i:ℕ)))
    (Fin.append (fun i : Fin p => h+1+(b (i.natAdd n):ℕ)) (fun i => 1+(c i:ℕ)))

theorem extraBoxShifts_eq {n p d h : ℕ} (r : Setoid (Fin (n+p)))
    (b : {b // b∈patternClass (α:=Fin h) r}) (c : Fin d → Fin h) :
    patternBoxShifts (extraBoxLabels r d) (splitOffsets _ d h)
      (Fin.append (patternTupleEquiv r h (h+1) b).val c)=extraShifts b.val c := by
  funext i
  have hb := patternTupleEquiv_labels r h (h+1) b
  cases i using Fin.addCases <;> rename_i i <;> cases i using Fin.addCases <;>
    simp only [extraBoxLabels,extraShifts,Fin.append_left,Fin.append_right,patternBoxShifts,
      splitOffsets,Fin.append_left,Fin.append_right]
  · exact congrFun hb _
  · exact congrFun hb _

theorem extra_pattern_sum_eq_box {n p d h X : ℕ} (r : Setoid (Fin (n+p)))
    (F : (Fin ((n+d)+(p+d)) → ℝ) → ℝ) :
    (∑ b∈patternClass (α:=Fin h) r,∑ c∈distinctBox (s:=d) (h:=h) (fun _ => (1:ℤ)),
      (average X (fun m => divisorSum X F m (extraShifts b c)):ℂ))=
    ∑ v∈distinctBox (s:=Fintype.card (Quotient r)+d) (h:=h)
      (fun j => (splitOffsets _ d h j:ℤ)),
      (average X (fun m => divisorSum X F m (patternBoxShifts (extraBoxLabels r d)
        (splitOffsets _ d h) v)):ℂ) := by
  classical
  rw [←split_double_sum]
  conv_lhs => rw [←Finset.sum_coe_sort]
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Fintype.sum_equiv (patternTupleEquiv r h ((h+1:ℕ):ℤ))
  intro b
  apply Finset.sum_congr rfl
  intro c _
  have he := extraBoxShifts_eq r b c
  convert congrArg (fun sh => (average X (fun m => divisorSum X F m sh):ℂ)) he.symm using 1
  norm_cast

theorem extra_square_pattern_sum {n d : ℕ} {tau sigma : ℝ} (lam : ℝ)
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsym : SymmetricFunction f)
    (w : (Fin d → ℝ) → ℝ) (hw : HasCompactSupport w) (hws : ContDiff ℝ ∞ w)
    (hsw : tsupport w⊆positiveSimplex d sigma) :
    (∑ r : Setoid (Fin (n+n)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient n) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*extraPairKernel tau sigma f f w hf hf hw hfs hfs hws r))=
      (alpha lam n*l2Mass f*l2Mass w:ℂ) := by
  classical
  let A := fun r : Setoid (Fin (n+n)) =>
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient n) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*extraPairKernel tau sigma f f w hf hf hw hfs hfs hws r)
  have hz : ∀ r,r∉Set.range (@matchedPattern n) → A r=0 := by
    intro r hr
    by_cases hl : Setoid.comap (Fin.castAdd n) r=⊥
    · by_cases hr' : Setoid.comap (Fin.natAdd n) r=⊥
      · have hne : Set.range (fun i : Fin n => numericPattern r (i.castAdd n))≠
            Set.range (fun i : Fin n => numericPattern r (i.natAdd n)) := by
          intro he
          obtain ⟨e,rfl⟩ := matching_pattern_eq r hl hr' he
          exact hr ⟨e,rfl⟩
        simp only [A,extraPairKernel_unmatched f f w hf hf hw hfs hfs hws hsf hsf hsw r hl hr' hne,mul_zero]
      · simp only [A,tensorCoefficient,subsetCoefficient,ite_eq_right hr',mul_zero,Complex.ofReal_zero,zero_mul]
    · simp only [A,tensorCoefficient,subsetCoefficient,ite_eq_right hl,zero_mul,Complex.ofReal_zero]
  have hv : ∀ e : Equiv.Perm (Fin n), A (matchedPattern e)=
      ((n.factorial:ℂ)⁻¹)^2*((lam:ℂ)^n*((l2Mass f:ℂ)*(l2Mass w:ℂ))) := by
    intro e
    simp only [A,tensorCoefficient,matchedPattern_left,matchedPattern_right,subsetCoefficient,
      ↓reduceIte,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_natCast,
      matchedPattern_quotient_card,extraPairKernel_matched f w hf hw hfs hws hsf hsw hsym e,Complex.ofReal_mul,pow_two]
  have hh := sum_matched_patterns _ A hz hv
  change (∑ r,A r)=_
  rw [hh]
  have hn : (n.factorial:ℂ)≠0 := by exact_mod_cast n.factorial_ne_zero
  simp only [alpha,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast]
  field_simp

theorem extra_cross_pattern_sum {m n d : ℕ} (hmn : m≠n) {tau sigma : ℝ} (lam : ℝ)
    (f : (Fin m → ℝ) → ℝ) (g : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex m tau) (hsg : tsupport g⊆positiveSimplex n tau)
    (w : (Fin d → ℝ) → ℝ) (hw : HasCompactSupport w) (hws : ContDiff ℝ ∞ w)
    (hsw : tsupport w⊆positiveSimplex d sigma) :
    (∑ r : Setoid (Fin (m+n)),
      (tensorCoefficient (subsetCoefficient m) (subsetCoefficient n) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*extraPairKernel tau sigma f g w hf hg hw hfs hgs hws r))=0 := by
  apply Finset.sum_eq_zero
  intro r _
  by_cases hl : Setoid.comap (Fin.castAdd n) r=⊥
  · by_cases hr : Setoid.comap (Fin.natAdd m) r=⊥
    · have hne : Set.range (fun i : Fin m => numericPattern r (i.castAdd n))≠
          Set.range (fun i : Fin n => numericPattern r (i.natAdd m)) := by
        intro he
        exact hmn (injective_ranges_card _ _ (numericPattern_left_injective r hl)
          (numericPattern_right_injective r hr) he)
      rw [extraPairKernel_unmatched f g w hf hg hw hfs hgs hws hsf hsg hsw r hl hr hne,mul_zero,mul_zero]
    · simp only [tensorCoefficient,subsetCoefficient,ite_eq_right hr,mul_zero,Complex.ofReal_zero,zero_mul]
  · simp only [tensorCoefficient,subsetCoefficient,ite_eq_right hl,zero_mul,Complex.ofReal_zero]

theorem extraBoxLabels_family {n p : ℕ} (r : Setoid (Fin (n+p))) (d : ℕ) :
    shiftFamily (fun i => ((extraBoxLabels r d i).val:ℤ))=extraPairFamily r d := by
  classical
  have he : ∀ i j, (extraBoxLabels r d i).val=(extraBoxLabels r d j).val ↔
      extraPairLabels r d i=extraPairLabels r d j := by
    intro i j
    rw [Fin.val_inj]
    cases i using Fin.addCases <;> cases j using Fin.addCases <;>
      simp only [extraPairLabels,extraBoxLabels,Fin.append_left,Fin.append_right] <;>
      rename_i i j <;> cases i using Fin.addCases <;> cases j using Fin.addCases <;>
      simp only [Fin.append_left,Fin.append_right,extendLabels_left,extendLabels_right,
        Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,Fin.castAdd_inj,Fin.natAdd_inj,
        castAdd_ne_natAdd,natAdd_ne_castAdd,numericPattern,patternLabels,Fin.val_inj]
  ext S
  simp only [shiftFamily,extraPairFamily,mem_fiberSubsetFamily_image,Int.natCast_inj,he]

theorem extra_pattern_limit {n p d : ℕ} {lam : ℝ} (hlam : 0<lam)
    (r : Setoid (Fin (n+p)))
    (F : (Fin ((n+(d+1))+(p+(d+1))) → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin ((n+(d+1))+(p+(d+1)))) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin ((n+(d+1))+(p+(d+1)))) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M) :
    Tendsto (fun X : ℕ => ∑ b∈patternClass (α:=Fin (blockLength lam X)) r,
      ∑ c∈distinctBox (s:=d+1) (h:=blockLength lam X) (fun _ => (1:ℤ)),
        (average X (fun m => divisorSum X F m (extraShifts b c)):ℂ)) atTop
      (𝓝 ((lam:ℂ)^(Fintype.card (Quotient r)+(d+1))*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin ((n+(d+1))+(p+(d+1)))))
          (fun v => (F v.ofLp:ℂ)) hF hFs) (extraPairFamily r (d+1)))) := by
  have hh := unmarked_box_pattern_limit hlam (extraBoxLabels r (d+1))
    (extraBoxLabels_surjective r (d+1)) (fun X => splitOffsets _ (d+1) (blockLength lam X))
    (splitOffsets_eventually hlam _ (d+1)) F rho hrho hrho1 hbudget hF hFs M hM hbound
  convert hh using 1
  · funext X
    exact extra_pattern_sum_eq_box r F
  · congr 3
    exact (extraBoxLabels_family (n:=n) (p:=p) r (d+1)).symm

noncomputable def extraAverage {d : ℕ} (X h : ℕ) (H : ℕ → ℝ)
    (W : (Fin d → ℝ) → ℝ) : ℝ :=
  average X (fun m => ∑ c∈distinctBox (s:=d) (h:=h) (fun _ => (1:ℤ)),
    H m * divisorSum X W m (fun i => 1+(c i:ℕ))^2)

theorem extraAverage_finset_sum {d : ℕ} {α : Type*} (X h : ℕ) (S : Finset α)
    (H : α → ℕ → ℝ) (W : (Fin d → ℝ) → ℝ) :
    extraAverage X h (fun m => ∑ i∈S,H i m) W=∑ i∈S,extraAverage X h (H i) W := by
  unfold extraAverage
  simp only [Finset.sum_mul,average_finset_sum]
  rw [Finset.sum_comm]

theorem extra_divisor_product {n p d X h : ℕ} {tau sigma : ℝ} (hX : 2≤X)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsg : tsupport g⊆positiveSimplex p tau)
    (hsw : tsupport w⊆positiveSimplex d sigma)
    (M : ℕ) (b : Fin (n+p) → Fin h) (c : Fin d → Fin h) :
    divisorSum X (cumulativeProfile ((tau+sigma)+(tau+sigma)) (extraPairProfile f g w)) M (extraShifts b c)=
      divisorSum X (cumulativeProfile tau f) M (fun i => h+1+(b (i.castAdd p):ℕ))*
      divisorSum X (cumulativeProfile tau g) M (fun i => h+1+(b (i.natAdd n):ℕ))*
      divisorSum X (cumulativeProfile sigma w) M (fun i => 1+(c i:ℕ))^2 := by
  unfold extraPairProfile extraShifts
  rw [divisorSum_cumulative_tensor _ _ (tensorProfile_tsupport f w hsf hsw)
    (tensorProfile_tsupport g w hsg hsw) hX,
    divisorSum_cumulative_tensor f w hsf hsw hX,
    divisorSum_cumulative_tensor g w hsg hsw hX]
  ring

theorem extra_block_expansion {n p d X : ℕ} {tau sigma : ℝ} (hX : 2≤X) (h : ℕ)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsg : tsupport g⊆positiveSimplex p tau)
    (hsw : tsupport w⊆positiveSimplex d sigma)
    (k : Setoid (Fin n) → ℝ) (l : Setoid (Fin p) → ℝ) :
    (extraAverage X h (fun m => weightedBlock X h (h+1) (cumulativeProfile tau f) k m*
      weightedBlock X h (h+1) (cumulativeProfile tau g) l m) (cumulativeProfile sigma w):ℂ)=
      ∑ b : Fin (n+p) → Fin h,(tensorCoefficient k l (Setoid.ker b):ℂ)*
        ∑ c∈distinctBox (s:=d) (h:=h) (fun _ => (1:ℤ)),
        (average X (fun m => divisorSum X (cumulativeProfile ((tau+sigma)+(tau+sigma))
          (extraPairProfile f g w)) m (extraShifts b c)):ℂ) := by
  have he (m : ℕ) (c : Fin d → Fin h) :
      weightedBlock X h (h+1) (cumulativeProfile tau f) k m*
      weightedBlock X h (h+1) (cumulativeProfile tau g) l m*
      divisorSum X (cumulativeProfile sigma w) m (fun i => 1+(c i:ℕ))^2=
      ∑ b : Fin (n+p) → Fin h,tensorCoefficient k l (Setoid.ker b)*
        divisorSum X (cumulativeProfile ((tau+sigma)+(tau+sigma)) (extraPairProfile f g w)) m (extraShifts b c) := by
    simp only [weightedBlock,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm,←Finset.sum_product']
    apply Finset.sum_equiv (Fin.appendEquiv n p)
    · intro bc; simp
    intro bc _
    rw [show (Fin.appendEquiv n p) bc=Fin.append bc.1 bc.2 from rfl,
      extra_divisor_product hX f g w hsf hsg hsw]
    simp only [tensorCoefficient,append_ker_left,append_ker_right,Fin.append_left,Fin.append_right]
    ring
  unfold extraAverage
  simp only [he,average_finset_sum,average_const_mul,Complex.ofReal_sum,Complex.ofReal_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]

theorem extra_labeled_limit {n p d : ℕ} {lam : ℝ} (hlam : 0<lam)
    (F : (Fin ((n+(d+1))+(p+(d+1))) → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin ((n+(d+1))+(p+(d+1)))) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin ((n+(d+1))+(p+(d+1)))) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M)
    (k : Setoid (Fin (n+p)) → ℝ) :
    Tendsto (fun X : ℕ => ∑ b : Fin (n+p) → Fin (blockLength lam X),(k (Setoid.ker b):ℂ)*
      ∑ c∈distinctBox (s:=d+1) (h:=blockLength lam X) (fun _ => (1:ℤ)),
        (average X (fun m => divisorSum X F m (extraShifts b c)):ℂ)) atTop
      (𝓝 (∑ r : Setoid (Fin (n+p)),(k r:ℂ)*((lam:ℂ)^(Fintype.card (Quotient r)+(d+1))*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin ((n+(d+1))+(p+(d+1)))))
          (fun v => (F v.ofLp:ℂ)) hF hFs) (extraPairFamily r (d+1))))) := by
  have hh := tendsto_finsetSum Finset.univ (fun r _ =>
    (extra_pattern_limit hlam r F rho hrho hrho1 hbudget hF hFs M hM hbound).const_mul (k r:ℂ))
  apply hh.congr'
  exact Eventually.of_forall fun X => by
    dsimp only
    calc
      (∑ r : Setoid (Fin (n+p)),(k r:ℂ)*∑ b∈patternClass (α:=Fin (blockLength lam X)) r,
        ∑ c∈distinctBox (s:=d+1) (h:=blockLength lam X) (fun _ => (1:ℤ)),
          (average X (fun m => divisorSum X F m (extraShifts b c)):ℂ)) =
        ∑ r : Setoid (Fin (n+p)),∑ b∈patternClass (α:=Fin (blockLength lam X)) r,
          (k (Setoid.ker b):ℂ)*∑ c∈distinctBox (s:=d+1) (h:=blockLength lam X) (fun _ => (1:ℤ)),
          (average X (fun m => divisorSum X F m (extraShifts b c)):ℂ) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        rw [(mem_patternClass r b).mp hb]
      _ = _ := sum_patterns _
    apply Finset.sum_congr (by ext b; simp)
    intro b _
    rfl

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_PairedDetectors

section File_OpenAIPrimeGaps_DetectorMoments

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem extra_cumulative_pair_limit {n p d : ℕ} {tau sigma lam : ℝ}
    (htau : 0≤tau) (hsigma : 0 ≤ sigma) (hbudget : 2*(tau+sigma)<1) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsg : tsupport g⊆positiveSimplex p tau)
    (w : (Fin (d+1) → ℝ) → ℝ) (hw : HasCompactSupport w) (hws : ContDiff ℝ ∞ w)
    (hsw : tsupport w⊆positiveSimplex (d+1) sigma) :
    Tendsto (fun X : ℕ => (extraAverage X (blockLength lam X) (fun m =>
      weightedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau f) (subsetCoefficient n) m*
      weightedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau g) (subsetCoefficient p) m)
      (cumulativeProfile sigma w):ℂ)) atTop
      (𝓝 ((lam:ℂ)^(d+1)*∑ r : Setoid (Fin (n+p)),
        (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*extraPairKernel tau sigma f g w hf hg hw hfs hgs hws r))) := by
  let P := extraPairProfile f g w
  have hPc : HasCompactSupport P := extraPairProfile_compact f g w hf hg hw
  have hPs : ContDiff ℝ ∞ P := extraPairProfile_smooth f g w hfs hgs hws
  have hPb : tsupport P⊆positiveSimplex _ ((tau+sigma)+(tau+sigma)) :=
    tensorProfile_tsupport _ _ (tensorProfile_tsupport f w hsf hsw) (tensorProfile_tsupport g w hsg hsw)
  let F := cumulativeProfile ((tau+sigma)+(tau+sigma)) P
  have hFc := cumulativeProfile_compact ((tau+sigma)+(tau+sigma)) P hPc
  have hFs := cumulativeProfile_smooth ((tau+sigma)+(tau+sigma)) P hPc hPs
  obtain ⟨M,hMb⟩ := hFs.continuous.bounded_above_of_compact_support hFc
  have hh := extra_labeled_limit (n:=n) (p:=p) (d:=d) hlam F ((tau+sigma)+(tau+sigma))
    (by positivity) (by linarith) (cumulativeProfile_budget _ P hPb)
    (realEuclidean_compact F hFc) (realEuclidean_smooth F hFs)
    (max 0 M) (le_max_left _ _) (fun v _ => by simpa only [Real.norm_eq_abs] using (hMb v).trans (le_max_right 0 M))
    (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p))
  have he : (∑ r : Setoid (Fin (n+p)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^(Fintype.card (Quotient r)+(d+1))*extraPairKernel tau sigma f g w hf hg hw hfs hgs hws r)) =
      (lam:ℂ)^(d+1)*∑ r : Setoid (Fin (n+p)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*extraPairKernel tau sigma f g w hf hg hw hfs hgs hws r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [pow_add]
    ring
  change Tendsto _ _ (𝓝 (∑ r : Setoid (Fin (n+p)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^(Fintype.card (Quotient r)+(d+1))*extraPairKernel tau sigma f g w hf hg hw hfs hgs hws r))) at hh
  rw [he] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  exact (extra_block_expansion hX _ f g w hsf hsg hsw _ _).symm

theorem extra_cumulative_square_limit {n d : ℕ} {tau sigma lam : ℝ}
    (htau : 0≤tau) (hsigma : 0 ≤ sigma) (hbudget : 2*(tau+sigma)<1) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsym : SymmetricFunction f)
    (w : (Fin (d+1) → ℝ) → ℝ) (hw : HasCompactSupport w) (hws : ContDiff ℝ ∞ w)
    (hsw : tsupport w⊆positiveSimplex (d+1) sigma) :
    Tendsto (fun X : ℕ => extraAverage X (blockLength lam X) (fun m =>
      weightedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau f) (subsetCoefficient n) m^2)
      (cumulativeProfile sigma w)) atTop
      (𝓝 (lam^(d+1)*alpha lam n*l2Mass f*l2Mass w)) := by
  have hh := extra_cumulative_pair_limit htau hsigma hbudget hlam f f hf hf hfs hfs hsf hsf w hw hws hsw
  rw [extra_square_pattern_sum lam f hf hfs hsf hsym w hw hws hsw] at hh
  have hh' := Complex.continuous_re.continuousAt.tendsto.comp hh
  simpa [Function.comp_def,←Complex.ofReal_pow,Complex.mul_re,←pow_two,mul_assoc] using hh'

theorem extra_cumulative_cross_limit {n p d : ℕ} (hnp : n≠p) {tau sigma lam : ℝ}
    (htau : 0≤tau) (hsigma : 0 ≤ sigma) (hbudget : 2*(tau+sigma)<1) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsg : tsupport g⊆positiveSimplex p tau)
    (w : (Fin (d+1) → ℝ) → ℝ) (hw : HasCompactSupport w) (hws : ContDiff ℝ ∞ w)
    (hsw : tsupport w⊆positiveSimplex (d+1) sigma) :
    Tendsto (fun X : ℕ => extraAverage X (blockLength lam X) (fun m =>
      weightedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau f) (subsetCoefficient n) m*
      weightedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau g) (subsetCoefficient p) m)
      (cumulativeProfile sigma w)) atTop (𝓝 0) := by
  have hh := extra_cumulative_pair_limit htau hsigma hbudget hlam f g hf hg hfs hgs hsf hsg w hw hws hsw
  rw [extra_cross_pattern_sum hnp lam f g hf hg hfs hgs hsf hsg w hw hws hsw,mul_zero] at hh
  exact Complex.continuous_re.continuousAt.tendsto.comp hh

theorem orderedWeight_extra_limit {tau sigma lam : ℝ} {k d : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (hsigma : 0 ≤ sigma) (hbudget : 2*(tau+sigma)<1) (hlam : 0<lam)
    (w : (Fin (d+1) → ℝ) → ℝ) (hw : HasCompactSupport w) (hws : ContDiff ℝ ∞ w)
    (hsw : tsupport w⊆positiveSimplex (d+1) sigma) :
    Tendsto (fun X : ℕ => extraAverage X (blockLength lam X) (fun m => orderedWeight tau lam k f X m^2)
      (cumulativeProfile sigma w)) atTop (𝓝 (lam^(d+1)*l2Mass w*familyW lam k f)) := by
  classical
  let H := fun (j : Fin (k+1)) X m => weightedBlock X (blockLength lam X) (blockLength lam X+1)
       (cumulativeProfile tau (f j)) (subsetCoefficient j) m
  have hp (i j : Fin (k+1)) :
      Tendsto (fun X : ℕ => extraAverage X (blockLength lam X) (fun m => H i X m*H j X m)
        (cumulativeProfile sigma w)) atTop
        (𝓝 (if i=j then lam^(d+1)*alpha lam i*l2Mass (f i)*l2Mass w else 0)) := by
    have hfi := hf.2.1 i (by omega : (i:ℕ)≤k)
    have hfj := hf.2.1 j (by omega : (j:ℕ)≤k)
    by_cases hij : i=j
    · subst j
      simp only [↓reduceIte]
      simpa only [H,pow_two] using extra_cumulative_square_limit htau hsigma hbudget hlam
        (f i) hfi.2.1 hfi.1 hfi.2.2.1 hfi.2.2.2 w hw hws hsw
    · simp only [ite_eq_right hij]
      have hne : (i:ℕ)≠(j:ℕ) := fun h => hij (Fin.ext h)
      exact extra_cumulative_cross_limit hne htau hsigma hbudget hlam
        (f i) (f j) hfi.2.1 hfj.2.1 hfi.1 hfj.1 hfi.2.2.1 hfj.2.2.1 w hw hws hsw
  have hs := tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_finsetSum Finset.univ fun j _ => hp i j
  have he (X : ℕ) : extraAverage X (blockLength lam X) (fun m => orderedWeight tau lam k f X m^2)
      (cumulativeProfile sigma w)=
      ∑ i : Fin (k+1),∑ j : Fin (k+1),extraAverage X (blockLength lam X) (fun m => H i X m*H j X m)
        (cumulativeProfile sigma w) := by
    unfold orderedWeight
    simp only [pow_two,Finset.sum_mul_sum,extraAverage_finset_sum]
    rfl
  simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte] at hs
  have hv : (∑ i : Fin (k+1),lam^(d+1)*alpha lam i*l2Mass (f i)*l2Mass w)=
      lam^(d+1)*l2Mass w*familyW lam k f := by
    have he : ∀ i : Fin (k+1),lam^(d+1)*alpha lam i*l2Mass (f i)*l2Mass w=
        (lam^(d+1)*l2Mass w)*(alpha lam i*l2Mass (f i)) := fun _ => by ring
    simp only [he,←Finset.mul_sum]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun j : ℕ => alpha lam j*l2Mass (f j)) (k+1)
  rw [hv] at hs
  exact hs.congr' (Eventually.of_forall fun X => (he X).symm)

theorem distinctBox_pair_iff {h : ℕ} (b : Fin 2 → Fin h) :
    b∈distinctBox (fun _ => (1:ℤ)) ↔ b 0≠b 1 := by
  simp only [distinctBox,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro hb he
    have hh : boxTuple (fun _ => (1:ℤ)) b 0=boxTuple (fun _ => (1:ℤ)) b 1 := by simp only [boxTuple,he]
    have hi := hb hh
    exact (by decide : (0:Fin 2)≠1) hi
  · intro hb i j hij
    have he : b i=b j := by
      apply Fin.ext
      exact_mod_cast (add_left_cancel (show (1:ℤ)+(b i:ℤ)=1+(b j:ℤ) from hij))
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (hb he)
    · exact False.elim (hb he.symm)
    · rfl

theorem sum_distinctBox_pair {h : ℕ} (F : Fin h → Fin h → ℝ) :
    (∑ v∈distinctBox (s:=2) (h:=h) (fun _ => (1:ℤ)),F (v 0) (v 1))=
      ∑ b : Fin h,∑ c : Fin h,if b≠c then F b c else 0 := by
  classical
  have he : distinctBox (s:=2) (h:=h) (fun _ => (1:ℤ))=Finset.univ.filter (fun b => b 0≠b 1) := by
    ext b
    simp only [distinctBox_pair_iff,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [he,Finset.sum_filter]
  calc
    _ = ∑ bc : Fin h × Fin h, if bc.1≠bc.2 then F bc.1 bc.2 else 0 :=
      Fintype.sum_equiv (finTwoArrowEquiv (Fin h)) _ _ (fun _ => rfl)
    _ = _ := Fintype.sum_prod_type _

theorem sum_first_interval (h : ℕ) (F : ℕ → ℝ) :
    (∑ b∈Finset.Ioc 0 h,F b)=∑ b : Fin h,F (1+b) := by
  have he : Finset.Ioc 0 h=Finset.Ico 1 (h+1) := by
    ext b
    simp only [Finset.mem_Ioc,Finset.mem_Ico]
    omega
  rw [he,Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel,Finset.sum_range]

theorem sum_first_offdiagonal (h : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ b∈Finset.Ioc 0 h,∑ c∈(Finset.Ioc 0 h).erase b,F b c)=
      ∑ b : Fin h,∑ c : Fin h,if b≠c then F (1+b) (1+c) else 0 := by
  classical
  have he (b : ℕ) : (∑ c∈(Finset.Ioc 0 h).erase b,F b c)=
      ∑ c∈Finset.Ioc 0 h,if b≠c then F b c else 0 := by
    rw [←Finset.filter_ne,Finset.sum_filter]
  simp_rw [he,sum_first_interval]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  simp only [ne_eq,Nat.add_left_cancel_iff,Fin.val_inj]

theorem extraAverage_pair_identity {tau : ℝ} {X : ℕ} (hX : 2≤X) (h : ℕ)
    (H : ℕ → ℝ) (g : (Fin 1 → ℝ) → ℝ)
    (hgs : tsupport g⊆positiveSimplex 1 tau) :
    extraAverage X h H (cumulativeProfile (tau+tau) (tensorProfile g g))=
      ∑ b∈Finset.Ioc 0 h,∑ c∈(Finset.Ioc 0 h).erase b,
        average X (fun m => H m*divisorSum X (cumulativeProfile tau g) m (fun _ => b)^2*
          divisorSum X (cumulativeProfile tau g) m (fun _ => c)^2) := by
  classical
  have hd (m : ℕ) (v : Fin 2 → Fin h) :
      divisorSum X (cumulativeProfile (tau+tau) (tensorProfile g g)) m (fun i => 1+(v i:ℕ))=
        divisorSum X (cumulativeProfile tau g) m (fun _ => 1+(v 0:ℕ))*
        divisorSum X (cumulativeProfile tau g) m (fun _ => 1+(v 1:ℕ)) := by
    convert divisorSum_cumulative_tensor g g hgs hgs hX m
      (fun _ => 1+(v 0:ℕ)) (fun _ => 1+(v 1:ℕ)) using 1
    congr 1
    funext i
    fin_cases i <;> rfl
  unfold extraAverage
  simp_rw [hd,mul_pow,←mul_assoc]
  rw [average_finset_sum]
  rw [sum_distinctBox_pair (fun b c : Fin h => average X (fun m =>
    H m*divisorSum X (cumulativeProfile tau g) m (fun _ => 1+(b:ℕ))^2*
      divisorSum X (cumulativeProfile tau g) m (fun _ => 1+(c:ℕ))^2)),
    sum_first_offdiagonal]

theorem unorderedWeight_extra_pair_limit {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (hbudget : 6*tau<1) (hlam : 0<lam)
    (g : (Fin 1 → ℝ) → ℝ) (hgc : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    (hgt : tsupport g⊆positiveSimplex 1 tau) :
    Tendsto (fun X : ℕ => extraAverage X (blockLength lam X)
      (fun m => unorderedWeight tau lam k f X m^2)
      (cumulativeProfile (tau+tau) (tensorProfile g g)))
      atTop (𝓝 (lam^2*l2Mass g^2*familyW lam k f)) := by
  have hh := orderedWeight_extra_limit f hf htau (by linarith : 0≤tau+tau)
    (by linarith : 2*(tau+(tau+tau))<1) hlam (d:=1) (tensorProfile g g)
    (tensorProfile_compact g g hgc hgc) (tensorProfile_smooth g g hgs hgs)
    (tensorProfile_tsupport g g hgt hgt)
  rw [l2Mass_tensor,←pow_two] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  simp only [orderedWeight_eq_unordered f hf hX]

theorem unorderedWeight_detector_bound (hBV : BombieriVinogradov) {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (hbudget : 6*tau<1) (hlam : 0<lam)
    (hw : 0<familyW lam k f)
    (g : (Fin 1 → ℝ) → ℝ) (hgc : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    (hgt : tsupport g⊆positiveSimplex 1 tau) (hg0 : cumulativeProfile tau g 0=1) :
    ∀ᶠ X : ℕ in atTop,
      average X (fun m => unorderedWeight tau lam k f X m^2*
        detector X (Finset.Ioc 0 (blockLength lam X)) m^2)≤
      (lam+lam^2*l2Mass g^2+1)*familyW lam k f := by
  let q := fun X : ℕ => Real.log (2*X+2*blockLength lam X)/Real.log X
  let Z := unorderedWeight tau lam k f
  let E := fun X : ℕ => extraAverage X (blockLength lam X) (fun m => Z X m^2)
    (cumulativeProfile (tau+tau) (tensorProfile g g))
  have hlim := ((detector_log_ratio_tendsto hlam.le).mul
    (unorderedWeight_external_marked_limit hBV f hf htau (by linarith) hlam)).add
    (((detector_log_ratio_tendsto hlam.le).pow 2).mul
      (unorderedWeight_extra_pair_limit f hf htau hbudget hlam g hgc hgs hgt))
  simp only [one_mul,one_pow] at hlim
  have hlim' : Tendsto (fun X : ℕ => q X*average X (fun m => Z X m^2*
      detector X (Finset.Ioc 0 (blockLength lam X)) m)+q X^2*E X)
      atTop (𝓝 ((lam+lam^2*l2Mass g^2)*familyW lam k f)) := by
    convert hlim using 1
    congr 1
    ring
  have hstrict : (lam+lam^2*l2Mass g^2)*familyW lam k f<
      (lam+lam^2*l2Mass g^2+1)*familyW lam k f := by nlinarith
  have hu := hlim'.eventually_lt_const hstrict
  filter_upwards [eventually_ge_atTop 2,hu] with X hX hU
  apply le_trans _ hU.le
  have hh := weighted_detector_square_majorant (X:=X) (Y:=2*X+2*blockLength lam X)
    hX (by omega) (Finset.Ioc 0 (blockLength lam X))
    (by intro m hm b hb; have := Finset.mem_Ioc.mp hm; have := Finset.mem_Ioc.mp hb; omega)
    (by intro m hm b hb; have := Finset.mem_Ioc.mp hm; have := Finset.mem_Ioc.mp hb; omega)
    (fun m => Z X m^2) (fun _ _ => sq_nonneg _) (cumulativeProfile tau g)
    (by linarith : tau<1) (cumulativeProfile_budget tau g hgt) hg0
  rw [←extraAverage_pair_identity hX (blockLength lam X) (fun m => Z X m^2) g hgt] at hh
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,q,E] using hh

theorem index_density_of_bombieriVinogradov (hBV : BombieriVinogradov)
    (C : ℝ) (hC : 0<C) :
    ∃ c : ℝ, 0<c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀≤N →
      c*(N:ℝ)≤((largeGapIndices C N).card:ℝ) := by
  let tau : ℝ := 1/8
  let lam : ℝ := C+1
  have htau : 0<tau := by norm_num [tau]
  have hlam : 0<lam := by dsimp [lam]; linarith
  obtain ⟨g,hgs,hgc,hgt,_hgb,_hGc,_hGcompact,hg0⟩ := exists_detector_profile htau
  let D := lam+lam^2*l2Mass g^2+1
  have hD : 0<D := by dsimp [D]; positivity
  let eps := lam^2/(16*D)
  have heps : 0<eps := by dsimp [eps]; positivity
  obtain ⟨k,f,hf,_hf0,hw,hv⟩ := exists_family_small_marked_ratio hlam htau heps
  let w := familyW lam k f
  have hw' : 0<w := hw
  let a := lam*w/2
  let K := D*w
  let b := 2*(eps*w)
  have ha : 0<a := by dsimp [a]; positivity
  have hK : 0<K := mul_pos hD hw'
  have hab : a^2/K=4*(eps*w) := by
    dsimp [a,K,eps]
    field_simp
    ring
  have hb : b<a^2/K := by
    rw [hab]
    dsimp [b]
    nlinarith [mul_pos heps hw']
  obtain ⟨M,hM,hfourth⟩ := unorderedWeight_fourth_bound f hf htau.le
    (by norm_num [tau] : 4*tau<1) hlam
  apply index_density_from_weight_estimates hC
    (fun X m => unorderedWeight tau lam k f X m^2) a K b M ha hK hM hb
  · exact Eventually.of_forall fun _ _ _ => sq_nonneg _
  · have hlim := unorderedWeight_external_marked_limit hBV f hf htau.le
      (by norm_num [tau] : 2*tau<1/2) hlam
    have hlt : a<lam*familyW lam k f := by
      change lam*w/2<lam*w
      nlinarith [mul_pos hlam hw']
    exact Eventually.mono ((tendsto_order.mp hlim).1 a hlt) fun _ h => h.le
  · exact unorderedWeight_detector_bound hBV f hf htau.le
      (by norm_num [tau] : 6*tau<1) hlam hw g hgc hgs hgt hg0
  · have hlim := unorderedWeight_internal_marked_limit hBV f hf htau.le
      (by norm_num [tau] : 2*tau<1/2) hlam
    have hV : familyV lam k f≤eps*w := (div_le_iff₀ hw).mp hv
    have hlt : familyV lam k f<b := by
      dsimp [b]
      nlinarith [mul_pos heps hw']
    exact Eventually.mono ((tendsto_order.mp hlim).2 b hlt) fun _ h => h.le
  · filter_upwards [hfourth] with X hX
    simpa only [←pow_mul] using hX

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_DetectorMoments

section File_OpenAIPrimeGaps_CharacterErrors

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

noncomputable def primeCharacterPrefix (x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n∈Finset.Ioc 0 ⌊x⌋₊, χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)

noncomputable def primeCharacterError (x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  primeCharacterPrefix x χ-if χ=1 then (x:ℂ) else 0

theorem character_prefix_orthogonality (x : ℝ) {q c : ℕ} (hq : 0<q)
    (hc : c<q) (hcop : Nat.Coprime c q) :
    ∑ χ : DirichletCharacter ℂ q, χ (c:ZMod q)⁻¹*primeCharacterPrefix x χ=
      (q.totient:ℂ)*(residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c:ℂ) := by
  classical
  have : NeZero q := ⟨ne_of_gt hq⟩
  have hu : IsUnit (c:ZMod q) := (ZMod.isUnit_iff_coprime c q).mpr hcop
  have he (n : ℕ) : (c:ZMod q)=(n:ZMod q) ↔ n%q=c := by
    rw [ZMod.natCast_eq_natCast_iff',Nat.mod_eq_of_lt hc]
    exact eq_comm
  unfold primeCharacterPrefix
  simp_rw [Finset.mul_sum,←mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [←Finset.sum_mul,DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu,he]
  simp only [residuePrefix,residueSlice,Complex.ofReal_sum,Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> simp

theorem character_error_orthogonality (x : ℝ) {q c : ℕ} (hq : 0<q)
    (hc : c<q) (hcop : Nat.Coprime c q) :
    ∑ χ : DirichletCharacter ℂ q, χ (c:ZMod q)⁻¹*primeCharacterError x χ=
      (q.totient:ℂ)*((residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-x/q.totient:ℝ):ℂ) := by
  classical
  have : NeZero q := ⟨ne_of_gt hq⟩
  have hu : IsUnit (c:ZMod q) := (ZMod.isUnit_iff_coprime c q).mpr hcop
  have huinv : IsUnit (c:ZMod q)⁻¹ := by
    obtain ⟨u,hu⟩ := hu
    rw [←hu,ZMod.inv_coe_unit]
    exact (u⁻¹).isUnit
  have ht : (q.totient:ℂ)≠0 := by exact_mod_cast ne_of_gt (Nat.totient_pos.mpr hq)
  simp only [primeCharacterError,mul_sub,Finset.sum_sub_distrib]
  rw [character_prefix_orthogonality x hq hc hcop]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte,MulChar.one_apply huinv,one_mul]
  push_cast
  field_simp

theorem endpointClassError_le_character_sum (x : ℝ) {q c : ℕ} (hq : 0<q)
    (hc : c<q) (hcop : Nat.Coprime c q) :
    |residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-x/q.totient|≤
      (∑ χ : DirichletCharacter ℂ q, ‖primeCharacterError x χ‖)/(q.totient:ℝ) := by
  have hphi : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  apply (le_div_iff₀ hphi).mpr
  have hh := character_error_orthogonality x hq hc hcop
  calc
    _ = ‖(q.totient:ℂ)*((residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-x/q.totient:ℝ):ℂ)‖ := by
      rw [norm_mul,Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,mul_comm]
    _ = ‖∑ χ : DirichletCharacter ℂ q, χ (c:ZMod q)⁻¹*primeCharacterError x χ‖ := congrArg norm hh.symm
    _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖χ (c:ZMod q)⁻¹*primeCharacterError x χ‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro χ _
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

noncomputable def characterMeanError (x : ℝ) (q : ℕ) : ℝ :=
  (∑ χ : DirichletCharacter ℂ q, ‖primeCharacterError x χ‖)/(q.totient:ℝ)

theorem characterMeanError_nonneg (x : ℝ) (q : ℕ) : 0≤characterMeanError x q := by
  unfold characterMeanError
  positivity

theorem endpointError_le_characterMeanError (x : ℝ) {q : ℕ} (hq : 0<q) :
    (endpointError x q:ℝ)≤characterMeanError x q := by
  change (endpointError x q:ℝ)≤(⟨characterMeanError x q,characterMeanError_nonneg x q⟩:NNReal)
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro c hc
  split_ifs with hcop
  · exact NNReal.coe_le_coe.mp (endpointClassError_le_character_sum x hq (Finset.mem_range.mp hc) hcop)
  · exact bot_le

theorem endpointErrors_le_characterMeanErrors (x : ℝ) (Q : ℕ) :
    (∑ q∈Finset.Icc 1 Q,(endpointError x q:ℝ))≤
      ∑ q∈Finset.Icc 1 Q,characterMeanError x q := by
  apply Finset.sum_le_sum
  intro q hq
  exact endpointError_le_characterMeanError x (Finset.mem_Icc.mp hq).1

theorem vonMangoldt_noncoprime_sum_le (X : ℕ) {q : ℕ} (hq : 0<q) :
    (∑ n∈(Finset.Ioc 0 X).filter (fun n => ¬Nat.Coprime n q),
      ArithmeticFunction.vonMangoldt n)≤(Nat.log 2 X:ℝ)*Real.log q := by
  classical
  let S := (Finset.Ioc 0 X).filter (fun n => ¬Nat.Coprime n q ∧ ArithmeticFunction.vonMangoldt n≠0)
  have he : (∑ n∈(Finset.Ioc 0 X).filter (fun n => ¬Nat.Coprime n q),
      ArithmeticFunction.vonMangoldt n)=∑ n∈S,ArithmeticFunction.vonMangoldt n := by
    simp only [S,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hcop : Nat.Coprime n q <;> by_cases hn : ArithmeticFunction.vonMangoldt n=0 <;> simp [hcop,hn]
  rw [he]
  have hsub : S⊆(q^(Nat.log 2 X)).divisors := by
    intro n hn
    obtain ⟨hnI,hnq,hnv⟩ := Finset.mem_filter.mp hn
    obtain ⟨p,k,hp,_hk,hpkn⟩ := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hnv
    have hp' : p.Prime := Nat.prime_iff.mpr hp
    have hdp : p∣q := by
      by_contra hd
      have hc := (hp'.coprime_iff_not_dvd).mpr hd
      exact hnq (hpkn ▸ hc.pow_left k)
    have hkX : k≤Nat.log 2 X := by
      apply Nat.le_log_of_pow_le (by norm_num : 1<2)
      calc
        2^k≤p^k := Nat.pow_le_pow_left hp'.two_le k
        _ = n := hpkn
        _ ≤ X := (Finset.mem_Ioc.mp hnI).2
    apply Nat.mem_divisors.mpr
    refine ⟨?_,pow_ne_zero _ (ne_of_gt hq)⟩
    rw [←hpkn]
    exact (pow_dvd_pow_of_dvd hdp k).trans (pow_dvd_pow q hkX)
  calc
    _ ≤ ∑ n∈(q^(Nat.log 2 X)).divisors,ArithmeticFunction.vonMangoldt n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = Real.log ((q^(Nat.log 2 X):ℕ):ℝ) := ArithmeticFunction.vonMangoldt_sum
    _ = _ := by rw [Nat.cast_pow,Real.log_pow]

theorem primitiveCharacter_eq_one_iff {q : ℕ} (hq : 0<q) (χ : DirichletCharacter ℂ q) :
    χ.primitiveCharacter=1 ↔ χ=1 := by
  have : NeZero q := ⟨ne_of_gt hq⟩
  constructor
  · intro h
    rw [←DirichletCharacter.changeLevel_primitiveCharacter χ,h,DirichletCharacter.changeLevel_one]
  · rintro rfl
    exact DirichletCharacter.primitiveCharacter_one

theorem primeCharacterPrefix_primitive_difference (x : ℝ) {q : ℕ} (hq : 0<q)
    (χ : DirichletCharacter ℂ q) :
    ‖primeCharacterPrefix x χ-primeCharacterPrefix x χ.primitiveCharacter‖≤
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  have hsame (n : ℕ) (hn : Nat.Coprime n q) :
      χ.primitiveCharacter (n:ZMod χ.conductor)=χ (n:ZMod q) := by
    simpa only [Int.cast_natCast] using χ.primitiveCharacter_apply_of_isCoprime hn.isCoprime
  have hzero (n : ℕ) (hn : ¬Nat.Coprime n q) : χ (n:ZMod q)=0 :=
    χ.map_nonunit (fun h => hn ((ZMod.isUnit_iff_coprime n q).mp h))
  calc
    _ = ‖∑ n∈Finset.Ioc 0 ⌊x⌋₊,(χ (n:ZMod q)-χ.primitiveCharacter (n:ZMod χ.conductor))*
        (ArithmeticFunction.vonMangoldt n:ℂ)‖ := by
      congr 1
      simp only [primeCharacterPrefix,sub_mul,Finset.sum_sub_distrib]
    _ ≤ ∑ n∈Finset.Ioc 0 ⌊x⌋₊,‖(χ (n:ZMod q)-χ.primitiveCharacter (n:ZMod χ.conductor))*
        (ArithmeticFunction.vonMangoldt n:ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n∈(Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬Nat.Coprime n q),ArithmeticFunction.vonMangoldt n := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro n _
      by_cases hn : Nat.Coprime n q
      · simp [hn,hsame n hn]
      · simp only [ite_eq_left hn,hzero n hn,zero_sub,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
          (χ.primitiveCharacter.norm_le_one _)
    _ ≤ _ := vonMangoldt_noncoprime_sum_le _ hq

theorem primeCharacterError_primitive_difference (x : ℝ) {q : ℕ} (hq : 0<q)
    (χ : DirichletCharacter ℂ q) :
    ‖primeCharacterError x χ-primeCharacterError x χ.primitiveCharacter‖≤
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  have he : primeCharacterError x χ-primeCharacterError x χ.primitiveCharacter=
      primeCharacterPrefix x χ-primeCharacterPrefix x χ.primitiveCharacter := by
    simp only [primeCharacterError,primitiveCharacter_eq_one_iff hq χ]
    ring
  rw [he]
  exact primeCharacterPrefix_primitive_difference x hq χ

theorem primeCharacterError_le_primitive (x : ℝ) {q : ℕ} (hq : 0<q)
    (χ : DirichletCharacter ℂ q) :
    ‖primeCharacterError x χ‖≤‖primeCharacterError x χ.primitiveCharacter‖+
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  have hn := norm_add_le (primeCharacterError x χ.primitiveCharacter)
    (primeCharacterError x χ-primeCharacterError x χ.primitiveCharacter)
  rw [add_sub_cancel] at hn
  exact hn.trans (add_le_add_right (primeCharacterError_primitive_difference x hq χ) _)

theorem characterMeanError_le_primitive_average (x : ℝ) {q : ℕ} (hq : 0<q) :
    characterMeanError x q≤
      (∑ χ : DirichletCharacter ℂ q,‖primeCharacterError x χ.primitiveCharacter‖)/(q.totient:ℝ)+
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  have : NeZero q := ⟨ne_of_gt hq⟩
  have hphi : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hcard : Fintype.card (DirichletCharacter ℂ q)=q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  unfold characterMeanError
  calc
    _ ≤ (∑ χ : DirichletCharacter ℂ q,(‖primeCharacterError x χ.primitiveCharacter‖+
        (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q))/(q.totient:ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun χ _ => primeCharacterError_le_primitive x hq χ)) hphi.le
    _ = _ := by
      rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul,add_div]
      congr 1
      exact mul_div_cancel_left₀ _ hphi.ne'

noncomputable def primitiveErrorMass (x : ℝ) (d : ℕ) : ℝ :=
  ∑ χ∈(Finset.univ : Finset (DirichletCharacter ℂ d)).filter DirichletCharacter.IsPrimitive,
    ‖primeCharacterError x χ‖

theorem primitiveErrorMass_nonneg (x : ℝ) (d : ℕ) : 0≤primitiveErrorMass x d := by
  unfold primitiveErrorMass
  positivity

theorem induced_primitive_sum_le (x : ℝ) {q : ℕ} (hq : 0<q) :
    (∑ χ : DirichletCharacter ℂ q,‖primeCharacterError x χ.primitiveCharacter‖)≤
      ∑ d∈q.divisors,primitiveErrorMass x d := by
  classical
  let i : DirichletCharacter ℂ q → Sigma (DirichletCharacter ℂ) :=
    fun χ => ⟨χ.conductor,χ.primitiveCharacter⟩
  let lift : Sigma (DirichletCharacter ℂ) → DirichletCharacter ℂ q :=
    fun p => if h : p.1∣q then DirichletCharacter.changeLevel h p.2 else 1
  have hleft (χ : DirichletCharacter ℂ q) : lift (i χ)=χ := by
    dsimp [lift,i]
    rw [dite_eq_left χ.conductor_dvd_level,DirichletCharacter.changeLevel_primitiveCharacter]
  have hi : Function.Injective i := by
    intro χ ψ h
    simpa only [hleft] using congrArg lift h
  let S := q.divisors.sigma (fun d =>
    (Finset.univ : Finset (DirichletCharacter ℂ d)).filter DirichletCharacter.IsPrimitive)
  have hsub : Finset.univ.image i⊆S := by
    intro p hp
    obtain ⟨χ,_,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_sigma.mpr ⟨Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level,ne_of_gt hq⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,χ.primitiveCharacter_isPrimitive⟩⟩
  calc
    _ = ∑ p∈Finset.univ.image i,‖primeCharacterError x p.2‖ := by
      rw [Finset.sum_image (fun _ _ _ _ h => hi h)]
    _ ≤ ∑ p∈S,‖primeCharacterError x p.2‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)
    _ = _ := by rw [Finset.sum_sigma]; rfl

theorem endpointError_le_primitive_conductors (x : ℝ) {q : ℕ} (hq : 0<q) :
    (endpointError x q:ℝ)≤(∑ d∈q.divisors,primitiveErrorMass x d)/(q.totient:ℝ)+
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  apply (endpointError_le_characterMeanError x hq).trans
  apply (characterMeanError_le_primitive_average x hq).trans
  exact add_le_add_left (div_le_div_of_nonneg_right (induced_primitive_sum_le x hq) (Nat.cast_nonneg _)) _

theorem nat_le_card_divisors_mul_totient (q : ℕ) : q≤q.divisors.card*q.totient := by
  calc
    q = ∑ d∈q.divisors,d.totient := (Nat.sum_totient q).symm
    _ ≤ ∑ _d∈q.divisors,q.totient := by
      apply Finset.sum_le_sum
      intro d hd
      exact Nat.le_of_dvd (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2))
        (Nat.totient_dvd_of_dvd (Nat.mem_divisors.mp hd).1)
    _ = _ := by simp

theorem divisorMultiplicity_two (q : ℕ) : divisorMultiplicity 2 q=q.divisors.card := by
  rw [show 2=1+1 from rfl,divisorMultiplicity_succ]
  calc
    _ = ∑ _d∈q.divisors,1 := by
      apply Finset.sum_congr rfl
      intro d hd
      simp [divisorMultiplicity,ArithmeticFunction.zeta_apply_ne
        (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2)).ne']
    _ = _ := by simp

theorem sum_totient_reciprocal_le (Q : ℕ) :
    (∑ q∈Finset.Icc 1 Q,(1:ℝ)/(q.totient:ℝ))≤(harmonic Q:ℝ)^2 := by
  apply le_trans (Finset.sum_le_sum (g:=fun q => (divisorMultiplicity 2 q:ℝ)/(q:ℝ)) ?_)
    (sum_divisorMultiplicity_reciprocal_le 2 Q)
  intro q hq
  have hq0 : (0:ℝ)<q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
  have hp : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr (Finset.mem_Icc.mp hq).1
  rw [divisorMultiplicity_two,div_le_div_iff₀ hp hq0,one_mul]
  exact_mod_cast nat_le_card_divisors_mul_totient q

theorem reciprocal_totient_divisor_sum_le (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (∑ d ∈ q.divisors, f d) / (q.totient : ℝ)) ≤
      (∑ d ∈ Finset.Icc 1 Q, f d / (d.totient : ℝ)) * (harmonic Q : ℝ)^2 := by
  classical
  let s := (Finset.Icc 1 Q).sigma fun q => q.divisors
  let t := (Finset.Icc 1 Q) ×ˢ (Finset.Icc 1 Q)
  let e : (a : ℕ) × ℕ → ℕ × ℕ := fun x => (x.2, x.1/x.2)
  have he_mem : ∀ x ∈ s, e x ∈ t := by
    rintro ⟨q,d⟩ hx
    obtain ⟨hq, hd⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hq1,hqQ⟩ := Finset.mem_Icc.mp hq
    obtain ⟨hdq,hq0⟩ := Nat.mem_divisors.mp hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdq hq1
    have hdle : d ≤ q := Nat.le_of_dvd hq1 hdq
    have hdivpos : 0 < q/d := Nat.div_pos hdle hd0
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hd0, hdle.trans hqQ⟩,
      Finset.mem_Icc.mpr ⟨hdivpos, (Nat.div_le_self q d).trans hqQ⟩⟩
  have he_inj : Set.InjOn e s := by
    rintro ⟨q,d⟩ hx ⟨q',d'⟩ hy he
    obtain ⟨hq,hd⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hq',hd'⟩ := Finset.mem_sigma.mp hy
    have hed : d = d' := congrArg Prod.fst he
    have heq : q/d = q'/d' := congrArg Prod.snd he
    have hdq : d ∣ q := (Nat.mem_divisors.mp hd).1
    have hdq' : d' ∣ q' := (Nat.mem_divisors.mp hd').1
    have hqq : q = q' := by
      rw [← Nat.div_mul_cancel hdq, ← Nat.div_mul_cancel hdq', heq, hed]
    subst d'
    subst q'
    rfl
  have hsum : (∑ q ∈ Finset.Icc 1 Q, (∑ d ∈ q.divisors, f d) / (q.totient : ℝ)) ≤
      ∑ x ∈ s, f (e x).1 / (e x).1.totient / (e x).2.totient := by
    dsimp only [s]
    rw [Finset.sum_sigma]
    apply Finset.sum_le_sum
    intro q hq
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro d hd
    have hdq := (Nat.mem_divisors.mp hd).1
    have hq0 : 0<q := (Finset.mem_Icc.mp hq).1
    have hd0 : 0<d := Nat.pos_of_dvd_of_pos hdq hq0
    have hk0 : 0<q/d := Nat.div_pos (Nat.le_of_dvd hq0 hdq) hd0
    have ht : (d.totient:ℝ)*(q/d).totient≤q.totient := by
      have hh := Nat.totient_super_multiplicative d (q/d)
      rw [Nat.mul_div_cancel' hdq] at hh
      exact_mod_cast hh
    dsimp only [e]
    rw [div_div]
    exact div_le_div_of_nonneg_left (hf d) (mul_pos
      (by exact_mod_cast Nat.totient_pos.mpr hd0) (by exact_mod_cast Nat.totient_pos.mpr hk0)) ht
  apply hsum.trans
  calc
    _ = ∑ x ∈ s.image e, f x.1 / (x.1.totient : ℝ) / (x.2.totient : ℝ) := by
      rw [Finset.sum_image he_inj]
    _ ≤ ∑ x ∈ t, f x.1 / (x.1.totient : ℝ) / (x.2.totient : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr he_mem)
        (fun x _ _ => div_nonneg (div_nonneg (hf _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    _ = (∑ d∈Finset.Icc 1 Q,f d/(d.totient:ℝ))*(∑ k∈Finset.Icc 1 Q,(1:ℝ)/k.totient) := by
      simp only [t,Finset.sum_product,div_eq_mul_inv,one_mul,Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_totient_reciprocal_le Q)
      (Finset.sum_nonneg (fun _ _ => div_nonneg (hf _) (Nat.cast_nonneg _)))

theorem endpointErrors_le_primitive_weighted_sum (x : ℝ) (Q : ℕ) :
    (∑ q∈Finset.Icc 1 Q,(endpointError x q:ℝ))≤
      (∑ d∈Finset.Icc 1 Q,primitiveErrorMass x d/(d.totient:ℝ))*(harmonic Q:ℝ)^2+
      (Q:ℝ)*(Nat.log 2 ⌊x⌋₊:ℝ)*Real.log Q := by
  calc
    _ ≤ ∑ q∈Finset.Icc 1 Q,((∑ d∈q.divisors,primitiveErrorMass x d)/(q.totient:ℝ)+
        (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q) :=
      Finset.sum_le_sum (fun q hq => endpointError_le_primitive_conductors x (Finset.mem_Icc.mp hq).1)
    _ = (∑ q∈Finset.Icc 1 Q,(∑ d∈q.divisors,primitiveErrorMass x d)/(q.totient:ℝ))+
        ∑ q∈Finset.Icc 1 Q,(Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := Finset.sum_add_distrib
    _ ≤ _ := by
      apply add_le_add (reciprocal_totient_divisor_sum_le _ (primitiveErrorMass_nonneg x) Q)
      calc
        _ ≤ ∑ _q∈Finset.Icc 1 Q,(Nat.log 2 ⌊x⌋₊:ℝ)*Real.log Q := by
          apply Finset.sum_le_sum
          intro q hq
          exact mul_le_mul_of_nonneg_left (Real.log_le_log
            (by exact_mod_cast (Finset.mem_Icc.mp hq).1) (by exact_mod_cast (Finset.mem_Icc.mp hq).2))
            (Nat.cast_nonneg _)
        _ = _ := by simp [mul_assoc]

noncomputable def arithmeticCutoff (T : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n≤T then f n else 0,by simp⟩

@[simp] theorem arithmeticCutoff_apply (T n : ℕ) (f : ArithmeticFunction ℝ) :
    arithmeticCutoff T f n=if n≤T then f n else 0 := rfl

theorem vaughan_identity (U V : ℕ) :
    ArithmeticFunction.vonMangoldt =
      arithmeticCutoff U ArithmeticFunction.vonMangoldt+
      arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ)*ArithmeticFunction.log-
      arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ)*
        arithmeticCutoff U ArithmeticFunction.vonMangoldt*(ArithmeticFunction.zeta:ArithmeticFunction ℝ)+
      ((ArithmeticFunction.moebius:ArithmeticFunction ℝ)-arithmeticCutoff V ArithmeticFunction.moebius)*
        (ArithmeticFunction.vonMangoldt-arithmeticCutoff U ArithmeticFunction.vonMangoldt)*
        (ArithmeticFunction.zeta:ArithmeticFunction ℝ) := by
  rw [←ArithmeticFunction.vonMangoldt_mul_zeta]
  have hmu : (ArithmeticFunction.moebius:ArithmeticFunction ℝ)*ArithmeticFunction.zeta=1 :=
    ArithmeticFunction.coe_moebius_mul_coe_zeta
  linear_combination
    (arithmeticCutoff U ArithmeticFunction.vonMangoldt-ArithmeticFunction.vonMangoldt)*hmu

noncomputable def vaughanSecondCoefficient (U : ℕ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.vonMangoldt-arithmeticCutoff U ArithmeticFunction.vonMangoldt)*
    (ArithmeticFunction.zeta:ArithmeticFunction ℝ)

theorem vaughanSecondCoefficient_eq (U n : ℕ) :
    vaughanSecondCoefficient U n=
      ∑ d∈n.divisors,if U<d then ArithmeticFunction.vonMangoldt d else 0 := by
  rw [vaughanSecondCoefficient,ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_congr rfl
  intro d _
  change ArithmeticFunction.vonMangoldt d-(if d≤U then ArithmeticFunction.vonMangoldt d else 0)=_
  by_cases hd : d≤U
  · simp [hd,not_lt_of_ge hd]
  · simp [hd,lt_of_not_ge hd]

theorem vaughanSecondCoefficient_nonneg (U n : ℕ) :
    0≤vaughanSecondCoefficient U n := by
  rw [vaughanSecondCoefficient_eq]
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)

theorem vaughanSecondCoefficient_le_log (U n : ℕ) :
    vaughanSecondCoefficient U n≤Real.log n := by
  rw [vaughanSecondCoefficient_eq,←ArithmeticFunction.vonMangoldt_sum]
  apply Finset.sum_le_sum
  intro d _
  split_ifs
  · rfl
  · exact ArithmeticFunction.vonMangoldt_nonneg

theorem vaughanSecondCoefficient_zero_of_le {U n : ℕ} (hn : n≤U) :
    vaughanSecondCoefficient U n=0 := by
  rw [vaughanSecondCoefficient_eq]
  apply Finset.sum_eq_zero
  intro d hd
  have hdle := Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2)
    (Nat.mem_divisors.mp hd).1
  exact ite_eq_right (by omega)

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_CharacterErrors

