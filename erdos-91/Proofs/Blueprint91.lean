module

/-
Copyright 2026 The Formal Conjectures Authors.
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

public import MultiDeletionCore91

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

open scoped BigOperators
open scoped Classical
open scoped Finset

/-- The set of distances determined by a finite set of points in a metric space. -/
noncomputable def distanceSet {X : Type*} [MetricSpace X] (points : Finset X) : Finset ℝ :=
  points.offDiag.image fun (pair : X × X) => dist pair.1 pair.2

/-- The number of distinct distances between pairs of points. -/
noncomputable def distinctDistances {X : Type*} [MetricSpace X] (points : Finset X) : ℕ :=
  #(distanceSet points)

/-- The minimum number of distinct distances determined by a set of `n` points in `X`. -/
noncomputable def minimalDistinctDistances (X : Type*) [MetricSpace X] (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ points : Finset X, #points = n ∧ distinctDistances points = m}

namespace Erdos91

/-- A set $A$ is optimal if it has $n$ points and achieves the minimum distance count. -/
noncomputable def IsOptimal (A : Finset (EuclideanSpace ℝ (Fin 2))) (n : ℕ) : Prop :=
  A.card = n ∧ _root_.distinctDistances A = _root_.minimalDistinctDistances (EuclideanSpace ℝ (Fin 2)) n

/-- Two finite sets of points in $\mathbb{R}^2$ are similar if mapped by a `DilationEquiv`. -/
def DilationEquivSimilar (A B : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ f : EuclideanSpace ℝ (Fin 2) ≃ᵈ EuclideanSpace ℝ (Fin 2), (f '' (A : Set (EuclideanSpace ℝ (Fin 2)))) = B

/-- Equilateral triangle with unit side length, resting on the x-axis with one vertex at the origin. -/
noncomputable def equiTriangle : Finset (EuclideanSpace ℝ (Fin 2)) :=
  {!₂[0, 0], !₂[1, 0], !₂[1 / 2, Real.sqrt 3 / 2]}

/-- All optimal $n$-point subsets of $\mathbb{R}^2$ are similar up to `DilationEquiv`. -/
def UniqueMinimizer (n : ℕ) : Prop :=
  ∀ A B : Finset (EuclideanSpace ℝ (Fin 2)), IsOptimal A n → IsOptimal B n → DilationEquivSimilar A B

end Erdos91

open scoped Classical
open Finset Filter PlateauDefinitions91 Erdos91.TwoDistanceCapAndSixNonunique Erdos91.ThreeDistanceLevelAndDiameterFiberBounds Erdos91.CayleyMengerSymmetricAndDiameterAdjacentFibers Erdos91.SmallCasesAndSquareBarrier Erdos91.DistanceCompleteCoreDeletionInvariance Erdos91.MultiDeletionScoreInvarianceAndCoreMultiplicity Erdos91.LatticeMultiDeletionScoreAndPatchFamilies Erdos91.ArbitraryPatchCoordMultiDeletionTheory Erdos91.EquilateralTriangularPatchCoreAndPairDeletions Erdos91.TriangularLatticeHexagonAndSub130Majority Erdos91.SymbolicHexagonExactCardinalityAndDistanceSet Erdos91.UnconditionalNaturalDensityOne Erdos91.SublinearMinimalDistancesProof

abbrev Plane := Minimizer91.Plane

namespace Erdos91.SharpenedTwoCenterFiberSumBounds

/-- **Universal Two-Center Fiber Defect Sum Bound (`∀ S a b Q`):**
for any distinct `a, b ∈ S` and any subset `Q ⊆ distanceSet S ×ˢ distanceSet S` of radius
pairs whose two-center fibers over `(a, b)` have cardinality at most `1`,
`S.card + Q.card ≤ 2 * (distinctDistances S)^2 + 2`. -/
theorem two_center_fiber_defect_sum_bound
    (S : Finset Plane) (a b : Plane) (Q : Finset (ℝ × ℝ))
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hQ_sub : Q ⊆ Minimizer91.distanceSet S ×ˢ Minimizer91.distanceSet S)
    (hQ_cap : ∀ q ∈ Q, (S.filter (fun v => dist v a = q.1 ∧ dist v b = q.2)).card ≤ 1) :
    S.card + Q.card ≤ 2 * (Minimizer91.distinctDistances S) ^ 2 + 2 := by
  let B := (S.erase a).erase b
  have hbErase : b ∈ S.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  have hBcard : B.card + 2 = S.card := by
    have h1 : B.card = (S.erase a).card - 1 := Finset.card_erase_of_mem hbErase
    have h2 : (S.erase a).card = S.card - 1 := Finset.card_erase_of_mem ha
    have hpos : 2 ≤ S.card := Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab⟩
    omega
  let pairMap : Plane → ℝ × ℝ := fun v => (dist v a, dist v b)
  let P := Minimizer91.distanceSet S ×ˢ Minimizer91.distanceSet S
  have hPcard : P.card = (Minimizer91.distinctDistances S) ^ 2 := by
    dsimp [P, Minimizer91.distinctDistances]; rw [Finset.card_product]; ring
  have hmap_mem : ∀ v ∈ B, pairMap v ∈ P := by
    intro v hv
    obtain ⟨hvb, hva⟩ := Finset.mem_erase.mp hv
    obtain ⟨hva', hvS⟩ := Finset.mem_erase.mp hva
    exact Finset.mem_product.mpr
      ⟨(Erdos91.DistanceErasure.mem_distanceSet _ _).mpr ⟨v, hvS, a, ha, hva', rfl⟩,
       (Erdos91.DistanceErasure.mem_distanceSet _ _).mpr ⟨v, hvS, b, hb, hvb, rfl⟩⟩
  have hB_sum : B.card = ∑ q ∈ P, (B.filter (fun v => pairMap v = q)).card :=
    Finset.card_eq_sum_card_fiberwise hmap_mem
  have hsub_S : ∀ q : ℝ × ℝ,
      B.filter (fun v => pairMap v = q) ⊆ S.filter (fun v => dist v a = q.1 ∧ dist v b = q.2) := by
    intro q v hv
    obtain ⟨hvB, hq⟩ := Finset.mem_filter.mp hv
    have hvS : v ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hvB)
    exact Finset.mem_filter.mpr ⟨hvS, (Prod.ext_iff.mp hq).1, (Prod.ext_iff.mp hq).2⟩
  have h_all : ∀ q ∈ P, (B.filter (fun v => pairMap v = q)).card ≤ 2 := by
    intro q _
    refine (Finset.card_le_card (hsub_S q)).trans ?_
    exact CircleFibers91.two_centers_card
      (S.filter (fun v => dist v a = q.1 ∧ dist v b = q.2)) a b q.1 q.2 hab
      (fun v hv => (Finset.mem_filter.mp hv).2.1)
      (fun v hv => (Finset.mem_filter.mp hv).2.2)
  have h_Q : ∀ q ∈ Q, (B.filter (fun v => pairMap v = q)).card ≤ 1 := by
    intro q hq
    exact (Finset.card_le_card (hsub_S q)).trans (hQ_cap q hq)
  have hsplit : P = Q ∪ (P \ Q) := (Finset.union_sdiff_of_subset hQ_sub).symm
  have hdisj : Disjoint Q (P \ Q) := disjoint_sdiff_self_right
  have hsum_split : (∑ q ∈ P, (B.filter (fun v => pairMap v = q)).card) =
      (∑ q ∈ Q, (B.filter (fun v => pairMap v = q)).card) +
      (∑ q ∈ P \ Q, (B.filter (fun v => pairMap v = q)).card) := by
    conv_lhs => rw [hsplit]
    exact Finset.sum_union hdisj
  have hsum_Q : (∑ q ∈ Q, (B.filter (fun v => pairMap v = q)).card) ≤ Q.card := by
    calc (∑ q ∈ Q, (B.filter (fun v => pairMap v = q)).card)
        ≤ ∑ _q ∈ Q, 1 := Finset.sum_le_sum h_Q
      _ = Q.card := by simp
  have hsum_PQ : (∑ q ∈ P \ Q, (B.filter (fun v => pairMap v = q)).card) ≤ 2 * (P \ Q).card := by
    calc (∑ q ∈ P \ Q, (B.filter (fun v => pairMap v = q)).card)
        ≤ ∑ _q ∈ P \ Q, 2 := Finset.sum_le_sum (fun q hq => h_all q (Finset.sdiff_subset hq))
      _ = 2 * (P \ Q).card := by simp [Nat.mul_comm]
  have hcard_PQ : P.card = Q.card + (P \ Q).card := by
    conv_lhs => rw [hsplit]
    exact Finset.card_union_of_disjoint hdisj
  omega

/-- **Universal Triangle-Inequality Infeasible Fiber Empty Theorem (`∀ S a b r t`):**
if `(r, t)` violates the triangle inequality over `(a, b)`, then the `(r, t)`-fiber in `S` is empty. -/
theorem infeasible_triangle_fiber_card_eq_zero
    (S : Finset Plane) (a b : Plane) (r t : ℝ)
    (hinf : r + t < dist a b ∨ t + dist a b < r ∨ r + dist a b < t) :
    (S.filter (fun v => dist v a = r ∧ dist v b = t)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro v _ ⟨hva, hvb⟩
  have h1 : dist a b ≤ r + t := by
    rw [← hva, ← hvb]; simpa [dist_comm] using dist_triangle a v b
  have h2 : r ≤ t + dist a b := by
    rw [← hva, ← hvb]; simpa [dist_comm] using dist_triangle v b a
  have h3 : t ≤ r + dist a b := by
    rw [← hva, ← hvb]; simpa [dist_comm] using dist_triangle v a b
  rcases hinf with h | h | h <;> linarith

/-- **Universal Empty + Singleton Two-Center Fiber Defect Sum Bound (`∀ S a b Q₀ Q₁`):**
for any disjoint `Q₀, Q₁ ⊆ distanceSet S ×ˢ distanceSet S` where every `q ∈ Q₀` has empty fiber
and every `q ∈ Q₁` has fiber cardinality `≤ 1`, `S.card + 2 * Q₀.card + Q₁.card ≤ 2 * distinctDistances(S)^2 + 2`. -/
theorem two_center_empty_and_singleton_fiber_sum_bound
    (S : Finset Plane) (a b : Plane) (Q₀ Q₁ : Finset (ℝ × ℝ))
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hQ₀_sub : Q₀ ⊆ Minimizer91.distanceSet S ×ˢ Minimizer91.distanceSet S)
    (hQ₁_sub : Q₁ ⊆ Minimizer91.distanceSet S ×ˢ Minimizer91.distanceSet S)
    (hdisj₀₁ : Disjoint Q₀ Q₁)
    (hQ₀_empty : ∀ q ∈ Q₀, (S.filter (fun v => dist v a = q.1 ∧ dist v b = q.2)).card = 0)
    (hQ₁_cap : ∀ q ∈ Q₁, (S.filter (fun v => dist v a = q.1 ∧ dist v b = q.2)).card ≤ 1) :
    S.card + 2 * Q₀.card + Q₁.card ≤ 2 * (Minimizer91.distinctDistances S) ^ 2 + 2 := by
  let B := (S.erase a).erase b
  have hbErase : b ∈ S.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  have hBcard : B.card + 2 = S.card := by
    have h1 : B.card = (S.erase a).card - 1 := Finset.card_erase_of_mem hbErase
    have h2 : (S.erase a).card = S.card - 1 := Finset.card_erase_of_mem ha
    have hpos : 2 ≤ S.card := Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab⟩
    omega
  let pairMap : Plane → ℝ × ℝ := fun v => (dist v a, dist v b)
  let P := Minimizer91.distanceSet S ×ˢ Minimizer91.distanceSet S
  have hPcard : P.card = (Minimizer91.distinctDistances S) ^ 2 := by
    dsimp [P, Minimizer91.distinctDistances]; rw [Finset.card_product]; ring
  have hmap_mem : ∀ v ∈ B, pairMap v ∈ P := by
    intro v hv
    obtain ⟨hvb, hva⟩ := Finset.mem_erase.mp hv
    obtain ⟨hva', hvS⟩ := Finset.mem_erase.mp hva
    exact Finset.mem_product.mpr
      ⟨(Erdos91.DistanceErasure.mem_distanceSet _ _).mpr ⟨v, hvS, a, ha, hva', rfl⟩,
       (Erdos91.DistanceErasure.mem_distanceSet _ _).mpr ⟨v, hvS, b, hb, hvb, rfl⟩⟩
  have hB_sum : B.card = ∑ q ∈ P, (B.filter (fun v => pairMap v = q)).card :=
    Finset.card_eq_sum_card_fiberwise hmap_mem
  have hsub_S : ∀ q : ℝ × ℝ,
      B.filter (fun v => pairMap v = q) ⊆ S.filter (fun v => dist v a = q.1 ∧ dist v b = q.2) := by
    intro q v hv
    obtain ⟨hvB, hq⟩ := Finset.mem_filter.mp hv
    have hvS : v ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hvB)
    exact Finset.mem_filter.mpr ⟨hvS, (Prod.ext_iff.mp hq).1, (Prod.ext_iff.mp hq).2⟩
  have h_all : ∀ q ∈ P, (B.filter (fun v => pairMap v = q)).card ≤ 2 := by
    intro q _
    refine (Finset.card_le_card (hsub_S q)).trans ?_
    exact CircleFibers91.two_centers_card
      (S.filter (fun v => dist v a = q.1 ∧ dist v b = q.2)) a b q.1 q.2 hab
      (fun v hv => (Finset.mem_filter.mp hv).2.1)
      (fun v hv => (Finset.mem_filter.mp hv).2.2)
  have h_Q₀ : ∀ q ∈ Q₀, (B.filter (fun v => pairMap v = q)).card ≤ 0 := by
    intro q hq
    exact (Finset.card_le_card (hsub_S q)).trans (hQ₀_empty q hq).le
  have h_Q₁ : ∀ q ∈ Q₁, (B.filter (fun v => pairMap v = q)).card ≤ 1 := by
    intro q hq
    exact (Finset.card_le_card (hsub_S q)).trans (hQ₁_cap q hq)
  let Q := Q₀ ∪ Q₁
  have hQ_sub : Q ⊆ P := Finset.union_subset hQ₀_sub hQ₁_sub
  have hsplit : P = Q ∪ (P \ Q) := (Finset.union_sdiff_of_subset hQ_sub).symm
  have hdisj : Disjoint Q (P \ Q) := disjoint_sdiff_self_right
  have hsum_split : (∑ q ∈ P, (B.filter (fun v => pairMap v = q)).card) =
      (∑ q ∈ Q₀, (B.filter (fun v => pairMap v = q)).card) +
      (∑ q ∈ Q₁, (B.filter (fun v => pairMap v = q)).card) +
      (∑ q ∈ P \ Q, (B.filter (fun v => pairMap v = q)).card) := by
    conv_lhs => rw [hsplit]
    rw [Finset.sum_union hdisj, Finset.sum_union hdisj₀₁]
  have hsum_Q₀ : (∑ q ∈ Q₀, (B.filter (fun v => pairMap v = q)).card) ≤ 0 := by
    calc (∑ q ∈ Q₀, (B.filter (fun v => pairMap v = q)).card)
        ≤ ∑ _q ∈ Q₀, 0 := Finset.sum_le_sum h_Q₀
      _ = 0 := by simp
  have hsum_Q₁ : (∑ q ∈ Q₁, (B.filter (fun v => pairMap v = q)).card) ≤ Q₁.card := by
    calc (∑ q ∈ Q₁, (B.filter (fun v => pairMap v = q)).card)
        ≤ ∑ _q ∈ Q₁, 1 := Finset.sum_le_sum h_Q₁
      _ = Q₁.card := by simp
  have hsum_PQ : (∑ q ∈ P \ Q, (B.filter (fun v => pairMap v = q)).card) ≤ 2 * (P \ Q).card := by
    calc (∑ q ∈ P \ Q, (B.filter (fun v => pairMap v = q)).card)
        ≤ ∑ _q ∈ P \ Q, 2 := Finset.sum_le_sum (fun q hq => h_all q (Finset.sdiff_subset hq))
      _ = 2 * (P \ Q).card := by simp [Nat.mul_comm]
  have hcard_PQ : P.card = Q₀.card + Q₁.card + (P \ Q).card := by
    conv_lhs => rw [hsplit]
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_union_of_disjoint hdisj₀₁]
  omega

/-- **Sharpened Two-Center Fiber Sum Bound (`S.card ≤ 2 * distinctDistances(S)^2 + 1`, `∀ S`):**
applying `diameter_equilateral_fiber_card_le_one` to `two_center_fiber_defect_sum_bound`
improves `S.card ≤ 2 * distinctDistances(S)^2 + 2` to `S.card ≤ 2 * distinctDistances(S)^2 + 1`
(and `S.card ≤ 19` whenever `distinctDistances S ≤ 3`). -/
theorem card_le_two_mul_distinctDistances_sq_add_one (S : Finset Plane) :
    S.card ≤ 2 * (Minimizer91.distinctDistances S) ^ 2 + 1 ∧
      S.card - 1 ≤ 2 * (Minimizer91.distinctDistances S) ^ 2 ∧
      (Minimizer91.distinctDistances S ≤ 3 → S.card ≤ 19) := by
  have h1 : S.card ≤ 2 * (Minimizer91.distinctDistances S) ^ 2 + 1 := by
    by_cases hcard : S.card < 2
    · omega
    · obtain ⟨a, ha, b, hb, hab, hdiam⟩ := exists_diameter_pair S (by omega)
      have hd_mem : dist a b ∈ Minimizer91.distanceSet S :=
        (Erdos91.DistanceErasure.mem_distanceSet _ _).mpr ⟨a, ha, b, hb, hab, rfl⟩
      have hQ_sub : {(dist a b, dist a b)} ⊆
          Minimizer91.distanceSet S ×ˢ Minimizer91.distanceSet S := by
        intro q hq
        rw [Finset.mem_singleton.mp hq]
        exact Finset.mem_product.mpr ⟨hd_mem, hd_mem⟩
      have hQ_cap : ∀ q ∈ ({(dist a b, dist a b)} : Finset (ℝ × ℝ)),
          (S.filter (fun v => dist v a = q.1 ∧ dist v b = q.2)).card ≤ 1 := by
        intro q hq
        rw [Finset.mem_singleton.mp hq]
        exact diameter_equilateral_fiber_card_le_one S a b ha hb hab hdiam
      have hbnd := two_center_fiber_defect_sum_bound S a b {(dist a b, dist a b)}
        ha hb hab hQ_sub hQ_cap
      simp only [Finset.card_singleton] at hbnd
      omega
  refine ⟨h1, by omega, fun h3 => ?_⟩
  have hsq : (Minimizer91.distinctDistances S) ^ 2 ≤ 3 ^ 2 := Nat.pow_le_pow_left h3 2
  omega

/-- **Sharpened Quadratic Lower Bound on `minimalDistinctDistances n` (`∀ n K`):**
for every `n : ℕ`, `n - 1 ≤ 2 * (minimalDistinctDistances n)^2`, and for every `K : ℕ`,
`K ≤ minimalDistinctDistances (2 * (K - 1)^2 + 2)`. -/
theorem minimal_quadratic_lower_bound_sharpened (n K : ℕ) :
    n - 1 ≤ 2 * (Minimizer91.minimalDistinctDistances n) ^ 2 ∧
      K ≤ Minimizer91.minimalDistinctDistances (2 * (K - 1) ^ 2 + 2) := by
  obtain ⟨S, hS⟩ := Minimizer91.exists_optimal n
  have h1 := (card_le_two_mul_distinctDistances_sq_add_one S).2.1
  rw [hS.1, hS.2] at h1
  refine ⟨h1, ?_⟩
  by_cases hK : K = 0
  · omega
  · obtain ⟨S2, hS2⟩ := Minimizer91.exists_optimal (2 * (K - 1) ^ 2 + 2)
    have h2 := (card_le_two_mul_distinctDistances_sq_add_one S2).2.1
    rw [hS2.1, hS2.2] at h2
    by_contra hlt
    have hle : Minimizer91.minimalDistinctDistances (2 * (K - 1) ^ 2 + 2) ≤ K - 1 := by omega
    have hsq : (Minimizer91.minimalDistinctDistances (2 * (K - 1) ^ 2 + 2)) ^ 2 ≤ (K - 1) ^ 2 :=
      Nat.pow_le_pow_left hle 2
    omega

/-- **Exact Cardinality of Disjoint Diameter-Equilateral, Diameter-Adjacent, and Isosceles Fiber Families (`∀ d R_adj R_iso`):** -/
theorem card_diameter_fiber_cap_union
    (d : ℝ) (R_adj R_iso : Finset ℝ)
    (hadj_ne : ∀ r ∈ R_adj, r ≠ d)
    (hiso_ne : ∀ r ∈ R_iso, r ≠ d) :
    (insert (d, d) ((R_adj.image (fun r => (r, d))) ∪
      (R_adj.image (fun r => (d, r))) ∪
      (R_iso.image (fun r => (r, r))))).card =
      1 + 2 * R_adj.card + R_iso.card := by
  let Q1 := R_adj.image (fun r => (r, d))
  let Q2 := R_adj.image (fun r => (d, r))
  let Q3 := R_iso.image (fun r => (r, r))
  have hQ1_card : Q1.card = R_adj.card :=
    Finset.card_image_of_injective _ (fun x y h => (Prod.ext_iff.mp h).1)
  have hQ2_card : Q2.card = R_adj.card :=
    Finset.card_image_of_injective _ (fun x y h => (Prod.ext_iff.mp h).2)
  have hQ3_card : Q3.card = R_iso.card :=
    Finset.card_image_of_injective _ (fun x y h => (Prod.ext_iff.mp h).1)
  have hdisj12 : Disjoint Q1 Q2 := by
    refine Finset.disjoint_left.mpr (fun q hq1 hq2 => ?_)
    obtain ⟨r1, hr1, rfl⟩ := Finset.mem_image.mp hq1
    obtain ⟨r2, _, heq⟩ := Finset.mem_image.mp hq2
    exact hadj_ne r1 hr1 (Prod.ext_iff.mp heq).1.symm
  have hdisj12_3 : Disjoint (Q1 ∪ Q2) Q3 := by
    refine Finset.disjoint_left.mpr (fun q hq12 hq3 => ?_)
    obtain ⟨r3, hr3, rfl⟩ := Finset.mem_image.mp hq3
    rcases Finset.mem_union.mp hq12 with hq1 | hq2
    · obtain ⟨r1, _, heq⟩ := Finset.mem_image.mp hq1
      exact hiso_ne r3 hr3 (Prod.ext_iff.mp heq).2.symm
    · obtain ⟨r2, _, heq⟩ := Finset.mem_image.mp hq2
      exact hiso_ne r3 hr3 (Prod.ext_iff.mp heq).1.symm
  have hnot_dd : (d, d) ∉ (Q1 ∪ Q2) ∪ Q3 := by
    intro hmem
    rcases Finset.mem_union.mp hmem with h12 | h3
    · rcases Finset.mem_union.mp h12 with h1 | h2
      · obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp h1
        exact hadj_ne r hr (Prod.ext_iff.mp heq).1
      · obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp h2
        exact hadj_ne r hr (Prod.ext_iff.mp heq).2
    · obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp h3
      exact hiso_ne r hr (Prod.ext_iff.mp heq).1
  change (insert (d, d) ((Q1 ∪ Q2) ∪ Q3)).card = 1 + 2 * R_adj.card + R_iso.card
  rw [Finset.card_insert_of_notMem hnot_dd,
    Finset.card_union_of_disjoint hdisj12_3,
    Finset.card_union_of_disjoint hdisj12,
    hQ1_card, hQ2_card, hQ3_card]
  omega

/-- **Master Diameter-Equilateral + Diameter-Adjacent (`3 * r^2 ≥ d^2`) + Isosceles Fiber Sum Bound (`∀ S a b R_adj R_iso`):**
for any diameter pair `(a, b)` of `S`, any `R_adj ⊆ (distanceSet S).erase (dist a b)` with
`∀ r ∈ R_adj, dist a b ^ 2 ≤ 3 * r ^ 2`, and any `R_iso ⊆ (distanceSet S).erase (dist a b)` with
`∀ r ∈ R_iso, 4 * r ^ 2 ≤ dist a b ^ 2 ∨ 2 * dist a b ^ 2 < 4 * r ^ 2`, we have
`S.card + 2 * R_adj.card + R_iso.card ≤ 2 * (distinctDistances S)^2 + 1`. -/
theorem card_add_two_mul_adj_add_iso_le_two_mul_distinctDistances_sq_add_one
    (S : Finset Plane) (a b : Plane) (R_adj R_iso : Finset ℝ)
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ dist a b)
    (hR_adj_sub : R_adj ⊆ (Minimizer91.distanceSet S).erase (dist a b))
    (hR_adj_cap : ∀ r ∈ R_adj, dist a b ^ 2 ≤ 3 * r ^ 2)
    (hR_iso_sub : R_iso ⊆ (Minimizer91.distanceSet S).erase (dist a b))
    (hR_iso_cap : ∀ r ∈ R_iso, 4 * r ^ 2 ≤ dist a b ^ 2 ∨ 2 * dist a b ^ 2 < 4 * r ^ 2) :
    S.card + 2 * R_adj.card + R_iso.card ≤ 2 * (Minimizer91.distinctDistances S) ^ 2 + 1 := by
  let d := dist a b
  let Q := insert (d, d) ((R_adj.image (fun r => (r, d))) ∪
    (R_adj.image (fun r => (d, r))) ∪
    (R_iso.image (fun r => (r, r))))
  have hd_mem : d ∈ Minimizer91.distanceSet S :=
    (Erdos91.DistanceErasure.mem_distanceSet _ _).mpr ⟨a, ha, b, hb, hab, rfl⟩
  have hadj_ne : ∀ r ∈ R_adj, r ≠ d := fun r hr => (Finset.mem_erase.mp (hR_adj_sub hr)).1
  have hiso_ne : ∀ r ∈ R_iso, r ≠ d := fun r hr => (Finset.mem_erase.mp (hR_iso_sub hr)).1
  have hQ_card : Q.card = 1 + 2 * R_adj.card + R_iso.card :=
    card_diameter_fiber_cap_union d R_adj R_iso hadj_ne hiso_ne
  have hQ_sub : Q ⊆ Minimizer91.distanceSet S ×ˢ Minimizer91.distanceSet S := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq'
    · exact Finset.mem_product.mpr ⟨hd_mem, hd_mem⟩
    · rcases Finset.mem_union.mp hq' with h12 | h3
      · rcases Finset.mem_union.mp h12 with h1 | h2
        · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp h1
          exact Finset.mem_product.mpr ⟨Finset.mem_of_mem_erase (hR_adj_sub hr), hd_mem⟩
        · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp h2
          exact Finset.mem_product.mpr ⟨hd_mem, Finset.mem_of_mem_erase (hR_adj_sub hr)⟩
      · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp h3
        have hr_mem := Finset.mem_of_mem_erase (hR_iso_sub hr)
        exact Finset.mem_product.mpr ⟨hr_mem, hr_mem⟩
  have hQ_cap : ∀ q ∈ Q, (S.filter (fun v => dist v a = q.1 ∧ dist v b = q.2)).card ≤ 1 := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq'
    · exact diameter_equilateral_fiber_card_le_one S a b ha hb hab hdiam
    · rcases Finset.mem_union.mp hq' with h12 | h3
      · rcases Finset.mem_union.mp h12 with h1 | h2
        · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp h1
          exact (diameter_adjacent_fiber_card_le_one_of_diam_sq_le_three_mul_sq
            S a b r ha hb hab hdiam (hR_adj_cap r hr)).1
        · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp h2
          exact (diameter_adjacent_fiber_card_le_one_of_diam_sq_le_three_mul_sq
            S a b r ha hb hab hdiam (hR_adj_cap r hr)).2
      · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp h3
        exact isosceles_diameter_fiber_card_le_one S a b r hab hdiam (hR_iso_cap r hr)
  have hbnd := two_center_fiber_defect_sum_bound S a b Q ha hb hab hQ_sub hQ_cap
  omega

/-- **Universal 4-Point Cayley–Menger Incompatibility of Diameter-Equilateral and Two Diameter-Adjacent Completions (`∀ a b v0 w1 w2 r`):** -/
theorem no_diameter_equilateral_and_two_chord_completions
    {a b v0 w1 w2 : Plane} {r : ℝ} (hab : a ≠ b) (hw12 : w1 ≠ w2) (hr : 0 < r)
    (hv0a : dist v0 a = dist a b) (hv0b : dist v0 b = dist a b)
    (hw1a : dist w1 a = dist a b) (hw1b : dist w1 b = r)
    (hw2a : dist w2 a = dist a b) (hw2b : dist w2 b = r)
    (hdiam1 : dist v0 w1 ≤ dist a b) (hdiam2 : dist v0 w2 ≤ dist a b)
    (hdiam_r : r ≤ dist a b) : False := by
  have hc1 := cmPoly_dist_sq_eq_zero a b v0 w1
  have hc2 := cmPoly_dist_sq_eq_zero a b v0 w2
  have hc3 := cmPoly_dist_sq_eq_zero a b w1 w2
  have hc4 := cmPoly_dist_sq_eq_zero b v0 w1 w2
  rw [dist_comm a v0, dist_comm a w1, dist_comm b v0, dist_comm b w1,
      hv0a, hv0b, hw1a, hw1b] at hc1
  rw [dist_comm a v0, dist_comm a w2, dist_comm b v0, dist_comm b w2,
      hv0a, hv0b, hw2a, hw2b] at hc2
  rw [dist_comm a w1, dist_comm a w2, dist_comm b w1, dist_comm b w2,
      hw1a, hw2a, hw1b, hw2b] at hc3
  rw [dist_comm b v0, dist_comm b w1, dist_comm b w2,
      hv0b, hw1b, hw2b] at hc4
  have hab_pos : 0 < dist a b ^ 2 := sq_pos_of_pos (dist_pos.mpr hab)
  have hr_pos : 0 < r ^ 2 := sq_pos_of_pos hr
  have hu_pos : 0 < dist w1 w2 ^ 2 := sq_pos_of_pos (dist_pos.mpr hw12)
  have ht1_le : dist v0 w1 ^ 2 ≤ dist a b ^ 2 := pow_le_pow_left₀ dist_nonneg hdiam1 2
  have ht2_le : dist v0 w2 ^ 2 ≤ dist a b ^ 2 := pow_le_pow_left₀ dist_nonneg hdiam2 2
  have hr_le : r ^ 2 ≤ dist a b ^ 2 := pow_le_pow_left₀ (le_of_lt hr) hdiam_r 2
  by_cases hteq : dist v0 w1 ^ 2 = dist v0 w2 ^ 2
  · rw [← hteq] at hc4
    have hid : dist w1 w2 ^ 2 * cmPoly (dist a b ^ 2) (dist a b ^ 2) (dist a b ^ 2)
          (dist a b ^ 2) (r ^ 2) (dist v0 w1 ^ 2) +
        dist a b ^ 2 * cmPoly (dist a b ^ 2) (dist a b ^ 2) (dist a b ^ 2)
          (r ^ 2) (r ^ 2) (dist w1 w2 ^ 2) -
        dist a b ^ 2 * cmPoly (dist a b ^ 2) (r ^ 2) (r ^ 2)
          (dist v0 w1 ^ 2) (dist v0 w1 ^ 2) (dist w1 w2 ^ 2) =
        (dist a b ^ 2 * r ^ 2 * dist w1 w2 ^ 2) *
          (4 * dist a b ^ 2 - r ^ 2 - dist v0 w1 ^ 2) := by
      unfold cmPoly; ring
    rw [hc1, hc3, hc4] at hid
    have hprod_pos : 0 < dist a b ^ 2 * r ^ 2 * dist w1 w2 ^ 2 :=
      mul_pos (mul_pos hab_pos hr_pos) hu_pos
    nlinarith
  · have hid : cmPoly (dist a b ^ 2) (dist a b ^ 2) (dist a b ^ 2)
          (dist a b ^ 2) (r ^ 2) (dist v0 w1 ^ 2) -
        cmPoly (dist a b ^ 2) (dist a b ^ 2) (dist a b ^ 2)
          (dist a b ^ 2) (r ^ 2) (dist v0 w2 ^ 2) =
        - dist a b ^ 2 * (dist v0 w1 ^ 2 - dist v0 w2 ^ 2) *
          (dist v0 w1 ^ 2 + dist v0 w2 ^ 2 - 2 * dist a b ^ 2 - r ^ 2) := by
      unfold cmPoly; ring
    rw [hc1, hc2] at hid
    have hdiff_sq : 0 < (dist v0 w1 ^ 2 - dist v0 w2 ^ 2) ^ 2 :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr hteq)
    have hprod_pos : 0 < dist a b ^ 2 * (dist v0 w1 ^ 2 - dist v0 w2 ^ 2) ^ 2 :=
      mul_pos hab_pos hdiff_sq
    nlinarith

/-- **Unconditional `S.card ≤ 2 * distinctDistances(S)^2` for `4 ≤ S.card` (`∀ S`):**
for every planar configuration `S` of `4 ≤ S.card` points, combining `(d, d)` and `(d, r)`
via `no_diameter_equilateral_and_two_chord_completions` proves `S.card ≤ 2 * distinctDistances(S)^2`
(and `S.card ≤ 18` whenever `distinctDistances S ≤ 3`). -/
theorem card_le_two_mul_distinctDistances_sq_of_four_le
    (S : Finset Plane) (hS : 4 ≤ S.card) :
    S.card ≤ 2 * (Minimizer91.distinctDistances S) ^ 2 ∧
      (Minimizer91.distinctDistances S ≤ 3 → S.card ≤ 18) := by
  have hmain : S.card ≤ 2 * (Minimizer91.distinctDistances S) ^ 2 := by
    have hd2 : 2 ≤ Minimizer91.distinctDistances S := by
      by_contra hlt; have hle3 := Erdos91.SmallCasesAndSquareBarrier.equidistant_card_le_three S (by omega); omega
    obtain ⟨a, ha, b, hb, hab, hdiam⟩ := exists_diameter_pair S (by omega)
    let B := (S.erase a).erase b
    have hbErase : b ∈ S.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
    have hBcard : B.card = S.card - 2 := by
      dsimp [B]; rw [Finset.card_erase_of_mem hbErase, Finset.card_erase_of_mem ha]; omega
    have hdab_mem : dist a b ∈ Minimizer91.distanceSet S :=
      (Erdos91.DistanceErasure.mem_distanceSet _ _).mpr ⟨a, ha, b, hb, hab, rfl⟩
    have her_card : 0 < ((Minimizer91.distanceSet S).erase (dist a b)).card := by
      have h1 := Finset.card_erase_add_one hdab_mem
      change ((Minimizer91.distanceSet S).erase (dist a b)).card + 1 = Minimizer91.distinctDistances S at h1
      omega
    obtain ⟨r, hr_er⟩ := Finset.card_pos.mp her_card
    obtain ⟨hr_ne, hr_mem⟩ := Finset.mem_erase.mp hr_er
    obtain ⟨x0, hx0, y0, hy0, hx0y0, hxy_r⟩ := (Erdos91.DistanceErasure.mem_distanceSet _ _).mp hr_mem
    have hr_pos : 0 < r := hxy_r ▸ dist_pos.mpr hx0y0
    have hr_le : r ≤ dist a b := hxy_r ▸ hdiam x0 hx0 y0 hy0
    let pairMap : Plane → ℝ × ℝ := fun v => (dist v a, dist v b)
    let P := Minimizer91.distanceSet S ×ˢ Minimizer91.distanceSet S
    have hPcard : P.card = (Minimizer91.distinctDistances S) ^ 2 := by
      dsimp [P, Minimizer91.distinctDistances]; rw [Finset.card_product]; ring
    let p0 : ℝ × ℝ := (dist a b, dist a b)
    let p1 : ℝ × ℝ := (dist a b, r)
    have hp0_mem : p0 ∈ P := Finset.mem_product.mpr ⟨hdab_mem, hdab_mem⟩
    have hp1_mem : p1 ∈ P := Finset.mem_product.mpr ⟨hdab_mem, hr_mem⟩
    have hp10_ne : p1 ≠ p0 := fun h => hr_ne (Prod.ext_iff.mp h).2
    have hp1_er : p1 ∈ P.erase p0 := Finset.mem_erase.mpr ⟨hp10_ne, hp1_mem⟩
    have hmap_mem : ∀ v ∈ B, pairMap v ∈ P := by
      intro v hv
      obtain ⟨hvb, hva⟩ := Finset.mem_erase.mp hv
      obtain ⟨hva', hvS⟩ := Finset.mem_erase.mp hva
      exact Finset.mem_product.mpr
        ⟨(Erdos91.DistanceErasure.mem_distanceSet _ _).mpr ⟨v, hvS, a, ha, hva', rfl⟩,
         (Erdos91.DistanceErasure.mem_distanceSet _ _).mpr ⟨v, hvS, b, hb, hvb, rfl⟩⟩
    let B0 := B.filter (fun v => pairMap v = p0)
    let B1 := B.filter (fun v => pairMap v = p1)
    let B01 := B.filter (fun v => pairMap v = p0 ∨ pairMap v = p1)
    let B2 := B.filter (fun v => ¬ (pairMap v = p0 ∨ pairMap v = p1))
    have hpart : B01.card + B2.card = B.card :=
      Finset.card_filter_add_card_filter_not (s := B) (p := fun v => pairMap v = p0 ∨ pairMap v = p1)
    have hB01_sub : B01 ⊆ B0 ∪ B1 := by
      intro v hv; obtain ⟨hvB, h01⟩ := Finset.mem_filter.mp hv; rw [Finset.mem_union]
      rcases h01 with h0 | h1
      · exact Or.inl (Finset.mem_filter.mpr ⟨hvB, h0⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨hvB, h1⟩)
    have hB01_union : B01.card ≤ B0.card + B1.card :=
      (Finset.card_le_card hB01_sub).trans (Finset.card_union_le _ _)
    have hB0_le : B0.card ≤ 1 := by
      have hsub : B0 ⊆ S.filter (fun v => dist v a = dist a b ∧ dist v b = dist a b) := by
        intro v hv; obtain ⟨hvB, hp⟩ := Finset.mem_filter.mp hv
        exact Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hvB),
          (Prod.ext_iff.mp hp).1, (Prod.ext_iff.mp hp).2⟩
      exact (Finset.card_le_card hsub).trans (Erdos91.ThreeDistanceLevelAndDiameterFiberBounds.diameter_equilateral_fiber_card_le_one S a b ha hb hab hdiam)
    have hB1_le : B1.card ≤ 2 := by
      apply CircleFibers91.two_centers_card B1 a b (dist a b) r hab
      · intro v hv; exact (Prod.ext_iff.mp (Finset.mem_filter.mp hv).2).1
      · intro v hv; exact (Prod.ext_iff.mp (Finset.mem_filter.mp hv).2).2
    have hB01_le : B01.card ≤ 2 := by
      by_contra hgt
      obtain ⟨v0, hv0⟩ := Finset.card_pos.mp (by omega : 0 < B0.card)
      obtain ⟨w1, hw1, w2, hw2, hw12⟩ := Finset.one_lt_card.mp (by omega : 1 < B1.card)
      obtain ⟨hv0B, hp0_v0⟩ := Finset.mem_filter.mp hv0
      obtain ⟨hw1B, hp1_w1⟩ := Finset.mem_filter.mp hw1
      obtain ⟨hw2B, hp1_w2⟩ := Finset.mem_filter.mp hw2
      injection hp0_v0 with hv0a hv0b; injection hp1_w1 with hw1a hw1b; injection hp1_w2 with hw2a hw2b
      have hv0S : v0 ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hv0B)
      have hw1S : w1 ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw1B)
      have hw2S : w2 ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw2B)
      exact no_diameter_equilateral_and_two_chord_completions hab hw12 hr_pos
        hv0a hv0b hw1a hw1b hw2a hw2b (hdiam v0 hv0S w1 hw1S) (hdiam v0 hv0S w2 hw2S) hr_le
    have hB2_maps : ∀ v ∈ B2, pairMap v ∈ (P.erase p0).erase p1 := by
      intro v hv; obtain ⟨hvB, hnot⟩ := Finset.mem_filter.mp hv; rw [not_or] at hnot
      exact Finset.mem_erase.mpr ⟨hnot.2, Finset.mem_erase.mpr ⟨hnot.1, hmap_mem v hvB⟩⟩
    have hB2_le : B2.card ≤ 2 * ((P.erase p0).erase p1).card := by
      apply Finset.card_le_mul_card_image_of_maps_to hB2_maps
      intro q _
      have hsub : B2.filter (fun v => pairMap v = q) ⊆
          B.filter (fun v => dist v a = q.1 ∧ dist v b = q.2) := by
        intro v hv; obtain ⟨hv2, hvq⟩ := Finset.mem_filter.mp hv
        rw [← hvq]; exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv2).1, rfl, rfl⟩
      have h2 := CircleFibers91.two_centers_card
        (B.filter (fun v => dist v a = q.1 ∧ dist v b = q.2)) a b q.1 q.2 hab
        (fun v hv => (Finset.mem_filter.mp hv).2.1) (fun v hv => (Finset.mem_filter.mp hv).2.2)
      exact (Finset.card_le_card hsub).trans h2
    have hPer1 : ((P.erase p0).erase p1).card + 1 = (P.erase p0).card := Finset.card_erase_add_one hp1_er
    have hPer0 : (P.erase p0).card + 1 = P.card := Finset.card_erase_add_one hp0_mem
    rw [hPcard] at hPer0; omega
  refine ⟨hmain, fun h3 => ?_⟩
  have hsq : (Minimizer91.distinctDistances S) ^ 2 ≤ 3 ^ 2 := Nat.pow_le_pow_left h3 2
  omega

/-- **Sharpened Quadratic Lower Bound `n ≤ 2 * d(n)^2` for `n ≥ 4` and `K ≤ d(2*(K-1)^2 + 1)` (`∀ n ≥ 4, ∀ K ≥ 3`):** -/
theorem minimal_quadratic_lower_bound_of_four_le (n K : ℕ) (hn : 4 ≤ n) (hK : 3 ≤ K) :
    n ≤ 2 * (Minimizer91.minimalDistinctDistances n) ^ 2 ∧
      K ≤ Minimizer91.minimalDistinctDistances (2 * (K - 1) ^ 2 + 1) := by
  obtain ⟨S, hS⟩ := Minimizer91.exists_optimal n
  have hS4 : 4 ≤ S.card := by rw [hS.1]; exact hn
  have h1 := (card_le_two_mul_distinctDistances_sq_of_four_le S hS4).1
  rw [hS.1, hS.2] at h1
  refine ⟨h1, ?_⟩
  have h4 : 4 ≤ 2 * (K - 1) ^ 2 + 1 := by
    have : 2 ≤ K - 1 := by omega
    have : 4 ≤ (K - 1) ^ 2 := by nlinarith
    omega
  obtain ⟨S2, hS2⟩ := Minimizer91.exists_optimal (2 * (K - 1) ^ 2 + 1)
  have h2 := (card_le_two_mul_distinctDistances_sq_of_four_le S2 (by rw [hS2.1]; exact h4)).1
  rw [hS2.1, hS2.2] at h2
  by_contra hlt
  have hle : Minimizer91.minimalDistinctDistances (2 * (K - 1) ^ 2 + 1) ≤ K - 1 := by omega
  have hsq : (Minimizer91.minimalDistinctDistances (2 * (K - 1) ^ 2 + 1)) ^ 2 ≤ (K - 1) ^ 2 :=
    Nat.pow_le_pow_left hle 2
  omega

end Erdos91.SharpenedTwoCenterFiberSumBounds


namespace Erdos91.TruncatedTriangleAndHexagonMultiDeletionFamilies

/-- The 3 corner coordinates `{(0, 0), (0, 5), (5, 0)}` of `T_6 = hexCoords 6 0 5`. -/
def triPatch6Corner3 : Finset (ℕ × ℕ) :=
  {(0, 0), (0, 5), (5, 0)}

/-- The 18-point corner-truncated equilateral triangle `hexCoords 6 0 5 \ {(0, 0), (0, 5), (5, 0)}`. -/
def truncTri18Coords : Finset (ℕ × ℕ) :=
  hexCoords 6 0 5 \ triPatch6Corner3

/-- Irreducible 5-point distance-complete coordinate core `{(0, 2), (0, 3), (0, 4), (3, 1), (4, 2)}`
of `H_2 = hexCoords 5 2 4`. -/
def hex2Core5Coords : Finset (ℕ × ℕ) :=
  {(0, 2), (0, 3), (0, 4), (3, 1), (4, 2)}

/-- Planar 5-point distance-complete core `hex2Core5 = hex2Core5Coords.image triPoint` of `hexSet 5 2 4`. -/
noncomputable def hex2Core5 : Finset Plane :=
  hex2Core5Coords.image triPoint

/-- **Exact 18-Point Corner-Truncated `T_6` Identity and `hexSet 5 2 4` 5-Point Core Theorem (`∀ p`):**
`truncTri18Coords = hexCoords 5 1 4` (`truncTri18Coords.card = 18`), every `p ∈ hex2Core5Coords`
maps into `hexSet 5 2 4`, `hex2Core5.card = 5`, `IsDistanceCompleteCore hex2Core5 (hexSet 5 2 4)`,
`distanceSet (hexSet 5 2 4) = (triUtp 4).image triNorm`, `distinctDistances (hexSet 5 2 4) = 8`,
and `d(17) ≤ d(18) ≤ d(19) ≤ 8`. -/
theorem card_and_distanceSet_hexSet_5_2_4_and_core5
    (p : ℕ × ℕ) (hp : p ∈ hex2Core5Coords) :
    truncTri18Coords = hexCoords 5 1 4 ∧
      truncTri18Coords.card = 18 ∧
      triPoint p ∈ hexSet 5 2 4 ∧
      (hexSet 5 2 4).card = 19 ∧
      hex2Core5.card = 5 ∧
      IsDistanceCompleteCore hex2Core5 (hexSet 5 2 4) ∧
      Erdos91.DistanceErasure.distanceSet (hexSet 5 2 4) = (triUtp 4).image triNorm ∧
      Minimizer91.distinctDistances (hexSet 5 2 4) = 8 ∧
      Minimizer91.minimalDistinctDistances 19 ≤ 8 ∧
      Minimizer91.minimalDistinctDistances 18 ≤ 8 ∧
      Minimizer91.minimalDistinctDistances 17 ≤ 8 := by
  have htrunc_eq : truncTri18Coords = hexCoords 5 1 4 := by decide
  have htrunc_card : truncTri18Coords.card = 18 := rfl
  have hsub_coords : hex2Core5Coords ⊆ hexCoords 5 2 4 := by decide
  have hsub_core : hex2Core5 ⊆ hexSet 5 2 4 := Finset.image_subset_image hsub_coords
  have hcard19 : (hexSet 5 2 4).card = 19 :=
    Erdos91.ExactHexagonDistanceCountsR1To18.card_hexSet_regular_2
  have hcard5 : hex2Core5.card = 5 := by
    unfold hex2Core5
    rw [Finset.card_image_of_injective _ triPoint_injective]
    rfl
  have hDS_hex : Erdos91.DistanceErasure.distanceSet (hexSet 5 2 4) = (triUtp 4).image triNorm :=
    distanceSet_hexSet_regular_eq 2
  have hdd8 : Minimizer91.distinctDistances (hexSet 5 2 4) = 8 :=
    Erdos91.ExactHexagonDistanceCountsR1To18.distinctDistances_hexSet_regular_2
  have h_edge : ∀ a b : ℕ × ℕ, a ∈ hex2Core5Coords → b ∈ hex2Core5Coords → a ≠ b →
      triNorm (triOffset a b) ∈ Erdos91.DistanceErasure.distanceSet hex2Core5 := by
    intro a b ha hb hab
    exact (Erdos91.DistanceErasure.mem_distanceSet _ _).mpr
      ⟨triPoint a, Finset.mem_image_of_mem triPoint ha,
       triPoint b, Finset.mem_image_of_mem triPoint hb,
       fun h => hab (triPoint_injective h), dist_triPoint_eq a b⟩
  have hlower : (triUtp 4).image triNorm ⊆ Erdos91.DistanceErasure.distanceSet hex2Core5 := by
    intro r hr
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
    have hu_all : ∀ v ∈ triUtp 4,
        v = (0, 1) ∨ v = (0, 2) ∨ v = (0, 3) ∨ v = (0, 4) ∨
        v = (1, 1) ∨ v = (1, 2) ∨ v = (1, 3) ∨ v = (2, 2) := by decide
    rcases hu_all u hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h_edge (0, 2) (0, 3) (by decide) (by decide) (by decide)
    · exact h_edge (0, 2) (0, 4) (by decide) (by decide) (by decide)
    · exact h_edge (0, 4) (3, 1) (by decide) (by decide) (by decide)
    · exact h_edge (0, 2) (4, 2) (by decide) (by decide) (by decide)
    · exact h_edge (3, 1) (4, 2) (by decide) (by decide) (by decide)
    · exact h_edge (0, 2) (3, 1) (by decide) (by decide) (by decide)
    · exact h_edge (0, 3) (4, 2) (by decide) (by decide) (by decide)
    · exact h_edge (0, 4) (4, 2) (by decide) (by decide) (by decide)
  have hDS_core : Erdos91.DistanceErasure.distanceSet hex2Core5 = (triUtp 4).image triNorm :=
    Finset.Subset.antisymm ((distanceSet_mono hsub_core).trans hDS_hex.le) hlower
  have hCore : IsDistanceCompleteCore hex2Core5 (hexSet 5 2 4) :=
    ⟨hsub_core, hDS_core.trans hDS_hex.symm⟩
  have hd19 : Minimizer91.minimalDistinctDistances 19 ≤ 8 := minimalDistinctDistances_19_le_8
  have hd18 : Minimizer91.minimalDistinctDistances 18 ≤ 8 :=
    (MinimumMonotone91.minimum_monotone (by omega : 18 ≤ 19)).trans hd19
  have hd17 : Minimizer91.minimalDistinctDistances 17 ≤ 8 :=
    (MinimumMonotone91.minimum_monotone (by omega : 17 ≤ 18)).trans hd18
  exact ⟨htrunc_eq, htrunc_card, hsub_core (Finset.mem_image_of_mem triPoint hp),
    hcard19, hcard5, hCore, hDS_hex, hdd8, hd19, hd18, hd17⟩

/-- **Certified 4-Configuration (`n = 18`), 21-Configuration (`n = 17`), and 56-Configuration (`n = 16`) 8-Distance Families on `H_2 = hexSet 5 2 4` over `hex2Core5` (`∀ K₁₈ ≤ 4, ∀ K₁₇ ≤ 21, ∀ K₁₆ ≤ 56`):** -/
theorem hexSet_5_2_4_core5_eighteen_seventeen_sixteen_multi_deletion_families
    (K₁₈ K₁₇ K₁₆ : ℕ) (hK₁₈ : K₁₈ ≤ 4) (hK₁₇ : K₁₇ ≤ 21) (hK₁₆ : K₁₆ ≤ 56) :
    ((∃ G₁₈ : Finset (Finset Plane),
      G₁₈.card = K₁₈ ∧
      (∀ A ∈ G₁₈, A.card = 18 ∧
        Erdos91.DistanceErasure.distanceSet A = (triUtp 4).image triNorm ∧
        Minimizer91.distinctDistances A = 8) ∧
      (∀ A ∈ G₁₈, ∀ B ∈ G₁₈, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
      (8 ≤ Minimizer91.minimalDistinctDistances 18 → HasAtLeastKNonsimilarMinimizers K₁₈ 18)) ∧
    ((∃ G₁₇ : Finset (Finset Plane),
      G₁₇.card = K₁₇ ∧
      (∀ A ∈ G₁₇, A.card = 17 ∧
        Erdos91.DistanceErasure.distanceSet A = (triUtp 4).image triNorm ∧
        Minimizer91.distinctDistances A = 8) ∧
      (∀ A ∈ G₁₇, ∀ B ∈ G₁₇, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
      (8 ≤ Minimizer91.minimalDistinctDistances 17 → HasAtLeastKNonsimilarMinimizers K₁₇ 17)) ∧
    ((∃ G₁₆ : Finset (Finset Plane),
      G₁₆.card = K₁₆ ∧
      (∀ A ∈ G₁₆, A.card = 16 ∧
        Erdos91.DistanceErasure.distanceSet A = (triUtp 4).image triNorm ∧
        Minimizer91.distinctDistances A = 8) ∧
      (∀ A ∈ G₁₆, ∀ B ∈ G₁₆, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
      (8 ≤ Minimizer91.minimalDistinctDistances 16 → HasAtLeastKNonsimilarMinimizers K₁₆ 16)) := by
  obtain ⟨_, _, _, _, _, hCore, hDS8, hdd8, _, _, _⟩ :=
    card_and_distanceSet_hexSet_5_2_4_and_core5 (0, 2) (by decide)
  have hcard19_c : (hexCoords 5 2 4).card = 19 := rfl
  have hdiam_c : ∀ p ∈ hexCoords 5 2 4, ∀ q ∈ hexCoords 5 2 4,
      triNormSq (triOffset p q) ≤ triNormSq (triOffset (0, 2) (4, 2)) := by decide
  have hres1 := triCoord_powersetCard_multi_deletion_family
    (hexCoords 5 2 4) hex2Core5Coords (0, 2) (4, 2) 1 K₁₈
    hCore (by decide) (by decide) (by decide) hdiam_c (hK₁₈.trans_eq rfl)
  have hres2 := triCoord_powersetCard_multi_deletion_family
    (hexCoords 5 2 4) hex2Core5Coords (0, 2) (4, 2) 2 K₁₇
    hCore (by decide) (by decide) (by decide) hdiam_c (hK₁₇.trans_eq rfl)
  have hres3 := triCoord_powersetCard_multi_deletion_family
    (hexCoords 5 2 4) hex2Core5Coords (0, 2) (4, 2) 3 K₁₆
    hCore (by decide) (by decide) (by decide) hdiam_c (hK₁₆.trans_eq rfl)
  change IsDistanceCompleteCore (hex2Core5Coords.image triPoint)
    ((hexCoords 5 2 4).image triPoint) at hCore
  change Erdos91.DistanceErasure.distanceSet ((hexCoords 5 2 4).image triPoint) =
    (triUtp 4).image triNorm at hDS8
  change Minimizer91.distinctDistances ((hexCoords 5 2 4).image triPoint) = 8 at hdd8
  rw [hcard19_c, hDS8, hdd8] at hres1 hres2 hres3
  exact ⟨hres1, hres2, hres3⟩

/-- The 21-point 9-distance corner-truncated hexagonal coordinate patch
`insert (4, 4) (hexCoords 6 3 4 \ {(0, 3), (0, 5), (3, 0), (5, 0)})`. -/
def hex21NineDistCoords : Finset (ℕ × ℕ) :=
  insert (4, 4) (hexCoords 6 3 4 \ {(0, 3), (0, 5), (3, 0), (5, 0)})

/-- Irreducible 5-point distance-complete coordinate core `{(0, 4), (1, 2), (1, 3), (3, 4), (5, 2)}`
of `hex21NineDistCoords`. -/
def hex21NineDistCore5Coords : Finset (ℕ × ℕ) :=
  {(0, 4), (1, 2), (1, 3), (3, 4), (5, 2)}

/-- The 9-element triangular-lattice offset set `insert (2, 3) (triUtp 4)`
with squared norms `{4, 12, 16, 28, 36, 48, 52, 64, 76}`. -/
def hex21Utp9 : Finset (ℕ × ℕ) :=
  insert (2, 3) (triUtp 4)

/-- Planar 21-point 9-distance configuration `hex21NineDist = hex21NineDistCoords.image triPoint`. -/
noncomputable def hex21NineDist : Finset Plane :=
  hex21NineDistCoords.image triPoint

/-- Planar 5-point distance-complete core `hex21NineDistCore5 = hex21NineDistCore5Coords.image triPoint`. -/
noncomputable def hex21NineDistCore5 : Finset Plane :=
  hex21NineDistCore5Coords.image triPoint

/-- **Exact 21-Point 9-Distance Patch & 5-Point Core Theorem (`d(18) ≤ d(19) ≤ d(20) ≤ d(21) ≤ 9`, `∀ p`):** -/
theorem card_and_distanceSet_hex21NineDist_and_core5
    (p : ℕ × ℕ) (hp : p ∈ hex21NineDistCore5Coords) :
    triPoint p ∈ hex21NineDist ∧
      hex21NineDist.card = 21 ∧
      hex21NineDistCore5.card = 5 ∧
      IsDistanceCompleteCore hex21NineDistCore5 hex21NineDist ∧
      Erdos91.DistanceErasure.distanceSet hex21NineDist = hex21Utp9.image triNorm ∧
      Minimizer91.distinctDistances hex21NineDist = 9 ∧
      Minimizer91.minimalDistinctDistances 21 ≤ 9 ∧
      Minimizer91.minimalDistinctDistances 20 ≤ 9 ∧
      Minimizer91.minimalDistinctDistances 19 ≤ 9 ∧
      Minimizer91.minimalDistinctDistances 18 ≤ 9 := by
  have hsub_coords : hex21NineDistCore5Coords ⊆ hex21NineDistCoords := by decide
  have hsub_core : hex21NineDistCore5 ⊆ hex21NineDist := Finset.image_subset_image hsub_coords
  have hcard21 : hex21NineDist.card = 21 := by
    unfold hex21NineDist
    rw [Finset.card_image_of_injective _ triPoint_injective]
    rfl
  have hcard5 : hex21NineDistCore5.card = 5 := by
    unfold hex21NineDistCore5
    rw [Finset.card_image_of_injective _ triPoint_injective]
    rfl
  have h_off : ∀ a ∈ hex21NineDistCoords, ∀ b ∈ hex21NineDistCoords, a ≠ b →
      triOffset a b ∈ hex21Utp9 := by decide
  have hupper : Erdos91.DistanceErasure.distanceSet hex21NineDist ⊆ hex21Utp9.image triNorm := by
    intro r hr
    obtain ⟨x, hx, y, hy, hxy, rfl⟩ := (Erdos91.DistanceErasure.mem_distanceSet _ _).mp hr
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have hab : a ≠ b := fun h => hxy (congrArg triPoint h)
    rw [dist_triPoint_eq a b]
    exact Finset.mem_image_of_mem triNorm (h_off a ha b hb hab)
  have h_edge : ∀ a b : ℕ × ℕ, a ∈ hex21NineDistCore5Coords → b ∈ hex21NineDistCore5Coords → a ≠ b →
      triNorm (triOffset a b) ∈ Erdos91.DistanceErasure.distanceSet hex21NineDistCore5 := by
    intro a b ha hb hab
    exact (Erdos91.DistanceErasure.mem_distanceSet _ _).mpr
      ⟨triPoint a, Finset.mem_image_of_mem triPoint ha,
       triPoint b, Finset.mem_image_of_mem triPoint hb,
       fun h => hab (triPoint_injective h), dist_triPoint_eq a b⟩
  have hlower : hex21Utp9.image triNorm ⊆ Erdos91.DistanceErasure.distanceSet hex21NineDistCore5 := by
    intro r hr
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
    have hu_all : ∀ v ∈ hex21Utp9,
        v = (0, 1) ∨ v = (0, 2) ∨ v = (0, 3) ∨ v = (0, 4) ∨
        v = (1, 1) ∨ v = (1, 2) ∨ v = (1, 3) ∨ v = (2, 2) ∨ v = (2, 3) := by decide
    rcases hu_all u hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h_edge (0, 4) (1, 3) (by decide) (by decide) (by decide)
    · exact h_edge (3, 4) (5, 2) (by decide) (by decide) (by decide)
    · exact h_edge (0, 4) (3, 4) (by decide) (by decide) (by decide)
    · exact h_edge (1, 2) (5, 2) (by decide) (by decide) (by decide)
    · exact h_edge (0, 4) (1, 2) (by decide) (by decide) (by decide)
    · exact h_edge (1, 3) (3, 4) (by decide) (by decide) (by decide)
    · exact h_edge (1, 3) (5, 2) (by decide) (by decide) (by decide)
    · exact h_edge (1, 2) (3, 4) (by decide) (by decide) (by decide)
    · exact h_edge (0, 4) (5, 2) (by decide) (by decide) (by decide)
  have hDS_core : Erdos91.DistanceErasure.distanceSet hex21NineDistCore5 = hex21Utp9.image triNorm :=
    Finset.Subset.antisymm ((distanceSet_mono hsub_core).trans hupper) hlower
  have hDS_21 : Erdos91.DistanceErasure.distanceSet hex21NineDist = hex21Utp9.image triNorm :=
    Finset.Subset.antisymm hupper (hlower.trans (distanceSet_mono hsub_core))
  have hCore : IsDistanceCompleteCore hex21NineDistCore5 hex21NineDist :=
    ⟨hsub_core, hDS_core.trans hDS_21.symm⟩
  have hdd : Minimizer91.distinctDistances hex21NineDist = 9 := by
    change (Erdos91.DistanceErasure.distanceSet hex21NineDist).card = 9
    rw [hDS_21, card_image_triNorm_eq_card_image_triNormSq]
    rfl
  have hd21 : Minimizer91.minimalDistinctDistances 21 ≤ 9 :=
    (Minimizer91.minimal_le hex21NineDist 21 hcard21).trans hdd.le
  have hd20 : Minimizer91.minimalDistinctDistances 20 ≤ 9 :=
    (MinimumMonotone91.minimum_monotone (by omega : 20 ≤ 21)).trans hd21
  have hd19 : Minimizer91.minimalDistinctDistances 19 ≤ 9 :=
    (MinimumMonotone91.minimum_monotone (by omega : 19 ≤ 20)).trans hd20
  have hd18 : Minimizer91.minimalDistinctDistances 18 ≤ 9 :=
    (MinimumMonotone91.minimum_monotone (by omega : 18 ≤ 19)).trans hd19
  exact ⟨hsub_core (Finset.mem_image_of_mem triPoint hp),
    hcard21, hcard5, hCore, hDS_21, hdd, hd21, hd20, hd19, hd18⟩

/-- **Certified 5-Configuration (`n = 20`), 35-Configuration (`n = 19`), and 86-Configuration (`n = 18`) 9-Distance Families on `hex21NineDist` (`∀ K₂₀ ≤ 5, ∀ K₁₉ ≤ 35, ∀ K₁₈ ≤ 86`):** -/
theorem hex21NineDist_twenty_nineteen_eighteen_multi_deletion_families
    (K₂₀ K₁₉ K₁₈ : ℕ) (hK₂₀ : K₂₀ ≤ 5) (hK₁₉ : K₁₉ ≤ 35) (hK₁₈ : K₁₈ ≤ 86) :
    ((∃ G₂₀ : Finset (Finset Plane),
      G₂₀.card = K₂₀ ∧
      (∀ A ∈ G₂₀, A.card = 20 ∧
        Erdos91.DistanceErasure.distanceSet A = hex21Utp9.image triNorm ∧
        Minimizer91.distinctDistances A = 9) ∧
      (∀ A ∈ G₂₀, ∀ B ∈ G₂₀, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
      (9 ≤ Minimizer91.minimalDistinctDistances 20 → HasAtLeastKNonsimilarMinimizers K₂₀ 20)) ∧
    ((∃ G₁₉ : Finset (Finset Plane),
      G₁₉.card = K₁₉ ∧
      (∀ A ∈ G₁₉, A.card = 19 ∧
        Erdos91.DistanceErasure.distanceSet A = hex21Utp9.image triNorm ∧
        Minimizer91.distinctDistances A = 9) ∧
      (∀ A ∈ G₁₉, ∀ B ∈ G₁₉, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
      (9 ≤ Minimizer91.minimalDistinctDistances 19 → HasAtLeastKNonsimilarMinimizers K₁₉ 19)) ∧
    ((∃ G₁₈ : Finset (Finset Plane),
      G₁₈.card = K₁₈ ∧
      (∀ A ∈ G₁₈, A.card = 18 ∧
        Erdos91.DistanceErasure.distanceSet A = hex21Utp9.image triNorm ∧
        Minimizer91.distinctDistances A = 9) ∧
      (∀ A ∈ G₁₈, ∀ B ∈ G₁₈, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
      (9 ≤ Minimizer91.minimalDistinctDistances 18 → HasAtLeastKNonsimilarMinimizers K₁₈ 18)) := by
  obtain ⟨_, _, _, hCore, hDS9, hdd9, _, _, _, _⟩ :=
    card_and_distanceSet_hex21NineDist_and_core5 (0, 4) (by decide)
  have hcard21_c : hex21NineDistCoords.card = 21 := rfl
  have hdiam_c : ∀ p ∈ hex21NineDistCoords, ∀ q ∈ hex21NineDistCoords,
      triNormSq (triOffset p q) ≤ triNormSq (triOffset (0, 4) (5, 2)) := by decide
  have hres1 := triCoord_powersetCard_multi_deletion_family
    hex21NineDistCoords hex21NineDistCore5Coords (0, 4) (5, 2) 1 K₂₀
    hCore (by decide) (by decide) (by decide) hdiam_c (hK₂₀.trans_eq rfl)
  have hres2 := triCoord_powersetCard_multi_deletion_family
    hex21NineDistCoords hex21NineDistCore5Coords (0, 4) (5, 2) 2 K₁₉
    hCore (by decide) (by decide) (by decide) hdiam_c (hK₁₉.trans_eq rfl)
  have hres3 := triCoord_powersetCard_multi_deletion_family
    hex21NineDistCoords hex21NineDistCore5Coords (0, 4) (5, 2) 3 K₁₈
    hCore (by decide) (by decide) (by decide) hdiam_c (hK₁₈.trans_eq rfl)
  change IsDistanceCompleteCore (hex21NineDistCore5Coords.image triPoint)
    (hex21NineDistCoords.image triPoint) at hCore
  change Erdos91.DistanceErasure.distanceSet (hex21NineDistCoords.image triPoint) =
    hex21Utp9.image triNorm at hDS9
  change Minimizer91.distinctDistances (hex21NineDistCoords.image triPoint) = 9 at hdd9
  rw [hcard21_c, hDS9, hdd9] at hres1 hres2 hres3
  exact ⟨hres1, hres2, hres3⟩

/-- **Certified 55-, 95-, 92-, 66-, 32-, and 9-Configuration `k ≥ 3` Multi-Deletion Families on `T_6 = hexSet 6 0 5` (`n = 18, 17, 16, 15, 14, 13`):**
for every `K₁₈ ≤ 55`, `K₁₇ ≤ 95`, `K₁₆ ≤ 92`, `K₁₅ ≤ 66`, `K₁₄ ≤ 32`, and `K₁₃ ≤ 9`,
the 21-point equilateral triangular patch `triPatchSet 6 = hexSet 6 0 5` admits `K_n` pairwise
nonsimilar `n`-point deletions outside `triPatchCore 6` (`d = 3, 4, 5, 6, 7, 8`), all preserving
the 11-element distance set `(triUtp 5).image triNorm`. -/
theorem triPatchSet_6_multi_deletion_families_18_to_13
    (K₁₈ K₁₇ K₁₆ K₁₅ K₁₄ K₁₃ : ℕ)
    (hK₁₈ : K₁₈ ≤ 55) (hK₁₇ : K₁₇ ≤ 95) (hK₁₆ : K₁₆ ≤ 92)
    (hK₁₅ : K₁₅ ≤ 66) (hK₁₄ : K₁₄ ≤ 32) (hK₁₃ : K₁₃ ≤ 9) :
    ((∃ G₁₈ : Finset (Finset Plane),
      G₁₈.card = K₁₈ ∧
      (∀ A ∈ G₁₈, A.card = 18 ∧
        Erdos91.DistanceErasure.distanceSet A = (triUtp 5).image triNorm ∧
        Minimizer91.distinctDistances A = 11) ∧
      (∀ A ∈ G₁₈, ∀ B ∈ G₁₈, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
      (11 ≤ Minimizer91.minimalDistinctDistances 18 → HasAtLeastKNonsimilarMinimizers K₁₈ 18)) ∧
    (∃ G₁₇ : Finset (Finset Plane),
      G₁₇.card = K₁₇ ∧
      (∀ A ∈ G₁₇, A.card = 17 ∧
        Erdos91.DistanceErasure.distanceSet A = (triUtp 5).image triNorm ∧
        Minimizer91.distinctDistances A = 11) ∧
      (∀ A ∈ G₁₇, ∀ B ∈ G₁₇, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
    (∃ G₁₆ : Finset (Finset Plane),
      G₁₆.card = K₁₆ ∧
      (∀ A ∈ G₁₆, A.card = 16 ∧
        Erdos91.DistanceErasure.distanceSet A = (triUtp 5).image triNorm ∧
        Minimizer91.distinctDistances A = 11) ∧
      (∀ A ∈ G₁₆, ∀ B ∈ G₁₆, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
    (∃ G₁₅ : Finset (Finset Plane),
      G₁₅.card = K₁₅ ∧
      (∀ A ∈ G₁₅, A.card = 15 ∧
        Erdos91.DistanceErasure.distanceSet A = (triUtp 5).image triNorm ∧
        Minimizer91.distinctDistances A = 11) ∧
      (∀ A ∈ G₁₅, ∀ B ∈ G₁₅, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
    ((∃ G₁₄ : Finset (Finset Plane),
      G₁₄.card = K₁₄ ∧
      (∀ A ∈ G₁₄, A.card = 14 ∧
        Erdos91.DistanceErasure.distanceSet A = (triUtp 5).image triNorm ∧
        Minimizer91.distinctDistances A = 11) ∧
      (∀ A ∈ G₁₄, ∀ B ∈ G₁₄, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
      (11 ≤ Minimizer91.minimalDistinctDistances 14 → HasAtLeastKNonsimilarMinimizers K₁₄ 14)) ∧
    ((∃ G₁₃ : Finset (Finset Plane),
      G₁₃.card = K₁₃ ∧
      (∀ A ∈ G₁₃, A.card = 13 ∧
        Erdos91.DistanceErasure.distanceSet A = (triUtp 5).image triNorm ∧
        Minimizer91.distinctDistances A = 11) ∧
      (∀ A ∈ G₁₃, ∀ B ∈ G₁₃, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
      (11 ≤ Minimizer91.minimalDistinctDistances 13 → HasAtLeastKNonsimilarMinimizers K₁₃ 13)) := by
  have hcard21 : (triPatchSet 6).card = 21 := by
    unfold triPatchSet; rw [card_hexSet]; rfl
  have hdd11 : ((triUtp 5).image triNormSq).card = 11 := rfl
  have hres3 := triPatchSet_multi_deletion_family_of_le_card_image 6 3 K₁₈ (by omega) (hK₁₈.trans_eq rfl)
  have hres4 := (triPatchSet_multi_deletion_family_of_le_card_image 6 4 K₁₇ (by omega) (hK₁₇.trans_eq rfl)).1
  have hres5 := (triPatchSet_multi_deletion_family_of_le_card_image 6 5 K₁₆ (by omega) (hK₁₆.trans_eq rfl)).1
  have hres6 := (triPatchSet_multi_deletion_family_of_le_card_image 6 6 K₁₅ (by omega) (hK₁₅.trans_eq rfl)).1
  have hres7 := triPatchSet_multi_deletion_family_of_le_card_image 6 7 K₁₄ (by omega) (hK₁₄.trans_eq rfl)
  have hres8 := triPatchSet_multi_deletion_family_of_le_card_image 6 8 K₁₃ (by omega) (hK₁₃.trans_eq rfl)
  rw [hcard21, hdd11] at hres3 hres4 hres5 hres6 hres7 hres8
  exact ⟨hres3, hres4, hres5, hres6, hres7, hres8⟩

/-- Irreducible 6-point distance-complete coordinate core `{(0, 0), (0, 1), (0, 2), (0, 5), (1, 0), (2, 3)}`
of `T_6 = hexCoords 6 0 5`. -/
def triPatch6Core6Coords : Finset (ℕ × ℕ) :=
  {(0, 0), (0, 1), (0, 2), (0, 5), (1, 0), (2, 3)}

/-- Planar 6-point distance-complete core `triPatch6Core6 = triPatch6Core6Coords.image triPoint` of `hexSet 6 0 5`. -/
noncomputable def triPatch6Core6 : Finset Plane :=
  triPatch6Core6Coords.image triPoint

/-- **Exact 6-Point Distance-Complete Core Theorem on `T_6 = hexSet 6 0 5` (`∀ p`):** -/
theorem card_and_distanceSet_triPatchSet_6_and_core6
    (p : ℕ × ℕ) (hp : p ∈ triPatch6Core6Coords) :
    triPoint p ∈ hexSet 6 0 5 ∧
      (hexSet 6 0 5).card = 21 ∧
      triPatch6Core6.card = 6 ∧
      IsDistanceCompleteCore triPatch6Core6 (hexSet 6 0 5) ∧
      Erdos91.DistanceErasure.distanceSet (hexSet 6 0 5) = (triUtp 5).image triNorm ∧
      Minimizer91.distinctDistances (hexSet 6 0 5) = 11 := by
  obtain ⟨_, hDS6, hdd6, _⟩ := distanceSet_triPatchCore_eq_and_isDistanceCompleteCore 6 (by omega)
  change Erdos91.DistanceErasure.distanceSet (hexSet 6 0 5) = (triUtp 5).image triNorm at hDS6
  have hcard21 : (hexSet 6 0 5).card = 21 := by rw [card_hexSet]; rfl
  have hdd11 : Minimizer91.distinctDistances (hexSet 6 0 5) = 11 := by
    change Minimizer91.distinctDistances (triPatchSet 6) = 11
    rw [hdd6]; rfl
  have hcard6 : triPatch6Core6.card = 6 := by
    unfold triPatch6Core6
    rw [Finset.card_image_of_injective _ triPoint_injective]
    rfl
  have hsub_coords : triPatch6Core6Coords ⊆ hexCoords 6 0 5 := by decide
  have hsub_core : triPatch6Core6 ⊆ hexSet 6 0 5 := Finset.image_subset_image hsub_coords
  have h_edge : ∀ a b : ℕ × ℕ, a ∈ triPatch6Core6Coords → b ∈ triPatch6Core6Coords → a ≠ b →
      triNorm (triOffset a b) ∈ Erdos91.DistanceErasure.distanceSet triPatch6Core6 := by
    intro a b ha hb hab
    exact (Erdos91.DistanceErasure.mem_distanceSet _ _).mpr
      ⟨triPoint a, Finset.mem_image_of_mem triPoint ha,
       triPoint b, Finset.mem_image_of_mem triPoint hb,
       fun h => hab (triPoint_injective h), dist_triPoint_eq a b⟩
  have hlower : (triUtp 5).image triNorm ⊆ Erdos91.DistanceErasure.distanceSet triPatch6Core6 := by
    intro r hr
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
    have hu_all : ∀ v ∈ triUtp 5,
        v = (0, 1) ∨ v = (0, 2) ∨ v = (0, 3) ∨ v = (0, 4) ∨ v = (0, 5) ∨
        v = (1, 1) ∨ v = (1, 2) ∨ v = (1, 3) ∨ v = (1, 4) ∨ v = (2, 2) ∨ v = (2, 3) := by decide
    rcases hu_all u hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h_edge (0, 0) (0, 1) (by decide) (by decide) (by decide)
    · exact h_edge (0, 0) (0, 2) (by decide) (by decide) (by decide)
    · exact h_edge (0, 2) (0, 5) (by decide) (by decide) (by decide)
    · exact h_edge (0, 1) (0, 5) (by decide) (by decide) (by decide)
    · exact h_edge (0, 0) (0, 5) (by decide) (by decide) (by decide)
    · exact h_edge (0, 2) (1, 0) (by decide) (by decide) (by decide)
    · exact h_edge (0, 2) (2, 3) (by decide) (by decide) (by decide)
    · exact h_edge (1, 0) (2, 3) (by decide) (by decide) (by decide)
    · exact h_edge (0, 5) (1, 0) (by decide) (by decide) (by decide)
    · exact h_edge (0, 1) (2, 3) (by decide) (by decide) (by decide)
    · exact h_edge (0, 0) (2, 3) (by decide) (by decide) (by decide)
  have hDS_core : Erdos91.DistanceErasure.distanceSet triPatch6Core6 = (triUtp 5).image triNorm :=
    Finset.Subset.antisymm ((distanceSet_mono hsub_core).trans hDS6.le) hlower
  have hCore : IsDistanceCompleteCore triPatch6Core6 (hexSet 6 0 5) :=
    ⟨hsub_core, hDS_core.trans hDS6.symm⟩
  exact ⟨hsub_core (Finset.mem_image_of_mem triPoint hp), hcard21, hcard6, hCore, hDS6, hdd11⟩

/-- **Certified 37-Configuration (`n = 19`) and 103-Configuration (`n = 18`) Multi-Deletion Families on `T_6 = hexSet 6 0 5` over `triPatch6Core6` (`∀ K₁₉ ≤ 37, ∀ K₁₈ ≤ 103`):** -/
theorem triPatchSet_6_core6_nineteen_eighteen_multi_deletion_families
    (K₁₉ K₁₈ : ℕ) (hK₁₉ : K₁₉ ≤ 37) (hK₁₈ : K₁₈ ≤ 103) :
    ((∃ G₁₉ : Finset (Finset Plane),
      G₁₉.card = K₁₉ ∧
      (∀ A ∈ G₁₉, A.card = 19 ∧
        Erdos91.DistanceErasure.distanceSet A = (triUtp 5).image triNorm ∧
        Minimizer91.distinctDistances A = 11) ∧
      (∀ A ∈ G₁₉, ∀ B ∈ G₁₉, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
      (11 ≤ Minimizer91.minimalDistinctDistances 19 → HasAtLeastKNonsimilarMinimizers K₁₉ 19)) ∧
    ((∃ G₁₈ : Finset (Finset Plane),
      G₁₈.card = K₁₈ ∧
      (∀ A ∈ G₁₈, A.card = 18 ∧
        Erdos91.DistanceErasure.distanceSet A = (triUtp 5).image triNorm ∧
        Minimizer91.distinctDistances A = 11) ∧
      (∀ A ∈ G₁₈, ∀ B ∈ G₁₈, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
      (11 ≤ Minimizer91.minimalDistinctDistances 18 → HasAtLeastKNonsimilarMinimizers K₁₈ 18)) := by
  obtain ⟨_, _, _, hCore, hDS11, hdd11⟩ :=
    card_and_distanceSet_triPatchSet_6_and_core6 (0, 0) (by decide)
  have hcard21_c : (hexCoords 6 0 5).card = 21 := rfl
  have hdiam_c : ∀ p ∈ hexCoords 6 0 5, ∀ q ∈ hexCoords 6 0 5,
      triNormSq (triOffset p q) ≤ triNormSq (triOffset (0, 0) (0, 5)) := by decide
  have hres2 := triCoord_powersetCard_multi_deletion_family
    (hexCoords 6 0 5) triPatch6Core6Coords (0, 0) (0, 5) 2 K₁₉
    hCore (by decide) (by decide) (by decide) hdiam_c (hK₁₉.trans_eq rfl)
  have hres3 := triCoord_powersetCard_multi_deletion_family
    (hexCoords 6 0 5) triPatch6Core6Coords (0, 0) (0, 5) 3 K₁₈
    hCore (by decide) (by decide) (by decide) hdiam_c (hK₁₈.trans_eq rfl)
  change IsDistanceCompleteCore (triPatch6Core6Coords.image triPoint)
    ((hexCoords 6 0 5).image triPoint) at hCore
  change Erdos91.DistanceErasure.distanceSet ((hexCoords 6 0 5).image triPoint) =
    (triUtp 5).image triNorm at hDS11
  change Minimizer91.distinctDistances ((hexCoords 6 0 5).image triPoint) = 11 at hdd11
  rw [hcard21_c, hDS11, hdd11] at hres2 hres3
  exact ⟨hres2, hres3⟩

/-- **Unconditional `n = 16..20` Multiplicity Dichotomy (`∀ K₂₀ ≤ 5, ∀ K₁₈ ≤ 4, ∀ K₁₇ ≤ 21`):**
combining `hex21NineDist` (`d(21) ≤ 9`) and `hexSet 5 2 4` (`d(19) ≤ 8`), unconditionally either:
1. `9 ≤ d(20)` and `HasAtLeastKNonsimilarMinimizers K₂₀ 20`,
2. `d(19) = 8 ∧ d(20) = 8 ∧ ¬ UniqueMinimizer 19`,
3. `d(18) = 8 ∧ HasAtLeastKNonsimilarMinimizers K₁₈ 18` (and if `d(17) = 8`, `HasAtLeastKNonsimilarMinimizers K₁₇ 17`),
4. `d(17) = 7 ∧ d(18) = 7 ∧ ¬ UniqueMinimizer 17`,
5. `d(16) = 7 ∧ d(17) = 7 ∧ ¬ UniqueMinimizer 16`, or
6. `d(16) ≤ 6`. -/
theorem unconditional_sixteen_to_twenty_multiplicity_or_le_six
    (K₂₀ K₁₈ K₁₇ : ℕ) (hK₂₀ : K₂₀ ≤ 5) (hK₁₈ : K₁₈ ≤ 4) (hK₁₇ : K₁₇ ≤ 21) :
    (9 ≤ Minimizer91.minimalDistinctDistances 20 ∧ HasAtLeastKNonsimilarMinimizers K₂₀ 20) ∨
    (Minimizer91.minimalDistinctDistances 19 = 8 ∧
      Minimizer91.minimalDistinctDistances 20 = 8 ∧ ¬ PlateauDefinitions91.UniqueMinimizer 19) ∨
    (Minimizer91.minimalDistinctDistances 18 = 8 ∧ HasAtLeastKNonsimilarMinimizers K₁₈ 18 ∧
      (8 ≤ Minimizer91.minimalDistinctDistances 17 → HasAtLeastKNonsimilarMinimizers K₁₇ 17)) ∨
    (Minimizer91.minimalDistinctDistances 17 = 7 ∧
      Minimizer91.minimalDistinctDistances 18 = 7 ∧ ¬ PlateauDefinitions91.UniqueMinimizer 17) ∨
    (Minimizer91.minimalDistinctDistances 16 = 7 ∧
      Minimizer91.minimalDistinctDistances 17 = 7 ∧ ¬ PlateauDefinitions91.UniqueMinimizer 16) ∨
    Minimizer91.minimalDistinctDistances 16 ≤ 6 := by
  obtain ⟨⟨_, hfam20⟩, _, _⟩ :=
    hex21NineDist_twenty_nineteen_eighteen_multi_deletion_families K₂₀ 1 1 hK₂₀ (by omega) (by omega)
  obtain ⟨⟨_, hfam18⟩, ⟨_, hfam17⟩, _⟩ :=
    hexSet_5_2_4_core5_eighteen_seventeen_sixteen_multi_deletion_families K₁₈ K₁₇ 1 hK₁₈ hK₁₇ (by omega)
  have hd19_le8 : Minimizer91.minimalDistinctDistances 19 ≤ 8 := minimalDistinctDistances_19_le_8
  have hm16_17 := MinimumMonotone91.minimum_monotone (by omega : 16 ≤ 17)
  have hm17_18 := MinimumMonotone91.minimum_monotone (by omega : 17 ≤ 18)
  have hm18_19 := MinimumMonotone91.minimum_monotone (by omega : 18 ≤ 19)
  have hm19_20 := MinimumMonotone91.minimum_monotone (by omega : 19 ≤ 20)
  by_cases hd20_9 : 9 ≤ Minimizer91.minimalDistinctDistances 20
  · exact Or.inl ⟨hd20_9, hfam20 hd20_9⟩
  · by_cases hd18_8 : 8 ≤ Minimizer91.minimalDistinctDistances 18
    · right; right; left
      exact ⟨by omega, hfam18 hd18_8, hfam17⟩
    · by_cases hd19_8 : 8 ≤ Minimizer91.minimalDistinctDistances 19
      · right; left
        have hd19_eq : Minimizer91.minimalDistinctDistances 19 = 8 := by omega
        have hd20_eq : Minimizer91.minimalDistinctDistances 20 = 8 := by omega
        exact ⟨hd19_eq, hd20_eq,
          plateau_not_unique_of_two_mul_lt_sub_one 19 (by omega) (hd19_eq.trans hd20_eq.symm) (by omega)⟩
      · by_cases hd17_7 : 7 ≤ Minimizer91.minimalDistinctDistances 17
        · right; right; right; left
          have hd17_eq : Minimizer91.minimalDistinctDistances 17 = 7 := by omega
          have hd18_eq : Minimizer91.minimalDistinctDistances 18 = 7 := by omega
          exact ⟨hd17_eq, hd18_eq,
            plateau_not_unique_of_two_mul_lt_sub_one 17 (by omega) (hd17_eq.trans hd18_eq.symm) (by omega)⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega)))))

/-- **Unconditional `n ∈ {14..20}` Nonuniqueness Theorem:**
combining `d(7) = 3`, `d(19) ≤ 8` (`hexSet 5 2 4`), and `9 ≤ d(20) → HasAtLeastKNonsimilarMinimizers 2 20`
(`hex21NineDist`), at least one of `n ∈ {14, 15, 16, 17, 18, 19, 20}` fails `UniqueMinimizer n`. -/
theorem unconditional_fourteen_to_twenty_nonuniqueness :
    ¬ PlateauDefinitions91.UniqueMinimizer 14 ∨ ¬ PlateauDefinitions91.UniqueMinimizer 15 ∨
      ¬ PlateauDefinitions91.UniqueMinimizer 16 ∨ ¬ PlateauDefinitions91.UniqueMinimizer 17 ∨
      ¬ PlateauDefinitions91.UniqueMinimizer 18 ∨ ¬ PlateauDefinitions91.UniqueMinimizer 19 ∨
      ¬ PlateauDefinitions91.UniqueMinimizer 20 := by
  by_contra h
  push Not at h
  obtain ⟨h14, h15, h16, h17, h18, h19, h20⟩ := h
  have hd7 : Minimizer91.minimalDistinctDistances 7 = 3 := minimalDistinctDistances_seven
  have hd19_le8 : Minimizer91.minimalDistinctDistances 19 ≤ 8 := minimalDistinctDistances_19_le_8
  obtain ⟨⟨_, hfam20⟩, _, _⟩ :=
    hex21NineDist_twenty_nineteen_eighteen_multi_deletion_families 2 2 2 (by omega) (by omega) (by omega)
  have hm7_14 := MinimumMonotone91.minimum_monotone (by omega : 7 ≤ 14)
  have hm14_15 := MinimumMonotone91.minimum_monotone (by omega : 14 ≤ 15)
  have hm15_16 := MinimumMonotone91.minimum_monotone (by omega : 15 ≤ 16)
  have hm16_17 := MinimumMonotone91.minimum_monotone (by omega : 16 ≤ 17)
  have hm17_18 := MinimumMonotone91.minimum_monotone (by omega : 17 ≤ 18)
  have hm18_19 := MinimumMonotone91.minimum_monotone (by omega : 18 ≤ 19)
  have hd20_le8 : Minimizer91.minimalDistinctDistances 20 ≤ 8 := by
    by_contra hgt
    obtain ⟨G, hGcard, hGopt, hGnon⟩ := hfam20 (by omega)
    obtain ⟨A, hA, B, hB, hAB⟩ := Finset.one_lt_card.mp (by omega : 1 < G.card)
    exact hGnon A hA B hB hAB (h20 A B (hGopt A hA) (hGopt B hB))
  have hr19 : Minimizer91.minimalDistinctDistances 19 < Minimizer91.minimalDistinctDistances 20 :=
    uniqueMinimizer_imp_strict_rise_of_two_mul_lt_sub_one 19 (by omega) (by omega) h19
  have hr18 : Minimizer91.minimalDistinctDistances 18 < Minimizer91.minimalDistinctDistances 19 :=
    uniqueMinimizer_imp_strict_rise_of_two_mul_lt_sub_one 18 (by omega) (by omega) h18
  have hr17 : Minimizer91.minimalDistinctDistances 17 < Minimizer91.minimalDistinctDistances 18 :=
    uniqueMinimizer_imp_strict_rise_of_two_mul_lt_sub_one 17 (by omega) (by omega) h17
  have hr16 : Minimizer91.minimalDistinctDistances 16 < Minimizer91.minimalDistinctDistances 17 :=
    uniqueMinimizer_imp_strict_rise_of_two_mul_lt_sub_one 16 (by omega) (by omega) h16
  have hr15 : Minimizer91.minimalDistinctDistances 15 < Minimizer91.minimalDistinctDistances 16 :=
    uniqueMinimizer_imp_strict_rise_of_two_mul_lt_sub_one 15 (by omega) (by omega) h15
  have hr14 : Minimizer91.minimalDistinctDistances 14 < Minimizer91.minimalDistinctDistances 15 :=
    uniqueMinimizer_imp_strict_rise_of_two_mul_lt_sub_one 14 (by omega) (by omega) h14
  omega

end Erdos91.TruncatedTriangleAndHexagonMultiDeletionFamilies


namespace Erdos91.FormalConjecturesBridgesAndSolvedVariants
  open Erdos91.SharpenedTwoCenterFiberSumBounds Erdos91.TruncatedTriangleAndHexagonMultiDeletionFamilies

/-- **Exact `FormalConjectures` Distance-Set and Distinct-Distances Bridges (`∀ A`):** -/
theorem fc_distanceSet_and_distinctDistances_eq (A : Finset Plane) :
    _root_.distanceSet A = Minimizer91.distanceSet A ∧
      _root_.distinctDistances A = Minimizer91.distinctDistances A :=
  ⟨rfl, rfl⟩

/-- **Exact `FormalConjectures` `minimalDistinctDistances ℝ²` Bridge (`∀ n`):** -/
theorem fc_minimalDistinctDistances_eq (n : ℕ) :
    _root_.minimalDistinctDistances (EuclideanSpace ℝ (Fin 2)) n =
      Minimizer91.minimalDistinctDistances n := by
  unfold _root_.minimalDistinctDistances Minimizer91.minimalDistinctDistances
  congr 1
  ext m
  simp [(fc_distanceSet_and_distinctDistances_eq _).2, eq_comm]

/-- **Exact `FormalConjectures` `IsOptimal` and `DilationEquivSimilar` Bridges (`∀ A B n`):** -/
theorem fc_isOptimal_and_similar_iff (A B : Finset Plane) (n : ℕ) :
    (Erdos91.IsOptimal A n ↔ Minimizer91.IsOptimal A n) ∧
      (Erdos91.DilationEquivSimilar A B ↔ PlateauDefinitions91.DilationEquivSimilar A B) := by
  refine ⟨?_, Iff.rfl⟩
  unfold Erdos91.IsOptimal Minimizer91.IsOptimal
  rw [(fc_distanceSet_and_distinctDistances_eq A).2, fc_minimalDistinctDistances_eq]

/-- **Exact `FormalConjectures` `UniqueMinimizer` Bridge (`∀ n`):** -/
theorem fc_uniqueMinimizer_iff (n : ℕ) :
    Erdos91.UniqueMinimizer n ↔ PlateauDefinitions91.UniqueMinimizer n := by
  unfold Erdos91.UniqueMinimizer PlateauDefinitions91.UniqueMinimizer
  simp only [fun A => (fc_isOptimal_and_similar_iff A A n).1,
    fun A B => (fc_isOptimal_and_similar_iff A B n).2]

/-- **Unconditional Proof of `erdos_91.test.equiTriangle_unique_optimal` (`∀ A`):** -/
theorem fc_equiTriangle_unique_optimal (A : Finset Plane) (hA : Erdos91.IsOptimal A 3) :
    Erdos91.DilationEquivSimilar A Erdos91.equiTriangle :=
  Erdos91.ThreeUniqueMinimizer.equiTriangle_unique_optimal A
    ((fc_isOptimal_and_similar_iff A A 3).1.mp hA)

/-- **Unconditional Proofs of `erdos_91.variants.three`, `four`, `six`, `seven`, and `eight` / `nine` Dichotomy:** -/
theorem fc_erdos_91_solved_variants :
    Erdos91.UniqueMinimizer 3 ∧
      ¬ Erdos91.UniqueMinimizer 4 ∧
      ¬ Erdos91.UniqueMinimizer 6 ∧
      ¬ Erdos91.UniqueMinimizer 7 ∧
      (¬ Erdos91.UniqueMinimizer 8 ∨ ¬ Erdos91.UniqueMinimizer 9) ∧
      (¬ Erdos91.UniqueMinimizer 14 ∨ ¬ Erdos91.UniqueMinimizer 15 ∨
        ¬ Erdos91.UniqueMinimizer 16 ∨ ¬ Erdos91.UniqueMinimizer 17 ∨
        ¬ Erdos91.UniqueMinimizer 18 ∨ ¬ Erdos91.UniqueMinimizer 19 ∨
        ¬ Erdos91.UniqueMinimizer 20) := by
  refine ⟨(fc_uniqueMinimizer_iff 3).mpr Erdos91.ThreeUniqueMinimizer.uniqueMinimizer_three,
    fun h => Erdos91.FourNonuniqueAndDoubleEquilateral.not_uniqueMinimizer_four ((fc_uniqueMinimizer_iff 4).mp h),
    fun h => Erdos91.TwoDistanceCapAndSixNonunique.not_uniqueMinimizer_six ((fc_uniqueMinimizer_iff 6).mp h),
    fun h => Erdos91.SevenNonuniqueHeptagonAndWheel.not_uniqueMinimizer_seven ((fc_uniqueMinimizer_iff 7).mp h),
    ?_, ?_⟩
  · rcases Erdos91.UnconditionalEightNineDichotomy.not_uniqueMinimizer_eight_or_nine with h8 | h9
    · exact Or.inl (fun h => h8 ((fc_uniqueMinimizer_iff 8).mp h))
    · exact Or.inr (fun h => h9 ((fc_uniqueMinimizer_iff 9).mp h))
  · simp only [fc_uniqueMinimizer_iff]
    exact unconditional_fourteen_to_twenty_nonuniqueness

/-- **Top-Down `FormalConjectures.ErdosProblems.91` Reduction via Sharpened Quadratic Lower Bound (`erdos_91` RHS):**
`∀ᶠ n in atTop, ¬ Erdos91.UniqueMinimizer n` holds if and only if eventually every strict-rise
index `n` satisfying `n ≤ 2 * d(n)^2` and `4 * d(n) < n` fails `Erdos91.UniqueMinimizer n`. -/
theorem erdos_91_eventually_iff_strict_rises_and_quadratic_window :
    (∀ᶠ n : ℕ in Filter.atTop, ¬ Erdos91.UniqueMinimizer n) ↔
      (∀ᶠ n : ℕ in Filter.atTop,
        n ≤ 2 * (_root_.minimalDistinctDistances (EuclideanSpace ℝ (Fin 2)) n) ^ 2 ∧
          4 * _root_.minimalDistinctDistances (EuclideanSpace ℝ (Fin 2)) n < n ∧
          _root_.minimalDistinctDistances (EuclideanSpace ℝ (Fin 2)) n <
            _root_.minimalDistinctDistances (EuclideanSpace ℝ (Fin 2)) (n + 1) →
          ¬ Erdos91.UniqueMinimizer n) := by
  constructor
  · intro h
    filter_upwards [h] with n hn _
    exact hn
  · intro h
    have h4 : ∀ᶠ n : ℕ in Filter.atTop, 4 ≤ n := Filter.eventually_ge_atTop 4
    filter_upwards [h, h4, unconditional_sublinearMinimalDistances 4] with n hn hn4 hsub huniq
    have hquad : n ≤ 2 * (_root_.minimalDistinctDistances (EuclideanSpace ℝ (Fin 2)) n) ^ 2 := by
      rw [fc_minimalDistinctDistances_eq]
      exact (minimal_quadratic_lower_bound_of_four_le n 3 hn4 (by omega)).1
    have hsub_fc : 4 * _root_.minimalDistinctDistances (EuclideanSpace ℝ (Fin 2)) n < n := by
      rwa [fc_minimalDistinctDistances_eq]
    have huniq_local : PlateauDefinitions91.UniqueMinimizer n :=
      (fc_uniqueMinimizer_iff n).mp huniq
    have hrise : _root_.minimalDistinctDistances (EuclideanSpace ℝ (Fin 2)) n <
        _root_.minimalDistinctDistances (EuclideanSpace ℝ (Fin 2)) (n + 1) := by
      rw [fc_minimalDistinctDistances_eq, fc_minimalDistinctDistances_eq]
      exact uniqueMinimizer_imp_strict_rise_of_two_mul_lt_sub_one n (by omega) (by omega) huniq_local
    exact hn ⟨hquad, hsub_fc, hrise⟩ huniq

end Erdos91.FormalConjecturesBridgesAndSolvedVariants
