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

@[expose] public section

/-! ## Restated definitions

`distanceSet`, `distinctDistances`, and `minimalDistinctDistances` below repeat the definitions in
Formal Conjectures' `FormalConjecturesForMathlib/Geometry/Metric.lean`, so that this package
compiles without that dependency. They are not new. -/

scoped[EuclideanGeometry] notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)
scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
open Filter Finset EuclideanGeometry

namespace EuclideanGeometry
noncomputable def distanceSet {X : Type*} [MetricSpace X] (points : Finset X) : Finset ℝ :=
  points.offDiag.image fun (pair : X × X) => dist pair.1 pair.2

noncomputable def distinctDistances {X : Type*} [MetricSpace X] (points : Finset X) : ℕ :=
  #(distanceSet points)

noncomputable def minimalDistinctDistances (X : Type*) [MetricSpace X] (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ points : Finset X, #points = n ∧ distinctDistances points = m}
end EuclideanGeometry

/-! ## Helper lemmas for the minimisation problem

These lemmas support the internal planar comparison bound below (`erdos_661.variants.le_minimalDistinctDistances`),
which already carries a complete inline proof upstream in Formal Conjectures (PR #7490) and is
included only as a supporting lemma rather than a new result. The
`distanceSet`, `distinctDistances`, and `minimalDistinctDistances` definitions they refer to are
restated from Formal Conjectures' `FormalConjecturesForMathlib/Geometry/Metric.lean`. -/
namespace Erdos661Helpers
theorem infinite_euclideanSpace {d : ℕ} (hd : 1 ≤ d) :
    Infinite (EuclideanSpace ℝ (Fin d)) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  infer_instance

theorem validDistinctDistancesSet_nonempty (X : Type*) [MetricSpace X] [Infinite X] (n : ℕ) :
    {m : ℕ | ∃ A : Finset X, #A = n ∧ EuclideanGeometry.distinctDistances A = m}.Nonempty := by
  obtain ⟨A, hA⟩ := Infinite.exists_subset_card_eq X n
  exact ⟨EuclideanGeometry.distinctDistances A, A, hA, rfl⟩

theorem exists_minimizer_distinctDistances (X : Type*) [MetricSpace X] [Infinite X] (n : ℕ) :
    ∃ points : Finset X, #points = n ∧
      EuclideanGeometry.distinctDistances points = EuclideanGeometry.minimalDistinctDistances X n :=
  Nat.sInf_mem (validDistinctDistancesSet_nonempty X n)
end Erdos661Helpers

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

noncomputable section

namespace Erdos661

open Filter Finset EuclideanGeometry
open scoped BigOperators Classical EuclideanGeometry Finset

variable {X : Type*} [MetricSpace X]

/--
The set of distances `d(x, y)` with `x ∈ A` and `y ∈ B`.
Taken from `FormalConjectures/ErdosProblems/661.lean`.
-/
noncomputable def crossDistanceSet (A B : Finset X) : Finset ℝ :=
  (A ×ˢ B).image fun p : X × X => dist p.1 p.2

variable (X) in
noncomputable def minimalCrossDistances (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ A B : Finset X, #A = n ∧ #B = n ∧ Disjoint A B ∧
    #(crossDistanceSet A B) = m}
/-- Membership criterion for the bipartite cross-distance set. -/
theorem mem_crossDistanceSet {A B : Finset X} {r : ℝ} :
    r ∈ crossDistanceSet A B ↔ ∃ a ∈ A, ∃ b ∈ B, dist a b = r := by
  simp only [crossDistanceSet, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, b, ⟨ha, hb⟩, rfl⟩

/-- Cross-distances across a disjoint pair are among all distances of the union. -/
theorem crossDistanceSet_subset_distanceSet_union {A B : Finset X} (hAB : Disjoint A B) :
    crossDistanceSet A B ⊆ distanceSet (A ∪ B) := by
  intro r hr
  rcases mem_crossDistanceSet.mp hr with ⟨a, ha, b, hb, rfl⟩
  have hab : a ≠ b := by
    rintro rfl
    exact Finset.disjoint_left.mp hAB ha hb
  unfold distanceSet
  rw [Finset.mem_image]
  exact ⟨(a, b), Finset.mem_offDiag.mpr ⟨Finset.mem_union_left B ha, Finset.mem_union_right A hb, hab⟩, rfl⟩

/-- Cardinality version of the inclusion above. -/
theorem card_crossDistanceSet_le_distinctDistances_union {A B : Finset X} (hAB : Disjoint A B) :
    #(crossDistanceSet A B) ≤ distinctDistances (A ∪ B) :=
  Finset.card_le_card (crossDistanceSet_subset_distanceSet_union hAB)

/-- Disjoint finite sets of a prescribed size exist in any infinite metric space. -/
theorem exists_disjoint_finset_card_eq (X : Type*) [MetricSpace X] [Infinite X] (n : ℕ) :
    ∃ A B : Finset X, #A = n ∧ #B = n ∧ Disjoint A B := by
  obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq X (2 * n)
  have hn : n ≤ #S := by omega
  obtain ⟨A, hAS, hA⟩ := Finset.exists_subset_card_eq hn
  refine ⟨A, S \ A, hA, ?_, disjoint_sdiff_self_right⟩
  rw [Finset.card_sdiff_of_subset hAS, hS, hA]
  omega

/-- Realized cross-distance counts are nonempty in any infinite metric space. -/
theorem validCrossDistancesSet_nonempty (X : Type*) [MetricSpace X] [Infinite X] (n : ℕ) :
    {m : ℕ | ∃ A B : Finset X, #A = n ∧ #B = n ∧ Disjoint A B ∧
      #(crossDistanceSet A B) = m}.Nonempty := by
  obtain ⟨A, B, hA, hB, hAB⟩ := exists_disjoint_finset_card_eq X n
  exact ⟨#(crossDistanceSet A B), A, B, hA, hB, hAB, rfl⟩

/-- A minimizing disjoint pair realizes `minimalCrossDistances`. -/
theorem exists_minimizer_crossDistances (X : Type*) [MetricSpace X] [Infinite X] (n : ℕ) :
    ∃ A B : Finset X, #A = n ∧ #B = n ∧ Disjoint A B ∧
      #(crossDistanceSet A B) = minimalCrossDistances X n :=
  Nat.sInf_mem (validCrossDistancesSet_nonempty X n)

/-- Any disjoint pair of prescribed sizes upper-bounds `minimalCrossDistances`. -/
theorem minimalCrossDistances_le_of_witness {A B : Finset X} {n : ℕ}
    (hA : #A = n) (hB : #B = n) (hAB : Disjoint A B) :
    minimalCrossDistances X n ≤ #(crossDistanceSet A B) :=
  Nat.sInf_le ⟨A, B, hA, hB, hAB, rfl⟩

/-- The universal comparison bound, generalized to any infinite metric space. -/
theorem minimalCrossDistances_le_minimalDistinctDistances_two_mul [Infinite X] (n : ℕ) :
    minimalCrossDistances X n ≤ minimalDistinctDistances X (2 * n) := by
  obtain ⟨S, hS, hdistS⟩ := Erdos661Helpers.exists_minimizer_distinctDistances X (2 * n)
  have hn : n ≤ #S := by omega
  obtain ⟨A, hAS, hA⟩ := Finset.exists_subset_card_eq hn
  let B := S \ A
  have hB : #B = n := by
    dsimp [B]
    rw [Finset.card_sdiff_of_subset hAS, hS, hA]
    omega
  have hAB : Disjoint A B := disjoint_sdiff_self_right
  have hunion : A ∪ B = S := Finset.union_sdiff_of_subset hAS
  calc
    minimalCrossDistances X n ≤ #(crossDistanceSet A B) :=
      minimalCrossDistances_le_of_witness hA hB hAB
    _ ≤ distinctDistances (A ∪ B) := card_crossDistanceSet_le_distinctDistances_union hAB
    _ = distinctDistances S := by rw [hunion]
    _ = minimalDistinctDistances X (2 * n) := hdistS

/-- The planar instance of the universal comparison bound (`erdos_661.variants.le_minimalDistinctDistances`).
This statement already carries a complete inline proof upstream in Formal Conjectures (PR #7490);
it is recorded here only as an internal supporting lemma and is not exported as a package result. -/
theorem le_minimalDistinctDistances_plane (n : ℕ) :
    minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n) := by
  have : Infinite ℝ² := Erdos661Helpers.infinite_euclideanSpace (by decide : 1 ≤ 2)
  exact minimalCrossDistances_le_minimalDistinctDistances_two_mul n

/-- First coordinate of the rational parameterization of the unit circle at index `k : ℕ`. -/
def ratCos (k : ℕ) : ℝ := ((k : ℝ) ^ 2 - 1) / ((k : ℝ) ^ 2 + 1)

/-- Second coordinate of the rational parameterization of the unit circle at index `k : ℕ`. -/
def ratSin (k : ℕ) : ℝ := 2 * (k : ℝ) / ((k : ℝ) ^ 2 + 1)

/-- Exact Pythagorean identity `(ratCos k) ^ 2 + (ratSin k) ^ 2 = 1` for all `k : ℕ`. -/
theorem ratCos_sq_add_ratSin_sq (k : ℕ) : ratCos k ^ 2 + ratSin k ^ 2 = 1 := by
  unfold ratCos ratSin
  have hpos : (0 : ℝ) < (k : ℝ) ^ 2 + 1 := by positivity
  field_simp [hpos.ne']
  ring

/-- `ratCos : ℕ → ℝ` is injective on `ℕ`. -/
theorem ratCos_injective : Function.Injective ratCos := by
  intro j k hjk
  unfold ratCos at hjk
  have hj : (0 : ℝ) < (j : ℝ) ^ 2 + 1 := by positivity
  have hk : (0 : ℝ) < (k : ℝ) ^ 2 + 1 := by positivity
  have h1 : ((j : ℝ) ^ 2 - 1) * ((k : ℝ) ^ 2 + 1) = ((k : ℝ) ^ 2 - 1) * ((j : ℝ) ^ 2 + 1) :=
    (div_eq_div_iff hj.ne' hk.ne').mp hjk
  have hsq : (j : ℝ) ^ 2 = (k : ℝ) ^ 2 := by linarith
  have hnn_j : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hnn_k : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have heq : (j : ℝ) = (k : ℝ) := by nlinarith
  exact Nat.cast_injective heq

/-- Lenz's first-circle point in `ℝ⁴` of radius `1 / √2` in the `(x₀, x₁)` plane. -/
def lenzPointA (k : ℕ) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![ratCos k / Real.sqrt 2, ratSin k / Real.sqrt 2, 0, 0]

/-- Lenz's second-circle point in `ℝ⁴` of radius `1 / √2` in the orthogonal `(x₂, x₃)` plane. -/
def lenzPointB (k : ℕ) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![0, 0, ratCos k / Real.sqrt 2, ratSin k / Real.sqrt 2]

theorem lenzPointA_injective : Function.Injective lenzPointA := by
  intro j k hjk
  have h0 := congrArg (fun x : EuclideanSpace ℝ (Fin 4) => x.ofLp 0) hjk
  simp only [lenzPointA, Matrix.cons_val_zero] at h0
  have hsqrt : (Real.sqrt 2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  exact ratCos_injective (div_left_inj' hsqrt |>.mp h0)

theorem lenzPointB_injective : Function.Injective lenzPointB := by
  intro j k hjk
  have h2 := congrArg (fun x : EuclideanSpace ℝ (Fin 4) => x.ofLp 2) hjk
  simp only [lenzPointB, Matrix.cons_val_two, Matrix.cons_val_zero,
    Matrix.tail_cons, Matrix.head_cons] at h2
  have hsqrt : (Real.sqrt 2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  exact ratCos_injective (div_left_inj' hsqrt |>.mp h2)

theorem lenzPointA_ne_lenzPointB (j k : ℕ) : lenzPointA j ≠ lenzPointB k := by
  intro h
  have h0 := congrArg (fun x : EuclideanSpace ℝ (Fin 4) => x.ofLp 0) h
  have h1 := congrArg (fun x : EuclideanSpace ℝ (Fin 4) => x.ofLp 1) h
  simp only [lenzPointA, lenzPointB, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at h0 h1
  have hsqrt : (Real.sqrt 2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hc : ratCos j = 0 := (div_eq_zero_iff.mp h0).resolve_right hsqrt
  have hs : ratSin j = 0 := (div_eq_zero_iff.mp h1).resolve_right hsqrt
  have hsq := ratCos_sq_add_ratSin_sq j
  rw [hc, hs] at hsq
  norm_num at hsq

/-- Every point on Lenz's first circle has distance `1` to every point on Lenz's second circle. -/
theorem dist_lenzPointA_lenzPointB (j k : ℕ) :
    dist (lenzPointA j) (lenzPointB k) = 1 := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_four]
  simp only [lenzPointA, lenzPointB, Real.dist_eq, sq_abs,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  have hsqrt2 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hj := ratCos_sq_add_ratSin_sq j
  have hk := ratCos_sq_add_ratSin_sq k
  have hsum : (ratCos j / Real.sqrt 2 - 0) ^ 2 + (ratSin j / Real.sqrt 2 - 0) ^ 2 +
      (0 - ratCos k / Real.sqrt 2) ^ 2 + (0 - ratSin k / Real.sqrt 2) ^ 2 = 1 := by
    calc
      (ratCos j / Real.sqrt 2 - 0) ^ 2 + (ratSin j / Real.sqrt 2 - 0) ^ 2 +
          (0 - ratCos k / Real.sqrt 2) ^ 2 + (0 - ratSin k / Real.sqrt 2) ^ 2
        = (ratCos j ^ 2 + ratSin j ^ 2) / (Real.sqrt 2) ^ 2 +
            (ratCos k ^ 2 + ratSin k ^ 2) / (Real.sqrt 2) ^ 2 := by ring
      _ = 1 / 2 + 1 / 2 := by rw [hj, hk, hsqrt2]
      _ = 1 := by norm_num
  rw [hsum, Real.sqrt_one]

/-- The `n`-point finite set on Lenz's first circle in `ℝ⁴`. -/
def lenzSetA (n : ℕ) : Finset (EuclideanSpace ℝ (Fin 4)) :=
  (Finset.range n).image lenzPointA

/-- The `n`-point finite set on Lenz's second circle in `ℝ⁴`. -/
def lenzSetB (n : ℕ) : Finset (EuclideanSpace ℝ (Fin 4)) :=
  (Finset.range n).image lenzPointB

@[simp]
theorem lenzSetA_card (n : ℕ) : #(lenzSetA n) = n := by
  rw [lenzSetA, Finset.card_image_of_injective _ lenzPointA_injective, Finset.card_range]

@[simp]
theorem lenzSetB_card (n : ℕ) : #(lenzSetB n) = n := by
  rw [lenzSetB, Finset.card_image_of_injective _ lenzPointB_injective, Finset.card_range]

theorem disjoint_lenzSetA_lenzSetB (n : ℕ) : Disjoint (lenzSetA n) (lenzSetB n) := by
  rw [Finset.disjoint_left]
  simp only [lenzSetA, lenzSetB, Finset.mem_image]
  rintro _ ⟨j, _, rfl⟩ ⟨k, _, hjk⟩
  exact lenzPointA_ne_lenzPointB j k hjk.symm

/-- Complete proof of `erdos_661.variants.lenz`:
for every `n : ℕ`, there exist disjoint `n`-point sets `A, B ⊆ ℝ⁴` such that
`∀ x ∈ A, ∀ y ∈ B, dist x y = 1`. -/
theorem lenz_r4 (n : ℕ) :
    ∃ A B : Finset (EuclideanSpace ℝ (Fin 4)), #A = n ∧ #B = n ∧ Disjoint A B ∧
      ∀ x ∈ A, ∀ y ∈ B, dist x y = 1 := by
  refine ⟨lenzSetA n, lenzSetB n, lenzSetA_card n, lenzSetB_card n,
    disjoint_lenzSetA_lenzSetB n, ?_⟩
  intro x hx y hy
  rcases Finset.mem_image.mp hx with ⟨j, _, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨k, _, rfl⟩
  exact dist_lenzPointA_lenzPointB j k

end Erdos661
