module

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

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Geometry.Euclidean.Sphere.SecondInter
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Topology.MetricSpace.DilationEquiv
public import Mathlib.Tactic

@[expose] public section

/- Auxiliary literal distance-set erasure interfaces. No optimal-seed existence
or original eventual nonuniqueness theorem is assumed or asserted. -/
namespace Erdos91.DistanceErasure

variable {X : Type*} [MetricSpace X] [DecidableEq X]

noncomputable def distanceSet (S : Finset X) : Finset ℝ := by
  classical
  exact S.offDiag.image (fun p => dist p.1 p.2)

omit [DecidableEq X] in
theorem mem_distanceSet (S : Finset X) (r : ℝ) :
    r ∈ distanceSet S ↔ ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ dist a b = r := by
  classical
  constructor
  · rintro hr
    obtain ⟨⟨a, b⟩, hab, hd⟩ := Finset.mem_image.mp hr
    obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hab
    exact ⟨a, ha, b, hb, hne, hd⟩
  · rintro ⟨a, ha, b, hb, hne, hd⟩
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, hne⟩, hd⟩

end Erdos91.DistanceErasure

namespace Erdos91.ErasureCount

open Erdos91.DistanceErasure
variable {X : Type*} [MetricSpace X] [DecidableEq X]

end Erdos91.ErasureCount

/- The three distance definitions and IsOptimal follow formal-conjectures,
Apache-2.0, The Formal Conjectures Authors. No conjectural declaration imported. -/
namespace Minimizer91
abbrev Plane := EuclideanSpace ℝ (Fin 2)
noncomputable def distanceSet (points : Finset Plane) : Finset ℝ :=
  points.offDiag.image fun pair => dist pair.1 pair.2
noncomputable def distinctDistances (points : Finset Plane) : ℕ :=
  (distanceSet points).card
noncomputable def minimalDistinctDistances (n : ℕ) : ℕ :=
  sInf {(distinctDistances points : ℝ) | (points : Finset Plane) (_ : points.card = n)}
noncomputable def IsOptimal (A : Finset Plane) (n : ℕ) : Prop :=
  A.card = n ∧ distinctDistances A = minimalDistinctDistances n

private theorem exists_card (n : ℕ) : ∃ A : Finset Plane, A.card = n := by
  classical
  let f : ℕ → Plane := fun k => !₂[(k : ℝ), 0]
  have hf : Function.Injective f := by
    intro a b h
    have h0 := congrArg (fun p : Plane => p 0) h
    simpa [f] using h0
  exact ⟨(Finset.range n).image f, by simp [Finset.card_image_of_injective _ hf]⟩

theorem minimal_le (A : Finset Plane) (n : ℕ) (h : A.card = n) :
    minimalDistinctDistances n ≤ distinctDistances A := by
  apply Nat.sInf_le
  exact ⟨A, h, rfl⟩

theorem exists_optimal (n : ℕ) : ∃ A : Finset Plane, IsOptimal A n := by
  obtain ⟨A, hA⟩ := exists_card n
  have hne : ({(distinctDistances points : ℝ) | (points : Finset Plane)
      (_ : points.card = n)} : Set ℕ).Nonempty := by
    exact ⟨distinctDistances A, A, hA, rfl⟩
  obtain ⟨B, hB, heq⟩ := csInf_mem hne
  refine ⟨B, hB, ?_⟩
  unfold minimalDistinctDistances
  exact_mod_cast heq
end Minimizer91

namespace Erdos91.OptimalDeletion
open Erdos91.DistanceErasure Erdos91.ErasureCount

end Erdos91.OptimalDeletion

namespace Erdos91.OptimalDeletion
open Erdos91.DistanceErasure Erdos91.ErasureCount

end Erdos91.OptimalDeletion
namespace SimilarityEnergy91
open Finset
abbrev Plane := EuclideanSpace ℝ (Fin 2)
noncomputable def pairEnergy (A : Finset Plane) : ℝ := ∑ x ∈ A, ∑ y ∈ A, dist x y ^ 2

theorem pairEnergy_image (A : Finset Plane) (f : Plane ≃ᵈ Plane) :
    pairEnergy (A.image f) = (Dilation.ratio f : ℝ)^2 * pairEnergy A := by
  classical
  unfold pairEnergy
  rw [Finset.sum_image]
  · simp_rw [Finset.sum_image (fun x _ y _ h => f.injective h), Dilation.dist_eq,
      mul_pow, ← Finset.mul_sum]
  · intro x hx y hy h
    exact f.injective h

theorem ratio_one_of_shared_diameter (A B : Finset Plane) (f : Plane ≃ᵈ Plane)
    (himage : A.image f = B) (a b : Plane) (hab : a ≠ b)
    (haA : a ∈ A) (hbA : b ∈ A) (haB : a ∈ B) (hbB : b ∈ B)
    (hA : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ dist a b)
    (hB : ∀ x ∈ B, ∀ y ∈ B, dist x y ≤ dist a b) :
    (Dilation.ratio f : ℝ) = 1 := by
  classical
  have hd : 0 < dist a b := dist_pos.mpr hab
  have hfa : f a ∈ B := himage ▸ Finset.mem_image_of_mem f haA
  have hfb : f b ∈ B := himage ▸ Finset.mem_image_of_mem f hbA
  have hupper := hB (f a) hfa (f b) hfb
  rw [Dilation.dist_eq] at hupper
  have hratio : 0 ≤ (Dilation.ratio f : ℝ) := NNReal.coe_nonneg _
  rw [← himage] at haB hbB
  obtain ⟨x, hx, hxa⟩ := Finset.mem_image.mp haB
  obtain ⟨y, hy, hyb⟩ := Finset.mem_image.mp hbB
  have hdist : dist a b = (Dilation.ratio f : ℝ) * dist x y := by
    rw [← hxa, ← hyb, Dilation.dist_eq]
  have hlower := mul_le_mul_of_nonneg_left (hA x hx y hy) hratio
  rw [← hdist] at hlower
  nlinarith

theorem pairEnergy_eq_of_shared_diameter (A B : Finset Plane) (f : Plane ≃ᵈ Plane)
    (himage : A.image f = B) (a b : Plane) (hab : a ≠ b)
    (haA : a ∈ A) (hbA : b ∈ A) (haB : a ∈ B) (hbB : b ∈ B)
    (hA : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ dist a b)
    (hB : ∀ x ∈ B, ∀ y ∈ B, dist x y ≤ dist a b) : pairEnergy A = pairEnergy B := by
  have hr := ratio_one_of_shared_diameter A B f himage a b hab haA hbA haB hbB hA hB
  have he := pairEnergy_image A f
  rw [himage, hr] at he
  simpa using he.symm

end SimilarityEnergy91
namespace Erdos91.DeletionSpectrum
open Erdos91.DistanceErasure Erdos91.ErasureCount Erdos91.OptimalDeletion

theorem exists_diameter_pair (S : Finset Minimizer91.Plane) (hcard : 1 < S.card) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ dist a b := by
  classical
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hcard
  have hnon : S.offDiag.Nonempty :=
    ⟨(u, v), Finset.mem_offDiag.mpr ⟨hu, hv, huv⟩⟩
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image S.offDiag
    (fun q : Minimizer91.Plane × Minimizer91.Plane => dist q.1 q.2) hnon
  obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hp
  refine ⟨p.1, ha, p.2, hb, hab, ?_⟩
  intro x hx y hy
  by_cases hxy : x = y
  · subst y
    simpa only [dist_self] using dist_nonneg (x := p.1) (y := p.2)
  · exact hmax (x, y) (Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩)

end Erdos91.DeletionSpectrum

namespace EnergyLevels91
open Finset
abbrev Plane := EuclideanSpace ℝ (Fin 2)
noncomputable def energy (S : Finset Plane) (v : Plane) : ℝ := ∑ x ∈ S, dist v x^2
end EnergyLevels91

namespace DeletionEnergy91
open Finset
open SimilarityEnergy91 EnergyLevels91
abbrev Plane := EuclideanSpace ℝ (Fin 2)

theorem deletion_identity (S : Finset Plane) (v : Plane) (hv : v ∈ S) :
    pairEnergy (S.erase v) = pairEnergy S - 2*energy S v := by
  classical
  have hi (x : Plane) : (∑ y ∈ S.erase v, dist x y^2) =
      (∑ y ∈ S, dist x y^2) - dist x v^2 := by
    exact sum_erase_eq_sub hv
  unfold pairEnergy
  simp_rw [hi]
  rw [sum_sub_distrib, sum_erase_eq_sub hv, sum_erase_eq_sub hv]
  have hc : (∑ x ∈ S, dist x v^2) = energy S v := by
    unfold energy
    apply sum_congr rfl
    intro x hx
    rw [dist_comm]
  rw [hc]
  simp only [dist_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero]
  unfold energy
  ring
end DeletionEnergy91
namespace MinimumMonotone91
open Minimizer91

theorem distance_count_mono {A B : Finset Plane} (h : A ⊆ B) :
    distinctDistances A ≤ distinctDistances B := by
  classical
  exact Finset.card_le_card (Finset.image_subset_image (Finset.offDiag_mono h))

theorem minimum_monotone : Monotone minimalDistinctDistances := by
  intro m n hmn
  obtain ⟨B, hBcard, hBmin⟩ := exists_optimal n
  obtain ⟨A, hAB, hAcard⟩ := Finset.exists_subset_card_eq (hmn.trans_eq hBcard.symm)
  calc
    minimalDistinctDistances m ≤ distinctDistances A := minimal_le A m hAcard
    _ ≤ distinctDistances B := distance_count_mono hAB
    _ = minimalDistinctDistances n := hBmin

theorem plateau_subset_optimal (A B : Finset Plane) (m n : ℕ)
    (hB : IsOptimal B n) (hAB : A ⊆ B) (hA : A.card = m)
    (hplateau : minimalDistinctDistances m = minimalDistinctDistances n) :
    IsOptimal A m := by
  refine ⟨hA, le_antisymm ?_ (minimal_le A m hA)⟩
  calc
    distinctDistances A ≤ distinctDistances B := distance_count_mono hAB
    _ = minimalDistinctDistances n := hB.2
    _ = minimalDistinctDistances m := hplateau.symm

end MinimumMonotone91

namespace PlateauDefinitions91
open Minimizer91

def DilationEquivSimilar (A B : Finset Plane) : Prop :=
  ∃ f : Plane ≃ᵈ Plane, f '' (A : Set Plane) = (B : Set Plane)

def UniqueMinimizer (n : ℕ) : Prop :=
  ∀ A B : Finset Plane, IsOptimal A n → IsOptimal B n → DilationEquivSimilar A B

theorem similar_iff_image (A B : Finset Plane) :
    DilationEquivSimilar A B ↔ ∃ f : Plane ≃ᵈ Plane, A.image f = B := by
  classical
  unfold DilationEquivSimilar
  apply exists_congr
  intro f
  rw [← Finset.coe_image]
  exact Finset.coe_inj

theorem exists_diameter_pair (S : Finset Plane) (hS : 2 ≤ S.card) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ dist a b :=
  Erdos91.DeletionSpectrum.exists_diameter_pair S (by omega)

end PlateauDefinitions91

namespace CircleFibers91
open Finset
abbrev Plane := EuclideanSpace ℝ (Fin 2)

theorem two_centers_card (B : Finset Plane) (c p : Plane) (r t : ℝ)
    (hcp : c ≠ p) (hc : ∀ v ∈ B, dist v c = r)
    (hp : ∀ v ∈ B, dist v p = t) : B.card ≤ 2 := by
  classical
  by_cases hB : B.card ≤ 1
  · omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < B.card)
  have hsub : B ⊆ {x, y} := by
    intro v hv
    have he := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
      (V := Plane) (by simp : Module.finrank ℝ Plane = 2)
      hcp hxy (hc x hx) (hc y hy) (hc v hv) (hp x hx) (hp y hy) (hp v hv)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using he
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

theorem circle_card (B : Finset Plane) (c p : Plane) (r : ℝ)
    (hcp : c ≠ p) (hc : ∀ v ∈ B, dist v c = r) :
    B.card ≤ 2 * (B.image (fun v => dist v p)).card := by
  classical
  rw [Finset.card_eq_sum_card_image (fun v => dist v p) B]
  calc
    (∑ t ∈ B.image (fun v => dist v p), (B.filter (fun v => dist v p = t)).card)
        ≤ ∑ _t ∈ B.image (fun v => dist v p), 2 := by
      apply Finset.sum_le_sum
      intro t ht
      apply two_centers_card _ c p r t hcp
      · intro v hv
        exact hc v (Finset.mem_filter.mp hv).1
      · intro v hv
        exact (Finset.mem_filter.mp hv).2
    _ = _ := by simp [Nat.mul_comm]

end CircleFibers91

namespace CircleLevels91
open Finset
abbrev Plane := EuclideanSpace ℝ (Fin 2)

theorem distance_images_product (B : Finset Plane) (c p : Plane) (hcp : c ≠ p) :
    B.card ≤ 2 * (B.image (fun v => dist v p)).card *
      (B.image (fun v => dist v c)).card := by
  classical
  rw [Finset.card_eq_sum_card_image (fun v => dist v c) B]
  calc
    (∑ r ∈ B.image (fun v => dist v c), (B.filter (fun v => dist v c = r)).card)
        ≤ ∑ _r ∈ B.image (fun v => dist v c),
          2 * (B.image (fun v => dist v p)).card := by
      apply Finset.sum_le_sum
      intro r hr
      have hc : ∀ v ∈ B.filter (fun v => dist v c = r), dist v c = r := by
        intro v hv
        exact (Finset.mem_filter.mp hv).2
      have bound := CircleFibers91.circle_card (B.filter (fun v => dist v c = r))
        c p r hcp hc
      have sub : (B.filter (fun v => dist v c = r)).image (fun v => dist v p)
          ⊆ B.image (fun v => dist v p) := Finset.image_subset_image (Finset.filter_subset _ _)
      exact bound.trans (Nat.mul_le_mul_left 2 (Finset.card_le_card sub))
    _ = _ := by simp [Nat.mul_comm]

end CircleLevels91

namespace Energy91
open Finset
open scoped RealInnerProductSpace
abbrev Plane := EuclideanSpace ℝ (Fin 2)

theorem centered_energy (S : Finset Plane) (c v : Plane)
    (hc : ∑ x ∈ S, (x - c) = 0) :
    (∑ x ∈ S, dist v x ^ 2) =
      (S.card : ℝ) * dist v c ^ 2 + ∑ x ∈ S, dist x c ^ 2 := by
  have hpoint (x : Plane) : dist v x ^ 2 = dist v c ^ 2 -
      2 * inner ℝ (v - c) (x - c) + dist x c ^ 2 := by
    simp only [dist_eq_norm]
    rw [show v - x = (v - c) - (x - c) by abel, norm_sub_sq_real]
  have hz : (∑ x ∈ S, inner ℝ (v - c) (x - c)) = 0 := by
    rw [← inner_sum, hc]
    simp
  calc
    (∑ x ∈ S, dist v x ^ 2) = ∑ x ∈ S,
        (dist v c ^ 2 - 2 * inner ℝ (v - c) (x - c) + dist x c ^ 2) := by
      apply sum_congr rfl
      intro x hx
      exact hpoint x
    _ = _ := by
      simp only [sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul,
        ← mul_sum, hz, mul_zero, sub_zero]

theorem centroid_energy (S : Finset Plane) (hS : S.Nonempty) (v : Plane) :
    let c : Plane := (S.card : ℝ)⁻¹ • (∑ x ∈ S, x)
    (∑ x ∈ S, dist v x ^ 2) = (S.card : ℝ) * dist v c ^ 2 + ∑ x ∈ S, dist x c ^ 2 := by
  intro c
  apply centered_energy S c v
  have hn : (S.card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hS).ne'
  simp only [sum_sub_distrib, sum_const, c, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, mul_inv_cancel₀ hn, one_smul, sub_self]

end Energy91

namespace EnergyLevels91
open Finset

noncomputable def centroid (S : Finset Plane) : Plane := (S.card : ℝ)⁻¹ • ∑ x ∈ S, x

theorem radius_energy_card (S B : Finset Plane) (hS : S.Nonempty) :
    (B.image (fun v => dist v (centroid S))).card = (B.image (energy S)).card := by
  classical
  let c := centroid S
  let K : ℝ := ∑ x ∈ S, dist x c ^ 2
  let f : ℝ → ℝ := fun r => (S.card : ℝ) * r ^ 2 + K
  have hv (v : Plane) : energy S v = f (dist v c) :=
    Energy91.centroid_energy S hS v
  have him : (B.image (energy S)) = (B.image (fun v => dist v c)).image f := by
    rw [image_image]
    apply image_congr
    intro v hvB
    exact hv v
  have hinj : Set.InjOn f (B.image (fun v => dist v c)) := by
    intro a ha b hb heq
    obtain ⟨u, hu, rfl⟩ := mem_image.mp ha
    obtain ⟨v, hvB, rfl⟩ := mem_image.mp hb
    have hm : (0 : ℝ) < S.card := by exact_mod_cast card_pos.mpr hS
    have ha := dist_nonneg (x := u) (y := c)
    have hb := dist_nonneg (x := v) (y := c)
    dsimp [f] at heq
    have he : dist u c ^ 2 = dist v c ^ 2 := by nlinarith
    nlinarith
  rw [him, card_image_of_injOn hinj]

theorem energy_level_bound (S B : Finset Plane) (hS : S.Nonempty)
    (hBS : B ⊆ S) (p : Plane) (hp : p ∈ S) (hpB : p ∉ B)
    (hcp : centroid S ≠ p) :
    B.card ≤ 2 * (Minimizer91.distanceSet S).card * (B.image (energy S)).card := by
  classical
  have hsub : B.image (fun v => dist v p) ⊆ Minimizer91.distanceSet S := by
    intro r hr
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hr
    apply mem_image.mpr
    refine ⟨(v, p), mem_offDiag.mpr ⟨hBS hv, hp, ?_⟩, rfl⟩
    intro heq
    change v = p at heq
    exact hpB (heq ▸ hv)
  have h := CircleLevels91.distance_images_product B (centroid S) p hcp
  rw [radius_energy_card S B hS] at h
  exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (card_le_card hsub)))

end EnergyLevels91

namespace DeletionEnergy91
open Finset
open SimilarityEnergy91 EnergyLevels91

theorem nonsimilar_deletions (S : Finset Plane) (a b v w : Plane)
    (hab : a ≠ b) (ha : a ∈ S) (hb : b ∈ S) (hv : v ∈ S) (hw : w ∈ S)
    (hva : v ≠ a) (hvb : v ≠ b) (hwa : w ≠ a) (hwb : w ≠ b)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ dist a b)
    (hne : energy S v ≠ energy S w) :
    ¬ ∃ f : Plane ≃ᵈ Plane, (S.erase v).image f = S.erase w := by
  classical
  rintro ⟨f, hf⟩
  have he := pairEnergy_eq_of_shared_diameter (S.erase v) (S.erase w) f hf a b hab
    (mem_erase.mpr ⟨Ne.symm hva, ha⟩) (mem_erase.mpr ⟨Ne.symm hvb, hb⟩)
    (mem_erase.mpr ⟨Ne.symm hwa, ha⟩) (mem_erase.mpr ⟨Ne.symm hwb, hb⟩)
    (fun x hx y hy => hdiam x (mem_of_mem_erase hx) y (mem_of_mem_erase hy))
    (fun x hx y hy => hdiam x (mem_of_mem_erase hx) y (mem_of_mem_erase hy))
  rw [deletion_identity S v hv, deletion_identity S w hw] at he
  apply hne
  linarith

end DeletionEnergy91

namespace PlateauNonunique91
open Finset Minimizer91 PlateauDefinitions91

theorem low_distance_plateau_not_unique (n : ℕ) (hn : 3 ≤ n)
    (hplateau : minimalDistinctDistances n = minimalDistinctDistances (n + 1))
    (hlow : 2 * minimalDistinctDistances n < n - 1) : ¬ UniqueMinimizer n := by
  classical
  intro hunique
  obtain ⟨S, hSopt⟩ := exists_optimal (n + 1)
  have hScard : S.card = n + 1 := hSopt.1
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha, b, hb, hab, hdiam⟩ := exists_diameter_pair S (by omega)
  let B := S \ {a, b}
  have hBS : B ⊆ S := Finset.sdiff_subset
  have hmem (v : Plane) : v ∈ B ↔ v ∈ S ∧ v ≠ a ∧ v ≠ b := by
    simp only [B, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
  have hpair : ({a, b} : Finset Plane) ⊆ S := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha
    · have hxb := Finset.mem_singleton.mp hx
      exact hxb ▸ hb
  have hBcard : B.card = n - 1 := by
    rw [Finset.card_sdiff_of_subset hpair, Finset.card_pair hab, hScard]
    omega
  have hopt (v : Plane) (hv : v ∈ S) : IsOptimal (S.erase v) n := by
    apply MinimumMonotone91.plateau_subset_optimal (S.erase v) S n (n + 1)
      hSopt (Finset.erase_subset _ _) _ hplateau
    rw [Finset.card_erase_of_mem hv, hScard]
    omega
  have henergy : (B.image (EnergyLevels91.energy S)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro r hr t ht
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp ht
    have hvB := (hmem v).mp hv
    have hwB := (hmem w).mp hw
    by_contra hne
    have hnot := DeletionEnergy91.nonsimilar_deletions S a b v w hab ha hb
      hvB.1 hwB.1 hvB.2.1 hvB.2.2 hwB.2.1 hwB.2.2 hdiam hne
    exact hnot ((similar_iff_image _ _).mp (hunique _ _ (hopt v hvB.1) (hopt w hwB.1)))
  have hanchor : ∃ p ∈ S, p ∉ B ∧ EnergyLevels91.centroid S ≠ p := by
    by_cases hc : EnergyLevels91.centroid S = a
    · refine ⟨b, hb, ?_, ?_⟩
      · simp [hmem]
      · simpa only [hc] using hab
    · refine ⟨a, ha, ?_, hc⟩
      simp [hmem]
  obtain ⟨p, hp, hpB, hcp⟩ := hanchor
  have bound := EnergyLevels91.energy_level_bound S B hSne hBS p hp hpB hcp
  have hd : (distanceSet S).card = minimalDistinctDistances n := by
    exact hSopt.2.trans hplateau.symm
  rw [hBcard, hd] at bound
  have hbnd := bound.trans (Nat.mul_le_mul_left (2 * minimalDistinctDistances n) henergy)
  simp only [Nat.mul_one] at hbnd
  omega

end PlateauNonunique91

namespace DeletionFamily91
open Finset Minimizer91 PlateauDefinitions91
open EnergyLevels91 (energy centroid energy_level_bound)

end DeletionFamily91

namespace PlateauFamily91
open Finset Minimizer91 PlateauDefinitions91

end PlateauFamily91

namespace OneStepCount91
open Finset

theorem telescope (d : ℕ → ℕ) (hd : Monotone d) (L K : ℕ) :
    (∑ n ∈ range K, (d (L + n + 1) - d (L + n))) + d L = d (L + K) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ]
    norm_num [Nat.add_assoc] at *
    have h := hd (show L + K ≤ L + K + 1 by omega)
    simp only [Nat.add_assoc] at h
    omega

theorem card_le (d : ℕ → ℕ) (hd : Monotone d) (E : Finset ℕ) (L N : ℕ)
    (hE : E ⊆ Icc L N) (hstep : ∀ n ∈ E, d n < d (n + 1)) :
    E.card ≤ d (N + 1) - d L := by
  classical
  by_cases hLN : L ≤ N + 1
  · let F := (range (N + 1 - L)).image (fun k => L + k)
    have hsub : E ⊆ F := by
      intro n hn
      have h := mem_Icc.mp (hE hn)
      apply mem_image.mpr
      refine ⟨n - L, mem_range.mpr (by omega), by omega⟩
    have hb : E.card ≤ ∑ n ∈ F, (d (n + 1) - d n) := by
      calc
        E.card = ∑ _n ∈ E, 1 := by simp
        _ ≤ ∑ n ∈ E, (d (n + 1) - d n) := by
          apply sum_le_sum
          intro n hn
          have := hstep n hn
          omega
        _ ≤ ∑ n ∈ F, (d (n + 1) - d n) := sum_le_sum_of_subset hsub
    have ht := telescope d hd L (N + 1 - L)
    have hi : ∑ n ∈ F, (d (n + 1) - d n) =
        ∑ k ∈ range (N + 1 - L), (d (L + k + 1) - d (L + k)) := by
      unfold F
      rw [sum_image]
      intro a ha b hb heq
      exact Nat.add_left_cancel heq
    rw [hi] at hb
    have heq : L + (N + 1 - L) = N + 1 := by omega
    rw [heq] at ht
    omega
  · have hem : E = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro n hn
      have := mem_Icc.mp (hE hn)
      omega
    simp [hem]

end OneStepCount91

namespace ExceptionCount91
open Finset

theorem telescope (d : ℕ → ℕ) (hd : Monotone d) (N : ℕ) :
    (∑ n ∈ range N, (d (n + 2) - d n)) + d 0 + d 1 = d N + d (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    norm_num [Nat.add_assoc] at *
    have h := hd (show N ≤ N + 2 by omega)
    omega

end ExceptionCount91

/-! ## Quadratic Lower Bound, Unboundedness, and Infinite Strict Rises -/

namespace Erdos91.UnboundedRises
open Finset Minimizer91

theorem card_sub_two_le_two_mul_distinctDistances_sq (S : Finset Plane) :
    S.card - 2 ≤ 2 * (distinctDistances S) ^ 2 := by
  classical
  by_cases hcard : S.card < 2
  · omega
  · obtain ⟨c, hc, p, hp, hcp⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    let B := (S.erase c).erase p
    have hpErase : p ∈ S.erase c := Finset.mem_erase.mpr ⟨hcp.symm, hp⟩
    have hBcard : B.card = S.card - 2 := by
      dsimp [B]
      rw [Finset.card_erase_of_mem hpErase, Finset.card_erase_of_mem hc]
      omega
    have hsub_p : B.image (fun v => dist v p) ⊆ distanceSet S := by
      intro r hr
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨hvp, hvc⟩ := Finset.mem_erase.mp hv
      have hvS : v ∈ S := Finset.mem_of_mem_erase hvc
      exact Finset.mem_image.mpr ⟨(v, p), Finset.mem_offDiag.mpr ⟨hvS, hp, hvp⟩, rfl⟩
    have hsub_c : B.image (fun v => dist v c) ⊆ distanceSet S := by
      intro r hr
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨_, hvc⟩ := Finset.mem_erase.mp hv
      obtain ⟨hvc', hvS⟩ := Finset.mem_erase.mp hvc
      exact Finset.mem_image.mpr ⟨(v, c), Finset.mem_offDiag.mpr ⟨hvS, hc, hvc'⟩, rfl⟩
    have hprod := CircleLevels91.distance_images_product B c p hcp
    have h1 : (B.image (fun v => dist v p)).card ≤ distinctDistances S :=
      Finset.card_le_card hsub_p
    have h2 : (B.image (fun v => dist v c)).card ≤ distinctDistances S :=
      Finset.card_le_card hsub_c
    rw [hBcard] at hprod
    calc
      S.card - 2 ≤ 2 * (B.image (fun v => dist v p)).card *
          (B.image (fun v => dist v c)).card := hprod
      _ ≤ 2 * distinctDistances S * distinctDistances S :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1) h2
      _ = 2 * (distinctDistances S) ^ 2 := by ring

theorem minimal_quadratic_lower_bound (n : ℕ) :
    n - 2 ≤ 2 * (minimalDistinctDistances n) ^ 2 := by
  obtain ⟨S, hS⟩ := exists_optimal n
  have h := card_sub_two_le_two_mul_distinctDistances_sq S
  rw [hS.1, hS.2] at h
  exact h

end Erdos91.UnboundedRises

namespace Erdos91.GridUpperBound
open Finset Minimizer91 PlateauDefinitions91

noncomputable def gridPoint (p : ℕ × ℕ) : Plane := !₂[(p.1 : ℝ), (p.2 : ℝ)]

theorem gridPoint_injective : Function.Injective gridPoint := by
  intro p q h
  have h0 : (p.1 : ℝ) = (q.1 : ℝ) := congrArg (fun x : Plane => x 0) h
  have h1 : (p.2 : ℝ) = (q.2 : ℝ) := congrArg (fun x : Plane => x 1) h
  exact Prod.ext (Nat.cast_injective h0) (Nat.cast_injective h1)

noncomputable def gridSet (k : ℕ) : Finset Plane :=
  (Finset.range k ×ˢ Finset.range k).image gridPoint

theorem card_gridSet (k : ℕ) : (gridSet k).card = k * k := by
  unfold gridSet
  rw [Finset.card_image_of_injective _ gridPoint_injective,
    Finset.card_product, Finset.card_range]

noncomputable def gridNorm (p : ℕ × ℕ) : ℝ :=
  Real.sqrt ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)

theorem real_dist_sq_nat (a b : ℕ) :
    dist (a : ℝ) (b : ℝ) ^ 2 = ((Nat.dist a b : ℕ) : ℝ) ^ 2 := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab, Real.dist_eq, sq_abs, Nat.cast_sub hab]
    ring
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hba, Real.dist_eq, sq_abs, Nat.cast_sub hba]

theorem dist_gridPoint_eq (p q : ℕ × ℕ) :
    dist (gridPoint p) (gridPoint q) =
      gridNorm (if Nat.dist p.1 q.1 ≤ Nat.dist p.2 q.2 then
        (Nat.dist p.1 q.1, Nat.dist p.2 q.2)
      else
        (Nat.dist p.2 q.2, Nat.dist p.1 q.1)) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  change Real.sqrt (dist (p.1 : ℝ) (q.1 : ℝ) ^ 2 + dist (p.2 : ℝ) (q.2 : ℝ) ^ 2) = _
  rw [real_dist_sq_nat p.1 q.1, real_dist_sq_nat p.2 q.2]
  split_ifs
  · rfl
  · unfold gridNorm
    dsimp
    rw [add_comm]

def upperTriangle (k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range k ×ˢ Finset.range k).filter (fun p => p.1 ≤ p.2)

def upperTrianglePos (k : ℕ) : Finset (ℕ × ℕ) :=
  (upperTriangle k).erase (0, 0)

theorem card_upperTriangle_mul_two (k : ℕ) :
    2 * (upperTriangle k).card = k * (k + 1) := by
  classical
  let B := Finset.range k ×ˢ Finset.range k
  let L := B.filter (fun p : ℕ × ℕ => ¬ p.1 ≤ p.2)
  let D := (Finset.range k).image (fun i : ℕ => (i, i))
  have hBL : (upperTriangle k).card + L.card = k * k := by
    have h := Finset.card_filter_add_card_filter_not
      (s := B) (p := fun p : ℕ × ℕ => p.1 ≤ p.2)
    have hB : B.card = k * k := by
      dsimp [B]
      rw [Finset.card_product, Finset.card_range]
    simpa only [upperTriangle, B, L, hB] using h
  have hswap_inj : Function.Injective (Prod.swap : ℕ × ℕ → ℕ × ℕ) :=
    Prod.swap_injective
  have hD_inj : Function.Injective (fun i : ℕ => (i, i)) := by
    intro a b h
    exact (Prod.ext_iff.mp h).1
  have hDcard : D.card = k := by
    dsimp [D]
    rw [Finset.card_image_of_injective _ hD_inj, Finset.card_range]
  have hLcard : (L.image Prod.swap).card = L.card :=
    Finset.card_image_of_injective L hswap_inj
  have hdisj : Disjoint (L.image Prod.swap) D := by
    rw [Finset.disjoint_left]
    intro x hxL hxD
    obtain ⟨p, hpL, rfl⟩ := Finset.mem_image.mp hxL
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hxD
    have hp2 : ¬ p.1 ≤ p.2 := (Finset.mem_filter.mp hpL).2
    have h1 : i = p.2 := (Prod.ext_iff.mp hi).1
    have h2 : i = p.1 := (Prod.ext_iff.mp hi).2
    omega
  have hunion : L.image Prod.swap ∪ D = upperTriangle k := by
    ext ⟨x, y⟩
    simp only [Finset.mem_union, Finset.mem_image, L, D, upperTriangle, B,
      Finset.mem_filter, Finset.mem_product, Finset.mem_range, Prod.swap]
    constructor
    · rintro (⟨⟨a, b⟩, ⟨⟨ha, hb⟩, hab⟩, hpair⟩ | ⟨i, hi, hpair⟩)
      · have h1 : b = x := (Prod.ext_iff.mp hpair).1
        have h2 : a = y := (Prod.ext_iff.mp hpair).2
        omega
      · have h1 : i = x := (Prod.ext_iff.mp hpair).1
        have h2 : i = y := (Prod.ext_iff.mp hpair).2
        omega
    · rintro ⟨⟨hx, hy⟩, hxy⟩
      rcases eq_or_lt_of_le hxy with rfl | hlt
      · exact Or.inr ⟨x, hx, rfl⟩
      · exact Or.inl ⟨(y, x), ⟨⟨hy, hx⟩, by omega⟩, rfl⟩
  have hU : (upperTriangle k).card = L.card + k := by
    have hc : (L.image Prod.swap ∪ D).card = (upperTriangle k).card :=
      congrArg Finset.card hunion
    rw [Finset.card_union_of_disjoint hdisj, hLcard, hDcard] at hc
    exact hc.symm
  have hmul : k * (k + 1) = k * k + k := by ring
  omega

theorem card_upperTrianglePos_mul_two_add_two (k : ℕ) (hk : 1 ≤ k) :
    2 * (upperTrianglePos k).card + 2 = k * (k + 1) := by
  have h0 : (0, 0) ∈ upperTriangle k := by
    simp only [upperTriangle, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  have hc : (upperTrianglePos k).card + 1 = (upperTriangle k).card :=
    Finset.card_erase_add_one h0
  have h2 := card_upperTriangle_mul_two k
  omega

theorem distanceSet_gridSet_subset_image_upperTrianglePos (k : ℕ) :
    Erdos91.DistanceErasure.distanceSet (gridSet k) ⊆
      (upperTrianglePos k).image gridNorm := by
  classical
  intro r hr
  obtain ⟨a, ha, b, hb, hab, rfl⟩ :=
    (Erdos91.DistanceErasure.mem_distanceSet (gridSet k) r).mp hr
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
  have hpq : p ≠ q := fun h => hab (congrArg gridPoint h)
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hq
  rw [Finset.mem_range] at hp1 hp2 hq1 hq2
  rw [dist_gridPoint_eq p q]
  apply Finset.mem_image_of_mem gridNorm
  have hdx : Nat.dist p.1 q.1 < k := by
    unfold Nat.dist
    omega
  have hdy : Nat.dist p.2 q.2 < k := by
    unfold Nat.dist
    omega
  have hne0 : Nat.dist p.1 q.1 ≠ 0 ∨ Nat.dist p.2 q.2 ≠ 0 := by
    by_contra hboth
    push Not at hboth
    unfold Nat.dist at hboth
    apply hpq
    exact Prod.ext (by omega) (by omega)
  split_ifs with hle
  · simp only [upperTrianglePos, upperTriangle, Finset.mem_erase,
      Finset.mem_filter, Finset.mem_product, Finset.mem_range, ne_eq, Prod.mk.injEq]
    refine ⟨?_, ⟨hdx, hdy⟩, hle⟩
    omega
  · simp only [upperTrianglePos, upperTriangle, Finset.mem_erase,
      Finset.mem_filter, Finset.mem_product, Finset.mem_range, ne_eq, Prod.mk.injEq]
    refine ⟨?_, ⟨hdy, hdx⟩, by omega⟩
    omega

theorem distinctDistances_gridSet_le_upperTrianglePos (k : ℕ) :
    distinctDistances (gridSet k) ≤ (upperTrianglePos k).card := by
  classical
  exact (Finset.card_le_card (distanceSet_gridSet_subset_image_upperTrianglePos k)).trans
    Finset.card_image_le

theorem minimalDistinctDistances_sq_mul_two_add_two_le (k : ℕ) (hk : 1 ≤ k) :
    2 * minimalDistinctDistances (k * k) + 2 ≤ k * (k + 1) := by
  have hmin : minimalDistinctDistances (k * k) ≤ distinctDistances (gridSet k) :=
    minimal_le (gridSet k) (k * k) (card_gridSet k)
  have hle := distinctDistances_gridSet_le_upperTrianglePos k
  have hcard := card_upperTrianglePos_mul_two_add_two k hk
  omega
end Erdos91.GridUpperBound

namespace Erdos91.SmallCasesAndSquareBarrier
open Finset Erdos91.DistanceErasure Minimizer91 Erdos91.OptimalDeletion Erdos91.GridUpperBound

theorem plane_dist_sq (x y : Plane) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  change dist (x 0) (y 0) ^ 2 + dist (x 1) (y 1) ^ 2 = _
  rw [Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

/-- No four distinct points in the Euclidean plane can have all six pairwise
distances equal: proved via the 2D Cayley-Menger polynomial identity. -/
theorem no_four_equidistant_planar (a b c d : Plane) (r : ℝ) (hab : a ≠ b)
    (h1 : dist a b = r) (h2 : dist a c = r) (h3 : dist a d = r)
    (h4 : dist b c = r) (h5 : dist b d = r) (h6 : dist c d = r) : False := by
  let ab := (b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2
  let ac := (c 0 - a 0) ^ 2 + (c 1 - a 1) ^ 2
  let ad := (d 0 - a 0) ^ 2 + (d 1 - a 1) ^ 2
  let bc := (c 0 - b 0) ^ 2 + (c 1 - b 1) ^ 2
  let bd := (d 0 - b 0) ^ 2 + (d 1 - b 1) ^ 2
  let cd := (d 0 - c 0) ^ 2 + (d 1 - c 1) ^ 2
  have hab2 : ab = r ^ 2 := by dsimp [ab]; rw [← plane_dist_sq b a, dist_comm, h1]
  have hac2 : ac = r ^ 2 := by dsimp [ac]; rw [← plane_dist_sq c a, dist_comm, h2]
  have had2 : ad = r ^ 2 := by dsimp [ad]; rw [← plane_dist_sq d a, dist_comm, h3]
  have hbc2 : bc = r ^ 2 := by dsimp [bc]; rw [← plane_dist_sq c b, dist_comm, h4]
  have hbd2 : bd = r ^ 2 := by dsimp [bd]; rw [← plane_dist_sq d b, dist_comm, h5]
  have hcd2 : cd = r ^ 2 := by dsimp [cd]; rw [← plane_dist_sq d c, dist_comm, h6]
  have hpoly : 4 * ab * ac * ad + (ab + ac - bc) * (ab + ad - bd) * (ac + ad - cd)
      - ab * (ac + ad - cd) ^ 2 - ac * (ab + ad - bd) ^ 2 - ad * (ab + ac - bc) ^ 2 = 0 := by
    dsimp [ab, ac, ad, bc, bd, cd]
    ring
  rw [hab2, hac2, had2, hbc2, hbd2, hcd2] at hpoly
  have hr6 : r ^ 6 = 0 := by linear_combination hpoly / 2
  have hr0 : r = 0 := by simpa using hr6
  exact hab (dist_eq_zero.mp (h1.trans hr0))

/-- Any finite planar set with at most one positive distance has at most 3 points. -/
theorem equidistant_card_le_three (S : Finset Plane)
    (h : distinctDistances S ≤ 1) : S.card ≤ 3 := by
  classical
  by_contra hnot
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have hc1 : (S.erase a).card = S.card - 1 := Finset.card_erase_of_mem ha
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < (S.erase a).card)
  have hc2 : ((S.erase a).erase b).card = (S.erase a).card - 1 :=
    Finset.card_erase_of_mem hb
  obtain ⟨c, hc⟩ := Finset.card_pos.mp (by omega : 0 < ((S.erase a).erase b).card)
  have hc3 : (((S.erase a).erase b).erase c).card = ((S.erase a).erase b).card - 1 :=
    Finset.card_erase_of_mem hc
  obtain ⟨d, hd⟩ := Finset.card_pos.mp
    (by omega : 0 < (((S.erase a).erase b).erase c).card)
  obtain ⟨hdc, hd3⟩ := Finset.mem_erase.mp hd
  obtain ⟨hdb, hd2⟩ := Finset.mem_erase.mp hd3
  obtain ⟨hda, hdS⟩ := Finset.mem_erase.mp hd2
  obtain ⟨hcb, hc2'⟩ := Finset.mem_erase.mp hc
  obtain ⟨hca, hcS⟩ := Finset.mem_erase.mp hc2'
  obtain ⟨hba, hbS⟩ := Finset.mem_erase.mp hb
  have hpair (x y : Plane) (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
      dist x y = dist a b := by
    have hxy_mem : dist x y ∈ Erdos91.DistanceErasure.distanceSet S :=
      (mem_distanceSet S (dist x y)).mpr ⟨x, hx, y, hy, hxy, rfl⟩
    have hab_mem : dist a b ∈ Erdos91.DistanceErasure.distanceSet S :=
      (mem_distanceSet S (dist a b)).mpr ⟨a, ha, b, hbS, hba.symm, rfl⟩
    exact Finset.card_le_one.mp h (dist x y) hxy_mem (dist a b) hab_mem
  exact no_four_equidistant_planar a b c d (dist a b) hba.symm rfl
    (hpair a c ha hcS hca.symm)
    (hpair a d ha hdS hda.symm)
    (hpair b c hbS hcS hcb.symm)
    (hpair b d hbS hdS hdb.symm)
    (hpair c d hcS hdS hdc.symm)

theorem one_le_minimalDistinctDistances_of_two_le (n : ℕ) (hn : 2 ≤ n) :
    1 ≤ minimalDistinctDistances n := by
  obtain ⟨S, hScard, hSdist⟩ := exists_optimal n
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  have hmem : dist a b ∈ Erdos91.DistanceErasure.distanceSet S :=
    (mem_distanceSet S (dist a b)).mpr ⟨a, ha, b, hb, hab, rfl⟩
  have hpos : 0 < distinctDistances S := Finset.card_pos.mpr ⟨dist a b, hmem⟩
  omega

theorem minimalDistinctDistances_three : minimalDistinctDistances 3 = 1 := by
  classical
  have hlo := one_le_minimalDistinctDistances_of_two_le 3 (by omega)
  let p0 : Plane := !₂[0, 0]
  let p1 : Plane := !₂[1, 0]
  let p2 : Plane := !₂[1 / 2, Real.sqrt 3 / 2]
  let S : Finset Plane := {p0, p1, p2}
  have hp01 : p0 ≠ p1 := by
    intro h
    have h0 : (0 : ℝ) = 1 := congrArg (fun x : Plane => x 0) h
    norm_num at h0
  have hp02 : p0 ≠ p2 := by
    intro h
    have h0 : (0 : ℝ) = 1 / 2 := congrArg (fun x : Plane => x 0) h
    norm_num at h0
  have hp12 : p1 ≠ p2 := by
    intro h
    have h0 : (1 : ℝ) = 1 / 2 := congrArg (fun x : Plane => x 0) h
    norm_num at h0
  have hcard : S.card = 3 := by
    dsimp [S]
    rw [Finset.card_insert_of_notMem, Finset.card_pair hp12]
    simp [hp01, hp02]
  have hd01 : dist p0 p1 = 1 := by
    have hsq : dist p0 p1 ^ 2 = 1 ^ 2 := by
      rw [plane_dist_sq]
      change ((0 : ℝ) - 1) ^ 2 + ((0 : ℝ) - 0) ^ 2 = 1 ^ 2
      norm_num
    nlinarith [dist_nonneg (x := p0) (y := p1)]
  have hd02 : dist p0 p2 = 1 := by
    have hsq : dist p0 p2 ^ 2 = 1 ^ 2 := by
      rw [plane_dist_sq]
      change ((0 : ℝ) - 1 / 2) ^ 2 + ((0 : ℝ) - Real.sqrt 3 / 2) ^ 2 = 1 ^ 2
      have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      linear_combination hs / 4
    nlinarith [dist_nonneg (x := p0) (y := p2)]
  have hd12 : dist p1 p2 = 1 := by
    have hsq : dist p1 p2 ^ 2 = 1 ^ 2 := by
      rw [plane_dist_sq]
      change ((1 : ℝ) - 1 / 2) ^ 2 + ((0 : ℝ) - Real.sqrt 3 / 2) ^ 2 = 1 ^ 2
      have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      linear_combination hs / 4
    nlinarith [dist_nonneg (x := p1) (y := p2)]
  have hsub : Erdos91.DistanceErasure.distanceSet S ⊆ {1} := by
    intro r hr
    obtain ⟨a, ha, b, hb, hab, rfl⟩ := (mem_distanceSet S r).mp hr
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact False.elim (hab rfl)
    · simp [hd01]
    · simp [hd02]
    · simp [dist_comm, hd01]
    · exact False.elim (hab rfl)
    · simp [hd12]
    · simp [dist_comm, hd02]
    · simp [dist_comm, hd12]
    · exact False.elim (hab rfl)
  have hup : distinctDistances S ≤ 1 :=
    (Finset.card_le_card hsub).trans (by simp)
  have hmin := minimal_le S 3 hcard
  omega

theorem minimalDistinctDistances_four : minimalDistinctDistances 4 = 2 := by
  have hup := minimalDistinctDistances_sq_mul_two_add_two_le 2 (by omega)
  change 2 * minimalDistinctDistances 4 + 2 ≤ 2 * (2 + 1) at hup
  obtain ⟨S, hScard, hSdist⟩ := exists_optimal 4
  have hlo : 2 ≤ minimalDistinctDistances 4 := by
    by_contra hlt
    have hle1 : distinctDistances S ≤ 1 := by omega
    have hcard3 := equidistant_card_le_three S hle1
    omega
  omega

theorem unitSquare_isOptimal : IsOptimal (gridSet 2) 4 := by
  refine ⟨card_gridSet 2, ?_⟩
  have hlo := minimal_le (gridSet 2) 4 (card_gridSet 2)
  have hup := distinctDistances_gridSet_le_upperTrianglePos 2
  have hpos := card_upperTrianglePos_mul_two_add_two 2 (by omega)
  have hm4 := minimalDistinctDistances_four
  omega

end Erdos91.SmallCasesAndSquareBarrier
namespace Erdos91.FourNonuniqueAndDoubleEquilateral
open Finset Erdos91.DistanceErasure Minimizer91 PlateauDefinitions91
  Erdos91.GridUpperBound Erdos91.SmallCasesAndSquareBarrier
open EnergyLevels91 (energy)

theorem plane_ext {x y : Plane} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  apply dist_eq_zero.mp
  have hsq : dist x y ^ 2 = 0 := by
    rw [plane_dist_sq, h0, h1]
    ring
  simpa using hsq

theorem energy_image (A : Finset Plane) (f : Plane ≃ᵈ Plane) (v : Plane) :
    energy (A.image f) (f v) = (Dilation.ratio f : ℝ) ^ 2 * energy A v := by
  classical
  unfold energy
  rw [Finset.sum_image (fun x _ y _ h => f.injective h)]
  simp_rw [Dilation.dist_eq, mul_pow, ← Finset.mul_sum]

theorem energy_eq_of_similar_const {A B : Finset Plane} {c : ℝ}
    (hconst : ∀ x ∈ A, energy A x = c) {f : Plane ≃ᵈ Plane}
    (himg : A.image f = B) {w₁ w₂ : Plane} (hw₁ : w₁ ∈ B) (hw₂ : w₂ ∈ B) :
    energy B w₁ = energy B w₂ := by
  classical
  rw [← himg] at hw₁ hw₂
  obtain ⟨x₁, hx₁, rfl⟩ := Finset.mem_image.mp hw₁
  obtain ⟨x₂, hx₂, rfl⟩ := Finset.mem_image.mp hw₂
  rw [← himg, energy_image, energy_image, hconst x₁ hx₁, hconst x₂ hx₂]

theorem dist_gridPoint_sq (p q : ℕ × ℕ) :
    dist (gridPoint p) (gridPoint q) ^ 2 =
      ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 + ((p.2 : ℝ) - (q.2 : ℝ)) ^ 2 := by
  rw [plane_dist_sq]
  rfl

theorem unitSquare_energy_eq_four (x : Plane) (hx : x ∈ gridSet 2) :
    energy (gridSet 2) x = 4 := by
  classical
  obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hx
  simp only [Finset.mem_product, Finset.mem_range] at hij
  unfold energy gridSet
  rw [Finset.sum_image (fun p _ q _ h => gridPoint_injective h),
    Finset.sum_product]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, dist_gridPoint_sq]
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> norm_num

noncomputable def equiP0 : Plane := !₂[0, 0]
noncomputable def equiP1 : Plane := !₂[1, 0]
noncomputable def equiP2 : Plane := !₂[1 / 2, Real.sqrt 3 / 2]
noncomputable def equiP3 : Plane := !₂[1 / 2, -Real.sqrt 3 / 2]
noncomputable def doubleEqui : Finset Plane := {equiP0, equiP1, equiP2, equiP3}

theorem equi_pairwise_ne :
    equiP0 ≠ equiP1 ∧ equiP0 ≠ equiP2 ∧ equiP0 ≠ equiP3 ∧
      equiP1 ≠ equiP2 ∧ equiP1 ≠ equiP3 ∧ equiP2 ≠ equiP3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; have h0 : (0 : ℝ) = 1 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (0 : ℝ) = 1 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (0 : ℝ) = 1 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (1 : ℝ) = 1 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (1 : ℝ) = 1 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h
    have h1 : Real.sqrt 3 / 2 = -Real.sqrt 3 / 2 := congrArg (fun x : Plane => x 1) h
    have hpos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    linarith

theorem equi_dists :
    dist equiP0 equiP1 = 1 ∧ dist equiP0 equiP2 = 1 ∧ dist equiP0 equiP3 = 1 ∧
      dist equiP1 equiP2 = 1 ∧ dist equiP1 equiP3 = 1 ∧
      dist equiP2 equiP3 = Real.sqrt 3 := by
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos3 : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hd01 : dist equiP0 equiP1 = 1 := by
    have hsq : dist equiP0 equiP1 ^ 2 = 1 ^ 2 := by
      rw [plane_dist_sq]
      change ((0 : ℝ) - 1) ^ 2 + ((0 : ℝ) - 0) ^ 2 = 1 ^ 2
      norm_num
    nlinarith [dist_nonneg (x := equiP0) (y := equiP1)]
  have hd02 : dist equiP0 equiP2 = 1 := by
    have hsq : dist equiP0 equiP2 ^ 2 = 1 ^ 2 := by
      rw [plane_dist_sq]
      change ((0 : ℝ) - 1 / 2) ^ 2 + ((0 : ℝ) - Real.sqrt 3 / 2) ^ 2 = 1 ^ 2
      linear_combination hs3 / 4
    nlinarith [dist_nonneg (x := equiP0) (y := equiP2)]
  have hd03 : dist equiP0 equiP3 = 1 := by
    have hsq : dist equiP0 equiP3 ^ 2 = 1 ^ 2 := by
      rw [plane_dist_sq]
      change ((0 : ℝ) - 1 / 2) ^ 2 + ((0 : ℝ) - -Real.sqrt 3 / 2) ^ 2 = 1 ^ 2
      linear_combination hs3 / 4
    nlinarith [dist_nonneg (x := equiP0) (y := equiP3)]
  have hd12 : dist equiP1 equiP2 = 1 := by
    have hsq : dist equiP1 equiP2 ^ 2 = 1 ^ 2 := by
      rw [plane_dist_sq]
      change ((1 : ℝ) - 1 / 2) ^ 2 + ((0 : ℝ) - Real.sqrt 3 / 2) ^ 2 = 1 ^ 2
      linear_combination hs3 / 4
    nlinarith [dist_nonneg (x := equiP1) (y := equiP2)]
  have hd13 : dist equiP1 equiP3 = 1 := by
    have hsq : dist equiP1 equiP3 ^ 2 = 1 ^ 2 := by
      rw [plane_dist_sq]
      change ((1 : ℝ) - 1 / 2) ^ 2 + ((0 : ℝ) - -Real.sqrt 3 / 2) ^ 2 = 1 ^ 2
      linear_combination hs3 / 4
    nlinarith [dist_nonneg (x := equiP1) (y := equiP3)]
  have hd23 : dist equiP2 equiP3 = Real.sqrt 3 := by
    have hsq : dist equiP2 equiP3 ^ 2 = Real.sqrt 3 ^ 2 := by
      rw [plane_dist_sq]
      change ((1 / 2 : ℝ) - 1 / 2) ^ 2 + (Real.sqrt 3 / 2 - -Real.sqrt 3 / 2) ^ 2 =
        Real.sqrt 3 ^ 2
      ring
    nlinarith [dist_nonneg (x := equiP2) (y := equiP3)]
  exact ⟨hd01, hd02, hd03, hd12, hd13, hd23⟩

theorem card_doubleEqui : doubleEqui.card = 4 := by
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := equi_pairwise_ne
  unfold doubleEqui
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_pair h23]
  · simp [h12, h13]
  · simp [h01, h02, h03]

theorem doubleEqui_isOptimal : IsOptimal doubleEqui 4 := by
  classical
  obtain ⟨hd01, hd02, hd03, hd12, hd13, hd23⟩ := equi_dists
  have hsub : Erdos91.DistanceErasure.distanceSet doubleEqui ⊆ {1, Real.sqrt 3} := by
    intro r hr
    obtain ⟨a, ha, b, hb, hab, rfl⟩ := (mem_distanceSet doubleEqui r).mp hr
    simp only [doubleEqui, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
    · exact False.elim (hab rfl)
    · simp [hd01]
    · simp [hd02]
    · simp [hd03]
    · simp [dist_comm, hd01]
    · exact False.elim (hab rfl)
    · simp [hd12]
    · simp [hd13]
    · simp [dist_comm, hd02]
    · simp [dist_comm, hd12]
    · exact False.elim (hab rfl)
    · simp [hd23]
    · simp [dist_comm, hd03]
    · simp [dist_comm, hd13]
    · simp [dist_comm, hd23]
    · exact False.elim (hab rfl)
  have hup : distinctDistances doubleEqui ≤ 2 :=
    (Finset.card_le_card hsub).trans Finset.card_le_two
  have hlo := minimal_le doubleEqui 4 card_doubleEqui
  have hm4 := minimalDistinctDistances_four
  exact ⟨card_doubleEqui, by omega⟩

theorem doubleEqui_energies :
    energy doubleEqui equiP0 = 3 ∧ energy doubleEqui equiP2 = 5 := by
  classical
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := equi_pairwise_ne
  obtain ⟨hd01, hd02, hd03, hd12, hd13, hd23⟩ := equi_dists
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hmem0 : equiP0 ∉ ({equiP1, equiP2, equiP3} : Finset Plane) := by
    simp [h01, h02, h03]
  have hmem1 : equiP1 ∉ ({equiP2, equiP3} : Finset Plane) := by
    simp [h12, h13]
  have hmem2 : equiP2 ∉ ({equiP3} : Finset Plane) := by
    simp [h23]
  constructor
  · unfold energy doubleEqui
    rw [Finset.sum_insert hmem0, Finset.sum_insert hmem1, Finset.sum_insert hmem2,
      Finset.sum_singleton]
    rw [dist_self, hd01, hd02, hd03]
    norm_num
  · unfold energy doubleEqui
    rw [Finset.sum_insert hmem0, Finset.sum_insert hmem1, Finset.sum_insert hmem2,
      Finset.sum_singleton]
    rw [dist_comm equiP2 equiP0, dist_comm equiP2 equiP1, hd02, hd12, dist_self, hd23, hs3]
    norm_num

theorem not_similar_unitSquare_doubleEqui :
    ¬ DilationEquivSimilar (gridSet 2) doubleEqui := by
  intro hsim
  obtain ⟨f, hf⟩ := (similar_iff_image (gridSet 2) doubleEqui).mp hsim
  have hp0 : equiP0 ∈ doubleEqui := by simp [doubleEqui]
  have hp2 : equiP2 ∈ doubleEqui := by simp [doubleEqui]
  have heq := energy_eq_of_similar_const unitSquare_energy_eq_four hf hp0 hp2
  obtain ⟨he0, he2⟩ := doubleEqui_energies
  linarith

/-- Formal proof of `erdos_91.variants.four`: for n = 4, the unit square and the
double-equilateral configuration are both globally optimal 4-point planar sets
and are not similar under any DilationEquiv. -/
theorem not_uniqueMinimizer_four : ¬ UniqueMinimizer 4 := by
  intro huniq
  exact not_similar_unitSquare_doubleEqui
    (huniq (gridSet 2) doubleEqui unitSquare_isOptimal doubleEqui_isOptimal)
end Erdos91.FourNonuniqueAndDoubleEquilateral

namespace Erdos91.ThreeUniqueMinimizer
open scoped NNReal
open Finset Erdos91.DistanceErasure Minimizer91 PlateauDefinitions91
  Erdos91.SmallCasesAndSquareBarrier Erdos91.FourNonuniqueAndDoubleEquilateral

noncomputable def equiTriangle : Finset Plane := {equiP0, equiP1, equiP2}

theorem similar_refl (A : Finset Plane) : DilationEquivSimilar A A := by
  classical
  rw [similar_iff_image]
  exact ⟨DilationEquiv.refl Plane, Finset.image_id⟩

theorem similar_symm {A B : Finset Plane} (h : DilationEquivSimilar A B) :
    DilationEquivSimilar B A := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f.symm, ?_⟩
  rw [← hf, ← Set.image_comp]
  ext x
  simp

theorem similar_trans {A B C : Finset Plane}
    (hab : DilationEquivSimilar A B) (hbc : DilationEquivSimilar B C) :
    DilationEquivSimilar A C := by
  obtain ⟨f, hf⟩ := hab
  obtain ⟨g, hg⟩ := hbc
  refine ⟨f.trans g, ?_⟩
  change (g ∘ f) '' (A : Set Plane) = (C : Set Plane)
  rw [Set.image_comp, hf, hg]

noncomputable def planarSimilarity (a : Plane) (r u0 u1 s : ℝ) (x : Plane) : Plane :=
  !₂[a 0 + r * (x 0 * u0 - s * x 1 * u1), a 1 + r * (x 0 * u1 + s * x 1 * u0)]

noncomputable def planarSimilarityInv (a : Plane) (rinv u0 u1 s : ℝ) (y : Plane) : Plane :=
  !₂[rinv * ((y 0 - a 0) * u0 + (y 1 - a 1) * u1),
     s * rinv * (-(y 0 - a 0) * u1 + (y 1 - a 1) * u0)]

theorem planarSimilarity_left_inv (a : Plane) (r rinv u0 u1 s : ℝ)
    (hrinv : r * rinv = 1) (hu_sq : u0 ^ 2 + u1 ^ 2 = 1) (hs_sq : s ^ 2 = 1) :
    Function.LeftInverse (planarSimilarityInv a rinv u0 u1 s)
      (planarSimilarity a r u0 u1 s) := by
  intro x
  apply plane_ext
  · dsimp [planarSimilarityInv, planarSimilarity]
    linear_combination x 0 * (u0 ^ 2 + u1 ^ 2) * hrinv + x 0 * hu_sq
  · dsimp [planarSimilarityInv, planarSimilarity]
    linear_combination (s ^ 2) * x 1 * (u0 ^ 2 + u1 ^ 2) * hrinv +
      (s ^ 2) * x 1 * hu_sq + x 1 * hs_sq

theorem planarSimilarity_right_inv (a : Plane) (r rinv u0 u1 s : ℝ)
    (hrinv : r * rinv = 1) (hu_sq : u0 ^ 2 + u1 ^ 2 = 1) (hs_sq : s ^ 2 = 1) :
    Function.RightInverse (planarSimilarityInv a rinv u0 u1 s)
      (planarSimilarity a r u0 u1 s) := by
  intro y
  apply plane_ext
  · dsimp [planarSimilarityInv, planarSimilarity]
    linear_combination ((y 0 - a 0) * u0 ^ 2 + (y 1 - a 1) * u0 * u1 +
        s ^ 2 * (y 0 - a 0) * u1 ^ 2 - s ^ 2 * (y 1 - a 1) * u0 * u1) * hrinv +
      ((y 0 - a 0) * u1 ^ 2 - (y 1 - a 1) * u0 * u1) * hs_sq + (y 0 - a 0) * hu_sq
  · dsimp [planarSimilarityInv, planarSimilarity]
    linear_combination ((y 0 - a 0) * u0 * u1 + (y 1 - a 1) * u1 ^ 2 -
        s ^ 2 * (y 0 - a 0) * u0 * u1 + s ^ 2 * (y 1 - a 1) * u0 ^ 2) * hrinv +
      (-(y 0 - a 0) * u0 * u1 + (y 1 - a 1) * u0 ^ 2) * hs_sq + (y 1 - a 1) * hu_sq

theorem planarSimilarity_dist (a : Plane) (r u0 u1 s : ℝ) (hr : 0 < r)
    (hu_sq : u0 ^ 2 + u1 ^ 2 = 1) (hs_sq : s ^ 2 = 1) (x y : Plane) :
    dist (planarSimilarity a r u0 u1 s x) (planarSimilarity a r u0 u1 s y) =
      r * dist x y := by
  have hsq : dist (planarSimilarity a r u0 u1 s x) (planarSimilarity a r u0 u1 s y) ^ 2 =
      (r * dist x y) ^ 2 := by
    rw [plane_dist_sq, mul_pow, plane_dist_sq]
    dsimp [planarSimilarity]
    linear_combination (r ^ 2) * ((x 0 - y 0) ^ 2 + s ^ 2 * (x 1 - y 1) ^ 2) * hu_sq +
      (r ^ 2) * (x 1 - y 1) ^ 2 * hs_sq
  have hnonneg : 0 ≤ r * dist x y := mul_nonneg hr.le dist_nonneg
  nlinarith [dist_nonneg (x := planarSimilarity a r u0 u1 s x)
    (y := planarSimilarity a r u0 u1 s y)]

noncomputable def planarSimilarityDilationEquiv (a : Plane) (r rinv u0 u1 s : ℝ)
    (hr : 0 < r) (hrinv : r * rinv = 1) (hu_sq : u0 ^ 2 + u1 ^ 2 = 1)
    (hs_sq : s ^ 2 = 1) : Plane ≃ᵈ Plane :=
  let e : Plane ≃ Plane :=
    ⟨planarSimilarity a r u0 u1 s, planarSimilarityInv a rinv u0 u1 s,
     planarSimilarity_left_inv a r rinv u0 u1 s hrinv hu_sq hs_sq,
     planarSimilarity_right_inv a r rinv u0 u1 s hrinv hu_sq hs_sq⟩
  let d : Plane →ᵈ Plane := Dilation.mkOfDistEq (planarSimilarity a r u0 u1 s)
    ⟨⟨r, hr.le⟩, ne_of_gt (by exact_mod_cast hr),
     fun x y => planarSimilarity_dist a r u0 u1 s hr hu_sq hs_sq x y⟩
  { toEquiv := e, edist_eq' := d.edist_eq' }

theorem planarSimilarityDilationEquiv_apply (a : Plane) (r rinv u0 u1 s : ℝ)
    (hr : 0 < r) (hrinv : r * rinv = 1) (hu_sq : u0 ^ 2 + u1 ^ 2 = 1)
    (hs_sq : s ^ 2 = 1) (x : Plane) :
    planarSimilarityDilationEquiv a r rinv u0 u1 s hr hrinv hu_sq hs_sq x =
      planarSimilarity a r u0 u1 s x := rfl

/-- Given any three points `a, b, c` in the plane at mutual distance `r > 0`,
there is an explicit `DilationEquiv` mapping `equiP0, equiP1, equiP2` to `a, b, c`. -/
theorem exists_dilationEquiv_of_equilateral (a b c : Plane) (r : ℝ) (hr : 0 < r)
    (hab : dist a b = r) (hac : dist a c = r) (hbc : dist b c = r) :
    ∃ f : Plane ≃ᵈ Plane, f equiP0 = a ∧ f equiP1 = b ∧ f equiP2 = c := by
  classical
  have hr_ne : r ≠ 0 := ne_of_gt hr
  have hrinv : r * r⁻¹ = 1 := mul_inv_cancel₀ hr_ne
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hab_sq : (b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2 = r ^ 2 := by
    rw [← plane_dist_sq b a, dist_comm, hab]
  obtain ⟨u0, u1, hu0_def, hu1_def⟩ :
      ∃ u0 u1 : ℝ, u0 = r⁻¹ * (b 0 - a 0) ∧ u1 = r⁻¹ * (b 1 - a 1) :=
    ⟨_, _, rfl, rfl⟩
  obtain ⟨w0, w1, hw0_def, hw1_def⟩ :
      ∃ w0 w1 : ℝ, w0 = c 0 - a 0 ∧ w1 = c 1 - a 1 :=
    ⟨_, _, rfl, rfl⟩
  have hw_sq : w0 ^ 2 + w1 ^ 2 = r ^ 2 := by
    rw [hw0_def, hw1_def, ← plane_dist_sq c a, dist_comm, hac]
  have hbu0 : r * u0 = b 0 - a 0 := by
    rw [hu0_def]
    linear_combination (b 0 - a 0) * hrinv
  have hbu1 : r * u1 = b 1 - a 1 := by
    rw [hu1_def]
    linear_combination (b 1 - a 1) * hrinv
  have hbw_sq : (w0 - r * u0) ^ 2 + (w1 - r * u1) ^ 2 = r ^ 2 := by
    have h0 : w0 - r * u0 = c 0 - b 0 := by linarith [hw0_def, hbu0]
    have h1 : w1 - r * u1 = c 1 - b 1 := by linarith [hw1_def, hbu1]
    rw [h0, h1, ← plane_dist_sq c b, dist_comm, hbc]
  have hu_sq : u0 ^ 2 + u1 ^ 2 = 1 := by
    rw [hu0_def, hu1_def]
    linear_combination (r⁻¹ ^ 2) * hab_sq + (r * r⁻¹ + 1) * hrinv
  have hdot : 2 * (w0 * u0 + w1 * u1) = r := by
    have hmul : r * (2 * (w0 * u0 + w1 * u1) - r) = 0 := by
      linear_combination hw_sq + (r ^ 2) * hu_sq - hbw_sq
    rcases mul_eq_zero.mp hmul with h0 | h0
    · exact False.elim (hr_ne h0)
    · linarith
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = -w0 * u1 + w1 * u0 := ⟨_, rfl⟩
  have ht_sq : (t - r * Real.sqrt 3 / 2) * (t + r * Real.sqrt 3 / 2) = 0 := by
    rw [ht_def]
    linear_combination (u0 ^ 2 + u1 ^ 2) * hw_sq + (r ^ 2) * hu_sq -
      (1 / 4) * (2 * (w0 * u0 + w1 * u1) + r) * hdot - (r ^ 2 / 4) * hs3
  have hs_ex : ∃ s : ℝ, s ^ 2 = 1 ∧ s * (r * Real.sqrt 3 / 2) = t := by
    rcases mul_eq_zero.mp ht_sq with h1 | h2
    · exact ⟨1, by norm_num, by linarith⟩
    · exact ⟨-1, by norm_num, by linarith⟩
  obtain ⟨s, hs_sq, hst⟩ := hs_ex
  have hw0 : w0 = (r / 2) * u0 - t * u1 := by
    rw [ht_def]
    linear_combination -w0 * hu_sq + (1 / 2) * u0 * hdot
  have hw1 : w1 = (r / 2) * u1 + t * u0 := by
    rw [ht_def]
    linear_combination -w1 * hu_sq + (1 / 2) * u1 * hdot
  refine ⟨planarSimilarityDilationEquiv a r r⁻¹ u0 u1 s hr hrinv hu_sq hs_sq, ?_, ?_, ?_⟩
  · rw [planarSimilarityDilationEquiv_apply]
    apply plane_ext
    · dsimp [planarSimilarity, equiP0]; ring
    · dsimp [planarSimilarity, equiP0]; ring
  · rw [planarSimilarityDilationEquiv_apply]
    apply plane_ext
    · dsimp [planarSimilarity, equiP1]; linarith [hbu0]
    · dsimp [planarSimilarity, equiP1]; linarith [hbu1]
  · rw [planarSimilarityDilationEquiv_apply]
    apply plane_ext
    · dsimp [planarSimilarity, equiP2]
      linear_combination hw0_def - hw0 - u1 * hst
    · dsimp [planarSimilarity, equiP2]
      linear_combination hw1_def - hw1 + u0 * hst

/-- Formal proof of `erdos_91.test.equiTriangle_unique_optimal`: every globally
optimal 3-point planar configuration is similar to `equiTriangle`. -/
theorem equiTriangle_unique_optimal (A : Finset Plane) (hA : IsOptimal A 3) :
    DilationEquivSimilar A equiTriangle := by
  classical
  have hcard : A.card = 3 := hA.1
  have hdist1 : distinctDistances A = 1 := hA.2.trans minimalDistinctDistances_three
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
  have ha : a ∈ ({a, b, c} : Finset Plane) := by simp
  have hb : b ∈ ({a, b, c} : Finset Plane) := by simp
  have hc : c ∈ ({a, b, c} : Finset Plane) := by simp
  let r := dist a b
  have hr : 0 < r := dist_pos.mpr hab
  have hab_mem : dist a b ∈ Erdos91.DistanceErasure.distanceSet {a, b, c} :=
    (mem_distanceSet {a, b, c} (dist a b)).mpr ⟨a, ha, b, hb, hab, rfl⟩
  have hac_mem : dist a c ∈ Erdos91.DistanceErasure.distanceSet {a, b, c} :=
    (mem_distanceSet {a, b, c} (dist a c)).mpr ⟨a, ha, c, hc, hac, rfl⟩
  have hbc_mem : dist b c ∈ Erdos91.DistanceErasure.distanceSet {a, b, c} :=
    (mem_distanceSet {a, b, c} (dist b c)).mpr ⟨b, hb, c, hc, hbc, rfl⟩
  have hle1 : (Erdos91.DistanceErasure.distanceSet {a, b, c}).card ≤ 1 := by
    change distinctDistances {a, b, c} ≤ 1
    omega
  have hac_eq : dist a c = r :=
    Finset.card_le_one.mp hle1 (dist a c) hac_mem (dist a b) hab_mem
  have hbc_eq : dist b c = r :=
    Finset.card_le_one.mp hle1 (dist b c) hbc_mem (dist a b) hab_mem
  obtain ⟨f, hfa, hfb, hfc⟩ :=
    exists_dilationEquiv_of_equilateral a b c r hr rfl hac_eq hbc_eq
  apply similar_symm
  rw [similar_iff_image]
  refine ⟨f, ?_⟩
  unfold equiTriangle
  rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton,
    hfa, hfb, hfc]

/-- Formal proof of `erdos_91.variants.three`: for n = 3, the globally optimal
planar distinct-distance configuration is unique up to similarity. -/
theorem uniqueMinimizer_three : UniqueMinimizer 3 := by
  intro A B hA hB
  exact similar_trans (equiTriangle_unique_optimal A hA)
    (similar_symm (equiTriangle_unique_optimal B hB))

end Erdos91.ThreeUniqueMinimizer

/-! ## General m-Point Deletion Multiplicity, Ceiling Bounds, and Fixed-K Multiplicity Counting -/

namespace Erdos91.GeneralMultiplicityAndDensityOne
open Finset Erdos91.DistanceErasure Minimizer91 PlateauDefinitions91
  Erdos91.GridUpperBound

/-- Predicate asserting that cardinality `n` admits at least `K` pairwise
nonsimilar globally optimal planar distinct-distance minimizers. -/
def HasAtLeastKNonsimilarMinimizers (K n : ℕ) : Prop :=
  ∃ F : Finset (Finset Plane),
    F.card = K ∧
    (∀ A ∈ F, IsOptimal A n) ∧
    (∀ A ∈ F, ∀ C ∈ F, A ≠ C → ¬ DilationEquivSimilar A C)

end Erdos91.GeneralMultiplicityAndDensityOne

namespace Erdos91.SixAndSevenWheelConfig
open Finset Erdos91.DistanceErasure Minimizer91 PlateauDefinitions91
  Erdos91.SmallCasesAndSquareBarrier Erdos91.FourNonuniqueAndDoubleEquilateral
  Erdos91.ThreeUniqueMinimizer
open EnergyLevels91 (energy)

noncomputable def hexM1 : Plane := !₂[-1, 0]
noncomputable def hexQ2 : Plane := !₂[-1 / 2, Real.sqrt 3 / 2]
noncomputable def hexQ3 : Plane := !₂[-1 / 2, -Real.sqrt 3 / 2]

noncomputable def centeredWheelSeven : Finset Plane :=
  {equiP0, equiP1, hexM1, equiP2, hexQ2, equiP3, hexQ3}

noncomputable def regularHexagon : Finset Plane :=
  centeredWheelSeven.erase equiP0

noncomputable def spokedPentagon : Finset Plane :=
  centeredWheelSeven.erase equiP1

theorem sqrt3_sub_lemmas :
    ((0 : ℝ) - Real.sqrt 3 / 2) ^ 2 = 3 / 4 ∧
      ((0 : ℝ) - -Real.sqrt 3 / 2) ^ 2 = 3 / 4 ∧
      (Real.sqrt 3 / 2 - 0) ^ 2 = 3 / 4 ∧
      (-Real.sqrt 3 / 2 - 0) ^ 2 = 3 / 4 ∧
      (Real.sqrt 3 / 2 - -Real.sqrt 3 / 2) ^ 2 = 3 ∧
      (-Real.sqrt 3 / 2 - Real.sqrt 3 / 2) ^ 2 = 3 := by
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨by linear_combination hs3 / 4, by linear_combination hs3 / 4,
    by linear_combination hs3 / 4, by linear_combination hs3 / 4,
    by linear_combination hs3, by linear_combination hs3⟩

theorem wheel_pairwise_ne :
    equiP0 ≠ equiP1 ∧ equiP0 ≠ hexM1 ∧ equiP0 ≠ equiP2 ∧ equiP0 ≠ hexQ2 ∧
      equiP0 ≠ equiP3 ∧ equiP0 ≠ hexQ3 ∧
      equiP1 ≠ hexM1 ∧ equiP1 ≠ equiP2 ∧ equiP1 ≠ hexQ2 ∧ equiP1 ≠ equiP3 ∧
      equiP1 ≠ hexQ3 ∧
      hexM1 ≠ equiP2 ∧ hexM1 ≠ hexQ2 ∧ hexM1 ≠ equiP3 ∧ hexM1 ≠ hexQ3 ∧
      equiP2 ≠ hexQ2 ∧ equiP2 ≠ equiP3 ∧ equiP2 ≠ hexQ3 ∧
      hexQ2 ≠ equiP3 ∧ hexQ2 ≠ hexQ3 ∧
      equiP3 ≠ hexQ3 := by
  have hs_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; have h0 : (0 : ℝ) = 1 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (0 : ℝ) = -1 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (0 : ℝ) = 1 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (0 : ℝ) = -1 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (0 : ℝ) = 1 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (0 : ℝ) = -1 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (1 : ℝ) = -1 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (1 : ℝ) = 1 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (1 : ℝ) = -1 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (1 : ℝ) = 1 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (1 : ℝ) = -1 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (-1 : ℝ) = 1 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (-1 : ℝ) = -1 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (-1 : ℝ) = 1 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (-1 : ℝ) = -1 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (1 / 2 : ℝ) = -1 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h1 : Real.sqrt 3 / 2 = -Real.sqrt 3 / 2 := congrArg (fun x : Plane => x 1) h; linarith
  · intro h; have h0 : (1 / 2 : ℝ) = -1 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (-1 / 2 : ℝ) = 1 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h1 : Real.sqrt 3 / 2 = -Real.sqrt 3 / 2 := congrArg (fun x : Plane => x 1) h; linarith
  · intro h; have h0 : (1 / 2 : ℝ) = -1 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0

theorem card_centeredWheelSeven : centeredWheelSeven.card = 7 := by
  obtain ⟨h01, h0m1, h02, h0q2, h03, h0q3,
    h1m1, h12, h1q2, h13, h1q3,
    hm12, hm1q2, hm13, hm1q3,
    h2q2, h23, h2q3,
    hq23, hq2q3,
    h3q3⟩ := wheel_pairwise_ne
  unfold centeredWheelSeven
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem, Finset.card_pair h3q3]
  · simp [hq23, hq2q3]
  · simp [h2q2, h23, h2q3]
  · simp [hm12, hm1q2, hm13, hm1q3]
  · simp [h1m1, h12, h1q2, h13, h1q3]
  · simp [h01, h0m1, h02, h0q2, h03, h0q3]

theorem wheel_dist_sq_cases (x y : Plane)
    (hx : x ∈ centeredWheelSeven) (hy : y ∈ centeredWheelSeven) :
    dist x y ^ 2 = 0 ∨ dist x y ^ 2 = 1 ∨ dist x y ^ 2 = 3 ∨ dist x y ^ 2 = 4 := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := sqrt3_sub_lemmas
  simp only [centeredWheelSeven, Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    { rw [plane_dist_sq]
      dsimp [equiP0, equiP1, hexM1, equiP2, hexQ2, equiP3, hexQ3]
      try rw [s1]
      try rw [s2]
      try rw [s3]
      try rw [s4]
      try rw [s5]
      try rw [s6]
      norm_num }

theorem distanceSet_centeredWheelSeven_subset :
    Erdos91.DistanceErasure.distanceSet centeredWheelSeven ⊆ {1, Real.sqrt 3, 2} := by
  classical
  intro r hr
  obtain ⟨x, hx, y, hy, hxy, rfl⟩ := (mem_distanceSet centeredWheelSeven r).mp hr
  have hpos : 0 < dist x y := dist_pos.mpr hxy
  have hcases := wheel_dist_sq_cases x y hx hy
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases hcases with h0 | h1 | h3 | h4
  · exfalso; nlinarith
  · left; nlinarith
  · right; left
    have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hpos3 : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    nlinarith
  · right; right; nlinarith

theorem distinctDistances_centeredWheelSeven_le_three :
    distinctDistances centeredWheelSeven ≤ 3 := by
  classical
  have h := Finset.card_le_card distanceSet_centeredWheelSeven_subset
  have h3 : ({1, Real.sqrt 3, 2} : Finset ℝ).card ≤ 3 :=
    (Finset.card_insert_le _ _).trans (Nat.succ_le_succ Finset.card_le_two)
  exact h.trans h3

theorem minimalDistinctDistances_seven_le_three :
    minimalDistinctDistances 7 ≤ 3 :=
  (minimal_le centeredWheelSeven 7 card_centeredWheelSeven).trans
    distinctDistances_centeredWheelSeven_le_three

theorem minimalDistinctDistances_six_le_three :
    minimalDistinctDistances 6 ≤ 3 :=
  (MinimumMonotone91.minimum_monotone (by omega : 6 ≤ 7)).trans
    minimalDistinctDistances_seven_le_three

theorem centeredWheelSeven_diameter_pair (x y : Plane)
    (hx : x ∈ centeredWheelSeven) (hy : y ∈ centeredWheelSeven) :
    dist x y ≤ dist equiP2 hexQ3 := by
  obtain ⟨_, _, _, _, s5, _⟩ := sqrt3_sub_lemmas
  have hd_diam : dist equiP2 hexQ3 = 2 := by
    have hsq : dist equiP2 hexQ3 ^ 2 = 2 ^ 2 := by
      rw [plane_dist_sq]
      dsimp [equiP2, hexQ3]
      rw [s5]
      norm_num
    nlinarith [dist_nonneg (x := equiP2) (y := hexQ3)]
  rw [hd_diam]
  have hcases := wheel_dist_sq_cases x y hx hy
  have hsq_le : dist x y ^ 2 ≤ 4 := by
    rcases hcases with h | h | h | h <;> linarith
  nlinarith [dist_nonneg (x := x) (y := y)]

theorem centeredWheelSeven_energies :
    energy centeredWheelSeven equiP0 = 6 ∧
      energy centeredWheelSeven equiP1 = 13 := by
  classical
  obtain ⟨h01, h0m1, h02, h0q2, h03, h0q3,
    h1m1, h12, h1q2, h13, h1q3,
    hm12, hm1q2, hm13, hm1q3,
    h2q2, h23, h2q3,
    hq23, hq2q3,
    h3q3⟩ := wheel_pairwise_ne
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := sqrt3_sub_lemmas
  have hm0 : equiP0 ∉ ({equiP1, hexM1, equiP2, hexQ2, equiP3, hexQ3} : Finset Plane) := by
    simp [h01, h0m1, h02, h0q2, h03, h0q3]
  have hm1 : equiP1 ∉ ({hexM1, equiP2, hexQ2, equiP3, hexQ3} : Finset Plane) := by
    simp [h1m1, h12, h1q2, h13, h1q3]
  have hmm1 : hexM1 ∉ ({equiP2, hexQ2, equiP3, hexQ3} : Finset Plane) := by
    simp [hm12, hm1q2, hm13, hm1q3]
  have hm2 : equiP2 ∉ ({hexQ2, equiP3, hexQ3} : Finset Plane) := by
    simp [h2q2, h23, h2q3]
  have hmq2 : hexQ2 ∉ ({equiP3, hexQ3} : Finset Plane) := by
    simp [hq23, hq2q3]
  have hm3 : equiP3 ∉ ({hexQ3} : Finset Plane) := by
    simp [h3q3]
  constructor
  · unfold energy centeredWheelSeven
    rw [Finset.sum_insert hm0, Finset.sum_insert hm1, Finset.sum_insert hmm1,
      Finset.sum_insert hm2, Finset.sum_insert hmq2, Finset.sum_insert hm3,
      Finset.sum_singleton]
    simp only [plane_dist_sq]
    dsimp [equiP0, equiP1, hexM1, equiP2, hexQ2, equiP3, hexQ3]
    rw [s1, s2]
    norm_num
  · unfold energy centeredWheelSeven
    rw [Finset.sum_insert hm0, Finset.sum_insert hm1, Finset.sum_insert hmm1,
      Finset.sum_insert hm2, Finset.sum_insert hmq2, Finset.sum_insert hm3,
      Finset.sum_singleton]
    simp only [plane_dist_sq]
    dsimp [equiP0, equiP1, hexM1, equiP2, hexQ2, equiP3, hexQ3]
    rw [s1, s2]
    norm_num

/-- The regular hexagon (`centeredWheelSeven.erase equiP0`) and the spoked
5-wheel (`centeredWheelSeven.erase equiP1`) are both 6-point sets with at most
3 distinct distances and are nonsimilar under all full-plane similarities. -/
theorem not_similar_regularHexagon_spokedPentagon :
    ¬ DilationEquivSimilar regularHexagon spokedPentagon := by
  rw [similar_iff_image]
  obtain ⟨h01, _, h02, _, _, h0q3,
    _, h12, _, _, h1q3,
    _, _, _, _,
    _, _, h2q3, _⟩ := wheel_pairwise_ne
  obtain ⟨he0, he1⟩ := centeredWheelSeven_energies
  apply DeletionEnergy91.nonsimilar_deletions centeredWheelSeven
    equiP2 hexQ3 equiP0 equiP1 h2q3
    (by simp [centeredWheelSeven]) (by simp [centeredWheelSeven])
    (by simp [centeredWheelSeven]) (by simp [centeredWheelSeven])
    h02 h0q3 h12 h1q3 (fun x hx y hy => centeredWheelSeven_diameter_pair x y hx hy)
  linarith

/-- Reduction of `erdos_91.variants.six` (`¬ UniqueMinimizer 6`) and the plateau
`d(6) = d(7) = 3` to the 2-distance threshold `3 ≤ minimalDistinctDistances 6`. -/
theorem not_uniqueMinimizer_six_of_three_le
    (h6 : 3 ≤ minimalDistinctDistances 6) :
    minimalDistinctDistances 6 = 3 ∧
      minimalDistinctDistances 7 = 3 ∧
      ¬ UniqueMinimizer 6 := by
  classical
  have hm6 : minimalDistinctDistances 6 = 3 :=
    le_antisymm minimalDistinctDistances_six_le_three h6
  have hm7 : minimalDistinctDistances 7 = 3 := by
    apply le_antisymm minimalDistinctDistances_seven_le_three
    rw [← hm6]
    exact MinimumMonotone91.minimum_monotone (by omega)
  have hWopt : IsOptimal centeredWheelSeven 7 := by
    refine ⟨card_centeredWheelSeven, le_antisymm ?_
      (minimal_le centeredWheelSeven 7 card_centeredWheelSeven)⟩
    rw [hm7]
    exact distinctDistances_centeredWheelSeven_le_three
  have hHexOpt : IsOptimal regularHexagon 6 := by
    apply MinimumMonotone91.plateau_subset_optimal regularHexagon centeredWheelSeven 6 7
      hWopt (Finset.erase_subset _ _) _ (hm6.trans hm7.symm)
    unfold regularHexagon
    rw [Finset.card_erase_of_mem (by simp [centeredWheelSeven]), card_centeredWheelSeven]
  have hSpokeOpt : IsOptimal spokedPentagon 6 := by
    apply MinimumMonotone91.plateau_subset_optimal spokedPentagon centeredWheelSeven 6 7
      hWopt (Finset.erase_subset _ _) _ (hm6.trans hm7.symm)
    unfold spokedPentagon
    rw [Finset.card_erase_of_mem (by simp [centeredWheelSeven]), card_centeredWheelSeven]
  refine ⟨hm6, hm7, ?_⟩
  intro huniq
  exact not_similar_regularHexagon_spokedPentagon
    (huniq regularHexagon spokedPentagon hHexOpt hSpokeOpt)

end Erdos91.SixAndSevenWheelConfig

/-! ## Planar 2-Distance Set Cap (`distinctDistances S ≤ 2 → S.card ≤ 5`) and Unconditional `d(6) = d(7) = 3` & `¬ UniqueMinimizer 6` -/

namespace Erdos91.TwoDistanceCapAndSixNonunique
open Finset Erdos91.DistanceErasure Minimizer91 PlateauDefinitions91
  Erdos91.SmallCasesAndSquareBarrier Erdos91.SixAndSevenWheelConfig

def cmPoly (ab ac ad bc bd cd : ℝ) : ℝ :=
  4 * ab * ac * ad + (ab + ac - bc) * (ab + ad - bd) * (ac + ad - cd)
    - ab * (ac + ad - cd) ^ 2 - ac * (ab + ad - bd) ^ 2 - ad * (ab + ac - bc) ^ 2

theorem cmPoly_dist_sq_eq_zero (p1 p2 p3 p4 : Plane) :
    cmPoly (dist p1 p2 ^ 2) (dist p1 p3 ^ 2) (dist p1 p4 ^ 2)
      (dist p2 p3 ^ 2) (dist p2 p4 ^ 2) (dist p3 p4 ^ 2) = 0 := by
  simp only [plane_dist_sq, cmPoly]
  ring

theorem no_three_equidistant_from_two_centers
    {p1 p2 q1 q2 q3 : Plane} (r1 r2 : ℝ)
    (hp12 : p1 ≠ p2) (hq12 : q1 ≠ q2) (hq13 : q1 ≠ q3) (hq23 : q2 ≠ q3)
    (h11 : dist q1 p1 = r1) (h21 : dist q2 p1 = r1) (h31 : dist q3 p1 = r1)
    (h12 : dist q1 p2 = r2) (h22 : dist q2 p2 = r2) (h32 : dist q3 p2 = r2) :
    False := by
  classical
  let B : Finset Plane := {q1, q2, q3}
  have hcard : B.card = 3 := by
    dsimp [B]
    rw [Finset.card_insert_of_notMem, Finset.card_pair hq23]
    simp [hq12, hq13]
  have hle2 : B.card ≤ 2 := by
    apply CircleFibers91.two_centers_card B p1 p2 r1 r2 hp12
    · intro v hv
      simp only [B, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> assumption
    · intro v hv
      simp only [B, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> assumption
  omega

theorem no_two_same_typeB {u v w x1 x2 : Plane} {r d : ℝ}
    (hr : r ≠ 0)
    (huv : dist u v = r) (hvw : dist v w = r)
    (hux1 : dist u x1 = r) (hvx1 : dist v x1 = d) (hwx1 : dist w x1 = d)
    (hux2 : dist u x2 = r) (hvx2 : dist v x2 = d) (hwx2 : dist w x2 = d)
    (hx12 : dist x1 x2 = r ∨ dist x1 x2 = d)
    (hgB : d ^ 4 - 4 * d ^ 2 * r ^ 2 + r ^ 4 = 0) : False := by
  rcases hx12 with h12r | h12d
  · have hcm := cmPoly_dist_sq_eq_zero v w x1 x2
    rw [hvw, hvx1, hvx2, hwx1, hwx2, h12r] at hcm
    unfold cmPoly at hcm
    have hr8 : r ^ 8 = 0 := by
      linear_combination -(4 * r ^ 4) * hgB / 3 + (d ^ 2 - 7 / 2 * r ^ 2) * hcm / 3
    exact hr (by simpa using hr8)
  · have hcm := cmPoly_dist_sq_eq_zero u v x1 x2
    rw [huv, hux1, hux2, hvx1, hvx2, h12d] at hcm
    unfold cmPoly at hcm
    have hr8 : r ^ 8 = 0 := by
      linear_combination -(3 * d ^ 4 - 8 * d ^ 2 * r ^ 2 - 2 * r ^ 4) * hgB / 2 -
        (3 * d ^ 2 - 11 * r ^ 2) * hcm / 2
    exact hr (by simpa using hr8)

theorem no_two_diff_typeA {v w x1 x2 : Plane} {r d : ℝ}
    (hr : r ≠ 0)
    (hvw : dist v w = r)
    (hvx1 : dist v x1 = r) (hwx1 : dist w x1 = d)
    (hvx2 : dist v x2 = d) (hwx2 : dist w x2 = r)
    (hx12 : dist x1 x2 = r ∨ dist x1 x2 = d)
    (hgA : d ^ 2 - 3 * r ^ 2 = 0) : False := by
  have hcm := cmPoly_dist_sq_eq_zero v w x1 x2
  rw [hvw, hvx1, hvx2, hwx1, hwx2] at hcm
  unfold cmPoly at hcm
  rcases hx12 with h12r | h12d
  · rw [h12r] at hcm
    have hr6 : r ^ 6 = 0 := by
      linear_combination -hcm / 18 - (2 * d ^ 4 + 2 * d ^ 2 * r ^ 2 + 6 * r ^ 4) * hgA / 18
    exact hr (by simpa using hr6)
  · rw [h12d] at hcm
    have hr6 : r ^ 6 = 0 := by
      linear_combination -hcm / 4 - (d ^ 4 + d ^ 2 * r ^ 2 + r ^ 4) * hgA / 4
    exact hr (by simpa using hr6)

theorem no_two_diff_typeB {u v w x1 x2 : Plane} {r d : ℝ}
    (hr : r ≠ 0)
    (huv : dist u v = r) (huw : dist u w = r)
    (hux1 : dist u x1 = r) (hvx1 : dist v x1 = d) (hwx1 : dist w x1 = d)
    (hux2 : dist u x2 = d) (hvx2 : dist v x2 = r) (hwx2 : dist w x2 = d)
    (hx12 : dist x1 x2 = r ∨ dist x1 x2 = d)
    (hgB : d ^ 4 - 4 * d ^ 2 * r ^ 2 + r ^ 4 = 0) : False := by
  rcases hx12 with h12r | h12d
  · have hcm := cmPoly_dist_sq_eq_zero u w x1 x2
    rw [huw, hux1, hux2, hwx1, hwx2, h12r] at hcm
    unfold cmPoly at hcm
    have hr8 : r ^ 8 = 0 := by
      linear_combination (5 * d ^ 4 - 9 * d ^ 2 * r ^ 2 - 13 * r ^ 4) * hgB / 6 +
        (5 * d ^ 2 - 19 * r ^ 2) * hcm / 6
    exact hr (by simpa using hr8)
  · have hcm := cmPoly_dist_sq_eq_zero u v x1 x2
    rw [huv, hux1, hux2, hvx1, hvx2, h12d] at hcm
    unfold cmPoly at hcm
    have hr8 : r ^ 8 = 0 := by
      linear_combination (5 * d ^ 4 - 9 * d ^ 2 * r ^ 2 - 13 * r ^ 4) * hgB / 6 +
        (5 * d ^ 2 - 19 * r ^ 2) * hcm / 6
    exact hr (by simpa using hr8)

theorem equilateral_point_profile {a b c x : Plane} {r d : ℝ}
    (hr : r ≠ 0) (hd : d ≠ 0)
    (hab : dist a b = r) (hac : dist a c = r) (hbc : dist b c = r)
    (hax : dist a x = r ∨ dist a x = d)
    (hbx : dist b x = r ∨ dist b x = d)
    (hcx : dist c x = r ∨ dist c x = d) :
    (d ^ 2 - 3 * r ^ 2 = 0 ∧
      ((dist a x = r ∧ dist b x = r ∧ dist c x = d) ∨
       (dist a x = r ∧ dist b x = d ∧ dist c x = r) ∨
       (dist a x = d ∧ dist b x = r ∧ dist c x = r))) ∨
    (d ^ 4 - 4 * d ^ 2 * r ^ 2 + r ^ 4 = 0 ∧
      ((dist a x = r ∧ dist b x = d ∧ dist c x = d) ∨
       (dist a x = d ∧ dist b x = r ∧ dist c x = d) ∨
       (dist a x = d ∧ dist b x = d ∧ dist c x = r))) ∨
    (3 * d ^ 2 - r ^ 2 = 0 ∧
      (dist a x = d ∧ dist b x = d ∧ dist c x = d)) := by
  have hcm := cmPoly_dist_sq_eq_zero a b c x
  rw [hab, hac, hbc] at hcm
  unfold cmPoly at hcm
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hd2 : d ^ 2 ≠ 0 := pow_ne_zero 2 hd
  rcases hax with haxr | haxd <;> rcases hbx with hbxr | hbxd <;> rcases hcx with hcxr | hcxd
  · rw [haxr, hbxr, hcxr] at hcm
    have hr6 : r ^ 6 = 0 := by linear_combination hcm / 2
    exact False.elim (hr (by simpa using hr6))
  · left
    rw [haxr, hbxr, hcxd] at hcm
    have hfac : d ^ 2 * (r ^ 2 * (d ^ 2 - 3 * r ^ 2)) = 0 := by linear_combination -hcm
    have hgA : d ^ 2 - 3 * r ^ 2 = 0 := by
      rcases mul_eq_zero.mp hfac with h1 | h2
      · exact False.elim (hd2 h1)
      · rcases mul_eq_zero.mp h2 with h3 | h4
        · exact False.elim (hr2 h3)
        · exact h4
    exact ⟨hgA, Or.inl ⟨haxr, hbxr, hcxd⟩⟩
  · left
    rw [haxr, hbxd, hcxr] at hcm
    have hfac : d ^ 2 * (r ^ 2 * (d ^ 2 - 3 * r ^ 2)) = 0 := by linear_combination -hcm
    have hgA : d ^ 2 - 3 * r ^ 2 = 0 := by
      rcases mul_eq_zero.mp hfac with h1 | h2
      · exact False.elim (hd2 h1)
      · rcases mul_eq_zero.mp h2 with h3 | h4
        · exact False.elim (hr2 h3)
        · exact h4
    exact ⟨hgA, Or.inr (Or.inl ⟨haxr, hbxd, hcxr⟩)⟩
  · right; left
    rw [haxr, hbxd, hcxd] at hcm
    have hfac : r ^ 2 * (d ^ 4 - 4 * d ^ 2 * r ^ 2 + r ^ 4) = 0 := by linear_combination -hcm
    have hgB : d ^ 4 - 4 * d ^ 2 * r ^ 2 + r ^ 4 = 0 :=
      (mul_eq_zero.mp hfac).resolve_left hr2
    exact ⟨hgB, Or.inl ⟨haxr, hbxd, hcxd⟩⟩
  · left
    rw [haxd, hbxr, hcxr] at hcm
    have hfac : d ^ 2 * (r ^ 2 * (d ^ 2 - 3 * r ^ 2)) = 0 := by linear_combination -hcm
    have hgA : d ^ 2 - 3 * r ^ 2 = 0 := by
      rcases mul_eq_zero.mp hfac with h1 | h2
      · exact False.elim (hd2 h1)
      · rcases mul_eq_zero.mp h2 with h3 | h4
        · exact False.elim (hr2 h3)
        · exact h4
    exact ⟨hgA, Or.inr (Or.inr ⟨haxd, hbxr, hcxr⟩)⟩
  · right; left
    rw [haxd, hbxr, hcxd] at hcm
    have hfac : r ^ 2 * (d ^ 4 - 4 * d ^ 2 * r ^ 2 + r ^ 4) = 0 := by linear_combination -hcm
    have hgB : d ^ 4 - 4 * d ^ 2 * r ^ 2 + r ^ 4 = 0 :=
      (mul_eq_zero.mp hfac).resolve_left hr2
    exact ⟨hgB, Or.inr (Or.inl ⟨haxd, hbxr, hcxd⟩)⟩
  · right; left
    rw [haxd, hbxd, hcxr] at hcm
    have hfac : r ^ 2 * (d ^ 4 - 4 * d ^ 2 * r ^ 2 + r ^ 4) = 0 := by linear_combination -hcm
    have hgB : d ^ 4 - 4 * d ^ 2 * r ^ 2 + r ^ 4 = 0 :=
      (mul_eq_zero.mp hfac).resolve_left hr2
    exact ⟨hgB, Or.inr (Or.inr ⟨haxd, hbxd, hcxr⟩)⟩
  · right; right
    rw [haxd, hbxd, hcxd] at hcm
    have hfac : (r ^ 2) ^ 2 * (3 * d ^ 2 - r ^ 2) = 0 := by linear_combination hcm
    have hgC : 3 * d ^ 2 - r ^ 2 = 0 :=
      (mul_eq_zero.mp hfac).resolve_left (pow_ne_zero 2 hr2)
    exact ⟨hgC, ⟨haxd, hbxd, hcxd⟩⟩

/-- No planar 2-distance configuration `{r, d}` (`r ≠ 0, d ≠ 0`) can contain an
equilateral triangle `{a, b, c}` of side `r` together with two additional distinct
points `x1, x2`. -/
theorem no_equilateral_plus_two_of_two_distances
    {P : Plane → Prop} {r d : ℝ} (hr : r ≠ 0) (hd : d ≠ 0)
    (hpair : ∀ x y, x ≠ y → P x → P y → dist x y = r ∨ dist x y = d)
    {a b c x1 x2 : Plane}
    (ha : P a) (hb : P b) (hc : P c) (hx1 : P x1) (hx2 : P x2)
    (hab_ne : a ≠ b) (hac_ne : a ≠ c) (hbc_ne : b ≠ c)
    (hx1a : x1 ≠ a) (hx1b : x1 ≠ b) (hx1c : x1 ≠ c)
    (hx2a : x2 ≠ a) (hx2b : x2 ≠ b) (hx2c : x2 ≠ c)
    (hx12 : x1 ≠ x2)
    (hab : dist a b = r) (hac : dist a c = r) (hbc : dist b c = r) : False := by
  have hp1 := equilateral_point_profile hr hd hab hac hbc
    (hpair a x1 hx1a.symm ha hx1)
    (hpair b x1 hx1b.symm hb hx1)
    (hpair c x1 hx1c.symm hc hx1)
  have hp2 := equilateral_point_profile hr hd hab hac hbc
    (hpair a x2 hx2a.symm ha hx2)
    (hpair b x2 hx2b.symm hb hx2)
    (hpair c x2 hx2c.symm hc hx2)
  have hd12 := hpair x1 x2 hx12 hx1 hx2
  have hd21 : dist x2 x1 = r ∨ dist x2 x1 = d := by rw [dist_comm]; exact hd12
  rcases hp1 with ⟨hgA1, hA1⟩ | ⟨hgB1, hB1⟩ | ⟨hgC1, hC1⟩ <;>
    rcases hp2 with ⟨hgA2, hA2⟩ | ⟨hgB2, hB2⟩ | ⟨hgC2, hC2⟩
  · -- Type A & Type A
    rcases hA1 with ⟨ha1, hb1, hc1⟩ | ⟨ha1, hb1, hc1⟩ | ⟨ha1, hb1, hc1⟩ <;>
      rcases hA2 with ⟨ha2, hb2, hc2⟩ | ⟨ha2, hb2, hc2⟩ | ⟨ha2, hb2, hc2⟩
    · exact no_three_equidistant_from_two_centers r r hab_ne hx1c.symm hx2c.symm hx12
        (by rw [dist_comm]; exact hac) (by rw [dist_comm]; exact ha1) (by rw [dist_comm]; exact ha2)
        (by rw [dist_comm]; exact hbc) (by rw [dist_comm]; exact hb1) (by rw [dist_comm]; exact hb2)
    · exact no_two_diff_typeA hr hbc hb1 hc1 hb2 hc2 hd12 hgA1
    · exact no_two_diff_typeA hr hac ha1 hc1 ha2 hc2 hd12 hgA1
    · exact no_two_diff_typeA hr hbc hb2 hc2 hb1 hc1 hd21 hgA1
    · exact no_three_equidistant_from_two_centers r r hac_ne hx1b.symm hx2b.symm hx12
        (by rw [dist_comm]; exact hab) (by rw [dist_comm]; exact ha1) (by rw [dist_comm]; exact ha2)
        hbc (by rw [dist_comm]; exact hc1) (by rw [dist_comm]; exact hc2)
    · exact no_two_diff_typeA hr hab ha1 hb1 ha2 hb2 hd12 hgA1
    · exact no_two_diff_typeA hr hac ha2 hc2 ha1 hc1 hd21 hgA1
    · exact no_two_diff_typeA hr hab ha2 hb2 ha1 hb1 hd21 hgA1
    · exact no_three_equidistant_from_two_centers r r hbc_ne hx1a.symm hx2a.symm hx12
        hab (by rw [dist_comm]; exact hb1) (by rw [dist_comm]; exact hb2)
        hac (by rw [dist_comm]; exact hc1) (by rw [dist_comm]; exact hc2)
  · -- Type A & Type B
    have hr4 : r ^ 4 = 0 := by linear_combination -hgB2 / 2 + (d ^ 2 - r ^ 2) * hgA1 / 2
    exact hr (by simpa using hr4)
  · -- Type A & Type C
    have hr2 : r ^ 2 = 0 := by linarith
    exact hr (by simpa using hr2)
  · -- Type B & Type A
    have hr4 : r ^ 4 = 0 := by linear_combination -hgB1 / 2 + (d ^ 2 - r ^ 2) * hgA2 / 2
    exact hr (by simpa using hr4)
  · -- Type B & Type B
    rcases hB1 with ⟨ha1, hb1, hc1⟩ | ⟨ha1, hb1, hc1⟩ | ⟨ha1, hb1, hc1⟩ <;>
      rcases hB2 with ⟨ha2, hb2, hc2⟩ | ⟨ha2, hb2, hc2⟩ | ⟨ha2, hb2, hc2⟩
    · exact no_two_same_typeB hr hab hbc ha1 hb1 hc1 ha2 hb2 hc2 hd12 hgB1
    · exact no_two_diff_typeB hr hab hac ha1 hb1 hc1 ha2 hb2 hc2 hd12 hgB1
    · exact no_two_diff_typeB hr hac hab ha1 hc1 hb1 ha2 hc2 hb2 hd12 hgB1
    · exact no_two_diff_typeB hr hab hac ha2 hb2 hc2 ha1 hb1 hc1 hd21 hgB1
    · exact no_two_same_typeB hr (by rw [dist_comm]; exact hab) hac hb1 ha1 hc1 hb2 ha2 hc2 hd12 hgB1
    · exact no_two_diff_typeB hr hbc (by rw [dist_comm]; exact hab) hb1 hc1 ha1 hb2 hc2 ha2 hd12 hgB1
    · exact no_two_diff_typeB hr hac hab ha2 hc2 hb2 ha1 hc1 hb1 hd21 hgB1
    · exact no_two_diff_typeB hr hbc (by rw [dist_comm]; exact hab) hb2 hc2 ha2 hb1 hc1 ha1 hd21 hgB1
    · exact no_two_same_typeB hr (by rw [dist_comm]; exact hac) hab hc1 ha1 hb1 hc2 ha2 hb2 hd12 hgB1
  · -- Type B & Type C
    have hd4 : d ^ 4 = 0 := by linear_combination -hgB1 / 2 - (r ^ 2 - d ^ 2) * hgC2 / 2
    exact hd (by simpa using hd4)
  · -- Type C & Type A
    have hr2 : r ^ 2 = 0 := by linarith
    exact hr (by simpa using hr2)
  · -- Type C & Type B
    have hd4 : d ^ 4 = 0 := by linear_combination -hgB2 / 2 - (r ^ 2 - d ^ 2) * hgC1 / 2
    exact hd (by simpa using hd4)
  · -- Type C & Type C
    exact no_three_equidistant_from_two_centers d d hx12 hab_ne hac_ne hbc_ne
      hC1.1 hC1.2.1 hC1.2.2 hC2.1 hC2.2.1 hC2.2.2

theorem no_star_three_plus_one
    {P : Plane → Prop} {r d : ℝ} (hr : r ≠ 0) (hd : d ≠ 0)
    (hpair : ∀ x y, x ≠ y → P x → P y → dist x y = r ∨ dist x y = d)
    {v0 u1 u2 u3 y1 : Plane}
    (hv0 : P v0) (hu1 : P u1) (hu2 : P u2) (hu3 : P u3) (hy1 : P y1)
    (h01 : v0 ≠ u1) (h02 : v0 ≠ u2) (h03 : v0 ≠ u3) (h0y : v0 ≠ y1)
    (h12 : u1 ≠ u2) (h13 : u1 ≠ u3) (h1y : u1 ≠ y1)
    (h23 : u2 ≠ u3) (h2y : u2 ≠ y1) (h3y : u3 ≠ y1)
    (hd01 : dist v0 u1 = r) (hd02 : dist v0 u2 = r) (hd03 : dist v0 u3 = r) : False := by
  rcases hpair u1 u2 h12 hu1 hu2 with hd12 | hd12
  · exact no_equilateral_plus_two_of_two_distances hr hd hpair
      hv0 hu1 hu2 hu3 hy1 h01 h02 h12 h03.symm h13.symm h23.symm
      h0y.symm h1y.symm h2y.symm h3y hd01 hd02 hd12
  · rcases hpair u1 u3 h13 hu1 hu3 with hd13 | hd13
    · exact no_equilateral_plus_two_of_two_distances hr hd hpair
        hv0 hu1 hu3 hu2 hy1 h01 h03 h13 h02.symm h12.symm h23
        h0y.symm h1y.symm h3y.symm h2y hd01 hd03 hd13
    · rcases hpair u2 u3 h23 hu2 hu3 with hd23 | hd23
      · exact no_equilateral_plus_two_of_two_distances hr hd hpair
          hv0 hu2 hu3 hu1 hy1 h02 h03 h23 h01.symm h12 h13
          h0y.symm h2y.symm h3y.symm h1y hd02 hd03 hd23
      · have hpair_swap : ∀ x y, x ≠ y → P x → P y → dist x y = d ∨ dist x y = r :=
          fun x y hne hx hy => (hpair x y hne hx hy).symm
        exact no_equilateral_plus_two_of_two_distances hd hr hpair_swap
          hu1 hu2 hu3 hv0 hy1 h12 h13 h23 h01 h02 h03
          h1y.symm h2y.symm h3y.symm h0y hd12 hd13 hd23

/-- Ramsey `R(3, 3) = 6` + Cayley-Menger exclusion: no 6 distinct points in the
plane can have all pairwise distances in `{r, d}` (`r ≠ 0, d ≠ 0`). -/
theorem no_six_points_two_distances {P : Plane → Prop} {r d : ℝ}
    (hr : r ≠ 0) (hd : d ≠ 0)
    (hpair : ∀ x y, x ≠ y → P x → P y → dist x y = r ∨ dist x y = d)
    (p : Fin 6 → Plane) (hp_inj : Function.Injective p)
    (hp_mem : ∀ i, P (p i)) : False := by
  have hne {i j : Fin 6} (hij : i ≠ j) : p i ≠ p j := hp_inj.ne hij
  have hv0 := hp_mem 0
  have hv1 := hp_mem 1
  have hv2 := hp_mem 2
  have hv3 := hp_mem 3
  have hv4 := hp_mem 4
  have hv5 := hp_mem 5
  have hpair_swap : ∀ x y, x ≠ y → P x → P y → dist x y = d ∨ dist x y = r :=
    fun x y hxy hx hy => (hpair x y hxy hx hy).symm
  rcases hpair (p 0) (p 1) (hne (by rintro ⟨⟩)) hv0 hv1 with h01 | h01 <;>
    rcases hpair (p 0) (p 2) (hne (by rintro ⟨⟩)) hv0 hv2 with h02 | h02 <;>
    rcases hpair (p 0) (p 3) (hne (by rintro ⟨⟩)) hv0 hv3 with h03 | h03 <;>
    rcases hpair (p 0) (p 4) (hne (by rintro ⟨⟩)) hv0 hv4 with h04 | h04 <;>
    rcases hpair (p 0) (p 5) (hne (by rintro ⟨⟩)) hv0 hv5 with h05 | h05
  · exact no_star_three_plus_one hr hd hpair hv0 hv1 hv2 hv3 hv4 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h01 h02 h03
  · exact no_star_three_plus_one hr hd hpair hv0 hv1 hv2 hv3 hv4 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h01 h02 h03
  · exact no_star_three_plus_one hr hd hpair hv0 hv1 hv2 hv3 hv4 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h01 h02 h03
  · exact no_star_three_plus_one hr hd hpair hv0 hv1 hv2 hv3 hv4 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h01 h02 h03
  · exact no_star_three_plus_one hr hd hpair hv0 hv1 hv2 hv4 hv3 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h01 h02 h04
  · exact no_star_three_plus_one hr hd hpair hv0 hv1 hv2 hv4 hv3 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h01 h02 h04
  · exact no_star_three_plus_one hr hd hpair hv0 hv1 hv2 hv5 hv3 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h01 h02 h05
  · exact no_star_three_plus_one hd hr hpair_swap hv0 hv3 hv4 hv5 hv1 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h03 h04 h05
  · exact no_star_three_plus_one hr hd hpair hv0 hv1 hv3 hv4 hv2 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h01 h03 h04
  · exact no_star_three_plus_one hr hd hpair hv0 hv1 hv3 hv4 hv2 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h01 h03 h04
  · exact no_star_three_plus_one hr hd hpair hv0 hv1 hv3 hv5 hv2 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h01 h03 h05
  · exact no_star_three_plus_one hd hr hpair_swap hv0 hv2 hv4 hv5 hv1 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h02 h04 h05
  · exact no_star_three_plus_one hr hd hpair hv0 hv1 hv4 hv5 hv2 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h01 h04 h05
  · exact no_star_three_plus_one hd hr hpair_swap hv0 hv2 hv3 hv5 hv1 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h02 h03 h05
  · exact no_star_three_plus_one hd hr hpair_swap hv0 hv2 hv3 hv4 hv1 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h02 h03 h04
  · exact no_star_three_plus_one hd hr hpair_swap hv0 hv2 hv3 hv4 hv1 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h02 h03 h04
  · exact no_star_three_plus_one hr hd hpair hv0 hv2 hv3 hv4 hv1 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h02 h03 h04
  · exact no_star_three_plus_one hr hd hpair hv0 hv2 hv3 hv4 hv1 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h02 h03 h04
  · exact no_star_three_plus_one hr hd hpair hv0 hv2 hv3 hv5 hv1 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h02 h03 h05
  · exact no_star_three_plus_one hd hr hpair_swap hv0 hv1 hv4 hv5 hv2 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h01 h04 h05
  · exact no_star_three_plus_one hr hd hpair hv0 hv2 hv4 hv5 hv1 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h02 h04 h05
  · exact no_star_three_plus_one hd hr hpair_swap hv0 hv1 hv3 hv5 hv2 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h01 h03 h05
  · exact no_star_three_plus_one hd hr hpair_swap hv0 hv1 hv3 hv4 hv2 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h01 h03 h04
  · exact no_star_three_plus_one hd hr hpair_swap hv0 hv1 hv3 hv4 hv2 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h01 h03 h04
  · exact no_star_three_plus_one hr hd hpair hv0 hv3 hv4 hv5 hv1 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h03 h04 h05
  · exact no_star_three_plus_one hd hr hpair_swap hv0 hv1 hv2 hv5 hv3 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h01 h02 h05
  · exact no_star_three_plus_one hd hr hpair_swap hv0 hv1 hv2 hv4 hv3 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h01 h02 h04
  · exact no_star_three_plus_one hd hr hpair_swap hv0 hv1 hv2 hv4 hv3 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h01 h02 h04
  · exact no_star_three_plus_one hd hr hpair_swap hv0 hv1 hv2 hv3 hv4 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h01 h02 h03
  · exact no_star_three_plus_one hd hr hpair_swap hv0 hv1 hv2 hv3 hv4 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h01 h02 h03
  · exact no_star_three_plus_one hd hr hpair_swap hv0 hv1 hv2 hv3 hv4 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h01 h02 h03
  · exact no_star_three_plus_one hd hr hpair_swap hv0 hv1 hv2 hv3 hv4 (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) (hne (by rintro ⟨⟩)) h01 h02 h03

/-- Kelly (1947) / Einhorn-Schoenberg (1966) planar 2-distance theorem in Lean:
every finite planar point set with at most 2 distinct positive distances has
cardinality at most 5. -/
theorem two_distance_set_card_le_five (S : Finset Plane)
    (h : distinctDistances S ≤ 2) : S.card ≤ 5 := by
  classical
  by_contra hnot
  obtain ⟨v0, hv0⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have hc1 : (S.erase v0).card = S.card - 1 := Finset.card_erase_of_mem hv0
  obtain ⟨v1, hv1⟩ := Finset.card_pos.mp (by omega : 0 < (S.erase v0).card)
  have hc2 : ((S.erase v0).erase v1).card = (S.erase v0).card - 1 :=
    Finset.card_erase_of_mem hv1
  obtain ⟨v2, hv2⟩ := Finset.card_pos.mp (by omega : 0 < ((S.erase v0).erase v1).card)
  have hc3 : (((S.erase v0).erase v1).erase v2).card = ((S.erase v0).erase v1).card - 1 :=
    Finset.card_erase_of_mem hv2
  obtain ⟨v3, hv3⟩ := Finset.card_pos.mp
    (by omega : 0 < (((S.erase v0).erase v1).erase v2).card)
  have hc4 : ((((S.erase v0).erase v1).erase v2).erase v3).card =
      (((S.erase v0).erase v1).erase v2).card - 1 :=
    Finset.card_erase_of_mem hv3
  obtain ⟨v4, hv4⟩ := Finset.card_pos.mp
    (by omega : 0 < ((((S.erase v0).erase v1).erase v2).erase v3).card)
  have hc5 : (((((S.erase v0).erase v1).erase v2).erase v3).erase v4).card =
      ((((S.erase v0).erase v1).erase v2).erase v3).card - 1 :=
    Finset.card_erase_of_mem hv4
  obtain ⟨v5, hv5⟩ := Finset.card_pos.mp
    (by omega : 0 < (((((S.erase v0).erase v1).erase v2).erase v3).erase v4).card)
  obtain ⟨hv54, hv5_4⟩ := Finset.mem_erase.mp hv5
  obtain ⟨hv53, hv5_3⟩ := Finset.mem_erase.mp hv5_4
  obtain ⟨hv52, hv5_2⟩ := Finset.mem_erase.mp hv5_3
  obtain ⟨hv51, hv5_1⟩ := Finset.mem_erase.mp hv5_2
  obtain ⟨hv50, hv5S⟩ := Finset.mem_erase.mp hv5_1
  obtain ⟨hv43, hv4_3⟩ := Finset.mem_erase.mp hv4
  obtain ⟨hv42, hv4_2⟩ := Finset.mem_erase.mp hv4_3
  obtain ⟨hv41, hv4_1⟩ := Finset.mem_erase.mp hv4_2
  obtain ⟨hv40, hv4S⟩ := Finset.mem_erase.mp hv4_1
  obtain ⟨hv32, hv3_2⟩ := Finset.mem_erase.mp hv3
  obtain ⟨hv31, hv3_1⟩ := Finset.mem_erase.mp hv3_2
  obtain ⟨hv30, hv3S⟩ := Finset.mem_erase.mp hv3_1
  obtain ⟨hv21, hv2_1⟩ := Finset.mem_erase.mp hv2
  obtain ⟨hv20, hv2S⟩ := Finset.mem_erase.mp hv2_1
  obtain ⟨hv10, hv1S⟩ := Finset.mem_erase.mp hv1
  let r01 := dist v0 v1
  have hr01 : r01 ≠ 0 := (dist_pos.mpr hv10.symm).ne'
  have hr01_mem : r01 ∈ Erdos91.DistanceErasure.distanceSet S :=
    (mem_distanceSet S r01).mpr ⟨v0, hv0, v1, hv1S, hv10.symm, rfl⟩
  have hsub2 : ∃ d : ℝ, d ≠ 0 ∧ Erdos91.DistanceErasure.distanceSet S ⊆ {r01, d} := by
    by_cases hcard1 : (Erdos91.DistanceErasure.distanceSet S \ {r01}).Nonempty
    · obtain ⟨d, hd_mem⟩ := hcard1
      have hdS : d ∈ Erdos91.DistanceErasure.distanceSet S := (Finset.mem_sdiff.mp hd_mem).1
      have hdr01 : d ≠ r01 := by
        have h := (Finset.mem_sdiff.mp hd_mem).2
        simpa using h
      obtain ⟨x, _, y, _, hxy, rfl⟩ := (mem_distanceSet S d).mp hdS
      have hd_ne : dist x y ≠ 0 := (dist_pos.mpr hxy).ne'
      refine ⟨dist x y, hd_ne, ?_⟩
      intro t ht
      by_contra hnot_mem
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot_mem
      have hsub3 : ({r01, dist x y, t} : Finset ℝ) ⊆ Erdos91.DistanceErasure.distanceSet S := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact hr01_mem
        · exact hdS
        · exact ht
      have hc3_dist : ({r01, dist x y, t} : Finset ℝ).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hnot_mem.2)]
        simp [hdr01.symm, Ne.symm hnot_mem.1]
      have hle2 := (Finset.card_le_card hsub3).trans h
      omega
    · rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hcard1
      refine ⟨r01, hr01, ?_⟩
      intro t ht
      exact Finset.mem_insert_of_mem (hcard1 ht)
  obtain ⟨d, hd, hsub⟩ := hsub2
  have hpair : ∀ x y, x ≠ y → (x ∈ S) → (y ∈ S) → dist x y = r01 ∨ dist x y = d := by
    intro x y hxy hx hy
    have hmem : dist x y ∈ Erdos91.DistanceErasure.distanceSet S :=
      (mem_distanceSet S (dist x y)).mpr ⟨x, hx, y, hy, hxy, rfl⟩
    have hmem2 := hsub hmem
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem2
  let p : Fin 6 → Plane := ![v0, v1, v2, v3, v4, v5]
  have hp_mem : ∀ i, p i ∈ S := by
    intro i
    fin_cases i <;> assumption
  have hp_inj : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | exact False.elim (hv10.symm hij)
      | exact False.elim (hv20.symm hij)
      | exact False.elim (hv30.symm hij)
      | exact False.elim (hv40.symm hij)
      | exact False.elim (hv50.symm hij)
      | exact False.elim (hv10 hij)
      | exact False.elim (hv21.symm hij)
      | exact False.elim (hv31.symm hij)
      | exact False.elim (hv41.symm hij)
      | exact False.elim (hv51.symm hij)
      | exact False.elim (hv20 hij)
      | exact False.elim (hv21 hij)
      | exact False.elim (hv32.symm hij)
      | exact False.elim (hv42.symm hij)
      | exact False.elim (hv52.symm hij)
      | exact False.elim (hv30 hij)
      | exact False.elim (hv31 hij)
      | exact False.elim (hv32 hij)
      | exact False.elim (hv43.symm hij)
      | exact False.elim (hv53.symm hij)
      | exact False.elim (hv40 hij)
      | exact False.elim (hv41 hij)
      | exact False.elim (hv42 hij)
      | exact False.elim (hv43 hij)
      | exact False.elim (hv54.symm hij)
      | exact False.elim (hv50 hij)
      | exact False.elim (hv51 hij)
      | exact False.elim (hv52 hij)
      | exact False.elim (hv53 hij)
      | exact False.elim (hv54 hij)
  exact no_six_points_two_distances hr01 hd hpair p hp_inj hp_mem

theorem three_le_minimalDistinctDistances_six : 3 ≤ minimalDistinctDistances 6 := by
  obtain ⟨S, hScard, hSdist⟩ := exists_optimal 6
  by_contra hlt
  have hle2 : distinctDistances S ≤ 2 := by omega
  have hcard5 := two_distance_set_card_le_five S hle2
  omega

/-- Exact value `minimalDistinctDistances 6 = 3`, proved unconditionally in Lean. -/
theorem minimalDistinctDistances_six : minimalDistinctDistances 6 = 3 :=
  (not_uniqueMinimizer_six_of_three_le three_le_minimalDistinctDistances_six).1

/-- Exact value `minimalDistinctDistances 7 = 3`, proved unconditionally in Lean. -/
theorem minimalDistinctDistances_seven : minimalDistinctDistances 7 = 3 :=
  (not_uniqueMinimizer_six_of_three_le three_le_minimalDistinctDistances_six).2.1

/-- Unconditional formal proof of `erdos_91.variants.six`: `¬ UniqueMinimizer 6`. -/
theorem not_uniqueMinimizer_six : ¬ UniqueMinimizer 6 :=
  (not_uniqueMinimizer_six_of_three_le three_le_minimalDistinctDistances_six).2.2

end Erdos91.TwoDistanceCapAndSixNonunique

/-! ## Regular Heptagon Optimality and Unconditional Nonuniqueness at n = 7 (`¬ UniqueMinimizer 7`) -/

namespace Erdos91.SevenNonuniqueHeptagonAndWheel
open Finset Erdos91.DistanceErasure Minimizer91 PlateauDefinitions91
  Erdos91.SmallCasesAndSquareBarrier Erdos91.FourNonuniqueAndDoubleEquilateral
  Erdos91.SixAndSevenWheelConfig Erdos91.TwoDistanceCapAndSixNonunique
open EnergyLevels91 (energy)

noncomputable def unitCirclePoint (θ : ℝ) : Plane :=
  !₂[Real.cos θ, Real.sin θ]

theorem dist_unitCirclePoint_sq (α β : ℝ) :
    dist (unitCirclePoint α) (unitCirclePoint β) ^ 2 = 2 - 2 * Real.cos (α - β) := by
  rw [plane_dist_sq]
  dsimp [unitCirclePoint]
  rw [Real.cos_sub]
  linear_combination Real.cos_sq_add_sin_sq α + Real.cos_sq_add_sin_sq β

noncomputable def heptAngle (k : ℕ) : ℝ :=
  2 * Real.pi * (k : ℝ) / 7

noncomputable def heptPoint (k : ℕ) : Plane :=
  unitCirclePoint (heptAngle k)

noncomputable def regularHeptagon : Finset Plane :=
  (Finset.range 7).image heptPoint

theorem dist_heptPoint_sq_natDist (j k : ℕ) :
    dist (heptPoint j) (heptPoint k) ^ 2 =
      2 - 2 * Real.cos (heptAngle (Nat.dist j k)) := by
  unfold heptPoint
  rw [dist_unitCirclePoint_sq]
  congr 2
  rcases le_total j k with hjk | hkj
  · rw [Nat.dist_eq_sub_of_le hjk]
    have hsub : heptAngle j - heptAngle k = -heptAngle (k - j) := by
      unfold heptAngle
      rw [Nat.cast_sub hjk]
      ring
    rw [hsub, Real.cos_neg]
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hkj]
    have hsub : heptAngle j - heptAngle k = heptAngle (j - k) := by
      unfold heptAngle
      rw [Nat.cast_sub hkj]
      ring
    rw [hsub]

theorem cos_heptAngle_symm :
    Real.cos (heptAngle 0) = 1 ∧
      Real.cos (heptAngle 4) = Real.cos (heptAngle 3) ∧
      Real.cos (heptAngle 5) = Real.cos (heptAngle 2) ∧
      Real.cos (heptAngle 6) = Real.cos (heptAngle 1) := by
  have h0 : heptAngle 0 = 0 := by unfold heptAngle; ring
  have h4 : heptAngle 4 = 2 * Real.pi - heptAngle 3 := by unfold heptAngle; push_cast; ring
  have h5 : heptAngle 5 = 2 * Real.pi - heptAngle 2 := by unfold heptAngle; push_cast; ring
  have h6 : heptAngle 6 = 2 * Real.pi - heptAngle 1 := by unfold heptAngle; push_cast; ring
  refine ⟨by rw [h0, Real.cos_zero],
    by rw [h4, Real.cos_two_pi_sub],
    by rw [h5, Real.cos_two_pi_sub],
    by rw [h6, Real.cos_two_pi_sub]⟩

theorem cos_heptAngle_lt_one {d : ℕ} (hd1 : 1 ≤ d) (hd6 : d ≤ 6) :
    Real.cos (heptAngle d) < 1 := by
  obtain ⟨_, h4, h5, h6⟩ := cos_heptAngle_symm
  have hsmall : ∀ m : ℕ, 1 ≤ m → m ≤ 3 → Real.cos (heptAngle m) < 1 := by
    intro m hm1 hm3
    have hpi : 0 < Real.pi := Real.pi_pos
    have hm_lo : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hm_hi : (m : ℝ) ≤ 3 := by exact_mod_cast hm3
    have hpos : 0 < heptAngle m := by unfold heptAngle; nlinarith
    have hle_pi : heptAngle m ≤ Real.pi := by unfold heptAngle; nlinarith
    have hlt := Real.strictAntiOn_cos
      (Set.left_mem_Icc.mpr Real.pi_pos.le)
      ⟨hpos.le, hle_pi⟩ hpos
    simpa only [Real.cos_zero] using hlt
  have hd_cases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 := by omega
  rcases hd_cases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hsmall 1 (by omega) (by omega)
  · exact hsmall 2 (by omega) (by omega)
  · exact hsmall 3 (by omega) (by omega)
  · rw [h4]; exact hsmall 3 (by omega) (by omega)
  · rw [h5]; exact hsmall 2 (by omega) (by omega)
  · rw [h6]; exact hsmall 1 (by omega) (by omega)

theorem heptPoint_injOn : Set.InjOn heptPoint (Finset.range 7 : Set ℕ) := by
  intro j hj k hk hjk_eq
  rw [Finset.mem_coe, Finset.mem_range] at hj hk
  by_contra hne
  have hd_lo : 1 ≤ Nat.dist j k := by unfold Nat.dist; omega
  have hd_hi : Nat.dist j k ≤ 6 := by unfold Nat.dist; omega
  have hcos := cos_heptAngle_lt_one hd_lo hd_hi
  have hsq : dist (heptPoint j) (heptPoint k) ^ 2 = 0 := by
    rw [hjk_eq, dist_self, zero_pow (by rintro ⟨⟩)]
  rw [dist_heptPoint_sq_natDist] at hsq
  linarith

theorem card_regularHeptagon : regularHeptagon.card = 7 := by
  unfold regularHeptagon
  rw [Finset.card_image_of_injOn heptPoint_injOn, Finset.card_range]

noncomputable def heptDist (d : ℕ) : ℝ :=
  Real.sqrt (2 - 2 * Real.cos (heptAngle d))

theorem distanceSet_regularHeptagon_subset :
    Erdos91.DistanceErasure.distanceSet regularHeptagon ⊆
      {heptDist 1, heptDist 2, heptDist 3} := by
  classical
  obtain ⟨_, h4, h5, h6⟩ := cos_heptAngle_symm
  intro r hr
  obtain ⟨x, hx, y, hy, hxy, rfl⟩ := (mem_distanceSet regularHeptagon r).mp hr
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
  rw [Finset.mem_range] at hj hk
  have hjk : j ≠ k := fun h => hxy (congrArg heptPoint h)
  have hd_cases :
      Nat.dist j k = 1 ∨ Nat.dist j k = 2 ∨ Nat.dist j k = 3 ∨
        Nat.dist j k = 4 ∨ Nat.dist j k = 5 ∨ Nat.dist j k = 6 := by
    unfold Nat.dist; omega
  have hdist_eq (m : ℕ) (hcos : Real.cos (heptAngle (Nat.dist j k)) = Real.cos (heptAngle m)) :
      dist (heptPoint j) (heptPoint k) = heptDist m := by
    rw [← Real.sqrt_sq dist_nonneg, dist_heptPoint_sq_natDist, hcos]
    rfl
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases hd_cases with hd | hd | hd | hd | hd | hd
  · left; exact hdist_eq 1 (by rw [hd])
  · right; left; exact hdist_eq 2 (by rw [hd])
  · right; right; exact hdist_eq 3 (by rw [hd])
  · right; right; exact hdist_eq 3 (by rw [hd, h4])
  · right; left; exact hdist_eq 2 (by rw [hd, h5])
  · left; exact hdist_eq 1 (by rw [hd, h6])

theorem distinctDistances_regularHeptagon_le_three :
    distinctDistances regularHeptagon ≤ 3 := by
  classical
  have h := Finset.card_le_card distanceSet_regularHeptagon_subset
  have h3 : ({heptDist 1, heptDist 2, heptDist 3} : Finset ℝ).card ≤ 3 :=
    (Finset.card_insert_le _ _).trans (Nat.succ_le_succ Finset.card_le_two)
  exact h.trans h3

/-- Formal proof of `erdos_91.test.circleSeven_optimal`: the regular 7-gon has
7 vertices and achieves the global minimum `minimalDistinctDistances 7 = 3`. -/
theorem regularHeptagon_isOptimal : IsOptimal regularHeptagon 7 := by
  refine ⟨card_regularHeptagon, le_antisymm ?_
    (minimal_le regularHeptagon 7 card_regularHeptagon)⟩
  rw [minimalDistinctDistances_seven]
  exact distinctDistances_regularHeptagon_le_three

/-- Formal proof of `erdos_91.test.wheelSeven_optimal`: the 7-point wheel has
7 vertices and achieves the global minimum `minimalDistinctDistances 7 = 3`. -/
theorem centeredWheelSeven_isOptimal : IsOptimal centeredWheelSeven 7 := by
  refine ⟨card_centeredWheelSeven, le_antisymm ?_
    (minimal_le centeredWheelSeven 7 card_centeredWheelSeven)⟩
  rw [minimalDistinctDistances_seven]
  exact distinctDistances_centeredWheelSeven_le_three

noncomputable def heptConstEnergy : ℝ :=
  12 - 4 * (Real.cos (heptAngle 1) + Real.cos (heptAngle 2) + Real.cos (heptAngle 3))

theorem regularHeptagon_energy_const (x : Plane) (hx : x ∈ regularHeptagon) :
    energy regularHeptagon x = heptConstEnergy := by
  classical
  obtain ⟨h0, h4, h5, h6⟩ := cos_heptAngle_symm
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  rw [Finset.mem_range] at hj
  unfold energy regularHeptagon
  rw [Finset.sum_image heptPoint_injOn]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    dist_heptPoint_sq_natDist]
  have hj_cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases hj_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    { dsimp [Nat.dist]
      try rw [h0]
      try rw [h4]
      try rw [h5]
      try rw [h6]
      unfold heptConstEnergy
      ring }

/-- Formal proof of `erdos_91.test.dissimilar_circleSeven_wheelSeven`: the
regular 7-gon (which has constant vertex energy) is not similar to the 7-point
wheel (whose center and rim vertices have unequal energies `6 ≠ 13`). -/
theorem not_similar_regularHeptagon_centeredWheelSeven :
    ¬ DilationEquivSimilar regularHeptagon centeredWheelSeven := by
  intro hsim
  obtain ⟨f, hf⟩ := (similar_iff_image regularHeptagon centeredWheelSeven).mp hsim
  have hp0 : equiP0 ∈ centeredWheelSeven := by simp [centeredWheelSeven]
  have hp1 : equiP1 ∈ centeredWheelSeven := by simp [centeredWheelSeven]
  have heq := energy_eq_of_similar_const regularHeptagon_energy_const hf hp0 hp1
  obtain ⟨he0, he1⟩ := centeredWheelSeven_energies
  linarith

/-- Unconditional formal proof of `erdos_91.variants.seven`: for n = 7, the
regular 7-gon and the 7-point wheel are both globally optimal 7-point planar
sets and are not similar under any `DilationEquiv`. -/
theorem not_uniqueMinimizer_seven : ¬ UniqueMinimizer 7 := by
  intro huniq
  exact not_similar_regularHeptagon_centeredWheelSeven
    (huniq regularHeptagon centeredWheelSeven
      regularHeptagon_isOptimal centeredWheelSeven_isOptimal)

end Erdos91.SevenNonuniqueHeptagonAndWheel
namespace Erdos91.EightAndNineNonunique
open Finset Erdos91.DistanceErasure Minimizer91 PlateauDefinitions91
  Erdos91.SmallCasesAndSquareBarrier Erdos91.FourNonuniqueAndDoubleEquilateral
  Erdos91.SixAndSevenWheelConfig Erdos91.SevenNonuniqueHeptagonAndWheel
open EnergyLevels91 (energy)

noncomputable def triP7 : Plane := !₂[0, Real.sqrt 3]
noncomputable def triP8 : Plane := !₂[3 / 2, Real.sqrt 3 / 2]

noncomputable def triangularNine : Finset Plane :=
  insert triP7 (insert triP8 centeredWheelSeven)

noncomputable def triangularEightA : Finset Plane :=
  triangularNine.erase equiP0

noncomputable def triangularEightB : Finset Plane :=
  triangularNine.erase equiP1

theorem sqrt3_extra_lemmas :
    ((0 : ℝ) - Real.sqrt 3) ^ 2 = 3 ∧
      (Real.sqrt 3 - 0) ^ 2 = 3 ∧
      (Real.sqrt 3 / 2 - Real.sqrt 3) ^ 2 = 3 / 4 ∧
      (Real.sqrt 3 - Real.sqrt 3 / 2) ^ 2 = 3 / 4 ∧
      (-Real.sqrt 3 / 2 - Real.sqrt 3) ^ 2 = 27 / 4 ∧
      (Real.sqrt 3 - -Real.sqrt 3 / 2) ^ 2 = 27 / 4 := by
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨by linear_combination hs3, by linear_combination hs3,
    by linear_combination hs3 / 4, by linear_combination hs3 / 4,
    by linear_combination (9 / 4) * hs3, by linear_combination (9 / 4) * hs3⟩

theorem tri_extra_ne :
    triP7 ≠ triP8 ∧
      triP7 ≠ equiP0 ∧ triP7 ≠ equiP1 ∧ triP7 ≠ hexM1 ∧
      triP7 ≠ equiP2 ∧ triP7 ≠ hexQ2 ∧ triP7 ≠ equiP3 ∧ triP7 ≠ hexQ3 ∧
      triP8 ≠ equiP0 ∧ triP8 ≠ equiP1 ∧ triP8 ≠ hexM1 ∧
      triP8 ≠ equiP2 ∧ triP8 ≠ hexQ2 ∧ triP8 ≠ equiP3 ∧ triP8 ≠ hexQ3 := by
  have hs_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; have h0 : (0 : ℝ) = 3 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h1 : Real.sqrt 3 = 0 := congrArg (fun x : Plane => x 1) h; linarith
  · intro h; have h0 : (0 : ℝ) = 1 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (0 : ℝ) = -1 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (0 : ℝ) = 1 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (0 : ℝ) = -1 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (0 : ℝ) = 1 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (0 : ℝ) = -1 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (3 / 2 : ℝ) = 0 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (3 / 2 : ℝ) = 1 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (3 / 2 : ℝ) = -1 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (3 / 2 : ℝ) = 1 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (3 / 2 : ℝ) = -1 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (3 / 2 : ℝ) = 1 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0
  · intro h; have h0 : (3 / 2 : ℝ) = -1 / 2 := congrArg (fun x : Plane => x 0) h; norm_num at h0

theorem card_triangularNine : triangularNine.card = 9 := by
  obtain ⟨h78, h70, h71, h7m1, h72, h7q2, h73, h7q3,
    h80, h81, h8m1, h82, h8q2, h83, h8q3⟩ := tri_extra_ne
  unfold triangularNine
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, card_centeredWheelSeven]
  · simp [centeredWheelSeven, h80, h81, h8m1, h82, h8q2, h83, h8q3]
  · simp [centeredWheelSeven, h78, h70, h71, h7m1, h72, h7q2, h73, h7q3]

theorem triangularNine_dist_sq_cases (x y : Plane)
    (hx : x ∈ triangularNine) (hy : y ∈ triangularNine) :
    dist x y ^ 2 = 0 ∨ dist x y ^ 2 = 1 ∨ dist x y ^ 2 = 3 ∨
      dist x y ^ 2 = 4 ∨ dist x y ^ 2 = 7 := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := sqrt3_sub_lemmas
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := sqrt3_extra_lemmas
  simp only [triangularNine, centeredWheelSeven, Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    { rw [plane_dist_sq]
      dsimp [triP7, triP8, equiP0, equiP1, hexM1, equiP2, hexQ2, equiP3, hexQ3]
      try rw [s1]
      try rw [s2]
      try rw [s3]
      try rw [s4]
      try rw [s5]
      try rw [s6]
      try rw [e1]
      try rw [e2]
      try rw [e3]
      try rw [e4]
      try rw [e5]
      try rw [e6]
      norm_num }

theorem distanceSet_triangularNine_subset :
    Erdos91.DistanceErasure.distanceSet triangularNine ⊆
      {1, Real.sqrt 3, 2, Real.sqrt 7} := by
  classical
  intro r hr
  obtain ⟨x, hx, y, hy, hxy, rfl⟩ := (mem_distanceSet triangularNine r).mp hr
  have hpos : 0 < dist x y := dist_pos.mpr hxy
  have hcases := triangularNine_dist_sq_cases x y hx hy
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases hcases with h0 | h1 | h3 | h4 | h7
  · exfalso; nlinarith
  · left; nlinarith
  · right; left
    have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hpos3 : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    nlinarith
  · right; right; left; nlinarith
  · right; right; right
    have hs7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
    have hpos7 : (0 : ℝ) ≤ Real.sqrt 7 := Real.sqrt_nonneg 7
    nlinarith

theorem distinctDistances_triangularNine_le_four :
    distinctDistances triangularNine ≤ 4 := by
  classical
  have h := Finset.card_le_card distanceSet_triangularNine_subset
  have h4 : ({1, Real.sqrt 3, 2, Real.sqrt 7} : Finset ℝ).card ≤ 4 :=
    (Finset.card_insert_le _ _).trans
      (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
        (Nat.succ_le_succ Finset.card_le_two)))
  exact h.trans h4

theorem minimalDistinctDistances_nine_le_four :
    minimalDistinctDistances 9 ≤ 4 :=
  (minimal_le triangularNine 9 card_triangularNine).trans
    distinctDistances_triangularNine_le_four

theorem minimalDistinctDistances_eight_le_four :
    minimalDistinctDistances 8 ≤ 4 :=
  (MinimumMonotone91.minimum_monotone (by omega : 8 ≤ 9)).trans
    minimalDistinctDistances_nine_le_four

theorem triangularNine_diameter_pair (x y : Plane)
    (hx : x ∈ triangularNine) (hy : y ∈ triangularNine) :
    dist x y ≤ dist hexQ3 triP8 := by
  obtain ⟨_, _, _, _, _, s6⟩ := sqrt3_sub_lemmas
  have hd_sq : dist hexQ3 triP8 ^ 2 = 7 := by
    rw [plane_dist_sq]
    dsimp [hexQ3, triP8]
    rw [s6]
    norm_num
  have hcases := triangularNine_dist_sq_cases x y hx hy
  have hle : dist x y ^ 2 ≤ dist hexQ3 triP8 ^ 2 := by
    rw [hd_sq]
    rcases hcases with h | h | h | h | h <;> linarith
  nlinarith [dist_nonneg (x := x) (y := y), dist_nonneg (x := hexQ3) (y := triP8)]

theorem triangularNine_energies :
    energy triangularNine equiP0 = 12 ∧
      energy triangularNine equiP1 = 18 := by
  classical
  obtain ⟨h78, h70, h71, h7m1, h72, h7q2, h73, h7q3,
    h80, h81, h8m1, h82, h8q2, h83, h8q3⟩ := tri_extra_ne
  obtain ⟨he0, he1⟩ := centeredWheelSeven_energies
  obtain ⟨s1, _, _, _, _, _⟩ := sqrt3_sub_lemmas
  obtain ⟨e1, _, _, _, _, _⟩ := sqrt3_extra_lemmas
  have hm7 : triP7 ∉ insert triP8 centeredWheelSeven := by
    simp [centeredWheelSeven, h78, h70, h71, h7m1, h72, h7q2, h73, h7q3]
  have hm8 : triP8 ∉ centeredWheelSeven := by
    simp [centeredWheelSeven, h80, h81, h8m1, h82, h8q2, h83, h8q3]
  constructor
  · unfold energy triangularNine
    rw [Finset.sum_insert hm7, Finset.sum_insert hm8]
    change dist equiP0 triP7 ^ 2 + (dist equiP0 triP8 ^ 2 + energy centeredWheelSeven equiP0) = 12
    rw [he0, plane_dist_sq, plane_dist_sq]
    dsimp [equiP0, triP7, triP8]
    rw [e1, s1]
    norm_num
  · unfold energy triangularNine
    rw [Finset.sum_insert hm7, Finset.sum_insert hm8]
    change dist equiP1 triP7 ^ 2 + (dist equiP1 triP8 ^ 2 + energy centeredWheelSeven equiP1) = 18
    rw [he1, plane_dist_sq, plane_dist_sq]
    dsimp [equiP1, triP7, triP8]
    rw [e1, s1]
    norm_num

/-- The two 8-point deletions `triangularEightA` and `triangularEightB` of
`triangularNine` have at most 4 distinct distances and are nonsimilar under all
full-plane similarities. -/
theorem not_similar_triangularEightA_triangularEightB :
    ¬ DilationEquivSimilar triangularEightA triangularEightB := by
  rw [similar_iff_image]
  obtain ⟨_, _, _, _, _, _, _, _,
    h80, h81, _, _, _, _, h8q3⟩ := tri_extra_ne
  obtain ⟨h01, _, _, _, _, h0q3, _, _, _, _, h1q3, _⟩ := wheel_pairwise_ne
  obtain ⟨he0, he1⟩ := triangularNine_energies
  apply DeletionEnergy91.nonsimilar_deletions triangularNine
    hexQ3 triP8 equiP0 equiP1 h8q3.symm
    (by simp [triangularNine, centeredWheelSeven])
    (by simp [triangularNine])
    (by simp [triangularNine, centeredWheelSeven])
    (by simp [triangularNine, centeredWheelSeven])
    h0q3 h80.symm h1q3 h81.symm
    (fun x hx y hy => triangularNine_diameter_pair x y hx hy)
  linarith

noncomputable def nonagonAngle (k : ℕ) : ℝ :=
  2 * Real.pi * (k : ℝ) / 9

noncomputable def nonagonPoint (k : ℕ) : Plane :=
  unitCirclePoint (nonagonAngle k)

noncomputable def regularNonagon : Finset Plane :=
  (Finset.range 9).image nonagonPoint

theorem dist_nonagonPoint_sq_natDist (j k : ℕ) :
    dist (nonagonPoint j) (nonagonPoint k) ^ 2 =
      2 - 2 * Real.cos (nonagonAngle (Nat.dist j k)) := by
  unfold nonagonPoint
  rw [dist_unitCirclePoint_sq]
  congr 2
  rcases le_total j k with hjk | hkj
  · rw [Nat.dist_eq_sub_of_le hjk]
    have hsub : nonagonAngle j - nonagonAngle k = -nonagonAngle (k - j) := by
      unfold nonagonAngle
      rw [Nat.cast_sub hjk]
      ring
    rw [hsub, Real.cos_neg]
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hkj]
    have hsub : nonagonAngle j - nonagonAngle k = nonagonAngle (j - k) := by
      unfold nonagonAngle
      rw [Nat.cast_sub hkj]
      ring
    rw [hsub]

theorem cos_nonagonAngle_symm :
    Real.cos (nonagonAngle 0) = 1 ∧
      Real.cos (nonagonAngle 5) = Real.cos (nonagonAngle 4) ∧
      Real.cos (nonagonAngle 6) = Real.cos (nonagonAngle 3) ∧
      Real.cos (nonagonAngle 7) = Real.cos (nonagonAngle 2) ∧
      Real.cos (nonagonAngle 8) = Real.cos (nonagonAngle 1) := by
  have h0 : nonagonAngle 0 = 0 := by unfold nonagonAngle; ring
  have h5 : nonagonAngle 5 = 2 * Real.pi - nonagonAngle 4 := by unfold nonagonAngle; push_cast; ring
  have h6 : nonagonAngle 6 = 2 * Real.pi - nonagonAngle 3 := by unfold nonagonAngle; push_cast; ring
  have h7 : nonagonAngle 7 = 2 * Real.pi - nonagonAngle 2 := by unfold nonagonAngle; push_cast; ring
  have h8 : nonagonAngle 8 = 2 * Real.pi - nonagonAngle 1 := by unfold nonagonAngle; push_cast; ring
  refine ⟨by rw [h0, Real.cos_zero],
    by rw [h5, Real.cos_two_pi_sub],
    by rw [h6, Real.cos_two_pi_sub],
    by rw [h7, Real.cos_two_pi_sub],
    by rw [h8, Real.cos_two_pi_sub]⟩

theorem cos_nonagonAngle_lt_one {d : ℕ} (hd1 : 1 ≤ d) (hd8 : d ≤ 8) :
    Real.cos (nonagonAngle d) < 1 := by
  obtain ⟨_, h5, h6, h7, h8⟩ := cos_nonagonAngle_symm
  have hsmall : ∀ m : ℕ, 1 ≤ m → m ≤ 4 → Real.cos (nonagonAngle m) < 1 := by
    intro m hm1 hm4
    have hpi : 0 < Real.pi := Real.pi_pos
    have hm_lo : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hm_hi : (m : ℝ) ≤ 4 := by exact_mod_cast hm4
    have hpos : 0 < nonagonAngle m := by unfold nonagonAngle; nlinarith
    have hle_pi : nonagonAngle m ≤ Real.pi := by unfold nonagonAngle; nlinarith
    have hlt := Real.strictAntiOn_cos
      (Set.left_mem_Icc.mpr Real.pi_pos.le)
      ⟨hpos.le, hle_pi⟩ hpos
    simpa only [Real.cos_zero] using hlt
  have hd_cases :
      d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 := by omega
  rcases hd_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hsmall 1 (by omega) (by omega)
  · exact hsmall 2 (by omega) (by omega)
  · exact hsmall 3 (by omega) (by omega)
  · exact hsmall 4 (by omega) (by omega)
  · rw [h5]; exact hsmall 4 (by omega) (by omega)
  · rw [h6]; exact hsmall 3 (by omega) (by omega)
  · rw [h7]; exact hsmall 2 (by omega) (by omega)
  · rw [h8]; exact hsmall 1 (by omega) (by omega)

theorem nonagonPoint_injOn : Set.InjOn nonagonPoint (Finset.range 9 : Set ℕ) := by
  intro j hj k hk hjk_eq
  rw [Finset.mem_coe, Finset.mem_range] at hj hk
  by_contra hne
  have hd_lo : 1 ≤ Nat.dist j k := by unfold Nat.dist; omega
  have hd_hi : Nat.dist j k ≤ 8 := by unfold Nat.dist; omega
  have hcos := cos_nonagonAngle_lt_one hd_lo hd_hi
  have hsq : dist (nonagonPoint j) (nonagonPoint k) ^ 2 = 0 := by
    rw [hjk_eq, dist_self, zero_pow (by rintro ⟨⟩)]
  rw [dist_nonagonPoint_sq_natDist] at hsq
  linarith

theorem card_regularNonagon : regularNonagon.card = 9 := by
  unfold regularNonagon
  rw [Finset.card_image_of_injOn nonagonPoint_injOn, Finset.card_range]

noncomputable def nonagonDist (d : ℕ) : ℝ :=
  Real.sqrt (2 - 2 * Real.cos (nonagonAngle d))

theorem distanceSet_regularNonagon_subset :
    Erdos91.DistanceErasure.distanceSet regularNonagon ⊆
      {nonagonDist 1, nonagonDist 2, nonagonDist 3, nonagonDist 4} := by
  classical
  obtain ⟨_, h5, h6, h7, h8⟩ := cos_nonagonAngle_symm
  intro r hr
  obtain ⟨x, hx, y, hy, hxy, rfl⟩ := (mem_distanceSet regularNonagon r).mp hr
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
  rw [Finset.mem_range] at hj hk
  have hjk : j ≠ k := fun h => hxy (congrArg nonagonPoint h)
  have hd_cases :
      Nat.dist j k = 1 ∨ Nat.dist j k = 2 ∨ Nat.dist j k = 3 ∨ Nat.dist j k = 4 ∨
        Nat.dist j k = 5 ∨ Nat.dist j k = 6 ∨ Nat.dist j k = 7 ∨ Nat.dist j k = 8 := by
    unfold Nat.dist; omega
  have hdist_eq (m : ℕ)
      (hcos : Real.cos (nonagonAngle (Nat.dist j k)) = Real.cos (nonagonAngle m)) :
      dist (nonagonPoint j) (nonagonPoint k) = nonagonDist m := by
    rw [← Real.sqrt_sq dist_nonneg, dist_nonagonPoint_sq_natDist, hcos]
    rfl
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases hd_cases with hd | hd | hd | hd | hd | hd | hd | hd
  · left; exact hdist_eq 1 (by rw [hd])
  · right; left; exact hdist_eq 2 (by rw [hd])
  · right; right; left; exact hdist_eq 3 (by rw [hd])
  · right; right; right; exact hdist_eq 4 (by rw [hd])
  · right; right; right; exact hdist_eq 4 (by rw [hd, h5])
  · right; right; left; exact hdist_eq 3 (by rw [hd, h6])
  · right; left; exact hdist_eq 2 (by rw [hd, h7])
  · left; exact hdist_eq 1 (by rw [hd, h8])

theorem distinctDistances_regularNonagon_le_four :
    distinctDistances regularNonagon ≤ 4 := by
  classical
  have h := Finset.card_le_card distanceSet_regularNonagon_subset
  have h4 : ({nonagonDist 1, nonagonDist 2, nonagonDist 3, nonagonDist 4} : Finset ℝ).card ≤ 4 :=
    (Finset.card_insert_le _ _).trans
      (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
        (Nat.succ_le_succ Finset.card_le_two)))
  exact h.trans h4

noncomputable def nonagonConstEnergy : ℝ :=
  16 - 4 * (Real.cos (nonagonAngle 1) + Real.cos (nonagonAngle 2) +
    Real.cos (nonagonAngle 3) + Real.cos (nonagonAngle 4))

theorem regularNonagon_energy_const (x : Plane) (hx : x ∈ regularNonagon) :
    energy regularNonagon x = nonagonConstEnergy := by
  classical
  obtain ⟨h0, h5, h6, h7, h8⟩ := cos_nonagonAngle_symm
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  rw [Finset.mem_range] at hj
  unfold energy regularNonagon
  rw [Finset.sum_image nonagonPoint_injOn]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    dist_nonagonPoint_sq_natDist]
  have hj_cases :
      j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega
  rcases hj_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    { dsimp [Nat.dist]
      try rw [h0]
      try rw [h5]
      try rw [h6]
      try rw [h7]
      try rw [h8]
      unfold nonagonConstEnergy
      ring }

/-- The regular 9-gon (constant vertex energy) is not similar to the 9-point
triangular-lattice configuration `triangularNine` (whose vertices `equiP0` and
`equiP1` have unequal energies `12 ≠ 18`). -/
theorem not_similar_regularNonagon_triangularNine :
    ¬ DilationEquivSimilar regularNonagon triangularNine := by
  intro hsim
  obtain ⟨f, hf⟩ := (similar_iff_image regularNonagon triangularNine).mp hsim
  have hp0 : equiP0 ∈ triangularNine := by simp [triangularNine, centeredWheelSeven]
  have hp1 : equiP1 ∈ triangularNine := by simp [triangularNine, centeredWheelSeven]
  have heq := energy_eq_of_similar_const regularNonagon_energy_const hf hp0 hp1
  obtain ⟨he0, he1⟩ := triangularNine_energies
  linarith

/-- Reduction of `erdos_91.variants.eight` (`¬ UniqueMinimizer 8`),
`erdos_91.variants.nine` (`¬ UniqueMinimizer 9`), and `d(8) = d(9) = 4` to the
3-distance threshold `4 ≤ minimalDistinctDistances 8`. -/
theorem not_uniqueMinimizer_eight_and_nine_of_four_le
    (h8 : 4 ≤ minimalDistinctDistances 8) :
    minimalDistinctDistances 8 = 4 ∧
      minimalDistinctDistances 9 = 4 ∧
      ¬ UniqueMinimizer 8 ∧
      ¬ UniqueMinimizer 9 := by
  classical
  have hm8 : minimalDistinctDistances 8 = 4 :=
    le_antisymm minimalDistinctDistances_eight_le_four h8
  have hm9 : minimalDistinctDistances 9 = 4 := by
    apply le_antisymm minimalDistinctDistances_nine_le_four
    rw [← hm8]
    exact MinimumMonotone91.minimum_monotone (by omega)
  have hTri9Opt : IsOptimal triangularNine 9 := by
    refine ⟨card_triangularNine, le_antisymm ?_
      (minimal_le triangularNine 9 card_triangularNine)⟩
    rw [hm9]
    exact distinctDistances_triangularNine_le_four
  have hNon9Opt : IsOptimal regularNonagon 9 := by
    refine ⟨card_regularNonagon, le_antisymm ?_
      (minimal_le regularNonagon 9 card_regularNonagon)⟩
    rw [hm9]
    exact distinctDistances_regularNonagon_le_four
  have h8AOpt : IsOptimal triangularEightA 8 := by
    apply MinimumMonotone91.plateau_subset_optimal triangularEightA triangularNine 8 9
      hTri9Opt (Finset.erase_subset _ _) _ (hm8.trans hm9.symm)
    unfold triangularEightA
    rw [Finset.card_erase_of_mem (by simp [triangularNine, centeredWheelSeven]),
      card_triangularNine]
  have h8BOpt : IsOptimal triangularEightB 8 := by
    apply MinimumMonotone91.plateau_subset_optimal triangularEightB triangularNine 8 9
      hTri9Opt (Finset.erase_subset _ _) _ (hm8.trans hm9.symm)
    unfold triangularEightB
    rw [Finset.card_erase_of_mem (by simp [triangularNine, centeredWheelSeven]),
      card_triangularNine]
  refine ⟨hm8, hm9, ?_, ?_⟩
  · intro huniq8
    exact not_similar_triangularEightA_triangularEightB
      (huniq8 triangularEightA triangularEightB h8AOpt h8BOpt)
  · intro huniq9
    exact not_similar_regularNonagon_triangularNine
      (huniq9 regularNonagon triangularNine hNon9Opt hTri9Opt)

end Erdos91.EightAndNineNonunique
namespace Erdos91.AsymptoticDensityOneAndGlobalBounds
open Finset Filter Minimizer91 PlateauDefinitions91
  Erdos91.GeneralMultiplicityAndDensityOne

noncomputable instance : DecidablePred UniqueMinimizer :=
  Classical.decPred _

noncomputable instance (K : ℕ) : DecidablePred (HasAtLeastKNonsimilarMinimizers K) :=
  Classical.decPred _

noncomputable def uniqueMinimizerSet (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter UniqueMinimizer

noncomputable def badMultiplicitySet (K N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun n => ¬ HasAtLeastKNonsimilarMinimizers K n)

noncomputable def goodMultiplicitySet (K N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (HasAtLeastKNonsimilarMinimizers K)

theorem good_add_badMultiplicitySet_card (K N : ℕ) :
    (goodMultiplicitySet K N).card + (badMultiplicitySet K N).card = N + 1 := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.range (N + 1)) (p := HasAtLeastKNonsimilarMinimizers K)
  simpa only [goodMultiplicitySet, badMultiplicitySet, Finset.card_range] using h

end Erdos91.AsymptoticDensityOneAndGlobalBounds
namespace Erdos91.TwoPointDeletionAndTwoStepPlateau
open Finset Minimizer91 PlateauDefinitions91
open SimilarityEnergy91 (pairEnergy pairEnergy_eq_of_shared_diameter)
open EnergyLevels91 (energy)
open DeletionEnergy91 (deletion_identity)
open Erdos91.SmallCasesAndSquareBarrier (plane_dist_sq)

/-- Explicit planar difference dot product `(p - q) · (r - s)`. -/
def planeDot (p q r s : Plane) : ℝ :=
  (p 0 - q 0) * (r 0 - s 0) + (p 1 - q 1) * (r 1 - s 1)

/-- Row energy after erasing `u ∈ S`: `energy (S.erase u) v = energy S v - dist v u ^ 2`. -/
theorem energy_erase_eq_sub (S : Finset Plane) (u v : Plane) (hu : u ∈ S) :
    energy (S.erase u) v = energy S v - dist v u ^ 2 := by
  classical
  unfold energy
  exact sum_erase_eq_sub hu

/-- Exact double-deletion pair-energy identity (`TWO-DELETION.md`):
for any `u, v ∈ S` with `u ≠ v`,
`pairEnergy ((S.erase u).erase v) = pairEnergy S - 2 * energy S u - 2 * energy S v + 2 * dist u v ^ 2`. -/
theorem double_deletion_pairEnergy_identity
    (S : Finset Plane) (u v : Plane)
    (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) :
    pairEnergy ((S.erase u).erase v) =
      pairEnergy S - 2 * energy S u - 2 * energy S v + 2 * dist u v ^ 2 := by
  classical
  have hv_erase : v ∈ S.erase u := mem_erase.mpr ⟨huv.symm, hv⟩
  rw [deletion_identity (S.erase u) v hv_erase,
    deletion_identity S u hu,
    energy_erase_eq_sub S u v hu,
    dist_comm v u]
  ring

/-- Alternating four-point double-deletion pair-energy cancellation (`TWO-DELETION.md`):
for any `p, q, r, s ∈ S` with `p ≠ r`, `p ≠ s`, `q ≠ r`, `q ≠ s`,
all single-point row energies `energy S ·` and `pairEnergy S` cancel identically,
leaving `4 * ((p - q) · (s - r))`. -/
theorem alternating_double_deletion_pairEnergy
    (S : Finset Plane) (p q r s : Plane)
    (hp : p ∈ S) (hq : q ∈ S) (hr : r ∈ S) (hs : s ∈ S)
    (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) :
    (pairEnergy ((S.erase p).erase r) + pairEnergy ((S.erase q).erase s)) -
      (pairEnergy ((S.erase p).erase s) + pairEnergy ((S.erase q).erase r)) =
      4 * planeDot p q s r := by
  rw [double_deletion_pairEnergy_identity S p r hp hr hpr,
    double_deletion_pairEnergy_identity S q s hq hs hqs,
    double_deletion_pairEnergy_identity S p s hp hs hps,
    double_deletion_pairEnergy_identity S q r hq hr hqr,
    plane_dist_sq p r, plane_dist_sq q s, plane_dist_sq p s, plane_dist_sq q r]
  dsimp [planeDot]
  ring

/-- Five-point planar orthogonality exclusion (`TWO-DELETION.md`):
five distinct planar points `x1, x2, x3, x4, x5` cannot have all disjoint pairs of
difference vectors orthogonal. Specifically, `(x1 - x2) ⊥ (x3 - x4), (x4 - x5)`
forces `x3, x4, x5` collinear; `(x1 - x3) ⊥ (x2 - x4), (x4 - x5)` forces
`x2, x4, x5` collinear; hence `x2 - x3` is parallel to `x4 - x5`, which combined
with `(x2 - x3) ⊥ (x4 - x5)` and Lagrange's identity contradicts `x2 ≠ x3` and `x4 ≠ x5`. -/
theorem no_five_points_all_disjoint_pairs_orthogonal
    (x1 x2 x3 x4 x5 : Plane)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3) (h45 : x4 ≠ x5)
    (horth_12_34 : planeDot x1 x2 x3 x4 = 0)
    (horth_12_45 : planeDot x1 x2 x4 x5 = 0)
    (horth_13_24 : planeDot x1 x3 x2 x4 = 0)
    (horth_13_45 : planeDot x1 x3 x4 x5 = 0)
    (horth_23_45 : planeDot x2 x3 x4 x5 = 0) : False := by
  have hd12 : 0 < dist x1 x2 ^ 2 := sq_pos_of_pos (dist_pos.mpr h12)
  have hd13 : 0 < dist x1 x3 ^ 2 := sq_pos_of_pos (dist_pos.mpr h13)
  have hd23 : 0 < dist x2 x3 ^ 2 := sq_pos_of_pos (dist_pos.mpr h23)
  have hd45 : 0 < dist x4 x5 ^ 2 := sq_pos_of_pos (dist_pos.mpr h45)
  rw [plane_dist_sq] at hd12 hd13 hd23 hd45
  dsimp [planeDot] at horth_12_34 horth_12_45 horth_13_24 horth_13_45 horth_23_45
  have hdet1 :
      ((x1 0 - x2 0) ^ 2 + (x1 1 - x2 1) ^ 2) *
        ((x3 0 - x4 0) * (x4 1 - x5 1) - (x3 1 - x4 1) * (x4 0 - x5 0)) =
      ((x1 0 - x2 0) * (x3 0 - x4 0) + (x1 1 - x2 1) * (x3 1 - x4 1)) *
        ((x1 0 - x2 0) * (x4 1 - x5 1) - (x1 1 - x2 1) * (x4 0 - x5 0)) -
      ((x1 0 - x2 0) * (x4 0 - x5 0) + (x1 1 - x2 1) * (x4 1 - x5 1)) *
        ((x1 0 - x2 0) * (x3 1 - x4 1) - (x1 1 - x2 1) * (x3 0 - x4 0)) := by
    ring
  rw [horth_12_34, horth_12_45, zero_mul, zero_mul, sub_self] at hdet1
  have hcol_345 : (x3 0 - x4 0) * (x4 1 - x5 1) - (x3 1 - x4 1) * (x4 0 - x5 0) = 0 :=
    (mul_eq_zero.mp hdet1).resolve_left (ne_of_gt hd12)
  have hdet2 :
      ((x1 0 - x3 0) ^ 2 + (x1 1 - x3 1) ^ 2) *
        ((x2 0 - x4 0) * (x4 1 - x5 1) - (x2 1 - x4 1) * (x4 0 - x5 0)) =
      ((x1 0 - x3 0) * (x2 0 - x4 0) + (x1 1 - x3 1) * (x2 1 - x4 1)) *
        ((x1 0 - x3 0) * (x4 1 - x5 1) - (x1 1 - x3 1) * (x4 0 - x5 0)) -
      ((x1 0 - x3 0) * (x4 0 - x5 0) + (x1 1 - x3 1) * (x4 1 - x5 1)) *
        ((x1 0 - x3 0) * (x2 1 - x4 1) - (x1 1 - x3 1) * (x2 0 - x4 0)) := by
    ring
  rw [horth_13_24, horth_13_45, zero_mul, zero_mul, sub_self] at hdet2
  have hcol_245 : (x2 0 - x4 0) * (x4 1 - x5 1) - (x2 1 - x4 1) * (x4 0 - x5 0) = 0 :=
    (mul_eq_zero.mp hdet2).resolve_left (ne_of_gt hd13)
  have hcol_2345 : (x2 0 - x3 0) * (x4 1 - x5 1) - (x2 1 - x3 1) * (x4 0 - x5 0) = 0 := by
    linear_combination hcol_245 - hcol_345
  have hlagrange :
      ((x2 0 - x3 0) ^ 2 + (x2 1 - x3 1) ^ 2) *
        ((x4 0 - x5 0) ^ 2 + (x4 1 - x5 1) ^ 2) =
      ((x2 0 - x3 0) * (x4 0 - x5 0) + (x2 1 - x3 1) * (x4 1 - x5 1)) ^ 2 +
      ((x2 0 - x3 0) * (x4 1 - x5 1) - (x2 1 - x3 1) * (x4 0 - x5 0)) ^ 2 := by
    ring
  rw [horth_23_45, hcol_2345] at hlagrange
  nlinarith [mul_pos hd23 hd45]

/-- Extraction of 5 pairwise distinct elements from any finite set of cardinality `≥ 5`. -/
theorem exists_five_of_five_le_card {α : Type*} [DecidableEq α]
    (B : Finset α) (hB : 5 ≤ B.card) :
    ∃ x1 ∈ B, ∃ x2 ∈ B, ∃ x3 ∈ B, ∃ x4 ∈ B, ∃ x5 ∈ B,
      x1 ≠ x2 ∧ x1 ≠ x3 ∧ x1 ≠ x4 ∧ x1 ≠ x5 ∧
      x2 ≠ x3 ∧ x2 ≠ x4 ∧ x2 ≠ x5 ∧
      x3 ≠ x4 ∧ x3 ≠ x5 ∧ x4 ≠ x5 := by
  obtain ⟨x1, hx1⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
  have hB1 : 4 ≤ (B.erase x1).card := by rw [Finset.card_erase_of_mem hx1]; omega
  obtain ⟨x2, hx2_er⟩ := Finset.card_pos.mp (by omega : 0 < (B.erase x1).card)
  obtain ⟨hx21, hx2⟩ := Finset.mem_erase.mp hx2_er
  have hB2 : 3 ≤ ((B.erase x1).erase x2).card := by rw [Finset.card_erase_of_mem hx2_er]; omega
  obtain ⟨x3, hx3_er⟩ := Finset.card_pos.mp (by omega : 0 < ((B.erase x1).erase x2).card)
  obtain ⟨hx32, hx3_er1⟩ := Finset.mem_erase.mp hx3_er
  obtain ⟨hx31, hx3⟩ := Finset.mem_erase.mp hx3_er1
  have hB3 : 2 ≤ (((B.erase x1).erase x2).erase x3).card := by
    rw [Finset.card_erase_of_mem hx3_er]; omega
  obtain ⟨x4, hx4_er⟩ := Finset.card_pos.mp (by omega : 0 < (((B.erase x1).erase x2).erase x3).card)
  obtain ⟨hx43, hx4_er2⟩ := Finset.mem_erase.mp hx4_er
  obtain ⟨hx42, hx4_er1⟩ := Finset.mem_erase.mp hx4_er2
  obtain ⟨hx41, hx4⟩ := Finset.mem_erase.mp hx4_er1
  have hB4 : 1 ≤ ((((B.erase x1).erase x2).erase x3).erase x4).card := by
    rw [Finset.card_erase_of_mem hx4_er]; omega
  obtain ⟨x5, hx5_er⟩ :=
    Finset.card_pos.mp (by omega : 0 < ((((B.erase x1).erase x2).erase x3).erase x4).card)
  obtain ⟨hx54, hx5_er3⟩ := Finset.mem_erase.mp hx5_er
  obtain ⟨hx53, hx5_er2⟩ := Finset.mem_erase.mp hx5_er3
  obtain ⟨hx52, hx5_er1⟩ := Finset.mem_erase.mp hx5_er2
  obtain ⟨hx51, hx5⟩ := Finset.mem_erase.mp hx5_er1
  exact ⟨x1, hx1, x2, hx2, x3, hx3, x4, hx4, x5, hx5,
    hx21.symm, hx31.symm, hx41.symm, hx51.symm,
    hx32.symm, hx42.symm, hx52.symm,
    hx43.symm, hx53.symm, hx54.symm⟩

/-- Among any 5 distinct points `x1, x2, x3, x4, x5 ∈ S`, at least two distinct pairs
`(u, v)` and `(w, z)` yield different double-deletion pair energies
`pairEnergy ((S.erase u).erase v) ≠ pairEnergy ((S.erase w).erase z)`. -/
theorem exists_two_deletion_pairEnergy_ne_of_five_pts
    (S : Finset Plane) (x1 x2 x3 x4 x5 : Plane)
    (hx1 : x1 ∈ S) (hx2 : x2 ∈ S) (hx3 : x3 ∈ S) (hx4 : x4 ∈ S) (hx5 : x5 ∈ S)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h14 : x1 ≠ x4) (h15 : x1 ≠ x5)
    (h23 : x2 ≠ x3) (h24 : x2 ≠ x4) (h25 : x2 ≠ x5)
    (h34 : x3 ≠ x4) (h35 : x3 ≠ x5) (h45 : x4 ≠ x5) :
    ∃ u ∈ ({x1, x2, x3, x4, x5} : Finset Plane),
    ∃ v ∈ ({x1, x2, x3, x4, x5} : Finset Plane),
    ∃ w ∈ ({x1, x2, x3, x4, x5} : Finset Plane),
    ∃ z ∈ ({x1, x2, x3, x4, x5} : Finset Plane),
      u ≠ v ∧ w ≠ z ∧
      pairEnergy ((S.erase u).erase v) ≠ pairEnergy ((S.erase w).erase z) := by
  classical
  by_contra hall
  simp only [not_exists, not_and, not_ne_iff] at hall
  have hm1 : x1 ∈ ({x1, x2, x3, x4, x5} : Finset Plane) := by simp
  have hm2 : x2 ∈ ({x1, x2, x3, x4, x5} : Finset Plane) := by simp
  have hm3 : x3 ∈ ({x1, x2, x3, x4, x5} : Finset Plane) := by simp
  have hm4 : x4 ∈ ({x1, x2, x3, x4, x5} : Finset Plane) := by simp
  have hm5 : x5 ∈ ({x1, x2, x3, x4, x5} : Finset Plane) := by simp
  have heq (u v : Plane)
      (hu : u ∈ ({x1, x2, x3, x4, x5} : Finset Plane))
      (hv : v ∈ ({x1, x2, x3, x4, x5} : Finset Plane)) (huv : u ≠ v) :
      pairEnergy ((S.erase u).erase v) = pairEnergy ((S.erase x1).erase x2) :=
    hall u hu v hv x1 hm1 x2 hm2 huv h12
  have horth_12_34 : planeDot x1 x2 x3 x4 = 0 := by
    have h := alternating_double_deletion_pairEnergy S x1 x2 x4 x3
      hx1 hx2 hx4 hx3 h14 h13 h24 h23
    rw [heq x1 x4 hm1 hm4 h14, heq x2 x3 hm2 hm3 h23,
      heq x1 x3 hm1 hm3 h13, heq x2 x4 hm2 hm4 h24, sub_self] at h
    linarith
  have horth_12_45 : planeDot x1 x2 x4 x5 = 0 := by
    have h := alternating_double_deletion_pairEnergy S x1 x2 x5 x4
      hx1 hx2 hx5 hx4 h15 h14 h25 h24
    rw [heq x1 x5 hm1 hm5 h15, heq x2 x4 hm2 hm4 h24,
      heq x1 x4 hm1 hm4 h14, heq x2 x5 hm2 hm5 h25, sub_self] at h
    linarith
  have horth_13_24 : planeDot x1 x3 x2 x4 = 0 := by
    have h := alternating_double_deletion_pairEnergy S x1 x3 x4 x2
      hx1 hx3 hx4 hx2 h14 h12 h34 h23.symm
    rw [heq x1 x4 hm1 hm4 h14, heq x3 x2 hm3 hm2 h23.symm,
      heq x1 x2 hm1 hm2 h12, heq x3 x4 hm3 hm4 h34, sub_self] at h
    linarith
  have horth_13_45 : planeDot x1 x3 x4 x5 = 0 := by
    have h := alternating_double_deletion_pairEnergy S x1 x3 x5 x4
      hx1 hx3 hx5 hx4 h15 h14 h35 h34
    rw [heq x1 x5 hm1 hm5 h15, heq x3 x4 hm3 hm4 h34,
      heq x1 x4 hm1 hm4 h14, heq x3 x5 hm3 hm5 h35, sub_self] at h
    linarith
  have horth_23_45 : planeDot x2 x3 x4 x5 = 0 := by
    have h := alternating_double_deletion_pairEnergy S x2 x3 x5 x4
      hx2 hx3 hx5 hx4 h25 h24 h35 h34
    rw [heq x2 x5 hm2 hm5 h25, heq x3 x4 hm3 hm4 h34,
      heq x2 x4 hm2 hm4 h24, heq x3 x5 hm3 hm5 h35, sub_self] at h
    linarith
  exact no_five_points_all_disjoint_pairs_orthogonal x1 x2 x3 x4 x5
    h12 h13 h23 h45 horth_12_34 horth_12_45 horth_13_24 horth_13_45 horth_23_45

/-- Double deletions preserving a shared diameter pair `(a, b)` are nonsimilar
whenever their pair energies differ. -/
theorem nonsimilar_double_deletions_of_pairEnergy_ne
    (S : Finset Plane) (a b u v w z : Plane)
    (hab : a ≠ b) (ha : a ∈ S) (hb : b ∈ S)
    (hua : u ≠ a) (hub : u ≠ b) (hva : v ≠ a) (hvb : v ≠ b)
    (hwa : w ≠ a) (hwb : w ≠ b) (hza : z ≠ a) (hzb : z ≠ b)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ dist a b)
    (hne : pairEnergy ((S.erase u).erase v) ≠ pairEnergy ((S.erase w).erase z)) :
    ¬ DilationEquivSimilar ((S.erase u).erase v) ((S.erase w).erase z) := by
  classical
  intro hsim
  obtain ⟨f, hf⟩ := (similar_iff_image _ _).mp hsim
  have ha_uv : a ∈ (S.erase u).erase v :=
    mem_erase.mpr ⟨hva.symm, mem_erase.mpr ⟨hua.symm, ha⟩⟩
  have hb_uv : b ∈ (S.erase u).erase v :=
    mem_erase.mpr ⟨hvb.symm, mem_erase.mpr ⟨hub.symm, hb⟩⟩
  have ha_wz : a ∈ (S.erase w).erase z :=
    mem_erase.mpr ⟨hza.symm, mem_erase.mpr ⟨hwa.symm, ha⟩⟩
  have hb_wz : b ∈ (S.erase w).erase z :=
    mem_erase.mpr ⟨hzb.symm, mem_erase.mpr ⟨hwb.symm, hb⟩⟩
  have hsub_uv : (S.erase u).erase v ⊆ S :=
    (erase_subset _ _).trans (erase_subset _ _)
  have hsub_wz : (S.erase w).erase z ⊆ S :=
    (erase_subset _ _).trans (erase_subset _ _)
  have he := pairEnergy_eq_of_shared_diameter
    ((S.erase u).erase v) ((S.erase w).erase z) f hf a b hab
    ha_uv hb_uv ha_wz hb_wz
    (fun x hx y hy => hdiam x (hsub_uv hx) y (hsub_uv hy))
    (fun x hx y hy => hdiam x (hsub_wz hx) y (hsub_wz hy))
  exact hne he

/-- Cardinality of `(S.erase u).erase v` for distinct `u, v ∈ S`. -/
theorem card_erase_erase_of_mem {α : Type*} [DecidableEq α]
    (S : Finset α) (u v : α) (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) :
    ((S.erase u).erase v).card = S.card - 2 := by
  have hv_er : v ∈ S.erase u := mem_erase.mpr ⟨huv.symm, hv⟩
  rw [card_erase_of_mem hv_er, card_erase_of_mem hu]
  omega

/-- Universal 7-point two-deletion nonsimilarity theorem (`TWO-DELETION.md`):
every planar point set `S` with `7 ≤ S.card` contains two nonsimilar `(S.card - 2)`-point
subsets `(S.erase u).erase v` and `(S.erase w).erase z` (with reflections allowed in similarity). -/
theorem two_point_deletion_nonsimilar_of_seven_le
    (S : Finset Plane) (hS : 7 ≤ S.card) :
    ∃ u ∈ S, ∃ v ∈ S, ∃ w ∈ S, ∃ z ∈ S,
      u ≠ v ∧ w ≠ z ∧
      ((S.erase u).erase v).card = S.card - 2 ∧
      ((S.erase w).erase z).card = S.card - 2 ∧
      ¬ DilationEquivSimilar ((S.erase u).erase v) ((S.erase w).erase z) := by
  classical
  obtain ⟨a, ha, b, hb, hab, hdiam⟩ := exists_diameter_pair S (by omega)
  let B := S \ {a, b}
  have hmem (x : Plane) : x ∈ B ↔ x ∈ S ∧ x ≠ a ∧ x ≠ b := by
    dsimp [B]
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
  have hpair : ({a, b} : Finset Plane) ⊆ S := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact ha
    · exact (mem_singleton.mp hx) ▸ hb
  have hB_card : 5 ≤ B.card := by
    rw [card_sdiff_of_subset hpair, card_pair hab]
    omega
  obtain ⟨x1, hx1B, x2, hx2B, x3, hx3B, x4, hx4B, x5, hx5B,
    h12, h13, h14, h15, h23, h24, h25, h34, h35, h45⟩ :=
    exists_five_of_five_le_card B hB_card
  have hsub5 : ({x1, x2, x3, x4, x5} : Finset Plane) ⊆ B := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hx1B
    · rcases mem_insert.mp hx with rfl | hx
      · exact hx2B
      · rcases mem_insert.mp hx with rfl | hx
        · exact hx3B
        · rcases mem_insert.mp hx with rfl | hx
          · exact hx4B
          · exact (mem_singleton.mp hx) ▸ hx5B
  obtain ⟨u, hu5, v, hv5, w, hw5, z, hz5, huv, hwz, hne⟩ :=
    exists_two_deletion_pairEnergy_ne_of_five_pts S x1 x2 x3 x4 x5
      ((hmem x1).mp hx1B).1 ((hmem x2).mp hx2B).1 ((hmem x3).mp hx3B).1
      ((hmem x4).mp hx4B).1 ((hmem x5).mp hx5B).1
      h12 h13 h14 h15 h23 h24 h25 h34 h35 h45
  obtain ⟨huS, hua, hub⟩ := (hmem u).mp (hsub5 hu5)
  obtain ⟨hvS, hva, hvb⟩ := (hmem v).mp (hsub5 hv5)
  obtain ⟨hwS, hwa, hwb⟩ := (hmem w).mp (hsub5 hw5)
  obtain ⟨hzS, hza, hzb⟩ := (hmem z).mp (hsub5 hz5)
  exact ⟨u, huS, v, hvS, w, hwS, z, hzS, huv, hwz,
    card_erase_erase_of_mem S u v huS hvS huv,
    card_erase_erase_of_mem S w z hwS hzS hwz,
    nonsimilar_double_deletions_of_pairEnergy_ne S a b u v w z hab ha hb
      hua hub hva hvb hwa hwb hza hzb hdiam hne⟩

/-- Unconditional two-step plateau nonuniqueness theorem (`TWO-DELETION.md`):
for EVERY `n ≥ 5` (with NO distance-count assumption), if
`minimalDistinctDistances n = minimalDistinctDistances (n + 2)`, then
`¬ UniqueMinimizer n`. -/
theorem two_step_plateau_not_unique
    (n : ℕ) (hn : 5 ≤ n)
    (hplateau : minimalDistinctDistances n = minimalDistinctDistances (n + 2)) :
    ¬ UniqueMinimizer n := by
  classical
  intro huniq
  obtain ⟨S, hSopt⟩ := exists_optimal (n + 2)
  have hS_card : 7 ≤ S.card := by rw [hSopt.1]; omega
  obtain ⟨u, huS, v, hvS, w, hwS, z, hzS, huv, hwz, hcard_uv, hcard_wz, hnonsim⟩ :=
    two_point_deletion_nonsimilar_of_seven_le S hS_card
  have hsub_uv : (S.erase u).erase v ⊆ S :=
    (erase_subset _ _).trans (erase_subset _ _)
  have hsub_wz : (S.erase w).erase z ⊆ S :=
    (erase_subset _ _).trans (erase_subset _ _)
  have hopt_uv : IsOptimal ((S.erase u).erase v) n :=
    MinimumMonotone91.plateau_subset_optimal ((S.erase u).erase v) S n (n + 2)
      hSopt hsub_uv (by rw [hcard_uv, hSopt.1]; omega) hplateau
  have hopt_wz : IsOptimal ((S.erase w).erase z) n :=
    MinimumMonotone91.plateau_subset_optimal ((S.erase w).erase z) S n (n + 2)
      hSopt hsub_wz (by rw [hcard_wz, hSopt.1]; omega) hplateau
  exact hnonsim (huniq _ _ hopt_uv hopt_wz)

/-- Unconditional two-step strict-rise implication (`TWO-DELETION.md`):
for every `n ≥ 5`, `UniqueMinimizer n → minimalDistinctDistances n < minimalDistinctDistances (n + 2)`. -/
theorem uniqueMinimizer_imp_two_step_strict_rise
    (n : ℕ) (hn : 5 ≤ n) (huniq : UniqueMinimizer n) :
    minimalDistinctDistances n < minimalDistinctDistances (n + 2) := by
  have hle : minimalDistinctDistances n ≤ minimalDistinctDistances (n + 2) :=
    MinimumMonotone91.minimum_monotone (by omega)
  have hne : minimalDistinctDistances n ≠ minimalDistinctDistances (n + 2) :=
    fun heq => two_step_plateau_not_unique n hn heq huniq
  omega

end Erdos91.TwoPointDeletionAndTwoStepPlateau
namespace Erdos91.LevelSetExceptionBoundsAndLongPlateaus
open Finset Minimizer91 PlateauDefinitions91

/-- Exact two-step telescoping upper bound `d M + d (M + 1)` on `range M`. -/
theorem card_le_add_two_step (d : ℕ → ℕ) (hd : Monotone d) (E : Finset ℕ) (M : ℕ)
    (hE : E ⊆ range M) (hstep : ∀ n ∈ E, d n < d (n + 2)) :
    E.card ≤ d M + d (M + 1) := by
  have h1 : E.card ≤ ∑ n ∈ E, (d (n + 2) - d n) := by
    calc
      E.card = ∑ _n ∈ E, 1 := by simp
      _ ≤ ∑ n ∈ E, (d (n + 2) - d n) := by
        apply sum_le_sum
        intro n hn
        have h := hstep n hn
        omega
  have h2 : (∑ n ∈ E, (d (n + 2) - d n)) ≤ ∑ n ∈ range M, (d (n + 2) - d n) :=
    sum_le_sum_of_subset hE
  have ht := ExceptionCount91.telescope d hd M
  omega
end Erdos91.LevelSetExceptionBoundsAndLongPlateaus

namespace Erdos91.UnconditionalEightNineDichotomy
open Finset Minimizer91 PlateauDefinitions91
open Erdos91.TwoDistanceCapAndSixNonunique (minimalDistinctDistances_seven)
open Erdos91.EightAndNineNonunique (triangularNine regularNonagon card_triangularNine card_regularNonagon distinctDistances_triangularNine_le_four distinctDistances_regularNonagon_le_four minimalDistinctDistances_eight_le_four minimalDistinctDistances_nine_le_four not_similar_regularNonagon_triangularNine not_uniqueMinimizer_eight_and_nine_of_four_le)

/-- Unconditional lower bound `3 ≤ d(8)` from `d(7) = 3` and monotonicity. -/
theorem three_le_minimalDistinctDistances_eight :
    3 ≤ minimalDistinctDistances 8 := by
  rw [← minimalDistinctDistances_seven]
  exact MinimumMonotone91.minimum_monotone (by omega)

/-- Unconditional lower bound `3 ≤ d(9)` from `d(7) = 3` and monotonicity. -/
theorem three_le_minimalDistinctDistances_nine :
    3 ≤ minimalDistinctDistances 9 := by
  rw [← minimalDistinctDistances_seven]
  exact MinimumMonotone91.minimum_monotone (by omega)

/-- Unconditional two-value localization `d(9) ∈ {3, 4}`. -/
theorem minimalDistinctDistances_nine_eq_three_or_four :
    minimalDistinctDistances 9 = 3 ∨ minimalDistinctDistances 9 = 4 := by
  have hlo := three_le_minimalDistinctDistances_nine
  have hhi := minimalDistinctDistances_nine_le_four
  omega

/-- Weakened hypothesis for `n = 9`: `4 ≤ d(9)` alone (without assuming `4 ≤ d(8)`)
certifies global optimality of both `triangularNine` and `regularNonagon` and proves
`¬ UniqueMinimizer 9`. -/
theorem not_uniqueMinimizer_nine_of_four_le_nine
    (h9 : 4 ≤ minimalDistinctDistances 9) :
    minimalDistinctDistances 9 = 4 ∧
      IsOptimal triangularNine 9 ∧
      IsOptimal regularNonagon 9 ∧
      ¬ UniqueMinimizer 9 := by
  have hm9 : minimalDistinctDistances 9 = 4 :=
    le_antisymm minimalDistinctDistances_nine_le_four h9
  have hTri9Opt : IsOptimal triangularNine 9 := by
    refine ⟨card_triangularNine, le_antisymm ?_
      (minimal_le triangularNine 9 card_triangularNine)⟩
    rw [hm9]
    exact distinctDistances_triangularNine_le_four
  have hNon9Opt : IsOptimal regularNonagon 9 := by
    refine ⟨card_regularNonagon, le_antisymm ?_
      (minimal_le regularNonagon 9 card_regularNonagon)⟩
    rw [hm9]
    exact distinctDistances_regularNonagon_le_four
  refine ⟨hm9, hTri9Opt, hNon9Opt, ?_⟩
  intro huniq9
  exact not_similar_regularNonagon_triangularNine
    (huniq9 regularNonagon triangularNine hNon9Opt hTri9Opt)

/-- Complementary plateau case `d(9) = 3`: if `d(9) = 3`, then `3 = d(7) ≤ d(8) ≤ d(9) = 3`
forces the plateau `d(8) = d(9) = 3` with `2 * d(8) = 6 < 7 = 8 - 1`, which by
`PlateauNonunique91.low_distance_plateau_not_unique` proves `¬ UniqueMinimizer 8`! -/
theorem not_uniqueMinimizer_eight_of_nine_eq_three
    (h9 : minimalDistinctDistances 9 = 3) :
    minimalDistinctDistances 8 = 3 ∧ ¬ UniqueMinimizer 8 := by
  have hlo8 := three_le_minimalDistinctDistances_eight
  have h89 : minimalDistinctDistances 8 ≤ minimalDistinctDistances 9 :=
    MinimumMonotone91.minimum_monotone (by omega)
  have hm8 : minimalDistinctDistances 8 = 3 := by omega
  have hplat : minimalDistinctDistances 8 = minimalDistinctDistances 9 := by omega
  have hlow : 2 * minimalDistinctDistances 8 < 8 - 1 := by omega
  exact ⟨hm8, PlateauNonunique91.low_distance_plateau_not_unique 8 (by omega) hplat hlow⟩

/-- **Unconditional `n = 8, 9` nonuniqueness theorem:** with ZERO unproved premises,
at least one of `n = 8` or `n = 9` has nonunique planar distinct-distance minimizers
(`¬ UniqueMinimizer 8 ∨ ¬ UniqueMinimizer 9`).
Specifically, `3 ≤ d(9) ≤ 4`; if `d(9) = 3`, then `d(8) = d(9) = 3` and `2 * d(8) = 6 < 7`
forces `¬ UniqueMinimizer 8`, whereas if `d(9) = 4`, `triangularNine` and `regularNonagon`
force `¬ UniqueMinimizer 9`. -/
theorem not_uniqueMinimizer_eight_or_nine :
    ¬ UniqueMinimizer 8 ∨ ¬ UniqueMinimizer 9 := by
  rcases minimalDistinctDistances_nine_eq_three_or_four with h3 | h4
  · exact Or.inl (not_uniqueMinimizer_eight_of_nine_eq_three h3).2
  · exact Or.inr (not_uniqueMinimizer_nine_of_four_le_nine (by omega)).2.2.2

end Erdos91.UnconditionalEightNineDichotomy
namespace Erdos91.EquivalenceTwoMinimizersAndGeneralKFlatRises
open Finset Filter Minimizer91 PlateauDefinitions91
open Erdos91.ThreeUniqueMinimizer (similar_refl similar_symm)
open Erdos91.GeneralMultiplicityAndDensityOne (HasAtLeastKNonsimilarMinimizers)
open Erdos91.FourNonuniqueAndDoubleEquilateral (not_uniqueMinimizer_four)
open Erdos91.TwoDistanceCapAndSixNonunique (not_uniqueMinimizer_six)
open Erdos91.SevenNonuniqueHeptagonAndWheel (not_uniqueMinimizer_seven)
open Erdos91.AsymptoticDensityOneAndGlobalBounds (uniqueMinimizerSet badMultiplicitySet goodMultiplicitySet good_add_badMultiplicitySet_card)
open Erdos91.TwoPointDeletionAndTwoStepPlateau (two_step_plateau_not_unique)
open Erdos91.UnconditionalEightNineDichotomy (not_uniqueMinimizer_eight_or_nine)
/-- Exact equivalence between `HasAtLeastKNonsimilarMinimizers 2 n` and
`¬ UniqueMinimizer n` for every cardinality `n : ℕ`. -/
theorem hasAtLeastTwoMinimizers_iff_not_uniqueMinimizer (n : ℕ) :
    HasAtLeastKNonsimilarMinimizers 2 n ↔ ¬ UniqueMinimizer n := by
  classical
  unfold HasAtLeastKNonsimilarMinimizers UniqueMinimizer
  constructor
  · rintro ⟨F, hcard, hopt, hnon⟩ hall
    obtain ⟨A, B, hAB, rfl⟩ := Finset.card_eq_two.mp hcard
    have hA : A ∈ ({A, B} : Finset (Finset Plane)) := by simp
    have hB : B ∈ ({A, B} : Finset (Finset Plane)) := by simp
    exact hnon A hA B hB hAB (hall A B (hopt A hA) (hopt B hB))
  · intro hnot
    simp only [not_forall] at hnot
    obtain ⟨A, B, hA, hB, hnsim⟩ := hnot
    have hAB : A ≠ B := fun heq => hnsim (heq ▸ similar_refl A)
    refine ⟨{A, B}, Finset.card_pair hAB, ?_, ?_⟩
    · intro X hX
      simp only [Finset.mem_insert, Finset.mem_singleton] at hX
      rcases hX with rfl | rfl
      · exact hA
      · exact hB
    · intro X hX Y hY hXY hsim
      simp only [Finset.mem_insert, Finset.mem_singleton] at hX hY
      rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
      · exact hXY rfl
      · exact hnsim hsim
      · exact hnsim (similar_symm hsim)
      · exact hXY rfl

theorem hasAtLeastTwoMinimizers_four_six_seven :
    HasAtLeastKNonsimilarMinimizers 2 4 ∧
      HasAtLeastKNonsimilarMinimizers 2 6 ∧
      HasAtLeastKNonsimilarMinimizers 2 7 ∧
      (HasAtLeastKNonsimilarMinimizers 2 8 ∨ HasAtLeastKNonsimilarMinimizers 2 9) := by
  refine ⟨(hasAtLeastTwoMinimizers_iff_not_uniqueMinimizer 4).mpr not_uniqueMinimizer_four,
    (hasAtLeastTwoMinimizers_iff_not_uniqueMinimizer 6).mpr not_uniqueMinimizer_six,
    (hasAtLeastTwoMinimizers_iff_not_uniqueMinimizer 7).mpr not_uniqueMinimizer_seven, ?_⟩
  rcases not_uniqueMinimizer_eight_or_nine with h8 | h9
  · exact Or.inl ((hasAtLeastTwoMinimizers_iff_not_uniqueMinimizer 8).mpr h8)
  · exact Or.inr ((hasAtLeastTwoMinimizers_iff_not_uniqueMinimizer 9).mpr h9)

end Erdos91.EquivalenceTwoMinimizersAndGeneralKFlatRises

namespace Erdos91.ExactGridEnergyAndDeletionFamilies
open Finset
theorem exists_rep_subset_card_eq_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S₀ : Finset α) (g : α → β) :
    ∃ U₀ : Finset α,
      U₀ ⊆ S₀ ∧
      U₀.card = (S₀.image g).card ∧
      ∀ p ∈ U₀, ∀ q ∈ U₀, p ≠ q → g p ≠ g q := by
  classical
  obtain ⟨U₀, hU₀, hinj, himg⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn
    (S₀ : Set α) (S₀.image g) (by
      intro y hy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨p, hp, rfl⟩)
  refine ⟨U₀, hU₀, ?_, ?_⟩
  · rw [← himg, Finset.card_image_of_injOn hinj]
  · intro p hp q hq hpq hgpq
    exact hpq (hinj hp hq hgpq)

end Erdos91.ExactGridEnergyAndDeletionFamilies

namespace Erdos91.Grid20Exact179DistancesAndFullCertificate
def isStrictlyIncreasing : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a < b) && isStrictlyIncreasing (b :: rest)

theorem pairwise_lt_of_isStrictlyIncreasing :
    ∀ L : List ℕ, isStrictlyIncreasing L = true → L.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    simp only [isStrictlyIncreasing, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_lt_of_isStrictlyIncreasing (b :: rest) h.2
    refine List.Pairwise.cons (fun x hx => ?_) ih
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact h.1
    · exact lt_trans h.1 (List.rel_of_pairwise_cons ih hmem)

end Erdos91.Grid20Exact179DistancesAndFullCertificate

namespace Erdos91.UnconditionalKMultiplicityAndCubicTwoDeletion
open Finset Minimizer91
open SimilarityEnergy91 (pairEnergy)
/-- Set of distinct double-deletion pair energies on `B ⊆ S`. -/
noncomputable def doubleDeletionEnergySet (S B : Finset Plane) : Finset ℝ := by
  classical
  exact B.offDiag.image (fun uv => pairEnergy ((S.erase uv.1).erase uv.2))

end Erdos91.UnconditionalKMultiplicityAndCubicTwoDeletion

namespace Erdos91.QuadraticTwoDeletionMultiplicity
open Finset Minimizer91 PlateauDefinitions91
open SimilarityEnergy91 (pairEnergy)
open EnergyLevels91 (energy centroid radius_energy_card)
open DeletionEnergy91 (deletion_identity)
open CircleLevels91 (distance_images_product)
open Erdos91.GeneralMultiplicityAndDensityOne (HasAtLeastKNonsimilarMinimizers)
open Erdos91.AsymptoticDensityOneAndGlobalBounds (badMultiplicitySet)
open Erdos91.TwoPointDeletionAndTwoStepPlateau (nonsimilar_double_deletions_of_pairEnergy_ne card_erase_erase_of_mem)
open Erdos91.LevelSetExceptionBoundsAndLongPlateaus (card_le_add_two_step)
open Erdos91.ExactGridEnergyAndDeletionFamilies (exists_rep_subset_card_eq_image)
open Erdos91.UnconditionalKMultiplicityAndCubicTwoDeletion (doubleDeletionEnergySet)

/-- Distinct single-point deletions `S.erase x1` and `S.erase x2` (`2 ≤ S.card`, `x1 ≠ x2`)
have distinct centroids `centroid (S.erase x1) ≠ centroid (S.erase x2)`. -/
theorem centroid_erase_ne_centroid_erase
    (S : Finset Plane) (hS : 2 ≤ S.card)
    (x1 x2 : Plane) (hx1 : x1 ∈ S) (hx2 : x2 ∈ S) (h12 : x1 ≠ x2) :
    centroid (S.erase x1) ≠ centroid (S.erase x2) := by
  classical
  intro heq
  unfold EnergyLevels91.centroid at heq
  rw [Finset.card_erase_of_mem hx1, Finset.card_erase_of_mem hx2] at heq
  have hne0 : (((S.card - 1 : ℕ) : ℝ))⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact_mod_cast (by omega : S.card - 1 ≠ 0)
  have hsum : (∑ x ∈ S.erase x1, x) = ∑ x ∈ S.erase x2, x :=
    (smul_right_inj hne0).mp heq
  rw [Finset.sum_erase_eq_sub hx1, Finset.sum_erase_eq_sub hx2] at hsum
  exact h12 (sub_right_inj.mp hsum)

/-- For any `x ∈ B` (`B ⊆ S`) and `B' ⊆ B.erase x`, the number of distinct row
energies `energy (S.erase x) r` (`r ∈ B'`) is bounded by `(doubleDeletionEnergySet S B).card`. -/
theorem card_image_energy_erase_le_doubleDeletionEnergySet
    (S B B' : Finset Plane) (x : Plane) (hxB : x ∈ B) (hBS : B ⊆ S)
    (hB' : B' ⊆ B.erase x) :
    (B'.image (energy (S.erase x))).card ≤ (doubleDeletionEnergySet S B).card := by
  classical
  let g : ℝ → ℝ := fun e => pairEnergy (S.erase x) - 2 * e
  have hg_inj : Function.Injective g := by
    intro a b h
    dsimp [g] at h
    linarith
  have hcard : (B'.image (energy (S.erase x))).card =
      ((B'.image (energy (S.erase x))).image g).card :=
    (Finset.card_image_of_injective _ hg_inj).symm
  rw [hcard, Finset.image_image]
  unfold doubleDeletionEnergySet
  apply Finset.card_le_card
  intro y hy
  obtain ⟨r, hrB', rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨hrx, hrB⟩ := Finset.mem_erase.mp (hB' hrB')
  have hrS : r ∈ S.erase x := Finset.mem_erase.mpr ⟨hrx, hBS hrB⟩
  dsimp [g]
  rw [← deletion_identity (S.erase x) r hrS]
  exact Finset.mem_image.mpr ⟨(x, r), Finset.mem_offDiag.mpr ⟨hxB, hrB, hrx.symm⟩, rfl⟩

/-- **Universal quadratic double-deletion energy bound:**
for any `S B : Finset Plane` with `B ⊆ S` and `2 ≤ B.card` (with ZERO distance-count
assumption), `B.card - 2 ≤ 2 * (doubleDeletionEnergySet S B).card ^ 2`. -/
theorem card_sub_two_le_two_mul_sq_doubleDeletionEnergySet
    (S B : Finset Plane) (hBS : B ⊆ S) (hB : 2 ≤ B.card) :
    B.card - 2 ≤ 2 * (doubleDeletionEnergySet S B).card ^ 2 := by
  classical
  have hS2 : 2 ≤ S.card := hB.trans (Finset.card_le_card hBS)
  obtain ⟨x1, hx1, x2, hx2, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < B.card)
  let B' := (B.erase x1).erase x2
  have hB'_card : B'.card = B.card - 2 :=
    card_erase_erase_of_mem B x1 x2 hx1 hx2 h12
  have hcent_ne : centroid (S.erase x1) ≠ centroid (S.erase x2) :=
    centroid_erase_ne_centroid_erase S hS2 x1 x2 (hBS hx1) (hBS hx2) h12
  have hprod := distance_images_product B' (centroid (S.erase x1)) (centroid (S.erase x2)) hcent_ne
  have hS1_ne : (S.erase x1).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem (hBS hx1)]
    omega
  have hS2_ne : (S.erase x2).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem (hBS hx2)]
    omega
  rw [radius_energy_card (S.erase x1) B' hS1_ne,
    radius_energy_card (S.erase x2) B' hS2_ne] at hprod
  have hsub1 : B' ⊆ B.erase x1 := Finset.erase_subset _ _
  have hsub2 : B' ⊆ B.erase x2 := by
    intro r hr
    obtain ⟨hr2, hr1⟩ := Finset.mem_erase.mp hr
    exact Finset.mem_erase.mpr ⟨hr2, Finset.mem_of_mem_erase hr1⟩
  have hle1 := card_image_energy_erase_le_doubleDeletionEnergySet S B B' x1 hx1 hBS hsub1
  have hle2 := card_image_energy_erase_le_doubleDeletionEnergySet S B B' x2 hx2 hBS hsub2
  calc
    B.card - 2 = B'.card := hB'_card.symm
    _ ≤ 2 * (B'.image (energy (S.erase x2))).card *
          (B'.image (energy (S.erase x1))).card := hprod
    _ ≤ 2 * (doubleDeletionEnergySet S B).card *
          (doubleDeletionEnergySet S B).card :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hle2) hle1
    _ = 2 * (doubleDeletionEnergySet S B).card ^ 2 := by ring

/-- **Universal quadratic two-deletion multiplicity theorem:**
every finite planar point set `S` with `4 ≤ S.card` (with ZERO distance-count
assumption) admits a family `F` of `(S.card - 2)`-point double deletions
`(S.erase u).erase v`, pairwise nonsimilar under `DilationEquivSimilar`, such
that `S.card - 4 ≤ 2 * F.card ^ 2`. -/
theorem general_two_deletion_quadratic_multiplicity
    (S : Finset Plane) (hS : 4 ≤ S.card) :
    ∃ F : Finset (Finset Plane),
      (∀ A ∈ F, ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧
        A = (S.erase u).erase v ∧ A.card = S.card - 2) ∧
      (∀ A ∈ F, ∀ C ∈ F, A ≠ C → ¬ DilationEquivSimilar A C) ∧
      S.card - 4 ≤ 2 * F.card ^ 2 := by
  classical
  obtain ⟨a, ha, b, hb, hab, hdiam⟩ := exists_diameter_pair S (by omega)
  let B := S \ {a, b}
  have hBS : B ⊆ S := sdiff_subset
  have hmem (x : Plane) : x ∈ B ↔ x ∈ S ∧ x ≠ a ∧ x ≠ b := by
    simp only [B, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
  have hpair : ({a, b} : Finset Plane) ⊆ S := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact ha
    · exact (mem_singleton.mp hx) ▸ hb
  have hB_card : B.card = S.card - 2 := by
    rw [card_sdiff_of_subset hpair, card_pair hab]
  have hB2 : 2 ≤ B.card := by omega
  let g : Plane × Plane → ℝ := fun uv => pairEnergy ((S.erase uv.1).erase uv.2)
  obtain ⟨U₀, hU₀_sub, hU₀_card, hU₀_ne⟩ :=
    exists_rep_subset_card_eq_image B.offDiag g
  let delMap : Plane × Plane → Finset Plane := fun uv => (S.erase uv.1).erase uv.2
  have hdel_inj : Set.InjOn delMap (U₀ : Set (Plane × Plane)) := by
    intro p hp q hq heq
    by_contra hpq
    exact hU₀_ne p hp q hq hpq (congrArg pairEnergy heq)
  let F := U₀.image delMap
  have hF_card : F.card = (doubleDeletionEnergySet S B).card := by
    dsimp [F, doubleDeletionEnergySet]
    rw [Finset.card_image_of_injOn hdel_inj, hU₀_card]
  have hquad := card_sub_two_le_two_mul_sq_doubleDeletionEnergySet S B hBS hB2
  rw [hB_card, ← hF_card] at hquad
  refine ⟨F, ?_, ?_, by omega⟩
  · intro A hA
    obtain ⟨⟨u, v⟩, huvU, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨huB, hvB, huv⟩ := Finset.mem_offDiag.mp (hU₀_sub huvU)
    have huS := ((hmem u).mp huB).1
    have hvS := ((hmem v).mp hvB).1
    exact ⟨u, huS, v, hvS, huv, rfl, card_erase_erase_of_mem S u v huS hvS huv⟩
  · intro A hA C hC hAC
    obtain ⟨⟨u, v⟩, huvU, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨⟨w, z⟩, hwzU, rfl⟩ := Finset.mem_image.mp hC
    have hpq : (u, v) ≠ (w, z) := fun heq => hAC (congrArg delMap heq)
    obtain ⟨huB, hvB, _⟩ := Finset.mem_offDiag.mp (hU₀_sub huvU)
    obtain ⟨hwB, hzB, _⟩ := Finset.mem_offDiag.mp (hU₀_sub hwzU)
    obtain ⟨_, hua, hub⟩ := (hmem u).mp huB
    obtain ⟨_, hva, hvb⟩ := (hmem v).mp hvB
    obtain ⟨_, hwa, hwb⟩ := (hmem w).mp hwB
    obtain ⟨_, hza, hzb⟩ := (hmem z).mp hzB
    exact nonsimilar_double_deletions_of_pairEnergy_ne S a b u v w z hab ha hb
      hua hub hva hvb hwa hwb hza hzb hdiam (hU₀_ne (u, v) huvU (w, z) hwzU hpq)

theorem mul_sq_lt_imp_le {a b : ℕ} (h : 2 * b ^ 2 < 2 * a ^ 2) : b + 1 ≤ a := by
  by_contra hnot
  have hle : a ≤ b := by omega
  have hpow : a ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hle 2
  omega

/-- **Sharpened quadratic two-step plateau `K`-multiplicity theorem:**
for EVERY `K : ℕ` and EVERY `n ≥ 2 * (K - 1)^2 + 3` (improving `(K - 1)^3 + 4`
to quadratic `2 * (K - 1)^2 + 3`, with ZERO distance-count assumption!),
`minimalDistinctDistances n = minimalDistinctDistances (n + 2) → HasAtLeastKNonsimilarMinimizers K n`. -/
theorem two_step_plateau_has_K_minimizers_quadratic
    (K n : ℕ) (hn : 2 * (K - 1) ^ 2 + 3 ≤ n)
    (hplateau : minimalDistinctDistances n = minimalDistinctDistances (n + 2)) :
    HasAtLeastKNonsimilarMinimizers K n := by
  classical
  obtain ⟨S, hSopt⟩ := exists_optimal (n + 2)
  have hS4 : 4 ≤ S.card := by rw [hSopt.1]; omega
  obtain ⟨F', hF'_mem, hF'_non, hquad⟩ := general_two_deletion_quadratic_multiplicity S hS4
  rw [hSopt.1] at hquad
  have hKF' : K ≤ F'.card := by
    by_cases hK0 : K = 0
    · omega
    · have hlt : 2 * (K - 1) ^ 2 < 2 * F'.card ^ 2 := by omega
      have hle := mul_sq_lt_imp_le hlt
      omega
  obtain ⟨F, hFF', hFcard⟩ := Finset.exists_subset_card_eq hKF'
  refine ⟨F, hFcard, ?_, fun A hA C hC hAC => hF'_non A (hFF' hA) C (hFF' hC) hAC⟩
  intro A hA
  obtain ⟨u, _huS, v, _hvS, _huv, rfl, hAcard⟩ := hF'_mem A (hFF' hA)
  have hsub : (S.erase u).erase v ⊆ S := (erase_subset _ _).trans (erase_subset _ _)
  exact MinimumMonotone91.plateau_subset_optimal ((S.erase u).erase v) S n (n + 2)
    hSopt hsub (by rw [hAcard, hSopt.1]; omega) hplateau

/-- Contrapositive quadratic two-step strict rise for arbitrary `K`:
for every `K : ℕ` and `n ≥ 2 * (K - 1)^2 + 3`,
`¬ HasAtLeastKNonsimilarMinimizers K n → minimalDistinctDistances n < minimalDistinctDistances (n + 2)`. -/
theorem not_has_K_minimizers_imp_two_step_strict_rise_quadratic
    (K n : ℕ) (hn : 2 * (K - 1) ^ 2 + 3 ≤ n)
    (hnot : ¬ HasAtLeastKNonsimilarMinimizers K n) :
    minimalDistinctDistances n < minimalDistinctDistances (n + 2) := by
  have hle : minimalDistinctDistances n ≤ minimalDistinctDistances (n + 2) :=
    MinimumMonotone91.minimum_monotone (by omega)
  have hne : minimalDistinctDistances n ≠ minimalDistinctDistances (n + 2) :=
    fun heq => hnot (two_step_plateau_has_K_minimizers_quadratic K n hn heq)
  omega

/-- **Sharpened unconditional global bound on `badMultiplicitySet K N`:**
for every `K N : ℕ`,
`(badMultiplicitySet K N).card ≤ (2 * (K - 1)^2 + 3) + minimalDistinctDistances (N + 1) + minimalDistinctDistances (N + 2)`. -/
theorem badMultiplicitySet_card_le_quadratic_unconditional (K N : ℕ) :
    (badMultiplicitySet K N).card ≤
      (2 * (K - 1) ^ 2 + 3) + minimalDistinctDistances (N + 1) + minimalDistinctDistances (N + 2) := by
  classical
  let L := 2 * (K - 1) ^ 2 + 3
  let B := badMultiplicitySet K N
  let E0 := B.filter (fun n => n < L)
  let E1 := B.filter (fun n => ¬ n < L)
  have hpart : E0.card + E1.card = B.card :=
    card_filter_add_card_filter_not (s := B) (p := fun n => n < L)
  have hE0_sub : E0 ⊆ range L := by
    intro n hn
    exact mem_range.mpr (mem_filter.mp hn).2
  have hE0_le : E0.card ≤ L := by
    have h := card_le_card hE0_sub
    simpa only [card_range] using h
  have hE1_sub : E1 ⊆ range (N + 1) :=
    (filter_subset _ _).trans (filter_subset _ _)
  have hE1_step : ∀ n ∈ E1, minimalDistinctDistances n < minimalDistinctDistances (n + 2) := by
    intro n hn
    obtain ⟨hnB, hge⟩ := mem_filter.mp hn
    have hnot : ¬ HasAtLeastKNonsimilarMinimizers K n := (mem_filter.mp hnB).2
    exact not_has_K_minimizers_imp_two_step_strict_rise_quadratic K n (by omega) hnot
  have hE1_le : E1.card ≤ minimalDistinctDistances (N + 1) + minimalDistinctDistances (N + 2) :=
    card_le_add_two_step minimalDistinctDistances
      MinimumMonotone91.minimum_monotone E1 (N + 1) hE1_sub hE1_step
  change B.card ≤ L + minimalDistinctDistances (N + 1) + minimalDistinctDistances (N + 2)
  omega

end Erdos91.QuadraticTwoDeletionMultiplicity
namespace Erdos91.ConcreteMultiplicityBenchmarks322And398
open Finset
open Erdos91.GeneralMultiplicityAndDensityOne (HasAtLeastKNonsimilarMinimizers)
open Erdos91.AsymptoticDensityOneAndGlobalBounds (goodMultiplicitySet)
theorem exists_le_of_goodMultiplicitySet_pos {K N : ℕ}
    (hpos : 0 < (goodMultiplicitySet K N).card) :
    ∃ n ≤ N, HasAtLeastKNonsimilarMinimizers K n := by
  obtain ⟨n, hn⟩ := Finset.card_pos.mp hpos
  obtain ⟨hn_range, hgood⟩ := Finset.mem_filter.mp hn
  have hn_lt : n < N + 1 := Finset.mem_range.mp hn_range
  exact ⟨n, by omega, hgood⟩

end Erdos91.ConcreteMultiplicityBenchmarks322And398

namespace Erdos91.SharpenedTelescopingAndPrefixBounds
open Finset Minimizer91 PlateauDefinitions91
open Erdos91.UnboundedRises (minimal_quadratic_lower_bound)
open Erdos91.FourNonuniqueAndDoubleEquilateral (not_uniqueMinimizer_four)
open Erdos91.GeneralMultiplicityAndDensityOne (HasAtLeastKNonsimilarMinimizers)
open Erdos91.TwoDistanceCapAndSixNonunique (minimalDistinctDistances_six not_uniqueMinimizer_six)
open Erdos91.SevenNonuniqueHeptagonAndWheel (not_uniqueMinimizer_seven)
open Erdos91.AsymptoticDensityOneAndGlobalBounds (uniqueMinimizerSet badMultiplicitySet)
open Erdos91.TwoPointDeletionAndTwoStepPlateau (uniqueMinimizer_imp_two_step_strict_rise)
open Erdos91.UnconditionalEightNineDichotomy (three_le_minimalDistinctDistances_eight three_le_minimalDistinctDistances_nine)
open Erdos91.QuadraticTwoDeletionMultiplicity (not_has_K_minimizers_imp_two_step_strict_rise_quadratic)
/-- Shifted two-step telescoping identity starting at an arbitrary lower bound `L : ℕ`:
`(∑ k ∈ range K, (d (L + k + 2) - d (L + k))) + d L + d (L + 1) = d (L + K) + d (L + K + 1)`. -/
theorem two_step_telescope_shift (d : ℕ → ℕ) (hd : Monotone d) (L K : ℕ) :
    (∑ k ∈ range K, (d (L + k + 2) - d (L + k))) + d L + d (L + 1) =
      d (L + K) + d (L + K + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ]
    norm_num [Nat.add_assoc] at *
    have h := hd (show L + K ≤ L + (K + 2) by omega)
    omega

/-- Two-step telescoping bound on `Ico L M` retaining the boundary terms `d L + d (L + 1)`:
`E.card + d L + d (L + 1) ≤ d M + d (M + 1)`. -/
theorem card_Ico_add_two_step_le (d : ℕ → ℕ) (hd : Monotone d) (E : Finset ℕ) (L M : ℕ)
    (hLM : L ≤ M) (hE : E ⊆ Ico L M) (hstep : ∀ n ∈ E, d n < d (n + 2)) :
    E.card + d L + d (L + 1) ≤ d M + d (M + 1) := by
  classical
  let F := (range (M - L)).image (fun k => L + k)
  have hsub : E ⊆ F := by
    intro n hn
    have h := mem_Ico.mp (hE hn)
    apply mem_image.mpr
    refine ⟨n - L, mem_range.mpr (by omega), by omega⟩
  have hb : E.card ≤ ∑ n ∈ F, (d (n + 2) - d n) := by
    calc
      E.card = ∑ _n ∈ E, 1 := by simp
      _ ≤ ∑ n ∈ E, (d (n + 2) - d n) := by
        apply sum_le_sum
        intro n hn
        have := hstep n hn
        omega
      _ ≤ ∑ n ∈ F, (d (n + 2) - d n) := sum_le_sum_of_subset hsub
  have ht := two_step_telescope_shift d hd L (M - L)
  have hi : ∑ n ∈ F, (d (n + 2) - d n) =
      ∑ k ∈ range (M - L), (d (L + k + 2) - d (L + k)) := by
    unfold F
    rw [sum_image]
    intro a _ b _ heq
    exact Nat.add_left_cancel heq
  rw [hi] at hb
  have heq : L + (M - L) = M := by omega
  rw [heq] at ht
  omega

/-- Because `¬ UniqueMinimizer 4`, `¬ UniqueMinimizer 6`, and `¬ UniqueMinimizer 7`,
at most `5` indices in `[0, 7]` (`{0, 1, 2, 3, 5}`) can satisfy `UniqueMinimizer`. -/
theorem uniqueMinimizer_filter_lt_eight_card_le_five
    (E : Finset ℕ) (huniq : ∀ n ∈ E, UniqueMinimizer n) :
    haveI : DecidablePred (fun n => n < 8) := inferInstance
    (E.filter (fun n => n < 8)).card ≤ 5 := by
  have hsub : E.filter (fun n => n < 8) ⊆ ({0, 1, 2, 3, 5} : Finset ℕ) := by
    intro n hn
    obtain ⟨hnE, hlt⟩ := mem_filter.mp hn
    have hu := huniq n hnE
    have hn4 : n ≠ 4 := fun h => not_uniqueMinimizer_four (h ▸ hu)
    have hn6 : n ≠ 6 := fun h => not_uniqueMinimizer_six (h ▸ hu)
    have hn7 : n ≠ 7 := fun h => not_uniqueMinimizer_seven (h ▸ hu)
    simp only [mem_insert, mem_singleton]
    omega
  have hcard : ({0, 1, 2, 3, 5} : Finset ℕ).card = 5 := by decide
  exact (card_le_card hsub).trans (le_of_eq hcard)

/-- Unconditional lower bound `4 ≤ d(21)` from `21 - 2 = 19 ≤ 2 * d(21)^2`. -/
theorem four_le_minimalDistinctDistances_21 :
    4 ≤ minimalDistinctDistances 21 := by
  have h := minimal_quadratic_lower_bound 21
  nlinarith

/-- For every `n ≥ 8`, if `d(n + 1) ≤ 3`, then `3 ≤ d(8) ≤ d(n) ≤ d(n + 1) ≤ 3`
forces the one-step plateau `d(n) = d(n + 1) = 3` with `2 * d(n) = 6 < n - 1`,
proving `¬ UniqueMinimizer n`. -/
theorem not_uniqueMinimizer_of_eight_le_of_succ_le_three
    (n : ℕ) (hn : 8 ≤ n) (hd : minimalDistinctDistances (n + 1) ≤ 3) :
    ¬ UniqueMinimizer n := by
  have h8 : 3 ≤ minimalDistinctDistances n :=
    three_le_minimalDistinctDistances_eight.trans
      (MinimumMonotone91.minimum_monotone hn)
  have hle : minimalDistinctDistances n ≤ minimalDistinctDistances (n + 1) :=
    MinimumMonotone91.minimum_monotone (by omega)
  have hplat : minimalDistinctDistances n = minimalDistinctDistances (n + 1) := by omega
  exact PlateauNonunique91.low_distance_plateau_not_unique n (by omega) hplat (by omega)

/-- Inductive shift to the first index `L` with `4 ≤ d(L + 1)`, proving
`E1.card + 7 ≤ d(M) + d(M + 1)` on `Ico L M`. -/
theorem card_Ico_uniqueMinimizer_add_seven_le_aux
    (K : ℕ) :
    ∀ L M : ℕ, 8 ≤ L → L + K ≤ M → 4 ≤ minimalDistinctDistances (L + K + 1) →
      ∀ E1 : Finset ℕ, E1 ⊆ Ico L M → (∀ n ∈ E1, UniqueMinimizer n) →
        E1.card + 7 ≤ minimalDistinctDistances M + minimalDistinctDistances (M + 1) := by
  induction K with
  | zero =>
    intro L M hL hLM hd4 E1 hE1 huniq
    have hL8 : 3 ≤ minimalDistinctDistances L :=
      three_le_minimalDistinctDistances_eight.trans
        (MinimumMonotone91.minimum_monotone hL)
    have hstep : ∀ n ∈ E1, minimalDistinctDistances n < minimalDistinctDistances (n + 2) := by
      intro n hn
      have hnL : L ≤ n := (mem_Ico.mp (hE1 hn)).1
      exact uniqueMinimizer_imp_two_step_strict_rise n (by omega) (huniq n hn)
    have htele := card_Ico_add_two_step_le minimalDistinctDistances
      MinimumMonotone91.minimum_monotone E1 L M (by omega) hE1 hstep
    have hd4_L : 4 ≤ minimalDistinctDistances (L + 1) := by simpa using hd4
    omega
  | succ K ih =>
    intro L M hL hLM hd4 E1 hE1 huniq
    by_cases hL1 : 4 ≤ minimalDistinctDistances (L + 1)
    · have hL8 : 3 ≤ minimalDistinctDistances L :=
        three_le_minimalDistinctDistances_eight.trans
          (MinimumMonotone91.minimum_monotone hL)
      have hstep : ∀ n ∈ E1, minimalDistinctDistances n < minimalDistinctDistances (n + 2) := by
        intro n hn
        have hnL : L ≤ n := (mem_Ico.mp (hE1 hn)).1
        exact uniqueMinimizer_imp_two_step_strict_rise n (by omega) (huniq n hn)
      have htele := card_Ico_add_two_step_le minimalDistinctDistances
        MinimumMonotone91.minimum_monotone E1 L M (by omega) hE1 hstep
      omega
    · have hnotL : ¬ UniqueMinimizer L :=
        not_uniqueMinimizer_of_eight_le_of_succ_le_three L hL (by omega)
      have hE1_sub : E1 ⊆ Ico (L + 1) M := by
        intro n hn
        obtain ⟨hnL, hnM⟩ := mem_Ico.mp (hE1 hn)
        have hne : n ≠ L := fun heq => hnotL (heq ▸ huniq n hn)
        exact mem_Ico.mpr ⟨by omega, hnM⟩
      have hd4_next : 4 ≤ minimalDistinctDistances ((L + 1) + K + 1) := by
        have heq : (L + 1) + K + 1 = L + (K + 1) + 1 := by omega
        rw [heq]
        exact hd4
      exact ih (L + 1) M (by omega) (by omega) hd4_next E1 hE1_sub huniq

/-- **Sharpened prefix uniqueness bound for `M ≥ 20`:**
`E.card + 2 ≤ minimalDistinctDistances M + minimalDistinctDistances (M + 1)`
(improving `uniqueMinimizer_prefix_card_le` by `7`). -/
theorem uniqueMinimizer_prefix_card_add_two_le
    (M : ℕ) (hM : 20 ≤ M) (E : Finset ℕ) (hE : E ⊆ range M)
    (huniq : ∀ n ∈ E, UniqueMinimizer n) :
    E.card + 2 ≤ minimalDistinctDistances M + minimalDistinctDistances (M + 1) := by
  classical
  let E0 := E.filter (fun n => n < 8)
  let E1 := E.filter (fun n => ¬ n < 8)
  have hpart : E0.card + E1.card = E.card :=
    card_filter_add_card_filter_not (s := E) (p := fun n => n < 8)
  have hE0_le : E0.card ≤ 5 :=
    uniqueMinimizer_filter_lt_eight_card_le_five E huniq
  have hE1_sub : E1 ⊆ Ico 8 M := by
    intro n hn
    obtain ⟨hnE, hge⟩ := mem_filter.mp hn
    exact mem_Ico.mpr ⟨by omega, mem_range.mp (hE hnE)⟩
  have hE1_uniq : ∀ n ∈ E1, UniqueMinimizer n :=
    fun n hn => huniq n (mem_filter.mp hn).1
  have hE1_le := card_Ico_uniqueMinimizer_add_seven_le_aux 12 8 M
    (by omega) (by omega) four_le_minimalDistinctDistances_21 E1 hE1_sub hE1_uniq
  omega
/-- At the quadratic threshold `L = 2 * (K - 1)^2 + 3`, `L - 2 = 2 * (K - 1)^2 + 1 ≤ 2 * d(L)^2`
forces `K ≤ minimalDistinctDistances (2 * (K - 1)^2 + 3)` for every `K : ℕ`. -/
theorem le_minimalDistinctDistances_two_mul_sq_add_three (K : ℕ) :
    K ≤ minimalDistinctDistances (2 * (K - 1) ^ 2 + 3) := by
  by_cases hK : K = 0
  · omega
  · have h := minimal_quadratic_lower_bound (2 * (K - 1) ^ 2 + 3)
    by_contra hlt
    push Not at hlt
    have hle : minimalDistinctDistances (2 * (K - 1) ^ 2 + 3) ≤ K - 1 := by omega
    have hsq : (minimalDistinctDistances (2 * (K - 1) ^ 2 + 3)) ^ 2 ≤ (K - 1) ^ 2 :=
      Nat.pow_le_pow_left hle 2
    omega

/-- Sharpened quadratic `K`-multiplicity exception bound subtracting `2 * K` from
the boundary terms `d(L) + d(L + 1) ≥ 2 * K`:
for all `N ≥ 2 * (K - 1)^2 + 2`,
`(badMultiplicitySet K N).card + 2 * K ≤ (2 * (K - 1)^2 + 3) + d(N + 1) + d(N + 2)`. -/
theorem badMultiplicitySet_card_add_two_mul_le_of_ge (K N : ℕ)
    (hN : 2 * (K - 1) ^ 2 + 2 ≤ N) :
    (badMultiplicitySet K N).card + 2 * K ≤
      (2 * (K - 1) ^ 2 + 3) + minimalDistinctDistances (N + 1) + minimalDistinctDistances (N + 2) := by
  classical
  let L := 2 * (K - 1) ^ 2 + 3
  let B := badMultiplicitySet K N
  let E0 := B.filter (fun n => n < L)
  let E1 := B.filter (fun n => ¬ n < L)
  have hpart : E0.card + E1.card = B.card :=
    card_filter_add_card_filter_not (s := B) (p := fun n => n < L)
  have hE0_sub : E0 ⊆ range L := by
    intro n hn
    exact mem_range.mpr (mem_filter.mp hn).2
  have hE0_le : E0.card ≤ L := by
    have h := card_le_card hE0_sub
    simpa only [card_range] using h
  have hE1_sub : E1 ⊆ Ico L (N + 1) := by
    intro n hn
    obtain ⟨hnB, hge⟩ := mem_filter.mp hn
    have hn_lt : n < N + 1 := mem_range.mp (mem_filter.mp hnB).1
    exact mem_Ico.mpr ⟨by omega, hn_lt⟩
  have hE1_step : ∀ n ∈ E1, minimalDistinctDistances n < minimalDistinctDistances (n + 2) := by
    intro n hn
    obtain ⟨hnB, hge⟩ := mem_filter.mp hn
    have hnot : ¬ HasAtLeastKNonsimilarMinimizers K n := (mem_filter.mp hnB).2
    exact not_has_K_minimizers_imp_two_step_strict_rise_quadratic K n (by omega) hnot
  have hE1_le := card_Ico_add_two_step_le minimalDistinctDistances
    MinimumMonotone91.minimum_monotone E1 L (N + 1) (by omega) hE1_sub hE1_step
  have heq : N + 1 + 1 = N + 2 := by omega
  rw [heq] at hE1_le
  have hdL : K ≤ minimalDistinctDistances L :=
    le_minimalDistinctDistances_two_mul_sq_add_three K
  have hdL1 : K ≤ minimalDistinctDistances (L + 1) :=
    hdL.trans (MinimumMonotone91.minimum_monotone (by omega))
  change B.card + 2 * K ≤ L + minimalDistinctDistances (N + 1) + minimalDistinctDistances (N + 2)
  omega

/-- Global `K = 3` exception bound for all `N : ℕ`:
`(badMultiplicitySet 3 N).card ≤ 5 + minimalDistinctDistances (N + 1) + minimalDistinctDistances (N + 2)`
(reducing the additive constant for `K = 3` from `19` and `11` down to `5`). -/
theorem badMultiplicitySet_three_card_le_five_add (N : ℕ) :
    (badMultiplicitySet 3 N).card ≤
      5 + minimalDistinctDistances (N + 1) + minimalDistinctDistances (N + 2) := by
  classical
  by_cases hN : 10 ≤ N
  · have h := badMultiplicitySet_card_add_two_mul_le_of_ge 3 N (by omega)
    omega
  · have hsub : badMultiplicitySet 3 N ⊆ range (N + 1) := filter_subset _ _
    have hcard : (badMultiplicitySet 3 N).card ≤ N + 1 := by
      simpa using card_le_card hsub
    by_cases hN4 : N ≤ 4
    · omega
    · have h6 := minimalDistinctDistances_six
      have hm1 : minimalDistinctDistances 6 ≤ minimalDistinctDistances (N + 1) :=
        MinimumMonotone91.minimum_monotone (by omega)
      have hm2 : minimalDistinctDistances 6 ≤ minimalDistinctDistances (N + 2) :=
        MinimumMonotone91.minimum_monotone (by omega)
      omega

end Erdos91.SharpenedTelescopingAndPrefixBounds
namespace Erdos91.SharpenedFirstOccurrenceAnd36KSquaredBound
open Finset Minimizer91
open Erdos91.GeneralMultiplicityAndDensityOne (HasAtLeastKNonsimilarMinimizers)

/-- Every `n : ℕ` admits at least `1` globally optimal `n`-point configuration. -/
theorem hasAtLeastOneMinimizer (n : ℕ) : HasAtLeastKNonsimilarMinimizers 1 n := by
  classical
  obtain ⟨S, hS⟩ := exists_optimal n
  refine ⟨{S}, card_singleton S, ?_, ?_⟩
  · intro A hA
    rw [mem_singleton.mp hA]
    exact hS
  · intro A hA B hB hne
    rw [mem_singleton.mp hA, mem_singleton.mp hB] at hne
    exact False.elim (hne rfl)

end Erdos91.SharpenedFirstOccurrenceAnd36KSquaredBound

namespace Erdos91.FiveLe35TransitionAnd58ExceptionBound
open Finset Minimizer91 PlateauDefinitions91
open Erdos91.UnboundedRises (minimal_quadratic_lower_bound)
open Erdos91.EightAndNineNonunique (minimalDistinctDistances_eight_le_four not_uniqueMinimizer_eight_and_nine_of_four_le)
open Erdos91.TwoPointDeletionAndTwoStepPlateau (uniqueMinimizer_imp_two_step_strict_rise)
open Erdos91.UnconditionalEightNineDichotomy (three_le_minimalDistinctDistances_eight not_uniqueMinimizer_nine_of_four_le_nine)
open Erdos91.SharpenedTelescopingAndPrefixBounds (card_Ico_add_two_step_le uniqueMinimizer_filter_lt_eight_card_le_five)
/-- Unconditional lower bound `5 ≤ d(35)` from `35 - 2 = 33 ≤ 2 * d(35)^2`. -/
theorem five_le_minimalDistinctDistances_35 :
    5 ≤ minimalDistinctDistances 35 := by
  have h := minimal_quadratic_lower_bound 35
  nlinarith

/-- For every `n ≥ 8`, if `d(n) ≤ 4` and `UniqueMinimizer n`, then `d(n) < d(n + 1)`
(using `not_uniqueMinimizer_eight_and_nine_of_four_le` at `n = 8`,
`not_uniqueMinimizer_nine_of_four_le_nine` at `n = 9`, and `2 * d(n) ≤ 8 < n - 1`
for `n ≥ 10` and `d(n) = 3` at `n ≥ 8`). -/
theorem uniqueMinimizer_imp_strict_rise_of_eight_le_of_le_four
    (n : ℕ) (hn : 8 ≤ n) (hd : minimalDistinctDistances n ≤ 4)
    (huniq : UniqueMinimizer n) :
    minimalDistinctDistances n < minimalDistinctDistances (n + 1) := by
  have h8 : 3 ≤ minimalDistinctDistances n :=
    three_le_minimalDistinctDistances_eight.trans
      (MinimumMonotone91.minimum_monotone hn)
  have hle : minimalDistinctDistances n ≤ minimalDistinctDistances (n + 1) :=
    MinimumMonotone91.minimum_monotone (by omega)
  by_cases hd3 : minimalDistinctDistances n = 3
  · have hne : minimalDistinctDistances n ≠ minimalDistinctDistances (n + 1) :=
      fun heq => PlateauNonunique91.low_distance_plateau_not_unique n (by omega) heq (by omega) huniq
    omega
  · have hd4 : minimalDistinctDistances n = 4 := by omega
    by_cases hn8 : n = 8
    · subst hn8
      exact False.elim ((not_uniqueMinimizer_eight_and_nine_of_four_le (by omega)).2.2.1 huniq)
    · by_cases hn9 : n = 9
      · subst hn9
        exact False.elim ((not_uniqueMinimizer_nine_of_four_le_nine (by omega)).2.2.2 huniq)
      · have hne : minimalDistinctDistances n ≠ minimalDistinctDistances (n + 1) :=
          fun heq => PlateauNonunique91.low_distance_plateau_not_unique n (by omega) heq (by omega) huniq
        omega

/-- Existence of a transition index `L ∈ [a, a + K]` with `d(L) ≤ 4` and `5 ≤ d(L + 1)`. -/
theorem exists_transition_le_four_five_le_aux (K : ℕ) :
    ∀ a : ℕ, minimalDistinctDistances a ≤ 4 → 5 ≤ minimalDistinctDistances (a + K + 1) →
      ∃ L, a ≤ L ∧ L ≤ a + K ∧
        minimalDistinctDistances L ≤ 4 ∧ 5 ≤ minimalDistinctDistances (L + 1) := by
  induction K with
  | zero =>
    intro a ha h5
    exact ⟨a, le_refl a, le_refl a, ha, by simpa using h5⟩
  | succ K ih =>
    intro a ha h5
    by_cases ha1 : 5 ≤ minimalDistinctDistances (a + 1)
    · exact ⟨a, le_refl a, by omega, ha, ha1⟩
    · have h5_next : 5 ≤ minimalDistinctDistances ((a + 1) + K + 1) := by
        have heq : (a + 1) + K + 1 = a + (K + 1) + 1 := by omega
        rw [heq]; exact h5
      obtain ⟨L, hL1, hL2, hdL, hdL1⟩ := ih (a + 1) (by omega) h5_next
      exact ⟨L, by omega, by omega, hdL, hdL1⟩

/-- Splicing one-step telescoping on `[8, L)` (`E1a.card + d(8) ≤ d(L)`) with
two-step telescoping on `[L, M)` (`E1b.card + d(L) + d(L + 1) ≤ d(M) + d(M + 1)`)
cancels `d(L)` and uses `d(8) + d(L + 1) ≥ 3 + 5 = 8` to prove
`E1.card + 8 ≤ d(M) + d(M + 1)` for all `M ≥ 34`. -/
theorem card_Ico_eight_uniqueMinimizer_add_eight_le
    (M : ℕ) (hM : 34 ≤ M) (E1 : Finset ℕ) (hE1 : E1 ⊆ Ico 8 M)
    (huniq : ∀ n ∈ E1, UniqueMinimizer n) :
    E1.card + 8 ≤ minimalDistinctDistances M + minimalDistinctDistances (M + 1) := by
  classical
  obtain ⟨L, hL8, hL34, hdL4, hdL1_5⟩ :=
    exists_transition_le_four_five_le_aux 26 8
      minimalDistinctDistances_eight_le_four five_le_minimalDistinctDistances_35
  have h8 := three_le_minimalDistinctDistances_eight
  by_cases hL_eq : L = 8
  · subst hL_eq
    have hstep : ∀ n ∈ E1, minimalDistinctDistances n < minimalDistinctDistances (n + 2) := by
      intro n hn
      have hn8 : 8 ≤ n := (mem_Ico.mp (hE1 hn)).1
      exact uniqueMinimizer_imp_two_step_strict_rise n (by omega) (huniq n hn)
    have htele := card_Ico_add_two_step_le minimalDistinctDistances
      MinimumMonotone91.minimum_monotone E1 8 M (by omega) hE1 hstep
    omega
  · let E1a := E1.filter (fun n => n < L)
    let E1b := E1.filter (fun n => ¬ n < L)
    have hpart : E1a.card + E1b.card = E1.card :=
      card_filter_add_card_filter_not (s := E1) (p := fun n => n < L)
    have h1a : E1a.card ≤ minimalDistinctDistances ((L - 1) + 1) - minimalDistinctDistances 8 := by
      apply OneStepCount91.card_le minimalDistinctDistances
        MinimumMonotone91.minimum_monotone E1a 8 (L - 1)
      · intro n hn
        obtain ⟨hnE1, hlt⟩ := mem_filter.mp hn
        have h := mem_Ico.mp (hE1 hnE1)
        exact mem_Icc.mpr ⟨h.1, by omega⟩
      · intro n hn
        obtain ⟨hnE1, hlt⟩ := mem_filter.mp hn
        have hn8 : 8 ≤ n := (mem_Ico.mp (hE1 hnE1)).1
        have hdn : minimalDistinctDistances n ≤ 4 :=
          (MinimumMonotone91.minimum_monotone (by omega : n ≤ L)).trans hdL4
        exact uniqueMinimizer_imp_strict_rise_of_eight_le_of_le_four n hn8 hdn (huniq n hnE1)
    have hL_pred : (L - 1) + 1 = L := by omega
    rw [hL_pred] at h1a
    have h1b_sub : E1b ⊆ Ico L M := by
      intro n hn
      obtain ⟨hnE1, hge⟩ := mem_filter.mp hn
      have h := mem_Ico.mp (hE1 hnE1)
      exact mem_Ico.mpr ⟨by omega, h.2⟩
    have h1b_step : ∀ n ∈ E1b, minimalDistinctDistances n < minimalDistinctDistances (n + 2) := by
      intro n hn
      obtain ⟨hnE1, _⟩ := mem_filter.mp hn
      have hn8 : 8 ≤ n := (mem_Ico.mp (hE1 hnE1)).1
      exact uniqueMinimizer_imp_two_step_strict_rise n (by omega) (huniq n hnE1)
    have h1b := card_Ico_add_two_step_le minimalDistinctDistances
      MinimumMonotone91.minimum_monotone E1b L M (by omega) h1b_sub h1b_step
    have hm8L : minimalDistinctDistances 8 ≤ minimalDistinctDistances L :=
      MinimumMonotone91.minimum_monotone hL8
    omega

/-- **Sharpened prefix uniqueness bound for `M ≥ 34`:**
`E.card + 3 ≤ minimalDistinctDistances M + minimalDistinctDistances (M + 1)`
(improving `uniqueMinimizer_prefix_card_le` by `8`). -/
theorem uniqueMinimizer_prefix_card_add_three_le
    (M : ℕ) (hM : 34 ≤ M) (E : Finset ℕ) (hE : E ⊆ range M)
    (huniq : ∀ n ∈ E, UniqueMinimizer n) :
    E.card + 3 ≤ minimalDistinctDistances M + minimalDistinctDistances (M + 1) := by
  classical
  let E0 := E.filter (fun n => n < 8)
  let E1 := E.filter (fun n => ¬ n < 8)
  have hpart : E0.card + E1.card = E.card :=
    card_filter_add_card_filter_not (s := E) (p := fun n => n < 8)
  have hE0_le : E0.card ≤ 5 :=
    uniqueMinimizer_filter_lt_eight_card_le_five E huniq
  have hE1_sub : E1 ⊆ Ico 8 M := by
    intro n hn
    obtain ⟨hnE, hge⟩ := mem_filter.mp hn
    exact mem_Ico.mpr ⟨by omega, mem_range.mp (hE hnE)⟩
  have hE1_uniq : ∀ n ∈ E1, UniqueMinimizer n :=
    fun n hn => huniq n (mem_filter.mp hn).1
  have hE1_le := card_Ico_eight_uniqueMinimizer_add_eight_le M hM E1 hE1_sub hE1_uniq
  omega

end Erdos91.FiveLe35TransitionAnd58ExceptionBound

namespace Erdos91.EvenOddGapSplicingAnd21KDiv4Bounds
open Finset Minimizer91 PlateauDefinitions91
open Erdos91.TwoPointDeletionAndTwoStepPlateau (uniqueMinimizer_imp_two_step_strict_rise)

/-- On any 2-element interval `Ico a (a + 2)` (`a ≥ 5`), two-step plateau nonuniqueness
at `a` forces `E.card + d(a) ≤ 1 + d(a + 2)` for every `E ⊆ Ico a (a + 2)` of uniqueness indices. -/
theorem uniqueMinimizer_two_step_gap_card_add_le
    (a : ℕ) (ha : 5 ≤ a) (E : Finset ℕ) (hE : E ⊆ Ico a (a + 2))
    (huniq : ∀ n ∈ E, UniqueMinimizer n) :
    E.card + minimalDistinctDistances a ≤ 1 + minimalDistinctDistances (a + 2) := by
  classical
  by_cases haE : a ∈ E
  · have hcard : E.card ≤ (a + 2) - a := by
      simpa using card_le_card hE
    have hrise : minimalDistinctDistances a < minimalDistinctDistances (a + 2) :=
      uniqueMinimizer_imp_two_step_strict_rise a ha (huniq a haE)
    omega
  · have hsub : E ⊆ Ico (a + 1) (a + 2) := by
      intro n hn
      have h := mem_Ico.mp (hE hn)
      have hne : n ≠ a := fun heq => haE (heq ▸ hn)
      exact mem_Ico.mpr ⟨by omega, h.2⟩
    have hcard : E.card ≤ (a + 2) - (a + 1) := by
      simpa using card_le_card hsub
    have hmono : minimalDistinctDistances a ≤ minimalDistinctDistances (a + 2) :=
      MinimumMonotone91.minimum_monotone (by omega)
    omega

/-- General even-length gap splicing bound: for any `m : ℕ`, `a ≥ 5`, and
`E ⊆ Ico a (a + 2 * m)` of uniqueness indices,
`E.card + d(a) ≤ m + d(a + 2 * m)`. -/
theorem uniqueMinimizer_even_gap_card_add_le (m : ℕ) :
    ∀ (a : ℕ), 5 ≤ a → ∀ (E : Finset ℕ), E ⊆ Ico a (a + 2 * m) →
      (∀ n ∈ E, UniqueMinimizer n) →
        E.card + minimalDistinctDistances a ≤ m + minimalDistinctDistances (a + 2 * m) := by
  induction m with
  | zero =>
    intro a _ E hE _
    have hsub : E ⊆ ∅ := by simpa using hE
    have hem : E = ∅ := subset_empty.mp hsub
    simp [hem]
  | succ m ih =>
    intro a ha E hE huniq
    classical
    let E1 := E.filter (fun n => n < a + 2 * m)
    let E2 := E.filter (fun n => ¬ n < a + 2 * m)
    have hpart : E1.card + E2.card = E.card :=
      card_filter_add_card_filter_not (s := E) (p := fun n => n < a + 2 * m)
    have h1_sub : E1 ⊆ Ico a (a + 2 * m) := by
      intro n hn
      obtain ⟨hnE, hlt⟩ := mem_filter.mp hn
      exact mem_Ico.mpr ⟨(mem_Ico.mp (hE hnE)).1, hlt⟩
    have h1 := ih a ha E1 h1_sub (fun n hn => huniq n (mem_filter.mp hn).1)
    have h2_sub : E2 ⊆ Ico (a + 2 * m) (a + 2 * m + 2) := by
      intro n hn
      obtain ⟨hnE, hge⟩ := mem_filter.mp hn
      have h := mem_Ico.mp (hE hnE)
      exact mem_Ico.mpr ⟨by omega, by omega⟩
    have h2 := uniqueMinimizer_two_step_gap_card_add_le (a + 2 * m) (by omega) E2 h2_sub
      (fun n hn => huniq n (mem_filter.mp hn).1)
    have heq : a + 2 * (m + 1) = a + 2 * m + 2 := by omega
    rw [heq]
    omega

/-- General odd-length gap splicing bound: for any `m : ℕ`, `a ≥ 5`, and
`E ⊆ Ico a (a + 2 * m + 1)` of uniqueness indices,
`E.card + d(a) ≤ m + 1 + d(a + 2 * m + 1)`. -/
theorem uniqueMinimizer_odd_gap_card_add_le
    (m a : ℕ) (ha : 5 ≤ a) (E : Finset ℕ) (hE : E ⊆ Ico a (a + 2 * m + 1))
    (huniq : ∀ n ∈ E, UniqueMinimizer n) :
    E.card + minimalDistinctDistances a ≤ m + 1 + minimalDistinctDistances (a + 2 * m + 1) := by
  classical
  let E1 := E.filter (fun n => n < a + 2 * m)
  let E2 := E.filter (fun n => ¬ n < a + 2 * m)
  have hpart : E1.card + E2.card = E.card :=
    card_filter_add_card_filter_not (s := E) (p := fun n => n < a + 2 * m)
  have h1_sub : E1 ⊆ Ico a (a + 2 * m) := by
    intro n hn
    obtain ⟨hnE, hlt⟩ := mem_filter.mp hn
    exact mem_Ico.mpr ⟨(mem_Ico.mp (hE hnE)).1, hlt⟩
  have h1 := uniqueMinimizer_even_gap_card_add_le m a ha E1 h1_sub
    (fun n hn => huniq n (mem_filter.mp hn).1)
  have h2_sub : E2 ⊆ Ico (a + 2 * m) (a + 2 * m + 1) := by
    intro n hn
    obtain ⟨hnE, hge⟩ := mem_filter.mp hn
    have h := mem_Ico.mp (hE hnE)
    exact mem_Ico.mpr ⟨by omega, h.2⟩
  have h2 : E2.card ≤ (a + 2 * m + 1) - (a + 2 * m) := by
    simpa using card_le_card h2_sub
  have hm : minimalDistinctDistances (a + 2 * m) ≤ minimalDistinctDistances (a + 2 * m + 1) :=
    MinimumMonotone91.minimum_monotone (by omega)
  omega
end Erdos91.EvenOddGapSplicingAnd21KDiv4Bounds

namespace Erdos91.TriangularLatticeHexagonAndSub130Majority
open Finset Minimizer91 PlateauDefinitions91
open Erdos91.SmallCasesAndSquareBarrier (plane_dist_sq)
open Erdos91.FourNonuniqueAndDoubleEquilateral (plane_ext)
open Erdos91.GeneralMultiplicityAndDensityOne (HasAtLeastKNonsimilarMinimizers)
open Erdos91.AsymptoticDensityOneAndGlobalBounds (uniqueMinimizerSet badMultiplicitySet goodMultiplicitySet good_add_badMultiplicitySet_card)

open Erdos91.Grid20Exact179DistancesAndFullCertificate (isStrictlyIncreasing pairwise_lt_of_isStrictlyIncreasing)
open Erdos91.ConcreteMultiplicityBenchmarks322And398 (exists_le_of_goodMultiplicitySet_pos)
open Erdos91.SharpenedTelescopingAndPrefixBounds (uniqueMinimizer_prefix_card_add_two_le badMultiplicitySet_card_add_two_mul_le_of_ge badMultiplicitySet_three_card_le_five_add)
open Erdos91.FiveLe35TransitionAnd58ExceptionBound (uniqueMinimizer_prefix_card_add_three_le)
open Erdos91.EvenOddGapSplicingAnd21KDiv4Bounds (uniqueMinimizer_two_step_gap_card_add_le uniqueMinimizer_even_gap_card_add_le)
/-- Triangular-lattice embedding `(x, y) ↦ (2x + y, √3 y)` in the Euclidean plane. -/
noncomputable def triPoint (p : ℕ × ℕ) : Plane :=
  !₂[(2 * (p.1 : ℝ) + (p.2 : ℝ)), Real.sqrt 3 * (p.2 : ℝ)]

theorem triPoint_injective : Function.Injective triPoint := by
  intro p q h
  have h0 : triPoint p 0 = triPoint q 0 := congrArg (fun x : Plane => x 0) h
  have h1 : triPoint p 1 = triPoint q 1 := congrArg (fun x : Plane => x 1) h
  change 2 * (p.1 : ℝ) + (p.2 : ℝ) = 2 * (q.1 : ℝ) + (q.2 : ℝ) at h0
  change Real.sqrt 3 * (p.2 : ℝ) = Real.sqrt 3 * (q.2 : ℝ) at h1
  have hs3_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hy_real : (p.2 : ℝ) = (q.2 : ℝ) := mul_left_cancel₀ (ne_of_gt hs3_pos) h1
  have hx_real : (p.1 : ℝ) = (q.1 : ℝ) := by linarith
  exact Prod.ext (Nat.cast_injective hx_real) (Nat.cast_injective hy_real)

/-- Integer Eisenstein squared norm `4 * (a^2 + a*b + b^2)` of a triangular-lattice offset. -/
def triNormSq (u : ℕ × ℕ) : ℕ :=
  4 * (u.1 * u.1 + u.1 * u.2 + u.2 * u.2)

/-- Euclidean norm `√(triNormSq u)` of a triangular-lattice offset. -/
noncomputable def triNorm (u : ℕ × ℕ) : ℝ :=
  Real.sqrt (triNormSq u : ℝ)

theorem card_image_triNorm_eq_card_image_triNormSq (S : Finset (ℕ × ℕ)) :
    (S.image triNorm).card = (S.image triNormSq).card := by
  classical
  have him : S.image triNorm = (S.image triNormSq).image (fun n : ℕ => Real.sqrt (n : ℝ)) := by
    rw [Finset.image_image]
    rfl
  have hinj : Set.InjOn (fun n : ℕ => Real.sqrt (n : ℝ)) (S.image triNormSq) := by
    intro a _ b _ h
    have hsq := (Real.sqrt_inj (Nat.cast_nonneg a) (Nat.cast_nonneg b)).mp h
    exact_mod_cast hsq
  rw [him, Finset.card_image_of_injOn hinj]

/-- Canonical triangular-lattice offset map normalizing any pair `p, q : ℕ × ℕ` into
`(a, b)` with `a ≤ b` and equal Eisenstein norm. -/
def triOffset (p q : ℕ × ℕ) : ℕ × ℕ :=
  let dx := Nat.dist p.1 q.1
  let dy := Nat.dist p.2 q.2
  if (p.1 ≤ q.1 ∧ p.2 ≤ q.2) ∨ (q.1 ≤ p.1 ∧ q.2 ≤ p.2) then
    if dx ≤ dy then (dx, dy) else (dy, dx)
  else
    let u := if dx ≤ dy then dx else dy
    let v := if dx ≤ dy then dy else dx
    let w := v - u
    if u ≤ w then (u, w) else (w, u)

theorem dist_triPoint_sq_eq_triNormSq (p q : ℕ × ℕ) :
    dist (triPoint p) (triPoint q) ^ 2 = (triNormSq (triOffset p q) : ℝ) := by
  rcases p with ⟨x1, y1⟩
  rcases q with ⟨x2, y2⟩
  rw [plane_dist_sq]
  change ((2 * (x1 : ℝ) + (y1 : ℝ)) - (2 * (x2 : ℝ) + (y2 : ℝ))) ^ 2 +
    (Real.sqrt 3 * (y1 : ℝ) - Real.sqrt 3 * (y2 : ℝ)) ^ 2 = _
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h_alg : ((2 * (x1 : ℝ) + (y1 : ℝ)) - (2 * (x2 : ℝ) + (y2 : ℝ))) ^ 2 +
      (Real.sqrt 3 * (y1 : ℝ) - Real.sqrt 3 * (y2 : ℝ)) ^ 2 =
      4 * (((x1 : ℝ) - (x2 : ℝ)) ^ 2 + ((x1 : ℝ) - (x2 : ℝ)) * ((y1 : ℝ) - (y2 : ℝ)) +
        ((y1 : ℝ) - (y2 : ℝ)) ^ 2) := by
    linear_combination ((y1 : ℝ) - (y2 : ℝ)) ^ 2 * hs3
  rw [h_alg]
  unfold triOffset triNormSq
  dsimp
  split_ifs with hsame hle1 hle2 hle3 hle4
  · rcases hsame with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · have hdx : Nat.dist x1 x2 = x2 - x1 := Nat.dist_eq_sub_of_le hx
      have hdy : Nat.dist y1 y2 = y2 - y1 := Nat.dist_eq_sub_of_le hy
      rw [hdx, hdy]; push_cast [hx, hy]; ring
    · have hdx : Nat.dist x1 x2 = x1 - x2 := by rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hx]
      have hdy : Nat.dist y1 y2 = y1 - y2 := by rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hy]
      rw [hdx, hdy]; push_cast [hx, hy]; ring
  · rcases hsame with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · have hdx : Nat.dist x1 x2 = x2 - x1 := Nat.dist_eq_sub_of_le hx
      have hdy : Nat.dist y1 y2 = y2 - y1 := Nat.dist_eq_sub_of_le hy
      rw [hdx, hdy]; push_cast [hx, hy]; ring
    · have hdx : Nat.dist x1 x2 = x1 - x2 := by rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hx]
      have hdy : Nat.dist y1 y2 = y1 - y2 := by rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hy]
      rw [hdx, hdy]; push_cast [hx, hy]; ring
  · have hopp : (x1 ≤ x2 ∧ y2 ≤ y1) ∨ (x2 ≤ x1 ∧ y1 ≤ y2) := by omega
    rcases hopp with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · have hdx : Nat.dist x1 x2 = x2 - x1 := Nat.dist_eq_sub_of_le hx
      have hdy : Nat.dist y1 y2 = y1 - y2 := by rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hy]
      rw [hdx, hdy] at hle2 hle3 ⊢
      push_cast [hx, hy, hle2]; ring
    · have hdx : Nat.dist x1 x2 = x1 - x2 := by rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hx]
      have hdy : Nat.dist y1 y2 = y2 - y1 := Nat.dist_eq_sub_of_le hy
      rw [hdx, hdy] at hle2 hle3 ⊢
      push_cast [hx, hy, hle2]; ring
  · have hopp : (x1 ≤ x2 ∧ y2 ≤ y1) ∨ (x2 ≤ x1 ∧ y1 ≤ y2) := by omega
    rcases hopp with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · have hdx : Nat.dist x1 x2 = x2 - x1 := Nat.dist_eq_sub_of_le hx
      have hdy : Nat.dist y1 y2 = y1 - y2 := by rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hy]
      rw [hdx, hdy] at hle2 hle3 ⊢
      push_cast [hx, hy, hle2]; ring
    · have hdx : Nat.dist x1 x2 = x1 - x2 := by rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hx]
      have hdy : Nat.dist y1 y2 = y2 - y1 := Nat.dist_eq_sub_of_le hy
      rw [hdx, hdy] at hle2 hle3 ⊢
      push_cast [hx, hy, hle2]; ring
  · have hopp : (x1 ≤ x2 ∧ y2 ≤ y1) ∨ (x2 ≤ x1 ∧ y1 ≤ y2) := by omega
    have hdy_le : Nat.dist y1 y2 ≤ Nat.dist x1 x2 := by omega
    rcases hopp with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · have hdx : Nat.dist x1 x2 = x2 - x1 := Nat.dist_eq_sub_of_le hx
      have hdy : Nat.dist y1 y2 = y1 - y2 := by rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hy]
      rw [hdx, hdy] at hdy_le hle4 ⊢
      push_cast [hx, hy, hdy_le]; ring
    · have hdx : Nat.dist x1 x2 = x1 - x2 := by rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hx]
      have hdy : Nat.dist y1 y2 = y2 - y1 := Nat.dist_eq_sub_of_le hy
      rw [hdx, hdy] at hdy_le hle4 ⊢
      push_cast [hx, hy, hdy_le]; ring
  · have hopp : (x1 ≤ x2 ∧ y2 ≤ y1) ∨ (x2 ≤ x1 ∧ y1 ≤ y2) := by omega
    have hdy_le : Nat.dist y1 y2 ≤ Nat.dist x1 x2 := by omega
    rcases hopp with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · have hdx : Nat.dist x1 x2 = x2 - x1 := Nat.dist_eq_sub_of_le hx
      have hdy : Nat.dist y1 y2 = y1 - y2 := by rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hy]
      rw [hdx, hdy] at hdy_le hle4 ⊢
      push_cast [hx, hy, hdy_le]; ring
    · have hdx : Nat.dist x1 x2 = x1 - x2 := by rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hx]
      have hdy : Nat.dist y1 y2 = y2 - y1 := Nat.dist_eq_sub_of_le hy
      rw [hdx, hdy] at hdy_le hle4 ⊢
      push_cast [hx, hy, hdy_le]; ring

theorem dist_triPoint_eq (p q : ℕ × ℕ) :
    dist (triPoint p) (triPoint q) = triNorm (triOffset p q) := by
  unfold triNorm
  rw [← Real.sqrt_sq dist_nonneg, dist_triPoint_sq_eq_triNormSq]

def hexRowList (k c m x : ℕ) : List (ℕ × ℕ) :=
  ((List.range k).filter (fun y =>
    decide (c ≤ x + y ∧ x + y ≤ c + m))).map (fun y => (x, y))

def hexCoordsList (k c m : ℕ) : List (ℕ × ℕ) :=
  (List.range k).flatMap (hexRowList k c m)

def hexCoords (k c m : ℕ) : Finset (ℕ × ℕ) :=
  (hexCoordsList k c m).toFinset

noncomputable def hexSet (k c m : ℕ) : Finset Plane :=
  (hexCoords k c m).image triPoint

theorem hexRowList_nodup (k c m x : ℕ) : (hexRowList k c m x).Nodup := by
  unfold hexRowList
  exact List.Nodup.map (fun y1 y2 h => by injection h) (List.nodup_range.filter _)

theorem hexCoordsList_nodup (k c m : ℕ) : (hexCoordsList k c m).Nodup := by
  unfold hexCoordsList
  rw [List.nodup_flatMap]
  refine ⟨fun x _ => hexRowList_nodup k c m x, ?_⟩
  refine List.nodup_range.pairwise_of_forall_ne (fun x1 _ x2 _ hne => ?_)
  intro p hp1 hp2
  unfold hexRowList at hp1 hp2
  rw [List.mem_map] at hp1 hp2
  obtain ⟨y1, _, rfl⟩ := hp1
  obtain ⟨y2, _, heq⟩ := hp2
  injection heq with hx _
  exact hne hx.symm

theorem card_hexCoords (k c m : ℕ) :
    (hexCoords k c m).card =
      ((List.range k).map (fun x => (hexRowList k c m x).length)).sum := by
  unfold hexCoords
  rw [List.toFinset_card_of_nodup (hexCoordsList_nodup k c m)]
  exact List.length_flatMap

theorem card_hexSet (k c m : ℕ) :
    (hexSet k c m).card =
      ((List.range k).map (fun x => (hexRowList k c m x).length)).sum := by
  unfold hexSet
  rw [Finset.card_image_of_injective _ triPoint_injective, card_hexCoords]

theorem mem_hexCoords (k c m : ℕ) (p : ℕ × ℕ) (hp : p ∈ hexCoords k c m) :
    p.1 < k ∧ p.2 < k ∧ c ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ c + m := by
  rcases p with ⟨x, y⟩
  unfold hexCoords hexCoordsList hexRowList at hp
  rw [List.mem_toFinset, List.mem_flatMap] at hp
  obtain ⟨x0, hx0, hy0⟩ := hp
  rw [List.mem_range] at hx0
  rw [List.mem_map] at hy0
  obtain ⟨y0, hy0_mem, heq⟩ := hy0
  rw [List.mem_filter, List.mem_range, decide_eq_true_eq] at hy0_mem
  injection heq with hx hy
  subst hx; subst hy
  exact ⟨hx0, hy0_mem.1, hy0_mem.2⟩

def triUtpRowList (m x : ℕ) : List (ℕ × ℕ) :=
  ((List.range (m + 1)).filter (fun y =>
    decide ((x, y) ≠ (0, 0) ∧ x ≤ y ∧ x + y ≤ m))).map (fun y => (x, y))

def triUtpList (m : ℕ) : List (ℕ × ℕ) :=
  (List.range (m + 1)).flatMap (triUtpRowList m)

def triUtp (m : ℕ) : Finset (ℕ × ℕ) :=
  (triUtpList m).toFinset

theorem card_triUtp_le (m : ℕ) :
    (triUtp m).card ≤
      ((List.range (m + 1)).map (fun x => (triUtpRowList m x).length)).sum := by
  unfold triUtp
  exact (List.toFinset_card_le _).trans (le_of_eq List.length_flatMap)

theorem mem_triUtp_of_bounds (m : ℕ) (u : ℕ × ℕ)
    (hne0 : u ≠ (0, 0)) (hle : u.1 ≤ u.2) (hsum : u.1 + u.2 ≤ m) :
    u ∈ triUtp m := by
  rcases u with ⟨x, y⟩
  dsimp at hle hsum
  unfold triUtp triUtpList triUtpRowList
  rw [List.mem_toFinset, List.mem_flatMap]
  refine ⟨x, List.mem_range.mpr (by omega), List.mem_map.mpr ⟨y, ?_, rfl⟩⟩
  rw [List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨by omega, hne0, hle, hsum⟩

theorem triOffset_mem_triUtp (k c m : ℕ) (hkm : k ≤ m + 1)
    (p q : ℕ × ℕ) (hpq : p ≠ q)
    (hp : p ∈ hexCoords k c m) (hq : q ∈ hexCoords k c m) :
    triOffset p q ∈ triUtp m := by
  have hbp := mem_hexCoords k c m p hp
  have hbq := mem_hexCoords k c m q hq
  rcases p with ⟨x1, y1⟩
  rcases q with ⟨x2, y2⟩
  dsimp at hbp hbq ⊢
  have hdx : Nat.dist x1 x2 < k := by unfold Nat.dist; omega
  have hdy : Nat.dist y1 y2 < k := by unfold Nat.dist; omega
  have hne0 : Nat.dist x1 x2 ≠ 0 ∨ Nat.dist y1 y2 ≠ 0 := by
    by_contra hboth
    push Not at hboth
    unfold Nat.dist at hboth
    exact hpq (Prod.ext (by omega) (by omega))
  unfold triOffset
  dsimp
  split_ifs with hsame hle1 hle2 hle3 hle4
  · have hsum : Nat.dist x1 x2 + Nat.dist y1 y2 ≤ m := by unfold Nat.dist; omega
    apply mem_triUtp_of_bounds m _ _ hle1 hsum
    simp only [ne_eq, Prod.mk.injEq]; omega
  · have hsum : Nat.dist y1 y2 + Nat.dist x1 x2 ≤ m := by unfold Nat.dist; omega
    apply mem_triUtp_of_bounds m _ _ (by omega) hsum
    simp only [ne_eq, Prod.mk.injEq]; omega
  · apply mem_triUtp_of_bounds m _ _ hle3 (by omega)
    simp only [ne_eq, Prod.mk.injEq]; omega
  · apply mem_triUtp_of_bounds m _ _ (by omega) (by omega)
    simp only [ne_eq, Prod.mk.injEq]; omega
  · apply mem_triUtp_of_bounds m _ _ hle4 (by omega)
    simp only [ne_eq, Prod.mk.injEq]; omega
  · apply mem_triUtp_of_bounds m _ _ (by omega) (by omega)
    simp only [ne_eq, Prod.mk.injEq]; omega

theorem distanceSet_hexSet_subset (k c m : ℕ) (hkm : k ≤ m + 1) :
    Erdos91.DistanceErasure.distanceSet (hexSet k c m) ⊆ (triUtp m).image triNorm := by
  classical
  intro r hr
  obtain ⟨a, ha, b, hb, hab, rfl⟩ :=
    (Erdos91.DistanceErasure.mem_distanceSet (hexSet k c m) r).mp hr
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
  have hpq : p ≠ q := fun he => hab (congrArg triPoint he)
  rw [dist_triPoint_eq p q]
  exact Finset.mem_image_of_mem triNorm (triOffset_mem_triUtp k c m hkm p q hpq hp hq)

def triRedundant36U : List (ℕ × ℕ) :=
  [(3, 5), (4, 9), (5, 6), (5, 13), (5, 16), (6, 10), (6, 17), (6, 23), (7, 7), (7, 8), (7, 11), (7, 14), (7, 21), (8, 9), (8, 11), (8, 18), (8, 25), (9, 11), (9, 14), (9, 15), (9, 16), (9, 22), (9, 25), (10, 12), (10, 13), (10, 17), (10, 19), (10, 26), (11, 15), (11, 16), (11, 20), (11, 21), (11, 23), (11, 24), (12, 13), (12, 17), (12, 20), (12, 23), (13, 13), (13, 15), (13, 17), (13, 19), (14, 14), (14, 16), (14, 21), (14, 22), (15, 16), (15, 18), (15, 19), (16, 17), (16, 18), (17, 19)]

def triRedundant36V : (ℕ × ℕ) → (ℕ × ℕ)
  | (3, 5) => (0, 7)
  | (4, 9) => (1, 11)
  | (5, 6) => (1, 9)
  | (5, 13) => (2, 15)
  | (5, 16) => (0, 19)
  | (6, 10) => (0, 14)
  | (6, 17) => (3, 19)
  | (6, 23) => (1, 26)
  | (7, 7) => (2, 11)
  | (7, 8) => (0, 13)
  | (7, 11) => (3, 14)
  | (7, 14) => (1, 18)
  | (7, 21) => (4, 23)
  | (8, 9) => (3, 13)
  | (8, 11) => (1, 16)
  | (8, 18) => (2, 22)
  | (8, 25) => (5, 27)
  | (9, 11) => (4, 15)
  | (9, 14) => (2, 19)
  | (9, 15) => (0, 21)
  | (9, 16) => (5, 19)
  | (9, 22) => (3, 26)
  | (9, 25) => (1, 30)
  | (10, 12) => (2, 18)
  | (10, 13) => (5, 17)
  | (10, 17) => (3, 22)
  | (10, 19) => (1, 25)
  | (10, 26) => (4, 30)
  | (11, 15) => (6, 19)
  | (11, 16) => (1, 23)
  | (11, 20) => (4, 25)
  | (11, 21) => (7, 24)
  | (11, 23) => (2, 29)
  | (11, 24) => (0, 31)
  | (12, 13) => (3, 20)
  | (12, 17) => (4, 23)
  | (12, 20) => (0, 28)
  | (12, 23) => (5, 28)
  | (13, 13) => (1, 22)
  | (13, 15) => (7, 20)
  | (13, 17) => (2, 25)
  | (13, 19) => (8, 23)
  | (14, 14) => (4, 22)
  | (14, 16) => (0, 26)
  | (14, 21) => (1, 30)
  | (14, 22) => (6, 28)
  | (15, 16) => (5, 24)
  | (15, 18) => (3, 27)
  | (15, 19) => (1, 29)
  | (16, 17) => (9, 23)
  | (16, 18) => (6, 26)
  | (17, 19) => (4, 29)
  | p => p

theorem triRedundant36U_inc :
    isStrictlyIncreasing (triRedundant36U.map (fun p => 37 * p.1 + p.2)) = true := by
  decide

theorem triRedundant36U_nodup : triRedundant36U.Nodup := by
  exact List.Nodup.of_map (fun p : ℕ × ℕ => 37 * p.1 + p.2)
    ((pairwise_lt_of_isStrictlyIncreasing _ triRedundant36U_inc).imp ne_of_lt)

theorem triRedundant36U_valid :
    ∀ u ∈ triRedundant36U,
      (u ≠ (0, 0) ∧ u.1 ≤ u.2 ∧ u.1 + u.2 ≤ 36) ∧
      (triRedundant36V u ≠ (0, 0) ∧ (triRedundant36V u).1 ≤ (triRedundant36V u).2 ∧
        (triRedundant36V u).1 + (triRedundant36V u).2 ≤ u.1 + u.2) ∧
      triRedundant36V u ∉ triRedundant36U ∧
      triNormSq u = triNormSq (triRedundant36V u) := by
  decide

def hexRedundantPred (m : ℕ) (u : ℕ × ℕ) : Bool :=
  decide (u.1 + u.2 ≤ m)

def hexRedundantList (m : ℕ) : List (ℕ × ℕ) :=
  triRedundant36U.filter (hexRedundantPred m)

def hexRedundant (m : ℕ) : Finset (ℕ × ℕ) :=
  (hexRedundantList m).toFinset

theorem card_hexRedundant (m : ℕ) :
    (hexRedundant m).card = (hexRedundantList m).length :=
  List.toFinset_card_of_nodup (triRedundant36U_nodup.filter _)

theorem hexRedundant_subset_triUtp (m : ℕ) :
    hexRedundant m ⊆ triUtp m := by
  intro u hu
  unfold hexRedundant hexRedundantList hexRedundantPred at hu
  rw [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hu
  obtain ⟨⟨hne0, hle, _⟩, _, _, _⟩ := triRedundant36U_valid u hu.1
  exact mem_triUtp_of_bounds m u hne0 hle hu.2

theorem triUtp_image_subset_sdiff (m : ℕ) :
    (triUtp m).image triNormSq ⊆ (triUtp m \ hexRedundant m).image triNormSq := by
  classical
  intro r hr
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hr
  by_cases hpR : p ∈ hexRedundant m
  · have hp_mem := hpR
    unfold hexRedundant hexRedundantList hexRedundantPred at hp_mem
    rw [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hp_mem
    obtain ⟨_, ⟨hne0, hle, hv_sum⟩, hnotU, hnorm⟩ := triRedundant36U_valid p hp_mem.1
    rw [hnorm]
    apply Finset.mem_image_of_mem triNormSq
    refine Finset.mem_sdiff.mpr ⟨mem_triUtp_of_bounds m (triRedundant36V p) hne0 hle (hv_sum.trans hp_mem.2), ?_⟩
    intro hvm
    unfold hexRedundant hexRedundantList at hvm
    rw [List.mem_toFinset, List.mem_filter] at hvm
    exact hnotU hvm.1
  · exact Finset.mem_image_of_mem triNormSq (Finset.mem_sdiff.mpr ⟨hp, hpR⟩)

/-- **Master parameterized triangular-lattice hexagonal grid upper-bound theorem:**
for any `(k, c, m)` with `k ≤ m + 1`, `n` points in `hexSet k c m`, `u` offsets in `triUtp m`,
and `r` redundant offsets in `hexRedundant m`, `minimalDistinctDistances n ≤ u - r`. -/
theorem minimalDistinctDistances_hexCoords_le (k c m n u r : ℕ) (hkm : k ≤ m + 1)
    (hn : ((List.range k).map (fun x => (hexRowList k c m x).length)).sum = n)
    (hu : ((List.range (m + 1)).map (fun x => (triUtpRowList m x).length)).sum = u)
    (hr : (hexRedundantList m).length = r) :
    minimalDistinctDistances n ≤ u - r := by
  have hcard_set : (hexSet k c m).card = n := (card_hexSet k c m).trans hn
  have hmin : minimalDistinctDistances n ≤ distinctDistances (hexSet k c m) :=
    minimal_le (hexSet k c m) n hcard_set
  have hsub : distinctDistances (hexSet k c m) ≤ ((triUtp m).image triNorm).card :=
    Finset.card_le_card (distanceSet_hexSet_subset k c m hkm)
  rw [card_image_triNorm_eq_card_image_triNormSq] at hsub
  have h1 : ((triUtp m).image triNormSq).card ≤
      (triUtp m \ hexRedundant m).card :=
    (Finset.card_le_card (triUtp_image_subset_sdiff m)).trans Finset.card_image_le
  have hsdiff : (triUtp m \ hexRedundant m).card +
      (hexRedundant m).card = (triUtp m).card :=
    Finset.card_sdiff_add_card_eq_card (hexRedundant_subset_triUtp m)
  have hutp : (triUtp m).card ≤ u := (card_triUtp_le m).trans (le_of_eq hu)
  have hred : (hexRedundant m).card = r := (card_hexRedundant m).trans hr
  omega

theorem minimalDistinctDistances_12_le_5 : minimalDistinctDistances 12 ≤ 5 :=
  minimalDistinctDistances_hexCoords_le 4 1 3 12 5 0 (by omega) rfl rfl rfl

theorem minimalDistinctDistances_19_le_8 : minimalDistinctDistances 19 ≤ 8 :=
  minimalDistinctDistances_hexCoords_le 5 2 4 19 8 0 (by omega) rfl rfl rfl

theorem minimalDistinctDistances_27_le_11 : minimalDistinctDistances 27 ≤ 11 :=
  minimalDistinctDistances_hexCoords_le 6 2 5 27 11 0 (by omega) rfl rfl rfl

theorem minimalDistinctDistances_37_le_15 : minimalDistinctDistances 37 ≤ 15 :=
  minimalDistinctDistances_hexCoords_le 7 3 6 37 15 0 (by omega) rfl rfl rfl

theorem minimalDistinctDistances_48_le_19 : minimalDistinctDistances 48 ≤ 19 :=
  minimalDistinctDistances_hexCoords_le 8 3 7 48 19 0 (by omega) rfl rfl rfl

theorem minimalDistinctDistances_61_le_23 : minimalDistinctDistances 61 ≤ 23 :=
  minimalDistinctDistances_hexCoords_le 9 4 8 61 24 1 (by omega) rfl rfl rfl

theorem minimalDistinctDistances_75_le_28 : minimalDistinctDistances 75 ≤ 28 :=
  minimalDistinctDistances_hexCoords_le 10 4 9 75 29 1 (by omega) rfl rfl rfl

theorem minimalDistinctDistances_91_le_34 : minimalDistinctDistances 91 ≤ 34 :=
  minimalDistinctDistances_hexCoords_le 11 5 10 91 35 1 (by omega) rfl rfl rfl

theorem minimalDistinctDistances_108_le_39 : minimalDistinctDistances 108 ≤ 39 :=
  minimalDistinctDistances_hexCoords_le 12 5 11 108 41 2 (by omega) rfl rfl rfl

theorem minimalDistinctDistances_127_le_46 : minimalDistinctDistances 127 ≤ 46 :=
  minimalDistinctDistances_hexCoords_le 13 6 12 127 48 2 (by omega) rfl rfl rfl

theorem minimalDistinctDistances_147_le_52 : minimalDistinctDistances 147 ≤ 52 :=
  minimalDistinctDistances_hexCoords_le 14 6 13 147 55 3 (by omega) rfl rfl rfl

theorem minimalDistinctDistances_169_le_59 : minimalDistinctDistances 169 ≤ 59 :=
  minimalDistinctDistances_hexCoords_le 15 7 14 169 63 4 (by omega) rfl rfl rfl

theorem minimalDistinctDistances_192_le_66 : minimalDistinctDistances 192 ≤ 66 :=
  minimalDistinctDistances_hexCoords_le 16 7 15 192 71 5 (by omega) rfl rfl rfl

theorem minimalDistinctDistances_243_le_82 : minimalDistinctDistances 243 ≤ 82 :=
  minimalDistinctDistances_hexCoords_le 18 8 17 243 89 7 (by omega) rfl rfl rfl

theorem minimalDistinctDistances_300_le_99 : minimalDistinctDistances 300 ≤ 99 :=
  minimalDistinctDistances_hexCoords_le 20 9 19 300 109 10 (by omega) rfl rfl rfl

theorem minimalDistinctDistances_363_le_118 : minimalDistinctDistances 363 ≤ 118 :=
  minimalDistinctDistances_hexCoords_le 22 10 21 363 131 13 (by omega) rfl rfl rfl

theorem minimalDistinctDistances_432_le_138 : minimalDistinctDistances 432 ≤ 138 :=
  minimalDistinctDistances_hexCoords_le 24 11 23 432 155 17 (by omega) rfl rfl rfl

theorem minimalDistinctDistances_547_le_172 : minimalDistinctDistances 547 ≤ 172 :=
  minimalDistinctDistances_hexCoords_le 27 13 26 547 195 23 (by omega) rfl rfl rfl

theorem minimalDistinctDistances_721_le_222 : minimalDistinctDistances 721 ≤ 222 :=
  minimalDistinctDistances_hexCoords_le 31 15 30 721 255 33 (by omega) rfl rfl rfl

theorem minimalDistinctDistances_867_le_263 : minimalDistinctDistances 867 ≤ 263 :=
  minimalDistinctDistances_hexCoords_le 34 16 33 867 305 42 (by omega) rfl rfl rfl

/-- Folding map injecting `triUtp (2 * R)` into `(range (R + 1) ×ˢ range (R + 1)).erase (0, 0)`. -/
def triUtpFold (R : ℕ) (u : ℕ × ℕ) : ℕ × ℕ :=
  if u.2 ≤ R then u else (2 * R + 1 - u.2, u.1)

theorem mem_triUtp_iff (m : ℕ) (u : ℕ × ℕ) :
    u ∈ triUtp m ↔ u ≠ (0, 0) ∧ u.1 ≤ u.2 ∧ u.1 + u.2 ≤ m := by
  refine ⟨?_, fun ⟨h1, h2, h3⟩ => mem_triUtp_of_bounds m u h1 h2 h3⟩
  rcases u with ⟨x, y⟩
  intro hu
  unfold triUtp triUtpList
    triUtpRowList at hu
  rw [List.mem_toFinset, List.mem_flatMap] at hu
  obtain ⟨x0, hx0, hy0⟩ := hu
  rw [List.mem_map] at hy0
  obtain ⟨y0, hy0_mem, heq⟩ := hy0
  rw [List.mem_filter, List.mem_range, decide_eq_true_eq] at hy0_mem
  injection heq with hx hy
  subst hx; subst hy
  exact hy0_mem.2

/-- **Symbolic upper bound `(triUtp (2 * R)).card ≤ R * (R + 2)`** for all `R : ℕ`. -/
theorem card_triUtp_two_mul_le (R : ℕ) :
    (triUtp (2 * R)).card ≤ R * (R + 2) := by
  classical
  let Sq := (Finset.range (R + 1) ×ˢ Finset.range (R + 1)).erase (0, 0)
  have hmem0 : ((0, 0) : ℕ × ℕ) ∈ Finset.range (R + 1) ×ˢ Finset.range (R + 1) := by
    simp
  have hSq_card : Sq.card = R * (R + 2) := by
    have h1 := Finset.card_erase_add_one hmem0
    rw [Finset.card_product, Finset.card_range] at h1
    have hexp : (R + 1) * (R + 1) = R * (R + 2) + 1 := by ring
    dsimp [Sq]; omega
  have hinj : Set.InjOn (triUtpFold R) (triUtp (2 * R) : Set (ℕ × ℕ)) := by
    intro ⟨a1, b1⟩ h1 ⟨a2, b2⟩ h2 heq
    obtain ⟨_, hle1, hsum1⟩ := (mem_triUtp_iff (2 * R) (a1, b1)).mp h1
    obtain ⟨_, hle2, hsum2⟩ := (mem_triUtp_iff (2 * R) (a2, b2)).mp h2
    dsimp at hle1 hsum1 hle2 hsum2
    unfold triUtpFold at heq
    dsimp at heq
    split_ifs at heq with hb1 hb2 hb2'
    · exact heq
    · simp only [Prod.mk.injEq] at heq; omega
    · simp only [Prod.mk.injEq] at heq; omega
    · simp only [Prod.mk.injEq] at heq
      exact Prod.ext (by omega) (by omega)
  have hsub : (triUtp (2 * R)).image (triUtpFold R) ⊆ Sq := by
    intro x hx
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hne0, hle, hsum⟩ := (mem_triUtp_iff (2 * R) (a, b)).mp hab
    dsimp at hle hsum
    simp only [Sq, triUtpFold, Finset.mem_erase, Finset.mem_product, Finset.mem_range, ne_eq]
    split_ifs with hb
    · refine ⟨hne0, by omega, by omega⟩
    · refine ⟨?_, by omega, by omega⟩
      intro h0; simp only [Prod.mk.injEq] at h0; omega
  rw [← hSq_card, ← Finset.card_image_of_injOn hinj]
  exact Finset.card_le_card hsub

/-- Folding map injecting `(range (2R + 1) ×ˢ range (2R + 1)) \ hexCoords (2R + 1) R (2R)`
into `range R ×ˢ range (R + 1)`. -/
def hexCompFold (R : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  if p.1 + p.2 < R then p else (p.1 - R - 1, p.2 - R)

theorem mem_hexCoords_iff (k c m : ℕ) (p : ℕ × ℕ) :
    p ∈ hexCoords k c m ↔ p.1 < k ∧ p.2 < k ∧ c ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ c + m := by
  refine ⟨mem_hexCoords k c m p, ?_⟩
  rcases p with ⟨x, y⟩
  rintro ⟨hx, hy, hc1, hc2⟩
  dsimp at hx hy hc1 hc2
  unfold hexCoords hexCoordsList
    hexRowList
  rw [List.mem_toFinset, List.mem_flatMap]
  refine ⟨x, List.mem_range.mpr hx, List.mem_map.mpr ⟨y, ?_, rfl⟩⟩
  rw [List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨hy, hc1, hc2⟩

/-- **Symbolic lower bound `3 * R * (R + 1) + 1 ≤ (hexSet (2 * R + 1) R (2 * R)).card`** for all `R : ℕ`. -/
theorem three_mul_R_succ_add_one_le_card_hexSet (R : ℕ) :
    3 * R * (R + 1) + 1 ≤ (hexSet (2 * R + 1) R (2 * R)).card := by
  classical
  let Sq := Finset.range (2 * R + 1) ×ˢ Finset.range (2 * R + 1)
  let H := hexCoords (2 * R + 1) R (2 * R)
  let C := Sq \ H
  let Rect := Finset.range R ×ˢ Finset.range (R + 1)
  have hH_sub : H ⊆ Sq := by
    intro p hp
    obtain ⟨hx, hy, _, _⟩ := (mem_hexCoords_iff (2 * R + 1) R (2 * R) p).mp hp
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hx, Finset.mem_range.mpr hy⟩
  have hpart : C.card + H.card = (2 * R + 1) * (2 * R + 1) := by
    have h1 := Finset.card_sdiff_add_card_eq_card hH_sub
    rw [Finset.card_product, Finset.card_range] at h1
    exact h1
  have hRect_card : Rect.card = R * (R + 1) := by
    dsimp [Rect]; rw [Finset.card_product, Finset.card_range, Finset.card_range]
  have hinj : Set.InjOn (hexCompFold R) (C : Set (ℕ × ℕ)) := by
    intro ⟨x1, y1⟩ h1 ⟨x2, y2⟩ h2 heq
    have h1' : (x1, y1) ∈ Sq ∧ (x1, y1) ∉ H := Finset.mem_sdiff.mp h1
    have h2' : (x2, y2) ∈ Sq ∧ (x2, y2) ∉ H := Finset.mem_sdiff.mp h2
    simp only [Sq, H, mem_hexCoords_iff, Finset.mem_product, Finset.mem_range] at h1' h2'
    unfold hexCompFold at heq
    dsimp at heq
    split_ifs at heq with hs1 hs2 hs2'
    · exact heq
    · simp only [Prod.mk.injEq] at heq; omega
    · simp only [Prod.mk.injEq] at heq; omega
    · simp only [Prod.mk.injEq] at heq
      exact Prod.ext (by omega) (by omega)
  have hsub : C.image (hexCompFold R) ⊆ Rect := by
    intro z hz
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hz
    have hxy' : (x, y) ∈ Sq ∧ (x, y) ∉ H := Finset.mem_sdiff.mp hxy
    simp only [Sq, H, mem_hexCoords_iff, Finset.mem_product, Finset.mem_range] at hxy'
    simp only [Rect, hexCompFold, Finset.mem_product, Finset.mem_range]
    split_ifs with hs
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
  have hC_le : C.card ≤ R * (R + 1) := by
    rw [← hRect_card, ← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card hsub
  have hH_eq : (hexSet (2 * R + 1) R (2 * R)).card = H.card := by
    unfold hexSet; exact Finset.card_image_of_injective _ triPoint_injective
  have hexp : (2 * R + 1) * (2 * R + 1) = 3 * R * (R + 1) + 1 + R * (R + 1) := by ring
  omega

/-- **Master symbolic triangular-lattice regular hexagon theorem:**
for every `R : ℕ`, `minimalDistinctDistances (3 * R * (R + 1) + 1) ≤ R * (R + 2)`. -/
theorem minimalDistinctDistances_three_mul_R_succ_add_one_le (R : ℕ) :
    minimalDistinctDistances (3 * R * (R + 1) + 1) ≤ R * (R + 2) := by
  have hcard := three_mul_R_succ_add_one_le_card_hexSet R
  have hmono : minimalDistinctDistances (3 * R * (R + 1) + 1) ≤
      minimalDistinctDistances (hexSet (2 * R + 1) R (2 * R)).card :=
    MinimumMonotone91.minimum_monotone hcard
  have hmin : minimalDistinctDistances (hexSet (2 * R + 1) R (2 * R)).card ≤
      distinctDistances (hexSet (2 * R + 1) R (2 * R)) :=
    minimal_le (hexSet (2 * R + 1) R (2 * R)) _ rfl
  have hsub : distinctDistances (hexSet (2 * R + 1) R (2 * R)) ≤
      ((triUtp (2 * R)).image triNorm).card :=
    Finset.card_le_card (distanceSet_hexSet_subset (2 * R + 1) R (2 * R) (by omega))
  have himg : ((triUtp (2 * R)).image triNorm).card ≤ (triUtp (2 * R)).card :=
    Finset.card_image_le
  have hutp := card_triUtp_two_mul_le R
  omega

/-- **Universal `1 / 3` asymptotic upper bound on `minimalDistinctDistances n`:**
for every `n : ℕ`, `3 * minimalDistinctDistances n ≤ n + 12 * Nat.sqrt n + 9`
(lowering the leading slope from `0.454958` down to `1 / 3 = 0.333333`). -/
theorem minimalDistinctDistances_mul_three_le (n : ℕ) :
    3 * minimalDistinctDistances n ≤ n + 12 * Nat.sqrt n + 9 := by
  let m := n / 3
  let q := Nat.sqrt m
  let R := q + 1
  have hq_le_m : q * q ≤ m := Nat.sqrt_le m
  have hm_lt : m < R * R := Nat.lt_succ_sqrt m
  have hn_le : n ≤ 3 * R * (R + 1) + 1 := by
    have : R * R = q * q + 2 * q + 1 := by dsimp [R]; ring
    have : 3 * R * (R + 1) + 1 = 3 * (q * q) + 9 * q + 7 := by dsimp [R]; ring
    omega
  have hq_le_sqrt : q ≤ Nat.sqrt n := Nat.sqrt_le_sqrt (by omega)
  have hmono : minimalDistinctDistances n ≤ minimalDistinctDistances (3 * R * (R + 1) + 1) :=
    MinimumMonotone91.minimum_monotone hn_le
  have hhex := minimalDistinctDistances_three_mul_R_succ_add_one_le R
  have hexp : 3 * (R * (R + 2)) = 3 * (q * q) + 12 * q + 9 := by dsimp [R]; ring
  omega

theorem two_mul_minimalDistinctDistances_lt_of_ge_40 (n : ℕ) (hn : 40 ≤ n) :
    2 * minimalDistinctDistances n < n - 1 := by
  by_cases h48 : n ≤ 48
  · have hd := (MinimumMonotone91.minimum_monotone h48).trans minimalDistinctDistances_48_le_19; omega
  · by_cases h61 : n ≤ 61
    · have hd := (MinimumMonotone91.minimum_monotone h61).trans minimalDistinctDistances_61_le_23; omega
    · by_cases h75 : n ≤ 75
      · have hd := (MinimumMonotone91.minimum_monotone h75).trans minimalDistinctDistances_75_le_28; omega
      · by_cases h91 : n ≤ 91
        · have hd := (MinimumMonotone91.minimum_monotone h91).trans minimalDistinctDistances_91_le_34; omega
        · by_cases h108 : n ≤ 108
          · have hd := (MinimumMonotone91.minimum_monotone h108).trans minimalDistinctDistances_108_le_39; omega
          · by_cases h127 : n ≤ 127
            · have hd := (MinimumMonotone91.minimum_monotone h127).trans minimalDistinctDistances_127_le_46; omega
            · by_cases h169 : n ≤ 169
              · have hd := (MinimumMonotone91.minimum_monotone h169).trans minimalDistinctDistances_169_le_59; omega
              · by_cases h243 : n ≤ 243
                · have hd := (MinimumMonotone91.minimum_monotone h243).trans minimalDistinctDistances_243_le_82; omega
                · by_cases h363 : n ≤ 363
                  · have hd := (MinimumMonotone91.minimum_monotone h363).trans minimalDistinctDistances_363_le_118; omega
                  · by_cases h547 : n ≤ 547
                    · have hd := (MinimumMonotone91.minimum_monotone h547).trans minimalDistinctDistances_547_le_172; omega
                    · by_cases h721 : n ≤ 721
                      · have hd := (MinimumMonotone91.minimum_monotone h721).trans minimalDistinctDistances_721_le_222; omega
                      · have hd := minimalDistinctDistances_mul_three_le n
                        let q := Nat.sqrt n
                        have hq26 : 26 ≤ q := Nat.le_sqrt.mpr (by omega)
                        have hq_sq : q * q ≤ n := Nat.sqrt_le n
                        have h26q : 26 * q ≤ q * q := Nat.mul_le_mul_right q hq26
                        omega
/-- **Unconditional one-step plateau nonuniqueness for all `n ≥ 40`:**
if `40 ≤ n` and `d(n) = d(n + 1)`, then `¬ UniqueMinimizer n`. -/
theorem unconditional_plateau_not_unique_40 (n : ℕ) (hn : 40 ≤ n)
    (hplat : minimalDistinctDistances n = minimalDistinctDistances (n + 1)) :
    ¬ UniqueMinimizer n := by
  have hlt := two_mul_minimalDistinctDistances_lt_of_ge_40 n hn
  exact PlateauNonunique91.low_distance_plateau_not_unique n (by omega) hplat hlt

theorem uniqueMinimizer_imp_strict_rise_40 (n : ℕ) (hn : 40 ≤ n)
    (huniq : UniqueMinimizer n) :
    minimalDistinctDistances n < minimalDistinctDistances (n + 1) := by
  have hle : minimalDistinctDistances n ≤ minimalDistinctDistances (n + 1) :=
    MinimumMonotone91.minimum_monotone (by omega)
  have hne : minimalDistinctDistances n ≠ minimalDistinctDistances (n + 1) :=
    fun heq => unconditional_plateau_not_unique_40 n hn heq huniq
  omega

theorem uniqueMinimizer_count_le_40 (N : ℕ) (hN : 40 ≤ N)
    (E : Finset ℕ) (hE : E ⊆ Icc 40 N)
    (huniq : ∀ n ∈ E, UniqueMinimizer n) :
    E.card + minimalDistinctDistances 40 ≤ minimalDistinctDistances (N + 1) := by
  have hle : E.card ≤ minimalDistinctDistances (N + 1) - minimalDistinctDistances 40 := by
    apply OneStepCount91.card_le minimalDistinctDistances
      MinimumMonotone91.minimum_monotone E 40 N hE
    intro n hn
    have hn_ge : 40 ≤ n := (mem_Icc.mp (hE hn)).1
    exact uniqueMinimizer_imp_strict_rise_40 n hn_ge (huniq n hn)
  have hmono : minimalDistinctDistances 40 ≤ minimalDistinctDistances (N + 1) :=
    MinimumMonotone91.minimum_monotone (by omega)
  omega

theorem uniqueMinimizer_count_Icc_24_27
    (E : Finset ℕ) (hE : E ⊆ Icc 24 27)
    (huniq : ∀ n ∈ E, UniqueMinimizer n) :
    E.card + minimalDistinctDistances 24 ≤ minimalDistinctDistances 28 := by
  have hle : E.card ≤ minimalDistinctDistances (27 + 1) - minimalDistinctDistances 24 := by
    apply OneStepCount91.card_le minimalDistinctDistances
      MinimumMonotone91.minimum_monotone E 24 27 hE
    intro n hn
    have h := mem_Icc.mp (hE hn)
    have hd : minimalDistinctDistances n ≤ 11 :=
      (MinimumMonotone91.minimum_monotone h.2).trans minimalDistinctDistances_27_le_11
    have hlt : 2 * minimalDistinctDistances n < n - 1 := by omega
    have hle1 : minimalDistinctDistances n ≤ minimalDistinctDistances (n + 1) :=
      MinimumMonotone91.minimum_monotone (by omega)
    have hne : minimalDistinctDistances n ≠ minimalDistinctDistances (n + 1) :=
      fun heq => PlateauNonunique91.low_distance_plateau_not_unique n (by omega) heq hlt (huniq n hn)
    omega
  have hmono : minimalDistinctDistances 24 ≤ minimalDistinctDistances (27 + 1) :=
    MinimumMonotone91.minimum_monotone (by omega)
  change E.card + minimalDistinctDistances 24 ≤ minimalDistinctDistances (27 + 1)
  omega

theorem uniqueMinimizer_count_Icc_32_37
    (E : Finset ℕ) (hE : E ⊆ Icc 32 37)
    (huniq : ∀ n ∈ E, UniqueMinimizer n) :
    E.card + minimalDistinctDistances 32 ≤ minimalDistinctDistances 38 := by
  have hle : E.card ≤ minimalDistinctDistances (37 + 1) - minimalDistinctDistances 32 := by
    apply OneStepCount91.card_le minimalDistinctDistances
      MinimumMonotone91.minimum_monotone E 32 37 hE
    intro n hn
    have h := mem_Icc.mp (hE hn)
    have hd : minimalDistinctDistances n ≤ 15 :=
      (MinimumMonotone91.minimum_monotone h.2).trans minimalDistinctDistances_37_le_15
    have hlt : 2 * minimalDistinctDistances n < n - 1 := by omega
    have hle1 : minimalDistinctDistances n ≤ minimalDistinctDistances (n + 1) :=
      MinimumMonotone91.minimum_monotone (by omega)
    have hne : minimalDistinctDistances n ≠ minimalDistinctDistances (n + 1) :=
      fun heq => PlateauNonunique91.low_distance_plateau_not_unique n (by omega) heq hlt (huniq n hn)
    omega
  have hmono : minimalDistinctDistances 32 ≤ minimalDistinctDistances (37 + 1) :=
    MinimumMonotone91.minimum_monotone (by omega)
  change E.card + minimalDistinctDistances 32 ≤ minimalDistinctDistances (37 + 1)
  omega

/-- Splicing `[24, 28)` (1-step), `[28, 32)` (4-element even gap), `[32, 38)` (1-step),
and `[38, 40)` (2-element even gap) proves `E.card + d(24) ≤ 3 + d(40)`. -/
theorem uniqueMinimizer_Ico_24_40_card_add_le
    (E : Finset ℕ) (hE : E ⊆ Ico 24 40)
    (huniq : ∀ n ∈ E, UniqueMinimizer n) :
    E.card + minimalDistinctDistances 24 ≤ 3 + minimalDistinctDistances 40 := by
  classical
  let E1 := E.filter (fun n => n < 32)
  let E2 := E.filter (fun n => ¬ n < 32)
  have hp12 : E1.card + E2.card = E.card :=
    card_filter_add_card_filter_not (s := E) (p := fun n => n < 32)
  let E1a := E1.filter (fun n => n < 28)
  let E1b := E1.filter (fun n => ¬ n < 28)
  have hp1ab : E1a.card + E1b.card = E1.card :=
    card_filter_add_card_filter_not (s := E1) (p := fun n => n < 28)
  let E2a := E2.filter (fun n => n < 38)
  let E2b := E2.filter (fun n => ¬ n < 38)
  have hp2ab : E2a.card + E2b.card = E2.card :=
    card_filter_add_card_filter_not (s := E2) (p := fun n => n < 38)
  have h1a : E1a.card + minimalDistinctDistances 24 ≤ minimalDistinctDistances 28 := by
    apply uniqueMinimizer_count_Icc_24_27 E1a
    · intro n hn
      obtain ⟨hn1, hlt⟩ := mem_filter.mp hn
      obtain ⟨hnE, _⟩ := mem_filter.mp hn1
      have h := mem_Ico.mp (hE hnE)
      exact mem_Icc.mpr ⟨h.1, by omega⟩
    · intro n hn
      exact huniq n (mem_filter.mp (mem_filter.mp hn).1).1
  have h1b : E1b.card + minimalDistinctDistances 28 ≤ 2 + minimalDistinctDistances (28 + 2 * 2) := by
    apply uniqueMinimizer_even_gap_card_add_le 2 28 (by omega) E1b
    · intro n hn
      obtain ⟨hn1, hge⟩ := mem_filter.mp hn
      obtain ⟨hnE, hlt⟩ := mem_filter.mp hn1
      exact mem_Ico.mpr ⟨by omega, by omega⟩
    · intro n hn
      exact huniq n (mem_filter.mp (mem_filter.mp hn).1).1
  have h2a : E2a.card + minimalDistinctDistances 32 ≤ minimalDistinctDistances 38 := by
    apply uniqueMinimizer_count_Icc_32_37 E2a
    · intro n hn
      obtain ⟨hn2, hlt⟩ := mem_filter.mp hn
      obtain ⟨hnE, hge⟩ := mem_filter.mp hn2
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro n hn
      exact huniq n (mem_filter.mp (mem_filter.mp hn).1).1
  have h2b : E2b.card + minimalDistinctDistances 38 ≤ 1 + minimalDistinctDistances (38 + 2) := by
    apply uniqueMinimizer_two_step_gap_card_add_le 38 (by omega) E2b
    · intro n hn
      obtain ⟨hn2, hge⟩ := mem_filter.mp hn
      obtain ⟨hnE, _⟩ := mem_filter.mp hn2
      have h := mem_Ico.mp (hE hnE)
      exact mem_Ico.mpr ⟨by omega, by omega⟩
    · intro n hn
      exact huniq n (mem_filter.mp (mem_filter.mp hn).1).1
  change E1b.card + minimalDistinctDistances 28 ≤ 2 + minimalDistinctDistances 32 at h1b
  change E2b.card + minimalDistinctDistances 38 ≤ 1 + minimalDistinctDistances 40 at h2b
  omega

theorem uniqueMinimizer_prefix_40_card_le_12
    (E : Finset ℕ) (hE : E ⊆ range 40)
    (huniq : ∀ n ∈ E, UniqueMinimizer n) :
    E.card ≤ 12 + minimalDistinctDistances 40 := by
  classical
  let E_lo := E.filter (fun n => n < 24)
  let E_hi := E.filter (fun n => ¬ n < 24)
  have hpart : E_lo.card + E_hi.card = E.card :=
    card_filter_add_card_filter_not (s := E) (p := fun n => n < 24)
  have hlo_sub : E_lo ⊆ range 24 := by
    intro n hn
    exact mem_range.mpr (mem_filter.mp hn).2
  have hlo_uniq : ∀ n ∈ E_lo, UniqueMinimizer n :=
    fun n hn => huniq n (mem_filter.mp hn).1
  have hlo := uniqueMinimizer_prefix_card_add_two_le 24 (by omega) E_lo hlo_sub hlo_uniq
  have hd25 : minimalDistinctDistances (24 + 1) ≤ 11 :=
    (MinimumMonotone91.minimum_monotone (by omega : 24 + 1 ≤ 27)).trans
      minimalDistinctDistances_27_le_11
  have hhi_sub : E_hi ⊆ Ico 24 40 := by
    intro n hn
    obtain ⟨hnE, hge⟩ := mem_filter.mp hn
    exact mem_Ico.mpr ⟨by omega, mem_range.mp (hE hnE)⟩
  have hhi_uniq : ∀ n ∈ E_hi, UniqueMinimizer n :=
    fun n hn => huniq n (mem_filter.mp hn).1
  have hhi := uniqueMinimizer_Ico_24_40_card_add_le E_hi hhi_sub hhi_uniq
  omega

theorem uniqueMinimizer_prefix_38_card_le_12
    (E : Finset ℕ) (hE : E ⊆ range 38)
    (huniq : ∀ n ∈ E, UniqueMinimizer n) :
    E.card ≤ 12 + minimalDistinctDistances 38 := by
  classical
  let E_lo := E.filter (fun n => n < 34)
  let E_hi := E.filter (fun n => ¬ n < 34)
  have hpart : E_lo.card + E_hi.card = E.card :=
    card_filter_add_card_filter_not (s := E) (p := fun n => n < 34)
  have hlo_sub : E_lo ⊆ range 34 := by
    intro n hn
    exact mem_range.mpr (mem_filter.mp hn).2
  have hlo_uniq : ∀ n ∈ E_lo, UniqueMinimizer n :=
    fun n hn => huniq n (mem_filter.mp hn).1
  have hlo := uniqueMinimizer_prefix_card_add_three_le 34 (by omega) E_lo hlo_sub hlo_uniq
  have hd35 : minimalDistinctDistances (34 + 1) ≤ 15 :=
    (MinimumMonotone91.minimum_monotone (by omega : 34 + 1 ≤ 37)).trans
      minimalDistinctDistances_37_le_15
  have hhi_step : E_hi.card ≤ minimalDistinctDistances (37 + 1) - minimalDistinctDistances 34 := by
    apply OneStepCount91.card_le minimalDistinctDistances
      MinimumMonotone91.minimum_monotone E_hi 34 37
    · intro n hn
      obtain ⟨hnE, hge⟩ := mem_filter.mp hn
      have hn_lt : n < 38 := mem_range.mp (hE hnE)
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro n hn
      obtain ⟨hnE, hge⟩ := mem_filter.mp hn
      have hn_lt : n < 38 := mem_range.mp (hE hnE)
      have hd : minimalDistinctDistances n ≤ 15 :=
        (MinimumMonotone91.minimum_monotone (by omega : n ≤ 37)).trans minimalDistinctDistances_37_le_15
      have hlt : 2 * minimalDistinctDistances n < n - 1 := by omega
      have hle1 : minimalDistinctDistances n ≤ minimalDistinctDistances (n + 1) :=
        MinimumMonotone91.minimum_monotone (by omega)
      have hne : minimalDistinctDistances n ≠ minimalDistinctDistances (n + 1) :=
        fun heq => PlateauNonunique91.low_distance_plateau_not_unique n (by omega) heq hlt (huniq n hnE)
      omega
  have hmono : minimalDistinctDistances 34 ≤ minimalDistinctDistances (37 + 1) :=
    MinimumMonotone91.minimum_monotone (by omega)
  change E.card ≤ 12 + minimalDistinctDistances (37 + 1)
  omega

/-- **Sharpened global uniqueness-exception bound (`≤ 13 + d(N + 1)`):**
for EVERY `N : ℕ`, `(uniqueMinimizerSet N).card ≤ 13 + minimalDistinctDistances (N + 1)`
(cutting the global additive constant from `58` down to `13`). -/
theorem uniqueMinimizerSet_card_le_13_add (N : ℕ) :
    (uniqueMinimizerSet N).card ≤ 13 + minimalDistinctDistances (N + 1) := by
  classical
  have hU_sub : uniqueMinimizerSet N ⊆ range (N + 1) := filter_subset _ _
  have huniq : ∀ n ∈ uniqueMinimizerSet N, UniqueMinimizer n :=
    fun n hn => (mem_filter.mp hn).2
  by_cases hN40 : N < 40
  · by_cases hN19 : N < 19
    · by_cases hN13 : N < 13
      · have hs13 : uniqueMinimizerSet N ⊆ range 13 := by
          intro n hn
          have hn_lt : n < N + 1 := mem_range.mp (hU_sub hn)
          exact mem_range.mpr (by omega)
        have hle13 : (uniqueMinimizerSet N).card ≤ 13 := by
          simpa using card_le_card hs13
        omega
      · have hs19 : uniqueMinimizerSet N ⊆ range 19 := by
          intro n hn
          have hn_lt : n < N + 1 := mem_range.mp (hU_sub hn)
          exact mem_range.mpr (by omega)
        let E_lo := (uniqueMinimizerSet N).filter (fun n => n < 8)
        let E_hi := (uniqueMinimizerSet N).filter (fun n => ¬ n < 8)
        have hpart : E_lo.card + E_hi.card = (uniqueMinimizerSet N).card :=
          card_filter_add_card_filter_not (s := uniqueMinimizerSet N) (p := fun n => n < 8)
        have hlo5 : E_lo.card ≤ 5 :=
          Erdos91.SharpenedTelescopingAndPrefixBounds.uniqueMinimizer_filter_lt_eight_card_le_five
            (uniqueMinimizerSet N) huniq
        have hhi_sub : E_hi ⊆ Ico 8 19 := by
          intro n hn
          obtain ⟨hnU, hge⟩ := mem_filter.mp hn
          exact mem_Ico.mpr ⟨by omega, mem_range.mp (hs19 hnU)⟩
        have hhi11 : E_hi.card ≤ 19 - 8 := by
          simpa using card_le_card hhi_sub
        have hd3 : 3 ≤ minimalDistinctDistances (N + 1) :=
          Erdos91.UnconditionalEightNineDichotomy.three_le_minimalDistinctDistances_eight.trans
            (MinimumMonotone91.minimum_monotone (by omega))
        omega
    · by_cases hN36 : N < 36
      · have hp2 := uniqueMinimizer_prefix_card_add_two_le (N + 1) (by omega)
          (uniqueMinimizerSet N) hU_sub huniq
        have hd37 : minimalDistinctDistances (N + 1 + 1) ≤ 15 :=
          (MinimumMonotone91.minimum_monotone (by omega : N + 1 + 1 ≤ 37)).trans
            minimalDistinctDistances_37_le_15
        omega
      · by_cases hN36_eq : N = 36
        · subst hN36_eq
          let E_lo := (uniqueMinimizerSet 36).filter (fun n => n < 34)
          let E_hi := (uniqueMinimizerSet 36).filter (fun n => ¬ n < 34)
          have hpart : E_lo.card + E_hi.card = (uniqueMinimizerSet 36).card :=
            card_filter_add_card_filter_not (s := uniqueMinimizerSet 36) (p := fun n => n < 34)
          have hlo_sub : E_lo ⊆ range 34 := by
            intro n hn
            exact mem_range.mpr (mem_filter.mp hn).2
          have hlo_uniq : ∀ n ∈ E_lo, UniqueMinimizer n :=
            fun n hn => huniq n (mem_filter.mp hn).1
          have hlo := uniqueMinimizer_prefix_card_add_three_le 34 (by omega) E_lo hlo_sub hlo_uniq
          have hd35 : minimalDistinctDistances (34 + 1) ≤ 15 :=
            (MinimumMonotone91.minimum_monotone (by omega : 34 + 1 ≤ 37)).trans
              minimalDistinctDistances_37_le_15
          have hhi_step : E_hi.card ≤ minimalDistinctDistances (36 + 1) - minimalDistinctDistances 34 := by
            apply OneStepCount91.card_le minimalDistinctDistances
              MinimumMonotone91.minimum_monotone E_hi 34 36
            · intro n hn
              obtain ⟨hnU, hge⟩ := mem_filter.mp hn
              have hn_lt : n < 37 := mem_range.mp (hU_sub hnU)
              exact mem_Icc.mpr ⟨by omega, by omega⟩
            · intro n hn
              obtain ⟨hnU, hge⟩ := mem_filter.mp hn
              have hn_lt : n < 37 := mem_range.mp (hU_sub hnU)
              have hd : minimalDistinctDistances n ≤ 15 :=
                (MinimumMonotone91.minimum_monotone (by omega : n ≤ 37)).trans minimalDistinctDistances_37_le_15
              have hlt : 2 * minimalDistinctDistances n < n - 1 := by omega
              have hle1 : minimalDistinctDistances n ≤ minimalDistinctDistances (n + 1) :=
                MinimumMonotone91.minimum_monotone (by omega)
              have hne : minimalDistinctDistances n ≠ minimalDistinctDistances (n + 1) :=
                fun heq => PlateauNonunique91.low_distance_plateau_not_unique n (by omega) heq hlt (huniq n hnU)
              omega
          have hmono : minimalDistinctDistances 34 ≤ minimalDistinctDistances (36 + 1) :=
            MinimumMonotone91.minimum_monotone (by omega)
          change (uniqueMinimizerSet 36).card ≤ 13 + minimalDistinctDistances (36 + 1)
          omega
        · by_cases hN37_eq : N = 37
          · subst hN37_eq
            have hpref := uniqueMinimizer_prefix_38_card_le_12 (uniqueMinimizerSet 37) hU_sub huniq
            change (uniqueMinimizerSet 37).card ≤ 13 + minimalDistinctDistances 38
            omega
          · by_cases hN38_eq : N = 38
            · subst hN38_eq
              let E_lo := (uniqueMinimizerSet 38).filter (fun n => n < 38)
              let E_hi := (uniqueMinimizerSet 38).filter (fun n => ¬ n < 38)
              have hpart : E_lo.card + E_hi.card = (uniqueMinimizerSet 38).card :=
                card_filter_add_card_filter_not (s := uniqueMinimizerSet 38) (p := fun n => n < 38)
              have hlo_sub : E_lo ⊆ range 38 := by
                intro n hn; exact mem_range.mpr (mem_filter.mp hn).2
              have hlo_uniq : ∀ n ∈ E_lo, UniqueMinimizer n :=
                fun n hn => huniq n (mem_filter.mp hn).1
              have hlo := uniqueMinimizer_prefix_38_card_le_12 E_lo hlo_sub hlo_uniq
              have hhi_sub : E_hi ⊆ Ico 38 39 := by
                intro n hn
                obtain ⟨hnU, hge⟩ := mem_filter.mp hn
                have hn_lt : n < 39 := mem_range.mp (hU_sub hnU)
                exact mem_Ico.mpr ⟨by omega, hn_lt⟩
              have hhi1 : E_hi.card ≤ 39 - 38 := by
                simpa using card_le_card hhi_sub
              have hd38_39 : minimalDistinctDistances 38 ≤ minimalDistinctDistances (38 + 1) :=
                MinimumMonotone91.minimum_monotone (by omega)
              omega
            · have hN39 : N = 39 := by omega
              subst hN39
              have hpref := uniqueMinimizer_prefix_40_card_le_12 (uniqueMinimizerSet 39) hU_sub huniq
              change (uniqueMinimizerSet 39).card ≤ 13 + minimalDistinctDistances 40
              omega
  · let E_lo := (uniqueMinimizerSet N).filter (fun n => n < 40)
    let E_hi := (uniqueMinimizerSet N).filter (fun n => ¬ n < 40)
    have hpart : E_lo.card + E_hi.card = (uniqueMinimizerSet N).card :=
      card_filter_add_card_filter_not (s := uniqueMinimizerSet N) (p := fun n => n < 40)
    have hlo_sub : E_lo ⊆ range 40 := by
      intro n hn
      exact mem_range.mpr (mem_filter.mp hn).2
    have hlo_uniq : ∀ n ∈ E_lo, UniqueMinimizer n :=
      fun n hn => huniq n (mem_filter.mp hn).1
    have hlo := uniqueMinimizer_prefix_40_card_le_12 E_lo hlo_sub hlo_uniq
    have hhi_sub : E_hi ⊆ Icc 40 N := by
      intro n hn
      obtain ⟨hnU, hge⟩ := mem_filter.mp hn
      have hn_lt : n < N + 1 := mem_range.mp (hU_sub hnU)
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    have hhi_uniq : ∀ n ∈ E_hi, UniqueMinimizer n :=
      fun n hn => huniq n (mem_filter.mp hn).1
    have hhi := uniqueMinimizer_count_le_40 N (by omega) E_hi hhi_sub hhi_uniq
    omega

theorem unconditional_majority_nonunique_of_ge_130
    (N : ℕ) (hN : 130 ≤ N) :
    2 * (uniqueMinimizerSet N).card < N + 1 := by
  have hu := uniqueMinimizerSet_card_le_13_add N
  by_cases h146 : N ≤ 146
  · have hd := (MinimumMonotone91.minimum_monotone (by omega : N + 1 ≤ 147)).trans minimalDistinctDistances_147_le_52; omega
  · by_cases h168 : N ≤ 168
    · have hd := (MinimumMonotone91.minimum_monotone (by omega : N + 1 ≤ 169)).trans minimalDistinctDistances_169_le_59; omega
    · by_cases h191 : N ≤ 191
      · have hd := (MinimumMonotone91.minimum_monotone (by omega : N + 1 ≤ 192)).trans minimalDistinctDistances_192_le_66; omega
      · by_cases h242 : N ≤ 242
        · have hd := (MinimumMonotone91.minimum_monotone (by omega : N + 1 ≤ 243)).trans minimalDistinctDistances_243_le_82; omega
        · by_cases h299 : N ≤ 299
          · have hd := (MinimumMonotone91.minimum_monotone (by omega : N + 1 ≤ 300)).trans minimalDistinctDistances_300_le_99; omega
          · by_cases h362 : N ≤ 362
            · have hd := (MinimumMonotone91.minimum_monotone (by omega : N + 1 ≤ 363)).trans minimalDistinctDistances_363_le_118; omega
            · by_cases h431 : N ≤ 431
              · have hd := (MinimumMonotone91.minimum_monotone (by omega : N + 1 ≤ 432)).trans minimalDistinctDistances_432_le_138; omega
              · by_cases h546 : N ≤ 546
                · have hd := (MinimumMonotone91.minimum_monotone (by omega : N + 1 ≤ 547)).trans minimalDistinctDistances_547_le_172; omega
                · by_cases h720 : N ≤ 720
                  · have hd := (MinimumMonotone91.minimum_monotone (by omega : N + 1 ≤ 721)).trans minimalDistinctDistances_721_le_222; omega
                  · by_cases h866 : N ≤ 866
                    · have hd := (MinimumMonotone91.minimum_monotone (by omega : N + 1 ≤ 867)).trans minimalDistinctDistances_867_le_263; omega
                    · have hd := minimalDistinctDistances_mul_three_le (N + 1)
                      let q := Nat.sqrt (N + 1)
                      have hq29 : 29 ≤ q := Nat.le_sqrt.mpr (by omega)
                      have hq_sq : q * q ≤ N + 1 := Nat.sqrt_le (N + 1)
                      have h29q : 29 * q ≤ q * q := Nat.mul_le_mul_right q hq29
                      omega

theorem one_le_goodMultiplicitySet_three_35 :
    1 ≤ (goodMultiplicitySet 3 35).card := by
  have hpart := good_add_badMultiplicitySet_card 3 35
  have hb := badMultiplicitySet_three_card_le_five_add 35
  have hd1 := (MinimumMonotone91.minimum_monotone (by omega : 35 + 1 ≤ 37)).trans minimalDistinctDistances_37_le_15
  have hd2 : minimalDistinctDistances (35 + 2) ≤ 15 := minimalDistinctDistances_37_le_15
  omega

theorem exists_le_35_has_three_minimizers :
    ∃ n ≤ 35, HasAtLeastKNonsimilarMinimizers 3 n := by
  have h := one_le_goodMultiplicitySet_three_35
  exact exists_le_of_goodMultiplicitySet_pos (by omega)

end Erdos91.TriangularLatticeHexagonAndSub130Majority

namespace Erdos91.SymbolicTriangularHexagonAndSub7KSquaredBound
open Finset Minimizer91 PlateauDefinitions91
open Erdos91.GeneralMultiplicityAndDensityOne (HasAtLeastKNonsimilarMinimizers)
open Erdos91.AsymptoticDensityOneAndGlobalBounds (uniqueMinimizerSet badMultiplicitySet goodMultiplicitySet good_add_badMultiplicitySet_card)
open Erdos91.EquivalenceTwoMinimizersAndGeneralKFlatRises (hasAtLeastTwoMinimizers_four_six_seven)
open Erdos91.QuadraticTwoDeletionMultiplicity (badMultiplicitySet_card_le_quadratic_unconditional)
open Erdos91.ConcreteMultiplicityBenchmarks322And398 (exists_le_of_goodMultiplicitySet_pos)
open Erdos91.SharpenedTelescopingAndPrefixBounds (badMultiplicitySet_card_add_two_mul_le_of_ge)
open Erdos91.SharpenedFirstOccurrenceAnd36KSquaredBound (hasAtLeastOneMinimizer)
open Erdos91.TriangularLatticeHexagonAndSub130Majority (triPoint triPoint_injective triNorm hexCoords hexSet mem_hexCoords triUtp distanceSet_hexSet_subset uniqueMinimizerSet_card_le_13_add exists_le_35_has_three_minimizers triUtpFold mem_triUtp_iff card_triUtp_two_mul_le hexCompFold mem_hexCoords_iff three_mul_R_succ_add_one_le_card_hexSet minimalDistinctDistances_three_mul_R_succ_add_one_le minimalDistinctDistances_mul_three_le)

end Erdos91.SymbolicTriangularHexagonAndSub7KSquaredBound
namespace Erdos91.EisensteinSevenCollisionFamilyAndSub6KSquaredBound
open Finset Minimizer91 PlateauDefinitions91
open Erdos91.GeneralMultiplicityAndDensityOne (HasAtLeastKNonsimilarMinimizers)
open Erdos91.AsymptoticDensityOneAndGlobalBounds (uniqueMinimizerSet badMultiplicitySet goodMultiplicitySet good_add_badMultiplicitySet_card)
open Erdos91.EquivalenceTwoMinimizersAndGeneralKFlatRises (hasAtLeastTwoMinimizers_four_six_seven)
open Erdos91.QuadraticTwoDeletionMultiplicity (badMultiplicitySet_card_le_quadratic_unconditional)
open Erdos91.ConcreteMultiplicityBenchmarks322And398 (exists_le_of_goodMultiplicitySet_pos)
open Erdos91.SharpenedTelescopingAndPrefixBounds (badMultiplicitySet_card_add_two_mul_le_of_ge)
open Erdos91.SharpenedFirstOccurrenceAnd36KSquaredBound (hasAtLeastOneMinimizer)
open Erdos91.TriangularLatticeHexagonAndSub130Majority (triNorm triNormSq hexSet triUtp distanceSet_hexSet_subset uniqueMinimizerSet_card_le_13_add exists_le_35_has_three_minimizers)
open Erdos91.TriangularLatticeHexagonAndSub130Majority (mem_triUtp_iff card_triUtp_two_mul_le three_mul_R_succ_add_one_le_card_hexSet minimalDistinctDistances_three_mul_R_succ_add_one_le)

/-- First Eisenstein `7 = (2 - ω)(3 + ω)` collision map (deleted branch in `b < 4a`):
`eisU (b, m) = (3b + m, 5b + 4m)`. -/
def eisU (bm : ℕ × ℕ) : ℕ × ℕ :=
  (3 * bm.1 + bm.2, 5 * bm.1 + 4 * bm.2)

/-- Second Eisenstein `7 = (2 - ω)(3 + ω)` collision map (kept branch in `4a < b`):
`eisV (b, m) = (m, 7b + 4m)`. -/
def eisV (bm : ℕ × ℕ) : ℕ × ℕ :=
  (bm.2, 7 * bm.1 + 4 * bm.2)

theorem eisU_injective : Function.Injective eisU := by
  intro ⟨b1, m1⟩ ⟨b2, m2⟩ h
  simp only [eisU, Prod.mk.injEq] at h
  ext <;> omega

/-- Equal Eisenstein norms `triNorm (eisU bm) = triNorm (eisV bm)`. -/
theorem triNorm_eisU_eq_eisV (bm : ℕ × ℕ) :
    triNorm (eisU bm) = triNorm (eisV bm) := by
  unfold triNorm triNormSq eisU eisV
  dsimp
  congr 1
  push_cast
  ring

abbrev eisPred (R : ℕ) (bm : ℕ × ℕ) : Prop :=
  8 * bm.1 + 5 * bm.2 < 2 * R + 1

def eisTriangle (R s M : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ico 1 (s + 1) ×ˢ Finset.range M).filter (eisPred R)

def eisFlip (s M : ℕ) (bm : ℕ × ℕ) : ℕ × ℕ :=
  (s + 1 - bm.1, M - 1 - bm.2)

theorem card_eisTriangle_mul_two_ge (R s M : ℕ)
    (hsum : 8 * s + 5 * M + 3 < 4 * R + 2) :
    s * M ≤ 2 * (eisTriangle R s M).card := by
  classical
  let B := Finset.Ico 1 (s + 1) ×ˢ Finset.range M
  let T := B.filter (eisPred R)
  let F := B.filter (fun bm => ¬ eisPred R bm)
  have hBcard : B.card = s * M := by
    dsimp [B]
    rw [Finset.card_product, Nat.card_Ico, Finset.card_range]
    have : s + 1 - 1 = s := by omega
    rw [this]
  have hTF : T.card + F.card = s * M := by
    have h := Finset.card_filter_add_card_filter_not (s := B) (p := eisPred R)
    simpa only [T, F, hBcard] using h
  have hinj : Set.InjOn (eisFlip s M) (F : Set (ℕ × ℕ)) := by
    intro ⟨b1, m1⟩ h1 ⟨b2, m2⟩ h2 heq
    have hb1 : (b1, m1) ∈ B := (Finset.mem_filter.mp h1).1
    have hb2 : (b2, m2) ∈ B := (Finset.mem_filter.mp h2).1
    simp only [B, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hb1 hb2
    simp only [eisFlip, Prod.mk.injEq] at heq
    exact Prod.ext (by omega) (by omega)
  have hsub : F.image (eisFlip s M) ⊆ T := by
    intro x hx
    obtain ⟨⟨b, m⟩, hbmF, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hbmB, hnotP⟩ := Finset.mem_filter.mp hbmF
    simp only [B, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hbmB
    simp only [eisPred, not_lt] at hnotP
    simp only [T, B, eisPred, eisFlip,
      Finset.mem_filter, Finset.mem_product, Finset.mem_Ico, Finset.mem_range]
    refine ⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩
  have hFcard : F.card ≤ T.card := by
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card hsub
  change s * M ≤ 2 * T.card
  omega

theorem eisU_subset_triUtp_of_triangle (R s M : ℕ) :
    (eisTriangle R s M).image eisU ⊆ triUtp (2 * R) := by
  classical
  intro p hp
  obtain ⟨⟨b, m⟩, hbm, rfl⟩ := Finset.mem_image.mp hp
  simp only [eisTriangle, eisPred,
    Finset.mem_filter, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hbm
  rw [mem_triUtp_iff]
  unfold eisU
  dsimp
  refine ⟨?_, by omega, by omega⟩
  intro h0; simp only [Prod.mk.injEq] at h0; omega

def eisS (R : ℕ) : ℕ := (2 * R - 1) / 8
def eisM (R : ℕ) : ℕ := (4 * R - 8 * eisS R - 2) / 5

end Erdos91.EisensteinSevenCollisionFamilyAndSub6KSquaredBound

/-! ## Parallelogram-Law Triangular-Lattice Disks (`minimalDistinctDistances_triDisk_le`), Unconditional `n ≥ 18` One-Step Plateau Nonuniqueness, Exact Zero-Slack `[8, 18)` Prefix Splicing, Global Constant-`5` Uniqueness-Exception Bound (`≤ 5 + d(N + 1)`), Two-Digit `N ≥ 52` Unconditional Majority Nonuniqueness, and Sharpened `K = 4..15` Multiplicity Certificates -/

namespace Erdos91.TriangularLatticeDisksAndConstantFiveException
open Finset Minimizer91 PlateauDefinitions91
open Erdos91.SmallCasesAndSquareBarrier (plane_dist_sq)
open Erdos91.GeneralMultiplicityAndDensityOne (HasAtLeastKNonsimilarMinimizers)
open Erdos91.AsymptoticDensityOneAndGlobalBounds (uniqueMinimizerSet badMultiplicitySet goodMultiplicitySet good_add_badMultiplicitySet_card)
open Erdos91.TwoPointDeletionAndTwoStepPlateau (two_step_plateau_not_unique)
open Erdos91.UnconditionalEightNineDichotomy (three_le_minimalDistinctDistances_eight)
open Erdos91.EightAndNineNonunique (minimalDistinctDistances_eight_le_four minimalDistinctDistances_nine_le_four)

open Erdos91.ConcreteMultiplicityBenchmarks322And398 (exists_le_of_goodMultiplicitySet_pos)
open Erdos91.SharpenedTelescopingAndPrefixBounds (uniqueMinimizer_filter_lt_eight_card_le_five badMultiplicitySet_card_add_two_mul_le_of_ge)
open Erdos91.FiveLe35TransitionAnd58ExceptionBound (uniqueMinimizer_imp_strict_rise_of_eight_le_of_le_four)
open Erdos91.EvenOddGapSplicingAnd21KDiv4Bounds (uniqueMinimizer_two_step_gap_card_add_le uniqueMinimizer_odd_gap_card_add_le)
open Erdos91.TriangularLatticeHexagonAndSub130Majority (triPoint triPoint_injective triNormSq triNorm card_image_triNorm_eq_card_image_triNormSq triOffset dist_triPoint_sq_eq_triNormSq dist_triPoint_eq triRedundant36U triRedundant36V triRedundant36U_nodup triRedundant36U_valid minimalDistinctDistances_12_le_5 minimalDistinctDistances_19_le_8 minimalDistinctDistances_27_le_11 minimalDistinctDistances_37_le_15 minimalDistinctDistances_48_le_19 minimalDistinctDistances_61_le_23 minimalDistinctDistances_75_le_28 minimalDistinctDistances_91_le_34 minimalDistinctDistances_108_le_39 minimalDistinctDistances_127_le_46 minimalDistinctDistances_147_le_52 two_mul_minimalDistinctDistances_lt_of_ge_40 unconditional_majority_nonunique_of_ge_130)

/-- Scaled Eisenstein quadratic form `(6x - cx)^2 + (6x - cx)(6y - cy) + (6y - cy)^2`
measuring squared Euclidean distance from `triPoint (x, y)` to a rational center `(cx/6, cy/6)`. -/
def triDiskQuad (cx cy x y : ℕ) : ℤ :=
  let X : ℤ := 6 * (x : ℤ) - (cx : ℤ)
  let Y : ℤ := 6 * (y : ℤ) - (cy : ℤ)
  X * X + X * Y + Y * Y

/-- Exact integer formula for `triNormSq (triOffset p q)`. -/
theorem triNormSq_triOffset_int_eq (p q : ℕ × ℕ) :
    (triNormSq (triOffset p q) : ℤ) =
      4 * (((p.1 : ℤ) - (q.1 : ℤ)) ^ 2 +
        ((p.1 : ℤ) - (q.1 : ℤ)) * ((p.2 : ℤ) - (q.2 : ℤ)) +
        ((p.2 : ℤ) - (q.2 : ℤ)) ^ 2) := by
  have hreal := dist_triPoint_sq_eq_triNormSq p q
  rw [plane_dist_sq] at hreal
  change ((2 * (p.1 : ℝ) + (p.2 : ℝ)) - (2 * (q.1 : ℝ) + (q.2 : ℝ))) ^ 2 +
    (Real.sqrt 3 * (p.2 : ℝ) - Real.sqrt 3 * (q.2 : ℝ)) ^ 2 = _ at hreal
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h_alg : ((2 * (p.1 : ℝ) + (p.2 : ℝ)) - (2 * (q.1 : ℝ) + (q.2 : ℝ))) ^ 2 +
      (Real.sqrt 3 * (p.2 : ℝ) - Real.sqrt 3 * (q.2 : ℝ)) ^ 2 =
      4 * (((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 + ((p.1 : ℝ) - (q.1 : ℝ)) * ((p.2 : ℝ) - (q.2 : ℝ)) +
        ((p.2 : ℝ) - (q.2 : ℝ)) ^ 2) := by
    linear_combination ((p.2 : ℝ) - (q.2 : ℝ)) ^ 2 * hs3
  have heq : (triNormSq (triOffset p q) : ℝ) =
      ((4 * (((p.1 : ℤ) - (q.1 : ℤ)) ^ 2 +
        ((p.1 : ℤ) - (q.1 : ℤ)) * ((p.2 : ℤ) - (q.2 : ℤ)) +
        ((p.2 : ℤ) - (q.2 : ℤ)) ^ 2) : ℤ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast heq

/-- **Parallelogram law for `triDiskQuad`:** if `p` and `q` both lie in the disk
`triDiskQuad cx cy ≤ R0`, then `9 * triNormSq (triOffset p q) ≤ 4 * R0`. -/
theorem nine_mul_triNormSq_triOffset_le_four_mul (cx cy R0 : ℕ) (p q : ℕ × ℕ)
    (hp : triDiskQuad cx cy p.1 p.2 ≤ (R0 : ℤ))
    (hq : triDiskQuad cx cy q.1 q.2 ≤ (R0 : ℤ)) :
    9 * triNormSq (triOffset p q) ≤ 4 * R0 := by
  have hint : (9 * (triNormSq (triOffset p q) : ℤ)) ≤ 4 * (R0 : ℤ) := by
    rw [triNormSq_triOffset_int_eq p q]
    unfold triDiskQuad at hp hq
    dsimp at hp hq
    have hsq1 : 0 ≤ (2 * ((6 * (p.1 : ℤ) - (cx : ℤ)) + (6 * (q.1 : ℤ) - (cx : ℤ))) +
        ((6 * (p.2 : ℤ) - (cy : ℤ)) + (6 * (q.2 : ℤ) - (cy : ℤ)))) ^ 2 := sq_nonneg _
    have hsq2 : 0 ≤ ((6 * (p.2 : ℤ) - (cy : ℤ)) + (6 * (q.2 : ℤ) - (cy : ℤ))) ^ 2 := sq_nonneg _
    have hid :
        4 * (9 * (4 * (((p.1 : ℤ) - (q.1 : ℤ)) ^ 2 +
          ((p.1 : ℤ) - (q.1 : ℤ)) * ((p.2 : ℤ) - (q.2 : ℤ)) +
          ((p.2 : ℤ) - (q.2 : ℤ)) ^ 2))) +
        (2 * ((6 * (p.1 : ℤ) - (cx : ℤ)) + (6 * (q.1 : ℤ) - (cx : ℤ))) +
          ((6 * (p.2 : ℤ) - (cy : ℤ)) + (6 * (q.2 : ℤ) - (cy : ℤ)))) ^ 2 +
        3 * ((6 * (p.2 : ℤ) - (cy : ℤ)) + (6 * (q.2 : ℤ) - (cy : ℤ))) ^ 2 =
        8 * ((6 * (p.1 : ℤ) - (cx : ℤ)) * (6 * (p.1 : ℤ) - (cx : ℤ)) +
          (6 * (p.1 : ℤ) - (cx : ℤ)) * (6 * (p.2 : ℤ) - (cy : ℤ)) +
          (6 * (p.2 : ℤ) - (cy : ℤ)) * (6 * (p.2 : ℤ) - (cy : ℤ))) +
        8 * ((6 * (q.1 : ℤ) - (cx : ℤ)) * (6 * (q.1 : ℤ) - (cx : ℤ)) +
          (6 * (q.1 : ℤ) - (cx : ℤ)) * (6 * (q.2 : ℤ) - (cy : ℤ)) +
          (6 * (q.2 : ℤ) - (cy : ℤ)) * (6 * (q.2 : ℤ) - (cy : ℤ))) := by
      ring
    linarith
  exact_mod_cast hint

/-- Every `u : ℕ × ℕ` satisfies `3 * (u.1 + u.2)^2 ≤ triNormSq u`, so if `triNormSq u ≤ M`
and `M < 3 * (m + 1)^2`, then `u.1 + u.2 ≤ m`. -/
theorem add_le_of_triNormSq_le (m M : ℕ) (hm : M < 3 * ((m + 1) * (m + 1)))
    (u : ℕ × ℕ) (hu : triNormSq u ≤ M) :
    u.1 + u.2 ≤ m := by
  have hint : 3 * ((u.1 : ℤ) + (u.2 : ℤ)) ^ 2 + ((u.1 : ℤ) - (u.2 : ℤ)) ^ 2 =
      (triNormSq u : ℤ) := by
    unfold triNormSq
    push_cast
    ring
  have hsq : 0 ≤ ((u.1 : ℤ) - (u.2 : ℤ)) ^ 2 := sq_nonneg _
  have hle : 3 * ((u.1 + u.2) * (u.1 + u.2)) ≤ triNormSq u := by
    have h1 : (3 * (((u.1 : ℤ) + (u.2 : ℤ)) * ((u.1 : ℤ) + (u.2 : ℤ)))) ≤ (triNormSq u : ℤ) := by
      linarith
    exact_mod_cast h1
  by_contra hgt
  push Not at hgt
  have hge : m + 1 ≤ u.1 + u.2 := by omega
  have hmul : (m + 1) * (m + 1) ≤ (u.1 + u.2) * (u.1 + u.2) := Nat.mul_le_mul hge hge
  have hmul3 : 3 * ((m + 1) * (m + 1)) ≤ 3 * ((u.1 + u.2) * (u.1 + u.2)) :=
    Nat.mul_le_mul_left 3 hmul
  omega

def triDiskRowList (k cx cy R0 x : ℕ) : List (ℕ × ℕ) :=
  ((List.range k).filter (fun y =>
    decide (triDiskQuad cx cy x y ≤ (R0 : ℤ)))).map (fun y => (x, y))

def triDiskCoordsList (k cx cy R0 : ℕ) : List (ℕ × ℕ) :=
  (List.range k).flatMap (triDiskRowList k cx cy R0)

def triDiskCoords (k cx cy R0 : ℕ) : Finset (ℕ × ℕ) :=
  (triDiskCoordsList k cx cy R0).toFinset

noncomputable def triDiskSet (k cx cy R0 : ℕ) : Finset Plane :=
  (triDiskCoords k cx cy R0).image triPoint

theorem triDiskRowList_nodup (k cx cy R0 x : ℕ) : (triDiskRowList k cx cy R0 x).Nodup := by
  unfold triDiskRowList
  exact List.Nodup.map (fun y1 y2 h => by injection h) (List.nodup_range.filter _)

theorem triDiskCoordsList_nodup (k cx cy R0 : ℕ) : (triDiskCoordsList k cx cy R0).Nodup := by
  unfold triDiskCoordsList
  rw [List.nodup_flatMap]
  refine ⟨fun x _ => triDiskRowList_nodup k cx cy R0 x, ?_⟩
  refine List.nodup_range.pairwise_of_forall_ne (fun x1 _ x2 _ hne => ?_)
  intro p hp1 hp2
  unfold triDiskRowList at hp1 hp2
  rw [List.mem_map] at hp1 hp2
  obtain ⟨y1, _, rfl⟩ := hp1
  obtain ⟨y2, _, heq⟩ := hp2
  injection heq with hx _
  exact hne hx.symm

theorem card_triDiskCoords (k cx cy R0 : ℕ) :
    (triDiskCoords k cx cy R0).card =
      ((List.range k).map (fun x => (triDiskRowList k cx cy R0 x).length)).sum := by
  unfold triDiskCoords
  rw [List.toFinset_card_of_nodup (triDiskCoordsList_nodup k cx cy R0)]
  exact List.length_flatMap

theorem card_triDiskSet (k cx cy R0 : ℕ) :
    (triDiskSet k cx cy R0).card =
      ((List.range k).map (fun x => (triDiskRowList k cx cy R0 x).length)).sum := by
  unfold triDiskSet
  rw [Finset.card_image_of_injective _ triPoint_injective, card_triDiskCoords]

theorem mem_triDiskCoords (k cx cy R0 : ℕ) (p : ℕ × ℕ) (hp : p ∈ triDiskCoords k cx cy R0) :
    p.1 < k ∧ p.2 < k ∧ triDiskQuad cx cy p.1 p.2 ≤ (R0 : ℤ) := by
  rcases p with ⟨x, y⟩
  unfold triDiskCoords triDiskCoordsList triDiskRowList at hp
  rw [List.mem_toFinset, List.mem_flatMap] at hp
  obtain ⟨x0, hx0, hy0⟩ := hp
  rw [List.mem_range] at hx0
  rw [List.mem_map] at hy0
  obtain ⟨y0, hy0_mem, heq⟩ := hy0
  rw [List.mem_filter, List.mem_range, decide_eq_true_eq] at hy0_mem
  injection heq with hx hy
  subst hx; subst hy
  exact ⟨hx0, hy0_mem.1, hy0_mem.2⟩

def triBallRowList (m M x : ℕ) : List (ℕ × ℕ) :=
  ((List.range (m + 1)).filter (fun y =>
    decide ((x, y) ≠ (0, 0) ∧ x ≤ y ∧ x + y ≤ m ∧ triNormSq (x, y) ≤ M))).map (fun y => (x, y))

def triBallUtpList (m M : ℕ) : List (ℕ × ℕ) :=
  (List.range (m + 1)).flatMap (triBallRowList m M)

def triBallUtp (m M : ℕ) : Finset (ℕ × ℕ) :=
  (triBallUtpList m M).toFinset

theorem card_triBallUtp_le (m M : ℕ) :
    (triBallUtp m M).card ≤
      ((List.range (m + 1)).map (fun x => (triBallRowList m M x).length)).sum := by
  unfold triBallUtp
  exact (List.toFinset_card_le _).trans (le_of_eq List.length_flatMap)

theorem mem_triBallUtp_of_bounds (m M : ℕ) (u : ℕ × ℕ)
    (hne0 : u ≠ (0, 0)) (hle : u.1 ≤ u.2) (hsum : u.1 + u.2 ≤ m) (hnorm : triNormSq u ≤ M) :
    u ∈ triBallUtp m M := by
  rcases u with ⟨x, y⟩
  dsimp at hle hsum
  unfold triBallUtp triBallUtpList triBallRowList
  rw [List.mem_toFinset, List.mem_flatMap]
  refine ⟨x, List.mem_range.mpr (by omega), List.mem_map.mpr ⟨y, ?_, rfl⟩⟩
  rw [List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨by omega, hne0, hle, hsum, hnorm⟩

theorem triOffset_basic_bounds (p q : ℕ × ℕ) (hpq : p ≠ q) :
    triOffset p q ≠ (0, 0) ∧ (triOffset p q).1 ≤ (triOffset p q).2 := by
  rcases p with ⟨x1, y1⟩
  rcases q with ⟨x2, y2⟩
  have hne0 : Nat.dist x1 x2 ≠ 0 ∨ Nat.dist y1 y2 ≠ 0 := by
    by_contra hboth
    push Not at hboth
    unfold Nat.dist at hboth
    exact hpq (Prod.ext (by omega) (by omega))
  unfold triOffset
  dsimp
  split_ifs with hsame hle1 hle2 hle3 hle4 <;>
    refine ⟨by simp only [Prod.mk.injEq]; omega, by omega⟩

theorem distanceSet_triDiskSet_subset (k cx cy R0 m M : ℕ)
    (hMR : 4 * R0 ≤ 9 * M + 8) (hm : M < 3 * ((m + 1) * (m + 1))) :
    Erdos91.DistanceErasure.distanceSet (triDiskSet k cx cy R0) ⊆
      (triBallUtp m M).image triNorm := by
  classical
  intro r hr
  obtain ⟨a, ha, b, hb, hab, rfl⟩ :=
    (Erdos91.DistanceErasure.mem_distanceSet (triDiskSet k cx cy R0) r).mp hr
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
  have hpq : p ≠ q := fun he => hab (congrArg triPoint he)
  rw [dist_triPoint_eq p q]
  apply Finset.mem_image_of_mem triNorm
  obtain ⟨hne0, hle⟩ := triOffset_basic_bounds p q hpq
  have hbp := (mem_triDiskCoords k cx cy R0 p hp).2.2
  have hbq := (mem_triDiskCoords k cx cy R0 q hq).2.2
  have h9 := nine_mul_triNormSq_triOffset_le_four_mul cx cy R0 p q hbp hbq
  have hnorm : triNormSq (triOffset p q) ≤ M := by omega
  have hsum := add_le_of_triNormSq_le m M hm (triOffset p q) hnorm
  exact mem_triBallUtp_of_bounds m M (triOffset p q) hne0 hle hsum hnorm

def triBallRedundantPred (m M : ℕ) (u : ℕ × ℕ) : Bool :=
  decide (u.1 + u.2 ≤ m ∧ triNormSq u ≤ M)

def triBallRedundantList (m M : ℕ) : List (ℕ × ℕ) :=
  triRedundant36U.filter (triBallRedundantPred m M)

def triBallRedundant (m M : ℕ) : Finset (ℕ × ℕ) :=
  (triBallRedundantList m M).toFinset

theorem card_triBallRedundant (m M : ℕ) :
    (triBallRedundant m M).card = (triBallRedundantList m M).length :=
  List.toFinset_card_of_nodup (triRedundant36U_nodup.filter _)

theorem triBallRedundant_subset_triBallUtp (m M : ℕ) :
    triBallRedundant m M ⊆ triBallUtp m M := by
  intro u hu
  unfold triBallRedundant triBallRedundantList triBallRedundantPred at hu
  rw [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hu
  obtain ⟨⟨hne0, hle, _⟩, _, _, _⟩ := triRedundant36U_valid u hu.1
  exact mem_triBallUtp_of_bounds m M u hne0 hle hu.2.1 hu.2.2

theorem triBallUtp_image_subset_sdiff (m M : ℕ) :
    (triBallUtp m M).image triNormSq ⊆ (triBallUtp m M \ triBallRedundant m M).image triNormSq := by
  classical
  intro r hr
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hr
  by_cases hpR : p ∈ triBallRedundant m M
  · have hp_mem := hpR
    unfold triBallRedundant triBallRedundantList triBallRedundantPred at hp_mem
    rw [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hp_mem
    obtain ⟨_, ⟨hne0, hle, hv_sum⟩, hnotU, hnorm⟩ := triRedundant36U_valid p hp_mem.1
    rw [hnorm]
    apply Finset.mem_image_of_mem triNormSq
    refine Finset.mem_sdiff.mpr ⟨mem_triBallUtp_of_bounds m M (triRedundant36V p) hne0 hle
      (hv_sum.trans hp_mem.2.1) (hnorm ▸ hp_mem.2.2), ?_⟩
    intro hvm
    unfold triBallRedundant triBallRedundantList at hvm
    rw [List.mem_toFinset, List.mem_filter] at hvm
    exact hnotU hvm.1
  · exact Finset.mem_image_of_mem triNormSq (Finset.mem_sdiff.mpr ⟨hp, hpR⟩)

/-- **Master parallelogram-law triangular-lattice Euclidean disk theorem:**
for any `(k, cx, cy, R0, m, M, n, u, r)` with `4 * R0 ≤ 9 * M + 8` and `M < 3 * (m + 1)^2`,
`minimalDistinctDistances n ≤ u - r`. -/
theorem minimalDistinctDistances_triDisk_le (k cx cy R0 m M n u r : ℕ)
    (hMR : 4 * R0 ≤ 9 * M + 8) (hm : M < 3 * ((m + 1) * (m + 1)))
    (hn : ((List.range k).map (fun x => (triDiskRowList k cx cy R0 x).length)).sum = n)
    (hu : ((List.range (m + 1)).map (fun x => (triBallRowList m M x).length)).sum = u)
    (hr : (triBallRedundantList m M).length = r) :
    minimalDistinctDistances n ≤ u - r := by
  have hcard_set : (triDiskSet k cx cy R0).card = n := (card_triDiskSet k cx cy R0).trans hn
  have hmin : minimalDistinctDistances n ≤ distinctDistances (triDiskSet k cx cy R0) :=
    minimal_le (triDiskSet k cx cy R0) n hcard_set
  have hsub : distinctDistances (triDiskSet k cx cy R0) ≤ ((triBallUtp m M).image triNorm).card :=
    Finset.card_le_card (distanceSet_triDiskSet_subset k cx cy R0 m M hMR hm)
  rw [card_image_triNorm_eq_card_image_triNormSq] at hsub
  have h1 : ((triBallUtp m M).image triNormSq).card ≤
      (triBallUtp m M \ triBallRedundant m M).card :=
    (Finset.card_le_card (triBallUtp_image_subset_sdiff m M)).trans Finset.card_image_le
  have hsdiff : (triBallUtp m M \ triBallRedundant m M).card +
      (triBallRedundant m M).card = (triBallUtp m M).card :=
    Finset.card_sdiff_add_card_eq_card (triBallRedundant_subset_triBallUtp m M)
  have hutp : (triBallUtp m M).card ≤ u := (card_triBallUtp_le m M).trans (le_of_eq hu)
  have hred : (triBallRedundant m M).card = r := (card_triBallRedundant m M).trans hr
  omega

/-- Direct pairwise-bounded disk certificate for small non-antipodal equilateral disks
(such as the 21-point face-centered disk `d(21) ≤ 9`). -/
theorem minimalDistinctDistances_triDisk_pair_le (k cx cy R0 m M n u r : ℕ)
    (hm : M < 3 * ((m + 1) * (m + 1)))
    (hn : ((List.range k).map (fun x => (triDiskRowList k cx cy R0 x).length)).sum = n)
    (hu : ((List.range (m + 1)).map (fun x => (triBallRowList m M x).length)).sum = u)
    (hr : (triBallRedundantList m M).length = r)
    (hall : (triDiskCoordsList k cx cy R0).all (fun p =>
      (triDiskCoordsList k cx cy R0).all (fun q =>
        decide (triNormSq (triOffset p q) ≤ M))) = true) :
    minimalDistinctDistances n ≤ u - r := by
  have hcard_set : (triDiskSet k cx cy R0).card = n := (card_triDiskSet k cx cy R0).trans hn
  have hmin : minimalDistinctDistances n ≤ distinctDistances (triDiskSet k cx cy R0) :=
    minimal_le (triDiskSet k cx cy R0) n hcard_set
  have hsub_set : Erdos91.DistanceErasure.distanceSet (triDiskSet k cx cy R0) ⊆
      (triBallUtp m M).image triNorm := by
    classical
    intro dist_val hdist
    obtain ⟨a, ha, b, hb, hab, rfl⟩ :=
      (Erdos91.DistanceErasure.mem_distanceSet (triDiskSet k cx cy R0) dist_val).mp hdist
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
    have hpq : p ≠ q := fun he => hab (congrArg triPoint he)
    rw [dist_triPoint_eq p q]
    apply Finset.mem_image_of_mem triNorm
    obtain ⟨hne0, hle⟩ := triOffset_basic_bounds p q hpq
    have hpL : p ∈ triDiskCoordsList k cx cy R0 := List.mem_toFinset.mp hp
    have hqL : q ∈ triDiskCoordsList k cx cy R0 := List.mem_toFinset.mp hq
    have hnorm : triNormSq (triOffset p q) ≤ M := by
      have h1 := List.all_eq_true.mp hall p hpL
      have h2 := List.all_eq_true.mp h1 q hqL
      exact of_decide_eq_true h2
    have hsum := add_le_of_triNormSq_le m M hm (triOffset p q) hnorm
    exact mem_triBallUtp_of_bounds m M (triOffset p q) hne0 hle hsum hnorm
  have hsub : distinctDistances (triDiskSet k cx cy R0) ≤ ((triBallUtp m M).image triNorm).card :=
    Finset.card_le_card hsub_set
  rw [card_image_triNorm_eq_card_image_triNormSq] at hsub
  have h1 : ((triBallUtp m M).image triNormSq).card ≤
      (triBallUtp m M \ triBallRedundant m M).card :=
    (Finset.card_le_card (triBallUtp_image_subset_sdiff m M)).trans Finset.card_image_le
  have hsdiff : (triBallUtp m M \ triBallRedundant m M).card +
      (triBallRedundant m M).card = (triBallUtp m M).card :=
    Finset.card_sdiff_add_card_eq_card (triBallRedundant_subset_triBallUtp m M)
  have hutp : (triBallUtp m M).card ≤ u := (card_triBallUtp_le m M).trans (le_of_eq hu)
  have hred : (triBallRedundant m M).card = r := (card_triBallRedundant m M).trans hr
  omega

theorem minimalDistinctDistances_16_le_7 : minimalDistinctDistances 16 ≤ 7 :=
  minimalDistinctDistances_triDisk_le 5 11 12 133 4 59 16 7 0 (by omega) (by omega) rfl rfl rfl

theorem minimalDistinctDistances_21_le_9 : minimalDistinctDistances 21 ≤ 9 :=
  minimalDistinctDistances_triDisk_pair_le 6 14 14 192 5 76 21 9 0 (by omega) rfl rfl rfl (by decide)

theorem minimalDistinctDistances_24_le_10 : minimalDistinctDistances 24 ≤ 10 :=
  minimalDistinctDistances_triDisk_le 6 13 14 217 5 96 24 10 0 (by omega) (by omega) rfl rfl rfl

theorem minimalDistinctDistances_31_le_13 : minimalDistinctDistances 31 ≤ 13 :=
  minimalDistinctDistances_triDisk_le 7 18 18 252 6 112 31 13 0 (by omega) (by omega) rfl rfl rfl

theorem minimalDistinctDistances_34_le_14 : minimalDistinctDistances 34 ≤ 14 :=
  minimalDistinctDistances_triDisk_le 7 16 18 316 6 140 34 14 0 (by omega) (by omega) rfl rfl rfl

theorem minimalDistinctDistances_42_le_17 : minimalDistinctDistances 42 ≤ 17 :=
  minimalDistinctDistances_triDisk_le 8 20 20 372 7 165 42 17 0 (by omega) (by omega) rfl rfl rfl

theorem minimalDistinctDistances_55_le_21 : minimalDistinctDistances 55 ≤ 21 :=
  minimalDistinctDistances_triDisk_le 9 23 24 511 8 227 55 22 1 (by omega) (by omega) rfl rfl rfl

theorem minimalDistinctDistances_57_le_22 : minimalDistinctDistances 57 ≤ 22 :=
  minimalDistinctDistances_triDisk_le 9 22 25 543 9 241 57 23 1 (by omega) (by omega) rfl rfl rfl

theorem minimalDistinctDistances_63_le_25 : minimalDistinctDistances 63 ≤ 25 :=
  minimalDistinctDistances_triDisk_le 10 26 26 588 9 261 63 26 1 (by omega) (by omega) rfl rfl rfl

theorem minimalDistinctDistances_69_le_26 : minimalDistinctDistances 69 ≤ 26 :=
  minimalDistinctDistances_triDisk_le 10 26 26 624 9 277 69 27 1 (by omega) (by omega) rfl rfl rfl

theorem minimalDistinctDistances_85_le_32 : minimalDistinctDistances 85 ≤ 32 :=
  minimalDistinctDistances_triDisk_le 11 29 30 811 10 360 85 33 1 (by omega) (by omega) rfl rfl rfl

theorem minimalDistinctDistances_102_le_37 : minimalDistinctDistances 102 ≤ 37 :=
  minimalDistinctDistances_triDisk_le 12 32 32 948 11 421 102 39 2 (by omega) (by omega) rfl rfl rfl

theorem minimalDistinctDistances_199_le_68 : minimalDistinctDistances 199 ≤ 68 :=
  minimalDistinctDistances_triDisk_le 17 48 48 1872 16 832 199 74 6 (by omega) (by omega) rfl rfl rfl

theorem minimalDistinctDistances_270_le_90 : minimalDistinctDistances 270 ≤ 90 :=
  minimalDistinctDistances_triDisk_le 20 56 56 2604 19 1157 270 100 10 (by omega) (by omega) rfl rfl rfl

theorem minimalDistinctDistances_345_le_115 : minimalDistinctDistances 345 ≤ 115 :=
  minimalDistinctDistances_triDisk_le 22 62 62 3396 22 1509 345 129 14 (by omega) (by omega) rfl rfl rfl

theorem minimalDistinctDistances_421_le_135 : minimalDistinctDistances 421 ≤ 135 :=
  minimalDistinctDistances_triDisk_le 25 72 72 4032 24 1792 421 153 18 (by omega) (by omega) rfl rfl rfl

theorem minimalDistinctDistances_499_le_157 : minimalDistinctDistances 499 ≤ 157 :=
  minimalDistinctDistances_triDisk_le 27 78 78 4788 26 2128 499 180 23 (by omega) (by omega) rfl rfl rfl

theorem minimalDistinctDistances_597_le_186 : minimalDistinctDistances 597 ≤ 186 :=
  minimalDistinctDistances_triDisk_le 30 86 86 5844 29 2597 597 215 29 (by omega) (by omega) rfl rfl rfl

theorem minimalDistinctDistances_699_le_216 : minimalDistinctDistances 699 ≤ 216 :=
  minimalDistinctDistances_triDisk_le 32 93 91 6907 31 3069 699 252 36 (by omega) (by omega) rfl rfl rfl

theorem minimalDistinctDistances_815_le_250 : minimalDistinctDistances 815 ≤ 250 :=
  minimalDistinctDistances_triDisk_le 35 101 101 8067 34 3585 815 294 44 (by omega) (by omega) rfl rfl rfl

theorem minimalDistinctDistances_913_le_273 : minimalDistinctDistances 913 ≤ 273 :=
  minimalDistinctDistances_triDisk_le 37 108 108 8892 36 3952 913 324 51 (by omega) (by omega) rfl rfl rfl

/-- **Sharpened unconditional `n ≥ 18` low-distance inequality:**
for all `n ≥ 18`, `2 * minimalDistinctDistances n < n - 1` (lowering the threshold from `40` down to `18`). -/
theorem two_mul_minimalDistinctDistances_lt_of_ge_18 (n : ℕ) (hn : 18 ≤ n) :
    2 * minimalDistinctDistances n < n - 1 := by
  by_cases h19 : n ≤ 19
  · have hd := (MinimumMonotone91.minimum_monotone h19).trans minimalDistinctDistances_19_le_8; omega
  · by_cases h21 : n ≤ 21
    · have hd := (MinimumMonotone91.minimum_monotone h21).trans minimalDistinctDistances_21_le_9; omega
    · by_cases h24 : n ≤ 24
      · have hd := (MinimumMonotone91.minimum_monotone h24).trans minimalDistinctDistances_24_le_10; omega
      · by_cases h27 : n ≤ 27
        · have hd := (MinimumMonotone91.minimum_monotone h27).trans minimalDistinctDistances_27_le_11; omega
        · by_cases h31 : n ≤ 31
          · have hd := (MinimumMonotone91.minimum_monotone h31).trans minimalDistinctDistances_31_le_13; omega
          · by_cases h34 : n ≤ 34
            · have hd := (MinimumMonotone91.minimum_monotone h34).trans minimalDistinctDistances_34_le_14; omega
            · by_cases h37 : n ≤ 37
              · have hd := (MinimumMonotone91.minimum_monotone h37).trans minimalDistinctDistances_37_le_15; omega
              · by_cases h42 : n ≤ 42
                · have hd := (MinimumMonotone91.minimum_monotone h42).trans minimalDistinctDistances_42_le_17; omega
                · exact two_mul_minimalDistinctDistances_lt_of_ge_40 n (by omega)

/-- **Unconditional one-step plateau nonuniqueness for all `n ≥ 18`:**
if `18 ≤ n` and `d(n) = d(n + 1)`, then `¬ UniqueMinimizer n`. -/
theorem unconditional_plateau_not_unique_18 (n : ℕ) (hn : 18 ≤ n)
    (hplat : minimalDistinctDistances n = minimalDistinctDistances (n + 1)) :
    ¬ UniqueMinimizer n := by
  have hlt := two_mul_minimalDistinctDistances_lt_of_ge_18 n hn
  exact PlateauNonunique91.low_distance_plateau_not_unique n (by omega) hplat hlt

theorem uniqueMinimizer_imp_strict_rise_18 (n : ℕ) (hn : 18 ≤ n)
    (huniq : UniqueMinimizer n) :
    minimalDistinctDistances n < minimalDistinctDistances (n + 1) := by
  have hle : minimalDistinctDistances n ≤ minimalDistinctDistances (n + 1) :=
    MinimumMonotone91.minimum_monotone (by omega)
  have hne : minimalDistinctDistances n ≠ minimalDistinctDistances (n + 1) :=
    fun heq => unconditional_plateau_not_unique_18 n hn heq huniq
  omega

theorem uniqueMinimizer_count_le_18 (N : ℕ) (hN : 18 ≤ N)
    (E : Finset ℕ) (hE : E ⊆ Icc 18 N)
    (huniq : ∀ n ∈ E, UniqueMinimizer n) :
    E.card + minimalDistinctDistances 18 ≤ minimalDistinctDistances (N + 1) := by
  have hle : E.card ≤ minimalDistinctDistances (N + 1) - minimalDistinctDistances 18 := by
    apply OneStepCount91.card_le minimalDistinctDistances
      MinimumMonotone91.minimum_monotone E 18 N hE
    intro n hn
    have hn_ge : 18 ≤ n := (mem_Icc.mp (hE hn)).1
    exact uniqueMinimizer_imp_strict_rise_18 n hn_ge (huniq n hn)
  have hmono : minimalDistinctDistances 18 ≤ minimalDistinctDistances (N + 1) :=
    MinimumMonotone91.minimum_monotone (by omega)
  omega

/-- Every `n ∈ [8, 10]` with `UniqueMinimizer n` is a one-step strict rise `d(n) < d(n + 1)`. -/
theorem uniqueMinimizer_imp_strict_rise_Icc_8_10 (n : ℕ) (hn : n ∈ Icc 8 10)
    (huniq : UniqueMinimizer n) :
    minimalDistinctDistances n < minimalDistinctDistances (n + 1) := by
  obtain ⟨h8, h10⟩ := mem_Icc.mp hn
  by_cases hd4 : minimalDistinctDistances n ≤ 4
  · exact uniqueMinimizer_imp_strict_rise_of_eight_le_of_le_four n h8 hd4 huniq
  · have hn10 : n = 10 := by
      by_cases hn8 : n = 8
      · subst hn8; have := minimalDistinctDistances_eight_le_four; omega
      · by_cases hn9 : n = 9
        · subst hn9; have := minimalDistinctDistances_nine_le_four; omega
        · omega
    subst hn10
    have hd10_le : minimalDistinctDistances 10 ≤ minimalDistinctDistances 12 :=
      MinimumMonotone91.minimum_monotone (by omega)
    have hd12 : minimalDistinctDistances 12 ≤ 5 := minimalDistinctDistances_12_le_5
    have hplat : minimalDistinctDistances 10 = minimalDistinctDistances 12 := by omega
    exact False.elim (two_step_plateau_not_unique 10 (by omega) hplat huniq)

theorem uniqueMinimizer_count_Icc_8_10
    (E : Finset ℕ) (hE : E ⊆ Icc 8 10)
    (huniq : ∀ n ∈ E, UniqueMinimizer n) :
    E.card + minimalDistinctDistances 8 ≤ minimalDistinctDistances 11 := by
  have hle : E.card ≤ minimalDistinctDistances (10 + 1) - minimalDistinctDistances 8 := by
    apply OneStepCount91.card_le minimalDistinctDistances
      MinimumMonotone91.minimum_monotone E 8 10 hE
    intro n hn
    exact uniqueMinimizer_imp_strict_rise_Icc_8_10 n (hE hn) (huniq n hn)
  have hmono : minimalDistinctDistances 8 ≤ minimalDistinctDistances (10 + 1) :=
    MinimumMonotone91.minimum_monotone (by omega)
  change E.card + minimalDistinctDistances 8 ≤ minimalDistinctDistances (10 + 1)
  omega

/-- Every `n ∈ {12}` with `UniqueMinimizer 12` is a one-step strict rise `d(12) < d(13)`. -/
theorem uniqueMinimizer_imp_strict_rise_12 (huniq : UniqueMinimizer 12) :
    minimalDistinctDistances 12 < minimalDistinctDistances 13 := by
  have hd12 : minimalDistinctDistances 12 ≤ 5 := minimalDistinctDistances_12_le_5
  have hle : minimalDistinctDistances 12 ≤ minimalDistinctDistances 13 :=
    MinimumMonotone91.minimum_monotone (by omega)
  have hne : minimalDistinctDistances 12 ≠ minimalDistinctDistances 13 :=
    fun heq => PlateauNonunique91.low_distance_plateau_not_unique 12 (by omega) heq (by omega) huniq
  omega

theorem uniqueMinimizer_count_Icc_12_12
    (E : Finset ℕ) (hE : E ⊆ Icc 12 12)
    (huniq : ∀ n ∈ E, UniqueMinimizer n) :
    E.card + minimalDistinctDistances 12 ≤ minimalDistinctDistances 13 := by
  have hle : E.card ≤ minimalDistinctDistances (12 + 1) - minimalDistinctDistances 12 := by
    apply OneStepCount91.card_le minimalDistinctDistances
      MinimumMonotone91.minimum_monotone E 12 12 hE
    intro n hn
    have h := mem_Icc.mp (hE hn)
    have hn12 : n = 12 := by omega
    subst hn12
    exact uniqueMinimizer_imp_strict_rise_12 (huniq 12 hn)
  have hmono : minimalDistinctDistances 12 ≤ minimalDistinctDistances (12 + 1) :=
    MinimumMonotone91.minimum_monotone (by omega)
  change E.card + minimalDistinctDistances 12 ≤ minimalDistinctDistances (12 + 1)
  omega

/-- Every `n ∈ [16, 17]` with `UniqueMinimizer n` is a one-step strict rise `d(n) < d(n + 1)`. -/
theorem uniqueMinimizer_imp_strict_rise_Icc_16_17 (n : ℕ) (hn : n ∈ Icc 16 17)
    (huniq : UniqueMinimizer n) :
    minimalDistinctDistances n < minimalDistinctDistances (n + 1) := by
  obtain ⟨h16, h17⟩ := mem_Icc.mp hn
  by_cases hn16 : n = 16
  · subst hn16
    have hd16 : minimalDistinctDistances 16 ≤ 7 := minimalDistinctDistances_16_le_7
    have hle : minimalDistinctDistances 16 ≤ minimalDistinctDistances (16 + 1) :=
      MinimumMonotone91.minimum_monotone (by omega)
    have hne : minimalDistinctDistances 16 ≠ minimalDistinctDistances (16 + 1) :=
      fun heq => PlateauNonunique91.low_distance_plateau_not_unique 16 (by omega) heq (by omega) huniq
    omega
  · have hn17 : n = 17 := by omega
    subst hn17
    by_cases hd7 : minimalDistinctDistances 17 ≤ 7
    · have hle : minimalDistinctDistances 17 ≤ minimalDistinctDistances (17 + 1) :=
        MinimumMonotone91.minimum_monotone (by omega)
      have hne : minimalDistinctDistances 17 ≠ minimalDistinctDistances (17 + 1) :=
        fun heq => PlateauNonunique91.low_distance_plateau_not_unique 17 (by omega) heq (by omega) huniq
      omega
    · have hd17_le : minimalDistinctDistances 17 ≤ minimalDistinctDistances 19 :=
        MinimumMonotone91.minimum_monotone (by omega)
      have hd19 : minimalDistinctDistances 19 ≤ 8 := minimalDistinctDistances_19_le_8
      have hplat : minimalDistinctDistances 17 = minimalDistinctDistances 19 := by omega
      exact False.elim (two_step_plateau_not_unique 17 (by omega) hplat huniq)

theorem uniqueMinimizer_count_Icc_16_16
    (E : Finset ℕ) (hE : E ⊆ Icc 16 16)
    (huniq : ∀ n ∈ E, UniqueMinimizer n) :
    E.card + minimalDistinctDistances 16 ≤ minimalDistinctDistances 17 := by
  have hle : E.card ≤ minimalDistinctDistances (16 + 1) - minimalDistinctDistances 16 := by
    apply OneStepCount91.card_le minimalDistinctDistances
      MinimumMonotone91.minimum_monotone E 16 16 hE
    intro n hn
    have h := mem_Icc.mp (hE hn)
    exact uniqueMinimizer_imp_strict_rise_Icc_16_17 n (mem_Icc.mpr ⟨h.1, by omega⟩) (huniq n hn)
  have hmono : minimalDistinctDistances 16 ≤ minimalDistinctDistances (16 + 1) :=
    MinimumMonotone91.minimum_monotone (by omega)
  change E.card + minimalDistinctDistances 16 ≤ minimalDistinctDistances (16 + 1)
  omega

theorem uniqueMinimizer_count_Icc_16_17
    (E : Finset ℕ) (hE : E ⊆ Icc 16 17)
    (huniq : ∀ n ∈ E, UniqueMinimizer n) :
    E.card + minimalDistinctDistances 16 ≤ minimalDistinctDistances 18 := by
  have hle : E.card ≤ minimalDistinctDistances (17 + 1) - minimalDistinctDistances 16 := by
    apply OneStepCount91.card_le minimalDistinctDistances
      MinimumMonotone91.minimum_monotone E 16 17 hE
    intro n hn
    exact uniqueMinimizer_imp_strict_rise_Icc_16_17 n (hE hn) (huniq n hn)
  have hmono : minimalDistinctDistances 16 ≤ minimalDistinctDistances (17 + 1) :=
    MinimumMonotone91.minimum_monotone (by omega)
  change E.card + minimalDistinctDistances 16 ≤ minimalDistinctDistances (17 + 1)
  omega

/-- Helper bound on `[8, 13)`: `E.card + 3 ≤ 1 + d(13)`. -/
theorem uniqueMinimizer_Ico_8_13_card_add_le
    (E : Finset ℕ) (hE : E ⊆ Ico 8 13)
    (huniq : ∀ n ∈ E, UniqueMinimizer n) :
    E.card + 3 ≤ 1 + minimalDistinctDistances 13 := by
  classical
  let E1a := E.filter (fun n => n < 11)
  let E1b := E.filter (fun n => ¬ n < 11)
  have hp1ab : E1a.card + E1b.card = E.card :=
    card_filter_add_card_filter_not (s := E) (p := fun n => n < 11)
  let E1b1 := E1b.filter (fun n => n < 12)
  let E1b2 := E1b.filter (fun n => ¬ n < 12)
  have hp1b : E1b1.card + E1b2.card = E1b.card :=
    card_filter_add_card_filter_not (s := E1b) (p := fun n => n < 12)
  have h1a : E1a.card + minimalDistinctDistances 8 ≤ minimalDistinctDistances 11 := by
    apply uniqueMinimizer_count_Icc_8_10 E1a
    · intro n hn
      obtain ⟨hnE, hlt⟩ := mem_filter.mp hn
      exact mem_Icc.mpr ⟨(mem_Ico.mp (hE hnE)).1, by omega⟩
    · intro n hn
      exact huniq n (mem_filter.mp hn).1
  have h1b1_sub : E1b1 ⊆ Ico 11 12 := by
    intro n hn
    obtain ⟨hn1b, hlt⟩ := mem_filter.mp hn
    obtain ⟨_, hge⟩ := mem_filter.mp hn1b
    exact mem_Ico.mpr ⟨by omega, hlt⟩
  have h1b1 : E1b1.card ≤ 12 - 11 := by simpa using card_le_card h1b1_sub
  have hm11_12 : minimalDistinctDistances 11 ≤ minimalDistinctDistances 12 :=
    MinimumMonotone91.minimum_monotone (by omega)
  have h1b2 : E1b2.card + minimalDistinctDistances 12 ≤ minimalDistinctDistances 13 := by
    apply uniqueMinimizer_count_Icc_12_12 E1b2
    · intro n hn
      obtain ⟨hn1b, hge12⟩ := mem_filter.mp hn
      obtain ⟨hnE, _⟩ := mem_filter.mp hn1b
      have hlt13 := (mem_Ico.mp (hE hnE)).2
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro n hn
      exact huniq n (mem_filter.mp (mem_filter.mp hn).1).1
  have hd8 : 3 ≤ minimalDistinctDistances 8 := three_le_minimalDistinctDistances_eight
  omega

/-- **Exact zero-slack splicing on `[8, 18)`:**
splicing `[8, 13)` (`E1.card + 3 ≤ 1 + d(13)`), `[13, 16)` (3-element odd gap `E2a.card + d(13) ≤ 2 + d(16)`),
and `[16, 18)` (1-step `E2b.card + d(16) ≤ d(18)`) cancels `3 = 1 + 2`, proving `E.card ≤ d(18)`. -/
theorem uniqueMinimizer_Ico_8_18_card_le
    (E : Finset ℕ) (hE : E ⊆ Ico 8 18)
    (huniq : ∀ n ∈ E, UniqueMinimizer n) :
    E.card ≤ minimalDistinctDistances 18 := by
  classical
  let E1 := E.filter (fun n => n < 13)
  let E2 := E.filter (fun n => ¬ n < 13)
  have hp12 : E1.card + E2.card = E.card :=
    card_filter_add_card_filter_not (s := E) (p := fun n => n < 13)
  let E2a := E2.filter (fun n => n < 16)
  let E2b := E2.filter (fun n => ¬ n < 16)
  have hp2ab : E2a.card + E2b.card = E2.card :=
    card_filter_add_card_filter_not (s := E2) (p := fun n => n < 16)
  have h1 : E1.card + 3 ≤ 1 + minimalDistinctDistances 13 := by
    apply uniqueMinimizer_Ico_8_13_card_add_le E1
    · intro n hn
      obtain ⟨hnE, hlt⟩ := mem_filter.mp hn
      exact mem_Ico.mpr ⟨(mem_Ico.mp (hE hnE)).1, hlt⟩
    · intro n hn
      exact huniq n (mem_filter.mp hn).1
  have h2a : E2a.card + minimalDistinctDistances 13 ≤ 1 + 1 + minimalDistinctDistances (13 + 2 * 1 + 1) := by
    apply uniqueMinimizer_odd_gap_card_add_le 1 13 (by omega) E2a
    · intro n hn
      obtain ⟨hn2, hlt16⟩ := mem_filter.mp hn
      obtain ⟨_, hge13⟩ := mem_filter.mp hn2
      exact mem_Ico.mpr ⟨by omega, by omega⟩
    · intro n hn
      exact huniq n (mem_filter.mp (mem_filter.mp hn).1).1
  change E2a.card + minimalDistinctDistances 13 ≤ 2 + minimalDistinctDistances 16 at h2a
  have h2b : E2b.card + minimalDistinctDistances 16 ≤ minimalDistinctDistances 18 := by
    apply uniqueMinimizer_count_Icc_16_17 E2b
    · intro n hn
      obtain ⟨hn2, hge16⟩ := mem_filter.mp hn
      obtain ⟨hnE, _⟩ := mem_filter.mp hn2
      have hlt18 := (mem_Ico.mp (hE hnE)).2
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro n hn
      exact huniq n (mem_filter.mp (mem_filter.mp hn).1).1
  omega

/-- **Exact prefix uniqueness bound on `range 18`:**
for any `E ⊆ range 18` with `∀ n ∈ E, UniqueMinimizer n`,
`E.card ≤ 5 + minimalDistinctDistances 18`. -/
theorem uniqueMinimizer_prefix_18_card_le_five_add
    (E : Finset ℕ) (hE : E ⊆ range 18)
    (huniq : ∀ n ∈ E, UniqueMinimizer n) :
    E.card ≤ 5 + minimalDistinctDistances 18 := by
  classical
  let E_lo := E.filter (fun n => n < 8)
  let E_hi := E.filter (fun n => ¬ n < 8)
  have hpart : E_lo.card + E_hi.card = E.card :=
    card_filter_add_card_filter_not (s := E) (p := fun n => n < 8)
  have hlo5 : E_lo.card ≤ 5 :=
    uniqueMinimizer_filter_lt_eight_card_le_five E huniq
  have hhi_sub : E_hi ⊆ Ico 8 18 := by
    intro n hn
    obtain ⟨hnE, hge⟩ := mem_filter.mp hn
    exact mem_Ico.mpr ⟨by omega, mem_range.mp (hE hnE)⟩
  have hhi_uniq : ∀ n ∈ E_hi, UniqueMinimizer n :=
    fun n hn => huniq n (mem_filter.mp hn).1
  have hhi := uniqueMinimizer_Ico_8_18_card_le E_hi hhi_sub hhi_uniq
  omega

/-- **Global Constant-`5` Uniqueness-Exception Theorem (`≤ 5 + d(N + 1)`):**
for EVERY `N : ℕ`, `(uniqueMinimizerSet N).card ≤ 5 + minimalDistinctDistances (N + 1)`
(cutting the global additive constant from `13` down to `5`, the exact count of `{0, 1, 2, 3, 5}` in `[0, 7]`). -/
theorem uniqueMinimizerSet_card_le_five_add (N : ℕ) :
    (uniqueMinimizerSet N).card ≤ 5 + minimalDistinctDistances (N + 1) := by
  classical
  have hU_sub : uniqueMinimizerSet N ⊆ range (N + 1) := filter_subset _ _
  have huniq : ∀ n ∈ uniqueMinimizerSet N, UniqueMinimizer n :=
    fun n hn => (mem_filter.mp hn).2
  by_cases hN18 : N < 18
  · by_cases hN8 : N < 8
    · have hsub8 : uniqueMinimizerSet N ⊆ (uniqueMinimizerSet N).filter (fun n => n < 8) := by
        intro n hn
        have hn_lt : n < N + 1 := mem_range.mp (hU_sub hn)
        exact mem_filter.mpr ⟨hn, by omega⟩
      have hle8 : (uniqueMinimizerSet N).card ≤
          ((uniqueMinimizerSet N).filter (fun n => n < 8)).card := card_le_card hsub8
      have h5 := uniqueMinimizer_filter_lt_eight_card_le_five (uniqueMinimizerSet N) huniq
      omega
    · let E_lo := (uniqueMinimizerSet N).filter (fun n => n < 8)
      let E_hi := (uniqueMinimizerSet N).filter (fun n => ¬ n < 8)
      have hpart : E_lo.card + E_hi.card = (uniqueMinimizerSet N).card :=
        card_filter_add_card_filter_not (s := uniqueMinimizerSet N) (p := fun n => n < 8)
      have hlo5 : E_lo.card ≤ 5 :=
        uniqueMinimizer_filter_lt_eight_card_le_five (uniqueMinimizerSet N) huniq
      by_cases hN11 : N < 11
      · have hhi_sub : E_hi ⊆ Icc 8 10 := by
          intro n hn
          obtain ⟨hnU, hge⟩ := mem_filter.mp hn
          have hn_lt : n < N + 1 := mem_range.mp (hU_sub hnU)
          exact mem_Icc.mpr ⟨by omega, by omega⟩
        have hhi_step : E_hi.card ≤ minimalDistinctDistances (N + 1) - minimalDistinctDistances 8 := by
          apply OneStepCount91.card_le minimalDistinctDistances
            MinimumMonotone91.minimum_monotone E_hi 8 N
          · intro n hn
            obtain ⟨hnU, hge⟩ := mem_filter.mp hn
            have hn_lt : n < N + 1 := mem_range.mp (hU_sub hnU)
            exact mem_Icc.mpr ⟨by omega, by omega⟩
          · intro n hn
            exact uniqueMinimizer_imp_strict_rise_Icc_8_10 n (hhi_sub hn) (huniq n (mem_filter.mp hn).1)
        have hm : minimalDistinctDistances 8 ≤ minimalDistinctDistances (N + 1) :=
          MinimumMonotone91.minimum_monotone (by omega)
        omega
      · by_cases hN13 : N < 13
        · by_cases hN11_eq : N = 11
          · subst hN11_eq
            let E_a := E_hi.filter (fun n => n < 11)
            let E_b := E_hi.filter (fun n => ¬ n < 11)
            have hpart_ab : E_a.card + E_b.card = E_hi.card :=
              card_filter_add_card_filter_not (s := E_hi) (p := fun n => n < 11)
            have ha_step : E_a.card + minimalDistinctDistances 8 ≤ minimalDistinctDistances 11 := by
              apply uniqueMinimizer_count_Icc_8_10 E_a
              · intro n hn
                obtain ⟨hn_hi, hlt11⟩ := mem_filter.mp hn
                obtain ⟨_, hge8⟩ := mem_filter.mp hn_hi
                exact mem_Icc.mpr ⟨by omega, by omega⟩
              · intro n hn
                exact huniq n (mem_filter.mp (mem_filter.mp hn).1).1
            have hb_sub : E_b ⊆ Ico 11 12 := by
              intro n hn
              obtain ⟨hn_hi, hge11⟩ := mem_filter.mp hn
              have hn_lt : n < 12 := mem_range.mp (hU_sub (mem_filter.mp hn_hi).1)
              exact mem_Ico.mpr ⟨by omega, hn_lt⟩
            have hb1 : E_b.card ≤ 12 - 11 := by simpa using card_le_card hb_sub
            have hm11_12 : minimalDistinctDistances 11 ≤ minimalDistinctDistances (11 + 1) :=
              MinimumMonotone91.minimum_monotone (by omega)
            have hd8 : 3 ≤ minimalDistinctDistances 8 := three_le_minimalDistinctDistances_eight
            omega
          · have hN12 : N = 12 := by omega
            subst hN12
            have hhi_13 : E_hi.card + 3 ≤ 1 + minimalDistinctDistances (12 + 1) := by
              apply uniqueMinimizer_Ico_8_13_card_add_le E_hi
              · intro n hn
                obtain ⟨hnU, hge8⟩ := mem_filter.mp hn
                exact mem_Ico.mpr ⟨by omega, mem_range.mp (hU_sub hnU)⟩
              · intro n hn
                exact huniq n (mem_filter.mp hn).1
            omega
        · by_cases hN16 : N < 16
          · let E_a := E_hi.filter (fun n => n < 13)
            let E_b := E_hi.filter (fun n => ¬ n < 13)
            have hpart_ab : E_a.card + E_b.card = E_hi.card :=
              card_filter_add_card_filter_not (s := E_hi) (p := fun n => n < 13)
            have ha : E_a.card + 3 ≤ 1 + minimalDistinctDistances 13 := by
              apply uniqueMinimizer_Ico_8_13_card_add_le E_a
              · intro n hn
                obtain ⟨hn_hi, hlt13⟩ := mem_filter.mp hn
                obtain ⟨_, hge8⟩ := mem_filter.mp hn_hi
                exact mem_Ico.mpr ⟨by omega, hlt13⟩
              · intro n hn
                exact huniq n (mem_filter.mp (mem_filter.mp hn).1).1
            have hm13_N1 : minimalDistinctDistances 13 ≤ minimalDistinctDistances (N + 1) :=
              MinimumMonotone91.minimum_monotone (by omega)
            by_cases hN13_eq : N = 13
            · subst hN13_eq
              have hb_sub : E_b ⊆ Ico 13 14 := by
                intro n hn
                obtain ⟨hn_hi, hge13⟩ := mem_filter.mp hn
                have hn_lt : n < 14 := mem_range.mp (hU_sub (mem_filter.mp hn_hi).1)
                exact mem_Ico.mpr ⟨by omega, hn_lt⟩
              have hb1 : E_b.card ≤ 14 - 13 := by simpa using card_le_card hb_sub
              omega
            · by_cases hN14_eq : N = 14
              · subst hN14_eq
                have hb_step : E_b.card + minimalDistinctDistances 13 ≤ 1 + minimalDistinctDistances (13 + 2) := by
                  apply uniqueMinimizer_two_step_gap_card_add_le 13 (by omega) E_b
                  · intro n hn
                    obtain ⟨hn_hi, hge13⟩ := mem_filter.mp hn
                    have hn_lt : n < 15 := mem_range.mp (hU_sub (mem_filter.mp hn_hi).1)
                    exact mem_Ico.mpr ⟨by omega, hn_lt⟩
                  · intro n hn
                    exact huniq n (mem_filter.mp (mem_filter.mp hn).1).1
                change E_b.card + minimalDistinctDistances 13 ≤ 1 + minimalDistinctDistances (14 + 1) at hb_step
                omega
              · have hN15 : N = 15 := by omega
                subst hN15
                have hb_step : E_b.card + minimalDistinctDistances 13 ≤ 1 + 1 + minimalDistinctDistances (13 + 2 * 1 + 1) := by
                  apply uniqueMinimizer_odd_gap_card_add_le 1 13 (by omega) E_b
                  · intro n hn
                    obtain ⟨hn_hi, hge13⟩ := mem_filter.mp hn
                    have hn_lt : n < 16 := mem_range.mp (hU_sub (mem_filter.mp hn_hi).1)
                    exact mem_Ico.mpr ⟨by omega, hn_lt⟩
                  · intro n hn
                    exact huniq n (mem_filter.mp (mem_filter.mp hn).1).1
                change E_b.card + minimalDistinctDistances 13 ≤ 2 + minimalDistinctDistances (15 + 1) at hb_step
                omega
          · by_cases hN16_eq : N = 16
            · subst hN16_eq
              let E_a := E_hi.filter (fun n => n < 16)
              let E_b := E_hi.filter (fun n => ¬ n < 16)
              have hpart_ab : E_a.card + E_b.card = E_hi.card :=
                card_filter_add_card_filter_not (s := E_hi) (p := fun n => n < 16)
              let E_a1 := E_a.filter (fun n => n < 13)
              let E_a2 := E_a.filter (fun n => ¬ n < 13)
              have hpart_a : E_a1.card + E_a2.card = E_a.card :=
                card_filter_add_card_filter_not (s := E_a) (p := fun n => n < 13)
              have ha1 : E_a1.card + 3 ≤ 1 + minimalDistinctDistances 13 := by
                apply uniqueMinimizer_Ico_8_13_card_add_le E_a1
                · intro n hn
                  obtain ⟨hn_a, hlt13⟩ := mem_filter.mp hn
                  obtain ⟨hn_hi, _⟩ := mem_filter.mp hn_a
                  obtain ⟨_, hge8⟩ := mem_filter.mp hn_hi
                  exact mem_Ico.mpr ⟨by omega, hlt13⟩
                · intro n hn
                  exact huniq n (mem_filter.mp (mem_filter.mp (mem_filter.mp hn).1).1).1
              have ha2 : E_a2.card + minimalDistinctDistances 13 ≤ 1 + 1 + minimalDistinctDistances (13 + 2 * 1 + 1) := by
                apply uniqueMinimizer_odd_gap_card_add_le 1 13 (by omega) E_a2
                · intro n hn
                  obtain ⟨hn_a, hge13⟩ := mem_filter.mp hn
                  obtain ⟨_, hlt16⟩ := mem_filter.mp hn_a
                  exact mem_Ico.mpr ⟨by omega, hlt16⟩
                · intro n hn
                  exact huniq n (mem_filter.mp (mem_filter.mp (mem_filter.mp hn).1).1).1
              change E_a2.card + minimalDistinctDistances 13 ≤ 2 + minimalDistinctDistances 16 at ha2
              have hb : E_b.card + minimalDistinctDistances 16 ≤ minimalDistinctDistances (16 + 1) := by
                apply uniqueMinimizer_count_Icc_16_16 E_b
                · intro n hn
                  obtain ⟨hn_hi, hge16⟩ := mem_filter.mp hn
                  have hn_lt : n < 17 := mem_range.mp (hU_sub (mem_filter.mp hn_hi).1)
                  exact mem_Icc.mpr ⟨by omega, by omega⟩
                · intro n hn
                  exact huniq n (mem_filter.mp (mem_filter.mp hn).1).1
              omega
            · have hN17 : N = 17 := by omega
              subst hN17
              exact uniqueMinimizer_prefix_18_card_le_five_add (uniqueMinimizerSet 17) hU_sub huniq
  · let E_lo := (uniqueMinimizerSet N).filter (fun n => n < 18)
    let E_hi := (uniqueMinimizerSet N).filter (fun n => ¬ n < 18)
    have hpart : E_lo.card + E_hi.card = (uniqueMinimizerSet N).card :=
      card_filter_add_card_filter_not (s := uniqueMinimizerSet N) (p := fun n => n < 18)
    have hlo_sub : E_lo ⊆ range 18 := by
      intro n hn
      exact mem_range.mpr (mem_filter.mp hn).2
    have hlo_uniq : ∀ n ∈ E_lo, UniqueMinimizer n :=
      fun n hn => huniq n (mem_filter.mp hn).1
    have hlo := uniqueMinimizer_prefix_18_card_le_five_add E_lo hlo_sub hlo_uniq
    have hhi_sub : E_hi ⊆ Icc 18 N := by
      intro n hn
      obtain ⟨hnU, hge⟩ := mem_filter.mp hn
      have hn_lt : n < N + 1 := mem_range.mp (hU_sub hnU)
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    have hhi_uniq : ∀ n ∈ E_hi, UniqueMinimizer n :=
      fun n hn => huniq n (mem_filter.mp hn).1
    have hhi := uniqueMinimizer_count_le_18 N (by omega) E_hi hhi_sub hhi_uniq
    omega

/-- **Two-Digit Unconditional Majority Nonuniqueness (`N ≥ 52`):**
for all `N ≥ 52` (breaking the two-digit `N < 100` barrier down to `52` — a 2.5x reduction from `130`
and >2,884x reduction from `150,000`), `2 * (uniqueMinimizerSet N).card < N + 1`. -/
theorem unconditional_majority_nonunique_of_ge_52
    (N : ℕ) (hN : 52 ≤ N) :
    2 * (uniqueMinimizerSet N).card < N + 1 := by
  have hu := uniqueMinimizerSet_card_le_five_add N
  by_cases h54 : N ≤ 54
  · have hd := (MinimumMonotone91.minimum_monotone (by omega : N + 1 ≤ 55)).trans minimalDistinctDistances_55_le_21; omega
  · by_cases h56 : N ≤ 56
    · have hd := (MinimumMonotone91.minimum_monotone (by omega : N + 1 ≤ 57)).trans minimalDistinctDistances_57_le_22; omega
    · by_cases h60 : N ≤ 60
      · have hd := (MinimumMonotone91.minimum_monotone (by omega : N + 1 ≤ 61)).trans minimalDistinctDistances_61_le_23; omega
      · by_cases h62 : N ≤ 62
        · have hd := (MinimumMonotone91.minimum_monotone (by omega : N + 1 ≤ 63)).trans minimalDistinctDistances_63_le_25; omega
        · by_cases h68 : N ≤ 68
          · have hd := (MinimumMonotone91.minimum_monotone (by omega : N + 1 ≤ 69)).trans minimalDistinctDistances_69_le_26; omega
          · by_cases h74 : N ≤ 74
            · have hd := (MinimumMonotone91.minimum_monotone (by omega : N + 1 ≤ 75)).trans minimalDistinctDistances_75_le_28; omega
            · by_cases h84 : N ≤ 84
              · have hd := (MinimumMonotone91.minimum_monotone (by omega : N + 1 ≤ 85)).trans minimalDistinctDistances_85_le_32; omega
              · by_cases h90 : N ≤ 90
                · have hd := (MinimumMonotone91.minimum_monotone (by omega : N + 1 ≤ 91)).trans minimalDistinctDistances_91_le_34; omega
                · by_cases h107 : N ≤ 107
                  · have hd := (MinimumMonotone91.minimum_monotone (by omega : N + 1 ≤ 108)).trans minimalDistinctDistances_108_le_39; omega
                  · by_cases h126 : N ≤ 126
                    · have hd := (MinimumMonotone91.minimum_monotone (by omega : N + 1 ≤ 127)).trans minimalDistinctDistances_127_le_46; omega
                    · by_cases h129 : N ≤ 129
                      · have hd := (MinimumMonotone91.minimum_monotone (by omega : N + 1 ≤ 147)).trans minimalDistinctDistances_147_le_52; omega
                      · exact unconditional_majority_nonunique_of_ge_130 N (by omega)

theorem one_le_goodMultiplicitySet_four_59 :
    1 ≤ (goodMultiplicitySet 4 59).card := by
  have hpart := good_add_badMultiplicitySet_card 4 59
  have hb := badMultiplicitySet_card_add_two_mul_le_of_ge 4 59 (by omega)
  have hd1 := (MinimumMonotone91.minimum_monotone (by omega : 59 + 1 ≤ 61)).trans minimalDistinctDistances_61_le_23
  have hd2 : minimalDistinctDistances (59 + 2) ≤ 23 := minimalDistinctDistances_61_le_23
  omega

theorem exists_le_59_has_four_minimizers :
    ∃ n ≤ 59, HasAtLeastKNonsimilarMinimizers 4 n := by
  have h := one_le_goodMultiplicitySet_four_59
  exact exists_le_of_goodMultiplicitySet_pos (by omega)

theorem one_le_goodMultiplicitySet_five_99 :
    1 ≤ (goodMultiplicitySet 5 99).card := by
  have hpart := good_add_badMultiplicitySet_card 5 99
  have hb := badMultiplicitySet_card_add_two_mul_le_of_ge 5 99 (by omega)
  have hd1 := (MinimumMonotone91.minimum_monotone (by omega : 99 + 1 ≤ 102)).trans minimalDistinctDistances_102_le_37
  have hd2 := (MinimumMonotone91.minimum_monotone (by omega : 99 + 2 ≤ 102)).trans minimalDistinctDistances_102_le_37
  omega

theorem exists_le_99_has_five_minimizers :
    ∃ n ≤ 99, HasAtLeastKNonsimilarMinimizers 5 n := by
  have h := one_le_goodMultiplicitySet_five_99
  exact exists_le_of_goodMultiplicitySet_pos (by omega)

theorem one_le_goodMultiplicitySet_six_145 :
    1 ≤ (goodMultiplicitySet 6 145).card := by
  have hpart := good_add_badMultiplicitySet_card 6 145
  have hb := badMultiplicitySet_card_add_two_mul_le_of_ge 6 145 (by omega)
  have hd1 := (MinimumMonotone91.minimum_monotone (by omega : 145 + 1 ≤ 147)).trans minimalDistinctDistances_147_le_52
  have hd2 : minimalDistinctDistances (145 + 2) ≤ 52 := minimalDistinctDistances_147_le_52
  omega

theorem exists_le_145_has_six_minimizers :
    ∃ n ≤ 145, HasAtLeastKNonsimilarMinimizers 6 n := by
  have h := one_le_goodMultiplicitySet_six_145
  exact exists_le_of_goodMultiplicitySet_pos (by omega)

theorem one_le_goodMultiplicitySet_seven_197 :
    1 ≤ (goodMultiplicitySet 7 197).card := by
  have hpart := good_add_badMultiplicitySet_card 7 197
  have hb := badMultiplicitySet_card_add_two_mul_le_of_ge 7 197 (by omega)
  have hd1 := (MinimumMonotone91.minimum_monotone (by omega : 197 + 1 ≤ 199)).trans minimalDistinctDistances_199_le_68
  have hd2 : minimalDistinctDistances (197 + 2) ≤ 68 := minimalDistinctDistances_199_le_68
  omega

theorem exists_le_197_has_seven_minimizers :
    ∃ n ≤ 197, HasAtLeastKNonsimilarMinimizers 7 n := by
  have h := one_le_goodMultiplicitySet_seven_197
  exact exists_le_of_goodMultiplicitySet_pos (by omega)

theorem one_le_goodMultiplicitySet_eight_265 :
    1 ≤ (goodMultiplicitySet 8 265).card := by
  have hpart := good_add_badMultiplicitySet_card 8 265
  have hb := badMultiplicitySet_card_add_two_mul_le_of_ge 8 265 (by omega)
  have hd1 := (MinimumMonotone91.minimum_monotone (by omega : 265 + 1 ≤ 270)).trans minimalDistinctDistances_270_le_90
  have hd2 := (MinimumMonotone91.minimum_monotone (by omega : 265 + 2 ≤ 270)).trans minimalDistinctDistances_270_le_90
  omega

theorem exists_le_265_has_eight_minimizers :
    ∃ n ≤ 265, HasAtLeastKNonsimilarMinimizers 8 n := by
  have h := one_le_goodMultiplicitySet_eight_265
  exact exists_le_of_goodMultiplicitySet_pos (by omega)

theorem one_le_goodMultiplicitySet_nine_343 :
    1 ≤ (goodMultiplicitySet 9 343).card := by
  have hpart := good_add_badMultiplicitySet_card 9 343
  have hb := badMultiplicitySet_card_add_two_mul_le_of_ge 9 343 (by omega)
  have hd1 := (MinimumMonotone91.minimum_monotone (by omega : 343 + 1 ≤ 345)).trans minimalDistinctDistances_345_le_115
  have hd2 : minimalDistinctDistances (343 + 2) ≤ 115 := minimalDistinctDistances_345_le_115
  omega

theorem exists_le_343_has_nine_minimizers :
    ∃ n ≤ 343, HasAtLeastKNonsimilarMinimizers 9 n := by
  have h := one_le_goodMultiplicitySet_nine_343
  exact exists_le_of_goodMultiplicitySet_pos (by omega)

theorem one_le_goodMultiplicitySet_ten_415 :
    1 ≤ (goodMultiplicitySet 10 415).card := by
  have hpart := good_add_badMultiplicitySet_card 10 415
  have hb := badMultiplicitySet_card_add_two_mul_le_of_ge 10 415 (by omega)
  have hd1 := (MinimumMonotone91.minimum_monotone (by omega : 415 + 1 ≤ 421)).trans minimalDistinctDistances_421_le_135
  have hd2 := (MinimumMonotone91.minimum_monotone (by omega : 415 + 2 ≤ 421)).trans minimalDistinctDistances_421_le_135
  omega

theorem exists_le_415_has_ten_minimizers :
    ∃ n ≤ 415, HasAtLeastKNonsimilarMinimizers 10 n := by
  have h := one_le_goodMultiplicitySet_ten_415
  exact exists_le_of_goodMultiplicitySet_pos (by omega)

theorem one_le_goodMultiplicitySet_eleven_495 :
    1 ≤ (goodMultiplicitySet 11 495).card := by
  have hpart := good_add_badMultiplicitySet_card 11 495
  have hb := badMultiplicitySet_card_add_two_mul_le_of_ge 11 495 (by omega)
  have hd1 := (MinimumMonotone91.minimum_monotone (by omega : 495 + 1 ≤ 499)).trans minimalDistinctDistances_499_le_157
  have hd2 := (MinimumMonotone91.minimum_monotone (by omega : 495 + 2 ≤ 499)).trans minimalDistinctDistances_499_le_157
  omega

theorem exists_le_495_has_eleven_minimizers :
    ∃ n ≤ 495, HasAtLeastKNonsimilarMinimizers 11 n := by
  have h := one_le_goodMultiplicitySet_eleven_495
  exact exists_le_of_goodMultiplicitySet_pos (by omega)

theorem one_le_goodMultiplicitySet_twelve_593 :
    1 ≤ (goodMultiplicitySet 12 593).card := by
  have hpart := good_add_badMultiplicitySet_card 12 593
  have hb := badMultiplicitySet_card_add_two_mul_le_of_ge 12 593 (by omega)
  have hd1 := (MinimumMonotone91.minimum_monotone (by omega : 593 + 1 ≤ 597)).trans minimalDistinctDistances_597_le_186
  have hd2 := (MinimumMonotone91.minimum_monotone (by omega : 593 + 2 ≤ 597)).trans minimalDistinctDistances_597_le_186
  omega

theorem exists_le_593_has_twelve_minimizers :
    ∃ n ≤ 593, HasAtLeastKNonsimilarMinimizers 12 n := by
  have h := one_le_goodMultiplicitySet_twelve_593
  exact exists_le_of_goodMultiplicitySet_pos (by omega)

theorem one_le_goodMultiplicitySet_thirteen_697 :
    1 ≤ (goodMultiplicitySet 13 697).card := by
  have hpart := good_add_badMultiplicitySet_card 13 697
  have hb := badMultiplicitySet_card_add_two_mul_le_of_ge 13 697 (by omega)
  have hd1 := (MinimumMonotone91.minimum_monotone (by omega : 697 + 1 ≤ 699)).trans minimalDistinctDistances_699_le_216
  have hd2 : minimalDistinctDistances (697 + 2) ≤ 216 := minimalDistinctDistances_699_le_216
  omega

theorem exists_le_697_has_thirteen_minimizers :
    ∃ n ≤ 697, HasAtLeastKNonsimilarMinimizers 13 n := by
  have h := one_le_goodMultiplicitySet_thirteen_697
  exact exists_le_of_goodMultiplicitySet_pos (by omega)

theorem one_le_goodMultiplicitySet_fourteen_813 :
    1 ≤ (goodMultiplicitySet 14 813).card := by
  have hpart := good_add_badMultiplicitySet_card 14 813
  have hb := badMultiplicitySet_card_add_two_mul_le_of_ge 14 813 (by omega)
  have hd1 := (MinimumMonotone91.minimum_monotone (by omega : 813 + 1 ≤ 815)).trans minimalDistinctDistances_815_le_250
  have hd2 : minimalDistinctDistances (813 + 2) ≤ 250 := minimalDistinctDistances_815_le_250
  omega

theorem exists_le_813_has_fourteen_minimizers :
    ∃ n ≤ 813, HasAtLeastKNonsimilarMinimizers 14 n := by
  have h := one_le_goodMultiplicitySet_fourteen_813
  exact exists_le_of_goodMultiplicitySet_pos (by omega)

theorem one_le_goodMultiplicitySet_fifteen_911 :
    1 ≤ (goodMultiplicitySet 15 911).card := by
  have hpart := good_add_badMultiplicitySet_card 15 911
  have hb := badMultiplicitySet_card_add_two_mul_le_of_ge 15 911 (by omega)
  have hd1 := (MinimumMonotone91.minimum_monotone (by omega : 911 + 1 ≤ 913)).trans minimalDistinctDistances_913_le_273
  have hd2 : minimalDistinctDistances (911 + 2) ≤ 273 := minimalDistinctDistances_913_le_273
  omega

theorem exists_le_911_has_fifteen_minimizers :
    ∃ n ≤ 911, HasAtLeastKNonsimilarMinimizers 15 n := by
  have h := one_le_goodMultiplicitySet_fifteen_911
  exact exists_le_of_goodMultiplicitySet_pos (by omega)

end Erdos91.TriangularLatticeDisksAndConstantFiveException

/-! ## Factor-of-2 Sharpened First Eisenstein Family (`19 / 60` Slope), Simultaneous Two-Family (`17 / 55` Slope) and Three-Family Telescoping (`32 / 105 < 0.305` Slope) Eisenstein Collisions on `triUtp (2R)`, and Universal `3 n < 16 K^2` (`5.3333 K^2`) and `2 n < 11 K^2` (`5.5 K^2`) First-Occurrence Theorems -/

namespace Erdos91.ThreeFamilyEisensteinTelescopingAndSub56KSquared
open Finset Minimizer91 PlateauDefinitions91
open Erdos91.GeneralMultiplicityAndDensityOne (HasAtLeastKNonsimilarMinimizers)
open Erdos91.AsymptoticDensityOneAndGlobalBounds (uniqueMinimizerSet badMultiplicitySet goodMultiplicitySet good_add_badMultiplicitySet_card)
open Erdos91.EquivalenceTwoMinimizersAndGeneralKFlatRises (hasAtLeastTwoMinimizers_four_six_seven)
open Erdos91.QuadraticTwoDeletionMultiplicity (badMultiplicitySet_card_le_quadratic_unconditional)
open Erdos91.ConcreteMultiplicityBenchmarks322And398 (exists_le_of_goodMultiplicitySet_pos)
open Erdos91.SharpenedTelescopingAndPrefixBounds (badMultiplicitySet_card_add_two_mul_le_of_ge)
open Erdos91.SharpenedFirstOccurrenceAnd36KSquaredBound (hasAtLeastOneMinimizer)
open Erdos91.TriangularLatticeHexagonAndSub130Majority (triNorm triNormSq hexSet triUtp distanceSet_hexSet_subset exists_le_35_has_three_minimizers mem_triUtp_iff card_triUtp_two_mul_le three_mul_R_succ_add_one_le_card_hexSet minimalDistinctDistances_three_mul_R_succ_add_one_le)
open Erdos91.EisensteinSevenCollisionFamilyAndSub6KSquaredBound (eisU eisV eisU_injective triNorm_eisU_eq_eisV eisPred eisTriangle eisFlip card_eisTriangle_mul_two_ge eisU_subset_triUtp_of_triangle eisS eisM)
open Erdos91.TriangularLatticeDisksAndConstantFiveException (uniqueMinimizerSet_card_le_five_add exists_le_59_has_four_minimizers exists_le_99_has_five_minimizers exists_le_145_has_six_minimizers exists_le_197_has_seven_minimizers)

/-- **Factor-of-2 sharpened remainder-balanced product inequality for the first Eisenstein family:**
`R^2 ≤ 10 * (eisS R * eisM R) + 4 * R` for all `R ≥ 4` (improving `20` down to `10`). -/
theorem ten_mul_eisS_mul_eisM_add_four_mul_ge_sq
    (R : ℕ) (hR : 4 ≤ R) :
    R * R ≤ 10 * (eisS R * eisM R) + 4 * R := by
  have hs_def : eisS R = (2 * R - 1) / 8 := rfl
  have hM_def : eisM R = (4 * R - 8 * eisS R - 2) / 5 := rfl
  generalize hs_var : eisS R = s at hs_def hM_def ⊢
  generalize hM_var : eisM R = M at hM_def ⊢
  generalize hr_var : 2 * R - 8 * s = r
  have hr_lo : 1 ≤ r := by omega
  have hr_hi : r ≤ 8 := by omega
  have hRs : 8 * s = 2 * R - r := by omega
  have h5M : 2 * R + r - 6 ≤ 5 * M := by omega
  have hprod : (2 * R - r) * (2 * R + r - 6) ≤ 40 * (s * M) := by
    calc
      (2 * R - r) * (2 * R + r - 6) = (8 * s) * (2 * R + r - 6) := by rw [hRs]
      _ ≤ (8 * s) * (5 * M) := Nat.mul_le_mul_left (8 * s) h5M
      _ = 40 * (s * M) := by ring
  have hexp : (2 * R - r) * (2 * R + r - 6) + 16 * R = 4 * (R * R) + r * (8 - r) + 2 * (2 * R - r) := by
    zify [show r ≤ 2 * R by omega, show 6 ≤ 2 * R + r by omega, hr_hi]
    ring
  omega

/-- Second Eisenstein collision map (deleted branch in sector `6x ≤ 5y ∧ 3y < 5x`):
`eis2U (b, m) = (5b + 3m, 6b + 5m)`. -/
def eis2U (bm : ℕ × ℕ) : ℕ × ℕ :=
  (5 * bm.1 + 3 * bm.2, 6 * bm.1 + 5 * bm.2)

/-- Second Eisenstein collision map (kept branch in sector `4x < y`):
`eis2V (b, m) = (b, 9b + 7m)`. -/
def eis2V (bm : ℕ × ℕ) : ℕ × ℕ :=
  (bm.1, 9 * bm.1 + 7 * bm.2)

theorem eis2U_injective : Function.Injective eis2U := by
  intro ⟨b1, m1⟩ ⟨b2, m2⟩ h
  simp only [eis2U, Prod.mk.injEq] at h
  ext <;> omega

theorem triNorm_eis2U_eq_eis2V (bm : ℕ × ℕ) :
    triNorm (eis2U bm) = triNorm (eis2V bm) := by
  unfold triNorm triNormSq eis2U eis2V
  dsimp
  congr 1
  push_cast
  ring

abbrev eis2Pred (R : ℕ) (bm : ℕ × ℕ) : Prop :=
  11 * bm.1 + 8 * bm.2 < 2 * R + 1

def eis2Triangle (R s M : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ico 1 (s + 1) ×ˢ Finset.range M).filter (eis2Pred R)

theorem card_eis2Triangle_mul_two_ge (R s M : ℕ)
    (hsum : 11 * s + 8 * M + 3 < 4 * R + 2) :
    s * M ≤ 2 * (eis2Triangle R s M).card := by
  classical
  let B := Finset.Ico 1 (s + 1) ×ˢ Finset.range M
  let T := B.filter (eis2Pred R)
  let F := B.filter (fun bm => ¬ eis2Pred R bm)
  have hBcard : B.card = s * M := by
    dsimp [B]
    rw [Finset.card_product, Nat.card_Ico, Finset.card_range]
    have : s + 1 - 1 = s := by omega
    rw [this]
  have hTF : T.card + F.card = s * M := by
    have h := Finset.card_filter_add_card_filter_not (s := B) (p := eis2Pred R)
    simpa only [T, F, hBcard] using h
  have hinj : Set.InjOn (eisFlip s M) (F : Set (ℕ × ℕ)) := by
    intro ⟨b1, m1⟩ h1 ⟨b2, m2⟩ h2 heq
    have hb1 : (b1, m1) ∈ B := (Finset.mem_filter.mp h1).1
    have hb2 : (b2, m2) ∈ B := (Finset.mem_filter.mp h2).1
    simp only [B, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hb1 hb2
    simp only [eisFlip, Prod.mk.injEq] at heq
    exact Prod.ext (by omega) (by omega)
  have hsub : F.image (eisFlip s M) ⊆ T := by
    intro x hx
    obtain ⟨⟨b, m⟩, hbmF, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hbmB, hnotP⟩ := Finset.mem_filter.mp hbmF
    simp only [B, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hbmB
    simp only [eis2Pred, not_lt] at hnotP
    simp only [T, B, eis2Pred, eisFlip,
      Finset.mem_filter, Finset.mem_product, Finset.mem_Ico, Finset.mem_range]
    refine ⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩
  have hFcard : F.card ≤ T.card := by
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card hsub
  change s * M ≤ 2 * T.card
  omega

theorem eis2U_subset_triUtp_of_triangle (R s M : ℕ) :
    (eis2Triangle R s M).image eis2U ⊆ triUtp (2 * R) := by
  classical
  intro p hp
  obtain ⟨⟨b, m⟩, hbm, rfl⟩ := Finset.mem_image.mp hp
  simp only [eis2Triangle, eis2Pred,
    Finset.mem_filter, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hbm
  rw [mem_triUtp_iff]
  unfold eis2U
  dsimp
  refine ⟨?_, by omega, by omega⟩
  intro h0; simp only [Prod.mk.injEq] at h0; omega

def eis2S (R : ℕ) : ℕ := (2 * R - 1) / 11
def eis2M (R : ℕ) : ℕ := (4 * R - 11 * eis2S R - 2) / 8

/-- Remainder-balanced product inequality for the second Eisenstein family:
`R^2 ≤ 22 * (eis2S R * eis2M R) + 5 * R` for all `R ≥ 6`. -/
theorem twenty_two_mul_eis2S_mul_eis2M_add_five_mul_ge_sq
    (R : ℕ) (hR : 6 ≤ R) :
    R * R ≤ 22 * (eis2S R * eis2M R) + 5 * R := by
  have hs_def : eis2S R = (2 * R - 1) / 11 := rfl
  have hM_def : eis2M R = (4 * R - 11 * eis2S R - 2) / 8 := rfl
  generalize hs_var : eis2S R = s at hs_def hM_def ⊢
  generalize hM_var : eis2M R = M at hM_def ⊢
  generalize hr_var : 2 * R - 11 * s = r
  have hr_lo : 1 ≤ r := by omega
  have hr_hi : r ≤ 11 := by omega
  have hRs : 11 * s = 2 * R - r := by omega
  have h8M : 2 * R + r - 9 ≤ 8 * M := by omega
  have hprod : (2 * R - r) * (2 * R + r - 9) ≤ 88 * (s * M) := by
    calc
      (2 * R - r) * (2 * R + r - 9) = (11 * s) * (2 * R + r - 9) := by rw [hRs]
      _ ≤ (11 * s) * (8 * M) := Nat.mul_le_mul_left (11 * s) h8M
      _ = 88 * (s * M) := by ring
  have hexp : (2 * R - r) * (2 * R + r - 9) + 20 * R = 4 * (R * R) + r * (11 - r) + 2 * (R - r) := by
    zify [show r ≤ 2 * R by omega, show 9 ≤ 2 * R + r by omega, hr_hi, show r ≤ R by omega]
    ring
  omega

/-- Third Eisenstein collision map (deleted branch in sector `x ≤ y ∧ 5y < 6x`):
`eis3U (b, m) = (7b + 5m, 7b + 6m)`. -/
def eis3U (bm : ℕ × ℕ) : ℕ × ℕ :=
  (7 * bm.1 + 5 * bm.2, 7 * bm.1 + 6 * bm.2)

/-- Third Eisenstein collision map (kept branch in sector `4x < y`):
`eis3V (b, m) = (2b + m, 11b + 9m)`. -/
def eis3V (bm : ℕ × ℕ) : ℕ × ℕ :=
  (2 * bm.1 + bm.2, 11 * bm.1 + 9 * bm.2)

theorem eis3U_injective : Function.Injective eis3U := by
  intro ⟨b1, m1⟩ ⟨b2, m2⟩ h
  simp only [eis3U, Prod.mk.injEq] at h
  ext <;> omega

theorem triNorm_eis3U_eq_eis3V (bm : ℕ × ℕ) :
    triNorm (eis3U bm) = triNorm (eis3V bm) := by
  unfold triNorm triNormSq eis3U eis3V
  dsimp
  congr 1
  push_cast
  ring

abbrev eis3Pred (R : ℕ) (bm : ℕ × ℕ) : Prop :=
  14 * bm.1 + 11 * bm.2 < 2 * R + 1

def eis3Triangle (R s M : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ico 1 (s + 1) ×ˢ Finset.range M).filter (eis3Pred R)

theorem card_eis3Triangle_mul_two_ge (R s M : ℕ)
    (hsum : 14 * s + 11 * M + 3 < 4 * R + 2) :
    s * M ≤ 2 * (eis3Triangle R s M).card := by
  classical
  let B := Finset.Ico 1 (s + 1) ×ˢ Finset.range M
  let T := B.filter (eis3Pred R)
  let F := B.filter (fun bm => ¬ eis3Pred R bm)
  have hBcard : B.card = s * M := by
    dsimp [B]
    rw [Finset.card_product, Nat.card_Ico, Finset.card_range]
    have : s + 1 - 1 = s := by omega
    rw [this]
  have hTF : T.card + F.card = s * M := by
    have h := Finset.card_filter_add_card_filter_not (s := B) (p := eis3Pred R)
    simpa only [T, F, hBcard] using h
  have hinj : Set.InjOn (eisFlip s M) (F : Set (ℕ × ℕ)) := by
    intro ⟨b1, m1⟩ h1 ⟨b2, m2⟩ h2 heq
    have hb1 : (b1, m1) ∈ B := (Finset.mem_filter.mp h1).1
    have hb2 : (b2, m2) ∈ B := (Finset.mem_filter.mp h2).1
    simp only [B, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hb1 hb2
    simp only [eisFlip, Prod.mk.injEq] at heq
    exact Prod.ext (by omega) (by omega)
  have hsub : F.image (eisFlip s M) ⊆ T := by
    intro x hx
    obtain ⟨⟨b, m⟩, hbmF, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hbmB, hnotP⟩ := Finset.mem_filter.mp hbmF
    simp only [B, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hbmB
    simp only [eis3Pred, not_lt] at hnotP
    simp only [T, B, eis3Pred, eisFlip,
      Finset.mem_filter, Finset.mem_product, Finset.mem_Ico, Finset.mem_range]
    refine ⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩
  have hFcard : F.card ≤ T.card := by
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card hsub
  change s * M ≤ 2 * T.card
  omega

theorem eis3U_subset_triUtp_of_triangle (R s M : ℕ) :
    (eis3Triangle R s M).image eis3U ⊆ triUtp (2 * R) := by
  classical
  intro p hp
  obtain ⟨⟨b, m⟩, hbm, rfl⟩ := Finset.mem_image.mp hp
  simp only [eis3Triangle, eis3Pred,
    Finset.mem_filter, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hbm
  rw [mem_triUtp_iff]
  unfold eis3U
  dsimp
  refine ⟨?_, by omega, by omega⟩
  intro h0; simp only [Prod.mk.injEq] at h0; omega

def eis3S (R : ℕ) : ℕ := (2 * R - 1) / 14
def eis3M (R : ℕ) : ℕ := (4 * R - 14 * eis3S R - 2) / 11

/-- Remainder-balanced product inequality for the third Eisenstein family:
`2 * R^2 ≤ 77 * (eis3S R * eis3M R) + 13 * R` for all `R ≥ 8`. -/
theorem seventy_seven_mul_eis3S_mul_eis3M_add_thirteen_mul_ge_two_mul_sq
    (R : ℕ) (hR : 8 ≤ R) :
    2 * (R * R) ≤ 77 * (eis3S R * eis3M R) + 13 * R := by
  have hs_def : eis3S R = (2 * R - 1) / 14 := rfl
  have hM_def : eis3M R = (4 * R - 14 * eis3S R - 2) / 11 := rfl
  generalize hs_var : eis3S R = s at hs_def hM_def ⊢
  generalize hM_var : eis3M R = M at hM_def ⊢
  generalize hr_var : 2 * R - 14 * s = r
  have hr_lo : 1 ≤ r := by omega
  have hr_hi : r ≤ 14 := by omega
  have hRs : 14 * s = 2 * R - r := by omega
  have h11M : 2 * R + r - 12 ≤ 11 * M := by omega
  have hprod : (2 * R - r) * (2 * R + r - 12) ≤ 154 * (s * M) := by
    calc
      (2 * R - r) * (2 * R + r - 12) = (14 * s) * (2 * R + r - 12) := by rw [hRs]
      _ ≤ (14 * s) * (11 * M) := Nat.mul_le_mul_left (14 * s) h11M
      _ = 154 * (s * M) := by ring
  have hexp : (2 * R - r) * (2 * R + r - 12) + 26 * R + r * r = 4 * (R * R) + 2 * R + 12 * r := by
    zify [show r ≤ 2 * R by omega, show 12 ≤ 2 * R + r by omega]
    ring
  have hr_sq : r * r ≤ 2 * R + 12 * r := by
    rcases (by omega : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨
      r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  omega

/-- Sector separation `Disjoint U1 U2` (`5x ≤ 3y` vs `3y < 5x`). -/
theorem disjoint_eisU_eis2U (R s1 M1 s2 M2 : ℕ) :
    Disjoint ((eisTriangle R s1 M1).image eisU) ((eis2Triangle R s2 M2).image eis2U) := by
  classical
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  obtain ⟨⟨b1, m1⟩, hbm1, rfl⟩ := Finset.mem_image.mp hp1
  obtain ⟨⟨b2, m2⟩, hbm2, heq⟩ := Finset.mem_image.mp hp2
  simp only [eis2Triangle, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hbm2
  simp only [eisU, eis2U, Prod.mk.injEq] at heq
  omega

/-- Sector separation `Disjoint U1 U3` (`5x ≤ 3y` vs `5y < 6x`). -/
theorem disjoint_eisU_eis3U (R s1 M1 s3 M3 : ℕ) :
    Disjoint ((eisTriangle R s1 M1).image eisU) ((eis3Triangle R s3 M3).image eis3U) := by
  classical
  rw [Finset.disjoint_left]
  intro p hp1 hp3
  obtain ⟨⟨b1, m1⟩, hbm1, rfl⟩ := Finset.mem_image.mp hp1
  obtain ⟨⟨b3, m3⟩, hbm3, heq⟩ := Finset.mem_image.mp hp3
  simp only [eis3Triangle, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hbm3
  simp only [eisU, eis3U, Prod.mk.injEq] at heq
  omega

/-- Sector separation `Disjoint U2 U3` (`6x ≤ 5y` vs `5y < 6x`). -/
theorem disjoint_eis2U_eis3U (R s2 M2 s3 M3 : ℕ) :
    Disjoint ((eis2Triangle R s2 M2).image eis2U) ((eis3Triangle R s3 M3).image eis3U) := by
  classical
  rw [Finset.disjoint_left]
  intro p hp2 hp3
  obtain ⟨⟨b2, m2⟩, hbm2, rfl⟩ := Finset.mem_image.mp hp2
  obtain ⟨⟨b3, m3⟩, hbm3, heq⟩ := Finset.mem_image.mp hp3
  simp only [eis3Triangle, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hbm3
  simp only [eis2U, eis3U, Prod.mk.injEq] at heq
  omega

theorem eisV_mem_sdiff_three_families (R s1 M1 s2 M2 s3 M3 : ℕ)
    {bm : ℕ × ℕ} (hbm : bm ∈ eisTriangle R s1 M1) :
    eisV bm ∈ triUtp (2 * R) \
      (((eisTriangle R s1 M1).image eisU ∪ (eis2Triangle R s2 M2).image eis2U) ∪
        (eis3Triangle R s3 M3).image eis3U) := by
  classical
  rcases bm with ⟨b, m⟩
  simp only [eisTriangle, eisPred,
    Finset.mem_filter, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hbm
  rw [Finset.mem_sdiff, mem_triUtp_iff]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · unfold eisV; dsimp; intro h0; simp only [Prod.mk.injEq] at h0; omega
  · unfold eisV; dsimp; omega
  · unfold eisV; dsimp; omega
  · simp only [Finset.mem_union, not_or]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro hmem
      obtain ⟨⟨b1, m1⟩, hbm1, heq⟩ := Finset.mem_image.mp hmem
      simp only [eisTriangle, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hbm1
      simp only [eisU, eisV, Prod.mk.injEq] at heq; omega
    · intro hmem
      obtain ⟨⟨b2, m2⟩, hbm2, heq⟩ := Finset.mem_image.mp hmem
      simp only [eis2Triangle, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hbm2
      simp only [eis2U, eisV, Prod.mk.injEq] at heq; omega
    · intro hmem
      obtain ⟨⟨b3, m3⟩, hbm3, heq⟩ := Finset.mem_image.mp hmem
      simp only [eis3Triangle, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hbm3
      simp only [eis3U, eisV, Prod.mk.injEq] at heq; omega

theorem eis2V_mem_sdiff_three_families (R s1 M1 s2 M2 s3 M3 : ℕ)
    {bm : ℕ × ℕ} (hbm : bm ∈ eis2Triangle R s2 M2) :
    eis2V bm ∈ triUtp (2 * R) \
      (((eisTriangle R s1 M1).image eisU ∪ (eis2Triangle R s2 M2).image eis2U) ∪
        (eis3Triangle R s3 M3).image eis3U) := by
  classical
  rcases bm with ⟨b, m⟩
  simp only [eis2Triangle, eis2Pred,
    Finset.mem_filter, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hbm
  rw [Finset.mem_sdiff, mem_triUtp_iff]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · unfold eis2V; dsimp; intro h0; simp only [Prod.mk.injEq] at h0; omega
  · unfold eis2V; dsimp; omega
  · unfold eis2V; dsimp; omega
  · simp only [Finset.mem_union, not_or]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro hmem
      obtain ⟨⟨b1, m1⟩, hbm1, heq⟩ := Finset.mem_image.mp hmem
      simp only [eisTriangle, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hbm1
      simp only [eisU, eis2V, Prod.mk.injEq] at heq; omega
    · intro hmem
      obtain ⟨⟨b2, m2⟩, hbm2, heq⟩ := Finset.mem_image.mp hmem
      simp only [eis2Triangle, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hbm2
      simp only [eis2U, eis2V, Prod.mk.injEq] at heq; omega
    · intro hmem
      obtain ⟨⟨b3, m3⟩, hbm3, heq⟩ := Finset.mem_image.mp hmem
      simp only [eis3Triangle, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hbm3
      simp only [eis3U, eis2V, Prod.mk.injEq] at heq; omega

theorem eis3V_mem_sdiff_three_families (R s1 M1 s2 M2 s3 M3 : ℕ)
    {bm : ℕ × ℕ} (hbm : bm ∈ eis3Triangle R s3 M3) :
    eis3V bm ∈ triUtp (2 * R) \
      (((eisTriangle R s1 M1).image eisU ∪ (eis2Triangle R s2 M2).image eis2U) ∪
        (eis3Triangle R s3 M3).image eis3U) := by
  classical
  rcases bm with ⟨b, m⟩
  simp only [eis3Triangle, eis3Pred,
    Finset.mem_filter, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hbm
  rw [Finset.mem_sdiff, mem_triUtp_iff]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · unfold eis3V; dsimp; intro h0; simp only [Prod.mk.injEq] at h0; omega
  · unfold eis3V; dsimp; omega
  · unfold eis3V; dsimp; omega
  · simp only [Finset.mem_union, not_or]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro hmem
      obtain ⟨⟨b1, m1⟩, hbm1, heq⟩ := Finset.mem_image.mp hmem
      simp only [eisTriangle, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hbm1
      simp only [eisU, eis3V, Prod.mk.injEq] at heq; omega
    · intro hmem
      obtain ⟨⟨b2, m2⟩, hbm2, heq⟩ := Finset.mem_image.mp hmem
      simp only [eis2Triangle, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hbm2
      simp only [eis2U, eis3V, Prod.mk.injEq] at heq; omega
    · intro hmem
      obtain ⟨⟨b3, m3⟩, hbm3, heq⟩ := Finset.mem_image.mp hmem
      simp only [eis3Triangle, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hbm3
      simp only [eis3U, eis3V, Prod.mk.injEq] at heq; omega

/-- **Simultaneous three-family Eisenstein hexagonal collision theorem:**
for any `R, s1, M1, s2, M2, s3, M3` satisfying the three triangle sum bounds,
`2 * minimalDistinctDistances (3 * R * (R + 1) + 1) + s1 * M1 + s2 * M2 + s3 * M3 ≤ 2 * (R * (R + 2))`. -/
theorem minimalDistinctDistances_hex_mul_two_add_three_eis_le
    (R s1 M1 s2 M2 s3 M3 : ℕ)
    (hsum1 : 8 * s1 + 5 * M1 + 3 < 4 * R + 2)
    (hsum2 : 11 * s2 + 8 * M2 + 3 < 4 * R + 2)
    (hsum3 : 14 * s3 + 11 * M3 + 3 < 4 * R + 2) :
    2 * minimalDistinctDistances (3 * R * (R + 1) + 1) + s1 * M1 + s2 * M2 + s3 * M3 ≤
      2 * (R * (R + 2)) := by
  classical
  let T1 := eisTriangle R s1 M1
  let T2 := eis2Triangle R s2 M2
  let T3 := eis3Triangle R s3 M3
  let U1 := T1.image eisU
  let U2 := T2.image eis2U
  let U3 := T3.image eis3U
  let U := (U1 ∪ U2) ∪ U3
  have hsub_img : (triUtp (2 * R)).image triNorm ⊆ (triUtp (2 * R) \ U).image triNorm := by
    intro r hr
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hr
    by_cases hpU : p ∈ U
    · simp only [U, Finset.mem_union] at hpU
      rcases hpU with (hp1 | hp2) | hp3
      · obtain ⟨bm, hbm, rfl⟩ := Finset.mem_image.mp hp1
        rw [triNorm_eisU_eq_eisV bm]
        exact Finset.mem_image_of_mem triNorm
          (eisV_mem_sdiff_three_families R s1 M1 s2 M2 s3 M3 hbm)
      · obtain ⟨bm, hbm, rfl⟩ := Finset.mem_image.mp hp2
        rw [triNorm_eis2U_eq_eis2V bm]
        exact Finset.mem_image_of_mem triNorm
          (eis2V_mem_sdiff_three_families R s1 M1 s2 M2 s3 M3 hbm)
      · obtain ⟨bm, hbm, rfl⟩ := Finset.mem_image.mp hp3
        rw [triNorm_eis3U_eq_eis3V bm]
        exact Finset.mem_image_of_mem triNorm
          (eis3V_mem_sdiff_three_families R s1 M1 s2 M2 s3 M3 hbm)
    · exact Finset.mem_image_of_mem triNorm (Finset.mem_sdiff.mpr ⟨hp, hpU⟩)
  have hcard := three_mul_R_succ_add_one_le_card_hexSet R
  have hmono : minimalDistinctDistances (3 * R * (R + 1) + 1) ≤
      minimalDistinctDistances (hexSet (2 * R + 1) R (2 * R)).card :=
    MinimumMonotone91.minimum_monotone hcard
  have hmin : minimalDistinctDistances (hexSet (2 * R + 1) R (2 * R)).card ≤
      distinctDistances (hexSet (2 * R + 1) R (2 * R)) :=
    minimal_le (hexSet (2 * R + 1) R (2 * R)) _ rfl
  have hsub : Erdos91.DistanceErasure.distanceSet (hexSet (2 * R + 1) R (2 * R)) ⊆
      (triUtp (2 * R) \ U).image triNorm :=
    (distanceSet_hexSet_subset (2 * R + 1) R (2 * R) (by omega)).trans hsub_img
  have hcard1 : distinctDistances (hexSet (2 * R + 1) R (2 * R)) ≤
      (triUtp (2 * R) \ U).card :=
    (Finset.card_le_card hsub).trans Finset.card_image_le
  have hU_sub : U ⊆ triUtp (2 * R) :=
    Finset.union_subset
      (Finset.union_subset (eisU_subset_triUtp_of_triangle R s1 M1)
        (eis2U_subset_triUtp_of_triangle R s2 M2))
      (eis3U_subset_triUtp_of_triangle R s3 M3)
  have hsdiff : (triUtp (2 * R) \ U).card + U.card = (triUtp (2 * R)).card :=
    Finset.card_sdiff_add_card_eq_card hU_sub
  have hd12 : Disjoint U1 U2 := disjoint_eisU_eis2U R s1 M1 s2 M2
  have hd12_3 : Disjoint (U1 ∪ U2) U3 :=
    Finset.disjoint_union_left.mpr ⟨disjoint_eisU_eis3U R s1 M1 s3 M3,
      disjoint_eis2U_eis3U R s2 M2 s3 M3⟩
  have hU_card : U.card = T1.card + T2.card + T3.card := by
    dsimp [U]
    rw [Finset.card_union_of_disjoint hd12_3, Finset.card_union_of_disjoint hd12,
      Finset.card_image_of_injective _ eisU_injective,
      Finset.card_image_of_injective _ eis2U_injective,
      Finset.card_image_of_injective _ eis3U_injective]
  rw [hU_card] at hsdiff
  have hutp := card_triUtp_two_mul_le R
  have hT1 := card_eisTriangle_mul_two_ge R s1 M1 hsum1
  have hT2 := card_eis2Triangle_mul_two_ge R s2 M2 hsum2
  have hT3 := card_eis3Triangle_mul_two_ge R s3 M3 hsum3
  change s1 * M1 ≤ 2 * T1.card at hT1
  change s2 * M2 ≤ 2 * T2.card at hT2
  change s3 * M3 ≤ 2 * T3.card at hT3
  omega

/-- **Simultaneous three-family telescoping (`32 / 35`) regular-hexagon distance bound for `R ≥ 8`:**
`35 * minimalDistinctDistances (3 * R * (R + 1) + 1) ≤ 32 * R * R + 84 * R`. -/
theorem minimalDistinctDistances_hex_35_le_of_ge_8 (R : ℕ) (hR : 8 ≤ R) :
    35 * minimalDistinctDistances (3 * R * (R + 1) + 1) ≤ 32 * R * R + 84 * R := by
  have hsum1 : 8 * eisS R + 5 * eisM R + 3 < 4 * R + 2 := by
    unfold eisM eisS; omega
  have hsum2 : 11 * eis2S R + 8 * eis2M R + 3 < 4 * R + 2 := by
    unfold eis2M eis2S; omega
  have hsum3 : 14 * eis3S R + 11 * eis3M R + 3 < 4 * R + 2 := by
    unfold eis3M eis3S; omega
  have hhex := minimalDistinctDistances_hex_mul_two_add_three_eis_le
    R (eisS R) (eisM R) (eis2S R) (eis2M R) (eis3S R) (eis3M R) hsum1 hsum2 hsum3
  have hprod1 := ten_mul_eisS_mul_eisM_add_four_mul_ge_sq R (by omega)
  have hprod2 := twenty_two_mul_eis2S_mul_eis2M_add_five_mul_ge_sq R (by omega)
  have hprod3 := seventy_seven_mul_eis3S_mul_eis3M_add_thirteen_mul_ge_two_mul_sq R hR
  have hexp : R * (R + 2) = R * R + 2 * R := by ring
  have hexp2 : 32 * R * R = 32 * (R * R) := by ring
  omega

end Erdos91.ThreeFamilyEisensteinTelescopingAndSub56KSquared

/-! ## Fourth Eisenstein `(1, 2)`-Reflection Collision Family (`10 R^2 ≤ 147 s_4 M_4 + 120 R`), Simultaneous Four-Family Hexagonal Bound (`647 / 735`), Universal Sub-`0.30` Distance Bound (`10 d(n) ≤ 3 n + 49 √n + 40`, Slope `647 / 2205 < 3 / 10`), Universal `≥ 70%` Nonuniqueness (`10 |U(N)| ≤ 3 N + 49 √(N + 1) + 93`), Unconditional `> 2 / 5 = 40%` Multiplicity Density (`2 (N + 1) < 5 |G_K(N)|`), and Universal Sub-`5 K^2` (`100 n < 499 K^2` and `n < 5 K^2`) First-Occurrence Theorems -/

namespace Erdos91.FourFamilySub30SlopeAndSub5KSquared
open Finset Minimizer91 PlateauDefinitions91
open Erdos91.GeneralMultiplicityAndDensityOne (HasAtLeastKNonsimilarMinimizers)
open Erdos91.AsymptoticDensityOneAndGlobalBounds (uniqueMinimizerSet badMultiplicitySet goodMultiplicitySet good_add_badMultiplicitySet_card)
open Erdos91.EquivalenceTwoMinimizersAndGeneralKFlatRises (hasAtLeastTwoMinimizers_four_six_seven)
open Erdos91.QuadraticTwoDeletionMultiplicity (badMultiplicitySet_card_le_quadratic_unconditional)
open Erdos91.ConcreteMultiplicityBenchmarks322And398 (exists_le_of_goodMultiplicitySet_pos)
open Erdos91.SharpenedTelescopingAndPrefixBounds (badMultiplicitySet_card_add_two_mul_le_of_ge)
open Erdos91.SharpenedFirstOccurrenceAnd36KSquaredBound (hasAtLeastOneMinimizer)
open Erdos91.TriangularLatticeHexagonAndSub130Majority (triNorm triNormSq hexSet triUtp distanceSet_hexSet_subset exists_le_35_has_three_minimizers mem_triUtp_iff card_triUtp_two_mul_le three_mul_R_succ_add_one_le_card_hexSet minimalDistinctDistances_three_mul_R_succ_add_one_le)
open Erdos91.EisensteinSevenCollisionFamilyAndSub6KSquaredBound (eisU eisV eisU_injective triNorm_eisU_eq_eisV eisPred eisTriangle eisFlip card_eisTriangle_mul_two_ge eisU_subset_triUtp_of_triangle eisS eisM)
open Erdos91.TriangularLatticeDisksAndConstantFiveException (uniqueMinimizerSet_card_le_five_add exists_le_59_has_four_minimizers exists_le_99_has_five_minimizers exists_le_145_has_six_minimizers exists_le_197_has_seven_minimizers exists_le_265_has_eight_minimizers exists_le_343_has_nine_minimizers exists_le_415_has_ten_minimizers exists_le_495_has_eleven_minimizers exists_le_593_has_twelve_minimizers exists_le_697_has_thirteen_minimizers exists_le_813_has_fourteen_minimizers exists_le_911_has_fifteen_minimizers)
open Erdos91.ThreeFamilyEisensteinTelescopingAndSub56KSquared (ten_mul_eisS_mul_eisM_add_four_mul_ge_sq eis2U eis2V eis2U_injective triNorm_eis2U_eq_eis2V eis2Pred eis2Triangle card_eis2Triangle_mul_two_ge eis2U_subset_triUtp_of_triangle eis2S eis2M twenty_two_mul_eis2S_mul_eis2M_add_five_mul_ge_sq eis3U eis3V eis3U_injective triNorm_eis3U_eq_eis3V eis3Pred eis3Triangle card_eis3Triangle_mul_two_ge eis3U_subset_triUtp_of_triangle eis3S eis3M seventy_seven_mul_eis3S_mul_eis3M_add_thirteen_mul_ge_two_mul_sq disjoint_eisU_eis2U disjoint_eisU_eis3U disjoint_eis2U_eis3U minimalDistinctDistances_hex_35_le_of_ge_8)

/-- Five-residue lookup table in `{1..6}` avoiding `r ≡ 0 (mod 7)` and `r + 2c ≡ 0 (mod 7)`. -/
def eis4Rem (c j : ℕ) : ℕ :=
  match c, j with
  | 0, 0 => 1 | 0, 1 => 2 | 0, 2 => 3 | 0, 3 => 4 | 0, 4 => 5
  | 1, 0 => 1 | 1, 1 => 2 | 1, 2 => 3 | 1, 3 => 4 | 1, 4 => 6
  | 2, 0 => 1 | 2, 1 => 2 | 2, 2 => 4 | 2, 3 => 5 | 2, 4 => 6
  | 3, 0 => 2 | 3, 1 => 3 | 3, 2 => 4 | 3, 3 => 5 | 3, 4 => 6
  | 4, 0 => 1 | 4, 1 => 2 | 4, 2 => 3 | 4, 3 => 4 | 4, 4 => 5
  | 5, 0 => 1 | 5, 1 => 2 | 5, 2 => 3 | 5, 3 => 5 | 5, 4 => 6
  | 6, 0 => 1 | 6, 1 => 3 | 6, 2 => 4 | 6, 3 => 5 | 6, 4 => 6
  | _, _ => 1

theorem eis4Rem_spec :
    (∀ c ∈ List.range 7, ∀ j ∈ List.range 5,
      1 ≤ eis4Rem c j ∧ eis4Rem c j < 7 ∧
      (2 * eis4Rem c j) % 7 ≠ 0 ∧
      (2 * eis4Rem c j + 4 * c) % 7 ≠ 0 ∧
      5 * eis4Rem c j ≤ 7 * j + 10) ∧
    (∀ c ∈ List.range 7, ∀ j1 ∈ List.range 5, ∀ j2 ∈ List.range 5,
      eis4Rem c j1 = eis4Rem c j2 → j1 = j2) := by
  decide

/-- Residue-filtered parameter `7 * (m / 5) + eis4Rem (b % 7) (m % 5)`. -/
def eis4ActualM (b m : ℕ) : ℕ :=
  7 * (m / 5) + eis4Rem (b % 7) (m % 5)

theorem eis4Rem_bounds_of_mod (b m : ℕ) :
    1 ≤ eis4Rem (b % 7) (m % 5) ∧
    eis4Rem (b % 7) (m % 5) < 7 ∧
    (2 * eis4Rem (b % 7) (m % 5)) % 7 ≠ 0 ∧
    (2 * eis4Rem (b % 7) (m % 5) + 4 * (b % 7)) % 7 ≠ 0 ∧
    5 * eis4Rem (b % 7) (m % 5) ≤ 7 * (m % 5) + 10 :=
  eis4Rem_spec.1 (b % 7) (List.mem_range.mpr (Nat.mod_lt b (by omega)))
    (m % 5) (List.mem_range.mpr (Nat.mod_lt m (by omega)))

theorem eis4ActualM_injective (b : ℕ) : Function.Injective (eis4ActualM b) := by
  intro m1 m2 heq
  unfold eis4ActualM at heq
  have hb1 := eis4Rem_bounds_of_mod b m1
  have hb2 := eis4Rem_bounds_of_mod b m2
  have hq : m1 / 5 = m2 / 5 := by omega
  have hr : eis4Rem (b % 7) (m1 % 5) = eis4Rem (b % 7) (m2 % 5) := by omega
  have hj : m1 % 5 = m2 % 5 :=
    eis4Rem_spec.2 (b % 7) (List.mem_range.mpr (Nat.mod_lt b (by omega)))
      (m1 % 5) (List.mem_range.mpr (Nat.mod_lt m1 (by omega)))
      (m2 % 5) (List.mem_range.mpr (Nat.mod_lt m2 (by omega))) hr
  omega

theorem five_mul_eis4ActualM_le (b m : ℕ) :
    5 * eis4ActualM b m ≤ 7 * m + 10 := by
  unfold eis4ActualM
  have hb := (eis4Rem_bounds_of_mod b m).2.2.2.2
  omega

theorem two_mul_eis4ActualM_mod_seven_ne_zero (b m : ℕ) :
    (2 * eis4ActualM b m) % 7 ≠ 0 := by
  unfold eis4ActualM
  have hb := (eis4Rem_bounds_of_mod b m).2.2.1
  omega

theorem two_mul_eis4ActualM_add_four_mul_mod_seven_ne_zero (b m : ℕ) :
    (2 * eis4ActualM b m + 4 * b) % 7 ≠ 0 := by
  unfold eis4ActualM
  have hb := (eis4Rem_bounds_of_mod b m).2.2.2.1
  omega

/-- Fourth Eisenstein collision map (deleted branch in `y < 2x` with `4x - y ≢ 0 (mod 7)`):
`eis4U (b, m) = (7b + m', 7b + 2m')` where `m' = eis4ActualM b m`. -/
def eis4U (bm : ℕ × ℕ) : ℕ × ℕ :=
  let m' := eis4ActualM bm.1 bm.2
  (7 * bm.1 + m', 7 * bm.1 + 2 * m')

/-- Fourth Eisenstein collision map (kept branch in `2x < y` with `4x - y ≢ 0 (mod 7)`):
`eis4V (b, m) = (2b + m', 11b + 2m')` where `m' = eis4ActualM b m`. -/
def eis4V (bm : ℕ × ℕ) : ℕ × ℕ :=
  let m' := eis4ActualM bm.1 bm.2
  (2 * bm.1 + m', 11 * bm.1 + 2 * m')

theorem eis4U_injective : Function.Injective eis4U := by
  intro ⟨b1, m1⟩ ⟨b2, m2⟩ h
  simp only [eis4U, Prod.mk.injEq] at h
  have hb : b1 = b2 := by omega
  subst hb
  have hm' : eis4ActualM b1 m1 = eis4ActualM b1 m2 := by omega
  exact Prod.ext rfl (eis4ActualM_injective b1 hm')

theorem triNorm_eis4U_eq_eis4V (bm : ℕ × ℕ) :
    triNorm (eis4U bm) = triNorm (eis4V bm) := by
  unfold triNorm triNormSq eis4U eis4V
  dsimp
  congr 1
  push_cast
  ring

abbrev eis4Pred (R : ℕ) (bm : ℕ × ℕ) : Prop :=
  70 * bm.1 + 21 * bm.2 + 25 < 10 * R

def eis4Triangle (R s M : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ico 1 (s + 1) ×ˢ Finset.range M).filter (eis4Pred R)

theorem card_eis4Triangle_mul_two_ge (R s M : ℕ)
    (hsum : 70 * s + 21 * M + 99 < 20 * R) :
    s * M ≤ 2 * (eis4Triangle R s M).card := by
  classical
  let B := Finset.Ico 1 (s + 1) ×ˢ Finset.range M
  let T := B.filter (eis4Pred R)
  let F := B.filter (fun bm => ¬ eis4Pred R bm)
  have hBcard : B.card = s * M := by
    dsimp [B]
    rw [Finset.card_product, Nat.card_Ico, Finset.card_range]
    have : s + 1 - 1 = s := by omega
    rw [this]
  have hTF : T.card + F.card = s * M := by
    have h := Finset.card_filter_add_card_filter_not (s := B) (p := eis4Pred R)
    simpa only [T, F, hBcard] using h
  have hinj : Set.InjOn (eisFlip s M) (F : Set (ℕ × ℕ)) := by
    intro ⟨b1, m1⟩ h1 ⟨b2, m2⟩ h2 heq
    have hb1 : (b1, m1) ∈ B := (Finset.mem_filter.mp h1).1
    have hb2 : (b2, m2) ∈ B := (Finset.mem_filter.mp h2).1
    simp only [B, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hb1 hb2
    simp only [eisFlip, Prod.mk.injEq] at heq
    exact Prod.ext (by omega) (by omega)
  have hsub : F.image (eisFlip s M) ⊆ T := by
    intro x hx
    obtain ⟨⟨b, m⟩, hbmF, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hbmB, hnotP⟩ := Finset.mem_filter.mp hbmF
    simp only [B, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hbmB
    simp only [eis4Pred, not_lt] at hnotP
    simp only [T, B, eis4Pred, eisFlip,
      Finset.mem_filter, Finset.mem_product, Finset.mem_Ico, Finset.mem_range]
    refine ⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩
  have hFcard : F.card ≤ T.card := by
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card hsub
  change s * M ≤ 2 * T.card
  omega

theorem eis4U_subset_triUtp_of_triangle (R s M : ℕ) :
    (eis4Triangle R s M).image eis4U ⊆ triUtp (2 * R) := by
  classical
  intro p hp
  obtain ⟨⟨b, m⟩, hbm, rfl⟩ := Finset.mem_image.mp hp
  simp only [eis4Triangle, eis4Pred,
    Finset.mem_filter, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hbm
  have hm5 := five_mul_eis4ActualM_le b m
  rw [mem_triUtp_iff]
  unfold eis4U
  dsimp
  refine ⟨?_, by omega, by omega⟩
  intro h0; simp only [Prod.mk.injEq] at h0; omega

theorem disjoint_eisU_eis4U (R s1 M1 s4 M4 : ℕ) :
    Disjoint ((eisTriangle R s1 M1).image eisU) ((eis4Triangle R s4 M4).image eis4U) := by
  classical
  rw [Finset.disjoint_left]
  intro p hp1 hp4
  obtain ⟨⟨b1, m1⟩, _, rfl⟩ := Finset.mem_image.mp hp1
  obtain ⟨⟨b4, m4⟩, _, heq⟩ := Finset.mem_image.mp hp4
  simp only [eisU, eis4U, Prod.mk.injEq] at heq
  have hmod := two_mul_eis4ActualM_mod_seven_ne_zero b4 m4
  omega

theorem disjoint_eis2U_eis4U (R s2 M2 s4 M4 : ℕ) :
    Disjoint ((eis2Triangle R s2 M2).image eis2U) ((eis4Triangle R s4 M4).image eis4U) := by
  classical
  rw [Finset.disjoint_left]
  intro p hp2 hp4
  obtain ⟨⟨b2, m2⟩, _, rfl⟩ := Finset.mem_image.mp hp2
  obtain ⟨⟨b4, m4⟩, _, heq⟩ := Finset.mem_image.mp hp4
  simp only [eis2U, eis4U, Prod.mk.injEq] at heq
  have hmod := two_mul_eis4ActualM_mod_seven_ne_zero b4 m4
  omega

theorem disjoint_eis3U_eis4U (R s3 M3 s4 M4 : ℕ) :
    Disjoint ((eis3Triangle R s3 M3).image eis3U) ((eis4Triangle R s4 M4).image eis4U) := by
  classical
  rw [Finset.disjoint_left]
  intro p hp3 hp4
  obtain ⟨⟨b3, m3⟩, _, rfl⟩ := Finset.mem_image.mp hp3
  obtain ⟨⟨b4, m4⟩, _, heq⟩ := Finset.mem_image.mp hp4
  simp only [eis3U, eis4U, Prod.mk.injEq] at heq
  have hmod := two_mul_eis4ActualM_mod_seven_ne_zero b4 m4
  omega

theorem eisV_mem_sdiff_four_families (R s1 M1 s2 M2 s3 M3 s4 M4 : ℕ)
    {bm : ℕ × ℕ} (hbm : bm ∈ eisTriangle R s1 M1) :
    eisV bm ∈ triUtp (2 * R) \
      ((((eisTriangle R s1 M1).image eisU ∪ (eis2Triangle R s2 M2).image eis2U) ∪
        (eis3Triangle R s3 M3).image eis3U) ∪ (eis4Triangle R s4 M4).image eis4U) := by
  classical
  have h3 := Erdos91.ThreeFamilyEisensteinTelescopingAndSub56KSquared.eisV_mem_sdiff_three_families
    R s1 M1 s2 M2 s3 M3 hbm
  obtain ⟨hutp, hnot3⟩ := Finset.mem_sdiff.mp h3
  refine Finset.mem_sdiff.mpr ⟨hutp, ?_⟩
  simp only [Finset.mem_union, not_or] at hnot3 ⊢
  refine ⟨hnot3, ?_⟩
  rcases bm with ⟨b, m⟩
  simp only [eisTriangle, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hbm
  intro hmem
  obtain ⟨⟨b4, m4⟩, hbm4, heq⟩ := Finset.mem_image.mp hmem
  simp only [eis4Triangle, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hbm4
  simp only [eis4U, eisV, Prod.mk.injEq] at heq
  omega

theorem eis2V_mem_sdiff_four_families (R s1 M1 s2 M2 s3 M3 s4 M4 : ℕ)
    {bm : ℕ × ℕ} (hbm : bm ∈ eis2Triangle R s2 M2) :
    eis2V bm ∈ triUtp (2 * R) \
      ((((eisTriangle R s1 M1).image eisU ∪ (eis2Triangle R s2 M2).image eis2U) ∪
        (eis3Triangle R s3 M3).image eis3U) ∪ (eis4Triangle R s4 M4).image eis4U) := by
  classical
  have h3 := Erdos91.ThreeFamilyEisensteinTelescopingAndSub56KSquared.eis2V_mem_sdiff_three_families
    R s1 M1 s2 M2 s3 M3 hbm
  obtain ⟨hutp, hnot3⟩ := Finset.mem_sdiff.mp h3
  refine Finset.mem_sdiff.mpr ⟨hutp, ?_⟩
  simp only [Finset.mem_union, not_or] at hnot3 ⊢
  refine ⟨hnot3, ?_⟩
  rcases bm with ⟨b, m⟩
  simp only [eis2Triangle, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hbm
  intro hmem
  obtain ⟨⟨b4, m4⟩, hbm4, heq⟩ := Finset.mem_image.mp hmem
  simp only [eis4Triangle, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hbm4
  simp only [eis4U, eis2V, Prod.mk.injEq] at heq
  omega

theorem eis3V_mem_sdiff_four_families (R s1 M1 s2 M2 s3 M3 s4 M4 : ℕ)
    {bm : ℕ × ℕ} (hbm : bm ∈ eis3Triangle R s3 M3) :
    eis3V bm ∈ triUtp (2 * R) \
      ((((eisTriangle R s1 M1).image eisU ∪ (eis2Triangle R s2 M2).image eis2U) ∪
        (eis3Triangle R s3 M3).image eis3U) ∪ (eis4Triangle R s4 M4).image eis4U) := by
  classical
  have h3 := Erdos91.ThreeFamilyEisensteinTelescopingAndSub56KSquared.eis3V_mem_sdiff_three_families
    R s1 M1 s2 M2 s3 M3 hbm
  obtain ⟨hutp, hnot3⟩ := Finset.mem_sdiff.mp h3
  refine Finset.mem_sdiff.mpr ⟨hutp, ?_⟩
  simp only [Finset.mem_union, not_or] at hnot3 ⊢
  refine ⟨hnot3, ?_⟩
  rcases bm with ⟨b, m⟩
  simp only [eis3Triangle, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hbm
  intro hmem
  obtain ⟨⟨b4, m4⟩, hbm4, heq⟩ := Finset.mem_image.mp hmem
  simp only [eis4Triangle, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hbm4
  simp only [eis4U, eis3V, Prod.mk.injEq] at heq
  omega

theorem eis4V_mem_sdiff_four_families (R s1 M1 s2 M2 s3 M3 s4 M4 : ℕ)
    {bm : ℕ × ℕ} (hbm : bm ∈ eis4Triangle R s4 M4) :
    eis4V bm ∈ triUtp (2 * R) \
      ((((eisTriangle R s1 M1).image eisU ∪ (eis2Triangle R s2 M2).image eis2U) ∪
        (eis3Triangle R s3 M3).image eis3U) ∪ (eis4Triangle R s4 M4).image eis4U) := by
  classical
  rcases bm with ⟨b, m⟩
  simp only [eis4Triangle, eis4Pred,
    Finset.mem_filter, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hbm
  have hm5 := five_mul_eis4ActualM_le b m
  have hmod := two_mul_eis4ActualM_add_four_mul_mod_seven_ne_zero b m
  rw [Finset.mem_sdiff, mem_triUtp_iff]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · unfold eis4V; dsimp; intro h0; simp only [Prod.mk.injEq] at h0; omega
  · unfold eis4V; dsimp; omega
  · unfold eis4V; dsimp; omega
  · simp only [Finset.mem_union, not_or]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro hmem
      obtain ⟨⟨b1, m1⟩, _, heq⟩ := Finset.mem_image.mp hmem
      simp only [eisU, eis4V, Prod.mk.injEq] at heq; omega
    · intro hmem
      obtain ⟨⟨b2, m2⟩, _, heq⟩ := Finset.mem_image.mp hmem
      simp only [eis2U, eis4V, Prod.mk.injEq] at heq; omega
    · intro hmem
      obtain ⟨⟨b3, m3⟩, _, heq⟩ := Finset.mem_image.mp hmem
      simp only [eis3U, eis4V, Prod.mk.injEq] at heq; omega
    · intro hmem
      obtain ⟨⟨b4, m4⟩, hbm4, heq⟩ := Finset.mem_image.mp hmem
      simp only [eis4Triangle, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hbm4
      simp only [eis4U, eis4V, Prod.mk.injEq] at heq; omega

/-- **Simultaneous four-family Eisenstein hexagonal collision theorem:**
for any `R, s1, M1, s2, M2, s3, M3, s4, M4` satisfying the four triangle sum bounds,
`2 * minimalDistinctDistances (3 * R * (R + 1) + 1) + s1 * M1 + s2 * M2 + s3 * M3 + s4 * M4 ≤ 2 * (R * (R + 2))`. -/
theorem minimalDistinctDistances_hex_mul_two_add_four_eis_le
    (R s1 M1 s2 M2 s3 M3 s4 M4 : ℕ)
    (hsum1 : 8 * s1 + 5 * M1 + 3 < 4 * R + 2)
    (hsum2 : 11 * s2 + 8 * M2 + 3 < 4 * R + 2)
    (hsum3 : 14 * s3 + 11 * M3 + 3 < 4 * R + 2)
    (hsum4 : 70 * s4 + 21 * M4 + 99 < 20 * R) :
    2 * minimalDistinctDistances (3 * R * (R + 1) + 1) + s1 * M1 + s2 * M2 + s3 * M3 + s4 * M4 ≤
      2 * (R * (R + 2)) := by
  classical
  let T1 := eisTriangle R s1 M1
  let T2 := eis2Triangle R s2 M2
  let T3 := eis3Triangle R s3 M3
  let T4 := eis4Triangle R s4 M4
  let U1 := T1.image eisU
  let U2 := T2.image eis2U
  let U3 := T3.image eis3U
  let U4 := T4.image eis4U
  let U := ((U1 ∪ U2) ∪ U3) ∪ U4
  have hsub_img : (triUtp (2 * R)).image triNorm ⊆ (triUtp (2 * R) \ U).image triNorm := by
    intro r hr
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hr
    by_cases hpU : p ∈ U
    · simp only [U, Finset.mem_union] at hpU
      rcases hpU with ((hp1 | hp2) | hp3) | hp4
      · obtain ⟨bm, hbm, rfl⟩ := Finset.mem_image.mp hp1
        rw [triNorm_eisU_eq_eisV bm]
        exact Finset.mem_image_of_mem triNorm
          (eisV_mem_sdiff_four_families R s1 M1 s2 M2 s3 M3 s4 M4 hbm)
      · obtain ⟨bm, hbm, rfl⟩ := Finset.mem_image.mp hp2
        rw [triNorm_eis2U_eq_eis2V bm]
        exact Finset.mem_image_of_mem triNorm
          (eis2V_mem_sdiff_four_families R s1 M1 s2 M2 s3 M3 s4 M4 hbm)
      · obtain ⟨bm, hbm, rfl⟩ := Finset.mem_image.mp hp3
        rw [triNorm_eis3U_eq_eis3V bm]
        exact Finset.mem_image_of_mem triNorm
          (eis3V_mem_sdiff_four_families R s1 M1 s2 M2 s3 M3 s4 M4 hbm)
      · obtain ⟨bm, hbm, rfl⟩ := Finset.mem_image.mp hp4
        rw [triNorm_eis4U_eq_eis4V bm]
        exact Finset.mem_image_of_mem triNorm
          (eis4V_mem_sdiff_four_families R s1 M1 s2 M2 s3 M3 s4 M4 hbm)
    · exact Finset.mem_image_of_mem triNorm (Finset.mem_sdiff.mpr ⟨hp, hpU⟩)
  have hcard := three_mul_R_succ_add_one_le_card_hexSet R
  have hmono : minimalDistinctDistances (3 * R * (R + 1) + 1) ≤
      minimalDistinctDistances (hexSet (2 * R + 1) R (2 * R)).card :=
    MinimumMonotone91.minimum_monotone hcard
  have hmin : minimalDistinctDistances (hexSet (2 * R + 1) R (2 * R)).card ≤
      distinctDistances (hexSet (2 * R + 1) R (2 * R)) :=
    minimal_le (hexSet (2 * R + 1) R (2 * R)) _ rfl
  have hsub : Erdos91.DistanceErasure.distanceSet (hexSet (2 * R + 1) R (2 * R)) ⊆
      (triUtp (2 * R) \ U).image triNorm :=
    (distanceSet_hexSet_subset (2 * R + 1) R (2 * R) (by omega)).trans hsub_img
  have hcard1 : distinctDistances (hexSet (2 * R + 1) R (2 * R)) ≤
      (triUtp (2 * R) \ U).card :=
    (Finset.card_le_card hsub).trans Finset.card_image_le
  have hU_sub : U ⊆ triUtp (2 * R) :=
    Finset.union_subset
      (Finset.union_subset
        (Finset.union_subset (eisU_subset_triUtp_of_triangle R s1 M1)
          (eis2U_subset_triUtp_of_triangle R s2 M2))
        (eis3U_subset_triUtp_of_triangle R s3 M3))
      (eis4U_subset_triUtp_of_triangle R s4 M4)
  have hsdiff : (triUtp (2 * R) \ U).card + U.card = (triUtp (2 * R)).card :=
    Finset.card_sdiff_add_card_eq_card hU_sub
  have hd12 : Disjoint U1 U2 := disjoint_eisU_eis2U R s1 M1 s2 M2
  have hd12_3 : Disjoint (U1 ∪ U2) U3 :=
    Finset.disjoint_union_left.mpr ⟨disjoint_eisU_eis3U R s1 M1 s3 M3,
      disjoint_eis2U_eis3U R s2 M2 s3 M3⟩
  have hd123_4 : Disjoint ((U1 ∪ U2) ∪ U3) U4 :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr ⟨disjoint_eisU_eis4U R s1 M1 s4 M4,
        disjoint_eis2U_eis4U R s2 M2 s4 M4⟩,
       disjoint_eis3U_eis4U R s3 M3 s4 M4⟩
  have hU_card : U.card = T1.card + T2.card + T3.card + T4.card := by
    dsimp [U]
    rw [Finset.card_union_of_disjoint hd123_4,
      Finset.card_union_of_disjoint hd12_3, Finset.card_union_of_disjoint hd12,
      Finset.card_image_of_injective _ eisU_injective,
      Finset.card_image_of_injective _ eis2U_injective,
      Finset.card_image_of_injective _ eis3U_injective,
      Finset.card_image_of_injective _ eis4U_injective]
  rw [hU_card] at hsdiff
  have hutp := card_triUtp_two_mul_le R
  have hT1 := card_eisTriangle_mul_two_ge R s1 M1 hsum1
  have hT2 := card_eis2Triangle_mul_two_ge R s2 M2 hsum2
  have hT3 := card_eis3Triangle_mul_two_ge R s3 M3 hsum3
  have hT4 := card_eis4Triangle_mul_two_ge R s4 M4 hsum4
  change s1 * M1 ≤ 2 * T1.card at hT1
  change s2 * M2 ≤ 2 * T2.card at hT2
  change s3 * M3 ≤ 2 * T3.card at hT3
  change s4 * M4 ≤ 2 * T4.card at hT4
  omega

def eis4S (R : ℕ) : ℕ := (10 * R - 26) / 70
def eis4M (R : ℕ) : ℕ := (20 * R - 70 * eis4S R - 100) / 21

/-- Remainder-balanced product inequality for the fourth Eisenstein family:
`10 * R^2 ≤ 147 * (eis4S R * eis4M R) + 120 * R` for all `R ≥ 10`. -/
theorem hundred_forty_seven_mul_eis4S_mul_eis4M_add_120_mul_ge_ten_mul_sq
    (R : ℕ) (hR : 10 ≤ R) :
    10 * (R * R) ≤ 147 * (eis4S R * eis4M R) + 120 * R := by
  have hs_def : eis4S R = (10 * R - 26) / 70 := rfl
  have hM_def : eis4M R = (20 * R - 70 * eis4S R - 100) / 21 := rfl
  generalize hs_var : eis4S R = s at hs_def hM_def ⊢
  generalize hM_var : eis4M R = M at hM_def ⊢
  generalize hr_var : 10 * R - 70 * s = r
  have hr_lo : 26 ≤ r := by omega
  have hr_hi : r ≤ 95 := by omega
  have hRs : 70 * s = 10 * R - r := by omega
  have h21M : 10 * R + r - 120 ≤ 21 * M := by omega
  have hprod : (10 * R - r) * (10 * R + r - 120) ≤ 1470 * (s * M) := by
    calc
      (10 * R - r) * (10 * R + r - 120) = (70 * s) * (10 * R + r - 120) := by rw [hRs]
      _ ≤ (70 * s) * (21 * M) := Nat.mul_le_mul_left (70 * s) h21M
      _ = 1470 * (s * M) := by ring
  have hexp : (10 * R - r) * (10 * R + r - 120) + 1200 * R + r * r =
      100 * (R * R) + 120 * r := by
    zify [show r ≤ 10 * R by omega, show 120 ≤ 10 * R + r by omega]
    ring
  have hr_sq : r * r ≤ 120 * r := Nat.mul_le_mul_right r (by omega)
  omega

/-- **Simultaneous four-family (`647 / 735`) regular-hexagon distance bound for `R ≥ 10`:**
`735 * minimalDistinctDistances (3 * R * (R + 1) + 1) ≤ 647 * R * R + 2064 * R`. -/
theorem minimalDistinctDistances_hex_735_le_of_ge_10 (R : ℕ) (hR : 10 ≤ R) :
    735 * minimalDistinctDistances (3 * R * (R + 1) + 1) ≤ 647 * R * R + 2064 * R := by
  have hsum1 : 8 * eisS R + 5 * eisM R + 3 < 4 * R + 2 := by
    unfold eisM eisS; omega
  have hsum2 : 11 * eis2S R + 8 * eis2M R + 3 < 4 * R + 2 := by
    unfold eis2M eis2S; omega
  have hsum3 : 14 * eis3S R + 11 * eis3M R + 3 < 4 * R + 2 := by
    unfold eis3M eis3S; omega
  have hsum4 : 70 * eis4S R + 21 * eis4M R + 99 < 20 * R := by
    unfold eis4M eis4S; omega
  have hhex := minimalDistinctDistances_hex_mul_two_add_four_eis_le
    R (eisS R) (eisM R) (eis2S R) (eis2M R) (eis3S R) (eis3M R) (eis4S R) (eis4M R)
    hsum1 hsum2 hsum3 hsum4
  have hprod1 := ten_mul_eisS_mul_eisM_add_four_mul_ge_sq R (by omega)
  have hprod2 := twenty_two_mul_eis2S_mul_eis2M_add_five_mul_ge_sq R (by omega)
  have hprod3 := seventy_seven_mul_eis3S_mul_eis3M_add_thirteen_mul_ge_two_mul_sq R (by omega)
  have hprod4 := hundred_forty_seven_mul_eis4S_mul_eis4M_add_120_mul_ge_ten_mul_sq R hR
  have hexp : R * (R + 2) = R * R + 2 * R := by ring
  have hexp2 : 647 * R * R = 647 * (R * R) := by ring
  omega

/-- **Simultaneous four-family (`647 / 735`) regular-hexagon distance bound for ALL `R : ℕ`:**
`735 * minimalDistinctDistances (3 * R * (R + 1) + 1) ≤ 647 * R * R + 2262 * R`. -/
theorem minimalDistinctDistances_hex_735_le (R : ℕ) :
    735 * minimalDistinctDistances (3 * R * (R + 1) + 1) ≤ 647 * R * R + 2262 * R := by
  by_cases hR10 : 10 ≤ R
  · have h := minimalDistinctDistances_hex_735_le_of_ge_10 R hR10
    omega
  · by_cases hR8 : 8 ≤ R
    · have h := minimalDistinctDistances_hex_35_le_of_ge_8 R hR8
      have hexp : 32 * R * R = 32 * (R * R) := by ring
      have hexp2 : 647 * R * R = 647 * (R * R) := by ring
      have hle9 : 25 * (R * R) ≤ 225 * R := by
        rcases (by omega : R = 8 ∨ R = 9) with rfl | rfl <;> omega
      omega
    · have hhex := minimalDistinctDistances_three_mul_R_succ_add_one_le R
      have hexp : R * (R + 2) = R * R + 2 * R := by ring
      have hexp2 : 647 * R * R = 647 * (R * R) := by ring
      have hle7 : 88 * (R * R) ≤ 616 * R := by
        rcases (by omega : R = 0 ∨ R = 1 ∨ R = 2 ∨ R = 3 ∨ R = 4 ∨ R = 5 ∨ R = 6 ∨ R = 7) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      omega

/-- **Universal `647 / 2205 = 0.293424... < 0.30` four-family asymptotic upper bound on `minimalDistinctDistances n`:**
for every `n : ℕ`, `2205 * minimalDistinctDistances n ≤ 647 * n + 10668 * Nat.sqrt n + 8727`
(breaking the `3 / 10 = 0.30` slope barrier down to `647 / 2205 ≈ 0.293424`). -/
theorem minimalDistinctDistances_2205_le (n : ℕ) :
    2205 * minimalDistinctDistances n ≤ 647 * n + 10668 * Nat.sqrt n + 8727 := by
  let m := n / 3
  let q := Nat.sqrt m
  let R := q + 1
  have hq_le_m : q * q ≤ m := Nat.sqrt_le m
  have hm_lt : m < R * R := Nat.lt_succ_sqrt m
  have hn_le : n ≤ 3 * R * (R + 1) + 1 := by
    have : R * R = q * q + 2 * q + 1 := by dsimp [R]; ring
    have : 3 * R * (R + 1) + 1 = 3 * (q * q) + 9 * q + 7 := by dsimp [R]; ring
    omega
  have hq_le_sqrt : q ≤ Nat.sqrt n := Nat.sqrt_le_sqrt (by omega)
  have hmono : minimalDistinctDistances n ≤ minimalDistinctDistances (3 * R * (R + 1) + 1) :=
    MinimumMonotone91.minimum_monotone hn_le
  have hhex := minimalDistinctDistances_hex_735_le R
  have hexp : 3 * (647 * R * R + 2262 * R) = 647 * (3 * (q * q)) + 10668 * q + 8727 := by dsimp [R]; ring
  omega

/-- **Universal `3 / 10 = 0.30` upper bound on `minimalDistinctDistances n`:**
for every `n : ℕ`, `10 * minimalDistinctDistances n ≤ 3 * n + 49 * Nat.sqrt n + 40`. -/
theorem minimalDistinctDistances_ten_le (n : ℕ) :
    10 * minimalDistinctDistances n ≤ 3 * n + 49 * Nat.sqrt n + 40 := by
  have h := minimalDistinctDistances_2205_le n
  omega

/-- **Breaking the `2 / 5 = 40%` asymptotic density barrier for arbitrary multiplicity `K`:**
because `1 - 2 * (647 / 2205) = 911 / 2205 > 2 / 5`, for EVERY `K : ℕ` and every `N` with
`(1304 + 77 * (2 * (K - 1)^2 + 3))^2 ≤ N + 2`,
`2 * (N + 1) < 5 * (goodMultiplicitySet K N).card` (proving unconditional `> 2 / 5 = 40%` density for every `K`). -/
theorem goodMultiplicitySet_five_gt_two_of_ge_quadratic (K N : ℕ)
    (hN : (1304 + 77 * (2 * (K - 1) ^ 2 + 3)) *
      (1304 + 77 * (2 * (K - 1) ^ 2 + 3)) ≤ N + 2) :
    (badMultiplicitySet K N).card < N + 1 ∧
      2 * (N + 1) < 5 * (goodMultiplicitySet K N).card := by
  generalize hL : 2 * (K - 1) ^ 2 + 3 = L at hN
  have hL3 : 3 ≤ L := by omega
  have hpart := good_add_badMultiplicitySet_card K N
  have hb := badMultiplicitySet_card_le_quadratic_unconditional K N
  rw [hL] at hb
  have hmono : minimalDistinctDistances (N + 1) ≤ minimalDistinctDistances (N + 2) :=
    MinimumMonotone91.minimum_monotone (by omega)
  have hd := minimalDistinctDistances_2205_le (N + 2)
  let C := 1304 + 77 * L
  let q := Nat.sqrt (N + 2)
  have hqC : C ≤ q := Nat.le_sqrt.mpr hN
  have hq_sq : q * q ≤ N + 2 := Nat.sqrt_le (N + 2)
  have hCq : C * q ≤ q * q := Nat.mul_le_mul_right q hqC
  have hq1 : 1304 ≤ q := by dsimp [C] at hqC; omega
  have hCq_exp : (1304 + 77 * L) * q = 1304 * q + 77 * L * q := by ring
  have hL_le : 77 * L ≤ 77 * L * q := by
    have h1 : 1 ≤ q := by omega
    simpa using Nat.mul_le_mul_left (77 * L) h1
  dsimp [C] at hCq
  omega

/-- Eventual `> 2 / 5 = 40%` natural density for `goodMultiplicitySet K N` for every `K : ℕ`
(with ZERO unproved hypotheses). -/
theorem eventually_goodMultiplicitySet_five_gt_two (K : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop, 2 * (N + 1) < 5 * (goodMultiplicitySet K N).card := by
  rw [Filter.eventually_atTop]
  refine ⟨(1304 + 77 * (2 * (K - 1) ^ 2 + 3)) * (1304 + 77 * (2 * (K - 1) ^ 2 + 3)), ?_⟩
  intro N hN
  exact (goodMultiplicitySet_five_gt_two_of_ge_quadratic K N (by omega)).2

/-- Sharpened four-family hexagonal `K`-multiplicity formula at `N = 3 * R * (R + 1) - 1`:
for all `R ≥ 10` and `2 * (K - 1)^2 + 2 ≤ 3 * R * (R + 1) - 1`,
`911 * (R * R) + 1470 * K ≤ 735 * (goodMultiplicitySet K (3 * R * (R + 1) - 1)).card + 1923 * R + 1470 * (K - 1)^2 + 2205`. -/
theorem goodMultiplicitySet_hex_911_ge
    (K R : ℕ) (hR : 10 ≤ R) (hN : 2 * (K - 1) ^ 2 + 2 ≤ 3 * R * (R + 1) - 1) :
    911 * (R * R) + 1470 * K ≤
      735 * (goodMultiplicitySet K (3 * R * (R + 1) - 1)).card + 1923 * R + 1470 * (K - 1) ^ 2 + 2205 := by
  have hR6 : 2 ≤ 3 * R * (R + 1) := by nlinarith
  have hpart := good_add_badMultiplicitySet_card K (3 * R * (R + 1) - 1)
  have hb := badMultiplicitySet_card_add_two_mul_le_of_ge K (3 * R * (R + 1) - 1) hN
  have hidx1 : 3 * R * (R + 1) - 1 + 1 = 3 * R * (R + 1) := by omega
  have hidx2 : 3 * R * (R + 1) - 1 + 2 = 3 * R * (R + 1) + 1 := by omega
  rw [hidx1] at hpart hb
  rw [hidx2] at hb
  have hd1 : minimalDistinctDistances (3 * R * (R + 1)) ≤
      minimalDistinctDistances (3 * R * (R + 1) + 1) :=
    MinimumMonotone91.minimum_monotone (by omega)
  have hd2 := minimalDistinctDistances_hex_735_le_of_ge_10 R hR
  have hexp1 : 3 * R * (R + 1) = 3 * (R * R) + 3 * R := by ring
  have hexp2 : 647 * R * R = 647 * (R * R) := by ring
  omega

theorem minimalDistinctDistances_1519_le_482 : minimalDistinctDistances 1519 ≤ 482 := by
  have h := minimalDistinctDistances_hex_mul_two_add_four_eis_le 22 5 9 3 6 3 4 2 9
    (by omega) (by omega) (by omega) (by omega)
  change 2 * minimalDistinctDistances 1519 + 5 * 9 + 3 * 6 + 3 * 4 + 2 * 9 ≤ 2 * (22 * (22 + 2)) at h
  omega

theorem exists_le_1517_has_eighteen_minimizers :
    ∃ n ≤ 1517, HasAtLeastKNonsimilarMinimizers 18 n := by
  have hpart := good_add_badMultiplicitySet_card 18 1517
  have hb := badMultiplicitySet_card_add_two_mul_le_of_ge 18 1517 (by omega)
  have hd1 := (MinimumMonotone91.minimum_monotone (by omega : 1517 + 1 ≤ 1519)).trans minimalDistinctDistances_1519_le_482
  have hd2 : minimalDistinctDistances (1517 + 2) ≤ 482 := minimalDistinctDistances_1519_le_482
  exact exists_le_of_goodMultiplicitySet_pos (by omega)

theorem minimalDistinctDistances_2269_le_710 : minimalDistinctDistances 2269 ≤ 710 := by
  have h := minimalDistinctDistances_hex_mul_two_add_four_eis_le 27 7 10 5 6 4 4 3 10
    (by omega) (by omega) (by omega) (by omega)
  change 2 * minimalDistinctDistances 2269 + 7 * 10 + 5 * 6 + 4 * 4 + 3 * 10 ≤ 2 * (27 * (27 + 2)) at h
  omega

theorem exists_le_2267_has_twenty_two_minimizers :
    ∃ n ≤ 2267, HasAtLeastKNonsimilarMinimizers 22 n := by
  have hpart := good_add_badMultiplicitySet_card 22 2267
  have hb := badMultiplicitySet_card_add_two_mul_le_of_ge 22 2267 (by omega)
  have hd1 := (MinimumMonotone91.minimum_monotone (by omega : 2267 + 1 ≤ 2269)).trans minimalDistinctDistances_2269_le_710
  have hd2 : minimalDistinctDistances (2267 + 2) ≤ 710 := minimalDistinctDistances_2269_le_710
  exact exists_le_of_goodMultiplicitySet_pos (by omega)

theorem minimalDistinctDistances_3997_le_1234 : minimalDistinctDistances 3997 ≤ 1234 := by
  have h := minimalDistinctDistances_hex_mul_two_add_four_eis_le 36 8 15 6 9 5 6 4 16
    (by omega) (by omega) (by omega) (by omega)
  change 2 * minimalDistinctDistances 3997 + 8 * 15 + 6 * 9 + 5 * 6 + 4 * 16 ≤ 2 * (36 * (36 + 2)) at h
  omega

theorem exists_le_3995_has_twenty_nine_minimizers :
    ∃ n ≤ 3995, HasAtLeastKNonsimilarMinimizers 29 n := by
  have hpart := good_add_badMultiplicitySet_card 29 3995
  have hb := badMultiplicitySet_card_add_two_mul_le_of_ge 29 3995 (by omega)
  have hd1 := (MinimumMonotone91.minimum_monotone (by omega : 3995 + 1 ≤ 3997)).trans minimalDistinctDistances_3997_le_1234
  have hd2 : minimalDistinctDistances (3995 + 2) ≤ 1234 := minimalDistinctDistances_3997_le_1234
  exact exists_le_of_goodMultiplicitySet_pos (by omega)

/-- For all `K ≥ 9` outside `{11, 15, 18, 22, 29}`, `R = (9 * K - 3) / 7` satisfies
`0 < (goodMultiplicitySet K (3 * R * (R + 1) - 1)).card`. -/
theorem goodMultiplicitySet_9_K_sub_3_div_7_pos (K : ℕ) (hK : 9 ≤ K)
    (hne11 : K ≠ 11) (hne15 : K ≠ 15) (hne18 : K ≠ 18) (hne22 : K ≠ 22) (hne29 : K ≠ 29) :
    let R := (9 * K - 3) / 7
    0 < (goodMultiplicitySet K (3 * R * (R + 1) - 1)).card := by
  dsimp
  by_cases hK32 : 32 ≤ K
  · generalize hR_def : (9 * K - 3) / 7 = R
    have hR40 : 40 ≤ R := by omega
    have h7R_lo : 9 * (K - 1) ≤ 7 * R := by omega
    have h7R_hi : 7 * R ≤ 9 * K - 3 := by omega
    have h49R_sq : 81 * (K - 1) ^ 2 ≤ 49 * (R * R) := by
      have hmul := Nat.mul_le_mul h7R_lo h7R_lo
      linarith
    have h31K : 31 * (K - 1) ≤ (K - 1) ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul_right (K - 1) (by omega)
    have hexp_N : 3 * R * (R + 1) = 3 * (R * R) + 3 * R := by ring
    have hN : 2 * (K - 1) ^ 2 + 2 ≤ 3 * R * (R + 1) - 1 := by omega
    have hgood := goodMultiplicitySet_hex_911_ge K R (by omega) hN
    omega
  · rcases (by omega : K = 9 ∨ K = 10 ∨ K = 12 ∨ K = 13 ∨ K = 14 ∨ K = 16 ∨ K = 17 ∨
      K = 19 ∨ K = 20 ∨ K = 21 ∨ K = 23 ∨ K = 24 ∨ K = 25 ∨ K = 26 ∨ K = 27 ∨
      K = 28 ∨ K = 30 ∨ K = 31) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h := goodMultiplicitySet_hex_911_ge 9 11 (by omega) (by omega)
      change 0 < (goodMultiplicitySet 9 (3 * 11 * (11 + 1) - 1)).card; omega
    · have h := goodMultiplicitySet_hex_911_ge 10 12 (by omega) (by omega)
      change 0 < (goodMultiplicitySet 10 (3 * 12 * (12 + 1) - 1)).card; omega
    · have h := goodMultiplicitySet_hex_911_ge 12 15 (by omega) (by omega)
      change 0 < (goodMultiplicitySet 12 (3 * 15 * (15 + 1) - 1)).card; omega
    · have h := goodMultiplicitySet_hex_911_ge 13 16 (by omega) (by omega)
      change 0 < (goodMultiplicitySet 13 (3 * 16 * (16 + 1) - 1)).card; omega
    · have h := goodMultiplicitySet_hex_911_ge 14 17 (by omega) (by omega)
      change 0 < (goodMultiplicitySet 14 (3 * 17 * (17 + 1) - 1)).card; omega
    · have h := goodMultiplicitySet_hex_911_ge 16 20 (by omega) (by omega)
      change 0 < (goodMultiplicitySet 16 (3 * 20 * (20 + 1) - 1)).card; omega
    · have h := goodMultiplicitySet_hex_911_ge 17 21 (by omega) (by omega)
      change 0 < (goodMultiplicitySet 17 (3 * 21 * (21 + 1) - 1)).card; omega
    · have h := goodMultiplicitySet_hex_911_ge 19 24 (by omega) (by omega)
      change 0 < (goodMultiplicitySet 19 (3 * 24 * (24 + 1) - 1)).card; omega
    · have h := goodMultiplicitySet_hex_911_ge 20 25 (by omega) (by omega)
      change 0 < (goodMultiplicitySet 20 (3 * 25 * (25 + 1) - 1)).card; omega
    · have h := goodMultiplicitySet_hex_911_ge 21 26 (by omega) (by omega)
      change 0 < (goodMultiplicitySet 21 (3 * 26 * (26 + 1) - 1)).card; omega
    · have h := goodMultiplicitySet_hex_911_ge 23 29 (by omega) (by omega)
      change 0 < (goodMultiplicitySet 23 (3 * 29 * (29 + 1) - 1)).card; omega
    · have h := goodMultiplicitySet_hex_911_ge 24 30 (by omega) (by omega)
      change 0 < (goodMultiplicitySet 24 (3 * 30 * (30 + 1) - 1)).card; omega
    · have h := goodMultiplicitySet_hex_911_ge 25 31 (by omega) (by omega)
      change 0 < (goodMultiplicitySet 25 (3 * 31 * (31 + 1) - 1)).card; omega
    · have h := goodMultiplicitySet_hex_911_ge 26 33 (by omega) (by omega)
      change 0 < (goodMultiplicitySet 26 (3 * 33 * (33 + 1) - 1)).card; omega
    · have h := goodMultiplicitySet_hex_911_ge 27 34 (by omega) (by omega)
      change 0 < (goodMultiplicitySet 27 (3 * 34 * (34 + 1) - 1)).card; omega
    · have h := goodMultiplicitySet_hex_911_ge 28 35 (by omega) (by omega)
      change 0 < (goodMultiplicitySet 28 (3 * 35 * (35 + 1) - 1)).card; omega
    · have h := goodMultiplicitySet_hex_911_ge 30 38 (by omega) (by omega)
      change 0 < (goodMultiplicitySet 30 (3 * 38 * (38 + 1) - 1)).card; omega
    · have h := goodMultiplicitySet_hex_911_ge 31 39 (by omega) (by omega)
      change 0 < (goodMultiplicitySet 31 (3 * 39 * (39 + 1) - 1)).card; omega

/-- Exact `3 * R * (R + 1) - 1` (`R = (9 * K - 3) / 7`) first-occurrence bound for every `K ≥ 1`. -/
theorem exists_le_three_mul_9_K_sub_3_div_7_hasAtLeastKMinimizers (K : ℕ) (hK : 1 ≤ K) :
    let R := (9 * K - 3) / 7
    ∃ n ≤ 3 * R * (R + 1) - 1, HasAtLeastKNonsimilarMinimizers K n := by
  dsimp
  by_cases hK9 : 9 ≤ K
  · by_cases h11 : K = 11
    · subst h11; obtain ⟨n, hn, h⟩ := exists_le_495_has_eleven_minimizers; exact ⟨n, by omega, h⟩
    · by_cases h15 : K = 15
      · subst h15; obtain ⟨n, hn, h⟩ := exists_le_911_has_fifteen_minimizers; exact ⟨n, by omega, h⟩
      · by_cases h18 : K = 18
        · subst h18; obtain ⟨n, hn, h⟩ := exists_le_1517_has_eighteen_minimizers; exact ⟨n, by omega, h⟩
        · by_cases h22 : K = 22
          · subst h22; obtain ⟨n, hn, h⟩ := exists_le_2267_has_twenty_two_minimizers; exact ⟨n, by omega, h⟩
          · by_cases h29 : K = 29
            · subst h29; obtain ⟨n, hn, h⟩ := exists_le_3995_has_twenty_nine_minimizers; exact ⟨n, by omega, h⟩
            · exact exists_le_of_goodMultiplicitySet_pos
                (goodMultiplicitySet_9_K_sub_3_div_7_pos K hK9 h11 h15 h18 h22 h29)
  · rcases (by omega : K = 1 ∨ K = 2 ∨ K = 3 ∨ K = 4 ∨ K = 5 ∨ K = 6 ∨ K = 7 ∨ K = 8) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by omega, hasAtLeastOneMinimizer 0⟩
    · exact ⟨4, by omega, hasAtLeastTwoMinimizers_four_six_seven.1⟩
    · obtain ⟨n, hn, h⟩ := exists_le_35_has_three_minimizers; exact ⟨n, by omega, h⟩
    · obtain ⟨n, hn, h⟩ := exists_le_59_has_four_minimizers; exact ⟨n, by omega, h⟩
    · obtain ⟨n, hn, h⟩ := exists_le_99_has_five_minimizers; exact ⟨n, by omega, h⟩
    · obtain ⟨n, hn, h⟩ := exists_le_145_has_six_minimizers; exact ⟨n, by omega, h⟩
    · obtain ⟨n, hn, h⟩ := exists_le_197_has_seven_minimizers; exact ⟨n, by omega, h⟩
    · obtain ⟨n, hn, h⟩ := exists_le_265_has_eight_minimizers; exact ⟨n, by omega, h⟩

/-- **Universal `100 * n < 499 * K^2` (`n < 4.99 * K^2`) first-occurrence theorem**
for all `K ≥ 1` (breaking the `5 K^2` barrier). -/
theorem exists_mul_100_lt_499_mul_sq_hasAtLeastKMinimizers (K : ℕ) (hK : 1 ≤ K) :
    ∃ n, 100 * n < 499 * K ^ 2 ∧ HasAtLeastKNonsimilarMinimizers K n := by
  obtain ⟨n, hn, hmin⟩ := exists_le_three_mul_9_K_sub_3_div_7_hasAtLeastKMinimizers K hK
  by_cases hK18 : 18 ≤ K
  · let R := (9 * K - 3) / 7
    have hR22 : 22 ≤ R := by dsimp [R]; omega
    have h7R : 7 * R ≤ 9 * K - 3 := by dsimp [R]; omega
    change n ≤ 3 * R * (R + 1) - 1 at hn
    have h7R1 : 7 * (R + 1) ≤ 9 * K + 4 := by omega
    have hmul : (7 * R) * (7 * (R + 1)) ≤ (9 * K - 3) * (9 * K + 4) :=
      Nat.mul_le_mul h7R h7R1
    have hexp1 : 3 * ((7 * R) * (7 * (R + 1))) = 49 * (3 * R * (R + 1)) := by ring
    have hexp2 : (9 * K - 3) * (9 * K + 4) + 12 = 81 * K ^ 2 + 9 * K := by
      rcases K with _ | K
      · omega
      · have h1 : 9 * (K + 1) - 3 = 9 * K + 6 := by omega
        rw [h1]; ring
    have h18K : 18 * K ≤ K ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul_right K hK18
    exact ⟨n, by omega, hmin⟩
  · rcases (by omega : K = 1 ∨ K = 2 ∨ K = 3 ∨ K = 4 ∨ K = 5 ∨ K = 6 ∨ K = 7 ∨ K = 8 ∨ K = 9 ∨
      K = 10 ∨ K = 11 ∨ K = 12 ∨ K = 13 ∨ K = 14 ∨ K = 15 ∨ K = 16 ∨ K = 17) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by omega, hasAtLeastOneMinimizer 0⟩
    · exact ⟨4, by omega, hasAtLeastTwoMinimizers_four_six_seven.1⟩
    · obtain ⟨m, hm, h⟩ := exists_le_35_has_three_minimizers; exact ⟨m, by omega, h⟩
    · obtain ⟨m, hm, h⟩ := exists_le_59_has_four_minimizers; exact ⟨m, by omega, h⟩
    · obtain ⟨m, hm, h⟩ := exists_le_99_has_five_minimizers; exact ⟨m, by omega, h⟩
    · obtain ⟨m, hm, h⟩ := exists_le_145_has_six_minimizers; exact ⟨m, by omega, h⟩
    · obtain ⟨m, hm, h⟩ := exists_le_197_has_seven_minimizers; exact ⟨m, by omega, h⟩
    · obtain ⟨m, hm, h⟩ := exists_le_265_has_eight_minimizers; exact ⟨m, by omega, h⟩
    · obtain ⟨m, hm, h⟩ := exists_le_343_has_nine_minimizers; exact ⟨m, by omega, h⟩
    · obtain ⟨m, hm, h⟩ := exists_le_415_has_ten_minimizers; exact ⟨m, by omega, h⟩
    · obtain ⟨m, hm, h⟩ := exists_le_495_has_eleven_minimizers; exact ⟨m, by omega, h⟩
    · obtain ⟨m, hm, h⟩ := exists_le_593_has_twelve_minimizers; exact ⟨m, by omega, h⟩
    · obtain ⟨m, hm, h⟩ := exists_le_697_has_thirteen_minimizers; exact ⟨m, by omega, h⟩
    · obtain ⟨m, hm, h⟩ := exists_le_813_has_fourteen_minimizers; exact ⟨m, by omega, h⟩
    · obtain ⟨m, hm, h⟩ := exists_le_911_has_fifteen_minimizers; exact ⟨m, by omega, h⟩
    · exact ⟨n, by omega, hmin⟩
    · exact ⟨n, by omega, hmin⟩

/-- **Universal `n < 5 * K^2` first-occurrence theorem** for all `K ≥ 1`
(breaking the `5 * K^2` barrier, down from `6 * K^2` and `5.88 * K^2`). -/
theorem exists_lt_five_mul_sq_hasAtLeastKMinimizers (K : ℕ) (hK : 1 ≤ K) :
    ∃ n < 5 * K ^ 2, HasAtLeastKNonsimilarMinimizers K n := by
  obtain ⟨n, hn, hmin⟩ := exists_mul_100_lt_499_mul_sq_hasAtLeastKMinimizers K hK
  exact ⟨n, by omega, hmin⟩

end Erdos91.FourFamilySub30SlopeAndSub5KSquared

set_option pp.explicit false

set_option pp.explicit false

namespace Erdos91.FourFamilySub30SlopeAndSub5KSquared

theorem erdos91_eventually_iff_strict_rises :
    (∀ᶠ n : ℕ in Filter.atTop, ¬ PlateauDefinitions91.UniqueMinimizer n) ↔
      (∀ᶠ n : ℕ in Filter.atTop,
        Minimizer91.minimalDistinctDistances n < Minimizer91.minimalDistinctDistances (n + 1) →
          ¬ PlateauDefinitions91.UniqueMinimizer n) := by
  constructor
  · intro h
    exact h.mono (fun _ hn _ => hn)
  · intro h
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp h
    rw [Filter.eventually_atTop]
    refine ⟨max N0 18, ?_⟩
    intro n hn
    have hn0 : N0 ≤ n := le_trans (le_max_left _ _) hn
    have hn18 : 18 ≤ n := le_trans (le_max_right _ _) hn
    intro huniq
    have hrise := Erdos91.TriangularLatticeDisksAndConstantFiveException.uniqueMinimizer_imp_strict_rise_18 n hn18 huniq
    exact hN0 n hn0 hrise huniq

theorem unconditional_frequently_hasAtLeastKMinimizers (K : ℕ) :
    ∃ᶠ n : ℕ in Filter.atTop, Erdos91.GeneralMultiplicityAndDensityOne.HasAtLeastKNonsimilarMinimizers K n := by
  rw [Filter.frequently_atTop]
  intro M
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (eventually_goodMultiplicitySet_five_gt_two K)
  let N := max N0 (3 * M)
  have h5 := hN0 N (le_max_left _ _)
  have hNM : 3 * M ≤ N := le_max_right _ _
  have hcard : M < (Erdos91.AsymptoticDensityOneAndGlobalBounds.goodMultiplicitySet K N).card := by omega
  have hnot_sub : ¬ Erdos91.AsymptoticDensityOneAndGlobalBounds.goodMultiplicitySet K N ⊆ Finset.range M := by
    intro hsub
    have hle := Finset.card_le_card hsub
    rw [Finset.card_range] at hle
    omega
  obtain ⟨n, hn_good, hn_not_range⟩ := Finset.not_subset.mp hnot_sub
  rw [Finset.mem_range, not_lt] at hn_not_range
  have hn_prop : Erdos91.GeneralMultiplicityAndDensityOne.HasAtLeastKNonsimilarMinimizers K n :=
    (Finset.mem_filter.mp hn_good).2
  exact ⟨n, hn_not_range, hn_prop⟩

end Erdos91.FourFamilySub30SlopeAndSub5KSquared
