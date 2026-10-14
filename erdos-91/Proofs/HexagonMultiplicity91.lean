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

public import TriangularDisksAndEisenstein91

@[expose] public section

namespace Erdos91.SymbolicHexagonExactCardinalityAndDistanceSet
set_option maxRecDepth 20000
open Finset Minimizer91 PlateauDefinitions91
open Erdos91.Grid20Exact179DistancesAndFullCertificate (isStrictlyIncreasing pairwise_lt_of_isStrictlyIncreasing)
open Erdos91.TriangularLatticeHexagonAndSub130Majority (triPoint triPoint_injective triNormSq triNorm card_image_triNorm_eq_card_image_triNormSq triOffset dist_triPoint_sq_eq_triNormSq dist_triPoint_eq hexRowList hexCoordsList hexCoords hexSet card_hexCoords card_hexSet mem_hexCoords triUtpRowList triUtpList triUtp card_triUtp_le mem_triUtp_of_bounds triOffset_mem_triUtp distanceSet_hexSet_subset triRedundant36U triRedundant36V triRedundant36U_nodup triRedundant36U_valid hexRedundantPred hexRedundantList hexRedundant card_hexRedundant hexRedundant_subset_triUtp triUtp_image_subset_sdiff triUtpFold mem_triUtp_iff card_triUtp_two_mul_le hexCompFold mem_hexCoords_iff three_mul_R_succ_add_one_le_card_hexSet)

def hexCompUnfold (R : ℕ) (uv : ℕ × ℕ) : ℕ × ℕ :=
  if uv.1 + uv.2 < R then uv else (uv.1 + R + 1, uv.2 + R)

theorem hexCompFold_unfold (R : ℕ) {uv : ℕ × ℕ}
    (huv : uv ∈ Finset.range R ×ˢ Finset.range (R + 1)) :
    hexCompFold R (hexCompUnfold R uv) = uv := by
  rcases uv with ⟨u, v⟩
  simp only [Finset.mem_product, Finset.mem_range] at huv
  unfold hexCompUnfold hexCompFold
  dsimp
  split_ifs with h1 h2
  · rfl
  · omega
  · exact Prod.ext (by omega) (by omega)

theorem hexCompUnfold_mem_sdiff (R : ℕ) {uv : ℕ × ℕ}
    (huv : uv ∈ Finset.range R ×ˢ Finset.range (R + 1)) :
    hexCompUnfold R uv ∈
      (Finset.range (2 * R + 1) ×ˢ Finset.range (2 * R + 1)) \
        hexCoords (2 * R + 1) R (2 * R) := by
  rcases uv with ⟨u, v⟩
  simp only [Finset.mem_product, Finset.mem_range] at huv
  rw [Finset.mem_sdiff, Finset.mem_product, Finset.mem_range, Finset.mem_range, mem_hexCoords_iff]
  unfold hexCompUnfold
  dsimp
  split_ifs with h1
  · refine ⟨⟨by omega, by omega⟩, by omega⟩
  · refine ⟨⟨by omega, by omega⟩, by omega⟩

theorem rect_subset_image_hexCompFold (R : ℕ) :
    Finset.range R ×ˢ Finset.range (R + 1) ⊆
      ((Finset.range (2 * R + 1) ×ˢ Finset.range (2 * R + 1)) \
        hexCoords (2 * R + 1) R (2 * R)).image (hexCompFold R) := by
  intro uv huv
  exact Finset.mem_image.mpr ⟨hexCompUnfold R uv, hexCompUnfold_mem_sdiff R huv, hexCompFold_unfold R huv⟩

theorem card_sdiff_hexCoords_ge (R : ℕ) :
    R * (R + 1) ≤
      ((Finset.range (2 * R + 1) ×ˢ Finset.range (2 * R + 1)) \
        hexCoords (2 * R + 1) R (2 * R)).card := by
  have h1 := Finset.card_le_card (rect_subset_image_hexCompFold R)
  rw [Finset.card_product, Finset.card_range, Finset.card_range] at h1
  exact h1.trans Finset.card_image_le

theorem card_hexCoords_regular_le (R : ℕ) :
    (hexCoords (2 * R + 1) R (2 * R)).card ≤ 3 * R * (R + 1) + 1 := by
  classical
  let Sq := Finset.range (2 * R + 1) ×ˢ Finset.range (2 * R + 1)
  let H := hexCoords (2 * R + 1) R (2 * R)
  have hH_sub : H ⊆ Sq := by
    intro p hp
    obtain ⟨hx, hy, _, _⟩ := (mem_hexCoords_iff (2 * R + 1) R (2 * R) p).mp hp
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hx, Finset.mem_range.mpr hy⟩
  have hpart : (Sq \ H).card + H.card = (2 * R + 1) * (2 * R + 1) := by
    have h1 := Finset.card_sdiff_add_card_eq_card hH_sub
    rw [Finset.card_product, Finset.card_range] at h1
    exact h1
  have hge := card_sdiff_hexCoords_ge R
  change R * (R + 1) ≤ (Sq \ H).card at hge
  have hexp : (2 * R + 1) * (2 * R + 1) = 3 * R * (R + 1) + 1 + R * (R + 1) := by ring
  change H.card ≤ 3 * R * (R + 1) + 1
  omega

/-- **Exact symbolic cardinality of the regular hexagonal grid `hexSet (2R + 1) R (2R)`:**
for every `R : ℕ`, `(hexSet (2 * R + 1) R (2 * R)).card = 3 * R * (R + 1) + 1`. -/
theorem card_hexSet_regular_eq (R : ℕ) :
    (hexSet (2 * R + 1) R (2 * R)).card = 3 * R * (R + 1) + 1 := by
  have hlo := three_mul_R_succ_add_one_le_card_hexSet R
  have hhi : (hexSet (2 * R + 1) R (2 * R)).card ≤ 3 * R * (R + 1) + 1 := by
    unfold hexSet
    rw [Finset.card_image_of_injective _ triPoint_injective]
    exact card_hexCoords_regular_le R
  omega



end Erdos91.SymbolicHexagonExactCardinalityAndDistanceSet

/-! ## Exact Regular-Hexagon Cardinalities and Distance Counts for `R = 1..18` (`7` to `1027` Points, `3` to `308` Distances) and Exact Odd-Radius Norm Counts `m = 1..35` -/

namespace Erdos91.ExactHexagonDistanceCountsR1To18
set_option maxRecDepth 20000
open Finset Minimizer91
open Erdos91.TriangularLatticeHexagonAndSub130Majority (triNormSq hexSet triUtp minimalDistinctDistances_hexCoords_le)
open Erdos91.SymbolicHexagonExactCardinalityAndDistanceSet (card_hexSet_regular_eq)

end Erdos91.ExactHexagonDistanceCountsR1To18

/-! ## Central Inversion Symmetry `∑_{x ∈ H_R} (x - triPoint(R, R)) = 0`, Exact Closed-Form Hexagonal Row Energies, Symbolic Diameter Pair `(triPoint(0, R), triPoint(2R, R))`, 2D-Sector Nonsimilar Single-Point Deletion Theorem (`1 + |(triUtp R).image triNormSq|` Classes), and `R = 1..36` Certificates up to `309` Nonsimilar `3996`-Point Deletions -/

namespace Erdos91.HexagonCentralSymmetryEnergyAndNonsimilarDeletions
set_option maxRecDepth 20000
open Finset Minimizer91 PlateauDefinitions91
open EnergyLevels91 (energy)
open Erdos91.SmallCasesAndSquareBarrier (plane_dist_sq)
open Erdos91.FourNonuniqueAndDoubleEquilateral (plane_ext)
open Erdos91.ExactGridEnergyAndDeletionFamilies (exists_rep_subset_card_eq_image)
open Erdos91.TriangularLatticeHexagonAndSub130Majority (triPoint triPoint_injective triNormSq triNorm triOffset dist_triPoint_sq_eq_triNormSq dist_triPoint_eq hexCoords hexSet mem_hexCoords triUtpRowList triUtp mem_triUtp_of_bounds triOffset_mem_triUtp hexRedundantList mem_triUtp_iff mem_hexCoords_iff)
open Erdos91.SymbolicHexagonExactCardinalityAndDistanceSet (card_hexSet_regular_eq)


/-- Central inversion `(x, y) ↦ (2R - x, 2R - y)` on `hexCoords (2R + 1) R (2R)`. -/
def hexInv (R : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  (2 * R - p.1, 2 * R - p.2)

theorem hexInv_involutive_on_hexCoords (R : ℕ) {p : ℕ × ℕ}
    (hp : p ∈ hexCoords (2 * R + 1) R (2 * R)) :
    hexInv R (hexInv R p) = p := by
  obtain ⟨hx, hy, _, _⟩ := (mem_hexCoords_iff (2 * R + 1) R (2 * R) p).mp hp
  rcases p with ⟨x, y⟩
  dsimp at hx hy
  unfold hexInv
  exact Prod.ext (by omega) (by omega)

theorem hexInv_mem_hexCoords (R : ℕ) {p : ℕ × ℕ}
    (hp : p ∈ hexCoords (2 * R + 1) R (2 * R)) :
    hexInv R p ∈ hexCoords (2 * R + 1) R (2 * R) := by
  obtain ⟨hx, hy, hc1, hc2⟩ := (mem_hexCoords_iff (2 * R + 1) R (2 * R) p).mp hp
  rw [mem_hexCoords_iff]
  unfold hexInv
  dsimp
  omega

theorem hexInv_injOn_hexCoords (R : ℕ) :
    Set.InjOn (hexInv R) (hexCoords (2 * R + 1) R (2 * R) : Set (ℕ × ℕ)) := by
  intro p hp q hq heq
  rw [← hexInv_involutive_on_hexCoords R hp, ← hexInv_involutive_on_hexCoords R hq, heq]

theorem image_hexInv_hexCoords (R : ℕ) :
    (hexCoords (2 * R + 1) R (2 * R)).image (hexInv R) = hexCoords (2 * R + 1) R (2 * R) := by
  ext p
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hexInv_mem_hexCoords R hq
  · intro hp
    exact ⟨hexInv R p, hexInv_mem_hexCoords R hp, hexInv_involutive_on_hexCoords R hp⟩

theorem triPoint_sub_center_hexInv (R : ℕ) {p : ℕ × ℕ}
    (hp : p ∈ hexCoords (2 * R + 1) R (2 * R)) :
    triPoint (hexInv R p) - triPoint (R, R) = -(triPoint p - triPoint (R, R)) := by
  obtain ⟨hx, hy, _, _⟩ := (mem_hexCoords_iff (2 * R + 1) R (2 * R) p).mp hp
  rcases p with ⟨x, y⟩
  dsimp at hx hy
  have hx_le : x ≤ 2 * R := by omega
  have hy_le : y ≤ 2 * R := by omega
  apply plane_ext
  · change (2 * ((2 * R - x : ℕ) : ℝ) + ((2 * R - y : ℕ) : ℝ)) - (2 * (R : ℝ) + (R : ℝ)) =
      -((2 * (x : ℝ) + (y : ℝ)) - (2 * (R : ℝ) + (R : ℝ)))
    push_cast [hx_le, hy_le]
    ring
  · change Real.sqrt 3 * ((2 * R - y : ℕ) : ℝ) - Real.sqrt 3 * (R : ℝ) =
      -(Real.sqrt 3 * (y : ℝ) - Real.sqrt 3 * (R : ℝ))
    push_cast [hy_le]
    ring

theorem eq_zero_of_eq_neg_plane {v : Plane} (h : v = -v) : v = 0 := by
  have h0 : v 0 = -v 0 := congrArg (fun x : Plane => x 0) h
  have h1 : v 1 = -v 1 := congrArg (fun x : Plane => x 1) h
  apply plane_ext
  · change v 0 = 0; linarith
  · change v 1 = 0; linarith

/-- **Exact central symmetry of `hexSet (2R + 1) R (2R)` around `triPoint (R, R)`:**
for every `R : ℕ`, `∑ x ∈ hexSet (2 * R + 1) R (2 * R), (x - triPoint (R, R)) = 0`. -/
theorem sum_sub_center_hexSet_eq_zero (R : ℕ) :
    (∑ x ∈ hexSet (2 * R + 1) R (2 * R), (x - triPoint (R, R))) = 0 := by
  classical
  let H := hexCoords (2 * R + 1) R (2 * R)
  let c := triPoint (R, R)
  unfold hexSet
  rw [Finset.sum_image (fun _ _ _ _ h => triPoint_injective h)]
  apply eq_zero_of_eq_neg_plane
  calc
    (∑ p ∈ H, (triPoint p - c))
        = ∑ p ∈ H.image (hexInv R), (triPoint p - c) := by rw [image_hexInv_hexCoords R]
    _ = ∑ p ∈ H, (triPoint (hexInv R p) - c) :=
        Finset.sum_image (fun p hp q hq h => hexInv_injOn_hexCoords R hp hq h)
    _ = ∑ p ∈ H, -(triPoint p - c) :=
        Finset.sum_congr rfl (fun p hp => triPoint_sub_center_hexInv R hp)
    _ = -(∑ p ∈ H, (triPoint p - c)) := Finset.sum_neg_distrib (f := fun p => triPoint p - c)

/-- **Exact closed-form row energy on `hexSet (2R + 1) R (2R)`:**
for every `R : ℕ` and `v : Plane`,
`energy (hexSet (2R + 1) R (2R)) v = (3R(R + 1) + 1) * dist v (triPoint (R, R))^2 + ∑ x ∈ hexSet (2R + 1) R (2R), dist x (triPoint (R, R))^2`. -/
theorem energy_hexSet_regular_eq (R : ℕ) (v : Plane) :
    energy (hexSet (2 * R + 1) R (2 * R)) v =
      ((3 * R * (R + 1) + 1 : ℕ) : ℝ) * dist v (triPoint (R, R)) ^ 2 +
        ∑ x ∈ hexSet (2 * R + 1) R (2 * R), dist x (triPoint (R, R)) ^ 2 := by
  have h := Energy91.centered_energy (hexSet (2 * R + 1) R (2 * R))
    (triPoint (R, R)) v (sum_sub_center_hexSet_eq_zero R)
  rw [card_hexSet_regular_eq R] at h
  exact h

/-- **Exact row-energy difference identity on `hexSet (2R + 1) R (2R)`:**
`energy S_R u - energy S_R v = (3R(R + 1) + 1) * (dist u (triPoint (R, R))^2 - dist v (triPoint (R, R))^2)`. -/
theorem energy_hexSet_regular_sub_eq (R : ℕ) (u v : Plane) :
    energy (hexSet (2 * R + 1) R (2 * R)) u - energy (hexSet (2 * R + 1) R (2 * R)) v =
      ((3 * R * (R + 1) + 1 : ℕ) : ℝ) *
        (dist u (triPoint (R, R)) ^ 2 - dist v (triPoint (R, R)) ^ 2) := by
  rw [energy_hexSet_regular_eq R u, energy_hexSet_regular_eq R v]
  ring

theorem mem_hexCoords_diam_left (R : ℕ) :
    (0, R) ∈ hexCoords (2 * R + 1) R (2 * R) := by
  rw [mem_hexCoords_iff]; dsimp; omega

theorem mem_hexCoords_diam_right (R : ℕ) :
    (2 * R, R) ∈ hexCoords (2 * R + 1) R (2 * R) := by
  rw [mem_hexCoords_iff]; dsimp; omega

theorem mem_hexSet_diam_left (R : ℕ) :
    triPoint (0, R) ∈ hexSet (2 * R + 1) R (2 * R) :=
  Finset.mem_image_of_mem triPoint (mem_hexCoords_diam_left R)

theorem mem_hexSet_diam_right (R : ℕ) :
    triPoint (2 * R, R) ∈ hexSet (2 * R + 1) R (2 * R) :=
  Finset.mem_image_of_mem triPoint (mem_hexCoords_diam_right R)

theorem diam_pair_hexSet_ne (R : ℕ) (hR : 1 ≤ R) :
    triPoint (0, R) ≠ triPoint (2 * R, R) := by
  intro heq
  have hinj := triPoint_injective heq
  simp only [Prod.mk.injEq] at hinj
  omega

theorem dist_sq_diam_pair_hexSet (R : ℕ) :
    dist (triPoint (0, R)) (triPoint (2 * R, R)) ^ 2 = ((16 * R * R : ℕ) : ℝ) := by
  rw [dist_triPoint_sq_eq_triNormSq]
  have hdx : Nat.dist 0 (2 * R) = 2 * R := by unfold Nat.dist; omega
  have hdy : Nat.dist R R = 0 := by unfold Nat.dist; omega
  have hoff : triOffset (0, R) (2 * R, R) = (0, 2 * R) := by
    unfold triOffset; dsimp; rw [hdx, hdy]
    split_ifs <;> first | rfl | (apply Prod.ext <;> omega)
  rw [hoff]
  unfold triNormSq; dsimp; push_cast; ring

theorem triNormSq_le_four_mul_add_sq (u : ℕ × ℕ) :
    triNormSq u ≤ 4 * ((u.1 + u.2) * (u.1 + u.2)) := by
  unfold triNormSq
  nlinarith

/-- **Symbolic diameter bound on `hexSet (2R + 1) R (2R)`:**
every pair of points `x, y ∈ hexSet (2R + 1) R (2R)` satisfies
`dist x y ≤ dist (triPoint (0, R)) (triPoint (2R, R))`. -/
theorem dist_le_diam_pair_hexSet (R : ℕ) {x y : Plane}
    (hx : x ∈ hexSet (2 * R + 1) R (2 * R))
    (hy : y ∈ hexSet (2 * R + 1) R (2 * R)) :
    dist x y ≤ dist (triPoint (0, R)) (triPoint (2 * R, R)) := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
  by_cases hpq : p = q
  · subst hpq; rw [dist_self]; exact dist_nonneg
  · have hutp := triOffset_mem_triUtp (2 * R + 1) R (2 * R) (by omega) p q hpq hp hq
    obtain ⟨_, _, hsum⟩ := (mem_triUtp_iff (2 * R) (triOffset p q)).mp hutp
    have h1 := triNormSq_le_four_mul_add_sq (triOffset p q)
    have h2 : (triOffset p q).1 + (triOffset p q).2 ≤ 2 * R := hsum
    have h3 : ((triOffset p q).1 + (triOffset p q).2) * ((triOffset p q).1 + (triOffset p q).2) ≤
        (2 * R) * (2 * R) := Nat.mul_le_mul h2 h2
    have h4 : 4 * ((2 * R) * (2 * R)) = 16 * R * R := by ring
    have hnorm : triNormSq (triOffset p q) ≤ 16 * R * R := by omega
    have hsq_le : dist (triPoint p) (triPoint q) ^ 2 ≤ dist (triPoint (0, R)) (triPoint (2 * R, R)) ^ 2 := by
      rw [dist_triPoint_sq_eq_triNormSq, dist_sq_diam_pair_hexSet]
      exact_mod_cast hnorm
    rw [← Real.sqrt_sq dist_nonneg, ← Real.sqrt_sq (dist_nonneg (x := triPoint (0, R)))]
    exact Real.sqrt_le_sqrt hsq_le

end Erdos91.HexagonCentralSymmetryEnergyAndNonsimilarDeletions

/-! ## Universal Base-`M` Uniqueness (`mul_add_inj_of_lt`), Collision-Free Corner-Anchored Double-Point Deletions on `hexSet (2R+1) R (2R)` (`1 + (triUtp R).card` Classes for All `R ≥ 1` and `(m + 1)^2` Classes for All `R = 2m ≥ 2`), and `R = 1..36` Double-Deletion Certificates -/

namespace Erdos91.CornerSectorCollisionFreeDoubleDeletions
set_option maxRecDepth 100000
open Finset Minimizer91 PlateauDefinitions91
open EnergyLevels91 (energy)
open Erdos91.SmallCasesAndSquareBarrier (plane_dist_sq)
open Erdos91.FourNonuniqueAndDoubleEquilateral (plane_ext)
open Erdos91.TriangularLatticeHexagonAndSub130Majority (triPoint triPoint_injective triNormSq triNorm triOffset dist_triPoint_sq_eq_triNormSq hexCoords hexSet triUtpRowList triUtpList triUtp mem_triUtp_iff mem_hexCoords_iff)
open Erdos91.SymbolicHexagonExactCardinalityAndDistanceSet (card_hexSet_regular_eq)
open Erdos91.HexagonCentralSymmetryEnergyAndNonsimilarDeletions (energy_hexSet_regular_eq energy_hexSet_regular_sub_eq mem_hexSet_diam_left mem_hexSet_diam_right diam_pair_hexSet_ne dist_sq_diam_pair_hexSet dist_le_diam_pair_hexSet)

/-- **Universal base-`M` uniqueness theorem:**
if `r1 < M`, `r2 < M`, and `M * x1 + r1 = M * x2 + r2`, then `x1 = x2` and `r1 = r2`. -/
theorem mul_add_inj_of_lt {M x1 x2 r1 r2 : ℕ}
    (hr1 : r1 < M) (hr2 : r2 < M) (heq : M * x1 + r1 = M * x2 + r2) :
    x1 = x2 ∧ r1 = r2 := by
  have hx : x1 = x2 := by
    rcases lt_trichotomy x1 x2 with hlt | rfl | hgt
    · have h1 : M * (x1 + 1) ≤ M * x2 := Nat.mul_le_mul_left M hlt
      have h2 : M * (x1 + 1) = M * x1 + M := by ring
      omega
    · rfl
    · have h1 : M * (x2 + 1) ≤ M * x1 := Nat.mul_le_mul_left M hgt
      have h2 : M * (x2 + 1) = M * x2 + M := by ring
      omega
  subst hx
  exact ⟨rfl, by omega⟩

end Erdos91.CornerSectorCollisionFreeDoubleDeletions

/-! ## Collision-Free Exterior-Midpoint Single-Site Replacements `insert (triPoint (m, 4m + 1)) (H_{2m}.erase x)` (`(m + 1)^2` Pairwise Nonsimilar `(12m^2 + 6m + 1)`-Point Configurations for All `m ≥ 3`) -/

namespace Erdos91.HexagonSingleSiteReplacementAndStrictRiseFamilies
set_option maxRecDepth 100000
open Finset Minimizer91 PlateauDefinitions91
open EnergyLevels91 (energy)
open Erdos91.SmallCasesAndSquareBarrier (plane_dist_sq)
open Erdos91.TriangularLatticeHexagonAndSub130Majority (triPoint triPoint_injective triNormSq triNorm triOffset dist_triPoint_sq_eq_triNormSq hexCoords hexSet triUtp mem_triUtp_iff mem_hexCoords_iff)
open Erdos91.SymbolicHexagonExactCardinalityAndDistanceSet (card_hexSet_regular_eq)
open Erdos91.HexagonCentralSymmetryEnergyAndNonsimilarDeletions (energy_hexSet_regular_sub_eq mem_hexSet_diam_left mem_hexSet_diam_right diam_pair_hexSet_ne dist_sq_diam_pair_hexSet dist_le_diam_pair_hexSet)
open Erdos91.CornerSectorCollisionFreeDoubleDeletions (mul_add_inj_of_lt)

/-- Exterior top-edge midpoint `(m, 4m + 1)` lies strictly outside `hexCoords (4m + 1) (2m) (4m)`. -/
theorem exterior_top_midpoint_not_mem_hexCoords (m : ℕ) :
    (m, 4 * m + 1) ∉ hexCoords (4 * m + 1) (2 * m) (4 * m) := by
  rw [mem_hexCoords_iff]; dsimp; omega

theorem exterior_top_midpoint_not_mem_hexSet (m : ℕ) :
    triPoint (m, 4 * m + 1) ∉ hexSet (4 * m + 1) (2 * m) (4 * m) := by
  intro hmem
  obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hmem
  exact exterior_top_midpoint_not_mem_hexCoords m (triPoint_injective heq ▸ hp)

/-- **Exact polynomial cone bound for the exterior top-edge midpoint `(m, 4m + 1)`:**
for every `p = (x, y) ∈ hexCoords (4m + 1) (2m) (4m)`,
`dist (triPoint (m, 4m + 1)) (triPoint p)^2 ≤ 4 * (13m^2 + 7m + 1)`. -/
theorem dist_sq_exterior_top_midpoint_le_poly (m : ℕ)
    {p : ℕ × ℕ} (hp : p ∈ hexCoords (4 * m + 1) (2 * m) (4 * m)) :
    dist (triPoint (m, 4 * m + 1)) (triPoint p) ^ 2 ≤
      (4 * (13 * m * m + 7 * m + 1) : ℝ) := by
  obtain ⟨hx, hy, hc1, hc2⟩ := (mem_hexCoords_iff (4 * m + 1) (2 * m) (4 * m) p).mp hp
  rcases p with ⟨x, y⟩
  dsimp at hx hy hc1 hc2
  rw [plane_dist_sq]
  unfold triPoint
  dsimp
  change ((2 * (m : ℝ) + ((4 * m + 1 : ℕ) : ℝ)) - (2 * (x : ℝ) + (y : ℝ))) ^ 2 +
    (Real.sqrt 3 * ((4 * m + 1 : ℕ) : ℝ) - Real.sqrt 3 * (y : ℝ)) ^ 2 ≤ _
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h1 : (0 : ℝ) ≤ (x : ℝ) + (y : ℝ) - 2 * (m : ℝ) := by exact_mod_cast (show 0 ≤ (x : ℤ) + y - 2 * m by omega)
  have h2 : (0 : ℝ) ≤ 4 * (m : ℝ) + 1 - (x : ℝ) := by exact_mod_cast (show 0 ≤ 4 * (m : ℤ) + 1 - x by omega)
  have h3 : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
  have h4 : (0 : ℝ) ≤ 5 * (m : ℝ) + 1 - (y : ℝ) := by exact_mod_cast (show 0 ≤ 5 * (m : ℤ) + 1 - y by omega)
  have hprod1 : (0 : ℝ) ≤ ((x : ℝ) + (y : ℝ) - 2 * (m : ℝ)) * (4 * (m : ℝ) + 1 - (x : ℝ)) :=
    mul_nonneg h1 h2
  have hprod2 : (0 : ℝ) ≤ (y : ℝ) * (5 * (m : ℝ) + 1 - (y : ℝ)) :=
    mul_nonneg h3 h4
  push_cast
  have hid :
      4 * (13 * (m : ℝ) * (m : ℝ) + 7 * (m : ℝ) + 1) -
      (((2 * (m : ℝ) + (4 * (m : ℝ) + 1)) - (2 * (x : ℝ) + (y : ℝ))) ^ 2 +
        (Real.sqrt 3 * (4 * (m : ℝ) + 1) - Real.sqrt 3 * (y : ℝ)) ^ 2) =
      4 * (((x : ℝ) + (y : ℝ) - 2 * (m : ℝ)) * (4 * (m : ℝ) + 1 - (x : ℝ)) +
        (y : ℝ) * (5 * (m : ℝ) + 1 - (y : ℝ))) := by
    linear_combination -((4 * (m : ℝ) + 1 - (y : ℝ)) ^ 2) * hs3
  linarith

/-- **For all `m ≥ 3`, the exterior top-edge midpoint `(m, 4m + 1)` preserves the diameter `8m` of `hexSet (4m + 1) (2m) (4m)`:**
every `x, y ∈ insert (triPoint (m, 4m + 1)) (hexSet (4m + 1) (2m) (4m))` satisfies
`dist x y ≤ dist (triPoint (0, 2m)) (triPoint (4m, 2m))`. -/
theorem dist_le_diam_pair_insert_exterior_top_midpoint (m : ℕ) (hm : 3 ≤ m)
    {x y : Plane}
    (hx : x ∈ insert (triPoint (m, 4 * m + 1)) (hexSet (4 * m + 1) (2 * m) (4 * m)))
    (hy : y ∈ insert (triPoint (m, 4 * m + 1)) (hexSet (4 * m + 1) (2 * m) (4 * m))) :
    dist x y ≤ dist (triPoint (0, 2 * m)) (triPoint (4 * m, 2 * m)) := by
  have hdiam_sq : dist (triPoint (0, 2 * m)) (triPoint (4 * m, 2 * m)) ^ 2 =
      (64 * (m : ℝ) * (m : ℝ)) := by
    have h := dist_sq_diam_pair_hexSet (2 * m)
    change dist (triPoint (0, 2 * m)) (triPoint (2 * (2 * m), 2 * m)) ^ 2 = _ at h
    have h2 : 2 * (2 * m) = 4 * m := by omega
    rw [h2] at h
    rw [h]; push_cast; ring
  have hpoly_le : 4 * (13 * (m : ℝ) * (m : ℝ) + 7 * (m : ℝ) + 1) ≤ 64 * (m : ℝ) * (m : ℝ) := by
    have hm_real : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith
  rcases Finset.mem_insert.mp hx with rfl | hxH <;> rcases Finset.mem_insert.mp hy with rfl | hyH
  · rw [dist_self]; exact dist_nonneg
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hyH
    have hsq : dist (triPoint (m, 4 * m + 1)) (triPoint p) ^ 2 ≤
        dist (triPoint (0, 2 * m)) (triPoint (4 * m, 2 * m)) ^ 2 := by
      calc
        dist (triPoint (m, 4 * m + 1)) (triPoint p) ^ 2
            ≤ 4 * (13 * (m : ℝ) * (m : ℝ) + 7 * (m : ℝ) + 1) :=
          dist_sq_exterior_top_midpoint_le_poly m hp
        _ ≤ 64 * (m : ℝ) * (m : ℝ) := hpoly_le
        _ = dist (triPoint (0, 2 * m)) (triPoint (4 * m, 2 * m)) ^ 2 := hdiam_sq.symm
    rw [← Real.sqrt_sq dist_nonneg, ← Real.sqrt_sq (dist_nonneg (x := triPoint (0, 2 * m)))]
    exact Real.sqrt_le_sqrt hsq
  · rw [dist_comm]
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hxH
    have hsq : dist (triPoint (m, 4 * m + 1)) (triPoint p) ^ 2 ≤
        dist (triPoint (0, 2 * m)) (triPoint (4 * m, 2 * m)) ^ 2 := by
      calc
        dist (triPoint (m, 4 * m + 1)) (triPoint p) ^ 2
            ≤ 4 * (13 * (m : ℝ) * (m : ℝ) + 7 * (m : ℝ) + 1) :=
          dist_sq_exterior_top_midpoint_le_poly m hp
        _ ≤ 64 * (m : ℝ) * (m : ℝ) := hpoly_le
        _ = dist (triPoint (0, 2 * m)) (triPoint (4 * m, 2 * m)) ^ 2 := hdiam_sq.symm
    rw [← Real.sqrt_sq dist_nonneg, ← Real.sqrt_sq (dist_nonneg (x := triPoint (0, 2 * m)))]
    exact Real.sqrt_le_sqrt hsq
  · have h := dist_le_diam_pair_hexSet (2 * m) (x := x) (y := y)
    have h1 : 2 * (2 * m) + 1 = 4 * m + 1 := by omega
    have h2 : 2 * (2 * m) = 4 * m := by omega
    rw [h1, h2] at h
    exact h hxH hyH

end Erdos91.HexagonSingleSiteReplacementAndStrictRiseFamilies

/-! ## Central `(2m + 1) × (2m + 1)` Square Embedding `{(m + a, m + b) : 0 ≤ a, b ≤ 2m}` inside `hexSet (4m + 1) (2m) (4m)` — Universal `(2m + 1)^2 = 4m^2 + 4m + 1` Collision-Free Double-Point Deletion Multiplicity (Anchored at `(m, 4m - 1)`) and `(2m + 1)^2 = 4m^2 + 4m + 1` Collision-Free Single-Site Replacement Multiplicity (Anchored at `(m, 4m + 1)`) for All `m ≥ 3` -/

namespace Erdos91.HexagonCentralSquareFourMSquaredMultiplicity
set_option maxRecDepth 100000
open Finset Minimizer91 PlateauDefinitions91
open EnergyLevels91 (energy)
open Erdos91.SmallCasesAndSquareBarrier (plane_dist_sq)
open Erdos91.TriangularLatticeHexagonAndSub130Majority (triPoint triPoint_injective triNormSq triNorm triOffset dist_triPoint_sq_eq_triNormSq hexCoords hexSet mem_hexCoords_iff)
open Erdos91.SymbolicHexagonExactCardinalityAndDistanceSet (card_hexSet_regular_eq)
open Erdos91.HexagonCentralSymmetryEnergyAndNonsimilarDeletions (energy_hexSet_regular_sub_eq mem_hexSet_diam_left mem_hexSet_diam_right diam_pair_hexSet_ne dist_le_diam_pair_hexSet)
open Erdos91.CornerSectorCollisionFreeDoubleDeletions (mul_add_inj_of_lt)
open Erdos91.HexagonSingleSiteReplacementAndStrictRiseFamilies (exterior_top_midpoint_not_mem_hexSet dist_le_diam_pair_insert_exterior_top_midpoint)

/-- Unscaled integer Eisenstein norm `u.1^2 + u.1*u.2 + u.2^2` of `triOffset p (2m, 2m)`. -/
def centerQuad (m : ℕ) (p : ℕ × ℕ) : ℕ :=
  let w := triOffset p (2 * m, 2 * m)
  w.1 * w.1 + w.1 * w.2 + w.2 * w.2

theorem dist_sq_triPoint_center_eq_four_mul_centerQuad (m : ℕ) (p : ℕ × ℕ) :
    dist (triPoint p) (triPoint (2 * m, 2 * m)) ^ 2 =
      4 * (centerQuad m p : ℝ) := by
  rw [dist_triPoint_sq_eq_triNormSq]
  unfold centerQuad triNormSq
  push_cast
  ring

end Erdos91.HexagonCentralSquareFourMSquaredMultiplicity

/-! ## Clipped `(3m + 1) × (3m + 1)` Sub-Hexagon `hexSub3m` (`7m^2 + 5m` Vertices) and `(3m - 1) × (3m + 1)` Sub-Hexagon `hexSub3mDouble` (`7m^2 - m - 2` Vertices) — Universal `7m^2 + 5m` Single-Site Replacement Multiplicity and `7m^2 - m - 2` Double-Point Deletion Multiplicity on `hexSet (4m + 1) (2m) (4m)` for All `m ≥ 3` -/

namespace Erdos91.HexagonSevenMSquaredMultiplicity
set_option maxRecDepth 100000
open Finset Minimizer91 PlateauDefinitions91
open EnergyLevels91 (energy)
open Erdos91.SmallCasesAndSquareBarrier (plane_dist_sq)
open Erdos91.TriangularLatticeHexagonAndSub130Majority (triPoint triPoint_injective triNormSq triNorm triOffset dist_triPoint_sq_eq_triNormSq hexCoords hexSet mem_hexCoords_iff)
open Erdos91.SymbolicHexagonExactCardinalityAndDistanceSet (card_hexSet_regular_eq)
open Erdos91.HexagonCentralSymmetryEnergyAndNonsimilarDeletions (energy_hexSet_regular_sub_eq mem_hexSet_diam_left mem_hexSet_diam_right diam_pair_hexSet_ne dist_le_diam_pair_hexSet)
open Erdos91.CornerSectorCollisionFreeDoubleDeletions (mul_add_inj_of_lt)
open Erdos91.HexagonSingleSiteReplacementAndStrictRiseFamilies (exterior_top_midpoint_not_mem_hexSet dist_le_diam_pair_insert_exterior_top_midpoint)
open Erdos91.HexagonCentralSquareFourMSquaredMultiplicity (centerQuad dist_sq_triPoint_center_eq_four_mul_centerQuad)

/-- Lower-left corner triangle `{ p ∈ range (2m) ×ˢ range (2m) : p.1 + p.2 < 2m }`. -/
def lowerTri (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (2 * m) ×ˢ Finset.range (2 * m)).filter (fun p => p.1 + p.2 < 2 * m)

def lowerTriFold (m : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  if p.1 < m then p else (2 * m - 1 - p.1, 2 * m - p.2)

def lowerTriUnfold (m : ℕ) (uv : ℕ × ℕ) : ℕ × ℕ :=
  if uv.1 + uv.2 < 2 * m then uv else (2 * m - 1 - uv.1, 2 * m - uv.2)

theorem lowerTriFold_injOn (m : ℕ) :
    Set.InjOn (lowerTriFold m) (lowerTri m : Set (ℕ × ℕ)) := by
  intro ⟨x1, y1⟩ h1 ⟨x2, y2⟩ h2 heq
  simp only [lowerTri, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h1 h2
  unfold lowerTriFold at heq
  dsimp at heq
  split_ifs at heq with hx1 hx2 hx2'
  · exact heq
  · simp only [Prod.mk.injEq] at heq; omega
  · simp only [Prod.mk.injEq] at heq; omega
  · simp only [Prod.mk.injEq] at heq; exact Prod.ext (by omega) (by omega)

theorem image_lowerTriFold_subset (m : ℕ) :
    (lowerTri m).image (lowerTriFold m) ⊆ Finset.range m ×ˢ Finset.range (2 * m + 1) := by
  intro z hz
  obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hz
  simp only [lowerTri, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hxy
  simp only [lowerTriFold, Finset.mem_product, Finset.mem_range]
  split_ifs with hx
  · exact ⟨hx, by omega⟩
  · exact ⟨by omega, by omega⟩

theorem lowerTriFold_unfold (m : ℕ) {uv : ℕ × ℕ}
    (huv : uv ∈ Finset.range m ×ˢ Finset.range (2 * m + 1)) :
    lowerTriFold m (lowerTriUnfold m uv) = uv := by
  rcases uv with ⟨u, v⟩
  simp only [Finset.mem_product, Finset.mem_range] at huv
  unfold lowerTriUnfold lowerTriFold
  dsimp
  split_ifs with h1 h2 h3
  · rfl
  · omega
  · omega
  · exact Prod.ext (by omega) (by omega)

theorem lowerTriUnfold_mem_lowerTri (m : ℕ) {uv : ℕ × ℕ}
    (huv : uv ∈ Finset.range m ×ˢ Finset.range (2 * m + 1)) :
    lowerTriUnfold m uv ∈ lowerTri m := by
  rcases uv with ⟨u, v⟩
  simp only [Finset.mem_product, Finset.mem_range] at huv
  simp only [lowerTri, lowerTriUnfold, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  split_ifs with h1
  · exact ⟨⟨by omega, by omega⟩, h1⟩
  · exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem rect_subset_image_lowerTriFold (m : ℕ) :
    Finset.range m ×ˢ Finset.range (2 * m + 1) ⊆ (lowerTri m).image (lowerTriFold m) := by
  intro uv huv
  exact Finset.mem_image.mpr ⟨lowerTriUnfold m uv, lowerTriUnfold_mem_lowerTri m huv, lowerTriFold_unfold m huv⟩

/-- **Exact cardinality `(lowerTri m).card = m * (2m + 1)` for all `m : ℕ`:** -/
theorem card_lowerTri_eq (m : ℕ) : (lowerTri m).card = m * (2 * m + 1) := by
  have heq : (lowerTri m).image (lowerTriFold m) = Finset.range m ×ˢ Finset.range (2 * m + 1) :=
    Finset.Subset.antisymm (image_lowerTriFold_subset m) (rect_subset_image_lowerTriFold m)
  have hcard := congrArg Finset.card heq
  rw [Finset.card_image_of_injOn (lowerTriFold_injOn m), Finset.card_product,
    Finset.card_range, Finset.card_range] at hcard
  exact hcard

/-- Clipped `(3m + 1) × (3m + 1)` sub-hexagon `{ p ∈ range (3m+1) ×ˢ range (3m+1) : 2m ≤ p.1 + p.2 } \ {(0, 2m)}`. -/
def hexSub3m (m : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (3 * m + 1) ×ˢ Finset.range (3 * m + 1)).filter
    (fun p => 2 * m ≤ p.1 + p.2)).erase (0, 2 * m)

theorem filter_lt_eq_lowerTri (m a b : ℕ) (ha : 2 * m ≤ a) (hb : 2 * m ≤ b) :
    (Finset.range a ×ˢ Finset.range b).filter (fun p => ¬ 2 * m ≤ p.1 + p.2) = lowerTri m := by
  ext ⟨x, y⟩
  simp only [lowerTri, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨_, _⟩, hnot⟩; exact ⟨⟨by omega, by omega⟩, by omega⟩
  · rintro ⟨⟨_, _⟩, hlt⟩; exact ⟨⟨by omega, by omega⟩, by omega⟩

/-- **Exact symbolic cardinality `(hexSub3m m).card = 7m^2 + 5m` for all `m : ℕ`:** -/
theorem card_hexSub3m_eq (m : ℕ) : (hexSub3m m).card = 7 * m * m + 5 * m := by
  let B := Finset.range (3 * m + 1) ×ˢ Finset.range (3 * m + 1)
  let T := B.filter (fun p => 2 * m ≤ p.1 + p.2)
  let F := B.filter (fun p => ¬ 2 * m ≤ p.1 + p.2)
  have hpart : T.card + F.card = (3 * m + 1) * (3 * m + 1) := by
    have h := Finset.card_filter_add_card_filter_not (s := B) (p := fun p : ℕ × ℕ => 2 * m ≤ p.1 + p.2)
    have hB : B.card = (3 * m + 1) * (3 * m + 1) := by
      dsimp [B]; rw [Finset.card_product, Finset.card_range]
    simpa only [T, F, hB] using h
  have hF_eq : F = lowerTri m := filter_lt_eq_lowerTri m (3 * m + 1) (3 * m + 1) (by omega) (by omega)
  have hF_card : F.card = m * (2 * m + 1) := by rw [hF_eq, card_lowerTri_eq m]
  have hmem0 : (0, 2 * m) ∈ T := by
    simp only [T, B, Finset.mem_filter, Finset.mem_product, Finset.mem_range]; omega
  have her : (hexSub3m m).card + 1 = T.card := Finset.card_erase_add_one hmem0
  have hexp : (3 * m + 1) * (3 * m + 1) = (7 * m * m + 5 * m) + 1 + m * (2 * m + 1) := by ring
  omega

/-- Clipped `(3m - 1) × (3m + 1)` sub-hexagon `{ p ∈ range (3m-1) ×ˢ range (3m+1) : 2m ≤ p.1 + p.2 } \ {(0, 2m)}`. -/
def hexSub3mDouble (m : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (3 * m - 1) ×ˢ Finset.range (3 * m + 1)).filter
    (fun p => 2 * m ≤ p.1 + p.2)).erase (0, 2 * m)

/-- **Exact symbolic cardinality `(hexSub3mDouble m).card = 7m^2 - m - 2` for all `m ≥ 1`:** -/
theorem card_hexSub3mDouble_eq (m : ℕ) (hm : 1 ≤ m) :
    (hexSub3mDouble m).card = 7 * m * m - m - 2 := by
  let B := Finset.range (3 * m - 1) ×ˢ Finset.range (3 * m + 1)
  let T := B.filter (fun p => 2 * m ≤ p.1 + p.2)
  let F := B.filter (fun p => ¬ 2 * m ≤ p.1 + p.2)
  have hpart : T.card + F.card = (3 * m - 1) * (3 * m + 1) := by
    have h := Finset.card_filter_add_card_filter_not (s := B) (p := fun p : ℕ × ℕ => 2 * m ≤ p.1 + p.2)
    have hB : B.card = (3 * m - 1) * (3 * m + 1) := by
      dsimp [B]; rw [Finset.card_product, Finset.card_range, Finset.card_range]
    simpa only [T, F, hB] using h
  have hF_eq : F = lowerTri m := filter_lt_eq_lowerTri m (3 * m - 1) (3 * m + 1) (by omega) (by omega)
  have hF_card : F.card = m * (2 * m + 1) := by rw [hF_eq, card_lowerTri_eq m]
  have hmem0 : (0, 2 * m) ∈ T := by
    simp only [T, B, Finset.mem_filter, Finset.mem_product, Finset.mem_range]; omega
  have her : (hexSub3mDouble m).card + 1 = T.card := Finset.card_erase_add_one hmem0
  have h1 : (7 * m * m - m - 2) + 2 + m = 7 * m * m := by
    have : m + 2 ≤ 7 * m * m := by nlinarith
    omega
  have h2 : (3 * m - 1) * (3 * m + 1) + 1 = 9 * m * m := by
    zify [show 1 ≤ 3 * m by omega]; ring
  have h3 : 7 * m * m + m * (2 * m + 1) = 9 * m * m + m := by ring
  omega

theorem mem_hexSub3m_spec (m : ℕ) (hm : 1 ≤ m) {p : ℕ × ℕ} (hp : p ∈ hexSub3m m) :
    p ∈ hexCoords (4 * m + 1) (2 * m) (4 * m) ∧
    p ≠ (0, 2 * m) ∧ p ≠ (4 * m, 2 * m) ∧ p ≠ (m, 4 * m + 1) ∧
    p.1 ≤ 3 * m ∧ p.2 ≤ 3 * m := by
  rcases p with ⟨x, y⟩
  simp only [hexSub3m, Finset.mem_erase, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range] at hp
  rw [mem_hexCoords_iff]
  dsimp
  refine ⟨⟨by omega, by omega, hp.2.2, by omega⟩, hp.1, ?_, ?_, by omega, by omega⟩
  · intro h; simp only [Prod.mk.injEq] at h; omega
  · intro h; simp only [Prod.mk.injEq] at h; omega

theorem mem_hexSub3mDouble_spec (m : ℕ) (hm : 2 ≤ m) {p : ℕ × ℕ} (hp : p ∈ hexSub3mDouble m) :
    p ∈ hexCoords (4 * m + 1) (2 * m) (4 * m) ∧
    p ≠ (0, 2 * m) ∧ p ≠ (4 * m, 2 * m) ∧ p ≠ (m + 1, 4 * m - 1) ∧
    p.1 < 3 * m - 1 ∧ p.2 ≤ 3 * m := by
  rcases p with ⟨x, y⟩
  simp only [hexSub3mDouble, Finset.mem_erase, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range] at hp
  rw [mem_hexCoords_iff]
  dsimp
  refine ⟨⟨by omega, by omega, hp.2.2, by omega⟩, hp.1, ?_, ?_, hp.2.1.1, by omega⟩
  · intro h; simp only [Prod.mk.injEq] at h; omega
  · intro h; simp only [Prod.mk.injEq] at h; omega

/-- Unshifted squared-distance difference between `triPoint (m, 4m + 1)` and `triPoint (2m, 2m)`:
`dist(p, v0)^2 - dist(p, ctr)^2 = 4 * ((9m^2 + 7m + 1) - ((3m + 2)*p.2 + p.1))`. -/
theorem dist_sq_exterior_sub_center_point (m : ℕ) (p : ℕ × ℕ) :
    dist (triPoint p) (triPoint (m, 4 * m + 1)) ^ 2 -
      dist (triPoint p) (triPoint (2 * m, 2 * m)) ^ 2 =
      4 * ((9 * (m : ℝ) * (m : ℝ) + 9 * (m : ℝ) + 1) -
        ((3 * (m : ℝ) + 2) * (p.2 : ℝ) + (p.1 : ℝ))) := by
  rcases p with ⟨x, y⟩
  rw [plane_dist_sq, plane_dist_sq]
  unfold triPoint
  dsimp
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  push_cast
  linear_combination (((y : ℝ) - (4 * (m : ℝ) + 1)) ^ 2 -
    ((y : ℝ) - 2 * (m : ℝ)) ^ 2) * hs3

/-- Unshifted squared-distance difference between `triPoint (m + 1, 4m - 1)` and `triPoint (2m, 2m)`:
`dist(p, c2)^2 - dist(p, ctr)^2 = 4 * ((9m^2 - 3m + 1) - ((3m - 1)*p.2 + p.1))`. -/
theorem dist_sq_interior_shift_sub_center_point (m : ℕ) (hm : 1 ≤ m) (p : ℕ × ℕ) :
    dist (triPoint p) (triPoint (m + 1, 4 * m - 1)) ^ 2 -
      dist (triPoint p) (triPoint (2 * m, 2 * m)) ^ 2 =
      4 * ((9 * (m : ℝ) * (m : ℝ) - 3 * (m : ℝ) + 1) -
        ((3 * (m : ℝ) - 1) * (p.2 : ℝ) + (p.1 : ℝ))) := by
  rcases p with ⟨x, y⟩
  have hm4 : 1 ≤ 4 * m := by omega
  rw [plane_dist_sq, plane_dist_sq]
  unfold triPoint
  dsimp
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [Nat.cast_sub hm4]
  push_cast
  linear_combination (((y : ℝ) - (4 * (m : ℝ) - 1)) ^ 2 -
    ((y : ℝ) - 2 * (m : ℝ)) ^ 2) * hs3

/-- Collision-free integer single-site replacement key on `hexSub3m m`. -/
def hex7mReplaceKey (m : ℕ) (p : ℕ × ℕ) : ℕ :=
  (12 * m * m + 6 * m + 2) * centerQuad m p +
    ((9 * m * m + 9 * m) - ((3 * m + 2) * p.2 + p.1))

theorem hex7mReplaceKey_injOn (m : ℕ) (hm : 1 ≤ m) :
    Set.InjOn (hex7mReplaceKey m) ((hexSub3m m : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
  intro ⟨x1, y1⟩ h1 ⟨x2, y2⟩ h2 heq
  obtain ⟨_, _, _, _, hx1, hy1⟩ := mem_hexSub3m_spec m hm h1
  obtain ⟨_, _, _, _, hx2, hy2⟩ := mem_hexSub3m_spec m hm h2
  dsimp at hx1 hy1 hx2 hy2
  unfold hex7mReplaceKey at heq
  dsimp at heq
  have hle1 : (3 * m + 2) * y1 + x1 ≤ 9 * m * m + 9 * m := by nlinarith
  have hle2 : (3 * m + 2) * y2 + x2 ≤ 9 * m * m + 9 * m := by nlinarith
  have hgj : 9 * m * m + 9 * m < 12 * m * m + 6 * m + 2 := by nlinarith
  have hr1 : 9 * m * m + 9 * m - ((3 * m + 2) * y1 + x1) < 12 * m * m + 6 * m + 2 := by omega
  have hr2 : 9 * m * m + 9 * m - ((3 * m + 2) * y2 + x2) < 12 * m * m + 6 * m + 2 := by omega
  obtain ⟨_, hrem⟩ := mul_add_inj_of_lt hr1 hr2 heq
  have hlin : (3 * m + 2) * y1 + x1 = (3 * m + 2) * y2 + x2 := by omega
  obtain ⟨hy, hx⟩ := mul_add_inj_of_lt
    (by omega : x1 < 3 * m + 2) (by omega : x2 < 3 * m + 2) hlin
  exact Prod.ext hx hy

/-- Collision-free integer double-deletion key on `hexSub3mDouble m` anchored at `(m + 1, 4m - 1)`. -/
def hex7mDoubleKey (m : ℕ) (p : ℕ × ℕ) : ℕ :=
  (12 * m * m + 6 * m) * centerQuad m p +
    ((3 * m - 1) * p.2 + p.1)

theorem hex7mDoubleKey_injOn (m : ℕ) (hm : 2 ≤ m) :
    Set.InjOn (hex7mDoubleKey m) ((hexSub3mDouble m : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
  intro ⟨x1, y1⟩ h1 ⟨x2, y2⟩ h2 heq
  obtain ⟨_, _, _, _, hx1, hy1⟩ := mem_hexSub3mDouble_spec m hm h1
  obtain ⟨_, _, _, _, hx2, hy2⟩ := mem_hexSub3mDouble_spec m hm h2
  dsimp at hx1 hy1 hx2 hy2
  unfold hex7mDoubleKey at heq
  dsimp at heq
  have hmul1 : (3 * m - 1) * y1 ≤ (3 * m - 1) * (3 * m) := Nat.mul_le_mul_left (3 * m - 1) hy1
  have hmul2 : (3 * m - 1) * y2 ≤ (3 * m - 1) * (3 * m) := Nat.mul_le_mul_left (3 * m - 1) hy2
  have htop : (3 * m - 1) * (3 * m) + 3 * m = 9 * m * m := by
    zify [show 1 ≤ 3 * m by omega]; ring
  have hbound : 9 * m * m < 12 * m * m + 6 * m := by nlinarith
  have hr1 : (3 * m - 1) * y1 + x1 < 12 * m * m + 6 * m := by omega
  have hr2 : (3 * m - 1) * y2 + x2 < 12 * m * m + 6 * m := by omega
  obtain ⟨_, hlin⟩ := mul_add_inj_of_lt hr1 hr2 heq
  obtain ⟨hy, hx⟩ := mul_add_inj_of_lt hx1 hx2 hlin
  exact Prod.ext hx hy

theorem energy_insert_exterior_sub_eq_hexSub3m (m : ℕ) (hm : 1 ≤ m)
    {p q : ℕ × ℕ} (hp : p ∈ hexSub3m m) (hq : q ∈ hexSub3m m) :
    let H_set := hexSet (4 * m + 1) (2 * m) (4 * m)
    let v0 := triPoint (m, 4 * m + 1)
    energy (insert v0 H_set) (triPoint p) -
      energy (insert v0 H_set) (triPoint q) =
      4 * ((hex7mReplaceKey m p : ℝ) - (hex7mReplaceKey m q : ℝ)) := by
  classical
  dsimp
  let H_set := hexSet (4 * m + 1) (2 * m) (4 * m)
  let v0 := triPoint (m, 4 * m + 1)
  have hv0_not : v0 ∉ H_set := exterior_top_midpoint_not_mem_hexSet m
  have he_p : energy (insert v0 H_set) (triPoint p) =
      dist (triPoint p) v0 ^ 2 + energy H_set (triPoint p) := by
    unfold energy; exact Finset.sum_insert hv0_not
  have he_q : energy (insert v0 H_set) (triPoint q) =
      dist (triPoint q) v0 ^ 2 + energy H_set (triPoint q) := by
    unfold energy; exact Finset.sum_insert hv0_not
  rw [he_p, he_q]
  have hsub := energy_hexSet_regular_sub_eq (2 * m) (triPoint p) (triPoint q)
  have h1 : 2 * (2 * m) + 1 = 4 * m + 1 := by omega
  have h2 : 2 * (2 * m) = 4 * m := by omega
  have h3 : 3 * (2 * m) * (2 * m + 1) + 1 = 12 * m * m + 6 * m + 1 := by ring
  rw [h1, h2, h3] at hsub
  change energy H_set (triPoint p) - energy H_set (triPoint q) = _ at hsub
  have hdp := dist_sq_exterior_sub_center_point m p
  have hdq := dist_sq_exterior_sub_center_point m q
  change dist (triPoint p) v0 ^ 2 - dist (triPoint p) (triPoint (2 * m, 2 * m)) ^ 2 = _ at hdp
  change dist (triPoint q) v0 ^ 2 - dist (triPoint q) (triPoint (2 * m, 2 * m)) ^ 2 = _ at hdq
  have hcp := dist_sq_triPoint_center_eq_four_mul_centerQuad m p
  have hcq := dist_sq_triPoint_center_eq_four_mul_centerQuad m q
  rw [hcp] at hsub hdp
  rw [hcq] at hsub hdq
  obtain ⟨_, _, _, _, hxp, hyp⟩ := mem_hexSub3m_spec m hm hp
  obtain ⟨_, _, _, _, hxq, hyq⟩ := mem_hexSub3m_spec m hm hq
  have hle1 : (3 * m + 2) * p.2 + p.1 ≤ 9 * m * m + 9 * m := by nlinarith
  have hle2 : (3 * m + 2) * q.2 + q.1 ≤ 9 * m * m + 9 * m := by nlinarith
  unfold hex7mReplaceKey
  push_cast at hsub hdp hdq ⊢
  rw [Nat.cast_sub hle1, Nat.cast_sub hle2]
  push_cast
  linear_combination hdp - hdq + hsub

theorem mem_hexCoords_interior_shift_anchor (m : ℕ) (hm : 1 ≤ m) :
    (m + 1, 4 * m - 1) ∈ hexCoords (4 * m + 1) (2 * m) (4 * m) := by
  rw [mem_hexCoords_iff]; dsimp; omega

theorem mem_hexSet_interior_shift_anchor (m : ℕ) (hm : 1 ≤ m) :
    triPoint (m + 1, 4 * m - 1) ∈ hexSet (4 * m + 1) (2 * m) (4 * m) :=
  Finset.mem_image_of_mem triPoint (mem_hexCoords_interior_shift_anchor m hm)

theorem interior_shift_anchor_ne_diam_left (m : ℕ) :
    triPoint (m + 1, 4 * m - 1) ≠ triPoint (0, 2 * m) := by
  intro heq
  have hinj := triPoint_injective heq
  simp only [Prod.mk.injEq] at hinj
  omega

theorem interior_shift_anchor_ne_diam_right (m : ℕ) (_hm : 1 ≤ m) :
    triPoint (m + 1, 4 * m - 1) ≠ triPoint (4 * m, 2 * m) := by
  intro heq
  have hinj := triPoint_injective heq
  simp only [Prod.mk.injEq] at hinj
  omega

theorem energy_erase_interior_shift_sub_eq (m : ℕ) (hm : 2 ≤ m)
    {p q : ℕ × ℕ} (_hp : p ∈ hexSub3mDouble m) (_hq : q ∈ hexSub3mDouble m) :
    let H_set := hexSet (4 * m + 1) (2 * m) (4 * m)
    let c2 := triPoint (m + 1, 4 * m - 1)
    energy (H_set.erase c2) (triPoint p) -
      energy (H_set.erase c2) (triPoint q) =
      4 * ((hex7mDoubleKey m p : ℝ) - (hex7mDoubleKey m q : ℝ)) := by
  classical
  dsimp
  let H_set := hexSet (4 * m + 1) (2 * m) (4 * m)
  let c2 := triPoint (m + 1, 4 * m - 1)
  have hc2 : c2 ∈ H_set := mem_hexSet_interior_shift_anchor m (by omega)
  have he_p : energy (H_set.erase c2) (triPoint p) =
      energy H_set (triPoint p) - dist (triPoint p) c2 ^ 2 := by
    unfold energy; exact Finset.sum_erase_eq_sub hc2
  have he_q : energy (H_set.erase c2) (triPoint q) =
      energy H_set (triPoint q) - dist (triPoint q) c2 ^ 2 := by
    unfold energy; exact Finset.sum_erase_eq_sub hc2
  rw [he_p, he_q]
  have hsub := energy_hexSet_regular_sub_eq (2 * m) (triPoint p) (triPoint q)
  have h1 : 2 * (2 * m) + 1 = 4 * m + 1 := by omega
  have h2 : 2 * (2 * m) = 4 * m := by omega
  have h3 : 3 * (2 * m) * (2 * m + 1) + 1 = 12 * m * m + 6 * m + 1 := by ring
  rw [h1, h2, h3] at hsub
  change energy H_set (triPoint p) - energy H_set (triPoint q) = _ at hsub
  have hdp := dist_sq_interior_shift_sub_center_point m (by omega) p
  have hdq := dist_sq_interior_shift_sub_center_point m (by omega) q
  change dist (triPoint p) c2 ^ 2 - dist (triPoint p) (triPoint (2 * m, 2 * m)) ^ 2 = _ at hdp
  change dist (triPoint q) c2 ^ 2 - dist (triPoint q) (triPoint (2 * m, 2 * m)) ^ 2 = _ at hdq
  have hcp := dist_sq_triPoint_center_eq_four_mul_centerQuad m p
  have hcq := dist_sq_triPoint_center_eq_four_mul_centerQuad m q
  rw [hcp] at hsub hdp
  rw [hcq] at hsub hdq
  have hm1 : 1 ≤ 3 * m := by omega
  unfold hex7mDoubleKey
  push_cast at hsub hdp hdq ⊢
  rw [Nat.cast_sub hm1]
  push_cast
  linear_combination hsub - hdp + hdq

/-- **Pairwise nonsimilarity of `7m^2 - m - 2` double-point deletions on `hexSub3mDouble m` (`m ≥ 2`):** -/
theorem nonsimilar_hexSub3mDouble_erase (m : ℕ) (hm : 2 ≤ m)
    {p q : ℕ × ℕ} (hp : p ∈ hexSub3mDouble m) (hq : q ∈ hexSub3mDouble m) (hpq : p ≠ q) :
    let H_set := hexSet (4 * m + 1) (2 * m) (4 * m)
    let c2 := triPoint (m + 1, 4 * m - 1)
    ¬ DilationEquivSimilar
      ((H_set.erase c2).erase (triPoint p))
      ((H_set.erase c2).erase (triPoint q)) := by
  classical
  dsimp
  intro hsim
  let H_set := hexSet (4 * m + 1) (2 * m) (4 * m)
  let c2 := triPoint (m + 1, 4 * m - 1)
  let S := H_set.erase c2
  have hkey_ne : hex7mDoubleKey m p ≠ hex7mDoubleKey m q :=
    fun heq => hpq (hex7mDoubleKey_injOn m hm hp hq heq)
  have hkey_real : (hex7mDoubleKey m p : ℝ) ≠ (hex7mDoubleKey m q : ℝ) := by
    exact_mod_cast hkey_ne
  have hsub := energy_erase_interior_shift_sub_eq m hm hp hq
  have hne_en : energy S (triPoint p) ≠ energy S (triPoint q) := by
    intro heq
    dsimp [S, H_set, c2] at heq hsub
    apply hkey_real
    linarith
  have h1 : 2 * (2 * m) + 1 = 4 * m + 1 := by omega
  have h2 : 2 * (2 * m) = 4 * m := by omega
  have haH : triPoint (0, 2 * m) ∈ H_set := by
    have h := mem_hexSet_diam_left (2 * m); rwa [h1, h2] at h
  have hbH : triPoint (4 * m, 2 * m) ∈ H_set := by
    have h := mem_hexSet_diam_right (2 * m); rwa [h1, h2] at h
  have hab : triPoint (0, 2 * m) ≠ triPoint (4 * m, 2 * m) := by
    have h := diam_pair_hexSet_ne (2 * m) (by omega); rwa [h2] at h
  have haS : triPoint (0, 2 * m) ∈ S :=
    Finset.mem_erase.mpr ⟨(interior_shift_anchor_ne_diam_left m).symm, haH⟩
  have hbS : triPoint (4 * m, 2 * m) ∈ S :=
    Finset.mem_erase.mpr ⟨(interior_shift_anchor_ne_diam_right m (by omega)).symm, hbH⟩
  obtain ⟨hpH, hp_ne_a, hp_ne_b, hp_ne_c2, _, _⟩ := mem_hexSub3mDouble_spec m hm hp
  obtain ⟨hqH, hq_ne_a, hq_ne_b, hq_ne_c2, _, _⟩ := mem_hexSub3mDouble_spec m hm hq
  have hpS : triPoint p ∈ S :=
    Finset.mem_erase.mpr ⟨fun h => hp_ne_c2 (triPoint_injective h),
      Finset.mem_image_of_mem triPoint hpH⟩
  have hqS : triPoint q ∈ S :=
    Finset.mem_erase.mpr ⟨fun h => hq_ne_c2 (triPoint_injective h),
      Finset.mem_image_of_mem triPoint hqH⟩
  have hpa : triPoint p ≠ triPoint (0, 2 * m) := fun h => hp_ne_a (triPoint_injective h)
  have hpb : triPoint p ≠ triPoint (4 * m, 2 * m) := fun h => hp_ne_b (triPoint_injective h)
  have hqa : triPoint q ≠ triPoint (0, 2 * m) := fun h => hq_ne_a (triPoint_injective h)
  have hqb : triPoint q ≠ triPoint (4 * m, 2 * m) := fun h => hq_ne_b (triPoint_injective h)
  have hdiam_H : ∀ x ∈ H_set, ∀ y ∈ H_set, dist x y ≤ dist (triPoint (0, 2 * m)) (triPoint (4 * m, 2 * m)) := by
    intro x hx y hy
    have hd := dist_le_diam_pair_hexSet (2 * m) (x := x) (y := y)
    rw [h1, h2] at hd
    exact hd hx hy
  exact DeletionEnergy91.nonsimilar_deletions S
    (triPoint (0, 2 * m)) (triPoint (4 * m, 2 * m))
    (triPoint p) (triPoint q)
    hab haS hbS hpS hqS hpa hpb hqa hqb
    (fun x hx y hy => hdiam_H x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy))
    hne_en ((similar_iff_image _ _).mp hsim)

/-- **Symbolic `7m^2 - m - 2` double-point deletion multiplicity theorem (`m ≥ 2`):**
for every `m ≥ 2`, `hexSet (4m + 1) (2m) (4m)` admits an explicit family `F` of
`7m^2 - m - 2` pairwise nonsimilar `(12m^2 + 6m - 1)`-point double-point deletions! -/
theorem hexSet_seven_m_squared_double_deletion_family (m : ℕ) (hm : 2 ≤ m) :
    ∃ F : Finset (Finset Plane),
      F.card = 7 * m * m - m - 2 ∧
      (∀ A ∈ F, ∃ x ∈ hexSet (4 * m + 1) (2 * m) (4 * m),
        ∃ y ∈ hexSet (4 * m + 1) (2 * m) (4 * m), x ≠ y ∧
        A = ((hexSet (4 * m + 1) (2 * m) (4 * m)).erase x).erase y ∧
        A.card = 12 * m * m + 6 * m - 1) ∧
      (∀ A ∈ F, ∀ B ∈ F, A ≠ B → ¬ DilationEquivSimilar A B) := by
  classical
  let H_set := hexSet (4 * m + 1) (2 * m) (4 * m)
  let c2 := triPoint (m + 1, 4 * m - 1)
  let S := H_set.erase c2
  let U0 := hexSub3mDouble m
  let V := U0.image triPoint
  have hV_sub : V ⊆ S := by
    intro x hx
    obtain ⟨p, hpU, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hpH, _, _, hp_ne_c2, _, _⟩ := mem_hexSub3mDouble_spec m hm hpU
    exact Finset.mem_erase.mpr ⟨fun h => hp_ne_c2 (triPoint_injective h),
      Finset.mem_image_of_mem triPoint hpH⟩
  have hV_card : V.card = 7 * m * m - m - 2 :=
    (Finset.card_image_of_injective U0 triPoint_injective).trans (card_hexSub3mDouble_eq m (by omega))
  let F := V.image S.erase
  have hF_card : F.card = 7 * m * m - m - 2 := by
    dsimp [F]
    rw [Finset.card_image_of_injOn (S.erase_injOn.mono hV_sub), hV_card]
  have hc2H : c2 ∈ H_set := mem_hexSet_interior_shift_anchor m (by omega)
  have h1 : 2 * (2 * m) + 1 = 4 * m + 1 := by omega
  have h2 : 2 * (2 * m) = 4 * m := by omega
  have hH_card : H_set.card = 12 * m * m + 6 * m + 1 := by
    have h := card_hexSet_regular_eq (2 * m)
    have h3 : 3 * (2 * m) * (2 * m + 1) + 1 = 12 * m * m + 6 * m + 1 := by ring
    rwa [h1, h2, h3] at h
  have hS_card : S.card = 12 * m * m + 6 * m := by
    dsimp [S]; rw [Finset.card_erase_of_mem hc2H, hH_card]; omega
  refine ⟨F, hF_card, ?_, ?_⟩
  · intro A hA
    obtain ⟨y, hyV, rfl⟩ := Finset.mem_image.mp hA
    have hyS : y ∈ S := hV_sub hyV
    obtain ⟨hy_ne_c2, hyH⟩ := Finset.mem_erase.mp hyS
    refine ⟨c2, hc2H, y, hyH, hy_ne_c2.symm, rfl, ?_⟩
    rw [Finset.card_erase_of_mem hyS, hS_card]
  · intro A hA B hB hAB hsim
    obtain ⟨x, hxV, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨y, hyV, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨p, hpU, rfl⟩ := Finset.mem_image.mp hxV
    obtain ⟨q, hqU, rfl⟩ := Finset.mem_image.mp hyV
    have hpq : p ≠ q := fun heq => hAB (by rw [heq])
    exact nonsimilar_hexSub3mDouble_erase m hm hpU hqU hpq hsim

noncomputable def hex7mReplaceSet (m : ℕ) (p : ℕ × ℕ) : Finset Plane :=
  insert (triPoint (m, 4 * m + 1))
    ((hexSet (4 * m + 1) (2 * m) (4 * m)).erase (triPoint p))

theorem hex7mReplaceSet_eq_erase_insert (m : ℕ) (hm : 1 ≤ m)
    {p : ℕ × ℕ} (hp : p ∈ hexSub3m m) :
    hex7mReplaceSet m p =
      (insert (triPoint (m, 4 * m + 1)) (hexSet (4 * m + 1) (2 * m) (4 * m))).erase
        (triPoint p) := by
  classical
  unfold hex7mReplaceSet
  obtain ⟨_, _, _, hp_ne_v0, _, _⟩ := mem_hexSub3m_spec m hm hp
  have hne : triPoint p ≠ triPoint (m, 4 * m + 1) := fun h => hp_ne_v0 (triPoint_injective h)
  ext z
  simp only [Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro (rfl | ⟨hz_ne, hz_mem⟩)
    · exact ⟨hne.symm, Or.inl rfl⟩
    · exact ⟨hz_ne, Or.inr hz_mem⟩
  · rintro ⟨hz_ne, rfl | hz_mem⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hz_ne, hz_mem⟩

/-- **Pairwise nonsimilarity of `7m^2 + 5m` single-site replacements on `hexSub3m m` (`m ≥ 3`):** -/
theorem nonsimilar_hex7mReplaceSet_of_ne (m : ℕ) (hm : 3 ≤ m)
    {p q : ℕ × ℕ} (hp : p ∈ hexSub3m m) (hq : q ∈ hexSub3m m) (hpq : p ≠ q) :
    ¬ DilationEquivSimilar (hex7mReplaceSet m p) (hex7mReplaceSet m q) := by
  classical
  intro hsim
  rw [hex7mReplaceSet_eq_erase_insert m (by omega) hp,
    hex7mReplaceSet_eq_erase_insert m (by omega) hq] at hsim
  let H_set := hexSet (4 * m + 1) (2 * m) (4 * m)
  let v0 := triPoint (m, 4 * m + 1)
  let S := insert v0 H_set
  have hkey_ne : hex7mReplaceKey m p ≠ hex7mReplaceKey m q :=
    fun heq => hpq (hex7mReplaceKey_injOn m (by omega) hp hq heq)
  have hkey_real : (hex7mReplaceKey m p : ℝ) ≠ (hex7mReplaceKey m q : ℝ) := by
    exact_mod_cast hkey_ne
  have hsub := energy_insert_exterior_sub_eq_hexSub3m m (by omega) hp hq
  have hne_en : energy S (triPoint p) ≠ energy S (triPoint q) := by
    intro heq
    dsimp [S, H_set, v0] at heq hsub
    apply hkey_real
    linarith
  have h1 : 2 * (2 * m) + 1 = 4 * m + 1 := by omega
  have h2 : 2 * (2 * m) = 4 * m := by omega
  have haH : triPoint (0, 2 * m) ∈ H_set := by
    have h := mem_hexSet_diam_left (2 * m); rwa [h1, h2] at h
  have hbH : triPoint (4 * m, 2 * m) ∈ H_set := by
    have h := mem_hexSet_diam_right (2 * m); rwa [h1, h2] at h
  have hab : triPoint (0, 2 * m) ≠ triPoint (4 * m, 2 * m) := by
    have h := diam_pair_hexSet_ne (2 * m) (by omega); rwa [h2] at h
  have haS : triPoint (0, 2 * m) ∈ S := Finset.mem_insert_of_mem haH
  have hbS : triPoint (4 * m, 2 * m) ∈ S := Finset.mem_insert_of_mem hbH
  obtain ⟨hpH, hp_ne_a, hp_ne_b, _, _, _⟩ := mem_hexSub3m_spec m (by omega) hp
  obtain ⟨hqH, hq_ne_a, hq_ne_b, _, _, _⟩ := mem_hexSub3m_spec m (by omega) hq
  have hpS : triPoint p ∈ S := Finset.mem_insert_of_mem (Finset.mem_image_of_mem triPoint hpH)
  have hqS : triPoint q ∈ S := Finset.mem_insert_of_mem (Finset.mem_image_of_mem triPoint hqH)
  have hpa : triPoint p ≠ triPoint (0, 2 * m) := fun h => hp_ne_a (triPoint_injective h)
  have hpb : triPoint p ≠ triPoint (4 * m, 2 * m) := fun h => hp_ne_b (triPoint_injective h)
  have hqa : triPoint q ≠ triPoint (0, 2 * m) := fun h => hq_ne_a (triPoint_injective h)
  have hqb : triPoint q ≠ triPoint (4 * m, 2 * m) := fun h => hq_ne_b (triPoint_injective h)
  exact DeletionEnergy91.nonsimilar_deletions S
    (triPoint (0, 2 * m)) (triPoint (4 * m, 2 * m))
    (triPoint p) (triPoint q)
    hab haS hbS hpS hqS hpa hpb hqa hqb
    (fun x hx y hy => dist_le_diam_pair_insert_exterior_top_midpoint m hm hx hy)
    hne_en ((similar_iff_image _ _).mp hsim)

/-- **Symbolic `7m^2 + 5m` single-site replacement multiplicity theorem (`m ≥ 3`):**
for every `m ≥ 3`, `hexSet (4m + 1) (2m) (4m)` (`12m^2 + 6m + 1` points) admits an explicit
family `F` of `7m^2 + 5m` pairwise nonsimilar `(12m^2 + 6m + 1)`-point single-site replacements
`insert (triPoint (m, 4m + 1)) (H_{2m}.erase x)`! -/
theorem hexSet_seven_m_squared_single_site_replacement_family (m : ℕ) (hm : 3 ≤ m) :
    let H_set := hexSet (4 * m + 1) (2 * m) (4 * m)
    let v0 := triPoint (m, 4 * m + 1)
    ∃ F : Finset (Finset Plane),
      F.card = 7 * m * m + 5 * m ∧
      (∀ A ∈ F, ∃ x ∈ H_set,
        A = insert v0 (H_set.erase x) ∧ A.card = 12 * m * m + 6 * m + 1) ∧
      (∀ A ∈ F, ∀ B ∈ F, A ≠ B → ¬ DilationEquivSimilar A B) := by
  classical
  dsimp
  let H_set := hexSet (4 * m + 1) (2 * m) (4 * m)
  let v0 := triPoint (m, 4 * m + 1)
  let S := insert v0 H_set
  let U0 := hexSub3m m
  let V := U0.image triPoint
  have hV_sub_H : V ⊆ H_set := by
    intro x hx
    obtain ⟨p, hpU, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image_of_mem triPoint (mem_hexSub3m_spec m (by omega) hpU).1
  have hV_sub_S : V ⊆ S := hV_sub_H.trans (Finset.subset_insert v0 H_set)
  have hV_card : V.card = 7 * m * m + 5 * m :=
    (Finset.card_image_of_injective U0 triPoint_injective).trans (card_hexSub3m_eq m)
  let F := V.image (fun x => insert v0 (H_set.erase x))
  have hF_eq : F = V.image S.erase := by
    apply Finset.image_congr
    intro x hx
    obtain ⟨p, hpU, rfl⟩ := Finset.mem_image.mp hx
    exact hex7mReplaceSet_eq_erase_insert m (by omega) hpU
  have hF_card : F.card = 7 * m * m + 5 * m := by
    rw [hF_eq, Finset.card_image_of_injOn (S.erase_injOn.mono hV_sub_S), hV_card]
  have h1 : 2 * (2 * m) + 1 = 4 * m + 1 := by omega
  have h2 : 2 * (2 * m) = 4 * m := by omega
  have hH_card : H_set.card = 12 * m * m + 6 * m + 1 := by
    have h := card_hexSet_regular_eq (2 * m)
    have h3 : 3 * (2 * m) * (2 * m + 1) + 1 = 12 * m * m + 6 * m + 1 := by ring
    rwa [h1, h2, h3] at h
  have hv0_not : v0 ∉ H_set := exterior_top_midpoint_not_mem_hexSet m
  refine ⟨F, hF_card, ?_, ?_⟩
  · intro A hA
    obtain ⟨x, hxV, rfl⟩ := Finset.mem_image.mp hA
    have hxH : x ∈ H_set := hV_sub_H hxV
    have hv0_not_er : v0 ∉ H_set.erase x := fun h => hv0_not (Finset.mem_of_mem_erase h)
    refine ⟨x, hxH, rfl, ?_⟩
    rw [Finset.card_insert_of_notMem hv0_not_er, Finset.card_erase_of_mem hxH, hH_card]
    omega
  · intro A hA B hB hAB hsim
    obtain ⟨x, hxV, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨y, hyV, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨p, hpU, rfl⟩ := Finset.mem_image.mp hxV
    obtain ⟨q, hqU, rfl⟩ := Finset.mem_image.mp hyV
    have hpq : p ≠ q := fun heq => hAB (by rw [heq])
    exact nonsimilar_hex7mReplaceSet_of_ne m hm hpU hqU hpq hsim

/-- **Combined `7m^2 - m - 2` double-deletion and `7m^2 + 5m` single-site replacement theorem (`m ≥ 3`):** -/
theorem hexSet_seven_m_squared_combined (m : ℕ) (hm : 3 ≤ m) :
    (∃ F1 : Finset (Finset Plane),
      F1.card = 7 * m * m - m - 2 ∧
      (∀ A ∈ F1, ∃ x ∈ hexSet (4 * m + 1) (2 * m) (4 * m),
        ∃ y ∈ hexSet (4 * m + 1) (2 * m) (4 * m), x ≠ y ∧
        A = ((hexSet (4 * m + 1) (2 * m) (4 * m)).erase x).erase y ∧
        A.card = 12 * m * m + 6 * m - 1) ∧
      (∀ A ∈ F1, ∀ B ∈ F1, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
    (∃ F2 : Finset (Finset Plane),
      F2.card = 7 * m * m + 5 * m ∧
      (∀ A ∈ F2, ∃ x ∈ hexSet (4 * m + 1) (2 * m) (4 * m),
        A = insert (triPoint (m, 4 * m + 1)) ((hexSet (4 * m + 1) (2 * m) (4 * m)).erase x) ∧
        A.card = 12 * m * m + 6 * m + 1) ∧
      (∀ A ∈ F2, ∀ B ∈ F2, A ≠ B → ¬ DilationEquivSimilar A B)) :=
  ⟨hexSet_seven_m_squared_double_deletion_family m (by omega),
   hexSet_seven_m_squared_single_site_replacement_family m hm⟩

end Erdos91.HexagonSevenMSquaredMultiplicity


namespace Erdos91.DistanceErasure
variable {X : Type*} [MetricSpace X] [DecidableEq X]

theorem distanceSet_erase_subset (S : Finset X) (x : X) :
    distanceSet (S.erase x) ⊆ distanceSet S := by
  classical
  intro r hr
  obtain ⟨a, ha, b, hb, hne, hd⟩ := (mem_distanceSet _ _).mp hr
  exact (mem_distanceSet _ _).mpr
    ⟨a, Finset.mem_of_mem_erase ha, b, Finset.mem_of_mem_erase hb, hne, hd⟩

end Erdos91.DistanceErasure

namespace Erdos91.FlatCore
open Erdos91.DistanceErasure

/-- EVERY point deletion of an actual optimum preserves its complete distance
set at a preceding flat step; no larger-seed existence is assumed. -/
theorem flat_erase_distanceSet (A : Finset Minimizer91.Plane) (n : ℕ)
    (hA : Minimizer91.IsOptimal A n)
    (hflat : Minimizer91.minimalDistinctDistances (n - 1) =
      Minimizer91.minimalDistinctDistances n)
    (u : Minimizer91.Plane) (hu : u ∈ A) :
    distanceSet (A.erase u) = distanceSet A := by
  classical
  have hcard : (A.erase u).card = n - 1 := by
    rw [Finset.card_erase_of_mem hu, hA.1]
  have hmin := Minimizer91.minimal_le (A.erase u) (n - 1) hcard
  rw [hflat] at hmin
  apply Finset.eq_of_subset_of_card_le (distanceSet_erase_subset A u)
  change Minimizer91.distinctDistances A ≤ Minimizer91.distinctDistances (A.erase u)
  rw [hA.2]
  exact hmin

/-- The SAME deletion is an actual global (n-1)-point optimum. -/
theorem flat_erase_optimal (A : Finset Minimizer91.Plane) (n : ℕ)
    (hA : Minimizer91.IsOptimal A n)
    (hflat : Minimizer91.minimalDistinctDistances (n - 1) =
      Minimizer91.minimalDistinctDistances n)
    (u : Minimizer91.Plane) (hu : u ∈ A) :
    Minimizer91.IsOptimal (A.erase u) (n - 1) := by
  classical
  refine ⟨?_, ?_⟩
  · rw [Finset.card_erase_of_mem hu, hA.1]
  · change (distanceSet (A.erase u)).card = Minimizer91.minimalDistinctDistances (n - 1)
    rw [flat_erase_distanceSet A n hA hflat u hu]
    change Minimizer91.distinctDistances A = Minimizer91.minimalDistinctDistances (n - 1)
    rw [hA.2, hflat]

/-- The removed point ALREADY supplies one completion of the actual optimal
core. Finding an alternative point remains an unproved geometric task. -/
theorem flat_erase_first_completion (A : Finset Minimizer91.Plane) (n : ℕ)
    (hA : Minimizer91.IsOptimal A n)
    (hflat : Minimizer91.minimalDistinctDistances (n - 1) =
      Minimizer91.minimalDistinctDistances n)
    (u : Minimizer91.Plane) (hu : u ∈ A) :
    u ∉ A.erase u ∧ ∀ t ∈ A.erase u, dist u t ∈ distanceSet (A.erase u) := by
  classical
  refine ⟨by simp, ?_⟩
  intro t ht
  rw [flat_erase_distanceSet A n hA hflat u hu]
  exact (mem_distanceSet A (dist u t)).mpr
    ⟨u, hu, t, Finset.mem_of_mem_erase ht, (Finset.mem_erase.mp ht).1.symm, rfl⟩

end Erdos91.FlatCore

namespace Erdos91.MultiSiteReplacement
open Finset Erdos91.DistanceErasure Minimizer91
open SimilarityEnergy91 (pairEnergy)
open EnergyLevels91 (energy)

theorem pairEnergy_union_disjoint (U T : Finset Plane) (hdisj : Disjoint U T) :
    pairEnergy (U ∪ T) =
      pairEnergy T + pairEnergy U + 2 * ∑ u ∈ U, energy T u := by
  classical
  unfold pairEnergy
  rw [Finset.sum_union hdisj]
  have h1 : (∑ x ∈ U, ∑ y ∈ U ∪ T, dist x y ^ 2) =
      (∑ x ∈ U, ∑ y ∈ U, dist x y ^ 2) + ∑ u ∈ U, energy T u := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.sum_union hdisj]
    rfl
  have h2 : (∑ x ∈ T, ∑ y ∈ U ∪ T, dist x y ^ 2) =
      (∑ x ∈ T, ∑ y ∈ U, dist x y ^ 2) + ∑ x ∈ T, ∑ y ∈ T, dist x y ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.sum_union hdisj]
  have h3 : (∑ x ∈ T, ∑ y ∈ U, dist x y ^ 2) = ∑ u ∈ U, energy T u := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    unfold energy
    apply Finset.sum_congr rfl
    intro t ht
    rw [dist_comm]
  rw [h1, h2, h3]
  ring

/-- Multi-site surgery nonsimilarity theorem: if two disjoint extensions U, V of a
core T (with T.card ≥ 2) preserve the distance set of T and have different
multi-site extension energies pairEnergy(U) + 2 * ∑_{u ∈ U} energy(T, u), then
U ∪ T and V ∪ T are nonsimilar under all full-plane similarities (DilationEquiv).
Unlike single-site replacement, this remains available even when d(n+1) ≥ d(n) + 2. -/
theorem multisite_completions_nonsimilar_of_ne_energy
    (T U V : Finset Plane) (hTcard : 2 ≤ T.card)
    (hUT : Disjoint U T) (hVT : Disjoint V T)
    (hDS_U : Erdos91.DistanceErasure.distanceSet (U ∪ T) =
      Erdos91.DistanceErasure.distanceSet T)
    (hDS_V : Erdos91.DistanceErasure.distanceSet (V ∪ T) =
      Erdos91.DistanceErasure.distanceSet T)
    (hne : pairEnergy U + 2 * (∑ u ∈ U, energy T u) ≠
      pairEnergy V + 2 * (∑ v ∈ V, energy T v)) :
    ¬ ∃ f : Plane ≃ᵈ Plane, (U ∪ T).image f = V ∪ T := by
  classical
  obtain ⟨a, haT, b, hbT, hab, hdiam⟩ :=
    Erdos91.DeletionSpectrum.exists_diameter_pair T (by omega)
  have haU : a ∈ U ∪ T := Finset.mem_union_right U haT
  have hbU : b ∈ U ∪ T := Finset.mem_union_right U hbT
  have haV : a ∈ V ∪ T := Finset.mem_union_right V haT
  have hbV : b ∈ V ∪ T := Finset.mem_union_right V hbT
  have hbound (A : Finset Plane)
      (hDA : Erdos91.DistanceErasure.distanceSet A =
        Erdos91.DistanceErasure.distanceSet T) :
      ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ dist a b := by
    intro x hx y hy
    by_cases hxy : x = y
    · subst y
      simpa only [dist_self] using dist_nonneg (x := a) (y := b)
    · have hrA : dist x y ∈ Erdos91.DistanceErasure.distanceSet A :=
        (mem_distanceSet A (dist x y)).mpr ⟨x, hx, y, hy, hxy, rfl⟩
      rw [hDA] at hrA
      obtain ⟨p, hpT, q, hqT, _, hd⟩ := (mem_distanceSet T (dist x y)).mp hrA
      rw [← hd]
      exact hdiam p hpT q hqT
  rintro ⟨f, hf⟩
  have he := SimilarityEnergy91.pairEnergy_eq_of_shared_diameter
    (U ∪ T) (V ∪ T) f hf a b hab haU hbU haV hbV
    (hbound (U ∪ T) hDS_U) (hbound (V ∪ T) hDS_V)
  rw [pairEnergy_union_disjoint U T hUT, pairEnergy_union_disjoint V T hVT] at he
  apply hne
  linarith

theorem flat_sdiff_distanceSet (A U : Finset Plane) (n k : ℕ)
    (hA : IsOptimal A n) (hUA : U ⊆ A) (hUcard : U.card = k)
    (hflat : minimalDistinctDistances (n - k) = minimalDistinctDistances n) :
    Erdos91.DistanceErasure.distanceSet (A \ U) =
      Erdos91.DistanceErasure.distanceSet A := by
  classical
  have hcard : (A \ U).card = n - k := by
    rw [Finset.card_sdiff_of_subset hUA, hA.1, hUcard]
  have hsub : Erdos91.DistanceErasure.distanceSet (A \ U) ⊆
      Erdos91.DistanceErasure.distanceSet A := by
    change (A \ U).offDiag.image (fun p => dist p.1 p.2) ⊆
      A.offDiag.image (fun p => dist p.1 p.2)
    exact Finset.image_subset_image (Finset.offDiag_mono Finset.sdiff_subset)
  have hmin := minimal_le (A \ U) (n - k) hcard
  rw [hflat] at hmin
  apply Finset.eq_of_subset_of_card_le hsub
  change distinctDistances A ≤ distinctDistances (A \ U)
  rw [hA.2]
  exact hmin

theorem flat_sdiff_optimal (A U : Finset Plane) (n k : ℕ)
    (hA : IsOptimal A n) (hUA : U ⊆ A) (hUcard : U.card = k)
    (hflat : minimalDistinctDistances (n - k) = minimalDistinctDistances n) :
    IsOptimal (A \ U) (n - k) := by
  classical
  refine ⟨?_, ?_⟩
  · rw [Finset.card_sdiff_of_subset hUA, hA.1, hUcard]
  · change (Erdos91.DistanceErasure.distanceSet (A \ U)).card =
      minimalDistinctDistances (n - k)
    rw [flat_sdiff_distanceSet A U n k hA hUA hUcard hflat]
    change distinctDistances A = minimalDistinctDistances (n - k)
    rw [hA.2, hflat]

/-- Original-definition k-site replacement theorem: if A is an optimal n-point
set at a k-step flat d(n-k) = d(n) with 2 ≤ n - k, U ⊆ A has size k, V is
disjoint from A \ U, V ∪ (A \ U) is optimal for n, and U and V have unequal
multi-site extension energies over the shared core A \ U, then A and V ∪ (A \ U)
are nonsimilar under all full-plane similarities (DilationEquiv) and
UniqueMinimizer n fails. -/
theorem optimal_multisite_replacement_nonsimilar_of_ne_energy
    (A U V : Finset Plane) (n k : ℕ) (hnk : 2 ≤ n - k)
    (hA : IsOptimal A n) (hUA : U ⊆ A) (hUcard : U.card = k)
    (hflat : minimalDistinctDistances (n - k) = minimalDistinctDistances n)
    (hVT : Disjoint V (A \ U))
    (hVopt : IsOptimal (V ∪ (A \ U)) n)
    (hne : pairEnergy U + 2 * (∑ u ∈ U, energy (A \ U) u) ≠
      pairEnergy V + 2 * (∑ v ∈ V, energy (A \ U) v)) :
    (¬ ∃ f : Plane ≃ᵈ Plane, A.image f = V ∪ (A \ U)) ∧
      ¬ PlateauDefinitions91.UniqueMinimizer n := by
  classical
  let T := A \ U
  have hUT : Disjoint U T := disjoint_sdiff_self_right
  have hUTA : U ∪ T = A := Finset.union_sdiff_of_subset hUA
  have hTcard : 2 ≤ T.card := by
    dsimp [T]
    rw [Finset.card_sdiff_of_subset hUA, hA.1, hUcard]
    exact hnk
  have hDS_T : Erdos91.DistanceErasure.distanceSet T =
      Erdos91.DistanceErasure.distanceSet A :=
    flat_sdiff_distanceSet A U n k hA hUA hUcard hflat
  have hDS_U : Erdos91.DistanceErasure.distanceSet (U ∪ T) =
      Erdos91.DistanceErasure.distanceSet T := by
    rw [hUTA, hDS_T]
  have hsubV : Erdos91.DistanceErasure.distanceSet T ⊆
      Erdos91.DistanceErasure.distanceSet (V ∪ T) := by
    change T.offDiag.image (fun p => dist p.1 p.2) ⊆
      (V ∪ T).offDiag.image (fun p => dist p.1 p.2)
    exact Finset.image_subset_image (Finset.offDiag_mono Finset.subset_union_right)
  have hDS_V : Erdos91.DistanceErasure.distanceSet (V ∪ T) =
      Erdos91.DistanceErasure.distanceSet T := by
    apply (Finset.eq_of_subset_of_card_le hsubV ?_).symm
    change distinctDistances (V ∪ T) ≤ (Erdos91.DistanceErasure.distanceSet T).card
    rw [hVopt.2, hDS_T]
    change minimalDistinctDistances n ≤ distinctDistances A
    rw [hA.2]
  have hnon := multisite_completions_nonsimilar_of_ne_energy
    T U V hTcard hUT hVT hDS_U hDS_V hne
  rw [hUTA] at hnon
  refine ⟨hnon, ?_⟩
  intro huniq
  exact hnon ((PlateauDefinitions91.similar_iff_image A (V ∪ T)).mp
    (huniq A (V ∪ T) hA hVopt))

end Erdos91.MultiSiteReplacement

namespace Erdos91.DistanceCompleteCoreMultiSiteTheory
open Finset Erdos91.DistanceErasure Minimizer91 PlateauDefinitions91
  Erdos91.MultiSiteReplacement Erdos91.GeneralMultiplicityAndDensityOne Erdos91.AsymptoticDensityOneAndGlobalBounds
  Erdos91.ThreeUniqueMinimizer
open SimilarityEnergy91 (pairEnergy)
open EnergyLevels91 (energy)

/-- Multi-site extension energy of a disjoint set `U` over a core `T`. -/
noncomputable def extEnergy (T U : Finset Plane) : ℝ :=
  pairEnergy U + 2 * ∑ u ∈ U, energy T u

/-- Universal disjoint-union pair-energy decomposition in terms of `extEnergy`. -/
theorem pairEnergy_union_eq_add_extEnergy (U T : Finset Plane) (hdisj : Disjoint U T) :
    pairEnergy (U ∪ T) = pairEnergy T + extEnergy T U := by
  unfold extEnergy
  linarith [pairEnergy_union_disjoint U T hdisj]

/-- For a singleton completion `U = {u}`, `extEnergy T {u} = 2 * energy T u`. -/
theorem extEnergy_singleton (T : Finset Plane) (u : Plane) :
    extEnergy T {u} = 2 * energy T u := by
  unfold extEnergy pairEnergy
  simp

/-- Monotonicity of `distanceSet` ensures `distanceSet (U ∪ T) = distanceSet T`
whenever `distanceSet (U ∪ T) ⊆ distanceSet T`. -/
theorem distanceSet_union_eq_of_subset (T U : Finset Plane)
    (hDS : Erdos91.DistanceErasure.distanceSet (U ∪ T) ⊆
      Erdos91.DistanceErasure.distanceSet T) :
    Erdos91.DistanceErasure.distanceSet (U ∪ T) =
      Erdos91.DistanceErasure.distanceSet T := by
  classical
  apply Finset.Subset.antisymm hDS
  change T.offDiag.image (fun p => dist p.1 p.2) ⊆
    (U ∪ T).offDiag.image (fun p => dist p.1 p.2)
  exact Finset.image_subset_image (Finset.offDiag_mono Finset.subset_union_right)

/-- **Universal Strict-Rise Flat-Core Obstruction Theorem:** at any strict rise
`d(n - k) < d(n)` with `k ≤ n`, no optimal `(n - k)`-point configuration `T`
(`IsOptimal T (n - k)`) can possess a disjoint `k`-site completion `U` preserving
`distanceSet T`. Thus flat-core completions require `d(n - k) = d(n)`, whereas
strict-rise completions require a distance-complete core with `distinctDistances T = d(n)`. -/
theorem no_optimal_core_completion_at_strict_rise (T U : Finset Plane) (n k : ℕ)
    (hkn : k ≤ n) (hT : IsOptimal T (n - k)) (hUT : Disjoint U T) (hUcard : U.card = k)
    (hrise : minimalDistinctDistances (n - k) < minimalDistinctDistances n)
    (hDS : Erdos91.DistanceErasure.distanceSet (U ∪ T) ⊆
      Erdos91.DistanceErasure.distanceSet T) : False := by
  classical
  have hcard : (U ∪ T).card = n := by
    rw [Finset.card_union_of_disjoint hUT, hUcard, hT.1]
    omega
  have heq := distanceSet_union_eq_of_subset T U hDS
  have hdist : distinctDistances (U ∪ T) = minimalDistinctDistances (n - k) := by
    change (Erdos91.DistanceErasure.distanceSet (U ∪ T)).card = _
    rw [heq]
    exact hT.2
  have hmin := minimal_le (U ∪ T) n hcard
  omega

/-- **Universal Distance-Complete Core Optimality Theorem:** for any `n, k : ℕ`,
any core `T` with `T.card = n - k` and `distinctDistances T = d(n)`, and any
disjoint `k`-element set `U` with `distanceSet (U ∪ T) ⊆ distanceSet T`, the
completion `U ∪ T` is globally optimal for `n` (`IsOptimal (U ∪ T) n`). -/
theorem isOptimal_of_distance_complete_multisite_completion
    (T U : Finset Plane) (n k : ℕ) (hkn : k ≤ n)
    (hTcard : T.card = n - k) (hUcard : U.card = k) (hUT : Disjoint U T)
    (hTdist : distinctDistances T = minimalDistinctDistances n)
    (hDS : Erdos91.DistanceErasure.distanceSet (U ∪ T) ⊆
      Erdos91.DistanceErasure.distanceSet T) :
    IsOptimal (U ∪ T) n ∧
      Erdos91.DistanceErasure.distanceSet (U ∪ T) =
        Erdos91.DistanceErasure.distanceSet T := by
  classical
  have heq := distanceSet_union_eq_of_subset T U hDS
  refine ⟨⟨?_, ?_⟩, heq⟩
  · rw [Finset.card_union_of_disjoint hUT, hUcard, hTcard]
    omega
  · change (Erdos91.DistanceErasure.distanceSet (U ∪ T)).card = minimalDistinctDistances n
    rw [heq]
    exact hTdist

/-- **Universal Distance-Complete Core Multi-Site Nonsimilarity Theorem:**
if `T` is a distance-complete core of size `n - k ≥ 2` (`distinctDistances T = d(n)`),
and `U, V` are disjoint `k`-site completions of `T` with `extEnergy T U ≠ extEnergy T V`,
then `U ∪ T` and `V ∪ T` are nonsimilar optimal `n`-point configurations and
`¬ UniqueMinimizer n` holds (even when `d(n - k) < d(n)` is a strict rise). -/
theorem distance_complete_core_multisite_nonsimilar_of_ne_extEnergy
    (T U V : Finset Plane) (n k : ℕ) (hnk : 2 ≤ n - k) (hkn : k ≤ n)
    (hTcard : T.card = n - k) (hUcard : U.card = k) (hVcard : V.card = k)
    (hUT : Disjoint U T) (hVT : Disjoint V T)
    (hTdist : distinctDistances T = minimalDistinctDistances n)
    (hDS_U : Erdos91.DistanceErasure.distanceSet (U ∪ T) ⊆
      Erdos91.DistanceErasure.distanceSet T)
    (hDS_V : Erdos91.DistanceErasure.distanceSet (V ∪ T) ⊆
      Erdos91.DistanceErasure.distanceSet T)
    (hne : extEnergy T U ≠ extEnergy T V) :
    IsOptimal (U ∪ T) n ∧
      IsOptimal (V ∪ T) n ∧
      ¬ DilationEquivSimilar (U ∪ T) (V ∪ T) ∧
      ¬ UniqueMinimizer n := by
  classical
  obtain ⟨hUopt, hEqU⟩ := isOptimal_of_distance_complete_multisite_completion
    T U n k hkn hTcard hUcard hUT hTdist hDS_U
  obtain ⟨hVopt, hEqV⟩ := isOptimal_of_distance_complete_multisite_completion
    T V n k hkn hTcard hVcard hVT hTdist hDS_V
  have hnon_img := multisite_completions_nonsimilar_of_ne_energy
    T U V (by omega) hUT hVT hEqU hEqV hne
  have hnon_sim : ¬ DilationEquivSimilar (U ∪ T) (V ∪ T) := by
    rw [similar_iff_image]
    exact hnon_img
  refine ⟨hUopt, hVopt, hnon_sim, ?_⟩
  intro huniq
  exact hnon_sim (huniq (U ∪ T) (V ∪ T) hUopt hVopt)

/-- **Universal Three-Completion Multiplicity Theorem (`K = 3`):**
if a distance-complete core `T` (`T.card = n - k ≥ 2`, `distinctDistances T = d(n)`)
possesses three `k`-site completions `U₁, U₂, U₃` with pairwise distinct `extEnergy T ·`,
then `HasAtLeastKNonsimilarMinimizers 3 n` holds. -/
theorem distance_complete_core_three_completions_hasAtLeastThreeMinimizers
    (T U₁ U₂ U₃ : Finset Plane) (n k : ℕ) (hnk : 2 ≤ n - k) (hkn : k ≤ n)
    (hTcard : T.card = n - k)
    (hU₁ : U₁.card = k) (hU₂ : U₂.card = k) (hU₃ : U₃.card = k)
    (hd₁ : Disjoint U₁ T) (hd₂ : Disjoint U₂ T) (hd₃ : Disjoint U₃ T)
    (hTdist : distinctDistances T = minimalDistinctDistances n)
    (hDS₁ : Erdos91.DistanceErasure.distanceSet (U₁ ∪ T) ⊆
      Erdos91.DistanceErasure.distanceSet T)
    (hDS₂ : Erdos91.DistanceErasure.distanceSet (U₂ ∪ T) ⊆
      Erdos91.DistanceErasure.distanceSet T)
    (hDS₃ : Erdos91.DistanceErasure.distanceSet (U₃ ∪ T) ⊆
      Erdos91.DistanceErasure.distanceSet T)
    (hne12 : extEnergy T U₁ ≠ extEnergy T U₂)
    (hne13 : extEnergy T U₁ ≠ extEnergy T U₃)
    (hne23 : extEnergy T U₂ ≠ extEnergy T U₃) :
    HasAtLeastKNonsimilarMinimizers 3 n := by
  classical
  obtain ⟨hOpt1, hOpt2, hns12, _⟩ :=
    distance_complete_core_multisite_nonsimilar_of_ne_extEnergy
      T U₁ U₂ n k hnk hkn hTcard hU₁ hU₂ hd₁ hd₂ hTdist hDS₁ hDS₂ hne12
  obtain ⟨_, hOpt3, hns13, _⟩ :=
    distance_complete_core_multisite_nonsimilar_of_ne_extEnergy
      T U₁ U₃ n k hnk hkn hTcard hU₁ hU₃ hd₁ hd₃ hTdist hDS₁ hDS₃ hne13
  obtain ⟨_, _, hns23, _⟩ :=
    distance_complete_core_multisite_nonsimilar_of_ne_extEnergy
      T U₂ U₃ n k hnk hkn hTcard hU₂ hU₃ hd₂ hd₃ hTdist hDS₂ hDS₃ hne23
  let A₁ := U₁ ∪ T
  let A₂ := U₂ ∪ T
  let A₃ := U₃ ∪ T
  have hne_A12 : A₁ ≠ A₂ := by
    intro h
    apply hns12
    change DilationEquivSimilar A₁ A₂
    rw [← h]
    exact similar_refl A₁
  have hne_A13 : A₁ ≠ A₃ := by
    intro h
    apply hns13
    change DilationEquivSimilar A₁ A₃
    rw [← h]
    exact similar_refl A₁
  have hne_A23 : A₂ ≠ A₃ := by
    intro h
    apply hns23
    change DilationEquivSimilar A₂ A₃
    rw [← h]
    exact similar_refl A₂
  refine ⟨{A₁, A₂, A₃}, ?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem, Finset.card_pair hne_A23]
    simp [hne_A12, hne_A13]
  · intro A hA
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl | rfl
    · exact hOpt1
    · exact hOpt2
    · exact hOpt3
  · intro A hA C hC hAC hsim
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA hC
    rcases hA with rfl | rfl | rfl <;> rcases hC with rfl | rfl | rfl
    · exact hAC rfl
    · exact hns12 hsim
    · exact hns13 hsim
    · exact hns12 (similar_symm hsim)
    · exact hAC rfl
    · exact hns23 hsim
    · exact hns13 (similar_symm hsim)
    · exact hns23 (similar_symm hsim)
    · exact hAC rfl

end Erdos91.DistanceCompleteCoreMultiSiteTheory

namespace Erdos91.SixThreeMinimizersAndCoreCompletions
open scoped Classical
open Finset Erdos91.DistanceErasure Minimizer91 PlateauDefinitions91
  Erdos91.SmallCasesAndSquareBarrier Erdos91.FourNonuniqueAndDoubleEquilateral
  Erdos91.ThreeUniqueMinimizer Erdos91.SixAndSevenWheelConfig
  Erdos91.TwoDistanceCapAndSixNonunique Erdos91.EightAndNineNonunique
  Erdos91.DistanceCompleteCoreMultiSiteTheory
  Erdos91.GeneralMultiplicityAndDensityOne Erdos91.AsymptoticDensityOneAndGlobalBounds
open SimilarityEnergy91 (pairEnergy)
open EnergyLevels91 (energy)

/-- Shared 4-point distance-complete core `T₄ = {equiP1, hexM1, equiP2, hexQ2}` for `n = 6`. -/
noncomputable def hexCore4 : Finset Plane :=
  {equiP1, hexM1, equiP2, hexQ2}

/-- Shared 5-point distance-complete core `T₅ = insert equiP0 hexCore4` for `n = 6`. -/
noncomputable def hexCore5 : Finset Plane :=
  insert equiP0 hexCore4

/-- Alternative 5-point distance-complete core `T₅' = insert equiP3 hexCore4` for `n = 6`. -/
noncomputable def hexCore5Alt : Finset Plane :=
  insert equiP3 hexCore4

/-- 2-site completion `U_hex = {equiP3, hexQ3}` completing `hexCore4` to `regularHexagon`. -/
noncomputable def compHex2 : Finset Plane :=
  {equiP3, hexQ3}

/-- 2-site completion `U_tri = {equiP0, triP7}` completing `hexCore4` to `equiSixGrid`. -/
noncomputable def compTri2 : Finset Plane :=
  {equiP0, triP7}

/-- 2-site completion `U_spoke = {equiP0, equiP3}` completing `hexCore4` to `spokedPentagonB`. -/
noncomputable def compSpoke2 : Finset Plane :=
  {equiP0, equiP3}

/-- The 6-point equilateral triangle grid `equiSixGrid = compTri2 ∪ hexCore4`. -/
noncomputable def equiSixGrid : Finset Plane :=
  compTri2 ∪ hexCore4

/-- The 6-point 5-spoked wheel `spokedPentagonB = compSpoke2 ∪ hexCore4`. -/
noncomputable def spokedPentagonB : Finset Plane :=
  compSpoke2 ∪ hexCore4

/-- The 6-point regular hexagon written as the 2-site completion `compHex2 ∪ hexCore4`. -/
noncomputable def regularHexagonU : Finset Plane :=
  compHex2 ∪ hexCore4

theorem card_hexCore4 : hexCore4.card = 4 := by
  obtain ⟨_, _, _, _, _, _, h1m1, h12, h1q2, _, _, hm12, hm1q2, _, _, h2q2, _, _, _, _, _⟩ :=
    wheel_pairwise_ne
  unfold hexCore4
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair h2q2]
  · simp [hm12, hm1q2]
  · simp [h1m1, h12, h1q2]

theorem card_hexCore5 : hexCore5.card = 5 := by
  obtain ⟨h01, h0m1, h02, h0q2, _, _⟩ := wheel_pairwise_ne
  unfold hexCore5
  rw [Finset.card_insert_of_notMem, card_hexCore4]
  simp [hexCore4, h01, h0m1, h02, h0q2]

theorem card_hexCore5Alt : hexCore5Alt.card = 5 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, h13, _, _, _, hm13, _, _, h23, _, hq23, _, _⟩ :=
    wheel_pairwise_ne
  unfold hexCore5Alt
  rw [Finset.card_insert_of_notMem, card_hexCore4]
  simp [hexCore4, h13.symm, hm13.symm, h23.symm, hq23.symm]

theorem card_compHex2 : compHex2.card = 2 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h3q3⟩ :=
    wheel_pairwise_ne
  exact Finset.card_pair h3q3

theorem card_compTri2 : compTri2.card = 2 := by
  obtain ⟨_, h70, _⟩ := tri_extra_ne
  exact Finset.card_pair h70.symm

theorem card_compSpoke2 : compSpoke2.card = 2 := by
  obtain ⟨_, _, _, _, h03, _⟩ := wheel_pairwise_ne
  exact Finset.card_pair h03

theorem disjoint_compHex2_hexCore4 : Disjoint compHex2 hexCore4 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, h13, h1q3, _, _, hm13, hm1q3, _, h23, h2q3, hq23, hq2q3, _⟩ :=
    wheel_pairwise_ne
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [compHex2,Finset.mem_insert, Finset.mem_singleton] at hx1
  rcases hx1 with rfl | rfl <;>
    simp only [hexCore4, Finset.mem_insert, Finset.mem_singleton] at hx2 <;>
    rcases hx2 with h | h | h | h
  · exact h13 h.symm
  · exact hm13 h.symm
  · exact h23 h.symm
  · exact hq23 h.symm
  · exact h1q3 h.symm
  · exact hm1q3 h.symm
  · exact h2q3 h.symm
  · exact hq2q3 h.symm

theorem disjoint_compTri2_hexCore4 : Disjoint compTri2 hexCore4 := by
  obtain ⟨h01, h0m1, h02, h0q2, _, _⟩ := wheel_pairwise_ne
  obtain ⟨_, _, h71, h7m1, h72, h7q2, _, _⟩ := tri_extra_ne
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [compTri2, Finset.mem_insert, Finset.mem_singleton] at hx1
  rcases hx1 with rfl | rfl <;>
    simp only [hexCore4, Finset.mem_insert, Finset.mem_singleton] at hx2 <;>
    rcases hx2 with h | h | h | h
  · exact h01 h
  · exact h0m1 h
  · exact h02 h
  · exact h0q2 h
  · exact h71 h
  · exact h7m1 h
  · exact h72 h
  · exact h7q2 h

theorem disjoint_compSpoke2_hexCore4 : Disjoint compSpoke2 hexCore4 := by
  obtain ⟨h01, h0m1, h02, h0q2, _, _, _, _, _, h13, _, _, _, hm13, _, _, h23, _, hq23, _, _⟩ :=
    wheel_pairwise_ne
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [compSpoke2, Finset.mem_insert, Finset.mem_singleton] at hx1
  rcases hx1 with rfl | rfl <;>
    simp only [hexCore4, Finset.mem_insert, Finset.mem_singleton] at hx2 <;>
    rcases hx2 with h | h | h | h
  · exact h01 h
  · exact h0m1 h
  · exact h02 h
  · exact h0q2 h
  · exact h13 h.symm
  · exact hm13 h.symm
  · exact h23 h.symm
  · exact hq23 h.symm

theorem three_dists_subset_distanceSet_hexCore4 :
    ({1, Real.sqrt 3, 2} : Finset ℝ) ⊆ Erdos91.DistanceErasure.distanceSet hexCore4 := by
  obtain ⟨_, _, _, _, _, _, h1m1, h12, _, _, _, hm12, _, _⟩ := wheel_pairwise_ne
  obtain ⟨s1, _, _, _, _, _⟩ := sqrt3_sub_lemmas
  have hd1 : dist equiP1 equiP2 = 1 := by
    have hsq : dist equiP1 equiP2 ^ 2 = 1 ^ 2 := by
      rw [plane_dist_sq]; dsimp [equiP1, equiP2]; rw [s1]; norm_num
    nlinarith [dist_nonneg (x := equiP1) (y := equiP2)]
  have hd3 : dist hexM1 equiP2 = Real.sqrt 3 := by
    have hsq : dist hexM1 equiP2 ^ 2 = Real.sqrt 3 ^ 2 := by
      rw [plane_dist_sq, Real.sq_sqrt (by norm_num)]; dsimp [hexM1, equiP2]; rw [s1]; norm_num
    nlinarith [dist_nonneg (x := hexM1) (y := equiP2), Real.sqrt_nonneg 3]
  have hd2 : dist hexM1 equiP1 = 2 := by
    have hsq : dist hexM1 equiP1 ^ 2 = 2 ^ 2 := by
      rw [plane_dist_sq]; dsimp [hexM1, equiP1]; norm_num
    nlinarith [dist_nonneg (x := hexM1) (y := equiP1)]
  intro r hr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl
  · exact (mem_distanceSet hexCore4 1).mpr
      ⟨equiP1, by simp [hexCore4], equiP2, by simp [hexCore4], h12, hd1⟩
  · exact (mem_distanceSet hexCore4 (Real.sqrt 3)).mpr
      ⟨hexM1, by simp [hexCore4], equiP2, by simp [hexCore4], hm12, hd3⟩
  · exact (mem_distanceSet hexCore4 2).mpr
      ⟨hexM1, by simp [hexCore4], equiP1, by simp [hexCore4], h1m1.symm, hd2⟩

theorem card_three_dists_eq_three :
    ({1, Real.sqrt 3, 2} : Finset ℝ).card = 3 := by
  have hsub : Erdos91.DistanceErasure.distanceSet centeredWheelSeven ⊆
      {1, Real.sqrt 3, 2} := distanceSet_centeredWheelSeven_subset
  have hlo : 3 ≤ ({1, Real.sqrt 3, 2} : Finset ℝ).card := by
    have hmin := minimal_le centeredWheelSeven 7 card_centeredWheelSeven
    rw [minimalDistinctDistances_seven] at hmin
    exact hmin.trans (Finset.card_le_card hsub)
  have hhi : ({1, Real.sqrt 3, 2} : Finset ℝ).card ≤ 3 :=
    (Finset.card_insert_le _ _).trans (Nat.succ_le_succ Finset.card_le_two)
  omega

theorem distanceSet_eq_and_distinctDistances_eq_three_of_subset
    (S : Finset Plane) (hcore : hexCore4 ⊆ S)
    (hsub : Erdos91.DistanceErasure.distanceSet S ⊆ {1, Real.sqrt 3, 2}) :
    Erdos91.DistanceErasure.distanceSet S = {1, Real.sqrt 3, 2} ∧
      distinctDistances S = 3 := by
  have hcore_ds : Erdos91.DistanceErasure.distanceSet hexCore4 ⊆
      Erdos91.DistanceErasure.distanceSet S := by
    change hexCore4.offDiag.image (fun p => dist p.1 p.2) ⊆
      S.offDiag.image (fun p => dist p.1 p.2)
    exact Finset.image_subset_image (Finset.offDiag_mono hcore)
  have heq : Erdos91.DistanceErasure.distanceSet S = {1, Real.sqrt 3, 2} :=
    Finset.Subset.antisymm hsub (three_dists_subset_distanceSet_hexCore4.trans hcore_ds)
  refine ⟨heq, ?_⟩
  change (Erdos91.DistanceErasure.distanceSet S).card = 3
  rw [heq, card_three_dists_eq_three]

theorem hexCore4_subset_centeredWheelSeven : hexCore4 ⊆ centeredWheelSeven := by
  intro x hx
  simp only [hexCore4, centeredWheelSeven, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  tauto

theorem distanceSet_hexCore4_eq :
    Erdos91.DistanceErasure.distanceSet hexCore4 = {1, Real.sqrt 3, 2} ∧
      distinctDistances hexCore4 = 3 := by
  apply distanceSet_eq_and_distinctDistances_eq_three_of_subset hexCore4 (Subset.refl _)
  have hsub : Erdos91.DistanceErasure.distanceSet hexCore4 ⊆
      Erdos91.DistanceErasure.distanceSet centeredWheelSeven := by
    change hexCore4.offDiag.image (fun p => dist p.1 p.2) ⊆
      centeredWheelSeven.offDiag.image (fun p => dist p.1 p.2)
    exact Finset.image_subset_image (Finset.offDiag_mono hexCore4_subset_centeredWheelSeven)
  exact hsub.trans distanceSet_centeredWheelSeven_subset

theorem distanceSet_regularHexagonU_subset :
    Erdos91.DistanceErasure.distanceSet regularHexagonU ⊆
      Erdos91.DistanceErasure.distanceSet hexCore4 := by
  rw [distanceSet_hexCore4_eq.1]
  have hsub : regularHexagonU ⊆ centeredWheelSeven := by
    intro x hx
    simp only [regularHexagonU, compHex2, hexCore4, centeredWheelSeven,
      Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    tauto
  have hds : Erdos91.DistanceErasure.distanceSet regularHexagonU ⊆
      Erdos91.DistanceErasure.distanceSet centeredWheelSeven := by
    change regularHexagonU.offDiag.image (fun p => dist p.1 p.2) ⊆
      centeredWheelSeven.offDiag.image (fun p => dist p.1 p.2)
    exact Finset.image_subset_image (Finset.offDiag_mono hsub)
  exact hds.trans distanceSet_centeredWheelSeven_subset

theorem distanceSet_spokedPentagonB_subset :
    Erdos91.DistanceErasure.distanceSet spokedPentagonB ⊆
      Erdos91.DistanceErasure.distanceSet hexCore4 := by
  rw [distanceSet_hexCore4_eq.1]
  have hsub : spokedPentagonB ⊆ centeredWheelSeven := by
    intro x hx
    simp only [spokedPentagonB, compSpoke2, hexCore4, centeredWheelSeven,
      Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    tauto
  have hds : Erdos91.DistanceErasure.distanceSet spokedPentagonB ⊆
      Erdos91.DistanceErasure.distanceSet centeredWheelSeven := by
    change spokedPentagonB.offDiag.image (fun p => dist p.1 p.2) ⊆
      centeredWheelSeven.offDiag.image (fun p => dist p.1 p.2)
    exact Finset.image_subset_image (Finset.offDiag_mono hsub)
  exact hds.trans distanceSet_centeredWheelSeven_subset

theorem equiSixGrid_dist_sq_cases (x y : Plane)
    (hx : x ∈ equiSixGrid) (hy : y ∈ equiSixGrid) :
    dist x y ^ 2 = 0 ∨ dist x y ^ 2 = 1 ∨ dist x y ^ 2 = 3 ∨ dist x y ^ 2 = 4 := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := sqrt3_sub_lemmas
  obtain ⟨e1, e2, e3, e4, _, _⟩ := sqrt3_extra_lemmas
  simp only [equiSixGrid, compTri2, hexCore4, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with (rfl | rfl) | (rfl | rfl | rfl | rfl) <;>
    rcases hy with (rfl | rfl) | (rfl | rfl | rfl | rfl) <;>
    { rw [plane_dist_sq]
      dsimp [triP7, equiP0, equiP1, hexM1, equiP2, hexQ2]
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
      norm_num }

theorem distanceSet_equiSixGrid_subset :
    Erdos91.DistanceErasure.distanceSet equiSixGrid ⊆
      Erdos91.DistanceErasure.distanceSet hexCore4 := by
  rw [distanceSet_hexCore4_eq.1]
  intro r hr
  obtain ⟨x, hx, y, hy, hxy, rfl⟩ := (mem_distanceSet equiSixGrid r).mp hr
  have hpos : 0 < dist x y := dist_pos.mpr hxy
  have hcases := equiSixGrid_dist_sq_cases x y hx hy
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases hcases with h0 | h1 | h3 | h4
  · exfalso; nlinarith
  · left; nlinarith
  · right; left
    have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hpos3 : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    nlinarith
  · right; right; nlinarith

theorem extEnergy_hexCore4_completions :
    extEnergy hexCore4 compHex2 = 46 ∧
      extEnergy hexCore4 compTri2 = 34 ∧
      extEnergy hexCore4 compSpoke2 = 32 := by
  obtain ⟨h01, h0m1, h02, h0q2, h03, h0q3, h1m1, h12, h1q2, h13, h1q3,
    hm12, hm1q2, hm13, hm1q3, h2q2, h23, h2q3, hq23, hq2q3, h3q3⟩ := wheel_pairwise_ne
  obtain ⟨_, h70, h71, h7m1, h72, h7q2, _, _⟩ := tri_extra_ne
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hm_core4_1 : equiP1 ∉ ({hexM1, equiP2, hexQ2} : Finset Plane) := by
    simp [h1m1, h12, h1q2]
  have hm_core4_m1 : hexM1 ∉ ({equiP2, hexQ2} : Finset Plane) := by
    simp [hm12, hm1q2]
  have hm_core4_2 : equiP2 ∉ ({hexQ2} : Finset Plane) := by
    simp [h2q2]
  have he_core4 (v : Plane) :
      energy hexCore4 v =
        dist v equiP1 ^ 2 + dist v hexM1 ^ 2 + dist v equiP2 ^ 2 + dist v hexQ2 ^ 2 := by
    unfold energy hexCore4
    rw [Finset.sum_insert hm_core4_1, Finset.sum_insert hm_core4_m1,
      Finset.sum_insert hm_core4_2, Finset.sum_singleton]
    ring
  refine ⟨?_, ?_, ?_⟩
  · unfold extEnergy pairEnergy compHex2
    rw [Finset.sum_pair h3q3, Finset.sum_pair h3q3, Finset.sum_pair h3q3,
      Finset.sum_pair h3q3, he_core4 equiP3, he_core4 hexQ3]
    simp only [dist_self, plane_dist_sq]
    dsimp [equiP3, hexQ3, equiP1, hexM1, equiP2, hexQ2]
    ring_nf; rw [hs3]; norm_num
  · unfold extEnergy pairEnergy compTri2
    rw [Finset.sum_pair h70.symm, Finset.sum_pair h70.symm, Finset.sum_pair h70.symm,
      Finset.sum_pair h70.symm, he_core4 equiP0, he_core4 triP7]
    simp only [dist_self, plane_dist_sq]
    dsimp [equiP0, triP7, equiP1, hexM1, equiP2, hexQ2]
    ring_nf; rw [hs3]; norm_num
  · unfold extEnergy pairEnergy compSpoke2
    rw [Finset.sum_pair h03, Finset.sum_pair h03, Finset.sum_pair h03,
      Finset.sum_pair h03, he_core4 equiP0, he_core4 equiP3]
    simp only [dist_self, plane_dist_sq]
    dsimp [equiP0, equiP3, equiP1, hexM1, equiP2, hexQ2]
    ring_nf; rw [hs3]; norm_num

/-- **Unconditional `K = 3` Multiplicity Theorem at `n = 6` (`HasAtLeastKNonsimilarMinimizers 3 6`):**
at the unit rise `n = 6` (`d(5) = 2 < 3 = d(6)`), the three 2-site completions
`regularHexagonU`, `equiSixGrid`, and `spokedPentagonB` of the shared 4-point
distance-complete core `hexCore4` have pairwise distinct extension energies `46, 34, 32`,
certifying at least three pairwise nonsimilar optimal 6-point planar configurations. -/
theorem hasAtLeastThreeMinimizers_six :
    HasAtLeastKNonsimilarMinimizers 3 6 := by
  obtain ⟨he1, he2, he3⟩ := extEnergy_hexCore4_completions
  have hTdist : distinctDistances hexCore4 = minimalDistinctDistances 6 := by
    rw [distanceSet_hexCore4_eq.2, minimalDistinctDistances_six]
  exact distance_complete_core_three_completions_hasAtLeastThreeMinimizers
    hexCore4 compHex2 compTri2 compSpoke2 6 2 (by omega) (by omega)
    card_hexCore4 card_compHex2 card_compTri2 card_compSpoke2
    disjoint_compHex2_hexCore4 disjoint_compTri2_hexCore4 disjoint_compSpoke2_hexCore4
    hTdist distanceSet_regularHexagonU_subset distanceSet_equiSixGrid_subset
    distanceSet_spokedPentagonB_subset
    (by linarith) (by linarith) (by linarith)

/-- **Sharp First-Occurrence Bound for `K = 3` Minimizers (`n ≤ 6`):**
improves `exists_le_25_has_three_minimizers` (`n ≤ 25`) down to `n = 6`. -/
theorem exists_le_six_has_three_minimizers :
    ∃ n ≤ 6, HasAtLeastKNonsimilarMinimizers 3 n :=
  ⟨6, le_rfl, hasAtLeastThreeMinimizers_six⟩

/-- For every `N ≥ 6`, `6 ∈ goodMultiplicitySet 3 N`. -/
theorem six_mem_goodMultiplicitySet_three (N : ℕ) (hN : 6 ≤ N) :
    6 ∈ goodMultiplicitySet 3 N := by
  unfold goodMultiplicitySet
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hasAtLeastThreeMinimizers_six⟩

/-- For every `N : ℕ`, `6 ∉ badMultiplicitySet 3 N`. -/
theorem six_notMem_badMultiplicitySet_three (N : ℕ) :
    6 ∉ badMultiplicitySet 3 N := by
  unfold badMultiplicitySet
  rw [Finset.mem_filter]
  rintro ⟨_, hnot⟩
  exact hnot hasAtLeastThreeMinimizers_six


theorem distanceSet_hexCore5_eq :
    Erdos91.DistanceErasure.distanceSet hexCore5 = {1, Real.sqrt 3, 2} ∧
      distinctDistances hexCore5 = 3 := by
  apply distanceSet_eq_and_distinctDistances_eq_three_of_subset hexCore5
    (Finset.subset_insert _ _)
  have hsub : hexCore5 ⊆ centeredWheelSeven := by
    intro x hx
    simp only [hexCore5, hexCore4, centeredWheelSeven,
      Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    tauto
  have hds : Erdos91.DistanceErasure.distanceSet hexCore5 ⊆
      Erdos91.DistanceErasure.distanceSet centeredWheelSeven := by
    change hexCore5.offDiag.image (fun p => dist p.1 p.2) ⊆
      centeredWheelSeven.offDiag.image (fun p => dist p.1 p.2)
    exact Finset.image_subset_image (Finset.offDiag_mono hsub)
  exact hds.trans distanceSet_centeredWheelSeven_subset

theorem insert_triP7_hexCore5_eq_equiSixGrid :
    insert triP7 hexCore5 = equiSixGrid := by
  ext x
  simp only [hexCore5, equiSixGrid, compTri2, hexCore4,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem insert_equiP3_hexCore5_eq_spokedPentagonB :
    insert equiP3 hexCore5 = spokedPentagonB := by
  ext x
  simp only [hexCore5, spokedPentagonB, compSpoke2, hexCore4,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem energy_hexCore5_completions :
    energy hexCore5 triP7 = 13 ∧ energy hexCore5 equiP3 = 12 := by
  obtain ⟨h01, h0m1, h02, h0q2, h03, _, h1m1, h12, h1q2, _, _,
    hm12, hm1q2, _, _, h2q2, _, _, _, _, _⟩ := wheel_pairwise_ne
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hm0 : equiP0 ∉ hexCore4 := by simp [hexCore4, h01, h0m1, h02, h0q2]
  have hm1 : equiP1 ∉ ({hexM1, equiP2, hexQ2} : Finset Plane) := by simp [h1m1, h12, h1q2]
  have hmm1 : hexM1 ∉ ({equiP2, hexQ2} : Finset Plane) := by simp [hm12, hm1q2]
  have hm2 : equiP2 ∉ ({hexQ2} : Finset Plane) := by simp [h2q2]
  have he5 (v : Plane) :
      energy hexCore5 v =
        dist v equiP0 ^ 2 + dist v equiP1 ^ 2 + dist v hexM1 ^ 2 +
          dist v equiP2 ^ 2 + dist v hexQ2 ^ 2 := by
    unfold energy hexCore5
    rw [Finset.sum_insert hm0]
    unfold hexCore4
    rw [Finset.sum_insert hm1, Finset.sum_insert hmm1,
      Finset.sum_insert hm2, Finset.sum_singleton]
    ring
  refine ⟨?_, ?_⟩
  · rw [he5 triP7]
    simp only [plane_dist_sq]
    dsimp [triP7, equiP0, equiP1, hexM1, equiP2, hexQ2]
    ring_nf; rw [hs3]; norm_num
  · rw [he5 equiP3]
    simp only [plane_dist_sq]
    dsimp [equiP3, equiP0, equiP1, hexM1, equiP2, hexQ2]
    ring_nf; rw [hs3]; norm_num

/-- **Certified Single-Site (`k = 1`) Unequal-Energy Completions at the Unit Rise `n = 6`:**
the 5-point distance-complete core `hexCore5` possesses two single-site completions
`triP7` (`energy = 13`) and `equiP3` (`energy = 12`), certifying global optimality
and nonsimilarity of `equiSixGrid` and `spokedPentagonB` at the unit rise `d(5) = 2 < 3 = d(6)`. -/
theorem hexCore5_single_site_completions_nonsimilar :
    IsOptimal equiSixGrid 6 ∧
      IsOptimal spokedPentagonB 6 ∧
      ¬ DilationEquivSimilar equiSixGrid spokedPentagonB ∧
      ¬ UniqueMinimizer 6 := by
  obtain ⟨_, h70, h71, h7m1, h72, h7q2, _, _⟩ := tri_extra_ne
  obtain ⟨_, _, _, _, h03, _, _, _, _, h13, _, _, _, hm13, _, _, h23, _, hq23, _, _⟩ :=
    wheel_pairwise_ne
  obtain ⟨he7, he3⟩ := energy_hexCore5_completions
  have hTdist : distinctDistances hexCore5 = minimalDistinctDistances 6 := by
    rw [distanceSet_hexCore5_eq.2, minimalDistinctDistances_six]
  have hDS_tri : Erdos91.DistanceErasure.distanceSet ({triP7} ∪ hexCore5) ⊆
      Erdos91.DistanceErasure.distanceSet hexCore5 := by
    rw [Finset.singleton_union, insert_triP7_hexCore5_eq_equiSixGrid,
      distanceSet_hexCore5_eq.1, ← distanceSet_hexCore4_eq.1]
    exact distanceSet_equiSixGrid_subset
  have hDS_spoke : Erdos91.DistanceErasure.distanceSet ({equiP3} ∪ hexCore5) ⊆
      Erdos91.DistanceErasure.distanceSet hexCore5 := by
    rw [Finset.singleton_union, insert_equiP3_hexCore5_eq_spokedPentagonB,
      distanceSet_hexCore5_eq.1, ← distanceSet_hexCore4_eq.1]
    exact distanceSet_spokedPentagonB_subset
  have hd_tri : Disjoint ({triP7} : Finset Plane) hexCore5 := by
    rw [Finset.disjoint_singleton_left]
    simp [hexCore5, hexCore4, h70, h71, h7m1, h72, h7q2]
  have hd_spoke : Disjoint ({equiP3} : Finset Plane) hexCore5 := by
    rw [Finset.disjoint_singleton_left]
    simp [hexCore5, hexCore4, h03.symm, h13.symm, hm13.symm, h23.symm, hq23.symm]
  have hne_ext : extEnergy hexCore5 {triP7} ≠ extEnergy hexCore5 {equiP3} := by
    rw [extEnergy_singleton, extEnergy_singleton, he7, he3]
    norm_num
  have hres := distance_complete_core_multisite_nonsimilar_of_ne_extEnergy
    hexCore5 {triP7} {equiP3} 6 1 (by omega) (by omega) card_hexCore5
    (Finset.card_singleton _) (Finset.card_singleton _)
    hd_tri hd_spoke hTdist hDS_tri hDS_spoke hne_ext
  simpa only [Finset.singleton_union, insert_triP7_hexCore5_eq_equiSixGrid,
    insert_equiP3_hexCore5_eq_spokedPentagonB] using hres

end Erdos91.SixThreeMinimizersAndCoreCompletions

namespace Erdos91.EnergyLevelInvariance
open scoped Classical
open Finset Minimizer91 PlateauDefinitions91
  Erdos91.FourNonuniqueAndDoubleEquilateral
  Erdos91.ExactGridEnergyAndDeletionFamilies
  Erdos91.ThreeUniqueMinimizer
  Erdos91.GeneralMultiplicityAndDensityOne Erdos91.AsymptoticDensityOneAndGlobalBounds
open EnergyLevels91 (energy)

/-- Set of distinct vertex row energies `energy A x` attained across `x ∈ A`. -/
noncomputable def energyLevelSet (A : Finset Plane) : Finset ℝ :=
  A.image (energy A)

/-- Number of distinct vertex row energy levels `(A.image (energy A)).card` of `A`. -/
noncomputable def energyLevelCount (A : Finset Plane) : ℕ :=
  (energyLevelSet A).card

/-- Under any planar similarity `f : Plane ≃ᵈ Plane`, the vertex-energy level set scales
by `(Dilation.ratio f)^2`. -/
theorem energyLevelSet_image_dilationEquiv (A : Finset Plane) (f : Plane ≃ᵈ Plane) :
    energyLevelSet (A.image f) =
      (energyLevelSet A).image (fun e => (Dilation.ratio f : ℝ) ^ 2 * e) := by
  unfold energyLevelSet
  ext y
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨energy A x, ⟨x, hx, rfl⟩, (energy_image A f x).symm⟩
  · rintro ⟨e, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, energy_image A f x⟩

/-- The number of distinct vertex-energy levels `energyLevelCount` is invariant under
image by any `f : Plane ≃ᵈ Plane`. -/
theorem energyLevelCount_image_dilationEquiv (A : Finset Plane) (f : Plane ≃ᵈ Plane) :
    energyLevelCount (A.image f) = energyLevelCount A := by
  unfold energyLevelCount
  rw [energyLevelSet_image_dilationEquiv]
  have hr : (Dilation.ratio f : ℝ) ^ 2 ≠ 0 := by
    positivity [Dilation.ratio_pos f]
  exact Finset.card_image_of_injective _ (mul_right_injective₀ hr)

/-- **Universal Vertex-Energy Level-Count Similarity Invariance (`∀ A B`):**
any two similar finite planar point sets `A, B` have the same number of distinct
vertex-energy levels `energyLevelCount A = energyLevelCount B`. -/
theorem energyLevelCount_eq_of_similar (A B : Finset Plane)
    (hsim : DilationEquivSimilar A B) :
    energyLevelCount A = energyLevelCount B := by
  obtain ⟨f, rfl⟩ := (similar_iff_image A B).mp hsim
  exact (energyLevelCount_image_dilationEquiv A f).symm

/-- **Universal Vertex-Energy Level-Count Nonsimilarity Criterion (`∀ A B`):**
if `energyLevelCount A ≠ energyLevelCount B`, then `A` and `B` are not similar under
any full-plane similarity `DilationEquivSimilar`. -/
theorem not_similar_of_energyLevelCount_ne (A B : Finset Plane)
    (hne : energyLevelCount A ≠ energyLevelCount B) :
    ¬ DilationEquivSimilar A B :=
  fun hsim => hne (energyLevelCount_eq_of_similar A B hsim)

/-- Any two globally optimal `n`-point configurations with unequal vertex-energy level
counts certify `¬ UniqueMinimizer n`. -/
theorem not_uniqueMinimizer_of_optimal_energyLevelCount_ne (A B : Finset Plane) (n : ℕ)
    (hA : IsOptimal A n) (hB : IsOptimal B n)
    (hne : energyLevelCount A ≠ energyLevelCount B) :
    ¬ UniqueMinimizer n :=
  fun huniq => not_similar_of_energyLevelCount_ne A B hne (huniq A B hA hB)

/-- **Universal `K`-Multiplicity from Injective `energyLevelCount` (`∀ F K n`):**
any finite family `F` of at least `K` optimal `n`-point sets with pairwise distinct
`energyLevelCount` values certifies `HasAtLeastKNonsimilarMinimizers K n`. -/
theorem hasAtLeastKMinimizers_of_injOn_energyLevelCount
    (F : Finset (Finset Plane)) (K n : ℕ) (hK : K ≤ F.card)
    (hopt : ∀ A ∈ F, IsOptimal A n)
    (hinj : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → energyLevelCount A ≠ energyLevelCount B) :
    HasAtLeastKNonsimilarMinimizers K n := by
  obtain ⟨F0, hF0_sub, hF0_card⟩ := Finset.exists_subset_card_eq hK
  refine ⟨F0, hF0_card, fun A hA => hopt A (hF0_sub hA), ?_⟩
  intro A hA B hB hAB
  exact not_similar_of_energyLevelCount_ne A B (hinj A (hF0_sub hA) B (hF0_sub hB) hAB)

/-- **Universal `K`-Multiplicity from `energyLevelCount` Image Cardinality (`∀ F K n`):**
if `F` is a finite family of optimal `n`-point sets with `K ≤ (F.image energyLevelCount).card`,
then `HasAtLeastKNonsimilarMinimizers K n` holds. -/
theorem hasAtLeastKMinimizers_of_le_card_image_energyLevelCount
    (F : Finset (Finset Plane)) (K n : ℕ)
    (hK : K ≤ (F.image energyLevelCount).card)
    (hopt : ∀ A ∈ F, IsOptimal A n) :
    HasAtLeastKNonsimilarMinimizers K n := by
  obtain ⟨U0, hU0_sub, hU0_card, hU0_inj⟩ :=
    exists_rep_subset_card_eq_image F energyLevelCount
  apply hasAtLeastKMinimizers_of_injOn_energyLevelCount U0 K n (by omega)
  · intro A hA
    exact hopt A (hU0_sub hA)
  · exact hU0_inj

end Erdos91.EnergyLevelInvariance

namespace Erdos91.RegularHeptagonDeletionSpectrum
open scoped Classical
open Finset Minimizer91 PlateauDefinitions91
  Erdos91.TwoDistanceCapAndSixNonunique
  Erdos91.SevenNonuniqueHeptagonAndWheel
  Erdos91.EnergyLevelInvariance
open EnergyLevels91 (energy)

/-- The 6-point regular-heptagon arc obtained by deleting `heptPoint 0` from `regularHeptagon`. -/
noncomputable def heptagonSix : Finset Plane :=
  regularHeptagon.erase (heptPoint 0)

/-- Closed-form vertex energy `heptConstEnergy - (2 - 2 cos(2πd/7))` of `heptPoint d`
inside `heptagonSix = regularHeptagon.erase (heptPoint 0)`. -/
noncomputable def heptDelEnergy (d : ℕ) : ℝ :=
  heptConstEnergy - (2 - 2 * Real.cos (heptAngle d))

/-- **Universal Optimality and Distance-Set Preservation for Regular-Heptagon Deletions (`∀ x`):**
for every vertex `x ∈ regularHeptagon`, `regularHeptagon.erase x` is a globally optimal
6-point configuration (`IsOptimal (regularHeptagon.erase x) 6`) with the same distance
set `{heptDist 1, heptDist 2, heptDist 3}` as `regularHeptagon`. -/
theorem regularHeptagon_erase_isOptimal_and_distanceSet_eq
    (x : Plane) (hx : x ∈ regularHeptagon) :
    IsOptimal (regularHeptagon.erase x) 6 ∧
      Erdos91.DistanceErasure.distanceSet (regularHeptagon.erase x) =
        Erdos91.DistanceErasure.distanceSet regularHeptagon := by
  have hflat : minimalDistinctDistances (7 - 1) = minimalDistinctDistances 7 := by
    change minimalDistinctDistances 6 = minimalDistinctDistances 7
    rw [minimalDistinctDistances_six, minimalDistinctDistances_seven]
  exact ⟨Erdos91.FlatCore.flat_erase_optimal regularHeptagon 7
      regularHeptagon_isOptimal hflat x hx,
    Erdos91.FlatCore.flat_erase_distanceSet regularHeptagon 7
      regularHeptagon_isOptimal hflat x hx⟩

/-- **Universal Vertex-Energy Formula on `regularHeptagon.erase x` (`∀ x y`):**
for any `x ∈ regularHeptagon` and `y ∈ regularHeptagon.erase x`,
`energy (regularHeptagon.erase x) y = heptConstEnergy - dist y x ^ 2`. -/
theorem energy_regularHeptagon_erase_eq
    (x y : Plane) (hx : x ∈ regularHeptagon) (hy : y ∈ regularHeptagon.erase x) :
    energy (regularHeptagon.erase x) y = heptConstEnergy - dist y x ^ 2 := by
  have hyH : y ∈ regularHeptagon := Finset.mem_of_mem_erase hy
  have hsum : dist y x ^ 2 + energy (regularHeptagon.erase x) y = energy regularHeptagon y := by
    unfold energy
    exact Finset.add_sum_erase regularHeptagon (fun z => dist y z ^ 2) hx
  rw [regularHeptagon_energy_const y hyH] at hsum
  linarith

/-- **Exact Chord-Energy Formula on `heptagonSix` (`∀ j ∈ [1, 6]`):**
for every `1 ≤ j ≤ 6`, `heptPoint j ∈ heptagonSix` and
`energy heptagonSix (heptPoint j) = heptDelEnergy j`. -/
theorem energy_heptagonSix_heptPoint_eq (j : ℕ) (hj_lo : 1 ≤ j) (hj_hi : j ≤ 6) :
    heptPoint j ∈ heptagonSix ∧
      energy heptagonSix (heptPoint j) = heptDelEnergy j := by
  have hj7 : j ∈ Finset.range 7 := Finset.mem_range.mpr (by omega)
  have h07 : (0 : ℕ) ∈ Finset.range 7 := Finset.mem_range.mpr (by omega)
  have hj_mem : heptPoint j ∈ regularHeptagon :=
    Finset.mem_image_of_mem heptPoint hj7
  have h0_mem : heptPoint 0 ∈ regularHeptagon :=
    Finset.mem_image_of_mem heptPoint h07
  have hne : heptPoint j ≠ heptPoint 0 := fun h => by
    have heq := heptPoint_injOn hj7 h07 h
    omega
  have hj6 : heptPoint j ∈ heptagonSix :=
    Finset.mem_erase.mpr ⟨hne, hj_mem⟩
  refine ⟨hj6, ?_⟩
  unfold heptagonSix
  rw [energy_regularHeptagon_erase_eq (heptPoint 0) (heptPoint j) h0_mem hj6,
    dist_heptPoint_sq_natDist, Nat.dist_zero_right]
  rfl

/-- Strict antitonicity of `Real.cos (heptAngle d)` on `0 ≤ a < b ≤ 3`. -/
theorem cos_heptAngle_strictAnti_of_le_three (a b : ℕ) (hab : a < b) (hb : b ≤ 3) :
    Real.cos (heptAngle b) < Real.cos (heptAngle a) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have ha_lo : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hab_r : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have hb_hi : (b : ℝ) ≤ 3 := by exact_mod_cast hb
  have ha_nonneg : 0 ≤ heptAngle a := by unfold heptAngle; positivity
  have hab_ang : heptAngle a < heptAngle b := by unfold heptAngle; nlinarith
  have hb_pi : heptAngle b ≤ Real.pi := by unfold heptAngle; nlinarith
  exact Real.strictAntiOn_cos
    ⟨ha_nonneg, le_trans (le_of_lt hab_ang) hb_pi⟩
    ⟨le_trans ha_nonneg (le_of_lt hab_ang), hb_pi⟩
    hab_ang

/-- Strict antitonicity of `heptDelEnergy d` on `0 ≤ a < b ≤ 3`. -/
theorem heptDelEnergy_strictAnti_of_le_three (a b : ℕ) (hab : a < b) (hb : b ≤ 3) :
    heptDelEnergy b < heptDelEnergy a := by
  have hcos := cos_heptAngle_strictAnti_of_le_three a b hab hb
  unfold heptDelEnergy
  linarith

/-- **Exact 3-Level Energy Spectrum of `heptagonSix` (`∀ x ∈ heptagonSix`):**
every vertex of `heptagonSix` has energy in `{heptDelEnergy 1, heptDelEnergy 2, heptDelEnergy 3}`,
`energyLevelSet heptagonSix = {heptDelEnergy 1, heptDelEnergy 2, heptDelEnergy 3}`, and
`energyLevelCount heptagonSix = 3`. -/
theorem energyLevelSet_and_count_heptagonSix (x : Plane) (hx : x ∈ heptagonSix) :
    energy heptagonSix x ∈ ({heptDelEnergy 1, heptDelEnergy 2, heptDelEnergy 3} : Finset ℝ) ∧
      energyLevelSet heptagonSix = {heptDelEnergy 1, heptDelEnergy 2, heptDelEnergy 3} ∧
      energyLevelCount heptagonSix = 3 := by
  obtain ⟨_, h4, h5, h6⟩ := cos_heptAngle_symm
  have hd4 : heptDelEnergy 4 = heptDelEnergy 3 := by unfold heptDelEnergy; rw [h4]
  have hd5 : heptDelEnergy 5 = heptDelEnergy 2 := by unfold heptDelEnergy; rw [h5]
  have hd6 : heptDelEnergy 6 = heptDelEnergy 1 := by unfold heptDelEnergy; rw [h6]
  have hmem_level : ∀ y ∈ heptagonSix,
      energy heptagonSix y ∈ ({heptDelEnergy 1, heptDelEnergy 2, heptDelEnergy 3} : Finset ℝ) := by
    intro y hy
    obtain ⟨hy_ne, hy_reg⟩ := Finset.mem_erase.mp hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy_reg
    rw [Finset.mem_range] at hj
    have hj_pos : 1 ≤ j := by
      by_contra h0
      have hj0 : j = 0 := by omega
      subst hj0
      exact hy_ne rfl
    have he := (energy_heptagonSix_heptPoint_eq j hj_pos (by omega)).2
    rw [he]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    have hj_cases : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
    rcases hj_cases with rfl | rfl | rfl | rfl | rfl | rfl
    · left; rfl
    · right; left; rfl
    · right; right; rfl
    · right; right; exact hd4
    · right; left; exact hd5
    · left; exact hd6
  have heq_set : energyLevelSet heptagonSix =
      {heptDelEnergy 1, heptDelEnergy 2, heptDelEnergy 3} := by
    apply Finset.Subset.antisymm
    · intro e he
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp he
      exact hmem_level y hy
    · intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      unfold energyLevelSet
      rcases he with rfl | rfl | rfl
      · obtain ⟨hm1, he1⟩ := energy_heptagonSix_heptPoint_eq 1 (by omega) (by omega)
        exact Finset.mem_image.mpr ⟨heptPoint 1, hm1, he1⟩
      · obtain ⟨hm2, he2⟩ := energy_heptagonSix_heptPoint_eq 2 (by omega) (by omega)
        exact Finset.mem_image.mpr ⟨heptPoint 2, hm2, he2⟩
      · obtain ⟨hm3, he3⟩ := energy_heptagonSix_heptPoint_eq 3 (by omega) (by omega)
        exact Finset.mem_image.mpr ⟨heptPoint 3, hm3, he3⟩
  have h12 : heptDelEnergy 1 ≠ heptDelEnergy 2 :=
    (ne_of_lt (heptDelEnergy_strictAnti_of_le_three 1 2 (by omega) (by omega))).symm
  have h13 : heptDelEnergy 1 ≠ heptDelEnergy 3 :=
    (ne_of_lt (heptDelEnergy_strictAnti_of_le_three 1 3 (by omega) (by omega))).symm
  have h23 : heptDelEnergy 2 ≠ heptDelEnergy 3 :=
    (ne_of_lt (heptDelEnergy_strictAnti_of_le_three 2 3 (by omega) (by omega))).symm
  refine ⟨hmem_level x hx, heq_set, ?_⟩
  unfold energyLevelCount
  rw [heq_set, Finset.card_insert_of_notMem, Finset.card_pair h23]
  simp [h12, h13]

end Erdos91.RegularHeptagonDeletionSpectrum

namespace Erdos91.FourNonsimilarMinimizersSix
open scoped Classical
open Finset Minimizer91 PlateauDefinitions91
  Erdos91.SmallCasesAndSquareBarrier
  Erdos91.FourNonuniqueAndDoubleEquilateral
  Erdos91.SixAndSevenWheelConfig
  Erdos91.TwoDistanceCapAndSixNonunique
  Erdos91.SevenNonuniqueHeptagonAndWheel
  Erdos91.EightAndNineNonunique
  Erdos91.DistanceCompleteCoreMultiSiteTheory
  Erdos91.SixThreeMinimizersAndCoreCompletions
  Erdos91.GeneralMultiplicityAndDensityOne Erdos91.AsymptoticDensityOneAndGlobalBounds
  Erdos91.EnergyLevelInvariance
  Erdos91.RegularHeptagonDeletionSpectrum
open EnergyLevels91 (energy)

/-- **Exact 1-Level Energy Spectrum of `regularHexagonU` (`∀ x ∈ regularHexagonU`):**
every vertex of `regularHexagonU` has energy `12`, `energyLevelSet regularHexagonU = {12}`,
and `energyLevelCount regularHexagonU = 1`. -/
theorem energy_regularHexagonU_and_levelCount (x : Plane) (hx : x ∈ regularHexagonU) :
    energy regularHexagonU x = 12 ∧
      energyLevelSet regularHexagonU = {12} ∧
      energyLevelCount regularHexagonU = 1 := by
  obtain ⟨_, _, _, _, _, _, h1m1, h12, h1q2, _, _,
    hm12, hm1q2, _, _, h2q2, _, _, _, _, h3q3⟩ := wheel_pairwise_ne
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hm1 : equiP1 ∉ ({hexM1, equiP2, hexQ2} : Finset Plane) := by simp [h1m1, h12, h1q2]
  have hmm1 : hexM1 ∉ ({equiP2, hexQ2} : Finset Plane) := by simp [hm12, hm1q2]
  have hm2 : equiP2 ∉ ({hexQ2} : Finset Plane) := by simp [h2q2]
  have he_hex (v : Plane) :
      energy regularHexagonU v =
        dist v equiP3 ^ 2 + dist v hexQ3 ^ 2 + dist v equiP1 ^ 2 +
          dist v hexM1 ^ 2 + dist v equiP2 ^ 2 + dist v hexQ2 ^ 2 := by
    unfold energy regularHexagonU
    rw [Finset.sum_union disjoint_compHex2_hexCore4]
    unfold compHex2 hexCore4
    rw [Finset.sum_pair h3q3, Finset.sum_insert hm1, Finset.sum_insert hmm1,
      Finset.sum_insert hm2, Finset.sum_singleton]
    ring
  have hall : ∀ y ∈ regularHexagonU, energy regularHexagonU y = 12 := by
    intro y hy
    simp only [regularHexagonU, compHex2, hexCore4, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with (rfl | rfl) | (rfl | rfl | rfl | rfl) <;>
      { rw [he_hex]
        simp only [plane_dist_sq]
        dsimp [equiP3, hexQ3, equiP1, hexM1, equiP2, hexQ2]
        ring_nf; rw [hs3]; norm_num }
  have heq_set : energyLevelSet regularHexagonU = {12} := by
    apply Finset.Subset.antisymm
    · intro e he
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp he
      simp [hall y hy]
    · intro e he
      simp only [Finset.mem_singleton] at he
      subst he
      have hp1 : equiP1 ∈ regularHexagonU := by simp [regularHexagonU, hexCore4]
      exact Finset.mem_image.mpr ⟨equiP1, hp1, hall equiP1 hp1⟩
  refine ⟨hall x hx, heq_set, ?_⟩
  unfold energyLevelCount
  rw [heq_set, Finset.card_singleton]

/-- **Exact 2-Level Energy Spectrum of `equiSixGrid` (`∀ x ∈ equiSixGrid`):**
every vertex of `equiSixGrid` has energy in `{7, 13}`, `energyLevelSet equiSixGrid = {7, 13}`,
and `energyLevelCount equiSixGrid = 2`. -/
theorem energy_equiSixGrid_and_levelCount (x : Plane) (hx : x ∈ equiSixGrid) :
    energy equiSixGrid x ∈ ({7, 13} : Finset ℝ) ∧
      energyLevelSet equiSixGrid = {7, 13} ∧
      energyLevelCount equiSixGrid = 2 := by
  obtain ⟨_, _, _, _, _, _, h1m1, h12, h1q2, _, _,
    hm12, hm1q2, _, _, h2q2, _, _, _, _, _⟩ := wheel_pairwise_ne
  obtain ⟨_, h70, _⟩ := tri_extra_ne
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hm1 : equiP1 ∉ ({hexM1, equiP2, hexQ2} : Finset Plane) := by simp [h1m1, h12, h1q2]
  have hmm1 : hexM1 ∉ ({equiP2, hexQ2} : Finset Plane) := by simp [hm12, hm1q2]
  have hm2 : equiP2 ∉ ({hexQ2} : Finset Plane) := by simp [h2q2]
  have he_tri (v : Plane) :
      energy equiSixGrid v =
        dist v equiP0 ^ 2 + dist v triP7 ^ 2 + dist v equiP1 ^ 2 +
          dist v hexM1 ^ 2 + dist v equiP2 ^ 2 + dist v hexQ2 ^ 2 := by
    unfold energy equiSixGrid
    rw [Finset.sum_union disjoint_compTri2_hexCore4]
    unfold compTri2 hexCore4
    rw [Finset.sum_pair h70.symm, Finset.sum_insert hm1, Finset.sum_insert hmm1,
      Finset.sum_insert hm2, Finset.sum_singleton]
    ring
  have hp0_val : energy equiSixGrid equiP0 = 7 := by
    rw [he_tri]; simp only [plane_dist_sq]
    dsimp [equiP0, triP7, equiP1, hexM1, equiP2, hexQ2]; ring_nf; rw [hs3]; norm_num
  have hp1_val : energy equiSixGrid equiP1 = 13 := by
    rw [he_tri]; simp only [plane_dist_sq]
    dsimp [equiP0, triP7, equiP1, hexM1, equiP2, hexQ2]; ring_nf; rw [hs3]; norm_num
  have hall : ∀ y ∈ equiSixGrid, energy equiSixGrid y ∈ ({7, 13} : Finset ℝ) := by
    intro y hy
    simp only [equiSixGrid, compTri2, hexCore4, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton] at hy
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hy with (rfl | rfl) | (rfl | rfl | rfl | rfl)
    · left; exact hp0_val
    · right; rw [he_tri]; simp only [plane_dist_sq]
      dsimp [equiP0, triP7, equiP1, hexM1, equiP2, hexQ2]; ring_nf; rw [hs3]; norm_num
    · right; exact hp1_val
    · right; rw [he_tri]; simp only [plane_dist_sq]
      dsimp [equiP0, triP7, equiP1, hexM1, equiP2, hexQ2]; ring_nf; rw [hs3]; norm_num
    · left; rw [he_tri]; simp only [plane_dist_sq]
      dsimp [equiP0, triP7, equiP1, hexM1, equiP2, hexQ2]; ring_nf; rw [hs3]; norm_num
    · left; rw [he_tri]; simp only [plane_dist_sq]
      dsimp [equiP0, triP7, equiP1, hexM1, equiP2, hexQ2]; ring_nf; rw [hs3]; norm_num
  have heq_set : energyLevelSet equiSixGrid = {7, 13} := by
    apply Finset.Subset.antisymm
    · intro e he
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp he
      exact hall y hy
    · intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      unfold energyLevelSet
      rcases he with rfl | rfl
      · exact Finset.mem_image.mpr ⟨equiP0, by simp [equiSixGrid, compTri2], hp0_val⟩
      · exact Finset.mem_image.mpr ⟨equiP1, by simp [equiSixGrid, hexCore4], hp1_val⟩
  refine ⟨hall x hx, heq_set, ?_⟩
  unfold energyLevelCount
  rw [heq_set, Finset.card_pair (by norm_num)]

/-- **Exact 4-Level Energy Spectrum of `spokedPentagonB` (`∀ x ∈ spokedPentagonB`):**
every vertex of `spokedPentagonB` has energy in `{5, 9, 10, 12}`,
`energyLevelSet spokedPentagonB = {5, 9, 10, 12}`, and
`energyLevelCount spokedPentagonB = 4`. -/
theorem energy_spokedPentagonB_and_levelCount (x : Plane) (hx : x ∈ spokedPentagonB) :
    energy spokedPentagonB x ∈ ({5, 9, 10, 12} : Finset ℝ) ∧
      energyLevelSet spokedPentagonB = {5, 9, 10, 12} ∧
      energyLevelCount spokedPentagonB = 4 := by
  obtain ⟨_, _, _, _, h03, _, h1m1, h12, h1q2, _, _,
    hm12, hm1q2, _, _, h2q2, _, _, _, _, _⟩ := wheel_pairwise_ne
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hm1 : equiP1 ∉ ({hexM1, equiP2, hexQ2} : Finset Plane) := by simp [h1m1, h12, h1q2]
  have hmm1 : hexM1 ∉ ({equiP2, hexQ2} : Finset Plane) := by simp [hm12, hm1q2]
  have hm2 : equiP2 ∉ ({hexQ2} : Finset Plane) := by simp [h2q2]
  have he_sp (v : Plane) :
      energy spokedPentagonB v =
        dist v equiP0 ^ 2 + dist v equiP3 ^ 2 + dist v equiP1 ^ 2 +
          dist v hexM1 ^ 2 + dist v equiP2 ^ 2 + dist v hexQ2 ^ 2 := by
    unfold energy spokedPentagonB
    rw [Finset.sum_union disjoint_compSpoke2_hexCore4]
    unfold compSpoke2 hexCore4
    rw [Finset.sum_pair h03, Finset.sum_insert hm1, Finset.sum_insert hmm1,
      Finset.sum_insert hm2, Finset.sum_singleton]
    ring
  have hp0_val : energy spokedPentagonB equiP0 = 5 := by
    rw [he_sp]; simp only [plane_dist_sq]
    dsimp [equiP0, equiP3, equiP1, hexM1, equiP2, hexQ2]; ring_nf; rw [hs3]; norm_num
  have hp2_val : energy spokedPentagonB equiP2 = 9 := by
    rw [he_sp]; simp only [plane_dist_sq]
    dsimp [equiP0, equiP3, equiP1, hexM1, equiP2, hexQ2]; ring_nf; rw [hs3]; norm_num
  have hp1_val : energy spokedPentagonB equiP1 = 10 := by
    rw [he_sp]; simp only [plane_dist_sq]
    dsimp [equiP0, equiP3, equiP1, hexM1, equiP2, hexQ2]; ring_nf; rw [hs3]; norm_num
  have hp3_val : energy spokedPentagonB equiP3 = 12 := by
    rw [he_sp]; simp only [plane_dist_sq]
    dsimp [equiP0, equiP3, equiP1, hexM1, equiP2, hexQ2]; ring_nf; rw [hs3]; norm_num
  have hall : ∀ y ∈ spokedPentagonB, energy spokedPentagonB y ∈ ({5, 9, 10, 12} : Finset ℝ) := by
    intro y hy
    simp only [spokedPentagonB, compSpoke2, hexCore4, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton] at hy
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hy with (rfl | rfl) | (rfl | rfl | rfl | rfl)
    · left; exact hp0_val
    · right; right; right; exact hp3_val
    · right; right; left; exact hp1_val
    · right; right; right; rw [he_sp]; simp only [plane_dist_sq]
      dsimp [equiP0, equiP3, equiP1, hexM1, equiP2, hexQ2]; ring_nf; rw [hs3]; norm_num
    · right; left; exact hp2_val
    · right; right; left; rw [he_sp]; simp only [plane_dist_sq]
      dsimp [equiP0, equiP3, equiP1, hexM1, equiP2, hexQ2]; ring_nf; rw [hs3]; norm_num
  have heq_set : energyLevelSet spokedPentagonB = {5, 9, 10, 12} := by
    apply Finset.Subset.antisymm
    · intro e he
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp he
      exact hall y hy
    · intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      unfold energyLevelSet
      rcases he with rfl | rfl | rfl | rfl
      · exact Finset.mem_image.mpr ⟨equiP0, by simp [spokedPentagonB, compSpoke2], hp0_val⟩
      · exact Finset.mem_image.mpr ⟨equiP2, by simp [spokedPentagonB, hexCore4], hp2_val⟩
      · exact Finset.mem_image.mpr ⟨equiP1, by simp [spokedPentagonB, hexCore4], hp1_val⟩
      · exact Finset.mem_image.mpr ⟨equiP3, by simp [spokedPentagonB, compSpoke2], hp3_val⟩
  refine ⟨hall x hx, heq_set, ?_⟩
  unfold energyLevelCount
  rw [heq_set, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_pair (by norm_num)]
  · norm_num
  · norm_num

/-- **Unconditional `K = 4` Multiplicity at `n = 6` (`∀ K ≤ 4, ∀ N ≥ 6`):**
the four globally optimal 6-point 3-distance configurations `regularHexagonU`, `equiSixGrid`,
`heptagonSix`, and `spokedPentagonB` have exact vertex-energy level counts `1, 2, 3, 4`
respectively, unconditionally certifying `HasAtLeastKNonsimilarMinimizers K 6`,
`6 ∈ goodMultiplicitySet K N`, `6 ∉ badMultiplicitySet K N`, and
`∃ n ≤ 6, HasAtLeastKNonsimilarMinimizers K n`. -/
theorem hasAtLeastKMinimizers_six_of_le_four_and_goodMultiplicitySet
    (K N : ℕ) (hK : K ≤ 4) (hN : 6 ≤ N) :
    HasAtLeastKNonsimilarMinimizers K 6 ∧
      6 ∈ goodMultiplicitySet K N ∧
      6 ∉ badMultiplicitySet K N ∧
      (∃ n ≤ 6, HasAtLeastKNonsimilarMinimizers K n) := by
  let F : Finset (Finset Plane) :=
    {regularHexagonU, equiSixGrid, heptagonSix, spokedPentagonB}
  have hopt_hex : IsOptimal regularHexagonU 6 :=
    (isOptimal_of_distance_complete_multisite_completion
      hexCore4 compHex2 6 2 (by omega) card_hexCore4 card_compHex2
      disjoint_compHex2_hexCore4
      (by rw [distanceSet_hexCore4_eq.2, minimalDistinctDistances_six])
      distanceSet_regularHexagonU_subset).1
  have hopt_tri : IsOptimal equiSixGrid 6 :=
    hexCore5_single_site_completions_nonsimilar.1
  have hopt_spoke : IsOptimal spokedPentagonB 6 :=
    hexCore5_single_site_completions_nonsimilar.2.1
  have h0_mem : heptPoint 0 ∈ regularHeptagon :=
    Finset.mem_image_of_mem heptPoint (Finset.mem_range.mpr (by omega))
  have hopt_hept : IsOptimal heptagonSix 6 :=
    (regularHeptagon_erase_isOptimal_and_distanceSet_eq (heptPoint 0) h0_mem).1
  have hc_hex : energyLevelCount regularHexagonU = 1 :=
    (energy_regularHexagonU_and_levelCount equiP1 (by simp [regularHexagonU, hexCore4])).2.2
  have hc_tri : energyLevelCount equiSixGrid = 2 :=
    (energy_equiSixGrid_and_levelCount equiP1 (by simp [equiSixGrid, hexCore4])).2.2
  have hc_hept : energyLevelCount heptagonSix = 3 :=
    (energyLevelSet_and_count_heptagonSix (heptPoint 1)
      (energy_heptagonSix_heptPoint_eq 1 (by omega) (by omega)).1).2.2
  have hc_spoke : energyLevelCount spokedPentagonB = 4 :=
    (energy_spokedPentagonB_and_levelCount equiP1 (by simp [spokedPentagonB, hexCore4])).2.2
  have himg : F.image energyLevelCount = {1, 2, 3, 4} := by
    apply Finset.Subset.antisymm
    · intro c hc
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hc
      simp only [F, Finset.mem_insert, Finset.mem_singleton] at hA
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hA with rfl | rfl | rfl | rfl
      · left; exact hc_hex
      · right; left; exact hc_tri
      · right; right; left; exact hc_hept
      · right; right; right; exact hc_spoke
    · intro c hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact Finset.mem_image.mpr ⟨regularHexagonU, by simp [F], hc_hex⟩
      · exact Finset.mem_image.mpr ⟨equiSixGrid, by simp [F], hc_tri⟩
      · exact Finset.mem_image.mpr ⟨heptagonSix, by simp [F], hc_hept⟩
      · exact Finset.mem_image.mpr ⟨spokedPentagonB, by simp [F], hc_spoke⟩
  have hcard_img : (F.image energyLevelCount).card = 4 := by
    rw [himg, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_pair (by omega)]
    · simp
    · simp
  have hK6 : HasAtLeastKNonsimilarMinimizers K 6 := by
    apply hasAtLeastKMinimizers_of_le_card_image_energyLevelCount F K 6 (by omega)
    intro A hA
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl | rfl | rfl
    · exact hopt_hex
    · exact hopt_tri
    · exact hopt_hept
    · exact hopt_spoke
  refine ⟨hK6, ?_, ?_, ⟨6, le_refl 6, hK6⟩⟩
  · unfold goodMultiplicitySet
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hK6⟩
  · unfold badMultiplicitySet
    rw [Finset.mem_filter]
    rintro ⟨_, hnot⟩
    exact hnot hK6

end Erdos91.FourNonsimilarMinimizersSix

set_option pp.explicit false
