module

public import Geometry956


@[expose] public section

/-!
# Remote translate padding for Erdős #956

Appends remote translation centers `(10(j + 1), 0)` to reach any prescribed
cardinality `N` while preserving pairwise disjointness and all existing
unit-distance pairs.
-/

namespace Erdos956.Padding

open Erdos956.Geometry

def remote (j : ℕ) : Plane := point (10 * ((j : ℝ) + 1)) 0

noncomputable def remoteCenters (t : ℕ) : Finset Plane :=
  (Finset.range t).image remote

theorem remote_x_ge_ten (j : ℕ) : 10 ≤ (remote j) 0 := by
  simp only [remote, point_zero]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  nlinarith

theorem remote_injective : Function.Injective remote := by
  intro j l h
  have hx : 10 * ((j : ℝ) + 1) = 10 * ((l : ℝ) + 1) := by
    simpa only [remote, point_zero] using congrArg (fun z : Plane => z 0) h
  have hc : (j : ℝ) = (l : ℝ) := by nlinarith
  exact_mod_cast hc

theorem remoteCenters_card (t : ℕ) : (remoteCenters t).card = t := by
  unfold remoteCenters
  rw [Finset.card_image_iff.mpr (fun _ _ _ _ h => remote_injective h)]
  simp

theorem old_remote_disjoint (X : Finset Plane)
    (hX : ∀ x ∈ X, x 0 ≤ 1) (t : ℕ) :
    Disjoint X (remoteCenters t) := by
  apply Finset.disjoint_left.mpr
  intro x hxX hxR
  rcases Finset.mem_image.mp hxR with ⟨j, _, rfl⟩
  have hx := hX (remote j) hxX
  have hr := remote_x_ge_ten j
  linarith

noncomputable def paddedCenters (X : Finset Plane) (t : ℕ) : Finset Plane :=
  X ∪ remoteCenters t

theorem paddedCenters_card (X : Finset Plane)
    (hX : ∀ x ∈ X, x 0 ≤ 1) (t : ℕ) :
    (paddedCenters X t).card = X.card + t := by
  unfold paddedCenters
  rw [Finset.card_union_of_disjoint (old_remote_disjoint X hX t), remoteCenters_card]

theorem paddedCenters_card_exact (X : Finset Plane)
    (hX : ∀ x ∈ X, x 0 ≤ 1) {N : ℕ} (hXN : X.card ≤ N) :
    (paddedCenters X (N - X.card)).card = N := by
  rw [paddedCenters_card X hX]
  omega

theorem remote_gap (j l : ℕ) (hjl : j ≠ l) :
    1 / 2 < |(remote l) 0 - (remote j) 0| := by
  have hlt : j < l ∨ l < j := lt_or_gt_of_ne hjl
  rcases hlt with hlt | hlt
  · have hcast : (j : ℝ) + 1 ≤ l := by exact_mod_cast (by omega : j + 1 ≤ l)
    have hval : 10 ≤ (remote l) 0 - (remote j) 0 := by
      simp only [remote, point_zero]
      nlinarith
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hcast : (l : ℝ) + 1 ≤ j := by exact_mod_cast (by omega : l + 1 ≤ j)
    have hval : (remote l) 0 - (remote j) 0 ≤ -10 := by
      simp only [remote, point_zero]
      nlinarith
    rw [abs_of_nonpos (by linarith)]
    linarith

theorem padded_differences_excluded (D : Set Plane) (X : Finset Plane) (t : ℕ)
    (hD : ∀ z ∈ D, |z 0| ≤ 1 / 2)
    (hXlow : ∀ x ∈ X, 0 ≤ x 0)
    (hXhigh : ∀ x ∈ X, x 0 ≤ 1)
    (hold : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → y - x ∉ D) :
    ∀ x ∈ paddedCenters X t, ∀ y ∈ paddedCenters X t,
      x ≠ y → y - x ∉ D := by
  intro x hx y hy hne hz
  have hhalf : |(y - x) 0| ≤ 1 / 2 := hD (y - x) hz
  have hcoord : (y - x) 0 = y 0 - x 0 := by simp
  rw [hcoord] at hhalf
  rcases Finset.mem_union.mp hx with hxX | hxR
  · rcases Finset.mem_union.mp hy with hyX | hyR
    · exact hold x hxX y hyX hne hz
    · rcases Finset.mem_image.mp hyR with ⟨j, _, rfl⟩
      have hxhigh := hXhigh x hxX
      have hyten := remote_x_ge_ten j
      have hgap : 9 ≤ (remote j) 0 - x 0 := by linarith
      have habs : 9 ≤ |(remote j) 0 - x 0| := by
        rw [abs_of_nonneg (by linarith)]
        exact hgap
      linarith
  · rcases Finset.mem_image.mp hxR with ⟨j, _, rfl⟩
    rcases Finset.mem_union.mp hy with hyX | hyR
    · have hylow := hXlow y hyX
      have hyhigh := hXhigh y hyX
      have hxten := remote_x_ge_ten j
      have hgap : y 0 - (remote j) 0 ≤ -9 := by linarith
      have habs : 9 ≤ |y 0 - (remote j) 0| := by
        rw [abs_of_nonpos (by linarith)]
        linarith
      linarith
    · rcases Finset.mem_image.mp hyR with ⟨l, _, rfl⟩
      have hneIndex : j ≠ l := fun he => hne (he ▸ rfl)
      have hgap := remote_gap j l hneIndex
      linarith

end Erdos956.Padding
