module

public import Mathlib


@[expose] public section

/-!
# Bad fibers of product rectangle families

Defines the fiber slice union `badFiber S T x = ⋃_{i : x ∈ S i} T i` and bounds
its counting fraction by the sum of slice fractions $\sum_{i : x \in S_i} |T_i| / |\beta|$.
-/

namespace Erdos2.Rectangles

open Finset

variable {Ω β I : Type*} [Fintype Ω] [Fintype β] [Fintype I]
  [DecidableEq Ω] [DecidableEq β]

/-- The union of rectangle slices above one old-coordinate point. -/
def badFiber (S : I → Finset Ω) (T : I → Finset β) (x : Ω) : Finset β :=
  univ.biUnion fun i => if x ∈ S i then T i else ∅

/-- Counting fraction, defined independently of any old-coordinate weight. -/
noncomputable def fraction (B : Finset β) : ℝ :=
  (B.card : ℝ) / Fintype.card β

omit [Fintype Ω] [Fintype β] in
theorem mem_badFiber (S : I → Finset Ω) (T : I → Finset β) (x : Ω) (y : β) :
    y ∈ badFiber S T x ↔ ∃ i, x ∈ S i ∧ y ∈ T i := by
  classical
  simp only [badFiber, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    by_cases hx : x ∈ S i
    · exact ⟨i, hx, by simpa [hx] using hi⟩
    · simp [hx] at hi
  · rintro ⟨i, hx, hy⟩
    exact ⟨i, by simpa [hx] using hy⟩

omit [Fintype Ω] [Fintype β] in
theorem badFiber_card_le (S : I → Finset Ω) (T : I → Finset β) (x : Ω) :
    (badFiber S T x).card ≤ ∑ i, if x ∈ S i then (T i).card else 0 := by
  classical
  unfold badFiber
  calc
    _ ≤ ∑ i : I, (if x ∈ S i then T i else ∅).card := Finset.card_biUnion_le
    _ = _ := by
      apply sum_congr rfl
      intro i hi
      by_cases h : x ∈ S i <;> simp [h]

omit [DecidableEq β] in
theorem fraction_nonneg (B : Finset β) : 0 ≤ fraction B := by
  unfold fraction
  positivity

omit [DecidableEq β] in
theorem fraction_le_one (B : Finset β) [Nonempty β] : fraction B ≤ 1 := by
  have hN : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hN).mpr
  simpa using (show (B.card : ℝ) ≤ (Fintype.card β : ℝ) by
    exact_mod_cast B.card_le_univ)

omit [Fintype Ω] in
theorem badFiber_fraction_le (S : I → Finset Ω) (T : I → Finset β) (x : Ω)
    [Nonempty β] :
    fraction (badFiber S T x) ≤ ∑ i, if x ∈ S i then fraction (T i) else 0 := by
  classical
  have hreal : ((badFiber S T x).card : ℝ) ≤
      ∑ i, if x ∈ S i then ((T i).card : ℝ) else 0 := by
    exact_mod_cast badFiber_card_le S T x
  calc
    fraction (badFiber S T x) ≤
      (∑ i, if x ∈ S i then ((T i).card : ℝ) else 0) / Fintype.card β :=
        div_le_div_of_nonneg_right hreal (Nat.cast_nonneg _)
    _ = _ := by
      rw [Finset.sum_div]
      apply sum_congr rfl
      intro i hi
      by_cases h : x ∈ S i <;> simp [h, fraction]

end Erdos2.Rectangles
