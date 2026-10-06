module

public import Mathlib.Tactic

@[expose] public section

/-!
Numeric auxiliary for the Claim 4 three-component triangle path-length split.
-/

namespace ErdosProblems.AntiRamseyCycleQuotientTriangleLengths

def trianglePathL (k b : ℕ) : ℕ := min b (k - 2)

def trianglePathT (k b : ℕ) : ℕ := k - 1 - trianglePathL k b

/-- The literal split leaves one vertex for the first component. In particular,
T may equal one; no extra orientation or prescribed endpoints are required. -/
theorem triangle_path_lengths_bounds {k b c : ℕ}
    (hk : 5 ≤ k) (hb : 3 ≤ b) (hc : 3 ≤ c) (hbc : k + 1 ≤ b + c) :
    1 ≤ trianglePathL k b ∧ trianglePathL k b ≤ b ∧
      1 ≤ trianglePathT k b ∧ trianglePathT k b ≤ c ∧
      trianglePathL k b + trianglePathT k b + 1 = k := by
  simp only [trianglePathT, trianglePathL]
  by_cases hmin : b ≤ k - 2
  · rw [Nat.min_eq_left hmin]
    omega
  · rw [Nat.min_eq_right (by omega : k - 2 ≤ b)]
    omega

/-- The exact two component lower-order bounds supply the same split.
No upper-order premise is needed for this numeric auxiliary. -/
theorem triangle_path_lengths_of_component_lower_bounds {k b c : ℕ}
    (hk : 5 ≤ k) (hb : 3 ≤ b) (hc : 3 ≤ c)
    (hbLower : k + 1 ≤ 2 * b) (hcLower : k + 1 ≤ 2 * c) :
    1 ≤ trianglePathL k b ∧ trianglePathL k b ≤ b ∧
      1 ≤ trianglePathT k b ∧ trianglePathT k b ≤ c ∧
      trianglePathL k b + trianglePathT k b + 1 = k := by
  exact triangle_path_lengths_bounds hk hb hc (by omega)

end ErdosProblems.AntiRamseyCycleQuotientTriangleLengths
