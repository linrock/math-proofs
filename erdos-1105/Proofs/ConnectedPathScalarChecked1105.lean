module

public import CoreEndpointBound1105

@[expose] public section

/-!
cone scalar adapter. The formula is the imported original
extremalCount, including natural subtraction and division. The general
shift is proved by the exact Mathlib binomial recurrence, not by introducing
a replacement extremal formula. No connected graph, color or anti-Ramsey
conclusion is asserted here.
-/

namespace ErdosProblems.PathUpperReduction.ConnectedPathScalarChecked1105

open ErdosProblems.PathUpperReduction.CoreEndpointBound1105

theorem extremalCount_cone_shift (n k a : ℕ) (hk : 5 ≤ k) (hkn : k ≤ n)
    (_ha : 1 ≤ a) (hak : a ≤ k - 2) :
    extremalCount (n + 1) (k + 1) (a + 1) =
      n + extremalCount n (k - 1) a := by
  let u : ℕ := k - 1 - a
  let b : ℕ := n - (k - 1) + a
  have hleft : k + 1 - (a + 1) = u + 1 := by dsimp [u]; omega
  have htail : n + 1 - (k + 1) + (a + 1) = b := by dsimp [b]; omega
  have hsum : u + b = n := by dsimp [u, b]; omega
  have hchoose : (u + 1).choose 2 = u + u.choose 2 := by
    simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' u 1
  unfold extremalCount
  rw [hleft, htail]
  change (u + 1).choose 2 + (a + 1) * b = n + (u.choose 2 + a * b)
  rw [hchoose]
  calc
    u + u.choose 2 + (a + 1) * b = (u + b) + (u.choose 2 + a * b) := by ring
    _ = n + (u.choose 2 + a * b) := by rw [hsum]

theorem cone_first_endpoint (n k : ℕ) (hk : 5 ≤ k) (hkn : k ≤ n) :
    extremalCount (n + 1) (k + 1) 2 = n + extremalCount n (k - 1) 1 := by
  exact extremalCount_cone_shift n k 1 hk hkn (by omega) (by omega)

theorem cone_last_endpoint (n k : ℕ) (hk : 5 ≤ k) (hkn : k ≤ n) :
    extremalCount (n + 1) (k + 1) ((k + 1 - 1) / 2) =
      n + extremalCount n (k - 1) ((k - 2) / 2) := by
  have ha : 1 ≤ (k - 2) / 2 := by omega
  have hak : (k - 2) / 2 ≤ k - 2 := by omega
  have hindex : (k - 2) / 2 + 1 = (k + 1 - 1) / 2 := by omega
  have hshift := extremalCount_cone_shift n k ((k - 2) / 2) hk hkn ha hak
  rw [hindex] at hshift
  exact hshift

theorem cone_endpoint_max (n k : ℕ) (hk : 5 ≤ k) (hkn : k ≤ n) :
    max (extremalCount (n + 1) (k + 1) 2)
        (extremalCount (n + 1) (k + 1) ((k + 1 - 1) / 2)) =
      n + max (extremalCount n (k - 1) 1)
        (extremalCount n (k - 1) ((k - 2) / 2)) := by
  rw [cone_first_endpoint n k hk hkn, cone_last_endpoint n k hk hkn, ← add_max]

theorem cone_endpoint_bound_iff (n k e : ℕ) (hk : 5 ≤ k) (hkn : k ≤ n) :
    (n + e ≤ max (extremalCount (n + 1) (k + 1) 2)
        (extremalCount (n + 1) (k + 1) ((k + 1 - 1) / 2))) ↔
      e ≤ max (extremalCount n (k - 1) 1)
        (extremalCount n (k - 1) ((k - 2) / 2)) := by
  rw [cone_endpoint_max n k hk hkn]
  exact add_le_add_iff_left n

end ErdosProblems.PathUpperReduction.ConnectedPathScalarChecked1105
