module

public import CoreEndpointBound1105
public import ConnectedPathScalarChecked1105

@[expose] public section

/-!
Scalar extremal-count bounds on the core-size interval for the odd-path cone
reduction.
-/

namespace ErdosProblems.PathUpperReduction.UniformWindowScalar1105

open ErdosProblems.PathUpperReduction.CoreEndpointBound1105
open ErdosProblems.PathUpperReduction.ConnectedPathScalarChecked1105

/-- The odd-cone interval uses the accepted base endpoint theorem after the
exact cone shift. No new convexity argument is needed for this application. -/
theorem odd_cone_intermediate_count_le_endpoints (ell n d : ℕ)
    (hell : 4 ≤ ell) (hn : 2 * ell + 1 ≤ n)
    (hd3 : 3 ≤ d) (hdell : d ≤ ell) :
    extremalCount (n + 1) (2 * ell + 2) d ≤
      max (extremalCount (n + 1) (2 * ell + 2) 3)
        (extremalCount (n + 1) (2 * ell + 2) ell) := by
  have hk : 5 ≤ 2 * ell + 1 := by omega
  have hshift (a : ℕ) (ha : 1 ≤ a) (hak : a ≤ 2 * ell - 1) :
      extremalCount (n + 1) (2 * ell + 2) (a + 1) =
        n + extremalCount n (2 * ell) a := by
    have h := extremalCount_cone_shift n (2 * ell + 1) a hk hn ha (by omega)
    have hplus : 2 * ell + 1 + 1 = 2 * ell + 2 := by omega
    have hminus : 2 * ell + 1 - 1 = 2 * ell := by omega
    rw [hplus, hminus] at h
    exact h
  have hd : d - 1 + 1 = d := by omega
  have hl : ell - 1 + 1 = ell := by omega
  have h_d := hshift (d - 1) (by omega) (by omega)
  rw [hd] at h_d
  have h_three := hshift 2 (by omega) (by omega)
  have h_last := hshift (ell - 1) (by omega) (by omega)
  rw [hl] at h_last
  have hcap := extremalCount_endpoints n (2 * ell) (d - 1)
    (by omega) (by omega) (by omega) (by omega)
  have ht : (2 * ell - 1) / 2 = ell - 1 := by omega
  rw [ht] at hcap
  rw [h_d, h_three, h_last, ← add_max]
  exact Nat.add_le_add_left hcap n

/-- The literal odd FC linear branch, including its subtraction, equals
the existing h(n,k-1,ell-1) on the original n>=k domain. -/
theorem odd_linear_eq_extremal (ell n : ℕ) (hell : 4 ≤ ell)
    (hn : 2 * ell + 1 ≤ n) :
    extremalCount n (2 * ell) (ell - 1) =
      (ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + 1 := by
  have hmajor : 2 * ell - (ell - 1) = ell + 1 := by omega
  have hminor : n - 2 * ell + (ell - 1) = n - ell - 1 := by omega
  have htail : n - ell + 1 = (n - ell - 1) + 2 := by omega
  have hchoose_base : ell.choose 2 = (ell - 1) + (ell - 1).choose 2 := by
    have he : ell - 1 + 1 = ell := by omega
    simpa only [he, Nat.choose_one_right] using Nat.choose_succ_succ' (ell - 1) 1
  have hchoose : (ell + 1).choose 2 =
      (ell - 1).choose 2 + 2 * (ell - 1) + 1 := by
    have h : (ell + 1).choose 2 = ell + ell.choose 2 := by
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' ell 1
    rw [hchoose_base] at h
    omega
  unfold extremalCount
  rw [hmajor, hminor, hchoose, htail]
  ring

/-- For every original odd host, not just a finite window, the literal
maximum threshold dominates the intermediate a=2 path count. -/
theorem odd_original_threshold_dominates_two (ell n : ℕ) (hell : 4 ≤ ell)
    (hn : 2 * ell + 1 ≤ n) :
    extremalCount n (2 * ell) 2 ≤
      max ((2 * ell - 1).choose 2 + 1)
        (extremalCount n (2 * ell) (ell - 1)) := by
  have hKN : 2 * ell ≤ n := by omega
  have hpoly₂ := extremalCount_cast n (2 * ell) 2 (by omega) hKN
  have hpoly_last := extremalCount_cast n (2 * ell) (ell - 1) (by omega) hKN
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hpoly₂
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega : 1 ≤ ell),
    Nat.cast_one] at hpoly_last
  have hA :
      2 * (((2 * ell - 1).choose 2 + 1 : ℕ) : ℚ) =
        4 * (ell : ℚ) ^ 2 - 6 * (ell : ℚ) + 4 := by
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_choose_two,
      Nat.cast_sub (by omega : 1 ≤ 2 * ell), Nat.cast_mul, Nat.cast_ofNat]
    ring
  by_cases hlow : n ≤ 3 * ell - 3
  · have hnt : n + 3 ≤ 3 * ell := by omega
    have hnq : (n : ℚ) + 3 ≤ 3 * (ell : ℚ) := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        (Nat.cast_le.mpr hnt : ((n + 3 : ℕ) : ℚ) ≤ ((3 * ell : ℕ) : ℚ))
    have hreal : (extremalCount n (2 * ell) 2 : ℚ) ≤
        (((2 * ell - 1).choose 2 + 1 : ℕ) : ℚ) := by
      nlinarith [hpoly₂, hA]
    exact le_trans (Nat.cast_le.mp hreal) (le_max_left _ _)
  · have hnt : 3 * ell ≤ n + 2 := by omega
    have hnq : 3 * (ell : ℚ) ≤ (n : ℚ) + 2 := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        (Nat.cast_le.mpr hnt : ((3 * ell : ℕ) : ℚ) ≤ ((n + 2 : ℕ) : ℚ))
    have hellq : (4 : ℚ) ≤ (ell : ℚ) := Nat.cast_le.mpr hell
    have hfactor : 0 ≤ (ell : ℚ) - 3 := by linarith
    have hgap : 0 ≤ (n : ℚ) - (3 * (ell : ℚ) - 2) := by linarith
    have hmul := mul_nonneg hfactor hgap
    have hproduct := mul_nonneg
      (Nat.cast_nonneg ell : (0 : ℚ) ≤ (ell : ℚ)) hfactor
    have hreal : (extremalCount n (2 * ell) 2 : ℚ) ≤
        (extremalCount n (2 * ell) (ell - 1) : ℚ) := by
      nlinarith [hpoly₂, hpoly_last, hmul, hproduct]
    exact le_trans (Nat.cast_le.mp hreal) (le_max_right _ _)

/-- The exact original odd high-palette hypothesis gives the strict cone
threshold needed to exclude every actual core slot d>=3 and the empty core.
No graph, favorable core, rainbow path or closure premise is present. -/
theorem odd_palette_strict_cone_threshold (ell n q : ℕ) (hell : 4 ≤ ell)
    (hn : 2 * ell + 1 ≤ n)
    (hq : max ((2 * ell - 1).choose 2 + 1)
      ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + 1) < q) :
    max (extremalCount (n + 1) (2 * ell + 2) 3)
      (extremalCount (n + 1) (2 * ell + 2) ell) < n + q := by
  rw [← odd_linear_eq_extremal ell n hell hn] at hq
  have htwo : extremalCount n (2 * ell) 2 < q :=
    lt_of_le_of_lt (odd_original_threshold_dominates_two ell n hell hn) hq
  have hlast : extremalCount n (2 * ell) (ell - 1) < q :=
    lt_of_le_of_lt (le_max_right _ _) hq
  have hsucc : 2 * ell + 1 + 1 = 2 * ell + 2 := by omega
  have hpred : 2 * ell + 1 - 1 = 2 * ell := by omega
  have hlastSucc : ell - 1 + 1 = ell := by omega
  have hthree := extremalCount_cone_shift n (2 * ell + 1) 2
    (by omega) hn (by omega) (by omega)
  have hcone_last := extremalCount_cone_shift n (2 * ell + 1) (ell - 1)
    (by omega) hn (by omega) (by omega)
  rw [hsucc, hpred] at hthree
  rw [hsucc, hpred, hlastSucc] at hcone_last
  rw [hthree, hcone_last, ← add_max]
  exact Nat.add_lt_add_left (max_lt_iff.mpr ⟨htwo, hlast⟩) n

end ErdosProblems.PathUpperReduction.UniformWindowScalar1105
