module

public import CoreEndpointBound1105

@[expose] public section

/-!
Sharpened intermediate-core numerical bound for the
original even palette threshold. The existing exact rational polynomial API
is applied first; its broader endpoint interval does not supply this bound. All natural subtraction guards are derived. This source proves no graph classification or original-color theorem.
-/

namespace ErdosProblems.PathUpperReduction.EvenIntermediateCoreScalar1105

open ErdosProblems.PathUpperReduction.CoreEndpointBound1105

/-- The a=3 endpoint uses the ORIGINAL threshold, including its d=4 boundary. -/
theorem even_cone_three_le_original_threshold (d n : ℕ)
    (hd : 4 ≤ d) (hn : 2 * d + 2 ≤ n) :
    extremalCount (n + 1) (2 * d + 3) 3 ≤
      n + max ((2 * d).choose 2 + 1)
        ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 2) := by
  have hKN : 2 * d + 3 ≤ n + 1 := by omega
  have hpoly := extremalCount_cast (n + 1) (2 * d + 3) 3 (by omega) hKN
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at hpoly
  have hdq : (4 : ℚ) ≤ (d : ℚ) := Nat.cast_le.mpr hd
  let A : ℕ := (2 * d).choose 2 + 1
  let B : ℕ := (d - 1).choose 2 + (d - 1) * (n - d + 1) + 2
  have hA : 2 * (A : ℚ) = 4 * (d : ℚ) ^ 2 - 2 * (d : ℚ) + 2 := by
    simp only [A, Nat.cast_add, Nat.cast_one, Nat.cast_choose_two,
      Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hB : 2 * (B : ℚ) =
      2 * ((d : ℚ) - 1) * (n : ℚ) - (d : ℚ) * ((d : ℚ) - 1) + 4 := by
    simp only [B, Nat.cast_add, Nat.cast_mul, Nat.cast_choose_two,
      Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_sub (by omega : d ≤ n),
      Nat.cast_one, Nat.cast_ofNat]
    ring
  by_cases hsmall : n ≤ 3 * d - 1
  · have hnq : (n : ℚ) ≤ 3 * (d : ℚ) - 1 := by
      have h : (n : ℚ) ≤ ((3 * d - 1 : ℕ) : ℚ) := Nat.cast_le.mpr hsmall
      simpa only [Nat.cast_sub (by omega : 1 ≤ 3 * d), Nat.cast_mul,
        Nat.cast_ofNat, Nat.cast_one] using h
    have hq : (extremalCount (n + 1) (2 * d + 3) 3 : ℚ) ≤ ((n + A : ℕ) : ℚ) := by
      rw [Nat.cast_add]
      nlinarith [hpoly, hA]
    have hNat : extremalCount (n + 1) (2 * d + 3) 3 ≤ n + A := Nat.cast_le.mp hq
    exact hNat.trans (Nat.add_le_add_left (le_max_left A B) n)
  · have hlarge : 3 * d ≤ n := by omega
    have hnq : 3 * (d : ℚ) ≤ (n : ℚ) := by
      have h : ((3 * d : ℕ) : ℚ) ≤ (n : ℚ) := Nat.cast_le.mpr hlarge
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
    have hp₁ : 0 ≤ ((d : ℚ) - 3) * ((n : ℚ) - 3 * (d : ℚ)) :=
      mul_nonneg (by linarith) (by linarith)
    have hp₂ : 0 ≤ ((d : ℚ) - 4) * ((d : ℚ) + 1) :=
      mul_nonneg (by linarith) (by linarith)
    have hq : (extremalCount (n + 1) (2 * d + 3) 3 : ℚ) ≤ ((n + B : ℕ) : ℚ) := by
      rw [Nat.cast_add]
      nlinarith [hpoly, hB, hp₁, hp₂]
    have hNat : extremalCount (n + 1) (2 * d + 3) 3 ≤ n + B := Nat.cast_le.mp hq
    exact hNat.trans (Nat.add_le_add_left (le_max_right A B) n)

/-- Convex interpolation on the exact sharpened interval 3≤a≤d−1.
The collapsed d=4 interval is handled before positive-factor cancellation. -/
theorem even_cone_intermediate_le_original_threshold (d n a : ℕ)
    (hd : 4 ≤ d) (hn : 2 * d + 2 ≤ n) (ha : 3 ≤ a) (had : a ≤ d - 1) :
    extremalCount (n + 1) (2 * d + 3) a ≤
      n + max ((2 * d).choose 2 + 1)
        ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 2) := by
  let t : ℕ := d - 1
  let M : ℕ := n + max ((2 * d).choose 2 + 1)
    ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 2)
  have hat : a ≤ t := had
  have h3M : extremalCount (n + 1) (2 * d + 3) 3 ≤ M :=
    even_cone_three_le_original_threshold d n hd hn
  by_cases haeq : a = 3
  · subst a
    exact h3M
  have ht3 : 3 < t := by dsimp [t] at hat ⊢; omega
  have hd5 : 5 ≤ d := by dsimp [t] at ht3; omega
  have htK : t ≤ 2 * d + 3 := by dsimp [t]; omega
  have haK : a ≤ 2 * d + 3 := hat.trans htK
  have hKN : 2 * d + 3 ≤ n + 1 := by omega
  have hpoly₃ := extremalCount_cast (n + 1) (2 * d + 3) 3 (by omega) hKN
  have hpoly_t := extremalCount_cast (n + 1) (2 * d + 3) t htK hKN
  have hpoly_a := extremalCount_cast (n + 1) (2 * d + 3) a haK hKN
  have htM : extremalCount (n + 1) (2 * d + 3) t ≤ M := by
    let B : ℕ := (d - 1).choose 2 + (d - 1) * (n - d + 1) + 2
    have htcast : (t : ℚ) = (d : ℚ) - 1 := by
      dsimp [t]
      exact Nat.cast_sub (by omega : 1 ≤ d)
    have hpoly := hpoly_t
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, htcast] at hpoly
    have hB : 2 * (B : ℚ) =
        2 * ((d : ℚ) - 1) * (n : ℚ) - (d : ℚ) * ((d : ℚ) - 1) + 4 := by
      simp only [B, Nat.cast_add, Nat.cast_mul, Nat.cast_choose_two,
        Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_sub (by omega : d ≤ n),
        Nat.cast_one, Nat.cast_ofNat]
      ring
    have hnlarge : d + 7 ≤ n := by omega
    have hnq : (d : ℚ) + 7 ≤ (n : ℚ) := by
      have h : ((d + 7 : ℕ) : ℚ) ≤ (n : ℚ) := Nat.cast_le.mpr hnlarge
      simpa only [Nat.cast_add, Nat.cast_ofNat] using h
    have hq : (extremalCount (n + 1) (2 * d + 3) t : ℚ) ≤ ((n + B : ℕ) : ℚ) := by
      rw [Nat.cast_add]
      nlinarith [hpoly, hB]
    have hNat : extremalCount (n + 1) (2 * d + 3) t ≤ n + B := Nat.cast_le.mp hq
    exact hNat.trans (Nat.add_le_add_left (le_max_right _ B) n)
  have haq : (3 : ℚ) ≤ (a : ℚ) := Nat.cast_le.mpr ha
  have htaq : (a : ℚ) ≤ (t : ℚ) := Nat.cast_le.mpr hat
  have htq : (3 : ℚ) < (t : ℚ) := Nat.cast_lt.mpr ht3
  have hw₁ : 0 ≤ (t : ℚ) - (a : ℚ) := sub_nonneg.mpr htaq
  have hw₂ : 0 ≤ (a : ℚ) - 3 := sub_nonneg.mpr haq
  have hw : 0 < (t : ℚ) - 3 := sub_pos.mpr htq
  have hchord :
      ((t : ℚ) - (a : ℚ)) * (2 * (extremalCount (n + 1) (2 * d + 3) 3 : ℚ)) +
          ((a : ℚ) - 3) * (2 * (extremalCount (n + 1) (2 * d + 3) t : ℚ)) -
          ((t : ℚ) - 3) * (2 * (extremalCount (n + 1) (2 * d + 3) a : ℚ)) =
        3 * ((t : ℚ) - 3) * ((a : ℚ) - 3) * ((t : ℚ) - (a : ℚ)) := by
    rw [hpoly₃, hpoly_t, hpoly_a]
    ring
  have hproduct :
      0 ≤ 3 * ((t : ℚ) - 3) * ((a : ℚ) - 3) * ((t : ℚ) - (a : ℚ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hw)) hw₂) hw₁
  have hinterp :
      ((t : ℚ) - 3) * (2 * (extremalCount (n + 1) (2 * d + 3) a : ℚ)) ≤
        ((t : ℚ) - (a : ℚ)) * (2 * (extremalCount (n + 1) (2 * d + 3) 3 : ℚ)) +
          ((a : ℚ) - 3) * (2 * (extremalCount (n + 1) (2 * d + 3) t : ℚ)) := by
    linarith [hchord, hproduct]
  have h3Mq : (extremalCount (n + 1) (2 * d + 3) 3 : ℚ) ≤ (M : ℚ) := Nat.cast_le.mpr h3M
  have htMq : (extremalCount (n + 1) (2 * d + 3) t : ℚ) ≤ (M : ℚ) := Nat.cast_le.mpr htM
  have h3M' : 2 * (extremalCount (n + 1) (2 * d + 3) 3 : ℚ) ≤ 2 * (M : ℚ) := by linarith
  have htM' : 2 * (extremalCount (n + 1) (2 * d + 3) t : ℚ) ≤ 2 * (M : ℚ) := by linarith
  have hweighted :
      ((t : ℚ) - (a : ℚ)) * (2 * (extremalCount (n + 1) (2 * d + 3) 3 : ℚ)) +
          ((a : ℚ) - 3) * (2 * (extremalCount (n + 1) (2 * d + 3) t : ℚ)) ≤
        ((t : ℚ) - 3) * (2 * (M : ℚ)) := by
    calc
      _ ≤ ((t : ℚ) - (a : ℚ)) * (2 * (M : ℚ)) +
          ((a : ℚ) - 3) * (2 * (M : ℚ)) :=
        add_le_add (mul_le_mul_of_nonneg_left h3M' hw₁)
          (mul_le_mul_of_nonneg_left htM' hw₂)
      _ = _ := by ring
  have htwice : 2 * (extremalCount (n + 1) (2 * d + 3) a : ℚ) ≤ 2 * (M : ℚ) :=
    le_of_mul_le_mul_left (hinterp.trans hweighted) hw
  have hq : (extremalCount (n + 1) (2 * d + 3) a : ℚ) ≤ (M : ℚ) := by linarith
  exact Nat.cast_le.mp hq

/-- Exact intermediate core count at the original even palette threshold. -/
theorem intermediate_core_count_le_original_even_threshold (d n r : ℕ)
    (hd : 4 ≤ d) (hn : 2 * d + 2 ≤ n)
    (hrLower : d + 4 ≤ r) (hrUpper : r ≤ 2 * d) :
    r.choose 2 + (2 * d + 3 - r) * (n + 1 - r) ≤
      n + max ((2 * d).choose 2 + 1)
        ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 2) := by
  let a : ℕ := 2 * d + 3 - r
  have ha : 3 ≤ a := by dsimp [a]; omega
  have had : a ≤ d - 1 := by dsimp [a]; omega
  have hKa : 2 * d + 3 - a = r := by dsimp [a]; omega
  have hNKa : n + 1 - (2 * d + 3) + a = n + 1 - r := by dsimp [a]; omega
  have h := even_cone_intermediate_le_original_threshold d n a hd hn ha had
  change (2 * d + 3 - a).choose 2 + a * (n + 1 - (2 * d + 3) + a) ≤ _ at h
  rw [hKa, hNKa] at h
  exact h

end ErdosProblems.PathUpperReduction.EvenIntermediateCoreScalar1105
