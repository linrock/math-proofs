module

public import SudakovScalars546
public import SudakovScalarsSuccessor546
public import SudakovAmplificationScalars546


@[expose] public section

/-! Concrete quantitative parameters for the unconditional graph amplifier. -/

namespace Erdos546

theorem quantitative_amplification_parameters546 (m a D n N : ℕ)
    (hm : 64 ≤ m) (ha : 3 ≤ a)
    (haA : a ≤ finalAmplificationParameter546 m)
    (hD : (a : ℝ) ^ 3 * D ≤ 2 * Real.sqrt m) (hn : n ≤ 2 * m)
    (hN : Real.rpow 2 (500 * Real.sqrt m / a) ≤ N) :
    ∃ (ε : ℝ) (r h t u : ℕ), 1 ≤ r ∧ 0 < ε ∧ ε ≤ 1 / 8 ∧
      2 * (D + 1 : ℝ) ≤ (ε / 8) ^ D * r ∧
      1 / (2 ^ h : ℝ) ≤ ε / 2 ∧ (2 * r) ^ h * n ≤ N ∧
      1 ≤ ε * t ∧ ε * t ≤ u ∧ 1 ≤ u ∧
      (t : ℝ) ≤ ε ^ (20 * u) * ((N : ℝ) / (2 * (r : ℝ) ^ h)) ∧
      (2 : ℝ) ^ (2 * a) * Real.sqrt m ≤ t ∧
      (N : ℝ) * Real.rpow 2 (-400 * Real.sqrt m / a) ≤
        ε ^ (20 * u) * ((N : ℝ) / (2 * (r : ℝ) ^ h)) := by
  let s : ℝ := Real.sqrt m
  let A : ℕ := finalAmplificationParameter546 m
  let ε : ℝ := 1 / (2 : ℝ) ^ (3 * a)
  let r : ℕ := 2 * (D + 1) * 2 ^ ((3 * a + 3) * D)
  let h : ℕ := 3 * a + 2
  let t : ℕ := ⌈(2 : ℝ) ^ (2 * a) * s⌉₊
  let u : ℕ := ⌈ε * t⌉₊
  let K : ℕ := 1 + (3 * a + 4) * D
  let den : ℝ := 2 * (r : ℝ) ^ h
  let Q : ℝ := ε ^ (20 * u) * ((N : ℝ) / den)
  have hmzero : m ≠ 0 := by omega
  have hapos : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hx : 0 ≤ s / a := div_nonneg hs hapos.le
  have hAthree : 3 ≤ A := finalAmplificationParameter546_ge_three m hm
  have hAquad : (8 : ℝ) * (A : ℝ) ^ 2 ≤ 9 * (2 : ℝ) ^ A := by
    exact_mod_cast nat_sparse_loss_bound A hAthree
  have haquad : (8 : ℝ) * (a : ℝ) ^ 2 ≤ 9 * (2 : ℝ) ^ a := by
    exact_mod_cast nat_sparse_loss_bound a ha
  have hAsqrt : (2 : ℝ) ^ A ≤ s := finalAmplificationParameter546_sqrt_lower m hmzero
  have hasqrt : (2 : ℝ) ^ a ≤ s := by
    have hpa : (2 : ℝ) ^ a ≤ (2 : ℝ) ^ A := by
      exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) haA
    exact hpa.trans hAsqrt
  have haquadS : (8 : ℝ) * (a : ℝ) ^ 2 ≤ 9 * s := by
    exact haquad.trans (mul_le_mul_of_nonneg_left hasqrt (by norm_num))
  have hupper : (2 : ℝ) * m < (2 : ℝ) ^ (2 * A + 3) := by
    exact_mod_cast nat_twice_size_log_threshold_bound m A
      (finalAmplificationParameter546_upper m)
  have hvertex : (2 : ℝ) * m ≤ Real.rpow 2 (4 * s / a) :=
    ramsey_vertex_exponent_bound m a A ha haA hupper hAquad hAsqrt
  have hnreal : (n : ℝ) ≤ Real.rpow 2 (4 * s / a) := by
    have hnm : (n : ℝ) ≤ (2 : ℝ) * m := by exact_mod_cast hn
    exact hnm.trans hvertex
  obtain ⟨hε, hεsmall⟩ := amplification_epsilon_bound a (by omega)
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hr : 1 ≤ r := Nat.succ_le_of_lt hrpos
  have hrnonneg : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hden : 0 < den := by dsimp [den]; positivity
  have hNnonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hinverse : 2 * (D + 1 : ℝ) ≤ (ε / 8) ^ D * r := by
    simpa [ε, r, Nat.cast_mul, Nat.cast_add, Nat.cast_pow] using
      (extraction_inverse_exact a D).ge
  have hdepth : 1 / (2 ^ h : ℝ) ≤ ε / 2 := by
    simpa [h, ε] using extraction_depth_bound a
  have hp2one : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * a) := one_le_pow₀ (by norm_num)
  have hs8 : (8 : ℝ) ≤ s := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact_mod_cast hm
  have hbase : 1 ≤ (2 : ℝ) ^ (2 * a) * s := by
    have hh := mul_le_mul_of_nonneg_left hs8 (by positivity : 0 ≤ (2 : ℝ) ^ (2 * a))
    nlinarith only [hh, hp2one]
  have htbase : (2 : ℝ) ^ (2 * a) * s ≤ (t : ℝ) := Nat.le_ceil _
  have htupper : (t : ℝ) ≤ 2 * (2 : ℝ) ^ (2 * a) * s := by
    simpa [t, mul_assoc] using nat_ceil_le_two_mul_of_one_le _ hbase
  have hεt : 1 ≤ ε * t :=
    (amplification_sparse_scale_ge_one a s hasqrt).trans
      (mul_le_mul_of_nonneg_left htbase hε.le)
  have huscale : ε * t ≤ (u : ℝ) := Nat.le_ceil _
  have hu1 : 1 ≤ u := by exact_mod_cast hεt.trans huscale
  have huupper : (u : ℝ) ≤ 2 * (t : ℝ) / (2 : ℝ) ^ (3 * a) := by
    have hh := nat_ceil_le_two_mul_of_one_le (ε * t) hεt
    change (u : ℝ) ≤ 2 * (ε * t) at hh
    convert hh using 1; dsimp [ε]; ring
  have hubound : (u : ℝ) ≤ 4 * s / (2 : ℝ) ^ a :=
    rounded_sparse_parameter_bound a s t u htupper huupper
  have hlow : 60 * a * (u : ℝ) ≤ 270 * s / a :=
    low_density_rounding_loss_bound a s u ha (Nat.cast_nonneg u) haquad hubound
  have hextract : ((h : ℕ) : ℝ) * (2 + (3 * (a : ℝ) + 4) * D) + 1 ≤
      50 * s / a := sparse_extraction_exponent_bound a D s ha haquadS hD
  have hrnat : r ≤ 2 ^ K := nat_extraction_ratio_bound a D (nat_two_pow_ge_succ D)
  have hrreal : (r : ℝ) ≤ (2 : ℝ) ^ K := by exact_mod_cast hrnat
  have hhostExp : (((K + 1) * h : ℕ) : ℝ) ≤ 50 * s / a := by
    dsimp [K, h] at hextract ⊢
    push_cast at hextract ⊢
    nlinarith only [hextract]
  have hdenExp : ((1 + K * h : ℕ) : ℝ) ≤ 50 * s / a := by
    have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    dsimp [K] at hextract ⊢
    push_cast at hextract ⊢
    nlinarith only [hextract, hh]
  have hhostBase : 2 * r ≤ 2 ^ (K + 1) := by
    calc
      2 * r ≤ 2 * 2 ^ K := Nat.mul_le_mul_left 2 hrnat
      _ = 2 ^ (K + 1) := by rw [pow_succ]; ring
  have hhostBound : (((2 * r) ^ h : ℕ) : ℝ) ≤ Real.rpow 2 (50 * s / a) := by
    calc
      (((2 * r) ^ h : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((K + 1) * h) := by
        exact_mod_cast (show (2 * r) ^ h ≤ 2 ^ ((K + 1) * h) by
          simpa only [pow_mul] using Nat.pow_le_pow_left hhostBase h)
      _ = Real.rpow 2 (((K + 1) * h : ℕ) : ℝ) := (Real.rpow_natCast 2 _).symm
      _ ≤ Real.rpow 2 (50 * s / a) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hhostExp
  have hhostReal : (((2 * r) ^ h : ℕ) : ℝ) * n ≤ (N : ℝ) := by
    calc
      (((2 * r) ^ h : ℕ) : ℝ) * n ≤
          Real.rpow 2 (50 * s / a) * Real.rpow 2 (4 * s / a) :=
        mul_le_mul hhostBound hnreal (Nat.cast_nonneg n)
          (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
      _ = Real.rpow 2 (54 * s / a) := by
        simp only [Real.rpow_eq_pow]
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring
      _ ≤ Real.rpow 2 (500 * s / a) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
          ring_nf at hx ⊢
          nlinarith only [hx])
      _ ≤ N := hN
  have hhost : (2 * r) ^ h * n ≤ N := by exact_mod_cast hhostReal
  have hdenBound : den ≤ Real.rpow 2 (50 * s / a) := by
    calc
      den ≤ 2 * (2 : ℝ) ^ (K * h) := by
        dsimp [den]
        have hh := pow_le_pow_left₀ hrnonneg hrreal h
        rw [← pow_mul] at hh
        exact mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = Real.rpow 2 ((1 + K * h : ℕ) : ℝ) := by
        simp only [Real.rpow_eq_pow]
        rw [Real.rpow_natCast, pow_add]
        norm_num
      _ ≤ Real.rpow 2 (50 * s / a) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hdenExp
  have hεpower : ε ^ (20 * u) = Real.rpow 2 (-(60 * (a : ℝ) * u)) := by
    have he : 60 * (a : ℝ) * u = (((3 * a) * (20 * u) : ℕ) : ℝ) := by
      push_cast
      ring
    simp only [Real.rpow_eq_pow]
    rw [he, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    simp [ε, ← pow_mul]
  have hεlower : Real.rpow 2 (-270 * s / a) ≤ ε ^ (20 * u) := by
    rw [hεpower]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      ring_nf at hlow ⊢
      linarith only [hlow])
  have hinv : Real.rpow 2 (-50 * s / a) ≤ 1 / den := by
    calc
      Real.rpow 2 (-50 * s / a) = 1 / Real.rpow 2 (50 * s / a) := by
        simp only [Real.rpow_eq_pow]
        rw [show -50 * s / a = -(50 * s / a) by ring, Real.rpow_neg (by norm_num)]
        simp only [one_div]
      _ ≤ 1 / den := one_div_le_one_div_of_le hden hdenBound
  have hfrac : Real.rpow 2 (-320 * s / a) ≤ ε ^ (20 * u) / den := by
    calc
      Real.rpow 2 (-320 * s / a) =
          Real.rpow 2 (-270 * s / a) * Real.rpow 2 (-50 * s / a) := by
        simp only [Real.rpow_eq_pow]
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring
      _ ≤ ε ^ (20 * u) * (1 / den) :=
        mul_le_mul hεlower hinv
          (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
          (pow_nonneg hε.le _)
      _ = ε ^ (20 * u) / den := by ring
  have hQlower : (N : ℝ) * Real.rpow 2 (-320 * s / a) ≤ Q := by
    have hh := mul_le_mul_of_nonneg_left hfrac hNnonneg
    simpa [Q, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh
  have hQreadiness : Real.rpow 2 (180 * s / a) ≤ Q := by
    calc
      Real.rpow 2 (180 * s / a) =
          Real.rpow 2 (500 * s / a) * Real.rpow 2 (-320 * s / a) := by
        simp only [Real.rpow_eq_pow]
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring
      _ ≤ (N : ℝ) * Real.rpow 2 (-320 * s / a) :=
        mul_le_mul_of_nonneg_right hN
          (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
      _ ≤ Q := hQlower
  have hs2m : s ≤ (2 : ℝ) * m := by
    have hsm : Real.sqrt (m : ℝ) ≤ m :=
      Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast (show 1 ≤ m by omega)))
    dsimp [s]
    nlinarith only [hsm, show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
  have hsvertex : s ≤ Real.rpow 2 (4 * s / a) := hs2m.trans hvertex
  have hpref := amplification_target_prefactor_bound a s ha haquadS
  have htBound : (t : ℝ) ≤ Real.rpow 2 (7 * s / a) := by
    calc
      (t : ℝ) ≤ 2 * (2 : ℝ) ^ (2 * a) * s := htupper
      _ ≤ 2 * (2 : ℝ) ^ (2 * a) * Real.rpow 2 (4 * s / a) :=
        mul_le_mul_of_nonneg_left hsvertex (by positivity)
      _ = Real.rpow 2 ((2 * a + 1 : ℕ) : ℝ) * Real.rpow 2 (4 * s / a) := by
        simp only [Real.rpow_eq_pow]
        rw [Real.rpow_natCast, pow_add]
        norm_num
        ring_nf; simp
      _ ≤ Real.rpow 2 (3 * s / a) * Real.rpow 2 (4 * s / a) := by
        apply mul_le_mul_of_nonneg_right _
          (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hpref
      _ = Real.rpow 2 (7 * s / a) := by
        simp only [Real.rpow_eq_pow]
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring
  have htQ : (t : ℝ) ≤ Q := htBound.trans
    ((Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      ring_nf at hx ⊢
      nlinarith only [hx])).trans hQreadiness)
  have hfinalLoss : (N : ℝ) * Real.rpow 2 (-400 * s / a) ≤ Q := by
    have hp : Real.rpow 2 (-400 * s / a) ≤ Real.rpow 2 (-320 * s / a) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
        ring_nf at hx ⊢
        nlinarith only [hx])
    exact (mul_le_mul_of_nonneg_left hp hNnonneg).trans hQlower
  exact ⟨ε, r, h, t, u, hr, hε, hεsmall, hinverse, hdepth, hhost,
    hεt, huscale, hu1, htQ, htbase, hfinalLoss⟩

#print axioms quantitative_amplification_parameters546

end Erdos546
