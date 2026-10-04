module

public import LowDensityPairs546
public import LowDensityCleaningCorollaries546
public import LowDensityBinomial546
public import Mathlib.Analysis.SpecialFunctions.Pow.Real


@[expose] public section

/-!
# A completely rounded integer-power low-density pair lemma

An implementation of Sudakov's Lemma 2.3 with `u = ceil (ε*t)` and reservoir
`ε^(20*u)*N`. Since `u ≤ 2*ε*t` when `ε*t ≥ 1`, this gives the same type of
lemma with real exponent constant 40. The larger absolute constant is harmless
for Erdős #546. No graph-theoretic implication is assumed.
-/

namespace Erdos546

open Finset
open scoped BigOperators

variable {V : Type*} [DecidableEq V]

set_option maxHeartbeats 2000000 in
/-- The integer-power version permits any integer `u ≥ ε*t`; choosing its
ceiling gives the desired asymptotic loss. All host and clique sizes are exact
natural cardinalities, and the reservoir lower bound is a real inequality. -/
theorem exists_monoPair_of_low_density_integer_power
    (H : SimpleGraph V) [DecidableRel H.Adj] (U : Finset V) (ε : ℝ) (t u : ℕ)
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 8) (hεt : 1 ≤ ε * t)
    (hu : ε * t ≤ u) (hu1 : 1 ≤ u)
    (hsize : (t : ℝ) ≤ ε ^ (20 * u) * U.card)
    (hdensity : (redDegreeSum H U : ℝ) ≤ ε * U.card ^ 2) :
    ∃ X Y : Finset V, X ⊆ U ∧ Y ⊆ U ∧
      (MonoPair H X Y ∨ MonoPair Hᶜ X Y) ∧ X.card = t ∧
      ε ^ (20 * u) * U.card ≤ (Y.card : ℝ) := by
  classical
  have hεone : ε ≤ 1 := by linarith
  have htpos : 0 < t := by
    by_contra hn
    have : t = 0 := by omega
    norm_num [this] at hεt
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (Nat.succ_le_of_lt htpos)
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hN0 : (0 : ℝ) ≤ U.card := Nat.cast_nonneg U.card
  have huR : ε * t ≤ (u : ℝ) := hu
  have hu1R : (1 : ℝ) ≤ u := by exact_mod_cast hu1
  have hpow_small : ε ^ (20 * u) ≤ 1 / 84 := by
    calc
      ε ^ (20 * u) ≤ ε ^ 3 := pow_le_pow_of_le_one hε.le hεone (by omega)
      _ ≤ (1 / 8 : ℝ) ^ 3 := pow_le_pow_left₀ hε.le hεsmall 3
      _ ≤ 1 / 84 := by norm_num
  have hNlargeR : 84 * (t : ℝ) ≤ U.card := by
    have hp := mul_le_mul_of_nonneg_right hpow_small hN0
    nlinarith only [hp, hsize]
  have hNlarge : 84 * t ≤ U.card := by exact_mod_cast hNlargeR
  have hNpos : 0 < U.card := by omega
  obtain ⟨T, hTU, hTcard, hTdeg⟩ :=
    exists_half_subset_degree_le_density H U ε hε hdensity
  have hTpos : 0 < T.card := by omega
  obtain ⟨B, hBT, hBc, hBpos, hBbound, hBcase⟩ :
      ∃ B : Finset V, B ⊆ T ∧ Hᶜ.IsClique (B : Set V) ∧ 0 < B.card ∧
        B.card ≤ 2 * t ∧ (B.card = 2 * t ∨ MaximumClique Hᶜ B T) := by
    obtain ⟨B₀, hmax⟩ := exists_maximumClique Hᶜ T
    by_cases hbig : 2 * t ≤ B₀.card
    · obtain ⟨B, hBB, hBcard⟩ := exists_subset_card_eq hbig
      refine ⟨B, hBB.trans hmax.1, hmax.2.1.subset (by simpa using hBB), ?_, ?_, Or.inl hBcard⟩
      · omega
      · omega
    · obtain ⟨v, hv⟩ := card_pos.mp hTpos
      have hsingle : Hᶜ.IsClique (({v} : Finset V) : Set V) := by
        simp [SimpleGraph.IsClique]
      have hB1 : 1 ≤ B₀.card := by
        simpa using hmax.2.2 {v} (singleton_subset_iff.mpr hv) hsingle
      exact ⟨B₀, hmax.1, hmax.2.1, by omega, by omega, Or.inr hmax⟩
  obtain ⟨F, hFsub, hFbudget, hFmask⟩ :=
    exists_third_budget_mask_subset H T B U.card ε hε hBpos (by
      intro b hb
      exact hTdeg b (hBT hb))
  have hFB : Disjoint B F := by
    apply disjoint_left.mpr
    intro b hb hf
    exact (mem_sdiff.mp (hFsub hf)).2 hb
  have hFT : F ⊆ T := hFsub.trans Finset.sdiff_subset
  have hFU : F ⊆ U := hFT.trans hTU
  have hBcardT : B.card ≤ T.card := card_le_card hBT
  have hFlarge : (U.card : ℝ) / 7 ≤ F.card := by
    have hdiff : (((T \ B).card : ℕ) : ℝ) = (T.card : ℝ) - B.card := by
      rw [card_sdiff_of_subset hBT, Nat.cast_sub hBcardT]
    have hTcardR : (U.card : ℝ) ≤ 2 * T.card := by exact_mod_cast hTcard
    have hBboundR : (B.card : ℝ) ≤ 2 * t := by exact_mod_cast hBbound
    rw [hdiff] at hFbudget
    linarith only [hFbudget, hTcardR, hBboundR, hNlargeR]
  let r : ℕ := ⌈3 * ε * B.card⌉₊
  let l : ℕ := ⌈8 * ε * t⌉₊
  have hb0 : (0 : ℝ) ≤ B.card := Nat.cast_nonneg B.card
  have hBboundR : (B.card : ℝ) ≤ 2 * t := by exact_mod_cast hBbound
  have hepsB := mul_le_mul_of_nonneg_left hBboundR hε.le
  have hεBt : 3 * ε * B.card ≤ 6 * ε * t := by nlinarith only [hepsB]
  have hrscale : 3 * ε * B.card ≤ (r : ℝ) := Nat.le_ceil _
  have hrupper : (r : ℝ) < 3 * ε * B.card + 1 := Nat.ceil_lt_add_one (by positivity)
  have hlscale : 8 * ε * t ≤ (l : ℝ) := Nat.le_ceil _
  have hlupper : (l : ℝ) < 8 * ε * t + 1 := Nat.ceil_lt_add_one (by positivity)
  have hrB : r ≤ B.card := by
    apply Nat.ceil_le.mpr
    have hmul := mul_nonneg (show 0 ≤ (1 / 8 : ℝ) - ε by linarith) hb0
    nlinarith only [hmul, hb0]
  have hlt : l ≤ t := by
    apply Nat.ceil_le.mpr
    have hmul := mul_nonneg (show 0 ≤ (1 / 8 : ℝ) - ε by linarith) ht0
    nlinarith only [hmul, ht0]
  have hrl : r < l := by
    have hR : (r : ℝ) < l := by nlinarith only [hrupper, hεBt, hεt, hlscale]
    exact_mod_cast hR
  have hrbound : r ≤ 7 * u := by
    have : (r : ℝ) ≤ 7 * u := by nlinarith only [hrupper, hεBt, huR, hu1R]
    exact_mod_cast this
  have hlbound : l ≤ 9 * u := by
    have : (l : ℝ) ≤ 9 * u := by nlinarith only [hlupper, huR, hu1R]
    exact_mod_cast this
  have hrlt : r + l ≤ 16 * u := by omega
  have hm : ∀ v ∈ F, (B.filter (H.Adj v)).card ≤ r := by
    intro v hv
    exact Nat.cast_le.mp ((hFmask v hv).trans hrscale)
  have hsmall_binom : (B.card.choose r : ℝ) * ε ^ r ≤ 1 :=
    choose_mul_pow_le_one_of_three_mul B.card r ε hε hrscale
  have hlarge_binom : ((t + l).choose t : ℝ) * ε ^ l ≤ 1 := by
    rw [Nat.choose_symm_add]
    apply choose_mul_pow_le_one_of_three_mul (t + l) l ε hε
    have hlR : (l : ℝ) ≤ t := by exact_mod_cast hlt
    have hmul := mul_le_mul_of_nonneg_left hlR hε.le
    simp only [Nat.cast_add]
    nlinarith only [hmul, hlscale]
  let C : ℕ := B.card.choose r * (t + l).choose t
  have hCscale : (C : ℝ) * ε ^ (r + l) ≤ 1 := by
    have hmul := mul_le_mul hsmall_binom hlarge_binom (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    dsimp [C]
    rw [Nat.cast_mul, pow_add]
    nlinarith only [hmul]
  let A : ℝ := ε ^ (20 * u) * U.card
  let q : ℕ := ⌈A⌉₊
  have hA1 : 1 ≤ A := ht1.trans hsize
  have hA0 : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 1).trans hA1
  have hqA : A ≤ (q : ℝ) := Nat.le_ceil _
  have hqthree : ((q + 1 : ℕ) : ℝ) ≤ 3 * A := by
    have hqupper : (q : ℝ) < A + 1 := Nat.ceil_lt_add_one hA0
    simp only [Nat.cast_add, Nat.cast_one]
    linarith only [hqupper, hA1]
  let z : ℕ := 20 * u - (r + l)
  have hz4 : 4 ≤ z := by dsimp [z]; omega
  have hpow_split : ε ^ (20 * u) = ε ^ (r + l) * ε ^ z := by
    rw [← pow_add]
    congr 1
    dsimp [z]
    omega
  have hpz : ε ^ z ≤ 1 / 21 := by
    calc
      ε ^ z ≤ ε ^ 4 := pow_le_pow_of_le_one hε.le hεone hz4
      _ ≤ (1 / 8 : ℝ) ^ 4 := pow_le_pow_left₀ hε.le hεsmall 4
      _ ≤ 1 / 21 := by norm_num
  have hCA : (C : ℝ) * A ≤ ε ^ z * U.card := by
    have hmul := mul_le_mul_of_nonneg_right hCscale (show 0 ≤ ε ^ z * U.card by positivity)
    dsimp [A]
    rw [hpow_split]
    nlinarith only [hmul]
  have hthreshold : (C : ℝ) * (q + 1 : ℕ) ≤ (U.card : ℝ) / 7 := by
    have hqmul := mul_le_mul_of_nonneg_left hqthree (Nat.cast_nonneg C)
    have hpzmul := mul_le_mul_of_nonneg_right hpz hN0
    nlinarith only [hCA, hqmul, hpzmul]
  have hFsize : B.card.choose r * ((t + l).choose t * (q + 1)) ≤ F.card := by
    have hR : ((C * (q + 1) : ℕ) : ℝ) ≤ (F.card : ℝ) := by
      simpa only [Nat.cast_mul] using hthreshold.trans hFlarge
    have hNat : C * (q + 1) ≤ F.card := by exact_mod_cast hR
    simpa only [C, Nat.mul_assoc] using hNat
  rcases hBcase with hBlarge | hmax
  · have hrt : r ≤ t := by
      apply Nat.ceil_le.mpr
      rw [hBlarge, Nat.cast_mul, Nat.cast_ofNat]
      have hmul := mul_nonneg (show 0 ≤ (1 / 8 : ℝ) - ε by linarith) ht0
      nlinarith only [hmul, ht0]
    have htr : t + r ≤ B.card := by omega
    have hmasksize : B.card.choose r * q ≤ F.card := by
      have hchoosepos : 1 ≤ (t + l).choose t := Nat.succ_le_of_lt (Nat.choose_pos (by omega))
      have hqbound : q ≤ (t + l).choose t * (q + 1) := by
        exact (Nat.le_succ q).trans (by
          simpa only [Nat.one_mul] using Nat.mul_le_mul_right (q + 1) hchoosepos)
      exact (Nat.mul_le_mul_left _ hqbound).trans hFsize
    obtain ⟨X, Y, hXB, hYF, hp, hXcard, hYcard⟩ :=
      exists_blue_monoPair_of_clique_masks H B F r t q hBc hFB hrB htr hm hmasksize
    refine ⟨X, Y, hXB.trans (hBT.trans hTU), hYF.trans hFU, Or.inr hp, hXcard, ?_⟩
    exact hqA.trans (Nat.cast_le.mpr hYcard)
  · obtain ⟨X, Y, hXF, hYF, hp, hXcard, hYcard⟩ :=
      exists_red_monoPair_of_maximum_complClique_masks H B T F r t l q
        hmax hFT hFB hrB hrl hm hFsize
    refine ⟨X, Y, hXF.trans hFU, hYF.trans hFU, Or.inl hp, hXcard, ?_⟩
    exact hqA.trans (Nat.cast_le.mpr hYcard)

/-- Choose the smallest permitted integer exponent parameter. -/
theorem exists_monoPair_of_low_density_ceil
    (H : SimpleGraph V) [DecidableRel H.Adj] (U : Finset V) (ε : ℝ) (t : ℕ)
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 8) (hεt : 1 ≤ ε * t)
    (hsize : (t : ℝ) ≤ ε ^ (20 * ⌈ε * t⌉₊) * U.card)
    (hdensity : (redDegreeSum H U : ℝ) ≤ ε * U.card ^ 2) :
    ∃ X Y : Finset V, X ⊆ U ∧ Y ⊆ U ∧
      (MonoPair H X Y ∨ MonoPair Hᶜ X Y) ∧ X.card = t ∧
      ε ^ (20 * ⌈ε * t⌉₊) * U.card ≤ (Y.card : ℝ) := by
  have hceil : ε * t ≤ (⌈ε * t⌉₊ : ℝ) := Nat.le_ceil _
  have hceil1 : 1 ≤ ⌈ε * t⌉₊ := by exact_mod_cast (hεt.trans hceil)
  exact exists_monoPair_of_low_density_integer_power H U ε t ⌈ε * t⌉₊
    hε hεsmall hεt hceil hceil1 hsize hdensity

/-- A fully uniform real-exponent form of Sudakov's low-density pair lemma.
The enlarged absolute constant absorbs both integer roundings. -/
theorem exists_monoPair_of_low_density
    (H : SimpleGraph V) [DecidableRel H.Adj] (U : Finset V) (ε : ℝ) (t : ℕ)
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 8) (hεt : 1 ≤ ε * t)
    (hsize : (t : ℝ) ≤ Real.rpow ε (40 * ε * t) * U.card)
    (hdensity : (redDegreeSum H U : ℝ) ≤ ε * U.card ^ 2) :
    ∃ X Y : Finset V, X ⊆ U ∧ Y ⊆ U ∧
      (MonoPair H X Y ∨ MonoPair Hᶜ X Y) ∧ X.card = t ∧
      Real.rpow ε (40 * ε * t) * U.card ≤ (Y.card : ℝ) := by
  have hceil : (⌈ε * t⌉₊ : ℝ) < ε * t + 1 := Nat.ceil_lt_add_one (by positivity)
  have hexp : ((20 * ⌈ε * t⌉₊ : ℕ) : ℝ) ≤ 40 * ε * t := by
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith only [hceil, hεt]
  have hpow : Real.rpow ε (40 * ε * t) ≤ ε ^ (20 * ⌈ε * t⌉₊) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hε (by linarith : ε ≤ 1) hexp
    simpa only [Real.rpow_eq_pow, Real.rpow_natCast] using h
  have hscaled := mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg U.card)
  obtain ⟨X, Y, hXU, hYU, hp, hXcard, hYcard⟩ :=
    exists_monoPair_of_low_density_ceil H U ε t hε hεsmall hεt
      (hsize.trans hscaled) hdensity
  exact ⟨X, Y, hXU, hYU, hp, hXcard, hscaled.trans hYcard⟩

/-- The normalized edge-density interface used by the sparse-subset lemma. -/
theorem exists_monoPair_of_low_edgeDensity
    (H : SimpleGraph V) [DecidableRel H.Adj] (U : Finset V) (ε : ℝ) (t : ℕ)
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 8) (hεt : 1 ≤ ε * t)
    (hsize : (t : ℝ) ≤ Real.rpow ε (40 * ε * t) * U.card)
    (hdensity : (H.edgeDensity U U : ℝ) ≤ ε) :
    ∃ X Y : Finset V, X ⊆ U ∧ Y ⊆ U ∧
      (MonoPair H X Y ∨ MonoPair Hᶜ X Y) ∧ X.card = t ∧
      Real.rpow ε (40 * ε * t) * U.card ≤ (Y.card : ℝ) := by
  exact exists_monoPair_of_low_density H U ε t hε hεsmall hεt hsize
    (redDegreeSum_le_of_edgeDensity_le H U ε hdensity)

#print axioms exists_monoPair_of_low_density_integer_power
#print axioms exists_monoPair_of_low_density_ceil
#print axioms exists_monoPair_of_low_density
#print axioms exists_monoPair_of_low_edgeDensity

end Erdos546
