module

public import StrictGapIntervals1139

@[expose] public section


/-!
# A uniform strict improvement for maximal almost-prime gaps

The genuine positive conductor saving extracted from the local Erdős #689 proof
produces an interval at every sufficiently large prescribed length.  Choosing
that length just above a fixed multiple of `log X` places a whole almost-prime-
free interval below EVERY sufficiently large height `X`.

This is stronger than a subsequential strict lower bound on the normalized
gaps.  It still does not establish the original infinite-limsup conjecture:
the certified improvement coefficient is fixed.
-/

open Finset Filter
open scoped ArithmeticFunction.Omega Topology

namespace Erdos1139

/-- At every sufficiently large height, there is a literal interval below that
    height containing no integer with at most two prime factors, whose length
    is at least `c * log X` for one unconditional constant `c > 1`.

    The interval has the exact historical multiplicity convention `Ω`. -/
theorem uniform_maximal_almost_prime_gap_strictly_exceeds_logarithm :
    ∃ c : ℝ, 1 < c ∧
      ∀ᶠ X : ℕ in atTop,
        ∃ N y : ℕ,
          0 < N ∧ N + y ≤ X ∧
          c * Real.log (X : ℝ) ≤ (y : ℝ) ∧
          ∀ h ∈ Finset.Icc 1 y, 3 ≤ Ω (N + h) := by
  obtain ⟨η, hη, hηone, hintervals⟩ :=
    eventual_three_factor_intervals_at_strictly_subprimorial_location
  obtain ⟨Y, hY⟩ := eventually_atTop.mp hintervals
  let c : ℝ := 1 + η / 4
  let d : ℝ := 1 + η / 2
  let α : ℝ := (1 - η) * d
  have hc : 1 < c := by dsimp [c]; linarith
  have hd : 0 < d := by dsimp [d]; linarith
  have hdifference : 0 < d - c := by dsimp [d, c]; linarith
  have halpha : α < 1 := by
    dsimp [α, d]
    nlinarith [sq_nonneg η]
  have hlogtop : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlength := (tendsto_atTop.1 hlogtop) ((Y : ℝ) / d)
  have hfloor := (tendsto_atTop.1 hlogtop) (1 / (d - c))
  have hlocation := (tendsto_atTop.1 hlogtop)
    (Real.log (2 : ℝ) / (1 - α))
  have hscale := Erdos689.eventually_logarithmic_scale_dominates_one
    (1 / (2 * d)) (by positivity) 1
  refine ⟨c, hc, ?_⟩
  filter_upwards [hlength, hfloor, hlocation, hscale,
      eventually_ge_atTop 2] with X hlengthX hfloorX hlocationX hscaleX hX
  have hXpositive : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hXlarge : (1 : ℝ) < X := by exact_mod_cast (by omega : 1 < X)
  have hlogpositive : 0 < Real.log (X : ℝ) := Real.log_pos hXlarge
  let y : ℕ := ⌊d * Real.log (X : ℝ)⌋₊
  have hthreshold : (Y : ℝ) ≤ d * Real.log (X : ℝ) := by
    have h := (div_le_iff₀ hd).mp hlengthX
    nlinarith
  have hylarge : Y ≤ y := Nat.le_floor hthreshold
  obtain ⟨N, hN, hthree, hlogN⟩ := hY y hylarge
  have hyupper : (y : ℝ) ≤ d * Real.log (X : ℝ) :=
    Nat.floor_le (mul_nonneg hd.le hlogpositive.le)
  have hyfloor := Nat.lt_floor_add_one (d * Real.log (X : ℝ))
  have hmargin : (1 : ℝ) ≤ (d - c) * Real.log (X : ℝ) := by
    have h := (div_le_iff₀ hdifference).mp hfloorX
    nlinarith
  have hylower : c * Real.log (X : ℝ) ≤ (y : ℝ) := by
    change d * Real.log (X : ℝ) < (y : ℝ) + 1 at hyfloor
    nlinarith
  have hNpositive : 0 < (N : ℝ) := by exact_mod_cast hN
  have hlogNbound : Real.log (N : ℝ) ≤ α * Real.log (X : ℝ) := by
    have hηnonnegative : 0 ≤ 1 - η := by linarith
    calc
      Real.log (N : ℝ) ≤ (1 - η) * (y : ℝ) := hlogN
      _ ≤ (1 - η) * (d * Real.log (X : ℝ)) :=
        mul_le_mul_of_nonneg_left hyupper hηnonnegative
      _ = α * Real.log (X : ℝ) := by dsimp [α]; ring
  have hlogtwo : Real.log (2 : ℝ) ≤ (1 - α) * Real.log (X : ℝ) := by
    have h := (div_le_iff₀ (by linarith : 0 < 1 - α)).mp hlocationX
    nlinarith
  have hdoublelog :
      Real.log (2 : ℝ) + Real.log (N : ℝ) ≤ Real.log (X : ℝ) := by
    nlinarith
  have hdouble := (Real.exp_le_exp).mpr hdoublelog
  rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2),
    Real.exp_log hNpositive, Real.exp_log hXpositive] at hdouble
  have hscale_rewritten :
      (1 : ℝ) ≤ (1 / (2 * d)) *
        ((X : ℝ) / Real.log (X : ℝ)) := by
    simpa using hscaleX
  have hloghalf : Real.log (X : ℝ) ≤ (X : ℝ) / (2 * d) := by
    calc
      Real.log (X : ℝ) = 1 * Real.log (X : ℝ) := by ring
      _ ≤ ((1 / (2 * d)) * ((X : ℝ) / Real.log (X : ℝ))) *
          Real.log (X : ℝ) :=
        mul_le_mul_of_nonneg_right hscale_rewritten hlogpositive.le
      _ = (X : ℝ) / (2 * d) := by
        field_simp [hlogpositive.ne', hd.ne']
  have hyhalf : (y : ℝ) ≤ (X : ℝ) / 2 := by
    calc
      (y : ℝ) ≤ d * Real.log (X : ℝ) := hyupper
      _ ≤ d * ((X : ℝ) / (2 * d)) :=
        mul_le_mul_of_nonneg_left hloghalf hd.le
      _ = (X : ℝ) / 2 := by field_simp [hd.ne']
  have hsumreal : (N : ℝ) + (y : ℝ) ≤ (X : ℝ) := by linarith
  have hsum : N + y ≤ X := by exact_mod_cast hsumreal
  exact ⟨N, y, hN, hsum, hylower, hthree⟩


end Erdos1139
