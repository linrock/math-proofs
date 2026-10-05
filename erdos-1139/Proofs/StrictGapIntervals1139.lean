module

public import ExpandedCoverConstruction1139

@[expose] public section


/-!
# Uniform genuinely subprimorial almost-prime-free intervals

The strict matching-reserve surplus in the completed local Erdős #689 proof
does more than create a subsequence of unusually large normalized gaps.
For EVERY sufficiently large prescribed interval length `y`, it supplies an
actual integer `N` such that all `N+1,...,N+y` have at least three prime
factors and `log N ≤ (1-η)y` for one fixed `η > 0`.

Thus the strict improvement over coefficient one is uniform in the requested
gap length.  The original #1139 infinite-limsup conjecture remains unproved:
the certified saving `η` is fixed, rather than approaching one.
-/

open Finset Filter
open scoped ArithmeticFunction.Omega Topology

namespace Erdos1139

/-- UNCONDITIONAL genuine three-factor intervals at every sufficiently large
    length, with one strictly subunit logarithmic location coefficient.  The
    interval is literal `[N+1,N+y]`, multiplicities use the historical `Ω`,
    and the CRT representative is an actual positive natural number. -/
theorem eventual_three_factor_intervals_at_strictly_subprimorial_location :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧
      ∀ᶠ y : ℕ in atTop,
        ∃ N : ℕ,
          0 < N ∧
          (∀ h ∈ Finset.Icc 1 y, 3 ≤ Ω (N + h)) ∧
          Real.log (N : ℝ) ≤ (1 - η) * (y : ℝ) := by
  obtain ⟨r, hr, hcovers⟩ :=
    eventual_original_covers_with_strictly_improved_conductor
  let t : ℝ := max r (1 / 2)
  have htpositive : 0 < t :=
    lt_of_lt_of_le (by norm_num) (le_max_right r (1 / 2))
  have htone : t < 1 := max_lt hr (by norm_num)
  have hrt : r ≤ t := le_max_left r (1 / 2)
  let η : ℝ := (1 - t) / 2
  have hηpositive : 0 < η := by dsimp [η]; linarith
  have hηone : η < 1 := by dsimp [η]; linarith
  obtain ⟨B, hB⟩ := exists_nat_ge (Real.log (2 : ℝ) / η)
  refine ⟨η, hηpositive, hηone, ?_⟩
  filter_upwards [hcovers, eventually_ge_atTop B] with y witness hyB
  obtain ⟨P, squared, residue, hcover, hcost⟩ := witness
  obtain ⟨N, hNlower, hNupper, hthree⟩ :=
    unrestricted_square_double_cover_forces_three_factor_interval hcover
  let Q : ℕ := ∏ p ∈ P, selectedPrimePower squared p
  have hQnat : 0 < Q := by
    dsimp [Q]
    exact Finset.prod_pos (fun p hp => pow_pos (hcover.1 p hp).pos _)
  have hNpositive : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hNlower
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNpositive
  have hQreal : 0 < (Q : ℝ) := by exact_mod_cast hQnat
  have htwopositive : 0 < (2 : ℝ) * (Q : ℝ) := by positivity
  have hboundreal : (N : ℝ) ≤ (2 : ℝ) * (Q : ℝ) := by
    exact_mod_cast hNupper
  have hlog := Real.strictMonoOn_log.monotoneOn
    hNreal htwopositive hboundreal
  rw [Real.log_mul (by norm_num) hQreal.ne'] at hlog
  have hyreal : (B : ℝ) ≤ (y : ℝ) := by exact_mod_cast hyB
  have hfixed : Real.log (2 : ℝ) ≤ η * (y : ℝ) := by
    have hquotient : Real.log (2 : ℝ) / η ≤ (y : ℝ) := hB.trans hyreal
    have hscaled := (div_le_iff₀ hηpositive).mp hquotient
    nlinarith
  change Real.log (Q : ℝ) ≤ r * (y : ℝ) at hcost
  have hvariable : Real.log (Q : ℝ) ≤ t * (y : ℝ) :=
    hcost.trans (mul_le_mul_of_nonneg_right hrt (Nat.cast_nonneg y))
  refine ⟨N, hNpositive, hthree, ?_⟩
  have hcoefficient : η + t = 1 - η := by
    dsimp [η]
    ring
  nlinarith


end Erdos1139
