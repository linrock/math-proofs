import ActualMajorArcBoundary433
import ActualMajorArcParityCRT433

/-!
# Completion of the signed denominator-dependent singular-integral tail

The actual Selberg/Hardy--Littlewood outside coefficients are signed and
absolutely summable, while the true symmetric Farey radius depends on the
ORIGINAL denominator.  Existing results bounded small-denominator tails and
the arithmetic large-denominator shell separately.  This module combines the
genuine analytic tail for *every* denominator with the sharp absolutely
summable shell; no signed center contribution or endpoint is discarded.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos689

/-- The complete genuine signed middle-tail at every original denominator
up to the sharp manuscript cutoff. Each summand keeps its own actual
denominator-dependent Farey radius. -/
noncomputable def actualMajorArcFullSignedFareyTail
    (excluded : ℕ) (lower : ℕ → ℕ)
    (a d n : ℕ) (τ ell : ℝ) : ℂ :=
  ∑ denominator ∈ Finset.Icc 1 (compatibleLogMinorCutoff n),
    ((actualMajorArcRestrictedSignedCoefficient
      excluded denominator : ℝ) : ℂ) *
      ∫ β in Set.Icc
          (actualMajorArcTailFareyRadius lower n denominator)
          (1 - actualMajorArcTailFareyRadius lower n denominator),
        actualMajorArcArchimedeanSmoothCubic a d n τ ell β

/-- The large actual-denominator tail starts STRICTLY above the small
`sqrt(P)` boundary and includes the true sharp endpoint `P`. -/
noncomputable def actualMajorArcLargeSignedFareyTail
    (excluded : ℕ) (lower : ℕ → ℕ)
    (a d n : ℕ) (τ ell : ℝ) : ℂ :=
  ∑ denominator ∈ Finset.Icc
      (compatibleLogBase n ^ 6 + 1) (compatibleLogMinorCutoff n),
    ((actualMajorArcRestrictedSignedCoefficient
      excluded denominator : ℝ) : ℂ) *
      ∫ β in Set.Icc
          (actualMajorArcTailFareyRadius lower n denominator)
          (1 - actualMajorArcTailFareyRadius lower n denominator),
        actualMajorArcArchimedeanSmoothCubic a d n τ ell β

/-- The exact large sharp-cutoff arithmetic shell tends to zero, including
the ORIGINAL endpoint `P`; the existing half-open shell alone omits it. -/
theorem actualMajorArcFullTail_large_sharp_coefficient_mass_tendsto_zero
    (excluded : ℕ) :
    Tendsto
      (fun n : ℕ =>
        ∑ denominator ∈ Finset.Icc
          (compatibleLogBase n ^ 6 + 1)
          (compatibleLogMinorCutoff n),
            ‖actualMajorArcRestrictedSignedCoefficient
              excluded denominator‖)
      atTop (nhds 0) := by
  have hsummable :=
    actualMajorArcRestrictedSignedCoefficient_norm_summable excluded
  have hsmallTop :
      Tendsto (fun n : ℕ => compatibleLogBase n ^ 6 + 1)
        atTop atTop :=
    (tendsto_add_atTop_nat 1).comp
      ((tendsto_pow_atTop (by norm_num : (6 : ℕ) ≠ 0)).comp
        compatibleLogBase_tendsto_atTop)
  have hlargeTop :
      Tendsto (fun n : ℕ => compatibleLogMinorCutoff n + 1)
        atTop atTop :=
    (tendsto_add_atTop_nat 1).comp compatibleLogMinorCutoff_tendsto_atTop
  have hupper := hsummable.hasSum.tendsto_sum_nat.comp hlargeTop
  have hlower := hsummable.hasSum.tendsto_sum_nat.comp hsmallTop
  have hdifference :
      Tendsto
        (fun n : ℕ =>
          (∑ denominator ∈ Finset.range
            (compatibleLogMinorCutoff n + 1),
              ‖actualMajorArcRestrictedSignedCoefficient
                excluded denominator‖) -
          (∑ denominator ∈ Finset.range
            (compatibleLogBase n ^ 6 + 1),
              ‖actualMajorArcRestrictedSignedCoefficient
                excluded denominator‖))
        atTop (nhds 0) := by
    simpa using hupper.sub hlower
  refine Filter.Tendsto.congr' ?_ hdifference
  filter_upwards
    [(tendsto_atTop.1 compatibleLogBase_tendsto_atTop 1)] with n hbase
  have hcutoff : compatibleLogBase n ^ 6 + 1 ≤
      compatibleLogMinorCutoff n + 1 := by
    apply Nat.add_le_add_right
    unfold compatibleLogMinorCutoff
    exact Nat.pow_le_pow_right hbase (by norm_num)
  have hsets :
      Finset.Icc (compatibleLogBase n ^ 6 + 1)
          (compatibleLogMinorCutoff n) =
        Finset.Ico (compatibleLogBase n ^ 6 + 1)
          (compatibleLogMinorCutoff n + 1) := by
    ext denominator
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hsets]
  exact (Finset.sum_Ico_eq_sub
    (fun denominator : ℕ =>
      ‖actualMajorArcRestrictedSignedCoefficient
        excluded denominator‖) hcutoff).symm

/-- Every ACTUAL large-denominator signed smooth tail is controlled by its
absolutely summable coefficient shell. The true denominator-specific
analytic bound is `q/P ≤ 1`, including the sharp endpoint `q = P`. -/
theorem actualMajorArcFullTail_large_signed_normalized_eventually
    (excluded : ℕ) (lower : ℕ → ℕ)
    (hendpoint : ∀ᶠ n : ℕ in atTop, lower n ≤ n)
    (a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (τ ell : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      ‖actualMajorArcLargeSignedFareyTail
        excluded lower a d n τ ell‖ / (n : ℝ) ^ 2 ≤
        ∑ denominator ∈ Finset.Icc
          (compatibleLogBase n ^ 6 + 1)
          (compatibleLogMinorCutoff n),
            ‖actualMajorArcRestrictedSignedCoefficient
              excluded denominator‖ := by
  filter_upwards
    [eventually_gt_atTop (0 : ℕ),
      (tendsto_atTop.1 compatibleLogBase_tendsto_atTop 1),
      actualMajorArcTail_log_cutoff_le_scale_eventually,
      hendpoint] with n hn hbase hscale hupper
  let F := Finset.Icc
    (compatibleLogBase n ^ 6 + 1) (compatibleLogMinorCutoff n)
  let term : ℕ → ℂ := fun denominator =>
    ((actualMajorArcRestrictedSignedCoefficient
      excluded denominator : ℝ) : ℂ) *
      ∫ β in Set.Icc
          (actualMajorArcTailFareyRadius lower n denominator)
          (1 - actualMajorArcTailFareyRadius lower n denominator),
        actualMajorArcArchimedeanSmoothCubic a d n τ ell β
  have hcutoff : 0 < compatibleLogMinorCutoff n := by
    unfold compatibleLogMinorCutoff
    positivity
  have hcutoffReal : (0 : ℝ) < compatibleLogMinorCutoff n := by
    exact_mod_cast hcutoff
  have hterm : ∀ denominator ∈ F,
      ‖term denominator‖ / (n : ℝ) ^ 2 ≤
        ‖actualMajorArcRestrictedSignedCoefficient
          excluded denominator‖ := by
    intro denominator hdenominator
    obtain ⟨hbottom, htop⟩ := Finset.mem_Icc.mp hdenominator
    have hpositive : 0 < denominator := by omega
    have htail := actualMajorArcTail_true_farey_normalized_le
      lower a d n denominator τ ell ha hd hn hpositive
        hcutoff hscale hupper
    have hratio :
        (denominator : ℝ) /
          (compatibleLogMinorCutoff n : ℝ) ≤ 1 := by
      apply (div_le_iff₀ hcutoffReal).mpr
      norm_num
      exact_mod_cast htop
    dsimp [term]
    rw [norm_mul, Complex.norm_real]
    calc
      ‖actualMajorArcRestrictedSignedCoefficient
          excluded denominator‖ *
          ‖∫ β in Set.Icc
              (actualMajorArcTailFareyRadius lower n denominator)
              (1 - actualMajorArcTailFareyRadius lower n denominator),
            actualMajorArcArchimedeanSmoothCubic
              a d n τ ell β‖ / (n : ℝ) ^ 2 =
        ‖actualMajorArcRestrictedSignedCoefficient
          excluded denominator‖ *
          (‖∫ β in Set.Icc
              (actualMajorArcTailFareyRadius lower n denominator)
              (1 - actualMajorArcTailFareyRadius lower n denominator),
            actualMajorArcArchimedeanSmoothCubic
              a d n τ ell β‖ / (n : ℝ) ^ 2) := by ring
      _ ≤ ‖actualMajorArcRestrictedSignedCoefficient
          excluded denominator‖ * 1 :=
        mul_le_mul_of_nonneg_left (htail.trans hratio) (norm_nonneg _)
      _ = _ := by simp
  change ‖∑ denominator ∈ F, term denominator‖ / (n : ℝ) ^ 2 ≤ _
  calc
    _ ≤ (∑ denominator ∈ F, ‖term denominator‖) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (norm_sum_le _ _) (by positivity)
    _ = ∑ denominator ∈ F,
        (‖term denominator‖ / (n : ℝ) ^ 2) := by
      rw [Finset.sum_div]
    _ ≤ ∑ denominator ∈ F,
        ‖actualMajorArcRestrictedSignedCoefficient
          excluded denominator‖ := Finset.sum_le_sum hterm

/-- The ENTIRE genuine large-denominator signed analytic tail is `o(n²)`,
not merely its arithmetic coefficient shell. Every original true width and
all actual affine resonances remain intact. -/
theorem actualMajorArcFullTail_large_signed_normalized_tendsto_zero
    (excluded : ℕ) (lower : ℕ → ℕ)
    (hendpoint : ∀ᶠ n : ℕ in atTop, lower n ≤ n)
    (a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (τ ell : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ‖actualMajorArcLargeSignedFareyTail
          excluded lower a d n τ ell‖ / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  exact squeeze_zero'
    (Eventually.of_forall fun n => by positivity)
    (actualMajorArcFullTail_large_signed_normalized_eventually
      excluded lower hendpoint a d ha hd τ ell)
    (actualMajorArcFullTail_large_sharp_coefficient_mass_tendsto_zero
      excluded)

/-- Exact signed splitting of the COMPLETE sharp-denominator tail into its
genuine small and large portions; neither the breakpoint nor the original
endpoint is duplicated or omitted. -/
theorem actualMajorArcFullSignedFareyTail_eq_small_add_large_eventually
    (excluded : ℕ) (lower : ℕ → ℕ)
    (a d : ℕ) (τ ell : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      actualMajorArcFullSignedFareyTail
          excluded lower a d n τ ell =
        actualMajorArcTailSmallSignedSum
            excluded lower a d n τ ell +
          actualMajorArcLargeSignedFareyTail
            excluded lower a d n τ ell := by
  filter_upwards
    [(tendsto_atTop.1 compatibleLogBase_tendsto_atTop 1)] with n hbase
  have hsmall : compatibleLogBase n ^ 6 ≤
      compatibleLogMinorCutoff n := by
    unfold compatibleLogMinorCutoff
    exact Nat.pow_le_pow_right hbase (by norm_num)
  have hsets :
      Finset.Icc 1 (compatibleLogMinorCutoff n) =
        (Finset.Icc 1 (compatibleLogBase n ^ 6)) ∪
          (Finset.Icc (compatibleLogBase n ^ 6 + 1)
            (compatibleLogMinorCutoff n)) := by
    ext denominator
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisjoint :
      Disjoint
        (Finset.Icc 1 (compatibleLogBase n ^ 6))
        (Finset.Icc (compatibleLogBase n ^ 6 + 1)
          (compatibleLogMinorCutoff n)) := by
    apply Finset.disjoint_left.mpr
    intro denominator hleft hright
    have hleft' := (Finset.mem_Icc.mp hleft).2
    have hright' := (Finset.mem_Icc.mp hright).1
    omega
  unfold actualMajorArcFullSignedFareyTail
    actualMajorArcTailSmallSignedSum actualMajorArcLargeSignedFareyTail
  rw [hsets, Finset.sum_union hdisjoint]

/-- The COMPLETE genuinely signed archimedean tail over EVERY original
outside denominator up to the sharp Farey cutoff is `o(n²)`. This combines
both analytic ranges; it does not merely bound a coefficient shell, discard
signed rational centers, or replace their individual widest radii. -/
theorem actualMajorArcFullSignedFareyTail_normalized_tendsto_zero
    (excluded : ℕ) (lower : ℕ → ℕ)
    (hendpoint : ∀ᶠ n : ℕ in atTop, lower n ≤ n)
    (a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (τ ell : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ‖actualMajorArcFullSignedFareyTail
          excluded lower a d n τ ell‖ / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  have hsmall := actualMajorArcTail_small_signed_normalized_tendsto_zero
    excluded lower hendpoint a d ha hd τ ell
  have hlarge := actualMajorArcFullTail_large_signed_normalized_tendsto_zero
    excluded lower hendpoint a d ha hd τ ell
  have hsum :
      Tendsto
        (fun n : ℕ =>
          ‖actualMajorArcTailSmallSignedSum
              excluded lower a d n τ ell‖ / (n : ℝ) ^ 2 +
            ‖actualMajorArcLargeSignedFareyTail
              excluded lower a d n τ ell‖ / (n : ℝ) ^ 2)
        atTop (nhds 0) := by
    simpa using hsmall.add hlarge
  refine squeeze_zero'
    (Eventually.of_forall fun n => by positivity) ?_ hsum
  filter_upwards
    [actualMajorArcFullSignedFareyTail_eq_small_add_large_eventually
      excluded lower a d τ ell] with n hsplit
  rw [hsplit]
  calc
    ‖actualMajorArcTailSmallSignedSum
        excluded lower a d n τ ell +
      actualMajorArcLargeSignedFareyTail
        excluded lower a d n τ ell‖ / (n : ℝ) ^ 2 ≤
      (‖actualMajorArcTailSmallSignedSum
          excluded lower a d n τ ell‖ +
        ‖actualMajorArcLargeSignedFareyTail
          excluded lower a d n τ ell‖) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (norm_add_le _ _) (by positivity)
    _ = _ := by ring

/-- The GENUINE doubled-parity conductor family.  Its signed coefficient is
indexed by the odd outside denominator `r`, but its actual arc radius is
that of `2*r`, and its cutoff is the honest `2*r ≤ P`. -/
noncomputable def actualMajorArcParitySignedFareyTail
    (excluded : ℕ) (lower : ℕ → ℕ)
    (a d n : ℕ) (τ ell : ℝ) : ℂ :=
  ∑ denominator ∈ Finset.Icc 1 (compatibleLogMinorCutoff n / 2),
    ((actualMajorArcRestrictedSignedCoefficient
      excluded denominator : ℝ) : ℂ) *
      ∫ β in Set.Icc
          (actualMajorArcTailFareyRadius lower n (2 * denominator))
          (1 - actualMajorArcTailFareyRadius lower n (2 * denominator)),
        actualMajorArcArchimedeanSmoothCubic a d n τ ell β

/-- Small outside denominators whose DOUBLED genuine conductor still lies
in the existing sharp `sqrt(P)` analytic range. -/
noncomputable def actualMajorArcParitySmallSignedFareyTail
    (excluded : ℕ) (lower : ℕ → ℕ)
    (a d n : ℕ) (τ ell : ℝ) : ℂ :=
  ∑ denominator ∈ Finset.Icc 1 (compatibleLogBase n ^ 6 / 2),
    ((actualMajorArcRestrictedSignedCoefficient
      excluded denominator : ℝ) : ℂ) *
      ∫ β in Set.Icc
          (actualMajorArcTailFareyRadius lower n (2 * denominator))
          (1 - actualMajorArcTailFareyRadius lower n (2 * denominator)),
        actualMajorArcArchimedeanSmoothCubic a d n τ ell β

/-- Large true parity companions, still respecting the exact original
denominator cutoff `2*r ≤ P`. -/
noncomputable def actualMajorArcParityLargeSignedFareyTail
    (excluded : ℕ) (lower : ℕ → ℕ)
    (a d n : ℕ) (τ ell : ℝ) : ℂ :=
  ∑ denominator ∈ Finset.Icc
      (compatibleLogBase n ^ 6 / 2 + 1)
      (compatibleLogMinorCutoff n / 2),
    ((actualMajorArcRestrictedSignedCoefficient
      excluded denominator : ℝ) : ℂ) *
      ∫ β in Set.Icc
          (actualMajorArcTailFareyRadius lower n (2 * denominator))
          (1 - actualMajorArcTailFareyRadius lower n (2 * denominator)),
        actualMajorArcArchimedeanSmoothCubic a d n τ ell β

/-- The exact coefficient shell for genuine doubled parity conductors
tends to zero; BOTH its lower and upper sharp cutoffs are halved. -/
theorem actualMajorArcParityTail_large_coefficient_mass_tendsto_zero
    (excluded : ℕ) :
    Tendsto
      (fun n : ℕ =>
        ∑ denominator ∈ Finset.Icc
          (compatibleLogBase n ^ 6 / 2 + 1)
          (compatibleLogMinorCutoff n / 2),
            ‖actualMajorArcRestrictedSignedCoefficient
              excluded denominator‖)
      atTop (nhds 0) := by
  have hsummable :=
    actualMajorArcRestrictedSignedCoefficient_norm_summable excluded
  have hbasePow : Tendsto (fun n : ℕ => compatibleLogBase n ^ 6)
      atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (6 : ℕ) ≠ 0)).comp
      compatibleLogBase_tendsto_atTop
  have hsmallTop :
      Tendsto (fun n : ℕ => compatibleLogBase n ^ 6 / 2 + 1)
        atTop atTop :=
    (tendsto_add_atTop_nat 1).comp
      (actualMajorArcParity_half_cutoff_tendsto_atTop.comp hbasePow)
  have hlargeTop :
      Tendsto (fun n : ℕ => compatibleLogMinorCutoff n / 2 + 1)
        atTop atTop :=
    (tendsto_add_atTop_nat 1).comp
      (actualMajorArcParity_half_cutoff_tendsto_atTop.comp
        compatibleLogMinorCutoff_tendsto_atTop)
  have hupper := hsummable.hasSum.tendsto_sum_nat.comp hlargeTop
  have hlower := hsummable.hasSum.tendsto_sum_nat.comp hsmallTop
  have hdifference :
      Tendsto
        (fun n : ℕ =>
          (∑ denominator ∈ Finset.range
            (compatibleLogMinorCutoff n / 2 + 1),
              ‖actualMajorArcRestrictedSignedCoefficient
                excluded denominator‖) -
          (∑ denominator ∈ Finset.range
            (compatibleLogBase n ^ 6 / 2 + 1),
              ‖actualMajorArcRestrictedSignedCoefficient
                excluded denominator‖))
        atTop (nhds 0) := by
    simpa using hupper.sub hlower
  refine Filter.Tendsto.congr' ?_ hdifference
  filter_upwards
    [(tendsto_atTop.1 compatibleLogBase_tendsto_atTop 1)] with n hbase
  have hpower : compatibleLogBase n ^ 6 ≤
      compatibleLogMinorCutoff n := by
    unfold compatibleLogMinorCutoff
    exact Nat.pow_le_pow_right hbase (by norm_num)
  have hcutoff : compatibleLogBase n ^ 6 / 2 + 1 ≤
      compatibleLogMinorCutoff n / 2 + 1 := by
    exact Nat.add_le_add_right (Nat.div_le_div_right hpower) 1
  have hsets :
      Finset.Icc (compatibleLogBase n ^ 6 / 2 + 1)
          (compatibleLogMinorCutoff n / 2) =
        Finset.Ico (compatibleLogBase n ^ 6 / 2 + 1)
          (compatibleLogMinorCutoff n / 2 + 1) := by
    ext denominator
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hsets]
  exact (Finset.sum_Ico_eq_sub
    (fun denominator : ℕ =>
      ‖actualMajorArcRestrictedSignedCoefficient
        excluded denominator‖) hcutoff).symm

/-- All genuine SMALL doubled-parity conductors obey the same vanishing
analytic rate as ordinary small denominators, with their ACTUAL radius
`1/(2*r*(Q+1))` retained. -/
theorem actualMajorArcParityTail_small_signed_normalized_eventually
    (excluded : ℕ) (lower : ℕ → ℕ)
    (hendpoint : ∀ᶠ n : ℕ in atTop, lower n ≤ n)
    (a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (τ ell : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      ‖actualMajorArcParitySmallSignedFareyTail
        excluded lower a d n τ ell‖ / (n : ℝ) ^ 2 ≤
        (1 / (compatibleLogBase n : ℝ) ^ 6) *
          ∑' denominator : ℕ,
            ‖actualMajorArcRestrictedSignedCoefficient
              excluded denominator‖ := by
  have hsummable :=
    actualMajorArcRestrictedSignedCoefficient_norm_summable excluded
  filter_upwards
    [actualMajorArcTail_small_denominator_normalized_eventually
      lower hendpoint a d ha hd τ ell] with n hsmall
  let F := Finset.Icc 1 (compatibleLogBase n ^ 6 / 2)
  let rate : ℝ := 1 / (compatibleLogBase n : ℝ) ^ 6
  let term : ℕ → ℂ := fun denominator =>
    ((actualMajorArcRestrictedSignedCoefficient
      excluded denominator : ℝ) : ℂ) *
      ∫ β in Set.Icc
          (actualMajorArcTailFareyRadius lower n (2 * denominator))
          (1 - actualMajorArcTailFareyRadius lower n (2 * denominator)),
        actualMajorArcArchimedeanSmoothCubic a d n τ ell β
  have hterm : ∀ denominator ∈ F,
      ‖term denominator‖ / (n : ℝ) ^ 2 ≤
        rate * ‖actualMajorArcRestrictedSignedCoefficient
          excluded denominator‖ := by
    intro denominator hdenominator
    obtain ⟨hpositive, hhalf⟩ := Finset.mem_Icc.mp hdenominator
    have hdouble : 2 * denominator ≤ compatibleLogBase n ^ 6 := by
      have h :=
        (Nat.le_div_iff_mul_le (by norm_num : 0 < (2 : ℕ))).mp hhalf
      omega
    have htail := hsmall (2 * denominator) (by omega) hdouble
    dsimp [term, rate]
    rw [norm_mul, Complex.norm_real]
    calc
      ‖actualMajorArcRestrictedSignedCoefficient
          excluded denominator‖ *
          ‖∫ β in Set.Icc
              (actualMajorArcTailFareyRadius
                lower n (2 * denominator))
              (1 - actualMajorArcTailFareyRadius
                lower n (2 * denominator)),
            actualMajorArcArchimedeanSmoothCubic
              a d n τ ell β‖ / (n : ℝ) ^ 2 =
        ‖actualMajorArcRestrictedSignedCoefficient
          excluded denominator‖ *
          (‖∫ β in Set.Icc
              (actualMajorArcTailFareyRadius
                lower n (2 * denominator))
              (1 - actualMajorArcTailFareyRadius
                lower n (2 * denominator)),
            actualMajorArcArchimedeanSmoothCubic
              a d n τ ell β‖ / (n : ℝ) ^ 2) := by ring
      _ ≤ ‖actualMajorArcRestrictedSignedCoefficient
          excluded denominator‖ *
            (1 / (compatibleLogBase n : ℝ) ^ 6) :=
        mul_le_mul_of_nonneg_left htail (norm_nonneg _)
      _ = _ := by
        rw [Real.norm_eq_abs]
        ring
  have hmass :
      (∑ denominator ∈ F,
        ‖actualMajorArcRestrictedSignedCoefficient
          excluded denominator‖) ≤
        ∑' denominator : ℕ,
          ‖actualMajorArcRestrictedSignedCoefficient
            excluded denominator‖ :=
    hsummable.sum_le_tsum F (fun _ _ => norm_nonneg _)
  change ‖∑ denominator ∈ F, term denominator‖ / (n : ℝ) ^ 2 ≤
    rate * _
  calc
    _ ≤ (∑ denominator ∈ F, ‖term denominator‖) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (norm_sum_le _ _) (by positivity)
    _ = ∑ denominator ∈ F,
        (‖term denominator‖ / (n : ℝ) ^ 2) := by
      rw [Finset.sum_div]
    _ ≤ ∑ denominator ∈ F,
        rate * ‖actualMajorArcRestrictedSignedCoefficient
          excluded denominator‖ := Finset.sum_le_sum hterm
    _ = rate * ∑ denominator ∈ F,
        ‖actualMajorArcRestrictedSignedCoefficient
          excluded denominator‖ := by
      rw [Finset.mul_sum]
    _ ≤ rate * ∑' denominator : ℕ,
        ‖actualMajorArcRestrictedSignedCoefficient
          excluded denominator‖ :=
      mul_le_mul_of_nonneg_left hmass (by dsimp [rate]; positivity)

/-- The entire actual small doubled-parity smooth tail is `o(n²)`. -/
theorem actualMajorArcParityTail_small_signed_normalized_tendsto_zero
    (excluded : ℕ) (lower : ℕ → ℕ)
    (hendpoint : ∀ᶠ n : ℕ in atTop, lower n ≤ n)
    (a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (τ ell : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ‖actualMajorArcParitySmallSignedFareyTail
          excluded lower a d n τ ell‖ / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  have hmajor :
      Tendsto
        (fun n : ℕ =>
          (1 / (compatibleLogBase n : ℝ) ^ 6) *
            ∑' denominator : ℕ,
              ‖actualMajorArcRestrictedSignedCoefficient
                excluded denominator‖)
        atTop (nhds 0) := by
    simpa using
      actualMajorArcTail_small_denominator_rate_tendsto_zero.mul_const
        (∑' denominator : ℕ,
          ‖actualMajorArcRestrictedSignedCoefficient
            excluded denominator‖)
  exact squeeze_zero'
    (Eventually.of_forall fun n => by positivity)
    (actualMajorArcParityTail_small_signed_normalized_eventually
      excluded lower hendpoint a d ha hd τ ell)
    hmajor

/-- Every LARGE parity companion has its true original radius indexed by
`2*r`; because `2*r ≤ P`, its normalized signed tail is bounded by its
outside coefficient, with no parity-width substitution. -/
theorem actualMajorArcParityTail_large_signed_normalized_eventually
    (excluded : ℕ) (lower : ℕ → ℕ)
    (hendpoint : ∀ᶠ n : ℕ in atTop, lower n ≤ n)
    (a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (τ ell : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      ‖actualMajorArcParityLargeSignedFareyTail
        excluded lower a d n τ ell‖ / (n : ℝ) ^ 2 ≤
        ∑ denominator ∈ Finset.Icc
          (compatibleLogBase n ^ 6 / 2 + 1)
          (compatibleLogMinorCutoff n / 2),
            ‖actualMajorArcRestrictedSignedCoefficient
              excluded denominator‖ := by
  filter_upwards
    [eventually_gt_atTop (0 : ℕ),
      (tendsto_atTop.1 compatibleLogBase_tendsto_atTop 1),
      actualMajorArcTail_log_cutoff_le_scale_eventually,
      hendpoint] with n hn hbase hscale hupper
  let F := Finset.Icc
    (compatibleLogBase n ^ 6 / 2 + 1)
    (compatibleLogMinorCutoff n / 2)
  let term : ℕ → ℂ := fun denominator =>
    ((actualMajorArcRestrictedSignedCoefficient
      excluded denominator : ℝ) : ℂ) *
      ∫ β in Set.Icc
          (actualMajorArcTailFareyRadius lower n (2 * denominator))
          (1 - actualMajorArcTailFareyRadius lower n (2 * denominator)),
        actualMajorArcArchimedeanSmoothCubic a d n τ ell β
  have hcutoff : 0 < compatibleLogMinorCutoff n := by
    unfold compatibleLogMinorCutoff
    positivity
  have hcutoffReal : (0 : ℝ) < compatibleLogMinorCutoff n := by
    exact_mod_cast hcutoff
  have hterm : ∀ denominator ∈ F,
      ‖term denominator‖ / (n : ℝ) ^ 2 ≤
        ‖actualMajorArcRestrictedSignedCoefficient
          excluded denominator‖ := by
    intro denominator hdenominator
    obtain ⟨hbottom, htop⟩ := Finset.mem_Icc.mp hdenominator
    have hpositive : 0 < denominator := by omega
    have hdouble : 2 * denominator ≤ compatibleLogMinorCutoff n := by
      have h :=
        (Nat.le_div_iff_mul_le (by norm_num : 0 < (2 : ℕ))).mp htop
      omega
    have htail := actualMajorArcTail_true_farey_normalized_le
      lower a d n (2 * denominator) τ ell ha hd hn (by omega)
        hcutoff hscale hupper
    have hratio :
        ((2 * denominator : ℕ) : ℝ) /
          (compatibleLogMinorCutoff n : ℝ) ≤ 1 := by
      apply (div_le_iff₀ hcutoffReal).mpr
      norm_num
      exact_mod_cast hdouble
    dsimp [term]
    rw [norm_mul, Complex.norm_real]
    calc
      ‖actualMajorArcRestrictedSignedCoefficient
          excluded denominator‖ *
          ‖∫ β in Set.Icc
              (actualMajorArcTailFareyRadius
                lower n (2 * denominator))
              (1 - actualMajorArcTailFareyRadius
                lower n (2 * denominator)),
            actualMajorArcArchimedeanSmoothCubic
              a d n τ ell β‖ / (n : ℝ) ^ 2 =
        ‖actualMajorArcRestrictedSignedCoefficient
          excluded denominator‖ *
          (‖∫ β in Set.Icc
              (actualMajorArcTailFareyRadius
                lower n (2 * denominator))
              (1 - actualMajorArcTailFareyRadius
                lower n (2 * denominator)),
            actualMajorArcArchimedeanSmoothCubic
              a d n τ ell β‖ / (n : ℝ) ^ 2) := by ring
      _ ≤ ‖actualMajorArcRestrictedSignedCoefficient
          excluded denominator‖ * 1 :=
        mul_le_mul_of_nonneg_left (htail.trans hratio) (norm_nonneg _)
      _ = _ := by simp
  change ‖∑ denominator ∈ F, term denominator‖ / (n : ℝ) ^ 2 ≤ _
  calc
    _ ≤ (∑ denominator ∈ F, ‖term denominator‖) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (norm_sum_le _ _) (by positivity)
    _ = ∑ denominator ∈ F,
        (‖term denominator‖ / (n : ℝ) ^ 2) := by
      rw [Finset.sum_div]
    _ ≤ ∑ denominator ∈ F,
        ‖actualMajorArcRestrictedSignedCoefficient
          excluded denominator‖ := Finset.sum_le_sum hterm

/-- The ENTIRE actual large-parity-conductor signed smooth tail is `o(n²)`,
with every actual doubled width and signed coefficient preserved. -/
theorem actualMajorArcParityTail_large_signed_normalized_tendsto_zero
    (excluded : ℕ) (lower : ℕ → ℕ)
    (hendpoint : ∀ᶠ n : ℕ in atTop, lower n ≤ n)
    (a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (τ ell : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ‖actualMajorArcParityLargeSignedFareyTail
          excluded lower a d n τ ell‖ / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  exact squeeze_zero'
    (Eventually.of_forall fun n => by positivity)
    (actualMajorArcParityTail_large_signed_normalized_eventually
      excluded lower hendpoint a d ha hd τ ell)
    (actualMajorArcParityTail_large_coefficient_mass_tendsto_zero
      excluded)

/-- Exact signed decomposition of the genuine doubled-parity family at
the halved small-denominator breakpoint, retaining its exact upper cutoff. -/
theorem actualMajorArcParitySignedFareyTail_eq_small_add_large_eventually
    (excluded : ℕ) (lower : ℕ → ℕ)
    (a d : ℕ) (τ ell : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      actualMajorArcParitySignedFareyTail
          excluded lower a d n τ ell =
        actualMajorArcParitySmallSignedFareyTail
            excluded lower a d n τ ell +
          actualMajorArcParityLargeSignedFareyTail
            excluded lower a d n τ ell := by
  filter_upwards
    [(tendsto_atTop.1 compatibleLogBase_tendsto_atTop 1)] with n hbase
  have hpower : compatibleLogBase n ^ 6 ≤
      compatibleLogMinorCutoff n := by
    unfold compatibleLogMinorCutoff
    exact Nat.pow_le_pow_right hbase (by norm_num)
  have hsmall : compatibleLogBase n ^ 6 / 2 ≤
      compatibleLogMinorCutoff n / 2 := Nat.div_le_div_right hpower
  have hsets :
      Finset.Icc 1 (compatibleLogMinorCutoff n / 2) =
        (Finset.Icc 1 (compatibleLogBase n ^ 6 / 2)) ∪
          (Finset.Icc (compatibleLogBase n ^ 6 / 2 + 1)
            (compatibleLogMinorCutoff n / 2)) := by
    ext denominator
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisjoint :
      Disjoint
        (Finset.Icc 1 (compatibleLogBase n ^ 6 / 2))
        (Finset.Icc (compatibleLogBase n ^ 6 / 2 + 1)
          (compatibleLogMinorCutoff n / 2)) := by
    apply Finset.disjoint_left.mpr
    intro denominator hleft hright
    have hleft' := (Finset.mem_Icc.mp hleft).2
    have hright' := (Finset.mem_Icc.mp hright).1
    omega
  unfold actualMajorArcParitySignedFareyTail
    actualMajorArcParitySmallSignedFareyTail
    actualMajorArcParityLargeSignedFareyTail
  rw [hsets, Finset.sum_union hdisjoint]

/-- The COMPLETE signed archimedean parity-companion tail is `o(n²)` using
the GENUINE original conductors `2*r`, their narrower widths, and their
different sharp cutoff `r≤P/2`. -/
theorem actualMajorArcParitySignedFareyTail_normalized_tendsto_zero
    (excluded : ℕ) (lower : ℕ → ℕ)
    (hendpoint : ∀ᶠ n : ℕ in atTop, lower n ≤ n)
    (a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (τ ell : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ‖actualMajorArcParitySignedFareyTail
          excluded lower a d n τ ell‖ / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  have hsmall :=
    actualMajorArcParityTail_small_signed_normalized_tendsto_zero
      excluded lower hendpoint a d ha hd τ ell
  have hlarge :=
    actualMajorArcParityTail_large_signed_normalized_tendsto_zero
      excluded lower hendpoint a d ha hd τ ell
  have hsum :
      Tendsto
        (fun n : ℕ =>
          ‖actualMajorArcParitySmallSignedFareyTail
              excluded lower a d n τ ell‖ / (n : ℝ) ^ 2 +
            ‖actualMajorArcParityLargeSignedFareyTail
              excluded lower a d n τ ell‖ / (n : ℝ) ^ 2)
        atTop (nhds 0) := by
    simpa using hsmall.add hlarge
  refine squeeze_zero'
    (Eventually.of_forall fun n => by positivity) ?_ hsum
  filter_upwards
    [actualMajorArcParitySignedFareyTail_eq_small_add_large_eventually
      excluded lower a d τ ell] with n hsplit
  rw [hsplit]
  calc
    ‖actualMajorArcParitySmallSignedFareyTail
        excluded lower a d n τ ell +
      actualMajorArcParityLargeSignedFareyTail
        excluded lower a d n τ ell‖ / (n : ℝ) ^ 2 ≤
      (‖actualMajorArcParitySmallSignedFareyTail
          excluded lower a d n τ ell‖ +
        ‖actualMajorArcParityLargeSignedFareyTail
          excluded lower a d n τ ell‖) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (norm_add_le _ _) (by positivity)
    _ = _ := by ring

#print axioms Erdos689.actualMajorArcFullTail_large_sharp_coefficient_mass_tendsto_zero
#print axioms Erdos689.actualMajorArcFullTail_large_signed_normalized_eventually
#print axioms Erdos689.actualMajorArcFullTail_large_signed_normalized_tendsto_zero
#print axioms Erdos689.actualMajorArcFullSignedFareyTail_eq_small_add_large_eventually
#print axioms Erdos689.actualMajorArcFullSignedFareyTail_normalized_tendsto_zero
#print axioms Erdos689.actualMajorArcParityTail_large_coefficient_mass_tendsto_zero
#print axioms Erdos689.actualMajorArcParityTail_small_signed_normalized_eventually
#print axioms Erdos689.actualMajorArcParityTail_small_signed_normalized_tendsto_zero
#print axioms Erdos689.actualMajorArcParityTail_large_signed_normalized_eventually
#print axioms Erdos689.actualMajorArcParityTail_large_signed_normalized_tendsto_zero
#print axioms Erdos689.actualMajorArcParitySignedFareyTail_eq_small_add_large_eventually
#print axioms Erdos689.actualMajorArcParitySignedFareyTail_normalized_tendsto_zero

end Erdos689
