module

public import ActualLeftVertexMajorCubicModel433
public import ActualMajorArcPositivityError433

@[expose] public section


/-!
# Full actual shifted-center approximation without discarding signed cells

The original prime-only cubic is partitioned into ALL `lcm(q,W)^3` true
residue triples. Its compatible support-switched unit triples receive the
fully rated three-factor interval model; EVERY other actual triple remains
as its exact signed prime cubic. The accumulated approximation error is the
sum of the actual per-cell errors. The proper-prime-power component becomes
negligible only after the indispensable major-arc width `1/n` is restored.
No conductor cancellation, incompatible-cell deletion, or global positivity
is assumed.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos689

/-- Every genuine common-modulus triple, including nonunit and incompatible
support cells. -/
def actualMajorArcLcmAllCellTriples
    (S : Finset ℕ) (denominator : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (actualMajorArcLcmResidueModulus S denominator)).product
    ((Finset.range (actualMajorArcLcmResidueModulus S denominator)).product
      (Finset.range (actualMajorArcLcmResidueModulus S denominator)))

/-- Precisely those actual triple cells for which all three prime
progressions are units, the robust label projects to its target, and both
ORIGINAL switched masks vanish. -/
def actualMajorArcLcmAdmissibleCell
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d denominator : ℕ) (triple : ℕ × ℕ × ℕ) : Prop :=
  triple.1 % (∏ p ∈ S, p) = target ∧
    Nat.Coprime triple.1 (actualMajorArcLcmResidueModulus S denominator) ∧
    Nat.Coprime triple.2.1 (actualMajorArcLcmResidueModulus S denominator) ∧
    Nat.Coprime triple.2.2 (actualMajorArcLcmResidueModulus S denominator) ∧
    switchedHits S b (2 * (a * triple.2.1)) = 0 ∧
    switchedHits S b (2 * (2 * d * triple.2.2)) = 0

/-- Actual compatible switched-unit triples to which the full cell model
applies. -/
noncomputable def actualMajorArcLcmAdmissibleCellTriples
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d denominator : ℕ) : Finset (ℕ × ℕ × ℕ) := by
  classical
  exact (actualMajorArcLcmAllCellTriples S denominator).filter
    (actualMajorArcLcmAdmissibleCell S b target a d denominator)

/-- ALL remaining signed cells, kept as their exact actual prime cubics. -/
noncomputable def actualMajorArcLcmExceptionalCellTriples
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d denominator : ℕ) : Finset (ℕ × ℕ × ℕ) := by
  classical
  exact (actualMajorArcLcmAllCellTriples S denominator).filter
    (fun triple =>
      ¬ actualMajorArcLcmAdmissibleCell S b target a d denominator triple)

/-- The exact full triple-cell inventory is the common modulus cubed. -/
theorem actualMajorArcLcmAllCellTriples_card
    (S : Finset ℕ) (denominator : ℕ) :
    (actualMajorArcLcmAllCellTriples S denominator).card =
      (actualMajorArcLcmResidueModulus S denominator) ^ 3 := by
  simp [actualMajorArcLcmAllCellTriples, pow_succ, mul_assoc]

/-- The genuine modeled triple family never exceeds the independently
audited `(W*P)^3` bound, uniformly for EVERY denominator `q≤P`. -/
theorem actualMajorArcLcmAdmissibleCellTriples_card_le
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d denominator cutoff : ℕ)
    (hdenominator : 0 < denominator)
    (hcutoff : denominator ≤ cutoff)
    (hsupport : ∀ p ∈ S, p.Prime) :
    (actualMajorArcLcmAdmissibleCellTriples
      S b target a d denominator).card ≤
        ((∏ p ∈ S, p) * cutoff) ^ 3 := by
  have hfilter :
      (actualMajorArcLcmAdmissibleCellTriples
        S b target a d denominator).card ≤
        (actualMajorArcLcmAllCellTriples S denominator).card := by
    classical
    change
      ((actualMajorArcLcmAllCellTriples S denominator).filter
        (actualMajorArcLcmAdmissibleCell
          S b target a d denominator)).card ≤ _
    exact Finset.card_filter_le _ _
  rw [actualMajorArcLcmAllCellTriples_card] at hfilter
  exact hfilter.trans
    (actualMajorArcError_lcm_triple_cell_card_le
      S denominator cutoff hdenominator hcutoff hsupport)

/-- EXACT original full prime cubic: modeled-eligible actual cells PLUS all
other actual cells with their ORIGINAL signed prime values. -/
theorem actualMajorArcPrimeCubic_eq_admissible_add_exceptional_cells
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J target a d denominator : ℕ) (τ ell : ℝ) (α : ℝ)
    (hdenominator : 0 < denominator)
    (hsupport : ∀ p ∈ S, p.Prime) :
    actualMajorArcPrimeCubic S b n J target a d τ ell α =
      (∑ triple ∈ actualMajorArcLcmAdmissibleCellTriples
          S b target a d denominator,
        actualMajorArcLcmPrimeCellCubic
          S b n J target a d denominator
          triple.1 triple.2.1 triple.2.2 τ ell α) +
      ∑ triple ∈ actualMajorArcLcmExceptionalCellTriples
          S b target a d denominator,
        actualMajorArcLcmPrimeCellCubic
          S b n J target a d denominator
          triple.1 triple.2.1 triple.2.2 τ ell α := by
  classical
  have hfull := actualMajorArcPrimeCubic_eq_lcm_residue_cell_triple_sum
    S b n J target a d denominator τ ell α hdenominator hsupport
  have hflat :
      actualMajorArcPrimeCubic S b n J target a d τ ell α =
        ∑ triple ∈ actualMajorArcLcmAllCellTriples S denominator,
          actualMajorArcLcmPrimeCellCubic
            S b n J target a d denominator
            triple.1 triple.2.1 triple.2.2 τ ell α := by
    simpa [actualMajorArcLcmAllCellTriples,
      actualMajorArcLcmPrimeCellCubic, Finset.sum_product] using hfull
  rw [hflat]
  simpa [actualMajorArcLcmAdmissibleCellTriples,
    actualMajorArcLcmExceptionalCellTriples] using
    (Finset.sum_filter_add_sum_filter_not
    (actualMajorArcLcmAllCellTriples S denominator)
    (actualMajorArcLcmAdmissibleCell S b target a d denominator)
    (fun triple => actualMajorArcLcmPrimeCellCubic
      S b n J target a d denominator
      triple.1 triple.2.1 triple.2.2 τ ell α)).symm

/-- Pointwise full-cubic proper-prime-power correction is `n` times the
historical INTEGRATED quadratic-scale correction. -/
theorem actualMajorArcFullCubicPrimePowerError_eq_n_mul
    (n : ℕ) :
    actualMajorArcFullCubicPrimePowerError n =
      (n : ℝ) * ternaryPrimePowerErrorBound n := by
  unfold actualMajorArcFullCubicPrimePowerError
    ternaryPrimePowerErrorBound
  ring

/-- After restoring an actual arc-width factor `1/n`, even ANY fixed
polynomial number of denominators, cells, or coefficient branches leaves
the genuine full-cubic prime-power correction `o(n²)`. -/
theorem actualMajorArcFullCubicPrimePowerError_arc_normalized_tendsto_zero
    (power : ℕ) :
    Tendsto
      (fun n : ℕ =>
        (compatibleLogMinorCutoff n : ℝ) ^ power *
          (((n : ℝ)⁻¹ * actualMajorArcFullCubicPrimePowerError n) /
            (n : ℝ) ^ 2))
      atTop (nhds 0) := by
  have hbase :=
    actualMajorArcError_cutoff_power_prime_power_normalized_tendsto_zero
      power
  refine Filter.Tendsto.congr' ?_ hbase
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [actualMajorArcFullCubicPrimePowerError_eq_n_mul]
  field_simp

/-- The ORIGINAL prime-only cubic at EVERY actual shifted Farey center is
approximated by the sum of ALL compatible switched-unit smooth triples,
while retaining EVERY remaining signed actual triple exactly. Its error is
the FULL SUM of independent three-factor SW and proper-prime-power errors.

This makes the exact residual task explicit: integrated conductor grouping
and positivity of the retained smooth-plus-signed-complement expression. -/
theorem actualMajorArcPrimeCubic_shifted_full_cell_model
    (S : Finset ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ (J target a d denominator : ℕ) (τ ell : ℝ),
          0 < denominator → denominator ≤ compatibleLogMinorCutoff n →
          0 < a → 0 < d →
          target ∈ robustResidues S b J →
          manuscriptRealLabelLower τ n ≤ manuscriptRealLabelUpper τ ell n →
          manuscriptRealLabelUpper τ ell n ≤ n →
          n / (2 * a) + 1 ≤ n →
          n / (4 * d) + 1 ≤ n →
          ∀ numerator shift lift : ℤ, ∀ β : ℝ,
            let L := actualMajorArcLcmResidueModulus S denominator
            let effective : ℤ := numerator * ((L / denominator : ℕ) : ℤ) -
              shift * ((L / (∏ p ∈ S, p) : ℕ) : ℤ) + lift * (L : ℤ)
            let α : ℝ := (numerator : ℝ) / denominator -
              (shift : ℝ) / (((∏ p ∈ S, p) : ℕ) : ℝ) +
              (lift : ℝ) + β
            ‖actualMajorArcPrimeCubic S b n J target a d τ ell α -
              ((∑ triple ∈ actualMajorArcLcmAdmissibleCellTriples
                  S b target a d denominator,
                actualMajorArcLcmSmoothCellCubic
                  S n a d denominator triple.1 triple.2.1 triple.2.2
                    τ ell effective β) +
                ∑ triple ∈ actualMajorArcLcmExceptionalCellTriples
                  S b target a d denominator,
                  actualMajorArcLcmPrimeCellCubic
                    S b n J target a d denominator
                      triple.1 triple.2.1 triple.2.2 τ ell α)‖ ≤
              ∑ triple ∈ actualMajorArcLcmAdmissibleCellTriples
                S b target a d denominator,
                  (ternaryManuscriptMajorArcCubicError
                    c C n L triple.1 triple.2.1 triple.2.2 a d
                    (manuscriptRealLabelLower τ n)
                    (manuscriptRealLabelUpper τ ell n)
                    1 (n / (2 * a) + 1)
                    1 (n / (4 * d) + 1)
                    effective β +
                    actualMajorArcFullCubicPrimePowerError n) := by
  classical
  obtain ⟨c, C, hc, hC, hmodel⟩ :=
    actualMajorArcLcm_shifted_actual_prime_cell_cubic_model
      S b hsupport
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [hmodel] with n hn
  intro J target a d denominator τ ell hdenominator hcutoff
    ha hd htarget hlabelLower hlabelUpper hleftUpper hrightUpper
    numerator shift lift β
  let L := actualMajorArcLcmResidueModulus S denominator
  let effective : ℤ := numerator * ((L / denominator : ℕ) : ℤ) -
    shift * ((L / (∏ p ∈ S, p) : ℕ) : ℤ) + lift * (L : ℤ)
  let α : ℝ := (numerator : ℝ) / denominator -
    (shift : ℝ) / (((∏ p ∈ S, p) : ℕ) : ℝ) +
    (lift : ℝ) + β
  let good := actualMajorArcLcmAdmissibleCellTriples
    S b target a d denominator
  let bad := actualMajorArcLcmExceptionalCellTriples
    S b target a d denominator
  let prime : ℕ × ℕ × ℕ → ℂ := fun triple =>
    actualMajorArcLcmPrimeCellCubic S b n J target a d denominator
      triple.1 triple.2.1 triple.2.2 τ ell α
  let smooth : ℕ × ℕ × ℕ → ℂ := fun triple =>
    actualMajorArcLcmSmoothCellCubic S n a d denominator
      triple.1 triple.2.1 triple.2.2 τ ell effective β
  let error : ℕ × ℕ × ℕ → ℝ := fun triple =>
    ternaryManuscriptMajorArcCubicError
      c C n L triple.1 triple.2.1 triple.2.2 a d
      (manuscriptRealLabelLower τ n)
      (manuscriptRealLabelUpper τ ell n)
      1 (n / (2 * a) + 1)
      1 (n / (4 * d) + 1)
      effective β + actualMajorArcFullCubicPrimePowerError n
  have hsplit := actualMajorArcPrimeCubic_eq_admissible_add_exceptional_cells
    S b n J target a d denominator τ ell α hdenominator hsupport
  change
    ‖actualMajorArcPrimeCubic S b n J target a d τ ell α -
      ((∑ triple ∈ good, smooth triple) +
        ∑ triple ∈ bad, prime triple)‖ ≤
      ∑ triple ∈ good, error triple
  rw [hsplit]
  change
    ‖((∑ triple ∈ good, prime triple) +
        ∑ triple ∈ bad, prime triple) -
      ((∑ triple ∈ good, smooth triple) +
        ∑ triple ∈ bad, prime triple)‖ ≤
      ∑ triple ∈ good, error triple
  have hcancel :
      ((∑ triple ∈ good, prime triple) +
        ∑ triple ∈ bad, prime triple) -
      ((∑ triple ∈ good, smooth triple) +
        ∑ triple ∈ bad, prime triple) =
        ∑ triple ∈ good, (prime triple - smooth triple) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [hcancel]
  calc
    ‖∑ triple ∈ good, (prime triple - smooth triple)‖ ≤
        ∑ triple ∈ good, ‖prime triple - smooth triple‖ :=
      norm_sum_le _ _
    _ ≤ ∑ triple ∈ good, error triple := by
      apply Finset.sum_le_sum
      intro triple htriple
      have htriple' :
          triple ∈ (actualMajorArcLcmAllCellTriples S denominator).filter
            (actualMajorArcLcmAdmissibleCell
              S b target a d denominator) := by
        simpa [good, actualMajorArcLcmAdmissibleCellTriples] using htriple
      have hmember := (Finset.mem_filter.mp htriple')
      have hcoordinates := Finset.mem_product.mp hmember.1
      have hinner := Finset.mem_product.mp hcoordinates.2
      have hlabel : triple.1 < L := Finset.mem_range.mp hcoordinates.1
      have hleft : triple.2.1 < L := Finset.mem_range.mp hinner.1
      have hright : triple.2.2 < L := Finset.mem_range.mp hinner.2
      have hadmissible :
          triple.1 % (∏ p ∈ S, p) = target ∧
            Nat.Coprime triple.1 L ∧
            Nat.Coprime triple.2.1 L ∧
            Nat.Coprime triple.2.2 L ∧
            switchedHits S b (2 * (a * triple.2.1)) = 0 ∧
            switchedHits S b (2 * (2 * d * triple.2.2)) = 0 := by
        exact hmember.2
      rcases hadmissible with
        ⟨hprojection, hlabelUnit, hleftUnit, hrightUnit,
          hleftSwitched, hrightSwitched⟩
      exact hn J target a d denominator
        triple.1 triple.2.1 triple.2.2 τ ell
        hdenominator hcutoff ha hd htarget hprojection
        hlabel hleft hright hlabelUnit hleftUnit hrightUnit
        hleftSwitched hrightSwitched hlabelLower hlabelUpper
        hleftUpper hrightUpper numerator shift lift β

#print axioms Erdos689.actualMajorArcLcmAllCellTriples_card
#print axioms Erdos689.actualMajorArcLcmAdmissibleCellTriples_card_le
#print axioms Erdos689.actualMajorArcPrimeCubic_eq_admissible_add_exceptional_cells
#print axioms Erdos689.actualMajorArcFullCubicPrimePowerError_eq_n_mul
#print axioms Erdos689.actualMajorArcFullCubicPrimePowerError_arc_normalized_tendsto_zero
#print axioms Erdos689.actualMajorArcPrimeCubic_shifted_full_cell_model

end Erdos689
