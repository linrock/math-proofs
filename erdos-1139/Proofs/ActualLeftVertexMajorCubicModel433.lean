module

public import ActualLeftVertexMajorCellModel433

@[expose] public section


/-!
# The actual shifted, prime-only three-cell major-arc model

The original manuscript Fourier cubic is partitioned into genuine
`lcm(q,W)` residue cells.  On its actual support-admissible unit cells, the
left and center intervals retain the indispensable endpoints `n/(2*a)`
and `n/(4*d)`, while the label interval retains the original arbitrary-real
strict/weak strip and robust residue.  The true shifted center
`h/q-j/W+k` uses its exact integral lifted numerator.  The three-factor
Siegel--Walfisz/Abel model and the FULL prime-power correction are both
kept explicitly; no signed support center, nonunit exception, or
integrated singular-series lower bound is silently discarded.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos689

/-- The actual original prime-only manuscript cubic in ONE genuine
`lcm(q,W)` triple residue cell; all original prime and switched filters
remain inside the three actual finite windows. -/
noncomputable def actualMajorArcLcmPrimeCellCubic
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J target a d denominator labelResidue leftResidue rightResidue : ℕ)
    (τ ell : ℝ) (α : ℝ) : ℂ :=
  ternaryExponentialSum
      ((actualMajorArcLabelPrimeWindow S b n J target τ ell).filter
        (fun t => t % actualMajorArcLcmResidueModulus S denominator =
          labelResidue))
      (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
      1 α *
    ternaryExponentialSum
      ((actualMajorArcLeftPrimeWindow S b n a).filter
        (fun t => t % actualMajorArcLcmResidueModulus S denominator =
          leftResidue))
      (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
      (a : ℤ) α *
    ternaryExponentialSum
      ((actualMajorArcCenterPrimeWindow S b n d).filter
        (fun t => t % actualMajorArcLcmResidueModulus S denominator =
          rightResidue))
      (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
      (-2 * (d : ℤ)) α

/-- The actual smooth three-factor interval model for one coefficient pair,
one common-modulus residue triple, and the original three edge intervals. -/
noncomputable def actualMajorArcLcmSmoothCellCubic
    (S : Finset ℕ)
    (n a d denominator labelResidue leftResidue rightResidue : ℕ)
    (τ ell : ℝ) (effective : ℤ) (β : ℝ) : ℂ :=
  ternaryMajorArcIntervalModel
      (manuscriptRealLabelLower τ n)
      (manuscriptRealLabelUpper τ ell n)
      (actualMajorArcLcmResidueModulus S denominator)
      labelResidue 1 effective β *
    ternaryMajorArcIntervalModel
      1 (n / (2 * a) + 1)
      (actualMajorArcLcmResidueModulus S denominator)
      leftResidue (a : ℤ) effective β *
    ternaryMajorArcIntervalModel
      1 (n / (4 * d) + 1)
      (actualMajorArcLcmResidueModulus S denominator)
      rightResidue (-2 * (d : ℤ)) effective β

/-- Exact reduction of a genuine support-admissible unit-cell of the
ACTUAL shifted manuscript cubic to the already audited prime-filtered
interval cubic, with the ORIGINAL shifted numerator retained exactly. -/
theorem actualMajorArcLcmPrimeCellCubic_eq_interval_prime_cubic
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J target a d denominator labelResidue leftResidue rightResidue : ℕ)
    (τ ell : ℝ) (numerator shift lift : ℤ) (β : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hdenominator : 0 < denominator)
    (ha : 0 < a) (hd : 0 < d)
    (htarget : target ∈ robustResidues S b J)
    (hlabelProjection : labelResidue % (∏ p ∈ S, p) = target)
    (hleftUnit : Nat.Coprime leftResidue
      (actualMajorArcLcmResidueModulus S denominator))
    (hrightUnit : Nat.Coprime rightResidue
      (actualMajorArcLcmResidueModulus S denominator))
    (hleftSwitched : switchedHits S b (2 * (a * leftResidue)) = 0)
    (hrightSwitched : switchedHits S b (2 * (2 * d * rightResidue)) = 0) :
    actualMajorArcLcmPrimeCellCubic S b n J target a d denominator
      labelResidue leftResidue rightResidue τ ell
        ((numerator : ℝ) / denominator -
          (shift : ℝ) / (((∏ p ∈ S, p) : ℕ) : ℝ) +
          (lift : ℝ) + β) =
      ternaryManuscriptResidueCubicPrimeOnly
        (actualMajorArcLcmResidueModulus S denominator)
        labelResidue leftResidue rightResidue a d
        (manuscriptRealLabelLower τ n)
        (manuscriptRealLabelUpper τ ell n)
        1 (n / (2 * a) + 1)
        1 (n / (4 * d) + 1)
        (numerator *
            ((actualMajorArcLcmResidueModulus S denominator /
              denominator : ℕ) : ℤ) -
          shift *
            ((actualMajorArcLcmResidueModulus S denominator /
              (∏ p ∈ S, p) : ℕ) : ℤ) +
          lift * (actualMajorArcLcmResidueModulus S denominator : ℤ))
        β := by
  unfold actualMajorArcLcmPrimeCellCubic
    ternaryManuscriptResidueCubicPrimeOnly
  rw [actualMajorArcLabelPrime_compatible_cell_eq_interval
      S b n J target denominator labelResidue τ ell
        htarget hlabelProjection,
    actualMajorArcLeftPrime_unit_cell_eq_interval
      S b n a denominator leftResidue hsupport ha hleftUnit hleftSwitched,
    actualMajorArcCenterPrime_unit_cell_eq_interval
      S b n d denominator rightResidue hsupport hd hrightUnit hrightSwitched,
    actualMajorArcLcm_rescaled_shifted_rational_center
      S denominator numerator shift lift hdenominator hsupport]

/-- The actual three-prime pointwise correction incurred when replacing
all three von-Mangoldt intervals by genuine prime-filtered intervals. -/
noncomputable def actualMajorArcFullCubicPrimePowerError
    (n : ℕ) : ℝ :=
  3 * ((n : ℝ) * Real.log n) ^ 2 *
    ((Nat.sqrt n : ℝ) * (Nat.log 2 n + 1) * Real.log n)

/-- Uniform rated PRIME-ONLY interval cubic model with all three actual
frequencies and the complete independent proper-prime-power correction. -/
theorem actualMajorArcPrimeOnly_interval_cubic_model
    (B : ℝ) (hB : 1 ≤ B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N →
        ∀ labelLower labelUpper leftLower leftUpper rightLower rightUpper : ℕ,
          labelLower ≤ labelUpper → labelUpper ≤ N →
          leftLower ≤ leftUpper → leftUpper ≤ N →
          rightLower ≤ rightUpper → rightUpper ≤ N →
          ∀ modulus : ℕ, 0 < modulus →
            (modulus : ℝ) ≤ Real.log N ^ B →
            ∀ labelResidue leftResidue rightResidue : ℕ,
              labelResidue < modulus →
              leftResidue < modulus →
              rightResidue < modulus →
              Nat.gcd labelResidue modulus = 1 →
              Nat.gcd leftResidue modulus = 1 →
              Nat.gcd rightResidue modulus = 1 →
              ∀ a d : ℕ, ∀ numerator : ℤ, ∀ β : ℝ,
                ‖ternaryManuscriptResidueCubicPrimeOnly
                    modulus labelResidue leftResidue rightResidue a d
                    labelLower labelUpper leftLower leftUpper
                    rightLower rightUpper numerator β -
                  (ternaryMajorArcIntervalModel
                      labelLower labelUpper modulus labelResidue 1 numerator β *
                    ternaryMajorArcIntervalModel
                      leftLower leftUpper modulus leftResidue
                        (a : ℤ) numerator β *
                    ternaryMajorArcIntervalModel
                      rightLower rightUpper modulus rightResidue
                        (-2 * (d : ℤ)) numerator β)‖ ≤
                  ternaryManuscriptMajorArcCubicError
                    c C N modulus labelResidue leftResidue rightResidue a d
                    labelLower labelUpper leftLower leftUpper
                    rightLower rightUpper numerator β +
                  actualMajorArcFullCubicPrimePowerError N := by
  obtain ⟨c, C, hc, hC, N₀, hmodel⟩ :=
    ternary_rated_manuscript_interval_major_arc_product_model B hB
  refine ⟨c, C, hc, hC, N₀, ?_⟩
  intro N hN labelLower labelUpper leftLower leftUpper rightLower rightUpper
    hlabelLower hlabelUpper hleftLower hleftUpper hrightLower hrightUpper
    modulus hmodulus hsize labelResidue leftResidue rightResidue
    hlabelResidue hleftResidue hrightResidue
    hlabelUnit hleftUnit hrightUnit a d numerator β
  let prime := ternaryManuscriptResidueCubicPrimeOnly
    modulus labelResidue leftResidue rightResidue a d
    labelLower labelUpper leftLower leftUpper
    rightLower rightUpper numerator β
  let von := ternaryManuscriptResidueCubicVonMangoldt
    modulus labelResidue leftResidue rightResidue a d
    labelLower labelUpper leftLower leftUpper
    rightLower rightUpper numerator β
  let smooth :=
    ternaryMajorArcIntervalModel
        labelLower labelUpper modulus labelResidue 1 numerator β *
      ternaryMajorArcIntervalModel
        leftLower leftUpper modulus leftResidue (a : ℤ) numerator β *
      ternaryMajorArcIntervalModel
        rightLower rightUpper modulus rightResidue
          (-2 * (d : ℤ)) numerator β
  have hvon := hmodel N hN
    labelLower labelUpper leftLower leftUpper rightLower rightUpper
    hlabelLower hlabelUpper hleftLower hleftUpper
    hrightLower hrightUpper modulus hmodulus hsize
    labelResidue leftResidue rightResidue
    hlabelResidue hleftResidue hrightResidue
    hlabelUnit hleftUnit hrightUnit a d numerator β
  have hvon' :
      ‖von - smooth‖ ≤
        ternaryManuscriptMajorArcCubicError
          c C N modulus labelResidue leftResidue rightResidue a d
          labelLower labelUpper leftLower leftUpper
          rightLower rightUpper numerator β := by
    exact hvon
  have hpowers := ternaryManuscriptResidueCubicPrimeOnly_error
    modulus labelResidue leftResidue rightResidue a d N
      labelLower labelUpper leftLower leftUpper rightLower rightUpper
        hlabelUpper hleftUpper hrightUpper numerator β
  have hpowers' :
      ‖prime - von‖ ≤ actualMajorArcFullCubicPrimePowerError N := by
    rw [norm_sub_rev]
    exact hpowers
  change ‖prime - smooth‖ ≤ _
  calc
    ‖prime - smooth‖ = ‖(prime - von) + (von - smooth)‖ := by
      congr 1
      ring
    _ ≤ ‖prime - von‖ + ‖von - smooth‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-- The ACTUAL support-switched, prime-only, three-cell manuscript cubic
has a complete explicit major-arc model at EVERY genuine shifted center
`h/q-j/W+k`, uniformly for all Farey denominators `q≤P`, including
denominators sharing support primes or containing prime powers. -/
theorem actualMajorArcLcm_shifted_actual_prime_cell_cubic_model
    (S : Finset ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ (J target a d denominator labelResidue leftResidue rightResidue : ℕ)
          (τ ell : ℝ),
          0 < denominator → denominator ≤ compatibleLogMinorCutoff n →
          0 < a → 0 < d →
          target ∈ robustResidues S b J →
          labelResidue % (∏ p ∈ S, p) = target →
          labelResidue < actualMajorArcLcmResidueModulus S denominator →
          leftResidue < actualMajorArcLcmResidueModulus S denominator →
          rightResidue < actualMajorArcLcmResidueModulus S denominator →
          Nat.Coprime labelResidue
            (actualMajorArcLcmResidueModulus S denominator) →
          Nat.Coprime leftResidue
            (actualMajorArcLcmResidueModulus S denominator) →
          Nat.Coprime rightResidue
            (actualMajorArcLcmResidueModulus S denominator) →
          switchedHits S b (2 * (a * leftResidue)) = 0 →
          switchedHits S b (2 * (2 * d * rightResidue)) = 0 →
          manuscriptRealLabelLower τ n ≤ manuscriptRealLabelUpper τ ell n →
          manuscriptRealLabelUpper τ ell n ≤ n →
          n / (2 * a) + 1 ≤ n →
          n / (4 * d) + 1 ≤ n →
          ∀ numerator shift lift : ℤ, ∀ β : ℝ,
            let L := actualMajorArcLcmResidueModulus S denominator
            let effective : ℤ := numerator * ((L / denominator : ℕ) : ℤ) -
              shift * ((L / (∏ p ∈ S, p) : ℕ) : ℤ) + lift * (L : ℤ)
            ‖actualMajorArcLcmPrimeCellCubic
                  S b n J target a d denominator
                  labelResidue leftResidue rightResidue τ ell
                    ((numerator : ℝ) / denominator -
                      (shift : ℝ) / (((∏ p ∈ S, p) : ℕ) : ℝ) +
                      (lift : ℝ) + β) -
                actualMajorArcLcmSmoothCellCubic
                  S n a d denominator labelResidue leftResidue rightResidue
                    τ ell effective β‖ ≤
              ternaryManuscriptMajorArcCubicError
                c C n L labelResidue leftResidue rightResidue a d
                (manuscriptRealLabelLower τ n)
                (manuscriptRealLabelUpper τ ell n)
                1 (n / (2 * a) + 1)
                1 (n / (4 * d) + 1)
                effective β +
              actualMajorArcFullCubicPrimePowerError n := by
  obtain ⟨c, C, hc, hC, N₀, hmodel⟩ :=
    actualMajorArcPrimeOnly_interval_cubic_model
      (13 : ℝ) (by norm_num)
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards
    [eventually_ge_atTop N₀,
      actualMajorArcLcmResidueModulus_eventually_siegel_walfisz_range
        S hsupport] with n hn hcommon
  intro J target a d denominator labelResidue leftResidue rightResidue
    τ ell hdenominator hcutoff ha hd htarget hprojection
    hlabelResidue hleftResidue hrightResidue
    hlabelUnit hleftUnit hrightUnit hleftSwitched hrightSwitched
    hlabelLower hlabelUpper hleftUpper hrightUpper
    numerator shift lift β
  let L := actualMajorArcLcmResidueModulus S denominator
  let effective : ℤ := numerator * ((L / denominator : ℕ) : ℤ) -
    shift * ((L / (∏ p ∈ S, p) : ℕ) : ℤ) + lift * (L : ℤ)
  have hL : 0 < L := actualMajorArcLcmResidueModulus_pos
    S denominator hdenominator hsupport
  have hsize : (L : ℝ) ≤ Real.log (n : ℝ) ^ (13 : ℝ) := by
    rw [show (13 : ℝ) = ((13 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    exact hcommon denominator hdenominator hcutoff
  have hleftlower : 1 ≤ n / (2 * a) + 1 := Nat.le_add_left 1 _
  have hrightlower : 1 ≤ n / (4 * d) + 1 := Nat.le_add_left 1 _
  have hactual := actualMajorArcLcmPrimeCellCubic_eq_interval_prime_cubic
    S b n J target a d denominator labelResidue leftResidue rightResidue
      τ ell numerator shift lift β hsupport hdenominator ha hd
      htarget hprojection hleftUnit hrightUnit
        hleftSwitched hrightSwitched
  have hpoint := hmodel n hn
    (manuscriptRealLabelLower τ n)
    (manuscriptRealLabelUpper τ ell n)
    1 (n / (2 * a) + 1)
    1 (n / (4 * d) + 1)
    hlabelLower hlabelUpper hleftlower hleftUpper
      hrightlower hrightUpper L hL hsize
    labelResidue leftResidue rightResidue
      hlabelResidue hleftResidue hrightResidue
      hlabelUnit hleftUnit hrightUnit a d effective β
  change
    ‖actualMajorArcLcmPrimeCellCubic S b n J target a d denominator
      labelResidue leftResidue rightResidue τ ell
        ((numerator : ℝ) / denominator -
          (shift : ℝ) / (((∏ p ∈ S, p) : ℕ) : ℝ) +
          (lift : ℝ) + β) -
      actualMajorArcLcmSmoothCellCubic
        S n a d denominator labelResidue leftResidue rightResidue
          τ ell effective β‖ ≤ _
  rw [hactual]
  exact hpoint


end Erdos689
