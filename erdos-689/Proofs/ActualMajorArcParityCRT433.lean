import ActualMajorArcPositivityTail433
import ActualRightVertexMajorSingularAssembly433
import ActualMajorArcSupportSelectorBridge433

/-!
# Actual parity-conductor cutoff and higher-conductor cancellation

The original shifted major arcs contain both odd outside denominators `r`
and their genuine parity companions `2*r`.  Their sharp Farey cutoffs are
different: the exact arithmetic contribution is `A(P) + A(P/2)`, not
`2*A(P)`.  Absolute convergence makes their discrepancy negligible, but the
finite equality with the doubled model would be false.

Higher parity conductors must also be cancelled with the actual fixed-label
support residue and full common-modulus UNIT filter intact.  The original
three-cell smooth factorization then transfers that cancellation to the
genuine selected cubic; no signed support or outside contribution is
discarded.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos689

/-- The exact sharp outside-support signed rational-denominator sum. -/
noncomputable def actualMajorArcParityOutsidePartial
    (excluded cutoff : ℕ) : ℝ :=
  ∑ denominator ∈ Finset.Icc 1 cutoff,
    actualMajorArcRestrictedSignedCoefficient excluded denominator

/-- The TRUE finite parity conductor sum retains the different sharp
cutoffs `r ≤ P` and `2*r ≤ P`. -/
noncomputable def actualMajorArcParitySharpPartial
    (excluded cutoff : ℕ) : ℝ :=
  actualMajorArcParityOutsidePartial excluded cutoff +
    actualMajorArcParityOutsidePartial excluded (cutoff / 2)

/-- Exactly the genuine outside denominators whose parity companion still
satisfies the original sharp Farey cutoff. -/
theorem actualMajorArcParity_even_companion_filter
    (cutoff : ℕ) :
    (Finset.Icc 1 cutoff).filter
        (fun denominator => 2 * denominator ≤ cutoff) =
      Finset.Icc 1 (cutoff / 2) := by
  ext denominator
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hpositive, _⟩, hdouble⟩
    exact ⟨hpositive, (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)⟩
  · rintro ⟨hpositive, hhalf⟩
    have hdouble :=
      (Nat.le_div_iff_mul_le (by norm_num : 0 < (2 : ℕ))).mp hhalf
    exact ⟨⟨hpositive, by omega⟩, by omega⟩

/-- The parity term is an exact sum over genuine original denominators
`2*r ≤ P`, with no silently doubled endpoint. -/
theorem actualMajorArcParitySharpPartial_eq_actual_cutoffs
    (excluded cutoff : ℕ) :
    actualMajorArcParitySharpPartial excluded cutoff =
      (∑ denominator ∈ Finset.Icc 1 cutoff,
        actualMajorArcRestrictedSignedCoefficient excluded denominator) +
      ∑ denominator ∈
        (Finset.Icc 1 cutoff).filter
          (fun denominator => 2 * denominator ≤ cutoff),
        actualMajorArcRestrictedSignedCoefficient excluded denominator := by
  unfold actualMajorArcParitySharpPartial
    actualMajorArcParityOutsidePartial
  rw [actualMajorArcParity_even_companion_filter cutoff]

/-- Exact decomposition of the sharp outside sum into its parity-compatible
part and the genuine omitted top half-shell. -/
theorem actualMajorArcParityOutsidePartial_eq_half_add_shell
    (excluded cutoff : ℕ) :
    actualMajorArcParityOutsidePartial excluded cutoff =
      actualMajorArcParityOutsidePartial excluded (cutoff / 2) +
        ∑ denominator ∈ Finset.Icc (cutoff / 2 + 1) cutoff,
          actualMajorArcRestrictedSignedCoefficient excluded denominator := by
  have hsplit :
      Finset.Icc 1 cutoff =
        (Finset.Icc 1 (cutoff / 2)) ∪
          (Finset.Icc (cutoff / 2 + 1) cutoff) := by
    ext denominator
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisjoint :
      Disjoint (Finset.Icc 1 (cutoff / 2))
        (Finset.Icc (cutoff / 2 + 1) cutoff) := by
    apply Finset.disjoint_left.mpr
    intro denominator hleft hright
    have hleft' := (Finset.mem_Icc.mp hleft).2
    have hright' := (Finset.mem_Icc.mp hright).1
    omega
  unfold actualMajorArcParityOutsidePartial
  rw [hsplit, Finset.sum_union hdisjoint]

/-- The finite correction to the doubled outside model is EXACTLY the
negative signed top parity shell; it is not identically zero. -/
theorem actualMajorArcParitySharpPartial_sub_doubled_eq_neg_shell
    (excluded cutoff : ℕ) :
    actualMajorArcParitySharpPartial excluded cutoff -
        2 * actualMajorArcParityOutsidePartial excluded cutoff =
      -(∑ denominator ∈ Finset.Icc (cutoff / 2 + 1) cutoff,
        actualMajorArcRestrictedSignedCoefficient excluded denominator) := by
  have hsplit :=
    actualMajorArcParityOutsidePartial_eq_half_add_shell excluded cutoff
  unfold actualMajorArcParitySharpPartial
  linarith

/-- The true halved natural Farey cutoff still tends to infinity. -/
theorem actualMajorArcParity_half_cutoff_tendsto_atTop :
    Tendsto (fun cutoff : ℕ => cutoff / 2) atTop atTop := by
  apply tendsto_atTop.2
  intro bound
  filter_upwards [eventually_ge_atTop (2 * bound)] with cutoff hcutoff
  exact (Nat.le_div_iff_mul_le (by norm_num : 0 < (2 : ℕ))).mpr
    (by omega)

/-- The sharp odd-outside and genuine parity-companion sums converge to
the SAME already-proved absolutely convergent signed Euler series. -/
theorem actualMajorArcParity_half_series_tendsto
    (excluded : ℕ) :
    Tendsto
      (fun cutoff : ℕ =>
        actualMajorArcParityOutsidePartial excluded (cutoff / 2))
      atTop
      (nhds (∑' denominator : ℕ,
        actualMajorArcRestrictedSignedCoefficient excluded denominator)) := by
  exact
    (actualMajorArcRestrictedSignedCoefficient_sharp_truncation_tendsto
      excluded).comp actualMajorArcParity_half_cutoff_tendsto_atTop

/-- The genuine two-cutoff parity singular sum converges to twice the
actual restricted Euler series; this is a LIMIT, not a false finite identity. -/
theorem actualMajorArcParitySharpPartial_tendsto
    (excluded : ℕ) :
    Tendsto (actualMajorArcParitySharpPartial excluded)
      atTop
      (nhds (2 * ∑' denominator : ℕ,
        actualMajorArcRestrictedSignedCoefficient excluded denominator)) := by
  have hfull :=
    actualMajorArcRestrictedSignedCoefficient_sharp_truncation_tendsto
      excluded
  have hhalf := actualMajorArcParity_half_series_tendsto excluded
  convert hfull.add hhalf using 1
  · funext cutoff
    rfl
  · ring

/-- The EXACT finite parity cutoff discrepancy from the doubled model
tends to zero; this discharges the previously missing parity shell. -/
theorem actualMajorArcParitySharpPartial_sub_doubled_tendsto_zero
    (excluded : ℕ) :
    Tendsto
      (fun cutoff : ℕ =>
        actualMajorArcParitySharpPartial excluded cutoff -
          2 * actualMajorArcParityOutsidePartial excluded cutoff)
      atTop (nhds 0) := by
  have hfull :=
    actualMajorArcRestrictedSignedCoefficient_sharp_truncation_tendsto
      excluded
  have hhalf := actualMajorArcParity_half_series_tendsto excluded
  have hdifference := hhalf.sub hfull
  convert hdifference using 1
  · ext cutoff
    unfold actualMajorArcParitySharpPartial
      actualMajorArcParityOutsidePartial
    ring
  · simp

/-- The actual manuscript cutoff `P(n)=floor(log n)^12` has negligible
parity-shell discrepancy, with ALL fixed support exclusions retained. -/
theorem actualMajorArcParity_compatible_cutoff_discrepancy_tendsto_zero
    (excluded : ℕ) :
    Tendsto
      (fun n : ℕ =>
        actualMajorArcParitySharpPartial excluded
            (compatibleLogMinorCutoff n) -
          2 * actualMajorArcParityOutsidePartial excluded
            (compatibleLogMinorCutoff n))
      atTop (nhds 0) := by
  exact
    (actualMajorArcParitySharpPartial_sub_doubled_tendsto_zero excluded).comp
      compatibleLogMinorCutoff_tendsto_atTop

/-- The EXACT genuine parity-corrected sharp series is eventually at least
`1/2` for EVERY fixed even support exclusion. -/
theorem actualMajorArcParitySharpPartial_eventually_ge_half
    (excluded : ℕ) (heven : 2 ∣ excluded) :
    ∀ᶠ cutoff : ℕ in atTop,
      (1 / 2 : ℝ) ≤ actualMajorArcParitySharpPartial excluded cutoff := by
  have hfull :=
    actualMajorArcRestrictedSignedCoefficient_sharp_truncation_ge_quarter
      excluded heven
  have hhalf :=
    actualMajorArcParity_half_cutoff_tendsto_atTop.eventually hfull
  filter_upwards [hfull, hhalf] with cutoff hcutoff hhalfcutoff
  unfold actualMajorArcParitySharpPartial
    actualMajorArcParityOutsidePartial
  linarith

/-- The same positive parity-corrected bound holds at the TRUE manuscript
Farey denominator cutoff, uniformly in each fixed support. -/
theorem actualMajorArcParity_compatible_cutoff_ge_half
    (excluded : ℕ) (heven : 2 ∣ excluded) :
    ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) ≤
        actualMajorArcParitySharpPartial excluded
          (compatibleLogMinorCutoff n) := by
  exact compatibleLogMinorCutoff_tendsto_atTop.eventually
    (actualMajorArcParitySharpPartial_eventually_ge_half excluded heven)

/-- Every primitive rational-center label phase at a denominator divisible
by four vanishes, including all outside prime factors. -/
theorem actualMajorArcParity_unit_phase_zero_of_four_dvd
    (denominator numerator : ℕ)
    (hdenominator : 0 < denominator)
    (hfour : 4 ∣ denominator)
    (hnumerator : Nat.Coprime numerator denominator) :
    actualMajorArcUnitResiduePhase denominator (numerator : ℤ) = 0 := by
  have hnot : ¬ Squarefree denominator := by
    intro hsquarefree
    have h := (Nat.squarefree_iff_prime_squarefree.mp hsquarefree)
      2 Nat.prime_two
    apply h
    simpa using hfour
  rw [actualMajorArcUnitResiduePhase_eq_moebius
    denominator (numerator : ℤ) hdenominator
      (actualMajorArc_natCast_frequency_gcd
        numerator denominator hnumerator),
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnot]
  norm_num

/-- A genuine unit-residue phase is invariant under changing the sign of
its natural integral frequency, including NONUNIT frequencies. -/
theorem actualMajorArcParity_unit_phase_neg_nat_eq
    (denominator frequency : ℕ)
    (hdenominator : 0 < denominator) :
    actualMajorArcUnitResiduePhase denominator (-(frequency : ℤ)) =
      actualMajorArcUnitResiduePhase denominator (frequency : ℤ) := by
  unfold actualMajorArcUnitResiduePhase
  rw [GoldbachChain.MinorArc.ramanujan_sum_divisor
    (-(frequency : ℤ)) denominator hdenominator,
    GoldbachChain.MinorArc.ramanujan_sum_divisor
      (frequency : ℤ) denominator hdenominator]
  simp

/-- The actual NONUNIT doubled right frequency at parity conductor `2*r`
has phase exactly `μ(r)`.  This retains the original frequency `-2*d*h`,
all outside denominator primes, and every true unit residue. -/
theorem actualMajorArcParity_doubled_right_phase
    (outside d numerator : ℕ)
    (houtside : 0 < outside)
    (hodd : Nat.Coprime 2 outside)
    (hcoeff : Nat.Coprime outside (2 * d))
    (hnumerator : Nat.Coprime numerator (2 * outside)) :
    actualMajorArcUnitResiduePhase
        (2 * outside) (-(2 * d * numerator : ℕ) : ℤ) =
      (ArithmeticFunction.moebius outside : ℂ) := by
  let frequency := 2 * d * numerator
  have hmodulus : 0 < 2 * outside := by omega
  have houtsideDivides : outside ∣ 2 * outside := by
    exact dvd_mul_left outside 2
  have hnumeratorOutside : Nat.Coprime numerator outside :=
    hnumerator.coprime_dvd_right houtsideDivides
  have hfrequencyOutside : Nat.Coprime frequency outside := by
    dsimp [frequency]
    exact hcoeff.symm.mul_left hnumeratorOutside
  have htwoFrequency : 2 ∣ frequency := by
    dsimp [frequency]
    exact dvd_mul_of_dvd_left (dvd_mul_right 2 d) numerator
  rw [actualMajorArcParity_unit_phase_neg_nat_eq
    (2 * outside) frequency hmodulus]
  have hram :
      actualMajorArcUnitResiduePhase (2 * outside) (frequency : ℤ) =
        GoldbachChain.MajorArcMainTerm.ramSum
          (2 * outside) frequency := by
    rfl
  rw [hram,
    GoldbachChain.MajorArcMainTerm.ramSum_eq_cRam
      (2 * outside) frequency hmodulus,
    GoldbachChain.MajorArcMainTerm.cRam_mul
      frequency 2 outside hodd,
    GoldbachChain.MajorArcMainTerm.cRam_prime
      2 frequency Nat.prime_two,
    if_pos htwoFrequency]
  norm_num
  have hphase :
      (GoldbachChain.MajorArcMainTerm.cRam
        outside frequency : ℂ) =
          (ArithmeticFunction.moebius outside : ℂ) := by
    rw [← GoldbachChain.MajorArcMainTerm.ramSum_eq_cRam
      outside frequency houtside]
    change
      actualMajorArcUnitResiduePhase outside (frequency : ℤ) =
        (ArithmeticFunction.moebius outside : ℂ)
    exact actualMajorArcUnitResiduePhase_eq_moebius
      outside (frequency : ℤ) houtside
        (actualMajorArc_natCast_frequency_gcd
          frequency outside hfrequencyOutside)
  exact_mod_cast hphase

/-- At EVERY genuine doubled outside denominator, the FULL ORIGINAL
three-form rational-center phase equals `μ(r)^3`; the two odd-coordinate
minus signs cancel and the doubled right coordinate contributes `μ(r)`. -/
theorem actualMajorArcParity_doubled_center_phase
    (outside a d numerator : ℕ)
    (houtside : 0 < outside)
    (hodd : Nat.Coprime 2 outside)
    (haodd : Nat.Coprime a 2)
    (hcoeff : Nat.Coprime outside (2 * a * d))
    (hnumerator : Nat.Coprime numerator (2 * outside)) :
    actualMajorArcGenericPrimeCenterPhase
        (2 * outside) a d numerator =
      (ArithmeticFunction.moebius outside : ℂ) ^ 3 := by
  have hmodulus : 0 < 2 * outside := by omega
  have haoutside : Nat.Coprime a outside := by
    apply hcoeff.symm.coprime_dvd_left
    refine ⟨2 * d, ?_⟩
    ring
  have hdenominator : Nat.Coprime a (2 * outside) :=
    (Nat.coprime_mul_iff_right).mpr ⟨haodd, haoutside⟩
  have hleft : Nat.Coprime (a * numerator) (2 * outside) :=
    hdenominator.mul_left hnumerator
  have hdoubled : Nat.Coprime outside (2 * d) := by
    apply hcoeff.coprime_dvd_right
    refine ⟨a, ?_⟩
    ring
  unfold actualMajorArcGenericPrimeCenterPhase
  rw [actualMajorArcUnitResiduePhase_eq_moebius
      (2 * outside) (numerator : ℤ) hmodulus
        (actualMajorArc_natCast_frequency_gcd
          numerator (2 * outside) hnumerator),
    actualMajorArcUnitResiduePhase_eq_moebius
      (2 * outside) ((a * numerator : ℕ) : ℤ) hmodulus
        (actualMajorArc_natCast_frequency_gcd
          (a * numerator) (2 * outside) hleft),
    actualMajorArcParity_doubled_right_phase
      outside d numerator houtside hodd hdoubled hnumerator,
    ArithmeticFunction.isMultiplicative_moebius.2 hodd,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  push_cast
  ring

/-- Summing ALL genuine reduced numerators at the true doubled parity
conductor gives `φ(r)*μ(r)^3`, not an omitted or unsigned contribution. -/
theorem actualMajorArcParity_doubled_center_phase_sum
    (outside a d : ℕ)
    (houtside : 0 < outside)
    (hodd : Nat.Coprime 2 outside)
    (haodd : Nat.Coprime a 2)
    (hcoeff : Nat.Coprime outside (2 * a * d)) :
    (∑ numerator ∈ (Finset.range (2 * outside)).filter
        (fun numerator => Nat.gcd numerator (2 * outside) = 1),
      actualMajorArcGenericPrimeCenterPhase
        (2 * outside) a d numerator) =
      (Nat.totient outside : ℂ) *
        (ArithmeticFunction.moebius outside : ℂ) ^ 3 := by
  calc
    (∑ numerator ∈ (Finset.range (2 * outside)).filter
        (fun numerator => Nat.gcd numerator (2 * outside) = 1),
      actualMajorArcGenericPrimeCenterPhase
        (2 * outside) a d numerator) =
      ∑ _numerator ∈ (Finset.range (2 * outside)).filter
          (fun numerator => Nat.gcd numerator (2 * outside) = 1),
        (ArithmeticFunction.moebius outside : ℂ) ^ 3 := by
          apply Finset.sum_congr rfl
          intro numerator hnumerator
          exact actualMajorArcParity_doubled_center_phase
            outside a d numerator houtside hodd haodd hcoeff
              (Finset.mem_filter.mp hnumerator).2
    _ = (Nat.totient (2 * outside) : ℂ) *
          (ArithmeticFunction.moebius outside : ℂ) ^ 3 := by
          rw [Finset.sum_const, nsmul_eq_mul,
            actualMajorArcComposite_unit_numerators_card]
    _ = (Nat.totient outside : ℂ) *
          (ArithmeticFunction.moebius outside : ℂ) ^ 3 := by
          rw [Nat.totient_two_mul_of_odd hodd.odd_of_left]

/-- The EXACT normalized signed contribution of EVERY doubled genuine
outside conductor is `μ(r)/φ(r)^2`, identical to its odd companion.
This is proved from all actual three affine frequencies and all reduced
rational numerators, not from an assumed parity factor. -/
theorem actualMajorArcParity_doubled_center_signed_correction
    (outside a d : ℕ)
    (houtside : 0 < outside)
    (hodd : Nat.Coprime 2 outside)
    (haodd : Nat.Coprime a 2)
    (hcoeff : Nat.Coprime outside (2 * a * d)) :
    (∑ numerator ∈ (Finset.range (2 * outside)).filter
        (fun numerator => Nat.gcd numerator (2 * outside) = 1),
      actualMajorArcGenericPrimeCenterPhase
        (2 * outside) a d numerator) /
          (Nat.totient (2 * outside) : ℂ) ^ 3 =
        (ArithmeticFunction.moebius outside : ℂ) /
          (Nat.totient outside : ℂ) ^ 2 := by
  rw [actualMajorArcParity_doubled_center_phase_sum
    outside a d houtside hodd haodd hcoeff,
    actualMajorArcComposite_moebius_cube outside,
    Nat.totient_two_mul_of_odd hodd.odd_of_left]
  have htotient : (Nat.totient outside : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr houtside).ne'
  field_simp

/-- Genuine integral-frequency denominator phases depend only on the
outside natural residue, even when the represented integer is a full
support-times-outside CRT lift. -/
theorem actualMajorArcParity_phase_eq_mod
    (outside value : ℕ) (frequency : ℤ)
    (houtside : 0 < outside) :
    GoldbachChain.e (((frequency : ℝ) * value) / outside) =
      GoldbachChain.e
        (((frequency : ℝ) * ((value % outside : ℕ) : ℝ)) / outside) := by
  have houtsideReal : (outside : ℝ) ≠ 0 := by
    exact_mod_cast houtside.ne'
  have hdivision :
      (value : ℝ) = ((value % outside : ℕ) : ℝ) +
        (outside : ℝ) * ((value / outside : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div value outside).symm
  have hdecomposition :
      (((frequency : ℝ) * value) / outside) =
        (((frequency : ℝ) * ((value % outside : ℕ) : ℝ)) / outside) +
          ((frequency * ((value / outside : ℕ) : ℤ) : ℤ) : ℝ) := by
    rw [hdivision]
    simp only [Int.cast_mul, Int.cast_natCast]
    field_simp
  rw [hdecomposition, ← GoldbachChain.e_add,
    GoldbachChain.MinorArc.e_int, mul_one]

/-- Exact finite CRT on a genuine selected support-unit residue: lifting
through ALL full-common-modulus units preserves precisely the outside
unit-residue character sum.  The fixed support residue is neither removed
nor assumed independent. -/
theorem actualMajorArcParity_coprime_support_unit_lift_phase
    (support outside supportResidue : ℕ)
    (frequency : ℤ)
    (hsupport : 0 < support)
    (houtside : 0 < outside)
    (hcoprime : Nat.Coprime support outside)
    (hresidue : supportResidue < support)
    (hunit : Nat.Coprime supportResidue support) :
    (∑ value ∈ (Finset.range (support * outside)).filter
        (fun value =>
          value % support = supportResidue ∧
            Nat.Coprime value (support * outside)),
      GoldbachChain.e (((frequency : ℝ) * value) / outside)) =
      actualMajorArcUnitResiduePhase outside frequency := by
  classical
  unfold actualMajorArcUnitResiduePhase
  apply Finset.sum_bij (fun value _ => value % outside)
  · intro value hvalue
    obtain ⟨_, _, hvalueUnit⟩ := Finset.mem_filter.mp hvalue
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (Nat.mod_lt value houtside), ?_⟩
    have hcoprimeOutside : Nat.Coprime value outside :=
      (Nat.coprime_mul_iff_right.mp hvalueUnit).2
    have hmod : Nat.Coprime (value % outside) outside :=
      (ZMod.coprime_mod_iff_coprime value outside).mpr hcoprimeOutside
    exact hmod
  · intro x hx y hy hequal
    obtain ⟨hxrange, hxresidue, _⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyrange, hyresidue, _⟩ := Finset.mem_filter.mp hy
    have hsupportEq : Nat.ModEq support x y := by
      change x % support = y % support
      exact hxresidue.trans hyresidue.symm
    have houtsideEq : Nat.ModEq outside x y := by
      exact hequal
    have hproduct :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcoprime).mp
        ⟨hsupportEq, houtsideEq⟩
    have hxless := Finset.mem_range.mp hxrange
    have hyless := Finset.mem_range.mp hyrange
    change x % (support * outside) = y % (support * outside) at hproduct
    simpa [Nat.mod_eq_of_lt hxless, Nat.mod_eq_of_lt hyless] using hproduct
  · intro residue hresidueOutside
    obtain ⟨hresidueRange, hresidueUnit⟩ :=
      Finset.mem_filter.mp hresidueOutside
    let lift := Nat.chineseRemainder hcoprime supportResidue residue
    have hliftLess : (lift : ℕ) < support * outside :=
      Nat.chineseRemainder_lt_mul hcoprime supportResidue residue
        hsupport.ne' houtside.ne'
    have hliftSupport : (lift : ℕ) % support = supportResidue := by
      have h := lift.property.1
      change (lift : ℕ) % support = supportResidue % support at h
      simpa [Nat.mod_eq_of_lt hresidue] using h
    have hresidueLess : residue < outside :=
      Finset.mem_range.mp hresidueRange
    have hliftOutside : (lift : ℕ) % outside = residue := by
      have h := lift.property.2
      change (lift : ℕ) % outside = residue % outside at h
      simpa [Nat.mod_eq_of_lt hresidueLess] using h
    have hliftSupportUnit : Nat.Coprime (lift : ℕ) support := by
      apply (ZMod.coprime_mod_iff_coprime (lift : ℕ) support).mp
      simpa [hliftSupport] using hunit
    have hliftOutsideUnit : Nat.Coprime (lift : ℕ) outside := by
      apply (ZMod.coprime_mod_iff_coprime (lift : ℕ) outside).mp
      rw [hliftOutside]
      exact hresidueUnit
    refine ⟨lift, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hliftLess, hliftSupport,
        (Nat.coprime_mul_iff_right).mpr
          ⟨hliftSupportUnit, hliftOutsideUnit⟩⟩, ?_⟩
    exact hliftOutside
  · intro value hvalue
    exact actualMajorArcParity_phase_eq_mod
      outside value frequency houtside

/-- The exact full-modulus UNIT lifts of one fixed switched-support residue. -/
noncomputable def actualMajorArcParitySupportUnitLift
    (support outside residue : ℕ) : Finset ℕ :=
  (Finset.range (support * outside)).filter fun value =>
    value % support = residue ∧ Nat.Coprime value (support * outside)

/-- Convenient genuine-CRT character evaluation in the exact finite lift
family used by all three original major-arc coordinates. -/
theorem actualMajorArcParitySupportUnitLift_phase
    (support outside residue : ℕ) (frequency : ℤ)
    (hsupport : 0 < support) (houtside : 0 < outside)
    (hcoprime : Nat.Coprime support outside)
    (hresidue : residue < support)
    (hunit : Nat.Coprime residue support) :
    (∑ value ∈ actualMajorArcParitySupportUnitLift
        support outside residue,
      GoldbachChain.e (((frequency : ℝ) * value) / outside)) =
      actualMajorArcUnitResiduePhase outside frequency := by
  exact actualMajorArcParity_coprime_support_unit_lift_phase
    support outside residue frequency hsupport houtside
      hcoprime hresidue hunit

/-- The ACTUAL full-common-modulus admissible switched/unit triples that
survive the genuine support-character compatibility projection. -/
noncomputable def actualMajorArcParityCompatibleFullCellTriples
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d denominator : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (actualMajorArcLcmAdmissibleCellTriples
    S b target a d denominator).filter fun triple =>
      (a * triple.2.1 + triple.1) % (∏ p ∈ S, p) =
        (2 * d * triple.2.2) % (∏ p ∈ S, p)

/-- Membership in the genuine support-compatible full-modulus triple
retains all ranges, three FULL unit filters, both switched masks, the true
fixed label residue, and its affine support congruence. -/
theorem actualMajorArcParityCompatibleFullCellTriples_mem_iff
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d denominator : ℕ)
    (triple : ℕ × ℕ × ℕ) :
    triple ∈ actualMajorArcParityCompatibleFullCellTriples
        S b target a d denominator ↔
      triple.1 < actualMajorArcLcmResidueModulus S denominator ∧
        triple.2.1 < actualMajorArcLcmResidueModulus S denominator ∧
        triple.2.2 < actualMajorArcLcmResidueModulus S denominator ∧
        triple.1 % (∏ p ∈ S, p) = target ∧
        Nat.Coprime triple.1
          (actualMajorArcLcmResidueModulus S denominator) ∧
        Nat.Coprime triple.2.1
          (actualMajorArcLcmResidueModulus S denominator) ∧
        Nat.Coprime triple.2.2
          (actualMajorArcLcmResidueModulus S denominator) ∧
        switchedHits S b (2 * (a * triple.2.1)) = 0 ∧
        switchedHits S b (2 * (2 * d * triple.2.2)) = 0 ∧
        (a * triple.2.1 + triple.1) % (∏ p ∈ S, p) =
          (2 * d * triple.2.2) % (∏ p ∈ S, p) := by
  simp [actualMajorArcParityCompatibleFullCellTriples,
    actualMajorArcLcmAdmissibleCellTriples,
    actualMajorArcLcmAllCellTriples,
    actualMajorArcLcmAdmissibleCell, and_assoc]

/-- Reducing each coordinate of an ACTUAL compatible full-common-modulus
triple gives precisely an original genuine switched/unit support triple. -/
theorem actualMajorArcParity_full_triple_support_reduction_mem
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d denominator : ℕ)
    (triple : ℕ × ℕ × ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (htriple : triple ∈ actualMajorArcParityCompatibleFullCellTriples
      S b target a d denominator) :
    (triple.1 % (∏ p ∈ S, p),
      triple.2.1 % (∏ p ∈ S, p),
      triple.2.2 % (∏ p ∈ S, p)) ∈
        actualMajorArcSupportCompatibleCellTriples S b target a d := by
  let W := ∏ p ∈ S, p
  let L := actualMajorArcLcmResidueModulus S denominator
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).pos
  have hWdivide : W ∣ L :=
    (actualMajorArcLcmResidueModulus_divisibility S denominator).2
  obtain ⟨hlabel, hleft, hright, htarget,
    hlabelUnit, hleftUnit, hrightUnit,
    hleftSwitch, hrightSwitch, hcompatible⟩ :=
      (actualMajorArcParityCompatibleFullCellTriples_mem_iff
        S b target a d denominator triple).mp htriple
  apply (actualMajorArcSupportCompatibleCellTriples_mem_iff
    S b target a d _).mpr
  refine ⟨Nat.mod_lt _ hW, Nat.mod_lt _ hW, Nat.mod_lt _ hW,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using htarget
  · exact (ZMod.coprime_mod_iff_coprime triple.1 W).mpr
      (hlabelUnit.coprime_dvd_right hWdivide)
  · exact (ZMod.coprime_mod_iff_coprime triple.2.1 W).mpr
      (hleftUnit.coprime_dvd_right hWdivide)
  · exact (ZMod.coprime_mod_iff_coprime triple.2.2 W).mpr
      (hrightUnit.coprime_dvd_right hWdivide)
  · rw [labelFiber_switchedHits_eq_of_support_mod
    S b (2 * (a * (triple.2.1 % W)))
        (2 * (a * triple.2.1)) (by simp [W, Nat.mul_mod])]
    exact hleftSwitch
  · rw [labelFiber_switchedHits_eq_of_support_mod
    S b (2 * (2 * d * (triple.2.2 % W)))
        (2 * (2 * d * triple.2.2)) (by simp [W, Nat.mul_mod])]
    exact hrightSwitch
  · simpa [Nat.add_mod, Nat.mul_mod] using hcompatible

/-- Every genuine compatible support triple has EXACTLY the Cartesian
product of its three actual full-modulus unit CRT lift fibers.  Both true
switched masks, the fixed robust label, and its affine compatibility are
preserved in the equality of finite families. -/
theorem actualMajorArcParity_full_triple_fiber_eq_unit_lifts
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d outside : ℕ)
    (supportTriple : ℕ × ℕ × ℕ)
    (_hsupport : ∀ p ∈ S, p.Prime)
    (hcoprime : Nat.Coprime (∏ p ∈ S, p) outside)
    (htriple : supportTriple ∈
      actualMajorArcSupportCompatibleCellTriples S b target a d) :
    (actualMajorArcParityCompatibleFullCellTriples
        S b target a d outside).filter
      (fun triple =>
        (triple.1 % (∏ p ∈ S, p),
          triple.2.1 % (∏ p ∈ S, p),
          triple.2.2 % (∏ p ∈ S, p)) = supportTriple) =
      (actualMajorArcParitySupportUnitLift
        (∏ p ∈ S, p) outside supportTriple.1).product
        ((actualMajorArcParitySupportUnitLift
          (∏ p ∈ S, p) outside supportTriple.2.1).product
          (actualMajorArcParitySupportUnitLift
            (∏ p ∈ S, p) outside supportTriple.2.2)) := by
  classical
  let W := ∏ p ∈ S, p
  have hmodulus : actualMajorArcLcmResidueModulus S outside =
      W * outside := by
    unfold actualMajorArcLcmResidueModulus
    rw [hcoprime.symm.lcm_eq_mul]
    exact Nat.mul_comm outside W
  obtain ⟨hsLabelBound, hsLeftBound, hsRightBound,
    hsTarget, hsLabelUnit, hsLeftUnit, hsRightUnit,
    hsLeftSwitch, hsRightSwitch, hsCompatible⟩ :=
      (actualMajorArcSupportCompatibleCellTriples_mem_iff
        S b target a d supportTriple).mp htriple
  ext triple
  rcases triple with ⟨label, left, right⟩
  constructor
  · intro hmember
    obtain ⟨hfull, hprojection⟩ := Finset.mem_filter.mp hmember
    obtain ⟨hlabelBound, hleftBound, hrightBound, _,
      hlabelUnit, hleftUnit, hrightUnit, _⟩ :=
        (actualMajorArcParityCompatibleFullCellTriples_mem_iff
          S b target a d outside (label, left, right)).mp hfull
    have hlabelProjection : label % W = supportTriple.1 :=
      congrArg Prod.fst hprojection
    have hleftProjection : left % W = supportTriple.2.1 :=
      congrArg (fun triple : ℕ × ℕ × ℕ => triple.2.1) hprojection
    have hrightProjection : right % W = supportTriple.2.2 :=
      congrArg (fun triple : ℕ × ℕ × ℕ => triple.2.2) hprojection
    apply Finset.mem_product.mpr
    refine ⟨?_, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (by simpa [hmodulus] using hlabelBound),
        hlabelProjection, by simpa [hmodulus] using hlabelUnit⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (by simpa [hmodulus] using hleftBound),
        hleftProjection, by simpa [hmodulus] using hleftUnit⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (by simpa [hmodulus] using hrightBound),
        hrightProjection, by simpa [hmodulus] using hrightUnit⟩
  · intro hmember
    obtain ⟨hlabelLift, hremaining⟩ := Finset.mem_product.mp hmember
    obtain ⟨hleftLift, hrightLift⟩ := Finset.mem_product.mp hremaining
    obtain ⟨hlabelRange, hlabelProjection, hlabelUnit⟩ :=
      Finset.mem_filter.mp hlabelLift
    obtain ⟨hleftRange, hleftProjection, hleftUnit⟩ :=
      Finset.mem_filter.mp hleftLift
    obtain ⟨hrightRange, hrightProjection, hrightUnit⟩ :=
      Finset.mem_filter.mp hrightLift
    have hlabelEq : Nat.ModEq W label supportTriple.1 := by
      change label % W = supportTriple.1 % W
      rw [Nat.mod_eq_of_lt (show supportTriple.1 < W from hsLabelBound)]
      exact hlabelProjection
    have hleftEq : Nat.ModEq W left supportTriple.2.1 := by
      change left % W = supportTriple.2.1 % W
      rw [Nat.mod_eq_of_lt (show supportTriple.2.1 < W from hsLeftBound)]
      exact hleftProjection
    have hrightEq : Nat.ModEq W right supportTriple.2.2 := by
      change right % W = supportTriple.2.2 % W
      rw [Nat.mod_eq_of_lt (show supportTriple.2.2 < W from hsRightBound)]
      exact hrightProjection
    apply Finset.mem_filter.mpr
    refine ⟨?_, Prod.ext hlabelProjection
      (Prod.ext hleftProjection hrightProjection)⟩
    apply (actualMajorArcParityCompatibleFullCellTriples_mem_iff
      S b target a d outside (label, left, right)).mpr
    refine ⟨by simpa [hmodulus] using Finset.mem_range.mp hlabelRange,
      by simpa [hmodulus] using Finset.mem_range.mp hleftRange,
      by simpa [hmodulus] using Finset.mem_range.mp hrightRange,
      ?_, by simpa [hmodulus] using hlabelUnit,
      by simpa [hmodulus] using hleftUnit,
      by simpa [hmodulus] using hrightUnit,
      ?_, ?_, ?_⟩
    · have hsTarget' : supportTriple.1 = target := by
        simpa [Nat.mod_eq_of_lt hsLabelBound] using hsTarget
      exact hlabelProjection.trans hsTarget'
    · rw [labelFiber_switchedHits_eq_of_support_mod
        S b (2 * (a * left))
          (2 * (a * supportTriple.2.1))
            ((hleftEq.mul_left a).mul_left 2)]
      exact hsLeftSwitch
    · rw [labelFiber_switchedHits_eq_of_support_mod
        S b (2 * (2 * d * right))
          (2 * (2 * d * supportTriple.2.2))
            ((hrightEq.mul_left (2 * d)).mul_left 2)]
      exact hsRightSwitch
    · have hmiddle :
          Nat.ModEq W
            (a * supportTriple.2.1 + supportTriple.1)
              (2 * d * supportTriple.2.2) := hsCompatible
      exact ((hleftEq.mul_left a).add hlabelEq).trans
        (hmiddle.trans (hrightEq.mul_left (2 * d)).symm)

/-- The COMPLETE signed actual three-cell phase over ONE true compatible
support fiber factors into exactly the three genuine outside unit-residue
Ramanujan sums.  Both original switched masks and all full-modulus unit
filters are retained in the fiber definition. -/
theorem actualMajorArcParity_support_fiber_phase_sum
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d outside numerator : ℕ)
    (supportTriple : ℕ × ℕ × ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (houtside : 0 < outside)
    (hcoprime : Nat.Coprime (∏ p ∈ S, p) outside)
    (htriple : supportTriple ∈
      actualMajorArcSupportCompatibleCellTriples S b target a d) :
    (∑ triple ∈ (actualMajorArcParityCompatibleFullCellTriples
        S b target a d outside).filter
        (fun triple =>
          (triple.1 % (∏ p ∈ S, p),
            triple.2.1 % (∏ p ∈ S, p),
            triple.2.2 % (∏ p ∈ S, p)) = supportTriple),
      actualMajorArcSquarefreeTriplePhase
        triple.1 triple.2.1 triple.2.2 a d
          ((numerator : ℝ) / outside)) =
      actualMajorArcGenericPrimeCenterPhase outside a d numerator := by
  let W := ∏ p ∈ S, p
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).pos
  obtain ⟨hsLabelBound, hsLeftBound, hsRightBound,
    _, hsLabelUnit, hsLeftUnit, hsRightUnit, _⟩ :=
      (actualMajorArcSupportCompatibleCellTriples_mem_iff
        S b target a d supportTriple).mp htriple
  let labels := actualMajorArcParitySupportUnitLift
    W outside supportTriple.1
  let lefts := actualMajorArcParitySupportUnitLift
    W outside supportTriple.2.1
  let rights := actualMajorArcParitySupportUnitLift
    W outside supportTriple.2.2
  let F : ℕ → ℂ := fun label =>
    GoldbachChain.e (((numerator : ℝ) * label) / outside)
  let G : ℕ → ℂ := fun left =>
    GoldbachChain.e
      (((((a * numerator : ℕ) : ℤ) : ℝ) * left) / outside)
  let H : ℕ → ℂ := fun right =>
    GoldbachChain.e
      ((((-(2 * d * numerator : ℕ) : ℤ) : ℝ) * right) / outside)
  have hphase (label left right : ℕ) :
      actualMajorArcSquarefreeTriplePhase label left right a d
          ((numerator : ℝ) / outside) =
        F label * G left * H right := by
    unfold actualMajorArcSquarefreeTriplePhase
    dsimp [F, G, H]
    congr 1 <;> push_cast <;> ring
  rw [actualMajorArcParity_full_triple_fiber_eq_unit_lifts
    S b target a d outside supportTriple hsupport hcoprime htriple]
  change
    (∑ triple ∈ labels.product (lefts.product rights),
      actualMajorArcSquarefreeTriplePhase
        triple.1 triple.2.1 triple.2.2 a d
          ((numerator : ℝ) / outside)) =
      actualMajorArcGenericPrimeCenterPhase outside a d numerator
  simp_rw [hphase]
  have hfactor :
      (∑ triple ∈ labels.product (lefts.product rights),
        F triple.1 * G triple.2.1 * H triple.2.2) =
        (∑ label ∈ labels, F label) *
          (∑ left ∈ lefts, G left) *
          (∑ right ∈ rights, H right) := by
    simp [Finset.sum_product, Finset.mul_sum, Finset.sum_mul]
    calc
      _ = ∑ label ∈ labels, ∑ right ∈ rights, ∑ left ∈ lefts,
          F label * G left * H right := by
        apply Finset.sum_congr rfl
        intro label hlabel
        exact Finset.sum_comm
      _ = ∑ right ∈ rights, ∑ label ∈ labels, ∑ left ∈ lefts,
          F label * G left * H right := by
        exact Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro right hright
        exact Finset.sum_comm
  rw [hfactor]
  have hlabel := actualMajorArcParitySupportUnitLift_phase
    W outside supportTriple.1 (numerator : ℤ)
      hW houtside hcoprime hsLabelBound hsLabelUnit
  simp only [Int.cast_natCast] at hlabel
  have hleft := actualMajorArcParitySupportUnitLift_phase
    W outside supportTriple.2.1 ((a * numerator : ℕ) : ℤ)
      hW houtside hcoprime hsLeftBound hsLeftUnit
  have hright := actualMajorArcParitySupportUnitLift_phase
    W outside supportTriple.2.2 (-(2 * d * numerator : ℕ) : ℤ)
      hW houtside hcoprime hsRightBound hsRightUnit
  change
    (∑ label ∈ labels, F label) *
      (∑ left ∈ lefts, G left) *
      (∑ right ∈ rights, H right) =
        actualMajorArcGenericPrimeCenterPhase outside a d numerator
  change
    (∑ label ∈ actualMajorArcParitySupportUnitLift
        W outside supportTriple.1,
      GoldbachChain.e (((numerator : ℝ) * label) / outside)) *
      (∑ left ∈ actualMajorArcParitySupportUnitLift
          W outside supportTriple.2.1,
        GoldbachChain.e
          (((((a * numerator : ℕ) : ℤ) : ℝ) * left) / outside)) *
      (∑ right ∈ actualMajorArcParitySupportUnitLift
          W outside supportTriple.2.2,
        GoldbachChain.e
          ((((-(2 * d * numerator : ℕ) : ℤ) : ℝ) * right) / outside)) =
        actualMajorArcGenericPrimeCenterPhase outside a d numerator
  rw [hlabel, hleft, hright]
  rfl

/-- Exact COMPLETE actual support/outside CRT factorization: the signed
phase of EVERY true compatible full-common-modulus switched/unit triple is
the actual support-selector cardinality times the ORIGINAL outside
three-frequency rational phase.  No independence or selector assumption
is made. -/
theorem actualMajorArcParity_full_compatible_phase_sum
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d outside numerator : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (houtside : 0 < outside)
    (hcoprime : Nat.Coprime (∏ p ∈ S, p) outside) :
    (∑ triple ∈ actualMajorArcParityCompatibleFullCellTriples
        S b target a d outside,
      actualMajorArcSquarefreeTriplePhase
        triple.1 triple.2.1 triple.2.2 a d
          ((numerator : ℝ) / outside)) =
      (((actualMajorArcSupportCompatibleCellTriples
        S b target a d).card : ℕ) : ℂ) *
          actualMajorArcGenericPrimeCenterPhase
            outside a d numerator := by
  let W := ∏ p ∈ S, p
  let full := actualMajorArcParityCompatibleFullCellTriples
    S b target a d outside
  let support := actualMajorArcSupportCompatibleCellTriples
    S b target a d
  let projection : (ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ) :=
    fun triple =>
      (triple.1 % W, triple.2.1 % W, triple.2.2 % W)
  let phase : (ℕ × ℕ × ℕ) → ℂ := fun triple =>
    actualMajorArcSquarefreeTriplePhase
      triple.1 triple.2.1 triple.2.2 a d
        ((numerator : ℝ) / outside)
  have hmap : ∀ triple ∈ full, projection triple ∈ support := by
    intro triple htriple
    exact actualMajorArcParity_full_triple_support_reduction_mem
      S b target a d outside triple hsupport htriple
  change
    (∑ triple ∈ full, phase triple) =
      (support.card : ℂ) *
        actualMajorArcGenericPrimeCenterPhase outside a d numerator
  calc
    (∑ triple ∈ full, phase triple) =
        ∑ supportTriple ∈ support,
          ∑ triple ∈ full with projection triple = supportTriple,
            phase triple :=
      (Finset.sum_fiberwise_of_maps_to hmap phase).symm
    _ = ∑ _supportTriple ∈ support,
          actualMajorArcGenericPrimeCenterPhase
            outside a d numerator := by
      apply Finset.sum_congr rfl
      intro supportTriple htriple
      exact actualMajorArcParity_support_fiber_phase_sum
        S b target a d outside numerator supportTriple
          hsupport houtside hcoprime htriple
    _ = (support.card : ℂ) *
          actualMajorArcGenericPrimeCenterPhase
            outside a d numerator := by
      simp

/-- Summing ALL genuine support-character shifts of the FULL ACTUAL
selected three-cell phase gives exactly `W * #supportSelectors` times the
original outside signed rational-center phase, for EVERY support-coprime
denominator, odd or parity-doubled. -/
theorem actualMajorArcParity_full_shifted_admissible_phase_sum
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d outside numerator : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (houtside : 0 < outside)
    (hcoprime : Nat.Coprime (∏ p ∈ S, p) outside) :
    (∑ shift ∈ Finset.range (∏ p ∈ S, p),
      ∑ triple ∈ actualMajorArcLcmAdmissibleCellTriples
          S b target a d outside,
        actualMajorArcSquarefreeTriplePhase
          triple.1 triple.2.1 triple.2.2 a d
          ((numerator : ℝ) / outside -
            (shift : ℝ) / (((∏ p ∈ S, p) : ℕ) : ℝ))) =
      (((∏ p ∈ S, p) : ℕ) : ℂ) *
        (((actualMajorArcSupportCompatibleCellTriples
          S b target a d).card : ℕ) : ℂ) *
        actualMajorArcGenericPrimeCenterPhase
          outside a d numerator := by
  have hprojection :=
    actualMajorArcSquarefree_admissible_triple_shift_projection
      S b target a d outside (numerator : ℤ) 0
      (fun _ => (1 : ℂ)) hsupport
  have hterms (triple : ℕ × ℕ × ℕ) :
      GoldbachChain.e
        (((actualMajorArcSquarefreeAffineDefect
          triple.1 triple.2.1 triple.2.2 a d : ℝ) *
            (numerator : ℤ)) / outside) =
        actualMajorArcSquarefreeTriplePhase
          triple.1 triple.2.1 triple.2.2 a d
            ((numerator : ℝ) / outside) := by
    rw [actualMajorArcSquarefreeTriplePhase_eq_defect_phase]
    congr 1
    push_cast
    ring
  simp only [Int.cast_natCast, Int.cast_zero, add_zero,
    one_mul] at hprojection
  simp only [Int.cast_natCast] at hterms
  rw [show
      (actualMajorArcLcmAdmissibleCellTriples
        S b target a d outside).filter
        (fun triple =>
          (a * triple.2.1 + triple.1) % (∏ p ∈ S, p) =
            (2 * d * triple.2.2) % (∏ p ∈ S, p)) =
        actualMajorArcParityCompatibleFullCellTriples
          S b target a d outside by rfl] at hprojection
  simp_rw [hterms] at hprojection
  rw [actualMajorArcParity_full_compatible_phase_sum
    S b target a d outside numerator
      hsupport houtside hcoprime] at hprojection
  simpa [mul_assoc] using hprojection

/-- The sum over ALL reduced rational numerators, ALL genuine support
shifts, and ALL actual switched/unit common-modulus cells factors exactly
into the real support-selector cardinality and the complete outside
three-form rational-center phase sum. -/
theorem actualMajorArcParity_full_shifted_numerator_phase_sum
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d outside : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (houtside : 0 < outside)
    (hcoprime : Nat.Coprime (∏ p ∈ S, p) outside) :
    (∑ numerator ∈ (Finset.range outside).filter
        (fun numerator => Nat.gcd numerator outside = 1),
      ∑ shift ∈ Finset.range (∏ p ∈ S, p),
        ∑ triple ∈ actualMajorArcLcmAdmissibleCellTriples
            S b target a d outside,
          actualMajorArcSquarefreeTriplePhase
            triple.1 triple.2.1 triple.2.2 a d
            ((numerator : ℝ) / outside -
              (shift : ℝ) / (((∏ p ∈ S, p) : ℕ) : ℝ))) =
      (((∏ p ∈ S, p) : ℕ) : ℂ) *
        (((actualMajorArcSupportCompatibleCellTriples
          S b target a d).card : ℕ) : ℂ) *
        (∑ numerator ∈ (Finset.range outside).filter
            (fun numerator => Nat.gcd numerator outside = 1),
          actualMajorArcGenericPrimeCenterPhase
            outside a d numerator) := by
  simp_rw [actualMajorArcParity_full_shifted_admissible_phase_sum
    S b target a d outside _ hsupport houtside hcoprime]
  rw [Finset.mul_sum]

/-- Exact normalized FULL ACTUAL support/outside CRT separation.  The
common-modulus denominator is precisely `φ(lcm(q,W))³`; the resulting
factors are the genuine support selector density and the complete signed
three-coordinate outside center correction.  Works for odd and parity
doubled denominators alike. -/
theorem actualMajorArcParity_full_shifted_normalized_CRT
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d outside : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (houtside : 0 < outside)
    (hcoprime : Nat.Coprime (∏ p ∈ S, p) outside) :
    (∑ numerator ∈ (Finset.range outside).filter
        (fun numerator => Nat.gcd numerator outside = 1),
      ∑ shift ∈ Finset.range (∏ p ∈ S, p),
        ∑ triple ∈ actualMajorArcLcmAdmissibleCellTriples
            S b target a d outside,
          actualMajorArcSquarefreeTriplePhase
            triple.1 triple.2.1 triple.2.2 a d
            ((numerator : ℝ) / outside -
              (shift : ℝ) / (((∏ p ∈ S, p) : ℕ) : ℝ))) /
        (Nat.totient
          (actualMajorArcLcmResidueModulus S outside) : ℂ) ^ 3 =
      ((((actualMajorArcSupportCompatibleCellTriples
          S b target a d).card : ℕ) : ℂ) *
        (((∏ p ∈ S, p) : ℕ) : ℂ) /
          (Nat.totient (∏ p ∈ S, p) : ℂ) ^ 3) *
        ((∑ numerator ∈ (Finset.range outside).filter
            (fun numerator => Nat.gcd numerator outside = 1),
          actualMajorArcGenericPrimeCenterPhase
            outside a d numerator) /
              (Nat.totient outside : ℂ) ^ 3) := by
  let W := ∏ p ∈ S, p
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).pos
  have hmodulus : actualMajorArcLcmResidueModulus S outside =
      W * outside := by
    unfold actualMajorArcLcmResidueModulus
    rw [hcoprime.symm.lcm_eq_mul]
    exact Nat.mul_comm outside W
  have hphiW : (Nat.totient W : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hW).ne'
  have hphiOutside : (Nat.totient outside : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr houtside).ne'
  rw [actualMajorArcParity_full_shifted_numerator_phase_sum
    S b target a d outside hsupport houtside hcoprime,
    hmodulus, Nat.totient_mul hcoprime]
  push_cast
  field_simp

/-- The COMPLETE TRUE normalized signed local factor at an odd
outside-support rational denominator: ALL actual support shifts, true
three-cell selectors, reduced numerators, and `φ(lcm(q,W))³` density give
exactly `(a*d*actualWeight/φ(W)) * μ(q)/φ(q)²`. -/
theorem actualMajorArcParity_actual_odd_center_normalized_factor
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d outside : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (ha : a ∣ ∏ p ∈ S, p)
    (hd : d ∣ ∏ p ∈ S, p)
    (hcoefficient : Nat.Coprime a d)
    (htargetRange : target < ∏ p ∈ S, p)
    (htarget : ∀ p ∈ S, ¬ p ∣ target)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (houtside : 0 < outside)
    (hcoprime : Nat.Coprime (∏ p ∈ S, p) outside)
    (houtsideCoefficients : Nat.Coprime outside (2 * a * d)) :
    (∑ numerator ∈ (Finset.range outside).filter
        (fun numerator => Nat.gcd numerator outside = 1),
      ∑ shift ∈ Finset.range (∏ p ∈ S, p),
        ∑ triple ∈ actualMajorArcLcmAdmissibleCellTriples
            S b target a d outside,
          actualMajorArcSquarefreeTriplePhase
            triple.1 triple.2.1 triple.2.2 a d
            ((numerator : ℝ) / outside -
              (shift : ℝ) / (((∏ p ∈ S, p) : ℕ) : ℝ))) /
        (Nat.totient
          (actualMajorArcLcmResidueModulus S outside) : ℂ) ^ 3 =
      (((a : ℂ) * d *
        (actualFixedLabelDoubleCoefficientWeight S target b a d : ℂ)) /
          (Nat.totient (∏ p ∈ S, p) : ℂ)) *
        ((ArithmeticFunction.moebius outside : ℂ) /
          (Nat.totient outside : ℂ) ^ 2) := by
  rw [actualMajorArcParity_full_shifted_normalized_CRT
    S b target a d outside (fun p hp => (hsupport p hp).1)
      houtside hcoprime,
    actualMajorArcCompositeCenter_signed_correction
      outside a d houtside houtsideCoefficients]
  congr 1
  have hreal :=
    actualMajorArcSupportCompatibleCellTriples_compensated_normalization
      S b target a d hsupport ha hd hcoefficient htargetRange htarget hb
  have hcomplex := congrArg (fun value : ℝ => (value : ℂ)) hreal
  push_cast at hcomplex
  simpa only [Nat.cast_prod] using hcomplex

/-- The COMPLETE TRUE normalized signed local factor at a genuine
parity-doubled outside denominator `2*r`: ALL actual support shifts,
three true switched/unit cell filters, reduced rational numerators, the
NONUNIT doubled right frequency, and the exact full common-modulus density
give the SAME factor `(a*d*actualWeight/φ(W))*μ(r)/φ(r)²`. -/
theorem actualMajorArcParity_actual_doubled_center_normalized_factor
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d outside : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (ha : a ∣ ∏ p ∈ S, p)
    (hd : d ∣ ∏ p ∈ S, p)
    (hcoefficient : Nat.Coprime a d)
    (htargetRange : target < ∏ p ∈ S, p)
    (htarget : ∀ p ∈ S, ¬ p ∣ target)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (houtside : 0 < outside)
    (hodd : Nat.Coprime 2 outside)
    (hcoprime : Nat.Coprime (∏ p ∈ S, p) outside)
    (houtsideCoefficients : Nat.Coprime outside (2 * a * d)) :
    (∑ numerator ∈ (Finset.range (2 * outside)).filter
        (fun numerator => Nat.gcd numerator (2 * outside) = 1),
      ∑ shift ∈ Finset.range (∏ p ∈ S, p),
        ∑ triple ∈ actualMajorArcLcmAdmissibleCellTriples
            S b target a d (2 * outside),
          actualMajorArcSquarefreeTriplePhase
            triple.1 triple.2.1 triple.2.2 a d
            ((numerator : ℝ) / (((2 * outside : ℕ) : ℝ)) -
              (shift : ℝ) / (((∏ p ∈ S, p) : ℕ) : ℝ))) /
        (Nat.totient
          (actualMajorArcLcmResidueModulus S (2 * outside)) : ℂ) ^ 3 =
      (((a : ℂ) * d *
        (actualFixedLabelDoubleCoefficientWeight S target b a d : ℂ)) /
          (Nat.totient (∏ p ∈ S, p) : ℂ)) *
        ((ArithmeticFunction.moebius outside : ℂ) /
          (Nat.totient outside : ℂ) ^ 2) := by
  have hWtwo : Nat.Coprime (∏ p ∈ S, p) 2 :=
    oddSupportDivisor_coprime_two
      S (∏ p ∈ S, p) hsupport (dvd_refl _)
  have hWoutside : Nat.Coprime (∏ p ∈ S, p) (2 * outside) :=
    (Nat.coprime_mul_iff_right).mpr ⟨hWtwo, hcoprime⟩
  have haodd : Nat.Coprime a 2 :=
    oddSupportDivisor_coprime_two S a hsupport ha
  rw [actualMajorArcParity_full_shifted_normalized_CRT
    S b target a d (2 * outside) (fun p hp => (hsupport p hp).1)
      (by omega) hWoutside,
    actualMajorArcParity_doubled_center_signed_correction
      outside a d houtside hodd haodd houtsideCoefficients]
  congr 1
  have hreal :=
    actualMajorArcSupportCompatibleCellTriples_compensated_normalization
      S b target a d hsupport ha hd hcoefficient htargetRange htarget hb
  have hcomplex := congrArg (fun value : ℝ => (value : ℂ)) hreal
  push_cast at hcomplex
  simpa only [Nat.cast_prod] using hcomplex

/-- Every genuine switched support modulus is odd, including the empty
support modulus one. -/
theorem actualMajorArcParity_support_coprime_two
    (S : Finset ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p) :
    Nat.Coprime (∏ p ∈ S, p) 2 := by
  exact oddSupportDivisor_coprime_two
    S (∏ p ∈ S, p) hsupport (dvd_refl _)

/-- At EVERY denominator divisible by four, the exact full common
modulus still contains the complete odd support after division by two. -/
theorem actualMajorArcParity_support_dvd_lcm_div_two
    (S : Finset ℕ) (denominator : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hfour : 4 ∣ denominator) :
    (∏ p ∈ S, p) ∣
      actualMajorArcLcmResidueModulus S denominator / 2 := by
  let W := ∏ p ∈ S, p
  let L := actualMajorArcLcmResidueModulus S denominator
  have hdenominator : denominator ∣ L :=
    (actualMajorArcLcmResidueModulus_divisibility S denominator).1
  have hW : W ∣ L :=
    (actualMajorArcLcmResidueModulus_divisibility S denominator).2
  have htwo : 2 ∣ L :=
    dvd_trans (dvd_trans (by norm_num : 2 ∣ 4) hfour) hdenominator
  have hcoprime : Nat.Coprime W 2 :=
    actualMajorArcParity_support_coprime_two S hsupport
  have hproduct : W * 2 ∣ L :=
    hcoprime.mul_dvd_of_dvd_of_dvd hW htwo
  exact (Nat.dvd_div_iff_mul_dvd htwo).mpr
    (by simpa [W, Nat.mul_comm] using hproduct)

/-- The true support quotient of a common modulus at a four-divisible
denominator remains divisible by four; no coprimality of denominator and
support is assumed. -/
theorem actualMajorArcParity_four_dvd_lcm_div_support
    (S : Finset ℕ) (denominator : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hfour : 4 ∣ denominator) :
    4 ∣ actualMajorArcLcmResidueModulus S denominator /
      (∏ p ∈ S, p) := by
  let W := ∏ p ∈ S, p
  let L := actualMajorArcLcmResidueModulus S denominator
  have hdenominator : denominator ∣ L :=
    (actualMajorArcLcmResidueModulus_divisibility S denominator).1
  have hW : W ∣ L :=
    (actualMajorArcLcmResidueModulus_divisibility S denominator).2
  have hfourL : 4 ∣ L := dvd_trans hfour hdenominator
  have htwo : Nat.Coprime 2 W :=
    (actualMajorArcParity_support_coprime_two S hsupport).symm
  have hfourCoprime : Nat.Coprime 4 W := by
    simpa using htwo.pow_left 2
  have hproduct : 4 * W ∣ L :=
    hfourCoprime.mul_dvd_of_dvd_of_dvd hfourL hW
  exact (Nat.dvd_div_iff_mul_dvd hW).mpr
    (by simpa [Nat.mul_comm] using hproduct)

/-- Squarefreeness of the actual switched support forces the denominator
lift `lcm(q,W)/q` to be odd whenever `4 ∣ q`. -/
theorem actualMajorArcParity_lcm_denominator_lift_odd
    (S : Finset ℕ) (denominator : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hdenominator : 0 < denominator)
    (hfour : 4 ∣ denominator) :
    ¬ 2 ∣ actualMajorArcLcmResidueModulus S denominator / denominator := by
  let W := ∏ p ∈ S, p
  have hsquarefree : Squarefree W :=
    Sieve.prodDistinctPrimes_squarefree S
      (fun p hp => (hsupport p hp).1)
  have hcoprime :=
    actualMajorArcMixedConductor_lcm_div_coprime_denominator
      W denominator hsquarefree hdenominator
  have htwo : 2 ∣ denominator :=
    dvd_trans (by norm_num : 2 ∣ 4) hfour
  have hliftTwo :
      Nat.Coprime
        (actualMajorArcLcmResidueModulus S denominator / denominator) 2 :=
    hcoprime.coprime_dvd_right htwo
  exact (Nat.prime_two.coprime_iff_not_dvd).mp hliftTwo.symm

/-- The ENTIRE true shifted common-modulus numerator is odd at every
four-divisible denominator, including arbitrary support shifts and integer
periodic lifts. -/
theorem actualMajorArcParity_shifted_numerator_not_even
    (S : Finset ℕ) (denominator numerator : ℕ)
    (shift lift : ℤ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hdenominator : 0 < denominator)
    (hfour : 4 ∣ denominator)
    (hnumerator : Nat.Coprime numerator denominator) :
    ¬ (2 : ℤ) ∣
      actualMajorArcSingularShiftedNumerator
        S denominator numerator shift lift := by
  let W := ∏ p ∈ S, p
  let L := actualMajorArcLcmResidueModulus S denominator
  have hdenominatorDivides : denominator ∣ L :=
    (actualMajorArcLcmResidueModulus_divisibility S denominator).1
  have htwoDenominator : 2 ∣ denominator :=
    dvd_trans (by norm_num : 2 ∣ 4) hfour
  have htwoL : 2 ∣ L := dvd_trans htwoDenominator hdenominatorDivides
  have htwoSupportLift : 2 ∣ L / W :=
    dvd_trans (by norm_num : 2 ∣ 4)
      (actualMajorArcParity_four_dvd_lcm_div_support
        S denominator hsupport hfour)
  have hnumeratorTwo : Nat.Coprime numerator 2 :=
    hnumerator.coprime_dvd_right htwoDenominator
  have hnumeratorOdd : ¬ 2 ∣ numerator :=
    (Nat.prime_two.coprime_iff_not_dvd).mp hnumeratorTwo.symm
  have hliftOdd : ¬ 2 ∣ L / denominator :=
    actualMajorArcParity_lcm_denominator_lift_odd
      S denominator hsupport hdenominator hfour
  have hproductOdd : ¬ 2 ∣ numerator * (L / denominator) := by
    intro hproduct
    rcases (Nat.prime_two.dvd_mul).mp hproduct with hfirst | hsecond
    · exact hnumeratorOdd hfirst
    · exact hliftOdd hsecond
  have hsupportLiftInt : (2 : ℤ) ∣ ((L / W : ℕ) : ℤ) := by
    exact_mod_cast htwoSupportLift
  have hmodulusInt : (2 : ℤ) ∣ (L : ℤ) := by
    exact_mod_cast htwoL
  have hshift : (2 : ℤ) ∣ shift * ((L / W : ℕ) : ℤ) :=
    dvd_mul_of_dvd_right hsupportLiftInt shift
  have hperiodic : (2 : ℤ) ∣ lift * (L : ℤ) :=
    dvd_mul_of_dvd_right hmodulusInt lift
  intro hfrequency
  have hidentity :
      actualMajorArcSingularShiftedNumerator
          S denominator numerator shift lift -
        lift * (L : ℤ) + shift * ((L / W : ℕ) : ℤ) =
          (numerator : ℤ) * ((L / denominator : ℕ) : ℤ) := by
    simp [actualMajorArcSingularShiftedNumerator, L, W]
  have hproductInt :
      (2 : ℤ) ∣ (numerator : ℤ) * ((L / denominator : ℕ) : ℤ) := by
    rw [← hidentity]
    exact dvd_add (dvd_sub hfrequency hperiodic) hshift
  have hproductNat : 2 ∣ numerator * (L / denominator) := by
    exact_mod_cast hproductInt
  exact hproductOdd hproductNat

/-- The ORIGINAL fixed-label support-residue phase cancels at every
four-divisible mixed denominator while preserving the FULL common-modulus
UNIT filter, all support shifts, and all periodic lifts. -/
theorem actualMajorArcParity_shifted_unit_label_phase_zero_of_four_dvd
    (S : Finset ℕ)
    (denominator numerator target : ℕ)
    (shift lift : ℤ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hdenominator : 0 < denominator)
    (hfour : 4 ∣ denominator)
    (hnumerator : Nat.Coprime numerator denominator) :
    (∑ label ∈ actualMajorArcSingularLabelResidues
        S target denominator,
      GoldbachChain.e
        (((label : ℝ) *
          actualMajorArcSingularShiftedNumerator
            S denominator numerator shift lift) /
              actualMajorArcLcmResidueModulus S denominator)) = 0 := by
  let W := ∏ p ∈ S, p
  let L := actualMajorArcLcmResidueModulus S denominator
  have hL : 0 < L :=
    actualMajorArcLcmResidueModulus_pos
      S denominator hdenominator (fun p hp => (hsupport p hp).1)
  have hdenominatorDivides : denominator ∣ L :=
    (actualMajorArcLcmResidueModulus_divisibility S denominator).1
  have hfourL : 2 ^ 2 ∣ L := by
    have h := dvd_trans hfour hdenominatorDivides
    simpa using h
  have hsupportBlock : W ∣ L / 2 :=
    actualMajorArcParity_support_dvd_lcm_div_two
      S denominator hsupport hfour
  have hfrequency :
      ¬ (2 : ℤ) ∣
        actualMajorArcSingularShiftedNumerator
          S denominator numerator shift lift :=
    actualMajorArcParity_shifted_numerator_not_even
      S denominator numerator shift lift hsupport
        hdenominator hfour hnumerator
  have hzero :=
    actualMajorArcUnitOrbit_weighted_support_unit_phase_sum_zero
      W L 2 target
      (actualMajorArcSingularShiftedNumerator
        S denominator numerator shift lift)
      (fun _ => (1 : ℂ)) Nat.prime_two hL hfourL hsupportBlock
        hfrequency (by intros; rfl)
  simpa [actualMajorArcSingularLabelResidues,
    L, W, mul_comm] using hzero

/-- The COMPLETE genuine three-coordinate switched-unit phase is zero at
every denominator divisible by four.  This includes the actual robust label,
both switched masks, all support shifts, and all outside conductor factors. -/
theorem actualMajorArcParity_admissible_phase_zero_of_four_dvd
    (S : Finset ℕ) (b : ℕ → ℕ)
    (denominator numerator target a d : ℕ)
    (shift lift : ℤ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hdenominator : 0 < denominator)
    (hfour : 4 ∣ denominator)
    (hnumerator : Nat.Coprime numerator denominator) :
    (∑ triple ∈ actualMajorArcLcmAdmissibleCellTriples
        S b target a d denominator,
      actualMajorArcArchimedeanCellPhase
        (actualMajorArcLcmResidueModulus S denominator)
        triple.1 triple.2.1 triple.2.2 a d
        (actualMajorArcSingularShiftedNumerator
          S denominator numerator shift lift)) = 0 := by
  rw [actualMajorArcSingular_admissible_phase_eq_three_unit_sums]
  rw [actualMajorArcParity_shifted_unit_label_phase_zero_of_four_dvd
    S denominator numerator target shift lift
      hsupport hdenominator hfour hnumerator]
  ring

/-- Every higher parity conductor annihilates the ENTIRE ACTUAL signed
switched-unit smooth cubic, pointwise at every genuine shifted center. -/
theorem actualMajorArcParity_admissible_smooth_zero_of_four_dvd
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n denominator numerator target a d : ℕ)
    (shift lift : ℤ) (τ ell β : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hdenominator : 0 < denominator)
    (hfour : 4 ∣ denominator)
    (hnumerator : Nat.Coprime numerator denominator) :
    (∑ triple ∈ actualMajorArcLcmAdmissibleCellTriples
        S b target a d denominator,
      actualMajorArcLcmSmoothCellCubic
        S n a d denominator triple.1 triple.2.1 triple.2.2
        τ ell
        (actualMajorArcSingularShiftedNumerator
          S denominator numerator shift lift) β) = 0 := by
  rw [actualMajorArcSingular_admissible_smooth_eq_phase_cubic]
  rw [actualMajorArcParity_admissible_phase_zero_of_four_dvd
    S b denominator numerator target a d shift lift
      hsupport hdenominator hfour hnumerator]
  ring

#print axioms Erdos689.actualMajorArcParity_even_companion_filter
#print axioms Erdos689.actualMajorArcParitySharpPartial_eq_actual_cutoffs
#print axioms Erdos689.actualMajorArcParityOutsidePartial_eq_half_add_shell
#print axioms Erdos689.actualMajorArcParitySharpPartial_sub_doubled_eq_neg_shell
#print axioms Erdos689.actualMajorArcParity_half_cutoff_tendsto_atTop
#print axioms Erdos689.actualMajorArcParity_half_series_tendsto
#print axioms Erdos689.actualMajorArcParitySharpPartial_tendsto
#print axioms Erdos689.actualMajorArcParitySharpPartial_sub_doubled_tendsto_zero
#print axioms Erdos689.actualMajorArcParity_compatible_cutoff_discrepancy_tendsto_zero
#print axioms Erdos689.actualMajorArcParitySharpPartial_eventually_ge_half
#print axioms Erdos689.actualMajorArcParity_compatible_cutoff_ge_half
#print axioms Erdos689.actualMajorArcParity_unit_phase_zero_of_four_dvd
#print axioms Erdos689.actualMajorArcParity_unit_phase_neg_nat_eq
#print axioms Erdos689.actualMajorArcParity_doubled_right_phase
#print axioms Erdos689.actualMajorArcParity_doubled_center_phase
#print axioms Erdos689.actualMajorArcParity_doubled_center_phase_sum
#print axioms Erdos689.actualMajorArcParity_doubled_center_signed_correction
#print axioms Erdos689.actualMajorArcParity_phase_eq_mod
#print axioms Erdos689.actualMajorArcParity_coprime_support_unit_lift_phase
#print axioms Erdos689.actualMajorArcParitySupportUnitLift_phase
#print axioms Erdos689.actualMajorArcParityCompatibleFullCellTriples_mem_iff
#print axioms Erdos689.actualMajorArcParity_full_triple_support_reduction_mem
#print axioms Erdos689.actualMajorArcParity_full_triple_fiber_eq_unit_lifts
#print axioms Erdos689.actualMajorArcParity_support_fiber_phase_sum
#print axioms Erdos689.actualMajorArcParity_full_compatible_phase_sum
#print axioms Erdos689.actualMajorArcParity_full_shifted_admissible_phase_sum
#print axioms Erdos689.actualMajorArcParity_full_shifted_numerator_phase_sum
#print axioms Erdos689.actualMajorArcParity_full_shifted_normalized_CRT
#print axioms Erdos689.actualMajorArcParity_actual_odd_center_normalized_factor
#print axioms Erdos689.actualMajorArcParity_actual_doubled_center_normalized_factor
#print axioms Erdos689.actualMajorArcParity_support_coprime_two
#print axioms Erdos689.actualMajorArcParity_support_dvd_lcm_div_two
#print axioms Erdos689.actualMajorArcParity_four_dvd_lcm_div_support
#print axioms Erdos689.actualMajorArcParity_lcm_denominator_lift_odd
#print axioms Erdos689.actualMajorArcParity_shifted_numerator_not_even
#print axioms Erdos689.actualMajorArcParity_shifted_unit_label_phase_zero_of_four_dvd
#print axioms Erdos689.actualMajorArcParity_admissible_phase_zero_of_four_dvd
#print axioms Erdos689.actualMajorArcParity_admissible_smooth_zero_of_four_dvd

end Erdos689
