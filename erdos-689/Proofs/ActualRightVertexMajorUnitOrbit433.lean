module

public import ActualRightVertexMajorSquarefreeSupport433
public import ActualMajorArcPositivityArchimedean433

@[expose] public section


/-!
# Unit-filter-preserving mixed support-conductor cancellation

At a denominator containing the square of a switched-support prime, the
complete label residue-cell phase vanishes.  The actual major-arc model,
however, retains only labels coprime to its full common modulus.  We preserve
that exact unit filter by decomposing each common-modulus residue into a
base residue and a complete support-prime orbit.  Every orbit preserves both
the switched-support residue and common-modulus coprimality, while its true
shifted additive phase cancels.  Arbitrary orbit-invariant weights are also
permitted; no signed major-arc contribution is silently discarded.
-/

open Finset
open scoped BigOperators

namespace Erdos689

/-- Exact block/orbit reindexing of a complete natural residue interval. -/
theorem actualMajorArcUnitOrbit_sum_range_mul
    (block count : ℕ) (hblock : 0 < block) (f : ℕ → ℂ) :
    (∑ t ∈ Finset.range (block * count), f t) =
      ∑ u ∈ Finset.range block, ∑ j ∈ Finset.range count,
        f (u + block * j) := by
  classical
  have hflatten :
      (∑ u ∈ Finset.range block, ∑ j ∈ Finset.range count,
        f (u + block * j)) =
      ∑ pair ∈ (Finset.range block).product (Finset.range count),
        f (pair.1 + block * pair.2) := by
    simp [Finset.sum_product]
  rw [hflatten]
  symm
  apply Finset.sum_bij
    (fun pair _ => pair.1 + block * pair.2)
  · intro pair hpair
    obtain ⟨hu, hj⟩ := Finset.mem_product.mp hpair
    have huless := Finset.mem_range.mp hu
    have hjless := Finset.mem_range.mp hj
    apply Finset.mem_range.mpr
    calc
      pair.1 + block * pair.2 < block + block * pair.2 := by omega
      _ = block * (pair.2 + 1) := by ring
      _ ≤ block * count := Nat.mul_le_mul_left block (by omega)
  · intro x hx y hy hequal
    have hxfirst : x.1 < block :=
      Finset.mem_range.mp (Finset.mem_product.mp hx).1
    have hyfirst : y.1 < block :=
      Finset.mem_range.mp (Finset.mem_product.mp hy).1
    have hmod := congrArg (fun t : ℕ => t % block) hequal
    have hfirst : x.1 = y.1 := by
      simpa [Nat.add_mod, Nat.mod_eq_of_lt hxfirst,
        Nat.mod_eq_of_lt hyfirst] using hmod
    have hsecond : x.2 = y.2 := by
      apply Nat.eq_of_mul_eq_mul_left hblock
      apply Nat.add_left_cancel (n := x.1)
      simpa [hfirst] using hequal
    exact Prod.ext hfirst hsecond
  · intro t ht
    have htless := Finset.mem_range.mp ht
    have hfirst : t % block < block := Nat.mod_lt t hblock
    have hsecond : t / block < count := by
      apply (Nat.div_lt_iff_lt_mul hblock).mpr
      simpa [Nat.mul_comm] using htless
    refine ⟨(t % block, t / block),
      Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hfirst,
          Finset.mem_range.mpr hsecond⟩, ?_⟩
    exact Nat.mod_add_div t block
  · intro pair hpair
    rfl

/-- A full support-prime orbit preserves the exact fixed support residue. -/
theorem actualMajorArcUnitOrbit_support_residue_add_block
    (support block u j : ℕ) (hdivide : support ∣ block) :
    (u + block * j) % support = u % support := by
  simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd hdivide]

/-- If the orbit block is already divisible by its prime, translating along
the complete prime orbit preserves coprimality with the FULL common modulus. -/
theorem actualMajorArcUnitOrbit_coprime_add_block_iff
    (p block u j : ℕ) (hdivide : p ∣ block) :
    Nat.Coprime (u + block * j) (p * block) ↔
      Nat.Coprime u (p * block) := by
  obtain ⟨m, hm⟩ := hdivide
  rw [Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right]
  constructor
  · rintro ⟨hp, hblock⟩
    refine ⟨?_, ?_⟩
    · have hreindex : u + block * j = u + p * (m * j) := by
        rw [hm]
        ring
      rw [hreindex] at hp
      exact (Nat.coprime_add_mul_left_left u p (m * j)).mp hp
    · exact (Nat.coprime_add_mul_left_left u block j).mp hblock
  · rintro ⟨hp, hblock⟩
    refine ⟨?_, ?_⟩
    · have hreindex : u + block * j = u + p * (m * j) := by
        rw [hm]
        ring
      rw [hreindex]
      exact (Nat.coprime_add_mul_left_left u p (m * j)).mpr hp
    · exact (Nat.coprime_add_mul_left_left u block j).mpr hblock

/-- The true integer-frequency phase along a complete prime orbit factors
into its fixed base phase and the primitive prime-conductor character. -/
theorem actualMajorArcUnitOrbit_phase_add_block
    (block p u j : ℕ) (frequency : ℤ)
    (hblock : 0 < block) (hp : 0 < p) :
    GoldbachChain.e
        (((frequency : ℝ) * (u + block * j)) / (block * p)) =
      GoldbachChain.e (((frequency : ℝ) * u) / (block * p)) *
        GoldbachChain.e (((frequency : ℝ) * j) / p) := by
  have hbReal : (block : ℝ) ≠ 0 := by exact_mod_cast hblock.ne'
  have hpReal : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [GoldbachChain.e_add]
  congr 1
  field_simp

/-- Exact cancellation over the TRUE support-fixed, common-modulus-unit
label cells, even with arbitrary weights invariant along the support-prime
orbits.  Outside-prime residue selectors can consequently be retained. -/
theorem actualMajorArcUnitOrbit_weighted_support_unit_phase_sum_zero
    (support modulus p residue : ℕ)
    (frequency : ℤ) (weight : ℕ → ℂ)
    (hp : p.Prime) (hmodulus : 0 < modulus)
    (hpSquare : p ^ 2 ∣ modulus)
    (hsupport : support ∣ modulus / p)
    (hfrequency : ¬ (p : ℤ) ∣ frequency)
    (hweight :
      ∀ u < modulus / p, ∀ j < p,
        weight (u + (modulus / p) * j) = weight u) :
    (∑ t ∈ (Finset.range modulus).filter
        (fun t => t % support = residue ∧ Nat.Coprime t modulus),
      weight t *
        GoldbachChain.e (((frequency : ℝ) * t) / modulus)) = 0 := by
  classical
  let block := modulus / p
  have hpModulus : p ∣ modulus :=
    dvd_trans (by simp : p ∣ p ^ 2) hpSquare
  have hfactor : block * p = modulus := by
    simpa [block, Nat.mul_comm] using
      (Nat.mul_div_cancel' hpModulus)
  have hblock : 0 < block := by
    apply Nat.div_pos
    · exact Nat.le_of_dvd hmodulus hpModulus
    · exact hp.pos
  have hpBlock : p ∣ block := by
    apply (Nat.dvd_div_iff_mul_dvd hpModulus).mpr
    simpa [pow_two] using hpSquare
  have hcharacter :
      (∑ j ∈ Finset.range p,
        GoldbachChain.e (((frequency : ℝ) * j) / p)) = 0 :=
    actualMajorArcMixedConductor_complete_int_phase_sum_zero
      p frequency hp.pos hfrequency
  rw [Finset.sum_filter]
  conv_lhs =>
    rw [← hfactor]
  rw [actualMajorArcUnitOrbit_sum_range_mul block p hblock]
  apply Finset.sum_eq_zero
  intro u hu
  have huBlock : u < block := Finset.mem_range.mp hu
  have horbit (j : ℕ) :
      (u + block * j) % support = u % support :=
    actualMajorArcUnitOrbit_support_residue_add_block
      support block u j hsupport
  have hunit (j : ℕ) :
      Nat.Coprime (u + block * j) (block * p) ↔
        Nat.Coprime u (block * p) := by
    simpa [Nat.mul_comm] using
      (actualMajorArcUnitOrbit_coprime_add_block_iff
        p block u j hpBlock)
  by_cases hbase : u % support = residue ∧
      Nat.Coprime u (block * p)
  · have hterm (j : ℕ) (hj : j ∈ Finset.range p) :
        (if (u + block * j) % support = residue ∧
            Nat.Coprime (u + block * j) (block * p) then
          weight (u + block * j) *
            GoldbachChain.e
              (((frequency : ℝ) * (u + block * j)) /
                (block * p)) else 0) =
          (weight u *
            GoldbachChain.e
              (((frequency : ℝ) * u) / (block * p))) *
            GoldbachChain.e (((frequency : ℝ) * j) / p) := by
      have hjless := Finset.mem_range.mp hj
      rw [if_pos (by simpa [horbit j, hunit j] using hbase)]
      rw [hweight u huBlock j hjless,
        actualMajorArcUnitOrbit_phase_add_block
          block p u j frequency hblock hp.pos]
      ring
    calc
      _ = ∑ j ∈ Finset.range p,
            (weight u *
              GoldbachChain.e
                (((frequency : ℝ) * u) / (block * p))) *
              GoldbachChain.e (((frequency : ℝ) * j) / p) := by
            apply Finset.sum_congr rfl
            intro j hj
            simpa [Nat.cast_add, Nat.cast_mul] using hterm j hj
      _ = (weight u *
            GoldbachChain.e
              (((frequency : ℝ) * u) / (block * p))) *
            ∑ j ∈ Finset.range p,
              GoldbachChain.e (((frequency : ℝ) * j) / p) := by
            rw [Finset.mul_sum]
      _ = 0 := by rw [hcharacter, mul_zero]
  · apply Finset.sum_eq_zero
    intro j hj
    rw [if_neg]
    simpa [horbit j, hunit j] using hbase

/-- At EVERY true mixed denominator carrying the square of a switched
support prime, the actual label phase cancels after retaining BOTH its
prescribed support residue and its full common-modulus unit condition.
All genuine character shifts and periodic lifts remain, and an arbitrary
orbit-invariant outside-residue weight is permitted. -/
theorem actualMajorArcUnitOrbit_actual_weighted_shifted_unit_label_sum_zero
    (S : Finset ℕ)
    (denominator p numerator target : ℕ)
    (shift lift : ℤ) (weight : ℕ → ℂ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hdenominator : 0 < denominator)
    (hpSupport : p ∈ S)
    (hpSquare : p ^ 2 ∣ denominator)
    (hnumerator : Nat.Coprime numerator denominator)
    (hweight :
      ∀ u < actualMajorArcLcmResidueModulus S denominator / p,
      ∀ j < p,
        weight
            (u + (actualMajorArcLcmResidueModulus S denominator / p) * j) =
          weight u) :
    (∑ t ∈ (Finset.range
        (actualMajorArcLcmResidueModulus S denominator)).filter
          (fun t => t % (∏ s ∈ S, s) = target ∧
            Nat.Coprime t (actualMajorArcLcmResidueModulus S denominator)),
      weight t *
        GoldbachChain.e
          (((((numerator : ℤ) *
                  ((actualMajorArcLcmResidueModulus S denominator /
                    denominator : ℕ) : ℤ) -
                shift *
                  ((actualMajorArcLcmResidueModulus S denominator /
                    (∏ s ∈ S, s) : ℕ) : ℤ) +
                lift *
                  (actualMajorArcLcmResidueModulus S denominator : ℤ) :
                    ℤ) : ℝ) * t) /
            (actualMajorArcLcmResidueModulus S denominator))) = 0 := by
  let W := ∏ s ∈ S, s
  let L := actualMajorArcLcmResidueModulus S denominator
  have hp : p.Prime := hsupport p hpSupport
  have hL : 0 < L := actualMajorArcLcmResidueModulus_pos
    S denominator hdenominator hsupport
  have hWsquare : Squarefree W :=
    Sieve.prodDistinctPrimes_squarefree S hsupport
  have hpW : p ∣ W :=
    Finset.dvd_prod_of_mem (fun s : ℕ => s) hpSupport
  have hdenominatorDivides : denominator ∣ L :=
    (actualMajorArcLcmResidueModulus_divisibility S denominator).1
  have hWdiv : W ∣ L :=
    (actualMajorArcLcmResidueModulus_divisibility S denominator).2
  have hpSquareL : p ^ 2 ∣ L := dvd_trans hpSquare hdenominatorDivides
  have hpL : p ∣ L :=
    dvd_trans (by simp : p ∣ p ^ 2) hpSquareL
  have hpLift : p ∣ L / W :=
    actualMajorArcMixedConductor_support_prime_dvd_lcm_support_lift
      W denominator p hp hWsquare hpW hpSquare
  have hproduct : W * p ∣ L :=
    (Nat.dvd_div_iff_mul_dvd hWdiv).mp hpLift
  have hWblock : W ∣ L / p := by
    apply (Nat.dvd_div_iff_mul_dvd hpL).mpr
    simpa [Nat.mul_comm] using hproduct
  have hnot : ¬ (p : ℤ) ∣
      (numerator : ℤ) * ((L / denominator : ℕ) : ℤ) -
        shift * ((L / W : ℕ) : ℤ) + lift * (L : ℤ) :=
    actualMajorArcMixedConductor_shifted_numerator_not_dvd
      W denominator p numerator shift lift hp hWsquare
        hdenominator hpW hpSquare hnumerator
  exact actualMajorArcUnitOrbit_weighted_support_unit_phase_sum_zero
    W L p target
      ((numerator : ℤ) * ((L / denominator : ℕ) : ℤ) -
        shift * ((L / W : ℕ) : ℤ) + lift * (L : ℤ))
      weight hp hL hpSquareL hWblock hnot hweight

/-- The exact ORIGINAL shifted mixed-conductor label cell cancels over its
TRUE unit-filtered residue set.  This repairs the gap in cancellation over
all residue lifts: the nonunit lifts are not assumed to be actual cells. -/
theorem actualMajorArcUnitOrbit_actual_shifted_unit_label_sum_zero
    (S : Finset ℕ)
    (denominator p numerator target : ℕ)
    (shift lift : ℤ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hdenominator : 0 < denominator)
    (hpSupport : p ∈ S)
    (hpSquare : p ^ 2 ∣ denominator)
    (hnumerator : Nat.Coprime numerator denominator) :
    (∑ t ∈ (Finset.range
        (actualMajorArcLcmResidueModulus S denominator)).filter
          (fun t => t % (∏ s ∈ S, s) = target ∧
            Nat.Coprime t (actualMajorArcLcmResidueModulus S denominator)),
      GoldbachChain.e
        (((((numerator : ℤ) *
                ((actualMajorArcLcmResidueModulus S denominator /
                  denominator : ℕ) : ℤ) -
              shift *
                ((actualMajorArcLcmResidueModulus S denominator /
                  (∏ s ∈ S, s) : ℕ) : ℤ) +
              lift *
                (actualMajorArcLcmResidueModulus S denominator : ℤ) :
                  ℤ) : ℝ) * t) /
          (actualMajorArcLcmResidueModulus S denominator))) = 0 := by
  simpa using
    (actualMajorArcUnitOrbit_actual_weighted_shifted_unit_label_sum_zero
      S denominator p numerator target shift lift (fun _ => (1 : ℂ))
      hsupport hdenominator hpSupport hpSquare hnumerator
      (by intros; rfl))

#print axioms Erdos689.actualMajorArcUnitOrbit_sum_range_mul
#print axioms Erdos689.actualMajorArcUnitOrbit_support_residue_add_block
#print axioms Erdos689.actualMajorArcUnitOrbit_coprime_add_block_iff
#print axioms Erdos689.actualMajorArcUnitOrbit_phase_add_block
#print axioms Erdos689.actualMajorArcUnitOrbit_weighted_support_unit_phase_sum_zero
#print axioms Erdos689.actualMajorArcUnitOrbit_actual_weighted_shifted_unit_label_sum_zero
#print axioms Erdos689.actualMajorArcUnitOrbit_actual_shifted_unit_label_sum_zero

end Erdos689
