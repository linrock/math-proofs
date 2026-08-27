import ActualMajorArcGlobalStrata433
import ActualConductorDedupCompletion433
import ActualMajorArcSignedTailAssembly433
import ActualMajorArcCorrectedModel433

/-!
# Exact odd-versus-doubled original conductor partition

The ACTUAL support-free original denominator family contains odd outside
conductors, their doubled parity companions, and conductors divisible by
four. A divisible-by-four summand can be removed ONLY after its actual
signed weight is proved zero. The even companion has the indispensable
genuine sharp cutoff `P / 2`; it is never replaced by a duplicated odd
conductor sum.
-/

open Finset
open scoped BigOperators

namespace Erdos689

/-- EXACT arbitrary-additive-weight partition of ALL original support-free
denominators. True odd conductors use the sharp cutoff `P`; genuine doubled
odd conductors use the different sharp cutoff `P/2`. The entire remaining
`4 ∣ q` family disappears only under the supplied POINTWISE ZERO proof. -/
theorem actualMajorArcFinalPartition_support_free_parity_sum
    {A : Type*} [AddCommMonoid A]
    (support cutoff : ℕ) (weight : ℕ → A)
    (hsupportOdd : Nat.Coprime support 2)
    (hfour : ∀ denominator,
      denominator ∈ actualMajorArcGlobalStrataDenominators
        support cutoff →
        4 ∣ denominator → weight denominator = 0) :
    (∑ denominator ∈ actualMajorArcGlobalStrataDenominators
      support cutoff, weight denominator) =
      (∑ outside ∈ (Finset.Icc 1 cutoff).filter
          (fun outside => Nat.Coprime outside (2 * support)),
        weight outside) +
      ∑ outside ∈ (Finset.Icc 1 (cutoff / 2)).filter
          (fun outside => Nat.Coprime outside (2 * support)),
        weight (2 * outside) := by
  classical
  let all := actualMajorArcGlobalStrataDenominators support cutoff
  let odd := (Finset.Icc 1 cutoff).filter
    (fun outside => Nat.Coprime outside (2 * support))
  let half := (Finset.Icc 1 (cutoff / 2)).filter
    (fun outside => Nat.Coprime outside (2 * support))
  let doubled := half.image (fun outside : ℕ => 2 * outside)
  have hoddCoprime (outside : ℕ)
      (h : Nat.Coprime outside (2 * support)) :
      Nat.Coprime outside 2 ∧ Nat.Coprime outside support :=
    (Nat.coprime_mul_iff_right).mp h
  have hoddNotTwo (outside : ℕ)
      (h : Nat.Coprime outside (2 * support)) : ¬ 2 ∣ outside := by
    exact Nat.prime_two.coprime_iff_not_dvd.mp
      (hoddCoprime outside h).1.symm
  have hsubsetOdd : odd ⊆ all := by
    intro outside houtside
    obtain ⟨hinterval, hcoprime⟩ := Finset.mem_filter.mp houtside
    exact Finset.mem_filter.mpr
      ⟨hinterval, (hoddCoprime outside hcoprime).2⟩
  have hsubsetDoubled : doubled ⊆ all := by
    intro denominator hdenominator
    obtain ⟨outside, houtside, rfl⟩ := Finset.mem_image.mp hdenominator
    obtain ⟨hinterval, hcoprime⟩ := Finset.mem_filter.mp houtside
    obtain ⟨hpositive, hhalf⟩ := Finset.mem_Icc.mp hinterval
    have hcutoff :=
      (Nat.le_div_iff_mul_le (by norm_num : 0 < (2 : ℕ))).mp hhalf
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · apply (Nat.coprime_mul_iff_left).mpr
      exact ⟨hsupportOdd.symm, (hoddCoprime outside hcoprime).2⟩
  have hdisjoint : Disjoint odd doubled := by
    apply Finset.disjoint_left.mpr
    intro denominator hodd hdoubled
    obtain ⟨_, hcoprime⟩ := Finset.mem_filter.mp hodd
    obtain ⟨outside, _, hequal⟩ := Finset.mem_image.mp hdoubled
    apply hoddNotTwo denominator hcoprime
    rw [← hequal]
    exact dvd_mul_right 2 outside
  have hunionSubset : odd ∪ doubled ⊆ all :=
    Finset.union_subset hsubsetOdd hsubsetDoubled
  have hremainingZero :
      ∀ denominator ∈ all, denominator ∉ odd ∪ doubled →
        weight denominator = 0 := by
    intro denominator hdenominator hremaining
    obtain ⟨hinterval, hcoprimeSupport⟩ :=
      Finset.mem_filter.mp hdenominator
    obtain ⟨hpositive, hcutoff⟩ := Finset.mem_Icc.mp hinterval
    have hnotOdd : denominator ∉ odd := by
      intro hodd
      exact hremaining (Finset.mem_union_left doubled hodd)
    have htwo : 2 ∣ denominator := by
      by_contra hnotTwo
      have hcoprimeTwo : Nat.Coprime denominator 2 :=
        (Nat.prime_two.coprime_iff_not_dvd.mpr hnotTwo).symm
      apply hnotOdd
      exact Finset.mem_filter.mpr
        ⟨hinterval,
          (Nat.coprime_mul_iff_right).mpr
            ⟨hcoprimeTwo, hcoprimeSupport⟩⟩
    let outside := denominator / 2
    have hrepresentation : denominator = 2 * outside :=
      (Nat.mul_div_cancel' htwo).symm
    have houtsidePositive : 0 < outside := by omega
    have houtsideCutoff : outside ≤ cutoff / 2 := by
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < (2 : ℕ))).mpr
      omega
    have houtsideSupport : Nat.Coprime outside support := by
      apply hcoprimeSupport.coprime_dvd_left
      rw [hrepresentation]
      exact dvd_mul_left outside 2
    have houtsideEven : 2 ∣ outside := by
      by_contra hnotEven
      have houtsideTwo : Nat.Coprime outside 2 :=
        (Nat.prime_two.coprime_iff_not_dvd.mpr hnotEven).symm
      have houtsideHalf : outside ∈ half := by
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨houtsidePositive, houtsideCutoff⟩,
            (Nat.coprime_mul_iff_right).mpr
              ⟨houtsideTwo, houtsideSupport⟩⟩
      apply hremaining
      apply Finset.mem_union_right odd
      exact Finset.mem_image.mpr
        ⟨outside, houtsideHalf, hrepresentation.symm⟩
    apply hfour denominator hdenominator
    obtain ⟨k, hk⟩ := houtsideEven
    rw [hrepresentation, hk]
    exact ⟨k, by ring⟩
  change (∑ denominator ∈ all, weight denominator) =
    (∑ outside ∈ odd, weight outside) +
      ∑ outside ∈ half, weight (2 * outside)
  calc
    (∑ denominator ∈ all, weight denominator) =
        ∑ denominator ∈ odd ∪ doubled, weight denominator := by
      symm
      apply Finset.sum_subset hunionSubset
      exact hremainingZero
    _ = (∑ outside ∈ odd, weight outside) +
          ∑ denominator ∈ doubled, weight denominator :=
      Finset.sum_union hdisjoint
    _ = _ := by
      congr 1
      unfold doubled
      rw [Finset.sum_image]
      intro left _ right _ hequal
      change 2 * left = 2 * right at hequal
      omega

#print axioms Erdos689.actualMajorArcFinalPartition_support_free_parity_sum

end Erdos689
