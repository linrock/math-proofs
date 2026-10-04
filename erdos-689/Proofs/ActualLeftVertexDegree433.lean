module

public import ActualLeftVertexSelectors433
public import ActualRightVertexLeftAuditBounds433

@[expose] public section


/-!
# Exact fixed-left endpoint, support-unit refinement, and optimized sieve

Every parameter in the original left graph fiber satisfies the genuine
endpoint `4*d*q ≤ n`.  Replacing its switched-only selector by the actual
two-prime support-unit selector loses at most `2*#S` genuine parameters.
The resulting optimized Selberg bound keeps the sharp `1/(4*d*W)` main
coefficient, the complete cutoff-fourth-power and small-prime errors, and
the determinant exclusion needed even when the fixed vertex contains the
prime three.
-/

open Finset Filter
open scoped BigOperators Topology

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Erdos689

/-- The genuine fixed-left manuscript parameter fiber with the original
right endpoint `2*y = 4*d*q ≤ n`, never enlarged to `n+1`. -/
def edgeBoundedLeftVertexPrimeParameters
    (S : Finset ℕ) (b : ℕ → ℕ) (n x d : ℕ) : Finset ℕ :=
  (leftFiberSwitchedPrimeParameters S b n x d).filter fun q =>
    4 * d * q ≤ n

/-- The actual left finite-field selector agrees with the two genuine
natural prime-unit tests and both original switched targets.  Natural
subtraction is interpreted only on its true non-underflow branch. -/
theorem actualLeftVertexLocalResidues_mem_natCast_iff
    (p x bp d q : ℕ)
    (hp : p.Prime)
    (hunderflow : x ≤ 2 * d * q) :
    (q : ZMod p) ∈ actualLeftVertexLocalResidues p x bp d ↔
      (¬ p ∣ q) ∧ (¬ p ∣ 2 * d * q - x) ∧
        (¬ bp ≡ 4 * d * q [MOD p]) ∧
          (¬ bp ≡ 2 * x [MOD p]) := by
  classical
  unfold actualLeftVertexLocalResidues
  simp only [hp, ↓reduceDIte, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hq : (q : ZMod p) ≠ 0 ↔ ¬ p ∣ q :=
    not_congr (ZMod.natCast_eq_zero_iff q p)
  have hcast :
      ((2 * d * q - x : ℕ) : ZMod p) =
        ((2 * d : ℕ) : ZMod p) * (q : ZMod p) - (x : ZMod p) := by
    rw [Nat.cast_sub hunderflow, Nat.cast_mul]
  have hz :
      ((2 * d : ℕ) : ZMod p) * (q : ZMod p) - (x : ZMod p) ≠ 0 ↔
        ¬ p ∣ 2 * d * q - x := by
    rw [← hcast]
    exact not_congr (ZMod.natCast_eq_zero_iff (2 * d * q - x) p)
  have hproduct :
      ((2 * d * q : ℕ) : ZMod p) =
        ((2 * d : ℕ) : ZMod p) * (q : ZMod p) := by
    rw [Nat.cast_mul]
  have htarget : 2 * (2 * d * q) = 4 * d * q := by ring
  rw [hq, hz, ← hproduct,
    zmod_switched_target_ne_iff_not_modEq,
    zmod_switched_target_ne_iff_not_modEq, htarget]

/-- At a genuine non-underflow parameter, the actual left selector is
exactly the old switched selector plus both genuine support-unit tests. -/
theorem actualLeftVertexUnitSelectorResidues_mem_mod_iff
    (S : Finset ℕ) (b : ℕ → ℕ) (x d q : ℕ)
    (hprime : ∀ p ∈ S, p.Prime)
    (hW : 0 < ∏ p ∈ S, p)
    (hunderflow : x ≤ 2 * d * q) :
    q % (∏ p ∈ S, p) ∈
        actualLeftVertexUnitSelectorResidues S b x d ↔
      q % (∏ p ∈ S, p) ∈
          actualLeftFiberSelectorResidues S b x d ∧
        (∀ p ∈ S, ¬ p ∣ q) ∧
          (∀ p ∈ S, ¬ p ∣ 2 * d * q - x) := by
  classical
  have hcanonical : q % (∏ p ∈ S, p) < ∏ p ∈ S, p :=
    Nat.mod_lt q hW
  have hlocal (p : ℕ) (hp : p ∈ S) :
      ((q % (∏ s ∈ S, s) : ℕ) : ZMod p) = (q : ZMod p) :=
    actualRightVertex_support_residue_natCast S p q hp
  constructor
  · intro hselector
    unfold actualLeftVertexUnitSelectorResidues at hselector
    obtain ⟨_, hcoordinates⟩ := Finset.mem_filter.mp hselector
    have hall (p : ℕ) (hp : p ∈ S) :=
      (actualLeftVertexLocalResidues_mem_natCast_iff
        p x (b p) d q (hprime p hp) hunderflow).mp
          (by rw [← hlocal p hp]; exact hcoordinates ⟨p, hp⟩)
    refine ⟨?_, fun p hp => (hall p hp).1,
      fun p hp => (hall p hp).2.1⟩
    apply (leftFiberSwitched_selector_iff_mem_actual_residues
      S b x d q hW).mp
    constructor
    · apply (switchedHits_zero_iff_forall_not_modEq S b (2 * x)).mpr
      intro p hp
      exact (hall p hp).2.2.2
    · apply (switchedHits_zero_iff_forall_not_modEq S b (4 * d * q)).mpr
      intro p hp
      exact (hall p hp).2.2.1
  · rintro ⟨hold, hqunit, hzunit⟩
    have hswitch :=
      (leftFiberSwitched_selector_iff_mem_actual_residues
        S b x d q hW).mpr hold
    have hfixed :=
      (switchedHits_zero_iff_forall_not_modEq S b (2 * x)).mp hswitch.1
    have hmoving :=
      (switchedHits_zero_iff_forall_not_modEq
        S b (4 * d * q)).mp hswitch.2
    unfold actualLeftVertexUnitSelectorResidues
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hcanonical, ?_⟩
    intro p
    rw [actualRightVertex_support_residue_natCast S p q p.property]
    apply (actualLeftVertexLocalResidues_mem_natCast_iff
      p x (b p) d q (hprime p p.property) hunderflow).mpr
    exact ⟨hqunit p p.property, hzunit p p.property,
      hmoving p p.property, hfixed p p.property⟩

/-- The genuine natural truncation from the ORIGINAL fixed-left endpoint
`4*d*q ≤ n`; no enlarged `n+1` parameter range is used. -/
def actualLeftVertexSharpTruncation (n d : ℕ) : ℕ :=
  n / (4 * d) + 1

/-- The actual sharp left graph fiber is exactly its old switched-selector
prime family on the original coefficient-sensitive endpoint. -/
theorem edgeBoundedLeftVertexPrimeParameters_eq_sharp_selected
    (S : Finset ℕ) (b : ℕ → ℕ) (n x d : ℕ)
    (hW : 0 < ∏ p ∈ S, p) (hd : 0 < d) :
    edgeBoundedLeftVertexPrimeParameters S b n x d =
      (Finset.range (actualLeftVertexSharpTruncation n d)).filter
        fun q =>
          q % (∏ p ∈ S, p) ∈
            actualLeftFiberSelectorResidues S b x d ∧
              q.Prime ∧ (2 * d * q - x).Prime := by
  classical
  rw [edgeBoundedLeftVertexPrimeParameters,
    leftFiberSwitchedPrimeParameters_eq_selected S b n x d hW]
  ext q
  simp only [Finset.mem_filter, Finset.mem_range]
  have hfour : 0 < 4 * d := by omega
  have hendpoint : q < actualLeftVertexSharpTruncation n d ↔
      4 * d * q ≤ n := by
    unfold actualLeftVertexSharpTruncation
    rw [Nat.lt_add_one_iff, Nat.le_div_iff_mul_le hfour]
    simp [mul_comm, mul_left_comm]
  constructor
  · rintro ⟨⟨_, hselector, hqprime, hzprime⟩, hbound⟩
    exact ⟨hendpoint.mpr hbound, hselector, hqprime, hzprime⟩
  · rintro ⟨hqrange, hselector, hqprime, hzprime⟩
    have hbound : 4 * d * q ≤ n := hendpoint.mp hqrange
    have hqn : q < n + 1 := by
      have hfactor : q ≤ 4 * d * q := by nlinarith
      omega
    exact ⟨⟨hqn, hselector, hqprime, hzprime⟩, hbound⟩

/-- Genuine support-prime exceptions for the increasing fixed-left label
form; the non-underflow restriction is explicit and indispensable. -/
def actualLeftVertexIncreasingSupportExceptions
    (S : Finset ℕ) (N d x : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun q =>
    2 * d * q - x ∈ S ∧ x < 2 * d * q

/-- A positive increasing affine difference is injective on its genuine
non-underflow branch, so at most `#S` labels can be support primes. -/
theorem actualLeftVertexIncreasingSupportExceptions_card_le
    (S : Finset ℕ) (N d x : ℕ)
    (hd : 0 < d) :
    (actualLeftVertexIncreasingSupportExceptions S N d x).card ≤ S.card := by
  classical
  let exceptions := actualLeftVertexIncreasingSupportExceptions S N d x
  have hinjective : Set.InjOn (fun q : ℕ => 2 * d * q - x)
      (↑exceptions : Set ℕ) := by
    intro q hq r hr heq
    have hqpositive :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2.2
    have hrpositive :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp hr)).2.2
    change 2 * d * q - x = 2 * d * r - x at heq
    have hmul : 2 * d * q = 2 * d * r := by omega
    exact Nat.mul_left_cancel (by omega : 0 < 2 * d) hmul
  calc
    exceptions.card = (exceptions.image fun q => 2 * d * q - x).card :=
      (Finset.card_image_iff.mpr hinjective).symm
    _ ≤ S.card := by
      apply Finset.card_le_card
      intro z hz
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hq).2.1

/-- Refinement from the actual switched selector to the genuine two-unit
left selector loses at most the two true support-prime exception families. -/
theorem actualLeftVertexSelected_card_le_unit_refinement
    (S : Finset ℕ) (b : ℕ → ℕ) (N x d : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hW : 0 < ∏ p ∈ S, p)
    (hd : 0 < d) :
    (((Finset.range N).filter fun q =>
      q % (∏ p ∈ S, p) ∈
          actualLeftFiberSelectorResidues S b x d ∧
        q.Prime ∧ (2 * d * q - x).Prime).card) ≤
      (((Finset.range N).filter fun q =>
        q % (∏ p ∈ S, p) ∈
            actualLeftVertexUnitSelectorResidues S b x d ∧
          q.Prime ∧ (2 * d * q - x).Prime).card) + 2 * S.card := by
  classical
  let source := (Finset.range N).filter fun q =>
    q % (∏ p ∈ S, p) ∈
        actualLeftFiberSelectorResidues S b x d ∧
      q.Prime ∧ (2 * d * q - x).Prime
  let refined := (Finset.range N).filter fun q =>
    q % (∏ p ∈ S, p) ∈
        actualLeftVertexUnitSelectorResidues S b x d ∧
      q.Prime ∧ (2 * d * q - x).Prime
  let primeExceptions := (Finset.range N).filter fun q => q ∈ S
  let labelExceptions := actualLeftVertexIncreasingSupportExceptions S N d x
  have hsubset : source ⊆ refined ∪ (primeExceptions ∪ labelExceptions) := by
    intro q hq
    obtain ⟨hqrange, hold, hqprime, hzprime⟩ := Finset.mem_filter.mp hq
    have hpositive : x < 2 * d * q := Nat.sub_pos_iff_lt.mp hzprime.pos
    by_cases hqunit : ∀ p ∈ S, ¬ p ∣ q
    · by_cases hzunit : ∀ p ∈ S, ¬ p ∣ 2 * d * q - x
      · apply Finset.mem_union_left
        apply Finset.mem_filter.mpr
        exact ⟨hqrange,
          (actualLeftVertexUnitSelectorResidues_mem_mod_iff
            S b x d q hsupport hW hpositive.le).mpr
              ⟨hold, hqunit, hzunit⟩,
          hqprime, hzprime⟩
      · apply Finset.mem_union_right
        apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        exact ⟨hqrange,
          actualRightVertex_prime_mem_support_of_not_unit
            S (2 * d * q - x) hsupport hzprime hzunit,
          hpositive⟩
    · apply Finset.mem_union_right
      apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      exact ⟨hqrange,
        actualRightVertex_prime_mem_support_of_not_unit
          S q hsupport hqprime hqunit⟩
  have hprimeExceptions : primeExceptions.card ≤ S.card := by
    apply Finset.card_le_card
    intro q hq
    exact (Finset.mem_filter.mp hq).2
  have hlabelExceptions : labelExceptions.card ≤ S.card :=
    actualLeftVertexIncreasingSupportExceptions_card_le S N d x hd
  have hcard := Finset.card_le_card hsubset
  have hunion := Finset.card_union_le refined (primeExceptions ∪ labelExceptions)
  have hexception := Finset.card_union_le primeExceptions labelExceptions
  change source.card ≤ refined.card + 2 * S.card
  omega

/-- Every genuinely edge-bounded left fiber is controlled by the exact
sharp support-unit-selected progression plus at most `2*#S` exceptions. -/
theorem edgeBoundedLeftVertexPrimeParameters_card_le_unit_progression
    (S : Finset ℕ) (b : ℕ → ℕ) (n x d : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hW : 0 < ∏ p ∈ S, p)
    (hd : 0 < d) :
    (edgeBoundedLeftVertexPrimeParameters S b n x d).card ≤
      (((Finset.range (actualLeftVertexSharpTruncation n d)).filter
        fun q =>
          q % (∏ p ∈ S, p) ∈
            actualLeftVertexUnitSelectorResidues S b x d ∧
              q.Prime ∧ (2 * d * q - x).Prime).card) + 2 * S.card := by
  rw [edgeBoundedLeftVertexPrimeParameters_eq_sharp_selected
    S b n x d hW hd]
  exact actualLeftVertexSelected_card_le_unit_refinement S b
    (actualLeftVertexSharpTruncation n d) x d hsupport hW hd

/-- The true fixed-left endpoint retains `1/(4*d)` with only one natural
rounding unit. -/
theorem actualLeftVertexSharpTruncation_real_le
    (n d : ℕ) (_hd : 0 < d) :
    (actualLeftVertexSharpTruncation n d : ℝ) ≤
      (n : ℝ) / (4 * (d : ℝ)) + 1 := by
  unfold actualLeftVertexSharpTruncation
  have hdiv : ((n / (4 * d) : ℕ) : ℝ) ≤
      (n : ℝ) / ((4 * d : ℕ) : ℝ) := Nat.cast_div_le
  push_cast at hdiv ⊢
  linarith

/-- Normalizing by the genuine support product preserves the precise
fixed-left endpoint `1/(4*d*W)` up to two bounded rounding units. -/
theorem actualLeftVertexSharpTruncation_support_normalized_le
    (S : Finset ℕ) (n d : ℕ)
    (hW : 0 < ∏ p ∈ S, p) (hd : 0 < d) :
    (actualLeftVertexSharpTruncation n d : ℝ) /
        (((∏ p ∈ S, p) : ℕ) : ℝ) + 1 ≤
      (n : ℝ) /
        (4 * (d : ℝ) * (((∏ p ∈ S, p) : ℕ) : ℝ)) + 2 := by
  have hWreal : (0 : ℝ) < ((∏ p ∈ S, p) : ℕ) := by exact_mod_cast hW
  have hWone : (1 : ℝ) ≤ ((∏ p ∈ S, p) : ℕ) := by exact_mod_cast hW
  have hendpoint := actualLeftVertexSharpTruncation_real_le n d hd
  have hfraction :
      (1 : ℝ) / (((∏ p ∈ S, p) : ℕ) : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hWreal).mpr
    linarith
  calc
    (actualLeftVertexSharpTruncation n d : ℝ) /
        (((∏ p ∈ S, p) : ℕ) : ℝ) + 1 ≤
      ((n : ℝ) / (4 * (d : ℝ)) + 1) /
        (((∏ p ∈ S, p) : ℕ) : ℝ) + 1 := by gcongr
    _ = (n : ℝ) /
          (4 * (d : ℝ) * (((∏ p ∈ S, p) : ℕ) : ℝ)) +
        1 / (((∏ p ∈ S, p) : ℕ) : ℝ) + 1 := by
      field_simp
    _ ≤ (n : ℝ) /
          (4 * (d : ℝ) * (((∏ p ∈ S, p) : ℕ) : ℝ)) + 2 := by
      linarith

/-- Complete optimized Selberg bound for the ACTUAL sharp fixed-left
graph fiber, retaining its true selector, `1/(4*d*W)` endpoint, cutoff
fourth power, small-prime errors, support-prime exceptions, and exact
moving determinant exclusion. -/
theorem edgeBoundedLeftVertexPrimeParameters_card_le_unit_selected_sieve
    (S P : Finset ℕ) (b : ℕ → ℕ) (M n z x d : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hW : 0 < ∏ p ∈ S, p)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z)
    (hd : ∀ p ∈ P, ¬ p ∣ 2 * d)
    (hx : ∀ p ∈ P, ¬ p ∣ x)
    (hM : 2 ∣ M)
    (hPM : Nat.Coprime (∏ p ∈ P, p) M)
    (hWM : (∏ p ∈ S, p) ∣ M)
    (hprimes : ∀ p : ℕ, p.Prime →
      (p ∣ ∏ q ∈ P, q ↔ p ≤ z ∧ Nat.Coprime p M))
    (hdpositive : 0 < d) :
    ((edgeBoundedLeftVertexPrimeParameters S b n x d).card : ℝ) ≤
      ((actualLeftVertexUnitSelectorResidues S b x d).card : ℝ) *
        (((n : ℝ) /
            (4 * (d : ℝ) * (((∏ p ∈ S, p) : ℕ) : ℝ)) + 2) /
          twoRootSelbergDenominator M z + (z : ℝ) ^ 4 +
            ((2 * Nat.primeCounting z : ℕ) : ℝ)) +
        ((2 * S.card : ℕ) : ℝ) := by
  let N := actualLeftVertexSharpTruncation n d
  let residues := actualLeftVertexUnitSelectorResidues S b x d
  have hfinite := edgeBoundedLeftVertexPrimeParameters_card_le_unit_progression
    S b n x d hsupport hW hdpositive
  have hfiniteReal :
      ((edgeBoundedLeftVertexPrimeParameters S b n x d).card : ℝ) ≤
        ((((Finset.range N).filter fun q =>
          q % (∏ p ∈ S, p) ∈ residues ∧
            q.Prime ∧ (2 * d * q - x).Prime).card : ℕ) : ℝ) +
          ((2 * S.card : ℕ) : ℝ) := by
    exact_mod_cast hfinite
  have hsieve := actualAffineSelected_prime_difference_card_le_density
    P residues M N z (∏ p ∈ S, p) (2 * d) x hW
    (by
      intro r hr
      change r ∈ actualLeftVertexUnitSelectorResidues S b x d at hr
      unfold actualLeftVertexUnitSelectorResidues at hr
      exact Finset.mem_range.mp (Finset.mem_filter.mp hr).1)
    hprime hlarge hz hd hx hM hPM hWM hprimes (by omega)
  have hdenominator : 0 ≤ twoRootSelbergDenominator M z :=
    twoRootSelbergDenominator_nonneg hM z
  calc
    ((edgeBoundedLeftVertexPrimeParameters S b n x d).card : ℝ) ≤
        ((((Finset.range N).filter fun q =>
          q % (∏ p ∈ S, p) ∈ residues ∧
            q.Prime ∧ (2 * d * q - x).Prime).card : ℕ) : ℝ) +
          ((2 * S.card : ℕ) : ℝ) := hfiniteReal
    _ ≤ (residues.card : ℝ) *
          (((N : ℝ) / (((∏ p ∈ S, p) : ℕ) : ℝ) + 1) /
            twoRootSelbergDenominator M z + (z : ℝ) ^ 4 +
              ((2 * Nat.primeCounting z : ℕ) : ℝ)) +
            ((2 * S.card : ℕ) : ℝ) := by linarith
    _ ≤ _ := by
      have hendpoint := actualLeftVertexSharpTruncation_support_normalized_le
        S n d hW hdpositive
      have hdivision := div_le_div_of_nonneg_right hendpoint hdenominator
      have hfull := add_le_add_right
        (add_le_add_right hdivision ((z : ℝ) ^ 4))
          ((2 * Nat.primeCounting z : ℕ) : ℝ)
      have hnonnegative : (0 : ℝ) ≤ residues.card := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hfull hnonnegative]

#print axioms Erdos689.actualLeftVertexLocalResidues_mem_natCast_iff
#print axioms Erdos689.actualLeftVertexUnitSelectorResidues_mem_mod_iff
#print axioms Erdos689.edgeBoundedLeftVertexPrimeParameters_eq_sharp_selected
#print axioms Erdos689.actualLeftVertexIncreasingSupportExceptions_card_le
#print axioms Erdos689.actualLeftVertexSelected_card_le_unit_refinement
#print axioms Erdos689.edgeBoundedLeftVertexPrimeParameters_card_le_unit_progression
#print axioms Erdos689.actualLeftVertexSharpTruncation_real_le
#print axioms Erdos689.actualLeftVertexSharpTruncation_support_normalized_le
#print axioms Erdos689.edgeBoundedLeftVertexPrimeParameters_card_le_unit_selected_sieve

end Erdos689
