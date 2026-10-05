module

public import ScaleAdaptiveBandActualTargetLoad1139
public import ScaleAdaptiveDyadicEulerShell1139
public import ScaleAdaptiveDyadicShellGeometry1139
public import ScaleAdaptiveColoredEulerAmplification1139

@[expose] public section


/-!
# Genuine multi-shell aggregation of actual inverse-degree target loads

For a FIXED finite family of dyadic exponents, the physical prime-label
scale is exactly `N_j(Y) = Y / 2^j`.  Each genuine signed prime-pattern
sampler is normalized by its actual integer degree, and its good typed
targets have load at least `F_j/8` on both adjacent physical cells.

This file transports each exceptional-target limit from `N_j/log N_j` to
the ORIGINAL `Y/log Y` normalization, takes finite unions over exponents,
actual target cells, shared outcomes, and physical indices, and adds the
true per-shell loads.  In particular the resulting lower bound is
`(∑_j F_j)/8`, not a uniform fixed positive factor that silently ignores
the decay of `F_j`.

All exponent families and pattern complexities are fixed before `Y→∞`.
No cross-shell prime-pattern independence, repeated prime label, actual
covering, or additional target correlation estimate is assumed.
-/

open Finset Filter
open scoped BigOperators Topology

namespace Erdos1139

/-- A zero-density genuine exceptional family at physical scale `Y/d`
remains zero-density in the ORIGINAL `Y/log Y` normalization.  The proof
retains exact natural flooring and the already audited prime-scale ratio. -/
theorem scaleAdaptiveFixedDivisorBadTargets_global_tendsto_zero
    (divisor : ℕ) (positive : 0 < divisor)
    (bad : ℕ → Finset ℕ)
    (local_density : Tendsto
      (fun N : ℕ =>
        ((bad N).card : ℝ) * Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun length : ℕ =>
        ((bad (length / divisor)).card : ℝ) *
          Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)) := by
  have pulled := local_density.comp
    (Nat.tendsto_div_const_atTop positive.ne')
  have scaling := Erdos689.nat_div_prime_scale_ratio_tendsto
    divisor positive
  have product : Tendsto
      (fun length : ℕ =>
        (((bad (length / divisor)).card : ℝ) *
          Real.log ((length / divisor : ℕ) : ℝ) /
            ((length / divisor : ℕ) : ℝ)) *
          ((((length / divisor : ℕ) : ℝ) /
            Real.log ((length / divisor : ℕ) : ℝ)) /
              ((length : ℝ) / Real.log (length : ℝ))))
      atTop (nhds (0 : ℝ)) := by
    simpa using pulled.mul scaling
  apply product.congr'
  filter_upwards [eventually_ge_atTop (2 * divisor)] with length large
  have length_positive : (0 : ℝ) < length := by
    exact_mod_cast (show 0 < length by omega)
  have quotient_large : 2 ≤ length / divisor :=
    (Nat.le_div_iff_mul_le positive).mpr (by omega)
  have quotient_positive : (0 : ℝ) < (length / divisor : ℕ) := by
    exact_mod_cast (show 0 < length / divisor by omega)
  have log_length_nonzero : Real.log (length : ℝ) ≠ 0 := by
    apply (Real.log_pos ?_).ne'
    exact_mod_cast (show 1 < length by omega)
  have log_quotient_nonzero :
      Real.log ((length / divisor : ℕ) : ℝ) ≠ 0 := by
    apply (Real.log_pos ?_).ne'
    exact_mod_cast quotient_large
  field_simp [length_positive.ne', quotient_positive.ne',
    log_length_nonzero, log_quotient_nonzero]

/-- The preceding original-scale transfer at the TRUE physical dyadic
scale `Y / 2^j`; the exponent is fixed before the limit. -/
theorem scaleAdaptiveDyadicBadTargets_global_tendsto_zero
    (exponent : ℕ) (bad : ℕ → Finset ℕ)
    (local_density : Tendsto
      (fun N : ℕ =>
        ((bad N).card : ℝ) * Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun length : ℕ =>
        ((bad (length / 2 ^ exponent)).card : ℝ) *
          Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)) := by
  exact scaleAdaptiveFixedDivisorBadTargets_global_tendsto_zero
    (2 ^ exponent) (pow_pos (by omega) exponent) bad local_density

/-- A FINITE family of actual scale-dependent exceptional sets remains
negligible at the original interval normalization.  Each index may have a
different genuine fixed dyadic scale and a different pattern support. -/
theorem scaleAdaptiveFiniteDyadicBadUnion_global_tendsto_zero
    {α : Type*} [DecidableEq α]
    (family : Finset α) (exponent : α → ℕ)
    (bad : α → ℕ → Finset ℕ)
    (local_density : ∀ item ∈ family,
      Tendsto
        (fun N : ℕ =>
          ((bad item N).card : ℝ) * Real.log (N : ℝ) / (N : ℝ))
        atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun length : ℕ =>
        ((family.biUnion fun item =>
          bad item (length / 2 ^ exponent item)).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)) := by
  apply scaleAdaptiveBandFiniteBadUnion_normalized_card_tendsto_zero
  intro item selected
  exact scaleAdaptiveDyadicBadTargets_global_tendsto_zero
    (exponent item) (bad item) (local_density item selected)

/-- Every actually usable adjacent target-cell pair at one fixed dyadic
prime-label shell.  The true physical index condition `2m ≤ 2^j+1` is
retained, as is the nondegenerate requirement `m ≥ 2`. -/
def scaleAdaptiveMultiShellValidCells (exponent : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (2 ^ exponent)).filter
    fun cell => 2 * cell ≤ 2 ^ exponent + 1

/-- Exact membership conditions for a genuine fixed-shell target-cell
pair; no cell outside the actual mixed-pattern index range is included. -/
theorem mem_scaleAdaptiveMultiShellValidCells
    {exponent cell : ℕ} :
    cell ∈ scaleAdaptiveMultiShellValidCells exponent ↔
      2 ≤ cell ∧ cell ≤ 2 ^ exponent ∧
        2 * cell ≤ 2 ^ exponent + 1 := by
  simp [scaleAdaptiveMultiShellValidCells, and_assoc]

/-- Actual bad PRIME targets across BOTH adjacent cells and every valid
physical index window of ONE fixed dyadic label shell. -/
noncomputable def scaleAdaptiveMultiShellPrimeCellBadTargets
    (support : Finset ℕ) (exponent : ℕ) (lower upper : ℝ)
    (N : ℕ) : Finset ℕ :=
  (scaleAdaptiveMultiShellValidCells exponent).biUnion fun cell =>
    (Finset.range 2).biUnion fun parity =>
      scaleAdaptiveBandPrimeBadTargets
        support (2 ^ exponent) cell
          (scaleAdaptiveBandAdjacentTypedTargets 1 cell parity)
          (scaleAdaptiveBandActualInverseTargetLoad
            support (2 ^ exponent) lower upper) N

/-- Actual bad type-`s` SEMIPRIME targets across both adjacent cells of ONE
fixed dyadic label shell.  This family is used only when the real type is
contained in the genuine scale-dependent support. -/
noncomputable def scaleAdaptiveMultiShellSemiprimeCellBadTargets
    (support : Finset ℕ) (targetType exponent : ℕ)
    (lower upper : ℝ) (N : ℕ) : Finset ℕ :=
  (scaleAdaptiveMultiShellValidCells exponent).biUnion fun cell =>
    (Finset.range 2).biUnion fun parity =>
      scaleAdaptiveBandSemiprimeBadTargets
        support targetType (2 ^ exponent) cell
          (scaleAdaptiveBandAdjacentTypedTargets
            targetType cell parity)
          (scaleAdaptiveBandActualInverseTargetLoad
            support (2 ^ exponent) lower upper) N

/-- All actual PRIME target cells of one fixed shell have one finite
zero-density exceptional union.  Both target-cell parities and every
genuine common-outcome/index exception are included. -/
theorem scaleAdaptiveMultiShellPrimeCellBadTargets_tendsto_zero_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (exponent : ℕ) (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1) :
    Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveMultiShellPrimeCellBadTargets
          support exponent lower upper N).card : ℝ) *
            Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds (0 : ℝ)) := by
  unfold scaleAdaptiveMultiShellPrimeCellBadTargets
  apply scaleAdaptiveBandFiniteBadUnion_normalized_card_tendsto_zero
  intro cell selected
  have valid := mem_scaleAdaptiveMultiShellValidCells.mp selected
  apply scaleAdaptiveBandFiniteBadUnion_normalized_card_tendsto_zero
  intro parity bounded
  have parity_bounded : parity ≤ 1 := by
    have strict := Finset.mem_range.mp bounded
    omega
  exact scaleAdaptiveBandActualPrimeBadTargets_tendsto_zero_of_GTZ
    green_tao support (2 ^ exponent) cell parity lower upper primes
      valid.2.2 parity_bounded lower_nonnegative
        band_nonempty upper_bounded

/-- All actual SEMIPRIME target cells of one fixed supported type and
shell have one finite zero-density exceptional union. -/
theorem scaleAdaptiveMultiShellSemiprimeCellBadTargets_tendsto_zero_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    {support : Finset ℕ} {targetType : ℕ}
    (exponent : ℕ) (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (type_supported : targetType ∈ support)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1) :
    Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveMultiShellSemiprimeCellBadTargets
          support targetType exponent lower upper N).card : ℝ) *
            Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds (0 : ℝ)) := by
  unfold scaleAdaptiveMultiShellSemiprimeCellBadTargets
  apply scaleAdaptiveBandFiniteBadUnion_normalized_card_tendsto_zero
  intro cell selected
  have valid := mem_scaleAdaptiveMultiShellValidCells.mp selected
  apply scaleAdaptiveBandFiniteBadUnion_normalized_card_tendsto_zero
  intro parity bounded
  have parity_bounded : parity ≤ 1 := by
    have strict := Finset.mem_range.mp bounded
    omega
  exact scaleAdaptiveBandActualSemiprimeBadTargets_tendsto_zero_of_GTZ
    green_tao (2 ^ exponent) cell parity lower upper primes
      type_supported valid.2.2 parity_bounded lower_nonnegative
        band_nonempty upper_bounded

/-- The complete ORIGINAL-scale bad PRIME target set for a finite family
of genuine dyadic shells, with each shell using its OWN actual support,
its OWN exact integer floor, and both physical target-cell parities. -/
noncomputable def scaleAdaptiveMultiShellPrimeBadTargets
    (exponents : Finset ℕ) (support : ℕ → Finset ℕ)
    (lower upper : ℝ) (length : ℕ) : Finset ℕ :=
  exponents.biUnion fun exponent =>
    scaleAdaptiveMultiShellPrimeCellBadTargets
      (support exponent) exponent lower upper
        (length / 2 ^ exponent)

/-- The complete ORIGINAL-scale bad SEMIPRIME target set for one true
supported type and a finite family of genuinely eligible dyadic shells. -/
noncomputable def scaleAdaptiveMultiShellSemiprimeBadTargets
    (exponents : Finset ℕ) (support : ℕ → Finset ℕ)
    (targetType : ℕ) (lower upper : ℝ)
    (length : ℕ) : Finset ℕ :=
  exponents.biUnion fun exponent =>
    scaleAdaptiveMultiShellSemiprimeCellBadTargets
      (support exponent) targetType exponent lower upper
        (length / 2 ^ exponent)

/-- All finite-shell PRIME exceptions have density zero in the ORIGINAL
interval normalization `Y/log Y`.  Supports may vary from shell to shell;
no cross-support second moment or complexity-uniform limit is used. -/
theorem scaleAdaptiveMultiShellPrimeBadTargets_global_tendsto_zero_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (exponents : Finset ℕ) (support : ℕ → Finset ℕ)
    (lower upper : ℝ)
    (primes : ∀ exponent ∈ exponents,
      ∀ prime ∈ support exponent, prime.Prime)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1) :
    Tendsto
      (fun length : ℕ =>
        ((scaleAdaptiveMultiShellPrimeBadTargets
          exponents support lower upper length).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)) := by
  unfold scaleAdaptiveMultiShellPrimeBadTargets
  apply scaleAdaptiveFiniteDyadicBadUnion_global_tendsto_zero
  intro exponent selected
  exact scaleAdaptiveMultiShellPrimeCellBadTargets_tendsto_zero_of_GTZ
    green_tao (support exponent) exponent lower upper
      (primes exponent selected) lower_nonnegative
        band_nonempty upper_bounded

/-- Every finite family of genuinely eligible shells has one
original-scale negligible bad set for its ACTUAL semiprime type. -/
theorem scaleAdaptiveMultiShellSemiprimeBadTargets_global_tendsto_zero_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (exponents : Finset ℕ) (support : ℕ → Finset ℕ)
    (targetType : ℕ) (lower upper : ℝ)
    (primes : ∀ exponent ∈ exponents,
      ∀ prime ∈ support exponent, prime.Prime)
    (type_supported : ∀ exponent ∈ exponents,
      targetType ∈ support exponent)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1) :
    Tendsto
      (fun length : ℕ =>
        ((scaleAdaptiveMultiShellSemiprimeBadTargets
          exponents support targetType lower upper length).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)) := by
  unfold scaleAdaptiveMultiShellSemiprimeBadTargets
  apply scaleAdaptiveFiniteDyadicBadUnion_global_tendsto_zero
  intro exponent selected
  exact scaleAdaptiveMultiShellSemiprimeCellBadTargets_tendsto_zero_of_GTZ
    green_tao exponent lower upper (primes exponent selected)
      (type_supported exponent selected) lower_nonnegative
        band_nonempty upper_bounded

/-- The actual target's physical normalized integer cell in a dyadic shell;
its quotient is retained exactly, including natural flooring. -/
def scaleAdaptiveMultiShellTargetQuotient
    (length exponent target : ℕ) : ℕ :=
  target / (length / 2 ^ exponent)

/-- The paired adjacent-cell index associated with the true target. -/
def scaleAdaptiveMultiShellTargetCell
    (length exponent target : ℕ) : ℕ :=
  scaleAdaptiveMultiShellTargetQuotient length exponent target / 2

/-- The actual even/odd physical target-cell parity. -/
def scaleAdaptiveMultiShellTargetParity
    (length exponent target : ℕ) : ℕ :=
  scaleAdaptiveMultiShellTargetQuotient length exponent target % 2

/-- Every target above the genuine four-scale lower endpoint, below the
original interval length, and not on an actual moving cell boundary has a
VALID physical index pair and belongs to its unique STRICT adjacent cell.
No real-label or prime-target existence is inferred from this arithmetic. -/
theorem scaleAdaptiveMultiShellTargetCell_physical
    (length exponent target : ℕ)
    (scale_large : 2 ^ exponent ≤ length / 2 ^ exponent)
    (target_low : 4 * (length / 2 ^ exponent) ≤ target)
    (target_high : target ≤ length)
    (not_boundary : target % (length / 2 ^ exponent) ≠ 0) :
    let scale := length / 2 ^ exponent
    let cell := scaleAdaptiveMultiShellTargetCell
      length exponent target
    let parity := scaleAdaptiveMultiShellTargetParity
      length exponent target
    cell ∈ scaleAdaptiveMultiShellValidCells exponent ∧
      parity ≤ 1 ∧
      (2 * cell + parity) * scale < target ∧
        target < (2 * cell + parity + 1) * scale := by
  let divisor := 2 ^ exponent
  let scale := length / divisor
  let quotient := target / scale
  let cell := quotient / 2
  let parity := quotient % 2
  have divisor_positive : 0 < divisor := by
    dsimp [divisor]
    exact pow_pos (by omega) exponent
  have scale_positive : 0 < scale := by
    exact lt_of_lt_of_le divisor_positive scale_large
  have length_remainder := Nat.mod_add_div length divisor
  have length_remainder_lt := Nat.mod_lt length divisor_positive
  have scale_ge_divisor : divisor ≤ length / divisor := by
    simpa [divisor] using scale_large
  have remainder_lt_scale : length % divisor < length / divisor :=
    length_remainder_lt.trans_le scale_ge_divisor
  have length_bound : length < (divisor + 1) * scale := by
    change length < (divisor + 1) * (length / divisor)
    rw [Nat.add_mul, one_mul]
    omega
  have quotient_bounded : quotient ≤ divisor := by
    apply Nat.lt_succ_iff.mp
    exact (Nat.div_lt_iff_lt_mul scale_positive).mpr
      (target_high.trans_lt length_bound)
  have quotient_large : 4 ≤ quotient := by
    exact (Nat.le_div_iff_mul_le scale_positive).mpr
      (by simpa [scale] using target_low)
  have quotient_remainder := Nat.mod_add_div quotient 2
  have parity_bounded : parity ≤ 1 := by
    dsimp [parity]
    have bound := Nat.mod_lt quotient (by omega : 0 < 2)
    omega
  have quotient_split : 2 * cell + parity = quotient := by
    dsimp [cell, parity]
    omega
  have cell_large : 2 ≤ cell := by
    dsimp [cell]
    omega
  have cell_bounded : cell ≤ divisor := by
    omega
  have physical : 2 * cell ≤ divisor + 1 := by
    omega
  have remainder := Nat.mod_add_div target scale
  have remainder_bound := Nat.mod_lt target scale_positive
  have remainder_positive : 0 < target % scale :=
    Nat.pos_of_ne_zero (by simpa [scale, divisor] using not_boundary)
  have remainder_decomposition :
      target % scale + (target / scale) * scale = target := by
    simpa [Nat.mul_comm] using remainder
  have lower : quotient * scale < target := by
    dsimp [quotient]
    omega
  have upper : target < (quotient + 1) * scale := by
    dsimp [quotient]
    rw [Nat.add_mul, one_mul]
    omega
  change cell ∈ scaleAdaptiveMultiShellValidCells exponent ∧
    parity ≤ 1 ∧
      (2 * cell + parity) * scale < target ∧
        target < (2 * cell + parity + 1) * scale
  refine ⟨?_, parity_bounded, ?_, ?_⟩
  · apply mem_scaleAdaptiveMultiShellValidCells.mpr
    exact ⟨cell_large, by simpa [divisor] using cell_bounded,
      by simpa [divisor] using physical⟩
  · simpa [quotient_split] using lower
  · simpa [quotient_split] using upper

/-- A genuine prime target away from a moving boundary belongs to the
exact OPEN prime-type cell selected by its actual quotient and parity. -/
theorem scaleAdaptiveMultiShellPrimeTarget_mem_actual_cell
    (length exponent target : ℕ)
    (prime : target.Prime)
    (scale_large : 2 ^ exponent ≤ length / 2 ^ exponent)
    (target_low : 4 * (length / 2 ^ exponent) ≤ target)
    (target_high : target ≤ length)
    (not_boundary : target % (length / 2 ^ exponent) ≠ 0) :
    target ∈ scaleAdaptiveBandAdjacentTypedTargets 1
      (scaleAdaptiveMultiShellTargetCell length exponent target)
      (scaleAdaptiveMultiShellTargetParity length exponent target)
      (length / 2 ^ exponent) := by
  obtain ⟨_valid, _parity, lower, upper⟩ :=
    scaleAdaptiveMultiShellTargetCell_physical
      length exponent target scale_large target_low target_high
        not_boundary
  apply (mem_scaleAdaptiveTypedPrimeTargetsInOpenIntegerCell
    (by omega : 0 < 1)).mpr
  refine ⟨target, prime, ?_, ?_, ?_⟩
  · exact lower
  · exact upper
  · simp

/-- A genuine semiprime `s*q` away from a moving boundary belongs to the
exact OPEN type-`s` cell selected by its actual quotient and parity. -/
theorem scaleAdaptiveMultiShellSemiprimeTarget_mem_actual_cell
    (length exponent targetType prime : ℕ)
    (prime_is_prime : prime.Prime)
    (type_positive : 0 < targetType)
    (scale_large : 2 ^ exponent ≤ length / 2 ^ exponent)
    (target_low : 4 * (length / 2 ^ exponent) ≤ targetType * prime)
    (target_high : targetType * prime ≤ length)
    (not_boundary :
      (targetType * prime) % (length / 2 ^ exponent) ≠ 0) :
    targetType * prime ∈ scaleAdaptiveBandAdjacentTypedTargets
      targetType
      (scaleAdaptiveMultiShellTargetCell
        length exponent (targetType * prime))
      (scaleAdaptiveMultiShellTargetParity
        length exponent (targetType * prime))
      (length / 2 ^ exponent) := by
  obtain ⟨_valid, _parity, lower, upper⟩ :=
    scaleAdaptiveMultiShellTargetCell_physical
      length exponent (targetType * prime)
        scale_large target_low target_high not_boundary
  apply (mem_scaleAdaptiveTypedPrimeTargetsInOpenIntegerCell
    type_positive).mpr
  exact ⟨prime, prime_is_prime, lower, upper, rfl⟩

/-- Sum of the ACTUAL inverse-integer-degree prime-target loads from a
finite family of distinct physical prime-label shells.  The correct cell
and parity are recomputed from the SAME target at every floored scale. -/
noncomputable def scaleAdaptiveMultiShellPrimeActualLoad
    (exponents : Finset ℕ) (support : ℕ → Finset ℕ)
    (lower upper : ℝ) (length target : ℕ) : ℝ :=
  ∑ exponent ∈ exponents,
    scaleAdaptiveBandPrimeOutcomeLoad
      (support exponent) (2 ^ exponent)
      (scaleAdaptiveMultiShellTargetCell
        length exponent target)
      (fun index outcome =>
        scaleAdaptiveBandActualInverseTargetLoad
          (support exponent) (2 ^ exponent) lower upper index outcome
            (length / 2 ^ exponent))
      target

/-- Sum of ACTUAL inverse-integer-degree semiprime-target loads from
genuinely eligible shells.  The same target `s*q` determines its own true
physical cell independently at every shell scale. -/
noncomputable def scaleAdaptiveMultiShellSemiprimeActualLoad
    (exponents : Finset ℕ) (support : ℕ → Finset ℕ)
    (targetType : ℕ) (lower upper : ℝ)
    (length target : ℕ) : ℝ :=
  ∑ exponent ∈ exponents,
    scaleAdaptiveBandSemiprimeOutcomeLoad
      (support exponent) targetType (2 ^ exponent)
      (scaleAdaptiveMultiShellTargetCell
        length exponent target)
      (fun index outcome =>
        scaleAdaptiveBandActualInverseTargetLoad
          (support exponent) (2 ^ exponent) lower upper index outcome
            (length / 2 ^ exponent))
      target

/-- One actual prime target outside the finite ORIGINAL-scale bad union
receives the SUM of its true per-shell loads, at least `Σ F_j/8`.  Shell
factors may genuinely decay, supports may vary, and all weights are actual
`μθ/dθ(p)`.  Boundaries and the low physical endpoint are explicit. -/
theorem scaleAdaptiveMultiShellPrimeActualLoad_ge_euler_sum
    (exponents : Finset ℕ) (support : ℕ → Finset ℕ)
    (lower upper : ℝ) (length target : ℕ)
    (primes : ∀ exponent ∈ exponents,
      ∀ prime ∈ support exponent, prime.Prime)
    (target_prime : target.Prime)
    (target_high : target ≤ length)
    (scales_large : ∀ exponent ∈ exponents,
      2 ^ exponent ≤ length / 2 ^ exponent)
    (target_interior : ∀ exponent ∈ exponents,
      4 * (length / 2 ^ exponent) ≤ target)
    (not_boundaries : ∀ exponent ∈ exponents,
      target % (length / 2 ^ exponent) ≠ 0)
    (not_bad : target ∉ scaleAdaptiveMultiShellPrimeBadTargets
      exponents support lower upper length) :
    (∑ exponent ∈ exponents,
      adaptivePatternEulerFactor (support exponent)
        (2 ^ exponent)) / 8 ≤
      scaleAdaptiveMultiShellPrimeActualLoad
        exponents support lower upper length target := by
  unfold scaleAdaptiveMultiShellPrimeActualLoad
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro exponent selected
  let cell := scaleAdaptiveMultiShellTargetCell
    length exponent target
  let parity := scaleAdaptiveMultiShellTargetParity
    length exponent target
  let physicalScale := length / 2 ^ exponent
  have physical := scaleAdaptiveMultiShellTargetCell_physical
    length exponent target (scales_large exponent selected)
      (target_interior exponent selected) target_high
        (not_boundaries exponent selected)
  have cell_selected : cell ∈ scaleAdaptiveMultiShellValidCells exponent :=
    physical.1
  have parity_selected : parity ∈ Finset.range 2 := by
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_iff.mpr physical.2.1
  have target_selected := scaleAdaptiveMultiShellPrimeTarget_mem_actual_cell
    length exponent target target_prime
      (scales_large exponent selected)
      (target_interior exponent selected) target_high
        (not_boundaries exponent selected)
  have local_good : target ∉
      scaleAdaptiveBandPrimeBadTargets
        (support exponent) (2 ^ exponent) cell
          (scaleAdaptiveBandAdjacentTypedTargets 1 cell parity)
          (scaleAdaptiveBandActualInverseTargetLoad
            (support exponent) (2 ^ exponent) lower upper)
          physicalScale := by
    intro bad
    apply not_bad
    apply Finset.mem_biUnion.mpr
    refine ⟨exponent, selected, ?_⟩
    unfold scaleAdaptiveMultiShellPrimeCellBadTargets
    apply Finset.mem_biUnion.mpr
    refine ⟨cell, cell_selected, ?_⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨parity, parity_selected, bad⟩
  exact scaleAdaptiveBandPrimeOutcomeLoad_ge_outside_bad
    (support exponent) (2 ^ exponent) cell physicalScale target
      (scaleAdaptiveBandAdjacentTypedTargets 1 cell parity)
      (scaleAdaptiveBandActualInverseTargetLoad
        (support exponent) (2 ^ exponent) lower upper)
      (primes exponent selected)
      (mem_scaleAdaptiveMultiShellValidCells.mp cell_selected).1
      target_selected local_good

/-- The SAME actual supported semiprime target receives the exact SUM of
the genuine Euler-factor loads over every eligible dyadic shell.  Its
true pattern probabilities cancel type `s` shell-by-shell; no unsupported
type or duplicate prime label is counted. -/
theorem scaleAdaptiveMultiShellSemiprimeActualLoad_ge_euler_sum
    (exponents : Finset ℕ) (support : ℕ → Finset ℕ)
    (targetType : ℕ) (lower upper : ℝ)
    (length prime : ℕ)
    (primes : ∀ exponent ∈ exponents,
      ∀ label ∈ support exponent, label.Prime)
    (type_supported : ∀ exponent ∈ exponents,
      targetType ∈ support exponent)
    (target_prime : prime.Prime)
    (type_positive : 0 < targetType)
    (target_high : targetType * prime ≤ length)
    (scales_large : ∀ exponent ∈ exponents,
      2 ^ exponent ≤ length / 2 ^ exponent)
    (target_interior : ∀ exponent ∈ exponents,
      4 * (length / 2 ^ exponent) ≤ targetType * prime)
    (not_boundaries : ∀ exponent ∈ exponents,
      (targetType * prime) % (length / 2 ^ exponent) ≠ 0)
    (not_bad : targetType * prime ∉
      scaleAdaptiveMultiShellSemiprimeBadTargets
        exponents support targetType lower upper length) :
    (∑ exponent ∈ exponents,
      adaptivePatternEulerFactor (support exponent)
        (2 ^ exponent)) / 8 ≤
      scaleAdaptiveMultiShellSemiprimeActualLoad
        exponents support targetType lower upper length
          (targetType * prime) := by
  unfold scaleAdaptiveMultiShellSemiprimeActualLoad
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro exponent selected
  let target := targetType * prime
  let cell := scaleAdaptiveMultiShellTargetCell
    length exponent target
  let parity := scaleAdaptiveMultiShellTargetParity
    length exponent target
  let physicalScale := length / 2 ^ exponent
  have physical := scaleAdaptiveMultiShellTargetCell_physical
    length exponent target (scales_large exponent selected)
      (target_interior exponent selected) target_high
        (not_boundaries exponent selected)
  have cell_selected : cell ∈ scaleAdaptiveMultiShellValidCells exponent :=
    physical.1
  have parity_selected : parity ∈ Finset.range 2 := by
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_iff.mpr physical.2.1
  have target_selected :=
    scaleAdaptiveMultiShellSemiprimeTarget_mem_actual_cell
      length exponent targetType prime target_prime type_positive
        (scales_large exponent selected)
        (target_interior exponent selected) target_high
          (not_boundaries exponent selected)
  have local_good : target ∉
      scaleAdaptiveBandSemiprimeBadTargets
        (support exponent) targetType (2 ^ exponent) cell
          (scaleAdaptiveBandAdjacentTypedTargets
            targetType cell parity)
          (scaleAdaptiveBandActualInverseTargetLoad
            (support exponent) (2 ^ exponent) lower upper)
          physicalScale := by
    intro bad
    apply not_bad
    apply Finset.mem_biUnion.mpr
    refine ⟨exponent, selected, ?_⟩
    unfold scaleAdaptiveMultiShellSemiprimeCellBadTargets
    apply Finset.mem_biUnion.mpr
    refine ⟨cell, cell_selected, ?_⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨parity, parity_selected, bad⟩
  exact scaleAdaptiveBandSemiprimeOutcomeLoad_ge_outside_bad
    (2 ^ exponent) cell physicalScale target
      (scaleAdaptiveBandAdjacentTypedTargets targetType cell parity)
      (scaleAdaptiveBandActualInverseTargetLoad
        (support exponent) (2 ^ exponent) lower upper)
      (primes exponent selected) (type_supported exponent selected)
      (mem_scaleAdaptiveMultiShellValidCells.mp cell_selected).1
      target_selected local_good

/-- All ACTUAL moving open-cell boundaries of a finite dyadic shell
family.  These are true original integer targets, not a zero-measure
heuristic about real normalized cells. -/
noncomputable def scaleAdaptiveMultiShellBoundaryTargets
    (exponents : Finset ℕ) (length : ℕ) : Finset ℕ :=
  exponents.biUnion fun exponent =>
    scaleAdaptiveDyadicTargetBoundaries length exponent

/-- The complete finite union of genuine moving boundaries is negligible
at the ORIGINAL prime-target normalization. -/
theorem scaleAdaptiveMultiShellBoundaryTargets_global_tendsto_zero
    (exponents : Finset ℕ) :
    Tendsto
      (fun length : ℕ =>
        ((scaleAdaptiveMultiShellBoundaryTargets
          exponents length).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)) := by
  unfold scaleAdaptiveMultiShellBoundaryTargets
  apply scaleAdaptiveBandFiniteBadUnion_normalized_card_tendsto_zero
  intro exponent _
  exact scaleAdaptiveDyadicTargetBoundaries_normalized_tendsto_zero
    exponent

/-- Union of two actual original-scale zero-density target families;
their genuine finite cardinalities are charged without independence. -/
theorem scaleAdaptiveTwoBadTargetUnions_global_tendsto_zero
    (first second : ℕ → Finset ℕ)
    (first_zero : Tendsto
      (fun length : ℕ =>
        ((first length).card : ℝ) *
          Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)))
    (second_zero : Tendsto
      (fun length : ℕ =>
        ((second length).card : ℝ) *
          Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun length : ℕ =>
        ((first length ∪ second length).card : ℝ) *
          Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)) := by
  have combined : Tendsto
      (fun length : ℕ =>
        ((first length).card : ℝ) *
          Real.log (length : ℝ) / (length : ℝ) +
        ((second length).card : ℝ) *
          Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)) := by
    simpa using first_zero.add second_zero
  apply squeeze_zero' _ _ combined
  · filter_upwards [eventually_ge_atTop 2] with length large
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (Real.log_nonneg (by
          exact_mod_cast (show 1 ≤ length by omega))))
      (Nat.cast_nonneg _)
  · filter_upwards [eventually_ge_atTop 2] with length large
    have cardinal :
        ((first length ∪ second length).card : ℝ) ≤
          ((first length).card : ℝ) +
            ((second length).card : ℝ) := by
      exact_mod_cast Finset.card_union_le (first length) (second length)
    have weight_nonnegative :
        0 ≤ Real.log (length : ℝ) / (length : ℝ) := by
      apply div_nonneg
      · exact Real.log_nonneg (by
          exact_mod_cast (show 1 ≤ length by omega))
      · exact Nat.cast_nonneg _
    have weighted := mul_le_mul_of_nonneg_right cardinal weight_nonnegative
    calc
      _ = ((first length ∪ second length).card : ℝ) *
        (Real.log (length : ℝ) / (length : ℝ)) := by ring
      _ ≤ (((first length).card : ℝ) +
            ((second length).card : ℝ)) *
              (Real.log (length : ℝ) / (length : ℝ)) := weighted
      _ = _ := by ring

/-- One complete actual PRIME-target exceptional set, containing BOTH the
zero-density shared-outcome target failures and every moving cell boundary. -/
noncomputable def scaleAdaptiveMultiShellPrimeExceptions
    (exponents : Finset ℕ) (support : ℕ → Finset ℕ)
    (lower upper : ℝ) (length : ℕ) : Finset ℕ :=
  scaleAdaptiveMultiShellPrimeBadTargets
    exponents support lower upper length ∪
      scaleAdaptiveMultiShellBoundaryTargets exponents length

/-- One complete actual SEMIPRIME-target exceptional set, including all
genuine moving cell endpoints. -/
noncomputable def scaleAdaptiveMultiShellSemiprimeExceptions
    (exponents : Finset ℕ) (support : ℕ → Finset ℕ)
    (targetType : ℕ) (lower upper : ℝ) (length : ℕ) : Finset ℕ :=
  scaleAdaptiveMultiShellSemiprimeBadTargets
    exponents support targetType lower upper length ∪
      scaleAdaptiveMultiShellBoundaryTargets exponents length

/-- The COMPLETE prime-target exception, including endpoints, has density
zero at the ORIGINAL interval scale directly from the signed GTZ input. -/
theorem scaleAdaptiveMultiShellPrimeExceptions_global_tendsto_zero_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (exponents : Finset ℕ) (support : ℕ → Finset ℕ)
    (lower upper : ℝ)
    (primes : ∀ exponent ∈ exponents,
      ∀ prime ∈ support exponent, prime.Prime)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1) :
    Tendsto
      (fun length : ℕ =>
        ((scaleAdaptiveMultiShellPrimeExceptions
          exponents support lower upper length).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)) := by
  apply scaleAdaptiveTwoBadTargetUnions_global_tendsto_zero
  · exact scaleAdaptiveMultiShellPrimeBadTargets_global_tendsto_zero_of_GTZ
      green_tao exponents support lower upper primes
        lower_nonnegative band_nonempty upper_bounded
  · exact scaleAdaptiveMultiShellBoundaryTargets_global_tendsto_zero
      exponents

/-- The COMPLETE supported-semiprime-target exception, including all
endpoints, has density zero at the ORIGINAL interval scale. -/
theorem scaleAdaptiveMultiShellSemiprimeExceptions_global_tendsto_zero_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (exponents : Finset ℕ) (support : ℕ → Finset ℕ)
    (targetType : ℕ) (lower upper : ℝ)
    (primes : ∀ exponent ∈ exponents,
      ∀ prime ∈ support exponent, prime.Prime)
    (type_supported : ∀ exponent ∈ exponents,
      targetType ∈ support exponent)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1) :
    Tendsto
      (fun length : ℕ =>
        ((scaleAdaptiveMultiShellSemiprimeExceptions
          exponents support targetType lower upper length).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)) := by
  apply scaleAdaptiveTwoBadTargetUnions_global_tendsto_zero
  · exact
      scaleAdaptiveMultiShellSemiprimeBadTargets_global_tendsto_zero_of_GTZ
        green_tao exponents support targetType lower upper primes
          type_supported lower_nonnegative band_nonempty upper_bounded
  · exact scaleAdaptiveMultiShellBoundaryTargets_global_tendsto_zero
      exponents

/-- An actual positive target outside the finite shell-boundary exception
is not on ANY individual physical target-cell endpoint. -/
theorem scaleAdaptiveMultiShell_not_boundary_of_not_mem
    {exponents : Finset ℕ} {length target exponent : ℕ}
    (selected : exponent ∈ exponents)
    (positive : 0 < target)
    (bounded : target ≤ length)
    (not_boundary : target ∉
      scaleAdaptiveMultiShellBoundaryTargets exponents length) :
    target % (length / 2 ^ exponent) ≠ 0 := by
  intro divisible
  apply not_boundary
  apply Finset.mem_biUnion.mpr
  refine ⟨exponent, selected, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨by omega, bounded⟩, ?_⟩
  exact divisible

/-- The real prime-target load bound with ALL moving boundary assumptions
absorbed into the explicit original-density-zero exception. -/
theorem scaleAdaptiveMultiShellPrimeActualLoad_ge_euler_sum_of_good_target
    (exponents : Finset ℕ) (support : ℕ → Finset ℕ)
    (lower upper : ℝ) (length target : ℕ)
    (primes : ∀ exponent ∈ exponents,
      ∀ prime ∈ support exponent, prime.Prime)
    (target_prime : target.Prime)
    (target_high : target ≤ length)
    (scales_large : ∀ exponent ∈ exponents,
      2 ^ exponent ≤ length / 2 ^ exponent)
    (target_interior : ∀ exponent ∈ exponents,
      4 * (length / 2 ^ exponent) ≤ target)
    (not_exception : target ∉ scaleAdaptiveMultiShellPrimeExceptions
      exponents support lower upper length) :
    (∑ exponent ∈ exponents,
      adaptivePatternEulerFactor (support exponent)
        (2 ^ exponent)) / 8 ≤
      scaleAdaptiveMultiShellPrimeActualLoad
        exponents support lower upper length target := by
  have not_bad : target ∉ scaleAdaptiveMultiShellPrimeBadTargets
      exponents support lower upper length := by
    intro bad
    exact not_exception (Finset.mem_union_left _ bad)
  have not_boundaries : target ∉
      scaleAdaptiveMultiShellBoundaryTargets exponents length := by
    intro boundary
    exact not_exception (Finset.mem_union_right _ boundary)
  apply scaleAdaptiveMultiShellPrimeActualLoad_ge_euler_sum
    exponents support lower upper length target primes
      target_prime target_high scales_large target_interior _ not_bad
  intro exponent selected
  exact scaleAdaptiveMultiShell_not_boundary_of_not_mem
    selected target_prime.pos target_high not_boundaries

/-- The genuine semiprime-target load bound with EVERY moving cell
boundary absorbed into the explicit zero-density target exception. -/
theorem scaleAdaptiveMultiShellSemiprimeActualLoad_ge_euler_sum_of_good_target
    (exponents : Finset ℕ) (support : ℕ → Finset ℕ)
    (targetType : ℕ) (lower upper : ℝ)
    (length prime : ℕ)
    (primes : ∀ exponent ∈ exponents,
      ∀ label ∈ support exponent, label.Prime)
    (type_supported : ∀ exponent ∈ exponents,
      targetType ∈ support exponent)
    (target_prime : prime.Prime)
    (type_positive : 0 < targetType)
    (target_high : targetType * prime ≤ length)
    (scales_large : ∀ exponent ∈ exponents,
      2 ^ exponent ≤ length / 2 ^ exponent)
    (target_interior : ∀ exponent ∈ exponents,
      4 * (length / 2 ^ exponent) ≤ targetType * prime)
    (not_exception : targetType * prime ∉
      scaleAdaptiveMultiShellSemiprimeExceptions
        exponents support targetType lower upper length) :
    (∑ exponent ∈ exponents,
      adaptivePatternEulerFactor (support exponent)
        (2 ^ exponent)) / 8 ≤
      scaleAdaptiveMultiShellSemiprimeActualLoad
        exponents support targetType lower upper length
          (targetType * prime) := by
  have not_bad : targetType * prime ∉
      scaleAdaptiveMultiShellSemiprimeBadTargets
        exponents support targetType lower upper length := by
    intro bad
    exact not_exception (Finset.mem_union_left _ bad)
  have not_boundaries : targetType * prime ∉
      scaleAdaptiveMultiShellBoundaryTargets exponents length := by
    intro boundary
    exact not_exception (Finset.mem_union_right _ boundary)
  apply scaleAdaptiveMultiShellSemiprimeActualLoad_ge_euler_sum
    exponents support targetType lower upper length prime primes
      type_supported target_prime type_positive target_high
      scales_large target_interior _ not_bad
  intro exponent selected
  exact scaleAdaptiveMultiShell_not_boundary_of_not_mem
    selected (Nat.mul_pos type_positive target_prime.pos)
      target_high not_boundaries

/-- The exact shell sum for the TRUE scale-adaptive low family is the
genuine dyadic Mertens product sum; its support can vary with every
physical exponent without affecting this identity. -/
theorem scaleAdaptiveMultiShellLowEulerSum_eq_shellMass
    (lowerExponent upperExponent familyCutoff : ℕ) :
    (∑ exponent ∈ Finset.Ioc lowerExponent upperExponent,
      adaptivePatternEulerFactor
        (adaptiveLowPrimeSupport (2 ^ exponent) familyCutoff)
          (2 ^ exponent)) =
      scaleAdaptiveDyadicEulerShellMass lowerExponent upperExponent := by
  unfold scaleAdaptiveDyadicEulerShellMass
  apply Finset.sum_congr rfl
  intro exponent _
  exact scaleAdaptiveLowDyadicPatternEulerFactor_eq
    exponent familyCutoff

/-- The exact high-family shell sum retains its genuine fixed high support
AND the outside-prime local selector; this is the already audited true
short/long colored Euler-factor sum. -/
theorem scaleAdaptiveMultiShellHighEulerSum_eq_shellMass
    (lowerExponent upperExponent splitExponent fullExponent : ℕ) :
    (∑ exponent ∈ Finset.Ioc lowerExponent upperExponent,
      adaptivePatternEulerFactor
        (adaptiveHighPrimeSupport
          (2 ^ fullExponent) (2 ^ splitExponent))
          (2 ^ exponent)) =
      scaleAdaptiveHighDyadicEulerShellMass
        fullExponent splitExponent lowerExponent upperExponent := by
  rfl

/-- Actual LOW-color prime-target load from genuine disjoint physical
shells is at least ONE EIGHTH of the full true dyadic Mertens shell mass.
No uniform positive per-shell factor is asserted. -/
theorem scaleAdaptiveMultiShellLowPrimeActualLoad_ge_shellMass
    (lowerExponent upperExponent familyCutoff : ℕ)
    (lower upper : ℝ) (length target : ℕ)
    (target_prime : target.Prime)
    (target_high : target ≤ length)
    (scales_large : ∀ exponent ∈ Finset.Ioc lowerExponent upperExponent,
      2 ^ exponent ≤ length / 2 ^ exponent)
    (target_interior : ∀ exponent ∈ Finset.Ioc lowerExponent upperExponent,
      4 * (length / 2 ^ exponent) ≤ target)
    (not_exception : target ∉ scaleAdaptiveMultiShellPrimeExceptions
      (Finset.Ioc lowerExponent upperExponent)
      (fun exponent =>
        adaptiveLowPrimeSupport (2 ^ exponent) familyCutoff)
      lower upper length) :
    scaleAdaptiveDyadicEulerShellMass
      lowerExponent upperExponent / 8 ≤
        scaleAdaptiveMultiShellPrimeActualLoad
          (Finset.Ioc lowerExponent upperExponent)
          (fun exponent =>
            adaptiveLowPrimeSupport (2 ^ exponent) familyCutoff)
          lower upper length target := by
  rw [← scaleAdaptiveMultiShellLowEulerSum_eq_shellMass
    lowerExponent upperExponent familyCutoff]
  apply scaleAdaptiveMultiShellPrimeActualLoad_ge_euler_sum_of_good_target
    (Finset.Ioc lowerExponent upperExponent)
    (fun exponent =>
      adaptiveLowPrimeSupport (2 ^ exponent) familyCutoff)
    lower upper length target _ target_prime target_high
      scales_large target_interior not_exception
  intro exponent _ prime selected
  exact (mem_adaptiveLowPrimeSupport.mp selected).1

/-- Actual HIGH-color prime-target load is at least one eighth of its
correct genuine high-family shell mass, including the shrinking support
ratio at short scales and the constant `V_z` on long scales. -/
theorem scaleAdaptiveMultiShellHighPrimeActualLoad_ge_shellMass
    (lowerExponent upperExponent splitExponent fullExponent : ℕ)
    (lower upper : ℝ) (length target : ℕ)
    (target_prime : target.Prime)
    (target_high : target ≤ length)
    (scales_large : ∀ exponent ∈ Finset.Ioc lowerExponent upperExponent,
      2 ^ exponent ≤ length / 2 ^ exponent)
    (target_interior : ∀ exponent ∈ Finset.Ioc lowerExponent upperExponent,
      4 * (length / 2 ^ exponent) ≤ target)
    (not_exception : target ∉ scaleAdaptiveMultiShellPrimeExceptions
      (Finset.Ioc lowerExponent upperExponent)
      (fun _exponent =>
        adaptiveHighPrimeSupport
          (2 ^ fullExponent) (2 ^ splitExponent))
      lower upper length) :
    scaleAdaptiveHighDyadicEulerShellMass
      fullExponent splitExponent lowerExponent upperExponent / 8 ≤
        scaleAdaptiveMultiShellPrimeActualLoad
          (Finset.Ioc lowerExponent upperExponent)
          (fun _exponent =>
            adaptiveHighPrimeSupport
              (2 ^ fullExponent) (2 ^ splitExponent))
          lower upper length target := by
  rw [← scaleAdaptiveMultiShellHighEulerSum_eq_shellMass
    lowerExponent upperExponent splitExponent fullExponent]
  apply scaleAdaptiveMultiShellPrimeActualLoad_ge_euler_sum_of_good_target
    (Finset.Ioc lowerExponent upperExponent)
    (fun _exponent =>
      adaptiveHighPrimeSupport
        (2 ^ fullExponent) (2 ^ splitExponent))
    lower upper length target _ target_prime target_high
      scales_large target_interior not_exception
  intro exponent _ prime selected
  exact (mem_adaptiveHighPrimeSupport.mp selected).1

/-- Actual LOW-family semiprime load on EVERY shell where its genuine
small prime type is eligible.  The same true dyadic Euler mass arises after
the exact cancellation of the `F/s` sample probability with `s/i`. -/
theorem scaleAdaptiveMultiShellLowSemiprimeActualLoad_ge_shellMass
    (lowerExponent upperExponent familyCutoff targetType : ℕ)
    (lower upper : ℝ) (length prime : ℕ)
    (target_prime : prime.Prime)
    (type_prime : targetType.Prime)
    (type_cutoff : targetType ≤ familyCutoff)
    (type_eligible : ∀ exponent ∈ Finset.Ioc lowerExponent upperExponent,
      targetType ≤ 2 ^ exponent)
    (target_high : targetType * prime ≤ length)
    (scales_large : ∀ exponent ∈ Finset.Ioc lowerExponent upperExponent,
      2 ^ exponent ≤ length / 2 ^ exponent)
    (target_interior : ∀ exponent ∈ Finset.Ioc lowerExponent upperExponent,
      4 * (length / 2 ^ exponent) ≤ targetType * prime)
    (not_exception : targetType * prime ∉
      scaleAdaptiveMultiShellSemiprimeExceptions
        (Finset.Ioc lowerExponent upperExponent)
        (fun exponent =>
          adaptiveLowPrimeSupport (2 ^ exponent) familyCutoff)
        targetType lower upper length) :
    scaleAdaptiveDyadicEulerShellMass
      lowerExponent upperExponent / 8 ≤
        scaleAdaptiveMultiShellSemiprimeActualLoad
          (Finset.Ioc lowerExponent upperExponent)
          (fun exponent =>
            adaptiveLowPrimeSupport (2 ^ exponent) familyCutoff)
          targetType lower upper length (targetType * prime) := by
  rw [← scaleAdaptiveMultiShellLowEulerSum_eq_shellMass
    lowerExponent upperExponent familyCutoff]
  apply scaleAdaptiveMultiShellSemiprimeActualLoad_ge_euler_sum_of_good_target
    (Finset.Ioc lowerExponent upperExponent)
    (fun exponent =>
      adaptiveLowPrimeSupport (2 ^ exponent) familyCutoff)
    targetType lower upper length prime _ _ target_prime
      type_prime.pos target_high scales_large target_interior
        not_exception
  · intro exponent _ label selected
    exact (mem_adaptiveLowPrimeSupport.mp selected).1
  · intro exponent selected
    exact mem_adaptiveLowPrimeSupport.mpr
      ⟨type_prime, type_eligible exponent selected, type_cutoff⟩

/-- Actual HIGH-family semiprime load from the SAME fixed high support
and every genuine physical shell; its true short-scale support ratio is
never silently replaced by a constant. -/
theorem scaleAdaptiveMultiShellHighSemiprimeActualLoad_ge_shellMass
    (lowerExponent upperExponent splitExponent fullExponent targetType : ℕ)
    (lower upper : ℝ) (length prime : ℕ)
    (target_prime : prime.Prime)
    (type_prime : targetType.Prime)
    (above_split : 2 ^ splitExponent < targetType)
    (below_full : targetType ≤ 2 ^ fullExponent)
    (target_high : targetType * prime ≤ length)
    (scales_large : ∀ exponent ∈ Finset.Ioc lowerExponent upperExponent,
      2 ^ exponent ≤ length / 2 ^ exponent)
    (target_interior : ∀ exponent ∈ Finset.Ioc lowerExponent upperExponent,
      4 * (length / 2 ^ exponent) ≤ targetType * prime)
    (not_exception : targetType * prime ∉
      scaleAdaptiveMultiShellSemiprimeExceptions
        (Finset.Ioc lowerExponent upperExponent)
        (fun _exponent =>
          adaptiveHighPrimeSupport
            (2 ^ fullExponent) (2 ^ splitExponent))
        targetType lower upper length) :
    scaleAdaptiveHighDyadicEulerShellMass
      fullExponent splitExponent lowerExponent upperExponent / 8 ≤
        scaleAdaptiveMultiShellSemiprimeActualLoad
          (Finset.Ioc lowerExponent upperExponent)
          (fun _exponent =>
            adaptiveHighPrimeSupport
              (2 ^ fullExponent) (2 ^ splitExponent))
          targetType lower upper length (targetType * prime) := by
  rw [← scaleAdaptiveMultiShellHighEulerSum_eq_shellMass
    lowerExponent upperExponent splitExponent fullExponent]
  apply scaleAdaptiveMultiShellSemiprimeActualLoad_ge_euler_sum_of_good_target
    (Finset.Ioc lowerExponent upperExponent)
    (fun _exponent =>
      adaptiveHighPrimeSupport
        (2 ^ fullExponent) (2 ^ splitExponent))
    targetType lower upper length prime _ _ target_prime
      type_prime.pos target_high scales_large target_interior
        not_exception
  · intro exponent _ label selected
    exact (mem_adaptiveHighPrimeSupport.mp selected).1
  · intro exponent _
    exact mem_adaptiveHighPrimeSupport.mpr
      ⟨type_prime, above_split, below_full⟩

end Erdos1139

