module

public import ActualRightVertexSelectors433

@[expose] public section


/-!
# Genuine fixed-right endpoint and support-unit refinement

This bridge keeps the original manuscript endpoint `2*a*q ≤ n`, the
descending-prime non-underflow interval, both switched selectors, and both
actual support-unit exclusions.  Requiring those units loses at most
`2 * #S` genuine prime pairs.  No global degree estimate, sieve hypothesis,
or artificial selector equality is assumed.
-/

open Finset Filter
open scoped BigOperators Topology

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Erdos689

/-- On its true non-underflow interval, the finite-field fixed-right
selector is exactly the original pair of support-unit and switched
conditions, with the genuine descending natural prime value. -/
theorem actualRightVertexLocalResidues_mem_natCast_iff
    (p y bp a q : ℕ)
    (hp : p.Prime)
    (hunderflow : a * q ≤ y) :
    (q : ZMod p) ∈ actualRightVertexLocalResidues p y bp a ↔
      (¬ p ∣ q) ∧ (¬ p ∣ y - a * q) ∧
        (¬ bp ≡ 2 * (a * q) [MOD p]) ∧
          (¬ bp ≡ 2 * y [MOD p]) := by
  classical
  unfold actualRightVertexLocalResidues
  simp only [hp, ↓reduceDIte, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hq : (q : ZMod p) ≠ 0 ↔ ¬ p ∣ q :=
    not_congr (ZMod.natCast_eq_zero_iff q p)
  have hsub :
      ((y - a * q : ℕ) : ZMod p) =
        (y : ZMod p) - (a : ZMod p) * (q : ZMod p) := by
    rw [Nat.cast_sub hunderflow]
    push_cast
    rfl
  have hz :
      (y : ZMod p) - (a : ZMod p) * (q : ZMod p) ≠ 0 ↔
        ¬ p ∣ y - a * q := by
    rw [← hsub]
    exact not_congr (ZMod.natCast_eq_zero_iff (y - a * q) p)
  have hproduct :
      ((a * q : ℕ) : ZMod p) = (a : ZMod p) * (q : ZMod p) := by
    push_cast
    rfl
  rw [hq, hz, ← hproduct,
    zmod_switched_target_ne_iff_not_modEq,
    zmod_switched_target_ne_iff_not_modEq]

/-- Reducing a parameter modulo the actual support product does not change
any genuine support-prime finite-field coordinate. -/
theorem actualRightVertex_support_residue_natCast
    (S : Finset ℕ) (p q : ℕ) (hp : p ∈ S) :
    ((q % (∏ s ∈ S, s) : ℕ) : ZMod p) = (q : ZMod p) := by
  apply (ZMod.natCast_eq_natCast_iff
    (q % (∏ s ∈ S, s)) q p).mpr
  exact Nat.mod_mod_of_dvd q
    (Finset.dvd_prod_of_mem (fun s : ℕ => s) hp)

/-- At the actual canonical residue, the corrected selector is precisely the
old fixed-right switched selector plus the two genuine support-unit tests.
The second test refers to the real descending prime value. -/
theorem actualRightVertexUnitSelectorResidues_mem_mod_iff
    (S : Finset ℕ) (b : ℕ → ℕ) (y a q : ℕ)
    (hprime : ∀ p ∈ S, p.Prime)
    (hW : 0 < ∏ p ∈ S, p)
    (hunderflow : a * q ≤ y) :
    q % (∏ p ∈ S, p) ∈
        actualRightVertexUnitSelectorResidues S b y a ↔
      q % (∏ p ∈ S, p) ∈
          actualRightFiberSelectorResidues S b y a ∧
        (∀ p ∈ S, ¬ p ∣ q) ∧
          (∀ p ∈ S, ¬ p ∣ y - a * q) := by
  classical
  have hcanonical : q % (∏ p ∈ S, p) < ∏ p ∈ S, p :=
    Nat.mod_lt q hW
  have hlocal (p : ℕ) (hp : p ∈ S) :
      ((q % (∏ s ∈ S, s) : ℕ) : ZMod p) = (q : ZMod p) :=
    actualRightVertex_support_residue_natCast S p q hp
  constructor
  · intro hselector
    unfold actualRightVertexUnitSelectorResidues at hselector
    obtain ⟨_, hcoordinates⟩ := Finset.mem_filter.mp hselector
    have hall (p : ℕ) (hp : p ∈ S) :=
      (actualRightVertexLocalResidues_mem_natCast_iff
        p y (b p) a q (hprime p hp) hunderflow).mp
          (by rw [← hlocal p hp]; exact hcoordinates ⟨p, hp⟩)
    refine ⟨?_, fun p hp => (hall p hp).1,
      fun p hp => (hall p hp).2.1⟩
    apply (rightFiberSwitched_selector_iff_mem_actual_residues
      S b y a q hW).mp
    constructor
    · apply (switchedHits_zero_iff_forall_not_modEq
        S b (2 * a * q)).mpr
      intro p hp
      simpa [mul_assoc] using (hall p hp).2.2.1
    · apply (switchedHits_zero_iff_forall_not_modEq S b (2 * y)).mpr
      intro p hp
      exact (hall p hp).2.2.2
  · rintro ⟨hold, hqunit, hzunit⟩
    have hswitch :=
      (rightFiberSwitched_selector_iff_mem_actual_residues
        S b y a q hW).mpr hold
    have hleft :=
      (switchedHits_zero_iff_forall_not_modEq
        S b (2 * a * q)).mp hswitch.1
    have hright :=
      (switchedHits_zero_iff_forall_not_modEq
        S b (2 * y)).mp hswitch.2
    unfold actualRightVertexUnitSelectorResidues
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hcanonical, ?_⟩
    intro p
    rw [actualRightVertex_support_residue_natCast S p q p.property]
    apply (actualRightVertexLocalResidues_mem_natCast_iff
      p y (b p) a q (hprime p p.property) hunderflow).mpr
    exact ⟨hqunit p p.property, hzunit p p.property,
      by simpa [mul_assoc] using hleft p p.property,
      hright p p.property⟩

/-- The genuine edge-bounded fixed-right parameter family; the original
coefficient-sensitive manuscript condition `2*a*q ≤ n` is retained. -/
def edgeBoundedRightVertexPrimeParameters
    (S : Finset ℕ) (b : ℕ → ℕ) (n y a : ℕ) : Finset ℕ :=
  (rightFiberSwitchedPrimeParameters S b n y a).filter fun q =>
    2 * a * q ≤ n

/-- The exact natural parameter endpoint simultaneously retaining the true
graph cutoff and the descending-prime non-underflow cutoff. -/
def actualRightVertexSharpTruncation (n a y : ℕ) : ℕ :=
  min (n / (2 * a) + 1) (y / a + 1)

/-- Every parameter below the true edge-bounded endpoint is automatically
inside the non-underflow interval required by the descending sieve. -/
theorem actualRightVertexSharpTruncation_no_underflow
    (n a y : ℕ) (ha : 0 < a) :
    ∀ q < actualRightVertexSharpTruncation n a y, a * q ≤ y := by
  intro q hq
  have hupper : actualRightVertexSharpTruncation n a y ≤ y / a + 1 :=
    min_le_right _ _
  have hdiv : q ≤ y / a := by omega
  simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le ha).mp hdiv

/-- The actual right fiber equals its genuinely sharp selected descending
prime progression.  No enlargement to the old `n+1` endpoint occurs. -/
theorem edgeBoundedRightVertexPrimeParameters_eq_sharp_selected
    (S : Finset ℕ) (b : ℕ → ℕ) (n y a : ℕ)
    (hW : 0 < ∏ p ∈ S, p) (ha : 0 < a) :
    edgeBoundedRightVertexPrimeParameters S b n y a =
      (Finset.range (actualRightVertexSharpTruncation n a y)).filter
        fun q =>
          q % (∏ p ∈ S, p) ∈
            actualAdmissibleRightFiberSelectorResidues S b y a ∧
              q.Prime ∧ (y - a * q).Prime := by
  classical
  ext q
  simp only [edgeBoundedRightVertexPrimeParameters,
    rightFiberSwitchedPrimeParameters, rightFiberPrimeParameters,
    actualAdmissibleRightFiberSelectorResidues, Finset.mem_filter,
    Finset.mem_Icc, Finset.mem_range]
  have htwoa : 0 < 2 * a := by omega
  constructor
  · rintro ⟨⟨⟨⟨hqpos, hqn⟩, hqprime, hzprime⟩,
      hleft, hright⟩, hbound⟩
    have hproduct : a * q < y := Nat.sub_pos_iff_lt.mp hzprime.pos
    have hdivy : q ≤ y / a := by
      apply (Nat.le_div_iff_mul_le ha).mpr
      simpa [Nat.mul_comm] using hproduct.le
    have hdivn : q ≤ n / (2 * a) := by
      apply (Nat.le_div_iff_mul_le htwoa).mpr
      simpa [mul_assoc, mul_comm, mul_left_comm] using hbound
    have hselector :=
      (rightFiberSwitched_selector_iff_mem_actual_residues
        S b y a q hW).mp ⟨hleft, hright⟩
    have hresidue : a * (q % (∏ p ∈ S, p)) ≤ y :=
      (Nat.mul_le_mul_left a (Nat.mod_le q _)).trans hproduct.le
    refine ⟨?_, ⟨hselector, hresidue⟩, hqprime, hzprime⟩
    unfold actualRightVertexSharpTruncation
    omega
  · rintro ⟨hqbound, ⟨hselector, hresidue⟩, hqprime, hzprime⟩
    have hselectors :=
      (rightFiberSwitched_selector_iff_mem_actual_residues
        S b y a q hW).mpr hselector
    have hmax : actualRightVertexSharpTruncation n a y ≤
        n / (2 * a) + 1 := min_le_left _ _
    have hdiv : q ≤ n / (2 * a) := by omega
    have hmul : q * (2 * a) ≤ n :=
      (Nat.le_div_iff_mul_le htwoa).mp hdiv
    have hbound : 2 * a * q ≤ n := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
    have hqn : q ≤ n := by nlinarith
    exact ⟨⟨⟨⟨hqprime.one_le, hqn⟩, hqprime, hzprime⟩,
      hselectors.1, hselectors.2⟩, hbound⟩

/-- Actual descending prime-value exceptions indexed by support primes. -/
def actualRightVertexDescendingSupportExceptions
    (S : Finset ℕ) (N a y : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun q => y - a * q ∈ S

/-- On the genuine non-underflow interval a positive descending affine
function is injective, so at most `#S` prime parameters can have their
descending prime value equal to a support prime. -/
theorem actualRightVertexDescendingSupportExceptions_card_le
    (S : Finset ℕ) (N a y : ℕ)
    (ha : 0 < a)
    (hunderflow : ∀ q < N, a * q ≤ y) :
    (actualRightVertexDescendingSupportExceptions S N a y).card ≤ S.card := by
  classical
  let exceptions := actualRightVertexDescendingSupportExceptions S N a y
  have hinjective : Set.InjOn (fun q : ℕ => y - a * q)
      (↑exceptions : Set ℕ) := by
    intro q hq r hr heq
    have hqrange : q < N := Finset.mem_range.mp
      (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).1
    have hrrange : r < N := Finset.mem_range.mp
      (Finset.mem_filter.mp (Finset.mem_coe.mp hr)).1
    have hqbound := hunderflow q hqrange
    have hrbound := hunderflow r hrrange
    change y - a * q = y - a * r at heq
    have hmul : a * q = a * r := by omega
    exact Nat.mul_left_cancel ha hmul
  calc
    exceptions.card = (exceptions.image fun q => y - a * q).card :=
      (Finset.card_image_iff.mpr hinjective).symm
    _ ≤ S.card := by
      apply Finset.card_le_card
      intro z hz
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hq).2

/-- The actual corrected support-unit selector further restricted to residue
classes compatible with genuine descending non-underflow. -/
noncomputable def actualRightVertexAdmissibleUnitSelectorResidues
    (S : Finset ℕ) (b : ℕ → ℕ) (y a : ℕ) : Finset ℕ := by
  classical
  exact (actualRightVertexUnitSelectorResidues S b y a).filter
    fun q => a * q ≤ y

/-- A genuine prime failing its support-unit test must itself be one of
the finitely many actual support primes. -/
theorem actualRightVertex_prime_mem_support_of_not_unit
    (S : Finset ℕ) (q : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hq : q.Prime)
    (hnot : ¬ ∀ p ∈ S, ¬ p ∣ q) :
    q ∈ S := by
  classical
  simp only [not_forall, not_not] at hnot
  obtain ⟨p, hp, hdiv⟩ := hnot
  have heq : p = q :=
    (Nat.prime_dvd_prime_iff_eq (hsupport p hp) hq).mp hdiv
  exact heq ▸ hp

/-- Refining the real fixed-right switched selector to the actual two-unit
selector loses at most `2*#S` genuine prime pairs.  Both the moving prime
and the descending prime contribute their own independently bounded
support-prime exception family. -/
theorem actualRightVertexSelected_card_le_unit_refinement
    (S : Finset ℕ) (b : ℕ → ℕ) (N y a : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hW : 0 < ∏ p ∈ S, p)
    (ha : 0 < a)
    (hunderflow : ∀ q < N, a * q ≤ y) :
    (((Finset.range N).filter fun q =>
      q % (∏ p ∈ S, p) ∈
          actualAdmissibleRightFiberSelectorResidues S b y a ∧
        q.Prime ∧ (y - a * q).Prime).card) ≤
      (((Finset.range N).filter fun q =>
        q % (∏ p ∈ S, p) ∈
            actualRightVertexAdmissibleUnitSelectorResidues S b y a ∧
          q.Prime ∧ (y - a * q).Prime).card) + 2 * S.card := by
  classical
  let source := (Finset.range N).filter fun q =>
    q % (∏ p ∈ S, p) ∈
        actualAdmissibleRightFiberSelectorResidues S b y a ∧
      q.Prime ∧ (y - a * q).Prime
  let refined := (Finset.range N).filter fun q =>
    q % (∏ p ∈ S, p) ∈
        actualRightVertexAdmissibleUnitSelectorResidues S b y a ∧
      q.Prime ∧ (y - a * q).Prime
  let primeExceptions := (Finset.range N).filter fun q => q ∈ S
  let labelExceptions := actualRightVertexDescendingSupportExceptions S N a y
  have hsubset : source ⊆ refined ∪ (primeExceptions ∪ labelExceptions) := by
    intro q hq
    obtain ⟨hqrange, hresidue, hqprime, hzprime⟩ :=
      Finset.mem_filter.mp hq
    have hqN : q < N := Finset.mem_range.mp hqrange
    have hqbound := hunderflow q hqN
    obtain ⟨hold, hresiduebound⟩ := Finset.mem_filter.mp hresidue
    by_cases hqunit : ∀ p ∈ S, ¬ p ∣ q
    · by_cases hzunit : ∀ p ∈ S, ¬ p ∣ y - a * q
      · apply Finset.mem_union_left
        apply Finset.mem_filter.mpr
        refine ⟨hqrange, ?_, hqprime, hzprime⟩
        unfold actualRightVertexAdmissibleUnitSelectorResidues
        apply Finset.mem_filter.mpr
        exact ⟨(actualRightVertexUnitSelectorResidues_mem_mod_iff
          S b y a q hsupport hW hqbound).mpr
            ⟨hold, hqunit, hzunit⟩, hresiduebound⟩
      · apply Finset.mem_union_right
        apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        exact ⟨hqrange,
          actualRightVertex_prime_mem_support_of_not_unit
            S (y - a * q) hsupport hzprime hzunit⟩
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
    actualRightVertexDescendingSupportExceptions_card_le
      S N a y ha hunderflow
  have hcard := Finset.card_le_card hsubset
  have hunion := Finset.card_union_le refined (primeExceptions ∪ labelExceptions)
  have hexception := Finset.card_union_le primeExceptions labelExceptions
  change source.card ≤ refined.card + 2 * S.card
  omega

/-- The original edge-bounded right fiber injects into the genuine sharp
support-unit-selected prime progression, with exactly the two unavoidable
finite support-prime exception families retained. -/
theorem edgeBoundedRightVertexPrimeParameters_card_le_unit_progression
    (S : Finset ℕ) (b : ℕ → ℕ) (n y a : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hW : 0 < ∏ p ∈ S, p)
    (ha : 0 < a) :
    (edgeBoundedRightVertexPrimeParameters S b n y a).card ≤
      (((Finset.range (actualRightVertexSharpTruncation n a y)).filter
        fun q =>
          q % (∏ p ∈ S, p) ∈
            actualRightVertexAdmissibleUnitSelectorResidues S b y a ∧
              q.Prime ∧ (y - a * q).Prime).card) + 2 * S.card := by
  rw [edgeBoundedRightVertexPrimeParameters_eq_sharp_selected
    S b n y a hW ha]
  exact actualRightVertexSelected_card_le_unit_refinement S b
    (actualRightVertexSharpTruncation n a y) y a hsupport hW ha
    (actualRightVertexSharpTruncation_no_underflow n a y ha)

/-- The true fixed-right truncation retains its indispensable `1/(2*a)`
graph-endpoint factor, with at most one natural rounding unit. -/
theorem actualRightVertexSharpTruncation_real_le
    (n y a : ℕ) (_ha : 0 < a) :
    (actualRightVertexSharpTruncation n a y : ℝ) ≤
      (n : ℝ) / (2 * (a : ℝ)) + 1 := by
  have htrunc : actualRightVertexSharpTruncation n a y ≤
      n / (2 * a) + 1 := min_le_left _ _
  have hcast :
      (actualRightVertexSharpTruncation n a y : ℝ) ≤
        ((n / (2 * a) + 1 : ℕ) : ℝ) := by
    exact_mod_cast htrunc
  have hdiv : ((n / (2 * a) : ℕ) : ℝ) ≤
      (n : ℝ) / ((2 * a : ℕ) : ℝ) := Nat.cast_div_le
  push_cast at hcast hdiv
  linarith

/-- Normalizing by the *actual* switched support product preserves the
sharp fixed-right `1/(2*a*W)` coefficient and loses at most two endpoint
units. -/
theorem actualRightVertexSharpTruncation_support_normalized_le
    (S : Finset ℕ) (n y a : ℕ)
    (hW : 0 < ∏ p ∈ S, p) (ha : 0 < a) :
    (actualRightVertexSharpTruncation n a y : ℝ) /
        (((∏ p ∈ S, p) : ℕ) : ℝ) + 1 ≤
      (n : ℝ) /
        (2 * (a : ℝ) * (((∏ p ∈ S, p) : ℕ) : ℝ)) + 2 := by
  have hWreal : (0 : ℝ) < ((∏ p ∈ S, p) : ℕ) := by
    exact_mod_cast hW
  have hWone : (1 : ℝ) ≤ ((∏ p ∈ S, p) : ℕ) := by
    exact_mod_cast hW
  have hendpoint := actualRightVertexSharpTruncation_real_le n y a ha
  have hfraction :
      (1 : ℝ) / (((∏ p ∈ S, p) : ℕ) : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hWreal).mpr
    linarith
  calc
    (actualRightVertexSharpTruncation n a y : ℝ) /
        (((∏ p ∈ S, p) : ℕ) : ℝ) + 1 ≤
      ((n : ℝ) / (2 * (a : ℝ)) + 1) /
        (((∏ p ∈ S, p) : ℕ) : ℝ) + 1 := by gcongr
    _ = (n : ℝ) /
          (2 * (a : ℝ) * (((∏ p ∈ S, p) : ℕ) : ℝ)) +
        1 / (((∏ p ∈ S, p) : ℕ) : ℝ) + 1 := by
      field_simp
    _ ≤ (n : ℝ) /
          (2 * (a : ℝ) * (((∏ p ∈ S, p) : ℕ) : ℝ)) + 2 := by
      linarith

/-- Full optimized descending Selberg bound for the *actual edge-bounded*
fixed-right graph fiber.  Its leading term contains the exact actual
support-unit selector and indispensable `1/(2*a*W)` endpoint.  The genuine
cutoff-fourth-power, small-sieve-prime, and `2*#S` support-prime errors
all remain explicit. -/
theorem edgeBoundedRightVertexPrimeParameters_card_le_unit_selected_sieve
    (S P : Finset ℕ) (b : ℕ → ℕ) (M n z y a : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hW : 0 < ∏ p ∈ S, p)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z)
    (ha : ∀ p ∈ P, ¬ p ∣ a)
    (hy : ∀ p ∈ P, ¬ p ∣ y)
    (hM : 2 ∣ M)
    (hPM : Nat.Coprime (∏ p ∈ P, p) M)
    (hWM : (∏ p ∈ S, p) ∣ M)
    (hprimes : ∀ p : ℕ, p.Prime →
      (p ∣ ∏ q ∈ P, q ↔ p ≤ z ∧ Nat.Coprime p M))
    (hapositive : 0 < a) :
    ((edgeBoundedRightVertexPrimeParameters S b n y a).card : ℝ) ≤
      ((actualRightVertexUnitSelectorResidues S b y a).card : ℝ) *
        (((n : ℝ) /
            (2 * (a : ℝ) * (((∏ p ∈ S, p) : ℕ) : ℝ)) + 2) /
          twoRootSelbergDenominator M z + (z : ℝ) ^ 4 +
            ((2 * Nat.primeCounting z : ℕ) : ℝ)) +
        ((2 * S.card : ℕ) : ℝ) := by
  let N := actualRightVertexSharpTruncation n a y
  let residues := actualRightVertexAdmissibleUnitSelectorResidues S b y a
  have hfinite := edgeBoundedRightVertexPrimeParameters_card_le_unit_progression
    S b n y a hsupport hW hapositive
  have hfiniteReal :
      ((edgeBoundedRightVertexPrimeParameters S b n y a).card : ℝ) ≤
        ((((Finset.range N).filter fun q =>
          q % (∏ p ∈ S, p) ∈ residues ∧
            q.Prime ∧ (y - a * q).Prime).card : ℕ) : ℝ) +
          ((2 * S.card : ℕ) : ℝ) := by
    exact_mod_cast hfinite
  have hsieve := actualMixedAffineSelected_prime_pair_card_le_density
    P residues M N z (∏ p ∈ S, p) a y hW
    (by
      intro r hr
      obtain ⟨hunit, hbound⟩ := Finset.mem_filter.mp hr
      unfold actualRightVertexUnitSelectorResidues at hunit
      obtain ⟨hrange, _⟩ := Finset.mem_filter.mp hunit
      exact ⟨Finset.mem_range.mp hrange, hbound⟩)
    hprime hlarge hz ha hy
    (actualRightVertexSharpTruncation_no_underflow n a y hapositive)
      hM hPM hWM hprimes hapositive
  have hresidues : residues.card ≤
      (actualRightVertexUnitSelectorResidues S b y a).card := by
    exact Finset.card_filter_le _ _
  have hresiduesReal : (residues.card : ℝ) ≤
      ((actualRightVertexUnitSelectorResidues S b y a).card : ℝ) := by
    exact_mod_cast hresidues
  have hdenominator : 0 ≤ twoRootSelbergDenominator M z :=
    twoRootSelbergDenominator_nonneg hM z
  have hterm :
      0 ≤ (((n : ℝ) /
            (2 * (a : ℝ) * (((∏ p ∈ S, p) : ℕ) : ℝ)) + 2) /
          twoRootSelbergDenominator M z + (z : ℝ) ^ 4 +
            ((2 * Nat.primeCounting z : ℕ) : ℝ)) := by positivity
  calc
    ((edgeBoundedRightVertexPrimeParameters S b n y a).card : ℝ) ≤
        ((((Finset.range N).filter fun q =>
          q % (∏ p ∈ S, p) ∈ residues ∧
            q.Prime ∧ (y - a * q).Prime).card : ℕ) : ℝ) +
          ((2 * S.card : ℕ) : ℝ) := hfiniteReal
    _ ≤ (residues.card : ℝ) *
          (((N : ℝ) / (((∏ p ∈ S, p) : ℕ) : ℝ) + 1) /
            twoRootSelbergDenominator M z + (z : ℝ) ^ 4 +
              ((2 * Nat.primeCounting z : ℕ) : ℝ)) +
            ((2 * S.card : ℕ) : ℝ) := by linarith
    _ ≤ (residues.card : ℝ) *
          (((n : ℝ) /
              (2 * (a : ℝ) * (((∏ p ∈ S, p) : ℕ) : ℝ)) + 2) /
            twoRootSelbergDenominator M z + (z : ℝ) ^ 4 +
              ((2 * Nat.primeCounting z : ℕ) : ℝ)) +
            ((2 * S.card : ℕ) : ℝ) := by
      have hendpoint :
          (N : ℝ) / (((∏ p ∈ S, p) : ℕ) : ℝ) + 1 ≤
            (n : ℝ) /
              (2 * (a : ℝ) * (((∏ p ∈ S, p) : ℕ) : ℝ)) + 2 := by
        exact actualRightVertexSharpTruncation_support_normalized_le
          S n y a hW hapositive
      have hdivision := div_le_div_of_nonneg_right hendpoint hdenominator
      have hfull := add_le_add_right
        (add_le_add_right hdivision ((z : ℝ) ^ 4))
          ((2 * Nat.primeCounting z : ℕ) : ℝ)
      have hcardnonnegative : (0 : ℝ) ≤ residues.card := by exact_mod_cast
        (Nat.zero_le residues.card)
      nlinarith [mul_le_mul_of_nonneg_left hfull hcardnonnegative]
    _ ≤ _ := by
      nlinarith [mul_le_mul_of_nonneg_right hresiduesReal hterm]

/-- The actual right graph fiber injects into the union of all genuinely
edge-bounded coefficient-parameter fibers; in particular every resulting
fiber still contains the indispensable original condition `2*a*q ≤ n`. -/
theorem manuscriptEdge_right_fiber_card_le_edgeBoundedRight_parameter_sum
    {S : Finset ℕ} {b : ℕ → ℕ} {n : ℕ} {τ ell : ℝ}
    (E : Finset TripleEdge) (y : ℕ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hactual : ∀ e ∈ E, manuscriptEdge S b n τ ell e) :
    (E.filter fun e => e.2.1 = y).card ≤
      ∑ a ∈ (∏ s ∈ S, s).divisors,
        (edgeBoundedRightVertexPrimeParameters S b n y a).card := by
  classical
  let W := ∏ s ∈ S, s
  let fiber := E.filter fun e => e.2.1 = y
  let parameterVertices : ℕ → Finset ℕ := fun a =>
    (edgeBoundedRightVertexPrimeParameters S b n y a).image
      (fun q => a * q)
  have hW : 0 < W := Finset.prod_pos fun s hs => (hsupport s hs).pos
  have hinjective := manuscriptEdge_left_injective_on_right_fiber E y hactual
  have hsubset : fiber.image (fun e : TripleEdge => e.1) ⊆
      W.divisors.biUnion parameterVertices := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨heE, hey⟩ := Finset.mem_filter.mp he
    obtain ⟨hlabelprime, hrelation, hleftbound, _, hleftmiss,
      hrightmiss, _, _, ⟨a, q, ha, hq, hrepr⟩, _⟩ := hactual e heE
    have hapos : 0 < a := Nat.pos_of_dvd_of_pos ha hW
    have hqleft : q ≤ e.1 := by
      rw [hrepr]
      exact Nat.le_mul_of_pos_left q hapos
    have hqn : q ≤ n := by omega
    have hlabel : y - a * q = e.2.2 := by omega
    have hlefttarget : 2 * e.1 = 2 * a * q := by
      rw [hrepr]
      ring
    rw [hlefttarget] at hleftmiss
    rw [hey] at hrightmiss
    apply Finset.mem_biUnion.mpr
    refine ⟨a, Nat.mem_divisors.mpr ⟨ha, Nat.ne_of_gt hW⟩, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨q, Finset.mem_filter.mpr ?_, hrepr.symm⟩
    refine ⟨Finset.mem_filter.mpr ?_, ?_⟩
    · exact ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hq.one_le, hqn⟩,
          hq, hlabel.symm ▸ hlabelprime⟩, hleftmiss, hrightmiss⟩
    · omega
  calc
    fiber.card = (fiber.image fun e : TripleEdge => e.1).card :=
      (Finset.card_image_iff.mpr hinjective).symm
    _ ≤ (W.divisors.biUnion parameterVertices).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ a ∈ W.divisors, (parameterVertices a).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ a ∈ W.divisors,
        (edgeBoundedRightVertexPrimeParameters S b n y a).card := by
      apply Finset.sum_le_sum
      intro a _
      exact Finset.card_image_le

#print axioms Erdos689.actualRightVertexLocalResidues_mem_natCast_iff
#print axioms Erdos689.actualRightVertex_support_residue_natCast
#print axioms Erdos689.actualRightVertexUnitSelectorResidues_mem_mod_iff
#print axioms Erdos689.actualRightVertexSharpTruncation_no_underflow
#print axioms Erdos689.edgeBoundedRightVertexPrimeParameters_eq_sharp_selected
#print axioms Erdos689.actualRightVertexDescendingSupportExceptions_card_le
#print axioms Erdos689.actualRightVertex_prime_mem_support_of_not_unit
#print axioms Erdos689.actualRightVertexSelected_card_le_unit_refinement
#print axioms Erdos689.edgeBoundedRightVertexPrimeParameters_card_le_unit_progression
#print axioms Erdos689.actualRightVertexSharpTruncation_real_le
#print axioms Erdos689.actualRightVertexSharpTruncation_support_normalized_le
#print axioms Erdos689.edgeBoundedRightVertexPrimeParameters_card_le_unit_selected_sieve
#print axioms Erdos689.manuscriptEdge_right_fiber_card_le_edgeBoundedRight_parameter_sum

end Erdos689
