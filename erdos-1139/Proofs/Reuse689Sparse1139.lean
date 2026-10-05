module

public import GoalRootSparseLimsup433

@[expose] public section


/-!
# Exact sparse reserve cleanup for the original Erdős #1139 obstruction

The already proved #689 theorem only supplies coverings with primorial
conductor, whose logarithmic cost is linear in the covered length.  It cannot
by itself discharge the sublinear-conductor hypothesis for #1139.  This file
instead isolates and proves the finite reserve-cleanup step: an arbitrary
mixed prime/prime-square partial core can be completed using two fresh prime
labels per deficient target, with every selected prime and its actual
conductor charged explicitly.

No prime-pattern estimate, matching theorem, asymptotic reserve supply, or
unconditional solution of #1139 is asserted.
-/

open Finset Filter
open scoped ArithmeticFunction.Omega Topology

namespace Erdos1139

/-- Targets on the literal original closed interval that have fewer than
two genuine mixed broad/nested-square residue hits from the current core. -/
def deficientTargets (y : ℕ) (P squared : Finset ℕ) (a : ℕ → ℕ) : Finset ℕ :=
  (Finset.Icc 1 y).filter fun h =>
    (P.filter fun p => a p ≡ h [MOD p]).card +
      (squared.filter fun p => a p ≡ h [MOD p ^ 2]).card < 2

/-- Any finite fresh-prime supply of at least twice the number of deficient
targets admits a genuinely injective pair of reserve labels for every target.
The embedding keeps its entire range inside the actual supplied prime set. -/
theorem reserve_pair_embedding_of_card
    (D R : Finset ℕ) (capacity : 2 * D.card ≤ R.card) :
    ∃ assignment : (↥D × Bool) ↪ ℕ,
      Set.range assignment ⊆ (R : Set ℕ) := by
  apply Function.Embedding.exists_of_card_le_finset
  simpa [Fintype.card_prod, Fintype.card_bool, Nat.mul_comm] using capacity

/-- The exact set of selected reserve primes: one distinct label for each
deficient-target/Boolean-color pair. -/
noncomputable def selectedReserveLabels
    (D : Finset ℕ) (assignment : (↥D × Bool) ↪ ℕ) : Finset ℕ :=
  Finset.univ.map assignment

/-- The cleanup selects exactly twice the number of deficient targets; no
reserve-prime collisions or hidden duplicate-label savings are assumed. -/
theorem selectedReserveLabels_card
    (D : Finset ℕ) (assignment : (↥D × Bool) ↪ ℕ) :
    (selectedReserveLabels D assignment).card = 2 * D.card := by
  simp [selectedReserveLabels, Fintype.card_prod, Fintype.card_bool,
    Nat.mul_comm]

/-- Coherent residue attached to an actual selected reserve prime.  The
injective assignment guarantees that its deficient target is unique. -/
noncomputable def reserveAssignmentResidue
    (D : Finset ℕ) (assignment : (↥D × Bool) ↪ ℕ) (p : ℕ) : ℕ :=
  if witness : ∃ target : ↥D × Bool, assignment target = p then
    (Classical.choose witness).1.val
  else 0

/-- Both differently colored reserve labels for a given target receive
exactly that target's residue, with equality and hence its true congruence. -/
theorem reserveAssignmentResidue_apply
    (D : Finset ℕ) (assignment : (↥D × Bool) ↪ ℕ)
    (target : ↥D × Bool) :
    reserveAssignmentResidue D assignment (assignment target) =
      target.1.val := by
  have witness : ∃ other : ↥D × Bool,
      assignment other = assignment target := ⟨target, rfl⟩
  unfold reserveAssignmentResidue
  rw [dif_pos witness]
  have same : Classical.choose witness = target :=
    assignment.injective (Classical.choose_spec witness)
  rw [same]

/-- Exact deterministic cleanup for an arbitrary mixed partial core.  Every
deficient target receives TWO genuinely distinct fresh prime labels from the
available supply.  Existing nested square residues remain coherent; selected
reserve labels are used to exponent one; and the complete CRT conductor is
exactly the old conductor multiplied by the actual newly selected primes. -/
theorem complete_partial_core_with_fresh_reserve
    (y : ℕ) (P squared R : Finset ℕ) (a : ℕ → ℕ)
    (core_primes : ∀ p ∈ P, p.Prime)
    (square_support : squared ⊆ P)
    (reserve_primes : ∀ p ∈ R, p.Prime)
    (fresh : Disjoint P R)
    (capacity : 2 * (deficientTargets y P squared a).card ≤ R.card) :
    ∃ (completed : Finset ℕ) (residue : ℕ → ℕ),
      UnrestrictedPrimeSquareDoubleCover y completed squared residue ∧
      P ⊆ completed ∧
      (completed \ P).card =
        2 * (deficientTargets y P squared a).card ∧
      completed \ P ⊆ R ∧
      (∏ p ∈ completed, selectedPrimePower squared p) =
        (∏ p ∈ P, selectedPrimePower squared p) *
          ∏ p ∈ completed \ P, p := by
  classical
  let D := deficientTargets y P squared a
  obtain ⟨assignment, range_in_reserve⟩ :=
    reserve_pair_embedding_of_card D R capacity
  let T := selectedReserveLabels D assignment
  have selected_in_reserve : T ⊆ R := by
    intro p hp
    obtain ⟨target, _, htarget⟩ := Finset.mem_map.mp hp
    apply range_in_reserve
    exact ⟨target, htarget⟩
  have disjoint : Disjoint P T := by
    apply Finset.disjoint_left.mpr
    intro p hp hselected
    exact Finset.disjoint_left.mp fresh hp (selected_in_reserve hselected)
  let residue : ℕ → ℕ := fun p =>
    if p ∈ P then a p else reserveAssignmentResidue D assignment p
  have difference : (P ∪ T) \ P = T := by
    ext p
    by_cases hp : p ∈ P
    · have hnot : p ∉ T := Finset.disjoint_left.mp disjoint hp
      simp [hp, hnot]
    · simp [hp]
  refine ⟨P ∪ T, residue, ?_, Finset.subset_union_left,
    ?_, ?_, ?_⟩
  · refine ⟨?_, fun p hp => Finset.mem_union_left _ (square_support hp), ?_⟩
    · intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact core_primes p hp
      · exact reserve_primes p (selected_in_reserve hp)
    · intro h hh
      by_cases bad : h ∈ D
      · let target_false : ↥D × Bool := (⟨h, bad⟩, false)
        let target_true : ↥D × Bool := (⟨h, bad⟩, true)
        have first_selected : assignment target_false ∈ T := by
          exact Finset.mem_map.mpr ⟨target_false, Finset.mem_univ _, rfl⟩
        have second_selected : assignment target_true ∈ T := by
          exact Finset.mem_map.mpr ⟨target_true, Finset.mem_univ _, rfl⟩
        have first_fresh : assignment target_false ∉ P := by
          intro hp
          exact Finset.disjoint_left.mp disjoint hp first_selected
        have second_fresh : assignment target_true ∉ P := by
          intro hp
          exact Finset.disjoint_left.mp disjoint hp second_selected
        have first_hit : residue (assignment target_false) ≡ h
            [MOD assignment target_false] := by
          dsimp [residue]
          rw [if_neg first_fresh, reserveAssignmentResidue_apply]
        have second_hit : residue (assignment target_true) ≡ h
            [MOD assignment target_true] := by
          dsimp [residue]
          rw [if_neg second_fresh, reserveAssignmentResidue_apply]
        have distinct : assignment target_false ≠ assignment target_true := by
          intro equality
          have same := assignment.injective equality
          have colors := congrArg Prod.snd same
          cases colors
        have at_least_two :
            1 < ((P ∪ T).filter fun p => residue p ≡ h [MOD p]).card := by
          apply Finset.one_lt_card.mpr
          refine ⟨assignment target_false, ?_, assignment target_true, ?_,
            distinct⟩
          · exact Finset.mem_filter.mpr
              ⟨Finset.mem_union_right P first_selected, first_hit⟩
          · exact Finset.mem_filter.mpr
              ⟨Finset.mem_union_right P second_selected, second_hit⟩
        omega
      · have core_good :
            2 ≤ (P.filter fun p => a p ≡ h [MOD p]).card +
              (squared.filter fun p => a p ≡ h [MOD p ^ 2]).card := by
          by_contra hbad
          have strict :
              (P.filter fun p => a p ≡ h [MOD p]).card +
                (squared.filter fun p => a p ≡ h [MOD p ^ 2]).card < 2 := by
            omega
          exact bad (Finset.mem_filter.mpr ⟨hh, strict⟩)
        have broad_monotone :
            (P.filter fun p => a p ≡ h [MOD p]).card ≤
              ((P ∪ T).filter fun p => residue p ≡ h [MOD p]).card := by
          apply Finset.card_le_card
          intro p hp
          obtain ⟨hcore, hhit⟩ := Finset.mem_filter.mp hp
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_union_left _ hcore, ?_⟩
          simpa [residue, hcore] using hhit
        have square_monotone :
            (squared.filter fun p => a p ≡ h [MOD p ^ 2]).card ≤
              (squared.filter fun p => residue p ≡ h [MOD p ^ 2]).card := by
          apply Finset.card_le_card
          intro p hp
          obtain ⟨hsquare, hhit⟩ := Finset.mem_filter.mp hp
          apply Finset.mem_filter.mpr
          refine ⟨hsquare, ?_⟩
          simpa [residue, square_support hsquare] using hhit
        exact core_good.trans (Nat.add_le_add broad_monotone square_monotone)
  · rw [difference]
    exact selectedReserveLabels_card D assignment
  · rw [difference]
    exact selected_in_reserve
  · rw [difference, Finset.prod_union disjoint]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    have not_squared : p ∉ squared := by
      intro hsquare
      exact Finset.disjoint_left.mp disjoint (square_support hsquare) hp
    simp [selectedPrimePower, selectedPrimeExponent, not_squared]

/-- Every actual selected reserve prime costs at most the logarithm of its
common genuine upper bound.  The empty-supply and zero-bound edge case is
handled without pretending that `log 0` is monotone. -/
theorem prime_product_log_le_card_mul_log_bound
    (R : Finset ℕ) (B : ℕ)
    (primes : ∀ p ∈ R, p.Prime)
    (bounded : ∀ p ∈ R, p ≤ B) :
    Real.log ((∏ p ∈ R, p : ℕ) : ℝ) ≤
      (R.card : ℝ) * Real.log (B : ℝ) := by
  have nonzero : ∀ p ∈ R, (p : ℝ) ≠ 0 := by
    intro p hp
    exact_mod_cast (primes p hp).ne_zero
  calc
    Real.log ((∏ p ∈ R, p : ℕ) : ℝ) =
        Real.log (∏ p ∈ R, (p : ℝ)) := by simp
    _ = ∑ p ∈ R, Real.log (p : ℝ) := Real.log_prod nonzero
    _ ≤ ∑ _p ∈ R, Real.log (B : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp_positive : 0 < (p : ℝ) := by
        exact_mod_cast (primes p hp).pos
      have hB_positive : 0 < (B : ℝ) := by
        have hB_nat : 0 < B := lt_of_lt_of_le (primes p hp).pos (bounded p hp)
        exact_mod_cast hB_nat
      have hcast : (p : ℝ) ≤ (B : ℝ) := by
        exact_mod_cast bounded p hp
      exact Real.strictMonoOn_log.monotoneOn hp_positive hB_positive hcast
    _ = (R.card : ℝ) * Real.log (B : ℝ) := by simp

/-- The exact quantitative cleanup estimate used by the informal proof.
The complete selected mixed conductor costs at most the old actual core
conductor plus `2 * (# deficient targets) * log B`; every reserve prime is
real, fresh, distinct, at most `B`, and paid for to exponent one. -/
theorem complete_partial_core_with_bounded_reserve_cost
    (y : ℕ) (P squared R : Finset ℕ) (a : ℕ → ℕ) (B : ℕ)
    (core_primes : ∀ p ∈ P, p.Prime)
    (square_support : squared ⊆ P)
    (reserve_primes : ∀ p ∈ R, p.Prime)
    (fresh : Disjoint P R)
    (capacity : 2 * (deficientTargets y P squared a).card ≤ R.card)
    (bounded : ∀ p ∈ R, p ≤ B) :
    ∃ (completed : Finset ℕ) (residue : ℕ → ℕ),
      UnrestrictedPrimeSquareDoubleCover y completed squared residue ∧
      P ⊆ completed ∧
      (completed \ P).card =
        2 * (deficientTargets y P squared a).card ∧
      Real.log ((∏ p ∈ completed, selectedPrimePower squared p : ℕ) : ℝ) ≤
        Real.log ((∏ p ∈ P, selectedPrimePower squared p : ℕ) : ℝ) +
          (2 * ((deficientTargets y P squared a).card : ℝ)) *
            Real.log (B : ℝ) := by
  obtain ⟨completed, residue, cover, core_subset,
    selected_card, selected_subset, exact_conductor⟩ :=
    complete_partial_core_with_fresh_reserve y P squared R a
      core_primes square_support reserve_primes fresh capacity
  refine ⟨completed, residue, cover, core_subset, selected_card, ?_⟩
  let core : ℕ := ∏ p ∈ P, selectedPrimePower squared p
  let selected : ℕ := ∏ p ∈ completed \ P, p
  have core_positive : 0 < core := by
    dsimp [core]
    exact Finset.prod_pos fun p hp => pow_pos (core_primes p hp).pos _
  have selected_positive : 0 < selected := by
    dsimp [selected]
    exact Finset.prod_pos fun p hp =>
      (reserve_primes p (selected_subset hp)).pos
  have core_real_positive : 0 < (core : ℝ) := by
    exact_mod_cast core_positive
  have selected_real_positive : 0 < (selected : ℝ) := by
    exact_mod_cast selected_positive
  have factorization :
      Real.log
        ((∏ p ∈ completed, selectedPrimePower squared p : ℕ) : ℝ) =
        Real.log (core : ℝ) + Real.log (selected : ℝ) := by
    rw [exact_conductor]
    change Real.log ((core * selected : ℕ) : ℝ) = _
    push_cast
    exact Real.log_mul core_real_positive.ne' selected_real_positive.ne'
  rw [factorization]
  have cost := prime_product_log_le_card_mul_log_bound
    (completed \ P) B
      (fun p hp => reserve_primes p (selected_subset hp))
      (fun p hp => bounded p (selected_subset hp))
  rw [selected_card] at cost
  change Real.log (selected : ℝ) ≤
    ((2 * (deficientTargets y P squared a).card : ℕ) : ℝ) *
      Real.log (B : ℝ) at cost
  norm_num only [Nat.cast_ofNat, Nat.cast_mul] at cost
  change Real.log (core : ℝ) + Real.log (selected : ℝ) ≤
    Real.log (core : ℝ) + _
  exact add_le_add (le_refl _) cost

/-- A plain numerical prime-counting inequality supplies all needed fresh
bounded reserve primes automatically.  Existing core primes are removed
from the actual finite set of primes at most `B`; no distributional or
prime-pattern theorem is hidden in the reserve construction. -/
theorem fresh_bounded_prime_reserve_of_primeCounting
    (P : Finset ℕ) (B deficit : ℕ)
    (counting : 2 * deficit + P.card ≤ Nat.primeCounting B) :
    ∃ R : Finset ℕ,
      (∀ p ∈ R, p.Prime) ∧ Disjoint P R ∧
        2 * deficit ≤ R.card ∧ ∀ p ∈ R, p ≤ B := by
  let R := Nat.primesLE B \ P
  refine ⟨R, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hp).1
  · apply Finset.disjoint_left.mpr
    intro p hp hR
    exact (Finset.mem_sdiff.mp hR).2 hp
  · have difference := Finset.le_card_sdiff P (Nat.primesLE B)
    rw [Nat.primesLE_card_eq_primeCounting] at difference
    change 2 * deficit ≤ (Nat.primesLE B \ P).card
    omega
  · intro p hp
    exact Nat.le_of_mem_primesLE (Finset.mem_sdiff.mp hp).1

/-- Finite exact-original completion from only a partial mixed core and a
numeric prime-counting capacity estimate.  The remaining conductor bound is
the ACTUAL core logarithm plus the fully charged reserve cleanup cost. -/
theorem complete_partial_core_of_primeCounting
    (y : ℕ) (P squared : Finset ℕ) (a : ℕ → ℕ) (B : ℕ)
    (core_primes : ∀ p ∈ P, p.Prime)
    (square_support : squared ⊆ P)
    (counting :
      2 * (deficientTargets y P squared a).card + P.card ≤
        Nat.primeCounting B) :
    ∃ (completed : Finset ℕ) (residue : ℕ → ℕ),
      UnrestrictedPrimeSquareDoubleCover y completed squared residue ∧
      P ⊆ completed ∧
      (completed \ P).card =
        2 * (deficientTargets y P squared a).card ∧
      Real.log ((∏ p ∈ completed, selectedPrimePower squared p : ℕ) : ℝ) ≤
        Real.log ((∏ p ∈ P, selectedPrimePower squared p : ℕ) : ℝ) +
          (2 * ((deficientTargets y P squared a).card : ℝ)) *
            Real.log (B : ℝ) := by
  obtain ⟨R, primes, fresh, capacity, bounded⟩ :=
    fresh_bounded_prime_reserve_of_primeCounting P B
      (deficientTargets y P squared a).card counting
  exact complete_partial_core_with_bounded_reserve_cost
    y P squared R a B core_primes square_support primes fresh capacity bounded

/-- A strictly analytic finite-deficiency target for the full #1139 proof.
One need only construct partial mixed cores with sufficiently few deficient
targets, enough primes below a selected reserve cutoff, and sublinear TOTAL
core-plus-cleanup cost.  Complete coverings, coherent cleanup residues, CRT,
almost-prime sequence gaps, and the original extended-real limsup are then
all supplied by unconditional formal theorems. -/
def HasSublinearDeficientCoreData : Prop :=
  ∀ (ε : ℝ), 0 < ε → ∀ Y₀ : ℕ,
    ∃ (y : ℕ) (P squared : Finset ℕ) (a : ℕ → ℕ) (B : ℕ),
      Y₀ ≤ y ∧
        (∀ p ∈ P, p.Prime) ∧ squared ⊆ P ∧
        2 * (deficientTargets y P squared a).card + P.card ≤
          Nat.primeCounting B ∧
        Real.log ((∏ p ∈ P, selectedPrimePower squared p : ℕ) : ℝ) +
          (2 * ((deficientTargets y P squared a).card : ℝ)) *
            Real.log (B : ℝ) ≤ ε * (y : ℝ)

/-- Exact reduction of the outstanding sparse-cover existence claim to a
partial-core deficiency estimate and a numeric bounded-prime supply. -/
theorem sublinear_unrestricted_conductors_of_deficient_core_data
    (partial_data : HasSublinearDeficientCoreData) :
    HasSublinearUnrestrictedConductorCovers := by
  intro ε positive Y₀
  obtain ⟨y, P, squared, a, B, large, primes,
    square_support, counting, cost⟩ := partial_data ε positive Y₀
  obtain ⟨completed, residue, cover, _core_subset,
    _selected_card, conductor⟩ :=
    complete_partial_core_of_primeCounting y P squared a B
      primes square_support counting
  exact ⟨y, completed, squared, residue, large, cover,
    conductor.trans cost⟩

/-- The literal full original Erdős #1139 conclusion now follows from the
single explicit deficient-core proposition.  The only remaining unproved
input is the analytic construction of those quantitatively sparse cores. -/
theorem original_normalized_limsup_top_of_deficient_core_data
    (partial_data : HasSublinearDeficientCoreData) :
    Filter.atTop.limsup
      (fun k : ℕ =>
        (((Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) (k + 1) : ℝ) -
           (Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) k : ℝ)) /
          Real.log ((k : ℝ) + 1) : EReal)) = ⊤ :=
  original_normalized_limsup_top_of_sublinear_unrestricted_conductors
    (sublinear_unrestricted_conductors_of_deficient_core_data partial_data)


end Erdos1139
