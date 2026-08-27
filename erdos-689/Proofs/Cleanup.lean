import Mathlib
import Structural

/-!
# Simultaneous safe cleanup by induction on an actual prime reserve

The reserve consists of genuine, bounded primes presently assigned residue zero.
Every multiple of a reserve prime already has two hits from primes outside the
entire reserve.  Those outside-reserve hits survive every subsequent reserve
reassignment, so cleanup is simultaneous, not merely individually safe.
-/

open scoped BigOperators

namespace Erdos689

/-- Covering primes whose assignments cannot be consumed by the current reserve. -/
def protectedPrimes (n : ℕ) (a : ℕ → ℕ) (R : Finset ℕ) (m : ℕ) : Finset ℕ :=
  (coveredPrimes n a m).filter fun p => p ∉ R

/-- The current number of missing covering hits on the actual closed interval. -/
def deficiency (n : ℕ) (a : ℕ → ℕ) : ℕ :=
  ∑ m ∈ Finset.Icc 1 n, (2 - coverage n a m)

/-- Concrete reserve invariant: every old zero-class multiple has two immutable hits. -/
def protectedReserve (n : ℕ) (a : ℕ → ℕ) (R : Finset ℕ) : Prop :=
  ∀ p ∈ R, p.Prime ∧ p ≤ n ∧ a p = 0 ∧
    ∀ m ∈ Finset.Icc 1 n, p ∣ m → 2 ≤ (protectedPrimes n a R m).card

/-- Every protected covering prime is, in particular, a genuine covering prime. -/
theorem protectedPrimes_subset_covered (n m : ℕ) (a : ℕ → ℕ) (R : Finset ℕ) :
    protectedPrimes n a R m ⊆ coveredPrimes n a m := by
  intro p hp
  exact (Finset.mem_filter.mp hp).1

/-- Removing and reassigning one reserve prime preserves every previously protected hit. -/
theorem protectedPrimes_switch_erase_subset {n m p r : ℕ}
    {a : ℕ → ℕ} {R : Finset ℕ} (hp : p ∈ R) :
    protectedPrimes n a R m ⊆
      protectedPrimes n (switch a p r) (R.erase p) m := by
  classical
  intro q hq
  obtain ⟨hcovered, hnotreserve⟩ := Finset.mem_filter.mp hq
  have hne : q ≠ p := by
    intro heq
    exact hnotreserve (heq.symm ▸ hp)
  apply Finset.mem_filter.mpr
  constructor
  · obtain ⟨hone, hbound, hprime, hmod⟩ := mem_coveredPrimes_iff.mp hcovered
    apply mem_coveredPrimes_iff.mpr
    refine ⟨hone, hbound, hprime, ?_⟩
    simpa [switch, hne] using hmod
  · intro herase
    exact hnotreserve (Finset.mem_of_mem_erase herase)

/-- The complete concrete reserve invariant survives a safe reassignment. -/
theorem protectedReserve_switch_erase {n p r : ℕ}
    {a : ℕ → ℕ} {R : Finset ℕ}
    (hreserve : protectedReserve n a R) (hp : p ∈ R) :
    protectedReserve n (switch a p r) (R.erase p) := by
  classical
  intro q hq
  have hqR : q ∈ R := Finset.mem_of_mem_erase hq
  have hqne : q ≠ p := (Finset.mem_erase.mp hq).1
  obtain ⟨hprime, hbound, hzero, hprotected⟩ := hreserve q hqR
  refine ⟨hprime, hbound, ?_, ?_⟩
  · simpa [switch, hqne] using hzero
  · intro m hm hdiv
    exact (hprotected m hm hdiv).trans
      (Finset.card_le_card (protectedPrimes_switch_erase_subset hp))

/-- A target that lacks two covering hits is divisible by no available reserve prime. -/
theorem protectedReserve_not_dvd_deficient {n p m : ℕ}
    {a : ℕ → ℕ} {R : Finset ℕ}
    (hreserve : protectedReserve n a R) (hp : p ∈ R)
    (hm : m ∈ Finset.Icc 1 n) (hdeficient : coverage n a m < 2) :
    ¬ p ∣ m := by
  intro hdiv
  have hprotected := (hreserve p hp).2.2.2 m hm hdiv
  have hsubset := Finset.card_le_card (protectedPrimes_subset_covered n m a R)
  change (protectedPrimes n a R m).card ≤ coverage n a m at hsubset
  omega

/-- Any reserve reassignment can only decrease each individual deficiency token count. -/
theorem protectedReserve_switch_token_le {n p r m : ℕ}
    {a : ℕ → ℕ} {R : Finset ℕ}
    (hreserve : protectedReserve n a R) (hp : p ∈ R)
    (hm : m ∈ Finset.Icc 1 n) :
    2 - coverage n (switch a p r) m ≤ 2 - coverage n a m := by
  classical
  by_cases hhit : a p ≡ m [MOD p]
  · have hdiv : p ∣ m :=
      (zero_class_hit_iff_dvd (hreserve p hp).2.2.1).mp hhit
    have hprotected := (hreserve p hp).2.2.2 m hm hdiv
    have hsurvive := Finset.card_le_card
      (protectedPrimes_switch_erase_subset
        (n := n) (m := m) (r := r) (a := a) hp)
    have hsubset := Finset.card_le_card
      (protectedPrimes_subset_covered n m (switch a p r) (R.erase p))
    change (protectedPrimes n (switch a p r) (R.erase p) m).card ≤
      coverage n (switch a p r) m at hsubset
    omega
  · have hmonotone := no_collateral_loss_of_old_nonhit (n := n) (r := r) hhit
    omega

/-- Repairing a deficient target with any reserve prime gains exactly one hit there. -/
theorem protectedReserve_switch_target_gain {n p m : ℕ}
    {a : ℕ → ℕ} {R : Finset ℕ}
    (hreserve : protectedReserve n a R) (hp : p ∈ R)
    (hm : m ∈ Finset.Icc 1 n) (hdeficient : coverage n a m < 2) :
    coverage n (switch a p m) m = coverage n a m + 1 := by
  obtain ⟨hprime, hbound, hzero, _⟩ := hreserve p hp
  apply switching_gain_exactly_one hprime hbound
  · intro hhit
    exact protectedReserve_not_dvd_deficient hreserve hp hm hdeficient
      ((zero_class_hit_iff_dvd hzero).mp hhit)
  · exact Nat.ModEq.rfl

/-- One reserve repair strictly decreases the exact total current deficiency. -/
theorem protectedReserve_switch_deficiency_lt {n p m : ℕ}
    {a : ℕ → ℕ} {R : Finset ℕ}
    (hreserve : protectedReserve n a R) (hp : p ∈ R)
    (hm : m ∈ Finset.Icc 1 n) (hdeficient : coverage n a m < 2) :
    deficiency n (switch a p m) < deficiency n a := by
  unfold deficiency
  apply Finset.sum_lt_sum
  · intro q hq
    exact protectedReserve_switch_token_le hreserve hp hq
  · refine ⟨m, hm, ?_⟩
    have hgain := protectedReserve_switch_target_gain hreserve hp hm hdeficient
    omega

/-- Every individual token count is bounded by the total current deficiency. -/
theorem deficiency_term_le {n m : ℕ} {a : ℕ → ℕ}
    (hm : m ∈ Finset.Icc 1 n) :
    2 - coverage n a m ≤ deficiency n a := by
  unfold deficiency
  exact Finset.single_le_sum
    (f := fun q => 2 - coverage n a q) (fun _ _ => Nat.zero_le _) hm

/-- A concrete prime reserve at least as large as the current token demand completes cleanup. -/
theorem exists_covering_of_protectedReserve {n : ℕ}
    {a : ℕ → ℕ} {R : Finset ℕ}
    (hreserve : protectedReserve n a R)
    (hbudget : deficiency n a ≤ R.card) :
    ∃ final : ℕ → ℕ,
      ∀ m ∈ Finset.Icc 1 n, 2 ≤ coverage n final m := by
  classical
  induction R using Finset.induction_on generalizing a with
  | empty =>
      refine ⟨a, ?_⟩
      intro m hm
      have hterm := deficiency_term_le (a := a) hm
      simp at hbudget
      omega
  | @insert p R hp ih =>
      by_cases hfinished : ∀ m ∈ Finset.Icc 1 n, 2 ≤ coverage n a m
      · exact ⟨a, hfinished⟩
      · push Not at hfinished
        obtain ⟨m, hm, hdeficient⟩ := hfinished
        have hpmem : p ∈ insert p R := Finset.mem_insert_self p R
        have hnext : protectedReserve n (switch a p m) R := by
          simpa [Finset.erase_insert hp] using
            (protectedReserve_switch_erase hreserve hpmem (r := m))
        have hdrop := protectedReserve_switch_deficiency_lt
          hreserve hpmem hm hdeficient
        have hnextbudget : deficiency n (switch a p m) ≤ R.card := by
          rw [Finset.card_insert_of_notMem hp] at hbudget
          omega
        exact ih hnext hnextbudget

end Erdos689

#print axioms Erdos689.protectedPrimes_subset_covered
#print axioms Erdos689.protectedPrimes_switch_erase_subset
#print axioms Erdos689.protectedReserve_switch_erase
#print axioms Erdos689.protectedReserve_not_dvd_deficient
#print axioms Erdos689.protectedReserve_switch_token_le
#print axioms Erdos689.protectedReserve_switch_target_gain
#print axioms Erdos689.protectedReserve_switch_deficiency_lt
#print axioms Erdos689.deficiency_term_le
#print axioms Erdos689.exists_covering_of_protectedReserve
