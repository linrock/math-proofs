module

public import GoalRootPNTLimsup433

@[expose] public section


/-!
# Keeping and removing unused protected primes in the Erdős #689 construction

The original #689 cleanup theorem discards the set of still-unused protected
primes.  Its invariant is stronger: every old zero-class multiple has two
covering primes outside the ENTIRE current protected reserve.  Therefore the
remaining reserve can be omitted simultaneously from the final conductor.

This module preserves the exact cardinality ledger through cleanup and proves
that the pruned genuine prime support still double-covers the whole historical
closed interval.  It does not assert any asymptotic reserve surplus.
-/

open Finset Filter
open scoped ArithmeticFunction.Omega Topology

namespace Erdos689

/-- Cleanup preserves a protected unused subset.  At most the initial actual
deficiency many reserve primes are consumed, including when one switch
incidentally repairs several targets. -/
theorem exists_covering_of_protectedReserve_with_unused
    {n : ℕ} {a : ℕ → ℕ} {R : Finset ℕ}
    (hreserve : protectedReserve n a R)
    (hbudget : deficiency n a ≤ R.card) :
    ∃ (final : ℕ → ℕ) (unused : Finset ℕ),
      unused ⊆ R ∧
        protectedReserve n final unused ∧
        (∀ m ∈ Finset.Icc 1 n, 2 ≤ coverage n final m) ∧
        R.card ≤ unused.card + deficiency n a := by
  classical
  induction R using Finset.induction_on generalizing a with
  | empty =>
      refine ⟨a, ∅, Finset.Subset.rfl, hreserve, ?_, by simp⟩
      intro m hm
      have hterm := deficiency_term_le (a := a) hm
      simp at hbudget
      omega
  | @insert p R hp ih =>
      by_cases hfinished :
          ∀ m ∈ Finset.Icc 1 n, 2 ≤ coverage n a m
      · exact ⟨a, insert p R, Finset.Subset.rfl, hreserve,
          hfinished, Nat.le_add_right _ _⟩
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
        obtain ⟨final, unused, hsubset, hprotected, hcovered, hledger⟩ :=
          ih hnext hnextbudget
        refine ⟨final, unused,
          fun q hq => Finset.mem_insert_of_mem (hsubset hq),
          hprotected, hcovered, ?_⟩
        rw [Finset.card_insert_of_notMem hp]
        omega

/-- Delete the entire remaining protected reserve from the exact original
set of prime moduli up to the interval endpoint. -/
def prunedPrimeSupport (n : ℕ) (unused : Finset ℕ) : Finset ℕ :=
  ((Finset.Icc 1 n).filter Nat.Prime) \ unused

/-- Pruned prime hits are definitionally the covering hits protected from
every member of the entire remaining reserve. -/
theorem prunedPrimeSupport_hits_eq_protectedPrimes
    (n m : ℕ) (a : ℕ → ℕ) (unused : Finset ℕ) :
    ((prunedPrimeSupport n unused).filter
      fun p => a p ≡ m [MOD p]) =
        protectedPrimes n a unused m := by
  classical
  ext p
  simp [prunedPrimeSupport, protectedPrimes, coveredPrimes, and_assoc,
    and_left_comm, and_comm]

/-- Once cleanup has finished, EVERY unused protected prime can be omitted
simultaneously without losing either of the two required covering hits. -/
theorem protectedReserve_pruned_coverage
    {n : ℕ} {a : ℕ → ℕ} {unused : Finset ℕ}
    (hreserve : protectedReserve n a unused)
    (hcovered : ∀ m ∈ Finset.Icc 1 n, 2 ≤ coverage n a m) :
    ∀ m ∈ Finset.Icc 1 n,
      2 ≤ ((prunedPrimeSupport n unused).filter
        fun p => a p ≡ m [MOD p]).card := by
  intro m hm
  rw [prunedPrimeSupport_hits_eq_protectedPrimes]
  by_cases hdivides : ∃ p ∈ unused, p ∣ m
  · obtain ⟨p, hp, hpm⟩ := hdivides
    exact (hreserve p hp).2.2.2 m hm hpm
  · have hsubset :
        coveredPrimes n a m ⊆ protectedPrimes n a unused m := by
      intro p hp
      apply Finset.mem_filter.mpr
      refine ⟨hp, ?_⟩
      intro hpunused
      have hzero := (hreserve p hpunused).2.2.1
      have hhit := (mem_coveredPrimes_iff.mp hp).2.2.2
      exact hdivides ⟨p, hpunused,
        (zero_class_hit_iff_dvd hzero).mp hhit⟩
    exact (hcovered m hm).trans (Finset.card_le_card hsubset)

end Erdos689

namespace Erdos1139

/-- Exact #1139-ready mixed covering on the PRUNED #689 prime support.  The
unused protected primes are absent from the real conductor, not merely
assigned arbitrary residues. -/
theorem protectedReserve_pruned_double_cover
    {n : ℕ} {a : ℕ → ℕ} {unused : Finset ℕ}
    (hreserve : Erdos689.protectedReserve n a unused)
    (hcovered : ∀ m ∈ Finset.Icc 1 n, 2 ≤ Erdos689.coverage n a m) :
    UnrestrictedPrimeSquareDoubleCover n
      (Erdos689.prunedPrimeSupport n unused) ∅ a := by
  refine ⟨?_, Finset.empty_subset _, ?_⟩
  · intro p hp
    have hprime :=
      (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2
    exact hprime
  · intro m hm
    simpa using
      Erdos689.protectedReserve_pruned_coverage hreserve hcovered m hm


end Erdos1139
