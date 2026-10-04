module

public import AnalyticBridge

@[expose] public section


/-!
# Exact structural classification of genuinely deficient initial targets

These results concern the actual initial assignment and the original closed
interval, not a surrogate counting function. Every prime divisor outside the
switched support and the prime two is assigned residue zero, so it contributes
one distinct old covering hit. An odd target additionally has the covering
hit at two whenever that prime is available. Consequently a deficient target
has at most one external prime factor, and an odd deficient target is entirely
supported on the switched primes. These are the structural classification
steps required on the upper-bound side of the initial-deficiency asymptotic.
-/

namespace Erdos689

/-- Distinct prime factors outside the switched support and the parity prime. -/
def externalPrimeFactors (S : Finset ℕ) (m : ℕ) : Finset ℕ :=
  m.primeFactors.filter fun p => p ≠ 2 ∧ p ∉ S

/-- Every external prime factor of an actual target is an old zero-class hit. -/
theorem externalPrimeFactors_subset_coveredPrimes
    {S : Finset ℕ} {b : ℕ → ℕ} {m n : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    externalPrimeFactors S m ⊆ coveredPrimes n (initialAssignment S b) m := by
  intro p hp
  obtain ⟨hfactor, hpnotwo, hpnotS⟩ := Finset.mem_filter.mp hp
  have hprime := Nat.prime_of_mem_primeFactors hfactor
  have hdiv := Nat.dvd_of_mem_primeFactors hfactor
  have hpm : p ≤ m := Nat.le_of_dvd (by omega) hdiv
  apply mem_coveredPrimes_iff.mpr
  refine ⟨hprime.one_le, hpm.trans hmn, hprime, ?_⟩
  have hzero : initialAssignment S b p = 0 := by
    simp [initialAssignment, hpnotwo, hpnotS]
  exact (zero_class_hit_iff_dvd hzero).mpr hdiv

/-- Distinct external prime divisors are bounded by actual covering multiplicity. -/
theorem externalPrimeFactors_card_le_coverage
    {S : Finset ℕ} {b : ℕ → ℕ} {m n : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    (externalPrimeFactors S m).card ≤ coverage n (initialAssignment S b) m := by
  exact Finset.card_le_card (externalPrimeFactors_subset_coveredPrimes hm hmn)

/-- A genuinely deficient target has at most one distinct external prime divisor. -/
theorem deficient_externalPrimeFactors_card_le_one
    {S : Finset ℕ} {b : ℕ → ℕ} {m n : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n)
    (hdeficient : coverage n (initialAssignment S b) m < 2) :
    (externalPrimeFactors S m).card ≤ 1 := by
  have hbound := externalPrimeFactors_card_le_coverage
    (S := S) (b := b) hm hmn
  omega

/-- Any two external prime divisors of a deficient target must coincide. -/
theorem deficient_external_prime_factor_unique
    {S : Finset ℕ} {b : ℕ → ℕ} {m n p q : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n)
    (hdeficient : coverage n (initialAssignment S b) m < 2)
    (hp : p ∈ externalPrimeFactors S m)
    (hq : q ∈ externalPrimeFactors S m) :
    p = q := by
  exact Finset.card_le_one.mp
    (deficient_externalPrimeFactors_card_le_one hm hmn hdeficient) p hp q hq

/-- Once the prime two is available, it covers every odd initial target. -/
theorem two_mem_initial_coveredPrimes_of_odd
    {S : Finset ℕ} {b : ℕ → ℕ} {m n : ℕ}
    (hn : 2 ≤ n) (hodd : m % 2 = 1) :
    2 ∈ coveredPrimes n (initialAssignment S b) m := by
  apply mem_coveredPrimes_iff.mpr
  refine ⟨by omega, hn, Nat.prime_two, ?_⟩
  simp [initialAssignment, Nat.ModEq, hodd]

/-- The actual old covering primes split exactly into parity, switched, and
external-divisor parts; all switched primes must already be in the interval. -/
theorem initialAssignment_coveredPrimes_eq_parity_union_support_union_external
    {S : Finset ℕ} {b : ℕ → ℕ} {m n : ℕ}
    (hsupport : ∀ s ∈ S, s.Prime ∧ s ≤ n)
    (htwo : 2 ∉ S) (hm : 1 ≤ m) (hmn : m ≤ n) (hn : 2 ≤ n) :
    coveredPrimes n (initialAssignment S b) m =
      (if m % 2 = 1 then {2} else ∅) ∪
        (S.filter fun s => b s ≡ m [MOD s]) ∪
        externalPrimeFactors S m := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨_, _, hprime, hhit⟩ := mem_coveredPrimes_iff.mp hp
    by_cases hp2 : p = 2
    · subst p
      have hodd : m % 2 = 1 := by
        simpa [initialAssignment, Nat.ModEq, eq_comm] using hhit
      simp [hodd]
    · by_cases hpS : p ∈ S
      · have hswitched : b p ≡ m [MOD p] := by
          simpa [initialAssignment, hp2, hpS] using hhit
        exact Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hpS, hswitched⟩))
      · have hzero : initialAssignment S b p = 0 := by
          simp [initialAssignment, hp2, hpS]
        have hdiv := (zero_class_hit_iff_dvd hzero).mp hhit
        have hfactor : p ∈ m.primeFactors := by
          exact Nat.mem_primeFactors.mpr ⟨hprime, hdiv, by omega⟩
        exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hfactor, hp2, hpS⟩)
  · intro hp
    rcases Finset.mem_union.mp hp with hleft | hexternal
    · rcases Finset.mem_union.mp hleft with hparity | hswitched
      · by_cases hodd : m % 2 = 1
        · have hp2 : p = 2 := by simpa [hodd] using hparity
          subst p
          exact two_mem_initial_coveredPrimes_of_odd hn hodd
        · simp [hodd] at hparity
      · obtain ⟨hpS, hhit⟩ := Finset.mem_filter.mp hswitched
        have hpnotwo : p ≠ 2 := by
          intro hp2
          subst p
          exact htwo hpS
        obtain ⟨hprime, hpn⟩ := hsupport p hpS
        apply mem_coveredPrimes_iff.mpr
        refine ⟨hprime.one_le, hpn, hprime, ?_⟩
        simpa [initialAssignment, hpnotwo, hpS] using hhit
    · exact externalPrimeFactors_subset_coveredPrimes hm hmn hexternal

/-- Exact old coverage equals the parity hit, switched hits, and distinct
external prime divisors; this is the actual deficiency-audit ledger. -/
theorem initialAssignment_coverage_eq_parity_add_switched_add_external
    {S : Finset ℕ} {b : ℕ → ℕ} {m n : ℕ}
    (hsupport : ∀ s ∈ S, s.Prime ∧ s ≤ n)
    (htwo : 2 ∉ S) (hm : 1 ≤ m) (hmn : m ≤ n) (hn : 2 ≤ n) :
    coverage n (initialAssignment S b) m =
      (if m % 2 = 1 then 1 else 0) + switchedHits S b m +
        (externalPrimeFactors S m).card := by
  classical
  let P : Finset ℕ := if m % 2 = 1 then {2} else ∅
  let T : Finset ℕ := S.filter fun s => b s ≡ m [MOD s]
  let E : Finset ℕ := externalPrimeFactors S m
  have hPT : Disjoint P T := by
    apply Finset.disjoint_left.mpr
    intro p hp hT
    by_cases hodd : m % 2 = 1
    · have hp2 : p = 2 := by simpa [P, hodd] using hp
      subst p
      exact htwo (Finset.mem_filter.mp hT).1
    · simp [P, hodd] at hp
  have hPTE : Disjoint (P ∪ T) E := by
    apply Finset.disjoint_left.mpr
    intro p hp hE
    obtain ⟨_, hpnotwo, hpnotS⟩ := Finset.mem_filter.mp hE
    rcases Finset.mem_union.mp hp with hP | hT
    · by_cases hodd : m % 2 = 1
      · have hp2 : p = 2 := by simpa [P, hodd] using hP
        exact hpnotwo hp2
      · simp [P, hodd] at hP
    · exact hpnotS (Finset.mem_filter.mp hT).1
  change (coveredPrimes n (initialAssignment S b) m).card = _
  rw [initialAssignment_coveredPrimes_eq_parity_union_support_union_external
    hsupport htwo hm hmn hn]
  change ((P ∪ T) ∪ E).card =
    (if m % 2 = 1 then 1 else 0) + switchedHits S b m + E.card
  rw [Finset.card_union_of_disjoint hPTE,
    Finset.card_union_of_disjoint hPT]
  by_cases hodd : m % 2 = 1 <;> simp [P, T, switchedHits, hodd]

/-- For odd targets the parity hit is distinct from every external divisor hit. -/
theorem odd_externalPrimeFactors_card_add_one_le_coverage
    {S : Finset ℕ} {b : ℕ → ℕ} {m n : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) (hn : 2 ≤ n)
    (hodd : m % 2 = 1) :
    (externalPrimeFactors S m).card + 1 ≤
      coverage n (initialAssignment S b) m := by
  have hnotwo : 2 ∉ externalPrimeFactors S m := by
    simp [externalPrimeFactors]
  have hsubset :
      insert 2 (externalPrimeFactors S m) ⊆
        coveredPrimes n (initialAssignment S b) m := by
    intro p hp
    rcases Finset.mem_insert.mp hp with heq | hexternal
    · subst p
      exact two_mem_initial_coveredPrimes_of_odd hn hodd
    · exact externalPrimeFactors_subset_coveredPrimes hm hmn hexternal
  have hcard := Finset.card_le_card hsubset
  simpa [Finset.card_insert_of_notMem hnotwo, coverage] using hcard

/-- An odd deficient actual target has no external prime divisor whatsoever. -/
theorem odd_deficient_externalPrimeFactors_eq_empty
    {S : Finset ℕ} {b : ℕ → ℕ} {m n : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) (hn : 2 ≤ n)
    (hodd : m % 2 = 1)
    (hdeficient : coverage n (initialAssignment S b) m < 2) :
    externalPrimeFactors S m = ∅ := by
  have hbound := odd_externalPrimeFactors_card_add_one_le_coverage
    (S := S) (b := b) hm hmn hn hodd
  apply Finset.card_eq_zero.mp
  omega

/-- Every prime factor of an odd deficient target belongs to switched support. -/
theorem odd_deficient_primeFactors_subset_support
    {S : Finset ℕ} {b : ℕ → ℕ} {m n : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) (hn : 2 ≤ n)
    (hodd : m % 2 = 1)
    (hdeficient : coverage n (initialAssignment S b) m < 2) :
    m.primeFactors ⊆ S := by
  have hempty := odd_deficient_externalPrimeFactors_eq_empty
    (S := S) (b := b) hm hmn hn hodd hdeficient
  intro p hp
  have hpnotwo : p ≠ 2 := by
    intro heq
    subst p
    have hzero : m % 2 = 0 :=
      Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mem_primeFactors hp)
    omega
  by_contra hpnotS
  have hexternal : p ∈ externalPrimeFactors S m := by
    exact Finset.mem_filter.mpr ⟨hp, hpnotwo, hpnotS⟩
  rw [hempty] at hexternal
  simp at hexternal

end Erdos689

#print axioms Erdos689.externalPrimeFactors_subset_coveredPrimes
#print axioms Erdos689.externalPrimeFactors_card_le_coverage
#print axioms Erdos689.deficient_externalPrimeFactors_card_le_one
#print axioms Erdos689.deficient_external_prime_factor_unique
#print axioms Erdos689.two_mem_initial_coveredPrimes_of_odd
#print axioms Erdos689.initialAssignment_coveredPrimes_eq_parity_union_support_union_external
#print axioms Erdos689.initialAssignment_coverage_eq_parity_add_switched_add_external
#print axioms Erdos689.odd_externalPrimeFactors_card_add_one_le_coverage
#print axioms Erdos689.odd_deficient_externalPrimeFactors_eq_empty
#print axioms Erdos689.odd_deficient_primeFactors_subset_support
