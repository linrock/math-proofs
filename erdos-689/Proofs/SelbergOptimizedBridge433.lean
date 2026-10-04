module

public import SelbergFinite433
public import AffineSieveRootRemainder433
public import AffineSieveExceptions433
public import SelbergCutoff433

@[expose] public section


/-!
# The uncollapsed optimized Selberg error

The externally verified optimized Selberg sieve states its error after
collapsing the two weight variables into a divisor sum.  That coarse version
introduces a `3 ^ ω(h)` loss.  Here we keep the actual optimized `Λ²` weights
uncollapsed, reindex them by their exact least common multiple, and prepare
the sharp fourth-power remainder bound needed by the affine two-form sieve.
-/

open Finset
open Filter
open scoped Topology

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Erdos689

/-- The optimized upper-bound sieve retains its exact error sum. -/
theorem parameter_sifted_card_le_optimized_exact_errSum
    (s : SelbergSieve) (I : Finset ℕ) (F : ℕ → ℕ)
    (hsupport : s.support = I.image F)
    (hweights : ∀ x ∈ s.support,
      s.weights x = ((I.filter fun t => F t = x).card : ℝ)) :
    ((I.filter fun t => Nat.Coprime s.prodPrimes (F t)).card : ℝ) ≤
      s.totalMass / s.selbergBoundingSum +
        BoundingSieve.errSum (s := s.toBoundingSieve)
          (SelbergSieve.selbergMuPlus s) := by
  rw [← siftedSum_eq_parameter_card s I F hsupport hweights]
  convert SelbergSieve.siftedSum_le_mainSum_errSum_of_UpperBoundSieve
    s.toBoundingSieve (SelbergSieve.selbergUbSieve s) using 1
  change
    s.totalMass / s.selbergBoundingSum +
        BoundingSieve.errSum (s := s.toBoundingSieve)
          (SelbergSieve.selbergMuPlus s) =
      s.totalMass * BoundingSieve.mainSum (s := s.toBoundingSieve)
          (SelbergSieve.selbergMuPlus s) +
        BoundingSieve.errSum (s := s.toBoundingSieve)
          (SelbergSieve.selbergMuPlus s)
  rw [SelbergSieve.selberg_bound_simple_mainSum]
  simp [div_eq_mul_inv]

/-- Reindex an uncollapsed divisor triple sum by its unique LCM. -/
theorem lcm_divisor_triple_sum_eq_double
    (P : ℕ) (hP : P ≠ 0) (f : ℕ → ℕ → ℕ → ℝ) :
    (∑ h ∈ P.divisors,
      ∑ d ∈ h.divisors,
        ∑ e ∈ h.divisors,
          if h = Nat.lcm d e then f d e h else 0) =
      ∑ d ∈ P.divisors,
        ∑ e ∈ P.divisors, f d e (Nat.lcm d e) := by
  classical
  calc
    (∑ h ∈ P.divisors,
      ∑ d ∈ h.divisors,
        ∑ e ∈ h.divisors,
          if h = Nat.lcm d e then f d e h else 0) =
      ∑ h ∈ P.divisors,
        ∑ d ∈ P.divisors,
          ∑ e ∈ P.divisors,
            if h = Nat.lcm d e then f d e h else 0 :=
      Aux.conv_lambda_sq_larger_sum f P
    _ = ∑ d ∈ P.divisors,
          ∑ e ∈ P.divisors,
            ∑ h ∈ P.divisors,
              if h = Nat.lcm d e then f d e h else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]
    _ = ∑ d ∈ P.divisors,
          ∑ e ∈ P.divisors, f d e (Nat.lcm d e) := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.sum_ite_eq_of_mem']
      exact Nat.mem_divisors.mpr
        ⟨Nat.lcm_dvd (Nat.dvd_of_mem_divisors hd)
          (Nat.dvd_of_mem_divisors he), hP⟩

/-- The exact optimized `Λ²` error is bounded by the genuine double LCM sum,
without replacing the weights by the coarse `3 ^ ω(h)` majorant. -/
theorem selberg_optimized_errSum_le_lcm_double_divisor_sum
    (s : SelbergSieve) :
    BoundingSieve.errSum (s := s.toBoundingSieve)
        (SelbergSieve.selbergMuPlus s) ≤
      ∑ d ∈ s.prodPrimes.divisors,
        ∑ e ∈ s.prodPrimes.divisors,
          |s.selbergWeights d * s.selbergWeights e *
            BoundingSieve.rem (s := s.toBoundingSieve) (Nat.lcm d e)| := by
  classical
  unfold BoundingSieve.errSum
  calc
    (∑ h ∈ s.prodPrimes.divisors,
      |SelbergSieve.selbergMuPlus s h| *
        |BoundingSieve.rem (s := s.toBoundingSieve) h|) ≤
      ∑ h ∈ s.prodPrimes.divisors,
        ∑ d ∈ h.divisors,
          ∑ e ∈ h.divisors,
            if h = Nat.lcm d e then
              |s.selbergWeights d * s.selbergWeights e *
                BoundingSieve.rem (s := s.toBoundingSieve) h|
            else 0 := by
      apply Finset.sum_le_sum
      intro h hh
      rw [← abs_mul]
      have hexpand :
          SelbergSieve.selbergMuPlus s h *
              BoundingSieve.rem (s := s.toBoundingSieve) h =
            ∑ d ∈ h.divisors,
              ∑ e ∈ h.divisors,
                if h = Nat.lcm d e then
                  s.selbergWeights d * s.selbergWeights e *
                    BoundingSieve.rem (s := s.toBoundingSieve) h
                else 0 := by
        simp [SelbergSieve.selbergMuPlus, SelbergSieve.lambdaSquared,
          Finset.sum_mul, ite_mul]
      rw [hexpand]
      calc
        |∑ d ∈ h.divisors,
          ∑ e ∈ h.divisors,
            if h = Nat.lcm d e then
              s.selbergWeights d * s.selbergWeights e *
                BoundingSieve.rem (s := s.toBoundingSieve) h
            else 0| ≤
          ∑ d ∈ h.divisors,
            |∑ e ∈ h.divisors,
              if h = Nat.lcm d e then
                s.selbergWeights d * s.selbergWeights e *
                  BoundingSieve.rem (s := s.toBoundingSieve) h
              else 0| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d ∈ h.divisors,
              ∑ e ∈ h.divisors,
                if h = Nat.lcm d e then
                  |s.selbergWeights d * s.selbergWeights e *
                    BoundingSieve.rem (s := s.toBoundingSieve) h|
                else 0 := by
          apply Finset.sum_le_sum
          intro d hd
          calc
            |∑ e ∈ h.divisors,
              if h = Nat.lcm d e then
                s.selbergWeights d * s.selbergWeights e *
                  BoundingSieve.rem (s := s.toBoundingSieve) h
              else 0| ≤
              ∑ e ∈ h.divisors,
                |if h = Nat.lcm d e then
                  s.selbergWeights d * s.selbergWeights e *
                    BoundingSieve.rem (s := s.toBoundingSieve) h
                else 0| := Finset.abs_sum_le_sum_abs _ _
            _ = _ := by
              apply Finset.sum_congr rfl
              intro e he
              split_ifs <;> simp
    _ = ∑ d ∈ s.prodPrimes.divisors,
          ∑ e ∈ s.prodPrimes.divisors,
            |s.selbergWeights d * s.selbergWeights e *
              BoundingSieve.rem (s := s.toBoundingSieve) (Nat.lcm d e)| :=
      lcm_divisor_triple_sum_eq_double s.prodPrimes
        s.prodPrimes_squarefree.ne_zero
        (fun d e h => |s.selbergWeights d * s.selbergWeights e *
          BoundingSieve.rem (s := s.toBoundingSieve) h|)

/-- An optimized Selberg weight vanishes beyond the square-root cutoff. -/
theorem selberg_optimized_weight_eq_zero_above_cutoff
    (s : SelbergSieve) (z d : ℕ)
    (hlevel : s.level ≤ (z : ℝ) ^ 2) (hd : z < d) :
    s.selbergWeights d = 0 := by
  apply s.selbergWeights_eq_zero d
  intro hbound
  have hsquare : (d : ℝ) ^ 2 ≤ (z : ℝ) ^ 2 := hbound.trans hlevel
  have hreal : (d : ℝ) ≤ z :=
    (sq_le_sq₀ (by positivity) (by positivity)).mp hsquare
  have hnat : d ≤ z := by exact_mod_cast hreal
  omega

/-- Keeping the optimized weights uncollapsed restricts both divisor
variables to the true square-root cutoff. -/
theorem selberg_optimized_errSum_le_lcm_double_cutoff_sum
    (s : SelbergSieve) (z : ℕ)
    (hlevel : s.level ≤ (z : ℝ) ^ 2) :
    BoundingSieve.errSum (s := s.toBoundingSieve)
        (SelbergSieve.selbergMuPlus s) ≤
      ∑ d ∈ Finset.Icc 1 z,
        ∑ e ∈ Finset.Icc 1 z,
          |s.selbergWeights d * s.selbergWeights e *
            BoundingSieve.rem (s := s.toBoundingSieve) (Nat.lcm d e)| := by
  classical
  let D : Finset ℕ := s.prodPrimes.divisors
  let Dsmall : Finset ℕ := D.filter fun d => d ≤ z
  let T : ℕ → ℕ → ℝ := fun d e =>
    |s.selbergWeights d * s.selbergWeights e *
      BoundingSieve.rem (s := s.toBoundingSieve) (Nat.lcm d e)|
  have hsubset : Dsmall ⊆ Finset.Icc 1 z := by
    intro d hd
    obtain ⟨hdD, hdz⟩ := Finset.mem_filter.mp hd
    have hdpositive : 0 < d := Nat.pos_of_mem_divisors hdD
    exact Finset.mem_Icc.mpr ⟨hdpositive, hdz⟩
  have hinner (d : ℕ) :
      (∑ e ∈ D, T d e) = ∑ e ∈ Dsmall, T d e := by
    unfold Dsmall
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e he
    split_ifs with hez
    · rfl
    · have hezero := selberg_optimized_weight_eq_zero_above_cutoff
        s z e hlevel (Nat.lt_of_not_ge hez)
      simp [T, hezero]
  have houter :
      (∑ d ∈ D, ∑ e ∈ Dsmall, T d e) =
        ∑ d ∈ Dsmall, ∑ e ∈ Dsmall, T d e := by
    unfold Dsmall
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    split_ifs with hdz
    · rfl
    · have hdzero := selberg_optimized_weight_eq_zero_above_cutoff
        s z d hlevel (Nat.lt_of_not_ge hdz)
      simp [T, hdzero]
  calc
    BoundingSieve.errSum (s := s.toBoundingSieve)
        (SelbergSieve.selbergMuPlus s) ≤
      ∑ d ∈ D, ∑ e ∈ D, T d e :=
      selberg_optimized_errSum_le_lcm_double_divisor_sum s
    _ = ∑ d ∈ D, ∑ e ∈ Dsmall, T d e := by
      apply Finset.sum_congr rfl
      intro d hd
      exact hinner d
    _ = ∑ d ∈ Dsmall, ∑ e ∈ Dsmall, T d e := houter
    _ ≤ ∑ d ∈ Dsmall, ∑ e ∈ Finset.Icc 1 z, T d e := by
      apply Finset.sum_le_sum
      intro d hd
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun e he hnot => abs_nonneg _)
    _ ≤ ∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z, T d e :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun d hd hnot => Finset.sum_nonneg fun e he => abs_nonneg _)

/-- For the concrete affine sieve, the actual optimized error has the sharp
fourth-power bound, with no collapsed-divisor or logarithmic loss. -/
theorem actualAffineSelberg_optimized_errSum_le_fourth_power
    (P : Finset ℕ) (N z u₁ v₁ u₂ v₂ : ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z)
    (hu₁ : ∀ p ∈ P, ¬p ∣ u₁)
    (hu₂ : ∀ p ∈ P, ¬p ∣ u₂)
    (hdet : ∀ p ∈ P,
      (u₁ : ZMod p) * (v₂ : ZMod p) ≠
        (u₂ : ZMod p) * (v₁ : ZMod p)) :
    let s := actualAffineSelbergSieve P N z u₁ v₁ u₂ v₂
      hprime hlarge hz
    BoundingSieve.errSum (s := s.toBoundingSieve)
        (SelbergSieve.selbergMuPlus s) ≤ (z : ℝ) ^ 4 := by
  let s := actualAffineSelbergSieve P N z u₁ v₁ u₂ v₂
    hprime hlarge hz
  change
    BoundingSieve.errSum (s := s.toBoundingSieve)
        (SelbergSieve.selbergMuPlus s) ≤ (z : ℝ) ^ 4
  calc
    BoundingSieve.errSum (s := s.toBoundingSieve)
        (SelbergSieve.selbergMuPlus s) ≤
      ∑ d ∈ Finset.Icc 1 z,
        ∑ e ∈ Finset.Icc 1 z,
          |s.selbergWeights d * s.selbergWeights e *
            BoundingSieve.rem (s := s.toBoundingSieve) (Nat.lcm d e)| :=
      selberg_optimized_errSum_le_lcm_double_cutoff_sum s z (by rfl)
    _ ≤ (z : ℝ) ^ 4 :=
      actualAffineSelberg_two_variable_remainder_le_fourth_power
        P N z u₁ v₁ u₂ v₂ hprime hlarge hz hu₁ hu₂ hdet

/-- The actual affine-parameter sifted count satisfies the fully optimized
Selberg bound with its genuine denominator and exact fourth-power remainder. -/
theorem actualAffineSelberg_sifted_card_le_optimized_fourth_power
    (P : Finset ℕ) (N z u₁ v₁ u₂ v₂ : ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z)
    (hu₁ : ∀ p ∈ P, ¬p ∣ u₁)
    (hu₂ : ∀ p ∈ P, ¬p ∣ u₂)
    (hdet : ∀ p ∈ P,
      (u₁ : ZMod p) * (v₂ : ZMod p) ≠
        (u₂ : ZMod p) * (v₁ : ZMod p)) :
    let s := actualAffineSelbergSieve P N z u₁ v₁ u₂ v₂
      hprime hlarge hz
    (((Finset.range N).filter fun t =>
      Nat.Coprime (∏ p ∈ P, p)
        (affineSieveProduct u₁ v₁ u₂ v₂ t)).card : ℝ) ≤
      (N : ℝ) / s.selbergBoundingSum + (z : ℝ) ^ 4 := by
  let s := actualAffineSelbergSieve P N z u₁ v₁ u₂ v₂
    hprime hlarge hz
  have hsifted := parameter_sifted_card_le_optimized_exact_errSum s
    (Finset.range N) (affineSieveProduct u₁ v₁ u₂ v₂)
    (by rfl) (by intro x hx; rfl)
  change
    (((Finset.range N).filter fun t =>
      Nat.Coprime (∏ p ∈ P, p)
        (affineSieveProduct u₁ v₁ u₂ v₂ t)).card : ℝ) ≤
      (N : ℝ) / s.selbergBoundingSum + (z : ℝ) ^ 4
  change
    (((Finset.range N).filter fun t =>
      Nat.Coprime (∏ p ∈ P, p)
        (affineSieveProduct u₁ v₁ u₂ v₂ t)).card : ℝ) ≤
      (N : ℝ) / s.selbergBoundingSum +
        BoundingSieve.errSum (s := s.toBoundingSieve)
          (SelbergSieve.selbergMuPlus s) at hsifted
  exact hsifted.trans (add_le_add (le_refl _)
    (actualAffineSelberg_optimized_errSum_le_fourth_power
      P N z u₁ v₁ u₂ v₂ hprime hlarge hz hu₁ hu₂ hdet))

/-- The concrete affine sieve bound, with its optimized denominator identified
exactly as the audited squarefree two-root denominator. -/
theorem actualAffineSelberg_sifted_card_le_twoRootDenominator
    (P : Finset ℕ) (M N z u₁ v₁ u₂ v₂ : ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z)
    (hu₁ : ∀ p ∈ P, ¬p ∣ u₁)
    (hu₂ : ∀ p ∈ P, ¬p ∣ u₂)
    (hdet : ∀ p ∈ P,
      (u₁ : ZMod p) * (v₂ : ZMod p) ≠
        (u₂ : ZMod p) * (v₁ : ZMod p))
    (hM : 2 ∣ M)
    (hPM : Nat.Coprime (∏ p ∈ P, p) M)
    (hprimes : ∀ p : ℕ, p.Prime →
      (p ∣ ∏ q ∈ P, q ↔ p ≤ z ∧ Nat.Coprime p M)) :
    (((Finset.range N).filter fun t =>
      Nat.Coprime (∏ p ∈ P, p)
        (affineSieveProduct u₁ v₁ u₂ v₂ t)).card : ℝ) ≤
      (N : ℝ) / twoRootSelbergDenominator M z + (z : ℝ) ^ 4 := by
  let s := actualAffineSelbergSieve P N z u₁ v₁ u₂ v₂
    hprime hlarge hz
  have hsifted := actualAffineSelberg_sifted_card_le_optimized_fourth_power
    P N z u₁ v₁ u₂ v₂ hprime hlarge hz hu₁ hu₂ hdet
  change
    (((Finset.range N).filter fun t =>
      Nat.Coprime (∏ p ∈ P, p)
        (affineSieveProduct u₁ v₁ u₂ v₂ t)).card : ℝ) ≤
      (N : ℝ) / s.selbergBoundingSum + (z : ℝ) ^ 4 at hsifted
  rw [affineSelbergBoundingSum_eq_twoRootDenominator
    s M z hM hPM rfl rfl hprimes] at hsifted
  exact hsifted

/-- The actual simultaneous prime values of two nondegenerate affine forms
obey the exact optimized Selberg bound, with every small-prime and product
collision condition accounted for in the genuine finite parameter set. -/
theorem actualAffineSelberg_large_prime_pair_card_le_twoRootDenominator
    (P : Finset ℕ) (M N z u₁ v₁ u₂ v₂ : ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z)
    (hu₁ : ∀ p ∈ P, ¬p ∣ u₁)
    (hu₂ : ∀ p ∈ P, ¬p ∣ u₂)
    (hdet : ∀ p ∈ P,
      (u₁ : ZMod p) * (v₂ : ZMod p) ≠
        (u₂ : ZMod p) * (v₁ : ZMod p))
    (hM : 2 ∣ M)
    (hPM : Nat.Coprime (∏ p ∈ P, p) M)
    (hprimes : ∀ p : ℕ, p.Prime →
      (p ∣ ∏ q ∈ P, q ↔ p ≤ z ∧ Nat.Coprime p M)) :
    (((Finset.range N).filter fun t =>
      (u₁ * t + v₁).Prime ∧ (u₂ * t + v₂).Prime ∧
        z < u₁ * t + v₁ ∧ z < u₂ * t + v₂).card : ℝ) ≤
      (N : ℝ) / twoRootSelbergDenominator M z + (z : ℝ) ^ 4 := by
  let s := actualAffineSelbergSieve P N z u₁ v₁ u₂ v₂
    hprime hlarge hz
  have hpairs := large_prime_pair_card_le_parameter_sifted
    s (Finset.range N) (fun t => u₁ * t + v₁)
    (fun t => u₂ * t + v₂) z
      (fun p hp hdiv => ((hprimes p hp).mp hdiv).1)
  change
    (((Finset.range N).filter fun t =>
      (u₁ * t + v₁).Prime ∧ (u₂ * t + v₂).Prime ∧
        z < u₁ * t + v₁ ∧ z < u₂ * t + v₂).card : ℝ) ≤
      (((Finset.range N).filter fun t =>
        Nat.Coprime (∏ p ∈ P, p)
          (affineSieveProduct u₁ v₁ u₂ v₂ t)).card : ℝ) at hpairs
  exact hpairs.trans
    (actualAffineSelberg_sifted_card_le_twoRootDenominator
      P M N z u₁ v₁ u₂ v₂ hprime hlarge hz hu₁ hu₂ hdet
        hM hPM hprimes)

/-- Every genuine affine prime pair is either larger than the sieve cutoff
in both coordinates or belongs to the explicitly verified small-prime
exception family.  No modulus-prime exception is necessary here: primes
dividing the excluded modulus are already absent from the sieve. -/
theorem twoAffinePrimeParameters_card_le_large_and_small_exceptions
    (N z u₁ v₁ u₂ v₂ : ℕ)
    (hu₁ : 0 < u₁) (hu₂ : 0 < u₂) :
    (twoAffinePrimeParameters N u₁ v₁ u₂ v₂).card ≤
      ((Finset.range N).filter fun t =>
        (u₁ * t + v₁).Prime ∧ (u₂ * t + v₂).Prime ∧
          z < u₁ * t + v₁ ∧ z < u₂ * t + v₂).card +
        2 * Nat.primeCounting z := by
  let large : Finset ℕ := (Finset.range N).filter fun t =>
    (u₁ * t + v₁).Prime ∧ (u₂ * t + v₂).Prime ∧
      z < u₁ * t + v₁ ∧ z < u₂ * t + v₂
  let exceptions := twoAffineSmallPrimeExceptions N z u₁ v₁ u₂ v₂
  have hsubset :
      twoAffinePrimeParameters N u₁ v₁ u₂ v₂ ⊆ large ∪ exceptions := by
    intro t ht
    obtain ⟨htN, hprime₁, hprime₂⟩ := Finset.mem_filter.mp ht
    by_cases hsmall₁ : u₁ * t + v₁ ≤ z
    · apply Finset.mem_union_right
      apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      exact ⟨htN, Nat.mem_primesLE.mpr ⟨hsmall₁, hprime₁⟩⟩
    by_cases hsmall₂ : u₂ * t + v₂ ≤ z
    · apply Finset.mem_union_right
      apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      exact ⟨htN, Nat.mem_primesLE.mpr ⟨hsmall₂, hprime₂⟩⟩
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      exact ⟨htN, hprime₁, hprime₂, by omega, by omega⟩
  have hcard := Finset.card_le_card hsubset
  have hunion := Finset.card_union_le large exceptions
  have hexceptions := twoAffineSmallPrimeExceptions_card_le
    N z u₁ v₁ u₂ v₂ hu₁ hu₂
  change exceptions.card ≤ 2 * Nat.primeCounting z at hexceptions
  change (twoAffinePrimeParameters N u₁ v₁ u₂ v₂).card ≤
    large.card + 2 * Nat.primeCounting z
  omega

/-- The complete, unrestricted affine two-prime count satisfies the exact
finite optimized Selberg bound, including the necessary `2 π(z)` exceptions. -/
theorem actualAffineSelberg_all_prime_pair_card_le_twoRootDenominator
    (P : Finset ℕ) (M N z u₁ v₁ u₂ v₂ : ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z)
    (hu₁ : ∀ p ∈ P, ¬p ∣ u₁)
    (hu₂ : ∀ p ∈ P, ¬p ∣ u₂)
    (hdet : ∀ p ∈ P,
      (u₁ : ZMod p) * (v₂ : ZMod p) ≠
        (u₂ : ZMod p) * (v₁ : ZMod p))
    (hM : 2 ∣ M)
    (hPM : Nat.Coprime (∏ p ∈ P, p) M)
    (hprimes : ∀ p : ℕ, p.Prime →
      (p ∣ ∏ q ∈ P, q ↔ p ≤ z ∧ Nat.Coprime p M))
    (hu₁positive : 0 < u₁) (hu₂positive : 0 < u₂) :
    ((twoAffinePrimeParameters N u₁ v₁ u₂ v₂).card : ℝ) ≤
      (N : ℝ) / twoRootSelbergDenominator M z + (z : ℝ) ^ 4 +
        ((2 * Nat.primeCounting z : ℕ) : ℝ) := by
  have hdecomp := twoAffinePrimeParameters_card_le_large_and_small_exceptions
    N z u₁ v₁ u₂ v₂ hu₁positive hu₂positive
  have hreal :
      ((twoAffinePrimeParameters N u₁ v₁ u₂ v₂).card : ℝ) ≤
        (((Finset.range N).filter fun t =>
          (u₁ * t + v₁).Prime ∧ (u₂ * t + v₂).Prime ∧
            z < u₁ * t + v₁ ∧ z < u₂ * t + v₂).card : ℝ) +
          ((2 * Nat.primeCounting z : ℕ) : ℝ) := by
    exact_mod_cast hdecomp
  exact hreal.trans (add_le_add
    (actualAffineSelberg_large_prime_pair_card_le_twoRootDenominator
      P M N z u₁ v₁ u₂ v₂ hprime hlarge hz hu₁ hu₂ hdet
      hM hPM hprimes) (le_refl _))

/-- The elementary prime-counting bound is sufficient to make all genuine
small-prime exceptions negligible at the fifth-root Selberg cutoff. -/
theorem primeCounting_le_self (z : ℕ) :
    Nat.primeCounting z ≤ z := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  calc
    (Nat.primesLE z).card ≤ (Finset.Icc 1 z).card := by
      apply Finset.card_le_card
      intro p hp
      obtain ⟨hpz, hpprime⟩ := Nat.mem_primesLE.mp hp
      exact Finset.mem_Icc.mpr ⟨hpprime.pos, hpz⟩
    _ = z := by simp

/-- The actual fifth-root square-block cutoff is positive at every positive
endpoint, so the genuinely instantiated Selberg sieve is never vacuous. -/
theorem selbergSquareRootBlockCutoff_sq_pos_of_pos
    (n : ℕ) (hn : 0 < n) :
    0 < selbergSquareRootBlockCutoff n ^ 2 := by
  have hroot : 1 ≤ selbergFifthRootCutoff n := by
    unfold selbergFifthRootCutoff
    apply (Nat.le_nthRoot_iff (by norm_num : (5 : ℕ) ≠ 0)).mpr
    simpa using (Nat.succ_le_of_lt hn)
  have hblock : 0 < selbergSquareRootBlockCutoff n := by
    unfold selbergSquareRootBlockCutoff
    exact Nat.sqrt_pos.mpr (by omega)
  positivity

/-- Uniform genuine affine-prime-pair bound for any moving outside prime.
The leading coefficient is the sharp verified `605 / 3`; the two explicit
error terms are the real optimized sieve remainder and the exact small-prime
exceptions, not a conjectural prime-pattern estimate. -/
theorem actualAffineSelberg_all_prime_pairs_fifth_root_eventually_explicit
    (M : ℕ) (hMeven : 2 ∣ M) (hM : 2 ≤ M) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (q : ℕ) (P : Finset ℕ) (u₁ v₁ u₂ v₂ : ℕ),
        q.Prime → Nat.Coprime q M → 5 ≤ q →
        (∀ p ∈ P, p.Prime) →
        (∀ p ∈ P, 2 < p) →
        (∀ p ∈ P, ¬p ∣ u₁) →
        (∀ p ∈ P, ¬p ∣ u₂) →
        (∀ p ∈ P,
          (u₁ : ZMod p) * (v₂ : ZMod p) ≠
            (u₂ : ZMod p) * (v₁ : ZMod p)) →
        Nat.Coprime (∏ p ∈ P, p) (M * q) →
        (∀ p : ℕ, p.Prime →
          (p ∣ ∏ r ∈ P, r ↔
            p ≤ selbergSquareRootBlockCutoff n ^ 2 ∧
              Nat.Coprime p (M * q))) →
        0 < u₁ → 0 < u₂ →
        ((twoAffinePrimeParameters n u₁ v₁ u₂ v₂).card : ℝ) ≤
          (605 / 3 : ℝ) * (((M : ℝ) / M.totient) ^ 2) *
              ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) +
            ((selbergSquareRootBlockCutoff n ^ 2 : ℕ) : ℝ) ^ 4 +
              ((2 * Nat.primeCounting
                (selbergSquareRootBlockCutoff n ^ 2) : ℕ) : ℝ) := by
  filter_upwards
    [twoRootSelbergDenominator_fifth_root_eventually_inv_le_explicit
      M hMeven hM, eventually_ge_atTop 1] with n hdenominator hn
  intro q P u₁ v₁ u₂ v₂ hq hqM hqfive hprime hlarge hu₁ hu₂ hdet
    hPM hprimes hu₁positive hu₂positive
  let z := selbergSquareRootBlockCutoff n ^ 2
  have hz : 0 < z := selbergSquareRootBlockCutoff_sq_pos_of_pos n (by omega)
  have hmodulus : 2 ∣ M * q := dvd_mul_of_dvd_left hMeven q
  have hpair := actualAffineSelberg_all_prime_pair_card_le_twoRootDenominator
    P (M * q) n z u₁ v₁ u₂ v₂ hprime hlarge hz hu₁ hu₂ hdet
      hmodulus hPM hprimes hu₁positive hu₂positive
  have hinverse := hdenominator q hq hqM hqfive
  have hmain :
      (n : ℝ) / twoRootSelbergDenominator (M * q) z ≤
        (605 / 3 : ℝ) * (((M : ℝ) / M.totient) ^ 2) *
          ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
    rw [div_eq_mul_inv]
    calc
      (n : ℝ) * (twoRootSelbergDenominator (M * q) z)⁻¹ ≤
        (n : ℝ) *
          ((605 / 3 : ℝ) * (((M : ℝ) / M.totient) ^ 2) /
            (Real.log (n : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hinverse (by positivity)
      _ = (605 / 3 : ℝ) * (((M : ℝ) / M.totient) ^ 2) *
          ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by ring
  exact hpair.trans (add_le_add
    (add_le_add hmain (le_refl _)) (le_refl _))

/-- At the actual block cutoff, the complete genuine error -- both the
optimized fourth-power Selberg remainder and all small-prime exceptions --
is little-o of the required `n / log(n)^2` degree scale. -/
theorem selberg_block_cutoff_complete_remainder_normalized_tendsto_zero :
    Tendsto
      (fun n : ℕ =>
        (((selbergSquareRootBlockCutoff n ^ 2 : ℕ) : ℝ) ^ 4 +
          ((2 * Nat.primeCounting
            (selbergSquareRootBlockCutoff n ^ 2) : ℕ) : ℝ)) /
            ((n : ℝ) / (Real.log (n : ℝ)) ^ 2))
      atTop (nhds 0) := by
  have hmajor :
      Tendsto
        (fun n : ℕ =>
          (3 : ℝ) *
            ((selbergFifthRootCutoff n : ℝ) ^ 4 /
              ((n : ℝ) / (Real.log (n : ℝ)) ^ 2)))
        atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul
        selbergFifthRootCutoff_fourth_power_normalized_tendsto_zero :
          Tendsto
            (fun n : ℕ =>
              (3 : ℝ) *
                ((selbergFifthRootCutoff n : ℝ) ^ 4 /
                  ((n : ℝ) / (Real.log (n : ℝ)) ^ 2)))
            atTop (nhds ((3 : ℝ) * 0)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hmajor ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnreal : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hnone : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnone
    positivity
  · filter_upwards [eventually_ge_atTop 2] with n hn
    let z := selbergSquareRootBlockCutoff n ^ 2
    let w := selbergFifthRootCutoff n
    have hnreal : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hnone : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnone
    have hdenominator :
        (0 : ℝ) < (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by positivity
    have hwpos : 1 ≤ w := by
      unfold w selbergFifthRootCutoff
      apply (Nat.le_nthRoot_iff (by norm_num : (5 : ℕ) ≠ 0)).mpr
      norm_num
      omega
    have hzw : z ≤ w := selbergSquareRootBlockCutoff_sq_le n
    have hzwreal : (z : ℝ) ≤ w := by exact_mod_cast hzw
    have hwr : (1 : ℝ) ≤ w := by exact_mod_cast hwpos
    have hfourth : (z : ℝ) ^ 4 ≤ (w : ℝ) ^ 4 := by gcongr
    have hlinear : (w : ℝ) ≤ (w : ℝ) ^ 4 := by
      calc
        (w : ℝ) = (w : ℝ) * 1 := by ring
        _ ≤ (w : ℝ) * (w : ℝ) ^ 3 := by
          gcongr
          exact one_le_pow₀ hwr
        _ = (w : ℝ) ^ 4 := by ring
    have hprimecount : (Nat.primeCounting z : ℝ) ≤ (w : ℝ) ^ 4 := by
      calc
        (Nat.primeCounting z : ℝ) ≤ z := by
          exact_mod_cast primeCounting_le_self z
        _ ≤ w := hzwreal
        _ ≤ (w : ℝ) ^ 4 := hlinear
    have hnumerator :
        (z : ℝ) ^ 4 + ((2 * Nat.primeCounting z : ℕ) : ℝ) ≤
          (3 : ℝ) * (w : ℝ) ^ 4 := by
      push_cast
      nlinarith
    change
      ((z : ℝ) ^ 4 + ((2 * Nat.primeCounting z : ℕ) : ℝ)) /
          ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) ≤
        (3 : ℝ) *
          ((w : ℝ) ^ 4 / ((n : ℝ) / (Real.log (n : ℝ)) ^ 2))
    rw [← mul_div_assoc]
    exact (div_le_div_iff_of_pos_right hdenominator).mpr hnumerator

/-- The concrete optimized sieve for *arbitrary* two parameter functions on
an arbitrary finite interval.  In particular, either function may encode a
genuine decreasing affine form; product collisions retain their exact fibers. -/
noncomputable def actualTwoFunctionSelbergSieve
    (P I : Finset ℕ) (f g : ℕ → ℕ) (z : ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z) : SelbergSieve where
  support := I.image (fun t => f t * g t)
  prodPrimes := ∏ p ∈ P, p
  prodPrimes_squarefree := Sieve.prodDistinctPrimes_squarefree P hprime
  weights := fun x =>
    ((I.filter fun t => f t * g t = x).card : ℝ)
  weights_nonneg := by
    intro x
    positivity
  totalMass := (I.card : ℝ)
  nu := twoRootDivisorMajorant
  nu_mult := twoRootDivisorMajorant_completelyMultiplicative.isMultiplicative
  nu_pos_of_prime := by
    intro p hp hdiv
    rw [twoRootDivisorMajorant_prime hp]
    exact div_pos (by norm_num) (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := by
    intro p hp hdiv
    have hPzero : (∏ q ∈ P, q) ≠ 0 :=
      Nat.ne_of_gt (Finset.prod_pos fun q hq => (hprime q hq).pos)
    have hpP : p ∈ (∏ q ∈ P, q).primeFactors :=
      (Nat.mem_primeFactors_of_ne_zero hPzero).mpr ⟨hp, hdiv⟩
    rw [Nat.primeFactors_prod hprime] at hpP
    rw [twoRootDivisorMajorant_prime hp]
    apply (div_lt_one (by exact_mod_cast hp.pos)).mpr
    exact_mod_cast hlarge p hpP
  level := (z : ℝ) ^ 2
  one_le_level := by
    have hzreal : (1 : ℝ) ≤ z := by exact_mod_cast hz
    nlinarith [sq_nonneg ((z : ℝ) - 1)]

/-- Exact divisor multiplicities for an arbitrary pair of parameter functions;
no monotonicity, sign, or injectivity is presumed. -/
theorem actualTwoFunctionSelberg_multSum_eq_parameter_card
    (P I : Finset ℕ) (f g : ℕ → ℕ) (z d : ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z) :
    BoundingSieve.multSum
      (s := (actualTwoFunctionSelbergSieve P I f g z
        hprime hlarge hz).toBoundingSieve) d =
      ((I.filter fun t => d ∣ f t * g t).card : ℝ) := by
  classical
  let F : ℕ → ℕ := fun t => f t * g t
  change
    (∑ x ∈ I.image F,
      if d ∣ x then ((I.filter fun t => F t = x).card : ℝ) else 0) =
        ((I.filter fun t => d ∣ F t).card : ℝ)
  rw [← Finset.sum_filter]
  calc
    (∑ x ∈ (I.image F).filter (fun x => d ∣ x),
      ((I.filter fun t => F t = x).card : ℝ)) =
        ((∑ x ∈ (I.image F).filter (fun x => d ∣ x),
          (I.filter fun t => F t = x).card : ℕ) : ℝ) := by
      norm_cast
    _ = ((I.filter fun t => d ∣ F t).card : ℝ) := by
      rw [Finset.sum_card_fiberwise_eq_card_filter]
      have hsets :
          I.filter (fun t => F t ∈ (I.image F).filter (fun x => d ∣ x)) =
            I.filter (fun t => d ∣ F t) := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_image]
        aesop
      rw [hsets]

/-- The only analytic contract needed for arbitrary or genuinely signed
two-form sieves: their actual divisor-count discrepancy has the exact
modulus bound on the divisors actually appearing in the finite sieve. -/
def ActualTwoFormDivisorRemainderContract (s : SelbergSieve) : Prop :=
  ∀ d : ℕ, d ∣ s.prodPrimes →
    |BoundingSieve.rem (s := s.toBoundingSieve) d| ≤ (d : ℝ)

/-- An arbitrary actual two-form sieve with the explicit divisor discrepancy
contract has the sharp fourth-power optimized error, regardless of signs. -/
theorem selberg_optimized_errSum_le_fourth_power_of_divisor_contract
    (s : SelbergSieve) (z : ℕ)
    (hlevel : s.level ≤ (z : ℝ) ^ 2)
    (hremainder : ActualTwoFormDivisorRemainderContract s) :
    BoundingSieve.errSum (s := s.toBoundingSieve)
      (SelbergSieve.selbergMuPlus s) ≤ (z : ℝ) ^ 4 := by
  classical
  let remainder : ℕ → ℝ := fun h =>
    if h ∣ s.prodPrimes then BoundingSieve.rem (s := s.toBoundingSieve) h
    else 0
  have hbounded : ∀ h : ℕ, |remainder h| ≤ (h : ℝ) := by
    intro h
    unfold remainder
    split_ifs with hd
    · exact hremainder h hd
    · simp
  have hrewrite (d e : ℕ) :
      s.selbergWeights d * s.selbergWeights e *
        BoundingSieve.rem (s := s.toBoundingSieve) (Nat.lcm d e) =
      s.selbergWeights d * s.selbergWeights e * remainder (Nat.lcm d e) := by
    unfold remainder
    split_ifs with hlcm
    · rfl
    · by_cases hd : d ∣ s.prodPrimes
      · have he : ¬e ∣ s.prodPrimes := by
          intro he
          exact hlcm (Nat.lcm_dvd hd he)
        rw [s.selbergWeights_eq_zero_of_not_dvd he]
        ring
      · rw [s.selbergWeights_eq_zero_of_not_dvd hd]
        ring
  calc
    BoundingSieve.errSum (s := s.toBoundingSieve)
        (SelbergSieve.selbergMuPlus s) ≤
      ∑ d ∈ Finset.Icc 1 z,
        ∑ e ∈ Finset.Icc 1 z,
          |s.selbergWeights d * s.selbergWeights e *
            BoundingSieve.rem (s := s.toBoundingSieve) (Nat.lcm d e)| :=
      selberg_optimized_errSum_le_lcm_double_cutoff_sum s z hlevel
    _ = ∑ d ∈ Finset.Icc 1 z,
          ∑ e ∈ Finset.Icc 1 z,
            |s.selbergWeights d * s.selbergWeights e *
              remainder (Nat.lcm d e)| := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      rw [hrewrite d e]
    _ ≤ (z : ℝ) ^ 4 :=
      selberg_two_variable_remainder_le_fourth_power z s.selbergWeights
        remainder (fun d => s.selberg_bound_weights d) hbounded

/-- Generic exact optimized two-function sieve, valid in particular for the
actual mixed-sign fiber `f(t) = t`, `g(t) = y - a*t`, conditional *only* on
the explicitly named genuine divisor discrepancy contract. -/
theorem actualTwoFunction_sifted_card_le_twoRootDenominator
    (P I : Finset ℕ) (f g : ℕ → ℕ) (M z : ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z)
    (hM : 2 ∣ M)
    (hPM : Nat.Coprime (∏ p ∈ P, p) M)
    (hprimes : ∀ p : ℕ, p.Prime →
      (p ∣ ∏ q ∈ P, q ↔ p ≤ z ∧ Nat.Coprime p M))
    (hremainder : ActualTwoFormDivisorRemainderContract
      (actualTwoFunctionSelbergSieve P I f g z hprime hlarge hz)) :
    ((I.filter fun t => Nat.Coprime (∏ p ∈ P, p) (f t * g t)).card : ℝ) ≤
      (I.card : ℝ) / twoRootSelbergDenominator M z + (z : ℝ) ^ 4 := by
  let s := actualTwoFunctionSelbergSieve P I f g z hprime hlarge hz
  have hsifted := parameter_sifted_card_le_optimized_exact_errSum s I
    (fun t => f t * g t) (by rfl) (by intro x hx; rfl)
  have herror := selberg_optimized_errSum_le_fourth_power_of_divisor_contract
    s z (by rfl) hremainder
  have hdenominator := affineSelbergBoundingSum_eq_twoRootDenominator
    s M z hM hPM rfl rfl hprimes
  change
    ((I.filter fun t => Nat.Coprime (∏ p ∈ P, p)
      (f t * g t)).card : ℝ) ≤
      (I.card : ℝ) / s.selbergBoundingSum +
        BoundingSieve.errSum (s := s.toBoundingSieve)
          (SelbergSieve.selbergMuPlus s) at hsifted
  rw [hdenominator] at hsifted
  exact hsifted.trans (add_le_add (le_refl _) herror)

/-- Replace a genuinely decreasing natural affine form by a positive-slope
form congruent at every divisor of a fixed positive sieve modulus.  The
explicit no-underflow hypothesis is essential: natural subtraction is not
globally compatible with modular reduction. -/
theorem mixedDescendingProduct_dvd_iff_positive_surrogate
    (B a y t d : ℕ) (hB : 0 < B) (hd : d ∣ B)
    (hunderflow : a * t ≤ y) :
    d ∣ t * (y - a * t) ↔
      d ∣ t * ((B - a % B) * t + y) := by
  let u := B - a % B
  have hmodbound : a % B ≤ B := (Nat.mod_lt a hB).le
  have hsum : u + a % B = B := Nat.sub_add_cancel hmodbound
  have hmod : Nat.ModEq d (a % B) a :=
    (Nat.mod_modEq a B).of_dvd hd
  have hsumcong : Nat.ModEq d (u + a) 0 := by
    have hreplace : Nat.ModEq d (u + a % B) (u + a) :=
      Nat.ModEq.rfl.add hmod
    have hzero : Nat.ModEq d (u + a % B) 0 := by
      rw [hsum]
      exact Nat.modEq_zero_iff_dvd.mpr hd
    exact hreplace.symm.trans hzero
  have hsurplus : Nat.ModEq d ((u * t + y) + a * t) y := by
    calc
      (u * t + y) + a * t = (u + a) * t + y := by ring
      _ ≡ 0 * t + y [MOD d] :=
        (hsumcong.mul_right t).add_right y
      _ = y := by simp
  have heq : (y - a * t) + a * t = y :=
    Nat.sub_add_cancel hunderflow
  have hlinear : Nat.ModEq d (u * t + y) (y - a * t) := by
    apply Nat.ModEq.add_right_cancel' (a * t)
    rw [heq]
    exact hsurplus
  have hproduct : Nat.ModEq d
      (t * (u * t + y)) (t * (y - a * t)) :=
    Nat.ModEq.rfl.mul hlinear
  exact (hproduct.dvd_iff (dvd_refl d)).symm

/-- The positive modular surrogate of a descending slope remains nonzero
at every sieve prime at which the original slope is nonzero. -/
theorem mixedDescendingSurrogate_not_dvd_of_not_dvd
    (B a p : ℕ) (hB : 0 < B) (hpB : p ∣ B)
    (hpa : ¬p ∣ a) :
    ¬p ∣ B - a % B := by
  intro hpu
  have hmodbound : a % B ≤ B := (Nat.mod_lt a hB).le
  have hsum : (B - a % B) + a % B = B :=
    Nat.sub_add_cancel hmodbound
  have hmoddiv : p ∣ a % B := by
    have hsumdiv : p ∣ (B - a % B) + a % B := by
      rw [hsum]
      exact hpB
    exact (Nat.dvd_add_iff_left hpu).mpr
      (by simpa [Nat.add_comm] using hsumdiv)
  have hmod : Nat.ModEq p (a % B) a :=
    (Nat.mod_modEq a B).of_dvd hpB
  exact hpa ((hmod.dvd_iff (dvd_refl p)).mp hmoddiv)

/-- Every actual mixed-sign divisor multiplicity coincides exactly with the
positive modular-surrogate sieve's divisor multiplicity.  The parameter
interval is restricted to the genuine non-saturated descending branch. -/
theorem actualMixedSelberg_multSum_eq_positive_surrogate
    (P : Finset ℕ) (N z a y d : ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z)
    (hunderflow : ∀ t < N, a * t ≤ y)
    (hd : d ∣ ∏ p ∈ P, p) :
    let B := ∏ p ∈ P, p
    let mixed := actualTwoFunctionSelbergSieve
      P (Finset.range N) (fun t => t) (fun t => y - a * t) z
      hprime hlarge hz
    let positive := actualAffineSelbergSieve
      P N z 1 0 (B - a % B) y hprime hlarge hz
    BoundingSieve.multSum (s := mixed.toBoundingSieve) d =
      BoundingSieve.multSum (s := positive.toBoundingSieve) d := by
  let B := ∏ p ∈ P, p
  have hB : 0 < B := Finset.prod_pos fun p hp => (hprime p hp).pos
  change
    BoundingSieve.multSum
      (s := (actualTwoFunctionSelbergSieve P (Finset.range N)
        (fun t => t) (fun t => y - a * t) z
        hprime hlarge hz).toBoundingSieve) d =
      BoundingSieve.multSum
        (s := (actualAffineSelbergSieve P N z 1 0 (B - a % B) y
          hprime hlarge hz).toBoundingSieve) d
  rw [actualTwoFunctionSelberg_multSum_eq_parameter_card,
    actualAffineSelberg_multSum_eq_parameter_card]
  have hsets :
      (Finset.range N).filter (fun t => d ∣ t * (y - a * t)) =
        (Finset.range N).filter
          (fun t => d ∣ affineSieveProduct 1 0 (B - a % B) y t) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    apply and_congr_right
    intro ht
    simpa [affineSieveProduct] using
      mixedDescendingProduct_dvd_iff_positive_surrogate
        B a y t d hB hd (hunderflow t ht)
  rw [hsets]

/-- The genuinely decreasing affine form satisfies the *actual* optimized
Selberg remainder contract unconditionally.  No signed prime-counting or
root-density hypothesis remains: both follow by exact transport to the
positive modular surrogate and its already verified CRT remainder. -/
theorem actualMixedSelberg_divisor_remainder_contract
    (P : Finset ℕ) (N z a y : ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z)
    (ha : ∀ p ∈ P, ¬p ∣ a)
    (hy : ∀ p ∈ P, ¬p ∣ y)
    (hunderflow : ∀ t < N, a * t ≤ y) :
    ActualTwoFormDivisorRemainderContract
      (actualTwoFunctionSelbergSieve P (Finset.range N)
        (fun t => t) (fun t => y - a * t) z hprime hlarge hz) := by
  let B := ∏ p ∈ P, p
  let u := B - a % B
  let mixed := actualTwoFunctionSelbergSieve P (Finset.range N)
    (fun t => t) (fun t => y - a * t) z hprime hlarge hz
  let positive := actualAffineSelbergSieve P N z 1 0 u y
    hprime hlarge hz
  have hB : 0 < B := Finset.prod_pos fun p hp => (hprime p hp).pos
  have hone : ∀ p ∈ P, ¬p ∣ (1 : ℕ) := by
    intro p hp hdiv
    exact (hprime p hp).ne_one (Nat.dvd_one.mp hdiv)
  have hu : ∀ p ∈ P, ¬p ∣ u := by
    intro p hp
    exact mixedDescendingSurrogate_not_dvd_of_not_dvd
      B a p hB (Finset.dvd_prod_of_mem (fun q : ℕ => q) hp)
        (ha p hp)
  have hdet : ∀ p ∈ P,
      ((1 : ℕ) : ZMod p) * (y : ZMod p) ≠
        (u : ZMod p) * ((0 : ℕ) : ZMod p) := by
    intro p hp
    simpa using fun h : (y : ZMod p) = 0 =>
      hy p hp ((ZMod.natCast_eq_zero_iff y p).mp h)
  intro d hd
  have hmult := actualMixedSelberg_multSum_eq_positive_surrogate
    P N z a y d hprime hlarge hz hunderflow hd
  change
    BoundingSieve.multSum (s := mixed.toBoundingSieve) d =
      BoundingSieve.multSum (s := positive.toBoundingSieve) d at hmult
  have hrem :
      BoundingSieve.rem (s := mixed.toBoundingSieve) d =
        BoundingSieve.rem (s := positive.toBoundingSieve) d := by
    unfold BoundingSieve.rem
    rw [hmult]
    change
      BoundingSieve.multSum (s := positive.toBoundingSieve) d -
          twoRootDivisorMajorant d * ((Finset.range N).card : ℝ) =
        BoundingSieve.multSum (s := positive.toBoundingSieve) d -
          twoRootDivisorMajorant d * (N : ℝ)
    simp
  change |BoundingSieve.rem (s := mixed.toBoundingSieve) d| ≤ (d : ℝ)
  rw [hrem]
  exact actualAffineSelberg_rem_abs_le_of_dvd
    P N z 1 0 u y d hprime hlarge hz hone hu hdet hd

/-- Fully unconditional optimized Selberg bound for the genuinely mixed-sign
product `t * (y - a*t)` on its nonsaturated interval.  The finite sieve,
its CRT remainder, its denominator, and its fourth-power error are all
constructed and proved; no signed-form remainder contract is assumed. -/
theorem actualMixedSelberg_sifted_card_le_twoRootDenominator
    (P : Finset ℕ) (M N z a y : ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z)
    (ha : ∀ p ∈ P, ¬p ∣ a)
    (hy : ∀ p ∈ P, ¬p ∣ y)
    (hunderflow : ∀ t < N, a * t ≤ y)
    (hM : 2 ∣ M)
    (hPM : Nat.Coprime (∏ p ∈ P, p) M)
    (hprimes : ∀ p : ℕ, p.Prime →
      (p ∣ ∏ q ∈ P, q ↔ p ≤ z ∧ Nat.Coprime p M)) :
    (((Finset.range N).filter fun t =>
      Nat.Coprime (∏ p ∈ P, p) (t * (y - a * t))).card : ℝ) ≤
      (N : ℝ) / twoRootSelbergDenominator M z + (z : ℝ) ^ 4 := by
  simpa using actualTwoFunction_sifted_card_le_twoRootDenominator
    P (Finset.range N) (fun t => t) (fun t => y - a * t)
    M z hprime hlarge hz hM hPM hprimes
      (actualMixedSelberg_divisor_remainder_contract
        P N z a y hprime hlarge hz ha hy hunderflow)

/-- Genuine mixed-sign simultaneous prime values satisfy the fully optimized
finite Selberg bound, with neither a positive-slope restriction nor an
unproved analytic remainder hypothesis. -/
theorem actualMixedSelberg_large_prime_pair_card_le_twoRootDenominator
    (P : Finset ℕ) (M N z a y : ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z)
    (ha : ∀ p ∈ P, ¬p ∣ a)
    (hy : ∀ p ∈ P, ¬p ∣ y)
    (hunderflow : ∀ t < N, a * t ≤ y)
    (hM : 2 ∣ M)
    (hPM : Nat.Coprime (∏ p ∈ P, p) M)
    (hprimes : ∀ p : ℕ, p.Prime →
      (p ∣ ∏ q ∈ P, q ↔ p ≤ z ∧ Nat.Coprime p M)) :
    (((Finset.range N).filter fun t =>
      t.Prime ∧ (y - a * t).Prime ∧ z < t ∧ z < y - a * t).card : ℝ) ≤
      (N : ℝ) / twoRootSelbergDenominator M z + (z : ℝ) ^ 4 := by
  let s := actualTwoFunctionSelbergSieve P (Finset.range N)
    (fun t => t) (fun t => y - a * t) z hprime hlarge hz
  have hpairs := large_prime_pair_card_le_parameter_sifted
    s (Finset.range N) (fun t => t) (fun t => y - a * t) z
      (fun p hp hdiv => ((hprimes p hp).mp hdiv).1)
  change
    (((Finset.range N).filter fun t =>
      t.Prime ∧ (y - a * t).Prime ∧ z < t ∧ z < y - a * t).card : ℝ) ≤
      (((Finset.range N).filter fun t =>
        Nat.Coprime (∏ p ∈ P, p) (t * (y - a * t))).card : ℝ) at hpairs
  exact hpairs.trans (actualMixedSelberg_sifted_card_le_twoRootDenominator
    P M N z a y hprime hlarge hz ha hy hunderflow hM hPM hprimes)

#print axioms Erdos689.parameter_sifted_card_le_optimized_exact_errSum
#print axioms Erdos689.lcm_divisor_triple_sum_eq_double
#print axioms Erdos689.selberg_optimized_errSum_le_lcm_double_divisor_sum
#print axioms Erdos689.selberg_optimized_weight_eq_zero_above_cutoff
#print axioms Erdos689.selberg_optimized_errSum_le_lcm_double_cutoff_sum
#print axioms Erdos689.actualAffineSelberg_optimized_errSum_le_fourth_power
#print axioms Erdos689.actualAffineSelberg_sifted_card_le_optimized_fourth_power
#print axioms Erdos689.actualAffineSelberg_sifted_card_le_twoRootDenominator
#print axioms Erdos689.actualAffineSelberg_large_prime_pair_card_le_twoRootDenominator
#print axioms Erdos689.twoAffinePrimeParameters_card_le_large_and_small_exceptions
#print axioms Erdos689.actualAffineSelberg_all_prime_pair_card_le_twoRootDenominator
#print axioms Erdos689.primeCounting_le_self
#print axioms Erdos689.selbergSquareRootBlockCutoff_sq_pos_of_pos
#print axioms Erdos689.actualAffineSelberg_all_prime_pairs_fifth_root_eventually_explicit
#print axioms Erdos689.selberg_block_cutoff_complete_remainder_normalized_tendsto_zero
#print axioms Erdos689.actualTwoFunctionSelberg_multSum_eq_parameter_card
#print axioms Erdos689.selberg_optimized_errSum_le_fourth_power_of_divisor_contract
#print axioms Erdos689.actualTwoFunction_sifted_card_le_twoRootDenominator
#print axioms Erdos689.mixedDescendingProduct_dvd_iff_positive_surrogate
#print axioms Erdos689.mixedDescendingSurrogate_not_dvd_of_not_dvd
#print axioms Erdos689.actualMixedSelberg_multSum_eq_positive_surrogate
#print axioms Erdos689.actualMixedSelberg_divisor_remainder_contract
#print axioms Erdos689.actualMixedSelberg_sifted_card_le_twoRootDenominator
#print axioms Erdos689.actualMixedSelberg_large_prime_pair_card_le_twoRootDenominator

end Erdos689
