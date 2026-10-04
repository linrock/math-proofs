module

public import SelbergOptimizedBridge433
public import AffineDegreeFibers433

@[expose] public section


/-!
# The genuine exceptional determinant prime in the Erdős #689 degree sieve

The full manuscript edge relation admits the outside prime `3`. At that
prime the two affine roots coincide, so the generic two-distinct-root formula
cannot be used. This file computes the actual one-root local class, its true
discrepancy, its exact CRT combination with all nondegenerate sieve primes,
and the correction factor `3 / 2`.

It also bounds the actual right-vertex and prime-label fibers coming from
left vertices with outside prime `3` by the number of support divisors.
No unrestricted degree estimate, ternary major-arc estimate, or covering
conclusion is asserted.
-/

open Filter
open scoped BigOperators Topology

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Erdos689

/-- When both slopes are nonzero and the determinant vanishes, the two actual
finite-field affine roots coincide and the product has exactly one root. -/
theorem twoAffineFieldRoots_card_eq_one_of_det_eq
    {K : Type*} [Field K] [Fintype K]
    (u₁ v₁ u₂ v₂ : K)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0)
    (hdet : u₁ * v₂ = u₂ * v₁) :
    (twoAffineFieldRoots K u₁ v₁ u₂ v₂).card = 1 := by
  classical
  have hsame : -v₁ / u₁ = -v₂ / u₂ := by
    apply (div_eq_div_iff hu₁ hu₂).mpr
    calc
      -v₁ * u₂ = -(u₂ * v₁) := by ring
      _ = -(u₁ * v₂) := by rw [hdet]
      _ = -v₂ * u₁ := by ring
  have hroots :
      twoAffineFieldRoots K u₁ v₁ u₂ v₂ = {-v₁ / u₁} := by
    ext x
    simp only [twoAffineFieldRoots, Finset.mem_filter, Finset.mem_univ,
      true_and, mul_eq_zero, Finset.mem_singleton]
    rw [affine_field_zero_iff u₁ v₁ x hu₁,
      affine_field_zero_iff u₂ v₂ x hu₂]
    simp [hsame]
  rw [hroots]
  exact Finset.card_singleton _

/-- The actual natural residue-root set has precisely one class at any prime
where both slopes are units and the affine determinant vanishes. -/
theorem affineSieveRootResidues_card_eq_one_of_prime_det_collision
    (p u₁ v₁ u₂ v₂ : ℕ) [Fact p.Prime] (hp : p.Prime)
    (hu₁ : ¬p ∣ u₁) (hu₂ : ¬p ∣ u₂)
    (hdet : (u₁ : ZMod p) * (v₂ : ZMod p) =
      (u₂ : ZMod p) * (v₁ : ZMod p)) :
    (affineSieveRootResidues p u₁ v₁ u₂ v₂).card = 1 := by
  rw [affineSieveRootResidues_card_eq_fieldRoots p u₁ v₁ u₂ v₂ hp]
  apply twoAffineFieldRoots_card_eq_one_of_det_eq
  · exact fun hzero => hu₁ ((ZMod.natCast_eq_zero_iff u₁ p).mp hzero)
  · exact fun hzero => hu₂ ((ZMod.natCast_eq_zero_iff u₂ p).mp hzero)
  · exact hdet

/-- At a genuine one-root determinant collision the actual interval-count
discrepancy is at most one, not the generic two-root bound. -/
theorem affineSieveRemainder_abs_le_one_of_prime_det_collision
    (N p u₁ v₁ u₂ v₂ : ℕ) [Fact p.Prime] (hp : p.Prime)
    (hu₁ : ¬p ∣ u₁) (hu₂ : ¬p ∣ u₂)
    (hdet : (u₁ : ZMod p) * (v₂ : ZMod p) =
      (u₂ : ZMod p) * (v₁ : ZMod p)) :
    |affineSieveRemainder N p u₁ v₁ u₂ v₂| ≤ (1 : ℝ) := by
  unfold affineSieveRemainder
  rw [if_neg (Nat.ne_of_gt hp.pos)]
  convert residueRootRemainder_abs_le_card N p
    (affineSieveRootResidues p u₁ v₁ u₂ v₂) hp.pos
      (Finset.filter_subset _ _) using 1
  exact_mod_cast (affineSieveRootResidues_card_eq_one_of_prime_det_collision
    p u₁ v₁ u₂ v₂ hp hu₁ hu₂ hdet).symm

/-- The actual determinant-three branch `t * (u*t+v)` has exactly one root
when `3 ∣ v` but `3 ∤ u`. -/
theorem exceptionalThree_affine_root_card
  (u v : ℕ) (hu : ¬3 ∣ u) (hv : 3 ∣ v) :
    (affineSieveRootResidues 3 1 0 u v).card = 1 := by
  have hprime : Nat.Prime 3 := by norm_num
  apply @affineSieveRootResidues_card_eq_one_of_prime_det_collision
    3 1 0 u v ⟨hprime⟩ hprime (by norm_num) hu
  have hzero : (v : ZMod 3) = 0 :=
    (ZMod.natCast_eq_zero_iff v 3).mpr hv
  simp [hzero]

/-- The determinant-three branch has the exact local singular correction
`(1-1/3)/(1-1/3)^2 = 3/2`; this comes from its real one-root class. -/
theorem exceptionalThree_actual_singular_factor
    (u v : ℕ) (hu : ¬3 ∣ u) (hv : 3 ∣ v) :
    ((1 : ℝ) -
      ((affineSieveRootResidues 3 1 0 u v).card : ℝ) / 3) /
      ((1 : ℝ) - 1 / 3) ^ 2 = 3 / 2 := by
  rw [exceptionalThree_affine_root_card u v hu hv]
  norm_num

/-- Combining the exceptional one-root prime `3` with any family of genuine
nondegenerate primes keeps exactly `2 ^ card(P)` actual CRT root classes. -/
theorem exceptionalThree_generic_prime_product_root_card
    (P : Finset ℕ) (u₁ v₁ u₂ v₂ : ℕ)
    (hthree : 3 ∉ P)
    (hprime : ∀ p ∈ P, p.Prime)
    (hu₁ : ∀ p ∈ P, ¬p ∣ u₁)
    (hu₂ : ∀ p ∈ P, ¬p ∣ u₂)
    (hdet : ∀ p ∈ P,
      (u₁ : ZMod p) * (v₂ : ZMod p) ≠
        (u₂ : ZMod p) * (v₁ : ZMod p))
    (hu₁three : ¬3 ∣ u₁) (hu₂three : ¬3 ∣ u₂)
    (hdetthree : (u₁ : ZMod 3) * (v₂ : ZMod 3) =
      (u₂ : ZMod 3) * (v₁ : ZMod 3)) :
    (affineSieveRootResidues (3 * ∏ p ∈ P, p)
      u₁ v₁ u₂ v₂).card = 2 ^ P.card := by
  classical
  have hthreeprime : Nat.Prime 3 := by norm_num
  have hproduct : 0 < ∏ p ∈ P, p :=
    Finset.prod_pos fun p hp => (hprime p hp).pos
  have hnotdiv : ¬3 ∣ ∏ p ∈ P, p := by
    intro hdiv
    obtain ⟨p, hp, hthreep⟩ :=
      (hthreeprime.prime.dvd_finsetProd_iff (fun p : ℕ => p)).mp hdiv
    have heq :=
      (Nat.prime_dvd_prime_iff_eq hthreeprime (hprime p hp)).mp hthreep
    exact hthree (heq ▸ hp)
  have hcoprime : Nat.Coprime 3 (∏ p ∈ P, p) :=
    hthreeprime.coprime_iff_not_dvd.mpr hnotdiv
  have hlocal := @affineSieveRootResidues_card_eq_one_of_prime_det_collision
    3 u₁ v₁ u₂ v₂ ⟨hthreeprime⟩ hthreeprime hu₁three hu₂three hdetthree
  rw [affineSieveRootResidues_card_mul_of_coprime
    3 (∏ p ∈ P, p) u₁ v₁ u₂ v₂ (by norm_num) hproduct hcoprime,
    hlocal,
    affineSieveRootResidues_card_prime_product
      P u₁ v₁ u₂ v₂ hprime hu₁ hu₂ hdet]
  simp

/-- The positive modular surrogate of a descending form remains congruent to
the actual natural subtraction even after multiplication by an arbitrary
increasing affine form.  The explicit no-underflow condition is essential. -/
theorem mixedDescendingAffineProduct_dvd_iff_positive_surrogate
    (B u v a y t d : ℕ) (hB : 0 < B) (hd : d ∣ B)
    (hunderflow : a * t ≤ y) :
    d ∣ (u * t + v) * (y - a * t) ↔
      d ∣ (u * t + v) * ((B - a % B) * t + y) := by
  let slope := B - a % B
  have hmodbound : a % B ≤ B := (Nat.mod_lt a hB).le
  have hsum : slope + a % B = B := Nat.sub_add_cancel hmodbound
  have hmod : Nat.ModEq d (a % B) a :=
    (Nat.mod_modEq a B).of_dvd hd
  have hsumcong : Nat.ModEq d (slope + a) 0 := by
    have hreplace : Nat.ModEq d (slope + a % B) (slope + a) :=
      Nat.ModEq.rfl.add hmod
    have hzero : Nat.ModEq d (slope + a % B) 0 := by
      rw [hsum]
      exact Nat.modEq_zero_iff_dvd.mpr hd
    exact hreplace.symm.trans hzero
  have hsurplus : Nat.ModEq d ((slope * t + y) + a * t) y := by
    calc
      (slope * t + y) + a * t = (slope + a) * t + y := by ring
      _ ≡ 0 * t + y [MOD d] :=
        (hsumcong.mul_right t).add_right y
      _ = y := by simp
  have heq : (y - a * t) + a * t = y :=
    Nat.sub_add_cancel hunderflow
  have hlinear : Nat.ModEq d (slope * t + y) (y - a * t) := by
    apply Nat.ModEq.add_right_cancel' (a * t)
    rw [heq]
    exact hsurplus
  have hproduct : Nat.ModEq d
      ((u * t + v) * (slope * t + y))
      ((u * t + v) * (y - a * t)) :=
    Nat.ModEq.rfl.mul hlinear
  exact (hproduct.dvd_iff (dvd_refl d)).symm

/-- Exact divisor multiplicity transport for the genuine product of an
arbitrary increasing affine form and an arbitrary nonsaturated decreasing
affine form. -/
theorem actualMixedAffineSelberg_multSum_eq_positive_surrogate
    (P : Finset ℕ) (N z u v a y d : ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z)
    (hunderflow : ∀ t < N, a * t ≤ y)
    (hd : d ∣ ∏ p ∈ P, p) :
    let B := ∏ p ∈ P, p
    let mixed := actualTwoFunctionSelbergSieve
      P (Finset.range N) (fun t => u * t + v)
        (fun t => y - a * t) z hprime hlarge hz
    let positive := actualAffineSelbergSieve
      P N z u v (B - a % B) y hprime hlarge hz
    BoundingSieve.multSum (s := mixed.toBoundingSieve) d =
      BoundingSieve.multSum (s := positive.toBoundingSieve) d := by
  let B := ∏ p ∈ P, p
  have hB : 0 < B := Finset.prod_pos fun p hp => (hprime p hp).pos
  change
    BoundingSieve.multSum
      (s := (actualTwoFunctionSelbergSieve P (Finset.range N)
        (fun t => u * t + v) (fun t => y - a * t) z
        hprime hlarge hz).toBoundingSieve) d =
      BoundingSieve.multSum
        (s := (actualAffineSelbergSieve P N z u v (B - a % B) y
          hprime hlarge hz).toBoundingSieve) d
  rw [actualTwoFunctionSelberg_multSum_eq_parameter_card,
    actualAffineSelberg_multSum_eq_parameter_card]
  have hsets :
      (Finset.range N).filter
        (fun t => d ∣ (u * t + v) * (y - a * t)) =
        (Finset.range N).filter
          (fun t => d ∣ affineSieveProduct u v (B - a % B) y t) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    apply and_congr_right
    intro ht
    simpa [affineSieveProduct] using
      mixedDescendingAffineProduct_dvd_iff_positive_surrogate
        B u v a y t d hB hd (hunderflow t ht)
  rw [hsets]

/-- The actual optimized divisor-remainder contract holds for every genuine
increasing/descending affine pair, including the nonzero intercept created
by a CRT-selected parameter progression. -/
theorem actualMixedAffineSelberg_divisor_remainder_contract
    (P : Finset ℕ) (N z u v a y : ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z)
    (hu : ∀ p ∈ P, ¬p ∣ u)
    (ha : ∀ p ∈ P, ¬p ∣ a)
    (hdet : ∀ p ∈ P,
      (u : ZMod p) * (y : ZMod p) ≠
        ((∏ q ∈ P, q) - a % (∏ q ∈ P, q) : ℕ) * (v : ZMod p))
    (hunderflow : ∀ t < N, a * t ≤ y) :
    ActualTwoFormDivisorRemainderContract
      (actualTwoFunctionSelbergSieve P (Finset.range N)
        (fun t => u * t + v) (fun t => y - a * t) z
          hprime hlarge hz) := by
  let B := ∏ p ∈ P, p
  let slope := B - a % B
  let mixed := actualTwoFunctionSelbergSieve P (Finset.range N)
    (fun t => u * t + v) (fun t => y - a * t) z hprime hlarge hz
  let positive := actualAffineSelbergSieve P N z u v slope y
    hprime hlarge hz
  have hB : 0 < B := Finset.prod_pos fun p hp => (hprime p hp).pos
  have hslope : ∀ p ∈ P, ¬p ∣ slope := by
    intro p hp
    exact mixedDescendingSurrogate_not_dvd_of_not_dvd
      B a p hB (Finset.dvd_prod_of_mem (fun q : ℕ => q) hp)
        (ha p hp)
  intro d hd
  have hmult := actualMixedAffineSelberg_multSum_eq_positive_surrogate
    P N z u v a y d hprime hlarge hz hunderflow hd
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
  apply actualAffineSelberg_rem_abs_le_of_dvd
    P N z u v slope y d hprime hlarge hz hu hslope
  · intro p hp
    exact hdet p hp
  · exact hd

/-- The complete optimized sifted bound for an arbitrary increasing affine
form and an actual nonsaturated descending affine form. -/
theorem actualMixedAffineSelberg_sifted_card_le_twoRootDenominator
    (P : Finset ℕ) (M N z u v a y : ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z)
    (hu : ∀ p ∈ P, ¬p ∣ u)
    (ha : ∀ p ∈ P, ¬p ∣ a)
    (hdet : ∀ p ∈ P,
      (u : ZMod p) * (y : ZMod p) ≠
        ((∏ q ∈ P, q) - a % (∏ q ∈ P, q) : ℕ) * (v : ZMod p))
    (hunderflow : ∀ t < N, a * t ≤ y)
    (hM : 2 ∣ M)
    (hPM : Nat.Coprime (∏ p ∈ P, p) M)
    (hprimes : ∀ p : ℕ, p.Prime →
      (p ∣ ∏ q ∈ P, q ↔ p ≤ z ∧ Nat.Coprime p M)) :
    (((Finset.range N).filter fun t =>
      Nat.Coprime (∏ p ∈ P, p)
        ((u * t + v) * (y - a * t))).card : ℝ) ≤
      (N : ℝ) / twoRootSelbergDenominator M z + (z : ℝ) ^ 4 := by
  simpa using actualTwoFunction_sifted_card_le_twoRootDenominator
    P (Finset.range N) (fun t => u * t + v) (fun t => y - a * t)
    M z hprime hlarge hz hM hPM hprimes
      (actualMixedAffineSelberg_divisor_remainder_contract
        P N z u v a y hprime hlarge hz hu ha hdet hunderflow)

/-- All actual simultaneous prime values of a general increasing and
decreasing affine pair, including nonzero progression intercepts. -/
def mixedAffinePrimeParameters (N u v a y : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun t =>
    (u * t + v).Prime ∧ (y - a * t).Prime

/-- The full general mixed affine prime family differs from its large-prime
subfamily by at most the two genuine injective small-prime exceptions. -/
theorem mixedAffinePrimeParameters_card_le_large_and_small_exceptions
    (N z u v a y : ℕ) (hu : 0 < u) (ha : 0 < a) :
    (mixedAffinePrimeParameters N u v a y).card ≤
      ((Finset.range N).filter fun t =>
        (u * t + v).Prime ∧ (y - a * t).Prime ∧
          z < u * t + v ∧ z < y - a * t).card +
            2 * Nat.primeCounting z := by
  let large : Finset ℕ := (Finset.range N).filter fun t =>
    (u * t + v).Prime ∧ (y - a * t).Prime ∧
      z < u * t + v ∧ z < y - a * t
  let exceptions := mixedAffineSmallPrimeExceptions N z u v a y
  have hsubset : mixedAffinePrimeParameters N u v a y ⊆
      large ∪ exceptions := by
    intro t ht
    obtain ⟨htN, hfirst, hsecond⟩ := Finset.mem_filter.mp ht
    by_cases hsmall : u * t + v ≤ z
    · apply Finset.mem_union_right
      apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      exact ⟨htN, Nat.mem_primesLE.mpr ⟨hsmall, hfirst⟩⟩
    by_cases hsmallDescending : y - a * t ≤ z
    · apply Finset.mem_union_right
      apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      exact ⟨htN, Nat.mem_primesLE.mpr
        ⟨hsmallDescending, hsecond⟩⟩
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      exact ⟨htN, hfirst, hsecond, by omega, by omega⟩
  have hcard := Finset.card_le_card hsubset
  have hunion := Finset.card_union_le large exceptions
  have hexceptions := mixedAffineSmallPrimeExceptions_card_le
    N z u v a y hu ha
  change exceptions.card ≤ 2 * Nat.primeCounting z at hexceptions
  change (mixedAffinePrimeParameters N u v a y).card ≤
    large.card + 2 * Nat.primeCounting z
  omega

/-- The unrestricted optimized prime-pair upper bound for every actual
increasing/descending affine pair.  This applies in particular after the
right-fiber progression substitution `t = r + W*k`. -/
theorem actualMixedAffineSelberg_all_prime_pair_card_le_twoRootDenominator
    (P : Finset ℕ) (M N z u v a y : ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z)
    (hu : ∀ p ∈ P, ¬p ∣ u)
    (ha : ∀ p ∈ P, ¬p ∣ a)
    (hdet : ∀ p ∈ P,
      (u : ZMod p) * (y : ZMod p) ≠
        ((∏ q ∈ P, q) - a % (∏ q ∈ P, q) : ℕ) * (v : ZMod p))
    (hunderflow : ∀ t < N, a * t ≤ y)
    (hM : 2 ∣ M)
    (hPM : Nat.Coprime (∏ p ∈ P, p) M)
    (hprimes : ∀ p : ℕ, p.Prime →
      (p ∣ ∏ q ∈ P, q ↔ p ≤ z ∧ Nat.Coprime p M))
    (hupositive : 0 < u) (hapositive : 0 < a) :
    ((mixedAffinePrimeParameters N u v a y).card : ℝ) ≤
      (N : ℝ) / twoRootSelbergDenominator M z + (z : ℝ) ^ 4 +
        ((2 * Nat.primeCounting z : ℕ) : ℝ) := by
  let s := actualTwoFunctionSelbergSieve P (Finset.range N)
    (fun t => u * t + v) (fun t => y - a * t) z hprime hlarge hz
  have hpairs := large_prime_pair_card_le_parameter_sifted
    s (Finset.range N) (fun t => u * t + v) (fun t => y - a * t) z
      (fun p hp hdiv => ((hprimes p hp).mp hdiv).1)
  change
    (((Finset.range N).filter fun t =>
      (u * t + v).Prime ∧ (y - a * t).Prime ∧
        z < u * t + v ∧ z < y - a * t).card : ℝ) ≤
      (((Finset.range N).filter fun t =>
        Nat.Coprime (∏ p ∈ P, p)
          ((u * t + v) * (y - a * t))).card : ℝ) at hpairs
  have hlargePairs := hpairs.trans
    (actualMixedAffineSelberg_sifted_card_le_twoRootDenominator
      P M N z u v a y hprime hlarge hz hu ha hdet
        hunderflow hM hPM hprimes)
  have hdecomp := mixedAffinePrimeParameters_card_le_large_and_small_exceptions
    N z u v a y hupositive hapositive
  have hreal :
      ((mixedAffinePrimeParameters N u v a y).card : ℝ) ≤
        (((Finset.range N).filter fun t =>
          (u * t + v).Prime ∧ (y - a * t).Prime ∧
            z < u * t + v ∧ z < y - a * t).card : ℝ) +
              ((2 * Nat.primeCounting z : ℕ) : ℝ) := by
    exact_mod_cast hdecomp
  exact hreal.trans (add_le_add hlargePairs (le_refl _))

/-- All actual simultaneous prime values on a positive/negative affine fiber;
the natural subtraction is not replaced by an increasing surrogate. -/
def mixedDescendingPrimeParameters (N a y : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun t => t.Prime ∧ (y - a * t).Prime

/-- On the genuine descending fiber every missing small-prime case is one of
the two injectively controlled exception families. -/
theorem mixedDescendingPrimeParameters_card_le_large_and_small_exceptions
    (N z a y : ℕ) (ha : 0 < a) :
    (mixedDescendingPrimeParameters N a y).card ≤
      ((Finset.range N).filter fun t =>
        t.Prime ∧ (y - a * t).Prime ∧ z < t ∧ z < y - a * t).card +
          2 * Nat.primeCounting z := by
  let large : Finset ℕ := (Finset.range N).filter fun t =>
    t.Prime ∧ (y - a * t).Prime ∧ z < t ∧ z < y - a * t
  let exceptions := mixedAffineSmallPrimeExceptions N z 1 0 a y
  have hsubset : mixedDescendingPrimeParameters N a y ⊆
      large ∪ exceptions := by
    intro t ht
    obtain ⟨htN, htprime, hdescending⟩ := Finset.mem_filter.mp ht
    by_cases hsmall : t ≤ z
    · apply Finset.mem_union_right
      apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      simpa using
        (show t ∈ Finset.range N ∧ t ∈ Nat.primesLE z from
          ⟨htN, Nat.mem_primesLE.mpr ⟨hsmall, htprime⟩⟩)
    by_cases hsmallDescending : y - a * t ≤ z
    · apply Finset.mem_union_right
      apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      exact ⟨htN, Nat.mem_primesLE.mpr
        ⟨hsmallDescending, hdescending⟩⟩
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      exact ⟨htN, htprime, hdescending, by omega, by omega⟩
  have hcard := Finset.card_le_card hsubset
  have hunion := Finset.card_union_le large exceptions
  have hexceptions := mixedAffineSmallPrimeExceptions_card_le
    N z 1 0 a y (by omega) ha
  change exceptions.card ≤ 2 * Nat.primeCounting z at hexceptions
  change (mixedDescendingPrimeParameters N a y).card ≤
    large.card + 2 * Nat.primeCounting z
  omega

/-- The full mixed-sign two-prime Selberg bound includes every actual prime
pair, with its optimized fourth-power remainder and the necessary `2 π(z)`
exceptions.  No positive-slope replacement or omitted small-prime branch is
used. -/
theorem actualMixedSelberg_all_prime_pair_card_le_twoRootDenominator
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
      (p ∣ ∏ q ∈ P, q ↔ p ≤ z ∧ Nat.Coprime p M))
    (hapositive : 0 < a) :
    ((mixedDescendingPrimeParameters N a y).card : ℝ) ≤
      (N : ℝ) / twoRootSelbergDenominator M z + (z : ℝ) ^ 4 +
        ((2 * Nat.primeCounting z : ℕ) : ℝ) := by
  have hdecomp := mixedDescendingPrimeParameters_card_le_large_and_small_exceptions
    N z a y hapositive
  have hreal :
      ((mixedDescendingPrimeParameters N a y).card : ℝ) ≤
        (((Finset.range N).filter fun t =>
          t.Prime ∧ (y - a * t).Prime ∧
            z < t ∧ z < y - a * t).card : ℝ) +
              ((2 * Nat.primeCounting z : ℕ) : ℝ) := by
    exact_mod_cast hdecomp
  exact hreal.trans (add_le_add
    (actualMixedSelberg_large_prime_pair_card_le_twoRootDenominator
      P M N z a y hprime hlarge hz ha hy hunderflow hM hPM hprimes)
        (le_refl _))

/-- Actual manuscript edges whose left vertex admits the exceptional external
prime-three representation. The filter retains the exact original edge set. -/
noncomputable def exceptionalThreeManuscriptEdges
    (S : Finset ℕ) (E : Finset TripleEdge) : Finset TripleEdge := by
  classical
  exact E.filter fun e =>
    ∃ d ∈ (∏ s ∈ S, s).divisors, e.1 = 3 * d

/-- The actual left coordinates of all exceptional-prime edges lie in the
image of the support-divisor set, with no representation uniqueness assumed. -/
theorem exceptionalThreeManuscriptEdges_left_image_card_le
    (S : Finset ℕ) (E : Finset TripleEdge) :
    ((exceptionalThreeManuscriptEdges S E).image
      (fun e : TripleEdge => e.1)).card ≤
        (∏ s ∈ S, s).divisors.card := by
  classical
  let W := ∏ s ∈ S, s
  have hsubset :
      (exceptionalThreeManuscriptEdges S E).image
        (fun e : TripleEdge => e.1) ⊆
          W.divisors.image (fun d => 3 * d) := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨_, d, hd, heq⟩ := Finset.mem_filter.mp he
    exact Finset.mem_image.mpr ⟨d, hd, heq.symm⟩
  exact (Finset.card_le_card hsubset).trans Finset.card_image_le

/-- Every fixed actual right vertex has at most `τ(W)` exceptional-prime-three
edges: the edge's left coordinate already determines its label. -/
theorem exceptionalThreeManuscriptEdges_right_fiber_card_le
    {S : Finset ℕ} {b : ℕ → ℕ} {n : ℕ} {τ ell : ℝ}
    (E : Finset TripleEdge) (y : ℕ)
    (hactual : ∀ e ∈ E, manuscriptEdge S b n τ ell e) :
    ((exceptionalThreeManuscriptEdges S E).filter
      fun e => e.2.1 = y).card ≤
        (∏ s ∈ S, s).divisors.card := by
  classical
  let exceptional := exceptionalThreeManuscriptEdges S E
  have hreal : ∀ e ∈ exceptional, manuscriptEdge S b n τ ell e := by
    intro e he
    exact hactual e (Finset.mem_filter.mp he).1
  have hinjective := manuscriptEdge_left_injective_on_right_fiber
    exceptional y hreal
  let fiber := exceptional.filter fun e => e.2.1 = y
  calc
    fiber.card = (fiber.image fun e : TripleEdge => e.1).card :=
      (Finset.card_image_iff.mpr hinjective).symm
    _ ≤ (exceptional.image fun e : TripleEdge => e.1).card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨e, (Finset.mem_filter.mp he).1, rfl⟩
    _ ≤ (∏ s ∈ S, s).divisors.card :=
      exceptionalThreeManuscriptEdges_left_image_card_le S E

/-- Every fixed actual prime label likewise has at most `τ(W)`
exceptional-prime-three edges; the left vertex determines the right vertex. -/
theorem exceptionalThreeManuscriptEdges_label_fiber_card_le
    {S : Finset ℕ} {b : ℕ → ℕ} {n : ℕ} {τ ell : ℝ}
    (E : Finset TripleEdge) (z : ℕ)
    (hactual : ∀ e ∈ E, manuscriptEdge S b n τ ell e) :
    ((exceptionalThreeManuscriptEdges S E).filter
      fun e => e.2.2 = z).card ≤
        (∏ s ∈ S, s).divisors.card := by
  classical
  let exceptional := exceptionalThreeManuscriptEdges S E
  have hreal : ∀ e ∈ exceptional, manuscriptEdge S b n τ ell e := by
    intro e he
    exact hactual e (Finset.mem_filter.mp he).1
  have hinjective := manuscriptEdge_left_injective_on_label_fiber
    exceptional z hreal
  let fiber := exceptional.filter fun e => e.2.2 = z
  calc
    fiber.card = (fiber.image fun e : TripleEdge => e.1).card :=
      (Finset.card_image_iff.mpr hinjective).symm
    _ ≤ (exceptional.image fun e : TripleEdge => e.1).card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨e, (Finset.mem_filter.mp he).1, rfl⟩
    _ ≤ (∏ s ∈ S, s).divisors.card :=
      exceptionalThreeManuscriptEdges_left_image_card_le S E

end Erdos689

#print axioms Erdos689.twoAffineFieldRoots_card_eq_one_of_det_eq
#print axioms Erdos689.affineSieveRootResidues_card_eq_one_of_prime_det_collision
#print axioms Erdos689.affineSieveRemainder_abs_le_one_of_prime_det_collision
#print axioms Erdos689.exceptionalThree_affine_root_card
#print axioms Erdos689.exceptionalThree_actual_singular_factor
#print axioms Erdos689.exceptionalThree_generic_prime_product_root_card
#print axioms Erdos689.mixedDescendingAffineProduct_dvd_iff_positive_surrogate
#print axioms Erdos689.actualMixedAffineSelberg_multSum_eq_positive_surrogate
#print axioms Erdos689.actualMixedAffineSelberg_divisor_remainder_contract
#print axioms Erdos689.actualMixedAffineSelberg_sifted_card_le_twoRootDenominator
#print axioms Erdos689.mixedAffinePrimeParameters_card_le_large_and_small_exceptions
#print axioms Erdos689.actualMixedAffineSelberg_all_prime_pair_card_le_twoRootDenominator
#print axioms Erdos689.mixedDescendingPrimeParameters_card_le_large_and_small_exceptions
#print axioms Erdos689.actualMixedSelberg_all_prime_pair_card_le_twoRootDenominator
#print axioms Erdos689.exceptionalThreeManuscriptEdges_left_image_card_le
#print axioms Erdos689.exceptionalThreeManuscriptEdges_right_fiber_card_le
#print axioms Erdos689.exceptionalThreeManuscriptEdges_label_fiber_card_le
