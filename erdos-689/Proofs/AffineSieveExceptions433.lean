import Mathlib

/-!
# Exact small-prime and inadmissible-class exceptions for two affine forms

A two-form Selberg sieve counts parameters for which neither affine value has
a forbidden small prime factor.  Genuine prime pairs can nevertheless fail
this condition when an affine value equals a sieved small prime or equals a
prime dividing the fixed modulus.  These isolated exceptions must be counted,
not silently discarded as locally inadmissible.

Each nonconstant natural affine form is injective on its parameter interval.
Consequently its small-prime exceptions number at most `π(z)`, and its
modulus-prime exceptions number at most `M.primeFactors.card`.  The two forms
together contribute at most twice each quantity.
-/

namespace Erdos689

/-- Parameters whose affine value belongs to a specified finite target set. -/
def affineValueParameters (N u v : ℕ) (values : Finset ℕ) : Finset ℕ :=
  (Finset.range N).filter fun t => u * t + v ∈ values

/-- A positive-slope natural affine form is injective. -/
theorem affine_nat_injective {u : ℕ} (v : ℕ) (hu : 0 < u) :
    Function.Injective (fun t : ℕ => u * t + v) := by
  intro t t' hvalues
  exact Nat.mul_left_cancel hu (Nat.add_right_cancel hvalues)

/-- An injective affine form hits at most one parameter per prescribed value. -/
theorem affineValueParameters_card_le (N u v : ℕ) (values : Finset ℕ)
    (hu : 0 < u) :
    (affineValueParameters N u v values).card ≤ values.card := by
  let parameters := affineValueParameters N u v values
  let f : ℕ → ℕ := fun t => u * t + v
  have hinjective : Set.InjOn f (↑parameters : Set ℕ) :=
    (affine_nat_injective v hu).injOn
  calc
    parameters.card = (parameters.image f).card :=
      (Finset.card_image_iff.mpr hinjective).symm
    _ ≤ values.card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp ht).2

/-- Parameters where at least one affine value is a prime at most `z`. -/
def twoAffineSmallPrimeExceptions
    (N z u₁ v₁ u₂ v₂ : ℕ) : Finset ℕ :=
  affineValueParameters N u₁ v₁ (Nat.primesLE z) ∪
    affineValueParameters N u₂ v₂ (Nat.primesLE z)

/-- The exact exceptional-prime contribution is bounded by `2 π(z)`. -/
theorem twoAffineSmallPrimeExceptions_card_le
    (N z u₁ v₁ u₂ v₂ : ℕ)
    (hu₁ : 0 < u₁) (hu₂ : 0 < u₂) :
    (twoAffineSmallPrimeExceptions N z u₁ v₁ u₂ v₂).card ≤
      2 * Nat.primeCounting z := by
  unfold twoAffineSmallPrimeExceptions
  calc
    (affineValueParameters N u₁ v₁ (Nat.primesLE z) ∪
        affineValueParameters N u₂ v₂ (Nat.primesLE z)).card ≤
      (affineValueParameters N u₁ v₁ (Nat.primesLE z)).card +
        (affineValueParameters N u₂ v₂ (Nat.primesLE z)).card :=
          Finset.card_union_le _ _
    _ ≤ (Nat.primesLE z).card + (Nat.primesLE z).card :=
      Nat.add_le_add
        (affineValueParameters_card_le N u₁ v₁ (Nat.primesLE z) hu₁)
        (affineValueParameters_card_le N u₂ v₂ (Nat.primesLE z) hu₂)
    _ = 2 * Nat.primeCounting z := by
      rw [Nat.primesLE_card_eq_primeCounting]
      omega

/-- Parameters where an affine value equals a prime divisor of the modulus. -/
def twoAffineModulusPrimeExceptions
    (N M u₁ v₁ u₂ v₂ : ℕ) : Finset ℕ :=
  affineValueParameters N u₁ v₁ M.primeFactors ∪
    affineValueParameters N u₂ v₂ M.primeFactors

/-- Inadmissible residue classes contribute at most `2 ω(M)` genuine pairs. -/
theorem twoAffineModulusPrimeExceptions_card_le
    (N M u₁ v₁ u₂ v₂ : ℕ)
    (hu₁ : 0 < u₁) (hu₂ : 0 < u₂) :
    (twoAffineModulusPrimeExceptions N M u₁ v₁ u₂ v₂).card ≤
      2 * M.primeFactors.card := by
  unfold twoAffineModulusPrimeExceptions
  calc
    (affineValueParameters N u₁ v₁ M.primeFactors ∪
        affineValueParameters N u₂ v₂ M.primeFactors).card ≤
      (affineValueParameters N u₁ v₁ M.primeFactors).card +
        (affineValueParameters N u₂ v₂ M.primeFactors).card :=
          Finset.card_union_le _ _
    _ ≤ M.primeFactors.card + M.primeFactors.card :=
      Nat.add_le_add
        (affineValueParameters_card_le N u₁ v₁ M.primeFactors hu₁)
        (affineValueParameters_card_le N u₂ v₂ M.primeFactors hu₂)
    _ = 2 * M.primeFactors.card := by omega

/-- All genuine simultaneous prime values of the two affine forms. -/
def twoAffinePrimeParameters (N u₁ v₁ u₂ v₂ : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun t =>
    (u₁ * t + v₁).Prime ∧ (u₂ * t + v₂).Prime

/-- Prime pairs remaining after removing both necessary exceptional families. -/
def twoAffineGoodPrimeParameters (N z M u₁ v₁ u₂ v₂ : ℕ) : Finset ℕ :=
  (twoAffinePrimeParameters N u₁ v₁ u₂ v₂).filter fun t =>
    z < u₁ * t + v₁ ∧ z < u₂ * t + v₂ ∧
      ¬ u₁ * t + v₁ ∣ M ∧ ¬ u₂ * t + v₂ ∣ M

/-- Every genuine pair is either sieve-eligible or one of the exact exceptions. -/
theorem twoAffinePrimeParameters_subset_good_union_exceptions
    (N z M u₁ v₁ u₂ v₂ : ℕ) (hM : M ≠ 0) :
    twoAffinePrimeParameters N u₁ v₁ u₂ v₂ ⊆
      (twoAffineGoodPrimeParameters N z M u₁ v₁ u₂ v₂ ∪
        twoAffineSmallPrimeExceptions N z u₁ v₁ u₂ v₂) ∪
          twoAffineModulusPrimeExceptions N M u₁ v₁ u₂ v₂ := by
  intro t ht
  obtain ⟨hinterval, hprime₁, hprime₂⟩ := Finset.mem_filter.mp ht
  by_cases hsmall₁ : u₁ * t + v₁ ≤ z
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    exact ⟨hinterval, Nat.mem_primesLE.mpr ⟨hsmall₁, hprime₁⟩⟩
  by_cases hsmall₂ : u₂ * t + v₂ ≤ z
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    exact ⟨hinterval, Nat.mem_primesLE.mpr ⟨hsmall₂, hprime₂⟩⟩
  by_cases hmodulus₁ : u₁ * t + v₁ ∣ M
  · apply Finset.mem_union_right
    apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    exact ⟨hinterval,
      Nat.mem_primeFactors.mpr ⟨hprime₁, hmodulus₁, hM⟩⟩
  by_cases hmodulus₂ : u₂ * t + v₂ ∣ M
  · apply Finset.mem_union_right
    apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    exact ⟨hinterval,
      Nat.mem_primeFactors.mpr ⟨hprime₂, hmodulus₂, hM⟩⟩
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    exact ⟨ht, by omega, by omega, hmodulus₁, hmodulus₂⟩

/-- Removing bad local classes never loses more than the two exact exception terms. -/
theorem twoAffinePrimeParameters_card_le_good_and_exceptions
    (N z M u₁ v₁ u₂ v₂ : ℕ)
    (hM : M ≠ 0) (hu₁ : 0 < u₁) (hu₂ : 0 < u₂) :
    (twoAffinePrimeParameters N u₁ v₁ u₂ v₂).card ≤
      (twoAffineGoodPrimeParameters N z M u₁ v₁ u₂ v₂).card +
        2 * Nat.primeCounting z + 2 * M.primeFactors.card := by
  have hsubset := twoAffinePrimeParameters_subset_good_union_exceptions
    N z M u₁ v₁ u₂ v₂ hM
  have hsmall := twoAffineSmallPrimeExceptions_card_le
    N z u₁ v₁ u₂ v₂ hu₁ hu₂
  have hmodulus := twoAffineModulusPrimeExceptions_card_le
    N M u₁ v₁ u₂ v₂ hu₁ hu₂
  have hfirst := Finset.card_union_le
    (twoAffineGoodPrimeParameters N z M u₁ v₁ u₂ v₂)
    (twoAffineSmallPrimeExceptions N z u₁ v₁ u₂ v₂)
  have hsecond := Finset.card_union_le
    (twoAffineGoodPrimeParameters N z M u₁ v₁ u₂ v₂ ∪
      twoAffineSmallPrimeExceptions N z u₁ v₁ u₂ v₂)
    (twoAffineModulusPrimeExceptions N M u₁ v₁ u₂ v₂)
  have hcard := Finset.card_le_card hsubset
  omega

/-- Parameters where a decreasing affine value belongs to a finite target set. -/
def affineDescendingValueParameters
    (N u v : ℕ) (values : Finset ℕ) : Finset ℕ :=
  (Finset.range N).filter fun t => v - u * t ∈ values

/-- Natural subtraction is injective on the positive part of a nonconstant form. -/
theorem affine_sub_injective_of_positive
    {u v t t' : ℕ} (hu : 0 < u)
    (_ht : 0 < v - u * t) (ht' : 0 < v - u * t')
    (hvalues : v - u * t = v - u * t') :
    t = t' := by
  have hproducts : u * t = u * t' := by omega
  exact Nat.mul_left_cancel hu hproducts

/-- Decreasing affine forms also hit each positive prescribed value at most once. -/
theorem affineDescendingValueParameters_card_le
    (N u v : ℕ) (values : Finset ℕ)
    (hu : 0 < u) (hvalues : ∀ p ∈ values, 0 < p) :
    (affineDescendingValueParameters N u v values).card ≤ values.card := by
  let parameters := affineDescendingValueParameters N u v values
  let f : ℕ → ℕ := fun t => v - u * t
  have hinjective : Set.InjOn f (↑parameters : Set ℕ) := by
    intro t ht t' ht' heq
    have hmember :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).2
    have hmember' :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp ht')).2
    exact affine_sub_injective_of_positive hu
      (hvalues _ hmember) (hvalues _ hmember') heq
  calc
    parameters.card = (parameters.image f).card :=
      (Finset.card_image_iff.mpr hinjective).symm
    _ ≤ values.card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp ht).2

/-- Small-prime exceptions for one increasing and one decreasing affine form. -/
def mixedAffineSmallPrimeExceptions
    (N z u₁ v₁ u₂ v₂ : ℕ) : Finset ℕ :=
  affineValueParameters N u₁ v₁ (Nat.primesLE z) ∪
    affineDescendingValueParameters N u₂ v₂ (Nat.primesLE z)

/-- The same exact `2 π(z)` bound remains valid for the negative-slope fiber. -/
theorem mixedAffineSmallPrimeExceptions_card_le
    (N z u₁ v₁ u₂ v₂ : ℕ)
    (hu₁ : 0 < u₁) (hu₂ : 0 < u₂) :
    (mixedAffineSmallPrimeExceptions N z u₁ v₁ u₂ v₂).card ≤
      2 * Nat.primeCounting z := by
  have hpositive : ∀ p ∈ Nat.primesLE z, 0 < p := by
    intro p hp
    exact (Nat.mem_primesLE.mp hp).2.pos
  unfold mixedAffineSmallPrimeExceptions
  have hunion := Finset.card_union_le
    (affineValueParameters N u₁ v₁ (Nat.primesLE z))
    (affineDescendingValueParameters N u₂ v₂ (Nat.primesLE z))
  have hfirst := affineValueParameters_card_le N u₁ v₁
    (Nat.primesLE z) hu₁
  have hsecond := affineDescendingValueParameters_card_le N u₂ v₂
    (Nat.primesLE z) hu₂ hpositive
  rw [Nat.primesLE_card_eq_primeCounting] at hfirst hsecond
  omega

/-- Modulus-prime exceptions for one increasing and one decreasing affine form. -/
def mixedAffineModulusPrimeExceptions
    (N M u₁ v₁ u₂ v₂ : ℕ) : Finset ℕ :=
  affineValueParameters N u₁ v₁ M.primeFactors ∪
    affineDescendingValueParameters N u₂ v₂ M.primeFactors

/-- The exact `2 ω(M)` bound also covers the genuine negative-slope fiber. -/
theorem mixedAffineModulusPrimeExceptions_card_le
    (N M u₁ v₁ u₂ v₂ : ℕ)
    (hu₁ : 0 < u₁) (hu₂ : 0 < u₂) :
    (mixedAffineModulusPrimeExceptions N M u₁ v₁ u₂ v₂).card ≤
      2 * M.primeFactors.card := by
  have hpositive : ∀ p ∈ M.primeFactors, 0 < p := by
    intro p hp
    exact (Nat.mem_primeFactors.mp hp).1.pos
  unfold mixedAffineModulusPrimeExceptions
  have hunion := Finset.card_union_le
    (affineValueParameters N u₁ v₁ M.primeFactors)
    (affineDescendingValueParameters N u₂ v₂ M.primeFactors)
  have hfirst := affineValueParameters_card_le N u₁ v₁
    M.primeFactors hu₁
  have hsecond := affineDescendingValueParameters_card_le N u₂ v₂
    M.primeFactors hu₂ hpositive
  omega

end Erdos689

#print axioms Erdos689.affine_nat_injective
#print axioms Erdos689.affineValueParameters_card_le
#print axioms Erdos689.twoAffineSmallPrimeExceptions_card_le
#print axioms Erdos689.twoAffineModulusPrimeExceptions_card_le
#print axioms Erdos689.twoAffinePrimeParameters_subset_good_union_exceptions
#print axioms Erdos689.twoAffinePrimeParameters_card_le_good_and_exceptions
#print axioms Erdos689.affine_sub_injective_of_positive
#print axioms Erdos689.affineDescendingValueParameters_card_le
#print axioms Erdos689.mixedAffineSmallPrimeExceptions_card_le
#print axioms Erdos689.mixedAffineModulusPrimeExceptions_card_le
