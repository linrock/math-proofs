module

public import TypedCoreMatchingBridge1139

@[expose] public section


/-!
# Exact scale-adaptive Euler-factor identities for Erdős #1139

The adaptive alternative to fixed-support hypergraph matching changes its
low semiprime support with each reciprocal prime-label scale.  Its key
algebraic gain is exact: if the supported prime types are all at most the
current scale `T`, the auxiliary local sieves combine to precisely the full
Euler product at `T`.

The high-support family's two branches are proved exactly as well, including
its genuine product ratio and type eligibility.  No asymptotic prime-pattern
estimate, probability hypothesis, or solution of #1139 is asserted.
-/

open Finset Filter
open scoped ArithmeticFunction.Omega Topology

namespace Erdos1139

/-- Exact finite local Euler product on a genuine selected prime support. -/
noncomputable def adaptivePrimeEulerProduct (S : Finset ℕ) : ℝ :=
  ∏ p ∈ S, (1 - (p : ℝ)⁻¹)

/-- Exact local factor in the scale-dependent admissible-pattern model. -/
noncomputable def adaptivePatternEulerFactor (S : Finset ℕ) (T : ℕ) : ℝ :=
  adaptivePrimeEulerProduct S *
    adaptivePrimeEulerProduct ((Nat.primesLE T) \ S)

/-- The support and its complementary primes through the reciprocal scale
partition their actual union without collisions. -/
theorem adaptivePatternEulerFactor_eq_union
    (S : Finset ℕ) (T : ℕ) :
    adaptivePatternEulerFactor S T =
      adaptivePrimeEulerProduct (S ∪ Nat.primesLE T) := by
  unfold adaptivePatternEulerFactor adaptivePrimeEulerProduct
  rw [← Finset.prod_union Finset.disjoint_sdiff]
  rw [Finset.union_sdiff_self_eq_union]

/-- Scale-adaptive low support: include exactly those low prime types that
are eligible at both the current scale and the fixed family cutoff. -/
def adaptiveLowPrimeSupport (T w : ℕ) : Finset ℕ :=
  Nat.primesLE (min T w)

/-- Fixed complementary high support, retaining its genuine strict lower
endpoint rather than silently including the cutoff prime. -/
def adaptiveHighPrimeSupport (z w : ℕ) : Finset ℕ :=
  (Nat.primesLE z) \ (Nat.primesLE w)

/-- A low semiprime type is available precisely on scales at least that
type; this scale-dependent eligibility is the source of the improved loads. -/
theorem mem_adaptiveLowPrimeSupport
    {T w s : ℕ} :
    s ∈ adaptiveLowPrimeSupport T w ↔
      s.Prime ∧ s ≤ T ∧ s ≤ w := by
  unfold adaptiveLowPrimeSupport
  rw [Nat.mem_primesLE]
  constructor
  · rintro ⟨bounded, prime⟩
    exact ⟨prime, bounded.trans (min_le_left T w),
      bounded.trans (min_le_right T w)⟩
  · rintro ⟨prime, scale, cutoff⟩
    exact ⟨le_min scale cutoff, prime⟩

/-- High-family membership retains both genuine prime cutoffs. -/
theorem mem_adaptiveHighPrimeSupport
    {z w s : ℕ} :
    s ∈ adaptiveHighPrimeSupport z w ↔
      s.Prime ∧ w < s ∧ s ≤ z := by
  unfold adaptiveHighPrimeSupport
  simp only [Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨bounded, prime⟩, not_low⟩
    refine ⟨prime, ?_, bounded⟩
    apply Nat.lt_of_not_ge
    intro low
    exact not_low ⟨low, prime⟩
  · rintro ⟨prime, large, bounded⟩
    exact ⟨⟨bounded, prime⟩,
      fun low => (Nat.not_le_of_gt large) low.1⟩

/-- KEY exact adaptive cancellation: at EVERY reciprocal scale, the
scale-adaptive low family has local factor `V_T`, not the worse fixed-family
factor `V_w` on short scales. -/
theorem adaptiveLowPatternEulerFactor_eq_scale_product
    (T w : ℕ) :
    adaptivePatternEulerFactor (adaptiveLowPrimeSupport T w) T =
      adaptivePrimeEulerProduct (Nat.primesLE T) := by
  rw [adaptivePatternEulerFactor_eq_union]
  congr 1
  apply Finset.union_eq_right.mpr
  exact Nat.primesLE_mono (min_le_left T w)

/-- On scales below the family split, the high support is disjoint from
the current low prime range. -/
theorem adaptiveHighPrimeSupport_disjoint_low_scale
    {T z w : ℕ} (small_scale : T ≤ w) :
    Disjoint (adaptiveHighPrimeSupport z w) (Nat.primesLE T) := by
  apply Finset.disjoint_left.mpr
  intro p high low
  have large := (mem_adaptiveHighPrimeSupport.mp high).2.1
  have bounded := Nat.le_of_mem_primesLE low
  omega

/-- Exact short-scale high-family factor: its fixed high-prime Euler product
multiplies the complete scale-`T` product. -/
theorem adaptiveHighPatternEulerFactor_of_small_scale
    {T z w : ℕ} (small_scale : T ≤ w) :
    adaptivePatternEulerFactor (adaptiveHighPrimeSupport z w) T =
      adaptivePrimeEulerProduct (adaptiveHighPrimeSupport z w) *
        adaptivePrimeEulerProduct (Nat.primesLE T) := by
  unfold adaptivePatternEulerFactor
  congr 1
  apply congrArg adaptivePrimeEulerProduct
  apply Finset.sdiff_eq_self_of_disjoint
  exact (adaptiveHighPrimeSupport_disjoint_low_scale small_scale).symm

/-- Exact long-scale high-family factor: as soon as the scale reaches the
split and remains below the endpoint, the combined local support is all
primes through `z`. -/
theorem adaptiveHighPatternEulerFactor_of_large_scale
    {T z w : ℕ} (large_scale : w ≤ T) (bounded_scale : T ≤ z) :
    adaptivePatternEulerFactor (adaptiveHighPrimeSupport z w) T =
      adaptivePrimeEulerProduct (Nat.primesLE z) := by
  rw [adaptivePatternEulerFactor_eq_union]
  congr 1
  ext p
  simp only [Finset.mem_union, adaptiveHighPrimeSupport,
    Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro (⟨⟨bounded, prime⟩, _⟩ | ⟨bounded, prime⟩)
    · exact ⟨bounded, prime⟩
    · exact ⟨bounded.trans bounded_scale, prime⟩
  · rintro ⟨bounded, prime⟩
    by_cases low : p ≤ w
    · exact Or.inr ⟨low.trans large_scale, prime⟩
    · exact Or.inl ⟨⟨bounded, prime⟩,
        fun small => low small.1⟩

/-- Genuine finite Euler products on prime supports are strictly positive;
division by the lower-cutoff product is consequently legitimate. -/
theorem adaptivePrimeEulerProduct_pos
    (S : Finset ℕ) (primes : ∀ p ∈ S, p.Prime) :
    0 < adaptivePrimeEulerProduct S := by
  unfold adaptivePrimeEulerProduct
  apply Finset.prod_pos
  intro p selected
  have prime := primes p selected
  have one_lt : (1 : ℝ) < p := by exact_mod_cast prime.one_lt
  have reciprocal_lt : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ (by positivity)).mpr one_lt
  linarith

/-- The high-support Euler product is exactly `V_z / V_w`, with both factors
strictly positive and no heuristic or asymptotic cancellation. -/
theorem adaptiveHighPrimeEulerProduct_eq_ratio
    {z w : ℕ} (cutoff : w ≤ z) :
    adaptivePrimeEulerProduct (adaptiveHighPrimeSupport z w) =
      adaptivePrimeEulerProduct (Nat.primesLE z) /
        adaptivePrimeEulerProduct (Nat.primesLE w) := by
  have combined := adaptiveHighPatternEulerFactor_of_large_scale
    (T := w) (z := z) (w := w) le_rfl cutoff
  have split := adaptiveHighPatternEulerFactor_of_small_scale
    (T := w) (z := z) (w := w) le_rfl
  rw [split] at combined
  have positive := adaptivePrimeEulerProduct_pos
    (Nat.primesLE w) (fun p selected => Nat.prime_of_mem_primesLE selected)
  exact (eq_div_iff positive.ne').mpr combined

/-- Short-scale high-family factors have the exact advertised ratio form
`(V_z / V_w) * V_T`. -/
theorem adaptiveHighPatternEulerFactor_small_scale_ratio
    {T z w : ℕ} (small_scale : T ≤ w) (cutoff : w ≤ z) :
    adaptivePatternEulerFactor (adaptiveHighPrimeSupport z w) T =
      (adaptivePrimeEulerProduct (Nat.primesLE z) /
        adaptivePrimeEulerProduct (Nat.primesLE w)) *
        adaptivePrimeEulerProduct (Nat.primesLE T) := by
  rw [adaptiveHighPatternEulerFactor_of_small_scale small_scale,
    adaptiveHighPrimeEulerProduct_eq_ratio cutoff]


end Erdos1139
