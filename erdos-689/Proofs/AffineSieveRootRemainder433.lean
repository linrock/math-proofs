import Mathlib
import SelbergExplicitConstant433

/-!
# Actual affine residue roots and their exact finite sieve remainder

The generic Selberg remainder estimate needs a theorem about genuine parameter
counts, rather than an abstract hypothesis on an unspecified remainder.  This
module counts any set of actual residue roots exactly and proves that its
interval discrepancy is bounded by the number of roots, hence by the modulus.
No prime-pattern theorem or degree estimate is assumed.
-/

open Finset

namespace Erdos689

/-- Parameters in the initial interval whose residue belongs to an actual
finite root set. -/
def residueRootParameters (N h : ℕ) (roots : Finset ℕ) : Finset ℕ :=
  (Finset.range N).filter fun t => t % h ∈ roots

/-- An individual residue occurs exactly `N / h` times, with one additional
occurrence precisely when it belongs to the incomplete last block. -/
theorem parameter_residue_fiber_card (N h r : ℕ)
    (hh : 0 < h) (hr : r < h) :
    ((Finset.range N).filter fun t => t % h = r).card =
      N / h + if r < N % h then 1 else 0 := by
  have hcount := Nat.count_modEq_card N hh r
  rw [Nat.count_eq_card_filter_range] at hcount
  have hmod : r % h = r := Nat.mod_eq_of_lt hr
  simpa [Nat.ModEq, hmod] using hcount

/-- Exact root count, including the incomplete block.  The root set may be
arbitrary; it is not presumed to arise independently at different primes. -/
theorem residueRootParameters_card_eq (N h : ℕ) (roots : Finset ℕ)
    (hh : 0 < h) (hroots : roots ⊆ Finset.range h) :
    (residueRootParameters N h roots).card =
      roots.card * (N / h) +
        (roots.filter fun r => r < N % h).card := by
  classical
  unfold residueRootParameters
  rw [← Finset.sum_card_fiberwise_eq_card_filter (Finset.range N) roots
    (fun t => t % h)]
  calc
    (∑ r ∈ roots, ((Finset.range N).filter fun t => t % h = r).card) =
        ∑ r ∈ roots, (N / h + if r < N % h then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro r hr
          exact parameter_residue_fiber_card N h r hh
            (Finset.mem_range.mp (hroots hr))
    _ = roots.card * (N / h) +
          (roots.filter fun r => r < N % h).card := by
            simp [Finset.sum_add_distrib]

/-- The actual real Selberg discrepancy of a finite residue-root set. -/
noncomputable def residueRootRemainder
    (N h : ℕ) (roots : Finset ℕ) : ℝ :=
  ((residueRootParameters N h roots).card : ℝ) -
    (N : ℝ) * (roots.card : ℝ) / (h : ℝ)

/-- Every residue-root remainder is bounded by the exact number of root
classes; no spurious factor of `3 ^ ω(h)` or modulus is introduced. -/
theorem residueRootRemainder_abs_le_card (N h : ℕ) (roots : Finset ℕ)
    (hh : 0 < h) (hroots : roots ⊆ Finset.range h) :
    |residueRootRemainder N h roots| ≤ (roots.card : ℝ) := by
  have hhreal : (0 : ℝ) < h := by exact_mod_cast hh
  have hrem : N % h < h := Nat.mod_lt N hh
  have hremreal : ((N % h : ℕ) : ℝ) ≤ h := by
    exact_mod_cast hrem.le
  have hroot_nonneg : (0 : ℝ) ≤ (roots.card : ℝ) := by positivity
  have hlast :
      ((roots.filter fun r => r < N % h).card : ℝ) ≤ roots.card := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have hlast_nonneg :
      (0 : ℝ) ≤ ((roots.filter fun r => r < N % h).card : ℝ) := by
    positivity
  have hfraction_nonneg :
      0 ≤ (((N % h : ℕ) : ℝ) * (roots.card : ℝ) / (h : ℝ)) := by
    positivity
  have hfraction_le :
      (((N % h : ℕ) : ℝ) * (roots.card : ℝ) / (h : ℝ)) ≤ roots.card := by
    apply (div_le_iff₀ hhreal).mpr
    nlinarith
  have hdecomp : (N : ℝ) =
      (h : ℝ) * ((N / h : ℕ) : ℝ) + ((N % h : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod N h).symm
  have hcard := residueRootParameters_card_eq N h roots hh hroots
  unfold residueRootRemainder
  rw [hcard]
  push_cast
  rw [hdecomp]
  have hnonzero : (h : ℝ) ≠ 0 := ne_of_gt hhreal
  have hidentity :
      (roots.card : ℝ) * ((N / h : ℕ) : ℝ) +
          ((roots.filter fun r => r < N % h).card : ℝ) -
        ((h : ℝ) * ((N / h : ℕ) : ℝ) + ((N % h : ℕ) : ℝ)) *
          (roots.card : ℝ) / (h : ℝ) =
      ((roots.filter fun r => r < N % h).card : ℝ) -
        ((N % h : ℕ) : ℝ) * (roots.card : ℝ) / (h : ℝ) := by
    field_simp
    ring
  rw [hidentity]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- In particular, the true root-count remainder always has the exact
modulus bound required by the already verified two-variable Selberg error. -/
theorem residueRootRemainder_abs_le_modulus (N h : ℕ) (roots : Finset ℕ)
    (hh : 0 < h) (hroots : roots ⊆ Finset.range h) :
    |residueRootRemainder N h roots| ≤ (h : ℝ) := by
  calc
    |residueRootRemainder N h roots| ≤ (roots.card : ℝ) :=
      residueRootRemainder_abs_le_card N h roots hh hroots
    _ ≤ h := by
      exact_mod_cast (by simpa using Finset.card_le_card hroots)

/-- The concrete product of two natural affine forms.  The parameter can
already include any fixed translation of the original interval. -/
def affineSieveProduct (u₁ v₁ u₂ v₂ t : ℕ) : ℕ :=
  (u₁ * t + v₁) * (u₂ * t + v₂)

/-- Genuine roots of the actual affine product modulo `h`, represented by
their canonical natural residues. -/
def affineSieveRootResidues (h u₁ v₁ u₂ v₂ : ℕ) : Finset ℕ :=
  (Finset.range h).filter fun r => h ∣ affineSieveProduct u₁ v₁ u₂ v₂ r

/-- The affine product respects reduction of the parameter modulo `h`. -/
theorem affineSieveProduct_mod_parameter
    (h u₁ v₁ u₂ v₂ t : ℕ) :
    affineSieveProduct u₁ v₁ u₂ v₂ (t % h) % h =
      affineSieveProduct u₁ v₁ u₂ v₂ t % h := by
  simp [affineSieveProduct, Nat.add_mod, Nat.mul_mod]

/-- Membership in the actual residue-root set is equivalent to divisibility
of the genuine affine product at the original parameter. -/
theorem affineSieveRootResidues_mem_mod_iff
    (h u₁ v₁ u₂ v₂ t : ℕ) (hh : 0 < h) :
    t % h ∈ affineSieveRootResidues h u₁ v₁ u₂ v₂ ↔
      h ∣ affineSieveProduct u₁ v₁ u₂ v₂ t := by
  simp only [affineSieveRootResidues, Finset.mem_filter, Finset.mem_range,
    Nat.mod_lt t hh, true_and, Nat.dvd_iff_mod_eq_zero]
  rw [affineSieveProduct_mod_parameter]

/-- Exact finite count of parameters on which the true affine product is
divisible by a given positive modulus. -/
theorem affineSieveProduct_dvd_parameter_card
    (N h u₁ v₁ u₂ v₂ : ℕ) (hh : 0 < h) :
    ((Finset.range N).filter
      fun t => h ∣ affineSieveProduct u₁ v₁ u₂ v₂ t).card =
        (affineSieveRootResidues h u₁ v₁ u₂ v₂).card * (N / h) +
          ((affineSieveRootResidues h u₁ v₁ u₂ v₂).filter
            fun r => r < N % h).card := by
  have hsets :
      (Finset.range N).filter
        (fun t => h ∣ affineSieveProduct u₁ v₁ u₂ v₂ t) =
      residueRootParameters N h (affineSieveRootResidues h u₁ v₁ u₂ v₂) := by
    ext t
    simp only [residueRootParameters, Finset.mem_filter]
    exact and_congr_right fun _ =>
      (affineSieveRootResidues_mem_mod_iff h u₁ v₁ u₂ v₂ t hh).symm
  rw [hsets]
  exact residueRootParameters_card_eq N h _ hh (Finset.filter_subset _ _)

/-- The actual Selberg remainder of a concrete affine-product divisor count;
its irrelevant zero-modulus value is defined as zero. -/
noncomputable def affineSieveRemainder
    (N h u₁ v₁ u₂ v₂ : ℕ) : ℝ :=
  if h = 0 then 0 else
    residueRootRemainder N h (affineSieveRootResidues h u₁ v₁ u₂ v₂)

/-- At every positive modulus, the defined remainder is exactly the actual
affine divisibility count minus its true root-density main term. -/
theorem affineSieveRemainder_eq_actual_discrepancy
    (N h u₁ v₁ u₂ v₂ : ℕ) (hh : 0 < h) :
    affineSieveRemainder N h u₁ v₁ u₂ v₂ =
      (((Finset.range N).filter
        fun t => h ∣ affineSieveProduct u₁ v₁ u₂ v₂ t).card : ℝ) -
        (N : ℝ) *
          ((affineSieveRootResidues h u₁ v₁ u₂ v₂).card : ℝ) / (h : ℝ) := by
  unfold affineSieveRemainder
  rw [if_neg (Nat.ne_of_gt hh)]
  unfold residueRootRemainder
  have hsets :
      residueRootParameters N h (affineSieveRootResidues h u₁ v₁ u₂ v₂) =
        (Finset.range N).filter
          (fun t => h ∣ affineSieveProduct u₁ v₁ u₂ v₂ t) := by
    ext t
    simp only [residueRootParameters, Finset.mem_filter]
    exact and_congr_right fun _ =>
      affineSieveRootResidues_mem_mod_iff h u₁ v₁ u₂ v₂ t hh
  rw [hsets]

/-- The complete actual affine-root remainder has the modulus bound required
by the existing optimized two-variable Selberg estimate. -/
theorem affineSieveRemainder_abs_le_modulus
    (N h u₁ v₁ u₂ v₂ : ℕ) :
    |affineSieveRemainder N h u₁ v₁ u₂ v₂| ≤ (h : ℝ) := by
  by_cases hh : h = 0
  · simp [affineSieveRemainder, hh]
  · unfold affineSieveRemainder
    rw [if_neg hh]
    exact residueRootRemainder_abs_le_modulus N h _ (Nat.pos_of_ne_zero hh)
      (Finset.filter_subset _ _)

/-- The previously abstract fourth-power error bound now holds for the
genuine two-affine-form divisor remainder at every actual LCM modulus. -/
theorem affineSieve_two_variable_remainder_le_fourth_power
    (N z u₁ v₁ u₂ v₂ : ℕ) (weights : ℕ → ℝ)
    (hweights : ∀ d : ℕ, |weights d| ≤ 1) :
    (∑ d ∈ Finset.Icc 1 z,
      ∑ e ∈ Finset.Icc 1 z,
        |weights d * weights e *
          affineSieveRemainder N (Nat.lcm d e) u₁ v₁ u₂ v₂|) ≤
      (z : ℝ) ^ 4 := by
  exact selberg_two_variable_remainder_le_fourth_power z weights
    (fun h => affineSieveRemainder N h u₁ v₁ u₂ v₂) hweights
      (fun h => affineSieveRemainder_abs_le_modulus N h u₁ v₁ u₂ v₂)

/-- A nonconstant affine form over a field has exactly its expected root. -/
theorem affine_field_zero_iff {K : Type*} [Field K]
    (u v x : K) (hu : u ≠ 0) :
    u * x + v = 0 ↔ x = -v / u := by
  constructor
  · intro hx
    apply (eq_div_iff hu).mpr
    calc
      x * u = u * x := mul_comm _ _
      _ = -v := eq_neg_of_add_eq_zero_left hx
  · intro hx
    rw [hx]
    field_simp
    ring

/-- The actual zero classes of the two affine forms over a finite field. -/
noncomputable def twoAffineFieldRoots
    (K : Type*) [Field K] [Fintype K]
    (u₁ v₁ u₂ v₂ : K) : Finset K := by
  classical
  exact Finset.univ.filter fun x =>
    (u₁ * x + v₁) * (u₂ * x + v₂) = 0

/-- Membership in the actual finite-field affine root set. -/
theorem mem_twoAffineFieldRoots_iff
    {K : Type*} [Field K] [Fintype K]
    (u₁ v₁ u₂ v₂ x : K) :
    x ∈ twoAffineFieldRoots K u₁ v₁ u₂ v₂ ↔
      (u₁ * x + v₁) * (u₂ * x + v₂) = 0 := by
  classical
  simp [twoAffineFieldRoots]

/-- If the slopes and determinant are nonzero, the genuine affine product
has exactly two distinct residue roots, not merely at most two. -/
theorem twoAffineFieldRoots_card_eq_two
    {K : Type*} [Field K] [Fintype K]
    (u₁ v₁ u₂ v₂ : K)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0)
    (hdet : u₁ * v₂ ≠ u₂ * v₁) :
    (twoAffineFieldRoots K u₁ v₁ u₂ v₂).card = 2 := by
  classical
  have hdistinct : -v₁ / u₁ ≠ -v₂ / u₂ := by
    intro heq
    apply hdet
    field_simp [hu₁, hu₂] at heq
    have hcancel := neg_inj.mp heq
    calc
      u₁ * v₂ = v₁ * u₂ := hcancel.symm
      _ = u₂ * v₁ := mul_comm _ _
  have hroots :
      twoAffineFieldRoots K u₁ v₁ u₂ v₂ =
        {-v₁ / u₁, -v₂ / u₂} := by
    ext x
    simp only [twoAffineFieldRoots, Finset.mem_filter, Finset.mem_univ,
      true_and, mul_eq_zero, Finset.mem_insert, Finset.mem_singleton]
    rw [affine_field_zero_iff u₁ v₁ x hu₁,
      affine_field_zero_iff u₂ v₂ x hu₂]
  rw [hroots]
  exact Finset.card_pair hdistinct

/-- Canonical natural residues and finite-field elements encode exactly the
same genuine affine-product roots at a prime modulus. -/
theorem affineSieveRootResidues_card_eq_fieldRoots
    (p u₁ v₁ u₂ v₂ : ℕ) [Fact p.Prime] (_hp : p.Prime) :
    (affineSieveRootResidues p u₁ v₁ u₂ v₂).card =
      (twoAffineFieldRoots (ZMod p)
        (u₁ : ZMod p) (v₁ : ZMod p) (u₂ : ZMod p) (v₂ : ZMod p)).card := by
  classical
  apply Finset.card_bij
    (s := affineSieveRootResidues p u₁ v₁ u₂ v₂)
    (t := twoAffineFieldRoots (ZMod p)
      (u₁ : ZMod p) (v₁ : ZMod p) (u₂ : ZMod p) (v₂ : ZMod p))
    (fun r _ => (r : ZMod p))
  · intro r hr
    obtain ⟨hrange, hroot⟩ := Finset.mem_filter.mp hr
    apply (mem_twoAffineFieldRoots_iff
      (u₁ : ZMod p) (v₁ : ZMod p) (u₂ : ZMod p) (v₂ : ZMod p)
        (r : ZMod p)).mpr
    have hzero : (affineSieveProduct u₁ v₁ u₂ v₂ r : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ p).mpr hroot
    simpa [affineSieveProduct] using hzero
  · intro r hr s hs heq
    have hrlt : r < p :=
      Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    have hslt : s < p :=
      Finset.mem_range.mp (Finset.mem_filter.mp hs).1
    have hval := congrArg ZMod.val heq
    simpa [ZMod.val_natCast_of_lt hrlt,
      ZMod.val_natCast_of_lt hslt] using hval
  · intro x hx
    refine ⟨x.val, ?_, ZMod.natCast_zmod_val x⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr x.val_lt, ?_⟩
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    have hzero :=
      (mem_twoAffineFieldRoots_iff
        (u₁ : ZMod p) (v₁ : ZMod p) (u₂ : ZMod p) (v₂ : ZMod p) x).mp hx
    simpa [affineSieveProduct, ZMod.natCast_zmod_val] using hzero

/-- At every prime avoiding both slopes and the determinant, the actual
natural affine-product residue set has exactly two roots. -/
theorem affineSieveRootResidues_card_eq_two_of_prime
    (p u₁ v₁ u₂ v₂ : ℕ) [Fact p.Prime] (hp : p.Prime)
    (hu₁ : ¬p ∣ u₁) (hu₂ : ¬p ∣ u₂)
    (hdet : (u₁ : ZMod p) * (v₂ : ZMod p) ≠
      (u₂ : ZMod p) * (v₁ : ZMod p)) :
    (affineSieveRootResidues p u₁ v₁ u₂ v₂).card = 2 := by
  rw [affineSieveRootResidues_card_eq_fieldRoots p u₁ v₁ u₂ v₂ hp]
  apply twoAffineFieldRoots_card_eq_two
  · exact fun hzero => hu₁ ((ZMod.natCast_eq_zero_iff u₁ p).mp hzero)
  · exact fun hzero => hu₂ ((ZMod.natCast_eq_zero_iff u₂ p).mp hzero)
  · exact hdet

/-- For a genuinely nondegenerate prime modulus the actual affine divisor
count has discrepancy at most two, its exact local root count. -/
theorem affineSieveRemainder_abs_le_two_of_prime
    (N p u₁ v₁ u₂ v₂ : ℕ) [Fact p.Prime] (hp : p.Prime)
    (hu₁ : ¬p ∣ u₁) (hu₂ : ¬p ∣ u₂)
    (hdet : (u₁ : ZMod p) * (v₂ : ZMod p) ≠
      (u₂ : ZMod p) * (v₁ : ZMod p)) :
    |affineSieveRemainder N p u₁ v₁ u₂ v₂| ≤ (2 : ℝ) := by
  unfold affineSieveRemainder
  rw [if_neg (Nat.ne_of_gt hp.pos)]
  convert residueRootRemainder_abs_le_card N p
    (affineSieveRootResidues p u₁ v₁ u₂ v₂) hp.pos
      (Finset.filter_subset _ _) using 1
  exact_mod_cast (affineSieveRootResidues_card_eq_two_of_prime
    p u₁ v₁ u₂ v₂ hp hu₁ hu₂ hdet).symm

/-- The actual affine-product root count is multiplicative on coprime
moduli, by a genuine finite Chinese-remainder bijection. -/
theorem affineSieveRootResidues_card_mul_of_coprime
    (m n u₁ v₁ u₂ v₂ : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hcoprime : m.Coprime n) :
    (affineSieveRootResidues (m * n) u₁ v₁ u₂ v₂).card =
      (affineSieveRootResidues m u₁ v₁ u₂ v₂).card *
        (affineSieveRootResidues n u₁ v₁ u₂ v₂).card := by
  classical
  let A := affineSieveRootResidues (m * n) u₁ v₁ u₂ v₂
  let B := affineSieveRootResidues m u₁ v₁ u₂ v₂
  let C := affineSieveRootResidues n u₁ v₁ u₂ v₂
  have hcard : A.card = (B.product C).card := by
    apply Finset.card_bij (s := A) (t := B.product C)
      (fun r _ => (r % m, r % n))
    · intro r hr
      have hdiv := (Finset.mem_filter.mp hr).2
      have hmdiv : m ∣ affineSieveProduct u₁ v₁ u₂ v₂ r :=
        (dvd_mul_right m n).trans hdiv
      have hndiv : n ∣ affineSieveProduct u₁ v₁ u₂ v₂ r :=
        (dvd_mul_left n m).trans hdiv
      apply Finset.mem_product.mpr
      exact ⟨(affineSieveRootResidues_mem_mod_iff
        m u₁ v₁ u₂ v₂ r hm).mpr hmdiv,
        (affineSieveRootResidues_mem_mod_iff
          n u₁ v₁ u₂ v₂ r hn).mpr hndiv⟩
    · intro r hr s hs heq
      have hrlt : r < m * n :=
        Finset.mem_range.mp (Finset.mem_filter.mp hr).1
      have hslt : s < m * n :=
        Finset.mem_range.mp (Finset.mem_filter.mp hs).1
      have hfirst : r % m = s % m := congrArg Prod.fst heq
      have hsecond : r % n = s % n := congrArg Prod.snd heq
      have hmod : r ≡ s [MOD m * n] :=
        (Nat.modEq_and_modEq_iff_modEq_mul hcoprime).mp
          ⟨hfirst, hsecond⟩
      simpa [Nat.ModEq, Nat.mod_eq_of_lt hrlt,
        Nat.mod_eq_of_lt hslt] using hmod
    · rintro ⟨a, b⟩ hab
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      let r : ℕ := Nat.chineseRemainder hcoprime a b
      have hra : r % m = a := by
        have heq := (Nat.chineseRemainder hcoprime a b).property.1
        have halt : a < m :=
          Finset.mem_range.mp (Finset.mem_filter.mp ha).1
        simpa [r, Nat.ModEq, Nat.mod_eq_of_lt halt] using heq
      have hrb : r % n = b := by
        have heq := (Nat.chineseRemainder hcoprime a b).property.2
        have hblt : b < n :=
          Finset.mem_range.mp (Finset.mem_filter.mp hb).1
        simpa [r, Nat.ModEq, Nat.mod_eq_of_lt hblt] using heq
      have hmroot : r % m ∈ affineSieveRootResidues m u₁ v₁ u₂ v₂ := by
        simpa [hra] using ha
      have hnroot : r % n ∈ affineSieveRootResidues n u₁ v₁ u₂ v₂ := by
        simpa [hrb] using hb
      have hmdiv := (affineSieveRootResidues_mem_mod_iff
        m u₁ v₁ u₂ v₂ r hm).mp hmroot
      have hndiv := (affineSieveRootResidues_mem_mod_iff
        n u₁ v₁ u₂ v₂ r hn).mp hnroot
      refine ⟨r, ?_, Prod.ext hra hrb⟩
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_range.mpr
          (Nat.chineseRemainder_lt_mul hcoprime a b
            (Nat.ne_of_gt hm) (Nat.ne_of_gt hn))
      · exact hcoprime.mul_dvd_of_dvd_of_dvd hmdiv hndiv
  simpa [A, B, C] using hcard

/-- For every finite squarefree family of nondegenerate sieve primes, the
actual affine-product root count is exactly `2 ^ card(P)`.  This is the full
finite CRT root multiplicity used in the manuscript's Selberg remainder. -/
theorem affineSieveRootResidues_card_prime_product
    (P : Finset ℕ) (u₁ v₁ u₂ v₂ : ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hu₁ : ∀ p ∈ P, ¬p ∣ u₁)
    (hu₂ : ∀ p ∈ P, ¬p ∣ u₂)
    (hdet : ∀ p ∈ P,
      (u₁ : ZMod p) * (v₂ : ZMod p) ≠
        (u₂ : ZMod p) * (v₁ : ZMod p)) :
    (affineSieveRootResidues (∏ p ∈ P, p)
      u₁ v₁ u₂ v₂).card = 2 ^ P.card := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [affineSieveRootResidues]
  | @insert p T hnotmem ih =>
    have hp : p.Prime := hprime p (by simp)
    have hrest : ∀ q ∈ T, q.Prime := by
      intro q hq
      exact hprime q (by simp [hq])
    have hrest₁ : ∀ q ∈ T, ¬q ∣ u₁ := by
      intro q hq
      exact hu₁ q (by simp [hq])
    have hrest₂ : ∀ q ∈ T, ¬q ∣ u₂ := by
      intro q hq
      exact hu₂ q (by simp [hq])
    have hrest_det : ∀ q ∈ T,
        (u₁ : ZMod q) * (v₂ : ZMod q) ≠
          (u₂ : ZMod q) * (v₁ : ZMod q) := by
      intro q hq
      exact hdet q (by simp [hq])
    have hproduct_pos : 0 < ∏ q ∈ T, q :=
      Finset.prod_pos fun q hq => (hrest q hq).pos
    have hnotdiv : ¬p ∣ ∏ q ∈ T, q := by
      intro hdiv
      obtain ⟨q, hq, hpq⟩ :=
        (hp.prime.dvd_finsetProd_iff (fun q : ℕ => q)).mp hdiv
      have heq := (Nat.prime_dvd_prime_iff_eq hp (hrest q hq)).mp hpq
      exact hnotmem (heq ▸ hq)
    have hcoprime : p.Coprime (∏ q ∈ T, q) :=
      hp.coprime_iff_not_dvd.mpr hnotdiv
    have hlocal :
        (affineSieveRootResidues p u₁ v₁ u₂ v₂).card = 2 :=
      @affineSieveRootResidues_card_eq_two_of_prime
        p u₁ v₁ u₂ v₂ ⟨hp⟩ hp
          (hu₁ p (by simp)) (hu₂ p (by simp)) (hdet p (by simp))
    rw [Finset.prod_insert hnotmem,
      Finset.card_insert_of_notMem hnotmem,
      affineSieveRootResidues_card_mul_of_coprime
        p (∏ q ∈ T, q) u₁ v₁ u₂ v₂ hp.pos hproduct_pos hcoprime,
      hlocal, ih hrest hrest₁ hrest₂ hrest_det]
    simp [pow_succ, Nat.mul_comm]

/-- Exact squarefree CRT root formula for the *actual* affine product:
`ρ(h) = 2 ^ #(primeFactors h)`. -/
theorem affineSieveRootResidues_card_squarefree
    (h u₁ v₁ u₂ v₂ : ℕ) (hsquare : Squarefree h)
    (hu₁ : ∀ p ∈ h.primeFactors, ¬p ∣ u₁)
    (hu₂ : ∀ p ∈ h.primeFactors, ¬p ∣ u₂)
    (hdet : ∀ p ∈ h.primeFactors,
      (u₁ : ZMod p) * (v₂ : ZMod p) ≠
        (u₂ : ZMod p) * (v₁ : ZMod p)) :
    (affineSieveRootResidues h u₁ v₁ u₂ v₂).card =
      2 ^ h.primeFactors.card := by
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hsquare]
  exact affineSieveRootResidues_card_prime_product h.primeFactors
    u₁ v₁ u₂ v₂
      (fun p hp => Nat.prime_of_mem_primeFactors hp) hu₁ hu₂ hdet

/-- The exact squarefree CRT root count bounds the genuine affine Selberg
remainder, recovering `|r_h| ≤ 2 ^ ω(h)` with no abstract root hypothesis. -/
theorem affineSieveRemainder_abs_le_two_pow_primeFactors
    (N h u₁ v₁ u₂ v₂ : ℕ) (hsquare : Squarefree h)
    (hu₁ : ∀ p ∈ h.primeFactors, ¬p ∣ u₁)
    (hu₂ : ∀ p ∈ h.primeFactors, ¬p ∣ u₂)
    (hdet : ∀ p ∈ h.primeFactors,
      (u₁ : ZMod p) * (v₂ : ZMod p) ≠
        (u₂ : ZMod p) * (v₁ : ZMod p)) :
    |affineSieveRemainder N h u₁ v₁ u₂ v₂| ≤
      (2 ^ h.primeFactors.card : ℕ) := by
  have hh : 0 < h := Nat.pos_of_ne_zero hsquare.ne_zero
  unfold affineSieveRemainder
  rw [if_neg (Nat.ne_of_gt hh)]
  convert residueRootRemainder_abs_le_card N h
    (affineSieveRootResidues h u₁ v₁ u₂ v₂) hh
      (Finset.filter_subset _ _) using 1
  exact_mod_cast (affineSieveRootResidues_card_squarefree
    h u₁ v₁ u₂ v₂ hsquare hu₁ hu₂ hdet).symm

/-- Once an actual bounding sieve uses the two-root local density, each of
its genuine squarefree Selberg terms is exactly the previously audited
`2 / (p - 2)` product. -/
theorem affineSelbergTerms_eq_twoRootWeight
    (s : SelbergSieve) (M d : ℕ)
    (hM : 2 ∣ M)
    (hd : d ∣ s.prodPrimes)
    (hdM : Nat.Coprime d M)
    (hnu : s.nu = twoRootDivisorMajorant) :
    SelbergSieve.selbergTerms s.toBoundingSieve d =
      twoRootSelbergWeight d := by
  have hsquare : Squarefree d :=
    Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree
  rw [SelbergSieve.selbergTerms_apply]
  change s.nu d *
    (∏ p ∈ d.primeFactors, 1 / (1 - s.nu p)) = _
  rw [hnu]
  exact (twoRootSelbergWeight_eq_geometric_majorant hM hsquare hdM).symm

/-- If the actual sieve contains exactly all primes up to its cutoff that are
coprime to the excluded modulus, its optimized abstract Selberg denominator
is *identically* the already audited concrete squarefree two-root denominator.
This identifies the full denominator, not just its individual local factors. -/
theorem affineSelbergBoundingSum_eq_twoRootDenominator
    (s : SelbergSieve) (M z : ℕ)
    (hM : 2 ∣ M)
    (hPM : Nat.Coprime s.prodPrimes M)
    (hnu : s.nu = twoRootDivisorMajorant)
    (hlevel : s.level = (z : ℝ) ^ 2)
    (hprimes : ∀ p : ℕ, p.Prime →
      (p ∣ s.prodPrimes ↔ p ≤ z ∧ Nat.Coprime p M)) :
    s.selbergBoundingSum = twoRootSelbergDenominator M z := by
  classical
  have hPzero : s.prodPrimes ≠ 0 := s.prodPrimes_squarefree.ne_zero
  have hcut (d : ℕ) :
      (d : ℝ) ^ 2 ≤ s.level ↔ d ≤ z := by
    rw [hlevel]
    constructor
    · intro hbound
      exact_mod_cast (sq_le_sq₀ (by positivity) (by positivity)).mp hbound
    · intro hbound
      apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
      exact_mod_cast hbound
  have hsets :
      s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ^ 2 ≤ s.level) =
        (Finset.Icc 1 z).filter
          (fun d : ℕ => Squarefree d ∧ Nat.Coprime d M) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc, hcut]
    constructor
    · rintro ⟨⟨hd, _⟩, hdz⟩
      have hdpos : 0 < d :=
        Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hPzero)
      exact ⟨⟨hdpos, hdz⟩,
        Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree,
        Nat.Coprime.coprime_dvd_left hd hPM⟩
    · rintro ⟨⟨hdpos, hdz⟩, hdsquare, hdM⟩
      have hddiv : d ∣ s.prodPrimes := by
        rw [← Nat.prod_primeFactors_of_squarefree hdsquare]
        apply (Nat.prod_primeFactors_dvd_iff hPzero).mpr
        intro p hp
        have hpprime := Nat.prime_of_mem_primeFactors hp
        have hpd := Nat.dvd_of_mem_primeFactors hp
        apply (Nat.mem_primeFactors_of_ne_zero hPzero).mpr
        refine ⟨hpprime, (hprimes p hpprime).mpr ?_⟩
        exact ⟨(Nat.le_of_dvd hdpos hpd).trans hdz,
          Nat.Coprime.coprime_dvd_left hpd hdM⟩
      exact ⟨⟨hddiv, hPzero⟩, hdz⟩
  unfold SelbergSieve.selbergBoundingSum twoRootSelbergDenominator
  rw [← Finset.sum_filter, hsets]
  apply Finset.sum_congr rfl
  intro d hd
  have hdM := (Finset.mem_filter.mp hd).2.2
  have hdin : d ∈ s.prodPrimes.divisors.filter
      (fun d : ℕ => (d : ℝ) ^ 2 ≤ s.level) := hsets.symm ▸ hd
  have hdP := (Nat.mem_divisors.mp (Finset.mem_filter.mp hdin).1).1
  exact affineSelbergTerms_eq_twoRootWeight s M d hM hdP hdM hnu

/-- The concrete Selberg sieve for an actual affine-product parameter
interval.  Its weights preserve collisions by counting every product fiber;
its multiplicative local density is exactly the genuine two-root density. -/
noncomputable def actualAffineSelbergSieve
    (P : Finset ℕ) (N z u₁ v₁ u₂ v₂ : ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z) : SelbergSieve where
  support := (Finset.range N).image (affineSieveProduct u₁ v₁ u₂ v₂)
  prodPrimes := ∏ p ∈ P, p
  prodPrimes_squarefree := Sieve.prodDistinctPrimes_squarefree P hprime
  weights := fun x =>
    (((Finset.range N).filter
      fun t => affineSieveProduct u₁ v₁ u₂ v₂ t = x).card : ℝ)
  weights_nonneg := by
    intro x
    positivity
  totalMass := (N : ℝ)
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

/-- The concrete product-fiber weights recover the exact actual count of
parameters on which a modulus divides the two affine forms' product. -/
theorem actualAffineSelberg_multSum_eq_parameter_card
    (P : Finset ℕ) (N z u₁ v₁ u₂ v₂ d : ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z) :
    BoundingSieve.multSum
      (s := (actualAffineSelbergSieve P N z u₁ v₁ u₂ v₂
        hprime hlarge hz).toBoundingSieve) d =
      (((Finset.range N).filter
        fun t => d ∣ affineSieveProduct u₁ v₁ u₂ v₂ t).card : ℝ) := by
  classical
  let F := affineSieveProduct u₁ v₁ u₂ v₂
  change
    (∑ x ∈ (Finset.range N).image F,
      if d ∣ x then
        (((Finset.range N).filter fun t => F t = x).card : ℝ)
      else 0) =
        (((Finset.range N).filter fun t => d ∣ F t).card : ℝ)
  rw [← Finset.sum_filter]
  calc
    (∑ x ∈ ((Finset.range N).image F).filter (fun x => d ∣ x),
      (((Finset.range N).filter fun t => F t = x).card : ℝ)) =
        ((∑ x ∈ ((Finset.range N).image F).filter (fun x => d ∣ x),
          ((Finset.range N).filter fun t => F t = x).card : ℕ) : ℝ) := by
            norm_cast
    _ = (((Finset.range N).filter fun t => d ∣ F t).card : ℝ) := by
      rw [Finset.sum_card_fiberwise_eq_card_filter]
      have hsets :
          (Finset.range N).filter
            (fun t => F t ∈ ((Finset.range N).image F).filter
              (fun x => d ∣ x)) =
            (Finset.range N).filter (fun t => d ∣ F t) := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
        aesop
      rw [hsets]

/-- On an actual nondegenerate squarefree modulus, the sieve's completely
multiplicative density equals the genuine affine-root proportion. -/
theorem twoRootDivisorMajorant_eq_affineRoot_density
    (d u₁ v₁ u₂ v₂ : ℕ) (hsquare : Squarefree d)
    (hu₁ : ∀ p ∈ d.primeFactors, ¬p ∣ u₁)
    (hu₂ : ∀ p ∈ d.primeFactors, ¬p ∣ u₂)
    (hdet : ∀ p ∈ d.primeFactors,
      (u₁ : ZMod p) * (v₂ : ZMod p) ≠
        (u₂ : ZMod p) * (v₁ : ZMod p)) :
    twoRootDivisorMajorant d =
      ((affineSieveRootResidues d u₁ v₁ u₂ v₂).card : ℝ) / (d : ℝ) := by
  have hproduct :
      twoRootDivisorMajorant d =
        ∏ p ∈ d.primeFactors, twoRootDivisorMajorant p := by
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hsquare]
    exact
      twoRootDivisorMajorant_completelyMultiplicative.isMultiplicative.map_prod_of_subset_primeFactors
        _ _ (Finset.Subset.refl _)
  have hroots := affineSieveRootResidues_card_squarefree
    d u₁ v₁ u₂ v₂ hsquare hu₁ hu₂ hdet
  calc
    twoRootDivisorMajorant d =
        ∏ p ∈ d.primeFactors, twoRootDivisorMajorant p := hproduct
    _ = ∏ p ∈ d.primeFactors, (2 : ℝ) / p := by
      apply Finset.prod_congr rfl
      intro p hp
      exact twoRootDivisorMajorant_prime (Nat.prime_of_mem_primeFactors hp)
    _ = (2 : ℝ) ^ d.primeFactors.card / (d : ℝ) := by
      rw [Finset.prod_div_distrib]
      simp only [Finset.prod_const]
      congr 1
      have hcast := congrArg (fun n : ℕ => (n : ℝ))
        (Nat.prod_primeFactors_of_squarefree hsquare)
      push_cast at hcast
      exact hcast
    _ = ((affineSieveRootResidues d u₁ v₁ u₂ v₂).card : ℝ) /
          (d : ℝ) := by
      congr 1
      exact_mod_cast hroots.symm

/-- The abstract `BoundingSieve.rem` of the genuinely instantiated affine
Selberg sieve is *exactly* the previously computed actual root discrepancy.
All squarefree divisor and coefficient hypotheses are transported from the
actual finite sieve-prime family. -/
theorem actualAffineSelberg_rem_eq_affineSieveRemainder
    (P : Finset ℕ) (N z u₁ v₁ u₂ v₂ d : ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z)
    (hu₁ : ∀ p ∈ P, ¬p ∣ u₁)
    (hu₂ : ∀ p ∈ P, ¬p ∣ u₂)
    (hdet : ∀ p ∈ P,
      (u₁ : ZMod p) * (v₂ : ZMod p) ≠
        (u₂ : ZMod p) * (v₁ : ZMod p))
    (hd : d ∣ ∏ p ∈ P, p) :
    BoundingSieve.rem
      (s := (actualAffineSelbergSieve P N z u₁ v₁ u₂ v₂
        hprime hlarge hz).toBoundingSieve) d =
      affineSieveRemainder N d u₁ v₁ u₂ v₂ := by
  have hPpositive : 0 < ∏ p ∈ P, p :=
    Finset.prod_pos fun p hp => (hprime p hp).pos
  have hdpositive : 0 < d := Nat.pos_of_dvd_of_pos hd hPpositive
  have hdsquare : Squarefree d :=
    Squarefree.squarefree_of_dvd hd
      (Sieve.prodDistinctPrimes_squarefree P hprime)
  have hsubset : d.primeFactors ⊆ P := by
    have h := Nat.primeFactors_mono hd (Nat.ne_of_gt hPpositive)
    rwa [Nat.primeFactors_prod hprime] at h
  have hdensity := twoRootDivisorMajorant_eq_affineRoot_density
    d u₁ v₁ u₂ v₂ hdsquare
      (fun p hp => hu₁ p (hsubset hp))
      (fun p hp => hu₂ p (hsubset hp))
      (fun p hp => hdet p (hsubset hp))
  unfold BoundingSieve.rem
  rw [actualAffineSelberg_multSum_eq_parameter_card
    P N z u₁ v₁ u₂ v₂ d hprime hlarge hz]
  rw [affineSieveRemainder_eq_actual_discrepancy
    N d u₁ v₁ u₂ v₂ hdpositive]
  change
    (((Finset.range N).filter
      fun t => d ∣ affineSieveProduct u₁ v₁ u₂ v₂ t).card : ℝ) -
      twoRootDivisorMajorant d * (N : ℝ) = _
  rw [hdensity]
  ring

/-- The genuine abstract Selberg remainder of the instantiated affine sieve
satisfies the exact modulus bound on every divisor actually used by the sieve. -/
theorem actualAffineSelberg_rem_abs_le_of_dvd
    (P : Finset ℕ) (N z u₁ v₁ u₂ v₂ d : ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z)
    (hu₁ : ∀ p ∈ P, ¬p ∣ u₁)
    (hu₂ : ∀ p ∈ P, ¬p ∣ u₂)
    (hdet : ∀ p ∈ P,
      (u₁ : ZMod p) * (v₂ : ZMod p) ≠
        (u₂ : ZMod p) * (v₁ : ZMod p))
    (hd : d ∣ ∏ p ∈ P, p) :
    |BoundingSieve.rem
      (s := (actualAffineSelbergSieve P N z u₁ v₁ u₂ v₂
        hprime hlarge hz).toBoundingSieve) d| ≤ (d : ℝ) := by
  rw [actualAffineSelberg_rem_eq_affineSieveRemainder
    P N z u₁ v₁ u₂ v₂ d hprime hlarge hz hu₁ hu₂ hdet hd]
  exact affineSieveRemainder_abs_le_modulus N d u₁ v₁ u₂ v₂

/-- Full fourth-power bound for the *actual optimized Selberg weights and
actual abstract sieve remainders*.  Unsupported divisor pairs vanish because
the optimized weights vanish; supported pairs have the genuine CRT bound. -/
theorem actualAffineSelberg_two_variable_remainder_le_fourth_power
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
    (∑ d ∈ Finset.Icc 1 z,
      ∑ e ∈ Finset.Icc 1 z,
        |s.selbergWeights d * s.selbergWeights e *
          BoundingSieve.rem (s := s.toBoundingSieve) (Nat.lcm d e)|) ≤
      (z : ℝ) ^ 4 := by
  classical
  let s := actualAffineSelbergSieve P N z u₁ v₁ u₂ v₂
    hprime hlarge hz
  change
    (∑ d ∈ Finset.Icc 1 z,
      ∑ e ∈ Finset.Icc 1 z,
        |s.selbergWeights d * s.selbergWeights e *
          BoundingSieve.rem (s := s.toBoundingSieve) (Nat.lcm d e)|) ≤
      (z : ℝ) ^ 4
  let remainder : ℕ → ℝ := fun h =>
    if h ∣ s.prodPrimes then BoundingSieve.rem (s := s.toBoundingSieve) h
    else 0
  have hbounded : ∀ h : ℕ, |remainder h| ≤ (h : ℝ) := by
    intro h
    unfold remainder
    split_ifs with hd
    · exact actualAffineSelberg_rem_abs_le_of_dvd
        P N z u₁ v₁ u₂ v₂ h hprime hlarge hz hu₁ hu₂ hdet hd
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
    (∑ d ∈ Finset.Icc 1 z,
      ∑ e ∈ Finset.Icc 1 z,
        |s.selbergWeights d * s.selbergWeights e *
          BoundingSieve.rem (s := s.toBoundingSieve) (Nat.lcm d e)|) =
        ∑ d ∈ Finset.Icc 1 z,
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

#print axioms Erdos689.parameter_residue_fiber_card
#print axioms Erdos689.residueRootParameters_card_eq
#print axioms Erdos689.residueRootRemainder_abs_le_card
#print axioms Erdos689.residueRootRemainder_abs_le_modulus
#print axioms Erdos689.affineSieveProduct_mod_parameter
#print axioms Erdos689.affineSieveRootResidues_mem_mod_iff
#print axioms Erdos689.affineSieveProduct_dvd_parameter_card
#print axioms Erdos689.affineSieveRemainder_eq_actual_discrepancy
#print axioms Erdos689.affineSieveRemainder_abs_le_modulus
#print axioms Erdos689.affineSieve_two_variable_remainder_le_fourth_power
#print axioms Erdos689.affine_field_zero_iff
#print axioms Erdos689.mem_twoAffineFieldRoots_iff
#print axioms Erdos689.twoAffineFieldRoots_card_eq_two
#print axioms Erdos689.affineSieveRootResidues_card_eq_fieldRoots
#print axioms Erdos689.affineSieveRootResidues_card_eq_two_of_prime
#print axioms Erdos689.affineSieveRemainder_abs_le_two_of_prime
#print axioms Erdos689.affineSieveRootResidues_card_mul_of_coprime
#print axioms Erdos689.affineSieveRootResidues_card_prime_product
#print axioms Erdos689.affineSieveRootResidues_card_squarefree
#print axioms Erdos689.affineSieveRemainder_abs_le_two_pow_primeFactors
#print axioms Erdos689.affineSelbergTerms_eq_twoRootWeight
#print axioms Erdos689.affineSelbergBoundingSum_eq_twoRootDenominator
#print axioms Erdos689.actualAffineSelberg_multSum_eq_parameter_card
#print axioms Erdos689.twoRootDivisorMajorant_eq_affineRoot_density
#print axioms Erdos689.actualAffineSelberg_rem_eq_affineSieveRemainder
#print axioms Erdos689.actualAffineSelberg_rem_abs_le_of_dvd
#print axioms Erdos689.actualAffineSelberg_two_variable_remainder_le_fourth_power

end Erdos689
