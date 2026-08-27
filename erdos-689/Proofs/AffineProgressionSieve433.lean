import SelbergOptimizedBridge433
import AffineSieveDegreeSelectors433
import AffineDegreeFibers433
import ExceptionalPrimeThree433

/-!
# Exact selector-preserving arithmetic-progression sieve transport

The existing optimized two-form sieves count parameters in initial intervals.
Actual manuscript vertex fibers first impose CRT residue selectors modulo the
fixed switched support.  This module transports each genuine residue class to
its exact parameter interval, preserving its `1 / W` spacing and the true
affine nondegeneracy conditions.  No prime-pattern estimate or original
covering statement is assumed.
-/

open Finset
open Filter
open scoped BigOperators

namespace Erdos689

/-- The exact number of integers below `N` in the residue class `r mod W`. -/
def affineProgressionLength (N W r : ℕ) : ℕ :=
  N / W + if r < N % W then 1 else 0

/-- The endpoint of a genuine residue progression is exact, including the
possibly incomplete final block. -/
theorem affine_progression_mem_iff
    (N W r k : ℕ) (hW : 0 < W) (hr : r < W) :
    r + W * k < N ↔ k < affineProgressionLength N W r := by
  have hN := Nat.mod_add_div N W
  by_cases hlast : r < N % W
  · simp only [affineProgressionLength, hlast, ↓reduceIte]
    constructor
    · intro hk
      have hdiv : (r + W * k) / W ≤ N / W :=
        Nat.div_le_div_right (Nat.le_of_lt hk)
      have hquot : (r + W * k) / W = k := by
        rw [Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt hr, Nat.zero_add]
      omega
    · intro hk
      have hkle : k ≤ N / W := by omega
      have hmul : W * k ≤ W * (N / W) :=
        Nat.mul_le_mul_left W hkle
      omega
  · simp only [affineProgressionLength, hlast, ↓reduceIte, Nat.add_zero]
    constructor
    · intro hk
      have hdiv : (r + W * k) / W ≤ N / W :=
        Nat.div_le_div_right (Nat.le_of_lt hk)
      have hquot : (r + W * k) / W = k := by
        rw [Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt hr, Nat.zero_add]
      have hkle : k ≤ N / W := by omega
      rcases Nat.lt_or_eq_of_le hkle with hlt | heq
      · exact hlt
      · subst k
        omega
    · intro hk
      have hsucc : k + 1 ≤ N / W := by omega
      have hmul : W * (k + 1) ≤ W * (N / W) :=
        Nat.mul_le_mul_left W hsucc
      have hdistribute : W * (k + 1) = W * k + W := by ring
      omega

/-- Genuine integers in a selected residue class are exactly the image of
their initial progression interval, with no ceiling or endpoint relaxation. -/
theorem affine_residue_parameters_eq_progression_image
    (N W r : ℕ) (hW : 0 < W) (hr : r < W) :
    ((Finset.range N).filter fun t => t % W = r) =
      (Finset.range (affineProgressionLength N W r)).image
        (fun k => r + W * k) := by
  classical
  ext t
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨ht, hresidue⟩
    have hrepresentation : r + W * (t / W) = t := by
      simpa [hresidue] using (Nat.mod_add_div t W)
    refine ⟨t / W, ?_, ?_⟩
    · apply (affine_progression_mem_iff N W r (t / W) hW hr).mp
      simpa [hrepresentation] using ht
    · exact hrepresentation
  · rintro ⟨k, hk, rfl⟩
    refine ⟨(affine_progression_mem_iff N W r k hW hr).mpr hk, ?_⟩
    simp [Nat.add_mod, Nat.mod_eq_of_lt hr]

/-- Exact reindexing for an arbitrary predicate, so switched selectors and
both primality conditions survive the progression transformation. -/
theorem affine_residue_filter_card_eq_progression
    (N W r : ℕ) (hW : 0 < W) (hr : r < W)
    (predicate : ℕ → Prop) [DecidablePred predicate] :
    (((Finset.range N).filter fun t => t % W = r ∧ predicate t).card) =
      ((Finset.range (affineProgressionLength N W r)).filter
        fun k => predicate (r + W * k)).card := by
  classical
  let source := (Finset.range N).filter fun t => t % W = r ∧ predicate t
  let target := (Finset.range (affineProgressionLength N W r)).filter
    fun k => predicate (r + W * k)
  have hsets : source = target.image (fun k => r + W * k) := by
    ext t
    simp only [source, target, Finset.mem_filter, Finset.mem_range,
      Finset.mem_image]
    constructor
    · rintro ⟨ht, hresidue, hpredicate⟩
      have hrepresentation : r + W * (t / W) = t := by
        simpa [hresidue] using (Nat.mod_add_div t W)
      refine ⟨t / W, ⟨?_, ?_⟩, ?_⟩
      · apply (affine_progression_mem_iff N W r (t / W) hW hr).mp
        simpa [hrepresentation] using ht
      · simpa [hrepresentation] using hpredicate
      · exact hrepresentation
    · rintro ⟨k, ⟨hk, hpredicate⟩, rfl⟩
      exact ⟨(affine_progression_mem_iff N W r k hW hr).mpr hk,
        by simp [Nat.add_mod, Nat.mod_eq_of_lt hr], hpredicate⟩
  have hinjective : Function.Injective (fun k : ℕ => r + W * k) := by
    intro k k' heq
    exact Nat.mul_left_cancel hW (Nat.add_left_cancel heq)
  change source.card = target.card
  rw [hsets, Finset.card_image_of_injective _ hinjective]

/-- The exact progression length is at most its natural density plus one. -/
theorem affine_progression_length_real_le
    (N W r : ℕ) :
    (affineProgressionLength N W r : ℝ) ≤
      (N : ℝ) / (W : ℝ) + 1 := by
  unfold affineProgressionLength
  have hdivision : ((N / W : ℕ) : ℝ) ≤ (N : ℝ) / (W : ℝ) :=
    Nat.cast_div_le
  split_ifs with h
  · push_cast
    linarith
  · push_cast
    linarith

/-- Reparametrizing an affine form along a residue class preserves its exact
value, including its slope and intercept. -/
theorem affine_progression_affine_value
    (u v W r k : ℕ) :
    u * (r + W * k) + v = (u * W) * k + (u * r + v) := by
  ring

/-- A sieve prime avoiding both the original slope and the progression
modulus also avoids the reparametrized slope. -/
theorem affine_progression_slope_not_dvd
    (p u W : ℕ) (hp : p.Prime)
    (hu : ¬ p ∣ u) (hW : ¬ p ∣ W) :
    ¬ p ∣ u * W := by
  intro h
  exact (hp.dvd_mul.mp h).elim hu hW

/-- Progression reparametrization preserves the two distinct affine roots at
every sieve prime avoiding the progression modulus. -/
theorem affine_progression_determinant_nondegenerate
    (p W r u₁ v₁ u₂ v₂ : ℕ) (hp : p.Prime)
    (hW : ¬ p ∣ W)
    (hdet : (u₁ : ZMod p) * (v₂ : ZMod p) ≠
      (u₂ : ZMod p) * (v₁ : ZMod p)) :
    ((u₁ * W : ℕ) : ZMod p) * ((u₂ * r + v₂ : ℕ) : ZMod p) ≠
      ((u₂ * W : ℕ) : ZMod p) * ((u₁ * r + v₁ : ℕ) : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  intro heq
  have hWnonzero : (W : ZMod p) ≠ 0 := by
    intro hzero
    exact hW ((ZMod.natCast_eq_zero_iff W p).mp hzero)
  have hproduct :
      (W : ZMod p) *
        ((u₁ : ZMod p) * (v₂ : ZMod p) -
          (u₂ : ZMod p) * (v₁ : ZMod p)) = 0 := by
    push_cast at heq
    linear_combination heq
  exact hdet (sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_left hWnonzero))

/-- Sieve primes coprime to the excluded modulus automatically avoid every
divisor of that modulus, in particular the CRT progression spacing. -/
theorem affine_sieve_prime_not_dvd_progression_modulus
    (P : Finset ℕ) (M W p : ℕ)
    (hp : p.Prime) (hpP : p ∈ P)
    (hPM : Nat.Coprime (∏ q ∈ P, q) M)
    (hWM : W ∣ M) :
    ¬ p ∣ W := by
  have hpProduct : p ∣ ∏ q ∈ P, q :=
    Finset.dvd_prod_of_mem (fun q : ℕ => q) hpP
  have hpM : Nat.Coprime p M := hPM.coprime_dvd_left hpProduct
  intro hpW
  exact (hp.coprime_iff_not_dvd.mp hpM) (dvd_trans hpW hWM)

/-- The exact two-prime family in one actual residue class equals the
reparametrized affine-prime family on its sharp progression interval. -/
theorem affine_progression_prime_pair_card_eq
    (N W r u₁ v₁ u₂ v₂ : ℕ)
    (hW : 0 < W) (hr : r < W) :
    (((Finset.range N).filter fun t =>
      t % W = r ∧ (u₁ * t + v₁).Prime ∧ (u₂ * t + v₂).Prime).card) =
      (twoAffinePrimeParameters (affineProgressionLength N W r)
        (u₁ * W) (u₁ * r + v₁) (u₂ * W) (u₂ * r + v₂)).card := by
  simpa [twoAffinePrimeParameters, affine_progression_affine_value] using
    affine_residue_filter_card_eq_progression N W r hW hr
      (fun t => (u₁ * t + v₁).Prime ∧ (u₂ * t + v₂).Prime)

/-- The genuine optimized affine prime-pair sieve on one CRT residue class.
Its numerator is the exact class length, not the ambient interval length;
all transformed slopes, determinant conditions, and small-prime exceptions
are proved from the original forms. -/
theorem actualAffineProgression_prime_pair_card_le_twoRootDenominator
    (P : Finset ℕ) (M N z W r u₁ v₁ u₂ v₂ : ℕ)
    (hW : 0 < W) (hr : r < W)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z)
    (hu₁ : ∀ p ∈ P, ¬ p ∣ u₁)
    (hu₂ : ∀ p ∈ P, ¬ p ∣ u₂)
    (hdet : ∀ p ∈ P,
      (u₁ : ZMod p) * (v₂ : ZMod p) ≠
        (u₂ : ZMod p) * (v₁ : ZMod p))
    (hM : 2 ∣ M)
    (hPM : Nat.Coprime (∏ p ∈ P, p) M)
    (hWM : W ∣ M)
    (hprimes : ∀ p : ℕ, p.Prime →
      (p ∣ ∏ q ∈ P, q ↔ p ≤ z ∧ Nat.Coprime p M))
    (hu₁positive : 0 < u₁) (hu₂positive : 0 < u₂) :
    ((((Finset.range N).filter fun t =>
      t % W = r ∧ (u₁ * t + v₁).Prime ∧ (u₂ * t + v₂).Prime).card) : ℝ) ≤
      (affineProgressionLength N W r : ℝ) /
        twoRootSelbergDenominator M z + (z : ℝ) ^ 4 +
          ((2 * Nat.primeCounting z : ℕ) : ℝ) := by
  have havoid : ∀ p ∈ P, ¬ p ∣ W := fun p hp =>
    affine_sieve_prime_not_dvd_progression_modulus
      P M W p (hprime p hp) hp hPM hWM
  have hbound := actualAffineSelberg_all_prime_pair_card_le_twoRootDenominator
    P M (affineProgressionLength N W r) z
    (u₁ * W) (u₁ * r + v₁) (u₂ * W) (u₂ * r + v₂)
    hprime hlarge hz
    (fun p hp => affine_progression_slope_not_dvd
      p u₁ W (hprime p hp) (hu₁ p hp) (havoid p hp))
    (fun p hp => affine_progression_slope_not_dvd
      p u₂ W (hprime p hp) (hu₂ p hp) (havoid p hp))
    (fun p hp => affine_progression_determinant_nondegenerate
      p W r u₁ v₁ u₂ v₂ (hprime p hp) (havoid p hp) (hdet p hp))
    hM hPM hprimes (Nat.mul_pos hu₁positive hW)
      (Nat.mul_pos hu₂positive hW)
  rw [affine_progression_prime_pair_card_eq
    N W r u₁ v₁ u₂ v₂ hW hr]
  exact hbound

/-- The same genuine CRT-selected prime-pair bound with its explicit
`N / W` class spacing and at most one incomplete-block parameter. -/
theorem actualAffineProgression_prime_pair_card_le_density
    (P : Finset ℕ) (M N z W r u₁ v₁ u₂ v₂ : ℕ)
    (hW : 0 < W) (hr : r < W)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z)
    (hu₁ : ∀ p ∈ P, ¬ p ∣ u₁)
    (hu₂ : ∀ p ∈ P, ¬ p ∣ u₂)
    (hdet : ∀ p ∈ P,
      (u₁ : ZMod p) * (v₂ : ZMod p) ≠
        (u₂ : ZMod p) * (v₁ : ZMod p))
    (hM : 2 ∣ M)
    (hPM : Nat.Coprime (∏ p ∈ P, p) M)
    (hWM : W ∣ M)
    (hprimes : ∀ p : ℕ, p.Prime →
      (p ∣ ∏ q ∈ P, q ↔ p ≤ z ∧ Nat.Coprime p M))
    (hu₁positive : 0 < u₁) (hu₂positive : 0 < u₂) :
    ((((Finset.range N).filter fun t =>
      t % W = r ∧ (u₁ * t + v₁).Prime ∧ (u₂ * t + v₂).Prime).card) : ℝ) ≤
      ((N : ℝ) / (W : ℝ) + 1) /
        twoRootSelbergDenominator M z + (z : ℝ) ^ 4 +
          ((2 * Nat.primeCounting z : ℕ) : ℝ) := by
  calc
    ((((Finset.range N).filter fun t =>
      t % W = r ∧ (u₁ * t + v₁).Prime ∧ (u₂ * t + v₂).Prime).card) : ℝ) ≤
        (affineProgressionLength N W r : ℝ) /
          twoRootSelbergDenominator M z + (z : ℝ) ^ 4 +
            ((2 * Nat.primeCounting z : ℕ) : ℝ) :=
      actualAffineProgression_prime_pair_card_le_twoRootDenominator
        P M N z W r u₁ v₁ u₂ v₂ hW hr hprime hlarge hz hu₁ hu₂
        hdet hM hPM hWM hprimes hu₁positive hu₂positive
    _ ≤ ((N : ℝ) / (W : ℝ) + 1) /
          twoRootSelbergDenominator M z + (z : ℝ) ^ 4 +
            ((2 * Nat.primeCounting z : ℕ) : ℝ) := by
      have hdenominator : 0 ≤ twoRootSelbergDenominator M z :=
        twoRootSelbergDenominator_nonneg hM z
      gcongr
      exact affine_progression_length_real_le N W r

/-- Partition an arbitrary predicate exactly over its selected CRT residue
classes; unlike a union bound, no residue overlap or multiplicity is lost. -/
theorem affine_selected_filter_card_eq_sum
    (N W : ℕ) (residues : Finset ℕ)
    (predicate : ℕ → Prop) [DecidablePred predicate] :
    (((Finset.range N).filter fun t =>
      t % W ∈ residues ∧ predicate t).card) =
      ∑ r ∈ residues,
        (((Finset.range N).filter fun t =>
          t % W = r ∧ predicate t).card) := by
  classical
  have hpartition := Finset.sum_card_fiberwise_eq_card_filter
    ((Finset.range N).filter predicate) residues (fun t => t % W)
  calc
    (((Finset.range N).filter fun t =>
      t % W ∈ residues ∧ predicate t).card) =
        (((Finset.range N).filter predicate).filter
          fun t => t % W ∈ residues).card := by
      congr 1
      ext t
      simp only [Finset.mem_filter, Finset.mem_range]
      tauto
    _ = ∑ r ∈ residues,
          (((Finset.range N).filter predicate).filter
            fun t => t % W = r).card := hpartition.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      congr 1
      ext t
      simp only [Finset.mem_filter, Finset.mem_range]
      tauto

/-- Full optimized prime-pair transport through an arbitrary genuine set of
CRT-selected residue classes.  The leading term keeps the exact selector
cardinality and the required `1 / W` spacing. -/
theorem actualAffineSelected_prime_pair_card_le_density
    (P residues : Finset ℕ) (M N z W u₁ v₁ u₂ v₂ : ℕ)
    (hW : 0 < W) (hresidues : ∀ r ∈ residues, r < W)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z)
    (hu₁ : ∀ p ∈ P, ¬ p ∣ u₁)
    (hu₂ : ∀ p ∈ P, ¬ p ∣ u₂)
    (hdet : ∀ p ∈ P,
      (u₁ : ZMod p) * (v₂ : ZMod p) ≠
        (u₂ : ZMod p) * (v₁ : ZMod p))
    (hM : 2 ∣ M)
    (hPM : Nat.Coprime (∏ p ∈ P, p) M)
    (hWM : W ∣ M)
    (hprimes : ∀ p : ℕ, p.Prime →
      (p ∣ ∏ q ∈ P, q ↔ p ≤ z ∧ Nat.Coprime p M))
    (hu₁positive : 0 < u₁) (hu₂positive : 0 < u₂) :
    ((((Finset.range N).filter fun t =>
      t % W ∈ residues ∧
        (u₁ * t + v₁).Prime ∧ (u₂ * t + v₂).Prime).card) : ℝ) ≤
      (residues.card : ℝ) *
        (((N : ℝ) / (W : ℝ) + 1) /
          twoRootSelbergDenominator M z + (z : ℝ) ^ 4 +
            ((2 * Nat.primeCounting z : ℕ) : ℝ)) := by
  have hpartition := affine_selected_filter_card_eq_sum N W residues
    (fun t => (u₁ * t + v₁).Prime ∧ (u₂ * t + v₂).Prime)
  have hpartitionReal :
      ((((Finset.range N).filter fun t =>
        t % W ∈ residues ∧
          (u₁ * t + v₁).Prime ∧ (u₂ * t + v₂).Prime).card) : ℝ) =
        ∑ r ∈ residues,
          ((((Finset.range N).filter fun t =>
            t % W = r ∧
              (u₁ * t + v₁).Prime ∧ (u₂ * t + v₂).Prime).card) : ℝ) := by
    exact_mod_cast hpartition
  rw [hpartitionReal]
  calc
    (∑ r ∈ residues,
      ((((Finset.range N).filter fun t =>
        t % W = r ∧
          (u₁ * t + v₁).Prime ∧ (u₂ * t + v₂).Prime).card) : ℝ)) ≤
        ∑ _r ∈ residues,
          (((N : ℝ) / (W : ℝ) + 1) /
            twoRootSelbergDenominator M z + (z : ℝ) ^ 4 +
              ((2 * Nat.primeCounting z : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro r hr
      exact actualAffineProgression_prime_pair_card_le_density
        P M N z W r u₁ v₁ u₂ v₂ hW (hresidues r hr)
        hprime hlarge hz hu₁ hu₂ hdet hM hPM hWM hprimes
        hu₁positive hu₂positive
    _ = _ := by
      simp
      ring

/-- Uniform moving-exceptional-prime Selberg asymptotics for the actual union
of any selected CRT residue classes.  The explicit leading coefficient
retains the required selector density `#T / W`; the threshold depends only
on the fixed even excluded modulus. -/
theorem actualAffineSelected_prime_pairs_fifth_root_eventually_explicit
    (M W : ℕ) (hMeven : 2 ∣ M) (hM : 2 ≤ M)
    (hW : 0 < W) (hWM : W ∣ M) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (q : ℕ) (P residues : Finset ℕ) (u₁ v₁ u₂ v₂ : ℕ),
        q.Prime → Nat.Coprime q M → 5 ≤ q →
        (∀ r ∈ residues, r < W) →
        (∀ p ∈ P, p.Prime) →
        (∀ p ∈ P, 2 < p) →
        (∀ p ∈ P, ¬ p ∣ u₁) →
        (∀ p ∈ P, ¬ p ∣ u₂) →
        (∀ p ∈ P,
          (u₁ : ZMod p) * (v₂ : ZMod p) ≠
            (u₂ : ZMod p) * (v₁ : ZMod p)) →
        Nat.Coprime (∏ p ∈ P, p) (M * q) →
        (∀ p : ℕ, p.Prime →
          (p ∣ ∏ p' ∈ P, p' ↔
            p ≤ selbergSquareRootBlockCutoff n ^ 2 ∧
              Nat.Coprime p (M * q))) →
        0 < u₁ → 0 < u₂ →
        ((((Finset.range n).filter fun t =>
          t % W ∈ residues ∧
            (u₁ * t + v₁).Prime ∧ (u₂ * t + v₂).Prime).card) : ℝ) ≤
          (residues.card : ℝ) *
            ((605 / 3 : ℝ) * (((M : ℝ) / M.totient) ^ 2) *
              ((n : ℝ) / (W : ℝ) + 1) / (Real.log (n : ℝ)) ^ 2 +
                ((selbergSquareRootBlockCutoff n ^ 2 : ℕ) : ℝ) ^ 4 +
                  ((2 * Nat.primeCounting
                    (selbergSquareRootBlockCutoff n ^ 2) : ℕ) : ℝ)) := by
  filter_upwards
    [twoRootSelbergDenominator_fifth_root_eventually_inv_le_explicit
      M hMeven hM, eventually_ge_atTop 1] with n hreciprocal hn
  intro q P residues u₁ v₁ u₂ v₂ hq hqM hqfive hresidues
    hprime hlarge hu₁ hu₂ hdet hPM hprimes hu₁positive hu₂positive
  let z := selbergSquareRootBlockCutoff n ^ 2
  have hz : 0 < z :=
    selbergSquareRootBlockCutoff_sq_pos_of_pos n (by omega)
  have hMevenq : 2 ∣ M * q := dvd_mul_of_dvd_left hMeven q
  have hWMq : W ∣ M * q := dvd_mul_of_dvd_left hWM q
  have hsingle := actualAffineSelected_prime_pair_card_le_density
    P residues (M * q) n z W u₁ v₁ u₂ v₂ hW hresidues
    hprime hlarge hz hu₁ hu₂ hdet hMevenq hPM hWMq hprimes
    hu₁positive hu₂positive
  have hreciprocal' := hreciprocal q hq hqM hqfive
  change (twoRootSelbergDenominator (M * q) z)⁻¹ ≤
    (605 / 3 : ℝ) * (((M : ℝ) / M.totient) ^ 2) /
      (Real.log (n : ℝ)) ^ 2 at hreciprocal'
  calc
    ((((Finset.range n).filter fun t =>
      t % W ∈ residues ∧
        (u₁ * t + v₁).Prime ∧ (u₂ * t + v₂).Prime).card) : ℝ) ≤
      (residues.card : ℝ) *
        (((n : ℝ) / (W : ℝ) + 1) /
          twoRootSelbergDenominator (M * q) z + (z : ℝ) ^ 4 +
            ((2 * Nat.primeCounting z : ℕ) : ℝ)) := hsingle
    _ ≤ (residues.card : ℝ) *
        ((605 / 3 : ℝ) * (((M : ℝ) / M.totient) ^ 2) *
          ((n : ℝ) / (W : ℝ) + 1) / (Real.log (n : ℝ)) ^ 2 +
            (z : ℝ) ^ 4 +
              ((2 * Nat.primeCounting z : ℕ) : ℝ)) := by
      have hmain :
          ((n : ℝ) / (W : ℝ) + 1) /
              twoRootSelbergDenominator (M * q) z ≤
            (605 / 3 : ℝ) * (((M : ℝ) / M.totient) ^ 2) *
              ((n : ℝ) / (W : ℝ) + 1) /
                (Real.log (n : ℝ)) ^ 2 := by
        calc
          ((n : ℝ) / (W : ℝ) + 1) /
              twoRootSelbergDenominator (M * q) z =
            ((n : ℝ) / (W : ℝ) + 1) *
              (twoRootSelbergDenominator (M * q) z)⁻¹ := by
                rfl
          _ ≤ ((n : ℝ) / (W : ℝ) + 1) *
              ((605 / 3 : ℝ) * (((M : ℝ) / M.totient) ^ 2) /
                (Real.log (n : ℝ)) ^ 2) := by
                exact mul_le_mul_of_nonneg_left hreciprocal' (by positivity)
          _ = (605 / 3 : ℝ) * (((M : ℝ) / M.totient) ^ 2) *
                ((n : ℝ) / (W : ℝ) + 1) /
                  (Real.log (n : ℝ)) ^ 2 := by
                ring
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ = _ := by rfl

/-- The actual switched-hit predicate is constant on every genuine support
product residue class, including an arbitrary natural affine multiplier. -/
theorem switchedHits_mul_eq_of_support_residue
    (S : Finset ℕ) (b : ℕ → ℕ) (c t r : ℕ)
    (hresidue : t % (∏ s ∈ S, s) = r) :
    switchedHits S b (c * t) = switchedHits S b (c * r) := by
  unfold switchedHits
  congr 1
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hp, hhit⟩
    refine ⟨hp, ?_⟩
    have hdiv : p ∣ ∏ s ∈ S, s :=
      Finset.dvd_prod_of_mem (fun s : ℕ => s) hp
    have hmod : t % p = r % p := by
      calc
        t % p = (t % (∏ s ∈ S, s)) % p :=
          (Nat.mod_mod_of_dvd t hdiv).symm
        _ = r % p := by rw [hresidue]
    have hmul : (c * t) % p = (c * r) % p := by
      simp [Nat.mul_mod, hmod]
    change b p % p = (c * t) % p at hhit
    change b p % p = (c * r) % p
    exact hhit.trans hmul
  · rintro ⟨hp, hhit⟩
    refine ⟨hp, ?_⟩
    have hdiv : p ∣ ∏ s ∈ S, s :=
      Finset.dvd_prod_of_mem (fun s : ℕ => s) hp
    have hmod : t % p = r % p := by
      calc
        t % p = (t % (∏ s ∈ S, s)) % p :=
          (Nat.mod_mod_of_dvd t hdiv).symm
        _ = r % p := by rw [hresidue]
    have hmul : (c * t) % p = (c * r) % p := by
      simp [Nat.mul_mod, hmod]
    change b p % p = (c * r) % p at hhit
    change b p % p = (c * t) % p
    exact hhit.trans hmul.symm

/-- The genuine support-product residues retaining both fixed-left manuscript
selectors, rather than an assumed local-density surrogate. -/
def actualLeftFiberSelectorResidues
    (S : Finset ℕ) (b : ℕ → ℕ) (x d : ℕ) : Finset ℕ :=
  (Finset.range (∏ s ∈ S, s)).filter fun r =>
    switchedHits S b (2 * x) = 0 ∧
      switchedHits S b (4 * d * r) = 0

/-- The genuine support-product residues retaining both fixed-right manuscript
selectors. -/
def actualRightFiberSelectorResidues
    (S : Finset ℕ) (b : ℕ → ℕ) (y a : ℕ) : Finset ℕ :=
  (Finset.range (∏ s ∈ S, s)).filter fun r =>
    switchedHits S b (2 * a * r) = 0 ∧
      switchedHits S b (2 * y) = 0

/-- Fixed-left switched selectors are exactly membership in their genuine
support-product residue finset. -/
theorem leftFiberSwitched_selector_iff_mem_actual_residues
    (S : Finset ℕ) (b : ℕ → ℕ) (x d q : ℕ)
    (hW : 0 < ∏ s ∈ S, s) :
    (switchedHits S b (2 * x) = 0 ∧
      switchedHits S b (4 * d * q) = 0) ↔
        q % (∏ s ∈ S, s) ∈
          actualLeftFiberSelectorResidues S b x d := by
  unfold actualLeftFiberSelectorResidues
  rw [Finset.mem_filter, Finset.mem_range]
  have hclass : q % (∏ s ∈ S, s) < ∏ s ∈ S, s :=
    Nat.mod_lt q hW
  have hperiod := switchedHits_mul_eq_of_support_residue
    S b (4 * d) q (q % (∏ s ∈ S, s)) rfl
  simp [hclass, hperiod]

/-- Fixed-right switched selectors are exactly membership in their genuine
support-product residue finset. -/
theorem rightFiberSwitched_selector_iff_mem_actual_residues
    (S : Finset ℕ) (b : ℕ → ℕ) (y a q : ℕ)
    (hW : 0 < ∏ s ∈ S, s) :
    (switchedHits S b (2 * a * q) = 0 ∧
      switchedHits S b (2 * y) = 0) ↔
        q % (∏ s ∈ S, s) ∈
          actualRightFiberSelectorResidues S b y a := by
  unfold actualRightFiberSelectorResidues
  rw [Finset.mem_filter, Finset.mem_range]
  have hclass : q % (∏ s ∈ S, s) < ∏ s ∈ S, s :=
    Nat.mod_lt q hW
  have hperiod := switchedHits_mul_eq_of_support_residue
    S b (2 * a) q (q % (∏ s ∈ S, s)) rfl
  simp [hclass, hperiod]

/-- The actual fixed-left graph parameter finset equals a prime-pair family
with the exact global switched-selector residue classes retained. -/
theorem leftFiberSwitchedPrimeParameters_eq_selected
    (S : Finset ℕ) (b : ℕ → ℕ) (n x d : ℕ)
    (hW : 0 < ∏ s ∈ S, s) :
    leftFiberSwitchedPrimeParameters S b n x d =
      (Finset.range (n + 1)).filter fun q =>
        q % (∏ s ∈ S, s) ∈ actualLeftFiberSelectorResidues S b x d ∧
          q.Prime ∧ (2 * d * q - x).Prime := by
  ext q
  simp only [leftFiberSwitchedPrimeParameters, leftFiberPrimeParameters,
    Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  rw [← leftFiberSwitched_selector_iff_mem_actual_residues S b x d q hW]
  constructor
  · rintro ⟨⟨⟨hpositive, hupper⟩, hprime, hlabel⟩, hleft, hright⟩
    exact ⟨by omega, ⟨hleft, hright⟩, hprime, hlabel⟩
  · rintro ⟨hupper, ⟨hleft, hright⟩, hprime, hlabel⟩
    exact ⟨⟨⟨hprime.one_le, by omega⟩, hprime, hlabel⟩,
      hleft, hright⟩

/-- The actual fixed-right graph parameter finset likewise retains the exact
global selector residue classes and its genuinely decreasing second form. -/
theorem rightFiberSwitchedPrimeParameters_eq_selected
    (S : Finset ℕ) (b : ℕ → ℕ) (n y a : ℕ)
    (hW : 0 < ∏ s ∈ S, s) :
    rightFiberSwitchedPrimeParameters S b n y a =
      (Finset.range (n + 1)).filter fun q =>
        q % (∏ s ∈ S, s) ∈ actualRightFiberSelectorResidues S b y a ∧
          q.Prime ∧ (y - a * q).Prime := by
  ext q
  simp only [rightFiberSwitchedPrimeParameters, rightFiberPrimeParameters,
    Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  rw [← rightFiberSwitched_selector_iff_mem_actual_residues S b y a q hW]
  constructor
  · rintro ⟨⟨⟨hpositive, hupper⟩, hprime, hlabel⟩, hleft, hright⟩
    exact ⟨by omega, ⟨hleft, hright⟩, hprime, hlabel⟩
  · rintro ⟨hupper, ⟨hleft, hright⟩, hprime, hlabel⟩
    exact ⟨⟨⟨hprime.one_le, by omega⟩, hprime, hlabel⟩,
      hleft, hright⟩

/-- Natural subtraction commutes exactly with progression reparametrization;
the nested subtraction records the genuine decreasing affine intercept. -/
theorem affine_progression_descending_value
    (y a W r k : ℕ) :
    y - a * (r + W * k) =
      (y - a * r) - (a * W) * k := by
  rw [Nat.sub_sub]
  congr 1
  ring

/-- An actual mixed prime family in a fixed CRT class is exactly the general
increasing/descending affine family on the sharp progression interval. -/
theorem affine_progression_mixed_prime_pair_card_eq
    (N W r a y : ℕ)
    (hW : 0 < W) (hr : r < W) :
    (((Finset.range N).filter fun t =>
      t % W = r ∧ t.Prime ∧ (y - a * t).Prime).card) =
      (mixedAffinePrimeParameters (affineProgressionLength N W r)
        W r (a * W) (y - a * r)).card := by
  have hreindex := affine_residue_filter_card_eq_progression N W r hW hr
    (fun t => t.Prime ∧ (y - a * t).Prime)
  rw [hreindex]
  unfold mixedAffinePrimeParameters
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  rw [affine_progression_descending_value y a W r k]
  simp [Nat.add_comm]

/-- The genuine mixed progression determinant is nonzero whenever sieve
primes avoid the original intercept and the support-product spacing.  This
eliminates the positive modular-surrogate determinant as an extra hypothesis. -/
theorem affine_progression_mixed_determinant_nondegenerate
    (P : Finset ℕ) (p W r a y : ℕ)
    (hprime : ∀ q ∈ P, q.Prime) (hp : p.Prime) (hpP : p ∈ P)
    (hW : ¬ p ∣ W) (hy : ¬ p ∣ y)
    (har : a * r ≤ y) :
    (W : ZMod p) * ((y - a * r : ℕ) : ZMod p) ≠
      ((∏ q ∈ P, q) - (a * W) % (∏ q ∈ P, q) : ℕ) *
        (r : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  let B := ∏ q ∈ P, q
  have hpB : p ∣ B :=
    Finset.dvd_prod_of_mem (fun q : ℕ => q) hpP
  have hBpositive : 0 < B :=
    Finset.prod_pos fun q hq => (hprime q hq).pos
  intro heq
  have hmodcast : (((a * W) % B : ℕ) : ZMod p) =
      ((a * W : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr
      ((Nat.mod_modEq (a * W) B).of_dvd hpB)
  have hbound : (a * W) % B ≤ B :=
    (Nat.mod_lt (a * W) hBpositive).le
  have hsum : B - (a * W) % B + (a * W) % B = B :=
    Nat.sub_add_cancel hbound
  have hsumcast := congrArg (fun n : ℕ => (n : ZMod p)) hsum
  push_cast at hsumcast
  rw [hmodcast, (ZMod.natCast_eq_zero_iff B p).mpr hpB] at hsumcast
  have hsubcast : ((y - a * r : ℕ) : ZMod p) =
      (y : ZMod p) - (a : ZMod p) * (r : ZMod p) := by
    rw [Nat.cast_sub har, Nat.cast_mul]
  change (W : ZMod p) * ((y - a * r : ℕ) : ZMod p) =
    ((B - (a * W) % B : ℕ) : ZMod p) * (r : ZMod p) at heq
  rw [hsubcast] at heq
  have hzero : (W : ZMod p) * (y : ZMod p) = 0 := by
    push_cast at hsumcast
    linear_combination heq + (r : ZMod p) * hsumcast
  have hWnonzero : (W : ZMod p) ≠ 0 := by
    intro hzeroW
    exact hW ((ZMod.natCast_eq_zero_iff W p).mp hzeroW)
  have hynonzero : (y : ZMod p) ≠ 0 := by
    intro hzeroy
    exact hy ((ZMod.natCast_eq_zero_iff y p).mp hzeroy)
  exact (mul_ne_zero hWnonzero hynonzero) hzero

/-- The complete optimized sieve for the genuine descending prime pair in
one actual CRT-selected residue class.  Its determinant and divisor
remainder are discharged, and both small-prime exceptions are retained. -/
theorem actualMixedAffineProgression_prime_pair_card_le_twoRootDenominator
    (P : Finset ℕ) (M N z W r a y : ℕ)
    (hW : 0 < W) (hr : r < W) (har : a * r ≤ y)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z)
    (ha : ∀ p ∈ P, ¬ p ∣ a)
    (hy : ∀ p ∈ P, ¬ p ∣ y)
    (hunderflow : ∀ t < N, a * t ≤ y)
    (hM : 2 ∣ M)
    (hPM : Nat.Coprime (∏ p ∈ P, p) M)
    (hWM : W ∣ M)
    (hprimes : ∀ p : ℕ, p.Prime →
      (p ∣ ∏ q ∈ P, q ↔ p ≤ z ∧ Nat.Coprime p M))
    (hapositive : 0 < a) :
    ((((Finset.range N).filter fun t =>
      t % W = r ∧ t.Prime ∧ (y - a * t).Prime).card) : ℝ) ≤
      (affineProgressionLength N W r : ℝ) /
        twoRootSelbergDenominator M z + (z : ℝ) ^ 4 +
          ((2 * Nat.primeCounting z : ℕ) : ℝ) := by
  have havoid : ∀ p ∈ P, ¬ p ∣ W := fun p hp =>
    affine_sieve_prime_not_dvd_progression_modulus
      P M W p (hprime p hp) hp hPM hWM
  have hparameter : ∀ k < affineProgressionLength N W r,
      (a * W) * k ≤ y - a * r := by
    intro k hk
    have hkN := (affine_progression_mem_iff N W r k hW hr).mpr hk
    have horiginal := hunderflow (r + W * k) hkN
    have hrewrite : a * (r + W * k) = a * r + (a * W) * k := by ring
    omega
  have hbound := actualMixedAffineSelberg_all_prime_pair_card_le_twoRootDenominator
    P M (affineProgressionLength N W r) z W r (a * W) (y - a * r)
    hprime hlarge hz havoid
    (fun p hp => affine_progression_slope_not_dvd
      p a W (hprime p hp) (ha p hp) (havoid p hp))
    (fun p hp => affine_progression_mixed_determinant_nondegenerate
      P p W r a y hprime (hprime p hp) hp (havoid p hp) (hy p hp) har)
    hparameter hM hPM hprimes hW (Nat.mul_pos hapositive hW)
  rw [affine_progression_mixed_prime_pair_card_eq N W r a y hW hr]
  exact hbound

/-- The genuine selected descending prime-pair bound retains the true
progression density and the complete optimized error. -/
theorem actualMixedAffineProgression_prime_pair_card_le_density
    (P : Finset ℕ) (M N z W r a y : ℕ)
    (hW : 0 < W) (hr : r < W) (har : a * r ≤ y)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z)
    (ha : ∀ p ∈ P, ¬ p ∣ a)
    (hy : ∀ p ∈ P, ¬ p ∣ y)
    (hunderflow : ∀ t < N, a * t ≤ y)
    (hM : 2 ∣ M)
    (hPM : Nat.Coprime (∏ p ∈ P, p) M)
    (hWM : W ∣ M)
    (hprimes : ∀ p : ℕ, p.Prime →
      (p ∣ ∏ q ∈ P, q ↔ p ≤ z ∧ Nat.Coprime p M))
    (hapositive : 0 < a) :
    ((((Finset.range N).filter fun t =>
      t % W = r ∧ t.Prime ∧ (y - a * t).Prime).card) : ℝ) ≤
      ((N : ℝ) / (W : ℝ) + 1) /
        twoRootSelbergDenominator M z + (z : ℝ) ^ 4 +
          ((2 * Nat.primeCounting z : ℕ) : ℝ) := by
  have hdenominator : 0 ≤ twoRootSelbergDenominator M z :=
    twoRootSelbergDenominator_nonneg hM z
  calc
    ((((Finset.range N).filter fun t =>
      t % W = r ∧ t.Prime ∧ (y - a * t).Prime).card) : ℝ) ≤
      (affineProgressionLength N W r : ℝ) /
        twoRootSelbergDenominator M z + (z : ℝ) ^ 4 +
          ((2 * Nat.primeCounting z : ℕ) : ℝ) :=
        actualMixedAffineProgression_prime_pair_card_le_twoRootDenominator
          P M N z W r a y hW hr har hprime hlarge hz ha hy hunderflow
            hM hPM hWM hprimes hapositive
    _ ≤ ((N : ℝ) / (W : ℝ) + 1) /
        twoRootSelbergDenominator M z + (z : ℝ) ^ 4 +
          ((2 * Nat.primeCounting z : ℕ) : ℝ) := by
      gcongr
      exact affine_progression_length_real_le N W r

/-- The complete actual descending two-prime sieve over any finite family of
CRT-selected residue classes.  The selector cardinality, `1 / W` spacing,
divisor remainder, moving determinant exclusions, and all small-prime
exceptions remain explicit. -/
theorem actualMixedAffineSelected_prime_pair_card_le_density
    (P residues : Finset ℕ) (M N z W a y : ℕ)
    (hW : 0 < W)
    (hresidues : ∀ r ∈ residues, r < W ∧ a * r ≤ y)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z)
    (ha : ∀ p ∈ P, ¬ p ∣ a)
    (hy : ∀ p ∈ P, ¬ p ∣ y)
    (hunderflow : ∀ t < N, a * t ≤ y)
    (hM : 2 ∣ M)
    (hPM : Nat.Coprime (∏ p ∈ P, p) M)
    (hWM : W ∣ M)
    (hprimes : ∀ p : ℕ, p.Prime →
      (p ∣ ∏ q ∈ P, q ↔ p ≤ z ∧ Nat.Coprime p M))
    (hapositive : 0 < a) :
    ((((Finset.range N).filter fun t =>
      t % W ∈ residues ∧ t.Prime ∧ (y - a * t).Prime).card) : ℝ) ≤
      (residues.card : ℝ) *
        (((N : ℝ) / (W : ℝ) + 1) /
          twoRootSelbergDenominator M z + (z : ℝ) ^ 4 +
            ((2 * Nat.primeCounting z : ℕ) : ℝ)) := by
  have hpartition := affine_selected_filter_card_eq_sum N W residues
    (fun t => t.Prime ∧ (y - a * t).Prime)
  have hpartitionReal :
      ((((Finset.range N).filter fun t =>
        t % W ∈ residues ∧ t.Prime ∧ (y - a * t).Prime).card) : ℝ) =
        ∑ r ∈ residues,
          ((((Finset.range N).filter fun t =>
            t % W = r ∧ t.Prime ∧ (y - a * t).Prime).card) : ℝ) := by
    exact_mod_cast hpartition
  rw [hpartitionReal]
  calc
    (∑ r ∈ residues,
      ((((Finset.range N).filter fun t =>
        t % W = r ∧ t.Prime ∧ (y - a * t).Prime).card) : ℝ)) ≤
        ∑ _r ∈ residues,
          (((N : ℝ) / (W : ℝ) + 1) /
            twoRootSelbergDenominator M z + (z : ℝ) ^ 4 +
              ((2 * Nat.primeCounting z : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro r hr
      exact actualMixedAffineProgression_prime_pair_card_le_density
        P M N z W r a y hW (hresidues r hr).1 (hresidues r hr).2
        hprime hlarge hz ha hy hunderflow hM hPM hWM hprimes hapositive
    _ = _ := by
      simp
      ring

/-- Actual right-fiber residue selectors after discarding classes that cannot
possibly lie in the non-underflow interval. -/
def actualAdmissibleRightFiberSelectorResidues
    (S : Finset ℕ) (b : ℕ → ℕ) (y a : ℕ) : Finset ℕ :=
  (actualRightFiberSelectorResidues S b y a).filter fun r => a * r ≤ y

/-- The exact endpoint needed for a genuine descending right-fiber pair;
beyond it the natural subtraction cannot be a positive prime. -/
def actualRightFiberTruncation (n a y : ℕ) : ℕ :=
  min (n + 1) (y / a + 1)

/-- The actual fixed-right manuscript parameter set is exactly its
CRT-selected, automatically non-underflow-truncated two-prime family. -/
theorem rightFiberSwitchedPrimeParameters_eq_truncated_selected
    (S : Finset ℕ) (b : ℕ → ℕ) (n y a : ℕ)
    (hW : 0 < ∏ s ∈ S, s) (ha : 0 < a) :
    rightFiberSwitchedPrimeParameters S b n y a =
      (Finset.range (actualRightFiberTruncation n a y)).filter fun q =>
        q % (∏ s ∈ S, s) ∈
          actualAdmissibleRightFiberSelectorResidues S b y a ∧
            q.Prime ∧ (y - a * q).Prime := by
  ext q
  simp only [rightFiberSwitchedPrimeParameters, rightFiberPrimeParameters,
    actualAdmissibleRightFiberSelectorResidues, Finset.mem_filter,
    Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨⟨⟨hpositive, hupper⟩, hprime, hlabel⟩, hfirst, hsecond⟩
    have hproduct : a * q < y := Nat.sub_pos_iff_lt.mp hlabel.pos
    have hdiv : q ≤ y / a := by
      apply (Nat.le_div_iff_mul_le ha).mpr
      simpa [Nat.mul_comm] using hproduct.le
    have hresidue :=
      (rightFiberSwitched_selector_iff_mem_actual_residues
        S b y a q hW).mp ⟨hfirst, hsecond⟩
    have hresidueUnderflow : a * (q % (∏ s ∈ S, s)) ≤ y :=
      (Nat.mul_le_mul_left a (Nat.mod_le q _)).trans hproduct.le
    refine ⟨?_, ⟨hresidue, hresidueUnderflow⟩, hprime, hlabel⟩
    unfold actualRightFiberTruncation
    omega
  · rintro ⟨hupper, ⟨hresidue, hresidueUnderflow⟩, hprime, hlabel⟩
    have hselectors :=
      (rightFiberSwitched_selector_iff_mem_actual_residues
        S b y a q hW).mpr hresidue
    have hq : q ≤ n := by
      have hmin : actualRightFiberTruncation n a y ≤ n + 1 :=
        min_le_left _ _
      omega
    exact ⟨⟨⟨hprime.one_le, hq⟩, hprime, hlabel⟩,
      hselectors.1, hselectors.2⟩

/-- Every parameter in the true right-fiber truncated interval satisfies the
non-underflow condition required by the optimized descending sieve. -/
theorem actualRightFiberTruncation_no_underflow
    (n a y : ℕ) (ha : 0 < a) :
    ∀ t < actualRightFiberTruncation n a y, a * t ≤ y := by
  intro t ht
  have hupper : actualRightFiberTruncation n a y ≤ y / a + 1 :=
    min_le_right _ _
  have hdiv : t ≤ y / a := by omega
  have hmul := (Nat.le_div_iff_mul_le ha).mp hdiv
  simpa [Nat.mul_comm] using hmul

/-- Full optimized Selberg bound for the actual fixed-right manuscript graph
fiber, retaining both real switched selectors and their exact `1 / W` CRT
spacing.  The descending remainder, natural-subtraction truncation, and all
small-prime exceptions are unconditional. -/
theorem rightFiberSwitchedPrimeParameters_card_le_selected_sieve
    (S P : Finset ℕ) (b : ℕ → ℕ) (M n z y a : ℕ)
    (hW : 0 < ∏ s ∈ S, s)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z)
    (ha : ∀ p ∈ P, ¬ p ∣ a)
    (hy : ∀ p ∈ P, ¬ p ∣ y)
    (hM : 2 ∣ M)
    (hPM : Nat.Coprime (∏ p ∈ P, p) M)
    (hWM : (∏ s ∈ S, s) ∣ M)
    (hprimes : ∀ p : ℕ, p.Prime →
      (p ∣ ∏ q ∈ P, q ↔ p ≤ z ∧ Nat.Coprime p M))
    (hapositive : 0 < a) :
    ((rightFiberSwitchedPrimeParameters S b n y a).card : ℝ) ≤
      ((actualAdmissibleRightFiberSelectorResidues S b y a).card : ℝ) *
        (((actualRightFiberTruncation n a y : ℝ) /
            (((∏ s ∈ S, s) : ℕ) : ℝ) + 1) /
              twoRootSelbergDenominator M z + (z : ℝ) ^ 4 +
                ((2 * Nat.primeCounting z : ℕ) : ℝ)) := by
  rw [rightFiberSwitchedPrimeParameters_eq_truncated_selected
    S b n y a hW hapositive]
  apply actualMixedAffineSelected_prime_pair_card_le_density
    P (actualAdmissibleRightFiberSelectorResidues S b y a)
      M (actualRightFiberTruncation n a y) z
      (∏ s ∈ S, s) a y hW
  · intro r hr
    obtain ⟨hselector, hnonnegative⟩ := Finset.mem_filter.mp hr
    obtain ⟨hrange, _⟩ := Finset.mem_filter.mp hselector
    exact ⟨Finset.mem_range.mp hrange, hnonnegative⟩
  · exact hprime
  · exact hlarge
  · exact hz
  · exact ha
  · exact hy
  · exact actualRightFiberTruncation_no_underflow n a y hapositive
  · exact hM
  · exact hPM
  · exact hWM
  · exact hprimes
  · exact hapositive

/-- Exact translation of the tail of an initial natural interval, preserving
an arbitrary predicate and every endpoint. -/
theorem affine_tail_filter_card_eq_shift
    (N shift : ℕ)
    (predicate : ℕ → Prop) [DecidablePred predicate] :
    (((Finset.range N).filter fun t => shift ≤ t ∧ predicate t).card) =
      (((Finset.range (N - shift)).filter
        fun k => predicate (shift + k)).card) := by
  classical
  let source := (Finset.range N).filter fun t => shift ≤ t ∧ predicate t
  let target := (Finset.range (N - shift)).filter
    fun k => predicate (shift + k)
  have hsets : source = target.image (fun k => shift + k) := by
    ext t
    simp only [source, target, Finset.mem_filter, Finset.mem_range,
      Finset.mem_image]
    constructor
    · rintro ⟨ht, hshift, hpredicate⟩
      refine ⟨t - shift, ⟨?_, ?_⟩, ?_⟩
      · omega
      · simpa [Nat.add_sub_of_le hshift] using hpredicate
      · omega
    · rintro ⟨k, ⟨hk, hpredicate⟩, rfl⟩
      exact ⟨by omega, by omega, hpredicate⟩
  have hinjective : Function.Injective (fun k : ℕ => shift + k) :=
    fun _ _ h => Nat.add_left_cancel h
  change source.card = target.card
  rw [hsets, Finset.card_image_of_injective _ hinjective]

/-- The genuine selector set after translating a parameter interval by a
fixed natural shift. -/
def affineShiftedSelectorResidues
    (W shift : ℕ) (residues : Finset ℕ) : Finset ℕ :=
  (Finset.range W).filter fun r => (shift + r) % W ∈ residues

/-- Translation modulo the positive CRT spacing is injective on canonical
residue representatives. -/
theorem affine_residue_translation_injective
    (W shift : ℕ) (_hW : 0 < W) :
    Set.InjOn (fun r : ℕ => (shift + r) % W)
      (↑(Finset.range W) : Set ℕ) := by
  intro r hr r' hr' heq
  have hrlt : r < W := Finset.mem_range.mp (Finset.mem_coe.mp hr)
  have hr'lt : r' < W := Finset.mem_range.mp (Finset.mem_coe.mp hr')
  have hmod : Nat.ModEq W (shift + r) (shift + r') := heq
  have hcancel := Nat.ModEq.add_left_cancel' shift hmod
  change r % W = r' % W at hcancel
  simpa [Nat.mod_eq_of_lt hrlt, Nat.mod_eq_of_lt hr'lt] using hcancel

/-- Translating actual CRT selectors never increases their cardinality, so
no support-dependent leading factor is lost when removing a negative
intercept. -/
theorem affineShiftedSelectorResidues_card_le
    (W shift : ℕ) (residues : Finset ℕ) (hW : 0 < W) :
    (affineShiftedSelectorResidues W shift residues).card ≤ residues.card := by
  let selected := affineShiftedSelectorResidues W shift residues
  let rotation : ℕ → ℕ := fun r => (shift + r) % W
  have hinjective : Set.InjOn rotation (↑selected : Set ℕ) := by
    intro r hr r' hr' heq
    apply affine_residue_translation_injective W shift hW
    · exact Finset.mem_coe.mpr
        ((Finset.mem_filter.mp (Finset.mem_coe.mp hr)).1)
    · exact Finset.mem_coe.mpr
        ((Finset.mem_filter.mp (Finset.mem_coe.mp hr')).1)
    · exact heq
  calc
    selected.card = (selected.image rotation).card :=
      (Finset.card_image_iff.mpr hinjective).symm
    _ ≤ residues.card := by
      apply Finset.card_le_card
      intro r hr
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
      exact (Finset.mem_filter.mp hk).2

/-- The original and translated actual selector predicates agree exactly
after reduction to the canonical CRT residue. -/
theorem affineShiftedSelectorResidues_mem_iff
    (W shift k : ℕ) (residues : Finset ℕ) (hW : 0 < W) :
    k % W ∈ affineShiftedSelectorResidues W shift residues ↔
      (shift + k) % W ∈ residues := by
  unfold affineShiftedSelectorResidues
  rw [Finset.mem_filter, Finset.mem_range]
  have hcanonical : k % W < W := Nat.mod_lt k hW
  have hclass : (shift + k % W) % W = (shift + k) % W := by
    simp [Nat.add_mod]
  simp [hcanonical, hclass]

/-- A prime-valued natural affine difference lies strictly beyond its exact
quotient threshold, so its negative intercept can be removed without losing
or adding any genuine prime parameter. -/
theorem affine_prime_difference_threshold
    (u x t : ℕ) (hu : 0 < u)
    (hprime : (u * t - x).Prime) :
    x / u + 1 ≤ t := by
  have hpositive : x < u * t := Nat.sub_pos_iff_lt.mp hprime.pos
  have hdiv : x / u < t := by
    apply (Nat.div_lt_iff_lt_mul hu).mpr
    simpa [Nat.mul_comm] using hpositive
  omega

/-- The shifted positive-intercept form retains the exact original moving
determinant: a sieve prime avoiding `x` cannot identify its two affine roots. -/
theorem affine_shifted_negative_intercept_determinant
    (p u shift x : ℕ)
    (hxshift : x ≤ u * shift) (hx : ¬ p ∣ x) :
    (1 : ZMod p) * ((u * shift - x : ℕ) : ZMod p) ≠
      (u : ZMod p) * (shift : ZMod p) := by
  intro heq
  have hcast : ((u * shift - x : ℕ) : ZMod p) =
      (u : ZMod p) * (shift : ZMod p) - (x : ZMod p) := by
    rw [Nat.cast_sub hxshift, Nat.cast_mul]
  rw [one_mul, hcast] at heq
  have hzero : (x : ZMod p) = 0 := by
    linear_combination -heq
  exact hx ((ZMod.natCast_eq_zero_iff x p).mp hzero)

/-- Exact conversion of selected prime pairs with an increasing natural
difference into positive-intercept affine prime pairs.  Translation rotates
the actual selector classes and uses the exact truncated interval. -/
theorem affineSelected_prime_difference_card_eq_shift
    (N W u x : ℕ) (residues : Finset ℕ)
    (hW : 0 < W) (hu : 0 < u) :
    (((Finset.range N).filter fun t =>
      t % W ∈ residues ∧ t.Prime ∧ (u * t - x).Prime).card) =
      (((Finset.range (N - (x / u + 1))).filter fun k =>
        k % W ∈ affineShiftedSelectorResidues W (x / u + 1) residues ∧
          (1 * k + (x / u + 1)).Prime ∧
            (u * k + (u * (x / u + 1) - x)).Prime).card) := by
  let shift := x / u + 1
  have hpositive : x < u * shift := by
    have hquotient :=
      (Nat.div_lt_iff_lt_mul hu).mp (Nat.lt_succ_self (x / u))
    simpa [shift, Nat.mul_comm] using hquotient
  have htail :
      ((Finset.range N).filter fun t =>
        t % W ∈ residues ∧ t.Prime ∧ (u * t - x).Prime) =
      ((Finset.range N).filter fun t =>
        shift ≤ t ∧
          (t % W ∈ residues ∧ t.Prime ∧ (u * t - x).Prime)) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨ht, hresidue, hprime, hdifference⟩
      exact ⟨ht, affine_prime_difference_threshold u x t hu hdifference,
        hresidue, hprime, hdifference⟩
    · rintro ⟨ht, _, hresidue, hprime, hdifference⟩
      exact ⟨ht, hresidue, hprime, hdifference⟩
  rw [htail]
  rw [affine_tail_filter_card_eq_shift N shift
    (fun t => t % W ∈ residues ∧ t.Prime ∧ (u * t - x).Prime)]
  change
    (((Finset.range (N - shift)).filter fun k =>
      (shift + k) % W ∈ residues ∧
        (shift + k).Prime ∧ (u * (shift + k) - x).Prime).card) =
      (((Finset.range (N - shift)).filter fun k =>
        k % W ∈ affineShiftedSelectorResidues W shift residues ∧
          (1 * k + shift).Prime ∧
            (u * k + (u * shift - x)).Prime).card)
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  rw [affineShiftedSelectorResidues_mem_iff W shift k residues hW]
  have hvalue : u * (shift + k) - x = u * k + (u * shift - x) := by
    have hdistribute : u * (shift + k) = u * shift + u * k := by ring
    omega
  rw [hvalue]
  simp [Nat.add_comm]

/-- Actual selector-preserving optimized Selberg bound for increasing
prime differences, including negative intercepts and the genuine `q = 3`
fixed-left vertex. -/
theorem actualAffineSelected_prime_difference_card_le_density
    (P residues : Finset ℕ) (M N z W u x : ℕ)
    (hW : 0 < W) (_hresidues : ∀ r ∈ residues, r < W)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z)
    (hu : ∀ p ∈ P, ¬ p ∣ u)
    (hx : ∀ p ∈ P, ¬ p ∣ x)
    (hM : 2 ∣ M)
    (hPM : Nat.Coprime (∏ p ∈ P, p) M)
    (hWM : W ∣ M)
    (hprimes : ∀ p : ℕ, p.Prime →
      (p ∣ ∏ q ∈ P, q ↔ p ≤ z ∧ Nat.Coprime p M))
    (hupositive : 0 < u) :
    ((((Finset.range N).filter fun t =>
      t % W ∈ residues ∧ t.Prime ∧ (u * t - x).Prime).card) : ℝ) ≤
      (residues.card : ℝ) *
        (((N : ℝ) / (W : ℝ) + 1) /
          twoRootSelbergDenominator M z + (z : ℝ) ^ 4 +
            ((2 * Nat.primeCounting z : ℕ) : ℝ)) := by
  let shift := x / u + 1
  have hshift : x < u * shift := by
    have hquotient :=
      (Nat.div_lt_iff_lt_mul hupositive).mp (Nat.lt_succ_self (x / u))
    simpa [shift, Nat.mul_comm] using hquotient
  have hrotated :
      (affineShiftedSelectorResidues W shift residues).card ≤ residues.card :=
    affineShiftedSelectorResidues_card_le W shift residues hW
  have hselected := actualAffineSelected_prime_pair_card_le_density
    P (affineShiftedSelectorResidues W shift residues)
      M (N - shift) z W 1 shift u (u * shift - x)
      hW
      (fun r hr => Finset.mem_range.mp (Finset.mem_filter.mp hr).1)
      hprime hlarge hz
      (fun p hp hdiv => (hprime p hp).ne_one (Nat.dvd_one.mp hdiv))
      hu
      (fun p hp => by
        simpa using affine_shifted_negative_intercept_determinant
          p u shift x hshift.le (hx p hp))
      hM hPM hWM hprimes (by norm_num) hupositive
  rw [affineSelected_prime_difference_card_eq_shift N W u x residues
    hW hupositive]
  have hrotatedReal :
      ((affineShiftedSelectorResidues W shift residues).card : ℝ) ≤
        (residues.card : ℝ) := by
    exact_mod_cast hrotated
  have hendpoint : ((N - shift : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.sub_le N shift
  have hdenominator : 0 ≤ twoRootSelbergDenominator M z :=
    twoRootSelbergDenominator_nonneg hM z
  calc
    ((((Finset.range (N - shift)).filter fun k =>
      k % W ∈ affineShiftedSelectorResidues W shift residues ∧
        (1 * k + shift).Prime ∧
          (u * k + (u * shift - x)).Prime).card) : ℝ) ≤
      ((affineShiftedSelectorResidues W shift residues).card : ℝ) *
        ((((N - shift : ℕ) : ℝ) / (W : ℝ) + 1) /
          twoRootSelbergDenominator M z + (z : ℝ) ^ 4 +
            ((2 * Nat.primeCounting z : ℕ) : ℝ)) := hselected
    _ ≤ (residues.card : ℝ) *
        (((N : ℝ) / (W : ℝ) + 1) /
          twoRootSelbergDenominator M z + (z : ℝ) ^ 4 +
            ((2 * Nat.primeCounting z : ℕ) : ℝ)) := by
      gcongr

/-- The full optimized Selberg bound for the actual fixed-left manuscript
parameter set, retaining both true switched selectors, their `1 / W`
spacing, the negative-intercept translation, and the exceptional `q = 3`
case whenever the sieve excludes its moving determinant. -/
theorem leftFiberSwitchedPrimeParameters_card_le_selected_sieve
    (S P : Finset ℕ) (b : ℕ → ℕ) (M n z x d : ℕ)
    (hW : 0 < ∏ s ∈ S, s)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z)
    (hd : ∀ p ∈ P, ¬ p ∣ 2 * d)
    (hx : ∀ p ∈ P, ¬ p ∣ x)
    (hM : 2 ∣ M)
    (hPM : Nat.Coprime (∏ p ∈ P, p) M)
    (hWM : (∏ s ∈ S, s) ∣ M)
    (hprimes : ∀ p : ℕ, p.Prime →
      (p ∣ ∏ q ∈ P, q ↔ p ≤ z ∧ Nat.Coprime p M))
    (hdpositive : 0 < d) :
    ((leftFiberSwitchedPrimeParameters S b n x d).card : ℝ) ≤
      ((actualLeftFiberSelectorResidues S b x d).card : ℝ) *
        ((((n + 1 : ℕ) : ℝ) /
            (((∏ s ∈ S, s) : ℕ) : ℝ) + 1) /
              twoRootSelbergDenominator M z + (z : ℝ) ^ 4 +
                ((2 * Nat.primeCounting z : ℕ) : ℝ)) := by
  rw [leftFiberSwitchedPrimeParameters_eq_selected S b n x d hW]
  exact actualAffineSelected_prime_difference_card_le_density
    P (actualLeftFiberSelectorResidues S b x d)
      M (n + 1) z (∏ s ∈ S, s) (2 * d) x hW
      (fun r hr => Finset.mem_range.mp (Finset.mem_filter.mp hr).1)
      hprime hlarge hz hd hx hM hPM hWM hprimes (by omega)

#print axioms Erdos689.affine_progression_mem_iff
#print axioms Erdos689.affine_residue_parameters_eq_progression_image
#print axioms Erdos689.affine_residue_filter_card_eq_progression
#print axioms Erdos689.affine_progression_length_real_le
#print axioms Erdos689.affine_progression_affine_value
#print axioms Erdos689.affine_progression_slope_not_dvd
#print axioms Erdos689.affine_progression_determinant_nondegenerate
#print axioms Erdos689.affine_sieve_prime_not_dvd_progression_modulus
#print axioms Erdos689.affine_progression_prime_pair_card_eq
#print axioms Erdos689.actualAffineProgression_prime_pair_card_le_twoRootDenominator
#print axioms Erdos689.actualAffineProgression_prime_pair_card_le_density
#print axioms Erdos689.affine_selected_filter_card_eq_sum
#print axioms Erdos689.actualAffineSelected_prime_pair_card_le_density
#print axioms Erdos689.actualAffineSelected_prime_pairs_fifth_root_eventually_explicit
#print axioms Erdos689.switchedHits_mul_eq_of_support_residue
#print axioms Erdos689.leftFiberSwitched_selector_iff_mem_actual_residues
#print axioms Erdos689.rightFiberSwitched_selector_iff_mem_actual_residues
#print axioms Erdos689.leftFiberSwitchedPrimeParameters_eq_selected
#print axioms Erdos689.rightFiberSwitchedPrimeParameters_eq_selected
#print axioms Erdos689.affine_progression_descending_value
#print axioms Erdos689.affine_progression_mixed_prime_pair_card_eq
#print axioms Erdos689.affine_progression_mixed_determinant_nondegenerate
#print axioms Erdos689.actualMixedAffineProgression_prime_pair_card_le_twoRootDenominator
#print axioms Erdos689.actualMixedAffineProgression_prime_pair_card_le_density
#print axioms Erdos689.actualMixedAffineSelected_prime_pair_card_le_density
#print axioms Erdos689.rightFiberSwitchedPrimeParameters_eq_truncated_selected
#print axioms Erdos689.actualRightFiberTruncation_no_underflow
#print axioms Erdos689.rightFiberSwitchedPrimeParameters_card_le_selected_sieve
#print axioms Erdos689.affine_tail_filter_card_eq_shift
#print axioms Erdos689.affine_residue_translation_injective
#print axioms Erdos689.affineShiftedSelectorResidues_card_le
#print axioms Erdos689.affineShiftedSelectorResidues_mem_iff
#print axioms Erdos689.affine_prime_difference_threshold
#print axioms Erdos689.affine_shifted_negative_intercept_determinant
#print axioms Erdos689.affineSelected_prime_difference_card_eq_shift
#print axioms Erdos689.actualAffineSelected_prime_difference_card_le_density
#print axioms Erdos689.leftFiberSwitchedPrimeParameters_card_le_selected_sieve

end Erdos689
