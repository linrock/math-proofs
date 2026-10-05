module

public import AnalyticScalarCapacity433
public import ProtectedReserveOmission1139

@[expose] public section


/-!
# Exact logarithmic savings from omitted protected Erdős #689 primes

Unused canonical protected primes can be deleted from the double covering.
This file charges the resulting exact prime conductor and proves a quantitative
lower bound for every omitted prime from its genuine canonical-reserve cutoff.

No positive-density reserve surplus is assumed as an axiom or proved here.
-/

open Finset Filter
open scoped ArithmeticFunction.Omega Topology

namespace Erdos689

/-- Every genuine protected reserve prime lies in the original full prime
support, so it can be removed by an exact finite-set difference. -/
theorem protectedReserve_subset_full_prime_support
    {n : ℕ} {a : ℕ → ℕ} {unused : Finset ℕ}
    (hreserve : protectedReserve n a unused) :
    unused ⊆ (Finset.Icc 1 n).filter Nat.Prime := by
  intro p hp
  obtain ⟨hprime, hbound, _⟩ := hreserve p hp
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hprime.one_le, hbound⟩, hprime⟩

/-- Exact multiplicative primorial ledger: the pruned genuine conductor times
the actual product of all omitted protected primes is the full primorial. -/
theorem prunedPrimeSupport_prod_mul_unused_eq_primorial
    {n : ℕ} {a : ℕ → ℕ} {unused : Finset ℕ}
    (hreserve : protectedReserve n a unused) :
    (∏ p ∈ prunedPrimeSupport n unused, p) *
        (∏ p ∈ unused, p) = primorial n := by
  rw [← Erdos1139.closed_prime_product_eq_primorial n]
  exact Finset.prod_sdiff
    (f := fun p : ℕ => p)
    (protectedReserve_subset_full_prime_support hreserve)

/-- Every canonical reserve prime satisfies its original strict cutoff.
No artificial lower prime window is substituted for the actual definition. -/
theorem canonicalReserve_prime_cutoff
    {S : Finset ℕ} {b : ℕ → ℕ} {n J p : ℕ}
    (hp : p ∈ canonicalReserve S b n J) :
    n < (J + 1) * p := by
  classical
  exact (Finset.mem_filter.mp hp).2.2.2.2.2

/-- Taking logarithms of the genuine canonical cutoff gives the exact fixed
parameter loss log(J+1) for each omitted protected prime. -/
theorem canonicalReserve_log_prime_lower
    {S : Finset ℕ} {b : ℕ → ℕ} {n J p : ℕ}
    (hn : 0 < n) (hp : p ∈ canonicalReserve S b n J) :
    Real.log (n : ℝ) - Real.log (((J + 1 : ℕ) : ℝ)) <
      Real.log (p : ℝ) := by
  classical
  have hprime : p.Prime := (Finset.mem_filter.mp hp).2.1
  have hcutoff := canonicalReserve_prime_cutoff hp
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hJreal : 0 < (((J + 1 : ℕ) : ℝ)) := by positivity
  have hpreal : 0 < (p : ℝ) := by exact_mod_cast hprime.pos
  have hcast :
      (n : ℝ) < (((J + 1 : ℕ) : ℝ)) * (p : ℝ) := by
    exact_mod_cast hcutoff
  have hlog := Real.strictMonoOn_log hnreal (mul_pos hJreal hpreal) hcast
  rw [Real.log_mul hJreal.ne' hpreal.ne'] at hlog
  linarith

/-- Product of omitted canonical reserve primes gains the full sum of its
individual logarithms, with no hidden collisions or density heuristic. -/
theorem canonicalReserve_unused_log_product_lower
    {S : Finset ℕ} {b : ℕ → ℕ} {n J : ℕ} {unused : Finset ℕ}
    (hn : 0 < n)
    (hsubset : unused ⊆ canonicalReserve S b n J) :
    (unused.card : ℝ) *
        (Real.log (n : ℝ) - Real.log (((J + 1 : ℕ) : ℝ))) ≤
      Real.log ((∏ p ∈ unused, p : ℕ) : ℝ) := by
  classical
  have hnonzero : ∀ p ∈ unused, (p : ℝ) ≠ 0 := by
    intro p hp
    have hprime := (Finset.mem_filter.mp (hsubset hp)).2.1
    exact_mod_cast hprime.ne_zero
  calc
    (unused.card : ℝ) *
        (Real.log (n : ℝ) - Real.log (((J + 1 : ℕ) : ℝ))) =
        ∑ _p ∈ unused,
          (Real.log (n : ℝ) - Real.log (((J + 1 : ℕ) : ℝ))) := by
            simp [mul_sub]
    _ ≤ ∑ p ∈ unused, Real.log (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact (canonicalReserve_log_prime_lower hn (hsubset hp)).le
    _ = Real.log (∏ p ∈ unused, (p : ℝ)) :=
      (Real.log_prod hnonzero).symm
    _ = Real.log ((∏ p ∈ unused, p : ℕ) : ℝ) := by simp

end Erdos689

namespace Erdos1139

/-- The exact #1139 mixed conductor of the pruned prime-only support is its
ordinary prime product; no squares or discarded moduli are charged. -/
theorem pruned_empty_square_conductor_eq
    (n : ℕ) (unused : Finset ℕ) :
    (∏ p ∈ Erdos689.prunedPrimeSupport n unused,
      selectedPrimePower ∅ p) =
        ∏ p ∈ Erdos689.prunedPrimeSupport n unused, p := by
  simp [selectedPrimePower, selectedPrimeExponent]

/-- Exact logarithmic conductor identity after deleting every unused protected
prime from the original #689 support. -/
theorem pruned_conductor_log_eq_primorial_sub_unused
    {n : ℕ} {a : ℕ → ℕ} {unused : Finset ℕ}
    (hreserve : Erdos689.protectedReserve n a unused) :
    Real.log
        ((∏ p ∈ Erdos689.prunedPrimeSupport n unused,
          selectedPrimePower ∅ p : ℕ) : ℝ) =
      Real.log (primorial n : ℝ) -
        Real.log ((∏ p ∈ unused, p : ℕ) : ℝ) := by
  let Q : ℕ := ∏ p ∈ Erdos689.prunedPrimeSupport n unused, p
  let U : ℕ := ∏ p ∈ unused, p
  have hQpositive : 0 < Q := by
    dsimp [Q]
    apply Finset.prod_pos
    intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2.pos
  have hUpositive : 0 < U := by
    dsimp [U]
    apply Finset.prod_pos
    intro p hp
    exact (hreserve p hp).1.pos
  have hQreal : 0 < (Q : ℝ) := by exact_mod_cast hQpositive
  have hUreal : 0 < (U : ℝ) := by exact_mod_cast hUpositive
  have hfactor := Erdos689.prunedPrimeSupport_prod_mul_unused_eq_primorial
    hreserve
  have hlog :
      Real.log (primorial n : ℝ) =
        Real.log (Q : ℝ) + Real.log (U : ℝ) := by
    rw [← hfactor]
    change Real.log ((Q * U : ℕ) : ℝ) = _
    push_cast
    exact Real.log_mul hQreal.ne' hUreal.ne'
  rw [pruned_empty_square_conductor_eq]
  change Real.log (Q : ℝ) =
    Real.log (primorial n : ℝ) - Real.log (U : ℝ)
  linarith

/-- Sharp deterministic saving from a canonical protected reserve: every
omitted prime saves at least log n minus log(J+1) from the exact conductor. -/
theorem pruned_conductor_log_le_primorial_sub_card
    {S : Finset ℕ} {b a : ℕ → ℕ} {n J : ℕ} {unused : Finset ℕ}
    (hn : 0 < n)
    (hreserve : Erdos689.protectedReserve n a unused)
    (hsubset : unused ⊆ Erdos689.canonicalReserve S b n J) :
    Real.log
        ((∏ p ∈ Erdos689.prunedPrimeSupport n unused,
          selectedPrimePower ∅ p : ℕ) : ℝ) ≤
      Real.log (primorial n : ℝ) -
        (unused.card : ℝ) *
          (Real.log (n : ℝ) - Real.log (((J + 1 : ℕ) : ℝ))) := by
  rw [pruned_conductor_log_eq_primorial_sub_unused hreserve]
  exact sub_le_sub_left
    (Erdos689.canonicalReserve_unused_log_product_lower hn hsubset) _

/-- A genuine positive density of omitted canonical reserve primes produces a
strictly subprimorial conductor.  The integer floor from the actual #689
matching ledger is absorbed using the already proved divergence of `n/log n`;
the fixed canonical cutoff loses only `log (J+1)` per omitted prime.  The
estimate is uniform in every final assignment and omitted protected set. -/
theorem eventually_pruned_conductor_linear_saving
    (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ)
    (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (a : ℕ → ℕ) (unused : Finset ℕ),
        Erdos689.protectedReserve n a unused →
        unused ⊆ Erdos689.canonicalReserve S b n J →
        ⌊γ * ((n : ℝ) / Real.log n)⌋₊ ≤ unused.card →
        Real.log
            ((∏ p ∈ Erdos689.prunedPrimeSupport n unused,
              selectedPrimePower ∅ p : ℕ) : ℝ) ≤
          (1 - γ / 8) * (n : ℝ) := by
  have hlogtop :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hcutoff : ∀ᶠ n : ℕ in atTop,
      2 * Real.log (((J + 1 : ℕ) : ℝ)) ≤ Real.log (n : ℝ) :=
    (tendsto_atTop.1 hlogtop)
      (2 * Real.log (((J + 1 : ℕ) : ℝ)))
  have hpnt : ∀ᶠ n : ℕ in atTop,
      Real.log (primorial n : ℝ) / (n : ℝ) < 1 + γ / 8 :=
    original_primorial_log_div_length_tendsto_one.eventually
      (Iio_mem_nhds (by linarith))
  have hscale := Erdos689.eventually_logarithmic_scale_dominates_one
    (γ / 2) (by positivity) 1
  filter_upwards [hcutoff, hpnt, hscale, eventually_ge_atTop 2]
      with n hcutoff_n hpnt_n hscale_n hn
  intro a unused hreserve hsubset hcard
  have hnpositive : 0 < n := by omega
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpositive
  have hnlarge : (1 : ℝ) < n := by exact_mod_cast hn
  have hlogpositive : 0 < Real.log (n : ℝ) := Real.log_pos hnlarge
  let X : ℝ := (n : ℝ) / Real.log (n : ℝ)
  have hXpositive : 0 < X := by dsimp [X]; positivity
  have hscaled : (1 : ℝ) ≤ (γ / 2) * X := by
    simpa [X] using hscale_n
  have hfloor := Nat.lt_floor_add_one (γ * X)
  have hcardreal :
      ((⌊γ * X⌋₊ : ℕ) : ℝ) ≤ (unused.card : ℝ) := by
    exact_mod_cast hcard
  have hcardlower : (γ / 2) * X ≤ (unused.card : ℝ) := by
    linarith
  have hgap :
      (1 / 2 : ℝ) * Real.log (n : ℝ) ≤
        Real.log (n : ℝ) - Real.log (((J + 1 : ℕ) : ℝ)) := by
    linarith
  have hsaving :
      (γ / 4) * (n : ℝ) ≤
        (unused.card : ℝ) *
          (Real.log (n : ℝ) - Real.log (((J + 1 : ℕ) : ℝ))) := by
    calc
      (γ / 4) * (n : ℝ) =
          ((γ / 2) * X) * ((1 / 2 : ℝ) * Real.log (n : ℝ)) := by
            dsimp [X]
            field_simp [hlogpositive.ne']
            ring
      _ ≤ (unused.card : ℝ) * ((1 / 2 : ℝ) * Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hcardlower (by positivity)
      _ ≤ (unused.card : ℝ) *
          (Real.log (n : ℝ) - Real.log (((J + 1 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hgap (by positivity)
  have hpnt_bound :
      Real.log (primorial n : ℝ) < (1 + γ / 8) * (n : ℝ) :=
    (div_lt_iff₀ hnreal).mp hpnt_n
  have hconductor :=
    pruned_conductor_log_le_primorial_sub_card hnpositive hreserve hsubset
  nlinarith


end Erdos1139
