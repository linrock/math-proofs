import LabelDoubleCoefficient433

/-!
# Genuine support-unit refinement for the fixed-label prime sieve

The manuscript's existing progression selector only imposes the two
switched-hit conditions.  The three-state local coefficient calculation
also removes the classes where either affine prime parameter is divisible
by a support prime.  Such a parameter can only equal that support prime,
so the missing refinement costs at most twice the support cardinality.
-/

open Finset
open scoped BigOperators

namespace Erdos689

/-- An affine value is a support unit when no genuine support prime
divides it.  This formulation keeps the actual prime set explicit. -/
def affineSupportUnit (S : Finset ℕ) (u v k : ℕ) : Prop :=
  ∀ p ∈ S, ¬ p ∣ u * k + v

/-- Reducing an affine parameter modulo its full support product preserves
its actual support-unit condition, prime by prime. -/
theorem affineSupportUnit_iff_support_residue
    (S : Finset ℕ) (u v k : ℕ) :
    affineSupportUnit S u v (k % (∏ p ∈ S, p)) ↔
      affineSupportUnit S u v k := by
  unfold affineSupportUnit
  constructor
  · intro h p hp
    have hpW : p ∣ ∏ q ∈ S, q :=
      Finset.dvd_prod_of_mem (fun q : ℕ => q) hp
    have hparameter : (k % (∏ q ∈ S, q)) % p = k % p :=
      Nat.mod_mod_of_dvd k hpW
    have hvalue :
        (u * (k % (∏ q ∈ S, q)) + v) % p =
          (u * k + v) % p := by
      simp [Nat.add_mod, Nat.mul_mod, hparameter]
    intro hdiv
    apply h p hp
    apply Nat.dvd_iff_mod_eq_zero.mpr
    rw [hvalue]
    exact Nat.dvd_iff_mod_eq_zero.mp hdiv
  · intro h p hp
    have hpW : p ∣ ∏ q ∈ S, q :=
      Finset.dvd_prod_of_mem (fun q : ℕ => q) hp
    have hparameter : (k % (∏ q ∈ S, q)) % p = k % p :=
      Nat.mod_mod_of_dvd k hpW
    have hvalue :
        (u * (k % (∏ q ∈ S, q)) + v) % p =
          (u * k + v) % p := by
      simp [Nat.add_mod, Nat.mul_mod, hparameter]
    intro hdiv
    apply h p hp
    apply Nat.dvd_iff_mod_eq_zero.mpr
    rw [← hvalue]
    exact Nat.dvd_iff_mod_eq_zero.mp hdiv

/-- The actual fixed-label progression selector after requiring both
genuine affine prime values to be units at every switched support prime. -/
noncomputable def actualLabelFiberUnitSelectorResidues
    (S : Finset ℕ) (b : ℕ → ℕ) (z a d q₀ r₀ : ℕ) : Finset ℕ := by
  classical
  exact (actualLabelFiberSelectorResidues S b z a d q₀).filter fun k =>
    affineSupportUnit S (2 * d) q₀ k ∧
      affineSupportUnit S a r₀ k

/-- The unit-refined selector at the canonical support residue is exactly
the original selector plus the two genuine affine support-unit conditions. -/
theorem actualLabelFiberUnitSelectorResidues_mem_mod_iff
    (S : Finset ℕ) (b : ℕ → ℕ) (z a d q₀ r₀ k : ℕ) :
    k % (∏ p ∈ S, p) ∈
        actualLabelFiberUnitSelectorResidues S b z a d q₀ r₀ ↔
      k % (∏ p ∈ S, p) ∈
          actualLabelFiberSelectorResidues S b z a d q₀ ∧
        affineSupportUnit S (2 * d) q₀ k ∧
          affineSupportUnit S a r₀ k := by
  classical
  unfold actualLabelFiberUnitSelectorResidues
  rw [Finset.mem_filter,
    affineSupportUnit_iff_support_residue,
    affineSupportUnit_iff_support_residue]

/-- A genuine prime affine value failing the support-unit condition is
itself one of the finitely many actual support primes. -/
theorem affine_prime_mem_support_of_not_supportUnit
    (S : Finset ℕ) (u v k : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hprime : (u * k + v).Prime)
    (hnot : ¬ affineSupportUnit S u v k) :
    u * k + v ∈ S := by
  classical
  simp only [affineSupportUnit, not_forall, not_not] at hnot
  obtain ⟨p, hp, hdiv⟩ := hnot
  have heq : p = u * k + v :=
    (Nat.prime_dvd_prime_iff_eq (hsupport p hp) hprime).mp hdiv
  exact heq ▸ hp

/-- Refining the actual selected prime-pair progression to support units
loses at most `2*#S` genuine prime pairs, uniformly in its endpoint,
coefficient pair, seed, label, and switched assignment. -/
theorem actualLabelSelectedProgression_card_le_unit_refinement
    (S : Finset ℕ) (b : ℕ → ℕ)
    (N z a d q₀ r₀ : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (ha : 0 < a) (hd : 0 < d) :
    (((Finset.range N).filter fun k =>
      k % (∏ p ∈ S, p) ∈
          actualLabelFiberSelectorResidues S b z a d q₀ ∧
        ((2 * d) * k + q₀).Prime ∧ (a * k + r₀).Prime).card) ≤
      (((Finset.range N).filter fun k =>
        k % (∏ p ∈ S, p) ∈
            actualLabelFiberUnitSelectorResidues S b z a d q₀ r₀ ∧
          ((2 * d) * k + q₀).Prime ∧ (a * k + r₀).Prime).card) +
        2 * S.card := by
  classical
  let source := (Finset.range N).filter fun k =>
    k % (∏ p ∈ S, p) ∈
        actualLabelFiberSelectorResidues S b z a d q₀ ∧
      ((2 * d) * k + q₀).Prime ∧ (a * k + r₀).Prime
  let refined := (Finset.range N).filter fun k =>
    k % (∏ p ∈ S, p) ∈
        actualLabelFiberUnitSelectorResidues S b z a d q₀ r₀ ∧
      ((2 * d) * k + q₀).Prime ∧ (a * k + r₀).Prime
  let exceptions := affineValueParameters N (2 * d) q₀ S ∪
    affineValueParameters N a r₀ S
  have hsubset : source ⊆ refined ∪ exceptions := by
    intro k hk
    obtain ⟨hkN, hselector, hfirst, hsecond⟩ := Finset.mem_filter.mp hk
    by_cases hunitfirst : affineSupportUnit S (2 * d) q₀ k
    · by_cases hunitsecond : affineSupportUnit S a r₀ k
      · apply Finset.mem_union_left
        apply Finset.mem_filter.mpr
        exact ⟨hkN,
          (actualLabelFiberUnitSelectorResidues_mem_mod_iff
            S b z a d q₀ r₀ k).mpr
              ⟨hselector, hunitfirst, hunitsecond⟩,
          hfirst, hsecond⟩
      · apply Finset.mem_union_right
        apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        exact ⟨hkN, affine_prime_mem_support_of_not_supportUnit
          S a r₀ k hsupport hsecond hunitsecond⟩
    · apply Finset.mem_union_right
      apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      exact ⟨hkN, affine_prime_mem_support_of_not_supportUnit
        S (2 * d) q₀ k hsupport hfirst hunitfirst⟩
  have hcard := Finset.card_le_card hsubset
  have hunion := Finset.card_union_le refined exceptions
  have hexceptions : exceptions.card ≤ 2 * S.card := by
    calc
      exceptions.card ≤
          (affineValueParameters N (2 * d) q₀ S).card +
            (affineValueParameters N a r₀ S).card :=
        Finset.card_union_le _ _
      _ ≤ S.card + S.card := Nat.add_le_add
        (affineValueParameters_card_le N (2 * d) q₀ S (by omega))
        (affineValueParameters_card_le N a r₀ S ha)
      _ = 2 * S.card := by omega
  change source.card ≤ refined.card + 2 * S.card
  omega

/-- The actual fixed-label graph fiber injects into the genuinely
support-unit-refined canonical progression, up to its exact finite
`2*#S` support-prime exceptions. -/
theorem labelFiberSwitchedPrimeParameters_card_le_unit_selected_progression
    (S : Finset ℕ) (b : ℕ → ℕ) (n z a d q₀ r₀ : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hW : 0 < ∏ s ∈ S, s)
    (ha : 0 < a) (hd : 0 < d) (hq₀ : q₀ < 2 * d)
    (hcoprime : Nat.Coprime a (2 * d))
    (hseed : 2 * d * r₀ = a * q₀ + z) :
    (labelFiberSwitchedPrimeParameters S b n z a d).card ≤
      (((Finset.range (affineProgressionLength (n + 1) (2 * d) q₀)).filter
        fun k =>
          k % (∏ s ∈ S, s) ∈
              actualLabelFiberUnitSelectorResidues S b z a d q₀ r₀ ∧
            ((2 * d) * k + q₀).Prime ∧ (a * k + r₀).Prime).card) +
          2 * S.card := by
  have hinjection := labelFiberSwitchedPrimeParameters_card_le_selected_progression
    S b n z a d q₀ r₀ hW hd hq₀ hcoprime hseed
  have hrefinement := actualLabelSelectedProgression_card_le_unit_refinement
    S b (affineProgressionLength (n + 1) (2 * d) q₀)
    z a d q₀ r₀ hsupport ha hd
  omega

/-- The genuine manuscript left-endpoint bound, retained inside the
fixed-label coefficient fiber rather than discarded in an enlarged sum. -/
noncomputable def edgeBoundedLabelFiberSwitchedPrimeParameters
    (S : Finset ℕ) (b : ℕ → ℕ) (n z a d : ℕ) : Finset ℕ := by
  classical
  exact (labelFiberSwitchedPrimeParameters S b n z a d).filter fun q =>
    2 * a * q ≤ n

/-- The genuine edge-bounded fixed-label coefficient fiber injects into a
canonical progression of length `floor(n/(2*a))/(2*d)`, retaining the
previously lost `1/a` factor and both actual switched selectors. -/
theorem edgeBoundedLabelFiber_card_le_selected_progression
    (S : Finset ℕ) (b : ℕ → ℕ) (n z a d q₀ r₀ : ℕ)
    (hW : 0 < ∏ s ∈ S, s)
    (ha : 0 < a) (hd : 0 < d) (hq₀ : q₀ < 2 * d)
    (hcoprime : Nat.Coprime a (2 * d))
    (hseed : 2 * d * r₀ = a * q₀ + z) :
    (edgeBoundedLabelFiberSwitchedPrimeParameters S b n z a d).card ≤
      (((Finset.range
          (affineProgressionLength (n / (2 * a) + 1) (2 * d) q₀)).filter
        fun k =>
          k % (∏ s ∈ S, s) ∈
              actualLabelFiberSelectorResidues S b z a d q₀ ∧
            ((2 * d) * k + q₀).Prime ∧ (a * k + r₀).Prime).card) := by
  classical
  let source := edgeBoundedLabelFiberSwitchedPrimeParameters S b n z a d
  let target :=
    (Finset.range
      (affineProgressionLength (n / (2 * a) + 1) (2 * d) q₀)).filter
        fun k =>
          k % (∏ s ∈ S, s) ∈
              actualLabelFiberSelectorResidues S b z a d q₀ ∧
            ((2 * d) * k + q₀).Prime ∧ (a * k + r₀).Prime
  let parameter : ℕ → ℕ := fun q => q / (2 * d)
  have hrepresentation : ∀ q ∈ source,
      ∃ r : ℕ, r.Prime ∧
        q = q₀ + (2 * d) * parameter q ∧
        r = r₀ + a * parameter q := by
    intro q hq
    have hmember : q ∈ labelFiberSwitchedPrimeParameters S b n z a d :=
      (Finset.mem_filter.mp hq).1
    obtain ⟨_, _, ⟨r, _, hrprime, hequation⟩, _, _⟩ :=
      (mem_labelFiberSwitchedPrimeParameters_iff S b n z a d q).mp hmember
    obtain ⟨hqrepr, hrrepr⟩ :=
      labelFiber_solution_eq_seed_progression
        a d z q₀ r₀ q r hd hq₀ hcoprime hseed hequation
    exact ⟨r, hrprime, hqrepr, hrrepr⟩
  have hinjective : Set.InjOn parameter (↑source : Set ℕ) := by
    intro q hq q' hq' heq
    obtain ⟨r, _, hrepr, _⟩ :=
      hrepresentation q (Finset.mem_coe.mp hq)
    obtain ⟨r', _, hrepr', _⟩ :=
      hrepresentation q' (Finset.mem_coe.mp hq')
    rw [hrepr, hrepr', heq]
  calc
    source.card = (source.image parameter).card :=
      (Finset.card_image_iff.mpr hinjective).symm
    _ ≤ target.card := by
      apply Finset.card_le_card
      intro k hk
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hqoriginal, hqbound⟩ := Finset.mem_filter.mp hq
      obtain ⟨_, hqprime, _, hfirst, hsecond⟩ :=
        (mem_labelFiberSwitchedPrimeParameters_iff S b n z a d q).mp hqoriginal
      obtain ⟨r, hrprime, hqrepr, hrrepr⟩ := hrepresentation q hq
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_, ?_, ?_, ?_⟩
      · apply (affine_progression_mem_iff
          (n / (2 * a) + 1) (2 * d) q₀ (parameter q)
          (by omega) hq₀).mp
        have hqa : q ≤ n / (2 * a) := by
          apply (Nat.le_div_iff_mul_le (by omega : 0 < 2 * a)).mpr
          nlinarith
        omega
      · apply (labelFiber_progression_selectors_iff_residue
          S b z a d q₀ (parameter q) hW).mp
        unfold actualLabelFiberProgressionSelectors
        rw [← hqrepr]
        exact ⟨hfirst, hsecond⟩
      · have hvalue : (2 * d) * parameter q + q₀ = q := by omega
        rw [hvalue]
        exact hqprime
      · have hvalue : a * parameter q + r₀ = r := by omega
        rw [hvalue]
        exact hrprime

/-- The genuinely edge-bounded label fiber has both indispensable analytic
corrections simultaneously: sharp `1/(a*d)` progression spacing and the
support-unit selector, with at most `2*#S` actual prime exceptions. -/
theorem edgeBoundedLabelFiber_card_le_unit_selected_progression
    (S : Finset ℕ) (b : ℕ → ℕ) (n z a d q₀ r₀ : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hW : 0 < ∏ s ∈ S, s)
    (ha : 0 < a) (hd : 0 < d) (hq₀ : q₀ < 2 * d)
    (hcoprime : Nat.Coprime a (2 * d))
    (hseed : 2 * d * r₀ = a * q₀ + z) :
    (edgeBoundedLabelFiberSwitchedPrimeParameters S b n z a d).card ≤
      (((Finset.range
          (affineProgressionLength (n / (2 * a) + 1) (2 * d) q₀)).filter
        fun k =>
          k % (∏ s ∈ S, s) ∈
              actualLabelFiberUnitSelectorResidues S b z a d q₀ r₀ ∧
            ((2 * d) * k + q₀).Prime ∧ (a * k + r₀).Prime).card) +
          2 * S.card := by
  have hinjection := edgeBoundedLabelFiber_card_le_selected_progression
    S b n z a d q₀ r₀ hW ha hd hq₀ hcoprime hseed
  have hrefinement := actualLabelSelectedProgression_card_le_unit_refinement
    S b (affineProgressionLength (n / (2 * a) + 1) (2 * d) q₀)
    z a d q₀ r₀ hsupport ha hd
  omega

/-- Complete optimized Selberg bound for an *actual edge-bounded* fixed
label fiber, with both indispensable corrections present: exact
`floor(n/(2*a))` progression endpoint and support-unit selector density.
All genuine support-prime-value exceptions are retained explicitly. -/
theorem edgeBoundedLabelFiber_card_le_unit_selected_sieve
    (S P : Finset ℕ) (b : ℕ → ℕ)
    (M n cutoff z a d q₀ r₀ : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hW : 0 < ∏ s ∈ S, s)
    (hd : 0 < d) (ha : 0 < a) (hq₀ : q₀ < 2 * d)
    (hcoprime : Nat.Coprime a (2 * d))
    (hseed : 2 * d * r₀ = a * q₀ + z)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hcutoff : 0 < cutoff)
    (havoidd : ∀ p ∈ P, ¬ p ∣ 2 * d)
    (havoida : ∀ p ∈ P, ¬ p ∣ a)
    (havoidz : ∀ p ∈ P, ¬ p ∣ z)
    (hM : 2 ∣ M)
    (hPM : Nat.Coprime (∏ p ∈ P, p) M)
    (hWM : (∏ s ∈ S, s) ∣ M)
    (hprimes : ∀ p : ℕ, p.Prime →
      (p ∣ ∏ q ∈ P, q ↔ p ≤ cutoff ∧ Nat.Coprime p M)) :
    ((edgeBoundedLabelFiberSwitchedPrimeParameters S b n z a d).card : ℝ) ≤
      ((actualLabelFiberUnitSelectorResidues S b z a d q₀ r₀).card : ℝ) *
        (((affineProgressionLength
            (n / (2 * a) + 1) (2 * d) q₀ : ℝ) /
            (((∏ s ∈ S, s) : ℕ) : ℝ) + 1) /
          twoRootSelbergDenominator M cutoff + (cutoff : ℝ) ^ 4 +
            ((2 * Nat.primeCounting cutoff : ℕ) : ℝ)) +
        ((2 * S.card : ℕ) : ℝ) := by
  classical
  let N := affineProgressionLength (n / (2 * a) + 1) (2 * d) q₀
  let T := actualLabelFiberUnitSelectorResidues S b z a d q₀ r₀
  have hrefinement := edgeBoundedLabelFiber_card_le_unit_selected_progression
    S b n z a d q₀ r₀ hsupport hW ha hd hq₀ hcoprime hseed
  have hreal :
      ((edgeBoundedLabelFiberSwitchedPrimeParameters S b n z a d).card : ℝ) ≤
        ((((Finset.range N).filter fun k =>
          k % (∏ s ∈ S, s) ∈ T ∧
            ((2 * d) * k + q₀).Prime ∧ (a * k + r₀).Prime).card) : ℝ) +
          ((2 * S.card : ℕ) : ℝ) := by
    exact_mod_cast hrefinement
  have hselected := actualAffineSelected_prime_pair_card_le_density
    P T M N cutoff (∏ s ∈ S, s) (2 * d) q₀ a r₀ hW
      (by
        intro r hr
        have hold := (Finset.mem_filter.mp hr).1
        exact Finset.mem_range.mp (Finset.mem_filter.mp hold).1)
      hprime hlarge hcutoff havoidd havoida
      (fun p hp => labelFiber_affine_determinant_nondegenerate
        p a d z q₀ r₀ hseed (havoidz p hp))
      hM hPM hWM hprimes (by omega) ha
  change
    ((edgeBoundedLabelFiberSwitchedPrimeParameters S b n z a d).card : ℝ) ≤
      (T.card : ℝ) *
        (((N : ℝ) / (((∏ s ∈ S, s) : ℕ) : ℝ) + 1) /
          twoRootSelbergDenominator M cutoff + (cutoff : ℝ) ^ 4 +
            ((2 * Nat.primeCounting cutoff : ℕ) : ℝ)) +
        ((2 * S.card : ℕ) : ℝ)
  linarith

#print axioms Erdos689.affineSupportUnit_iff_support_residue
#print axioms Erdos689.actualLabelFiberUnitSelectorResidues_mem_mod_iff
#print axioms Erdos689.affine_prime_mem_support_of_not_supportUnit
#print axioms Erdos689.actualLabelSelectedProgression_card_le_unit_refinement
#print axioms Erdos689.labelFiberSwitchedPrimeParameters_card_le_unit_selected_progression
#print axioms Erdos689.edgeBoundedLabelFiber_card_le_selected_progression
#print axioms Erdos689.edgeBoundedLabelFiber_card_le_unit_selected_progression
#print axioms Erdos689.edgeBoundedLabelFiber_card_le_unit_selected_sieve

end Erdos689
