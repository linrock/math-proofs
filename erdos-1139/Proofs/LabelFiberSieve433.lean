module

public import AffineProgressionSieve433

@[expose] public section


/-!
# Exact fixed-label manuscript fibers and their affine prime sieve

An actual fixed-label edge satisfies `2*d*r = a*q + z`.  For coprime
coefficients the first prime parameter belongs to one, not `2*d`, residue
class.  Its canonical progression converts the second prime exactly into a
positive affine form.  The actual two switched selectors remain attached to
the transformed parameter.
-/

open Finset
open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Erdos689

/-- All solutions of the fixed-label linear equation occupy the same genuine
residue class modulo `2*d` whenever the coefficient is invertible there. -/
theorem labelFiber_prime_parameter_unique_residue
    (a d z q q₀ : ℕ)
    (hcoprime : Nat.Coprime a (2 * d))
    (hq : 2 * d ∣ a * q + z)
    (hq₀ : 2 * d ∣ a * q₀ + z) :
    q % (2 * d) = q₀ % (2 * d) := by
  have hfirst : Nat.ModEq (2 * d) (a * q + z) 0 :=
    Nat.modEq_zero_iff_dvd.mpr hq
  have hsecond : Nat.ModEq (2 * d) (a * q₀ + z) 0 :=
    Nat.modEq_zero_iff_dvd.mpr hq₀
  have hsum : Nat.ModEq (2 * d) (a * q + z) (a * q₀ + z) :=
    hfirst.trans hsecond.symm
  have hproducts := Nat.ModEq.add_right_cancel' z hsum
  exact Nat.ModEq.cancel_left_of_coprime hcoprime.symm hproducts

/-- A canonical first-prime residue converts the exact linear equation into
two positive affine forms on the progression parameter. -/
theorem labelFiber_second_prime_progression_value
    (a d z q₀ r₀ k : ℕ)
    (hseed : 2 * d * r₀ = a * q₀ + z) :
    a * (q₀ + (2 * d) * k) + z =
      (2 * d) * (r₀ + a * k) := by
  calc
    a * (q₀ + (2 * d) * k) + z =
        (a * q₀ + z) + (2 * d) * (a * k) := by ring
    _ = (2 * d) * r₀ + (2 * d) * (a * k) := by rw [← hseed]
    _ = (2 * d) * (r₀ + a * k) := by ring

/-- The actual fixed-label switched selectors after the canonical
`q = q₀ + 2*d*k` substitution. -/
def actualLabelFiberProgressionSelectors
    (S : Finset ℕ) (b : ℕ → ℕ) (z a d q₀ k : ℕ) : Prop :=
  switchedHits S b (2 * a * (q₀ + 2 * d * k)) = 0 ∧
    switchedHits S b (2 * (a * (q₀ + 2 * d * k) + z)) = 0

/-- The true finite CRT selector set for the fixed-label progression
parameter, retaining both manuscript switched-hit predicates. -/
noncomputable def actualLabelFiberSelectorResidues
    (S : Finset ℕ) (b : ℕ → ℕ) (z a d q₀ : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (∏ s ∈ S, s)).filter fun k =>
    actualLabelFiberProgressionSelectors S b z a d q₀ k

/-- Any function with the same support-product residue has the same true
switched-hit count; unlike a symbolic selector, this uses the actual graph
definition. -/
theorem labelFiber_switchedHits_eq_of_support_mod
    (S : Finset ℕ) (b : ℕ → ℕ) (x y : ℕ)
    (hmod : x % (∏ s ∈ S, s) = y % (∏ s ∈ S, s)) :
    switchedHits S b x = switchedHits S b y := by
  have hleft := switchedHits_mul_eq_of_support_residue
    S b 1 x (x % (∏ s ∈ S, s)) rfl
  have hright := switchedHits_mul_eq_of_support_residue
    S b 1 y (y % (∏ s ∈ S, s)) rfl
  calc
    switchedHits S b x = switchedHits S b (x % (∏ s ∈ S, s)) := by
      simpa using hleft
    _ = switchedHits S b (y % (∏ s ∈ S, s)) := by rw [hmod]
    _ = switchedHits S b y := by simpa using hright.symm

/-- Both actual fixed-label switched selectors depend only on the canonical
progression-parameter residue modulo the switched support product. -/
theorem labelFiber_progression_selectors_iff_residue
    (S : Finset ℕ) (b : ℕ → ℕ) (z a d q₀ k : ℕ)
    (hW : 0 < ∏ s ∈ S, s) :
    actualLabelFiberProgressionSelectors S b z a d q₀ k ↔
      k % (∏ s ∈ S, s) ∈
        actualLabelFiberSelectorResidues S b z a d q₀ := by
  classical
  unfold actualLabelFiberSelectorResidues
  rw [Finset.mem_filter, Finset.mem_range]
  have hcanonical : k % (∏ s ∈ S, s) < ∏ s ∈ S, s :=
    Nat.mod_lt k hW
  let W := ∏ s ∈ S, s
  have hq :
      (q₀ + 2 * d * k) % W =
        (q₀ + 2 * d * (k % W)) % W := by
    simp [Nat.add_mod, Nat.mul_mod]
  have hfirst :
      (2 * a * (q₀ + 2 * d * k)) % W =
        (2 * a * (q₀ + 2 * d * (k % W))) % W := by
    simp [Nat.mul_mod, hq]
  have hsecond :
      (2 * (a * (q₀ + 2 * d * k) + z)) % W =
        (2 * (a * (q₀ + 2 * d * (k % W)) + z)) % W := by
    simp [Nat.mul_mod, Nat.add_mod, hq]
  have hfirstHits := labelFiber_switchedHits_eq_of_support_mod
    S b (2 * a * (q₀ + 2 * d * k))
      (2 * a * (q₀ + 2 * d * (k % W))) hfirst
  have hsecondHits := labelFiber_switchedHits_eq_of_support_mod
    S b (2 * (a * (q₀ + 2 * d * k) + z))
      (2 * (a * (q₀ + 2 * d * (k % W)) + z)) hsecond
  dsimp [W] at hfirstHits hsecondHits
  unfold actualLabelFiberProgressionSelectors
  simp [hcanonical, hfirstHits, hsecondHits]

/-- Every actual fixed-label solution has the unique explicit two-affine
parameter representation determined by one canonical seed solution. -/
theorem labelFiber_solution_eq_seed_progression
    (a d z q₀ r₀ q r : ℕ)
    (hd : 0 < d) (hq₀ : q₀ < 2 * d)
    (hcoprime : Nat.Coprime a (2 * d))
    (hseed : 2 * d * r₀ = a * q₀ + z)
    (hsolution : 2 * d * r = a * q + z) :
    q = q₀ + (2 * d) * (q / (2 * d)) ∧
      r = r₀ + a * (q / (2 * d)) := by
  have hqdiv : 2 * d ∣ a * q + z := hsolution ▸ dvd_mul_right _ _
  have hq₀div : 2 * d ∣ a * q₀ + z := hseed ▸ dvd_mul_right _ _
  have hresidue := labelFiber_prime_parameter_unique_residue
    a d z q q₀ hcoprime hqdiv hq₀div
  rw [Nat.mod_eq_of_lt hq₀] at hresidue
  have hfirst : q = q₀ + (2 * d) * (q / (2 * d)) := by
    simpa [hresidue] using (Nat.mod_add_div q (2 * d)).symm
  refine ⟨hfirst, ?_⟩
  have hvalue := labelFiber_second_prime_progression_value
    a d z q₀ r₀ (q / (2 * d)) hseed
  have heq : 2 * d * r = (2 * d) * (r₀ + a * (q / (2 * d))) := by
    calc
      2 * d * r = a * q + z := hsolution
      _ = a * (q₀ + (2 * d) * (q / (2 * d))) + z := by rw [← hfirst]
      _ = (2 * d) * (r₀ + a * (q / (2 * d))) := hvalue
  exact Nat.mul_left_cancel (by omega : 0 < 2 * d) heq

/-- Membership in the genuine fixed-label graph fiber exposes both exact
switched selectors and the witnessing second prime. -/
theorem mem_labelFiberSwitchedPrimeParameters_iff
    (S : Finset ℕ) (b : ℕ → ℕ) (n z a d q : ℕ) :
    q ∈ labelFiberSwitchedPrimeParameters S b n z a d ↔
      q ∈ Finset.Icc 1 n ∧ q.Prime ∧
        (∃ r ∈ Finset.Icc 1 n,
          r.Prime ∧ 2 * d * r = a * q + z) ∧
        switchedHits S b (2 * a * q) = 0 ∧
          switchedHits S b (2 * (a * q + z)) = 0 := by
  classical
  simp only [labelFiberSwitchedPrimeParameters,
    labelFiberPrimeParameters, Finset.mem_filter]
  tauto

/-- The exact actual fixed-label graph fiber injects into its one canonical
progression of positive affine prime pairs, retaining both genuine switched
selectors and the sharp `1/(2*d)` interval length. -/
theorem labelFiberSwitchedPrimeParameters_card_le_selected_progression
    (S : Finset ℕ) (b : ℕ → ℕ) (n z a d q₀ r₀ : ℕ)
    (hW : 0 < ∏ s ∈ S, s)
    (hd : 0 < d) (hq₀ : q₀ < 2 * d)
    (hcoprime : Nat.Coprime a (2 * d))
    (hseed : 2 * d * r₀ = a * q₀ + z) :
    (labelFiberSwitchedPrimeParameters S b n z a d).card ≤
      (((Finset.range (affineProgressionLength (n + 1) (2 * d) q₀)).filter
        fun k =>
          k % (∏ s ∈ S, s) ∈
            actualLabelFiberSelectorResidues S b z a d q₀ ∧
              ((2 * d) * k + q₀).Prime ∧ (a * k + r₀).Prime).card) := by
  classical
  let source := labelFiberSwitchedPrimeParameters S b n z a d
  let target :=
    (Finset.range (affineProgressionLength (n + 1) (2 * d) q₀)).filter
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
    obtain ⟨_, _, ⟨r, hrange, hrprime, hequation⟩, _, _⟩ :=
      (mem_labelFiberSwitchedPrimeParameters_iff S b n z a d q).mp hq
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
      obtain ⟨hqrange, hqprime, _, hfirst, hsecond⟩ :=
        (mem_labelFiberSwitchedPrimeParameters_iff S b n z a d q).mp hq
      obtain ⟨r, hrprime, hqrepr, hrrepr⟩ := hrepresentation q hq
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_, ?_, ?_, ?_⟩
      · apply (affine_progression_mem_iff
          (n + 1) (2 * d) q₀ (parameter q)
          (by omega) hq₀).mp
        have hupper := (Finset.mem_Icc.mp hqrange).2
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

/-- The determinant of the two canonical fixed-label affine prime forms is
exactly the actual moving prime label; excluding that label suffices. -/
theorem labelFiber_affine_determinant_nondegenerate
    (p a d z q₀ r₀ : ℕ)
    (hseed : 2 * d * r₀ = a * q₀ + z)
    (hz : ¬ p ∣ z) :
    ((2 * d : ℕ) : ZMod p) * (r₀ : ZMod p) ≠
      (a : ZMod p) * (q₀ : ZMod p) := by
  intro heq
  have hseedcast := congrArg (fun t : ℕ => (t : ZMod p)) hseed
  push_cast at hseedcast
  push_cast at heq
  have hzero : (z : ZMod p) = 0 := by
    linear_combination heq - hseedcast
  exact hz ((ZMod.natCast_eq_zero_iff z p).mp hzero)

/-- Complete optimized Selberg bound for the third, actual fixed-label
manuscript graph fiber.  The first prime occupies its single canonical
`2*d`-progression, both switched selectors survive modulo the support
product, and the leading numerator retains both genuine spacing factors. -/
theorem labelFiberSwitchedPrimeParameters_card_le_selected_sieve
    (S P : Finset ℕ) (b : ℕ → ℕ)
    (M n cutoff z a d q₀ r₀ : ℕ)
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
    ((labelFiberSwitchedPrimeParameters S b n z a d).card : ℝ) ≤
      ((actualLabelFiberSelectorResidues S b z a d q₀).card : ℝ) *
        (((affineProgressionLength (n + 1) (2 * d) q₀ : ℝ) /
            (((∏ s ∈ S, s) : ℕ) : ℝ) + 1) /
          twoRootSelbergDenominator M cutoff + (cutoff : ℝ) ^ 4 +
            ((2 * Nat.primeCounting cutoff : ℕ) : ℝ)) := by
  classical
  have hinjection := labelFiberSwitchedPrimeParameters_card_le_selected_progression
    S b n z a d q₀ r₀ hW hd hq₀ hcoprime hseed
  have hinjectionReal :
      ((labelFiberSwitchedPrimeParameters S b n z a d).card : ℝ) ≤
        ((((Finset.range (affineProgressionLength (n + 1) (2 * d) q₀)).filter
          fun k =>
            k % (∏ s ∈ S, s) ∈
              actualLabelFiberSelectorResidues S b z a d q₀ ∧
                ((2 * d) * k + q₀).Prime ∧ (a * k + r₀).Prime).card) : ℝ) := by
    exact_mod_cast hinjection
  exact hinjectionReal.trans
    (actualAffineSelected_prime_pair_card_le_density
      P (actualLabelFiberSelectorResidues S b z a d q₀)
      M (affineProgressionLength (n + 1) (2 * d) q₀)
      cutoff (∏ s ∈ S, s) (2 * d) q₀ a r₀ hW
      (fun r hr => Finset.mem_range.mp (Finset.mem_filter.mp hr).1)
      hprime hlarge hcutoff havoidd havoida
      (fun p hp => labelFiber_affine_determinant_nondegenerate
        p a d z q₀ r₀ hseed (havoidz p hp))
      hM hPM hWM hprimes (by omega) ha)


end Erdos689
