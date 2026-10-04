module

public import ActualLeftVertexSummed433
public import ActualRightVertexLeftAuditErrors433

@[expose] public section


/-!
# Unconditional original fixed-left graph degree and complete degree closure

Every actual fixed left vertex is `x = a*r`, with `a` a support divisor and
`r` prime.  The fixed excluded modulus `6*W` together with one canonical
moving outside prime avoids this entire determinant, including the genuine
`r=3` and support-prime branches.  The exact sharp selector-summed main
constant is `1815/4`; all genuine errors are uniformly negligible.  Thus
every actual fixed-left graph degree is eventually at most
`455*n/log(n)^2`.  Combining the independently proved right and label
coordinates discharges the full original graph-degree proposition outright.
-/

open Filter
open scoped BigOperators Topology

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Erdos689

/-- Every genuine fixed-left graph fiber injects into the union of the
ACTUAL edge-bounded parameter fibers, each retaining `4*d*q ≤ n`. -/
theorem manuscriptEdge_left_fiber_card_le_edgeBoundedLeft_parameter_sum
    {S : Finset ℕ} {b : ℕ → ℕ} {n : ℕ} {τ ell : ℝ}
    (E : Finset TripleEdge) (x : ℕ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hactual : ∀ e ∈ E, manuscriptEdge S b n τ ell e) :
    (E.filter fun e => e.1 = x).card ≤
      ∑ d ∈ (∏ s ∈ S, s).divisors,
        (edgeBoundedLeftVertexPrimeParameters S b n x d).card := by
  classical
  let W := ∏ s ∈ S, s
  let fiber := E.filter fun e => e.1 = x
  let parameterVertices : ℕ → Finset ℕ := fun d =>
    (edgeBoundedLeftVertexPrimeParameters S b n x d).image
      (fun q => 2 * d * q)
  have hW : 0 < W := Finset.prod_pos fun s hs => (hsupport s hs).pos
  have hinjective := manuscriptEdge_right_injective_on_left_fiber E x hactual
  have hsubset : fiber.image (fun e : TripleEdge => e.2.1) ⊆
      W.divisors.biUnion parameterVertices := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨heE, hex⟩ := Finset.mem_filter.mp he
    obtain ⟨hlabelprime, hrelation, _, hrightbound, hleftmiss,
      hrightmiss, _, _, _, ⟨d, q, hd, hq, hrepr⟩⟩ := hactual e heE
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hW
    have hqright : q ≤ e.2.1 := by
      rw [hrepr]
      simpa [mul_assoc] using
        (Nat.le_mul_of_pos_left q (Nat.mul_pos (by norm_num) hdpos))
    have hqn : q ≤ n := by omega
    have hlabel : 2 * d * q - x = e.2.2 := by omega
    have hrighttarget : 2 * e.2.1 = 4 * d * q := by
      rw [hrepr]
      ring
    rw [hex] at hleftmiss
    rw [hrighttarget] at hrightmiss
    apply Finset.mem_biUnion.mpr
    refine ⟨d, Nat.mem_divisors.mpr ⟨hd, Nat.ne_of_gt hW⟩, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨q, Finset.mem_filter.mpr ?_, hrepr.symm⟩
    refine ⟨Finset.mem_filter.mpr ?_, ?_⟩
    · exact ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hq.one_le, hqn⟩,
          hq, hlabel.symm ▸ hlabelprime⟩, hleftmiss, hrightmiss⟩
    · omega
  calc
    fiber.card = (fiber.image fun e : TripleEdge => e.2.1).card :=
      (Finset.card_image_iff.mpr hinjective).symm
    _ ≤ (W.divisors.biUnion parameterVertices).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ d ∈ W.divisors, (parameterVertices d).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ d ∈ W.divisors,
        (edgeBoundedLeftVertexPrimeParameters S b n x d).card := by
      apply Finset.sum_le_sum
      intro d _
      exact Finset.card_image_le

/-- The complete ACTUAL fixed-left support-divisor fiber sum is eventually
at most `455*n/log(n)^2` for every genuine determinant `x=a*r`, uniformly
in every prime `r`, including `r=3` and all support-prime cases. -/
theorem actualLeftVertex_canonical_sieve_fiber_sum_eventually_le
    (S : Finset ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hb : ∀ p ∈ S, ¬ p ∣ b p) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ x a r : ℕ,
        a ∣ ∏ p ∈ S, p → r.Prime → x = a * r →
        (∀ p ∈ S,
          (2 : ZMod p) * (x : ZMod p) ≠ (b p : ZMod p)) →
        (∑ d ∈ (∏ p ∈ S, p).divisors,
          ((edgeBoundedLeftVertexPrimeParameters S b n x d).card : ℝ)) ≤
          (455 : ℝ) *
            ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
  filter_upwards
    [actualLeftMoving_fixedModulus_main_term_eventually_le S hsupport,
      actualLeftMoving_fixedModulus_errors_eventually_lt_scale S hsupport,
      eventually_ge_atTop 2] with n hmain herror hn
  intro x a r ha hr hx hfixed
  let W : ℕ := ∏ p ∈ S, p
  let q := actualLeftMovingExcludedPrime S r
  let M := (6 * W) * q
  let R := selbergSquareRootBlockCutoff n ^ 2
  let P := actualLeftCanonicalMovingSievePrimes S n r
  have hnpositive : 0 < n := by omega
  have hcutoff : 0 < R :=
    selbergSquareRootBlockCutoff_sq_pos_of_pos n hnpositive
  have hM : 2 ∣ M := by
    dsimp [M]
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left (by norm_num : 2 ∣ 6) W) q
  have hWM : W ∣ M := by
    refine ⟨6 * q, ?_⟩
    dsimp [M]
    ring
  have havoidx : ∀ p ∈ P, ¬ p ∣ x := by
    intro p hp
    rw [hx]
    exact actualLeftCanonicalMovingSievePrimes_avoid_determinant
      S n r a p ha hp
  have hfinite := actualLeftVertexFiber_sum_le_sharp_main_and_errors
    S P b n x M R hsupport hb hfixed
      (fun p hp => actualLeftCanonicalMovingSievePrimes_prime S n r p hp)
      (fun p hp => actualLeftCanonicalMovingSievePrimes_gt_two S n r p hp)
      hcutoff havoidx hM
      (actualLeftCanonicalMovingSievePrimes_product_coprime S n r)
      hWM
      (fun p hp => actualLeftCanonicalMovingSievePrimes_dvd_product_iff
        S n r p hp)
  have hmain' := hmain r hr
  have herror' := herror r hr
  have hscale : 0 ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by positivity
  change
    (∑ d ∈ W.divisors,
      ((edgeBoundedLeftVertexPrimeParameters S b n x d).card : ℝ)) ≤
        (455 : ℝ) * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2)
  change
    (∑ d ∈ W.divisors,
      ((edgeBoundedLeftVertexPrimeParameters S b n x d).card : ℝ)) ≤
      (n : ℝ) * (W.totient : ℝ) ^ 2 /
        (4 * (W : ℝ) ^ 2 * twoRootSelbergDenominator M R) +
      (W.divisors.card : ℝ) *
        ((W : ℝ) *
          (2 / twoRootSelbergDenominator M R + (R : ℝ) ^ 4 +
            ((2 * Nat.primeCounting R : ℕ) : ℝ)) +
          ((2 * S.card : ℕ) : ℝ)) at hfinite
  change
    (n : ℝ) * (W.totient : ℝ) ^ 2 /
      (4 * (W : ℝ) ^ 2 * twoRootSelbergDenominator M R) ≤
      (1815 / 4 : ℝ) * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) at hmain'
  change
    (W.divisors.card : ℝ) *
      ((W : ℝ) *
        (2 / twoRootSelbergDenominator M R +
          ((R : ℝ) ^ 4 +
            ((2 * Nat.primeCounting R : ℕ) : ℝ))) +
        ((2 * S.card : ℕ) : ℝ)) <
      (n : ℝ) / (Real.log (n : ℝ)) ^ 2 at herror'
  nlinarith

/-- The genuine fixed-left coordinate of the ORIGINAL manuscript graph
degree estimate is proved unconditionally with absolute constant `455`:
eventually every actual finite edge family and every left vertex satisfy
the bound, with no sieve, selector, determinant, or degree assumptions. -/
theorem manuscriptEdge_actual_left_degree_eventually_le
    (S : Finset ℕ) (b : ℕ → ℕ) (τ ell : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hb : ∀ p ∈ S, ¬ p ∣ b p) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ E : Finset TripleEdge,
        (∀ e ∈ E, manuscriptEdge S b n τ ell e) →
          ∀ x : ℕ,
            (((E.filter fun e => e.1 = x).card : ℕ) : ℝ) ≤
              (455 : ℝ) *
                ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
  filter_upwards
    [actualLeftVertex_canonical_sieve_fiber_sum_eventually_le
      S b hsupport hb] with n hbound
  intro E hactual x
  by_cases hnonempty : (E.filter fun e => e.1 = x).Nonempty
  · obtain ⟨e, he⟩ := hnonempty
    obtain ⟨heE, hex⟩ := Finset.mem_filter.mp he
    obtain ⟨_, _, _, _, hleftmiss, _, _, _,
      ⟨a, r, ha, hr, hrepr⟩, _⟩ := hactual e heE
    have hx : x = a * r := by omega
    rw [hex] at hleftmiss
    have hnot :=
      (switchedHits_zero_iff_forall_not_modEq S b (2 * x)).mp hleftmiss
    have hfixed : ∀ p ∈ S,
        (2 : ZMod p) * (x : ZMod p) ≠ (b p : ZMod p) := by
      intro p hp
      exact (zmod_switched_target_ne_iff_not_modEq p (b p) x).mpr
        (hnot p hp)
    have hfiber := manuscriptEdge_left_fiber_card_le_edgeBoundedLeft_parameter_sum
      E x (fun p hp => (hsupport p hp).1) hactual
    have hfiberReal :
        (((E.filter fun e => e.1 = x).card : ℕ) : ℝ) ≤
          ∑ d ∈ (∏ p ∈ S, p).divisors,
            ((edgeBoundedLeftVertexPrimeParameters S b n x d).card : ℝ) := by
      exact_mod_cast hfiber
    exact hfiberReal.trans (hbound x a r ha hr hx hfixed)
  · have hempty : E.filter (fun e => e.1 = x) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnonempty
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

/-- The entire sole remaining fixed-left degree proposition is now an
UNCONDITIONAL Lean theorem with absolute support-independent constant 455. -/
theorem fixedModulusLeftVertexDegreeBound_unconditional :
    FixedModulusLeftVertexDegreeBound := by
  refine ⟨455, by norm_num, ?_⟩
  intro S b τ ell hsupport _hτ _hell _hstrip
  have hprimes : ∀ p ∈ S, p.Prime ∧ 3 < p := by
    intro p hp
    exact ⟨(hsupport p hp).1, (hsupport p hp).2.1⟩
  have hb : ∀ p ∈ S, ¬ p ∣ b p := by
    intro p hp hdivisor
    exact (hsupport p hp).2.2 (Nat.mod_eq_zero_of_dvd hdivisor)
  filter_upwards
    [manuscriptEdge_actual_left_degree_eventually_le
      S b τ ell hprimes hb] with n hbound
  intro E hactual x
  simpa [div_eq_mul_inv, mul_assoc] using hbound E hactual x

/-- The COMPLETE original three-coordinate manuscript graph-degree input
is now proved without any mathematical assumptions: fixed left `455`,
fixed right `243`, and prime label `122`. -/
theorem fixedModulusTwoFormDegreeBound_unconditional :
    FixedModulusTwoFormDegreeBound :=
  fixedModulusTwoFormDegreeBound_of_left_vertex_degree
    fixedModulusLeftVertexDegreeBound_unconditional

#print axioms Erdos689.manuscriptEdge_left_fiber_card_le_edgeBoundedLeft_parameter_sum
#print axioms Erdos689.actualLeftVertex_canonical_sieve_fiber_sum_eventually_le
#print axioms Erdos689.manuscriptEdge_actual_left_degree_eventually_le
#print axioms Erdos689.fixedModulusLeftVertexDegreeBound_unconditional
#print axioms Erdos689.fixedModulusTwoFormDegreeBound_unconditional

end Erdos689
