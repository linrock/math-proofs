module

public import ActualRightVertexSummed433

@[expose] public section


/-!
# Toward the unconditional genuine fixed-right manuscript graph degree

The fixed even support modulus is `2*W`.  Its totient normalization makes
the actual sharp fixed-right Selberg main constant `242`.  The full summed
endpoint, fourth-power, small-prime, and support-prime error is negligible
on the original `n/log(n)^2` scale.
-/

open Filter
open scoped BigOperators Topology

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Erdos689

/-- Every support divisor occurs among the genuine coprime label
coefficient pairs via the injective pair `(1,a)`. -/
theorem actualRightVertex_divisor_card_le_label_pair_card
    (S : Finset ℕ)
    (hsupport : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, p).divisors.card ≤
      (actualCanonicalLabelCoefficientPairs S).card := by
  classical
  let W : ℕ := ∏ p ∈ S, p
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).pos
  have hone : 1 ∈ W.divisors :=
    Nat.mem_divisors.mpr ⟨one_dvd W, Nat.ne_of_gt hW⟩
  have hinjective : Set.InjOn (fun a : ℕ => (1, a))
      (↑W.divisors : Set ℕ) := by
    intro a _ d _ heq
    exact congrArg Prod.snd heq
  have hsubset : W.divisors.image (fun a : ℕ => (1, a)) ⊆
      actualCanonicalLabelCoefficientPairs S := by
    intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
    unfold actualCanonicalLabelCoefficientPairs
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨hone, ha⟩,
      Nat.coprime_one_left a⟩
  calc
    W.divisors.card = (W.divisors.image fun a : ℕ => (1, a)).card :=
      (Finset.card_image_iff.mpr hinjective).symm
    _ ≤ (actualCanonicalLabelCoefficientPairs S).card :=
      Finset.card_le_card hsubset

/-- The true doubled-modulus fixed-right main term has absolute constant
`242`; its edge endpoint is twice the previously verified label main term. -/
theorem actualRightVertex_fixedModulus_main_term_eventually_le
    (S : Finset ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) * ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2 /
        (2 * (((∏ p ∈ S, p) : ℕ) : ℝ) ^ 2 *
          twoRootSelbergDenominator (2 * (∏ p ∈ S, p))
            (selbergSquareRootBlockCutoff n ^ 2)) ≤
        (242 : ℝ) *
          ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
  filter_upwards
    [actualFixedLabel_fixedModulus_main_term_eventually_le S hsupport]
      with n hmain
  calc
    (n : ℝ) * ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2 /
        (2 * (((∏ p ∈ S, p) : ℕ) : ℝ) ^ 2 *
          twoRootSelbergDenominator (2 * (∏ p ∈ S, p))
            (selbergSquareRootBlockCutoff n ^ 2)) =
      2 * ((n : ℝ) * ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2 /
        (4 * (((∏ p ∈ S, p) : ℕ) : ℝ) ^ 2 *
          twoRootSelbergDenominator (2 * (∏ p ∈ S, p))
            (selbergSquareRootBlockCutoff n ^ 2))) := by ring
    _ ≤ 2 * ((121 : ℝ) *
          ((n : ℝ) / (Real.log (n : ℝ)) ^ 2)) := by gcongr
    _ = (242 : ℝ) *
          ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by ring

/-- Every actual summed fixed-right Selberg error is negligible on the true
degree scale.  The bound follows by positive domination by the independently
proved complete fixed-label error; no analytic remainder is assumed. -/
theorem actualRightVertex_fixedModulus_errors_normalized_tendsto_zero
    (S : Finset ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p) :
    Tendsto
      (fun n : ℕ =>
        (((((∏ p ∈ S, p).divisors.card : ℕ) : ℝ)) *
          ((((∏ p ∈ S, p) : ℕ) : ℝ) *
            (2 / twoRootSelbergDenominator (2 * (∏ p ∈ S, p))
                (selbergSquareRootBlockCutoff n ^ 2) +
              (((selbergSquareRootBlockCutoff n ^ 2 : ℕ) : ℝ) ^ 4 +
                ((2 * Nat.primeCounting
                  (selbergSquareRootBlockCutoff n ^ 2) : ℕ) : ℝ))) +
            ((2 * S.card : ℕ) : ℝ))) /
          ((n : ℝ) / (Real.log (n : ℝ)) ^ 2))
      atTop (nhds 0) := by
  have hlabel := actualFixedLabel_fixedModulus_errors_normalized_tendsto_zero
    S hsupport
  apply squeeze_zero'
    (Eventually.of_forall (fun n => by
      have hD := twoRootSelbergDenominator_nonneg
        (M := 2 * (∏ p ∈ S, p)) (by simp)
          (selbergSquareRootBlockCutoff n ^ 2)
      positivity)) _ hlabel
  apply Eventually.of_forall
  intro n
  have hD := twoRootSelbergDenominator_nonneg
    (M := 2 * (∏ p ∈ S, p)) (by simp)
      (selbergSquareRootBlockCutoff n ^ 2)
  have hcards :
      ((((∏ p ∈ S, p).divisors.card : ℕ) : ℝ)) ≤
        ((actualCanonicalLabelCoefficientPairs S).card : ℝ) := by
    exact_mod_cast actualRightVertex_divisor_card_le_label_pair_card
      S (fun p hp => (hsupport p hp).1)
  have hsmall :
      (2 : ℝ) /
        twoRootSelbergDenominator (2 * (∏ p ∈ S, p))
          (selbergSquareRootBlockCutoff n ^ 2) ≤
      (3 : ℝ) /
        twoRootSelbergDenominator (2 * (∏ p ∈ S, p))
          (selbergSquareRootBlockCutoff n ^ 2) := by
    exact div_le_div_of_nonneg_right (by norm_num) hD
  have hinner :
      (((∏ p ∈ S, p) : ℕ) : ℝ) *
        (2 / twoRootSelbergDenominator (2 * (∏ p ∈ S, p))
            (selbergSquareRootBlockCutoff n ^ 2) +
          (((selbergSquareRootBlockCutoff n ^ 2 : ℕ) : ℝ) ^ 4 +
            ((2 * Nat.primeCounting
              (selbergSquareRootBlockCutoff n ^ 2) : ℕ) : ℝ))) +
          ((2 * S.card : ℕ) : ℝ) ≤
      (((∏ p ∈ S, p) : ℕ) : ℝ) *
        (3 / twoRootSelbergDenominator (2 * (∏ p ∈ S, p))
            (selbergSquareRootBlockCutoff n ^ 2) +
          (((selbergSquareRootBlockCutoff n ^ 2 : ℕ) : ℝ) ^ 4 +
            ((2 * Nat.primeCounting
              (selbergSquareRootBlockCutoff n ^ 2) : ℕ) : ℝ))) +
          ((2 * S.card : ℕ) : ℝ) := by gcongr
  have hleftnonnegative :
      (0 : ℝ) ≤
      (((∏ p ∈ S, p) : ℕ) : ℝ) *
        (2 / twoRootSelbergDenominator (2 * (∏ p ∈ S, p))
            (selbergSquareRootBlockCutoff n ^ 2) +
          (((selbergSquareRootBlockCutoff n ^ 2 : ℕ) : ℝ) ^ 4 +
            ((2 * Nat.primeCounting
              (selbergSquareRootBlockCutoff n ^ 2) : ℕ) : ℝ))) +
          ((2 * S.card : ℕ) : ℝ) := by positivity
  have hproduct := (mul_le_mul_of_nonneg_right hcards hleftnonnegative).trans
    (mul_le_mul_of_nonneg_left hinner (by positivity))
  exact div_le_div_of_nonneg_right hproduct (by positivity)

/-- With the actual fixed even modulus, the complete genuine all-divisor
fixed-right graph-fiber sum is eventually at most `243*n/log(n)^2`.
Only the explicit real sieve-prime family and fixed-vertex exclusions are
required at this intermediate stage. -/
theorem actualRightVertex_fixedModulus_fiber_sum_eventually_le
    (S : Finset ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hb : ∀ p ∈ S, ¬ p ∣ b p) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (y : ℕ) (P : Finset ℕ),
        (∀ p ∈ S,
          (2 : ZMod p) * (y : ZMod p) ≠ (b p : ZMod p)) →
        (∀ p ∈ P, p.Prime) →
        (∀ p ∈ P, 2 < p) →
        (∀ p ∈ P, ¬ p ∣ y) →
        Nat.Coprime (∏ p ∈ P, p) (2 * (∏ p ∈ S, p)) →
        (∀ p : ℕ, p.Prime →
          (p ∣ ∏ q ∈ P, q ↔
            p ≤ selbergSquareRootBlockCutoff n ^ 2 ∧
              Nat.Coprime p (2 * (∏ p ∈ S, p)))) →
        (∑ a ∈ (∏ p ∈ S, p).divisors,
          ((edgeBoundedRightVertexPrimeParameters S b n y a).card : ℝ)) ≤
          (243 : ℝ) *
            ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
  have hsmall :=
    (actualRightVertex_fixedModulus_errors_normalized_tendsto_zero
      S hsupport).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards
    [actualRightVertex_fixedModulus_main_term_eventually_le S hsupport,
      hsmall, eventually_ge_atTop 2] with n hmain herror hn
  intro y P hfixed hprime hlarge havoidy hPM hprimes
  have hnpositive : 0 < n := by omega
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnreal
  have hscale : 0 < (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by positivity
  have hcutoff : 0 < selbergSquareRootBlockCutoff n ^ 2 :=
    selbergSquareRootBlockCutoff_sq_pos_of_pos n hnpositive
  have hWM : (∏ p ∈ S, p) ∣ 2 * (∏ p ∈ S, p) := by
    refine ⟨2, ?_⟩
    ring
  have hfinite := actualRightVertexFiber_sum_le_sharp_main_and_errors
    S P b n y (2 * (∏ p ∈ S, p))
      (selbergSquareRootBlockCutoff n ^ 2)
        hsupport hb hfixed hprime hlarge hcutoff havoidy
          (by simp) hPM hWM hprimes
  have herror' := (div_lt_one hscale).mp herror
  nlinarith

/-- A genuine right vertex `y = 2*d*r` above a fixed positive linear
threshold cannot be divisible by any canonical fixed-modulus sieve prime:
the support coefficient is excluded and the actual remaining prime `r`
eventually lies strictly above the sieve cutoff. -/
theorem actualRightVertexCanonicalSieve_avoids_large_vertices_eventually
    (S : Finset ℕ) (τ : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hτ : 0 < τ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ y d r : ℕ,
        d ∣ (∏ p ∈ S, p) →
        r.Prime →
        y = 2 * d * r →
        τ * n < (y : ℝ) →
          ∀ p ∈ actualCanonicalLabelSievePrimes S n, ¬ p ∣ y := by
  let W : ℕ := ∏ p ∈ S, p
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).pos
  have hWreal : (0 : ℝ) < W := by exact_mod_cast hW
  let δ : ℝ := τ / (2 * (W : ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards
    [actualCanonicalLabelSieveCutoff_lt_linear_eventually δ hδ] with
      n hcutoff
  intro y d r hd hr hy hylinear p hp hdivisor
  have hpprime := actualCanonicalLabelSievePrimes_prime S n p hp
  have hpmember := (mem_actualCanonicalLabelSievePrimes_iff S n p).mp hp
  have hpnot : ¬ p ∣ 2 * W :=
    (hpprime.coprime_iff_not_dvd.mp hpmember.2.2)
  have hpnotcoefficient : ¬ p ∣ 2 * d := by
    intro hdiv
    apply hpnot
    exact dvd_trans hdiv (mul_dvd_mul_left 2 hd)
  rw [hy] at hdivisor
  have hpr : p ∣ r := by
    rcases (hpprime.dvd_mul).mp hdivisor with hcoefficient | hremaining
    · exact (hpnotcoefficient hcoefficient).elim
    · exact hremaining
  have heq : p = r :=
    (Nat.prime_dvd_prime_iff_eq hpprime hr).mp hpr
  have hrbound : r ≤ selbergSquareRootBlockCutoff n ^ 2 := by
    simpa [heq] using hpmember.1
  have hdW : d ≤ W := Nat.le_of_dvd hW hd
  have hyupper :
      y ≤ 2 * W * (selbergSquareRootBlockCutoff n ^ 2) := by
    rw [hy]
    gcongr
  have hscaled := mul_lt_mul_of_pos_left hcutoff
    (show (0 : ℝ) < 2 * (W : ℝ) by positivity)
  have hcancel :
      (2 * (W : ℝ)) * (δ * (n : ℝ)) = τ * n := by
    dsimp [δ]
    field_simp
  rw [hcancel] at hscaled
  have hyupperReal :
      (y : ℝ) ≤ (2 * (W : ℝ)) *
        (((selbergSquareRootBlockCutoff n ^ 2 : ℕ) : ℝ)) := by
    exact_mod_cast hyupper
  linarith

/-- The complete genuine all-divisor fixed-right parameter sum is uniformly
at most `243*n/log(n)^2` for every actual manuscript right vertex.  The
canonical sieve-prime set is constructed explicitly, and all determinant,
support, switched-selector, and support-prime exceptions are discharged. -/
theorem actualRightVertex_canonical_sieve_fiber_sum_eventually_le
    (S : Finset ℕ) (b : ℕ → ℕ) (τ ell : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (hτ : 0 < τ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ y : ℕ,
        (∃ e : TripleEdge,
          manuscriptEdge S b n τ ell e ∧ e.2.1 = y) →
        (∑ a ∈ (∏ p ∈ S, p).divisors,
          ((edgeBoundedRightVertexPrimeParameters S b n y a).card : ℝ)) ≤
          (243 : ℝ) *
            ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
  filter_upwards
    [actualRightVertex_fixedModulus_fiber_sum_eventually_le
      S b hsupport hb,
      actualRightVertexCanonicalSieve_avoids_large_vertices_eventually
        S τ (fun p hp => (hsupport p hp).1) hτ] with
      n hbound havoid
  intro y hactual
  obtain ⟨e, hedge, hey⟩ := hactual
  obtain ⟨_, hrelation, _, _, _, hmiss, hlabel,
    _, _, ⟨d, r, hd, hr, hrepr⟩⟩ := hedge
  have hyrepr : y = 2 * d * r := hey.symm.trans hrepr
  have hlabelle : e.2.2 ≤ y := by omega
  have hlabelleReal : (e.2.2 : ℝ) ≤ y := by exact_mod_cast hlabelle
  have hylinear : τ * n < (y : ℝ) := hlabel.trans_le hlabelleReal
  have hfixed : ∀ p ∈ S,
      (2 : ZMod p) * (y : ZMod p) ≠ (b p : ZMod p) := by
    rw [hey] at hmiss
    have hnot := (switchedHits_zero_iff_forall_not_modEq
      S b (2 * y)).mp hmiss
    intro p hp
    exact (zmod_switched_target_ne_iff_not_modEq p (b p) y).mpr
      (hnot p hp)
  let P := actualCanonicalLabelSievePrimes S n
  exact hbound y P hfixed
    (fun p hp => actualCanonicalLabelSievePrimes_prime S n p hp)
    (fun p hp => actualCanonicalLabelSievePrimes_gt_two S n p hp)
    (havoid y d r hd hr hyrepr hylinear)
    (actualCanonicalLabelSievePrimes_product_coprime S n)
    (fun p hp => actualCanonicalLabelSievePrimes_dvd_product_iff
      S n p hp)

/-- The genuine fixed-right coordinate of the original manuscript graph
degree estimate is proved unconditionally with absolute constant `243`:
eventually EVERY actual finite edge family and EVERY right vertex satisfy
the bound, with no prime-pattern, sieve-prime, remainder, coefficient,
selector, or degree hypothesis. -/
theorem manuscriptEdge_actual_right_degree_eventually_le
    (S : Finset ℕ) (b : ℕ → ℕ) (τ ell : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (hτ : 0 < τ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ E : Finset TripleEdge,
        (∀ e ∈ E, manuscriptEdge S b n τ ell e) →
          ∀ y : ℕ,
            (((E.filter fun e => e.2.1 = y).card : ℕ) : ℝ) ≤
              (243 : ℝ) *
                ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
  filter_upwards
    [actualRightVertex_canonical_sieve_fiber_sum_eventually_le
      S b τ ell hsupport hb hτ] with n hbound
  intro E hactual y
  by_cases hnonempty : (E.filter fun e => e.2.1 = y).Nonempty
  · obtain ⟨e, he⟩ := hnonempty
    obtain ⟨heE, hey⟩ := Finset.mem_filter.mp he
    have hfiber := manuscriptEdge_right_fiber_card_le_edgeBoundedRight_parameter_sum
      E y (fun p hp => (hsupport p hp).1) hactual
    have hfiberReal :
        (((E.filter fun e => e.2.1 = y).card : ℕ) : ℝ) ≤
          ∑ a ∈ (∏ p ∈ S, p).divisors,
            ((edgeBoundedRightVertexPrimeParameters S b n y a).card : ℝ) := by
      exact_mod_cast hfiber
    exact hfiberReal.trans (hbound y ⟨e, hactual e heE, hey⟩)
  · have hempty : E.filter (fun e => e.2.1 = y) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnonempty
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

#print axioms Erdos689.actualRightVertex_divisor_card_le_label_pair_card
#print axioms Erdos689.actualRightVertex_fixedModulus_main_term_eventually_le
#print axioms Erdos689.actualRightVertex_fixedModulus_errors_normalized_tendsto_zero
#print axioms Erdos689.actualRightVertex_fixedModulus_fiber_sum_eventually_le
#print axioms Erdos689.actualRightVertexCanonicalSieve_avoids_large_vertices_eventually
#print axioms Erdos689.actualRightVertex_canonical_sieve_fiber_sum_eventually_le
#print axioms Erdos689.manuscriptEdge_actual_right_degree_eventually_le

end Erdos689
