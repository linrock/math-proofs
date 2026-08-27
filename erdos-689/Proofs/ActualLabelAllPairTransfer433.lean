import ActualLabelCanonicalSieve433
import LabelFiberClosure433

/-!
# Full actual fixed-label graph degree bound

For genuine large prime labels, every nonempty fixed-label coefficient fiber
forces its two support divisors to be coprime.  The already proved canonical
optimized sieve therefore controls the sum over *all* support-divisor pairs.
An exact graph-fiber injection retaining the true endpoint then gives the
actual fixed-label manuscript graph degree, uniformly, with constant `122`.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos689

/-- A genuinely noncoprime support-coefficient pair cannot support any
actual edge-bounded label-fiber solution when the prime label is coprime to
the doubled right coefficient. -/
theorem edgeBoundedLabelFiber_eq_empty_of_not_coprime
    (S : Finset ℕ) (b : ℕ → ℕ) (n z a d : ℕ)
    (hz : Nat.Coprime z (2 * d))
    (hcoprime : ¬ Nat.Coprime a d) :
    edgeBoundedLabelFiberSwitchedPrimeParameters S b n z a d = ∅ := by
  classical
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨q, hmember⟩
  have hold := (Finset.mem_filter.mp hmember).1
  obtain ⟨_, _, ⟨r, _, _, hsolution⟩, _, _⟩ :=
    (mem_labelFiberSwitchedPrimeParameters_iff
      S b n z a d q).mp hold
  have hcoefficient := labelFiber_coefficient_coprime_of_label_coprime
    a d z q r hz hsolution
  have hdivisor : d ∣ 2 * d := by
    refine ⟨2, ?_⟩
    ring
  exact hcoprime (hcoefficient.coprime_dvd_right hdivisor)

/-- With a label coprime to the doubled support product, summing actual
edge-bounded graph fibers over *all* support-divisor pairs is exactly the
same as summing over the genuinely coprime pairs. -/
theorem edgeBoundedLabelFiber_all_pair_sum_eq_coprime_sum
    (S : Finset ℕ) (b : ℕ → ℕ) (n z : ℕ)
    (hz : Nat.Coprime z (2 * (∏ p ∈ S, p))) :
    (∑ c ∈ ((∏ p ∈ S, p).divisors.product
        (∏ p ∈ S, p).divisors),
      ((edgeBoundedLabelFiberSwitchedPrimeParameters
        S b n z c.1 c.2).card : ℝ)) =
      ∑ c ∈ actualCanonicalLabelCoefficientPairs S,
        ((edgeBoundedLabelFiberSwitchedPrimeParameters
          S b n z c.1 c.2).card : ℝ) := by
  classical
  unfold actualCanonicalLabelCoefficientPairs
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hcoprime : Nat.Coprime c.1 c.2
  · simp [hcoprime]
  · have hd := (Nat.mem_divisors.mp
        (Finset.mem_product.mp hc).2).1
    have htwod : 2 * c.2 ∣ 2 * (∏ p ∈ S, p) :=
      mul_dvd_mul_left 2 hd
    have hempty := edgeBoundedLabelFiber_eq_empty_of_not_coprime
      S b n z c.1 c.2 (hz.coprime_dvd_right htwod) hcoprime
    simp [hcoprime, hempty]

/-- Every actual prime label above a fixed positive linear threshold is
eventually coprime to the entire doubled fixed support product. -/
theorem actualPrimeLabel_coprime_doubled_support_eventually
    (S : Finset ℕ) (τ : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hτ : 0 < τ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ z : ℕ, z.Prime → τ * n < (z : ℝ) →
        Nat.Coprime z (2 * (∏ p ∈ S, p)) := by
  have hhalf : 0 < τ / 2 := by positivity
  filter_upwards
    [actualSupportProduct_lt_linear_eventually S (τ / 2) hhalf] with n hbound
  intro z hz hzlower
  have hW : 0 < ∏ p ∈ S, p :=
    Finset.prod_pos fun p hp => (hsupport p hp).1.pos
  have htwolower :
      (((2 * (∏ p ∈ S, p) : ℕ) : ℝ)) < τ * n := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  have hlarge : 2 * (∏ p ∈ S, p) < z := by
    exact_mod_cast htwolower.trans hzlower
  apply (hz.coprime_iff_not_dvd).mpr
  exact Nat.not_dvd_of_pos_of_lt (by positivity) hlarge

/-- Fully unconditional support-uniform Selberg bound for the sum of the
*actual* edge-bounded fixed-label graph fibers over every support-divisor
pair, including the formerly omitted noncoprime coefficient pairs. -/
theorem actualFixedLabel_all_pair_fiber_sum_eventually_le
    (S : Finset ℕ) (b : ℕ → ℕ) (τ : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (hτ : 0 < τ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ z : ℕ, z.Prime → τ * n < (z : ℝ) →
        (∑ c ∈ ((∏ p ∈ S, p).divisors.product
            (∏ p ∈ S, p).divisors),
          ((edgeBoundedLabelFiberSwitchedPrimeParameters
            S b n z c.1 c.2).card : ℝ)) ≤
          (122 : ℝ) *
            ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
  filter_upwards
    [actualFixedLabel_canonical_sieve_fiber_sum_eventually_le
      S b τ hsupport hb hτ,
      actualPrimeLabel_coprime_doubled_support_eventually
        S τ hsupport hτ] with n hbound hcoprime
  intro z hz hzlower
  rw [edgeBoundedLabelFiber_all_pair_sum_eq_coprime_sum
    S b n z (hcoprime z hz hzlower)]
  exact hbound z hz hzlower

/-- The actual fixed-label manuscript graph fiber injects into the union of
the genuinely edge-bounded switched prime-parameter fibers.  The graph's
true first-endpoint inequality survives the injection exactly. -/
theorem manuscriptEdge_label_fiber_card_le_edgeBounded_parameter_sum
    {S : Finset ℕ} {b : ℕ → ℕ} {n : ℕ} {τ ell : ℝ}
    (E : Finset TripleEdge) (z : ℕ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hactual : ∀ e ∈ E, manuscriptEdge S b n τ ell e) :
    (E.filter fun e => e.2.2 = z).card ≤
      ∑ c ∈ ((∏ s ∈ S, s).divisors.product
          (∏ s ∈ S, s).divisors),
        (edgeBoundedLabelFiberSwitchedPrimeParameters
          S b n z c.1 c.2).card := by
  classical
  let W := ∏ s ∈ S, s
  let fiber := E.filter fun e => e.2.2 = z
  let coefficients := W.divisors.product W.divisors
  let parameterVertices : (ℕ × ℕ) → Finset ℕ := fun c =>
    (edgeBoundedLabelFiberSwitchedPrimeParameters
      S b n z c.1 c.2).image (fun q => c.1 * q)
  have hW : 0 < W := Finset.prod_pos fun s hs => (hsupport s hs).pos
  have hinjective := manuscriptEdge_left_injective_on_label_fiber E z hactual
  have hsubset : fiber.image (fun e : TripleEdge => e.1) ⊆
      coefficients.biUnion parameterVertices := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨heE, hez⟩ := Finset.mem_filter.mp he
    obtain ⟨_, hrelation, hleftbound, hrightbound,
      hleftmiss, hrightmiss, _, _,
      ⟨a, q, ha, hq, hleftrepr⟩,
      ⟨d, r, hd, hr, hrightrepr⟩⟩ := hactual e heE
    have hapos : 0 < a := Nat.pos_of_dvd_of_pos ha hW
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hW
    have hqleft : q ≤ e.1 := by
      rw [hleftrepr]
      exact Nat.le_mul_of_pos_left q hapos
    have hrright : r ≤ e.2.1 := by
      rw [hrightrepr]
      simpa [mul_assoc] using
        (Nat.le_mul_of_pos_left r (Nat.mul_pos (by norm_num) hdpos))
    have hqn : q ≤ n := by omega
    have hrn : r ≤ n := by omega
    have hequation : 2 * d * r = a * q + z := by omega
    have hlefttarget : 2 * e.1 = 2 * a * q := by
      rw [hleftrepr]
      ring
    have hrighttarget : 2 * e.2.1 = 2 * (a * q + z) := by omega
    rw [hlefttarget] at hleftmiss
    rw [hrighttarget] at hrightmiss
    apply Finset.mem_biUnion.mpr
    refine ⟨(a, d), Finset.mem_product.mpr
      ⟨Nat.mem_divisors.mpr ⟨ha, Nat.ne_of_gt hW⟩,
        Nat.mem_divisors.mpr ⟨hd, Nat.ne_of_gt hW⟩⟩, ?_⟩
    apply Finset.mem_image.mpr
    have hqmember : q ∈ labelFiberSwitchedPrimeParameters S b n z a d := by
      simp only [labelFiberSwitchedPrimeParameters,
        labelFiberPrimeParameters, Finset.mem_filter]
      exact ⟨⟨Finset.mem_Icc.mpr ⟨hq.one_le, hqn⟩,
        hq, r, Finset.mem_Icc.mpr ⟨hr.one_le, hrn⟩,
          hr, hequation⟩, hleftmiss, hrightmiss⟩
    refine ⟨q, Finset.mem_filter.mpr ⟨hqmember, ?_⟩,
      hleftrepr.symm⟩
    rw [← hlefttarget]
    exact hleftbound
  calc
    fiber.card = (fiber.image fun e : TripleEdge => e.1).card :=
      (Finset.card_image_iff.mpr hinjective).symm
    _ ≤ (coefficients.biUnion parameterVertices).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ c ∈ coefficients, (parameterVertices c).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ c ∈ coefficients,
        (edgeBoundedLabelFiberSwitchedPrimeParameters
          S b n z c.1 c.2).card := by
      apply Finset.sum_le_sum
      intro c _
      exact Finset.card_image_le

/-- The genuine fixed-label coordinate of the full manuscript graph-degree
estimate is proved unconditionally, with absolute constant `122`, for every
actual finite edge family and every label.  No sieve set, prime-pattern,
degree, density, or remainder hypothesis remains. -/
theorem manuscriptEdge_actual_label_degree_eventually_le
    (S : Finset ℕ) (b : ℕ → ℕ) (τ ell : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (hτ : 0 < τ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ E : Finset TripleEdge,
        (∀ e ∈ E, manuscriptEdge S b n τ ell e) →
          ∀ z : ℕ,
            (((E.filter fun e => e.2.2 = z).card : ℕ) : ℝ) ≤
              (122 : ℝ) *
                ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
  filter_upwards
    [actualFixedLabel_all_pair_fiber_sum_eventually_le
      S b τ hsupport hb hτ] with n hbound
  intro E hactual z
  by_cases hnonempty : (E.filter fun e => e.2.2 = z).Nonempty
  · obtain ⟨e, he⟩ := hnonempty
    obtain ⟨heE, hez⟩ := Finset.mem_filter.mp he
    have hedge := hactual e heE
    have hzprime : z.Prime := by
      rw [← hez]
      exact hedge.1
    have hzlower : τ * n < (z : ℝ) := by
      rw [← hez]
      exact hedge.2.2.2.2.2.2.1
    have hfiber := manuscriptEdge_label_fiber_card_le_edgeBounded_parameter_sum
      E z (fun p hp => (hsupport p hp).1) hactual
    have hfiberReal :
        (((E.filter fun e => e.2.2 = z).card : ℕ) : ℝ) ≤
          ∑ c ∈ ((∏ p ∈ S, p).divisors.product
              (∏ p ∈ S, p).divisors),
            ((edgeBoundedLabelFiberSwitchedPrimeParameters
              S b n z c.1 c.2).card : ℝ) := by
      exact_mod_cast hfiber
    exact hfiberReal.trans (hbound z hzprime hzlower)
  · have hempty : E.filter (fun e => e.2.2 = z) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnonempty
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

#print axioms Erdos689.edgeBoundedLabelFiber_eq_empty_of_not_coprime
#print axioms Erdos689.edgeBoundedLabelFiber_all_pair_sum_eq_coprime_sum
#print axioms Erdos689.actualPrimeLabel_coprime_doubled_support_eventually
#print axioms Erdos689.actualFixedLabel_all_pair_fiber_sum_eventually_le
#print axioms Erdos689.manuscriptEdge_label_fiber_card_le_edgeBounded_parameter_sum
#print axioms Erdos689.manuscriptEdge_actual_label_degree_eventually_le

end Erdos689
