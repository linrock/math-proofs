import ManuscriptLocal

/-!
# Multiplicity-free transfer from three-prime patterns to manuscript edges

A circle-method estimate naturally counts tuples consisting of two support
divisors and two external primes.  To turn such an estimate into a lower bound
for the *actual edge set*, one must show that different tuples cannot encode
the same three-partite edge.  This file proves that transfer without assuming
any analytic prime-pattern estimate.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos689

/-- An external prime cannot divide any divisor of the support product. -/
theorem external_prime_not_dvd_support_divisor
    {S : Finset ℕ} {d p : ℕ}
    (hsupport : ∀ s ∈ S, s.Prime)
    (hd : d ∣ ∏ s ∈ S, s)
    (hp : p.Prime) (houtside : p ∉ S) :
    ¬ p ∣ d := by
  intro hdiv
  exact houtside
    (prime_mem_of_dvd_support_product hp hsupport (dvd_trans hdiv hd))

/-- A support divisor times an external prime determines both factors. -/
theorem support_divisor_external_prime_injective
    {S : Finset ℕ} {a a' q q' : ℕ}
    (hsupport : ∀ s ∈ S, s.Prime)
    (ha' : a' ∣ ∏ s ∈ S, s)
    (hq : q.Prime) (hq' : q'.Prime)
    (houtside : q ∉ S)
    (heq : a * q = a' * q') :
    a = a' ∧ q = q' := by
  have hdiv : q ∣ a' * q' := by
    rw [← heq]
    exact dvd_mul_left q a
  rcases hq.dvd_mul.mp hdiv with hcoefficient | hprime
  · exact False.elim
      ((external_prime_not_dvd_support_divisor hsupport ha' hq houtside)
        hcoefficient)
  · have hqeq := (Nat.prime_dvd_prime_iff_eq hq hq').mp hprime
    subst q'
    exact ⟨Nat.mul_right_cancel hq.pos heq, rfl⟩

/-- Doubling the support-divisor representation preserves its uniqueness. -/
theorem doubled_support_divisor_external_prime_injective
    {S : Finset ℕ} {d d' q q' : ℕ}
    (hsupport : ∀ s ∈ S, s.Prime)
    (hd' : d' ∣ ∏ s ∈ S, s)
    (hq : q.Prime) (hq' : q'.Prime)
    (houtside : q ∉ S)
    (heq : 2 * d * q = 2 * d' * q') :
    d = d' ∧ q = q' := by
  have hcancel : 2 * (d * q) = 2 * (d' * q') := by
    simpa [mul_assoc] using heq
  have hproduct : d * q = d' * q' := by omega
  exact support_divisor_external_prime_injective
    hsupport hd' hq hq' houtside hproduct

/-- The edge encoded by a pair of support divisors and external primes. -/
def primePatternEdge (a d q r : ℕ) : TripleEdge :=
  (a * q, 2 * d * r, 2 * d * r - a * q)

/-- Equality of encoded edges forces equality of all four pattern parameters. -/
theorem primePatternEdge_injective_of_support_divisors
    {S : Finset ℕ} {a a' d d' q q' r r' : ℕ}
    (hsupport : ∀ s ∈ S, s.Prime)
    (ha' : a' ∣ ∏ s ∈ S, s)
    (hd' : d' ∣ ∏ s ∈ S, s)
    (hq : q.Prime) (hq' : q'.Prime)
    (hr : r.Prime) (hr' : r'.Prime)
    (hqoutside : q ∉ S) (hroutside : r ∉ S)
    (hedge : primePatternEdge a d q r = primePatternEdge a' d' q' r') :
    a = a' ∧ d = d' ∧ q = q' ∧ r = r' := by
  have hleft : a * q = a' * q' := by
    exact congrArg (fun e : TripleEdge => e.1) hedge
  have hright : 2 * d * r = 2 * d' * r' := by
    exact congrArg (fun e : TripleEdge => e.2.1) hedge
  obtain ⟨haeq, hqeq⟩ := support_divisor_external_prime_injective
    hsupport ha' hq hq' hqoutside hleft
  obtain ⟨hdeq, hreq⟩ := doubled_support_divisor_external_prime_injective
    hsupport hd' hr hr' hroutside hright
  exact ⟨haeq, hdeq, hqeq, hreq⟩

/-- A four-parameter tuple, grouped into its coefficient and prime pairs. -/
abbrev PrimePatternParameters := (ℕ × ℕ) × (ℕ × ℕ)

/-- Admissible coefficients divide the support product; primes lie outside it. -/
def supportPrimePattern (S : Finset ℕ) (v : PrimePatternParameters) : Prop :=
  v.1.1 ∣ ∏ s ∈ S, s ∧
  v.1.2 ∣ ∏ s ∈ S, s ∧
  v.2.1.Prime ∧ v.2.1 ∉ S ∧
  v.2.2.Prime ∧ v.2.2 ∉ S

/-- Bundle the four parameters into the corresponding three-partite edge. -/
def primePatternEncoding (v : PrimePatternParameters) : TripleEdge :=
  primePatternEdge v.1.1 v.1.2 v.2.1 v.2.2

/-- Every finite admissible prime-pattern family maps injectively into edges. -/
theorem primePatternEncoding_injOn
    {S : Finset ℕ} (patterns : Finset PrimePatternParameters)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hadmissible : ∀ v ∈ patterns, supportPrimePattern S v) :
    Set.InjOn primePatternEncoding (↑patterns : Set PrimePatternParameters) := by
  intro v hv w hw hedge
  obtain ⟨_, _, hvq, hvqoutside, hvr, hvroutside⟩ :=
    hadmissible v (Finset.mem_coe.mp hv)
  obtain ⟨hwa, hwd, hwq, _, hwr, _⟩ :=
    hadmissible w (Finset.mem_coe.mp hw)
  obtain ⟨haeq, hdeq, hqeq, hreq⟩ :=
    primePatternEdge_injective_of_support_divisors
      hsupport hwa hwd hvq hwq hvr hwr hvqoutside hvroutside hedge
  exact Prod.ext (Prod.ext haeq hdeq) (Prod.ext hqeq hreq)

/-- Counting admissible parameter tuples incurs exactly no multiplicity loss. -/
theorem card_primePatternEncoding_image
    {S : Finset ℕ} (patterns : Finset PrimePatternParameters)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hadmissible : ∀ v ∈ patterns, supportPrimePattern S v) :
    (patterns.image primePatternEncoding).card = patterns.card := by
  exact Finset.card_image_iff.mpr
    (primePatternEncoding_injOn patterns hsupport hadmissible)

/-- Any realized admissible parameter family lower-bounds the genuine edge set. -/
theorem card_prime_patterns_le_robustManuscriptEdges
    {S : Finset ℕ} {b : ℕ → ℕ} {n J : ℕ} {τ ell : ℝ}
    (patterns : Finset PrimePatternParameters)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hadmissible : ∀ v ∈ patterns, supportPrimePattern S v)
    (hrealized : ∀ v ∈ patterns,
      primePatternEncoding v ∈ robustManuscriptEdges S b n J τ ell) :
    patterns.card ≤ (robustManuscriptEdges S b n J τ ell).card := by
  rw [← card_primePatternEncoding_image patterns hsupport hadmissible]
  apply Finset.card_le_card
  intro e he
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
  exact hrealized v hv

/-- The concrete coefficient/prime tuples underlying robust manuscript edges. -/
noncomputable def manuscriptPrimePatterns
    (S : Finset ℕ) (b : ℕ → ℕ) (n J : ℕ) (τ ell : ℝ) :
    Finset PrimePatternParameters := by
  classical
  let W := ∏ s ∈ S, s
  exact ((W.divisors.product W.divisors).product
    ((Finset.Icc 1 n).product (Finset.Icc 1 n))).filter fun v =>
      v.2.1.Prime ∧ v.2.1 ∉ S ∧
      v.2.2.Prime ∧ v.2.2 ∉ S ∧
      manuscriptEdge S b n τ ell (primePatternEncoding v) ∧
      robustResidue S b J (primePatternEncoding v).2.2

/-- Every selected concrete tuple has admissible divisors and external primes. -/
theorem manuscriptPrimePatterns_admissible
    {S : Finset ℕ} {b : ℕ → ℕ} {n J : ℕ} {τ ell : ℝ}
    {v : PrimePatternParameters}
    (hv : v ∈ manuscriptPrimePatterns S b n J τ ell) :
    supportPrimePattern S v := by
  classical
  obtain ⟨hbase, hq, hqoutside, hr, hroutside, _⟩ :=
    Finset.mem_filter.mp hv
  obtain ⟨hcoefficients, _⟩ := Finset.mem_product.mp hbase
  obtain ⟨ha, hd⟩ := Finset.mem_product.mp hcoefficients
  exact ⟨(Nat.mem_divisors.mp ha).1,
    (Nat.mem_divisors.mp hd).1, hq, hqoutside, hr, hroutside⟩

/-- The explicitly defined coefficient tuples really encode actual robust edges. -/
theorem manuscriptPrimePatterns_encoding_mem
    {S : Finset ℕ} {b : ℕ → ℕ} {n J : ℕ} {τ ell : ℝ}
    {v : PrimePatternParameters}
    (hv : v ∈ manuscriptPrimePatterns S b n J τ ell) :
    primePatternEncoding v ∈ robustManuscriptEdges S b n J τ ell := by
  classical
  obtain ⟨hbase, hq, _, hr, _, hedge, hrobust⟩ :=
    Finset.mem_filter.mp hv
  obtain ⟨hcoefficients, _⟩ := Finset.mem_product.mp hbase
  obtain ⟨ha, hd⟩ := Finset.mem_product.mp hcoefficients
  have hW : 0 < ∏ s ∈ S, s :=
    Nat.pos_of_ne_zero (Nat.mem_divisors.mp ha).2
  have hapos : 0 < v.1.1 :=
    Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp ha).1 hW
  have hdpos : 0 < v.1.2 :=
    Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hW
  have hleftpos : 0 < (primePatternEncoding v).1 := by
    exact Nat.mul_pos hapos hq.pos
  have hrightpos : 0 < (primePatternEncoding v).2.1 := by
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) hdpos) hr.pos
  have hlabelpos : 0 < (primePatternEncoding v).2.2 := hedge.1.pos
  have hleftbound := hedge.2.2.1
  have hrightbound := hedge.2.2.2.1
  have hrelation := hedge.2.1
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ?_,
    Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ?_,
      Finset.mem_Icc.mpr ?_⟩⟩, hedge, hrobust⟩
  · omega
  · omega
  · omega

/-- The actual ternary coefficient-pattern count has no representation loss. -/
theorem card_manuscriptPrimePatterns_le_robustManuscriptEdges
    {S : Finset ℕ} {b : ℕ → ℕ} {n J : ℕ} {τ ell : ℝ}
    (hsupport : ∀ s ∈ S, s.Prime) :
    (manuscriptPrimePatterns S b n J τ ell).card ≤
      (robustManuscriptEdges S b n J τ ell).card := by
  apply card_prime_patterns_le_robustManuscriptEdges
    (manuscriptPrimePatterns S b n J τ ell) hsupport
  · intro v hv
    exact manuscriptPrimePatterns_admissible hv
  · intro v hv
    exact manuscriptPrimePatterns_encoding_mem hv

/-- The precise coefficient-summed ternary prime estimate, stated on tuples. -/
def UniformManuscriptPrimePatternLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ) (τ ell : ℝ),
      (∀ s ∈ S, s.Prime ∧ 3 < s ∧ J < s ∧ b s % s ≠ 0) →
      0 < τ → 0 < ell → τ + ell < 1 / 10 →
        ∀ᶠ n : ℕ in Filter.atTop,
          c * (((robustResidues S b J).card : ℝ) /
            (((∏ s ∈ S, s).totient : ℕ) : ℝ)) * ell * (n : ℝ) ^ 2 /
              (Real.log n) ^ 3 ≤
            ((manuscriptPrimePatterns S b n J τ ell).card : ℝ)

/-- The targeted tuple estimate implies the exact global genuine-edge estimate. -/
theorem uniformRobustManuscriptEdgeLowerBound_of_primePatternLowerBound
    (hpatterns : UniformManuscriptPrimePatternLowerBound) :
    UniformRobustManuscriptEdgeLowerBound := by
  obtain ⟨c, hc, hpatterns⟩ := hpatterns
  refine ⟨c, hc, ?_⟩
  intro S b J τ ell hsupport hτ hell hstrip
  filter_upwards [hpatterns S b J τ ell hsupport hτ hell hstrip] with n hn
  refine hn.trans ?_
  exact_mod_cast card_manuscriptPrimePatterns_le_robustManuscriptEdges
    (S := S) (b := b) (n := n) (J := J) (τ := τ) (ell := ell)
    (fun s hs => (hsupport s hs).1)

end Erdos689

#print axioms Erdos689.external_prime_not_dvd_support_divisor
#print axioms Erdos689.support_divisor_external_prime_injective
#print axioms Erdos689.doubled_support_divisor_external_prime_injective
#print axioms Erdos689.primePatternEdge_injective_of_support_divisors
#print axioms Erdos689.primePatternEncoding_injOn
#print axioms Erdos689.card_primePatternEncoding_image
#print axioms Erdos689.card_prime_patterns_le_robustManuscriptEdges
#print axioms Erdos689.manuscriptPrimePatterns_admissible
#print axioms Erdos689.manuscriptPrimePatterns_encoding_mem
#print axioms Erdos689.card_manuscriptPrimePatterns_le_robustManuscriptEdges
#print axioms Erdos689.uniformRobustManuscriptEdgeLowerBound_of_primePatternLowerBound
