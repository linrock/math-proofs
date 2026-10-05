module

public import PrimePatternMultiplicity433
public import ThreePrimeWeightTransfer433
public import TwoInputAssembly433

@[expose] public section


/-!
# Exact weighted three-prime pattern bridge for Erdős problem #689

The concrete manuscript pattern family contains support divisors, two
external primes, and the prime edge label.  Its encoding is already proved
injective into the actual robust edge set.  This module supplies the missing
exact finite transfer from the corresponding three-factor von Mangoldt sum to
the real robust-edge count.

The final conditional theorem has precisely two hypotheses: a global weighted
three-prime estimate with its constant selected before the support, and the
existing unrestricted two-form degree estimate.  No prime-pattern asymptotic
is silently postulated or proved here.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos689

/-- The exact three-prime von Mangoldt weight of one actual manuscript
coefficient tuple: its two outside primes and its genuine prime edge label. -/
noncomputable def manuscriptPrimePatternVonMangoldtWeight
    (v : PrimePatternParameters) : ℝ :=
  ArithmeticFunction.vonMangoldt v.2.1 *
    ArithmeticFunction.vonMangoldt v.2.2 *
      ArithmeticFunction.vonMangoldt (primePatternEncoding v).2.2

/-- The coefficient-summed von Mangoldt total on the actual robust manuscript
patterns, with no multiplicity assumptions or asymptotic hypotheses. -/
noncomputable def manuscriptWeightedPrimePatternCount
    (S : Finset ℕ) (b : ℕ → ℕ) (n J : ℕ) (τ ell : ℝ) : ℝ :=
  ∑ v ∈ manuscriptPrimePatterns S b n J τ ell,
    manuscriptPrimePatternVonMangoldtWeight v

/-- The two outside-prime coordinates and the actual encoded edge label are
all genuine primes no larger than the original covering endpoint. -/
theorem manuscriptPrimePatterns_three_primes_le
    {S : Finset ℕ} {b : ℕ → ℕ} {n J : ℕ} {τ ell : ℝ}
    {v : PrimePatternParameters}
    (hv : v ∈ manuscriptPrimePatterns S b n J τ ell) :
    v.2.1.Prime ∧ v.2.1 ≤ n ∧
      v.2.2.Prime ∧ v.2.2 ≤ n ∧
      (primePatternEncoding v).2.2.Prime ∧
        (primePatternEncoding v).2.2 ≤ n := by
  classical
  have hadmissible := manuscriptPrimePatterns_admissible hv
  obtain ⟨_, _, hq, _, hr, _⟩ := hadmissible
  have hbase := (Finset.mem_filter.mp hv).1
  have hcoordinates := (Finset.mem_product.mp hbase).2
  obtain ⟨hqcoord, hrcoord⟩ := Finset.mem_product.mp hcoordinates
  have hqn : v.2.1 ≤ n := (Finset.mem_Icc.mp hqcoord).2
  have hrn : v.2.2 ≤ n := (Finset.mem_Icc.mp hrcoord).2
  have hedge := manuscriptPrimePatterns_encoding_mem hv
  obtain ⟨hedge_coordinates, hedge_properties⟩ := Finset.mem_filter.mp hedge
  obtain ⟨_, hremaining⟩ := Finset.mem_product.mp hedge_coordinates
  obtain ⟨_, hlabelcoord⟩ := Finset.mem_product.mp hremaining
  have hlabeln : (primePatternEncoding v).2.2 ≤ n :=
    (Finset.mem_Icc.mp hlabelcoord).2
  exact ⟨hq, hqn, hr, hrn, hedge_properties.1.1, hlabeln⟩

/-- On every actual coefficient tuple its three von Mangoldt values equal
the logarithms of its actual three prime coordinates. -/
theorem manuscriptPrimePatternVonMangoldtWeight_eq_logs
    {S : Finset ℕ} {b : ℕ → ℕ} {n J : ℕ} {τ ell : ℝ}
    {v : PrimePatternParameters}
    (hv : v ∈ manuscriptPrimePatterns S b n J τ ell) :
    manuscriptPrimePatternVonMangoldtWeight v =
      Real.log (v.2.1 : ℝ) * Real.log (v.2.2 : ℝ) *
        Real.log ((primePatternEncoding v).2.2 : ℝ) := by
  obtain ⟨hq, _, hr, _, hp, _⟩ := manuscriptPrimePatterns_three_primes_le hv
  unfold manuscriptPrimePatternVonMangoldtWeight
  rw [ArithmeticFunction.vonMangoldt_apply_prime hq,
    ArithmeticFunction.vonMangoldt_apply_prime hr,
    ArithmeticFunction.vonMangoldt_apply_prime hp]

/-- All three genuine logarithmic prime weights are nonnegative and bounded
by the logarithm of the same original endpoint. -/
theorem manuscriptPrimePatterns_three_log_bounds
    {S : Finset ℕ} {b : ℕ → ℕ} {n J : ℕ} {τ ell : ℝ}
    {v : PrimePatternParameters}
    (hv : v ∈ manuscriptPrimePatterns S b n J τ ell) :
    (0 ≤ Real.log (v.2.1 : ℝ) ∧
      Real.log (v.2.1 : ℝ) ≤ Real.log (n : ℝ)) ∧
    (0 ≤ Real.log (v.2.2 : ℝ) ∧
      Real.log (v.2.2 : ℝ) ≤ Real.log (n : ℝ)) ∧
    (0 ≤ Real.log ((primePatternEncoding v).2.2 : ℝ) ∧
      Real.log ((primePatternEncoding v).2.2 : ℝ) ≤ Real.log (n : ℝ)) := by
  obtain ⟨hq, hqn, hr, hrn, hp, hpn⟩ :=
    manuscriptPrimePatterns_three_primes_le hv
  constructor
  · constructor
    · exact Real.log_nonneg (by exact_mod_cast hq.one_le)
    · exact Real.log_le_log (by exact_mod_cast hq.pos)
        (by exact_mod_cast hqn)
  constructor
  · constructor
    · exact Real.log_nonneg (by exact_mod_cast hr.one_le)
    · exact Real.log_le_log (by exact_mod_cast hr.pos)
        (by exact_mod_cast hrn)
  constructor
  · exact Real.log_nonneg (by exact_mod_cast hp.one_le)
  · exact Real.log_le_log (by exact_mod_cast hp.pos)
      (by exact_mod_cast hpn)

/-- The complete coefficient-summed actual three-prime weight is bounded
by its genuine tuple count times exactly `log(n)^3`. -/
theorem manuscriptWeightedPrimePatternCount_le_card_mul_log_cube
    (S : Finset ℕ) (b : ℕ → ℕ) (n J : ℕ) (τ ell : ℝ)
    (hn : 2 ≤ n) :
    manuscriptWeightedPrimePatternCount S b n J τ ell ≤
      ((manuscriptPrimePatterns S b n J τ ell).card : ℝ) *
        (Real.log (n : ℝ)) ^ 3 := by
  let F := manuscriptPrimePatterns S b n J τ ell
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hbound := sum_three_bounded_weights_le_card_mul_cube F
    (fun v : PrimePatternParameters => Real.log (v.2.1 : ℝ))
    (fun v : PrimePatternParameters => Real.log (v.2.2 : ℝ))
    (fun v : PrimePatternParameters =>
      Real.log ((primePatternEncoding v).2.2 : ℝ))
    (Real.log (n : ℝ)) hlog
    (fun v hv => manuscriptPrimePatterns_three_log_bounds hv)
  unfold manuscriptWeightedPrimePatternCount
  change (∑ v ∈ F, manuscriptPrimePatternVonMangoldtWeight v) ≤ _
  calc
    (∑ v ∈ F, manuscriptPrimePatternVonMangoldtWeight v) =
        ∑ v ∈ F,
          Real.log (v.2.1 : ℝ) * Real.log (v.2.2 : ℝ) *
            Real.log ((primePatternEncoding v).2.2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro v hv
      exact manuscriptPrimePatternVonMangoldtWeight_eq_logs hv
    _ ≤ _ := hbound

/-- The complete actual three-prime weighted total, after the exact
logarithmic conversion, lower-bounds the actual robust edge cardinality
without any representation or coefficient multiplicity loss. -/
theorem manuscriptWeightedPrimePatternCount_div_log_cube_le_actual_edges
    (S : Finset ℕ) (b : ℕ → ℕ) (n J : ℕ) (τ ell : ℝ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hn : 2 ≤ n) :
    manuscriptWeightedPrimePatternCount S b n J τ ell /
        (Real.log (n : ℝ)) ^ 3 ≤
      ((robustManuscriptEdges S b n J τ ell).card : ℝ) := by
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hpatterns :
      manuscriptWeightedPrimePatternCount S b n J τ ell /
          (Real.log (n : ℝ)) ^ 3 ≤
        ((manuscriptPrimePatterns S b n J τ ell).card : ℝ) := by
    apply (div_le_iff₀ (pow_pos hlog 3)).2
    exact manuscriptWeightedPrimePatternCount_le_card_mul_log_cube
      S b n J τ ell hn
  calc
    manuscriptWeightedPrimePatternCount S b n J τ ell /
        (Real.log (n : ℝ)) ^ 3 ≤
      ((manuscriptPrimePatterns S b n J τ ell).card : ℝ) := hpatterns
    _ ≤ ((robustManuscriptEdges S b n J τ ell).card : ℝ) := by
      exact_mod_cast card_manuscriptPrimePatterns_le_robustManuscriptEdges
        (S := S) (b := b) (n := n) (J := J) (τ := τ) (ell := ell)
        hsupport

/-- The sole remaining ternary-prime analytic estimate, expressed directly
as a lower bound for the exact coefficient-summed actual von Mangoldt total.
The absolute constant is chosen before the support, while its eventual
threshold may depend on every fixed manuscript parameter. -/
def UniformWeightedManuscriptPrimePatternLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ) (τ ell : ℝ),
      (∀ s ∈ S, s.Prime ∧ 3 < s ∧ J < s ∧ b s % s ≠ 0) →
      0 < τ → 0 < ell → τ + ell < 1 / 10 →
        ∀ᶠ n : ℕ in atTop,
          c * (((robustResidues S b J).card : ℝ) /
            (((∏ s ∈ S, s).totient : ℕ) : ℝ)) * ell * (n : ℝ) ^ 2 ≤
            manuscriptWeightedPrimePatternCount S b n J τ ell

/-- The exact coefficient-uniform weighted estimate implies the genuine
unweighted coefficient-pattern lower bound, with the same absolute constant. -/
theorem uniformManuscriptPrimePatternLowerBound_of_weighted
    (hweighted : UniformWeightedManuscriptPrimePatternLowerBound) :
    UniformManuscriptPrimePatternLowerBound := by
  obtain ⟨c, hc, hweighted⟩ := hweighted
  refine ⟨c, hc, ?_⟩
  intro S b J τ ell hsupport hτ hell hstrip
  filter_upwards [hweighted S b J τ ell hsupport hτ hell hstrip,
    eventually_ge_atTop 2] with n hn hlarge
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  apply (div_le_iff₀ (pow_pos hlog 3)).2
  exact hn.trans
    (manuscriptWeightedPrimePatternCount_le_card_mul_log_cube
      S b n J τ ell hlarge)

/-- The genuine coefficient-uniform three-von-Mangoldt estimate supplies the
exact actual robust-edge proposition required by the covering assembly. -/
theorem uniformRobustManuscriptEdgeLowerBound_of_weighted_prime_patterns
    (hweighted : UniformWeightedManuscriptPrimePatternLowerBound) :
    UniformRobustManuscriptEdgeLowerBound :=
  uniformRobustManuscriptEdgeLowerBound_of_primePatternLowerBound
    (uniformManuscriptPrimePatternLowerBound_of_weighted hweighted)

/-- Exact reduction of the original covering conjecture to a coefficient-
uniform actual three-von-Mangoldt lower bound and the unrestricted actual
two-form degree upper bound.  Every support, cutoff, reserve, density,
deficiency, multiplicity, and matching step is already kernel-proved. -/
theorem officialStatement_of_weighted_prime_patterns_and_two_form_degree
    (hweighted : UniformWeightedManuscriptPrimePatternLowerBound)
    (hdegree : FixedModulusTwoFormDegreeBound) :
    OfficialStatement :=
  officialStatement_of_uniform_edge_and_two_form_degree
    (uniformRobustManuscriptEdgeLowerBound_of_weighted_prime_patterns hweighted)
    hdegree


end Erdos689
