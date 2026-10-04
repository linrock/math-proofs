module

public import AnalyticBridge

@[expose] public section


/-!
# Exact three-prime weighted-to-unweighted transfer for Erdős problem #689

Green--Tao prime-pattern estimates naturally count products of three von
Mangoldt weights.  The covering argument instead requires the cardinality of
the actual prime-only affine-pattern finset.  This module proves the exact
finite conversion, including a separately quantified exceptional-set error.
No prime-pattern theorem, asymptotic estimate, or extra axiom is assumed.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos689

/-- Three individually bounded nonnegative weights have total mass at most
the cardinality of their indexing set times the cube of the common bound. -/
theorem sum_three_bounded_weights_le_card_mul_cube
    {ι : Type*} (F : Finset ι) (u v w : ι → ℝ) (L : ℝ)
    (hL : 0 ≤ L)
    (hweights : ∀ x ∈ F,
      (0 ≤ u x ∧ u x ≤ L) ∧
      (0 ≤ v x ∧ v x ≤ L) ∧
      (0 ≤ w x ∧ w x ≤ L)) :
    (∑ x ∈ F, u x * v x * w x) ≤ (F.card : ℝ) * L ^ 3 := by
  calc
    (∑ x ∈ F, u x * v x * w x) ≤ ∑ _x ∈ F, L ^ 3 := by
      apply Finset.sum_le_sum
      intro x hx
      obtain ⟨⟨hu0, hu⟩, ⟨hv0, hv⟩, ⟨hw0, hw⟩⟩ := hweights x hx
      calc
        u x * v x * w x ≤ L * L * L := by gcongr
        _ = L ^ 3 := by ring
    _ = (F.card : ℝ) * L ^ 3 := by simp

/-- An arbitrary lower bound for a nonnegative bounded triple-weight sum
transfers to the cardinality after division by the exact cube. -/
theorem card_lower_of_three_bounded_weight_sum
    {ι : Type*} (F : Finset ι) (u v w : ι → ℝ) (L B : ℝ)
    (hL : 0 < L)
    (hweights : ∀ x ∈ F,
      (0 ≤ u x ∧ u x ≤ L) ∧
      (0 ≤ v x ∧ v x ≤ L) ∧
      (0 ≤ w x ∧ w x ≤ L))
    (hlower : B ≤ ∑ x ∈ F, u x * v x * w x) :
    B / L ^ 3 ≤ (F.card : ℝ) := by
  apply (div_le_iff₀ (pow_pos hL 3)).2
  exact hlower.trans
    (sum_three_bounded_weights_le_card_mul_cube F u v w L hL.le hweights)

/-- Every member of the actual affine-prime candidate finset consists of
three genuine primes, each at most the manuscript endpoint. -/
theorem primeLinearCandidates_three_primes_le
    (n a b M r s t : ℕ) (τ ell : ℝ)
    (hstrip : τ + ell ≤ 1)
    {v : ℕ × ℕ}
    (hv : v ∈ primeLinearCandidates n a b M r s t τ ell) :
    v.1.Prime ∧ v.1 ≤ n ∧
      v.2.Prime ∧ v.2 ≤ n ∧
      (b * v.2 - a * v.1).Prime ∧ b * v.2 - a * v.1 ≤ n := by
  classical
  change v ∈
    ((Finset.Icc 1 n).product (Finset.Icc 1 n)).filter _ at hv
  obtain ⟨hcoordinates, hconditions⟩ := Finset.mem_filter.mp hv
  obtain ⟨hfirst, hsecond⟩ := Finset.mem_product.mp hcoordinates
  obtain ⟨hq, hq', hp, _hr, _hs, _ht, _hleft, _hright, _hlower, hupper⟩ :=
    hconditions
  have hlabel_real : ((b * v.2 - a * v.1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    calc
      ((b * v.2 - a * v.1 : ℕ) : ℝ) ≤
          (τ + ell) * (n : ℝ) := hupper
      _ ≤ 1 * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hstrip (by positivity)
      _ = (n : ℝ) := one_mul _
  have hlabel : b * v.2 - a * v.1 ≤ n := by
    exact_mod_cast hlabel_real
  exact ⟨hq, (Finset.mem_Icc.mp hfirst).2,
    hq', (Finset.mem_Icc.mp hsecond).2, hp, hlabel⟩

/-- The exact three-factor von Mangoldt weight of a manuscript affine pair. -/
noncomputable def threePrimeVonMangoldtWeight
    (a b : ℕ) (v : ℕ × ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt v.1 *
    ArithmeticFunction.vonMangoldt v.2 *
      ArithmeticFunction.vonMangoldt (b * v.2 - a * v.1)

/-- On the actual prime-only candidate finset, all three von Mangoldt
factors are exactly the logarithms of their corresponding genuine primes. -/
theorem threePrimeVonMangoldtWeight_eq_log_weight
    (n a b M r s t : ℕ) (τ ell : ℝ)
    (hstrip : τ + ell ≤ 1)
    {v : ℕ × ℕ}
    (hv : v ∈ primeLinearCandidates n a b M r s t τ ell) :
    threePrimeVonMangoldtWeight a b v =
      Real.log (v.1 : ℝ) * Real.log (v.2 : ℝ) *
        Real.log ((b * v.2 - a * v.1 : ℕ) : ℝ) := by
  obtain ⟨hq, _, hq', _, hp, _⟩ :=
    primeLinearCandidates_three_primes_le n a b M r s t τ ell hstrip hv
  unfold threePrimeVonMangoldtWeight
  rw [ArithmeticFunction.vonMangoldt_apply_prime hq,
    ArithmeticFunction.vonMangoldt_apply_prime hq',
    ArithmeticFunction.vonMangoldt_apply_prime hp]

/-- Every prime-factor logarithm in the actual manuscript candidate finset
is nonnegative and bounded by the endpoint logarithm. -/
theorem primeLinearCandidates_three_log_bounds
    (n a b M r s t : ℕ) (τ ell : ℝ)
    (hstrip : τ + ell ≤ 1)
    {v : ℕ × ℕ}
    (hv : v ∈ primeLinearCandidates n a b M r s t τ ell) :
    (0 ≤ Real.log (v.1 : ℝ) ∧
      Real.log (v.1 : ℝ) ≤ Real.log (n : ℝ)) ∧
    (0 ≤ Real.log (v.2 : ℝ) ∧
      Real.log (v.2 : ℝ) ≤ Real.log (n : ℝ)) ∧
    (0 ≤ Real.log ((b * v.2 - a * v.1 : ℕ) : ℝ) ∧
      Real.log ((b * v.2 - a * v.1 : ℕ) : ℝ) ≤ Real.log (n : ℝ)) := by
  obtain ⟨hq, hqn, hq', hq'n, hp, hpn⟩ :=
    primeLinearCandidates_three_primes_le n a b M r s t τ ell hstrip hv
  constructor
  · constructor
    · exact Real.log_nonneg (by exact_mod_cast hq.one_le)
    · exact Real.log_le_log (by exact_mod_cast hq.pos)
        (by exact_mod_cast hqn)
  constructor
  · constructor
    · exact Real.log_nonneg (by exact_mod_cast hq'.one_le)
    · exact Real.log_le_log (by exact_mod_cast hq'.pos)
        (by exact_mod_cast hq'n)
  constructor
  · exact Real.log_nonneg (by exact_mod_cast hp.one_le)
  · exact Real.log_le_log (by exact_mod_cast hp.pos)
      (by exact_mod_cast hpn)

/-- Exact finite conversion bound for the genuine prime-only three-form
von Mangoldt count; the endpoint logarithm occurs with exponent exactly three. -/
theorem primeLinearCandidates_vonMangoldt_sum_le_card_mul_log_cube
    (n a b M r s t : ℕ) (τ ell : ℝ)
    (hn : 2 ≤ n)
    (hstrip : τ + ell ≤ 1) :
    (∑ v ∈ primeLinearCandidates n a b M r s t τ ell,
      threePrimeVonMangoldtWeight a b v) ≤
      ((primeLinearCandidates n a b M r s t τ ell).card : ℝ) *
        (Real.log (n : ℝ)) ^ 3 := by
  let F := primeLinearCandidates n a b M r s t τ ell
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hbound := sum_three_bounded_weights_le_card_mul_cube F
    (fun v : ℕ × ℕ => Real.log (v.1 : ℝ))
    (fun v : ℕ × ℕ => Real.log (v.2 : ℝ))
    (fun v : ℕ × ℕ => Real.log ((b * v.2 - a * v.1 : ℕ) : ℝ))
    (Real.log (n : ℝ)) hlog
    (fun v hv => primeLinearCandidates_three_log_bounds
      n a b M r s t τ ell hstrip hv)
  change (∑ v ∈ F, threePrimeVonMangoldtWeight a b v) ≤ _
  calc
    (∑ v ∈ F, threePrimeVonMangoldtWeight a b v) =
        ∑ v ∈ F,
          Real.log (v.1 : ℝ) * Real.log (v.2 : ℝ) *
            Real.log ((b * v.2 - a * v.1 : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro v hv
      exact threePrimeVonMangoldtWeight_eq_log_weight
        n a b M r s t τ ell hstrip hv
    _ ≤ _ := hbound

/-- A quantitative lower bound for the genuine weighted three-prime count
implies the exact unweighted affine-prime candidate lower bound. -/
theorem primeLinearCandidates_card_lower_of_vonMangoldt_sum
    (n a b M r s t : ℕ) (τ ell B : ℝ)
    (hn : 2 ≤ n)
    (hstrip : τ + ell ≤ 1)
    (hlower : B ≤
      ∑ v ∈ primeLinearCandidates n a b M r s t τ ell,
        threePrimeVonMangoldtWeight a b v) :
    B / (Real.log (n : ℝ)) ^ 3 ≤
      ((primeLinearCandidates n a b M r s t τ ell).card : ℝ) := by
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  apply (div_le_iff₀ (pow_pos hlog 3)).2
  exact hlower.trans
    (primeLinearCandidates_vonMangoldt_sum_le_card_mul_log_cube
      n a b M r s t τ ell hn hstrip)

/-- Removing a precisely bounded exceptional subset from any weighted finite
sum preserves the total lower bound minus exactly that exceptional error. -/
theorem weighted_core_lower_of_exceptional_error
    {ι : Type*} [DecidableEq ι]
    (F G : Finset ι) (w : ι → ℝ) (A E : ℝ)
    (hsubset : G ⊆ F)
    (htotal : A ≤ ∑ x ∈ F, w x)
    (herror : (∑ x ∈ F \ G, w x) ≤ E) :
    A - E ≤ ∑ x ∈ G, w x := by
  have hdecomposition :
      (∑ x ∈ F, w x) = (∑ x ∈ F \ G, w x) + ∑ x ∈ G, w x := by
    exact (Finset.sum_sdiff hsubset).symm
  rw [hdecomposition] at htotal
  linarith

/-- Exact transfer from an unrestricted von Mangoldt lattice sum to the
actual prime-only affine candidate count, with the prime-power or other
exceptional contribution explicitly subtracted before dividing by `log(n)^3`. -/
theorem primeLinearCandidates_card_lower_of_vonMangoldt_with_error
    (n a b M r s t : ℕ) (τ ell A E : ℝ)
    (F : Finset (ℕ × ℕ))
    (hn : 2 ≤ n)
    (hstrip : τ + ell ≤ 1)
    (hsubset : primeLinearCandidates n a b M r s t τ ell ⊆ F)
    (htotal : A ≤ ∑ v ∈ F, threePrimeVonMangoldtWeight a b v)
    (herror :
      (∑ v ∈ F \ primeLinearCandidates n a b M r s t τ ell,
        threePrimeVonMangoldtWeight a b v) ≤ E) :
    (A - E) / (Real.log (n : ℝ)) ^ 3 ≤
      ((primeLinearCandidates n a b M r s t τ ell).card : ℝ) := by
  apply primeLinearCandidates_card_lower_of_vonMangoldt_sum
    n a b M r s t τ ell (A - E) hn hstrip
  exact weighted_core_lower_of_exceptional_error
    F (primeLinearCandidates n a b M r s t τ ell)
    (threePrimeVonMangoldtWeight a b) A E hsubset htotal herror

#print axioms Erdos689.sum_three_bounded_weights_le_card_mul_cube
#print axioms Erdos689.card_lower_of_three_bounded_weight_sum
#print axioms Erdos689.primeLinearCandidates_three_primes_le
#print axioms Erdos689.threePrimeVonMangoldtWeight_eq_log_weight
#print axioms Erdos689.primeLinearCandidates_three_log_bounds
#print axioms Erdos689.primeLinearCandidates_vonMangoldt_sum_le_card_mul_log_cube
#print axioms Erdos689.primeLinearCandidates_card_lower_of_vonMangoldt_sum
#print axioms Erdos689.weighted_core_lower_of_exceptional_error
#print axioms Erdos689.primeLinearCandidates_card_lower_of_vonMangoldt_with_error

end Erdos689
