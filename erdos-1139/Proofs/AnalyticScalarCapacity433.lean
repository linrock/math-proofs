module

public import NoncircularScalarBridge433
public import ReserveDensity433

@[expose] public section


/-!
# Exact analytic-to-scalar capacity for the actual Erdős #689 graph

The old conditional bridge assumed an existential positive matching scalar.
This module eliminates that scalar exactly: for degree `D > 0`, its existence
is equivalent to the nonempty greedy capacity `⌊|E| / (3D)⌋` covering the
actual deficiency left after the actual canonical reserve.

The final theorem then manufactures the integer degree and matching scalars
directly from real actual-edge and actual-degree estimates, the *upper*
asymptotic for the actual initial deficiency, and the already-proved exact
canonical reserve density.  The remaining hypotheses are genuine analytic
estimates, not a covering, construction, matching, or ledger witness.

The unrestricted degree estimate must include the actual `q = 3` fiber; an
optional restricted-graph constant cannot be substituted without its factor
of two.  The true reserve density is `δ * (1 - 1 / (J + 1))`, not the weaker
informal `δ * (1 - τ)` lower bound.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos689

/-- The exact fixed-support density of actual robust residue classes. -/
noncomputable def manuscriptRobustDensity
    (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ) : ℝ :=
  ((robustResidues S b J).card : ℝ) /
    (((∏ s ∈ S, s).totient : ℕ) : ℝ)

/-- The exact density of the actual canonical reserve, including its integer cutoff. -/
noncomputable def manuscriptReserveDensity
    (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ) : ℝ :=
  manuscriptRobustDensity S b J *
    (1 - (((J + 1 : ℕ) : ℝ)⁻¹))

/-- A real bound on all three coordinate degrees of the actual robust graph. -/
def actualManuscriptDegreeAtMost
    (S : Finset ℕ) (b : ℕ → ℕ) (J n : ℕ) (τ ell B : ℝ) : Prop :=
  (∀ x : ℕ,
    (((robustManuscriptEdges S b n J τ ell).filter
      fun e => e.1 = x).card : ℝ) ≤ B) ∧
  (∀ y : ℕ,
    (((robustManuscriptEdges S b n J τ ell).filter
      fun e => e.2.1 = y).card : ℝ) ≤ B) ∧
  (∀ z : ℕ,
    (((robustManuscriptEdges S b n J τ ell).filter
      fun e => e.2.2 = z).card : ℝ) ≤ B)

/-- Robust residue density is nonnegative, including empty/degenerate support. -/
theorem manuscriptRobustDensity_nonneg
    (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ) :
    0 ≤ manuscriptRobustDensity S b J := by
  unfold manuscriptRobustDensity
  positivity

/-- The actual canonical reserve is at least as dense as the manuscript's
informal `τ`-band whenever its correct fixed cutoff condition holds. -/
theorem manuscriptReserveDensity_ge_tau_band
    (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ) (τ : ℝ)
    (hscale : (1 : ℝ) ≤ ((J + 1 : ℕ) : ℝ) * τ) :
    manuscriptRobustDensity S b J * (1 - τ) ≤
      manuscriptReserveDensity S b J := by
  have hpositive : (0 : ℝ) < ((J + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.zero_lt_succ J
  have hinverse : (((J + 1 : ℕ) : ℝ)⁻¹) ≤ τ := by
    rw [inv_eq_one_div, div_le_iff₀ hpositive]
    simpa [mul_comm] using hscale
  unfold manuscriptReserveDensity
  exact mul_le_mul_of_nonneg_left (by linarith)
    (manuscriptRobustDensity_nonneg S b J)

/-- The already-proved exact reserve asymptotic supplies the informal `τ`-band
lower estimate with every fixed positive slack, without a covering assumption. -/
theorem canonicalReserve_eventual_tau_band_lower
    (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ) (τ ε : ℝ)
    (hsupport : ∀ s ∈ S, 0 < s)
    (hscale : (1 : ℝ) ≤ ((J + 1 : ℕ) : ℝ) * τ)
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (manuscriptRobustDensity S b J * (1 - τ) - ε) *
          ((n : ℝ) / Real.log n) ≤
        ((canonicalReserve S b n J).card : ℝ) := by
  have hlimit : Tendsto
      (fun n : ℕ =>
        ((canonicalReserve S b n J).card : ℝ) /
          ((n : ℝ) / Real.log n))
      atTop (nhds (manuscriptReserveDensity S b J)) := by
    simpa [manuscriptRobustDensity, manuscriptReserveDensity] using
      canonicalReserve_asymptotic S b J hsupport
  have hbelow :
      manuscriptRobustDensity S b J * (1 - τ) - ε <
        manuscriptReserveDensity S b J :=
    lt_of_lt_of_le (sub_lt_self _ hε)
      (manuscriptReserveDensity_ge_tau_band S b J τ hscale)
  have heventual := (tendsto_order.mp hlimit).1 _ hbelow
  filter_upwards [heventual, eventually_ge_atTop 2] with n hbound hn
  have hnreal : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hprimeScale : 0 < (n : ℝ) / Real.log n := by
    exact div_pos (by positivity) (Real.log_pos hnreal)
  exact le_of_lt ((lt_div_iff₀ hprimeScale).mp hbound)

/-- Exact iff, including nonemptiness: a positive matching demand exists
precisely when the integer greedy capacity is positive and covers the deficit. -/
theorem positive_matching_exists_iff_exact_greedy_capacity
    (demand reserve edgeCount D : ℕ) (hD : 0 < D) :
    (∃ k : ℕ, 0 < k ∧ 3 * D * k ≤ edgeCount ∧ demand ≤ reserve + k) ↔
      3 * D ≤ edgeCount ∧ demand ≤ reserve + edgeCount / (3 * D) := by
  have hdenominator : 0 < 3 * D := Nat.mul_pos (by decide) hD
  constructor
  · rintro ⟨k, hk, hedges, hsurplus⟩
    have hnonempty : 3 * D ≤ edgeCount := by
      have hproduct : 3 * D * 1 ≤ 3 * D * k :=
        Nat.mul_le_mul_left (3 * D) hk
      simpa using hproduct.trans hedges
    have hcapacity : k ≤ edgeCount / (3 * D) := by
      apply (Nat.le_div_iff_mul_le hdenominator).mpr
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hedges
    exact ⟨hnonempty, hsurplus.trans (Nat.add_le_add_left hcapacity reserve)⟩
  · rintro ⟨hnonempty, hsurplus⟩
    refine ⟨edgeCount / (3 * D),
      Nat.div_pos hnonempty hdenominator, ?_, hsurplus⟩
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.div_mul_le_self edgeCount (3 * D)

/-- Exact integer greedy capacity produces the genuine nondegenerate actual
scalar certificate, with no existential matching-size hypothesis. -/
theorem actualManuscriptScalarData_of_exact_greedy_capacity
    {S : Finset ℕ} {b : ℕ → ℕ} {J n D : ℕ} {τ ell : ℝ}
    (hD : 0 < D)
    (hx : ∀ x : ℕ,
      ((robustManuscriptEdges S b n J τ ell).filter fun e => e.1 = x).card ≤ D)
    (hy : ∀ y : ℕ,
      ((robustManuscriptEdges S b n J τ ell).filter fun e => e.2.1 = y).card ≤ D)
    (hz : ∀ z : ℕ,
      ((robustManuscriptEdges S b n J τ ell).filter fun e => e.2.2 = z).card ≤ D)
    (hnonempty : 3 * D ≤ (robustManuscriptEdges S b n J τ ell).card)
    (hcapacity : deficiency n (initialAssignment S b) ≤
      (canonicalReserve S b n J).card +
        (robustManuscriptEdges S b n J τ ell).card / (3 * D)) :
    Nonempty (ActualManuscriptScalarData S b J τ ell n) := by
  obtain ⟨k, hk, hedges, hsurplus⟩ :=
    (positive_matching_exists_iff_exact_greedy_capacity
      (deficiency n (initialAssignment S b))
      (canonicalReserve S b n J).card
      (robustManuscriptEdges S b n J τ ell).card D hD).mpr
      ⟨hnonempty, hcapacity⟩
  exact ⟨{
    degree := D
    requiredMatching := k
    degree_positive := hD
    matching_positive := hk
    degree_left := hx
    degree_right := hy
    degree_label := hz
    enough_edges := hedges
    reserve_surplus := hsurplus
  }⟩

/-- Real analytic rates manufacture *both* positive natural scalars exactly:
`D = floor (C Y)` and `k = max 1 (actual deficiency - actual reserve)`.
There is no omitted ceiling error or abstract matching witness. -/
theorem actualManuscriptScalarData_of_pointwise_analytic_rates
    {S : Finset ℕ} {b : ℕ → ℕ} {J n : ℕ} {τ ell X Y A C κ : ℝ}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hC : 0 < C)
    (hdegree_scale : 1 ≤ C * Y)
    (hmatching_scale : 1 ≤ κ * X)
    (hmargin : 3 * C * κ ≤ A)
    (hedges : A * X * Y ≤ ((robustManuscriptEdges S b n J τ ell).card : ℝ))
    (hdegree : actualManuscriptDegreeAtMost S b J n τ ell (C * Y))
    (hdeficiency : ((deficiency n (initialAssignment S b) : ℕ) : ℝ) ≤
      ((canonicalReserve S b n J).card : ℝ) + κ * X) :
    Nonempty (ActualManuscriptScalarData S b J τ ell n) := by
  let D : ℕ := ⌊C * Y⌋₊
  let demand : ℕ := deficiency n (initialAssignment S b)
  let reserve : ℕ := (canonicalReserve S b n J).card
  let k : ℕ := max 1 (demand - reserve)
  have hDpositive : 0 < D := by
    dsimp [D]
    exact Nat.floor_pos.mpr hdegree_scale
  have hDupper : (D : ℝ) ≤ C * Y := by
    dsimp [D]
    exact Nat.floor_le (mul_nonneg hC.le hY)
  have hkpositive : 0 < k := by
    dsimp [k]
    omega
  have hdeficit : ((demand - reserve : ℕ) : ℝ) ≤ κ * X := by
    by_cases hcomparison : demand ≤ reserve
    · rw [Nat.sub_eq_zero_of_le hcomparison, Nat.cast_zero]
      linarith
    · have hreverse : reserve ≤ demand :=
        Nat.le_of_lt (Nat.lt_of_not_ge hcomparison)
      rw [Nat.cast_sub hreverse]
      dsimp [demand, reserve] at hdeficiency ⊢
      linarith
  have hkupper : (k : ℝ) ≤ κ * X := by
    dsimp [k]
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le hmatching_scale hdeficit
  have hmatching_nonnegative : 0 ≤ κ * X := by linarith
  have hedges_natural :
      3 * D * k ≤ (robustManuscriptEdges S b n J τ ell).card := by
    have hreal :
        ((3 * D * k : ℕ) : ℝ) ≤
          ((robustManuscriptEdges S b n J τ ell).card : ℝ) := by
      calc
        ((3 * D * k : ℕ) : ℝ) = 3 * (D : ℝ) * (k : ℝ) := by norm_num
        _ ≤ 3 * (C * Y) * (κ * X) := by gcongr
        _ = (3 * C * κ) * X * Y := by ring
        _ ≤ A * X * Y := by gcongr
        _ ≤ ((robustManuscriptEdges S b n J τ ell).card : ℝ) := hedges
    exact_mod_cast hreal
  rcases hdegree with ⟨hx, hy, hz⟩
  refine ⟨{
    degree := D
    requiredMatching := k
    degree_positive := hDpositive
    matching_positive := hkpositive
    degree_left := ?_
    degree_right := ?_
    degree_label := ?_
    enough_edges := hedges_natural
    reserve_surplus := ?_
  }⟩
  · intro x
    exact Nat.le_floor (hx x)
  · intro y
    exact Nat.le_floor (hy y)
  · intro z
    exact Nat.le_floor (hz z)
  · change demand ≤ reserve + k
    dsimp [k]
    omega

/-- Every fixed positive multiple of `n / log(n)^j` eventually exceeds one. -/
theorem eventually_logarithmic_scale_dominates_one
    (C : ℝ) (hC : 0 < C) (j : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) ≤ C * ((n : ℝ) / (Real.log n) ^ j) := by
  have hzero : Tendsto
      (fun n : ℕ => (Real.log (n : ℝ)) ^ j / (n : ℝ))
      atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop
        1 0 j (by norm_num)).comp
          (tendsto_natCast_atTop_atTop (R := ℝ))
  have hbound := (tendsto_order.mp hzero).2 C hC
  filter_upwards [hbound, eventually_ge_atTop 2] with n hsmall hn
  have hnreal : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hnpositive : (0 : ℝ) < n := by linarith
  have hpower : 0 < (Real.log (n : ℝ)) ^ j :=
    pow_pos (Real.log_pos hnreal) j
  have hcomparison : (Real.log (n : ℝ)) ^ j ≤ C * n :=
    le_of_lt ((div_lt_iff₀ hnpositive).mp hsmall)
  calc
    (1 : ℝ) ≤ (C * n) / (Real.log (n : ℝ)) ^ j := by
      apply (le_div_iff₀ hpower).mpr
      simpa using hcomparison
    _ = C * ((n : ℝ) / (Real.log n) ^ j) := by ring

/-- The globally quantified two-form proposition really controls the actual
unrestricted graph, including its permitted exceptional left core `q = 3`. -/
theorem actualManuscriptDegreeAtMost_of_two_form_bound
    (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ) (τ ell : ℝ)
    (hsupport : ∀ s ∈ S, s.Prime ∧ 3 < s ∧ b s % s ≠ 0)
    (htau : 0 < τ) (hell : 0 < ell)
    (hstrip : τ + ell < 1 / 10)
    (hsieve : FixedModulusTwoFormDegreeBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      actualManuscriptDegreeAtMost S b J n τ ell
        (C * n / (Real.log n) ^ 2) := by
  classical
  obtain ⟨C, hC, hbound⟩ := hsieve
  refine ⟨C, hC, ?_⟩
  have hactual := hbound S b τ ell hsupport htau hell hstrip
  filter_upwards [hactual] with n hn
  exact hn (robustManuscriptEdges S b n J τ ell)
    (fun e he => (Finset.mem_filter.mp he).2.1)

/-- The global coefficient-uniform prime-pattern proposition specializes to
the exact cardinality and actual robust-residue density of this graph. -/
theorem actualManuscriptEdgeLower_of_uniform_bound
    (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ) (τ ell : ℝ)
    (hsupport : ∀ s ∈ S,
      s.Prime ∧ 3 < s ∧ J < s ∧ b s % s ≠ 0)
    (htau : 0 < τ) (hell : 0 < ell)
    (hstrip : τ + ell < 1 / 10)
    (huniform : UniformRobustManuscriptEdgeLowerBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * manuscriptRobustDensity S b J * ell * (n : ℝ) ^ 2 /
          (Real.log n) ^ 3 ≤
        ((robustManuscriptEdges S b n J τ ell).card : ℝ) := by
  obtain ⟨c, hc, hbound⟩ := huniform
  refine ⟨c, hc, ?_⟩
  simpa [manuscriptRobustDensity] using
    hbound S b J τ ell hsupport htau hell hstrip

/-- The strict density inequality used by the manuscript remains valid with
the *exact* canonical reserve and the exact capacity coefficient. -/
theorem dense_support_strict_scalar_margin
    {δ τ t ρ : ℝ}
    (ht : 0 < t) (htsmall : t < 1)
    (hdensity : 1 - t / 10 < δ)
    (htau : τ < t / 10)
    (hreserve : δ * (1 - τ) ≤ ρ) :
    1 < ρ + δ * t := by
  have hδ : 0 < δ := by nlinarith
  have hfactor : 0 < 1 + 9 * t / 10 := by linarith
  have hlarger : 1 + 9 * t / 10 < 1 - τ + t := by linarith
  have hproduct :
      (1 - t / 10) * (1 + 9 * t / 10) < δ * (1 - τ + t) := by
    calc
      (1 - t / 10) * (1 + 9 * t / 10) <
          δ * (1 + 9 * t / 10) :=
        mul_lt_mul_of_pos_right hdensity hfactor
      _ < δ * (1 - τ + t) := mul_lt_mul_of_pos_left hlarger hδ
  have hpolynomial : 1 < (1 - t / 10) * (1 + 9 * t / 10) := by
    nlinarith [mul_pos ht (sub_pos.mpr htsmall)]
  nlinarith

/-- Fully synthesized noncircular analytic reduction.  The only missing
inputs are actual-edge lower and unrestricted degree estimates, the actual
initial-deficiency *upper* bound, and the displayed strict numerical margin.
Neither a covering, matching, construction, nor scalar witness is assumed. -/
theorem officialStatement_of_fixed_support_analytic_rate_margin
    (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ)
    (τ ell c C : ℝ)
    (hsupport : ∀ s ∈ S, s.Prime ∧ 3 < s)
    (htau : 0 < τ) (hell : 0 < ell)
    (hcutoff : (1 : ℝ) ≤ ((J + 1 : ℕ) : ℝ) * τ)
    (hc : 0 < c) (hC : 0 < C)
    (hdensity : 0 < manuscriptRobustDensity S b J)
    (hedges : ∀ᶠ n : ℕ in atTop,
      c * manuscriptRobustDensity S b J * ell * (n : ℝ) ^ 2 /
          (Real.log n) ^ 3 ≤
        ((robustManuscriptEdges S b n J τ ell).card : ℝ))
    (hdegree : ∀ᶠ n : ℕ in atTop,
      actualManuscriptDegreeAtMost S b J n τ ell
        (C * n / (Real.log n) ^ 2))
    (hdeficiency_upper : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ((deficiency n (initialAssignment S b) : ℕ) : ℝ) /
          ((n : ℝ) / Real.log n) ≤ 1 + ε)
    (hmargin : 1 < manuscriptReserveDensity S b J +
      (c * manuscriptRobustDensity S b J * ell) / (3 * C)) :
    OfficialStatement := by
  let A : ℝ := c * manuscriptRobustDensity S b J * ell
  let κ : ℝ := A / (3 * C)
  let ρ : ℝ := manuscriptReserveDensity S b J
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hκ : 0 < κ := by
    dsimp [κ]
    positivity
  have hgap : 0 < κ - (1 - ρ) := by
    dsimp [κ, A, ρ]
    linarith
  let ε : ℝ := (κ - (1 - ρ)) / 3
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hreserve_limit : Tendsto
      (fun n : ℕ =>
        ((canonicalReserve S b n J).card : ℝ) /
          ((n : ℝ) / Real.log n))
      atTop (nhds ρ) := by
    dsimp [ρ]
    simpa [manuscriptRobustDensity, manuscriptReserveDensity] using
      canonicalReserve_asymptotic S b J
        (fun s hs => (hsupport s hs).1.pos)
  have hreserve_lower : ∀ᶠ n : ℕ in atTop,
      ρ - ε < ((canonicalReserve S b n J).card : ℝ) /
        ((n : ℝ) / Real.log n) :=
    (tendsto_order.mp hreserve_limit).1 _ (sub_lt_self _ hε)
  have hdeficiency := hdeficiency_upper ε hε
  have hdegree_scale := eventually_logarithmic_scale_dominates_one C hC 2
  have hmatching_scale := eventually_logarithmic_scale_dominates_one κ hκ 1
  apply officialStatement_of_eventual_actual_manuscript_scalar_data
    S b J τ ell hsupport htau hcutoff
  filter_upwards [hedges, hdegree, hdeficiency, hreserve_lower,
    hdegree_scale, hmatching_scale, eventually_ge_atTop 2]
      with n hnedge hndegree hndeficiency hnreserve hnD hnk hn
  let X : ℝ := (n : ℝ) / Real.log n
  let Y : ℝ := (n : ℝ) / (Real.log n) ^ 2
  have hnreal : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hnlog : 0 < Real.log (n : ℝ) := Real.log_pos hnreal
  have hXpositive : 0 < X := by
    dsimp [X]
    positivity
  have hYpositive : 0 < Y := by
    dsimp [Y]
    positivity
  have hDscale : 1 ≤ C * Y := by
    simpa [Y] using hnD
  have hkscale : 1 ≤ κ * X := by
    simpa [X] using hnk
  have hmargin_exact : 3 * C * κ ≤ A := by
    have hnonzero : 3 * C ≠ 0 := by positivity
    have hequality : 3 * C * κ = A := by
      dsimp [κ]
      field_simp
    exact hequality.le
  have hdegree_actual :
      actualManuscriptDegreeAtMost S b J n τ ell (C * Y) := by
    simpa [Y, div_eq_mul_inv, mul_assoc] using hndegree
  have hedge_identity :
      A * X * Y =
        c * manuscriptRobustDensity S b J * ell * (n : ℝ) ^ 2 /
          (Real.log n) ^ 3 := by
    dsimp [A, X, Y]
    field_simp
  have hedge_actual :
      A * X * Y ≤ ((robustManuscriptEdges S b n J τ ell).card : ℝ) := by
    rw [hedge_identity]
    exact hnedge
  have hratio :
      (((deficiency n (initialAssignment S b) : ℕ) : ℝ) -
        ((canonicalReserve S b n J).card : ℝ)) / X < κ := by
    have hcombine :
        ((deficiency n (initialAssignment S b) : ℕ) : ℝ) / X -
          ((canonicalReserve S b n J).card : ℝ) / X <
            1 - ρ + 2 * ε := by
      dsimp [X] at hndeficiency hnreserve ⊢
      linarith
    have hslack : 1 - ρ + 2 * ε < κ := by
      dsimp [ε]
      linarith
    rw [sub_div]
    exact hcombine.trans hslack
  have hdeficit_actual :
      ((deficiency n (initialAssignment S b) : ℕ) : ℝ) ≤
        ((canonicalReserve S b n J).card : ℝ) + κ * X := by
    have h := (div_lt_iff₀ hXpositive).mp hratio
    linarith
  exact actualManuscriptScalarData_of_pointwise_analytic_rates
    hXpositive.le hYpositive.le hC hDscale hkscale hmargin_exact
    hedge_actual hdegree_actual hdeficit_actual

/-- The manuscript's explicit dense-support and small-cutoff inequalities
imply the *actual* strict reserve-plus-greedy-capacity margin. -/
theorem actual_manuscript_strict_margin_of_dense_support
    (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ)
    (τ ell c C : ℝ)
    (hc : 0 < c) (hell : 0 < ell) (hC : 0 < C)
    (hcutoff : (1 : ℝ) ≤ ((J + 1 : ℕ) : ℝ) * τ)
    (htsmall : c * ell / (3 * C) < 1)
    (htau : τ < (c * ell / (3 * C)) / 10)
    (hdensity :
      1 - (c * ell / (3 * C)) / 10 < manuscriptRobustDensity S b J) :
    1 < manuscriptReserveDensity S b J +
      (c * manuscriptRobustDensity S b J * ell) / (3 * C) := by
  let t : ℝ := c * ell / (3 * C)
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hreserve := manuscriptReserveDensity_ge_tau_band S b J τ hcutoff
  have hstrict := dense_support_strict_scalar_margin
    (δ := manuscriptRobustDensity S b J)
    (τ := τ) (t := t) (ρ := manuscriptReserveDensity S b J)
    ht htsmall hdensity htau hreserve
  convert hstrict using 1
  dsimp [t]
  ring

/-- Fixed support satisfying the actual manuscript density/cutoff selection
needs only the three genuine analytic estimates: edge lower, unrestricted
degree upper, and actual initial-deficiency upper. -/
theorem officialStatement_of_dense_support_analytic_rates
    (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ)
    (τ ell c C : ℝ)
    (hsupport : ∀ s ∈ S, s.Prime ∧ 3 < s)
    (htau_positive : 0 < τ) (hell : 0 < ell)
    (hcutoff : (1 : ℝ) ≤ ((J + 1 : ℕ) : ℝ) * τ)
    (hc : 0 < c) (hC : 0 < C)
    (htsmall : c * ell / (3 * C) < 1)
    (htau : τ < (c * ell / (3 * C)) / 10)
    (hdensity :
      1 - (c * ell / (3 * C)) / 10 < manuscriptRobustDensity S b J)
    (hedges : ∀ᶠ n : ℕ in atTop,
      c * manuscriptRobustDensity S b J * ell * (n : ℝ) ^ 2 /
          (Real.log n) ^ 3 ≤
        ((robustManuscriptEdges S b n J τ ell).card : ℝ))
    (hdegree : ∀ᶠ n : ℕ in atTop,
      actualManuscriptDegreeAtMost S b J n τ ell
        (C * n / (Real.log n) ^ 2))
    (hdeficiency_upper : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ((deficiency n (initialAssignment S b) : ℕ) : ℝ) /
          ((n : ℝ) / Real.log n) ≤ 1 + ε) :
    OfficialStatement := by
  have hdensity_positive : 0 < manuscriptRobustDensity S b J := by
    nlinarith
  exact officialStatement_of_fixed_support_analytic_rate_margin
    S b J τ ell c C hsupport htau_positive hell hcutoff hc hC
    hdensity_positive hedges hdegree hdeficiency_upper
    (actual_manuscript_strict_margin_of_dense_support
      S b J τ ell c C hc hell hC hcutoff htsmall htau hdensity)

end Erdos689

