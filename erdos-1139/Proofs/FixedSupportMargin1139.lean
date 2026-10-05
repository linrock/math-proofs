module

public import ActualMajorArcFinalCoupling433

@[expose] public section


/-!
# Strict unused-prime density extracted from the completed Erdős #689 proof

The existing #689 scalar assembly selects only the *minimum* matching size
needed to close its covering.  That discards the genuinely strict asymptotic
margin between reserve density, full greedy matching capacity, and initial
deficiency.  This module retains that margin: it chooses a larger genuine
matching threshold and proves a positive-density supply of unused protected
reserve primes can remain after complete covering cleanup.

All analytic inputs are imported from the fully audited unconditional #689
development; no extra mathematical axiom or external prime-pattern theorem
is assumed.
-/

open Finset Filter
open scoped Topology

namespace Erdos1139

/-- The actual #689 manuscript graph has a genuine positive matching target
and enough reserve capacity to leave the specified number of protected
prime labels unused after exact deficiency cleanup. -/
structure StrictManuscriptScalarData
    (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ) (τ ell : ℝ)
    (n slack : ℕ) where
  degree : ℕ
  requiredMatching : ℕ
  degree_positive : 0 < degree
  matching_positive : 0 < requiredMatching
  degree_left : ∀ x : ℕ,
    ((Erdos689.robustManuscriptEdges S b n J τ ell).filter
      fun e => e.1 = x).card ≤ degree
  degree_right : ∀ y : ℕ,
    ((Erdos689.robustManuscriptEdges S b n J τ ell).filter
      fun e => e.2.1 = y).card ≤ degree
  degree_label : ∀ p : ℕ,
    ((Erdos689.robustManuscriptEdges S b n J τ ell).filter
      fun e => e.2.2 = p).card ≤ degree
  enough_edges :
    3 * degree * requiredMatching ≤
      (Erdos689.robustManuscriptEdges S b n J τ ell).card
  strict_reserve_surplus :
    Erdos689.deficiency n (Erdos689.initialAssignment S b) + slack ≤
      (Erdos689.canonicalReserve S b n J).card + requiredMatching

/-- Manufacture actual natural graph-degree and matching scalars from real
analytic rates while retaining the full specified integer reserve slack. -/
theorem strictManuscriptScalarData_of_pointwise_rates
    {S : Finset ℕ} {b : ℕ → ℕ} {J n slack : ℕ}
    {τ ell X Y A C κ : ℝ}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hC : 0 < C)
    (degree_scale : 1 ≤ C * Y)
    (matching_scale : 1 ≤ κ * X)
    (capacity : 3 * C * κ ≤ A)
    (edges : A * X * Y ≤
      ((Erdos689.robustManuscriptEdges S b n J τ ell).card : ℝ))
    (degrees : Erdos689.actualManuscriptDegreeAtMost
      S b J n τ ell (C * Y))
    (surplus :
      Erdos689.deficiency n (Erdos689.initialAssignment S b) + slack ≤
        (Erdos689.canonicalReserve S b n J).card + ⌊κ * X⌋₊) :
    Nonempty (StrictManuscriptScalarData S b J τ ell n slack) := by
  let D : ℕ := ⌊C * Y⌋₊
  let k : ℕ := ⌊κ * X⌋₊
  have Dpositive : 0 < D := Nat.floor_pos.mpr degree_scale
  have kpositive : 0 < k := Nat.floor_pos.mpr matching_scale
  have Dupper : (D : ℝ) ≤ C * Y :=
    Nat.floor_le (mul_nonneg hC.le hY)
  have kscale_nonnegative : 0 ≤ κ * X := matching_scale.trans' (by norm_num)
  have kupper : (k : ℝ) ≤ κ * X := Nat.floor_le kscale_nonnegative
  have natural_edges :
      3 * D * k ≤ (Erdos689.robustManuscriptEdges S b n J τ ell).card := by
    have real_edges :
        ((3 * D * k : ℕ) : ℝ) ≤
          ((Erdos689.robustManuscriptEdges S b n J τ ell).card : ℝ) := by
      calc
        ((3 * D * k : ℕ) : ℝ) = 3 * (D : ℝ) * (k : ℝ) := by norm_num
        _ ≤ 3 * (C * Y) * (κ * X) := by gcongr
        _ = (3 * C * κ) * X * Y := by ring
        _ ≤ A * X * Y := by gcongr
        _ ≤ _ := edges
    exact_mod_cast real_edges
  rcases degrees with ⟨left, right, label⟩
  exact ⟨{
    degree := D
    requiredMatching := k
    degree_positive := Dpositive
    matching_positive := kpositive
    degree_left := fun x => Nat.le_floor (left x)
    degree_right := fun y => Nat.le_floor (right y)
    degree_label := fun p => Nat.le_floor (label p)
    enough_edges := natural_edges
    strict_reserve_surplus := surplus
  }⟩

/-- All genuine fixed-support analytic data supplied by the completed #689
proof, with its strict reserve-plus-full-greedy-capacity margin retained. -/
structure FixedSupportAnalyticData where
  support : Finset ℕ
  residue : ℕ → ℕ
  parameter : ℕ
  tau : ℝ
  width : ℝ
  edgeConstant : ℝ
  degreeConstant : ℝ
  support_valid : ∀ p ∈ support,
    p.Prime ∧ 3 < p ∧ parameter < p ∧ residue p % p ≠ 0
  tau_positive : 0 < tau
  width_positive : 0 < width
  strip_small : tau + width < (1 : ℝ) / 10
  reserve_cutoff : (1 : ℝ) ≤ ((parameter + 1 : ℕ) : ℝ) * tau
  edge_positive : 0 < edgeConstant
  degree_positive : 0 < degreeConstant
  robust_positive :
    0 < Erdos689.manuscriptRobustDensity support residue parameter
  strict_margin :
    1 < Erdos689.manuscriptReserveDensity support residue parameter +
      (edgeConstant *
        Erdos689.manuscriptRobustDensity support residue parameter * width) /
          (3 * degreeConstant)
  eventual_edges : ∀ᶠ n : ℕ in atTop,
    edgeConstant *
      Erdos689.manuscriptRobustDensity support residue parameter * width *
        (n : ℝ) ^ 2 / (Real.log n) ^ 3 ≤
      ((Erdos689.robustManuscriptEdges
        support residue n parameter tau width).card : ℝ)
  eventual_degrees : ∀ᶠ n : ℕ in atTop,
    Erdos689.actualManuscriptDegreeAtMost
      support residue parameter n tau width
        (degreeConstant * n / (Real.log n) ^ 2)
  deficiency_limit :
    Tendsto
      (fun n : ℕ =>
        (Erdos689.deficiency n
          (Erdos689.initialAssignment support residue) : ℝ) /
            ((n : ℝ) / Real.log n))
      atTop (𝓝 (1 : ℝ))
  reserve_limit :
    Tendsto
      (fun n : ℕ =>
        ((Erdos689.canonicalReserve support residue n parameter).card : ℝ) /
          ((n : ℝ) / Real.log n))
      atTop
      (𝓝 (Erdos689.manuscriptReserveDensity support residue parameter))

/-- The original coefficient-uniform robust manuscript edge bound is an
UNCONDITIONAL consequence of the completed #689 major-arc proof. -/
theorem uniformRobustManuscriptEdgeLowerBound_unconditional1139 :
    Erdos689.UniformRobustManuscriptEdgeLowerBound :=
  Erdos689.uniformRobustManuscriptEdgeLowerBound_of_weighted_prime_patterns
    (Erdos689.uniformWeightedPrimePatternLowerBound_of_localized_major_arcs
      Erdos689.uniformLocalizedThreePrimeMajorArcLowerBound_unconditional)

/-- Construct the actual fixed support and all its strict positive-density
analytic rates directly from the completed, assumption-free #689 proof. -/
theorem exists_fixed_support_analytic_data :
    Nonempty FixedSupportAnalyticData := by
  classical
  obtain ⟨c, hc, edge_bound⟩ :=
    uniformRobustManuscriptEdgeLowerBound_unconditional1139
  obtain ⟨C, hC, degree_bound⟩ :=
    Erdos689.fixedModulusTwoFormDegreeBound_unconditional
  let ell : ℝ := min (1 / 40) (3 * C / (20 * c))
  have hell : 0 < ell := by
    dsimp [ell]
    exact lt_min (by norm_num) (by positivity)
  have hell_small : ell ≤ (1 / 40 : ℝ) := by
    dsimp [ell]
    exact min_le_left _ _
  have hell_capacity : ell ≤ 3 * C / (20 * c) := by
    dsimp [ell]
    exact min_le_right _ _
  let t : ℝ := c * ell / (3 * C)
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have ht_small : t ≤ (1 / 20 : ℝ) := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3 * C)).2
    calc
      c * ell ≤ c * (3 * C / (20 * c)) :=
        mul_le_mul_of_nonneg_left hell_capacity hc.le
      _ = (1 / 20 : ℝ) * (3 * C) := by
        field_simp [ne_of_gt hc]
  let τ : ℝ := t / 20
  have hτ : 0 < τ := by
    dsimp [τ]
    positivity
  have hτ_small : τ < t / 10 := by
    dsimp [τ]
    linarith
  have hstrip : τ + ell < (1 / 10 : ℝ) := by
    dsimp [τ]
    nlinarith
  obtain ⟨J, hJ⟩ := exists_nat_gt (1 / τ)
  have hJτ : (1 : ℝ) < (J : ℝ) * τ :=
    (div_lt_iff₀ hτ).mp hJ
  have hcutoff : (1 : ℝ) ≤ ((J + 1 : ℕ) : ℝ) * τ := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith
  obtain ⟨S, hS, hS_density⟩ :=
    Erdos689.exists_support_actual_robust_density_gt
      J (by positivity : (0 : ℝ) < t / 10)
  let b : ℕ → ℕ := fun _ => 1
  have hsupport : ∀ s ∈ S, s.Prime ∧ 3 < s ∧ J < s ∧ b s % s ≠ 0 := by
    intro s hs
    have hlarge : max J 3 < s := (hS s hs).2
    have hthree : 3 < s := lt_of_le_of_lt (le_max_right J 3) hlarge
    refine ⟨(hS s hs).1, hthree,
      lt_of_le_of_lt (le_max_left J 3) hlarge, ?_⟩
    dsimp [b]
    rw [Nat.mod_eq_of_lt (by omega : 1 < s)]
    omega
  have hsieve : ∀ s ∈ S, s.Prime ∧ 3 < s ∧ b s % s ≠ 0 := by
    intro s hs
    exact ⟨(hsupport s hs).1, (hsupport s hs).2.1,
      (hsupport s hs).2.2.2⟩
  have hb : ∀ s ∈ S, Nat.Coprime (b s) s := by
    intro s hs
    simp [b]
  have hdensity :
      1 - t / 10 < Erdos689.manuscriptRobustDensity S b J := by
    simpa [Erdos689.manuscriptRobustDensity, b] using hS_density
  have robust_positive :
      0 < Erdos689.manuscriptRobustDensity S b J := by
    nlinarith
  have hedges := edge_bound S b J τ ell hsupport hτ hell hstrip
  have hdegrees := degree_bound S b τ ell hsieve hτ hell hstrip
  have hactual_degree : ∀ᶠ n : ℕ in atTop,
      Erdos689.actualManuscriptDegreeAtMost S b J n τ ell
        (C * n / (Real.log n) ^ 2) := by
    filter_upwards [hdegrees] with n hn
    exact hn (Erdos689.robustManuscriptEdges S b n J τ ell)
      (fun e he => (Finset.mem_filter.mp he).2.1)
  have margin :
      1 < Erdos689.manuscriptReserveDensity S b J +
        (c * Erdos689.manuscriptRobustDensity S b J * ell) / (3 * C) :=
    Erdos689.actual_manuscript_strict_margin_of_dense_support
      S b J τ ell c C hc hell hC hcutoff
        (by change t < 1; linarith)
        (by change τ < t / 10; exact hτ_small)
        (by change 1 - t / 10 < _; exact hdensity)
  have hodd : 2 ∉ S := by
    intro htwo
    have := (hsupport 2 htwo).2.1
    omega
  have hdeficiency := Erdos689.initial_deficiency_asymptotic
    S b (fun s hs => (hsupport s hs).1) hodd hb
  have hreserve := Erdos689.canonicalReserve_asymptotic
    S b J (fun s hs => (hsupport s hs).1.pos)
  refine ⟨{
    support := S
    residue := b
    parameter := J
    tau := τ
    width := ell
    edgeConstant := c
    degreeConstant := C
    support_valid := hsupport
    tau_positive := hτ
    width_positive := hell
    strip_small := hstrip
    reserve_cutoff := hcutoff
    edge_positive := hc
    degree_positive := hC
    robust_positive := robust_positive
    strict_margin := margin
    eventual_edges := hedges
    eventual_degrees := hactual_degree
    deficiency_limit := hdeficiency
    reserve_limit := ?_
  }⟩
  simpa [Erdos689.manuscriptReserveDensity,
    Erdos689.manuscriptRobustDensity] using hreserve

/-- Retain a genuinely POSITIVE density of unused reserve primes.  Unlike the
historical #689 scalar assembly, the matching threshold here is chosen just
below its full greedy capacity, not at the minimum needed to close the
covering.  Its strict asymptotic surplus survives every natural floor. -/
theorem fixedSupportAnalyticData_eventual_strict_scalar_margin
    (data : FixedSupportAnalyticData) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ᶠ n : ℕ in atTop,
        (∀ p ∈ data.support, p ≤ n) ∧
          (2 : ℝ) ≤ data.tau * n ∧
          Nonempty
            (StrictManuscriptScalarData
              data.support data.residue data.parameter data.tau data.width n
              ⌊γ * ((n : ℝ) / Real.log n)⌋₊) := by
  let ρ : ℝ := Erdos689.manuscriptReserveDensity
    data.support data.residue data.parameter
  let A : ℝ := data.edgeConstant *
    Erdos689.manuscriptRobustDensity
      data.support data.residue data.parameter * data.width
  let κ : ℝ := A / (3 * data.degreeConstant)
  have Apositive : 0 < A := by
    dsimp [A]
    exact mul_pos (mul_pos data.edge_positive data.robust_positive)
      data.width_positive
  have κpositive : 0 < κ := by
    dsimp [κ]
    exact div_pos Apositive (mul_pos (by norm_num) data.degree_positive)
  let gap : ℝ := ρ + κ - 1
  have gap_positive : 0 < gap := by
    dsimp [gap, ρ, κ, A]
    linarith [data.strict_margin]
  let γ : ℝ := min (gap / 8) (κ / 4)
  have γpositive : 0 < γ := by
    dsimp [γ]
    exact lt_min (by positivity) (by positivity)
  have γ_gap : γ ≤ gap / 8 := min_le_left _ _
  have γ_capacity : γ ≤ κ / 4 := min_le_right _ _
  let reduced : ℝ := κ - 2 * γ
  have reduced_positive : 0 < reduced := by
    dsimp [reduced]
    linarith
  have reduced_le : reduced ≤ κ := by
    dsimp [reduced]
    linarith
  have reserve_lower : ∀ᶠ n : ℕ in atTop,
      ρ - γ <
        ((Erdos689.canonicalReserve
          data.support data.residue n data.parameter).card : ℝ) /
            ((n : ℝ) / Real.log n) := by
    exact (tendsto_order.mp data.reserve_limit).1
      (ρ - γ) (sub_lt_self ρ γpositive)
  have deficiency_upper : ∀ᶠ n : ℕ in atTop,
      (Erdos689.deficiency n
        (Erdos689.initialAssignment data.support data.residue) : ℝ) /
          ((n : ℝ) / Real.log n) < 1 + γ := by
    exact (tendsto_order.mp data.deficiency_limit).2
      (1 + γ) (by linarith)
  have degree_scale := Erdos689.eventually_logarithmic_scale_dominates_one
    data.degreeConstant data.degree_positive 2
  have matching_scale := Erdos689.eventually_logarithmic_scale_dominates_one
    reduced reduced_positive 1
  have slack_scale := Erdos689.eventually_logarithmic_scale_dominates_one
    γ γpositive 1
  have support_available := Erdos689.eventually_support_primes_available
    data.support (fun p hp => (data.support_valid p hp).1)
  have edge_cutoff :=
    Erdos689.eventually_manuscript_edge_lower_cutoff data.tau_positive
  refine ⟨γ, γpositive, ?_⟩
  filter_upwards [data.eventual_edges, data.eventual_degrees,
    reserve_lower, deficiency_upper, degree_scale, matching_scale,
    slack_scale, support_available, edge_cutoff,
    eventually_ge_atTop 2]
      with n hedge hdegree hreserve hdeficiency hD hk hslack
        hsupport hcutoff hn
  refine ⟨hsupport, hcutoff, ?_⟩
  let X : ℝ := (n : ℝ) / Real.log n
  let Y : ℝ := (n : ℝ) / (Real.log n) ^ 2
  have nreal : (1 : ℝ) < n := by
    exact_mod_cast (by omega : 1 < n)
  have log_positive : 0 < Real.log (n : ℝ) := Real.log_pos nreal
  have Xpositive : 0 < X := by
    dsimp [X]
    positivity
  have Ypositive : 0 < Y := by
    dsimp [Y]
    positivity
  have Dscale : 1 ≤ data.degreeConstant * Y := by
    simpa [Y] using hD
  have kscale : 1 ≤ reduced * X := by
    simpa [X] using hk
  have saved_scale : 1 ≤ γ * X := by
    simpa [X] using hslack
  have edge_identity :
      A * X * Y =
        data.edgeConstant *
          Erdos689.manuscriptRobustDensity
            data.support data.residue data.parameter * data.width *
          (n : ℝ) ^ 2 / (Real.log n) ^ 3 := by
    dsimp [A, X, Y]
    field_simp
  have actual_edges : A * X * Y ≤
      ((Erdos689.robustManuscriptEdges
        data.support data.residue n data.parameter data.tau data.width).card : ℝ) := by
    rw [edge_identity]
    exact hedge
  have actual_degrees :
      Erdos689.actualManuscriptDegreeAtMost
        data.support data.residue data.parameter n data.tau data.width
          (data.degreeConstant * Y) := by
    simpa [Y, div_eq_mul_inv, mul_assoc] using hdegree
  have full_capacity : 3 * data.degreeConstant * κ = A := by
    dsimp [κ]
    field_simp [ne_of_gt data.degree_positive]
  have capacity : 3 * data.degreeConstant * reduced ≤ A := by
    calc
      3 * data.degreeConstant * reduced ≤
          3 * data.degreeConstant * κ :=
            mul_le_mul_of_nonneg_left reduced_le
              (mul_nonneg (by norm_num) data.degree_positive.le)
      _ = A := full_capacity
  have actual_reserve :
      (ρ - γ) * X <
        ((Erdos689.canonicalReserve
          data.support data.residue n data.parameter).card : ℝ) := by
    change ρ - γ < _ / X at hreserve
    exact (lt_div_iff₀ Xpositive).mp hreserve
  have actual_deficiency :
      (Erdos689.deficiency n
        (Erdos689.initialAssignment data.support data.residue) : ℝ) <
        (1 + γ) * X := by
    change _ / X < 1 + γ at hdeficiency
    exact (div_lt_iff₀ Xpositive).mp hdeficiency
  have gap_scaled :
      4 * γ * X ≤ (gap - 4 * γ) * X := by
    apply mul_le_mul_of_nonneg_right _ Xpositive.le
    linarith
  have real_surplus :
      (Erdos689.deficiency n
        (Erdos689.initialAssignment data.support data.residue) : ℝ) +
          4 * γ * X ≤
        ((Erdos689.canonicalReserve
          data.support data.residue n data.parameter).card : ℝ) +
            reduced * X := by
    dsimp [gap, reduced] at gap_scaled ⊢
    nlinarith
  let saved : ℕ := ⌊γ * X⌋₊
  let matching : ℕ := ⌊reduced * X⌋₊
  have saved_upper : (saved : ℝ) ≤ γ * X :=
    Nat.floor_le (mul_nonneg γpositive.le Xpositive.le)
  have matching_lower : reduced * X < (matching : ℝ) + 1 :=
    Nat.lt_floor_add_one (reduced * X)
  have natural_surplus :
      Erdos689.deficiency n
          (Erdos689.initialAssignment data.support data.residue) + saved ≤
        (Erdos689.canonicalReserve
          data.support data.residue n data.parameter).card + matching := by
    have real_bound :
        ((Erdos689.deficiency n
            (Erdos689.initialAssignment data.support data.residue) +
              saved : ℕ) : ℝ) ≤
          (((Erdos689.canonicalReserve
            data.support data.residue n data.parameter).card +
              matching : ℕ) : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast real_bound
  change Nonempty
    (StrictManuscriptScalarData
      data.support data.residue data.parameter data.tau data.width n saved)
  apply strictManuscriptScalarData_of_pointwise_rates
    (X := X) (Y := Y) (A := A) (C := data.degreeConstant)
    (κ := reduced) Xpositive.le Ypositive.le data.degree_positive
      Dscale kscale capacity actual_edges actual_degrees
  exact natural_surplus

/-- UNCONDITIONAL fixed-support positive spare-density witness from the
completed #689 proof.  A genuine growing integer reserve of at least
`floor(γ * n / log n)` can remain after the covering is completed. -/
theorem exists_fixed_support_strict_scalar_margin :
    ∃ (data : FixedSupportAnalyticData) (γ : ℝ), 0 < γ ∧
      ∀ᶠ n : ℕ in atTop,
        (∀ p ∈ data.support, p ≤ n) ∧
          (2 : ℝ) ≤ data.tau * n ∧
          Nonempty
            (StrictManuscriptScalarData
              data.support data.residue data.parameter data.tau data.width n
              ⌊γ * ((n : ℝ) / Real.log n)⌋₊) := by
  obtain ⟨data⟩ := exists_fixed_support_analytic_data
  obtain ⟨γ, hγ, eventual⟩ :=
    fixedSupportAnalyticData_eventual_strict_scalar_margin data
  exact ⟨data, γ, hγ, eventual⟩


end Erdos1139
