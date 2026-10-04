module

public import ExactStripMinorArcs433
public import ThreePrimeLatticeLower433

@[expose] public section


/-!
# All-scale, arbitrary-real manuscript-strip archimedean mass

The older genuine-strip lattice bound used rational parameters and endpoints
restricted to one arithmetic subsequence.  Here the actual strict/weak label
strip is encoded by natural floors for arbitrary real `τ, ell`, while an
explicit integer left block works at every sufficiently large original `n`.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos689

/-- The exact first integer strictly above the real manuscript label floor. -/
noncomputable def manuscriptRealLabelLower (τ : ℝ) (n : ℕ) : ℕ :=
  Nat.floor (τ * (n : ℝ)) + 1

/-- The half-open endpoint encoding the weak upper manuscript inequality. -/
noncomputable def manuscriptRealLabelUpper (τ ell : ℝ) (n : ℕ) : ℕ :=
  Nat.floor ((τ + ell) * (n : ℝ)) + 1

/-- One complete positive left block inside `n/10 < a*q ≤ n/5`. -/
def manuscriptRealLeftBlock (a n : ℕ) : ℕ := n / (10 * a)

/-- The exact real strict/weak label strip is a genuine integer half-open
window; neither rationality nor an endpoint divisibility assumption occurs. -/
theorem mem_manuscriptRealLabelWindow_iff
    (τ ell : ℝ) (n p : ℕ) (hτ : 0 ≤ τ) (hell : 0 ≤ ell) :
    p ∈ Finset.Ico (manuscriptRealLabelLower τ n)
          (manuscriptRealLabelUpper τ ell n) ↔
      τ * (n : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (τ + ell) * n := by
  have hlow : 0 ≤ τ * (n : ℝ) := by positivity
  have hhigh : 0 ≤ (τ + ell) * (n : ℝ) := by positivity
  rw [Finset.mem_Ico]
  constructor
  · intro h
    have hleft : Nat.floor (τ * (n : ℝ)) < p := by
      dsimp [manuscriptRealLabelLower] at h
      omega
    have hright : p ≤ Nat.floor ((τ + ell) * (n : ℝ)) := by
      dsimp [manuscriptRealLabelUpper] at h
      omega
    exact ⟨(Nat.floor_lt hlow).mp hleft,
      (Nat.le_floor_iff hhigh).mp hright⟩
  · rintro ⟨hleft, hright⟩
    have hfloorleft : Nat.floor (τ * (n : ℝ)) < p :=
      (Nat.floor_lt hlow).mpr hleft
    have hfloorright : p ≤ Nat.floor ((τ + ell) * (n : ℝ)) :=
      (Nat.le_floor_iff hhigh).mpr hright
    dsimp [manuscriptRealLabelLower, manuscriptRealLabelUpper]
    omega

/-- Every member of the all-scale integer left block satisfies the actual
manuscript coefficient window, with the stronger strict lower inequality. -/
theorem manuscriptRealLeftWindow_bounds
    (a n q : ℕ) (ha : 0 < a)
    (hq : q ∈ Finset.Ico (manuscriptRealLeftBlock a n + 1)
      (2 * manuscriptRealLeftBlock a n + 1)) :
    (n : ℝ) / 10 < ((a * q : ℕ) : ℝ) ∧
      ((a * q : ℕ) : ℝ) ≤ (n : ℝ) / 5 := by
  let K := manuscriptRealLeftBlock a n
  have hmember := Finset.mem_Ico.mp hq
  have hdenominator : 0 < 10 * a := by omega
  have hlower : n < q * (10 * a) := by
    apply (Nat.div_lt_iff_lt_mul hdenominator).mp
    change manuscriptRealLeftBlock a n < q
    omega
  have hblock : 10 * a * K ≤ n := Nat.mul_div_le n (10 * a)
  have hupper : 5 * (a * q) ≤ n := by
    have hqblock : q ≤ 2 * K := by omega
    have hscaled := Nat.mul_le_mul_left (5 * a) hqblock
    nlinarith
  constructor
  · have hreal : (n : ℝ) < 10 * ((a * q : ℕ) : ℝ) := by
      exact_mod_cast (by nlinarith : n < 10 * (a * q))
    linarith
  · have hreal : 5 * ((a * q : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hupper
    linarith

/-- Every sufficiently large real manuscript label interval has at least
half of its genuine linear width, uniformly without rational approximations. -/
theorem manuscriptRealLabelWindow_width_eventually
    (τ ell : ℝ) (hτ : 0 ≤ τ) (hell : 0 < ell) :
    ∀ᶠ n : ℕ in atTop,
      ell * (n : ℝ) / 2 ≤
        ((manuscriptRealLabelUpper τ ell n -
          manuscriptRealLabelLower τ n : ℕ) : ℝ) := by
  have hscale := (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [(tendsto_atTop.1 hscale (2 / ell))] with n hn
  let low := manuscriptRealLabelLower τ n
  let high := manuscriptRealLabelUpper τ ell n
  have hlowpos : 0 ≤ τ * (n : ℝ) := by positivity
  have hhighpos : 0 ≤ (τ + ell) * (n : ℝ) := by positivity
  have horder : low ≤ high := by
    dsimp [low, high, manuscriptRealLabelLower, manuscriptRealLabelUpper]
    have hfloor := Nat.floor_mono
      (show τ * (n : ℝ) ≤ (τ + ell) * n by nlinarith)
    omega
  have hfloorlow :
      (Nat.floor (τ * (n : ℝ)) : ℝ) ≤ τ * n := Nat.floor_le hlowpos
  have hfloorhigh :
      (τ + ell) * (n : ℝ) <
        (Nat.floor ((τ + ell) * (n : ℝ)) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hwidth : ((high - low : ℕ) : ℝ) =
      (Nat.floor ((τ + ell) * (n : ℝ)) : ℝ) -
        (Nat.floor (τ * (n : ℝ)) : ℝ) := by
    rw [Nat.cast_sub horder]
    dsimp [low, high, manuscriptRealLabelLower, manuscriptRealLabelUpper]
    push_cast
    ring
  rw [hwidth]
  have hlarge : 2 ≤ ell * (n : ℝ) := by
    have := (div_le_iff₀ hell).mp hn
    nlinarith
  nlinarith

/-- The all-scale integer left block has at least half its ideal length once
the original endpoint exceeds two complete coefficient blocks. -/
theorem manuscriptRealLeftBlock_real_lower
    (a n : ℕ) (ha : 0 < a) (hn : 20 * a ≤ n) :
    (n : ℝ) / (20 * (a : ℝ)) ≤ manuscriptRealLeftBlock a n := by
  have hdenominator : 0 < 10 * a := by omega
  have hwidth : 2 * (10 * a) ≤ n := by omega
  have h := affineLattice_div_lower_half n (10 * a) hdenominator hwidth
  change (n : ℝ) / (20 * (a : ℝ)) ≤ ((n / (10 * a) : ℕ) : ℝ)
  convert h using 1
  · push_cast
    ring

/-- The exact arbitrary-real, all-endpoint manuscript strip has genuine
quadratic affine lattice mass with absolute coefficient-sensitive constant
`1/160`; no rational parameter or special endpoint subsequence is used. -/
theorem ternaryAffineTriples_real_manuscript_all_scales_quadratic_lower
    (a d : ℕ) (τ ell : ℝ)
    (ha : 0 < a) (hd : 0 < d)
    (hτ : 0 < τ) (hell : 0 < ell)
    (hstrip : τ + ell < (1 : ℝ) / 10) :
    ∀ᶠ n : ℕ in atTop,
      ell * (n : ℝ) ^ 2 / (160 * (a : ℝ) * d) ≤
        ((ternaryAffineTriples
          (Finset.Ico (manuscriptRealLeftBlock a n + 1)
            (2 * manuscriptRealLeftBlock a n + 1))
          (Finset.Ico 1 (n + 1))
          (Finset.Ico (manuscriptRealLabelLower τ n)
            (manuscriptRealLabelUpper τ ell n))
          a (2 * d)).card : ℝ) := by
  have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
  filter_upwards
    [eventually_ge_atTop (20 * a),
      manuscriptRealLabelWindow_width_eventually τ ell hτ.le hell,
      (tendsto_atTop.1 hcast ((8 * (d : ℝ)) / ell))]
    with n hn hlabelwidth hlarge
  let K := manuscriptRealLeftBlock a n
  let low := manuscriptRealLabelLower τ n
  let high := manuscriptRealLabelUpper τ ell n
  have hK := manuscriptRealLeftBlock_real_lower a n ha hn
  have horder : low ≤ high := by
    dsimp [low, high, manuscriptRealLabelLower, manuscriptRealLabelUpper]
    have hfloor := Nat.floor_mono
      (show τ * (n : ℝ) ≤ (τ + ell) * n by nlinarith)
    omega
  have hcoefficient : 0 < 2 * d := by omega
  have hwidthReal : (4 * d : ℝ) ≤ ((high - low : ℕ) : ℝ) := by
    have hlinear : (8 * (d : ℝ)) ≤ ell * n := by
      have := (div_le_iff₀ hell).mp hlarge
      nlinarith
    dsimp [low, high]
    nlinarith
  have hwidth : 2 * (2 * d) ≤ high - low := by
    have h : 4 * d ≤ high - low := by exact_mod_cast hwidthReal
    omega
  have hcenter : ∀ q ∈ Finset.Ico (K + 1) (2 * K + 1),
      ∀ p ∈ Finset.Ico low high,
        2 * d ∣ a * q + p →
          (a * q + p) / (2 * d) ∈ Finset.Ico 1 (n + 1) := by
    intro q hq p hp hdivisible
    have hqbounds := manuscriptRealLeftWindow_bounds a n q ha hq
    have hpbounds := (mem_manuscriptRealLabelWindow_iff
      τ ell n p hτ.le hell.le).mp hp
    have hpositive : 0 < a * q + p := by
      have hpcast : (0 : ℝ) < p := lt_of_le_of_lt
        (by positivity : (0 : ℝ) ≤ τ * n) hpbounds.1
      have hpnat : 0 < p := by exact_mod_cast hpcast
      omega
    have hsumreal : ((a * q + p : ℕ) : ℝ) < (n : ℝ) := by
      push_cast
      have hlabel : (p : ℝ) < (n : ℝ) / 10 :=
        hpbounds.2.trans_lt (by
          nlinarith [show (0 : ℝ) ≤ n by positivity])
      have hqreal := hqbounds.2
      push_cast at hqreal
      nlinarith
    have hsum : a * q + p ≤ n := by
      have hcastlt : (a * q + p : ℕ) < n := by exact_mod_cast hsumreal
      omega
    have hquotientpos : 0 < (a * q + p) / (2 * d) :=
      Nat.div_pos (Nat.le_of_dvd hpositive hdivisible) hcoefficient
    have hquotientle := Nat.div_le_self (a * q + p) (2 * d)
    rw [Finset.mem_Ico]
    omega
  have hrectangle := ternaryAffineTriples_rectangle_real_card_lower
    a (2 * d) (K + 1) (2 * K + 1) low high 1 (n + 1)
      hcoefficient horder hwidth hcenter
  have hleftwidth : (2 * K + 1) - (K + 1) = K := by omega
  rw [hleftwidth] at hrectangle
  have hdenominator : (0 : ℝ) < 4 * d := by positivity
  have hlabelhalf : ell * (n : ℝ) / 2 ≤ ((high - low : ℕ) : ℝ) :=
    hlabelwidth
  calc
    ell * (n : ℝ) ^ 2 / (160 * (a : ℝ) * d) =
        ((n : ℝ) / (20 * a)) *
          ((ell * (n : ℝ) / 2) / (4 * d)) := by
      field_simp
      ring
    _ ≤ (K : ℝ) * (((high - low : ℕ) : ℝ) / (4 * d)) := by
      gcongr
    _ ≤ ((ternaryAffineTriples
          (Finset.Ico (K + 1) (2 * K + 1))
          (Finset.Ico 1 (n + 1))
          (Finset.Ico low high) a (2 * d)).card : ℝ) := by
      convert hrectangle using 1
      push_cast
      ring

end Erdos689

#print axioms Erdos689.mem_manuscriptRealLabelWindow_iff
#print axioms Erdos689.manuscriptRealLeftWindow_bounds
#print axioms Erdos689.manuscriptRealLabelWindow_width_eventually
#print axioms Erdos689.manuscriptRealLeftBlock_real_lower
#print axioms Erdos689.ternaryAffineTriples_real_manuscript_all_scales_quadratic_lower
