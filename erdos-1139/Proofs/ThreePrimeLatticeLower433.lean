module

public import TernaryFourier433

@[expose] public section


/-!
# Quantitative archimedean lattice mass for the manuscript ternary forms

The whole-circle manuscript model has already been identified with the
number of affine lattice triples.  Here we give an explicit injective
rectangle of such triples, retaining the actual coefficient and all three
interval windows.  Consequently this is a quadratic lattice-count lower
bound, not merely positivity from a single witness.
-/

open Finset MeasureTheory
open scoped BigOperators

namespace Erdos689

/-- The least nonnegative shift making `x` divisible by `b`. -/
def affineLatticeResidueOffset (x b : ℕ) : ℕ :=
  (b - x % b) % b

theorem affineLatticeResidueOffset_lt
    (x b : ℕ) (hb : 0 < b) :
    affineLatticeResidueOffset x b < b := by
  exact Nat.mod_lt _ hb

theorem affineLatticeResidueOffset_dvd
    (x b : ℕ) (hb : 0 < b) :
    b ∣ x + affineLatticeResidueOffset x b := by
  have hrem : x % b < b := Nat.mod_lt x hb
  by_cases hzero : x % b = 0
  · rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]
    simp [affineLatticeResidueOffset, hzero]
  · have hpos : 0 < x % b := Nat.pos_of_ne_zero hzero
    have hsub : b - x % b < b := Nat.sub_lt hb hpos
    have hsum : x % b + (b - x % b) = b := by omega
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]
    simp [affineLatticeResidueOffset, Nat.mod_eq_of_lt hsub, hsum]

/-- Every left-window element supports exactly `floor(L / b)` explicitly
selected labels in any label window of length `L`, independently of the
left coefficient.  If their quotients land in the requested center window,
this injective rectangle is a subset of the actual affine triple finset. -/
theorem ternaryAffineTriples_rectangle_card_lower
    (a b leftLower leftUpper labelLower labelUpper
      centerLower centerUpper : ℕ)
    (hb : 0 < b)
    (hlabel : labelLower ≤ labelUpper)
    (hcenter : ∀ q ∈ Finset.Ico leftLower leftUpper,
      ∀ p ∈ Finset.Ico labelLower labelUpper,
        b ∣ a * q + p →
          (a * q + p) / b ∈ Finset.Ico centerLower centerUpper) :
    (leftUpper - leftLower) * ((labelUpper - labelLower) / b) ≤
      (ternaryAffineTriples
        (Finset.Ico leftLower leftUpper)
        (Finset.Ico centerLower centerUpper)
        (Finset.Ico labelLower labelUpper) a b).card := by
  classical
  let L : ℕ := labelUpper - labelLower
  let offset : ℕ → ℕ := fun q =>
    affineLatticeResidueOffset (a * q + labelLower) b
  let label : ℕ → ℕ → ℕ := fun q k => labelLower + offset q + b * k
  let center : ℕ → ℕ → ℕ := fun q k => (a * q + label q k) / b
  let encode : ℕ × ℕ → ℕ × (ℕ × ℕ) := fun v =>
    (v.1, (center v.1 v.2, label v.1 v.2))
  let domain : Finset (ℕ × ℕ) :=
    (Finset.Ico leftLower leftUpper).product (Finset.range (L / b))
  have hinjective : Function.Injective encode := by
    rintro ⟨q, k⟩ ⟨q', k'⟩ heq
    have hfirst : q = q' := by
      simpa [encode] using
        congrArg (fun z : ℕ × (ℕ × ℕ) => z.1) heq
    subst q'
    have hlast : label q k = label q k' := by
      simpa [encode] using
        congrArg (fun z : ℕ × (ℕ × ℕ) => z.2.2) heq
    have hproducts : b * k = b * k' := by
      dsimp [label] at hlast
      omega
    have hsecond : k = k' := Nat.mul_left_cancel hb hproducts
    exact Prod.ext rfl hsecond
  have hsubset : domain.image encode ⊆
      ternaryAffineTriples
        (Finset.Ico leftLower leftUpper)
        (Finset.Ico centerLower centerUpper)
        (Finset.Ico labelLower labelUpper) a b := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    have hdomain := Finset.mem_product.mp hv
    have hleft : v.1 ∈ Finset.Ico leftLower leftUpper := hdomain.1
    have hk : v.2 < L / b := Finset.mem_range.mp hdomain.2
    have hoffset : offset v.1 < b :=
      affineLatticeResidueOffset_lt (a * v.1 + labelLower) b hb
    have hstep : (v.2 + 1) * b ≤ L :=
      (Nat.le_div_iff_mul_le hb).mp (Nat.succ_le_of_lt hk)
    have hlabelbound : label v.1 v.2 ∈
        Finset.Ico labelLower labelUpper := by
      rw [Finset.mem_Ico]
      constructor
      · dsimp [label]
        omega
      · dsimp [label, L] at hstep ⊢
        have htotal : labelLower + (labelUpper - labelLower) = labelUpper := by
          omega
        nlinarith
    have hbase : b ∣ a * v.1 + labelLower + offset v.1 :=
      affineLatticeResidueOffset_dvd (a * v.1 + labelLower) b hb
    have hdivisible : b ∣ a * v.1 + label v.1 v.2 := by
      simpa [label, Nat.add_assoc] using
        dvd_add hbase (dvd_mul_right b v.2)
    have hcenterbound : center v.1 v.2 ∈
        Finset.Ico centerLower centerUpper :=
      hcenter v.1 hleft (label v.1 v.2) hlabelbound hdivisible
    have hequation : a * v.1 + label v.1 v.2 =
        b * center v.1 v.2 := by
      dsimp [center]
      exact (Nat.mul_div_cancel' hdivisible).symm
    change (v.1, (center v.1 v.2, label v.1 v.2)) ∈
      ternaryAffineTriples
        (Finset.Ico leftLower leftUpper)
        (Finset.Ico centerLower centerUpper)
        (Finset.Ico labelLower labelUpper) a b
    apply Finset.mem_filter.mpr
    refine ⟨?_, hequation⟩
    exact Finset.mem_product.mpr
      ⟨hleft, Finset.mem_product.mpr ⟨hcenterbound, hlabelbound⟩⟩
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_image_of_injective _ hinjective] at hcard
  simpa [domain, L, Finset.card_product] using hcard

/-- For an interval containing at least two complete coefficient blocks,
discarding the incomplete residue block loses at most a factor of two. -/
theorem affineLattice_div_lower_half
    (L b : ℕ) (hb : 0 < b) (hL : 2 * b ≤ L) :
    (L : ℝ) / (2 * b : ℝ) ≤ (L / b : ℕ) := by
  have hrem : L % b < b := Nat.mod_lt L hb
  have hdecomposition : b * (L / b) + L % b = L :=
    Nat.div_add_mod L b
  have htwice : L ≤ 2 * (b * (L / b)) := by
    omega
  have hreal : (L : ℝ) ≤ 2 * ((b : ℝ) * (L / b : ℕ)) := by
    exact_mod_cast htwice
  have hdenominator : (0 : ℝ) < 2 * b := by positivity
  apply (div_le_iff₀ hdenominator).mpr
  nlinarith

/-- Explicit coefficient-sensitive quadratic lattice lower bound.  When
the two free interval lengths scale as `n` and `ell*n`, respectively,
this has exactly the manuscript's required `ell*n²` scale. -/
theorem ternaryAffineTriples_rectangle_real_card_lower
    (a b leftLower leftUpper labelLower labelUpper
      centerLower centerUpper : ℕ)
    (hb : 0 < b)
    (hlabel : labelLower ≤ labelUpper)
    (hwidth : 2 * b ≤ labelUpper - labelLower)
    (hcenter : ∀ q ∈ Finset.Ico leftLower leftUpper,
      ∀ p ∈ Finset.Ico labelLower labelUpper,
        b ∣ a * q + p →
          (a * q + p) / b ∈ Finset.Ico centerLower centerUpper) :
    ((leftUpper - leftLower : ℕ) : ℝ) *
        (((labelUpper - labelLower : ℕ) : ℝ) / (2 * b : ℝ)) ≤
      ((ternaryAffineTriples
        (Finset.Ico leftLower leftUpper)
        (Finset.Ico centerLower centerUpper)
        (Finset.Ico labelLower labelUpper) a b).card : ℝ) := by
  have hfloor := affineLattice_div_lower_half
    (labelUpper - labelLower) b hb hwidth
  have hcard := ternaryAffineTriples_rectangle_card_lower
    a b leftLower leftUpper labelLower labelUpper
    centerLower centerUpper hb hlabel hcenter
  have hcardReal :
      ((leftUpper - leftLower : ℕ) : ℝ) *
        (((labelUpper - labelLower) / b : ℕ) : ℝ) ≤
      ((ternaryAffineTriples
        (Finset.Ico leftLower leftUpper)
        (Finset.Ico centerLower centerUpper)
        (Finset.Ico labelLower labelUpper) a b).card : ℝ) := by
    exact_mod_cast hcard
  exact le_trans (mul_le_mul_of_nonneg_left hfloor (by positivity)) hcardReal

/-- A simple endpoint test places every divisible affine quotient in the
actual ambient positive window `1 ≤ q' ≤ n`. -/
theorem affineLattice_positive_window_of_fit
    (n a b leftLower leftUpper labelLower labelUpper : ℕ)
    (hb : 0 < b)
    (hpositive : 0 < labelLower)
    (hfit : a * leftUpper + labelUpper ≤ n) :
    ∀ q ∈ Finset.Ico leftLower leftUpper,
      ∀ p ∈ Finset.Ico labelLower labelUpper,
        b ∣ a * q + p →
          (a * q + p) / b ∈ Finset.Ico 1 (n + 1) := by
  intro q hq p hp hdivisible
  have hqbound := (Finset.mem_Ico.mp hq).2
  have hpbound := Finset.mem_Ico.mp hp
  have hnumpos : 0 < a * q + p := by omega
  have hnumle : a * q + p ≤ n := by
    have hmul : a * q ≤ a * leftUpper :=
      Nat.mul_le_mul_left a (Nat.le_of_lt hqbound)
    omega
  have hquotientpos : 0 < (a * q + p) / b :=
    Nat.div_pos (Nat.le_of_dvd hnumpos hdivisible) hb
  have hquotientle := Nat.div_le_self (a * q + p) b
  rw [Finset.mem_Ico]
  omega

/-- A simple endpoint fit gives the quadratic lattice rectangle inside the
actual ambient positive window `1 ≤ q' ≤ n`.  In the manuscript strip one
has `a*q ≤ n/5` and `P < n/10`. -/
theorem ternaryAffineTriples_positive_window_card_lower
    (n a b leftLower leftUpper labelLower labelUpper : ℕ)
    (hb : 0 < b)
    (hlabel : labelLower ≤ labelUpper)
    (hpositive : 0 < labelLower)
    (hfit : a * leftUpper + labelUpper ≤ n) :
    (leftUpper - leftLower) * ((labelUpper - labelLower) / b) ≤
      (ternaryAffineTriples
        (Finset.Ico leftLower leftUpper)
        (Finset.Ico 1 (n + 1))
        (Finset.Ico labelLower labelUpper) a b).card := by
  exact ternaryAffineTriples_rectangle_card_lower
    a b leftLower leftUpper labelLower labelUpper 1 (n + 1)
    hb hlabel
    (affineLattice_positive_window_of_fit
      n a b leftLower leftUpper labelLower labelUpper
      hb hpositive hfit)

/-- Quantitative whole-circle singular-integral lower bound for the actual
manuscript coefficient `2*d`.  The three windows are precisely those of
`ternary_manuscript_interval_model_singular_integral`; no coefficient or
residue-cell density is discarded. -/
theorem ternary_manuscript_interval_model_singular_integral_rectangle_lower
    (modulus labelResidue leftResidue centerResidue a d : ℕ)
    (hmodulus : 0 < modulus)
    (hadmissible :
      (a * leftResidue + labelResidue) % modulus =
        (2 * d * centerResidue) % modulus)
    (labelLower labelUpper leftLower leftUpper centerLower centerUpper : ℕ)
    (hd : 0 < d)
    (hlabel : labelLower ≤ labelUpper)
    (hwidth : 4 * d ≤ labelUpper - labelLower)
    (hcenter : ∀ q ∈ Finset.Ico leftLower leftUpper,
      ∀ p ∈ Finset.Ico labelLower labelUpper,
        2 * d ∣ a * q + p →
          (a * q + p) / (2 * d) ∈ Finset.Ico centerLower centerUpper)
    (numerator : ℤ) :
    (1 / (modulus.totient : ℝ)) ^ 3 *
      (((leftUpper - leftLower : ℕ) : ℝ) *
        (((labelUpper - labelLower : ℕ) : ℝ) / (4 * d : ℝ))) ≤
      (∫ β in (0 : ℝ)..1,
        ternaryMajorArcIntervalModel
            labelLower labelUpper modulus labelResidue 1 numerator β *
          ternaryMajorArcIntervalModel
            leftLower leftUpper modulus leftResidue (a : ℤ) numerator β *
          ternaryMajorArcIntervalModel
            centerLower centerUpper modulus centerResidue
            (-2 * (d : ℤ)) numerator β).re := by
  have hcoefficient : 0 < 2 * d := by omega
  have hwidth' : 2 * (2 * d) ≤ labelUpper - labelLower := by omega
  have hcard := ternaryAffineTriples_rectangle_real_card_lower
    a (2 * d) leftLower leftUpper labelLower labelUpper
    centerLower centerUpper hcoefficient hlabel hwidth' hcenter
  have hcard' :
      (((leftUpper - leftLower : ℕ) : ℝ) *
        (((labelUpper - labelLower : ℕ) : ℝ) / (4 * d : ℝ))) ≤
      ((ternaryAffineTriples
        (Finset.Ico leftLower leftUpper)
        (Finset.Ico centerLower centerUpper)
        (Finset.Ico labelLower labelUpper) a (2 * d)).card : ℝ) := by
    convert hcard using 1
    push_cast
    ring
  rw [ternary_manuscript_interval_model_singular_integral
    modulus labelResidue leftResidue centerResidue a d hmodulus hadmissible
    labelLower labelUpper leftLower leftUpper centerLower centerUpper numerator]
  have hcast :
      (1 / (modulus.totient : ℂ)) ^ 3 *
          ((ternaryAffineTriples
            (Finset.Ico leftLower leftUpper)
            (Finset.Ico centerLower centerUpper)
            (Finset.Ico labelLower labelUpper)
            a (2 * d)).card : ℂ) =
        (((1 / (modulus.totient : ℝ)) ^ 3 *
          ((ternaryAffineTriples
            (Finset.Ico leftLower leftUpper)
            (Finset.Ico centerLower centerUpper)
            (Finset.Ico labelLower labelUpper)
            a (2 * d)).card : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_left hcard' (by positivity)

/-- Exact, nondegenerate rational manuscript windows.  At
`n = 10*a*Q*m`, the left window is exactly `n/(10*a) ≤ q < n/(5*a)`
and the label window is exactly `tau*n < P ≤ (tau+ell)*n` for
`tau = u/Q`, `ell = v/Q`. -/
theorem ternaryAffineTriples_rational_manuscript_card_lower
    (a d Q u v m : ℕ)
    (ha : 0 < a)
    (hd : 0 < d)
    (hm : 0 < m)
    (hstrip : 10 * (u + v) < Q) :
    Q * m * ((10 * a * v * m) / (2 * d)) ≤
      (ternaryAffineTriples
        (Finset.Ico (Q * m) (2 * Q * m))
        (Finset.Ico 1 (10 * a * Q * m + 1))
        (Finset.Ico
          (10 * a * u * m + 1)
          (10 * a * (u + v) * m + 1))
        a (2 * d)).card := by
  have hcoefficient : 0 < 2 * d := by omega
  have hlabel : 10 * a * u * m + 1 ≤
      10 * a * (u + v) * m + 1 := by
    have hexpand : 10 * a * (u + v) * m =
        10 * a * u * m + 10 * a * v * m := by ring
    omega
  have hscaled : 10 * a * (u + v) * m < a * Q * m := by
    have h := Nat.mul_lt_mul_of_pos_left hstrip (Nat.mul_pos ha hm)
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  have hfit : a * (2 * Q * m) +
      (10 * a * (u + v) * m + 1) ≤ 10 * a * Q * m := by
    nlinarith
  have hcard := ternaryAffineTriples_positive_window_card_lower
    (10 * a * Q * m) a (2 * d)
    (Q * m) (2 * Q * m)
    (10 * a * u * m + 1) (10 * a * (u + v) * m + 1)
    hcoefficient hlabel (by omega) hfit
  have hleftwidth : 2 * Q * m - Q * m = Q * m := by
    have hdouble : 2 * Q * m = Q * m + Q * m := by ring
    omega
  have hlabelwidth :
      (10 * a * (u + v) * m + 1) - (10 * a * u * m + 1) =
        10 * a * v * m := by
    have hexpand : 10 * a * (u + v) * m =
        10 * a * u * m + 10 * a * v * m := by ring
    omega
  simpa [hleftwidth, hlabelwidth] using hcard

/-- Concrete quantitative lattice mass in the exact rational manuscript
strip: `ell*n²/(40*a*d)`, retaining both support-divisor coefficients.
The scale `n=10*a*Q*m` is nonzero and the strip is genuine whenever
`10*(u+v)<Q` and `v>0`; `4*d≤10*a*v*m` merely discards rounding loss. -/
theorem ternaryAffineTriples_rational_manuscript_quadratic_lower
    (a d Q u v m : ℕ)
    (ha : 0 < a)
    (hd : 0 < d)
    (hQ : 0 < Q)
    (hm : 0 < m)
    (hstrip : 10 * (u + v) < Q)
    (hwidth : 4 * d ≤ 10 * a * v * m) :
    ((v : ℝ) / Q) * ((10 * a * Q * m : ℕ) : ℝ) ^ 2 /
        (40 * (a : ℝ) * d) ≤
      ((ternaryAffineTriples
        (Finset.Ico (Q * m) (2 * Q * m))
        (Finset.Ico 1 (10 * a * Q * m + 1))
        (Finset.Ico
          (10 * a * u * m + 1)
          (10 * a * (u + v) * m + 1))
        a (2 * d)).card : ℝ) := by
  have hcoefficient : 0 < 2 * d := by omega
  have hfloor := affineLattice_div_lower_half
    (10 * a * v * m) (2 * d) hcoefficient (by omega)
  have hcard := ternaryAffineTriples_rational_manuscript_card_lower
    a d Q u v m ha hd hm hstrip
  have hcardReal :
      ((Q * m : ℕ) : ℝ) *
        (((10 * a * v * m) / (2 * d) : ℕ) : ℝ) ≤
      ((ternaryAffineTriples
        (Finset.Ico (Q * m) (2 * Q * m))
        (Finset.Ico 1 (10 * a * Q * m + 1))
        (Finset.Ico
          (10 * a * u * m + 1)
          (10 * a * (u + v) * m + 1))
        a (2 * d)).card : ℝ) := by
    exact_mod_cast hcard
  have hrectangle := le_trans
    (mul_le_mul_of_nonneg_left hfloor
      (by positivity : (0 : ℝ) ≤ ((Q * m : ℕ) : ℝ)))
    hcardReal
  have hQreal : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hareal : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hdreal : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hidentity :
      ((v : ℝ) / Q) * ((10 * a * Q * m : ℕ) : ℝ) ^ 2 /
          (40 * (a : ℝ) * d) =
        ((Q * m : ℕ) : ℝ) *
          (((10 * a * v * m : ℕ) : ℝ) / (2 * (2 * d) : ℝ)) := by
    push_cast
    field_simp [hQreal, hareal, hdreal]
    ring
  rw [hidentity]
  exact_mod_cast hrectangle

/-- Every triple in the preceding rational windows satisfies, verbatim,
the manuscript's actual ambient bounds and its strict/weak archimedean
strip for `tau=u/Q`, `ell=v/Q`; the label is the genuine non-underflowing
difference `2*d*q' - a*q`. -/
theorem ternaryAffineTriples_rational_manuscript_actual_strip
    (a d Q u v m q q' p : ℕ)
    (ha : 0 < a)
    (hQ : 0 < Q)
    (hm : 0 < m)
    (htriple :
      (q, (q', p)) ∈ ternaryAffineTriples
        (Finset.Ico (Q * m) (2 * Q * m))
        (Finset.Ico 1 (10 * a * Q * m + 1))
        (Finset.Ico
          (10 * a * u * m + 1)
          (10 * a * (u + v) * m + 1))
        a (2 * d)) :
    q ∈ Finset.Icc 1 (10 * a * Q * m) ∧
      q' ∈ Finset.Icc 1 (10 * a * Q * m) ∧
      ((10 * a * Q * m : ℕ) : ℝ) / 10 ≤ (a * q : ℕ) ∧
      ((a * q : ℕ) : ℝ) ≤ ((10 * a * Q * m : ℕ) : ℝ) / 5 ∧
      ((u : ℝ) / Q) * ((10 * a * Q * m : ℕ) : ℝ) <
        ((2 * d * q' - a * q : ℕ) : ℝ) ∧
      ((2 * d * q' - a * q : ℕ) : ℝ) ≤
        (((u : ℝ) / Q) + ((v : ℝ) / Q)) *
          ((10 * a * Q * m : ℕ) : ℝ) := by
  have hfiltered := Finset.mem_filter.mp htriple
  have hmembers := Finset.mem_product.mp hfiltered.1
  have hrest := Finset.mem_product.mp hmembers.2
  have hleft : Q * m ≤ q ∧ q < 2 * Q * m := by
    simpa using Finset.mem_Ico.mp hmembers.1
  have hcenter : 1 ≤ q' ∧ q' < 10 * a * Q * m + 1 := by
    simpa using Finset.mem_Ico.mp hrest.1
  have hlabel : 10 * a * u * m + 1 ≤ p ∧
      p < 10 * a * (u + v) * m + 1 := by
    simpa using Finset.mem_Ico.mp hrest.2
  have hequation : a * q + p = 2 * d * q' := by
    simpa using hfiltered.2
  have hsub : 2 * d * q' - a * q = p := by omega
  have hqpositive : 0 < q := by
    have hblock : 0 < Q * m := Nat.mul_pos hQ hm
    omega
  have hscale : 2 * Q * m ≤ 10 * a * Q * m := by
    have hfactor : 2 ≤ 10 * a := by omega
    have h := Nat.mul_le_mul_right (Q * m) hfactor
    simpa [Nat.mul_assoc] using h
  have hqbound : q ≤ 10 * a * Q * m := by omega
  have hleftlower : a * (Q * m) ≤ a * q :=
    Nat.mul_le_mul_left a hleft.1
  have hleftupper : a * q ≤ 2 * a * Q * m := by
    have h := Nat.mul_le_mul_left a (Nat.le_of_lt hleft.2)
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  have hlowerreal :
      ((10 * a * Q * m : ℕ) : ℝ) / 10 =
        ((a * (Q * m) : ℕ) : ℝ) := by
    push_cast
    ring
  have hupperreal :
      ((10 * a * Q * m : ℕ) : ℝ) / 5 =
        ((2 * a * Q * m : ℕ) : ℝ) := by
    push_cast
    ring
  have hQreal : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have htaureal :
      ((u : ℝ) / Q) * ((10 * a * Q * m : ℕ) : ℝ) =
        ((10 * a * u * m : ℕ) : ℝ) := by
    push_cast
    field_simp [hQreal]
  have htopreal :
      (((u : ℝ) / Q) + ((v : ℝ) / Q)) *
          ((10 * a * Q * m : ℕ) : ℝ) =
        ((10 * a * (u + v) * m : ℕ) : ℝ) := by
    push_cast
    field_simp [hQreal]
  refine ⟨Finset.mem_Icc.mpr ⟨hqpositive, hqbound⟩,
    Finset.mem_Icc.mpr ⟨hcenter.1, by omega⟩, ?_, ?_, ?_, ?_⟩
  · rw [hlowerreal]
    exact_mod_cast hleftlower
  · rw [hupperreal]
    exact_mod_cast hleftupper
  · rw [hsub, htaureal]
    exact_mod_cast (show 10 * a * u * m < p by omega)
  · rw [hsub, htopreal]
    exact_mod_cast (show p ≤ 10 * a * (u + v) * m by omega)

/-- The rational specialization has exactly the manuscript's admissible
parameter regime, rather than satisfying the strip only formally. -/
theorem rational_manuscript_parameter_bounds
    (Q u v : ℕ)
    (hQ : 0 < Q)
    (hv : 0 < v)
    (hstrip : 10 * (u + v) < Q) :
    0 ≤ (u : ℝ) / Q ∧
      0 < (v : ℝ) / Q ∧
      ((u : ℝ) / Q) + ((v : ℝ) / Q) < (1 : ℝ) / 10 := by
  have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hvreal : (0 : ℝ) < v := by exact_mod_cast hv
  have hstripreal : (10 : ℝ) * ((u : ℝ) + v) < Q := by
    exact_mod_cast hstrip
  refine ⟨by positivity, div_pos hvreal hQreal, ?_⟩
  have hsum : ((u : ℝ) / Q) + ((v : ℝ) / Q) =
      ((u : ℝ) + v) / Q := by ring
  rw [hsum]
  apply (div_lt_iff₀ hQreal).mpr
  nlinarith

/-- The exact admissible-residue, whole-circle manuscript model in a genuine
rational manuscript strip has archimedean mass at least
`phi(W)^(-3) * ell*n²/(40*a*d)`.  This is a quantitative singular-
integral bound, not a major-arc approximation for prime weights. -/
theorem ternary_manuscript_rational_strip_singular_integral_quadratic_lower
    (modulus labelResidue leftResidue centerResidue a d Q u v m : ℕ)
    (hmodulus : 0 < modulus)
    (hadmissible :
      (a * leftResidue + labelResidue) % modulus =
        (2 * d * centerResidue) % modulus)
    (ha : 0 < a)
    (hd : 0 < d)
    (hQ : 0 < Q)
    (hm : 0 < m)
    (hstrip : 10 * (u + v) < Q)
    (hwidth : 4 * d ≤ 10 * a * v * m)
    (numerator : ℤ) :
    (1 / (modulus.totient : ℝ)) ^ 3 *
      (((v : ℝ) / Q) * ((10 * a * Q * m : ℕ) : ℝ) ^ 2 /
        (40 * (a : ℝ) * d)) ≤
      (∫ β in (0 : ℝ)..1,
        ternaryMajorArcIntervalModel
            (10 * a * u * m + 1)
            (10 * a * (u + v) * m + 1)
            modulus labelResidue 1 numerator β *
          ternaryMajorArcIntervalModel
            (Q * m) (2 * Q * m)
            modulus leftResidue (a : ℤ) numerator β *
          ternaryMajorArcIntervalModel
            1 (10 * a * Q * m + 1)
            modulus centerResidue (-2 * (d : ℤ)) numerator β).re := by
  have hcard := ternaryAffineTriples_rational_manuscript_quadratic_lower
    a d Q u v m ha hd hQ hm hstrip hwidth
  rw [ternary_manuscript_interval_model_singular_integral
    modulus labelResidue leftResidue centerResidue a d hmodulus hadmissible
    (10 * a * u * m + 1) (10 * a * (u + v) * m + 1)
    (Q * m) (2 * Q * m) 1 (10 * a * Q * m + 1) numerator]
  have hcast :
      (1 / (modulus.totient : ℂ)) ^ 3 *
          ((ternaryAffineTriples
            (Finset.Ico (Q * m) (2 * Q * m))
            (Finset.Ico 1 (10 * a * Q * m + 1))
            (Finset.Ico
              (10 * a * u * m + 1)
              (10 * a * (u + v) * m + 1))
            a (2 * d)).card : ℂ) =
        (((1 / (modulus.totient : ℝ)) ^ 3 *
          ((ternaryAffineTriples
            (Finset.Ico (Q * m) (2 * Q * m))
            (Finset.Ico 1 (10 * a * Q * m + 1))
            (Finset.Ico
              (10 * a * u * m + 1)
              (10 * a * (u + v) * m + 1))
            a (2 * d)).card : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_left hcard (by positivity)

/-- The hypotheses of the genuine rational manuscript-strip lower bound
are jointly satisfiable; this instance already contains at least 150
distinct affine lattice solutions with `n=300`, `tau=ell=1/30`. -/
theorem ternaryAffineTriples_rational_manuscript_nonvacuous :
    150 ≤
      (ternaryAffineTriples
        (Finset.Ico 30 60)
        (Finset.Ico 1 301)
        (Finset.Ico 11 21)
        1 2).card := by
  have h := ternaryAffineTriples_rational_manuscript_card_lower
    1 1 30 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h


end Erdos689
