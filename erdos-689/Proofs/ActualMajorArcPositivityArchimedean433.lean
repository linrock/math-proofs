import ActualMajorArcPositivityError433
import ActualLeftVertexMajorCubicModel433

/-!
# The genuine edge-bounded archimedean singular integral

The actual manuscript left and center windows end at `n/(2*a)` and
`n/(4*d)`, while the prime label has the original arbitrary-real
strict/weak strip.  The smooth affine lattice count in THESE exact windows
has a uniform quadratic lower bound at every sufficiently large original
endpoint.  Its whole-circle singular integral is exactly that count.

A truncated rational major arc is not the whole circle: its signed
complement is retained, and no full major-arc positivity is asserted.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos689

/-- The true coefficient-sensitive original left edge window. -/
def actualMajorArcArchimedeanLeftWindow (a n : ℕ) : Finset ℕ :=
  Finset.Ico 1 (n / (2 * a) + 1)

/-- The true coefficient-sensitive original center edge window. -/
def actualMajorArcArchimedeanCenterWindow (d n : ℕ) : Finset ℕ :=
  Finset.Ico 1 (n / (4 * d) + 1)

/-- The original label strip with its strict lower and weak upper endpoint. -/
noncomputable def actualMajorArcArchimedeanLabelWindow
    (τ ell : ℝ) (n : ℕ) : Finset ℕ :=
  Finset.Ico (manuscriptRealLabelLower τ n)
    (manuscriptRealLabelUpper τ ell n)

/-- Every true all-scale manuscript block solution already satisfies BOTH
actual edge bounds `2*a*q≤n` and `4*d*r≤n`; the unrestricted center window
in the earlier lattice theorem can therefore be replaced by its real edge
endpoint without losing any constructed witness. -/
theorem actualMajorArcArchimedean_block_triples_subset_true_edges
    (a d n : ℕ) (τ ell : ℝ)
    (ha : 0 < a) (hd : 0 < d)
    (hτ : 0 < τ) (hell : 0 < ell)
    (hstrip : τ + ell < (1 : ℝ) / 10) :
    ternaryAffineTriples
        (Finset.Ico (manuscriptRealLeftBlock a n + 1)
          (2 * manuscriptRealLeftBlock a n + 1))
        (Finset.Ico 1 (n + 1))
        (actualMajorArcArchimedeanLabelWindow τ ell n)
        a (2 * d) ⊆
      ternaryAffineTriples
        (actualMajorArcArchimedeanLeftWindow a n)
        (actualMajorArcArchimedeanCenterWindow d n)
        (actualMajorArcArchimedeanLabelWindow τ ell n)
        a (2 * d) := by
  intro v hv
  obtain ⟨hproduct, hequation⟩ := Finset.mem_filter.mp hv
  obtain ⟨hleft, hremaining⟩ := Finset.mem_product.mp hproduct
  obtain ⟨hcenter, hlabel⟩ := Finset.mem_product.mp hremaining
  have hleftBounds := manuscriptRealLeftWindow_bounds
    a n v.1 ha hleft
  have hlabelBounds :=
    (mem_manuscriptRealLabelWindow_iff
      τ ell n v.2.2 hτ.le hell.le).mp hlabel
  have hleftFive : 5 * (a * v.1) ≤ n := by
    have hreal : (5 : ℝ) * (a * v.1 : ℕ) ≤ n := by
      nlinarith [hleftBounds.2]
    exact_mod_cast hreal
  have hlabelTen : 10 * v.2.2 ≤ n := by
    have hreal : (10 : ℝ) * v.2.2 ≤ n := by
      have hscaled :=
        mul_le_mul_of_nonneg_right hstrip.le
          (show (0 : ℝ) ≤ n by positivity)
      nlinarith [hlabelBounds.2]
    exact_mod_cast hreal
  have hleftEdge : 2 * (a * v.1) ≤ n := by omega
  have hcenterEdge : 4 * d * v.2.1 ≤ n := by
    nlinarith [hequation]
  have hleftPositive : 0 < v.1 := by
    have h := (Finset.mem_Ico.mp hleft).1
    omega
  have hcenterPositive : 0 < v.2.1 :=
    (Finset.mem_Ico.mp hcenter).1
  unfold ternaryAffineTriples
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_,
    Finset.mem_product.mpr ⟨?_, hlabel⟩⟩, hequation⟩
  · unfold actualMajorArcArchimedeanLeftWindow
    apply Finset.mem_Ico.mpr
    refine ⟨hleftPositive, ?_⟩
    have hdiv : v.1 ≤ n / (2 * a) := by
      apply (Nat.le_div_iff_mul_le (by omega)).mpr
      nlinarith [hleftEdge]
    omega
  · unfold actualMajorArcArchimedeanCenterWindow
    apply Finset.mem_Ico.mpr
    refine ⟨hcenterPositive, ?_⟩
    have hdiv : v.2.1 ≤ n / (4 * d) := by
      apply (Nat.le_div_iff_mul_le (by omega)).mpr
      nlinarith [hcenterEdge]
    omega

/-- The ORIGINAL edge-bounded, arbitrary-real manuscript strip has actual
quadratic affine lattice mass `ell*n²/(160*a*d)` at ALL sufficiently large
original natural endpoints.  Neither endpoint is relaxed. -/
theorem actualMajorArcArchimedean_true_edge_lattice_quadratic_lower
    (a d : ℕ) (τ ell : ℝ)
    (ha : 0 < a) (hd : 0 < d)
    (hτ : 0 < τ) (hell : 0 < ell)
    (hstrip : τ + ell < (1 : ℝ) / 10) :
    ∀ᶠ n : ℕ in atTop,
      ell * (n : ℝ) ^ 2 / (160 * (a : ℝ) * d) ≤
        ((ternaryAffineTriples
          (actualMajorArcArchimedeanLeftWindow a n)
          (actualMajorArcArchimedeanCenterWindow d n)
          (actualMajorArcArchimedeanLabelWindow τ ell n)
          a (2 * d)).card : ℝ) := by
  filter_upwards
    [ternaryAffineTriples_real_manuscript_all_scales_quadratic_lower
      a d τ ell ha hd hτ hell hstrip] with n hblock
  apply hblock.trans
  exact_mod_cast Finset.card_le_card
    (actualMajorArcArchimedean_block_triples_subset_true_edges
      a d n τ ell ha hd hτ hell hstrip)

/-- The exact actual smooth cubic with BOTH genuine edge endpoints and the
original arbitrary-real label strip. -/
noncomputable def actualMajorArcArchimedeanSmoothCubic
    (a d n : ℕ) (τ ell β : ℝ) : ℂ :=
  ternaryExponentialSum
      (actualMajorArcArchimedeanLabelWindow τ ell n)
      (fun _ => 1) 1 β *
    ternaryExponentialSum
      (actualMajorArcArchimedeanLeftWindow a n)
      (fun _ => 1) (a : ℤ) β *
    ternaryExponentialSum
      (actualMajorArcArchimedeanCenterWindow d n)
      (fun _ => 1) (-2 * (d : ℤ)) β

/-- Whole-circle Fourier orthogonality identifies the actual edge-bounded
smooth singular integral with its genuine finite affine lattice count. -/
theorem actualMajorArcArchimedean_smooth_integral_eq_lattice
    (a d n : ℕ) (τ ell : ℝ) :
    (∫ β in (0 : ℝ)..1,
      actualMajorArcArchimedeanSmoothCubic a d n τ ell β) =
        ((ternaryAffineTriples
          (actualMajorArcArchimedeanLeftWindow a n)
          (actualMajorArcArchimedeanCenterWindow d n)
          (actualMajorArcArchimedeanLabelWindow τ ell n)
          a (2 * d)).card : ℂ) := by
  exact ternary_archimedean_interval_singular_integral
    (manuscriptRealLabelLower τ n)
    (manuscriptRealLabelUpper τ ell n)
    1 (n / (2 * a) + 1)
    1 (n / (4 * d) + 1)
    a d

/-- Exact whole-circle positivity for the ORIGINAL smooth manuscript
windows, with the actual arbitrary-real strip and both real edge cutoffs. -/
theorem actualMajorArcArchimedean_smooth_integral_quadratic_lower
    (a d : ℕ) (τ ell : ℝ)
    (ha : 0 < a) (hd : 0 < d)
    (hτ : 0 < τ) (hell : 0 < ell)
    (hstrip : τ + ell < (1 : ℝ) / 10) :
    ∀ᶠ n : ℕ in atTop,
      ell * (n : ℝ) ^ 2 / (160 * (a : ℝ) * d) ≤
        (∫ β in (0 : ℝ)..1,
          actualMajorArcArchimedeanSmoothCubic a d n τ ell β).re := by
  filter_upwards
    [actualMajorArcArchimedean_true_edge_lattice_quadratic_lower
      a d τ ell ha hd hτ hell hstrip] with n hn
  rw [actualMajorArcArchimedean_smooth_integral_eq_lattice]
  exact hn

/-- The ACTUAL signed rational-center phase of an arbitrary common-modulus
triple.  Incompatible triples are deliberately retained rather than
silently replaced by the positive compatible phase. -/
noncomputable def actualMajorArcArchimedeanCellPhase
    (modulus labelResidue leftResidue rightResidue a d : ℕ)
    (effective : ℤ) : ℂ :=
  GoldbachChain.e
      ((labelResidue : ℝ) * effective / modulus) *
    GoldbachChain.e
      (((a : ℝ) * leftResidue) * effective / modulus) *
    GoldbachChain.e
      ((((-2 * (d : ℤ) : ℤ) : ℝ) * rightResidue) *
        effective / modulus)

/-- EXACT pointwise factorization of the genuine `lcm(q,W)` smooth cell,
for EVERY compatible OR incompatible residue triple: its signed center
phase times `φ(lcm(q,W))⁻³` times the ACTUAL edge-bounded smooth cubic. -/
theorem actualMajorArcArchimedean_smooth_cell_eq_phase_cubic
    (S : Finset ℕ)
    (n a d denominator labelResidue leftResidue rightResidue : ℕ)
    (τ ell : ℝ) (effective : ℤ) (β : ℝ) :
    actualMajorArcLcmSmoothCellCubic
        S n a d denominator labelResidue leftResidue rightResidue
        τ ell effective β =
      actualMajorArcArchimedeanCellPhase
          (actualMajorArcLcmResidueModulus S denominator)
          labelResidue leftResidue rightResidue a d effective *
        (1 / ((actualMajorArcLcmResidueModulus S denominator).totient : ℂ)) ^ 3 *
          actualMajorArcArchimedeanSmoothCubic a d n τ ell β := by
  unfold actualMajorArcLcmSmoothCellCubic
    ternaryMajorArcIntervalModel
    actualMajorArcArchimedeanCellPhase
    actualMajorArcArchimedeanSmoothCubic
    actualMajorArcArchimedeanLabelWindow
    actualMajorArcArchimedeanLeftWindow
    actualMajorArcArchimedeanCenterWindow
  simp only [Int.cast_one, one_mul, Int.cast_natCast]
  ring

/-- The exact WHOLE-circle integral of every actual common-modulus smooth
cell, including INCOMPATIBLE signed triples, is its genuine center phase
times the actual edge-bounded affine lattice count and `φ(lcm(q,W))⁻³`.
No phase or residue class is discarded. -/
theorem actualMajorArcArchimedean_smooth_cell_integral_eq_signed_lattice
    (S : Finset ℕ)
    (n a d denominator labelResidue leftResidue rightResidue : ℕ)
    (τ ell : ℝ) (effective : ℤ) :
    (∫ β in (0 : ℝ)..1,
      actualMajorArcLcmSmoothCellCubic
        S n a d denominator labelResidue leftResidue rightResidue
        τ ell effective β) =
      actualMajorArcArchimedeanCellPhase
          (actualMajorArcLcmResidueModulus S denominator)
          labelResidue leftResidue rightResidue a d effective *
        (1 / ((actualMajorArcLcmResidueModulus S denominator).totient : ℂ)) ^ 3 *
          ((ternaryAffineTriples
            (actualMajorArcArchimedeanLeftWindow a n)
            (actualMajorArcArchimedeanCenterWindow d n)
            (actualMajorArcArchimedeanLabelWindow τ ell n)
            a (2 * d)).card : ℂ) := by
  calc
    (∫ β in (0 : ℝ)..1,
      actualMajorArcLcmSmoothCellCubic
        S n a d denominator labelResidue leftResidue rightResidue
        τ ell effective β) =
      ∫ β in (0 : ℝ)..1,
        actualMajorArcArchimedeanCellPhase
            (actualMajorArcLcmResidueModulus S denominator)
            labelResidue leftResidue rightResidue a d effective *
          (1 / ((actualMajorArcLcmResidueModulus S denominator).totient : ℂ)) ^ 3 *
            actualMajorArcArchimedeanSmoothCubic a d n τ ell β := by
      apply intervalIntegral.integral_congr
      intro β hβ
      exact actualMajorArcArchimedean_smooth_cell_eq_phase_cubic
        S n a d denominator labelResidue leftResidue rightResidue
        τ ell effective β
    _ = actualMajorArcArchimedeanCellPhase
            (actualMajorArcLcmResidueModulus S denominator)
            labelResidue leftResidue rightResidue a d effective *
          (1 / ((actualMajorArcLcmResidueModulus S denominator).totient : ℂ)) ^ 3 *
            (∫ β in (0 : ℝ)..1,
              actualMajorArcArchimedeanSmoothCubic a d n τ ell β) := by
      rw [intervalIntegral.integral_const_mul]
    _ = _ := by
      rw [actualMajorArcArchimedean_smooth_integral_eq_lattice]

/-- A genuine compatible common-modulus residue triple has center phase
exactly one, for the TRUE effective shifted numerator and every conductor. -/
theorem actualMajorArcArchimedean_compatible_cell_phase_eq_one
    (modulus labelResidue leftResidue rightResidue a d : ℕ)
    (hmodulus : 0 < modulus)
    (hadmissible :
      (a * leftResidue + labelResidue) % modulus =
        (2 * d * rightResidue) % modulus)
    (effective : ℤ) :
    actualMajorArcArchimedeanCellPhase modulus
      labelResidue leftResidue rightResidue a d effective = 1 := by
  exact ternary_manuscript_major_arc_phase_cancel
    modulus labelResidue leftResidue rightResidue a d
    hmodulus hadmissible effective

/-- The actual admissible common-modulus smooth cell has the full
coefficient-sensitive, arbitrary-real, all-endpoint whole-circle lower
bound `φ(lcm(q,W))⁻³*ell*n²/(160*a*d)`.  This conclusion is explicitly
WHOLE-circle only and is never substituted for a truncated major arc. -/
theorem actualMajorArcArchimedean_compatible_cell_integral_quadratic_lower
    (S : Finset ℕ)
    (a d denominator labelResidue leftResidue rightResidue : ℕ)
    (τ ell : ℝ) (effective : ℤ)
    (ha : 0 < a) (hd : 0 < d)
    (hτ : 0 < τ) (hell : 0 < ell)
    (hstrip : τ + ell < (1 : ℝ) / 10)
    (hmodulus : 0 < actualMajorArcLcmResidueModulus S denominator)
    (hadmissible :
      (a * leftResidue + labelResidue) %
          actualMajorArcLcmResidueModulus S denominator =
        (2 * d * rightResidue) %
          actualMajorArcLcmResidueModulus S denominator) :
    ∀ᶠ n : ℕ in atTop,
      (1 / ((actualMajorArcLcmResidueModulus S denominator).totient : ℝ)) ^ 3 *
          (ell * (n : ℝ) ^ 2 / (160 * (a : ℝ) * d)) ≤
        (∫ β in (0 : ℝ)..1,
          actualMajorArcLcmSmoothCellCubic
            S n a d denominator labelResidue leftResidue rightResidue
            τ ell effective β).re := by
  filter_upwards
    [actualMajorArcArchimedean_true_edge_lattice_quadratic_lower
      a d τ ell ha hd hτ hell hstrip] with n hn
  rw [actualMajorArcArchimedean_smooth_cell_integral_eq_signed_lattice,
    actualMajorArcArchimedean_compatible_cell_phase_eq_one
      (actualMajorArcLcmResidueModulus S denominator)
      labelResidue leftResidue rightResidue a d hmodulus hadmissible
      effective, one_mul]
  have hcast :
      (1 / ((actualMajorArcLcmResidueModulus S denominator).totient : ℂ)) ^ 3 *
          ((ternaryAffineTriples
            (actualMajorArcArchimedeanLeftWindow a n)
            (actualMajorArcArchimedeanCenterWindow d n)
            (actualMajorArcArchimedeanLabelWindow τ ell n)
            a (2 * d)).card : ℂ) =
        (((1 / ((actualMajorArcLcmResidueModulus S denominator).totient : ℝ)) ^ 3 *
          ((ternaryAffineTriples
            (actualMajorArcArchimedeanLeftWindow a n)
            (actualMajorArcArchimedeanCenterWindow d n)
            (actualMajorArcArchimedeanLabelWindow τ ell n)
            a (2 * d)).card : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_left hn (by positivity)

/-- On the ACTUAL coefficient-sensitive edge windows, the affine phase
height is bounded by `2*n`, independently of both coefficients. -/
theorem actualMajorArcArchimedean_true_edge_phase_le_two_n
    (a d n q r z : ℕ) (τ ell : ℝ)
    (ha : 0 < a) (hd : 0 < d)
    (hτ : 0 < τ) (hell : 0 < ell)
    (hstrip : τ + ell < (1 : ℝ) / 10)
    (hq : q ∈ actualMajorArcArchimedeanLeftWindow a n)
    (hr : r ∈ actualMajorArcArchimedeanCenterWindow d n)
    (hz : z ∈ actualMajorArcArchimedeanLabelWindow τ ell n) :
    |(a : ℝ) * q - (2 * d : ℕ) * r + z| ≤ 2 * (n : ℝ) := by
  have hqdiv : q ≤ n / (2 * a) := by
    unfold actualMajorArcArchimedeanLeftWindow at hq
    have h := (Finset.mem_Ico.mp hq).2
    omega
  have hrdiv : r ≤ n / (4 * d) := by
    unfold actualMajorArcArchimedeanCenterWindow at hr
    have h := (Finset.mem_Ico.mp hr).2
    omega
  have hqedge : 2 * a * q ≤ n := by
    have h := (Nat.le_div_iff_mul_le (by omega)).mp hqdiv
    nlinarith
  have hredge : 4 * d * r ≤ n := by
    have h := (Nat.le_div_iff_mul_le (by omega)).mp hrdiv
    nlinarith
  have hzstrip :=
    (mem_manuscriptRealLabelWindow_iff
      τ ell n z hτ.le hell.le).mp hz
  have hzle : (z : ℝ) ≤ n := by
    have hscaled := mul_le_mul_of_nonneg_right hstrip.le
      (show (0 : ℝ) ≤ n by positivity)
    nlinarith [hzstrip.2]
  have hqreal : (2 : ℝ) * a * q ≤ n := by
    exact_mod_cast hqedge
  have hrreal : (4 : ℝ) * d * r ≤ n := by
    exact_mod_cast hredge
  have haq : 0 ≤ (a : ℝ) * q := by positivity
  have hdr : 0 ≤ (d : ℝ) * r := by positivity
  have hznonnegative : (0 : ℝ) ≤ z := by positivity
  norm_num only [Nat.cast_ofNat, Nat.cast_mul]
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The exact ACTUAL edge-bounded smooth cubic has a positive genuine
TRUNCATED principal-arc lower bound; its radius is `1/(8*pi*n)` and its
phase constant is coefficient-independent.  No full-arc complement is
discarded. -/
theorem actualMajorArcArchimedean_principal_integral_card_lower
    (a d n : ℕ) (τ ell : ℝ)
    (ha : 0 < a) (hd : 0 < d) (hn : 0 < n)
    (hτ : 0 < τ) (hell : 0 < ell)
    (hstrip : τ + ell < (1 : ℝ) / 10) :
    (((actualMajorArcArchimedeanLeftWindow a n).card : ℝ) *
        ((actualMajorArcArchimedeanCenterWindow d n).card : ℝ) *
        ((actualMajorArcArchimedeanLabelWindow τ ell n).card : ℝ)) /
          (16 * Real.pi * n) ≤
      (∫ β in Set.Ioc (0 : ℝ) (1 / (8 * Real.pi * n)),
        actualMajorArcArchimedeanSmoothCubic a d n τ ell β).re := by
  have hK : (0 : ℝ) < 2 * n := by positivity
  have hprincipal := ternary_unweighted_cubic_principal_arc_integral_lower
    (actualMajorArcArchimedeanLeftWindow a n)
    (actualMajorArcArchimedeanCenterWindow d n)
    (actualMajorArcArchimedeanLabelWindow τ ell n)
    a (2 * d) (2 * (n : ℝ)) hK
    (fun q hq r hr z hz =>
      actualMajorArcArchimedean_true_edge_phase_le_two_n
        a d n q r z τ ell ha hd hτ hell hstrip hq hr hz)
  have hfrequency : (-(2 * d : ℕ) : ℤ) = -2 * (d : ℤ) := by
    push_cast
    ring
  have hinterval :
      (1 / (4 * Real.pi * (2 * (n : ℝ)))) =
        1 / (8 * Real.pi * n) := by ring
  rw [hfrequency, hinterval] at hprincipal
  convert hprincipal using 1
  · ring
  · congr 1
    apply setIntegral_congr_fun measurableSet_Ioc
    intro β hβ
    unfold actualMajorArcArchimedeanSmoothCubic
    ring

/-- Exact truncated-cell identity: the actual signed rational-center phase
multiplies the genuine edge-bounded smooth singular integral on EVERY
interval.  This retains incompatible/signed residue triples verbatim. -/
theorem actualMajorArcArchimedean_truncated_cell_integral_eq_signed_cubic
    (S : Finset ℕ)
    (n a d denominator labelResidue leftResidue rightResidue : ℕ)
    (τ ell : ℝ) (effective : ℤ) (lower upper : ℝ) :
    (∫ β in lower..upper,
      actualMajorArcLcmSmoothCellCubic
        S n a d denominator labelResidue leftResidue rightResidue
        τ ell effective β) =
      actualMajorArcArchimedeanCellPhase
          (actualMajorArcLcmResidueModulus S denominator)
          labelResidue leftResidue rightResidue a d effective *
        (1 / ((actualMajorArcLcmResidueModulus S denominator).totient : ℂ)) ^ 3 *
          (∫ β in lower..upper,
            actualMajorArcArchimedeanSmoothCubic a d n τ ell β) := by
  calc
    (∫ β in lower..upper,
      actualMajorArcLcmSmoothCellCubic
        S n a d denominator labelResidue leftResidue rightResidue
        τ ell effective β) =
      ∫ β in lower..upper,
        actualMajorArcArchimedeanCellPhase
            (actualMajorArcLcmResidueModulus S denominator)
            labelResidue leftResidue rightResidue a d effective *
          (1 / ((actualMajorArcLcmResidueModulus S denominator).totient : ℂ)) ^ 3 *
            actualMajorArcArchimedeanSmoothCubic a d n τ ell β := by
      apply intervalIntegral.integral_congr
      intro β hβ
      exact actualMajorArcArchimedean_smooth_cell_eq_phase_cubic
        S n a d denominator labelResidue leftResidue rightResidue
        τ ell effective β
    _ = _ := by rw [intervalIntegral.integral_const_mul]

/-- A true truncated rational-center cell is its signed WHOLE-circle lattice
main term MINUS its explicit signed archimedean tail.  The tail is NOT
assumed nonnegative or negligible; bounding/cancelling it is the exact
remaining analytic obstacle. -/
theorem actualMajorArcArchimedean_truncated_cell_eq_signed_lattice_sub_tail
    (S : Finset ℕ)
    (n a d denominator labelResidue leftResidue rightResidue : ℕ)
    (τ ell : ℝ) (effective : ℤ) (cutoff : ℝ) :
    (∫ β in (0 : ℝ)..cutoff,
      actualMajorArcLcmSmoothCellCubic
        S n a d denominator labelResidue leftResidue rightResidue
        τ ell effective β) =
      actualMajorArcArchimedeanCellPhase
          (actualMajorArcLcmResidueModulus S denominator)
          labelResidue leftResidue rightResidue a d effective *
        (1 / ((actualMajorArcLcmResidueModulus S denominator).totient : ℂ)) ^ 3 *
          ((ternaryAffineTriples
            (actualMajorArcArchimedeanLeftWindow a n)
            (actualMajorArcArchimedeanCenterWindow d n)
            (actualMajorArcArchimedeanLabelWindow τ ell n)
            a (2 * d)).card : ℂ) -
        ∫ β in cutoff..1,
          actualMajorArcLcmSmoothCellCubic
            S n a d denominator labelResidue leftResidue rightResidue
            τ ell effective β := by
  let f : ℝ → ℂ := fun β =>
    actualMajorArcLcmSmoothCellCubic
      S n a d denominator labelResidue leftResidue rightResidue
      τ ell effective β
  have hcontinuous : Continuous f := by
    dsimp [f, actualMajorArcLcmSmoothCellCubic,
      ternaryMajorArcIntervalModel]
    unfold ternaryExponentialSum GoldbachChain.e
    fun_prop
  have hfirst : IntervalIntegrable f volume 0 cutoff :=
    hcontinuous.intervalIntegrable 0 cutoff
  have hsecond : IntervalIntegrable f volume cutoff 1 :=
    hcontinuous.intervalIntegrable cutoff 1
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    hfirst hsecond
  change (∫ β in (0 : ℝ)..cutoff, f β) +
    (∫ β in cutoff..1, f β) =
      (∫ β in (0 : ℝ)..1, f β) at hsplit
  have hfull := actualMajorArcArchimedean_smooth_cell_integral_eq_signed_lattice
    S n a d denominator labelResidue leftResidue rightResidue
    τ ell effective
  change (∫ β in (0 : ℝ)..1, f β) = _ at hfull
  change (∫ β in (0 : ℝ)..cutoff, f β) =
    _ - (∫ β in cutoff..1, f β)
  rw [← hfull]
  exact eq_sub_of_add_eq hsplit

/-- The TRUE translated Farey anchor, with its ORIGINAL denominator `q`
and radius `1/(q*(Q+1))`, has exact real volume `2/(q*(Q+1))`. -/
theorem actualMajorArcArchimedean_shifted_anchor_volume
    (supportModulus cutoff denominator : ℕ)
    (numerator shift : ℤ) :
    (volume (shiftedFareyAnchorArc supportModulus cutoff denominator
      numerator shift)).toReal =
        2 / ((denominator : ℝ) * (cutoff + 1)) := by
  unfold shiftedFareyAnchorArc
  rw [Real.volume_closedBall, ENNReal.toReal_ofReal (by positivity)]
  ring

/-- Intersecting an actual shifted Farey anchor with the original circle
never increases its TRUE denominator-dependent arc measure. -/
theorem actualMajorArcArchimedean_shifted_anchor_circle_volume_le
    (supportModulus cutoff denominator : ℕ)
    (numerator shift : ℤ) :
    (volume (shiftedFareyAnchorArc supportModulus cutoff denominator
      numerator shift ∩ Set.Ioc (0 : ℝ) 1)).toReal ≤
        2 / ((denominator : ℝ) * (cutoff + 1)) := by
  have hmeasure :
      volume (shiftedFareyAnchorArc supportModulus cutoff denominator
        numerator shift ∩ Set.Ioc (0 : ℝ) 1) ≤
        volume (shiftedFareyAnchorArc supportModulus cutoff denominator
          numerator shift) :=
    measure_mono Set.inter_subset_left
  calc
    (volume (shiftedFareyAnchorArc supportModulus cutoff denominator
      numerator shift ∩ Set.Ioc (0 : ℝ) 1)).toReal ≤
        (volume (shiftedFareyAnchorArc supportModulus cutoff denominator
          numerator shift)).toReal := by
      apply ENNReal.toReal_mono _ hmeasure
      unfold shiftedFareyAnchorArc
      rw [Real.volume_closedBall]
      exact ENNReal.ofReal_ne_top
    _ = _ := actualMajorArcArchimedean_shifted_anchor_volume
      supportModulus cutoff denominator numerator shift

/-- At the ACTUAL fully compatible Farey cutoff, every translated anchor
recovers the indispensable factor `1/n` in its arc measure, uniformly for
every positive denominator and every integer numerator/shift. -/
theorem actualMajorArcArchimedean_shifted_anchor_scaled_volume_eventually
    (lower : ℕ → ℕ) (κ : ℝ) (hκ : 0 < κ)
    (hlower : ∀ᶠ n : ℕ in atTop,
      κ * (n : ℝ) ≤ (lower n : ℝ))
    (supportModulus : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ denominator : ℕ, 0 < denominator →
        ∀ numerator shift : ℤ,
          (volume (shiftedFareyAnchorArc supportModulus
            (fullyCompatibleFareyCutoff lower n) denominator
            numerator shift ∩ Set.Ioc (0 : ℝ) 1)).toReal * n ≤
              2 * (compatibleLogMinorCutoff n : ℝ) /
                (κ * denominator) := by
  filter_upwards
    [fullyCompatibleFareyCutoff_abel_scale_eventually
      lower κ hκ hlower] with n hscale
  intro denominator hdenominator numerator shift
  have hdenominatorReal : (0 : ℝ) < denominator := by
    exact_mod_cast hdenominator
  have hcutoffReal :
      (0 : ℝ) < (fullyCompatibleFareyCutoff lower n : ℝ) + 1 := by
    positivity
  have hscaleReal :
      (n : ℝ) / ((fullyCompatibleFareyCutoff lower n : ℝ) + 1) ≤
        (compatibleLogMinorCutoff n : ℝ) / κ := by
    exact_mod_cast hscale
  have hvolume :=
    actualMajorArcArchimedean_shifted_anchor_circle_volume_le
      supportModulus (fullyCompatibleFareyCutoff lower n)
      denominator numerator shift
  calc
    (volume (shiftedFareyAnchorArc supportModulus
        (fullyCompatibleFareyCutoff lower n) denominator
        numerator shift ∩ Set.Ioc (0 : ℝ) 1)).toReal * n ≤
      (2 / ((denominator : ℝ) *
        (fullyCompatibleFareyCutoff lower n + 1))) * n := by
        exact mul_le_mul_of_nonneg_right hvolume (by positivity)
    _ = (2 / (denominator : ℝ)) *
          ((n : ℝ) / (fullyCompatibleFareyCutoff lower n + 1)) := by
      field_simp [ne_of_gt hdenominatorReal, ne_of_gt hcutoffReal]
    _ ≤ (2 / (denominator : ℝ)) *
          ((compatibleLogMinorCutoff n : ℝ) / κ) := by
      exact mul_le_mul_of_nonneg_left hscaleReal (by positivity)
    _ = 2 * (compatibleLogMinorCutoff n : ℝ) /
          (κ * denominator) := by ring

/-- The true prime-only three-factor POINTWISE error has exactly one extra
factor `n` relative to the already proved integrated prime-power bound. -/
theorem actualMajorArcArchimedean_pointwise_prime_power_eq_n_mul
    (n : ℕ) :
    actualMajorArcFullCubicPrimePowerError n =
      (n : ℝ) * ternaryPrimePowerErrorBound n := by
  unfold actualMajorArcFullCubicPrimePowerError
    ternaryPrimePowerErrorBound
  ring

/-- Multiplying the exact pointwise cubic prime-power error by the TRUE
Farey-arc measure recovers its missing `1/n`.  The resulting normalized
bound is the proved proper-prime-power error times `2*P/(κ*q)`; no
unjustified pointwise `o(n²)` assertion is used. -/
theorem actualMajorArcArchimedean_shifted_anchor_prime_power_normalized_eventually
    (lower : ℕ → ℕ) (κ : ℝ) (hκ : 0 < κ)
    (hlower : ∀ᶠ n : ℕ in atTop,
      κ * (n : ℝ) ≤ (lower n : ℝ))
    (supportModulus : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ denominator : ℕ, 0 < denominator →
        ∀ numerator shift : ℤ,
          (volume (shiftedFareyAnchorArc supportModulus
              (fullyCompatibleFareyCutoff lower n) denominator
              numerator shift ∩ Set.Ioc (0 : ℝ) 1)).toReal *
            actualMajorArcFullCubicPrimePowerError n /
              (n : ℝ) ^ 2 ≤
            (2 * (compatibleLogMinorCutoff n : ℝ) /
              (κ * denominator)) *
                (ternaryPrimePowerErrorBound n / (n : ℝ) ^ 2) := by
  filter_upwards
    [actualMajorArcArchimedean_shifted_anchor_scaled_volume_eventually
      lower κ hκ hlower supportModulus] with n hvolume
  intro denominator hdenominator numerator shift
  have hscale := hvolume denominator hdenominator numerator shift
  have herror : 0 ≤ ternaryPrimePowerErrorBound n / (n : ℝ) ^ 2 := by
    unfold ternaryPrimePowerErrorBound
    positivity
  rw [actualMajorArcArchimedean_pointwise_prime_power_eq_n_mul]
  calc
    (volume (shiftedFareyAnchorArc supportModulus
        (fullyCompatibleFareyCutoff lower n) denominator
        numerator shift ∩ Set.Ioc (0 : ℝ) 1)).toReal *
        ((n : ℝ) * ternaryPrimePowerErrorBound n) / (n : ℝ) ^ 2 =
      ((volume (shiftedFareyAnchorArc supportModulus
        (fullyCompatibleFareyCutoff lower n) denominator
        numerator shift ∩ Set.Ioc (0 : ℝ) 1)).toReal * n) *
        (ternaryPrimePowerErrorBound n / (n : ℝ) ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hscale herror

#print axioms Erdos689.actualMajorArcArchimedean_block_triples_subset_true_edges
#print axioms Erdos689.actualMajorArcArchimedean_true_edge_lattice_quadratic_lower
#print axioms Erdos689.actualMajorArcArchimedean_smooth_integral_eq_lattice
#print axioms Erdos689.actualMajorArcArchimedean_smooth_integral_quadratic_lower
#print axioms Erdos689.actualMajorArcArchimedean_smooth_cell_eq_phase_cubic
#print axioms Erdos689.actualMajorArcArchimedean_smooth_cell_integral_eq_signed_lattice
#print axioms Erdos689.actualMajorArcArchimedean_compatible_cell_phase_eq_one
#print axioms Erdos689.actualMajorArcArchimedean_compatible_cell_integral_quadratic_lower
#print axioms Erdos689.actualMajorArcArchimedean_true_edge_phase_le_two_n
#print axioms Erdos689.actualMajorArcArchimedean_principal_integral_card_lower
#print axioms Erdos689.actualMajorArcArchimedean_truncated_cell_integral_eq_signed_cubic
#print axioms Erdos689.actualMajorArcArchimedean_truncated_cell_eq_signed_lattice_sub_tail
#print axioms Erdos689.actualMajorArcArchimedean_shifted_anchor_volume
#print axioms Erdos689.actualMajorArcArchimedean_shifted_anchor_circle_volume_le
#print axioms Erdos689.actualMajorArcArchimedean_shifted_anchor_scaled_volume_eventually
#print axioms Erdos689.actualMajorArcArchimedean_pointwise_prime_power_eq_n_mul
#print axioms Erdos689.actualMajorArcArchimedean_shifted_anchor_prime_power_normalized_eventually

end Erdos689
