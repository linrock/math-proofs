module

public import TernaryFourier433
public import ThreePrimeMajorArcReduction433

@[expose] public section


/-!
# Genuine three-prime extraction for the #689 major-arc route

The existing cubic Fourier development uses von Mangoldt windows, which also
contain proper prime powers.  The original covering problem, however, requires
all three affine coordinates to be actual primes.  This file removes that
analytic mismatch for arbitrary finite manuscript-shaped affine windows.

The positive localized major-arc asymptotic itself remains a separate goal.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos689

/-- Proper prime powers with nonzero von Mangoldt weight in the actual closed
positive interval `1 ≤ m ≤ n`. -/
noncomputable def ternaryProperPrimePowers (n : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 n).filter fun m =>
    ¬ m.Prime ∧ ArithmeticFunction.vonMangoldt m ≠ 0

/-- The upstream Goldbach circle-method proof already supplies the sharp
elementary proper-prime-power count in exactly the required interval. -/
theorem ternaryProperPrimePowers_card_le (n : ℕ) :
    ((ternaryProperPrimePowers n).card : ℝ) ≤
      (Nat.sqrt n : ℝ) * (Nat.log 2 n + 1) := by
  exact GoldbachChain.MinorArc.card_properPrimePow_le n

/-- The genuine three-coordinate von Mangoldt weight. -/
noncomputable def ternaryAffineVonMangoldtWeight
    (v : ℕ × (ℕ × ℕ)) : ℝ :=
  ArithmeticFunction.vonMangoldt v.1 *
    ArithmeticFunction.vonMangoldt v.2.1 *
      ArithmeticFunction.vonMangoldt v.2.2

/-- Affine triples with nonzero three-prime weight but at least one coordinate
which is a proper prime power rather than a genuine prime. -/
noncomputable def ternaryAffinePrimePowerExceptions
    (left center labels : Finset ℕ) (a c : ℕ) :
    Finset (ℕ × (ℕ × ℕ)) :=
  (ternaryAffineTriples left center labels a c).filter fun v =>
    ternaryAffineVonMangoldtWeight v ≠ 0 ∧
      (¬ v.1.Prime ∨ ¬ v.2.1.Prime ∨ ¬ v.2.2.Prime)

/-- An actual affine triple is uniquely determined by either its left/center,
center/left, or label/left coordinate pair; the last projection requires a
genuinely positive center coefficient. -/
theorem ternaryAffinePrimePowerExceptions_card_le
    (left center labels : Finset ℕ) (a c n : ℕ)
    (hc : 0 < c)
    (hleft : left ⊆ Finset.Ioc 0 n)
    (hcenter : center ⊆ Finset.Ioc 0 n)
    (hlabels : labels ⊆ Finset.Ioc 0 n) :
    (ternaryAffinePrimePowerExceptions left center labels a c).card ≤
      3 * (ternaryProperPrimePowers n).card * n := by
  classical
  let F := ternaryAffinePrimePowerExceptions left center labels a c
  let P := ternaryProperPrimePowers n
  let I := Finset.Ioc 0 n
  let A := F.filter fun v => ¬v.1.Prime
  let B := F.filter fun v => ¬v.2.1.Prime
  let C := F.filter fun v => ¬v.2.2.Prime
  have hdata (v : ℕ × (ℕ × ℕ)) (hv : v ∈ F) :
      v.1 ∈ I ∧ v.2.1 ∈ I ∧ v.2.2 ∈ I ∧
        a * v.1 + v.2.2 = c * v.2.1 ∧
        ArithmeticFunction.vonMangoldt v.1 ≠ 0 ∧
        ArithmeticFunction.vonMangoldt v.2.1 ≠ 0 ∧
        ArithmeticFunction.vonMangoldt v.2.2 ≠ 0 ∧
        (¬v.1.Prime ∨ ¬v.2.1.Prime ∨ ¬v.2.2.Prime) := by
    obtain ⟨htriple, hweight, hbad⟩ :=
      Finset.mem_filter.mp hv
    obtain ⟨hproduct, hequation⟩ := Finset.mem_filter.mp htriple
    obtain ⟨hvleft, hrest⟩ := Finset.mem_product.mp hproduct
    obtain ⟨hvcenter, hvlabel⟩ := Finset.mem_product.mp hrest
    have hfirst : ArithmeticFunction.vonMangoldt v.1 ≠ 0 := by
      intro hzero
      apply hweight
      simp [ternaryAffineVonMangoldtWeight, hzero]
    have hsecond : ArithmeticFunction.vonMangoldt v.2.1 ≠ 0 := by
      intro hzero
      apply hweight
      simp [ternaryAffineVonMangoldtWeight, hzero]
    have hthird : ArithmeticFunction.vonMangoldt v.2.2 ≠ 0 := by
      intro hzero
      apply hweight
      simp [ternaryAffineVonMangoldtWeight, hzero]
    exact ⟨hleft hvleft, hcenter hvcenter, hlabels hvlabel,
      hequation, hfirst, hsecond, hthird, hbad⟩
  have hA : A.card ≤ (P.product I).card := by
    apply Finset.card_le_card_of_injOn (fun v => (v.1, v.2.1))
    · intro v hv
      obtain ⟨hvF, hvbad⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hv)
      obtain ⟨hx, hy, _, _, hxweight, _, _, _⟩ := hdata v hvF
      apply Finset.mem_coe.mpr
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_filter.mpr ⟨hx, hvbad, hxweight⟩, hy⟩
    · intro v hv w hw heq
      have hx : v.1 = w.1 := congrArg (fun z : ℕ × ℕ => z.1) heq
      have hy : v.2.1 = w.2.1 := congrArg (fun z : ℕ × ℕ => z.2) heq
      have hvF := (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).1
      have hwF := (Finset.mem_filter.mp (Finset.mem_coe.mp hw)).1
      have hveq := (hdata v hvF).2.2.2.1
      have hweq := (hdata w hwF).2.2.2.1
      rw [hx, hy] at hveq
      have hz : v.2.2 = w.2.2 := by omega
      exact Prod.ext hx (Prod.ext hy hz)
  have hB : B.card ≤ (P.product I).card := by
    apply Finset.card_le_card_of_injOn (fun v => (v.2.1, v.1))
    · intro v hv
      obtain ⟨hvF, hvbad⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hv)
      obtain ⟨hx, hy, _, _, _, hyweight, _, _⟩ := hdata v hvF
      apply Finset.mem_coe.mpr
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_filter.mpr ⟨hy, hvbad, hyweight⟩, hx⟩
    · intro v hv w hw heq
      have hpair : (v.2.1, v.1) = (w.2.1, w.1) := heq
      have hy : v.2.1 = w.2.1 := by
        simpa using congrArg (fun z : ℕ × ℕ => z.1) hpair
      have hx : v.1 = w.1 := by
        simpa using congrArg (fun z : ℕ × ℕ => z.2) hpair
      have hvF := (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).1
      have hwF := (Finset.mem_filter.mp (Finset.mem_coe.mp hw)).1
      have hveq := (hdata v hvF).2.2.2.1
      have hweq := (hdata w hwF).2.2.2.1
      rw [hx, hy] at hveq
      have hz : v.2.2 = w.2.2 := by omega
      exact Prod.ext hx (Prod.ext hy hz)
  have hC : C.card ≤ (P.product I).card := by
    apply Finset.card_le_card_of_injOn (fun v => (v.2.2, v.1))
    · intro v hv
      obtain ⟨hvF, hvbad⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hv)
      obtain ⟨hx, _, hz, _, _, _, hzweight, _⟩ := hdata v hvF
      apply Finset.mem_coe.mpr
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_filter.mpr ⟨hz, hvbad, hzweight⟩, hx⟩
    · intro v hv w hw heq
      have hz : v.2.2 = w.2.2 := congrArg (fun z : ℕ × ℕ => z.1) heq
      have hx : v.1 = w.1 := congrArg (fun z : ℕ × ℕ => z.2) heq
      have hvF := (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).1
      have hwF := (Finset.mem_filter.mp (Finset.mem_coe.mp hw)).1
      have hveq := (hdata v hvF).2.2.2.1
      have hweq := (hdata w hwF).2.2.2.1
      rw [hx, hz] at hveq
      have hmul : c * v.2.1 = c * w.2.1 := by omega
      have hy : v.2.1 = w.2.1 := Nat.eq_of_mul_eq_mul_left hc hmul
      exact Prod.ext hx (Prod.ext hy hz)
  have hcover : F ⊆ (A ∪ B) ∪ C := by
    intro v hv
    rcases (hdata v hv).2.2.2.2.2.2.2 with hbad | hbad | hbad
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv, hbad⟩))
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv, hbad⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv, hbad⟩)
  have hcovered := Finset.card_le_card hcover
  have hfirstUnion := Finset.card_union_le A B
  have hsecondUnion := Finset.card_union_le (A ∪ B) C
  have hpair : (P.product I).card = P.card * n := by
    simp [I]
  change F.card ≤ 3 * P.card * n
  rw [hpair] at hA hB hC
  rw [mul_assoc]
  omega

/-- Every actual three-coordinate von Mangoldt weight is nonnegative. -/
theorem ternaryAffineVonMangoldtWeight_nonneg
    (v : ℕ × (ℕ × ℕ)) :
    0 ≤ ternaryAffineVonMangoldtWeight v := by
  unfold ternaryAffineVonMangoldtWeight
  exact mul_nonneg
    (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      ArithmeticFunction.vonMangoldt_nonneg)
    ArithmeticFunction.vonMangoldt_nonneg

/-- On the genuine positive interval `1 ≤ m ≤ n`, each of the three
logarithmic prime-power weights is bounded by `log(n)`. -/
theorem ternaryAffineVonMangoldtWeight_le_log_cube
    (v : ℕ × (ℕ × ℕ)) (n : ℕ)
    (hleft : v.1 ∈ Finset.Ioc 0 n)
    (hcenter : v.2.1 ∈ Finset.Ioc 0 n)
    (hlabel : v.2.2 ∈ Finset.Ioc 0 n) :
    ternaryAffineVonMangoldtWeight v ≤ (Real.log (n : ℝ)) ^ 3 := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hbound (m : ℕ) (hm : m ∈ Finset.Ioc 0 n) :
      ArithmeticFunction.vonMangoldt m ≤ Real.log (n : ℝ) := by
    obtain ⟨hpositive, hupper⟩ := Finset.mem_Ioc.mp hm
    exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast hpositive)
        (by exact_mod_cast hupper))
  unfold ternaryAffineVonMangoldtWeight
  calc
    ArithmeticFunction.vonMangoldt v.1 *
          ArithmeticFunction.vonMangoldt v.2.1 *
            ArithmeticFunction.vonMangoldt v.2.2 ≤
        Real.log (n : ℝ) * Real.log (n : ℝ) * Real.log (n : ℝ) := by
      gcongr
      · exact hbound v.1 hleft
      · exact hbound v.2.1 hcenter
      · exact hbound v.2.2 hlabel
    _ = (Real.log (n : ℝ)) ^ 3 := by ring

/-- The complete genuine affine prime-power error has the explicit uniform
bound `3 n sqrt(n) (log₂(n)+1) log(n)^3`, independently of both affine
coefficients and of all residue or interval restrictions on the windows. -/
theorem ternaryAffinePrimePowerExceptions_weight_le
    (left center labels : Finset ℕ) (a c n : ℕ)
    (hc : 0 < c)
    (hleft : left ⊆ Finset.Ioc 0 n)
    (hcenter : center ⊆ Finset.Ioc 0 n)
    (hlabels : labels ⊆ Finset.Ioc 0 n) :
    (∑ v ∈ ternaryAffinePrimePowerExceptions left center labels a c,
      ternaryAffineVonMangoldtWeight v) ≤
        3 * (n : ℝ) * (Nat.sqrt n : ℝ) *
          ((Nat.log 2 n : ℝ) + 1) * (Real.log (n : ℝ)) ^ 3 := by
  let F := ternaryAffinePrimePowerExceptions left center labels a c
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hterm (v : ℕ × (ℕ × ℕ)) (hv : v ∈ F) :
      ternaryAffineVonMangoldtWeight v ≤ (Real.log (n : ℝ)) ^ 3 := by
    have htriple := (Finset.mem_filter.mp hv).1
    have hproduct := (Finset.mem_filter.mp htriple).1
    obtain ⟨hx, hyz⟩ := Finset.mem_product.mp hproduct
    obtain ⟨hy, hz⟩ := Finset.mem_product.mp hyz
    exact ternaryAffineVonMangoldtWeight_le_log_cube
      v n (hleft hx) (hcenter hy) (hlabels hz)
  have hcard := ternaryAffinePrimePowerExceptions_card_le
    left center labels a c n hc hleft hcenter hlabels
  have hproper := ternaryProperPrimePowers_card_le n
  calc
    (∑ v ∈ F, ternaryAffineVonMangoldtWeight v) ≤
        ∑ _v ∈ F, (Real.log (n : ℝ)) ^ 3 := by
      exact Finset.sum_le_sum hterm
    _ = (F.card : ℝ) * (Real.log (n : ℝ)) ^ 3 := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((3 * (ternaryProperPrimePowers n).card * n : ℕ) : ℝ) *
          (Real.log (n : ℝ)) ^ 3 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hcard
    _ = 3 * (n : ℝ) * ((ternaryProperPrimePowers n).card : ℝ) *
          (Real.log (n : ℝ)) ^ 3 := by
      push_cast
      ring
    _ ≤ 3 * (n : ℝ) * (Nat.sqrt n : ℝ) *
          ((Nat.log 2 n : ℝ) + 1) * (Real.log (n : ℝ)) ^ 3 := by
      have hcoeff : 0 ≤ (3 : ℝ) * n * (Real.log (n : ℝ)) ^ 3 := by
        positivity
      have hscaled := mul_le_mul_of_nonneg_left hproper hcoeff
      nlinarith

/-- Exact separation of the unrestricted three-von-Mangoldt affine sum into
its genuine three-prime contribution and the proper-prime-power error.
Zero-weight nonprime coordinates disappear identically, without estimates. -/
theorem ternaryAffineVonMangoldtSum_eq_prime_sum_add_exceptions
    (left center labels : Finset ℕ) (a c : ℕ) :
    (∑ v ∈ ternaryAffineTriples left center labels a c,
      ternaryAffineVonMangoldtWeight v) =
      (∑ v ∈ (ternaryAffineTriples left center labels a c).filter
        (fun v => v.1.Prime ∧ v.2.1.Prime ∧ v.2.2.Prime),
          ternaryAffineVonMangoldtWeight v) +
      ∑ v ∈ ternaryAffinePrimePowerExceptions left center labels a c,
        ternaryAffineVonMangoldtWeight v := by
  classical
  let F := ternaryAffineTriples left center labels a c
  let good := fun v : ℕ × (ℕ × ℕ) =>
    v.1.Prime ∧ v.2.1.Prime ∧ v.2.2.Prime
  have hsplit := Finset.sum_filter_add_sum_filter_not
    F good ternaryAffineVonMangoldtWeight
  have hbad :
      (F.filter fun v => ¬good v).filter
        (fun v => ternaryAffineVonMangoldtWeight v ≠ 0) =
          ternaryAffinePrimePowerExceptions left center labels a c := by
    ext v
    simp only [Finset.mem_filter, ternaryAffinePrimePowerExceptions]
    change
      (v ∈ F ∧ ¬good v) ∧ ternaryAffineVonMangoldtWeight v ≠ 0 ↔
        v ∈ F ∧ ternaryAffineVonMangoldtWeight v ≠ 0 ∧
          (¬v.1.Prime ∨ ¬v.2.1.Prime ∨ ¬v.2.2.Prime)
    dsimp [good]
    constructor
    · rintro ⟨⟨hmember, hnot⟩, hweight⟩
      refine ⟨hmember, hweight, ?_⟩
      by_cases hfirst : v.1.Prime
      · by_cases hsecond : v.2.1.Prime
        · exact Or.inr (Or.inr fun hthird =>
            hnot ⟨hfirst, hsecond, hthird⟩)
        · exact Or.inr (Or.inl hsecond)
      · exact Or.inl hfirst
    · rintro ⟨hmember, hweight, hnot⟩
      refine ⟨⟨hmember, ?_⟩, hweight⟩
      rintro ⟨hfirst, hsecond, hthird⟩
      rcases hnot with hnot | hnot | hnot
      · exact hnot hfirst
      · exact hnot hsecond
      · exact hnot hthird
  change
    (∑ v ∈ F, ternaryAffineVonMangoldtWeight v) =
      (∑ v ∈ F.filter good, ternaryAffineVonMangoldtWeight v) +
        ∑ v ∈ ternaryAffinePrimePowerExceptions left center labels a c,
          ternaryAffineVonMangoldtWeight v
  calc
    (∑ v ∈ F, ternaryAffineVonMangoldtWeight v) =
        (∑ v ∈ F.filter good, ternaryAffineVonMangoldtWeight v) +
          ∑ v ∈ F.filter (fun v => ¬good v),
            ternaryAffineVonMangoldtWeight v := hsplit.symm
    _ = (∑ v ∈ F.filter good, ternaryAffineVonMangoldtWeight v) +
          ∑ v ∈ (F.filter (fun v => ¬good v)).filter
            (fun v => ternaryAffineVonMangoldtWeight v ≠ 0),
              ternaryAffineVonMangoldtWeight v := by
      rw [Finset.sum_filter_ne_zero]
    _ = _ := by rw [hbad]

/-- The coefficient-independent three-coordinate prime-power error bound. -/
noncomputable def ternaryPrimePowerErrorBound (n : ℕ) : ℝ :=
  3 * (n : ℝ) * (Nat.sqrt n : ℝ) *
    ((Nat.log 2 n : ℝ) + 1) * (Real.log (n : ℝ)) ^ 3

/-- The complete three-coordinate proper-prime-power error is genuinely
little-o of the quadratic ternary major-arc scale.  The estimate is uniform
in all affine coefficients, windows, and fixed or moving residue selectors. -/
theorem ternaryPrimePowerErrorBound_normalized_tendsto_zero :
    Tendsto (fun n : ℕ => ternaryPrimePowerErrorBound n / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  have hlogtwo : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogs :
      Tendsto
        (fun n : ℕ =>
          Real.log (n : ℝ) ^ 4 / (n : ℝ) ^ (1 / 2 : ℝ))
        atTop (nhds 0) := by
    have hreal :=
      (isLittleO_log_rpow_rpow_atTop 4
        (by norm_num : 0 < (1 / 2 : ℝ))).tendsto_div_nhds_zero
    have hnat := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [Function.comp_def, Real.rpow_natCast] using hnat
  have hupper :
      Tendsto
        (fun n : ℕ =>
          (6 / Real.log 2) *
            (Real.log (n : ℝ) ^ 4 / (n : ℝ) ^ (1 / 2 : ℝ)))
        atTop (nhds 0) := by
    simpa using hlogs.const_mul (6 / Real.log 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    unfold ternaryPrimePowerErrorBound
    positivity
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnpositive : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (by omega : 0 < n)
    have hnone : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ n)
    have hlog : (0 : ℝ) < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hlogmono : Real.log (2 : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have hnatlog := Real.natLog_le_logb n 2
    simp only [Real.logb, Nat.cast_ofNat] at hnatlog
    have honeLog : (1 : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 :=
      (le_div_iff₀ hlogtwo).mpr (by simpa using hlogmono)
    have hbinary :
        (Nat.log 2 n : ℝ) + 1 ≤
          2 * (Real.log (n : ℝ) / Real.log 2) := by
      linarith
    have hroot : (Nat.sqrt n : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.nat_sqrt_le_real_sqrt
    have hrootpos : 0 < (n : ℝ) ^ (1 / 2 : ℝ) := by positivity
    have hpow :
        (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) = n := by
      rw [← Real.rpow_add hnpositive]
      norm_num
    have hratio :
        (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) =
          1 / (n : ℝ) ^ (1 / 2 : ℝ) := by
      apply (div_eq_div_iff hnpositive.ne' hrootpos.ne').mpr
      simpa using hpow
    unfold ternaryPrimePowerErrorBound
    calc
      (3 * (n : ℝ) * (Nat.sqrt n : ℝ) *
          ((Nat.log 2 n : ℝ) + 1) * (Real.log (n : ℝ)) ^ 3) /
          (n : ℝ) ^ 2 ≤
        (3 * (n : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) *
          (2 * (Real.log (n : ℝ) / Real.log 2)) *
            (Real.log (n : ℝ)) ^ 3) / (n : ℝ) ^ 2 := by
          gcongr
      _ = (6 / Real.log 2) * (Real.log (n : ℝ)) ^ 4 *
          ((n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ)) := by
          field_simp; ring
      _ = (6 / Real.log 2) *
          (Real.log (n : ℝ) ^ 4 / (n : ℝ) ^ (1 / 2 : ℝ)) := by
          rw [hratio]
          ring

/-- For arbitrary moving affine coefficients and genuinely restricted moving
windows, the total actual proper-prime-power contribution is `o(n²)`. -/
theorem ternaryAffinePrimePowerExceptions_normalized_tendsto_zero
    (left center labels : ℕ → Finset ℕ)
    (a c : ℕ → ℕ)
    (hc : ∀ n, 0 < c n)
    (hleft : ∀ n, left n ⊆ Finset.Ioc 0 n)
    (hcenter : ∀ n, center n ⊆ Finset.Ioc 0 n)
    (hlabels : ∀ n, labels n ⊆ Finset.Ioc 0 n) :
    Tendsto
      (fun n : ℕ =>
        (∑ v ∈ ternaryAffinePrimePowerExceptions
          (left n) (center n) (labels n) (a n) (c n),
            ternaryAffineVonMangoldtWeight v) / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds ternaryPrimePowerErrorBound_normalized_tendsto_zero
    ?_ ?_
  · exact Eventually.of_forall fun n =>
      div_nonneg (Finset.sum_nonneg fun v _ =>
        ternaryAffineVonMangoldtWeight_nonneg v) (by positivity)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hpositive : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    apply (div_le_div_iff_of_pos_right hpositive).mpr
    exact ternaryAffinePrimePowerExceptions_weight_le
      (left n) (center n) (labels n) (a n) (c n) n
        (hc n) (hleft n) (hcenter n) (hlabels n)

/-- Replacing all three unrestricted von Mangoldt windows by actual prime
windows changes the genuine affine correlation by `o(n²)`, uniformly in
moving coefficients and arbitrary residue/archimedean selectors. -/
theorem ternaryAffineVonMangoldt_prime_restriction_tendsto_zero
    (left center labels : ℕ → Finset ℕ)
    (a c : ℕ → ℕ)
    (hc : ∀ n, 0 < c n)
    (hleft : ∀ n, left n ⊆ Finset.Ioc 0 n)
    (hcenter : ∀ n, center n ⊆ Finset.Ioc 0 n)
    (hlabels : ∀ n, labels n ⊆ Finset.Ioc 0 n) :
    Tendsto
      (fun n : ℕ =>
        ((∑ v ∈ ternaryAffineTriples
            (left n) (center n) (labels n) (a n) (c n),
              ternaryAffineVonMangoldtWeight v) -
          (∑ v ∈ (ternaryAffineTriples
            (left n) (center n) (labels n) (a n) (c n)).filter
              (fun v => v.1.Prime ∧ v.2.1.Prime ∧ v.2.2.Prime),
                ternaryAffineVonMangoldtWeight v)) / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  have herror := ternaryAffinePrimePowerExceptions_normalized_tendsto_zero
    left center labels a c hc hleft hcenter hlabels
  convert herror using 1
  ext n
  rw [ternaryAffineVonMangoldtSum_eq_prime_sum_add_exceptions
    (left n) (center n) (labels n) (a n) (c n)]
  ring

/-- The genuine circle character is globally Lipschitz at the principal
major-arc center, with the exact elementary constant `2π`. -/
theorem ternary_circle_character_sub_one_norm_le (θ : ℝ) :
    ‖GoldbachChain.e θ - 1‖ ≤ 2 * Real.pi * |θ| := by
  rw [GoldbachChain.e_sub_one_norm]
  calc
    2 * |Real.sin (Real.pi * θ)| ≤ 2 * |Real.pi * θ| := by
      exact mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = 2 * Real.pi * |θ| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      ring

/-- The real part of every principal-arc additive character is bounded below
without any sign, positivity, or exact-affine-relation assumption. -/
theorem ternary_circle_character_real_lower (θ : ℝ) :
    1 - 2 * Real.pi * |θ| ≤ (GoldbachChain.e θ).re := by
  have hnorm := ternary_circle_character_sub_one_norm_le θ
  have hreal := (Complex.abs_re_le_norm (GoldbachChain.e θ - 1)).trans hnorm
  have hlower := neg_le_of_abs_le hreal
  change -(2 * Real.pi * |θ|) ≤ (GoldbachChain.e θ).re - 1 at hlower
  linarith

/-- Exact pointwise expansion of the genuine unweighted ternary affine model;
unlike Fourier orthogonality, this identity is valid on a truncated arc. -/
theorem ternary_unweighted_cubic_pointwise_expansion
    (left center labels : Finset ℕ) (a c : ℕ) (β : ℝ) :
    ternaryExponentialSum left (fun _ => 1) (a : ℤ) β *
        ternaryExponentialSum center (fun _ => 1) (-(c : ℤ)) β *
          ternaryExponentialSum labels (fun _ => 1) 1 β =
      ∑ x ∈ left, ∑ y ∈ center, ∑ z ∈ labels,
        GoldbachChain.e
          (((a : ℝ) * x - (c : ℝ) * y + z) * β) := by
  unfold ternaryExponentialSum
  simp_rw [one_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  rw [GoldbachChain.e_add, GoldbachChain.e_add]
  congr 1
  push_cast
  ring

/-- On the genuine truncated principal major arc, every individual
three-window phase has real part at least `1/2`.  Consequently the full
smooth cubic model has a quantitative positive `card(left) card(center)
card(labels) / 2` lower bound, rather than mere whole-circle positivity. -/
theorem ternary_unweighted_cubic_principal_arc_real_lower
    (left center labels : Finset ℕ) (a c : ℕ) (K β : ℝ)
    (hK : 0 < K)
    (hphase : ∀ x ∈ left, ∀ y ∈ center, ∀ z ∈ labels,
      |(a : ℝ) * x - (c : ℝ) * y + z| ≤ K)
    (hβ : |β| ≤ 1 / (4 * Real.pi * K)) :
    ((left.card : ℝ) * (center.card : ℝ) * (labels.card : ℝ)) / 2 ≤
      (ternaryExponentialSum left (fun _ => 1) (a : ℤ) β *
        ternaryExponentialSum center (fun _ => 1) (-(c : ℤ)) β *
          ternaryExponentialSum labels (fun _ => 1) 1 β).re := by
  rw [ternary_unweighted_cubic_pointwise_expansion]
  simp_rw [Complex.re_sum]
  have hterm (x y z : ℕ) (hx : x ∈ left) (hy : y ∈ center)
      (hz : z ∈ labels) :
      (1 / 2 : ℝ) ≤
        (GoldbachChain.e
          (((a : ℝ) * x - (c : ℝ) * y + z) * β)).re := by
    have hproduct :
        2 * Real.pi *
            |((a : ℝ) * x - (c : ℝ) * y + z) * β| ≤ 1 / 2 := by
      rw [abs_mul]
      calc
        2 * Real.pi *
            (|(a : ℝ) * x - (c : ℝ) * y + z| * |β|) ≤
          2 * Real.pi * (K * (1 / (4 * Real.pi * K))) := by
            gcongr
            exact hphase x hx y hy z hz
        _ = 1 / 2 := by
          field_simp; ring
    have hreal := ternary_circle_character_real_lower
      (((a : ℝ) * x - (c : ℝ) * y + z) * β)
    linarith
  have hsum :
      (∑ x ∈ left, ∑ y ∈ center, ∑ _z ∈ labels, (1 / 2 : ℝ)) ≤
        ∑ x ∈ left, ∑ y ∈ center, ∑ z ∈ labels,
          (GoldbachChain.e
            (((a : ℝ) * x - (c : ℝ) * y + z) * β)).re := by
    apply Finset.sum_le_sum
    intro x hx
    apply Finset.sum_le_sum
    intro y hy
    apply Finset.sum_le_sum
    intro z hz
    exact hterm x y z hx hy hz
  convert hsum using 1
  simp [nsmul_eq_mul]
  ring

/-- The genuine *truncated* principal major arc already has explicit positive
quadratic-scale archimedean mass.  If the three windows have linear size and
the actual affine phases have linear height `K`, the lower bound is of order
`n²`; this is not an appeal to the unrelated whole-circle singular integral. -/
theorem ternary_unweighted_cubic_principal_arc_integral_lower
    (left center labels : Finset ℕ) (a c : ℕ) (K : ℝ)
    (hK : 0 < K)
    (hphase : ∀ x ∈ left, ∀ y ∈ center, ∀ z ∈ labels,
      |(a : ℝ) * x - (c : ℝ) * y + z| ≤ K) :
    ((left.card : ℝ) * (center.card : ℝ) * (labels.card : ℝ)) /
        (8 * Real.pi * K) ≤
      (∫ β in Set.Ioc (0 : ℝ) (1 / (4 * Real.pi * K)),
        ternaryExponentialSum left (fun _ => 1) (a : ℤ) β *
          ternaryExponentialSum center (fun _ => 1) (-(c : ℤ)) β *
            ternaryExponentialSum labels (fun _ => 1) 1 β).re := by
  let δ : ℝ := 1 / (4 * Real.pi * K)
  let f : ℝ → ℂ := fun β =>
    ternaryExponentialSum left (fun _ => 1) (a : ℤ) β *
      ternaryExponentialSum center (fun _ => 1) (-(c : ℤ)) β *
        ternaryExponentialSum labels (fun _ => 1) 1 β
  let mass : ℝ :=
    ((left.card : ℝ) * (center.card : ℝ) * (labels.card : ℝ)) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hcontinuous : Continuous f := by
    dsimp [f]
    unfold ternaryExponentialSum GoldbachChain.e
    fun_prop
  have hintegrable : IntegrableOn f (Set.Ioc (0 : ℝ) δ) volume :=
    hcontinuous.integrableOn_Ioc
  have hreal :
      (∫ β in Set.Ioc (0 : ℝ) δ, (f β).re) =
        (∫ β in Set.Ioc (0 : ℝ) δ, f β).re := by
    have h := integral_re hintegrable
    simpa [RCLike.re_to_complex] using h
  have hconstant :
      (∫ _β in Set.Ioc (0 : ℝ) δ, mass) = mass * δ := by
    rw [setIntegral_const, Real.volume_real_Ioc_of_le hδ.le,
      sub_zero, smul_eq_mul, mul_comm]
  have hcomparison :
      (∫ _β in Set.Ioc (0 : ℝ) δ, mass) ≤
        ∫ β in Set.Ioc (0 : ℝ) δ, (f β).re := by
    apply setIntegral_mono_on
      (integrableOn_const (by
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top))
      hintegrable.re measurableSet_Ioc
    intro β hβ
    have hsmall : |β| ≤ δ := by
      rw [abs_of_nonneg hβ.1.le]
      exact hβ.2
    exact ternary_unweighted_cubic_principal_arc_real_lower
      left center labels a c K β hK hphase hsmall
  change
    ((left.card : ℝ) * (center.card : ℝ) * (labels.card : ℝ)) /
        (8 * Real.pi * K) ≤
      (∫ β in Set.Ioc (0 : ℝ) δ, f β).re
  calc
    ((left.card : ℝ) * (center.card : ℝ) * (labels.card : ℝ)) /
        (8 * Real.pi * K) = mass * δ := by
      dsimp [mass, δ]
      field_simp; ring
    _ = ∫ _β in Set.Ioc (0 : ℝ) δ, mass := hconstant.symm
    _ ≤ ∫ β in Set.Ioc (0 : ℝ) δ, (f β).re := hcomparison
    _ = (∫ β in Set.Ioc (0 : ℝ) δ, f β).re := hreal

/-- The actual admissible residue-cell major-arc model itself has positive
mass on a genuinely truncated arc, with its exact `φ(modulus)⁻³` factor and
its three true archimedean interval cardinalities.  This strengthens the
previous whole-circle singular-integral identity to an explicit local arc. -/
theorem ternary_manuscript_interval_model_principal_arc_integral_lower
    (modulus labelResidue leftResidue rightResidue a d : ℕ)
    (hmodulus : 0 < modulus)
    (hadmissible :
      (a * leftResidue + labelResidue) % modulus =
        (2 * d * rightResidue) % modulus)
    (labelLower labelUpper leftLower leftUpper rightLower rightUpper : ℕ)
    (numerator : ℤ) (K : ℝ)
    (hK : 0 < K)
    (hphase :
      ∀ x ∈ Finset.Ico leftLower leftUpper,
        ∀ y ∈ Finset.Ico rightLower rightUpper,
          ∀ z ∈ Finset.Ico labelLower labelUpper,
            |(a : ℝ) * x - (2 * d : ℕ) * y + z| ≤ K) :
    (1 / (modulus.totient : ℝ)) ^ 3 *
      (((Finset.Ico leftLower leftUpper).card : ℝ) *
        ((Finset.Ico rightLower rightUpper).card : ℝ) *
        ((Finset.Ico labelLower labelUpper).card : ℝ) /
          (8 * Real.pi * K)) ≤
      (∫ β in Set.Ioc (0 : ℝ) (1 / (4 * Real.pi * K)),
        ternaryMajorArcIntervalModel
            labelLower labelUpper modulus labelResidue 1 numerator β *
          ternaryMajorArcIntervalModel
            leftLower leftUpper modulus leftResidue
              (a : ℤ) numerator β *
          ternaryMajorArcIntervalModel
            rightLower rightUpper modulus rightResidue
              (-2 * (d : ℤ)) numerator β).re := by
  let left := Finset.Ico leftLower leftUpper
  let center := Finset.Ico rightLower rightUpper
  let labels := Finset.Ico labelLower labelUpper
  let δ : ℝ := 1 / (4 * Real.pi * K)
  let smooth : ℝ → ℂ := fun β =>
    ternaryExponentialSum left (fun _ => 1) (a : ℤ) β *
      ternaryExponentialSum center (fun _ => 1)
        (-(2 * d : ℕ) : ℤ) β *
        ternaryExponentialSum labels (fun _ => 1) 1 β
  let model : ℝ → ℂ := fun β =>
    ternaryMajorArcIntervalModel
        labelLower labelUpper modulus labelResidue 1 numerator β *
      ternaryMajorArcIntervalModel
        leftLower leftUpper modulus leftResidue
          (a : ℤ) numerator β *
      ternaryMajorArcIntervalModel
        rightLower rightUpper modulus rightResidue
          (-2 * (d : ℤ)) numerator β
  have hfrequency :
      (-2 * (d : ℤ)) = (-(2 * d : ℕ) : ℤ) := by
    push_cast
    ring
  have hpoint (β : ℝ) :
      model β = (1 / (modulus.totient : ℂ)) ^ 3 * smooth β := by
    have hmodel := ternary_manuscript_interval_model_product_eq
      modulus labelResidue leftResidue rightResidue a d
      hmodulus hadmissible labelLower labelUpper leftLower leftUpper
      rightLower rightUpper numerator β
    rw [hfrequency] at hmodel
    change model β = _ at hmodel
    rw [hmodel]
    dsimp [smooth, left, center, labels]
    ring
  have hintegral :
      (∫ β in Set.Ioc (0 : ℝ) δ, model β) =
        (1 / (modulus.totient : ℂ)) ^ 3 *
          (∫ β in Set.Ioc (0 : ℝ) δ, smooth β) := by
    calc
      (∫ β in Set.Ioc (0 : ℝ) δ, model β) =
          ∫ β in Set.Ioc (0 : ℝ) δ,
            (1 / (modulus.totient : ℂ)) ^ 3 * smooth β := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro β hβ
        exact hpoint β
      _ = _ := by rw [integral_const_mul]
  have hbase := ternary_unweighted_cubic_principal_arc_integral_lower
    left center labels a (2 * d) K hK hphase
  have hcoefficient :
      (1 / (modulus.totient : ℂ)) ^ 3 =
        (((1 / (modulus.totient : ℝ)) ^ 3 : ℝ) : ℂ) := by
    push_cast
    rfl
  change
    (1 / (modulus.totient : ℝ)) ^ 3 *
      (((left.card : ℝ) * (center.card : ℝ) * (labels.card : ℝ)) /
        (8 * Real.pi * K)) ≤
      (∫ β in Set.Ioc (0 : ℝ) δ, model β).re
  rw [hintegral, hcoefficient, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_le_mul_of_nonneg_left hbase (by positivity)

/-- The actual residue-restricted manuscript cubic, with its genuine
von-Mangoldt weights, independent archimedean windows, integral affine
coefficients, and shifted rational major-arc center. -/
noncomputable def ternaryManuscriptResidueCubicVonMangoldt
    (modulus labelResidue leftResidue rightResidue a d : ℕ)
    (labelLower labelUpper leftLower leftUpper rightLower rightUpper : ℕ)
    (numerator : ℤ) (β : ℝ) : ℂ :=
  ternaryExponentialSum
      ((Finset.Ico labelLower labelUpper).filter
        fun n => n % modulus = labelResidue)
      (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
      1 ((numerator : ℝ) / modulus + β) *
    ternaryExponentialSum
      ((Finset.Ico leftLower leftUpper).filter
        fun n => n % modulus = leftResidue)
      (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
      (a : ℤ) ((numerator : ℝ) / modulus + β) *
    ternaryExponentialSum
      ((Finset.Ico rightLower rightUpper).filter
        fun n => n % modulus = rightResidue)
      (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
      (-2 * (d : ℤ)) ((numerator : ℝ) / modulus + β)

/-- The positive truncated central-arc lower bound transfers to the *actual*
three-von-Mangoldt cubic, with the exact arc-length error cost.  The remaining
hypothesis is only an explicit pointwise approximation error; it is not a
postulated positive lower bound for the actual prime correlation. -/
theorem ternary_manuscript_residue_vonMangoldt_principal_arc_integral_lower_of_error
    (modulus labelResidue leftResidue rightResidue a d : ℕ)
    (hmodulus : 0 < modulus)
    (hadmissible :
      (a * leftResidue + labelResidue) % modulus =
        (2 * d * rightResidue) % modulus)
    (labelLower labelUpper leftLower leftUpper rightLower rightUpper : ℕ)
    (numerator : ℤ) (K bound : ℝ)
    (hK : 1 ≤ K)
    (hphase :
      ∀ x ∈ Finset.Ico leftLower leftUpper,
        ∀ y ∈ Finset.Ico rightLower rightUpper,
          ∀ z ∈ Finset.Ico labelLower labelUpper,
            |(a : ℝ) * x - (2 * d : ℕ) * y + z| ≤ K)
    (herror :
      ∀ β ∈ Set.Ioc (0 : ℝ) (1 / (4 * Real.pi * K)),
        ‖ternaryManuscriptResidueCubicVonMangoldt
            modulus labelResidue leftResidue rightResidue a d
            labelLower labelUpper leftLower leftUpper
            rightLower rightUpper numerator β -
          ternaryMajorArcIntervalModel
              labelLower labelUpper modulus labelResidue 1 numerator β *
            ternaryMajorArcIntervalModel
              leftLower leftUpper modulus leftResidue
                (a : ℤ) numerator β *
            ternaryMajorArcIntervalModel
              rightLower rightUpper modulus rightResidue
                (-2 * (d : ℤ)) numerator β‖ ≤ bound) :
    (1 / (modulus.totient : ℝ)) ^ 3 *
      (((Finset.Ico leftLower leftUpper).card : ℝ) *
        ((Finset.Ico rightLower rightUpper).card : ℝ) *
        ((Finset.Ico labelLower labelUpper).card : ℝ) /
          (8 * Real.pi * K)) - bound / (4 * Real.pi * K) ≤
      (∫ β in Set.Ioc (0 : ℝ) (1 / (4 * Real.pi * K)),
        ternaryManuscriptResidueCubicVonMangoldt
          modulus labelResidue leftResidue rightResidue a d
          labelLower labelUpper leftLower leftUpper
          rightLower rightUpper numerator β).re := by
  let δ : ℝ := 1 / (4 * Real.pi * K)
  let actual : ℝ → ℂ := fun β =>
    ternaryManuscriptResidueCubicVonMangoldt
      modulus labelResidue leftResidue rightResidue a d
      labelLower labelUpper leftLower leftUpper
      rightLower rightUpper numerator β
  let model : ℝ → ℂ := fun β =>
    ternaryMajorArcIntervalModel
        labelLower labelUpper modulus labelResidue 1 numerator β *
      ternaryMajorArcIntervalModel
        leftLower leftUpper modulus leftResidue
          (a : ℤ) numerator β *
      ternaryMajorArcIntervalModel
        rightLower rightUpper modulus rightResidue
          (-2 * (d : ℤ)) numerator β
  let main : ℝ :=
    (1 / (modulus.totient : ℝ)) ^ 3 *
      (((Finset.Ico leftLower leftUpper).card : ℝ) *
        ((Finset.Ico rightLower rightUpper).card : ℝ) *
        ((Finset.Ico labelLower labelUpper).card : ℝ) /
          (8 * Real.pi * K))
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδone : δ ≤ 1 := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity : 0 < 4 * Real.pi * K)).mpr
    nlinarith [Real.pi_gt_three]
  have hsubset : Set.Ioc (0 : ℝ) δ ⊆ Set.Ioc (0 : ℝ) 1 := by
    intro β hβ
    exact ⟨hβ.1, hβ.2.trans hδone⟩
  have hactualContinuous : Continuous actual := by
    dsimp [actual, ternaryManuscriptResidueCubicVonMangoldt]
    unfold ternaryExponentialSum GoldbachChain.e
    fun_prop
  have hmodelContinuous : Continuous model := by
    dsimp [model, ternaryMajorArcIntervalModel]
    unfold ternaryExponentialSum GoldbachChain.e
    fun_prop
  have hmain := ternary_manuscript_interval_model_principal_arc_integral_lower
    modulus labelResidue leftResidue rightResidue a d hmodulus hadmissible
    labelLower labelUpper leftLower leftUpper rightLower rightUpper
    numerator K hKpos hphase
  have htransfer := ternary_major_arc_real_lower_of_model
    (Set.Ioc (0 : ℝ) δ) measurableSet_Ioc hsubset actual model
    hactualContinuous.integrableOn_Ioc
    hmodelContinuous.integrableOn_Ioc bound main herror hmain
  rw [Real.volume_real_Ioc_of_le hδ.le, sub_zero] at htransfer
  change main - bound / (4 * Real.pi * K) ≤
    (∫ β in Set.Ioc (0 : ℝ) δ, actual β).re
  convert htransfer using 1
  dsimp [δ]
  ring

/-- The fully explicit cubic pointwise Siegel--Walfisz/Abel error for one
actual shifted residue cell and three independent finite manuscript windows. -/
noncomputable def ternaryManuscriptMajorArcCubicError
    (c C : ℝ) (N modulus labelResidue leftResidue rightResidue a d : ℕ)
    (labelLower labelUpper leftLower leftUpper rightLower rightUpper : ℕ)
    (numerator : ℤ) (β : ℝ) : ℝ :=
  let labelModel := ternaryMajorArcIntervalModel
    labelLower labelUpper modulus labelResidue 1 numerator β
  let leftModel := ternaryMajorArcIntervalModel
    leftLower leftUpper modulus leftResidue (a : ℤ) numerator β
  let rightModel := ternaryMajorArcIntervalModel
    rightLower rightUpper modulus rightResidue
      (-2 * (d : ℤ)) numerator β
  let labelError := 2 * ternaryMajorArcProgressionError c C N 1 β
  let leftError := 2 * ternaryMajorArcProgressionError c C N (a : ℤ) β
  let rightError :=
    2 * ternaryMajorArcProgressionError c C N (-2 * (d : ℤ)) β
  labelError * (‖leftModel‖ + leftError) *
      (‖rightModel‖ + rightError) +
    ‖labelModel‖ * leftError * (‖rightModel‖ + rightError) +
    ‖labelModel‖ * ‖leftModel‖ * rightError

/-- Unconditional rated positivity transfer to the *actual* truncated
three-prime von-Mangoldt central arc.  The subtractive error is exactly the
integral of the already proved explicit Siegel--Walfisz/Abel cubic error; no
pointwise approximation, positivity of the actual prime sum, or singular
series is assumed.  Complementary shifted/minor-arc cancellation remains a
separate obstruction. -/
theorem ternary_rated_manuscript_residue_principal_arc_integral_lower
    (B : ℝ) (hB : 1 ≤ B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N →
        ∀ labelLower labelUpper leftLower leftUpper rightLower rightUpper : ℕ,
          labelLower ≤ labelUpper → labelUpper ≤ N →
          leftLower ≤ leftUpper → leftUpper ≤ N →
          rightLower ≤ rightUpper → rightUpper ≤ N →
          ∀ modulus : ℕ, 0 < modulus →
            (modulus : ℝ) ≤ Real.log N ^ B →
            ∀ labelResidue leftResidue rightResidue : ℕ,
              labelResidue < modulus →
              leftResidue < modulus →
              rightResidue < modulus →
              Nat.gcd labelResidue modulus = 1 →
              Nat.gcd leftResidue modulus = 1 →
              Nat.gcd rightResidue modulus = 1 →
              ∀ a d : ℕ,
                (a * leftResidue + labelResidue) % modulus =
                  (2 * d * rightResidue) % modulus →
                ∀ numerator : ℤ, ∀ K : ℝ, 0 < K →
                  (∀ x ∈ Finset.Ico leftLower leftUpper,
                    ∀ y ∈ Finset.Ico rightLower rightUpper,
                      ∀ z ∈ Finset.Ico labelLower labelUpper,
                        |(a : ℝ) * x - (2 * d : ℕ) * y + z| ≤ K) →
                    (1 / (modulus.totient : ℝ)) ^ 3 *
                        (((Finset.Ico leftLower leftUpper).card : ℝ) *
                          ((Finset.Ico rightLower rightUpper).card : ℝ) *
                          ((Finset.Ico labelLower labelUpper).card : ℝ) /
                            (8 * Real.pi * K)) -
                      (∫ β in Set.Ioc (0 : ℝ) (1 / (4 * Real.pi * K)),
                        ternaryManuscriptMajorArcCubicError
                          c C N modulus labelResidue leftResidue rightResidue a d
                          labelLower labelUpper leftLower leftUpper
                          rightLower rightUpper numerator β) ≤
                      (∫ β in Set.Ioc (0 : ℝ) (1 / (4 * Real.pi * K)),
                        ternaryManuscriptResidueCubicVonMangoldt
                          modulus labelResidue leftResidue rightResidue a d
                          labelLower labelUpper leftLower leftUpper
                          rightLower rightUpper numerator β).re := by
  obtain ⟨c, C, hc, hC, N₀, hrated⟩ :=
    ternary_rated_manuscript_interval_major_arc_product_model B hB
  refine ⟨c, C, hc, hC, N₀, ?_⟩
  intro N hN labelLower labelUpper leftLower leftUpper
    rightLower rightUpper hlabelLower hlabelUpper hleftLower hleftUpper
    hrightLower hrightUpper modulus hmodulus hsize
    labelResidue leftResidue rightResidue hlabelResidue
    hleftResidue hrightResidue hlabelUnit hleftUnit hrightUnit
    a d hadmissible numerator K hK hphase
  let δ : ℝ := 1 / (4 * Real.pi * K)
  let actual : ℝ → ℂ := fun β =>
    ternaryManuscriptResidueCubicVonMangoldt
      modulus labelResidue leftResidue rightResidue a d
      labelLower labelUpper leftLower leftUpper
      rightLower rightUpper numerator β
  let model : ℝ → ℂ := fun β =>
    ternaryMajorArcIntervalModel
        labelLower labelUpper modulus labelResidue 1 numerator β *
      ternaryMajorArcIntervalModel
        leftLower leftUpper modulus leftResidue
          (a : ℤ) numerator β *
      ternaryMajorArcIntervalModel
        rightLower rightUpper modulus rightResidue
          (-2 * (d : ℤ)) numerator β
  let error : ℝ → ℝ := fun β =>
    ternaryManuscriptMajorArcCubicError
      c C N modulus labelResidue leftResidue rightResidue a d
      labelLower labelUpper leftLower leftUpper
      rightLower rightUpper numerator β
  have hpoint : ∀ β ∈ Set.Ioc (0 : ℝ) δ,
      ‖actual β - model β‖ ≤ error β := by
    intro β hβ
    exact hrated N hN labelLower labelUpper leftLower leftUpper
      rightLower rightUpper hlabelLower hlabelUpper hleftLower hleftUpper
      hrightLower hrightUpper modulus hmodulus hsize
      labelResidue leftResidue rightResidue hlabelResidue
      hleftResidue hrightResidue hlabelUnit hleftUnit hrightUnit
      a d numerator β
  have hactualContinuous : Continuous actual := by
    dsimp [actual, ternaryManuscriptResidueCubicVonMangoldt]
    unfold ternaryExponentialSum GoldbachChain.e
    fun_prop
  have hmodelContinuous : Continuous model := by
    dsimp [model, ternaryMajorArcIntervalModel]
    unfold ternaryExponentialSum GoldbachChain.e
    fun_prop
  have herrorContinuous : Continuous error := by
    dsimp [error, ternaryManuscriptMajorArcCubicError,
      ternaryMajorArcProgressionError, ternaryMajorArcIntervalModel]
    unfold ternaryExponentialSum GoldbachChain.e
    fun_prop
  have hnorm := ternary_major_arc_integrated_error
    (Set.Ioc (0 : ℝ) δ) measurableSet_Ioc actual model error
    hactualContinuous.integrableOn_Ioc
    hmodelContinuous.integrableOn_Ioc
    herrorContinuous.integrableOn_Ioc hpoint
  have hreal :=
    (Complex.abs_re_le_norm
      ((∫ β in Set.Ioc (0 : ℝ) δ, actual β) -
        (∫ β in Set.Ioc (0 : ℝ) δ, model β))).trans hnorm
  have hlower := neg_le_of_abs_le hreal
  change -(∫ β in Set.Ioc (0 : ℝ) δ, error β) ≤
    (∫ β in Set.Ioc (0 : ℝ) δ, actual β).re -
      (∫ β in Set.Ioc (0 : ℝ) δ, model β).re at hlower
  have hmain := ternary_manuscript_interval_model_principal_arc_integral_lower
    modulus labelResidue leftResidue rightResidue a d hmodulus hadmissible
    labelLower labelUpper leftLower leftUpper rightLower rightUpper
    numerator K hK hphase
  change
    (1 / (modulus.totient : ℝ)) ^ 3 *
          (((Finset.Ico leftLower leftUpper).card : ℝ) *
            ((Finset.Ico rightLower rightUpper).card : ℝ) *
            ((Finset.Ico labelLower labelUpper).card : ℝ) /
              (8 * Real.pi * K)) -
        (∫ β in Set.Ioc (0 : ℝ) δ, error β) ≤
      (∫ β in Set.Ioc (0 : ℝ) δ, actual β).re
  linarith

end Erdos689

#print axioms Erdos689.ternaryProperPrimePowers_card_le
#print axioms Erdos689.ternaryAffinePrimePowerExceptions_card_le
#print axioms Erdos689.ternaryAffineVonMangoldtWeight_nonneg
#print axioms Erdos689.ternaryAffineVonMangoldtWeight_le_log_cube
#print axioms Erdos689.ternaryAffinePrimePowerExceptions_weight_le
#print axioms Erdos689.ternaryAffineVonMangoldtSum_eq_prime_sum_add_exceptions
#print axioms Erdos689.ternaryPrimePowerErrorBound_normalized_tendsto_zero
#print axioms Erdos689.ternaryAffinePrimePowerExceptions_normalized_tendsto_zero
#print axioms Erdos689.ternaryAffineVonMangoldt_prime_restriction_tendsto_zero
#print axioms Erdos689.ternary_circle_character_sub_one_norm_le
#print axioms Erdos689.ternary_circle_character_real_lower
#print axioms Erdos689.ternary_unweighted_cubic_pointwise_expansion
#print axioms Erdos689.ternary_unweighted_cubic_principal_arc_real_lower
#print axioms Erdos689.ternary_unweighted_cubic_principal_arc_integral_lower
#print axioms Erdos689.ternary_manuscript_interval_model_principal_arc_integral_lower
#print axioms Erdos689.ternary_manuscript_residue_vonMangoldt_principal_arc_integral_lower_of_error
#print axioms Erdos689.ternary_rated_manuscript_residue_principal_arc_integral_lower
