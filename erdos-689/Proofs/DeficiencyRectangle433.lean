import DeficiencyTruncation433
import DeficiencyZeroCrt

/-!
# Actual finite smooth-coefficient rectangles for Erdős problem #689

The dyadic coordinate and the switched-prime coordinates are independent only
when the switched support excludes two. Distinct exponent vectors then encode
distinct positive even smooth coefficients. Combining their actual zero-hit
residue fibers with the finite smooth-family density theorem identifies the
finite Euler rectangle inside the real initial-deficiency ledger.

All results in this file concern the initial assignment, not the complete
eventual covering conjecture.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos689

/-- Bounded exponent vectors on the finite switched-prime support. -/
noncomputable def smoothRectangleExponentVectors (S : Finset ℕ) (E : ℕ) :
    Finset ({p : ℕ // p ∈ S} → ℕ) := by
  classical
  exact Fintype.piFinset fun _ : {p : ℕ // p ∈ S} => Finset.range (E + 1)

/-- The positive even smooth core specified by one dyadic/support exponent vector. -/
noncomputable def smoothRectangleCore (S : Finset ℕ) (k : ℕ)
    (v : {p : ℕ // p ∈ S} → ℕ) : ℕ :=
  2 ^ (k + 1) * ∏ p : {p : ℕ // p ∈ S}, (p : ℕ) ^ v p

/-- Every exponent-encoded smooth core is positive. -/
theorem smoothRectangleCore_pos (S : Finset ℕ) (k : ℕ)
    (v : {p : ℕ // p ∈ S} → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime) :
    0 < smoothRectangleCore S k v := by
  unfold smoothRectangleCore
  apply Nat.mul_pos
  · positivity
  · exact Finset.prod_pos fun p _ => pow_pos (hsupport p p.2).pos _

/-- Every exponent-encoded smooth core belongs to the genuine deficiency family. -/
theorem smoothRectangleCore_smooth (S : Finset ℕ) (k : ℕ)
    (v : {p : ℕ // p ∈ S} → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime) :
    deficiencySmoothCoefficient S (smoothRectangleCore S k v) := by
  refine ⟨smoothRectangleCore_pos S k v hsupport, ?_, ?_⟩
  · unfold smoothRectangleCore
    exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _
  · intro q hq hdiv
    unfold smoothRectangleCore at hdiv
    rcases hq.dvd_mul.mp hdiv with htwo | hproduct
    · left
      exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
        (hq.dvd_of_dvd_pow htwo)
    · right
      obtain ⟨p, _, hp⟩ :=
        (hq.prime.dvd_finsetProd_iff
          (fun p : {p : ℕ // p ∈ S} => (p : ℕ) ^ v p)).mp hproduct
      have heq := (Nat.prime_dvd_prime_iff_eq hq (hsupport p p.2)).mp
        (hq.dvd_of_dvd_pow hp)
      simp [heq, p.2]

/-- The dyadic coordinate is recovered exactly from the encoded smooth core. -/
theorem smoothRectangleCore_factorization_two (S : Finset ℕ) (k : ℕ)
    (v : {p : ℕ // p ∈ S} → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hodd : 2 ∉ S) :
    (smoothRectangleCore S k v).factorization 2 = k + 1 := by
  classical
  have hproduct : (∏ p : {p : ℕ // p ∈ S}, (p : ℕ) ^ v p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p _ =>
      pow_ne_zero _ (hsupport p p.2).ne_zero
  rw [smoothRectangleCore,
    Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hproduct,
    Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_prod_apply]
  · have hzero :
        (∑ p : {p : ℕ // p ∈ S}, ((p : ℕ) ^ v p).factorization 2) = 0 := by
        apply Finset.sum_eq_zero
        intro p _
        rw [(hsupport p p.2).factorization_pow, Finsupp.single_apply]
        have hpne : (p : ℕ) ≠ 2 := fun h => hodd (h ▸ p.2)
        simp [hpne]
    rw [hzero, add_zero]
  · intro p _
    exact pow_ne_zero _ (hsupport p p.2).ne_zero

/-- Every switched-prime exponent is recovered exactly from its smooth core. -/
theorem smoothRectangleCore_factorization_support (S : Finset ℕ) (k : ℕ)
    (v : {p : ℕ // p ∈ S} → ℕ) (p : {p : ℕ // p ∈ S})
    (hsupport : ∀ q ∈ S, q.Prime)
    (hodd : 2 ∉ S) :
    (smoothRectangleCore S k v).factorization (p : ℕ) = v p := by
  classical
  have hproduct : (∏ q : {q : ℕ // q ∈ S}, (q : ℕ) ^ v q) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun q _ =>
      pow_ne_zero _ (hsupport q q.2).ne_zero
  have hpne : (p : ℕ) ≠ 2 := fun h => hodd (h ▸ p.2)
  have htwo : (2 ^ (k + 1)).factorization (p : ℕ) = 0 := by
    rw [Nat.prime_two.factorization_pow, Finsupp.single_apply]
    simp [hpne.symm]
  rw [smoothRectangleCore,
    Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hproduct,
    Finsupp.add_apply, htwo, zero_add, Nat.factorization_prod_apply]
  · calc
      (∑ q : {q : ℕ // q ∈ S}, ((q : ℕ) ^ v q).factorization (p : ℕ)) =
          ((p : ℕ) ^ v p).factorization (p : ℕ) := by
            apply Finset.sum_eq_single p
            · intro q _ hqp
              rw [(hsupport q q.2).factorization_pow, Finsupp.single_apply]
              have hne : (q : ℕ) ≠ (p : ℕ) :=
                fun h => hqp (Subtype.ext h)
              simp [hne]
            · simp
      _ = v p := Nat.factorization_pow_self (hsupport p p.2)
  · intro q _
    exact pow_ne_zero _ (hsupport q q.2).ne_zero

/-- Odd prime support makes the full dyadic/smooth exponent encoding injective. -/
theorem smoothRectangleCore_injective (S : Finset ℕ)
    (hsupport : ∀ p ∈ S, p.Prime) (hodd : 2 ∉ S) :
    Function.Injective
      (fun v : ℕ × ({p : ℕ // p ∈ S} → ℕ) =>
        smoothRectangleCore S v.1 v.2) := by
  intro v v' heq
  have htwo := congrArg (fun c : ℕ => c.factorization 2) heq
  rw [smoothRectangleCore_factorization_two S v.1 v.2 hsupport hodd,
    smoothRectangleCore_factorization_two S v'.1 v'.2 hsupport hodd] at htwo
  have hfirst : v.1 = v'.1 := Nat.add_right_cancel htwo
  apply Prod.ext hfirst
  funext p
  have hp := congrArg (fun c : ℕ => c.factorization (p : ℕ)) heq
  rwa [smoothRectangleCore_factorization_support S v.1 v.2 p hsupport hodd,
    smoothRectangleCore_factorization_support S v'.1 v'.2 p hsupport hodd] at hp

/-- A switched support prime divides the encoded core exactly at positive exponent. -/
theorem smoothRectangleCore_support_dvd_iff (S : Finset ℕ) (k : ℕ)
    (v : {p : ℕ // p ∈ S} → ℕ) (p : {p : ℕ // p ∈ S})
    (hsupport : ∀ q ∈ S, q.Prime) (hodd : 2 ∉ S) :
    (p : ℕ) ∣ smoothRectangleCore S k v ↔ 0 < v p := by
  have hcore : smoothRectangleCore S k v ≠ 0 :=
    ne_of_gt (smoothRectangleCore_pos S k v hsupport)
  constructor
  · intro hdiv
    have hpositive := (hsupport p p.2).factorization_pos_of_dvd hcore hdiv
    rwa [smoothRectangleCore_factorization_support S k v p hsupport hodd] at hpositive
  · intro hpositive
    apply Nat.dvd_of_factorization_pos
    rw [smoothRectangleCore_factorization_support S k v p hsupport hodd]
    omega

/-- The normalized local Euler weight for a zero or positive switched exponent. -/
noncomputable def smoothRectangleLocalWeight (p e : ℕ) : ℝ :=
  if e = 0 then ((p : ℝ) - 2) / ((p : ℝ) - 1)
  else ((p : ℝ)⁻¹) ^ e

/-- Summing one bounded prime-exponent coordinate gives the manuscript selector. -/
theorem smoothRectangleLocalWeight_sum (p E : ℕ) :
    (∑ e ∈ Finset.range (E + 1), smoothRectangleLocalWeight p e) =
      truncatedSmoothDeficiencySelector p E := by
  rw [Finset.sum_range_succ']
  simp [smoothRectangleLocalWeight, truncatedSmoothDeficiencySelector, add_comm]

/-- The finite support-exponent cube has the exact expected Euler-product sum. -/
theorem smoothRectangleExponentVectors_euler_sum (S : Finset ℕ) (E : ℕ) :
    (∑ v ∈ smoothRectangleExponentVectors S E,
      ∏ p : {p : ℕ // p ∈ S}, smoothRectangleLocalWeight p (v p)) =
      ∏ p ∈ S, truncatedSmoothDeficiencySelector p E := by
  classical
  unfold smoothRectangleExponentVectors
  rw [← Finset.prod_univ_sum]
  calc
    (∏ p : {p : ℕ // p ∈ S},
      ∑ e ∈ Finset.range (E + 1), smoothRectangleLocalWeight p e) =
        ∏ p : {p : ℕ // p ∈ S}, truncatedSmoothDeficiencySelector p E := by
          apply Fintype.prod_congr
          intro p
          exact smoothRectangleLocalWeight_sum p E
    _ = ∏ p ∈ S, truncatedSmoothDeficiencySelector p E :=
      Finset.prod_coe_sort S fun p => truncatedSmoothDeficiencySelector p E

/-- One mixed CRT factor, its totient factor, and its prime power normalize exactly. -/
theorem smoothRectangleLocalWeight_eq_normalized_factor
    (p e : ℕ) (hp : p.Prime) :
    (((if 0 < e then p - 1 else p - 2 : ℕ) : ℝ) /
      (((p : ℝ) - 1) * (p : ℝ) ^ e)) =
        smoothRectangleLocalWeight p e := by
  have hpreal : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpne : (p : ℝ) ≠ 0 := by positivity
  have hpone : (p : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hpreal)
  by_cases he : e = 0
  · subst e
    simp [smoothRectangleLocalWeight,
      Nat.cast_sub (R := ℝ) hp.two_le]
  · have hepos : 0 < e := Nat.pos_of_ne_zero he
    rw [if_pos hepos, smoothRectangleLocalWeight, if_neg he,
      Nat.cast_sub (R := ℝ) hp.one_le]
    norm_num only [Nat.cast_one]
    calc
      ((p : ℝ) - 1) / (((p : ℝ) - 1) * (p : ℝ) ^ e) =
          ((p : ℝ) ^ e)⁻¹ := by field_simp
      _ = ((p : ℝ)⁻¹) ^ e := (inv_pow (p : ℝ) e).symm

/-- Every encoded core has its exact actual mixed zero-hit fiber weight. -/
theorem smoothRectangleCore_actual_zero_hit_weight
    (S : Finset ℕ) (b : ℕ → ℕ) (k : ℕ)
    (v : {p : ℕ // p ∈ S} → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hodd : 2 ∉ S)
    (hb : ∀ p ∈ S, Nat.Coprime (b p) p) :
    (((Finset.range (∏ p ∈ S, p)).filter fun r =>
        Nat.Coprime r (∏ p ∈ S, p) ∧
          switchedHits S b (smoothRectangleCore S k v * r) = 0).card : ℝ) *
        ((1 / (((∏ p ∈ S, p).totient : ℕ) : ℝ)) *
          ((smoothRectangleCore S k v : ℕ) : ℝ)⁻¹) =
      ((2 : ℝ)⁻¹) ^ (k + 1) *
        ∏ p : {p : ℕ // p ∈ S}, smoothRectangleLocalWeight p (v p) := by
  classical
  have hcount :
      (((Finset.range (∏ p ∈ S, p)).filter fun r =>
        Nat.Coprime r (∏ p ∈ S, p) ∧
          switchedHits S b (smoothRectangleCore S k v * r) = 0).card : ℝ) =
        ∏ p : {p : ℕ // p ∈ S},
          (((if 0 < v p then (p : ℕ) - 1 else (p : ℕ) - 2) : ℕ) : ℝ) := by
    rw [actual_zero_hit_unit_residues_card S b
      (smoothRectangleCore S k v) hsupport hb]
    push_cast
    rw [← Finset.prod_coe_sort S]
    apply Fintype.prod_congr
    intro p
    by_cases hv : 0 < v p
    · have hdiv :=
        (smoothRectangleCore_support_dvd_iff S k v p hsupport hodd).mpr hv
      simp [hdiv, hv]
    · have hnotdiv :=
        mt (smoothRectangleCore_support_dvd_iff S k v p hsupport hodd).mp hv
      simp [hnotdiv, hv]
  have htotient :
      (((∏ p ∈ S, p).totient : ℕ) : ℝ) =
        ∏ p : {p : ℕ // p ∈ S}, ((p : ℝ) - 1) := by
    rw [prime_support_totient_real_product S hsupport]
    exact (Finset.prod_coe_sort S fun p : ℕ => ((p : ℝ) - 1)).symm
  have hcore :
      ((smoothRectangleCore S k v : ℕ) : ℝ) =
        (2 : ℝ) ^ (k + 1) *
          ∏ p : {p : ℕ // p ∈ S}, (p : ℝ) ^ v p := by
    simp [smoothRectangleCore]
  rw [hcount, htotient, hcore]
  calc
    (∏ p : {p : ℕ // p ∈ S},
      (((if 0 < v p then (p : ℕ) - 1 else (p : ℕ) - 2) : ℕ) : ℝ)) *
        ((1 / (∏ p : {p : ℕ // p ∈ S}, ((p : ℝ) - 1))) *
          ((2 : ℝ) ^ (k + 1) *
            ∏ p : {p : ℕ // p ∈ S}, (p : ℝ) ^ v p)⁻¹) =
      ((2 : ℝ)⁻¹) ^ (k + 1) *
        ((∏ p : {p : ℕ // p ∈ S},
          (((if 0 < v p then (p : ℕ) - 1 else (p : ℕ) - 2) : ℕ) : ℝ)) /
          ((∏ p : {p : ℕ // p ∈ S}, ((p : ℝ) - 1)) *
            (∏ p : {p : ℕ // p ∈ S}, (p : ℝ) ^ v p))) := by
            simp [div_eq_mul_inv, inv_pow]
            ring
    _ = ((2 : ℝ)⁻¹) ^ (k + 1) *
        ∏ p : {p : ℕ // p ∈ S},
          (((if 0 < v p then (p : ℕ) - 1 else (p : ℕ) - 2 : ℕ) : ℝ) /
            (((p : ℝ) - 1) * (p : ℝ) ^ v p)) := by
          congr 1
          rw [← Finset.prod_mul_distrib, Finset.prod_div_distrib]
    _ = _ := by
      congr 1
      apply Fintype.prod_congr
      intro p
      exact smoothRectangleLocalWeight_eq_normalized_factor
        p (v p) (hsupport p p.2)

/-- The actual finite admissible core/residue family encoded by a bounded rectangle. -/
noncomputable def smoothRectangleFamily
    (S : Finset ℕ) (b : ℕ → ℕ) (E : ℕ) : Finset (ℕ × ℕ) := by
  classical
  let indices :=
    (Finset.range E).product (smoothRectangleExponentVectors S E)
  let representatives := Finset.range (∏ p ∈ S, p)
  exact ((indices.product representatives).filter fun v =>
    Nat.Coprime v.2 (∏ p ∈ S, p) ∧
      switchedHits S b (smoothRectangleCore S v.1.1 v.1.2 * v.2) = 0).image
        fun v => (smoothRectangleCore S v.1.1 v.1.2, v.2)

/-- The full core/residue encoding preserves every dyadic and support coordinate. -/
theorem smoothRectangleFamilyEncoding_injective
    (S : Finset ℕ) (hsupport : ∀ p ∈ S, p.Prime) (hodd : 2 ∉ S) :
    Function.Injective
      (fun v : (ℕ × ({p : ℕ // p ∈ S} → ℕ)) × ℕ =>
        (smoothRectangleCore S v.1.1 v.1.2, v.2)) := by
  intro v v' heq
  have hcore := congrArg Prod.fst heq
  have hindices := smoothRectangleCore_injective S hsupport hodd hcore
  have hresidue := congrArg Prod.snd heq
  exact Prod.ext hindices hresidue

/-- Every pair in the rectangle is genuinely admissible for the initial deficiency. -/
theorem smoothRectangleFamily_admissible
    (S : Finset ℕ) (b : ℕ → ℕ) (E : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime) :
    ∀ v ∈ smoothRectangleFamily S b E,
      admissibleSmoothDeficiencyCore S b v := by
  classical
  intro v hv
  unfold smoothRectangleFamily at hv
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨hproduct, hcoprime, hzero⟩ := Finset.mem_filter.mp hu
  have hrepresentative := (Finset.mem_product.mp hproduct).2
  exact ⟨smoothRectangleCore_smooth S u.1.1 u.1.2 hsupport,
    Finset.mem_range.mp hrepresentative, hcoprime, hzero⟩

/-- Summing the actual residue fibers gives the exact bounded Euler rectangle. -/
theorem smoothRectangleFamily_weight_eq
    (S : Finset ℕ) (b : ℕ → ℕ) (E : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hodd : 2 ∉ S)
    (hb : ∀ p ∈ S, Nat.Coprime (b p) p) :
    (∑ v ∈ smoothRectangleFamily S b E,
      (1 / (((∏ p ∈ S, p).totient : ℕ) : ℝ)) * ((v.1 : ℝ)⁻¹)) =
        truncatedInitialDeficiencyCoefficient S E := by
  classical
  unfold smoothRectangleFamily
  rw [Finset.sum_image]
  · rw [Finset.sum_filter]
    have hsplit :
        (∑ a ∈
          ((Finset.range E).product (smoothRectangleExponentVectors S E)).product
            (Finset.range (∏ p ∈ S, p)),
          if Nat.Coprime a.2 (∏ p ∈ S, p) ∧
            switchedHits S b (smoothRectangleCore S a.1.1 a.1.2 * a.2) = 0 then
              (1 / (((∏ p ∈ S, p).totient : ℕ) : ℝ)) *
                ((smoothRectangleCore S a.1.1 a.1.2 : ℕ) : ℝ)⁻¹
          else 0) =
        (∑ x ∈ (Finset.range E).product (smoothRectangleExponentVectors S E),
          ∑ r ∈ Finset.range (∏ p ∈ S, p),
            if Nat.Coprime r (∏ p ∈ S, p) ∧
              switchedHits S b (smoothRectangleCore S x.1 x.2 * r) = 0 then
                (1 / (((∏ p ∈ S, p).totient : ℕ) : ℝ)) *
                  ((smoothRectangleCore S x.1 x.2 : ℕ) : ℝ)⁻¹
            else 0) := by
      exact Finset.sum_product
        ((Finset.range E).product (smoothRectangleExponentVectors S E))
        (Finset.range (∏ p ∈ S, p))
        (fun a => if Nat.Coprime a.2 (∏ p ∈ S, p) ∧
          switchedHits S b (smoothRectangleCore S a.1.1 a.1.2 * a.2) = 0 then
            (1 / (((∏ p ∈ S, p).totient : ℕ) : ℝ)) *
              ((smoothRectangleCore S a.1.1 a.1.2 : ℕ) : ℝ)⁻¹
          else 0)
    have hsum :
        (∑ x ∈ (Finset.range E).product (smoothRectangleExponentVectors S E),
          ∑ r ∈ Finset.range (∏ p ∈ S, p),
            if Nat.Coprime r (∏ p ∈ S, p) ∧
              switchedHits S b (smoothRectangleCore S x.1 x.2 * r) = 0 then
                (1 / (((∏ p ∈ S, p).totient : ℕ) : ℝ)) *
                  ((smoothRectangleCore S x.1 x.2 : ℕ) : ℝ)⁻¹
            else 0) =
          ∑ x ∈ (Finset.range E).product (smoothRectangleExponentVectors S E),
            ((2 : ℝ)⁻¹) ^ (x.1 + 1) *
              ∏ p : {p : ℕ // p ∈ S}, smoothRectangleLocalWeight p (x.2 p) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact smoothRectangleCore_actual_zero_hit_weight
        S b x.1 x.2 hsupport hodd hb
    rw [hsplit, hsum]
    have hcoordinates :
        (∑ x ∈ (Finset.range E).product (smoothRectangleExponentVectors S E),
          ((2 : ℝ)⁻¹) ^ (x.1 + 1) *
            ∏ p : {p : ℕ // p ∈ S}, smoothRectangleLocalWeight p (x.2 p)) =
        (∑ k ∈ Finset.range E,
          ∑ v ∈ smoothRectangleExponentVectors S E,
            ((2 : ℝ)⁻¹) ^ (k + 1) *
              ∏ p : {p : ℕ // p ∈ S}, smoothRectangleLocalWeight p (v p)) :=
      Finset.sum_product (Finset.range E) (smoothRectangleExponentVectors S E)
        (fun x => ((2 : ℝ)⁻¹) ^ (x.1 + 1) *
          ∏ p : {p : ℕ // p ∈ S}, smoothRectangleLocalWeight p (x.2 p))
    rw [hcoordinates]
    simp_rw [← Finset.mul_sum]
    rw [smoothRectangleExponentVectors_euler_sum]
    unfold truncatedInitialDeficiencyCoefficient
      truncatedDyadicDeficiencyCoefficient
    rw [Finset.sum_mul]
  · intro x hx y hy heq
    exact smoothRectangleFamilyEncoding_injective S hsupport hodd heq

/-- Every finite diagonal coefficient rectangle is realized by actual admissible pairs. -/
theorem initial_deficiency_rectangular_realization
    (S : Finset ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hodd : 2 ∉ S)
    (hb : ∀ p ∈ S, Nat.Coprime (b p) p) :
    ∀ E : ℕ, ∃ F : Finset (ℕ × ℕ),
      (∀ v ∈ F, admissibleSmoothDeficiencyCore S b v) ∧
        (∑ v ∈ F,
          (1 / (((∏ p ∈ S, p).totient : ℕ) : ℝ)) * ((v.1 : ℝ)⁻¹)) =
            truncatedInitialDeficiencyCoefficient S E := by
  intro E
  exact ⟨smoothRectangleFamily S b E,
    smoothRectangleFamily_admissible S b E hsupport,
    smoothRectangleFamily_weight_eq S b E hsupport hodd hb⟩

/-- The actual initial deficiency has unconditional normalized liminf at least one. -/
theorem initial_deficiency_eventual_one_lower
    (S : Finset ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hodd : 2 ∉ S)
    (hb : ∀ p ∈ S, Nat.Coprime (b p) p)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      1 - ε ≤ (deficiency n (initialAssignment S b) : ℝ) /
        ((n : ℝ) / Real.log n) :=
  initial_deficiency_eventual_one_lower_of_rectangular_realization
    S b hsupport (initial_deficiency_rectangular_realization S b hsupport hodd hb)
    ε hε

#print axioms smoothRectangleCore_pos
#print axioms smoothRectangleCore_smooth
#print axioms smoothRectangleCore_factorization_two
#print axioms smoothRectangleCore_factorization_support
#print axioms smoothRectangleCore_injective
#print axioms smoothRectangleCore_support_dvd_iff
#print axioms smoothRectangleLocalWeight_sum
#print axioms smoothRectangleExponentVectors_euler_sum
#print axioms smoothRectangleLocalWeight_eq_normalized_factor
#print axioms smoothRectangleCore_actual_zero_hit_weight
#print axioms smoothRectangleFamilyEncoding_injective
#print axioms smoothRectangleFamily_admissible
#print axioms smoothRectangleFamily_weight_eq
#print axioms initial_deficiency_rectangular_realization
#print axioms initial_deficiency_eventual_one_lower

end Erdos689
