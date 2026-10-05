module

public import Erdos1054Conditional

@[expose] public section


/-!
# Conditional bridges for Erdős #1054

Connects the divisor-prefix reduction in the `Represented` namespace to the
asymptotic density and little-o formulations in `Erdos1054`, proving the
equivalence of rational epsilon-density and real little-o as well as natural
and real ratio thresholds.

Every theorem in this module takes the almost-all binary Goldbach density-zero
statement as an explicit hypothesis, which is discharged unconditionally in
`Unconditional1054.lean`.
-/

open Finset Filter Asymptotics
open scoped Topology

namespace Erdos1054

/-- Partial sum of all divisors of `e * d` not exceeding `d`. -/
noncomputable def F (e d : Nat) : Nat :=
  ((e * d).divisors.filter (fun q => q ≤ d)).sum (fun q => q)

/-- The exact modulus-first representation predicate in the comparator. -/
def IsRep (m N : Nat) : Prop :=
  ∃ e d, 0 < e ∧ 0 < d ∧ m = e * d ∧ N = F e d

/-- The positive represented integers; no total-representability assumption. -/
def Represented (N : Nat) : Prop :=
  ∃ e d, 0 < e ∧ 0 < d ∧ N = F e d

/-- The least representing modulus, with `sInf ∅ = 0` outside the domain. -/
noncomputable def f (N : Nat) : Nat := sInf {m | 0 < m ∧ IsRep m N}

/-- Count predicate members in the closed initial interval `[0, X]`. -/
noncomputable def countUpTo (P : Nat → Prop) (X : Nat) : Nat := by
  classical
  exact ((Finset.range (X + 1)).filter P).card

/-- Rational, eventual positive lower density, as in the comparator. -/
def PositiveLowerDensity (P : Nat → Prop) : Prop :=
  ∃ c : Rat, 0 < c ∧ ∃ X₀ : Nat, ∀ X : Nat, X ≥ X₀ →
    c * X ≤ (countUpTo P X : Rat)

/-- Rational, eventual density zero, as in the comparator. -/
def DensityZero (P : Nat → Prop) : Prop :=
  ∀ ε : Rat, 0 < ε → ∃ X₀ : Nat, ∀ X : Nat, X ≥ X₀ →
    (countUpTo P X : Rat) ≤ ε * X

/-- The precise even binary-Goldbach exceptional predicate. -/
def notSumOfTwoPrimes (n : Nat) : Prop :=
  Even n ∧ ¬ ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

/-- The comparator and supported reduction use definitionally identical `F`. -/
theorem F_eq (e d : Nat) : F e d = _root_.Represented.F e d := rfl

/-- Finset counting and the reduction's finite-set cardinality agree. -/
theorem countUpTo_eq (P : Nat → Prop) (X : Nat) :
    countUpTo P X = _root_.Represented.countUpTo P X := by
  classical
  have hset : _root_.Represented.setUpTo P X =
      (((Finset.range (X + 1)).filter P : Finset Nat) : Set Nat) := by
    ext n
    simp only [_root_.Represented.setUpTo, Set.mem_ofPred_eq, Finset.mem_coe,
      Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  have htf :
      (((Finset.range (X + 1)).filter P : Finset Nat) : Set Nat).toFinset =
        (Finset.range (X + 1)).filter P := by
    ext a
    simp
  rw [_root_.Represented.countUpTo, hset, Set.ncard_eq_toFinset_card', htf]
  simp only [countUpTo]

/-- Rational epsilon-density zero implies the exact real little-o hypothesis. -/
theorem densityZero_to_littleO (P : Nat → Prop) (h : DensityZero P) :
    _root_.Represented.CountIsLittleO P := by
  rw [_root_.Represented.CountIsLittleO, isLittleO_iff]
  intro ε hε
  obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn hε
  have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
  obtain ⟨X₀, hX₀⟩ := h q hq0'
  rw [eventually_atTop]
  refine ⟨X₀, fun X hX => ?_⟩
  have hle := hX₀ X hX
  have hcast : (countUpTo P X : ℝ) ≤ (q : ℝ) * X := by
    exact_mod_cast hle
  rw [← countUpTo_eq]
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  exact hcast.trans (mul_le_mul_of_nonneg_right hqε.le (by positivity))

/-- Conversely, real little-o implies the comparator's rational density-zero form. -/
theorem littleO_to_densityZero (P : Nat → Prop)
    (h : _root_.Represented.CountIsLittleO P) : DensityZero P := by
  intro ε hε
  have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hlittle :
      ∀ᶠ X : Nat in atTop,
        ‖(_root_.Represented.countUpTo P X : ℝ)‖ ≤
          (ε : ℝ) * ‖(X : ℝ)‖ := by
    exact (isLittleO_iff.mp h) hεR
  rw [eventually_atTop] at hlittle
  obtain ⟨X₀, hX₀⟩ := hlittle
  refine ⟨X₀, fun X hX => ?_⟩
  have hbound := hX₀ X hX
  rw [Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (by positivity), ← countUpTo_eq] at hbound
  exact_mod_cast hbound

/-- The two standard asymptotic-density-zero formulations are equivalent. -/
theorem densityZero_iff_littleO (P : Nat → Prop) :
    DensityZero P ↔ _root_.Represented.CountIsLittleO P :=
  ⟨densityZero_to_littleO P, littleO_to_densityZero P⟩

/-- The supported proof's sole deep input is *exactly* almost-all Goldbach. -/
theorem deepInputs_iff_goldbach :
    _root_.Represented.DeepInputs ↔ DensityZero notSumOfTwoPrimes := by
  constructor
  · intro h
    apply littleO_to_densityZero
    change _root_.Represented.CountIsLittleO
      (fun n => Even n ∧ ¬ ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q)
    exact h.goldbach_ae
  · intro h
    refine ⟨?_⟩
    change _root_.Represented.CountIsLittleO notSumOfTwoPrimes
    exact densityZero_to_littleO notSumOfTwoPrimes h

/-- A matching external Goldbach theorem discharges the entire deep-input record. -/
theorem goldbach_of_matching_density
    (hGoldbach : DensityZero notSumOfTwoPrimes) :
    _root_.Represented.DeepInputs :=
  deepInputs_iff_goldbach.mpr hGoldbach

/-- Positive real lower density yields the exact rational eventual-density form. -/
theorem lowerDensity_to_positiveLowerDensity (P : Nat → Prop)
    (h : ∃ c : ℝ, 0 < c ∧ c ≤ _root_.Represented.lowerDensity P) :
    PositiveLowerDensity P := by
  obtain ⟨c, hc0, hc⟩ := h
  obtain ⟨q, hq0, hqc⟩ := exists_rat_btwn hc0
  have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
  have hqc' : (q : ℝ) < _root_.Represented.lowerDensity P :=
    lt_of_lt_of_le hqc hc
  have hbdd : IsBoundedUnder (· ≥ ·) atTop
      (fun X : Nat => (_root_.Represented.countUpTo P X : ℝ) / (X : ℝ)) :=
    ⟨0, Filter.eventually_map.2
      (Filter.Eventually.of_forall (fun X => by positivity))⟩
  have hev : ∀ᶠ X : Nat in atTop,
      (q : ℝ) < (_root_.Represented.countUpTo P X : ℝ) / (X : ℝ) :=
    eventually_lt_of_lt_liminf hqc' hbdd
  rw [eventually_atTop] at hev
  obtain ⟨X₀, hX₀⟩ := hev
  refine ⟨q, hq0', max X₀ 1, fun X hX => ?_⟩
  have hX1 : 1 ≤ X := (le_max_right _ _).trans hX
  have hXX₀ : X₀ ≤ X := (le_max_left _ _).trans hX
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
  have hlt := hX₀ X hXX₀
  rw [lt_div_iff₀ hXpos, ← countUpTo_eq] at hlt
  exact_mod_cast hlt.le

/-- The two represented-integer domains are exactly equivalent. -/
theorem represented_iff_memR (N : Nat) :
    Represented N ↔ N ∈ _root_.Represented.R := by
  rw [_root_.Represented.mem_R_iff_exists_F]
  constructor
  · rintro ⟨e, d, he, hd, hN⟩
    exact ⟨e, d, he, hd, by rw [hN, F_eq]⟩
  · rintro ⟨e, d, he, hd, hN⟩
    exact ⟨e, d, he, hd, by rw [hN, ← F_eq]⟩

/-- The comparator and sorted-prefix formulations have the same minimum. -/
theorem f_eq (N : Nat) : f N = _root_.Represented.f N := by
  unfold f _root_.Represented.f
  congr 1
  rw [_root_.Represented.f_set_eq]
  ext m
  simp only [IsRep, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, e, d, he, hd, hme, hN⟩
    exact ⟨e, d, he, hd, hme, by rw [hN, F_eq]⟩
  · rintro ⟨e, d, he, hd, hme, hN⟩
    exact ⟨by rw [hme]; exact Nat.mul_pos he hd,
      e, d, he, hd, hme, by rw [hN, ← F_eq]⟩

/-- Positive lower density is monotone under inclusion of predicates. -/
theorem positiveLowerDensity_mono {P Q : Nat → Prop}
    (hPQ : ∀ N, P N → Q N) (hP : PositiveLowerDensity P) :
    PositiveLowerDensity Q := by
  obtain ⟨c, hc, X₀, hX₀⟩ := hP
  refine ⟨c, hc, X₀, fun X hX => ?_⟩
  have hcount : countUpTo P X ≤ countUpTo Q X := by
    rw [countUpTo_eq, countUpTo_eq]
    exact _root_.Represented.countUpTo_mono hPQ X
  exact (hX₀ X hX).trans (by exact_mod_cast hcount)

/-- Integer thresholds imply every real threshold by rounding upward. -/
theorem real_thresholds_of_nat_thresholds
    (hNat : ∀ A : Nat, 1 ≤ A →
      PositiveLowerDensity (fun N => Represented N ∧ A * N < f N))
    (A : ℝ) (hA : 1 ≤ A) :
    PositiveLowerDensity
      (fun N => Represented N ∧ A * (N : ℝ) < (f N : ℝ)) := by
  let B := Nat.ceil A
  have hAB : A ≤ (B : ℝ) := Nat.le_ceil A
  have hB : 1 ≤ B := by
    have hcast : (1 : ℝ) ≤ (B : ℝ) := hA.trans hAB
    exact_mod_cast hcast
  refine positiveLowerDensity_mono (P := fun N => Represented N ∧ B * N < f N)
    (fun N hN => ?_) (hNat B hB)
  refine ⟨hN.1, lt_of_le_of_lt (mul_le_mul_of_nonneg_right hAB (by positivity)) ?_⟩
  exact_mod_cast hN.2

/-- Real thresholds trivially specialize to natural thresholds. -/
theorem nat_thresholds_of_real_thresholds
    (hReal : ∀ A : ℝ, 1 ≤ A →
      PositiveLowerDensity
        (fun N => Represented N ∧ A * (N : ℝ) < (f N : ℝ)))
    (A : Nat) (hA : 1 ≤ A) :
    PositiveLowerDensity (fun N => Represented N ∧ A * N < f N) := by
  have hAreal : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  refine positiveLowerDensity_mono
    (P := fun N => Represented N ∧ (A : ℝ) * (N : ℝ) < (f N : ℝ))
    (fun N hN => ⟨hN.1, by exact_mod_cast hN.2⟩) (hReal A hAreal)

/-- The natural and real versions of the exact original conclusion agree. -/
theorem nat_and_real_density_forms_equivalent :
    (∀ A : Nat, 1 ≤ A →
      PositiveLowerDensity (fun N => Represented N ∧ A * N < f N)) ↔
    (∀ A : ℝ, 1 ≤ A →
      PositiveLowerDensity
        (fun N => Represented N ∧ A * (N : ℝ) < (f N : ℝ))) :=
  ⟨real_thresholds_of_nat_thresholds, nat_thresholds_of_real_thresholds⟩

/-- The exact comparator main theorem, conditional solely on published Goldbach. -/
theorem erdos1054_main_of_goldbach
    (hGoldbach : DensityZero notSumOfTwoPrimes)
    (A : Nat) (hA : 1 ≤ A) :
    PositiveLowerDensity (fun N => Represented N ∧ A * N < f N) := by
  have hAreal : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  obtain ⟨c, hc0, hc⟩ :=
    _root_.Represented.main (goldbach_of_matching_density hGoldbach) A hAreal
  apply lowerDensity_to_positiveLowerDensity
  refine ⟨c, hc0, ?_⟩
  have hpred :
      (fun N => Represented N ∧ A * N < f N) =
        (fun N => N ∈ _root_.Represented.R ∧
          (A : ℝ) * (N : ℝ) < (_root_.Represented.f N : ℝ)) := by
    funext N
    apply propext
    rw [represented_iff_memR]
    constructor
    · rintro ⟨hR, hlt⟩
      refine ⟨hR, ?_⟩
      rw [← f_eq]
      exact_mod_cast hlt
    · rintro ⟨hR, hlt⟩
      refine ⟨hR, ?_⟩
      rw [f_eq]
      exact_mod_cast hlt
  rw [hpred]
  exact hc

/-- The paper's real-threshold formulation follows without any new input. -/
theorem erdos1054_main_real_of_goldbach
    (hGoldbach : DensityZero notSumOfTwoPrimes)
    (A : ℝ) (hA : 1 ≤ A) :
    PositiveLowerDensity
      (fun N => Represented N ∧ A * (N : ℝ) < (f N : ℝ)) :=
  real_thresholds_of_nat_thresholds
    (erdos1054_main_of_goldbach hGoldbach) A hA

/-- The exact natural-threshold comparator corollary. -/
theorem erdos1054_ratio_unbounded_of_goldbach
    (hGoldbach : DensityZero notSumOfTwoPrimes)
    (A : Nat) (hA : 1 ≤ A) :
    ∃ N, Represented N ∧ A * N < f N := by
  obtain ⟨N, hNR, hratio⟩ :=
    _root_.Represented.ratio_unbounded
      (goldbach_of_matching_density hGoldbach) (A : ℝ)
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hNne : N ≠ 0 := by
    intro hzero
    subst N
    norm_num at hratio
    exact (not_lt_of_ge hApos.le) hratio
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hNne
  have hmul := (lt_div_iff₀ hNpos).mp hratio
  refine ⟨N, (represented_iff_memR N).mpr hNR, ?_⟩
  rw [f_eq]
  exact_mod_cast hmul

/-- A predicate of positive lower density occurs arbitrarily far out. -/
theorem positiveLowerDensity_frequently {P : Nat → Prop}
    (hP : PositiveLowerDensity P) : ∃ᶠ N : Nat in atTop, P N := by
  classical
  rw [frequently_atTop]
  intro B
  obtain ⟨c, hc, X₀, hX₀⟩ := hP
  obtain ⟨Y, hY⟩ := exists_nat_gt ((B : ℚ) / c)
  let X := max X₀ Y
  have hX : X₀ ≤ X := le_max_left X₀ Y
  have hYX : Y ≤ X := le_max_right X₀ Y
  have hcY : (B : ℚ) < c * (Y : ℚ) := by
    have hdiv := (div_lt_iff₀ hc).mp hY
    nlinarith
  have hcX : (B : ℚ) < c * (X : ℚ) := by
    refine hcY.trans_le (mul_le_mul_of_nonneg_left ?_ hc.le)
    exact_mod_cast hYX
  by_contra hnone
  have hsmall : ∀ N, P N → N < B := by
    intro N hN
    by_contra hNB
    exact hnone ⟨N, Nat.le_of_not_gt hNB, hN⟩
  have hsubset :
      ((Finset.range (X + 1)).filter P) ⊆ Finset.range B := by
    intro N hN
    exact Finset.mem_range.mpr
      (hsmall N (Finset.mem_filter.mp hN).2)
  have hcard : countUpTo P X ≤ B := by
    change ((Finset.range (X + 1)).filter P).card ≤ B
    simpa using Finset.card_le_card hsubset
  have hcardQ : (countUpTo P X : ℚ) ≤ (B : ℚ) := by
    exact_mod_cast hcard
  exact (not_le_of_gt hcX) ((hX₀ X hX).trans hcardQ)

/-- Every comparator threshold is exceeded by arbitrarily late represented integers. -/
theorem erdos1054_frequently_above_of_goldbach
    (hGoldbach : DensityZero notSumOfTwoPrimes)
    (A : Nat) (hA : 1 ≤ A) :
    ∃ᶠ N : Nat in atTop, Represented N ∧ A * N < f N :=
  positiveLowerDensity_frequently
    (erdos1054_main_of_goldbach hGoldbach A hA)

/-- Explicit nonvacuous arbitrary-cutoff form of the unbounded-ratio theorem. -/
theorem erdos1054_late_witness_of_goldbach
    (hGoldbach : DensityZero notSumOfTwoPrimes)
    (A B : Nat) (hA : 1 ≤ A) :
    ∃ N, B ≤ N ∧ Represented N ∧ A * N < f N := by
  obtain ⟨N, hBN, hN⟩ :=
    frequently_atTop.mp
      (erdos1054_frequently_above_of_goldbach hGoldbach A hA) B
  exact ⟨N, hBN, hN⟩

/-- Represented integers are strictly positive, including at all cutoff points. -/
theorem represented_pos {N : Nat} (hN : Represented N) : 0 < N := by
  obtain ⟨e, d, he, hd, hNeq⟩ := hN
  rw [hNeq, F]
  have hdmem : d ∈ (e * d).divisors.filter (· ≤ d) := by
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨dvd_mul_left d e, (Nat.mul_pos he hd).ne'⟩, le_rfl⟩
  exact lt_of_lt_of_le hd
    (Finset.single_le_sum (fun i _ => Nat.zero_le i) hdmem)

/-- Exact `EReal`-valued limsup conclusion used by the official formal statement. -/
theorem erdos1054_limsup_top_of_goldbach
    (hGoldbach : DensityZero notSumOfTwoPrimes) :
    atTop.limsup (fun N : Nat => (f N : EReal) / N) = ⊤ := by
  apply top_unique
  apply (le_limsup_iff).2
  intro y hy
  obtain ⟨a, hya, _⟩ := EReal.exists_between_coe_real hy
  let A : ℝ := max a 1
  have haA : a ≤ A := le_max_left a 1
  have hA : 1 ≤ A := le_max_right a 1
  have hfreq :
      ∃ᶠ N : Nat in atTop,
        Represented N ∧ A * (N : ℝ) < (f N : ℝ) :=
    positiveLowerDensity_frequently
      (erdos1054_main_real_of_goldbach hGoldbach A hA)
  refine hfreq.mono (fun N hN => ?_)
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast represented_pos hN.1
  have hratio : A < (f N : ℝ) / (N : ℝ) :=
    (lt_div_iff₀ hNpos).mpr hN.2
  have ha_ratio : a < (f N : ℝ) / (N : ℝ) := haA.trans_lt hratio
  calc
    y < (a : EReal) := hya
    _ < (((f N : ℝ) / (N : ℝ) : ℝ) : EReal) :=
      EReal.coe_lt_coe_iff.mpr ha_ratio
    _ = (f N : EReal) / N := by
      rw [EReal.coe_div]
      rfl

/-- Exact natural-number specialization of the official `Set.HasDensity 1`.

The formal-conjectures source abbreviates its density by intersecting twice
with `Set.univ`; those intersections simplify to this same formula. Keeping
the clean specialization here avoids importing that source's unrelated
`proof_wanted` declarations or its incompatible historical Lean toolchain.
-/
def HasDensityOne (S : Set Nat) : Prop :=
  Tendsto (fun b : Nat => ((S ∩ Set.Iio b).ncard : ℝ) / (b : ℝ))
    atTop (𝓝 1)

/-- A density-one subset cannot be empty, so its subtype order is inhabited. -/
theorem densityOne_nonempty {S : Set Nat} (hS : HasDensityOne S) :
    S.Nonempty := by
  by_contra hnone
  have hempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hnone
  subst S
  have hzero : Tendsto (fun _ : Nat => (0 : ℝ)) atTop (𝓝 1) := by
    simp [HasDensityOne] at hS
  have hcontra : (0 : ℝ) = 1 :=
    tendsto_nhds_unique tendsto_const_nhds hzero
  norm_num at hcontra

/-- Exact partition of a half-open natural interval into a set and its complement. -/
theorem complement_interval_card (S : Set Nat) (b : Nat) :
    (S ∩ Set.Iio b).ncard + (Sᶜ ∩ Set.Iio b).ncard = b := by
  have hpart := Set.ncard_inter_add_ncard_sdiff_eq_ncard
    (Set.Iio b) S (Set.finite_Iio b)
  have hdiff : Set.Iio b \ S = Sᶜ ∩ Set.Iio b := by
    ext n
    simp [and_comm]
  rw [hdiff, Set.ncard_Iio_nat, Set.inter_comm (Set.Iio b) S] at hpart
  exact hpart

/-- The closed-interval count used by the checked reduction is a shifted
half-open complement count. -/
theorem countUpTo_complement_eq (S : Set Nat) (X : Nat) :
    _root_.Represented.countUpTo (fun n => n ∉ S) X =
      (Sᶜ ∩ Set.Iio (X + 1)).ncard := by
  unfold _root_.Represented.countUpTo _root_.Represented.setUpTo
  congr 1
  ext n
  simp [and_comm]

/-- Density one implies that the complement has zero half-open density. -/
theorem densityOne_complement_tendsto {S : Set Nat}
    (hS : HasDensityOne S) :
    Tendsto
      (fun b : Nat => ((Sᶜ ∩ Set.Iio b).ncard : ℝ) / (b : ℝ))
      atTop (𝓝 0) := by
  have hsub : Tendsto
      (fun b : Nat => 1 - ((S ∩ Set.Iio b).ncard : ℝ) / (b : ℝ))
      atTop (𝓝 0) := by
    have hone : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) :=
      tendsto_const_nhds
    simpa using hone.sub hS
  refine hsub.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with b hb
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hpart :
      ((S ∩ Set.Iio b).ncard : ℝ) +
          ((Sᶜ ∩ Set.Iio b).ncard : ℝ) = (b : ℝ) := by
    exact_mod_cast complement_interval_card S b
  field_simp
  linarith

/-- The shifted normalization `(X+1)/X` tends to one. -/
theorem shifted_nat_ratio_tendsto_one :
    Tendsto (fun X : Nat => ((X + 1 : Nat) : ℝ) / (X : ℝ))
      atTop (𝓝 1) := by
  have hbase : Tendsto
      (fun X : Nat => (1 : ℝ) + 1 / (X : ℝ)) atTop (𝓝 1) := by
    simpa using
      (tendsto_const_nhds.add
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)))
  refine hbase.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with X hX
  have hXR : (X : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hX)
  push_cast
  field_simp

/-- Exact conversion of official density one into the supported `o(X)`
complement hypothesis, including the `Iio`/closed-count endpoint shift. -/
theorem densityOne_complement_littleO {S : Set Nat}
    (hS : HasDensityOne S) :
    _root_.Represented.CountIsLittleO (fun n => n ∉ S) := by
  have hshift : Tendsto
      (fun X : Nat =>
        ((Sᶜ ∩ Set.Iio (X + 1)).ncard : ℝ) / ((X + 1 : Nat) : ℝ))
      atTop (𝓝 0) :=
    (densityOne_complement_tendsto hS).comp (tendsto_add_atTop_nat 1)
  have hprod : Tendsto
      (fun X : Nat =>
        (((Sᶜ ∩ Set.Iio (X + 1)).ncard : ℝ) / ((X + 1 : Nat) : ℝ)) *
          (((X + 1 : Nat) : ℝ) / (X : ℝ)))
      atTop (𝓝 0) := by
    simpa using hshift.mul shifted_nat_ratio_tendsto_one
  have hratio : Tendsto
      (fun X : Nat =>
        (_root_.Represented.countUpTo (fun n => n ∉ S) X : ℝ) / (X : ℝ))
      atTop (𝓝 0) := by
    refine hprod.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with X hX
    rw [countUpTo_complement_eq]
    have hXp : ((X + 1 : Nat) : ℝ) ≠ 0 := by positivity
    field_simp
  rw [_root_.Represented.CountIsLittleO]
  refine (isLittleO_iff_tendsto' ?_).mpr hratio
  filter_upwards [eventually_gt_atTop 0] with X hX
  intro hzero
  have hpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  exact (hpos.ne' hzero).elim

/-- The clean specialization agrees exactly with the official partial-density
formula, including the zero-denominator endpoint `b = 0`. -/
theorem hasDensityOne_iff_official_formula (S : Set Nat) :
    HasDensityOne S ↔
      Tendsto
        (fun b : Nat =>
          ((((S ∩ Set.univ) ∩ Set.Iio b).ncard : ℝ) /
            ((Set.univ ∩ Set.Iio b).ncard : ℝ)))
        atTop (𝓝 1) := by
  simp [HasDensityOne, Set.ncard_Iio_nat]

/-- The full natural-number set has density one, as in the official source. -/
theorem hasDensityOne_univ : HasDensityOne (Set.univ : Set Nat) := by
  unfold HasDensityOne
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with b hb
  simp [Nat.ne_of_gt hb]

/-- Exact answer NO to the almost-everywhere official Erdős #1054 question.

The quantifier is over an actual density-one subset, and its little-o filter is
the order filter on the corresponding subtype, precisely as in the official
formal statement. The sole theorem parameter remains almost-all Goldbach.
-/
theorem erdos1054_not_almost_everywhere_littleO_of_goldbach
    (hGoldbach : DensityZero notSumOfTwoPrimes) :
    ¬ ∃ S : Set Nat, HasDensityOne S ∧
      (fun n : S => (f (n : Nat) : ℝ)) =o[atTop]
        (fun n : S => ((n : Nat) : ℝ)) := by
  classical
  rintro ⟨S, hS, hsmall⟩
  obtain ⟨a, ha⟩ := densityOne_nonempty hS
  let : Nonempty S := ⟨⟨a, ha⟩⟩
  obtain ⟨c, hc, hbad⟩ :=
    _root_.Represented.main (goldbach_of_matching_density hGoldbach)
      (1 : ℝ) (by norm_num)
  have hremaining :
      c ≤ _root_.Represented.lowerDensity
        (fun n =>
          (n ∈ _root_.Represented.R ∧
            ((1 : ℝ) * (n : ℝ) < (_root_.Represented.f n : ℝ))) ∧
              ¬ n ∉ S) :=
    _root_.Represented.lowerDensity_and_not hbad
      (densityOne_complement_littleO hS)
  have hfrequent :
      ∃ᶠ n : Nat in atTop,
        (n ∈ _root_.Represented.R ∧
          ((1 : ℝ) * (n : ℝ) < (_root_.Represented.f n : ℝ))) ∧
            ¬ n ∉ S :=
    positiveLowerDensity_frequently
      (lowerDensity_to_positiveLowerDensity _ ⟨c, hc, hremaining⟩)
  have hevent :
      ∀ᶠ n : S in atTop,
        ‖(f (n : Nat) : ℝ)‖ ≤ (1 : ℝ) * ‖((n : Nat) : ℝ)‖ :=
    (isLittleO_iff.mp hsmall) (by norm_num)
  rw [eventually_atTop] at hevent
  obtain ⟨a₀, hbound⟩ := hevent
  obtain ⟨N, hNa, hN⟩ := frequently_atTop.mp hfrequent (a₀ : Nat)
  have hNS : N ∈ S := Classical.byContradiction hN.2
  let nS : S := ⟨N, hNS⟩
  have hage : a₀ ≤ nS := hNa
  have hupper := hbound nS hage
  have hupper' : (f N : ℝ) ≤ (N : ℝ) := by
    change ‖(f N : ℝ)‖ ≤ (1 : ℝ) * ‖(N : ℝ)‖ at hupper
    rw [Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (by positivity), one_mul] at hupper
    exact hupper
  have hlower : (N : ℝ) < (f N : ℝ) := by
    rw [f_eq]
    simpa only [one_mul] using hN.1.2
  exact (not_le_of_gt hlower) hupper'

/-- Exact shape of the official third question, whose existential density-one
set does not occur in the `EReal` limsup expression. -/
theorem erdos1054_limsup_exists_density_one_of_goldbach
    (hGoldbach : DensityZero notSumOfTwoPrimes) :
    ∃ S : Set Nat, HasDensityOne S ∧
      atTop.limsup (fun n : Nat => (f n : EReal) / n) = ⊤ :=
  ⟨Set.univ, hasDensityOne_univ, erdos1054_limsup_top_of_goldbach hGoldbach⟩

end Erdos1054
