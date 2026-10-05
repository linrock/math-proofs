module

public import SecondMoment1054

@[expose] public section


/-!
# Divisor-sum small-ratio witnesses and two-way aliquot range equivalence

This module formalizes two complementary results for Erdős problem #1054:

1. **Small-ratio witness family (`f(σ(n)) ≤ n` and zero liminf on represented integers)**:
   - Every positive divisor-sum value `σ(n) = F(1, n)` (`n ≥ 1`) belongs to `R`
     (`sigma_mem_R`), and the official zero-padded minimizer satisfies
     `0 < f(σ(n)) ≤ n` (`official_f_sigma_le`).
   - Multiplying by `k ≥ 1` preserves or increases the abundancy index `σ(m)/m`
     (`sigma_mul_ge`), and `σ(m)/m` is unbounded (`sigma_ratio_unbounded`).
   - Consequently, for every `ε > 0` and `B`, there exists `N ≥ B` with `0 < f(N)`
     and `f(N) < ε * N` (`frequently_represented_small_ratio`).

2. **Two-way asymptotic density equivalence between `R_2` and `E_s`**:
   - Let `IsCofactorTwoValue N` (`N ∈ R_2`) be `∃ d > 0, N = s(2d)`, and
     `IsEvenAliquotValue N` (`N ∈ E_s`) be `Even N ∧ ∃ m > 0, N = s(m)`.
   - Both set differences `R_2 \ E_s` (`cofactorTwo_diff_evenAliquot_littleO`) and
     `E_s \ R_2` (`evenAliquot_diff_cofactorTwo_littleO`) have natural density zero (`o(X)`).
   - Therefore `R_2` and `E_s` have identical lower asymptotic density
     (`cofactorTwo_lowerDensity_eq_evenAliquot`) and identical upper asymptotic density
     (`cofactorTwo_upperDensity_eq_evenAliquot`).
-/

open Finset Filter Asymptotics
open scoped Topology BigOperators ArithmeticFunction

namespace Erdos1054.AliquotEquivalence

/-! ## Part 1: `f(σ(n)) ≤ n` and Unconditional Small-Ratio Represented Witnesses -/

/-- Every positive divisor-sum value `σ(n)` is represented (`σ(n) = F(1, n) ∈ R`). -/
theorem sigma_mem_R (n : ℕ) (hn : 1 ≤ n) :
    ArithmeticFunction.sigma 1 n ∈ _root_.Represented.R := by
  rw [_root_.Represented.mem_R_iff_exists_F]
  exact ⟨1, n, le_rfl, hn, (_root_.Represented.F_one_eq_sigma n).symm⟩

/-- On every positive divisor-sum value `σ(n)`, the official zero-padded minimizer
`f(σ(n))` is strictly positive and at most `n`. -/
theorem official_f_sigma_le (n : ℕ) (hn : 1 ≤ n) :
    0 < _root_.Erdos1054.OriginalNth.f (ArithmeticFunction.sigma 1 n) ∧
      _root_.Erdos1054.OriginalNth.f (ArithmeticFunction.sigma 1 n) ≤ n := by
  refine ⟨(_root_.Erdos1054.StatementAudit.official_f_pos_iff_represented _).mpr
    (sigma_mem_R n hn), ?_⟩
  rw [_root_.Erdos1054.OriginalNth.f_eq_supported, _root_.Represented.f]
  calc sInf {m | 1 ≤ m ∧ _root_.Represented.IsRep (ArithmeticFunction.sigma 1 n) m}
      ≤ 1 * n := by
        apply Nat.sInf_le
        rw [_root_.Represented.f_set_eq]
        exact ⟨1, n, le_rfl, hn, rfl, (_root_.Represented.F_one_eq_sigma n).symm⟩
    _ = n := one_mul n

/-- Multiplying the argument by `k ≥ 1` scales `σ(m)` by at least `k`. -/
theorem mul_sigma_le_sigma_mul (m k : ℕ) (hk : 1 ≤ k) :
    k * ArithmeticFunction.sigma 1 m ≤ ArithmeticFunction.sigma 1 (k * m) := by
  classical
  have hinj : Function.Injective (fun d : ℕ => k * d) :=
    mul_right_injective₀ (by omega)
  have hsub : m.divisors.image (fun d => k * d) ⊆ (k * m).divisors := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    rw [Nat.mem_divisors] at hd ⊢
    exact ⟨mul_dvd_mul_left k hd.1, mul_ne_zero (by omega) hd.2⟩
  calc k * ArithmeticFunction.sigma 1 m
      = ∑ d ∈ m.divisors, k * d := by
        rw [ArithmeticFunction.sigma_one_apply, Finset.mul_sum]
    _ = ∑ x ∈ m.divisors.image (fun d => k * d), x := by
        rw [Finset.sum_image (fun a _ b _ hab => hinj hab)]
    _ ≤ ∑ x ∈ (k * m).divisors, x :=
        Finset.sum_le_sum_of_subset hsub
    _ = ArithmeticFunction.sigma 1 (k * m) := by
        rw [ArithmeticFunction.sigma_one_apply]

/-- The abundancy index `σ(m)/m` is nondecreasing under multiplication by any `k ≥ 1`. -/
theorem sigma_mul_ge (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) :
    (ArithmeticFunction.sigma 1 m : ℝ) / m ≤
      (ArithmeticFunction.sigma 1 (k * m) : ℝ) / (k * m) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hle : (k : ℝ) * (ArithmeticFunction.sigma 1 m : ℝ) ≤
      (ArithmeticFunction.sigma 1 (k * m) : ℝ) := by
    exact_mod_cast mul_sigma_le_sigma_mul m k hk
  rw [div_le_div_iff₀ hmpos (mul_pos hkpos hmpos)]
  nlinarith [hle, hmpos]

lemma one_add_sum_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    1 + ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 + f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have ha0 : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hs0 : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hih := ih hs0
    have hsum0 : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg hs0
    nlinarith

lemma sigma_prod_primes {ι : Type*} (s : Finset ι) (g : ι → ℕ)
    (hg : ∀ i ∈ s, (g i).Prime) (hinj : Set.InjOn g s) :
    ArithmeticFunction.sigma 1 (∏ i ∈ s, g i) = ∏ i ∈ s, (g i + 1) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hga : (g a).Prime := hg a (Finset.mem_insert_self a s)
    have hgs : ∀ i ∈ s, (g i).Prime := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hinjs : Set.InjOn g s := hinj.mono (Finset.subset_insert a s)
    have hcop : Nat.Coprime (g a) (∏ i ∈ s, g i) := by
      refine Nat.Coprime.prod_right (fun i hi => ?_)
      rw [hga.coprime_iff_not_dvd]
      intro hdvd
      have hgi : (g i).Prime := hgs i hi
      have heq : g a = g i := ((Nat.dvd_prime hgi).mp hdvd).resolve_left hga.ne_one
      have hai : a = i := hinj (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi) heq
      exact ha (hai ▸ hi)
    have hsa : ArithmeticFunction.sigma 1 (g a) = g a + 1 := by
      rw [ArithmeticFunction.sigma_one_apply, Nat.Prime.divisors hga,
        Finset.sum_pair hga.one_lt.ne]
      omega
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hsa, ih hgs hinjs]

/-- The abundancy ratio `σ(m)/m` is unbounded on positive integers `m`. -/
theorem sigma_ratio_unbounded (M : ℝ) :
    ∃ m : ℕ, 1 ≤ m ∧ M * (m : ℝ) < (ArithmeticFunction.sigma 1 m : ℝ) := by
  classical
  let P := {p : ℕ // p.Prime ∧ (p : ZMod 2) = -1}
  have hdiv : ¬ Summable (fun p : P => (1 : ℝ) / (p : ℕ)) :=
    _root_.Represented.primes_neg_one_div_diverges 2 Nat.prime_two (by decide)
  have hnonneg : ∀ p : P, 0 ≤ (1 : ℝ) / (p : ℕ) := fun _ => by positivity
  obtain ⟨s, hs⟩ : ∃ s : Finset P, M < ∑ p ∈ s, (1 : ℝ) / (p : ℕ) := by
    by_contra! hcon
    exact hdiv (summable_of_sum_le hnonneg hcon)
  let m : ℕ := ∏ p ∈ s, (p : ℕ)
  have hmpos : 0 < m := Finset.prod_pos (fun p _ => p.2.1.pos)
  have hmposR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hinj : Set.InjOn (fun p : P => (p : ℕ)) s := fun a _ b _ hab => Subtype.ext hab
  have hsigma : ArithmeticFunction.sigma 1 m = ∏ p ∈ s, ((p : ℕ) + 1) :=
    sigma_prod_primes s (fun p : P => (p : ℕ)) (fun p _ => p.2.1) hinj
  have hprod_eq : (ArithmeticFunction.sigma 1 m : ℝ) / (m : ℝ) =
      ∏ p ∈ s, (1 + (1 : ℝ) / (p : ℕ)) := by
    rw [hsigma]
    have hmcast : (m : ℝ) = ∏ p ∈ s, ((p : ℕ) : ℝ) := by simp [m]
    rw [hmcast, Nat.cast_prod, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl (fun p _ => ?_)
    have hp0 : ((p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast p.2.1.ne_zero
    push_cast
    rw [add_div, div_self hp0]
  have hle : 1 + ∑ p ∈ s, (1 : ℝ) / (p : ℕ) ≤
      (ArithmeticFunction.sigma 1 m : ℝ) / (m : ℝ) := by
    rw [hprod_eq]
    exact one_add_sum_le_prod s (fun p : P => (1 : ℝ) / (p : ℕ)) (fun p _ => hnonneg p)
  have hgt : M < (ArithmeticFunction.sigma 1 m : ℝ) / (m : ℝ) := by linarith [hs, hle]
  refine ⟨m, hmpos, ?_⟩
  exact (lt_div_iff₀ hmposR).mp hgt

/-- For every `ε > 0` and `B`, there exists a genuinely represented integer `N ≥ B`
(`0 < f(N)`) with `f(N) < ε * N`. -/
theorem frequently_represented_small_ratio (ε : ℝ) (hε : 0 < ε) (B : ℕ) :
    ∃ N : ℕ, B ≤ N ∧ 0 < _root_.Erdos1054.OriginalNth.f N ∧
      (_root_.Erdos1054.OriginalNth.f N : ℝ) < ε * (N : ℝ) := by
  obtain ⟨m, hm1, hmgt⟩ := sigma_ratio_unbounded (1 / ε)
  set k : ℕ := max B 1
  have hk1 : 1 ≤ k := le_max_right B 1
  have hkB : B ≤ k := le_max_left B 1
  have hkm1 : 1 ≤ k * m := Nat.mul_pos hk1 hm1
  set N : ℕ := ArithmeticFunction.sigma 1 (k * m) with hNdef
  have hkm_le_N : k * m ≤ N := by
    have hmem : k * m ∈ (k * m).divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩
    calc k * m = ∑ x ∈ ({k * m} : Finset ℕ), x := by simp
      _ ≤ ∑ x ∈ (k * m).divisors, x := Finset.sum_le_sum_of_subset (by simp [hmem])
      _ = N := by rw [hNdef, ArithmeticFunction.sigma_one_apply]
  have hBN : B ≤ N := by
    calc B ≤ k := hkB
      _ ≤ k * m := Nat.le_mul_of_pos_right k hm1
      _ ≤ N := hkm_le_N
  obtain ⟨hfpos, hfle⟩ := official_f_sigma_le (k * m) hkm1
  rw [← hNdef] at hfpos hfle
  refine ⟨N, hBN, hfpos, ?_⟩
  have hfleR : (_root_.Erdos1054.OriginalNth.f N : ℝ) ≤ ((k * m : ℕ) : ℝ) := by
    exact_mod_cast hfle
  have hmul_sigma : k * ArithmeticFunction.sigma 1 m ≤ N := by
    rw [hNdef]
    exact mul_sigma_le_sigma_mul m k hk1
  have hmul_sigmaR : (k : ℝ) * (ArithmeticFunction.sigma 1 m : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hmul_sigma
  have h1 : (1 / ε) * (k : ℝ) * (m : ℝ) < (k : ℝ) * (ArithmeticFunction.sigma 1 m : ℝ) := by
    have hkposR : (0 : ℝ) < k := by exact_mod_cast hk1
    nlinarith [hmgt, hkposR]
  have h2 : (1 / ε) * ((k : ℝ) * (m : ℝ)) < (N : ℝ) := by linarith [h1, hmul_sigmaR]
  have h3 : (k : ℝ) * (m : ℝ) < ε * (N : ℝ) := by
    have := mul_lt_mul_of_pos_left h2 hε
    have hε0 : ε ≠ 0 := hε.ne'
    calc (k : ℝ) * (m : ℝ) = (ε * (1 / ε)) * ((k : ℝ) * (m : ℝ)) := by
          rw [mul_one_div_cancel hε0, one_mul]
      _ = ε * ((1 / ε) * ((k : ℝ) * (m : ℝ))) := by ring
      _ < ε * (N : ℝ) := this
  calc (_root_.Erdos1054.OriginalNth.f N : ℝ)
      ≤ ((k * m : ℕ) : ℝ) := hfleR
    _ = (k : ℝ) * (m : ℝ) := by push_cast; ring
    _ < ε * (N : ℝ) := h3

/-! ## Part 2: Two-Way Aliquot Range Density Equivalence (`R_2` vs `E_s`) -/

/-- `N` is in the cofactor-two divisor-prefix value range `R_2`, i.e., `N = s(2d)` for some `d > 0`. -/
def IsCofactorTwoValue (N : ℕ) : Prop :=
  ∃ d : ℕ, 0 < d ∧ N = _root_.Erdos1054.Aliquot.aliquot (2 * d)

/-- `N` is an even aliquot value (`N ∈ E_s`), i.e., `N` is even and `N = s(m)` for some `m > 0`. -/
def IsEvenAliquotValue (N : ℕ) : Prop :=
  Even N ∧ ∃ m : ℕ, 0 < m ∧ N = _root_.Erdos1054.Aliquot.aliquot m

/-- Forward symmetric-difference direction: `R_2 \ E_s` has natural density zero. -/
theorem cofactorTwo_diff_evenAliquot_littleO :
    _root_.Represented.CountIsLittleO
      (fun N : ℕ => IsCofactorTwoValue N ∧ ¬ IsEvenAliquotValue N) := by
  refine _root_.Represented.CountIsLittleO.mono ?_
    _root_.Erdos1054.CofactorParity.odd_aliquot_value_littleO
  rintro N ⟨⟨d, hd, hN⟩, hnot⟩
  refine ⟨?_, d, hd, hN⟩
  rw [← Nat.not_even_iff_odd]
  intro heven
  exact hnot ⟨heven, 2 * d, by omega, hN⟩

lemma aliquot_one_eq_zero : _root_.Erdos1054.Aliquot.aliquot 1 = 0 := by
  simp [_root_.Erdos1054.Aliquot.aliquot]

lemma aliquot_prime_sq {p : ℕ} (hp : p.Prime) :
    _root_.Erdos1054.Aliquot.aliquot (p ^ 2) = 1 + p := by
  have hsigma : ArithmeticFunction.sigma 1 (p ^ 2) = 1 + p + p ^ 2 := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.divisors_prime_pow hp]
    simp [Finset.sum_range_succ, sq]
  have hsplit := _root_.Erdos1054.CofactorParity.sigma_eq_aliquot_add (p ^ 2)
  omega

lemma composite_sq_le_aliquot_sq {t : ℕ} (ht2 : 2 ≤ t) (hnp : ¬ t.Prime) :
    t ^ 3 ≤ (_root_.Erdos1054.Aliquot.aliquot (t ^ 2)) ^ 2 := by
  set p : ℕ := t.minFac
  have hp_prime : p.Prime := Nat.minFac_prime (by omega)
  have hp_pos : 0 < p := hp_prime.pos
  have hp_dvd : p ∣ t := Nat.minFac_dvd t
  have hp_sq : p ^ 2 ≤ t := Nat.minFac_sq_le_self (by omega) hnp
  set d : ℕ := t * (t / p)
  have hd_mul : d * p = t ^ 2 := by
    dsimp [d]
    rw [mul_assoc, Nat.div_mul_cancel hp_dvd, sq]
  have hd_dvd : d ∣ t ^ 2 := ⟨p, by rw [← hd_mul, mul_comm]⟩
  have hd_lt : d < t ^ 2 := by
    have hp2 : 2 ≤ p := hp_prime.two_le
    have hd_pos : 0 < d := by
      have htp_pos : 0 < t / p := Nat.div_pos (Nat.le_of_dvd (by omega) hp_dvd) hp_pos
      exact Nat.mul_pos (by omega) htp_pos
    nlinarith [hd_mul, hp2, hd_pos]
  have hd_mem : d ∈ (t ^ 2).properDivisors :=
    Nat.mem_properDivisors.mpr ⟨hd_dvd, hd_lt⟩
  have hd_le_aliquot : d ≤ _root_.Erdos1054.Aliquot.aliquot (t ^ 2) :=
    Finset.single_le_sum (fun q _ => Nat.zero_le q) hd_mem
  have ht3_le : t ^ 3 * p ^ 2 ≤ d ^ 2 * p ^ 2 := by
    have hdp : d ^ 2 * p ^ 2 = (d * p) ^ 2 := by ring
    rw [hdp, hd_mul]
    calc t ^ 3 * p ^ 2 ≤ t ^ 3 * t := Nat.mul_le_mul_left (t ^ 3) hp_sq
      _ = (t ^ 2) ^ 2 := by ring
  have ht3_le_d2 : t ^ 3 ≤ d ^ 2 :=
    Nat.le_of_mul_le_mul_right ht3_le (by positivity)
  exact ht3_le_d2.trans (Nat.pow_le_pow_left hd_le_aliquot 2)

lemma countUpTo_zero_littleO :
    _root_.Represented.CountIsLittleO (fun N : ℕ => N = 0) := by
  have hle : ∀ X : ℕ, _root_.Represented.countUpTo (fun N : ℕ => N = 0) X ≤ 1 := by
    intro X
    unfold _root_.Represented.countUpTo
    have hsub : _root_.Represented.setUpTo (fun N : ℕ => N = 0) X ⊆ ({0} : Set ℕ) := by
      rintro n ⟨_, rfl⟩
      simp
    calc (_root_.Represented.setUpTo (fun N : ℕ => N = 0) X).ncard
        ≤ ({0} : Set ℕ).ncard := Set.ncard_le_ncard hsub (Set.finite_singleton 0)
      _ = 1 := Set.ncard_singleton 0
  refine Asymptotics.IsBigO.trans_isLittleO ?_ _root_.Represented.nat_sqrt_isLittleO
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with X hX1
  have hsqrt1 : (1 : ℝ) ≤ (Nat.sqrt X : ℝ) := by
    have : 1 ≤ Nat.sqrt X := Nat.le_sqrt'.mpr (by simpa using hX1)
    exact_mod_cast this
  have hc : (_root_.Represented.countUpTo (fun N : ℕ => N = 0) X : ℝ) ≤ 1 := by
    exact_mod_cast hle X
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul]
  linarith [hc, hsqrt1]

lemma countUpTo_one_add_prime_littleO :
    _root_.Represented.CountIsLittleO (fun N : ℕ => ∃ p : ℕ, p.Prime ∧ N = 1 + p) := by
  have hP : _root_.Represented.CountIsLittleO Nat.Prime := by
    have heq : (fun X : ℕ => (_root_.Represented.countUpTo Nat.Prime X : ℝ)) =
        (fun X : ℕ => (Nat.primeCounting X : ℝ)) := by
      funext X
      rw [_root_.Represented.countUpTo_prime_eq]
    rw [_root_.Represented.CountIsLittleO, heq]
    exact _root_.Represented.primeCounting_isLittleO
  refine _root_.Represented.CountIsLittleO.mono ?_ hP.pred
  rintro N ⟨p, hp, rfl⟩
  simpa using hp

lemma composite_sq_aliquot_count_le (K X : ℕ) (hK : 1 ≤ K) :
    _root_.Represented.countUpTo
        (fun N : ℕ => ∃ t : ℕ, 2 ≤ t ∧ ¬ t.Prime ∧ N = _root_.Erdos1054.Aliquot.aliquot (t ^ 2)) X ≤
      K ^ 2 + (X / K + 1) := by
  have hsub : _root_.Represented.setUpTo
      (fun N : ℕ => ∃ t : ℕ, 2 ≤ t ∧ ¬ t.Prime ∧ N = _root_.Erdos1054.Aliquot.aliquot (t ^ 2)) X ⊆
        ↑((Finset.range (K ^ 2)).image (fun t : ℕ => _root_.Erdos1054.Aliquot.aliquot (t ^ 2)) ∪
          (Finset.range (X / K + 1)).image (fun t : ℕ => _root_.Erdos1054.Aliquot.aliquot (t ^ 2))) := by
    rintro N ⟨hNX, t, ht2, hnp, rfl⟩
    simp only [Finset.coe_union, Finset.coe_image, Finset.coe_range, Set.mem_union,
      Set.mem_image, Set.mem_Iio]
    by_cases htK : t < K ^ 2
    · exact Or.inl ⟨t, htK, rfl⟩
    · push Not at htK
      refine Or.inr ⟨t, ?_, rfl⟩
      have ht3 : t ^ 3 ≤ X ^ 2 :=
        (composite_sq_le_aliquot_sq ht2 hnp).trans (Nat.pow_le_pow_left hNX 2)
      have hKt2 : K ^ 2 * t ^ 2 ≤ X ^ 2 := by
        calc K ^ 2 * t ^ 2 ≤ t * t ^ 2 := Nat.mul_le_mul_right (t ^ 2) htK
          _ = t ^ 3 := by ring
          _ ≤ X ^ 2 := ht3
      have hKt : K * t ≤ X := by
        nlinarith [hKt2]
      have ht_le : t ≤ X / K := (Nat.le_div_iff_mul_le hK).mpr (by linarith [hKt])
      omega
  calc (_root_.Represented.setUpTo
        (fun N : ℕ => ∃ t : ℕ, 2 ≤ t ∧ ¬ t.Prime ∧ N = _root_.Erdos1054.Aliquot.aliquot (t ^ 2)) X).ncard
      ≤ _ := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = _ := Set.ncard_coe_finset _
    _ ≤ K ^ 2 + (X / K + 1) := by
      refine (Finset.card_union_le _ _).trans ?_
      have h1 := Finset.card_image_le (s := Finset.range (K ^ 2))
        (f := fun t : ℕ => _root_.Erdos1054.Aliquot.aliquot (t ^ 2))
      have h2 := Finset.card_image_le (s := Finset.range (X / K + 1))
        (f := fun t : ℕ => _root_.Erdos1054.Aliquot.aliquot (t ^ 2))
      simp only [Finset.card_range] at h1 h2
      omega

lemma composite_sq_aliquot_littleO :
    _root_.Represented.CountIsLittleO
      (fun N : ℕ => ∃ t : ℕ, 2 ≤ t ∧ ¬ t.Prime ∧ N = _root_.Erdos1054.Aliquot.aliquot (t ^ 2)) := by
  rw [_root_.Represented.CountIsLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (2 / ε)
  have hK1 : 1 ≤ K := by
    by_contra! h0
    have hK0 : K = 0 := by omega
    subst hK0
    have : (2 / ε : ℝ) < 0 := by simpa using hK
    linarith [div_pos (by norm_num : (0 : ℝ) < 2) hε]
  have hKposR : (0 : ℝ) < K := by exact_mod_cast hK1
  have hinv : (1 : ℝ) / K < ε / 2 := by
    have h1 : 2 < (K : ℝ) * ε := (div_lt_iff₀ hε).mp hK
    rw [div_lt_iff₀ hKposR]
    linarith
  obtain ⟨X₀, hX₀⟩ := exists_nat_gt ((K ^ 2 + 1 : ℝ) / (ε / 2))
  filter_upwards [eventually_ge_atTop X₀] with X hX
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  have hcount := composite_sq_aliquot_count_le K X hK1
  have hdiv : (X / K : ℕ) * K ≤ X := Nat.div_mul_le_self X K
  have hdivR : ((X / K : ℕ) : ℝ) ≤ (X : ℝ) / K := by
    rw [le_div_iff₀ hKposR]
    exact_mod_cast hdiv
  have hcountR : (_root_.Represented.countUpTo
      (fun N : ℕ => ∃ t : ℕ, 2 ≤ t ∧ ¬ t.Prime ∧ N = _root_.Erdos1054.Aliquot.aliquot (t ^ 2)) X : ℝ) ≤
      (K : ℝ) ^ 2 + (X : ℝ) / K + 1 := by
    have hc : (_root_.Represented.countUpTo
        (fun N : ℕ => ∃ t : ℕ, 2 ≤ t ∧ ¬ t.Prime ∧ N = _root_.Erdos1054.Aliquot.aliquot (t ^ 2)) X : ℝ) ≤
        ((K ^ 2 + (X / K + 1) : ℕ) : ℝ) := by exact_mod_cast hcount
    push_cast at hc
    linarith [hc, hdivR]
  have hXlt : (K ^ 2 + 1 : ℝ) < (ε / 2) * (X : ℝ) := by
    have hX0R : (X₀ : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have h1 : (K ^ 2 + 1 : ℝ) < (X₀ : ℝ) * (ε / 2) :=
      (div_lt_iff₀ (by linarith : (0 : ℝ) < ε / 2)).mp hX₀
    nlinarith
  have hXdiv : (X : ℝ) / K ≤ (ε / 2) * (X : ℝ) := by
    have hXnonneg : (0 : ℝ) ≤ X := by positivity
    calc (X : ℝ) / K = (1 / (K : ℝ)) * (X : ℝ) := by ring
      _ ≤ (ε / 2) * (X : ℝ) := mul_le_mul_of_nonneg_right hinv.le hXnonneg
  linarith [hcountR, hXlt, hXdiv]

/-- Reverse symmetric-difference direction: `E_s \ R_2` has natural density zero. -/
theorem evenAliquot_diff_cofactorTwo_littleO :
    _root_.Represented.CountIsLittleO
      (fun N : ℕ => IsEvenAliquotValue N ∧ ¬ IsCofactorTwoValue N) := by
  refine _root_.Represented.CountIsLittleO.mono ?_
    ((countUpTo_zero_littleO.or countUpTo_one_add_prime_littleO).or composite_sq_aliquot_littleO)
  rintro N ⟨⟨hevenN, m, hmpos, hN⟩, hnot⟩
  have hmodd : Odd m := by
    rw [← Nat.not_even_iff_odd]
    rintro ⟨d, rfl⟩
    have hdpos : 0 < d := by omega
    exact hnot ⟨d, hdpos, by simpa [two_mul] using hN⟩
  have hsigma_odd : Odd (ArithmeticFunction.sigma 1 m) := by
    rw [_root_.Erdos1054.CofactorParity.sigma_eq_aliquot_add, ← hN]
    exact hevenN.add_odd hmodd
  obtain ⟨t, htpos, hmsq | hmtwosq⟩ :=
    (_root_.Erdos1054.CofactorParity.sigma_odd_iff_square_or_twice_square m).mp hsigma_odd
  · rcases eq_or_lt_of_le (show 1 ≤ t by omega) with rfl | ht2
    · refine Or.inl (Or.inl ?_)
      rw [hN, hmsq, one_pow, aliquot_one_eq_zero]
    · by_cases htp : t.Prime
      · refine Or.inl (Or.inr ⟨t, htp, ?_⟩)
        rw [hN, hmsq, aliquot_prime_sq htp]
      · exact Or.inr ⟨t, ht2, htp, by rw [hN, hmsq]⟩
  · exfalso
    have hmeven : Even m := ⟨t ^ 2, by rw [hmtwosq, two_mul]⟩
    exact (Nat.not_even_iff_odd.mpr hmodd) hmeven

lemma lowerDensity_le_of_diff_littleO {P Q : ℕ → Prop}
    (hdiff : _root_.Represented.CountIsLittleO (fun N => P N ∧ ¬ Q N)) :
    _root_.Represented.lowerDensity P ≤ _root_.Represented.lowerDensity Q := by
  have h1 : _root_.Represented.lowerDensity P ≤
      _root_.Represented.lowerDensity (fun N => P N ∧ ¬ (P N ∧ ¬ Q N)) :=
    _root_.Represented.lowerDensity_and_not (le_refl _) hdiff
  refine h1.trans (_root_.Represented.lowerDensity_mono ?_)
  intro n hn
  by_contra hQn
  exact hn.2 ⟨hn.1, hQn⟩

/-- Two-way lower-density equivalence between `R_2` (`IsCofactorTwoValue`)
and `E_s` (`IsEvenAliquotValue`). -/
theorem cofactorTwo_lowerDensity_eq_evenAliquot :
    _root_.Represented.lowerDensity IsCofactorTwoValue =
      _root_.Represented.lowerDensity IsEvenAliquotValue := by
  apply le_antisymm
  · exact lowerDensity_le_of_diff_littleO cofactorTwo_diff_evenAliquot_littleO
  · exact lowerDensity_le_of_diff_littleO evenAliquot_diff_cofactorTwo_littleO

lemma limsup_le_of_diff_littleO {P Q : ℕ → Prop}
    (hdiff : _root_.Represented.CountIsLittleO (fun N => P N ∧ ¬ Q N)) :
    limsup (fun X : ℕ => (_root_.Represented.countUpTo P X : ℝ) / X) atTop ≤
      limsup (fun X : ℕ => (_root_.Represented.countUpTo Q X : ℝ) / X) atTop := by
  let u : ℕ → ℝ := fun X => (_root_.Represented.countUpTo Q X : ℝ) / X
  let v : ℕ → ℝ := fun X => (_root_.Represented.countUpTo (fun N => P N ∧ ¬ Q N) X : ℝ) / X
  let w : ℕ → ℝ := fun X => (_root_.Represented.countUpTo P X : ℝ) / X
  have hvzero : Tendsto v atTop (𝓝 0) := hdiff.tendsto_div
  have huabove : IsBoundedUnder (· ≤ ·) atTop u := by
    refine ⟨2, Filter.eventually_map.2 ?_⟩
    exact Filter.Eventually.of_forall (fun X => _root_.Represented.countUpTo_div_le_two _ X)
  have hubelow : IsBoundedUnder (· ≥ ·) atTop u := by
    refine ⟨0, Filter.eventually_map.2 ?_⟩
    exact Filter.Eventually.of_forall (fun X => by positivity)
  have hvabove : IsBoundedUnder (· ≤ ·) atTop v := by
    refine ⟨2, Filter.eventually_map.2 ?_⟩
    exact Filter.Eventually.of_forall (fun X => _root_.Represented.countUpTo_div_le_two _ X)
  have hvbelow : IsBoundedUnder (· ≥ ·) atTop v := by
    refine ⟨0, Filter.eventually_map.2 ?_⟩
    exact Filter.Eventually.of_forall (fun X => by positivity)
  have hwbelow : IsBoundedUnder (· ≥ ·) atTop w := by
    refine ⟨0, Filter.eventually_map.2 ?_⟩
    exact Filter.Eventually.of_forall (fun X => by positivity)
  have huvabove : IsBoundedUnder (· ≤ ·) atTop (u + v) := by
    refine ⟨4, Filter.eventually_map.2 ?_⟩
    refine Filter.Eventually.of_forall (fun X => ?_)
    have h1 := _root_.Represented.countUpTo_div_le_two Q X
    have h2 := _root_.Represented.countUpTo_div_le_two (fun N => P N ∧ ¬ Q N) X
    change u X + v X ≤ 4
    linarith
  have hw_le_uv : limsup w atTop ≤ limsup (u + v) atTop := by
    apply limsup_le_limsup _ hwbelow.isCoboundedUnder_le huvabove
    filter_upwards [eventually_gt_atTop 0] with X hX
    have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
    have hcount : _root_.Represented.countUpTo P X ≤
        _root_.Represented.countUpTo Q X +
          _root_.Represented.countUpTo (fun N => P N ∧ ¬ Q N) X := by
      have h0 := _root_.Represented.countUpTo_and_not_ge P Q X
      omega
    have hcountR : (_root_.Represented.countUpTo P X : ℝ) ≤
        (_root_.Represented.countUpTo Q X : ℝ) +
          (_root_.Represented.countUpTo (fun N => P N ∧ ¬ Q N) X : ℝ) := by
      exact_mod_cast hcount
    change w X ≤ u X + v X
    dsimp [u, v, w]
    rw [← add_div]
    exact (div_le_div_iff_of_pos_right hXpos).2 hcountR
  have huv_le : limsup (u + v) atTop ≤ limsup u atTop + limsup v atTop :=
    limsup_add_le hubelow huabove hvbelow.isCoboundedUnder_le hvabove
  rw [hvzero.limsup_eq, add_zero] at huv_le
  exact hw_le_uv.trans huv_le

/-- Two-way upper-density equivalence between `R_2` (`IsCofactorTwoValue`)
and `E_s` (`IsEvenAliquotValue`). -/
theorem cofactorTwo_upperDensity_eq_evenAliquot :
    limsup (fun X : ℕ => (_root_.Represented.countUpTo IsCofactorTwoValue X : ℝ) / X) atTop =
      limsup (fun X : ℕ => (_root_.Represented.countUpTo IsEvenAliquotValue X : ℝ) / X) atTop := by
  apply le_antisymm
  · exact limsup_le_of_diff_littleO cofactorTwo_diff_evenAliquot_littleO
  · exact limsup_le_of_diff_littleO evenAliquot_diff_cofactorTwo_littleO

end Erdos1054.AliquotEquivalence
