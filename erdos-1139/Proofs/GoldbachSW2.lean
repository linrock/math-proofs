module

public import GoldbachSW1

@[expose] public section

set_option maxHeartbeats 4000000

/-! ### ================= SiegelTheorem.lean (verbatim, deduplicated) ================= -/

set_option maxHeartbeats 2000000

/-!
# Siegel's theorem for Dirichlet L-functions — brick-by-brick (Goldfeld's route)

Target: `siegel_zero_free`: ∀ ε > 0, ∃ c(ε) > 0, every real zero β of every L(·,χ)
(χ real nontrivial mod q) satisfies β ≤ 1 − c(ε)/q^ε. Ineffective (the dichotomy
case-split is classical); the last missing zero-free input for Siegel–Walfisz and
hence for almost-all binary Goldbach (see the approved roadmap plan).

Phase A of the roadmap; every lemma verified 0-error + `#print axioms`-clean
([propext, Classical.choice, Quot.sound]) before banking.
-/

open PowerSeries ArithmeticFunction Finset Filter

/-- The geometric power series `Σ xⁿ tⁿ` — the local Euler factor `(1 − xt)⁻¹`
    of a completely multiplicative function with `g(p) = x`. -/
noncomputable def geomPS (x : ℝ) : PowerSeries ℝ := PowerSeries.mk (fun n => x ^ n)

lemma coeff_geomPS (x : ℝ) (n : ℕ) : (PowerSeries.coeff (R := ℝ) n) (geomPS x) = x ^ n := by
  rw [geomPS, PowerSeries.coeff_mk]

/-- Products preserve coefficientwise nonnegativity. -/
lemma coeff_mul_nonneg (f g : PowerSeries ℝ)
    (hf : ∀ n, 0 ≤ (PowerSeries.coeff (R := ℝ) n) f) (hg : ∀ n, 0 ≤ (PowerSeries.coeff (R := ℝ) n) g)
    (n : ℕ) : 0 ≤ (PowerSeries.coeff (R := ℝ) n) (f * g) := by
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_nonneg
  intro p _
  exact mul_nonneg (hf p.1) (hg p.2)

/-- `(1−t)⁻¹(1−xt)⁻¹` has nonnegative coefficients for `x ∈ {−1,0,1}`
    (the character-value alphabet): `Σ_{j≤n} xʲ ≥ 0`. -/
lemma coeff_one_mul_geomPS_nonneg (x : ℝ) (hx : x = -1 ∨ x = 0 ∨ x = 1) (n : ℕ) :
    0 ≤ (PowerSeries.coeff (R := ℝ) n) (geomPS 1 * geomPS x) := by
  rw [PowerSeries.coeff_mul]
  have hsum : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      (PowerSeries.coeff (R := ℝ) p.1) (geomPS 1) * (PowerSeries.coeff (R := ℝ) p.2) (geomPS x)
      = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, x ^ p.2 := by
    apply Finset.sum_congr rfl
    intro p _
    rw [coeff_geomPS, coeff_geomPS, one_pow, one_mul]
  rw [hsum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only
  rcases hx with rfl | rfl | rfl
  · -- x = −1: the alternating partial sum is 0 or 1
    have h : ∑ i ∈ Finset.range (n + 1), ((-1:ℝ)) ^ (n - i)
        = ∑ i ∈ Finset.range (n + 1), ((-1:ℝ)) ^ i := by
      have hr := Finset.sum_range_reflect (fun i => ((-1:ℝ)) ^ i) (n + 1)
      simp only [Nat.add_sub_cancel] at hr
      exact hr
    rw [h, neg_one_geom_sum]
    split <;> norm_num
  · -- x = 0: only the i = n term (0^0 = 1) survives
    apply Finset.sum_nonneg
    intro i _
    rcases Nat.eq_zero_or_pos (n - i) with h0 | h0
    · rw [h0]; norm_num
    · rw [zero_pow h0.ne']
  · -- x = 1: n+1 ones
    simp
    positivity

/-- `(1−xt)⁻¹(1+xt)⁻¹ = (1−x²t²)⁻¹` has nonnegative coefficients for EVERY real `x`:
    the coefficient is `xⁿ` times the alternating sum, nonzero only for even `n`. -/
lemma coeff_geomPS_mul_neg_nonneg (x : ℝ) (n : ℕ) :
    0 ≤ (PowerSeries.coeff (R := ℝ) n) (geomPS x * geomPS (-x)) := by
  rw [PowerSeries.coeff_mul]
  have hsum : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      (PowerSeries.coeff (R := ℝ) p.1) (geomPS x) * (PowerSeries.coeff (R := ℝ) p.2) (geomPS (-x))
      = x ^ n * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (-1:ℝ) ^ p.2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [coeff_geomPS, coeff_geomPS, neg_pow]
    have hpn : p.1 + p.2 = n :=
      Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rw [show x ^ p.1 * ((-1:ℝ) ^ p.2 * x ^ p.2) = (-1:ℝ) ^ p.2 * (x ^ p.1 * x ^ p.2) by ring,
      ← pow_add, hpn]
    ring
  rw [hsum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only
  rcases Nat.even_or_odd n with he | ho
  · apply mul_nonneg (he.pow_nonneg x)
    have h : ∑ i ∈ Finset.range (n + 1), ((-1:ℝ)) ^ (n - i)
        = ∑ i ∈ Finset.range (n + 1), ((-1:ℝ)) ^ i := by
      have hr := Finset.sum_range_reflect (fun i => ((-1:ℝ)) ^ i) (n + 1)
      simp only [Nat.add_sub_cancel] at hr
      exact hr
    rw [h, neg_one_geom_sum]
    split <;> norm_num
  · -- odd n: the alternating sum over n+1 (even count) terms vanishes
    have h : ∑ i ∈ Finset.range (n + 1), ((-1:ℝ)) ^ (n - i)
        = ∑ i ∈ Finset.range (n + 1), ((-1:ℝ)) ^ i := by
      have hr := Finset.sum_range_reflect (fun i => ((-1:ℝ)) ^ i) (n + 1)
      simp only [Nat.add_sub_cancel] at hr
      exact hr
    rw [h, neg_one_geom_sum, if_pos ho.add_one, mul_zero]

/-- **The Goldfeld positivity core** (Siegel brick A1a): for character values
    `x, y ∈ {−1,0,1}`, the local factor product
    `(1−t)⁻¹(1−xt)⁻¹(1−yt)⁻¹(1−xyt)⁻¹` of `ζ·L(χ₁)·L(χ₂)·L(χ₁χ₂)` has
    nonnegative power-series coefficients — by pairing the four geometric series
    so each pair is nonneg: `y = 1`: `(1·x)(1·x)`; `y = 0`: the `y`-factors are `1`;
    `y = −1`: `(1·(−1)) ⋆ (x·(−x))`. -/
lemma coeff_euler_quad_nonneg (x y : ℝ) (hx : x = -1 ∨ x = 0 ∨ x = 1)
    (hy : y = -1 ∨ y = 0 ∨ y = 1) (n : ℕ) :
    0 ≤ (PowerSeries.coeff (R := ℝ) n) (geomPS 1 * geomPS x * geomPS y * geomPS (x * y)) := by
  rcases hy with rfl | rfl | rfl
  · -- y = −1: regroup as (1 ⋆ (−1)) * (x ⋆ (−x))
    have hre : geomPS 1 * geomPS x * geomPS (-1) * geomPS (x * -1)
        = (geomPS 1 * geomPS (-1)) * (geomPS x * geomPS (-x)) := by
      rw [show x * (-1:ℝ) = -x by ring]
      ring
    rw [hre]
    apply coeff_mul_nonneg
    · exact coeff_one_mul_geomPS_nonneg (-1) (Or.inl rfl)
    · exact coeff_geomPS_mul_neg_nonneg x
  · -- y = 0: geomPS 0 has coefficients δ₀; the product bound reduces via nonneg factors
    rw [show x * (0:ℝ) = 0 by ring]
    apply coeff_mul_nonneg
    · apply coeff_mul_nonneg
      · exact coeff_one_mul_geomPS_nonneg x hx
      · intro m
        rw [coeff_geomPS]
        rcases Nat.eq_zero_or_pos m with rfl | h0
        · norm_num
        · rw [zero_pow h0.ne']
    · intro m
      rw [coeff_geomPS]
      rcases Nat.eq_zero_or_pos m with rfl | h0
      · norm_num
      · rw [zero_pow h0.ne']
  · -- y = 1: regroup as (1 ⋆ x) * (1 ⋆ x)
    have hre : geomPS 1 * geomPS x * geomPS 1 * geomPS (x * 1)
        = (geomPS 1 * geomPS x) * (geomPS 1 * geomPS x) := by
      rw [mul_one]
      ring
    rw [hre]
    exact coeff_mul_nonneg _ _
      (coeff_one_mul_geomPS_nonneg x hx) (coeff_one_mul_geomPS_nonneg x hx) n

/-- **Dirichlet convolution at prime powers** (Siegel brick A1b-i):
    `(f ⋆ g)(pᵐ) = Σ_{i≤m} f(pⁱ)·g(p^{m−i})` — the divisor pairs of `pᵐ` are exactly
    `(pⁱ, p^{m−i})`. -/
lemma mul_apply_prime_pow (f g : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) (m : ℕ) :
    (f * g) (p ^ m) = ∑ i ∈ Finset.range (m + 1), f (p ^ i) * g (p ^ (m - i)) := by
  rw [ArithmeticFunction.mul_apply]
  have hp0 : p ≠ 0 := hp.ne_zero
  have hp1 : 1 < p := hp.one_lt
  apply Finset.sum_nbij' (fun pr => pr.1.factorization p)
    (fun i => ((p ^ i : ℕ), (p ^ (m - i) : ℕ)))
  · -- membership: divisor pair → range
    intro pr hpr
    rw [Nat.mem_divisorsAntidiagonal] at hpr
    obtain ⟨hmul, _⟩ := hpr
    have hdvd : pr.1 ∣ p ^ m := ⟨pr.2, hmul.symm⟩
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    rw [Finset.mem_range, hk', Nat.factorization_pow_self hp]
    omega
  · -- membership: range → divisor pair
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Nat.mem_divisorsAntidiagonal]
    constructor
    · rw [← pow_add]
      congr 1
      omega
    · positivity
  · -- left inverse
    intro pr hpr
    rw [Nat.mem_divisorsAntidiagonal] at hpr
    obtain ⟨hmul, _⟩ := hpr
    have hdvd : pr.1 ∣ p ^ m := ⟨pr.2, hmul.symm⟩
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hfact : pr.1.factorization p = k := by
      rw [hk', Nat.factorization_pow_self hp]
    rw [hfact]
    have hb : pr.2 = p ^ (m - k) := by
      have h1 : p ^ k * pr.2 = p ^ k * p ^ (m - k) := by
        rw [← pow_add, show k + (m - k) = m by omega, ← hk', hmul]
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
    rw [← hk', ← hb]
  · -- right inverse
    intro i hi
    rw [Nat.factorization_pow_self hp]
  · -- summand match
    intro pr hpr
    rw [Nat.mem_divisorsAntidiagonal] at hpr
    obtain ⟨hmul, _⟩ := hpr
    have hdvd : pr.1 ∣ p ^ m := ⟨pr.2, hmul.symm⟩
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hfact : pr.1.factorization p = k := by
      rw [hk', Nat.factorization_pow_self hp]
    have hb : pr.2 = p ^ (m - k) := by
      have h1 : p ^ k * pr.2 = p ^ k * p ^ (m - k) := by
        rw [← pow_add, show k + (m - k) = m by omega, ← hk', hmul]
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
    rw [hfact, ← hk', hb]

/-- The prime-power fiber of an arithmetic function, as a power series in the exponent. -/
noncomputable def primeFiber (f : ArithmeticFunction ℝ) (p : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk (fun m => f (p ^ m))

lemma coeff_primeFiber (f : ArithmeticFunction ℝ) (p m : ℕ) :
    (PowerSeries.coeff (R := ℝ) m) (primeFiber f p) = f (p ^ m) := by
  rw [primeFiber, PowerSeries.coeff_mk]

/-- **The prime fiber is multiplicative** (Siegel brick A1b-ii): Dirichlet convolution
    restricted to powers of one prime IS power-series multiplication. -/
lemma primeFiber_mul (f g : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) :
    primeFiber (f * g) p = primeFiber f p * primeFiber g p := by
  ext m
  rw [coeff_primeFiber, PowerSeries.coeff_mul, mul_apply_prime_pow f g hp,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro i _
  rw [coeff_primeFiber, coeff_primeFiber]

/-- A bare function packaged as an arithmetic function (forcing the value 0 at 0). -/
noncomputable def toArith (g : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else g n, by simp⟩

lemma toArith_apply (g : ℕ → ℝ) (n : ℕ) (hn : n ≠ 0) : toArith g n = g n := by
  simp [toArith, hn]

/-- Completely multiplicative bare functions give multiplicative arithmetic functions. -/
lemma toArith_isMultiplicative (g : ℕ → ℝ) (hg : ∀ m n, g (m * n) = g m * g n)
    (hg1 : g 1 = 1) : (toArith g).IsMultiplicative := by
  constructor
  · rw [toArith_apply g 1 one_ne_zero, hg1]
  · intro m n _
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [toArith]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [toArith]
    rw [toArith_apply g _ (by positivity), toArith_apply g _ hm.ne',
      toArith_apply g _ hn.ne', hg]

/-- Completely multiplicative functions turn powers into powers. -/
lemma comp_mult_pow (g : ℕ → ℝ) (hg : ∀ m n, g (m * n) = g m * g n) (hg1 : g 1 = 1)
    (a : ℕ) : ∀ m : ℕ, g (a ^ m) = g a ^ m := by
  intro m
  induction m with
  | zero => simpa using hg1
  | succ k ih =>
    rw [pow_succ, hg, ih, pow_succ]

/-- The prime fiber of a packaged completely multiplicative function is the geometric
    series at its prime value. -/
lemma primeFiber_toArith (g : ℕ → ℝ) (hg : ∀ m n, g (m * n) = g m * g n) (hg1 : g 1 = 1)
    {p : ℕ} (hp : p.Prime) : primeFiber (toArith g) p = geomPS (g p) := by
  ext m
  rw [coeff_primeFiber, coeff_geomPS, toArith_apply g _ (pow_ne_zero m hp.ne_zero),
    comp_mult_pow g hg hg1 p m]

/-- **Nonnegativity of the Goldfeld convolution** (Siegel brick A1c): for completely
    multiplicative `g₁, g₂` with values in `{−1,0,1}` (the real-character shape), every
    value of the Dirichlet convolution `1 ⋆ g₁ ⋆ g₂ ⋆ g₁g₂` — the coefficient sequence
    of `ζ(s)L(s,χ₁)L(s,χ₂)L(s,χ₁χ₂)` — is nonnegative, and the value at 1 is 1. -/
theorem quad_conv_nonneg (g₁ g₂ : ℕ → ℝ)
    (h₁ : ∀ m n, g₁ (m * n) = g₁ m * g₁ n) (h₂ : ∀ m n, g₂ (m * n) = g₂ m * g₂ n)
    (h₁1 : g₁ 1 = 1) (h₂1 : g₂ 1 = 1)
    (h₁v : ∀ n, g₁ n = -1 ∨ g₁ n = 0 ∨ g₁ n = 1)
    (h₂v : ∀ n, g₂ n = -1 ∨ g₂ n = 0 ∨ g₂ n = 1) :
    (∀ n, 0 ≤ (toArith (fun _ => 1) * toArith g₁ * toArith g₂
        * toArith (fun k => g₁ k * g₂ k)) n)
    ∧ (toArith (fun _ => 1) * toArith g₁ * toArith g₂
        * toArith (fun k => g₁ k * g₂ k)) 1 = 1 := by
  set A : ArithmeticFunction ℝ := toArith (fun _ => 1) * toArith g₁ * toArith g₂
    * toArith (fun k => g₁ k * g₂ k) with hA
  have hm0 : (toArith (fun _ => (1:ℝ))).IsMultiplicative :=
    toArith_isMultiplicative _ (fun _ _ => (one_mul 1).symm) rfl
  have hm1 : (toArith g₁).IsMultiplicative := toArith_isMultiplicative g₁ h₁ h₁1
  have hm2 : (toArith g₂).IsMultiplicative := toArith_isMultiplicative g₂ h₂ h₂1
  have h12 : ∀ m n, (fun k => g₁ k * g₂ k) (m * n)
      = (fun k => g₁ k * g₂ k) m * (fun k => g₁ k * g₂ k) n := by
    intro m n
    simp only
    rw [h₁, h₂]
    ring
  have h121 : (fun k => g₁ k * g₂ k) 1 = 1 := by
    simp only
    rw [h₁1, h₂1, one_mul]
  have hm3 : (toArith (fun k => g₁ k * g₂ k)).IsMultiplicative :=
    toArith_isMultiplicative _ h12 h121
  have hmA : A.IsMultiplicative := ((hm0.mul hm1).mul hm2).mul hm3
  -- prime-power nonnegativity via the fiber bridge + the A1a positivity core
  have hpp : ∀ p : ℕ, p.Prime → ∀ m : ℕ, 0 ≤ A (p ^ m) := by
    intro p hp m
    have hfib : primeFiber A p
        = geomPS 1 * geomPS (g₁ p) * geomPS (g₂ p) * geomPS (g₁ p * g₂ p) := by
      rw [hA, primeFiber_mul _ _ hp, primeFiber_mul _ _ hp, primeFiber_mul _ _ hp,
        primeFiber_toArith _ (fun _ _ => (one_mul 1).symm) rfl hp,
        primeFiber_toArith g₁ h₁ h₁1 hp, primeFiber_toArith g₂ h₂ h₂1 hp,
        primeFiber_toArith _ h12 h121 hp]
    have := coeff_euler_quad_nonneg (g₁ p) (g₂ p) (h₁v p) (h₂v p) m
    rw [← hfib, coeff_primeFiber] at this
    exact this
  refine ⟨?_, hmA.map_one⟩
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [ArithmeticFunction.map_zero]
  have hfac := hmA.multiplicative_factorization A hn.ne'
  rw [hfac, Finsupp.prod]
  apply Finset.prod_nonneg
  intro p hpmem
  have hp : p.Prime := Nat.prime_of_mem_primeFactors
    (by rwa [Nat.support_factorization] at hpmem)
  exact hpp p hp _

/-- The lattice-point index set of the hyperbola method: pairs `(d,e)` with
    `1 ≤ d, e` and `d·e ≤ N`. -/
def hypSet (N : ℕ) : Finset (ℕ × ℕ) :=
  (Ioc 0 N ×ˢ Ioc 0 N).filter (fun p => p.1 * p.2 ≤ N)

/-- **Convolution partial sums are lattice-point sums** (Siegel brick A2a-i). -/
lemma sum_conv_eq_sum_hypSet (f g : ArithmeticFunction ℝ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, (f * g) n = ∑ p ∈ hypSet N, f p.1 * g p.2 := by
  have hL : ∑ n ∈ Icc 1 N, (f * g) n
      = ∑ n ∈ Icc 1 N, ∑ p ∈ (Ioc 0 N ×ˢ Ioc 0 N).filter (fun x => x.1 * x.2 = n),
          f p.1 * g p.2 := by
    apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    rw [ArithmeticFunction.mul_apply,
      Nat.divisorsAntidiagonal_eq_prod_filter_of_le (by omega) hnN]
  rw [hL, Finset.sum_fiberwise_eq_sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  rw [hypSet]
  apply Finset.filter_congr
  intro p hp
  rw [Finset.mem_product, Finset.mem_Ioc, Finset.mem_Ioc] at hp
  simp only [Finset.mem_Icc]
  constructor
  · intro h
    exact h.2
  · intro h
    refine ⟨?_, h⟩
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos hp.1.1 hp.2.1).ne'

/-- Row fibers of the hyperbola set: for `1 ≤ d`, the `e` with `d·e ≤ N` form `Icc 1 (N/d)`. -/
lemma row_fiber (N d : ℕ) (hd : 0 < d) :
    (Ioc 0 N).filter (fun e => d * e ≤ N) = Icc 1 (N / d) := by
  ext e
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
  constructor
  · intro ⟨⟨he0, _⟩, hde⟩
    refine ⟨he0, (Nat.le_div_iff_mul_le hd).mpr ?_⟩
    rw [Nat.mul_comm]
    exact hde
  · intro ⟨he1, heNd⟩
    have hde : d * e ≤ N := by
      have h := (Nat.le_div_iff_mul_le hd).mp heNd
      rw [Nat.mul_comm e d] at h
      exact h
    have heN : e ≤ N := by
      calc e ≤ d * e := Nat.le_mul_of_pos_left e hd
        _ ≤ N := hde
    exact ⟨⟨by omega, heN⟩, hde⟩

/-- Column fibers above the split: for `1 ≤ e`, the `d > y` with `d·e ≤ N` form
    `Icc (y+1) (N/e)`. -/
lemma col_fiber (N y e : ℕ) (he : 0 < e) :
    (Ioc 0 N).filter (fun d => ¬ d ≤ y ∧ d * e ≤ N) = Icc (y + 1) (N / e) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc, not_le]
  constructor
  · intro ⟨⟨_, _⟩, hyd, hde⟩
    exact ⟨hyd, (Nat.le_div_iff_mul_le he).mpr hde⟩
  · intro ⟨hyd, hdNe⟩
    have hde : d * e ≤ N := (Nat.le_div_iff_mul_le he).mp hdNe
    have hdN : d ≤ N := by
      calc d ≤ d * e := Nat.le_mul_of_pos_right d he
        _ ≤ N := hde
    exact ⟨⟨by omega, hdN⟩, hyd, hde⟩

/-- **The Dirichlet hyperbola identity** (Siegel brick A2a): for any split `y ≤ N`,
    `Σ_{n≤N}(f⋆g)(n) = Σ_{d≤y} f(d)·G(N/d) + Σ_{e≤N/(y+1)} g(e)·(F(N/e) − F(y))` —
    the exact identity behind the coefficient asymptotic `A(x) = λx + O(Q^c x^{4/5})`. -/
theorem hyperbola_identity (f g : ArithmeticFunction ℝ) (N y : ℕ) (hy : y ≤ N) :
    ∑ n ∈ Icc 1 N, (f * g) n
      = ∑ d ∈ Icc 1 y, f d * (∑ e ∈ Icc 1 (N / d), g e)
        + ∑ e ∈ Icc 1 (N / (y + 1)),
            g e * ((∑ d ∈ Icc 1 (N / e), f d) - ∑ d ∈ Icc 1 y, f d) := by
  rw [sum_conv_eq_sum_hypSet, hypSet,
    ← Finset.sum_filter_add_sum_filter_not _ (fun p => p.1 ≤ y)]
  congr 1
  · -- head: rows d ≤ y
    rw [Finset.filter_filter, Finset.sum_filter, Finset.sum_product]
    simp only
    rw [← Finset.sum_filter_add_sum_filter_not (Ioc 0 N) (fun d => d ≤ y)]
    have hz : ∑ d ∈ (Ioc 0 N).filter (fun d => ¬ d ≤ y),
        ∑ e ∈ Ioc 0 N, (if d * e ≤ N ∧ d ≤ y then f d * g e else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      apply Finset.sum_eq_zero
      intro e _
      rw [Finset.mem_filter] at hd
      rw [if_neg]
      intro hcon
      exact hd.2 hcon.2
    rw [hz, add_zero]
    have hIoc : (Ioc 0 N).filter (fun d => d ≤ y) = Icc 1 y := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
      omega
    rw [hIoc]
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hd1, hdy⟩ := Finset.mem_Icc.mp hd
    rw [Finset.mul_sum, ← row_fiber N d (by omega), Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hde : d * e ≤ N
    · rw [if_pos ⟨hde, hdy⟩, if_pos hde]
    · rw [if_neg (fun h => hde h.1), if_neg hde]
  · -- tail: columns, d > y
    rw [Finset.filter_filter, Finset.sum_filter, Finset.sum_product_right]
    simp only
    have hsub : Icc 1 (N / (y + 1)) ⊆ Ioc 0 N := by
      intro e he
      obtain ⟨he1, heN⟩ := Finset.mem_Icc.mp he
      rw [Finset.mem_Ioc]
      have : N / (y + 1) ≤ N := Nat.div_le_self N (y + 1)
      omega
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro e he
      obtain ⟨he1, heNy⟩ := Finset.mem_Icc.mp he
      have hy1e : y + 1 ≤ N / e + 1 := by
        have h1 : e * (y + 1) ≤ N := (Nat.le_div_iff_mul_le (by omega)).mp heNy
        have h2 : y + 1 ≤ N / e := by
          apply (Nat.le_div_iff_mul_le (by omega : 0 < e)).mpr
          rw [Nat.mul_comm]
          exact h1
        omega
      have hIcoIcc : ∀ a b : ℕ, Ico a (b + 1) = Icc a b := by
        intro a b
        ext x
        simp only [Finset.mem_Ico, Finset.mem_Icc]
        omega
      have hdiff : (∑ d ∈ Icc 1 (N / e), f d) - ∑ d ∈ Icc 1 y, f d
          = ∑ d ∈ Icc (y + 1) (N / e), f d := by
        rw [← hIcoIcc 1 (N / e),
          ← Finset.sum_Ico_consecutive (fun d => f d) (by omega : 1 ≤ y + 1) hy1e,
          hIcoIcc 1 y, hIcoIcc (y + 1) (N / e), add_sub_cancel_left]
      rw [hdiff, Finset.mul_sum, ← col_fiber N y e (by omega), Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hcase : d * e ≤ N ∧ ¬ d ≤ y
      · rw [if_pos hcase, if_pos ⟨hcase.2, hcase.1⟩, mul_comm]
      · rw [if_neg hcase, if_neg (fun hcon => hcase ⟨hcon.2, hcon.1⟩)]
    · intro e heIoc heNot
      apply Finset.sum_eq_zero
      intro d _
      rw [if_neg]
      intro ⟨hde, hdy⟩
      apply heNot
      rw [Finset.mem_Icc]
      obtain ⟨he0, _⟩ := Finset.mem_Ioc.mp heIoc
      refine ⟨by omega, ?_⟩
      rw [Nat.le_div_iff_mul_le (by omega : 0 < y + 1)]
      push_neg at hdy
      calc e * (y + 1) ≤ e * d := by
            apply Nat.mul_le_mul_left
            omega
        _ = d * e := Nat.mul_comm e d
        _ ≤ N := hde

/-- **Harmonic partial sums** (Siegel brick A2b-i): `Σ_{c≤z} 1/c ≤ 1 + log z`. -/
lemma sum_one_div_le_log (z : ℕ) (hz : 1 ≤ z) :
    ∑ c ∈ Icc 1 z, (1 : ℝ) / c ≤ 1 + Real.log z := by
  have hh := harmonic_le_one_add_log z
  have hcast : ((harmonic z : ℚ) : ℝ) = ∑ c ∈ Icc 1 z, (1 : ℝ) / c := by
    rw [harmonic,
      show Icc 1 z = Ico 1 (z + 1) from by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega,
      Finset.sum_Ico_eq_sum_range]
    push_cast
    apply Finset.sum_congr (by norm_num)
    intro i _
    push_cast
    ring
  rw [← hcast]
  exact_mod_cast hh

/-- **Square-root reciprocal partial sums** (Siegel brick A2b-ii): `Σ_{e≤z} 1/√e ≤ 2√z` —
    by the telescoping `1/√e ≤ 2(√e − √(e−1))`. -/
lemma sum_one_div_sqrt_le (z : ℕ) :
    ∑ e ∈ Icc 1 z, (1 : ℝ) / Real.sqrt e ≤ 2 * Real.sqrt z := by
  induction z with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hstep : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hstep, Finset.sum_insert (by simp)]
    have hkey : (1 : ℝ) / Real.sqrt (n + 1) ≤ 2 * (Real.sqrt (n + 1) - Real.sqrt n) := by
      have hs1 : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
      have hs0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
      have hprod : (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n)
          * (Real.sqrt ((n : ℝ) + 1) + Real.sqrt n) = 1 := by
        have h1 : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 :=
          Real.sq_sqrt (by positivity)
        have h2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
        nlinarith [h1, h2]
      have hsumle : Real.sqrt ((n : ℝ) + 1) + Real.sqrt n
          ≤ 2 * Real.sqrt ((n : ℝ) + 1) := by
        have := Real.sqrt_le_sqrt (show (n : ℝ) ≤ (n : ℝ) + 1 by linarith)
        linarith
      rw [div_le_iff₀ hs1]
      have hdiffpos : 0 < Real.sqrt ((n : ℝ) + 1) - Real.sqrt n := by
        rcases lt_or_ge (Real.sqrt n) (Real.sqrt ((n:ℝ) + 1)) with h | h
        · linarith
        · exfalso
          nlinarith [hprod]
      nlinarith [hprod, hsumle, hdiffpos, hs1]
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast] at *
    linarith [ih, hkey]

/-- **Row decomposition of hyperbola-set sums** (Siegel brick A2b-iii):
    `Σ_{p ∈ hypSet N} F(p) = Σ_{d≤N} Σ_{e≤N/d} F(d,e)`. -/
lemma sum_hypSet_eq_rows (N : ℕ) (F : ℕ × ℕ → ℝ) :
    ∑ p ∈ (Ioc 0 N ×ˢ Ioc 0 N).filter (fun p => p.1 * p.2 ≤ N), F p
      = ∑ d ∈ Icc 1 N, ∑ e ∈ Icc 1 (N / d), F (d, e) := by
  rw [Finset.sum_filter, Finset.sum_product]
  have hIoc : (Ioc 0 N : Finset ℕ) = Icc 1 N := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hIoc]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
  have hrow : Icc 1 (N / d) = (Icc 1 N).filter (fun e => d * e ≤ N) := by
    ext e
    simp only [Finset.mem_Icc, Finset.mem_filter]
    constructor
    · intro ⟨he1, heNd⟩
      have hde : d * e ≤ N := by
        have h := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp heNd
        rw [Nat.mul_comm e d] at h
        exact h
      have heN : e ≤ N := le_trans (Nat.le_mul_of_pos_left e (by omega)) hde
      exact ⟨⟨he1, heN⟩, hde⟩
    · intro ⟨⟨he1, _⟩, hde⟩
      refine ⟨he1, (Nat.le_div_iff_mul_le (by omega : 0 < d)).mpr ?_⟩
      rw [Nat.mul_comm]
      exact hde
  rw [hrow, Finset.sum_filter]

/-- **The divisor-weighted root sum** (Siegel brick A2b-iv):
    `Σ_{p ∈ hypSet z} 1/√(p₁p₂) ≤ 2√z(1 + log z)` — the error-term workhorse:
    every `Σ_{e≤z} d(e)/√e` style bound routes through this lattice form. -/
lemma sum_hypSet_inv_sqrt_le (z : ℕ) (hz : 1 ≤ z) :
    ∑ p ∈ (Ioc 0 z ×ˢ Ioc 0 z).filter (fun p => p.1 * p.2 ≤ z),
        (1 : ℝ) / Real.sqrt (p.1 * p.2)
      ≤ 2 * Real.sqrt z * (1 + Real.log z) := by
  rw [sum_hypSet_eq_rows]
  have hrow : ∀ d ∈ Icc 1 z, ∑ e ∈ Icc 1 (z / d), (1 : ℝ) / Real.sqrt ((d, e).1 * (d, e).2)
      ≤ (1 / (d : ℝ)) * (2 * Real.sqrt z) := by
    intro d hd
    obtain ⟨hd1, hdz⟩ := Finset.mem_Icc.mp hd
    have hd0 : (0:ℝ) < d := by exact_mod_cast hd1
    have hsplit : ∀ e ∈ Icc 1 (z / d), (1 : ℝ) / Real.sqrt ((d, e).1 * (d, e).2)
        = (1 / Real.sqrt d) * (1 / Real.sqrt e) := by
      intro e he
      obtain ⟨he1, _⟩ := Finset.mem_Icc.mp he
      simp only
      rw [Real.sqrt_mul (Nat.cast_nonneg d)]
      ring
    rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum]
    have hsum := sum_one_div_sqrt_le (z / d)
    have hdivle : Real.sqrt ((z / d : ℕ) : ℝ) ≤ Real.sqrt z / Real.sqrt d := by
      calc Real.sqrt ((z / d : ℕ) : ℝ) ≤ Real.sqrt ((z : ℝ) / d) :=
            Real.sqrt_le_sqrt Nat.cast_div_le
        _ = Real.sqrt z / Real.sqrt d := Real.sqrt_div (Nat.cast_nonneg z) d
    have hsd : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.mpr hd0
    calc (1 / Real.sqrt d) * ∑ e ∈ Icc 1 (z / d), (1:ℝ) / Real.sqrt e
        ≤ (1 / Real.sqrt d) * (2 * Real.sqrt ((z / d : ℕ) : ℝ)) := by
          apply mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ (1 / Real.sqrt d) * (2 * (Real.sqrt z / Real.sqrt d)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [hdivle]
      _ = 2 * Real.sqrt z / (Real.sqrt d * Real.sqrt d) := by ring
      _ = (1 / (d : ℝ)) * (2 * Real.sqrt z) := by
          rw [Real.mul_self_sqrt (Nat.cast_nonneg d)]
          ring
  calc ∑ d ∈ Icc 1 z, ∑ e ∈ Icc 1 (z / d), (1 : ℝ) / Real.sqrt ((d, e).1 * (d, e).2)
      ≤ ∑ d ∈ Icc 1 z, (1 / (d : ℝ)) * (2 * Real.sqrt z) := Finset.sum_le_sum hrow
    _ = (∑ d ∈ Icc 1 z, (1 : ℝ) / d) * (2 * Real.sqrt z) := by
        rw [← Finset.sum_mul]
    _ ≤ (1 + Real.log z) * (2 * Real.sqrt z) := by
        apply mul_le_mul_of_nonneg_right (sum_one_div_le_log z hz) (by positivity)
    _ = 2 * Real.sqrt z * (1 + Real.log z) := by ring

/-- **Abel rearrangement over a tail window** (Siegel brick A2c-i-a): with
    `G t = Σ_{n≤t} g n`, for `y ≤ z`:
    `Σ_{y<d≤z} g(d)/d = Σ_{y<d≤z} G(d)(1/d − 1/(d+1)) + G(z)/(z+1) − G(y)/(y+1)`. -/
lemma abel_window (g : ℕ → ℝ) (y : ℕ) :
    ∀ z : ℕ, y ≤ z →
    ∑ d ∈ Icc (y + 1) z, g d / d
      = ∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1))
        + (∑ n ∈ Icc 1 z, g n) / (z + 1) - (∑ n ∈ Icc 1 y, g n) / (y + 1) := by
  intro z
  induction z with
  | zero =>
    intro hy0
    interval_cases y
    simp
  | succ m ih =>
    intro hym
    rcases Nat.lt_or_ge m y with hlt | hge
    · -- y = m + 1: both windows empty
      have hy : y = m + 1 := by omega
      subst hy
      simp
    · -- extend from m to m+1
      have hstepL : Icc (y + 1) (m + 1) = insert (m + 1) (Icc (y + 1) m) := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      have hstepG : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      rw [hstepL, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
        hstepG, Finset.sum_insert (by simp), ih hge]
      have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      have hm2 : ((m : ℝ) + 1 + 1) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

/-- The telescoping kernel sum: `Σ_{y<d≤z} (1/d − 1/(d+1)) = 1/(y+1) − 1/(z+1)`. -/
lemma telescope_kernel (y : ℕ) : ∀ z : ℕ, y ≤ z →
    ∑ d ∈ Icc (y + 1) z, ((1 : ℝ) / d - 1 / (d + 1)) = 1 / (y + 1) - 1 / (z + 1) := by
  intro z
  induction z with
  | zero =>
    intro hy0
    interval_cases y
    simp
  | succ m ihm =>
    intro hym
    rcases Nat.lt_or_ge m y with hlt | hge
    · have hy : y = m + 1 := by omega
      subst hy
      simp
    · have hstep : Icc (y + 1) (m + 1) = insert (m + 1) (Icc (y + 1) m) := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      rw [hstep, Finset.sum_insert (by simp), ihm hge]
      push_cast
      have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      have hm2 : ((m : ℝ) + 1 + 1) ≠ 0 := by positivity
      field_simp
      ring

/-- **The bounded-sum Abel tail bound** (Siegel brick A2c-i): if all partial sums of `g`
    are bounded by `q`, the tail `Σ_{y<d≤z} g(d)/d` is at most `2q/(y+1)` — uniformly
    in `z`. The engine of both `Σ_{d≤y} g(d)/d`'s convergence and its tail rate. -/
lemma abel_tail_bound (g : ℕ → ℝ) (q : ℝ)
    (hG : ∀ t : ℕ, |∑ n ∈ Icc 1 t, g n| ≤ q) (y z : ℕ) (hyz : y ≤ z) :
    |∑ d ∈ Icc (y + 1) z, g d / d| ≤ 2 * q / (y + 1) := by
  have hq : 0 ≤ q := le_trans (abs_nonneg _) (hG 0)
  rw [abel_window g y z hyz]
  have hterm : ∀ d ∈ Icc (y + 1) z,
      |(∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1))|
        ≤ q * ((1 : ℝ) / d - 1 / (d + 1)) := by
    intro d hd
    obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
    have hd0 : (0:ℝ) < d := by
      have : (1:ℕ) ≤ d := by omega
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
    have hker : (0:ℝ) ≤ 1 / (d : ℝ) - 1 / (d + 1) := by
      rw [sub_nonneg, div_le_div_iff₀ (by positivity) hd0]
      linarith
    rw [abs_mul, abs_of_nonneg hker]
    exact mul_le_mul_of_nonneg_right (hG d) hker
  have htele := telescope_kernel y z hyz
  calc |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1))
        + (∑ n ∈ Icc 1 z, g n) / (z + 1) - (∑ n ∈ Icc 1 y, g n) / (y + 1)|
      ≤ |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1))|
        + |(∑ n ∈ Icc 1 z, g n) / (z + 1)| + |(∑ n ∈ Icc 1 y, g n) / (y + 1)| := by
        set A := ∑ d ∈ Icc (y + 1) z,
          (∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1)) with hA
        set B := (∑ n ∈ Icc 1 z, g n) / ((z:ℝ) + 1) with hB
        set C := (∑ n ∈ Icc 1 y, g n) / ((y:ℝ) + 1) with hC
        have h1 : |A + B| ≤ |A| + |B| := abs_add_le A B
        have h2 : |A + B - C| ≤ |A + B| + |C| := by
          rw [sub_eq_add_neg]
          have := abs_add_le (A + B) (-C)
          rwa [abs_neg] at this
        linarith [h1, h2]
    _ ≤ (q * ((1:ℝ) / (y + 1) - 1 / (z + 1))) + q / (z + 1) + q / (y + 1) := by
        have hs : |∑ d ∈ Icc (y + 1) z,
            (∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1))|
            ≤ q * ((1:ℝ) / (y + 1) - 1 / (z + 1)) := by
          calc |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1))|
              ≤ ∑ d ∈ Icc (y + 1) z, |(∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1))| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ d ∈ Icc (y + 1) z, q * ((1 : ℝ) / d - 1 / (d + 1)) :=
                Finset.sum_le_sum hterm
            _ = q * ((1:ℝ) / (y + 1) - 1 / (z + 1)) := by
                rw [← Finset.mul_sum, htele]
        have hz1 : |(∑ n ∈ Icc 1 z, g n) / ((z:ℝ) + 1)| ≤ q / (z + 1) := by
          rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (z:ℝ) + 1)]
          apply div_le_div_of_nonneg_right (hG z) (by positivity)
        have hy1 : |(∑ n ∈ Icc 1 y, g n) / ((y:ℝ) + 1)| ≤ q / (y + 1) := by
          rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (y:ℝ) + 1)]
          apply div_le_div_of_nonneg_right (hG y) (by positivity)
        linarith [hs, hz1, hy1]
    _ ≤ 2 * q / (y + 1) := by
        have hzq : (0:ℝ) ≤ q / (z + 1) := by positivity
        have h1 : q * ((1:ℝ) / (y + 1) - 1 / (z + 1)) + q / (z + 1) = q / (y + 1) := by
          field_simp
          ring
        have h2 : q / ((y:ℝ) + 1) + q / (y + 1) = 2 * q / (y + 1) := by ring
        linarith [h1, h2]

/-- Prefix-sum difference over `Icc 1`: `Σ_{≤z} − Σ_{≤y} = Σ_{y<·≤z}`. -/
lemma sum_Icc_split (F : ℕ → ℝ) (y z : ℕ) (hyz : y ≤ z) :
    ∑ d ∈ Icc 1 z, F d - ∑ d ∈ Icc 1 y, F d = ∑ d ∈ Icc (y + 1) z, F d := by
  have hIcoIcc : ∀ a b : ℕ, Ico a (b + 1) = Icc a b := by
    intro a b
    ext x
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [← hIcoIcc 1 z,
    ← Finset.sum_Ico_consecutive F (by omega : 1 ≤ y + 1) (by omega : y + 1 ≤ z + 1),
    hIcoIcc 1 y, hIcoIcc (y + 1) z, add_sub_cancel_left]

/-- **The logarithmic mean exists with a tail rate** (Siegel brick A2c-ii): if every
    partial sum of `g` is bounded by `q`, then `S_y = Σ_{d≤y} g(d)/d` converges to some
    `L` with `|L − S_y| ≤ 2q/(y+1)` for every `y` — the abstract `L(1,χ)` of the
    hyperbola main term. -/
theorem log_mean_exists (g : ℕ → ℝ) (q : ℝ)
    (hG : ∀ t : ℕ, |∑ n ∈ Icc 1 t, g n| ≤ q) :
    ∃ L : ℝ, ∀ y : ℕ, |L - ∑ d ∈ Icc 1 y, g d / d| ≤ 2 * q / (y + 1) := by
  have hq : 0 ≤ q := le_trans (abs_nonneg _) (hG 0)
  set S : ℕ → ℝ := fun y => ∑ d ∈ Icc 1 y, g d / d with hS
  have hdiff : ∀ y z : ℕ, y ≤ z → |S z - S y| ≤ 2 * q / (y + 1) := by
    intro y z hyz
    rw [hS]
    simp only
    rw [sum_Icc_split (fun d => g d / d) y z hyz]
    exact abel_tail_bound g q hG y z hyz
  have hb0 : Filter.Tendsto (fun N : ℕ => 2 * q / ((N : ℝ) + 1))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun N : ℕ => ((N : ℝ) + 1)) Filter.atTop Filter.atTop := by
      apply Filter.tendsto_atTop_add_const_right
      exact tendsto_natCast_atTop_atTop
    have h2 := Filter.Tendsto.div_atTop (tendsto_const_nhds (x := 2 * q)) h1
    simpa using h2
  have hcauchy : CauchySeq S := by
    apply cauchySeq_of_le_tendsto_0 (b := fun N : ℕ => 2 * q / ((N : ℝ) + 1)) _ hb0
    intro n m N hn hm
    rw [Real.dist_eq]
    rcases le_total n m with h | h
    · rw [abs_sub_comm]
      calc |S m - S n| ≤ 2 * q / ((n : ℝ) + 1) := hdiff n m h
        _ ≤ 2 * q / ((N : ℝ) + 1) := by
            apply div_le_div_of_nonneg_left (by linarith) (by positivity)
            exact_mod_cast Nat.add_le_add_right hn 1
    · calc |S n - S m| ≤ 2 * q / ((m : ℝ) + 1) := hdiff m n h
        _ ≤ 2 * q / ((N : ℝ) + 1) := by
            apply div_le_div_of_nonneg_left (by linarith) (by positivity)
            exact_mod_cast Nat.add_le_add_right hm 1
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨L, ?_⟩
  intro y
  have htend : Filter.Tendsto (fun z : ℕ => |S z - S y|) Filter.atTop
      (nhds (|L - S y|)) := by
    apply Filter.Tendsto.abs
    exact Filter.Tendsto.sub_const hL (S y)
  apply le_of_tendsto htend
  filter_upwards [Filter.eventually_ge_atTop y] with z hz
  exact hdiff y z hz

/-- Partial sums of the packaged constant-one function count the interval. -/
lemma sum_toArith_one (M : ℕ) :
    ∑ e ∈ Icc 1 M, toArith (fun _ => (1:ℝ)) e = (M : ℝ) := by
  have hterm : ∀ e ∈ Icc 1 M, toArith (fun _ => (1:ℝ)) e = 1 := by
    intro e he
    obtain ⟨he1, _⟩ := Finset.mem_Icc.mp he
    rw [toArith_apply _ _ (by omega)]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Icc]
  simp

/-- **The divisor-character asymptotic** (Siegel brick A2c-iii): for `g` with values
    bounded by 1, partial sums bounded by `q`, and logarithmic mean `L`,
    `|Σ_{n≤N}(g⋆1)(n) − L·N| ≤ (1+4q)·(√N + 1)` — the `H₁(t) = L(1,χ)t + O(q√t)`
    input of the hyperbola method, with the split at `y = ⌊√N⌋`. -/
theorem divisor_char_asymptotic (g : ℕ → ℝ) (q L : ℝ)
    (hgb : ∀ n, |g n| ≤ 1)
    (hG : ∀ t : ℕ, |∑ n ∈ Icc 1 t, g n| ≤ q)
    (hL : ∀ y : ℕ, |L - ∑ d ∈ Icc 1 y, g d / d| ≤ 2 * q / (y + 1))
    (N : ℕ) (hN : 1 ≤ N) :
    |∑ n ∈ Icc 1 N, (toArith g * toArith (fun _ => (1:ℝ))) n - L * N|
      ≤ (1 + 4 * q) * (Real.sqrt N + 1) := by
  have hq : 0 ≤ q := le_trans (abs_nonneg _) (hG 0)
  set y : ℕ := Nat.sqrt N with hy
  have hyN : y ≤ N := Nat.sqrt_le_self N
  rw [hyperbola_identity _ _ N y hyN]
  -- head with the floor split
  have hhead : ∀ d ∈ Icc 1 y, toArith g d * (∑ e ∈ Icc 1 (N / d), toArith (fun _ => (1:ℝ)) e)
      = g d * ((N / d : ℕ) : ℝ) := by
    intro d hd
    obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
    rw [sum_toArith_one, toArith_apply _ _ (by omega)]
  rw [Finset.sum_congr rfl hhead]
  -- decompose ⌊N/d⌋ = N/d − frac(d)
  have hfloor : ∀ d ∈ Icc 1 y, g d * ((N / d : ℕ) : ℝ)
      = (N : ℝ) * (g d / d) - g d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ)) := by
    intro d hd
    obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
    have hd0 : ((d:ℝ)) ≠ 0 := by
      have : (0:ℝ) < d := by exact_mod_cast hd1
      linarith
    field_simp
    ring
  rw [Finset.sum_congr rfl hfloor, Finset.sum_sub_distrib, ← Finset.mul_sum]
  -- name the pieces
  set S : ℝ := ∑ d ∈ Icc 1 y, g d / d with hS
  set FR : ℝ := ∑ d ∈ Icc 1 y, g d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ)) with hFR
  set T : ℝ := ∑ e ∈ Icc 1 (N / (y + 1)), toArith (fun _ => (1:ℝ)) e
      * ((∑ d ∈ Icc 1 (N / e), toArith g d) - ∑ d ∈ Icc 1 y, toArith g d) with hT
  -- bound the fractional-part sum: |FR| ≤ y
  have hFRb : |FR| ≤ y := by
    rw [hFR]
    calc |∑ d ∈ Icc 1 y, g d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ))|
        ≤ ∑ d ∈ Icc 1 y, |g d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Icc 1 y, 1 := by
          apply Finset.sum_le_sum
          intro d hd
          obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
          have hd0 : (0:ℝ) < d := by exact_mod_cast hd1
          rw [abs_mul]
          have hfr0 : (0:ℝ) ≤ (N : ℝ) / d - ((N / d : ℕ) : ℝ) := by
            rw [sub_nonneg]
            exact Nat.cast_div_le
          have hfr1 : (N : ℝ) / d - ((N / d : ℕ) : ℝ) ≤ 1 := by
            have hlt : (N : ℝ) / d < ((N / d : ℕ) : ℝ) + 1 := by
              rw [div_lt_iff₀ hd0]
              have hnat : N < (N / d + 1) * d := by
                have hexp : (N / d + 1) * d = d * (N / d) + d := by ring
                rw [hexp]
                have h1 := Nat.div_add_mod N d
                have h2 := Nat.mod_lt N (show 0 < d by omega)
                omega
              exact_mod_cast hnat
            linarith
          rw [abs_of_nonneg hfr0]
          nlinarith [hgb d, hfr0, hfr1, abs_nonneg (g d)]
      _ ≤ (y : ℝ) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  -- bound the tail: |T| ≤ 2q · N/(y+1)
  have hTb : |T| ≤ 2 * q * ((N / (y + 1) : ℕ) : ℝ) := by
    rw [hT]
    calc |∑ e ∈ Icc 1 (N / (y + 1)), toArith (fun _ => (1:ℝ)) e
          * ((∑ d ∈ Icc 1 (N / e), toArith g d) - ∑ d ∈ Icc 1 y, toArith g d)|
        ≤ ∑ e ∈ Icc 1 (N / (y + 1)), |toArith (fun _ => (1:ℝ)) e
          * ((∑ d ∈ Icc 1 (N / e), toArith g d) - ∑ d ∈ Icc 1 y, toArith g d)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e ∈ Icc 1 (N / (y + 1)), 2 * q := by
          apply Finset.sum_le_sum
          intro e he
          obtain ⟨he1, _⟩ := Finset.mem_Icc.mp he
          have hone : toArith (fun _ => (1:ℝ)) e = 1 := toArith_apply _ _ (by omega)
          rw [hone, one_mul]
          have hsg : ∀ t : ℕ, ∑ d ∈ Icc 1 t, toArith g d = ∑ d ∈ Icc 1 t, g d := by
            intro t
            apply Finset.sum_congr rfl
            intro d hd
            obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
            exact toArith_apply _ _ (by omega)
          rw [hsg, hsg]
          calc |∑ d ∈ Icc 1 (N / e), g d - ∑ d ∈ Icc 1 y, g d|
              ≤ |∑ d ∈ Icc 1 (N / e), g d| + |∑ d ∈ Icc 1 y, g d| := by
                have := abs_add_le (∑ d ∈ Icc 1 (N / e), g d) (-(∑ d ∈ Icc 1 y, g d))
                rwa [abs_neg, ← sub_eq_add_neg] at this
            _ ≤ q + q := add_le_add (hG _) (hG _)
            _ = 2 * q := by ring
      _ = 2 * q * ((N / (y + 1) : ℕ) : ℝ) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
          ring
  -- bound the mean deviation: |N·S − N·L| ≤ 2qN/(y+1)
  have hSL : |(N : ℝ) * S - L * N| ≤ (N : ℝ) * (2 * q / (y + 1)) := by
    have h := hL y
    calc |(N : ℝ) * S - L * N| = (N : ℝ) * |L - S| := by
          rw [show (N : ℝ) * S - L * N = -((N:ℝ) * (L - S)) by ring, abs_neg, abs_mul,
            abs_of_nonneg (by positivity : (0:ℝ) ≤ (N:ℝ))]
      _ ≤ (N : ℝ) * (2 * q / (y + 1)) := by
          apply mul_le_mul_of_nonneg_left h (by positivity)
  -- the √N conversions
  have hyle : (y : ℝ) ≤ Real.sqrt N := by
    rw [hy]
    have h1 : ((Nat.sqrt N : ℝ)) ^ 2 ≤ (N : ℝ) := by
      exact_mod_cast Nat.sqrt_le' N
    exact Real.le_sqrt_of_sq_le h1
  have hNdiv : ((N / (y + 1) : ℕ) : ℝ) ≤ Real.sqrt N := by
    have h1 : ((N / (y + 1) : ℕ) : ℝ) ≤ (N : ℝ) / ((y : ℝ) + 1) := by
      have := Nat.cast_div_le (α := ℝ) (m := N) (n := y + 1)
      push_cast at this
      exact this
    have h2 : (N : ℝ) / ((y : ℝ) + 1) ≤ Real.sqrt N := by
      rw [div_le_iff₀ (by positivity)]
      have hsq : Real.sqrt N * Real.sqrt N = (N : ℝ) :=
        Real.mul_self_sqrt (Nat.cast_nonneg N)
      have hy1 : Real.sqrt N ≤ (y : ℝ) + 1 := by
        rw [hy]
        have := Nat.lt_succ_sqrt' N
        have hcast : (N : ℝ) < ((Nat.sqrt N : ℝ) + 1) ^ 2 := by
          push_cast
          exact_mod_cast this
        nlinarith [Real.sqrt_nonneg (N : ℝ), Real.sq_sqrt (Nat.cast_nonneg N),
          Real.sqrt_nonneg (N:ℝ), hcast]
      nlinarith [Real.sqrt_nonneg (N : ℝ)]
    linarith
  have hNy1 : (N : ℝ) * (2 * q / (y + 1)) ≤ 2 * q * Real.sqrt N := by
    rw [mul_div_assoc']
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (y:ℝ) + 1)]
    have hy1 : Real.sqrt N ≤ (y : ℝ) + 1 := by
      rw [hy]
      have := Nat.lt_succ_sqrt' N
      have hcast : (N : ℝ) < ((Nat.sqrt N : ℝ) + 1) ^ 2 := by
        push_cast
        exact_mod_cast this
      nlinarith [Real.sqrt_nonneg (N : ℝ), Real.sq_sqrt (Nat.cast_nonneg N), hcast]
    have hsq : Real.sqrt N * Real.sqrt N = (N : ℝ) :=
      Real.mul_self_sqrt (Nat.cast_nonneg N)
    have hkey : Real.sqrt N * Real.sqrt N ≤ Real.sqrt N * ((y:ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hy1 (Real.sqrt_nonneg _)
    nlinarith [Real.sqrt_nonneg (N : ℝ), hq, hkey, hsq]
  -- assemble
  have hgoal : |(N : ℝ) * S - FR + T - L * N| ≤ (1 + 4*q) * (Real.sqrt N + 1) := by
    have h1 : |(N : ℝ) * S - FR + T - L * N|
        ≤ |(N : ℝ) * S - L * N| + |FR| + |T| := by
      have ha := abs_add_le ((N : ℝ) * S - L * N) (-FR)
      have hb := abs_add_le ((N : ℝ) * S - L * N + -FR) T
      rw [abs_neg] at ha
      have hrw : (N : ℝ) * S - FR + T - L * N = ((N : ℝ) * S - L * N + -FR) + T := by
        ring
      rw [hrw]
      calc |((N : ℝ) * S - L * N + -FR) + T|
          ≤ |(N : ℝ) * S - L * N + -FR| + |T| := abs_add_le _ _
        _ ≤ |(N : ℝ) * S - L * N| + |FR| + |T| := by linarith [ha]
    calc |(N : ℝ) * S - FR + T - L * N|
        ≤ |(N : ℝ) * S - L * N| + |FR| + |T| := h1
      _ ≤ (N : ℝ) * (2 * q / (y + 1)) + (y : ℝ) + 2 * q * ((N / (y + 1) : ℕ) : ℝ) := by
          linarith [hSL, hFRb, hTb]
      _ ≤ 2 * q * Real.sqrt N + Real.sqrt N + 2 * q * Real.sqrt N := by
          have h3 : 2 * q * ((N / (y + 1) : ℕ) : ℝ) ≤ 2 * q * Real.sqrt N :=
            mul_le_mul_of_nonneg_left hNdiv (by linarith)
          linarith [hNy1, hyle, h3]
      _ ≤ (1 + 4*q) * (Real.sqrt N + 1) := by
          have hs0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
          nlinarith [hq, hs0]
  exact hgoal

/-- **The doubly-bounded convolution has √-size partial sums** (Siegel brick A2d):
    if `k₁, k₂` have values bounded by 1 and partial sums bounded by `q₁, q₂`, then
    `|Σ_{n≤t}(k₁⋆k₂)(n)| ≤ (2q₁+q₂)(√t+1)` — the `K(t) ≪ Q²√t` bound for
    `k = χ₂ ⋆ (χ₁χ₂)`, whose L-series has no pole. -/
theorem bounded_conv_sqrt_bound (k₁ k₂ : ℕ → ℝ) (q₁ q₂ : ℝ)
    (h1b : ∀ n, |k₁ n| ≤ 1) (h2b : ∀ n, |k₂ n| ≤ 1)
    (hK1 : ∀ t : ℕ, |∑ n ∈ Icc 1 t, k₁ n| ≤ q₁)
    (hK2 : ∀ t : ℕ, |∑ n ∈ Icc 1 t, k₂ n| ≤ q₂)
    (t : ℕ) :
    |∑ n ∈ Icc 1 t, (toArith k₁ * toArith k₂) n| ≤ (2 * q₁ + q₂) * (Real.sqrt t + 1) := by
  have hq1 : 0 ≤ q₁ := le_trans (abs_nonneg _) (hK1 0)
  have hq2 : 0 ≤ q₂ := le_trans (abs_nonneg _) (hK2 0)
  set y : ℕ := Nat.sqrt t with hy
  have hyt : y ≤ t := Nat.sqrt_le_self t
  rw [hyperbola_identity _ _ t y hyt]
  have hsg : ∀ (k : ℕ → ℝ) (M : ℕ), ∑ d ∈ Icc 1 M, toArith k d = ∑ d ∈ Icc 1 M, k d := by
    intro k M
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
    exact toArith_apply _ _ (by omega)
  -- the √ conversions (as in A2c-iii)
  have hyle : (y : ℝ) ≤ Real.sqrt t := by
    rw [hy]
    have h1 : ((Nat.sqrt t : ℝ)) ^ 2 ≤ (t : ℝ) := by exact_mod_cast Nat.sqrt_le' t
    exact Real.le_sqrt_of_sq_le h1
  have hy1 : Real.sqrt t ≤ (y : ℝ) + 1 := by
    rw [hy]
    have hlt := Nat.lt_succ_sqrt' t
    have hcast : (t : ℝ) < ((Nat.sqrt t : ℝ) + 1) ^ 2 := by
      push_cast
      exact_mod_cast hlt
    nlinarith [Real.sqrt_nonneg (t : ℝ), Real.sq_sqrt (Nat.cast_nonneg t), hcast]
  have hNdiv : ((t / (y + 1) : ℕ) : ℝ) ≤ Real.sqrt t := by
    have h1 : ((t / (y + 1) : ℕ) : ℝ) ≤ (t : ℝ) / ((y : ℝ) + 1) := by
      have := Nat.cast_div_le (α := ℝ) (m := t) (n := y + 1)
      push_cast at this
      exact this
    have h2 : (t : ℝ) / ((y : ℝ) + 1) ≤ Real.sqrt t := by
      rw [div_le_iff₀ (by positivity)]
      have hsq : Real.sqrt t * Real.sqrt t = (t : ℝ) :=
        Real.mul_self_sqrt (Nat.cast_nonneg t)
      nlinarith [Real.sqrt_nonneg (t : ℝ), hy1, hsq]
    linarith
  -- head bound
  have hhead : |∑ d ∈ Icc 1 y, toArith k₁ d * (∑ e ∈ Icc 1 (t / d), toArith k₂ e)|
      ≤ (y : ℝ) * q₂ := by
    calc |∑ d ∈ Icc 1 y, toArith k₁ d * (∑ e ∈ Icc 1 (t / d), toArith k₂ e)|
        ≤ ∑ d ∈ Icc 1 y, |toArith k₁ d * (∑ e ∈ Icc 1 (t / d), toArith k₂ e)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Icc 1 y, q₂ := by
          apply Finset.sum_le_sum
          intro d hd
          obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
          rw [abs_mul, toArith_apply _ _ (by omega), hsg]
          calc |k₁ d| * |∑ e ∈ Icc 1 (t / d), k₂ e| ≤ 1 * q₂ :=
              mul_le_mul (h1b d) (hK2 _) (abs_nonneg _) zero_le_one
            _ = q₂ := one_mul q₂
      _ = (y : ℝ) * q₂ := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  -- tail bound
  have htail : |∑ e ∈ Icc 1 (t / (y + 1)), toArith k₂ e
      * ((∑ d ∈ Icc 1 (t / e), toArith k₁ d) - ∑ d ∈ Icc 1 y, toArith k₁ d)|
      ≤ ((t / (y + 1) : ℕ) : ℝ) * (2 * q₁) := by
    calc |∑ e ∈ Icc 1 (t / (y + 1)), toArith k₂ e
        * ((∑ d ∈ Icc 1 (t / e), toArith k₁ d) - ∑ d ∈ Icc 1 y, toArith k₁ d)|
        ≤ ∑ e ∈ Icc 1 (t / (y + 1)), |toArith k₂ e
          * ((∑ d ∈ Icc 1 (t / e), toArith k₁ d) - ∑ d ∈ Icc 1 y, toArith k₁ d)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e ∈ Icc 1 (t / (y + 1)), 2 * q₁ := by
          apply Finset.sum_le_sum
          intro e he
          obtain ⟨he1, _⟩ := Finset.mem_Icc.mp he
          rw [abs_mul, toArith_apply _ _ (by omega), hsg, hsg]
          have hdiff : |∑ d ∈ Icc 1 (t / e), k₁ d - ∑ d ∈ Icc 1 y, k₁ d| ≤ 2 * q₁ := by
            have h := abs_add_le (∑ d ∈ Icc 1 (t / e), k₁ d) (-(∑ d ∈ Icc 1 y, k₁ d))
            rw [abs_neg, ← sub_eq_add_neg] at h
            calc |∑ d ∈ Icc 1 (t / e), k₁ d - ∑ d ∈ Icc 1 y, k₁ d|
                ≤ |∑ d ∈ Icc 1 (t / e), k₁ d| + |∑ d ∈ Icc 1 y, k₁ d| := h
              _ ≤ q₁ + q₁ := add_le_add (hK1 _) (hK1 _)
              _ = 2 * q₁ := by ring
          calc |k₂ e| * |∑ d ∈ Icc 1 (t / e), k₁ d - ∑ d ∈ Icc 1 y, k₁ d|
              ≤ 1 * (2 * q₁) := mul_le_mul (h2b e) hdiff (abs_nonneg _) zero_le_one
            _ = 2 * q₁ := one_mul _
      _ = ((t / (y + 1) : ℕ) : ℝ) * (2 * q₁) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  -- assemble
  calc |∑ d ∈ Icc 1 y, toArith k₁ d * (∑ e ∈ Icc 1 (t / d), toArith k₂ e)
        + ∑ e ∈ Icc 1 (t / (y + 1)), toArith k₂ e
          * ((∑ d ∈ Icc 1 (t / e), toArith k₁ d) - ∑ d ∈ Icc 1 y, toArith k₁ d)|
      ≤ |∑ d ∈ Icc 1 y, toArith k₁ d * (∑ e ∈ Icc 1 (t / d), toArith k₂ e)|
        + |∑ e ∈ Icc 1 (t / (y + 1)), toArith k₂ e
          * ((∑ d ∈ Icc 1 (t / e), toArith k₁ d) - ∑ d ∈ Icc 1 y, toArith k₁ d)| :=
        abs_add_le _ _
    _ ≤ (y : ℝ) * q₂ + ((t / (y + 1) : ℕ) : ℝ) * (2 * q₁) := add_le_add hhead htail
    _ ≤ Real.sqrt t * q₂ + Real.sqrt t * (2 * q₁) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hyle hq2
        · apply mul_le_mul_of_nonneg_right hNdiv (by linarith)
    _ ≤ (2 * q₁ + q₂) * (Real.sqrt t + 1) := by
        have hs0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
        nlinarith [hq1, hq2, hs0]

/-- Sharp 3/2-power telescoping (Siegel brick A2e-i-a):
    `Σ_{y<d≤z} 1/(d√d) ≤ 2/√y − 2/√z` for `1 ≤ y ≤ z` — from the previous-interval
    comparison `1/(d√d) ≤ 2(1/√(d−1) − 1/√d)`. -/
lemma sum_three_half_tail_sharp (y : ℕ) (hy1 : 1 ≤ y) : ∀ z : ℕ, y ≤ z →
    ∑ d ∈ Icc (y + 1) z, (1 : ℝ) / (d * Real.sqrt d)
      ≤ 2 / Real.sqrt y - 2 / Real.sqrt z := by
  intro z
  induction z with
  | zero =>
    intro hy0
    omega
  | succ m ihm =>
    intro hym
    rcases Nat.lt_or_ge m y with hlt | hge
    · -- y = m + 1: empty window, RHS = 0
      have hy : y = m + 1 := by omega
      subst hy
      simp
    · -- extend from m to m+1; m ≥ y ≥ 1
      have hm1 : 1 ≤ m := le_trans hy1 hge
      have hstep : Icc (y + 1) (m + 1) = insert (m + 1) (Icc (y + 1) m) := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      rw [hstep, Finset.sum_insert (by simp)]
      have hm0 : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm1
      have hm10 : (0:ℝ) < (m : ℝ) + 1 := by linarith
      set a : ℝ := Real.sqrt m with ha
      set b : ℝ := Real.sqrt ((m : ℝ) + 1) with hb
      have hs1 : (0:ℝ) < a := Real.sqrt_pos.mpr hm0
      have hs2 : (0:ℝ) < b := Real.sqrt_pos.mpr hm10
      have hsq1 : a * a = (m : ℝ) := Real.mul_self_sqrt hm0.le
      have hsq2 : b * b = (m : ℝ) + 1 := Real.mul_self_sqrt hm10.le
      have hmono : a ≤ b := Real.sqrt_le_sqrt (by linarith)
      have hba : b * b - a * a = 1 := by linarith [hsq1, hsq2]
      have hkey : (1 : ℝ) / (((m + 1 : ℕ) : ℝ) * Real.sqrt ((m + 1 : ℕ) : ℝ))
          ≤ 2 / a - 2 / b := by
        have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
        rw [hcast, ← hb]
        rw [div_sub_div _ _ (ne_of_gt hs1) (ne_of_gt hs2),
          div_le_div_iff₀ (by positivity) (by positivity)]
        -- goal: 1·(a·b) ≤ (2b − 2a)·((m+1)·b); with m+1 = b², reduces to ab ≤ m+2
        have hab : a * b ≤ b * b := mul_le_mul_of_nonneg_right hmono hs2.le
        nlinarith [hab, hba, hsq1, hsq2, hs1, hs2, hmono,
          mul_pos hs1 hs2, mul_nonneg (mul_nonneg (sub_nonneg.mpr hmono) hs2.le) hs2.le,
          mul_le_mul_of_nonneg_right hab hs2.le]
      have hih := ihm hge
      have hccast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      have hsm : Real.sqrt ((m : ℕ) : ℝ) = a := rfl
      calc (1 : ℝ) / (((m + 1 : ℕ) : ℝ) * Real.sqrt ((m + 1 : ℕ) : ℝ))
            + ∑ d ∈ Icc (y + 1) m, (1 : ℝ) / (d * Real.sqrt d)
          ≤ (2 / a - 2 / b) + (2 / Real.sqrt y - 2 / a) :=
            add_le_add hkey hih
        _ = 2 / Real.sqrt y - 2 / b := by ring
        _ = 2 / Real.sqrt y - 2 / Real.sqrt ((m + 1 : ℕ) : ℝ) := by
            rw [show Real.sqrt ((m + 1 : ℕ) : ℝ) = b from by rw [hccast]]

/-- Boundary helper: `(√t+1)/(t+1) ≤ 2/√t` for `t ≥ 1`. -/
lemma sqrt_boundary_le (t : ℕ) (ht : 1 ≤ t) :
    (Real.sqrt t + 1) / ((t : ℝ) + 1) ≤ 2 / Real.sqrt t := by
  have ht0 : (0:ℝ) < t := by exact_mod_cast ht
  have hs : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hsq : Real.sqrt t * Real.sqrt t = (t : ℝ) := Real.mul_self_sqrt ht0.le
  have hs1 : (1:ℝ) ≤ Real.sqrt t :=
    Real.one_le_sqrt.mpr (by exact_mod_cast ht)
  rw [div_le_div_iff₀ (by positivity) hs]
  nlinarith [hsq, hs1, hs]

/-- **The √-growth Abel tail** (Siegel brick A2e-ii-a): if the partial sums of `k`
    satisfy `|K(t)| ≤ B(√t+1)`, then `|Σ_{y<d≤z} k(d)/d| ≤ 7B/√y` for `1 ≤ y ≤ z` —
    the tail engine for the pole-free convolution side of the Goldfeld product. -/
theorem abel_tail_sqrt (k : ℕ → ℝ) (B : ℝ)
    (hK : ∀ t : ℕ, |∑ n ∈ Icc 1 t, k n| ≤ B * (Real.sqrt t + 1))
    (y z : ℕ) (hy1 : 1 ≤ y) (hyz : y ≤ z) :
    |∑ d ∈ Icc (y + 1) z, k d / d| ≤ 7 * B / Real.sqrt y := by
  have hB : 0 ≤ B := by
    have h0 := hK 0
    simp at h0
    linarith [abs_nonneg (∑ n ∈ Icc 1 0, k n), h0]
  have hy0 : (0:ℝ) < y := by exact_mod_cast hy1
  have hsy : (0:ℝ) < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have hsyz : Real.sqrt y ≤ Real.sqrt z := Real.sqrt_le_sqrt (by exact_mod_cast hyz)
  have hsz : (0:ℝ) < Real.sqrt z := lt_of_lt_of_le hsy hsyz
  rw [abel_window k y z hyz]
  -- termwise: |K(d)|·κ_d ≤ B/(d√d) + B·κ_d
  have hterm : ∀ d ∈ Icc (y + 1) z,
      |(∑ n ∈ Icc 1 d, k n) * ((1 : ℝ) / d - 1 / (d + 1))|
        ≤ B * ((1:ℝ) / (d * Real.sqrt d)) + B * ((1:ℝ) / d - 1 / (d + 1)) := by
    intro d hd
    obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
    have hd0 : (0:ℝ) < d := by
      have : (1:ℕ) ≤ d := by omega
      exact_mod_cast this
    have hsd : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.mpr hd0
    have hsqd : Real.sqrt d * Real.sqrt d = (d : ℝ) := Real.mul_self_sqrt hd0.le
    have hker : (0:ℝ) ≤ 1 / (d : ℝ) - 1 / (d + 1) := by
      rw [sub_nonneg, div_le_div_iff₀ (by positivity) hd0]
      linarith
    have hkerid : (1 : ℝ) / d - 1 / (d + 1) = 1 / ((d : ℝ) * (d + 1)) := by
      field_simp
      ring
    have hsdker : Real.sqrt d * ((1:ℝ) / d - 1 / (d + 1)) ≤ 1 / ((d:ℝ) * Real.sqrt d) := by
      rw [hkerid,
        show Real.sqrt d * ((1:ℝ) / ((d:ℝ) * (d + 1)))
          = Real.sqrt d / ((d:ℝ) * (d + 1)) from by ring,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hsqd, hd0, hsd]
    rw [abs_mul, abs_of_nonneg hker]
    calc |∑ n ∈ Icc 1 d, k n| * ((1:ℝ) / d - 1 / (d + 1))
        ≤ (B * (Real.sqrt d + 1)) * ((1:ℝ) / d - 1 / (d + 1)) :=
          mul_le_mul_of_nonneg_right (hK d) hker
      _ = B * (Real.sqrt d * ((1:ℝ) / d - 1 / (d + 1)))
          + B * ((1:ℝ) / d - 1 / (d + 1)) := by ring
      _ ≤ B * ((1:ℝ) / (d * Real.sqrt d)) + B * ((1:ℝ) / d - 1 / (d + 1)) := by
          have := mul_le_mul_of_nonneg_left hsdker hB
          linarith
  -- the summed middle piece
  have hmid : |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * ((1 : ℝ) / d - 1 / (d + 1))|
      ≤ B * (2 / Real.sqrt y) + B * (1 / ((y:ℝ) + 1)) := by
    calc |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * ((1 : ℝ) / d - 1 / (d + 1))|
        ≤ ∑ d ∈ Icc (y + 1) z, |(∑ n ∈ Icc 1 d, k n) * ((1 : ℝ) / d - 1 / (d + 1))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Icc (y + 1) z, (B * ((1:ℝ) / (d * Real.sqrt d))
          + B * ((1:ℝ) / d - 1 / (d + 1))) := Finset.sum_le_sum hterm
      _ = B * (∑ d ∈ Icc (y + 1) z, (1:ℝ) / (d * Real.sqrt d))
          + B * (∑ d ∈ Icc (y + 1) z, ((1:ℝ) / d - 1 / (d + 1))) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ B * (2 / Real.sqrt y - 2 / Real.sqrt z)
          + B * (1 / ((y:ℝ) + 1) - 1 / ((z:ℝ) + 1)) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left (sum_three_half_tail_sharp y hy1 z hyz) hB
          · rw [telescope_kernel y z hyz]
      _ ≤ B * (2 / Real.sqrt y) + B * (1 / ((y:ℝ) + 1)) := by
          have h1 : (0:ℝ) ≤ 2 / Real.sqrt z := by positivity
          have h2 : (0:ℝ) ≤ 1 / ((z:ℝ) + 1) := by positivity
          nlinarith [hB, h1, h2]
  -- boundaries
  have hbz : |(∑ n ∈ Icc 1 z, k n) / ((z:ℝ) + 1)| ≤ 2 * B / Real.sqrt y := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (z:ℝ) + 1)]
    have h1 : |∑ n ∈ Icc 1 z, k n| / ((z:ℝ) + 1) ≤ B * ((Real.sqrt z + 1) / ((z:ℝ) + 1)) := by
      rw [mul_div_assoc'] at *
      apply div_le_div_of_nonneg_right (hK z) (by positivity)
    have h2 : (Real.sqrt z + 1) / ((z:ℝ) + 1) ≤ 2 / Real.sqrt z :=
      sqrt_boundary_le z (by omega)
    have h3 : (2:ℝ) / Real.sqrt z ≤ 2 / Real.sqrt y := by
      apply div_le_div_of_nonneg_left (by norm_num) hsy hsyz
    calc |∑ n ∈ Icc 1 z, k n| / ((z:ℝ) + 1)
        ≤ B * ((Real.sqrt z + 1) / ((z:ℝ) + 1)) := h1
      _ ≤ B * (2 / Real.sqrt y) := by
          apply mul_le_mul_of_nonneg_left _ hB
          linarith
      _ = 2 * B / Real.sqrt y := by ring
  have hby : |(∑ n ∈ Icc 1 y, k n) / ((y:ℝ) + 1)| ≤ 2 * B / Real.sqrt y := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (y:ℝ) + 1)]
    have h1 : |∑ n ∈ Icc 1 y, k n| / ((y:ℝ) + 1) ≤ B * ((Real.sqrt y + 1) / ((y:ℝ) + 1)) := by
      rw [mul_div_assoc'] at *
      apply div_le_div_of_nonneg_right (hK y) (by positivity)
    have h2 : (Real.sqrt y + 1) / ((y:ℝ) + 1) ≤ 2 / Real.sqrt y :=
      sqrt_boundary_le y hy1
    calc |∑ n ∈ Icc 1 y, k n| / ((y:ℝ) + 1)
        ≤ B * ((Real.sqrt y + 1) / ((y:ℝ) + 1)) := h1
      _ ≤ B * (2 / Real.sqrt y) := mul_le_mul_of_nonneg_left h2 hB
      _ = 2 * B / Real.sqrt y := by ring
  -- assemble: mid + boundaries, with 1/(y+1) ≤ 1/√y
  have hy1r : (1:ℝ) / ((y:ℝ) + 1) ≤ 1 / Real.sqrt y := by
    apply div_le_div_of_nonneg_left one_pos.le hsy
    nlinarith [Real.mul_self_sqrt hy0.le,
      Real.one_le_sqrt.mpr (by exact_mod_cast hy1 : (1:ℝ) ≤ (y:ℝ)), hsy]
  set M := ∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * ((1 : ℝ) / d - 1 / (d + 1)) with hM
  set Bz := (∑ n ∈ Icc 1 z, k n) / ((z:ℝ) + 1) with hBz
  set By := (∑ n ∈ Icc 1 y, k n) / ((y:ℝ) + 1) with hBy
  have htri : |M + Bz - By| ≤ |M| + |Bz| + |By| := by
    have h1 := abs_add_le M Bz
    have h2 := abs_add_le (M + Bz) (-By)
    rw [abs_neg, ← sub_eq_add_neg] at h2
    linarith
  calc |M + Bz - By| ≤ |M| + |Bz| + |By| := htri
    _ ≤ (B * (2 / Real.sqrt y) + B * (1 / ((y:ℝ) + 1)))
        + 2 * B / Real.sqrt y + 2 * B / Real.sqrt y := by
        linarith [hmid, hbz, hby]
    _ ≤ 7 * B / Real.sqrt y := by
        have hstep : B * (1 / ((y:ℝ) + 1)) ≤ B * (1 / Real.sqrt y) :=
          mul_le_mul_of_nonneg_left hy1r hB
        have hexp : B * (2 / Real.sqrt y) = 2 * B / Real.sqrt y := by ring
        have hexp2 : B * (1 / Real.sqrt y) = B / Real.sqrt y := by ring
        have hexp3 : 7 * B / Real.sqrt y = 7 * (B / Real.sqrt y) := by ring
        have hexp4 : 2 * B / Real.sqrt y = 2 * (B / Real.sqrt y) := by ring
        linarith [hstep, hexp, hexp2, hexp3, hexp4]

/-- **The k-side mean exists with √-rate** (Siegel brick A2e-ii): with `|K(t)| ≤ B(√t+1)`,
    `S_y = Σ_{d≤y} k(d)/d` converges to some `Lk` with `|Lk − S_y| ≤ 7B/√y` for `y ≥ 1` —
    the abstract `L(1,χ₂)L(1,χ₁χ₂)` of the hyperbola main term. -/
theorem sqrt_mean_exists (k : ℕ → ℝ) (B : ℝ)
    (hK : ∀ t : ℕ, |∑ n ∈ Icc 1 t, k n| ≤ B * (Real.sqrt t + 1)) :
    ∃ Lk : ℝ, ∀ y : ℕ, 1 ≤ y →
      |Lk - ∑ d ∈ Icc 1 y, k d / d| ≤ 7 * B / Real.sqrt y := by
  have hB : 0 ≤ B := by
    have h0 := hK 0
    simp at h0
    linarith [abs_nonneg (∑ n ∈ Icc 1 0, k n), h0]
  set S : ℕ → ℝ := fun y => ∑ d ∈ Icc 1 y, k d / d with hS
  have hIcoIcc : ∀ a b : ℕ, Ico a (b + 1) = Icc a b := by
    intro a b
    ext x
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  have hdiff : ∀ y z : ℕ, 1 ≤ y → y ≤ z → |S z - S y| ≤ 7 * B / Real.sqrt y := by
    intro y z hy1 hyz
    have hsplit : S z - S y = ∑ d ∈ Icc (y + 1) z, k d / d := by
      rw [hS]
      simp only
      rw [← hIcoIcc 1 z,
        ← Finset.sum_Ico_consecutive (fun d => k d / d)
          (by omega : 1 ≤ y + 1) (by omega : y + 1 ≤ z + 1),
        hIcoIcc 1 y, hIcoIcc (y + 1) z, add_sub_cancel_left]
    rw [hsplit]
    exact abel_tail_sqrt k B hK y z hy1 hyz
  -- work with the shifted sequence T n = S (n+1): indices always ≥ 1
  set T : ℕ → ℝ := fun n => S (n + 1) with hT
  have hb0 : Filter.Tendsto (fun N : ℕ => 7 * B / Real.sqrt ((N:ℝ) + 1))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun N : ℕ => Real.sqrt ((N:ℝ) + 1))
        Filter.atTop Filter.atTop := by
      apply Filter.Tendsto.comp Real.tendsto_sqrt_atTop
      apply Filter.tendsto_atTop_add_const_right
      exact tendsto_natCast_atTop_atTop
    have h2 := Filter.Tendsto.div_atTop (tendsto_const_nhds (x := 7 * B)) h1
    simpa using h2
  have hcauchy : CauchySeq T := by
    apply cauchySeq_of_le_tendsto_0 (b := fun N : ℕ => 7 * B / Real.sqrt ((N:ℝ) + 1)) _ hb0
    intro n m N hn hm
    rw [Real.dist_eq]
    have hkey : ∀ u v : ℕ, u ≤ v → N ≤ u →
        |T v - T u| ≤ 7 * B / Real.sqrt ((N:ℝ) + 1) := by
      intro u v huv hNu
      calc |T v - T u| = |S (v + 1) - S (u + 1)| := by rw [hT]
        _ ≤ 7 * B / Real.sqrt ((u:ℝ) + 1) := by
            have h := hdiff (u + 1) (v + 1) (by omega) (by omega)
            have hc : ((u + 1 : ℕ) : ℝ) = (u : ℝ) + 1 := by push_cast; ring
            rwa [hc] at h
        _ ≤ 7 * B / Real.sqrt ((N:ℝ) + 1) := by
            apply div_le_div_of_nonneg_left (by linarith) (by positivity)
            apply Real.sqrt_le_sqrt
            have : (N:ℝ) ≤ (u:ℝ) := by exact_mod_cast hNu
            linarith
    rcases le_total n m with h | h
    · rw [abs_sub_comm]
      exact hkey n m h hn
    · exact hkey m n h hm
  obtain ⟨Lk, hLk⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨Lk, ?_⟩
  intro y hy1
  have htend : Filter.Tendsto (fun z : ℕ => |T z - S y|) Filter.atTop
      (nhds (|Lk - S y|)) := by
    apply Filter.Tendsto.abs
    exact Filter.Tendsto.sub_const hLk (S y)
  apply le_of_tendsto htend
  filter_upwards [Filter.eventually_ge_atTop y] with z hz
  calc |T z - S y| = |S (z + 1) - S y| := by rw [hT]
    _ ≤ 7 * B / Real.sqrt y := hdiff y (z + 1) hy1 (by omega)

/-- Convolution values are divisor-counted (Siegel brick A2e-iii-a1): for 1-bounded
    inputs, `|(k₁⋆k₂)(n)| ≤ τ(n)` where `τ(n) = #divisorsAntidiagonal(n)`. -/
lemma conv_value_le_tau (k₁ k₂ : ℕ → ℝ) (h1b : ∀ n, |k₁ n| ≤ 1) (h2b : ∀ n, |k₂ n| ≤ 1)
    (n : ℕ) :
    |(toArith k₁ * toArith k₂) n| ≤ ((n.divisorsAntidiagonal).card : ℝ) := by
  rw [ArithmeticFunction.mul_apply]
  calc |∑ p ∈ n.divisorsAntidiagonal, toArith k₁ p.1 * toArith k₂ p.2|
      ≤ ∑ p ∈ n.divisorsAntidiagonal, |toArith k₁ p.1 * toArith k₂ p.2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal, 1 := by
        apply Finset.sum_le_sum
        intro p hp
        rw [abs_mul]
        have h1 : |toArith k₁ p.1| ≤ 1 := by
          rcases Nat.eq_zero_or_pos p.1 with h0 | h0
          · simp [toArith, h0]
          · rw [show toArith k₁ p.1 = k₁ p.1 from by simp [toArith, h0.ne']]
            exact h1b p.1
        have h2 : |toArith k₂ p.2| ≤ 1 := by
          rcases Nat.eq_zero_or_pos p.2 with h0 | h0
          · simp [toArith, h0]
          · rw [show toArith k₂ p.2 = k₂ p.2 from by simp [toArith, h0.ne']]
            exact h2b p.2
        calc |toArith k₁ p.1| * |toArith k₂ p.2| ≤ 1 * 1 :=
            mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
    _ = ((n.divisorsAntidiagonal).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Fiberwise unfolding: divisor-pair sums over `d ≤ y` are hyperbola-set sums
    (Siegel brick A2e-iii-a2). -/
lemma sum_divA_eq_hypSet (y : ℕ) (F : ℕ × ℕ → ℝ) :
    ∑ d ∈ Icc 1 y, ∑ p ∈ d.divisorsAntidiagonal, F p
      = ∑ p ∈ (Ioc 0 y ×ˢ Ioc 0 y).filter (fun p => p.1 * p.2 ≤ y), F p := by
  have hL : ∑ d ∈ Icc 1 y, ∑ p ∈ d.divisorsAntidiagonal, F p
      = ∑ d ∈ Icc 1 y, ∑ p ∈ (Ioc 0 y ×ˢ Ioc 0 y).filter (fun x => x.1 * x.2 = d), F p := by
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hd1, hdy⟩ := Finset.mem_Icc.mp hd
    rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le (by omega) hdy]
  rw [hL, Finset.sum_fiberwise_eq_sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro p hp
  rw [Finset.mem_product, Finset.mem_Ioc, Finset.mem_Ioc] at hp
  simp only [Finset.mem_Icc]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos hp.1.1 hp.2.1).ne', h⟩

/-- **τ partial sums** (Siegel brick A2e-iii-a3): `Σ_{d≤y} τ(d) ≤ y(1 + log y)`. -/
lemma sum_tau_le (y : ℕ) (hy : 1 ≤ y) :
    ∑ d ∈ Icc 1 y, ((d.divisorsAntidiagonal).card : ℝ) ≤ (y : ℝ) * (1 + Real.log y) := by
  have hcard : ∀ d ∈ Icc 1 y, ((d.divisorsAntidiagonal).card : ℝ)
      = ∑ p ∈ d.divisorsAntidiagonal, (1 : ℝ) := by
    intro d _
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl hcard, sum_divA_eq_hypSet, sum_hypSet_eq_rows]
  have hrow : ∀ d ∈ Icc 1 y, ∑ e ∈ Icc 1 (y / d), (1:ℝ) ≤ (y : ℝ) * (1 / d) := by
    intro d hd
    obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
    have hd0 : (0:ℝ) < d := by exact_mod_cast hd1
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc, Nat.add_sub_cancel]
    have h1 : ((y / d : ℕ) : ℝ) ≤ (y : ℝ) / d := Nat.cast_div_le
    rw [mul_one_div]
    exact h1
  calc ∑ d ∈ Icc 1 y, ∑ e ∈ Icc 1 (y / d), (1:ℝ)
      ≤ ∑ d ∈ Icc 1 y, (y : ℝ) * (1 / d) := Finset.sum_le_sum hrow
    _ = (y : ℝ) * ∑ d ∈ Icc 1 y, (1 : ℝ) / d := by rw [← Finset.mul_sum]
    _ ≤ (y : ℝ) * (1 + Real.log y) := by
        apply mul_le_mul_of_nonneg_left (sum_one_div_le_log y hy) (by positivity)

/-- **τ/√ partial sums** (Siegel brick A2e-iii-a4):
    `Σ_{d≤y} τ(d)/√d ≤ 2√y(1 + log y)` — on each antidiagonal `p₁p₂ = d`. -/
lemma sum_tau_div_sqrt_le (y : ℕ) (hy : 1 ≤ y) :
    ∑ d ∈ Icc 1 y, ((d.divisorsAntidiagonal).card : ℝ) / Real.sqrt d
      ≤ 2 * Real.sqrt y * (1 + Real.log y) := by
  have hstep : ∀ d ∈ Icc 1 y, ((d.divisorsAntidiagonal).card : ℝ) / Real.sqrt d
      = ∑ p ∈ d.divisorsAntidiagonal, (1 : ℝ) / Real.sqrt (p.1 * p.2) := by
    intro d hd
    obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
    have hterm : ∀ p ∈ d.divisorsAntidiagonal, (1 : ℝ) / Real.sqrt (p.1 * p.2)
        = (1 : ℝ) / Real.sqrt d := by
      intro p hp
      rw [Nat.mem_divisorsAntidiagonal] at hp
      rw [show ((p.1 : ℝ) * (p.2 : ℝ)) = ((d : ℕ) : ℝ) from by exact_mod_cast hp.1]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one_div]
  rw [Finset.sum_congr rfl hstep, sum_divA_eq_hypSet]
  exact sum_hypSet_inv_sqrt_le y hy

/-- **The Goldfeld coefficient asymptotic** (Siegel brick A2e-iii, the analytic capstone
    of A2): with `h := 1⋆g₁` carrying the mean `L₁` and `k := g₂⋆(g₁g₂)` carrying the
    mean `Lk` (√-bounded partial sums `≤ B(√t+1)`),
    `|Σ_{n≤N} a(n) − L₁·Lk·N| ≤ 30(1+q₁)(1+B)·√N·√√N·(1+log N)` for `N ≥ 4` —
    the `A(x) = λx + O(Q^c x^{3/4+ε})` input of Goldfeld's lemma, with
    `λ = L₁·Lk` and the split at `y = ⌊√N⌋`. -/
theorem quad_coeff_asymptotic (g₁ g₂ : ℕ → ℝ) (q₁ B L₁ Lk : ℝ)
    (h1b : ∀ n, |g₁ n| ≤ 1) (h2b : ∀ n, |g₂ n| ≤ 1)
    (hL₁ : ∀ y : ℕ, |L₁ - ∑ d ∈ Icc 1 y, g₁ d / d| ≤ 2 * q₁ / (y + 1))
    (hq₁ : 0 ≤ q₁)
    (hH : ∀ M : ℕ, 1 ≤ M →
      |∑ n ∈ Icc 1 M, (toArith (fun _ => (1:ℝ)) * toArith g₁) n - L₁ * M|
        ≤ (1 + 4 * q₁) * (Real.sqrt M + 1))
    (hKb : ∀ t : ℕ, |∑ n ∈ Icc 1 t, (toArith g₂ * toArith (fun m => g₁ m * g₂ m)) n|
        ≤ B * (Real.sqrt t + 1))
    (hLk : ∀ y : ℕ, 1 ≤ y →
      |Lk - ∑ d ∈ Icc 1 y, (toArith g₂ * toArith (fun m => g₁ m * g₂ m)) d / d|
        ≤ 7 * B / Real.sqrt y)
    (N : ℕ) (hN : 4 ≤ N) :
    |∑ n ∈ Icc 1 N, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
        * toArith (fun m => g₁ m * g₂ m)) n - L₁ * Lk * N|
      ≤ 30 * (1 + q₁) * (1 + B)
        * (Real.sqrt N * Real.sqrt (Real.sqrt N) * (1 + Real.log N)) := by
  have hB : 0 ≤ B := by
    have h0 := hKb 0
    rw [show (Icc 1 0 : Finset ℕ) = ∅ from Finset.Icc_eq_empty (by omega),
      Finset.sum_empty, abs_zero, Nat.cast_zero, Real.sqrt_zero] at h0
    linarith
  have hN1 : 1 ≤ N := by omega
  have hNr : (4:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  -- names
  set h : ArithmeticFunction ℝ := toArith (fun _ => (1:ℝ)) * toArith g₁ with hh
  set k : ArithmeticFunction ℝ := toArith g₂ * toArith (fun m => g₁ m * g₂ m) with hk
  have hregroup : toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
      * toArith (fun m => g₁ m * g₂ m) = k * h := by
    rw [hh, hk, mul_assoc]
    exact mul_comm _ _
  rw [hregroup]
  set y : ℕ := Nat.sqrt N with hy
  have hy2 : 2 ≤ y := by
    rw [hy]
    exact Nat.le_sqrt.mpr (by omega)
  have hy1 : 1 ≤ y := by omega
  have hyN : y ≤ N := Nat.sqrt_le_self N
  rw [hyperbola_identity k h N y hyN]
  -- ===== √-conversions =====
  have hsN : (0:ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by linarith)
  have hsqN : Real.sqrt N * Real.sqrt N = (N:ℝ) := Real.mul_self_sqrt (by linarith)
  have hssN : (0:ℝ) < Real.sqrt (Real.sqrt N) := Real.sqrt_pos.mpr hsN
  have hsqsN : Real.sqrt (Real.sqrt N) * Real.sqrt (Real.sqrt N) = Real.sqrt N :=
    Real.mul_self_sqrt hsN.le
  have hyle : (y : ℝ) ≤ Real.sqrt N := by
    rw [hy]
    exact Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' N)
  have hsyle : Real.sqrt y ≤ Real.sqrt (Real.sqrt N) := Real.sqrt_le_sqrt hyle
  have hy1r : (1:ℝ) ≤ (y:ℝ) := by exact_mod_cast hy1
  have hsy : (0:ℝ) < Real.sqrt y := Real.sqrt_pos.mpr (by linarith)
  -- √N ≤ 2y (from ⌊√N⌋ ≥ √N − 1 ≥ √N/2 for N ≥ 4)
  have h2y : Real.sqrt N ≤ 2 * (y : ℝ) := by
    have hlt := Nat.lt_succ_sqrt' N
    have hcast : (N : ℝ) < ((y : ℝ) + 1) ^ 2 := by
      rw [hy]
      push_cast
      exact_mod_cast hlt
    have hsylt : Real.sqrt N < (y:ℝ) + 1 := by
      nlinarith [hcast, hsqN, hsN]
    linarith [hy1r]
  -- N/√y ≤ √2·√N·√√N — via √y ≥ √√N/√2, i.e. 2y ≥ √N → √(2y) ≥ √√N
  have hNdivsy : (N:ℝ) / Real.sqrt y ≤ 2 * (Real.sqrt N * Real.sqrt (Real.sqrt N)) := by
    rw [div_le_iff₀ hsy]
    -- √√N ≤ √(2y) = √2·√y, then N = (√N√√N)·√√N ≤ (√N√√N)·√2√y ≤ 2(√N√√N)√y
    have h1 : Real.sqrt (Real.sqrt N) ≤ Real.sqrt 2 * Real.sqrt y := by
      calc Real.sqrt (Real.sqrt N) ≤ Real.sqrt (2 * y) := Real.sqrt_le_sqrt (by
            push_cast
            linarith [h2y])
        _ = Real.sqrt 2 * Real.sqrt y := Real.sqrt_mul (by norm_num) _
    have hs2le : Real.sqrt 2 ≤ 2 := by
      have : (Real.sqrt 2) * (Real.sqrt 2) = 2 := Real.mul_self_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg 2]
    have hss1 : (1:ℝ) ≤ Real.sqrt (Real.sqrt N) := by
      apply Real.one_le_sqrt.mpr
      have h2s : (2:ℝ) ≤ Real.sqrt N := by
        apply Real.le_sqrt_of_sq_le
        nlinarith
      linarith
    have hmul := mul_le_mul_of_nonneg_left h1 (mul_nonneg hsN.le hssN.le)
    nlinarith [hmul, hsqN, hsqsN, hs2le,
      mul_nonneg (mul_nonneg hsN.le hssN.le) hsy.le]
  -- ===== value bounds =====
  have hg12b : ∀ n, |g₁ n * g₂ n| ≤ 1 := by
    intro n
    rw [abs_mul]
    calc |g₁ n| * |g₂ n| ≤ 1 * 1 := mul_le_mul (h1b n) (h2b n) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have honeb : ∀ n : ℕ, |(fun _ : ℕ => (1:ℝ)) n| ≤ 1 := fun n => by norm_num
  have hkτ : ∀ n, |k n| ≤ ((n.divisorsAntidiagonal).card : ℝ) := by
    intro n
    rw [hk]
    exact conv_value_le_tau g₂ (fun m => g₁ m * g₂ m) h2b hg12b n
  have hhτ : ∀ n, |h n| ≤ ((n.divisorsAntidiagonal).card : ℝ) := by
    intro n
    rw [hh]
    exact conv_value_le_tau (fun _ => (1:ℝ)) g₁ honeb h1b n
  have hL1b : |L₁| ≤ 1 + q₁ := by
    have h1 := hL₁ 1
    have hS1 : ∑ d ∈ Icc 1 1, g₁ d / d = g₁ 1 := by
      rw [show (Icc 1 1 : Finset ℕ) = {1} from rfl, Finset.sum_singleton]
      norm_num
    rw [hS1] at h1
    have habs := abs_add_le (L₁ - g₁ 1) (g₁ 1)
    simp only [sub_add_cancel] at habs
    have hc : ((1:ℕ):ℝ) + 1 = 2 := by norm_num
    rw [hc] at h1
    have hq2 : 2 * q₁ / 2 = q₁ := by ring
    linarith [habs, h1, h1b 1, hq2.le, hq2.ge]
  -- ===== M' facts =====
  set M' : ℕ := N / (y + 1) with hM'
  have hyy : y * y ≤ N := by
    have h := Nat.sqrt_le' N
    rw [pow_two] at h
    rw [hy]
    exact h
  have hyN2 : y + 1 ≤ N := by nlinarith [hy2, hyy]
  have hM'1 : 1 ≤ M' := by
    rw [hM', Nat.le_div_iff_mul_le (by omega : 0 < y + 1)]
    omega
  have hM'le : (M' : ℝ) ≤ Real.sqrt N := by
    have h1 : ((M' : ℕ) : ℝ) ≤ (N : ℝ) / ((y:ℝ) + 1) := by
      rw [hM']
      have := Nat.cast_div_le (α := ℝ) (m := N) (n := y + 1)
      push_cast at this
      exact this
    have hylt : Real.sqrt N < (y:ℝ) + 1 := by
      have hlt := Nat.lt_succ_sqrt' N
      have hcast : (N : ℝ) < ((y : ℝ) + 1) ^ 2 := by
        rw [hy]
        push_cast
        exact_mod_cast hlt
      nlinarith [hsqN, hsN]
    have h2 : (N : ℝ) / ((y:ℝ) + 1) ≤ Real.sqrt N := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hsqN, hylt, hsN]
    linarith
  have hsM'le : Real.sqrt M' ≤ Real.sqrt (Real.sqrt N) := Real.sqrt_le_sqrt hM'le
  have hlogy : Real.log y ≤ Real.log N := by
    apply Real.log_le_log (by exact_mod_cast hy1 : (0:ℝ) < (y:ℝ))
    exact_mod_cast hyN
  have hlogM' : Real.log M' ≤ Real.log N := by
    apply Real.log_le_log (by exact_mod_cast hM'1 : (0:ℝ) < (M':ℝ))
    have : M' ≤ N := Nat.div_le_self N (y + 1)
    exact_mod_cast this
  have hlogN0 : (0:ℝ) ≤ Real.log N := Real.log_nonneg (by linarith)
  have hlogy1 : 1 + Real.log y ≤ 1 + Real.log N := by linarith
  have hlogy0 : (0:ℝ) ≤ 1 + Real.log y := by
    have := Real.log_nonneg (by exact_mod_cast hy1 : (1:ℝ) ≤ (y:ℝ))
    linarith
  have hlogM'0 : (0:ℝ) ≤ 1 + Real.log M' := by
    have := Real.log_nonneg (by exact_mod_cast hM'1 : (1:ℝ) ≤ (M':ℝ))
    linarith
  have hlogM'1 : 1 + Real.log M' ≤ 1 + Real.log N := by linarith
  have hsqrtdiv : ∀ d : ℕ, 1 ≤ d → Real.sqrt ((N / d : ℕ) : ℝ) ≤ Real.sqrt N / Real.sqrt d := by
    intro d hd1
    calc Real.sqrt ((N / d : ℕ) : ℝ) ≤ Real.sqrt ((N : ℝ) / d) :=
          Real.sqrt_le_sqrt Nat.cast_div_le
      _ = Real.sqrt N / Real.sqrt d := Real.sqrt_div (Nat.cast_nonneg N) d
  -- ===== HEAD =====
  set Sk : ℝ := ∑ d ∈ Icc 1 y, k d / d with hSk
  have hSkLk : |Lk - Sk| ≤ 7 * B / Real.sqrt y := by
    rw [hSk, hk]
    exact hLk y hy1
  have hhead_eq : ∑ d ∈ Icc 1 y, k d * (∑ e ∈ Icc 1 (N / d), h e)
      = L₁ * (∑ d ∈ Icc 1 y, k d * ((N / d : ℕ) : ℝ))
        + ∑ d ∈ Icc 1 y, k d * ((∑ e ∈ Icc 1 (N / d), h e) - L₁ * ((N / d : ℕ) : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hfloor_eq : ∑ d ∈ Icc 1 y, k d * ((N / d : ℕ) : ℝ)
      = (N : ℝ) * Sk - ∑ d ∈ Icc 1 y, k d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ)) := by
    rw [hSk, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
    have hd0 : ((d:ℝ)) ≠ 0 := by
      have : (0:ℝ) < d := by exact_mod_cast hd1
      linarith
    field_simp
    ring
  have hfrac_le : |∑ d ∈ Icc 1 y, k d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ))|
      ≤ (y:ℝ) * (1 + Real.log y) := by
    calc |∑ d ∈ Icc 1 y, k d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ))|
        ≤ ∑ d ∈ Icc 1 y, |k d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Icc 1 y, ((d.divisorsAntidiagonal).card : ℝ) := by
          apply Finset.sum_le_sum
          intro d hd
          obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
          have hd0 : (0:ℝ) < d := by exact_mod_cast hd1
          rw [abs_mul]
          have hfr0 : (0:ℝ) ≤ (N : ℝ) / d - ((N / d : ℕ) : ℝ) := by
            rw [sub_nonneg]
            exact Nat.cast_div_le
          have hfr1 : (N : ℝ) / d - ((N / d : ℕ) : ℝ) ≤ 1 := by
            have hlt : (N : ℝ) / d < ((N / d : ℕ) : ℝ) + 1 := by
              rw [div_lt_iff₀ hd0]
              have hnat : N < (N / d + 1) * d := by
                have hexp : (N / d + 1) * d = d * (N / d) + d := by ring
                rw [hexp]
                have h1 := Nat.div_add_mod N d
                have h2 := Nat.mod_lt N (show 0 < d by omega)
                omega
              exact_mod_cast hnat
            linarith
          rw [abs_of_nonneg hfr0]
          have hτ1 : (1:ℝ) ≤ ((d.divisorsAntidiagonal).card : ℝ) := by
            have hmem : ((1:ℕ), d) ∈ d.divisorsAntidiagonal := by
              rw [Nat.mem_divisorsAntidiagonal]
              exact ⟨one_mul d, by omega⟩
            have hpos : 0 < (d.divisorsAntidiagonal).card := Finset.card_pos.mpr ⟨_, hmem⟩
            exact_mod_cast hpos
          nlinarith [hkτ d, hfr0, hfr1, abs_nonneg (k d), hτ1]
      _ ≤ (y:ℝ) * (1 + Real.log y) := sum_tau_le y hy1
  have hε_le : |∑ d ∈ Icc 1 y, k d * ((∑ e ∈ Icc 1 (N / d), h e) - L₁ * ((N / d : ℕ) : ℝ))|
      ≤ (1 + 4 * q₁) * (2 * Real.sqrt N * Real.sqrt y * (1 + Real.log y)
          + 2 * (y:ℝ) * (1 + Real.log y)) := by
    have hterm : ∀ d ∈ Icc 1 y, |k d * ((∑ e ∈ Icc 1 (N / d), h e) - L₁ * ((N / d : ℕ) : ℝ))|
        ≤ (1 + 4 * q₁) * (((d.divisorsAntidiagonal).card : ℝ) * (Real.sqrt N / Real.sqrt d)
            + ((d.divisorsAntidiagonal).card : ℝ)) := by
      intro d hd
      obtain ⟨hd1, hdy⟩ := Finset.mem_Icc.mp hd
      have hNd1 : 1 ≤ N / d := by
        rw [Nat.le_div_iff_mul_le (by omega : 0 < d)]
        have : d ≤ N := le_trans hdy hyN
        omega
      have hεd := hH (N / d) hNd1
      have hq4 : (0:ℝ) ≤ 1 + 4 * q₁ := by linarith
      rw [show |k d * ((∑ e ∈ Icc 1 (N / d), h e) - L₁ * ((N / d : ℕ) : ℝ))|
          = |k d| * |(∑ e ∈ Icc 1 (N / d), h e) - L₁ * ((N / d : ℕ) : ℝ)| from abs_mul _ _]
      calc |k d| * |(∑ e ∈ Icc 1 (N / d), h e) - L₁ * ((N / d : ℕ) : ℝ)|
          ≤ ((d.divisorsAntidiagonal).card : ℝ)
            * ((1 + 4 * q₁) * (Real.sqrt ((N / d : ℕ) : ℝ) + 1)) :=
            mul_le_mul (hkτ d) hεd (abs_nonneg _) (Nat.cast_nonneg _)
        _ ≤ ((d.divisorsAntidiagonal).card : ℝ)
            * ((1 + 4 * q₁) * (Real.sqrt N / Real.sqrt d + 1)) := by
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            apply mul_le_mul_of_nonneg_left _ hq4
            linarith [hsqrtdiv d hd1]
        _ = (1 + 4 * q₁) * (((d.divisorsAntidiagonal).card : ℝ) * (Real.sqrt N / Real.sqrt d)
            + ((d.divisorsAntidiagonal).card : ℝ)) := by ring
    calc |∑ d ∈ Icc 1 y, k d * ((∑ e ∈ Icc 1 (N / d), h e) - L₁ * ((N / d : ℕ) : ℝ))|
        ≤ ∑ d ∈ Icc 1 y, |k d * ((∑ e ∈ Icc 1 (N / d), h e) - L₁ * ((N / d : ℕ) : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Icc 1 y, (1 + 4 * q₁) * (((d.divisorsAntidiagonal).card : ℝ)
            * (Real.sqrt N / Real.sqrt d) + ((d.divisorsAntidiagonal).card : ℝ)) :=
          Finset.sum_le_sum hterm
      _ ≤ (1 + 4 * q₁) * (Real.sqrt N * (2 * Real.sqrt y * (1 + Real.log y))
            + (y:ℝ) * (1 + Real.log y)) := by
          rw [← Finset.mul_sum]
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          have hsplit : ∑ d ∈ Icc 1 y, (((d.divisorsAntidiagonal).card : ℝ)
              * (Real.sqrt N / Real.sqrt d) + ((d.divisorsAntidiagonal).card : ℝ))
              = Real.sqrt N * (∑ d ∈ Icc 1 y,
                  ((d.divisorsAntidiagonal).card : ℝ) / Real.sqrt d)
                + ∑ d ∈ Icc 1 y, ((d.divisorsAntidiagonal).card : ℝ) := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro d _
            ring
          rw [hsplit]
          exact add_le_add
            (mul_le_mul_of_nonneg_left (sum_tau_div_sqrt_le y hy1) hsN.le)
            (sum_tau_le y hy1)
      _ ≤ (1 + 4 * q₁) * (2 * Real.sqrt N * Real.sqrt y * (1 + Real.log y)
            + 2 * (y:ℝ) * (1 + Real.log y)) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          have hy0' : (0:ℝ) ≤ (y:ℝ) := by positivity
          nlinarith [hlogy0, hy0']
  -- ===== TAIL =====
  have htail_le : |∑ e ∈ Icc 1 M', h e * ((∑ d ∈ Icc 1 (N / e), k d) - ∑ d ∈ Icc 1 y, k d)|
      ≤ 2 * B * (2 * Real.sqrt N * Real.sqrt M' * (1 + Real.log M')
          + 2 * (M':ℝ) * (1 + Real.log M')) := by
    have hterm : ∀ e ∈ Icc 1 M', |h e * ((∑ d ∈ Icc 1 (N / e), k d) - ∑ d ∈ Icc 1 y, k d)|
        ≤ 2 * B * (((e.divisorsAntidiagonal).card : ℝ) * (Real.sqrt N / Real.sqrt e)
            + ((e.divisorsAntidiagonal).card : ℝ)) := by
      intro e he
      obtain ⟨he1, heM⟩ := Finset.mem_Icc.mp he
      have hyNe : y ≤ N / e := by
        rw [Nat.le_div_iff_mul_le (by omega : 0 < e)]
        have h1 : e * (y + 1) ≤ N := by
          rw [hM'] at heM
          have := (Nat.le_div_iff_mul_le (by omega : 0 < y + 1)).mp heM
          omega
        nlinarith [h1]
      have hKdiff : |(∑ d ∈ Icc 1 (N / e), k d) - ∑ d ∈ Icc 1 y, k d|
          ≤ 2 * B * (Real.sqrt ((N / e : ℕ) : ℝ) + 1) := by
        have h1 := hKb (N / e)
        have h2 := hKb y
        have hsymono : Real.sqrt ((y:ℕ) : ℝ) ≤ Real.sqrt ((N / e : ℕ) : ℝ) := by
          apply Real.sqrt_le_sqrt
          exact_mod_cast hyNe
        have htri := abs_add_le (∑ d ∈ Icc 1 (N / e), k d) (-(∑ d ∈ Icc 1 y, k d))
        rw [abs_neg, ← sub_eq_add_neg] at htri
        have hprod := mul_le_mul_of_nonneg_left hsymono hB
        linarith [htri, h1, h2, hprod]
      rw [abs_mul]
      have hB2 : (0:ℝ) ≤ 2 * B := by linarith
      calc |h e| * |(∑ d ∈ Icc 1 (N / e), k d) - ∑ d ∈ Icc 1 y, k d|
          ≤ ((e.divisorsAntidiagonal).card : ℝ)
            * (2 * B * (Real.sqrt ((N / e : ℕ) : ℝ) + 1)) :=
            mul_le_mul (hhτ e) hKdiff (abs_nonneg _) (Nat.cast_nonneg _)
        _ ≤ ((e.divisorsAntidiagonal).card : ℝ)
            * (2 * B * (Real.sqrt N / Real.sqrt e + 1)) := by
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            apply mul_le_mul_of_nonneg_left _ hB2
            linarith [hsqrtdiv e he1]
        _ = 2 * B * (((e.divisorsAntidiagonal).card : ℝ) * (Real.sqrt N / Real.sqrt e)
            + ((e.divisorsAntidiagonal).card : ℝ)) := by ring
    calc |∑ e ∈ Icc 1 M', h e * ((∑ d ∈ Icc 1 (N / e), k d) - ∑ d ∈ Icc 1 y, k d)|
        ≤ ∑ e ∈ Icc 1 M', |h e * ((∑ d ∈ Icc 1 (N / e), k d) - ∑ d ∈ Icc 1 y, k d)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e ∈ Icc 1 M', 2 * B * (((e.divisorsAntidiagonal).card : ℝ)
            * (Real.sqrt N / Real.sqrt e) + ((e.divisorsAntidiagonal).card : ℝ)) :=
          Finset.sum_le_sum hterm
      _ ≤ 2 * B * (Real.sqrt N * (2 * Real.sqrt M' * (1 + Real.log M'))
            + (M':ℝ) * (1 + Real.log M')) := by
          rw [← Finset.mul_sum]
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          have hsplit : ∑ e ∈ Icc 1 M', (((e.divisorsAntidiagonal).card : ℝ)
              * (Real.sqrt N / Real.sqrt e) + ((e.divisorsAntidiagonal).card : ℝ))
              = Real.sqrt N * (∑ e ∈ Icc 1 M',
                  ((e.divisorsAntidiagonal).card : ℝ) / Real.sqrt e)
                + ∑ e ∈ Icc 1 M', ((e.divisorsAntidiagonal).card : ℝ) := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro e _
            ring
          rw [hsplit]
          exact add_le_add
            (mul_le_mul_of_nonneg_left (sum_tau_div_sqrt_le M' hM'1) hsN.le)
            (sum_tau_le M' hM'1)
      _ ≤ 2 * B * (2 * Real.sqrt N * Real.sqrt M' * (1 + Real.log M')
            + 2 * (M':ℝ) * (1 + Real.log M')) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          have hM'0 : (0:ℝ) ≤ (M':ℝ) := by positivity
          nlinarith [hlogM'0, hM'0]
  -- ===== ASSEMBLE =====
  rw [hhead_eq, hfloor_eq]
  set FR := ∑ d ∈ Icc 1 y, k d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ)) with hFRd
  set T2 := ∑ d ∈ Icc 1 y, k d * ((∑ e ∈ Icc 1 (N / d), h e) - L₁ * ((N / d : ℕ) : ℝ)) with hT2d
  set TL := ∑ e ∈ Icc 1 M', h e * ((∑ d ∈ Icc 1 (N / e), k d) - ∑ d ∈ Icc 1 y, k d) with hTLd
  have hrw : L₁ * ((N : ℝ) * Sk - FR) + T2 + TL - L₁ * Lk * N
      = -(L₁ * ((N:ℝ) * (Lk - Sk))) - L₁ * FR + T2 + TL := by ring
  rw [hrw]
  have hb1 : |L₁ * ((N:ℝ) * (Lk - Sk))|
      ≤ (1 + q₁) * (14 * B * (Real.sqrt N * Real.sqrt (Real.sqrt N))) := by
    rw [abs_mul, abs_mul]
    have hNpos : (0:ℝ) ≤ (N:ℝ) := by positivity
    have h1 : |(N:ℝ)| * |Lk - Sk| ≤ (N:ℝ) * (7 * B / Real.sqrt y) := by
      rw [abs_of_nonneg hNpos]
      exact mul_le_mul_of_nonneg_left hSkLk hNpos
    have h3 : (N:ℝ) * (7 * B / Real.sqrt y)
        ≤ 14 * B * (Real.sqrt N * Real.sqrt (Real.sqrt N)) := by
      have h2 : (N:ℝ) * (7 * B / Real.sqrt y) = 7 * B * ((N:ℝ) / Real.sqrt y) := by ring
      rw [h2]
      calc 7 * B * ((N:ℝ) / Real.sqrt y)
          ≤ 7 * B * (2 * (Real.sqrt N * Real.sqrt (Real.sqrt N))) :=
            mul_le_mul_of_nonneg_left hNdivsy (by linarith)
        _ = 14 * B * (Real.sqrt N * Real.sqrt (Real.sqrt N)) := by ring
    calc |L₁| * (|(N:ℝ)| * |Lk - Sk|) ≤ (1 + q₁) * (|(N:ℝ)| * |Lk - Sk|) :=
        mul_le_mul_of_nonneg_right hL1b (by positivity)
      _ ≤ (1 + q₁) * (14 * B * (Real.sqrt N * Real.sqrt (Real.sqrt N))) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          linarith [h1, h3]
  have hb2 : |L₁ * FR| ≤ (1 + q₁) * ((y:ℝ) * (1 + Real.log y)) := by
    rw [abs_mul]
    apply mul_le_mul hL1b hfrac_le (abs_nonneg _) (by linarith)
  have htri4 : |-(L₁ * ((N:ℝ) * (Lk - Sk))) - L₁ * FR + T2 + TL|
      ≤ |L₁ * ((N:ℝ) * (Lk - Sk))| + |L₁ * FR| + |T2| + |TL| := by
    have t1 := abs_add_le (-(L₁ * ((N:ℝ) * (Lk - Sk))) - L₁ * FR) T2
    have t2 := abs_add_le ((-(L₁ * ((N:ℝ) * (Lk - Sk))) - L₁ * FR) + T2) TL
    have t3 := abs_add_le (-(L₁ * ((N:ℝ) * (Lk - Sk)))) (-(L₁ * FR))
    rw [abs_neg, abs_neg, ← sub_eq_add_neg] at t3
    calc |-(L₁ * ((N:ℝ) * (Lk - Sk))) - L₁ * FR + T2 + TL|
        ≤ |(-(L₁ * ((N:ℝ) * (Lk - Sk))) - L₁ * FR) + T2| + |TL| := t2
      _ ≤ |-(L₁ * ((N:ℝ) * (Lk - Sk))) - L₁ * FR| + |T2| + |TL| := by linarith [t1]
      _ ≤ |L₁ * ((N:ℝ) * (Lk - Sk))| + |L₁ * FR| + |T2| + |TL| := by linarith [t3]
  set U := Real.sqrt N * Real.sqrt (Real.sqrt N) * (1 + Real.log N) with hUd
  have hlogNfac : (1:ℝ) ≤ 1 + Real.log N := by linarith
  have hU0 : (0:ℝ) < U := by
    rw [hUd]
    have : (0:ℝ) < 1 + Real.log N := by linarith
    positivity
  have hss1 : (1:ℝ) ≤ Real.sqrt (Real.sqrt N) := by
    apply Real.one_le_sqrt.mpr
    apply Real.one_le_sqrt.mpr
    linarith
  have hu1 : Real.sqrt N * Real.sqrt (Real.sqrt N) ≤ U := by
    rw [hUd]
    nlinarith [mul_nonneg hsN.le hssN.le, hlogNfac]
  have hu2 : (y:ℝ) * (1 + Real.log y) ≤ U := by
    rw [hUd]
    have h1 : (y:ℝ) * (1 + Real.log y) ≤ Real.sqrt N * (1 + Real.log N) :=
      mul_le_mul hyle hlogy1 hlogy0 hsN.le
    nlinarith [hss1, hsN.le, hlogNfac, h1]
  have hu3 : 2 * Real.sqrt N * Real.sqrt y * (1 + Real.log y)
      + 2 * (y:ℝ) * (1 + Real.log y) ≤ 4 * U := by
    have h1 : Real.sqrt N * Real.sqrt y * (1 + Real.log y) ≤ U := by
      rw [hUd]
      have h2 : Real.sqrt N * Real.sqrt y ≤ Real.sqrt N * Real.sqrt (Real.sqrt N) :=
        mul_le_mul_of_nonneg_left hsyle hsN.le
      apply mul_le_mul h2 hlogy1 hlogy0 (by positivity)
    linarith [hu2]
  have hu4 : 2 * Real.sqrt N * Real.sqrt M' * (1 + Real.log M')
      + 2 * (M':ℝ) * (1 + Real.log M') ≤ 4 * U := by
    have h1 : Real.sqrt N * Real.sqrt M' * (1 + Real.log M') ≤ U := by
      rw [hUd]
      have h2 : Real.sqrt N * Real.sqrt M' ≤ Real.sqrt N * Real.sqrt (Real.sqrt N) :=
        mul_le_mul_of_nonneg_left hsM'le hsN.le
      apply mul_le_mul h2 hlogM'1 hlogM'0 (by positivity)
    have h2 : (M':ℝ) * (1 + Real.log M') ≤ U := by
      rw [hUd]
      have hM'N : (M':ℝ) * (1 + Real.log M') ≤ Real.sqrt N * (1 + Real.log N) :=
        mul_le_mul hM'le hlogM'1 hlogM'0 hsN.le
      nlinarith [hss1, hsN.le, hlogNfac, hM'N]
    linarith
  calc |-(L₁ * ((N:ℝ) * (Lk - Sk))) - L₁ * FR + T2 + TL|
      ≤ |L₁ * ((N:ℝ) * (Lk - Sk))| + |L₁ * FR| + |T2| + |TL| := htri4
    _ ≤ (1 + q₁) * (14 * B * (Real.sqrt N * Real.sqrt (Real.sqrt N)))
        + (1 + q₁) * ((y:ℝ) * (1 + Real.log y))
        + (1 + 4 * q₁) * (2 * Real.sqrt N * Real.sqrt y * (1 + Real.log y)
            + 2 * (y:ℝ) * (1 + Real.log y))
        + 2 * B * (2 * Real.sqrt N * Real.sqrt M' * (1 + Real.log M')
            + 2 * (M':ℝ) * (1 + Real.log M')) := by
        linarith [hb1, hb2, hε_le, htail_le]
    _ ≤ (1 + q₁) * (14 * B * U) + (1 + q₁) * U + (1 + 4 * q₁) * (4 * U)
        + 2 * B * (4 * U) := by
        have c1 : (1 + q₁) * (14 * B * (Real.sqrt N * Real.sqrt (Real.sqrt N)))
            ≤ (1 + q₁) * (14 * B * U) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact mul_le_mul_of_nonneg_left hu1 (by linarith)
        have c2 : (1 + q₁) * ((y:ℝ) * (1 + Real.log y)) ≤ (1 + q₁) * U :=
          mul_le_mul_of_nonneg_left hu2 (by linarith)
        have c3 : (1 + 4 * q₁) * (2 * Real.sqrt N * Real.sqrt y * (1 + Real.log y)
            + 2 * (y:ℝ) * (1 + Real.log y)) ≤ (1 + 4 * q₁) * (4 * U) :=
          mul_le_mul_of_nonneg_left hu3 (by linarith)
        have c4 : 2 * B * (2 * Real.sqrt N * Real.sqrt M' * (1 + Real.log M')
            + 2 * (M':ℝ) * (1 + Real.log M')) ≤ 2 * B * (4 * U) :=
          mul_le_mul_of_nonneg_left hu4 (by linarith)
        linarith [c1, c2, c3, c4]
    _ ≤ 30 * (1 + q₁) * (1 + B) * U := by
        nlinarith [hU0.le, hq₁, hB, mul_nonneg hq₁ hB,
          mul_nonneg (mul_nonneg hq₁ hB) hU0.le,
          mul_nonneg hq₁ hU0.le, mul_nonneg hB hU0.le]

/-- The ℂ-cast of a packaged real function. -/
noncomputable def castFn (g : ℕ → ℝ) : ℕ → ℂ := fun n => ((toArith g n : ℝ) : ℂ)

lemma castFn_zero (g : ℕ → ℝ) : castFn g 0 = 0 := by
  simp [castFn, toArith]

lemma castFn_bound (g : ℕ → ℝ) (hg : ∀ n, |g n| ≤ 1) (n : ℕ) : ‖castFn g n‖ ≤ 1 := by
  rw [castFn, Complex.norm_real, Real.norm_eq_abs]
  rcases Nat.eq_zero_or_pos n with rfl | h0
  · simp [toArith]
  · rw [show toArith g n = g n from by simp [toArith, h0.ne']]
    exact hg n

open scoped LSeries.notation in
/-- **Casting commutes with Dirichlet convolution** (Siegel brick A2f-i):
    the ℂ-cast of the `ArithmeticFunction` product is the `⍟`-convolution of the casts. -/
lemma castFn_conv (u v : ℕ → ℝ) (n : ℕ) :
    (((toArith u * toArith v) n : ℝ) : ℂ) = (castFn u ⍟ castFn v) n := by
  rw [ArithmeticFunction.mul_apply, LSeries.convolution_def]
  push_cast
  apply Finset.sum_congr rfl
  intro p hp
  rw [Nat.mem_divisorsAntidiagonal] at hp
  have h1 : p.1 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hp
    exact hp.2 hp.1.symm
  have h2 : p.2 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hp
    exact hp.2 hp.1.symm
  rw [castFn, castFn]

/-- **Summability of bounded packaged series** (Siegel brick A2f-ii): `Re s > 1`. -/
lemma castFn_summable (g : ℕ → ℝ) (hg : ∀ n, |g n| ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (castFn g) s :=
  LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => castFn_bound g hg n) hs

open scoped LSeries.notation in
/-- **The Goldfeld product identity** (Siegel brick A2f-iii): on `Re s > 1`, the
    L-series of the quadruple coefficient sequence factors as the product of the four
    L-series — the series side of `F(s) = ζ(s)L(s,χ₁)L(s,χ₂)L(s,χ₁χ₂)`. -/
theorem quad_LSeries_eq (g₁ g₂ : ℕ → ℝ)
    (h1b : ∀ n, |g₁ n| ≤ 1) (h2b : ∀ n, |g₂ n| ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (((toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
        * toArith (fun m => g₁ m * g₂ m)) n : ℝ) : ℂ)) s
      = LSeries (castFn (fun _ => (1:ℝ))) s * LSeries (castFn g₁) s
        * LSeries (castFn g₂) s * LSeries (castFn (fun m => g₁ m * g₂ m)) s := by
  have honeb : ∀ n : ℕ, |(fun _ : ℕ => (1:ℝ)) n| ≤ 1 := fun n => by norm_num
  have hg12b : ∀ n, |g₁ n * g₂ n| ≤ 1 := by
    intro n
    rw [abs_mul]
    calc |g₁ n| * |g₂ n| ≤ 1 * 1 := mul_le_mul (h1b n) (h2b n) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hS0 := castFn_summable (fun _ => (1:ℝ)) honeb hs
  have hS1 := castFn_summable g₁ h1b hs
  have hS2 := castFn_summable g₂ h2b hs
  have hS12 := castFn_summable (fun m => g₁ m * g₂ m) hg12b hs
  -- rewrite the coefficient function through the cast bridge, twice-nested
  have hbridge : (fun n => (((toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
      * toArith (fun m => g₁ m * g₂ m)) n : ℝ) : ℂ))
      = ((castFn (fun _ => (1:ℝ)) ⍟ castFn g₁) ⍟ castFn g₂)
        ⍟ castFn (fun m => g₁ m * g₂ m) := by
    funext n
    -- peel the outermost product
    have step1 : (((toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
        * toArith (fun m => g₁ m * g₂ m)) n : ℝ) : ℂ)
        = ((fun m => (((toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂) m : ℝ) : ℂ))
          ⍟ castFn (fun m => g₁ m * g₂ m)) n := by
      rw [ArithmeticFunction.mul_apply, LSeries.convolution_def]
      push_cast
      apply Finset.sum_congr rfl
      intro p hp
      rw [Nat.mem_divisorsAntidiagonal] at hp
      have h2 : p.2 ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hp
        exact hp.2 hp.1.symm
      rw [castFn]
    rw [step1]
    -- peel the middle product inside the left slot
    have step2 : (fun m => (((toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂) m : ℝ) : ℂ))
        = (fun m => (((toArith (fun _ => (1:ℝ)) * toArith g₁) m : ℝ) : ℂ)) ⍟ castFn g₂ := by
      funext m
      rw [ArithmeticFunction.mul_apply, LSeries.convolution_def]
      push_cast
      apply Finset.sum_congr rfl
      intro p hp
      rw [Nat.mem_divisorsAntidiagonal] at hp
      have h2 : p.2 ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hp
        exact hp.2 hp.1.symm
      rw [castFn]
    rw [step2]
    -- peel the innermost product
    have step3 : (fun m => (((toArith (fun _ => (1:ℝ)) * toArith g₁) m : ℝ) : ℂ))
        = castFn (fun _ => (1:ℝ)) ⍟ castFn g₁ := by
      funext m
      exact castFn_conv (fun _ => (1:ℝ)) g₁ m
    rw [step3]
  rw [hbridge]
  -- three applications of the convolution identity
  rw [LSeries_convolution' ((hS0.convolution hS1).convolution hS2) hS12,
    LSeries_convolution' (hS0.convolution hS1) hS2,
    LSeries_convolution' hS0 hS1]

/-- **ℂ-weighted Abel summation over an initial window** (Siegel brick A2g-i):
    `Σ_{n≤x} a(n)w(n) = A(x)w(x) + Σ_{n<x} A(n)(w(n) − w(n+1))` with
    `A(t) = Σ_{n≤t} a(n)` — the discrete engine of the integral representation,
    for arbitrary complex weights `w`. -/
lemma abel_initial (a : ℕ → ℂ) (w : ℕ → ℂ) :
    ∀ x : ℕ, 1 ≤ x →
    ∑ n ∈ Icc 1 x, a n * w n
      = (∑ n ∈ Icc 1 x, a n) * w x
        + ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m) * (w n - w (n + 1)) := by
  intro x
  induction x with
  | zero =>
    intro h0
    omega
  | succ p ih =>
    intro _
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · -- x = 1
      simp
    · -- step p → p+1
      have hstepL : Icc 1 (p + 1) = insert (p + 1) (Icc 1 p) := by
        ext m
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      have hp1 : p + 1 - 1 = p := by omega
      rw [hstepL, Finset.sum_insert (by simp), Finset.sum_insert (by simp), ih hp, hp1]
      have hstepW : Icc 1 p = insert p (Icc 1 (p - 1)) := by
        ext m
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      rw [show ∑ n ∈ Icc 1 p, (∑ m ∈ Icc 1 n, a m) * (w n - w (n + 1))
          = (∑ m ∈ Icc 1 p, a m) * (w p - w (p + 1))
            + ∑ n ∈ Icc 1 (p - 1), (∑ m ∈ Icc 1 n, a m) * (w n - w (n + 1)) from by
        rw [hstepW, Finset.sum_insert (by
          simp only [Finset.mem_Icc]
          omega), ← hstepW]]
      ring

/-! ### Duplicated verbatim from DirichletLPoleBound.lean (verified there) -/

/-- The weighted telescope: `Σ_{n≤x} n(wₙ − wₙ₊₁) = Σ_{n≤x} wₙ − x·w_{x+1}` (real). -/
lemma weighted_telescope (w : ℕ → ℝ) : ∀ x : ℕ,
    ∑ n ∈ Icc 1 x, (n : ℝ) * (w n - w (n + 1))
      = ∑ n ∈ Icc 1 x, w n - (x : ℝ) * w (x + 1) := by
  intro x
  induction x with
  | zero => simp
  | succ p ih =>
    have hstep : Icc 1 (p + 1) = insert (p + 1) (Icc 1 p) := by
      ext m
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hstep, Finset.sum_insert (by simp), Finset.sum_insert (by simp), ih]
    push_cast
    ring

/-- **The partial-sum series representation** (Siegel brick A2g-ii): for linearly
    bounded partial sums `‖A(x)‖ ≤ Cx` and `Re s > 1`,
    `Σ' n, a(n)n^{−s} = Σ' n, A(n)(n^{−s} − (n+1)^{−s})` — the boundary term
    `A(x)x^{−s}` dies and the Abel-rearranged series converges to the L-series. -/
theorem lseries_eq_tsum_abel (a : ℕ → ℂ) (C : ℝ)
    (hC : ∀ x : ℕ, ‖∑ n ∈ Icc 1 x, a n‖ ≤ C * x)
    {s : ℂ} (hs : 1 < s.re) (hsum : LSeriesSummable a s) :
    LSeries a s
      = ∑' n : ℕ, (∑ m ∈ Icc 1 n, a m) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)) := by
  -- the partial sums of the L-series along Icc 1 x
  have hterm_eq : ∀ n : ℕ, 1 ≤ n → LSeries.term a s n = a n * ((n:ℂ)) ^ (-s) := by
    intro n hn
    rw [LSeries.term_of_ne_zero (by omega), Complex.cpow_neg, div_eq_mul_inv]
  have hpartial : Tendsto (fun x : ℕ => ∑ n ∈ Icc 1 x, a n * ((n:ℂ)) ^ (-s))
      atTop (nhds (LSeries a s)) := by
    have h1 : Tendsto (fun x : ℕ => ∑ n ∈ range (x + 1), LSeries.term a s n)
        atTop (nhds (LSeries a s)) := by
      have := hsum.hasSum.tendsto_sum_nat
      exact this.comp (tendsto_add_atTop_nat 1)
    have h2 : ∀ x : ℕ, ∑ n ∈ range (x + 1), LSeries.term a s n
        = ∑ n ∈ Icc 1 x, a n * ((n:ℂ)) ^ (-s) := by
      intro x
      rw [show range (x + 1) = insert 0 (Icc 1 x) from by
        ext m
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
        omega]
      rw [Finset.sum_insert (by simp)]
      rw [LSeries.term_zero, zero_add]
      exact Finset.sum_congr rfl (fun n hn => hterm_eq n (Finset.mem_Icc.mp hn).1)
    rw [show (fun x : ℕ => ∑ n ∈ Icc 1 x, a n * ((n:ℂ)) ^ (-s))
        = (fun x : ℕ => ∑ n ∈ range (x + 1), LSeries.term a s n) from
      funext (fun x => (h2 x).symm)]
    exact h1
  -- boundary decay: A(x)·x^{−s} → 0
  have hboundary : Tendsto (fun x : ℕ => (∑ n ∈ Icc 1 x, a n) * ((x:ℂ)) ^ (-s))
      atTop (nhds 0) := by
    have hC0 : 0 ≤ C := by
      have h0 := hC 1
      have h1 : (0:ℝ) ≤ ‖∑ n ∈ Icc 1 1, a n‖ := norm_nonneg _
      have h2 : C * ((1:ℕ):ℝ) = C := by norm_num
      linarith [h0, h1, h2.le, h2.ge]
    have hbnd : ∀ x : ℕ, ‖(∑ n ∈ Icc 1 x, a n) * ((x:ℂ)) ^ (-s)‖
        ≤ C * ((x:ℝ)) ^ (1 - s.re) := by
      intro x
      rcases Nat.eq_zero_or_pos x with rfl | hx0
      · rw [show (Icc 1 0 : Finset ℕ) = ∅ from Finset.Icc_eq_empty (by omega),
          Finset.sum_empty, zero_mul, norm_zero, Nat.cast_zero,
          Real.zero_rpow (by linarith : (1:ℝ) - s.re ≠ 0), mul_zero]
      · rw [norm_mul, Complex.norm_natCast_cpow_of_pos hx0, Complex.neg_re]
        have hxr : (0:ℝ) < (x:ℝ) := by exact_mod_cast hx0
        calc ‖∑ n ∈ Icc 1 x, a n‖ * ((x:ℝ)) ^ (-s.re)
            ≤ (C * x) * ((x:ℝ)) ^ (-s.re) := by
              apply mul_le_mul_of_nonneg_right (hC x) (Real.rpow_nonneg hxr.le _)
          _ = C * ((x:ℝ)) ^ (1 - s.re) := by
              rw [show (1:ℝ) - s.re = 1 + (-s.re) by ring, Real.rpow_add hxr,
                Real.rpow_one]
              ring
    have hg0 : Tendsto (fun x : ℕ => C * ((x:ℝ)) ^ (1 - s.re)) atTop (nhds 0) := by
      have h1 : Tendsto (fun x : ℕ => ((x:ℝ)) ^ (1 - s.re)) atTop (nhds 0) := by
        have := tendsto_rpow_neg_atTop (show (0:ℝ) < s.re - 1 by linarith)
        have hcomp := this.comp tendsto_natCast_atTop_atTop
        simpa [Function.comp_def, neg_sub] using hcomp
      simpa using h1.const_mul C
    exact squeeze_zero_norm hbnd hg0
  -- Abel + limits
  have hAbel : ∀ x : ℕ, 1 ≤ x →
      ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m)
        * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))
      = ∑ n ∈ Icc 1 x, a n * ((n:ℂ)) ^ (-s)
        - (∑ n ∈ Icc 1 x, a n) * ((x:ℂ)) ^ (-s) := by
    intro x hx
    have := abel_initial a (fun n => ((n:ℂ)) ^ (-s)) x hx
    push_cast at this ⊢
    linear_combination -this
  have hlim : Tendsto (fun x : ℕ => ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m)
      * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) atTop (nhds (LSeries a s)) := by
    have heq : ∀ᶠ x : ℕ in atTop, ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m)
        * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))
        = ∑ n ∈ Icc 1 x, a n * ((n:ℂ)) ^ (-s)
          - (∑ n ∈ Icc 1 x, a n) * ((x:ℂ)) ^ (-s) := by
      filter_upwards [eventually_ge_atTop 1] with x hx
      exact hAbel x hx
    rw [Filter.tendsto_congr' heq]
    have := hpartial.sub hboundary
    simpa using this
  -- absolute convergence via the real difference kernel
  have hC0' : 0 ≤ C := by
    have h0 := hC 1
    have h1 : (0:ℝ) ≤ ‖∑ n ∈ Icc 1 1, a n‖ := norm_nonneg _
    have h2 : C * ((1:ℕ):ℝ) = C := by norm_num
    linarith [h0, h1, h2.le, h2.ge]
  have hσ0 : (0:ℝ) < s.re := by linarith
  have hsummable : Summable (fun n : ℕ => (∑ m ∈ Icc 1 n, a m)
      * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) := by
    set w : ℕ → ℝ := fun n => ((n:ℝ)) ^ (-s.re) with hw
    have hwanti : ∀ n : ℕ, 1 ≤ n → w (n + 1) ≤ w n := by
      intro n hn
      rw [hw]
      simp only
      apply Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hn) (by push_cast; linarith)
      linarith
    apply Summable.of_norm_bounded
      (g := fun n : ℕ => (C * (‖s‖ / s.re)) * ((n:ℝ) * (w n - w (n + 1))))
    · apply summable_of_sum_range_le (c := (C * (‖s‖ / s.re)) * (s.re / (s.re - 1)))
      · intro n
        rcases Nat.eq_zero_or_pos n with rfl | hn0
        · simp
        · apply mul_nonneg (by positivity)
          apply mul_nonneg (Nat.cast_nonneg n)
          linarith [hwanti n hn0]
      · intro x
        have hIcc : ∑ i ∈ range x, (C * (‖s‖ / s.re)) * ((i:ℝ) * (w i - w (i + 1)))
            = (C * (‖s‖ / s.re)) * ∑ i ∈ Icc 1 (x - 1), ((i:ℝ) * (w i - w (i + 1))) := by
          rw [Finset.mul_sum]
          rcases Nat.eq_zero_or_pos x with rfl | hx0
          · simp
          · rw [show range x = insert 0 (Icc 1 (x - 1)) from by
              ext m
              simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
              omega]
            rw [Finset.sum_insert (by simp)]
            simp
        rw [hIcc, weighted_telescope w (x - 1)]
        have htail : (0:ℝ) ≤ ((x - 1 : ℕ):ℝ) * w ((x - 1) + 1) := by
          apply mul_nonneg (Nat.cast_nonneg _)
          rw [hw]
          simp only
          positivity
        have hsums : ∑ n ∈ Icc 1 (x - 1), w n ≤ s.re / (s.re - 1) := by
          have hterm : ∀ n ∈ Icc 1 (x - 1), w n = 1 / ((n:ℝ)) ^ s.re := by
            intro n hn
            obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
            rw [hw]
            simp only
            rw [Real.rpow_neg (Nat.cast_nonneg n), one_div]
          rw [Finset.sum_congr rfl hterm]
          calc ∑ n ∈ Icc 1 (x - 1), 1 / ((n:ℝ)) ^ s.re
              ≤ ∑' n : ℕ, (1:ℝ) / ((n:ℝ)) ^ s.re :=
                Summable.sum_le_tsum _ (fun n _ => by positivity)
                  (Real.summable_one_div_nat_rpow.mpr hs)
            _ ≤ s.re / (s.re - 1) := tsum_one_div_nat_rpow_le s.re hs
        have hfac : (0:ℝ) ≤ C * (‖s‖ / s.re) := by positivity
        apply mul_le_mul_of_nonneg_left _ hfac
        linarith [hsums, htail]
    · intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp
      · rw [norm_mul]
        have h1 := hC n
        have h2 := cpow_diff_kernel_bound n hn0 s hσ0
        calc ‖∑ m ∈ Icc 1 n, a m‖ * ‖((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)‖
            ≤ (C * n) * ((‖s‖ / s.re) * ((n : ℝ) ^ (-s.re) - ((n + 1 : ℕ) : ℝ) ^ (-s.re))) := by
              apply mul_le_mul h1 h2 (norm_nonneg _)
              positivity
          _ = (C * (‖s‖ / s.re)) * ((n:ℝ) * (w n - w (n + 1))) := by
              rw [hw]
              simp only
              push_cast
              ring
  have hrange := hsummable.hasSum.tendsto_sum_nat
  have hIccrange : ∀ x : ℕ, ∑ n ∈ range x, (∑ m ∈ Icc 1 n, a m)
      * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))
      = ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m)
        * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)) := by
    intro x
    rcases Nat.eq_zero_or_pos x with rfl | hx0
    · simp
    · rw [show range x = insert 0 (Icc 1 (x - 1)) from by
        ext m
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
        omega]
      rw [Finset.sum_insert (by simp)]
      rw [show (Icc 1 0 : Finset ℕ) = ∅ from Finset.Icc_eq_empty (by omega),
        Finset.sum_empty, zero_mul, zero_add]
  have hrange' : Tendsto (fun x : ℕ => ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m)
      * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) atTop
      (nhds (∑' n : ℕ, (∑ m ∈ Icc 1 n, a m)
        * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)))) := by
    rw [show (fun x : ℕ => ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m)
        * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)))
        = (fun x : ℕ => ∑ n ∈ range x, (∑ m ∈ Icc 1 n, a m)
        * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) from
      funext (fun x => (hIccrange x).symm)]
    exact hrange
  exact (tendsto_nhds_unique hrange' hlim).symm

/-- **The Abel identity sums to ζ** (Siegel brick A2g-iii-b):
    `Σ' n·(n^{−s} − (n+1)^{−s}) = ζ(s)` on `Re s > 1` — the λ-part of the
    continuation `G` is Mathlib's `riemannZeta`, pole included. -/
theorem tsum_abel_id_eq_zeta {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, ((n:ℂ)) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)) = riemannZeta s := by
  set a : ℕ → ℂ := fun n => if n = 0 then 0 else 1 with ha
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0] at hs
    simp only [Complex.zero_re] at hs
    linarith
  have hA : ∀ x : ℕ, ∑ n ∈ Icc 1 x, a n = (x : ℂ) := by
    intro x
    have hterm : ∀ n ∈ Icc 1 x, a n = 1 := by
      intro n hn
      obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
      rw [ha]
      simp only [if_neg (by omega : ¬ n = 0)]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
      nsmul_eq_mul, mul_one]
  have hC : ∀ x : ℕ, ‖∑ n ∈ Icc 1 x, a n‖ ≤ 1 * x := by
    intro x
    rw [hA x, one_mul, Complex.norm_natCast]
  have hsummable : LSeriesSummable a s := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ hs
    intro n _
    rw [ha]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [if_neg hn]
  have hLS : LSeries a s = riemannZeta s := by
    rw [zeta_eq_tsum_one_div_nat_cpow hs, LSeries]
    apply tsum_congr
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [LSeries.term_zero]
      rw [Nat.cast_zero, Complex.zero_cpow hs0, div_zero]
    · rw [LSeries.term_of_ne_zero hn, ha]
      simp only [if_neg hn]
  have habel := lseries_eq_tsum_abel a 1 hC hs hsummable
  rw [hLS] at habel
  rw [habel]
  apply tsum_congr
  intro n
  rw [hA n]

/-- Bernoulli for negative real exponents (Siegel brick A2g-a1-i):
    `(1+u)^{−σ} ≥ 1 − σu` for `u, σ ≥ 0` — from `(1−x)eˣ ≤ 1` and `log(1+u) ≤ u`. -/
lemma rpow_neg_ge_one_sub (u σ : ℝ) (hu : 0 ≤ u) (hσ : 0 ≤ σ) :
    1 - σ * u ≤ (1 + u) ^ (-σ) := by
  by_cases hbig : 1 ≤ σ * u
  · -- trivial: LHS ≤ 0 ≤ RHS
    have h1 : (0:ℝ) < 1 + u := by linarith
    have h2 : (0:ℝ) ≤ (1 + u) ^ (-σ) := Real.rpow_nonneg h1.le _
    linarith
  · -- (1+u)^σ ≤ e^{σu} ≤ 1/(1−σu)
    push_neg at hbig
    have hsmall : σ * u < 1 := hbig
    have h1 : (0:ℝ) < 1 + u := by linarith
    have hlog : Real.log (1 + u) ≤ u := by
      have := Real.log_le_sub_one_of_pos h1
      linarith
    have hpow : (1 + u) ^ σ ≤ Real.exp (σ * u) := by
      rw [Real.rpow_def_of_pos h1]
      apply Real.exp_le_exp.mpr
      calc Real.log (1 + u) * σ ≤ u * σ := mul_le_mul_of_nonneg_right hlog hσ
        _ = σ * u := mul_comm _ _
    have hexp : Real.exp (σ * u) * (1 - σ * u) ≤ 1 := by
      have h2 := Real.add_one_le_exp (-(σ * u))
      have h3 : (0:ℝ) < Real.exp (σ * u) := Real.exp_pos _
      have h4 : Real.exp (-(σ * u)) = 1 / Real.exp (σ * u) := by
        rw [Real.exp_neg, one_div]
      rw [h4, le_div_iff₀ h3] at h2
      nlinarith [h2]
    have hposσu : (0:ℝ) < 1 - σ * u := by linarith
    have hpow0 : (0:ℝ) < (1 + u) ^ σ := Real.rpow_pos_of_pos h1 _
    rw [Real.rpow_neg h1.le, le_inv_comm₀ hposσu hpow0]
    calc (1 + u) ^ σ ≤ Real.exp (σ * u) := hpow
      _ ≤ 1 / (1 - σ * u) := by
          rw [le_div_iff₀ hposσu]
          exact hexp
      _ = (1 - σ * u)⁻¹ := one_div _

/-- **The kernel decay bound** (Siegel brick A2g-a1): for `σ ≥ 0` and `n ≥ 1`,
    `n^{−σ} − (n+1)^{−σ} ≤ σ·n^{−σ−1}` — the uniform-in-window majorant. -/
lemma rpow_diff_le (n : ℕ) (hn : 1 ≤ n) (σ : ℝ) (hσ : 0 ≤ σ) :
    (n : ℝ) ^ (-σ) - ((n + 1 : ℕ) : ℝ) ^ (-σ) ≤ σ * (n : ℝ) ^ (-σ - 1) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hu : (0:ℝ) ≤ 1 / n := by positivity
  have hb := rpow_neg_ge_one_sub (1 / n) σ hu hσ
  have hsplit : ((n + 1 : ℕ) : ℝ) = (n : ℝ) * (1 + 1 / n) := by
    push_cast
    field_simp
  have hmul : ((n + 1 : ℕ) : ℝ) ^ (-σ) = (n : ℝ) ^ (-σ) * (1 + 1 / n) ^ (-σ) := by
    rw [hsplit, Real.mul_rpow hn0.le (by positivity)]
  rw [hmul]
  have hnσ : (0:ℝ) < (n : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hn0 _
  have hkey : (n : ℝ) ^ (-σ) - (n : ℝ) ^ (-σ) * (1 + 1 / n) ^ (-σ)
      ≤ (n : ℝ) ^ (-σ) * (σ * (1 / n)) := by
    have h1 : (n : ℝ) ^ (-σ) * (1 - σ * (1 / n)) ≤ (n : ℝ) ^ (-σ) * (1 + 1 / n) ^ (-σ) :=
      mul_le_mul_of_nonneg_left hb hnσ.le
    nlinarith [h1]
  calc (n : ℝ) ^ (-σ) - (n : ℝ) ^ (-σ) * (1 + 1 / n) ^ (-σ)
      ≤ (n : ℝ) ^ (-σ) * (σ * (1 / n)) := hkey
    _ = σ * ((n : ℝ) ^ (-σ) * (n : ℝ) ^ (-(1:ℝ))) := by
        rw [Real.rpow_neg_one]
        field_simp
    _ = σ * (n : ℝ) ^ (-σ - 1) := by
        rw [← Real.rpow_add hn0]
        ring_nf

/-- **The E-series is differentiable on `Re s > 9/10`** (Siegel brick A2g-a2): with
    `|E(n)| ≤ C·n^{3/4}(1+log n)` and `E(0) = 0`, the series
    `s ↦ Σ' E(n)(n^{−s} − (n+1)^{−s})` is differentiable at every point of the
    half-plane — the analytic error part of the continuation `G`, via Mathlib's
    Weierstrass M-test `differentiableOn_tsum_of_summable_norm` on windows. -/
theorem eseries_differentiableAt (E : ℕ → ℝ) (C : ℝ) (hC0 : 0 ≤ C) (hE0 : E 0 = 0)
    (hE : ∀ n : ℕ, 1 ≤ n → |E n| ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)))
    (s₀ : ℂ) (hs₀ : 9/10 < s₀.re) :
    DifferentiableAt ℂ (fun s => ∑' n : ℕ,
      ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) s₀ := by
  set σ₀ : ℝ := (9/10 + s₀.re) / 2 with hσ₀
  have hσ₀1 : 9/10 < σ₀ := by rw [hσ₀]; linarith
  have hσ₀2 : σ₀ < s₀.re := by rw [hσ₀]; linarith
  set R : ℝ := ‖s₀‖ + 1 with hR
  have hR0 : 0 < R := by
    rw [hR]
    have := norm_nonneg s₀
    linarith
  set U : Set ℂ := {s : ℂ | σ₀ < s.re} ∩ Metric.ball 0 R with hU
  have hUopen : IsOpen U := by
    apply IsOpen.inter
    · exact isOpen_lt continuous_const Complex.continuous_re
    · exact Metric.isOpen_ball
  have hs₀U : s₀ ∈ U := by
    rw [hU]
    constructor
    · exact hσ₀2
    · rw [Metric.mem_ball, dist_zero_right, hR]
      linarith
  -- the majorant
  set u : ℕ → ℝ := fun n => if n = 0 then 0 else
    C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) * (R * ((n:ℝ)) ^ (-σ₀ - 1)) with hu
  have hmajsum : Summable (fun n : ℕ => (9 * C * R) * (1 / ((n:ℝ)) ^ (σ₀ + 1/8))) :=
    Summable.mul_left _ (Real.summable_one_div_nat_rpow.mpr (by linarith))
  have husum : Summable u := by
    apply Summable.of_nonneg_of_le _ _ hmajsum
    · intro n
      rw [hu]
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · simp only [if_neg hn]
        have hn1 : (1:ℝ) ≤ (n:ℝ) := by
          have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
          exact_mod_cast this
        have hlog0 : (0:ℝ) ≤ 1 + Real.log n := by
          have := Real.log_nonneg hn1
          linarith
        positivity
    · intro n
      rcases eq_or_ne n 0 with rfl | hn
      · rw [hu]
        simp only [if_pos rfl]
        positivity
      · rw [hu]
        simp only [if_neg hn]
        have hn1 : (1:ℝ) ≤ (n:ℝ) := by
          have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
          exact_mod_cast this
        have hn0 : (0:ℝ) < (n:ℝ) := by linarith
        -- (1 + log n) ≤ 9 n^{1/8}
        have hlogbound : 1 + Real.log n ≤ 9 * ((n:ℝ)) ^ ((1:ℝ)/8) := by
          have h1 : Real.log n ≤ ((n:ℝ)) ^ ((1:ℝ)/8) / (1/8) :=
            Real.log_le_rpow_div hn0.le (by norm_num)
          have h2 : ((n:ℝ)) ^ ((1:ℝ)/8) / (1/8) = 8 * ((n:ℝ)) ^ ((1:ℝ)/8) := by ring
          have h3 : (1:ℝ) ≤ ((n:ℝ)) ^ ((1:ℝ)/8) :=
            Real.one_le_rpow hn1 (by norm_num)
          linarith [h1, h2.le, h2.ge, h3]
        -- collect exponents: 3/4 + 1/8 − σ₀ − 1 = −(σ₀ + 1/8)
        have hcollect : ((n:ℝ)) ^ ((3:ℝ)/4) * ((n:ℝ)) ^ ((1:ℝ)/8) * ((n:ℝ)) ^ (-σ₀ - 1)
            = ((n:ℝ)) ^ (-(σ₀ + 1/8)) := by
          rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
          ring_nf
        have hfinal : C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) * (R * ((n:ℝ)) ^ (-σ₀ - 1))
            ≤ (9 * C * R) * ((n:ℝ)) ^ (-(σ₀ + 1/8)) := by
          calc C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) * (R * ((n:ℝ)) ^ (-σ₀ - 1))
              ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (9 * ((n:ℝ)) ^ ((1:ℝ)/8))) * (R * ((n:ℝ)) ^ (-σ₀ - 1)) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                apply mul_le_mul_of_nonneg_left _ hC0
                apply mul_le_mul_of_nonneg_left hlogbound (by positivity)
            _ = (9 * C * R) * (((n:ℝ)) ^ ((3:ℝ)/4) * ((n:ℝ)) ^ ((1:ℝ)/8) * ((n:ℝ)) ^ (-σ₀ - 1)) := by
                ring
            _ = (9 * C * R) * ((n:ℝ)) ^ (-(σ₀ + 1/8)) := by rw [hcollect]
        calc C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) * (R * ((n:ℝ)) ^ (-σ₀ - 1))
            ≤ (9 * C * R) * ((n:ℝ)) ^ (-(σ₀ + 1/8)) := hfinal
          _ = (9 * C * R) * (1 / ((n:ℝ)) ^ (σ₀ + 1/8)) := by
              rw [Real.rpow_neg hn0.le]
              ring
  -- pointwise bounds on U
  have hbound : ∀ (n : ℕ) (w : ℂ), w ∈ U →
      ‖((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-w) - (((n + 1 : ℕ):ℂ)) ^ (-w))‖ ≤ u n := by
    intro n w hw
    obtain ⟨hwre, hwball⟩ := hw
    have hwre' : σ₀ < w.re := hwre
    have hwσ : (0:ℝ) < w.re := by linarith
    have hwnorm : ‖w‖ ≤ R := by
      rw [Metric.mem_ball, dist_zero_right] at hwball
      linarith
    rcases eq_or_ne n 0 with rfl | hn
    · rw [hE0]
      simp only [Complex.ofReal_zero, zero_mul, norm_zero, hu, if_pos rfl]
      exact le_refl 0
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hn1r : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
      have hn0 : (0:ℝ) < (n:ℝ) := by linarith
      rw [hu]
      simp only [if_neg hn]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 := hE n hn1
      have h2 := cpow_diff_kernel_bound n hn1 w hwσ
      have h3 := rpow_diff_le n hn1 w.re hwσ.le
      have hker : ‖((n:ℂ)) ^ (-w) - (((n + 1 : ℕ):ℂ)) ^ (-w)‖ ≤ R * ((n:ℝ)) ^ (-σ₀ - 1) := by
        have hstep : (‖w‖ / w.re) * ((n : ℝ) ^ (-w.re) - ((n + 1 : ℕ) : ℝ) ^ (-w.re))
            ≤ (‖w‖ / w.re) * (w.re * (n : ℝ) ^ (-w.re - 1)) := by
          apply mul_le_mul_of_nonneg_left h3 (by positivity)
        have hsimp : (‖w‖ / w.re) * (w.re * (n : ℝ) ^ (-w.re - 1))
            = ‖w‖ * (n : ℝ) ^ (-w.re - 1) := by
          field_simp
        have hmono : ((n:ℝ)) ^ (-w.re - 1) ≤ ((n:ℝ)) ^ (-σ₀ - 1) := by
          apply Real.rpow_le_rpow_of_exponent_le hn1r
          linarith
        calc ‖((n:ℂ)) ^ (-w) - (((n + 1 : ℕ):ℂ)) ^ (-w)‖
            ≤ (‖w‖ / w.re) * ((n : ℝ) ^ (-w.re) - ((n + 1 : ℕ) : ℝ) ^ (-w.re)) := h2
          _ ≤ ‖w‖ * ((n:ℝ)) ^ (-w.re - 1) := by
              rw [← hsimp]
              exact hstep
          _ ≤ R * ((n:ℝ)) ^ (-σ₀ - 1) := by
              apply mul_le_mul hwnorm hmono (by positivity) hR0.le
      have hEnn : (0:ℝ) ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
        have hlog0 : (0:ℝ) ≤ 1 + Real.log n := by
          have := Real.log_nonneg hn1r
          linarith
        positivity
      calc |E n| * ‖((n:ℂ)) ^ (-w) - (((n + 1 : ℕ):ℂ)) ^ (-w)‖
          ≤ (C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n))) * (R * ((n:ℝ)) ^ (-σ₀ - 1)) :=
            mul_le_mul h1 hker (norm_nonneg _) hEnn
        _ = C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) * (R * ((n:ℝ)) ^ (-σ₀ - 1)) := by
            ring
  -- termwise differentiability on U
  have hdiff : ∀ n : ℕ, DifferentiableOn ℂ
      (fun s => ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) U := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [hE0]
      simp only [Complex.ofReal_zero, zero_mul]
      exact differentiableOn_const 0
    · have hn0 : ((n:ℂ)) ≠ 0 := by exact_mod_cast hn
      have hn10 : (((n + 1 : ℕ):ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      apply DifferentiableOn.const_mul
      apply DifferentiableOn.sub
      · exact ((Differentiable.neg differentiable_id).const_cpow
          (Or.inl hn0)).differentiableOn
      · exact ((Differentiable.neg differentiable_id).const_cpow
          (Or.inl hn10)).differentiableOn
  -- assemble
  have hDon := Complex.differentiableOn_tsum_of_summable_norm husum hdiff hUopen hbound
  exact (hDon.differentiableAt (hUopen.mem_nhds hs₀U))

/-- Linear-growth sequences give absolutely convergent Abel series (A2g-c-i):
    the summability half of `lseries_eq_tsum_abel`, exposed standalone. -/
lemma abel_tsum_summable (b : ℕ → ℂ) (C : ℝ)
    (hb : ∀ n : ℕ, ‖b n‖ ≤ C * n)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => b n * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) := by
  have hC0 : 0 ≤ C := by
    have h0 := hb 1
    have h1 : (0:ℝ) ≤ ‖b 1‖ := norm_nonneg _
    have h2 : C * ((1:ℕ):ℝ) = C := by norm_num
    linarith [h0, h1, h2.le, h2.ge]
  have hσ0 : (0:ℝ) < s.re := by linarith
  set w : ℕ → ℝ := fun n => ((n:ℝ)) ^ (-s.re) with hw
  have hwanti : ∀ n : ℕ, 1 ≤ n → w (n + 1) ≤ w n := by
    intro n hn
    rw [hw]
    simp only
    apply Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hn) (by push_cast; linarith)
    linarith
  apply Summable.of_norm_bounded
    (g := fun n : ℕ => (C * (‖s‖ / s.re)) * ((n:ℝ) * (w n - w (n + 1))))
  · apply summable_of_sum_range_le (c := (C * (‖s‖ / s.re)) * (s.re / (s.re - 1)))
    · intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp
      · apply mul_nonneg (by positivity)
        apply mul_nonneg (Nat.cast_nonneg n)
        linarith [hwanti n hn0]
    · intro x
      have hIcc : ∑ i ∈ range x, (C * (‖s‖ / s.re)) * ((i:ℝ) * (w i - w (i + 1)))
          = (C * (‖s‖ / s.re)) * ∑ i ∈ Icc 1 (x - 1), ((i:ℝ) * (w i - w (i + 1))) := by
        rw [Finset.mul_sum]
        rcases Nat.eq_zero_or_pos x with rfl | hx0
        · simp
        · rw [show range x = insert 0 (Icc 1 (x - 1)) from by
            ext m
            simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
            omega]
          rw [Finset.sum_insert (by simp)]
          simp
      rw [hIcc, weighted_telescope w (x - 1)]
      have htail : (0:ℝ) ≤ ((x - 1 : ℕ):ℝ) * w ((x - 1) + 1) := by
        apply mul_nonneg (Nat.cast_nonneg _)
        rw [hw]
        simp only
        positivity
      have hsums : ∑ n ∈ Icc 1 (x - 1), w n ≤ s.re / (s.re - 1) := by
        have hterm : ∀ n ∈ Icc 1 (x - 1), w n = 1 / ((n:ℝ)) ^ s.re := by
          intro n hn
          obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
          rw [hw]
          simp only
          rw [Real.rpow_neg (Nat.cast_nonneg n), one_div]
        rw [Finset.sum_congr rfl hterm]
        calc ∑ n ∈ Icc 1 (x - 1), 1 / ((n:ℝ)) ^ s.re
            ≤ ∑' n : ℕ, (1:ℝ) / ((n:ℝ)) ^ s.re :=
              Summable.sum_le_tsum _ (fun n _ => by positivity)
                (Real.summable_one_div_nat_rpow.mpr hs)
          _ ≤ s.re / (s.re - 1) := tsum_one_div_nat_rpow_le s.re hs
      have hfac : (0:ℝ) ≤ C * (‖s‖ / s.re) := by positivity
      apply mul_le_mul_of_nonneg_left _ hfac
      linarith [hsums, htail]
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · have hb0 : ‖b 0‖ = 0 := by
        have h := hb 0
        have h2 : C * ((0:ℕ):ℝ) = 0 := by norm_num
        have := norm_nonneg (b 0)
        linarith [h, h2.le, h2.ge]
      rw [norm_mul, hb0, zero_mul]
      have hrhs : (C * (‖s‖ / s.re)) * (((0:ℕ):ℝ) * (w 0 - w (0 + 1))) = 0 := by
        norm_num
      rw [hrhs]
    · rw [norm_mul]
      have h1 := hb n
      have h2 := cpow_diff_kernel_bound n hn0 s hσ0
      calc ‖b n‖ * ‖((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)‖
          ≤ (C * n) * ((‖s‖ / s.re) * ((n : ℝ) ^ (-s.re) - ((n + 1 : ℕ) : ℝ) ^ (-s.re))) := by
            apply mul_le_mul h1 h2 (norm_nonneg _)
            positivity
        _ = (C * (‖s‖ / s.re)) * ((n:ℝ) * (w n - w (n + 1))) := by
            rw [hw]
            simp only
            push_cast
            ring

/-- **The continuation identity on `Re s > 1`** (Siegel brick A2g-c): with
    `A(n) = λn + E(n)` (linear main term + controlled error), the L-series equals
    `λ·ζ(s) + Σ' E(n)Δₙ(s)` — the function `G` that continues it to `Re > 9/10`. -/
theorem lseries_eq_G (a : ℕ → ℂ) (lam : ℝ) (E : ℕ → ℝ) (C : ℝ)
    (hAE : ∀ n : ℕ, ∑ m ∈ Icc 1 n, a m = (lam * n : ℝ) + E n)
    (hEb : ∀ n : ℕ, |E n| ≤ C * n)
    {s : ℂ} (hs : 1 < s.re) (hsum : LSeriesSummable a s) :
    LSeries a s = (lam : ℂ) * riemannZeta s
      + ∑' n : ℕ, ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)) := by
  have hC0 : 0 ≤ C := by
    have h0 := hEb 1
    have h1 : (0:ℝ) ≤ |E 1| := abs_nonneg _
    have h2 : C * ((1:ℕ):ℝ) = C := by norm_num
    linarith [h0, h1, h2.le, h2.ge]
  -- the A-partial sums are linearly bounded
  have hA : ∀ x : ℕ, ‖∑ n ∈ Icc 1 x, a n‖ ≤ (|lam| + C) * x := by
    intro x
    rw [hAE x]
    calc ‖((lam * x : ℝ) : ℂ) + ((E x : ℝ) : ℂ)‖
        ≤ ‖((lam * x : ℝ) : ℂ)‖ + ‖((E x : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = |lam * x| + |E x| := by
          rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ |lam| * x + C * x := by
          apply add_le_add
          · rw [abs_mul, Nat.abs_cast]
          · exact hEb x
      _ = (|lam| + C) * x := by ring
  rw [lseries_eq_tsum_abel a (|lam| + C) hA hs hsum]
  -- split the tsum
  have hsplit : ∀ n : ℕ, (∑ m ∈ Icc 1 n, a m) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))
      = (lam : ℂ) * (((n:ℂ)) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)))
        + ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)) := by
    intro n
    rw [hAE n]
    push_cast
    ring
  rw [tsum_congr hsplit]
  -- summabilities for tsum_add
  have hid : Summable (fun n : ℕ =>
      ((n:ℂ)) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) := by
    apply abel_tsum_summable (fun n : ℕ => ((n:ℂ))) 1 _ hs
    intro n
    rw [Complex.norm_natCast, one_mul]
  have hsum1 : Summable (fun n : ℕ => (lam : ℂ)
      * (((n:ℂ)) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)))) :=
    hid.mul_left ((lam : ℝ) : ℂ)
  have hsum2 : Summable (fun n : ℕ =>
      ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) := by
    apply abel_tsum_summable (fun n : ℕ => ((E n : ℝ) : ℂ)) C _ hs
    intro n
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hEb n
  rw [hsum1.tsum_add hsum2, tsum_mul_left, tsum_abel_id_eq_zeta hs]

/-- Identity-theorem step on a convex open piece: agreement near one interior point
    propagates to the whole piece. -/
lemma eqOn_of_convex_piece (f g : ℂ → ℂ) (V : Set ℂ) (hVo : IsOpen V)
    (hVc : Convex ℝ V)
    (hf : DifferentiableOn ℂ f V) (hg : DifferentiableOn ℂ g V)
    (z₀ : ℂ) (hz₀ : z₀ ∈ V) (hseed : f =ᶠ[nhds z₀] g) :
    Set.EqOn f g V := by
  have hfa : AnalyticOnNhd ℂ f V := hf.analyticOnNhd hVo
  have hga : AnalyticOnNhd ℂ g V := hg.analyticOnNhd hVo
  exact hfa.eqOn_of_preconnected_of_eventuallyEq hga hVc.isPreconnected hz₀ hseed

/-- **The identity theorem on the slit half-plane** (Siegel brick A2h-iii): two
    functions differentiable on `{Re > 9/10} ∖ {1}` that agree on `{Re > 1}` agree
    everywhere on the slit half-plane — by chaining through overlapping convex pieces
    (no slit-plane connectivity needed). -/
theorem eqOn_slit_halfplane (f g : ℂ → ℂ)
    (hf : ∀ s : ℂ, 9/10 < s.re → s ≠ 1 → DifferentiableAt ℂ f s)
    (hg : ∀ s : ℂ, 9/10 < s.re → s ≠ 1 → DifferentiableAt ℂ g s)
    (heq : ∀ s : ℂ, 1 < s.re → f s = g s)
    (s₀ : ℂ) (h₀re : 9/10 < s₀.re) (h₀ne : s₀ ≠ 1) : f s₀ = g s₀ := by
  -- the convex pieces
  set V₁ : Set ℂ := {s : ℂ | 9/10 < s.re ∧ 0 < s.im} with hV₁
  set V₂ : Set ℂ := {s : ℂ | 9/10 < s.re ∧ s.im < 0} with hV₂
  set V₃ : Set ℂ := {s : ℂ | 1 < s.re} with hV₃
  set V₄ : Set ℂ := {s : ℂ | 9/10 < s.re ∧ s.re < 1} with hV₄
  -- openness
  have hV₁o : IsOpen V₁ :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hV₂o : IsOpen V₂ :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hV₃o : IsOpen V₃ := isOpen_lt continuous_const Complex.continuous_re
  have hV₄o : IsOpen V₄ :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  -- convexity: intersections of re/im half-spaces
  have hV₁c : Convex ℝ V₁ :=
    (convex_halfSpace_re_gt (9/10)).inter (convex_halfSpace_im_gt 0)
  have hV₂c : Convex ℝ V₂ :=
    (convex_halfSpace_re_gt (9/10)).inter (convex_halfSpace_im_lt 0)
  have hV₃c : Convex ℝ V₃ := convex_halfSpace_re_gt 1
  have hV₄c : Convex ℝ V₄ :=
    (convex_halfSpace_re_gt (9/10)).inter (convex_halfSpace_re_lt 1)
  -- every piece avoids 1 and sits in the domain
  have hne1 : ∀ {V : Set ℂ}, (∀ s ∈ V, 9/10 < s.re ∧ s ≠ 1) →
      DifferentiableOn ℂ f V ∧ DifferentiableOn ℂ g V := by
    intro V hV
    constructor
    · intro s hs
      exact ((hf s (hV s hs).1 (hV s hs).2).differentiableWithinAt)
    · intro s hs
      exact ((hg s (hV s hs).1 (hV s hs).2).differentiableWithinAt)
  have hdom₁ : ∀ s ∈ V₁, 9/10 < s.re ∧ s ≠ 1 := by
    rintro s ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro hc
    rw [hc] at h2
    simp at h2
  have hdom₂ : ∀ s ∈ V₂, 9/10 < s.re ∧ s ≠ 1 := by
    rintro s ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro hc
    rw [hc] at h2
    simp at h2
  have hdom₃ : ∀ s ∈ V₃, 9/10 < s.re ∧ s ≠ 1 := by
    intro s hs
    have h1 : 1 < s.re := hs
    refine ⟨by linarith, ?_⟩
    intro hc
    rw [hc] at h1
    simp at h1
  have hdom₄ : ∀ s ∈ V₄, 9/10 < s.re ∧ s ≠ 1 := by
    rintro s ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro hc
    rw [hc] at h2
    simp at h2
  obtain ⟨hf₁, hg₁⟩ := hne1 hdom₁
  obtain ⟨hf₂, hg₂⟩ := hne1 hdom₂
  obtain ⟨hf₄, hg₄⟩ := hne1 hdom₄
  -- seed on V₃ overlaps: 2 + i ∈ V₁ ∩ V₃, 2 − i ∈ V₂ ∩ V₃
  have hseed₁ : f =ᶠ[nhds (2 + Complex.I)] g := by
    have hmem : (2 + Complex.I) ∈ V₃ := by
      show (1:ℝ) < (2 + Complex.I).re
      simp
    filter_upwards [hV₃o.mem_nhds hmem] with w hw
    exact heq w hw
  have hseed₂ : f =ᶠ[nhds (2 - Complex.I)] g := by
    have hmem : (2 - Complex.I) ∈ V₃ := by
      show (1:ℝ) < (2 - Complex.I).re
      simp
    filter_upwards [hV₃o.mem_nhds hmem] with w hw
    exact heq w hw
  -- V₁, V₂ agreement
  have hEq₁ : Set.EqOn f g V₁ := by
    apply eqOn_of_convex_piece f g V₁ hV₁o hV₁c hf₁ hg₁ (2 + Complex.I) _ hseed₁
    constructor
    · show (9:ℝ)/10 < (2 + Complex.I).re
      simp
      norm_num
    · show (0:ℝ) < (2 + Complex.I).im
      simp
  have hEq₂ : Set.EqOn f g V₂ := by
    apply eqOn_of_convex_piece f g V₂ hV₂o hV₂c hf₂ hg₂ (2 - Complex.I) _ hseed₂
    constructor
    · show (9:ℝ)/10 < (2 - Complex.I).re
      simp
      norm_num
    · show (2 - Complex.I).im < 0
      simp
  -- V₄ agreement, seeded from V₁ at 19/20 + i/2
  have hmid : ((19:ℝ)/20 + Complex.I * (1/2)) ∈ V₁ ∩ V₄ := by
    constructor
    · constructor
      · show (9:ℝ)/10 < ((19:ℝ)/20 + Complex.I * (1/2)).re
        simp
        norm_num
      · show (0:ℝ) < ((19:ℝ)/20 + Complex.I * (1/2)).im
        simp
    · constructor
      · show (9:ℝ)/10 < ((19:ℝ)/20 + Complex.I * (1/2)).re
        simp
        norm_num
      · show ((19:ℝ)/20 + Complex.I * (1/2)).re < 1
        simp
        norm_num
  have hseed₄ : f =ᶠ[nhds ((19:ℝ)/20 + Complex.I * (1/2))] g := by
    filter_upwards [hV₁o.mem_nhds hmid.1] with w hw
    exact hEq₁ hw
  have hEq₄ : Set.EqOn f g V₄ := by
    apply eqOn_of_convex_piece f g V₄ hV₄o hV₄c hf₄ hg₄ _ hmid.2 hseed₄
  -- conclude by cases on s₀
  rcases lt_trichotomy s₀.re 1 with hlt | heq1 | hgt
  · exact hEq₄ ⟨h₀re, hlt⟩
  · -- re = 1: im ≠ 0
    have him : s₀.im ≠ 0 := by
      intro hc
      apply h₀ne
      apply Complex.ext
      · rw [heq1]
        simp
      · rw [hc]
        simp
    rcases lt_or_gt_of_ne him with hneg | hpos
    · exact hEq₂ ⟨h₀re, hneg⟩
    · exact hEq₁ ⟨h₀re, hpos⟩
  · exact heq s₀ hgt

/-- Complex log-Taylor remainder (A2h-i-a): for real `0 ≤ z ≤ 1/2`,
    `|log(1+z) − z| ≤ z²`. -/
lemma log_taylor_remainder (z : ℝ) (h0 : 0 ≤ z) (h1 : z ≤ 1/2) :
    |Real.log (1 + z) - z| ≤ z ^ 2 := by
  have h1z : (0:ℝ) < 1 + z := by linarith
  -- upper: log(1+z) ≤ z
  have hup : Real.log (1 + z) ≤ z := by
    have := Real.log_le_sub_one_of_pos h1z
    linarith
  -- lower: log(1+z) ≥ z − z² via log(1+z) = −log(1/(1+z)) and log(1/(1+z)) ≤ 1/(1+z) − 1
  have hlow : z - z ^ 2 ≤ Real.log (1 + z) := by
    have hinv : Real.log (1 / (1 + z)) ≤ 1 / (1 + z) - 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 / (1 + z) by positivity)
      linarith
    have hneg : Real.log (1 / (1 + z)) = -Real.log (1 + z) := by
      rw [one_div, Real.log_inv]
    rw [hneg] at hinv
    have halg : 1 / (1 + z) - 1 = -z / (1 + z) := by
      field_simp
      ring
    rw [halg] at hinv
    -- −log(1+z) ≤ −z/(1+z) ⟹ log(1+z) ≥ z/(1+z) ≥ z − z²
    have hfrac : z - z ^ 2 ≤ z / (1 + z) := by
      rw [le_div_iff₀ h1z]
      nlinarith [h0, h1]
    have : z / (1 + z) ≤ Real.log (1 + z) := by
      have := neg_le_neg hinv
      simp only [neg_neg] at this
      calc z / (1 + z) = -(-z / (1 + z)) := by ring
        _ ≤ Real.log (1 + z) := by linarith [hinv]
    linarith
  rw [abs_le]
  constructor
  · linarith
  · nlinarith [hup, h0]

/-- **Second-order cpow Taylor bound** (Siegel brick A2h-i): for `w : ℂ` and real
    `0 ≤ z ≤ 1/2` with `‖w‖ ≤ W` and `W*z ≤ 1`,
    `‖(1+z)^w − 1 − wz‖ ≤ 4(W+1)²z²` — the engine of the ζ-truncation defect. -/
lemma cpow_taylor_two (w : ℂ) (z : ℝ) (h0 : 0 ≤ z) (h1 : z ≤ 1/2)
    (W : ℝ) (hW : ‖w‖ ≤ W) (hWz : W * z ≤ 1) :
    ‖((1 + z : ℝ) : ℂ) ^ w - 1 - w * z‖ ≤ 4 * (W + 1) ^ 2 * z ^ 2 := by
  have hW0 : 0 ≤ W := le_trans (norm_nonneg w) hW
  have h1z : (0:ℝ) < 1 + z := by linarith
  -- (1+z)^w = exp(w log(1+z))
  have hcpow : ((1 + z : ℝ) : ℂ) ^ w = Complex.exp (w * Real.log (1 + z)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ne_of_gt h1z)]
    congr 1
    rw [Complex.ofReal_log h1z.le]
    ring
  rw [hcpow]
  -- split: exp(wL) − 1 − wz = [exp(wL) − 1 − wL] + w(L − z)
  set L : ℝ := Real.log (1 + z) with hL
  have hLz : |L - z| ≤ z ^ 2 := log_taylor_remainder z h0 h1
  have hLb : |L| ≤ z := by
    have h2 : 0 ≤ L := Real.log_nonneg (by linarith)
    have h3 : L ≤ z := by
      have := Real.log_le_sub_one_of_pos h1z
      rw [hL]
      linarith
    rw [abs_of_nonneg h2]
    exact h3
  have hwL : ‖w * (L : ℂ)‖ ≤ W * z := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul hW hLb (abs_nonneg _) hW0
  -- ‖exp(u) − 1 − u‖ ≤ ‖u‖² for ‖u‖ ≤ 1
  have hexp2 : ‖Complex.exp (w * L) - 1 - w * L‖ ≤ ‖w * (L : ℂ)‖ ^ 2 := by
    have := Complex.norm_exp_sub_one_sub_id_le (x := w * (L : ℂ)) (by
      calc ‖w * (L : ℂ)‖ ≤ W * z := hwL
        _ ≤ 1 := hWz)
    exact this
  have hsplit : Complex.exp (w * L) - 1 - w * z
      = (Complex.exp (w * L) - 1 - w * L) + w * ((L : ℂ) - z) := by
    ring
  rw [hsplit]
  have hterm2 : ‖w * ((L : ℂ) - z)‖ ≤ W * z ^ 2 := by
    rw [norm_mul, show ((L : ℂ) - (z : ℝ)) = (((L - z : ℝ)) : ℂ) from by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hW hLz (abs_nonneg _) hW0
  have hsq : ‖w * (L : ℂ)‖ ^ 2 ≤ (W * z) ^ 2 := by
    have h := norm_nonneg (w * (L : ℂ))
    nlinarith [hwL, h]
  calc ‖(Complex.exp (w * L) - 1 - w * L) + w * ((L : ℂ) - z)‖
      ≤ ‖Complex.exp (w * L) - 1 - w * L‖ + ‖w * ((L : ℂ) - z)‖ := norm_add_le _ _
    _ ≤ ‖w * (L : ℂ)‖ ^ 2 + W * z ^ 2 := add_le_add hexp2 hterm2
    _ ≤ (W * z) ^ 2 + W * z ^ 2 := by linarith [hsq]
    _ ≤ 4 * (W + 1) ^ 2 * z ^ 2 := by
        nlinarith [hW0, sq_nonneg z, sq_nonneg W, mul_nonneg hW0 (sq_nonneg z)]

/-- **The second-order Euler–Maclaurin kernel bound** (Siegel brick A2h-ii-α), in the
    `(s−1)`-cleared form: for `n ≥ 2`, `‖1−s‖ ≤ W`, `W/n ≤ 1`:
    `‖(s−1)n^{−s} − (n^{1−s} − (n+1)^{1−s})‖ ≤ 4(W+1)²·n^{−2}·n^{1−Re s}`. -/
lemma euler_maclaurin_kernel (s : ℂ) (n : ℕ) (hn2 : 2 ≤ n)
    (W : ℝ) (hW : ‖1 - s‖ ≤ W) (hWn : W * (1 / n) ≤ 1) :
    ‖(s - 1) * ((n:ℂ)) ^ (-s) - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))‖
      ≤ 4 * (W + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - s.re) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by
    have : (0:ℕ) < n := by omega
    exact_mod_cast this
  have hnc0 : ((n:ℂ)) ≠ 0 := by
    exact_mod_cast (by omega : n ≠ 0)
  have hz1 : (1:ℝ) / n ≤ 1/2 := by
    rw [div_le_div_iff₀ hn0 (by norm_num)]
    push_cast
    linarith [show (2:ℝ) ≤ (n:ℝ) from by exact_mod_cast hn2]
  have hz0 : (0:ℝ) ≤ 1 / n := by positivity
  -- (n+1)^{1−s} = n^{1−s}·(1+1/n)^{1−s}
  have hsplit : (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)
      = ((n:ℂ)) ^ ((1:ℂ) - s) * (((1 + 1/(n:ℝ) : ℝ)) : ℂ) ^ ((1:ℂ) - s) := by
    have hy0 : (0:ℝ) ≤ 1 + 1/(n:ℝ) := by positivity
    have hb : (((n + 1 : ℕ):ℂ)) = (((n:ℝ) : ℂ)) * (((1 + 1/(n:ℝ) : ℝ)) : ℂ) := by
      push_cast
      field_simp
    rw [hb, Complex.mul_cpow_ofReal_nonneg hn0.le hy0]
    norm_cast
  rw [hsplit]
  -- factor: LHS = n^{1−s}·[(1+1/n)^{1−s} − 1 − (1−s)(1/n)]
  have hpow : ((n:ℂ)) ^ ((1:ℂ) - s) = ((n:ℂ)) * ((n:ℂ)) ^ (-s) := by
    rw [show (1:ℂ) - s = 1 + (-s) by ring, Complex.cpow_add _ _ hnc0, Complex.cpow_one]
  have hnz : ((n:ℂ)) * ((1/(n:ℝ) : ℝ) : ℂ) = 1 := by
    have hc : ((1/(n:ℝ) : ℝ) : ℂ) = 1 / ((n:ℂ)) := by push_cast; ring
    rw [hc, mul_one_div, div_self hnc0]
  have hfactor : (s - 1) * ((n:ℂ)) ^ (-s)
      - (((n:ℂ)) ^ ((1:ℂ) - s) - ((n:ℂ)) ^ ((1:ℂ) - s) * (((1 + 1/(n:ℝ) : ℝ)) : ℂ) ^ ((1:ℂ) - s))
      = ((n:ℂ)) ^ ((1:ℂ) - s)
        * ((((1 + 1/(n:ℝ) : ℝ)) : ℂ) ^ ((1:ℂ) - s) - 1 - ((1:ℂ) - s) * ((1/(n:ℝ) : ℝ) : ℂ)) := by
    rw [hpow]
    linear_combination (((1:ℂ) - s) * ((n:ℂ)) ^ (-s)) * hnz
  rw [hfactor, norm_mul]
  have hnorm1 : ‖((n:ℂ)) ^ ((1:ℂ) - s)‖ = ((n:ℝ)) ^ (1 - s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    simp [Complex.sub_re]
  rw [hnorm1]
  have hbr := cpow_taylor_two ((1:ℂ) - s) (1/(n:ℝ)) hz0 hz1 W hW hWn
  calc ((n:ℝ)) ^ (1 - s.re)
        * ‖(((1 + 1/(n:ℝ) : ℝ)) : ℂ) ^ ((1:ℂ) - s) - 1 - ((1:ℂ) - s) * ((1/(n:ℝ) : ℝ) : ℂ)‖
      ≤ ((n:ℝ)) ^ (1 - s.re) * (4 * (W + 1) ^ 2 * (1/(n:ℝ)) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hn0.le _)
        have hcast : ((1:ℂ) - s) * ((1/(n:ℝ) : ℝ) : ℂ)
            = ((1:ℂ) - s) * (1/(n:ℝ) : ℝ) := by norm_num
        rw [hcast]
        exact hbr
    _ = 4 * (W + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - s.re) := by ring

/-- Reverse Bernoulli (A2h-ii-β1): `(1+θu)(1−u)^θ ≤ 1` for `θ ≥ 0`, `0 ≤ u < 1` —
    hence `(n−1)^{1−p} − n^{1−p} ≥ (p−1)n^{−p}`. -/
lemma one_add_mul_rpow_one_sub_le (θ u : ℝ) (hθ : 0 ≤ θ) (h0 : 0 ≤ u) (h1 : u < 1) :
    (1 + θ * u) * (1 - u) ^ θ ≤ 1 := by
  have h1u : (0:ℝ) < 1 - u := by linarith
  -- (1−u)^θ ≤ e^{−θu}
  have hlog : Real.log (1 - u) ≤ -u := by
    have := Real.log_le_sub_one_of_pos h1u
    linarith
  have hpow : (1 - u) ^ θ ≤ Real.exp (-(θ * u)) := by
    rw [Real.rpow_def_of_pos h1u]
    apply Real.exp_le_exp.mpr
    calc Real.log (1 - u) * θ ≤ (-u) * θ := mul_le_mul_of_nonneg_right hlog hθ
      _ = -(θ * u) := by ring
  -- (1+w)e^{−w} ≤ 1 for w := θu ≥ 0
  have hw0 : 0 ≤ θ * u := mul_nonneg hθ h0
  have hexp : (1 + θ * u) * Real.exp (-(θ * u)) ≤ 1 := by
    have h2 := Real.add_one_le_exp (θ * u)
    have h3 : (0:ℝ) < Real.exp (θ * u) := Real.exp_pos _
    have h4 : Real.exp (-(θ * u)) = 1 / Real.exp (θ * u) := by
      rw [Real.exp_neg, one_div]
    rw [h4, mul_one_div, div_le_one h3]
    linarith
  calc (1 + θ * u) * (1 - u) ^ θ ≤ (1 + θ * u) * Real.exp (-(θ * u)) := by
        apply mul_le_mul_of_nonneg_left hpow (by linarith)
    _ ≤ 1 := hexp

/-- The decreasing-power telescoping comparison (A2h-ii-β2): for `p > 1`, `n ≥ 2`:
    `(p−1)·n^{−p} ≤ (n−1)^{1−p} − n^{1−p}` — each tail term is dominated by the
    telescoping antiderivative decrement. -/
lemma rpow_tail_term_le (p : ℝ) (hp : 1 < p) (n : ℕ) (hn : 2 ≤ n) :
    (p - 1) * ((n:ℝ)) ^ (-p) ≤ (((n - 1 : ℕ)):ℝ) ^ (1 - p) - ((n:ℝ)) ^ (1 - p) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by
    have : (0:ℕ) < n := by omega
    exact_mod_cast this
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by
    have : (1:ℕ) ≤ n := by omega
    exact_mod_cast this
  set u : ℝ := 1 / n with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u < 1 := by
    rw [hu, div_lt_one hn0]
    linarith [show (2:ℝ) ≤ (n:ℝ) from by exact_mod_cast hn]
  have hcast : (((n - 1 : ℕ)):ℝ) = (n:ℝ) * (1 - u) := by
    rw [hu]
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
    field_simp
  have hber := one_add_mul_rpow_one_sub_le (p - 1) u (by linarith) hu0 hu1
  -- (n−1)^{1−p} = n^{1−p}·(1−u)^{1−p}; want n^{1−p}[(1−u)^{1−p} − 1] ≥ (p−1)n^{−p}
  have hsplit : (((n - 1 : ℕ)):ℝ) ^ (1 - p) = ((n:ℝ)) ^ (1 - p) * (1 - u) ^ (1 - p) := by
    rw [hcast, Real.mul_rpow hn0.le (by linarith)]
  rw [hsplit]
  have hnp : ((n:ℝ)) ^ (1 - p) = (n:ℝ) * ((n:ℝ)) ^ (-p) := by
    rw [show (1:ℝ) - p = 1 + (-p) by ring, Real.rpow_add hn0, Real.rpow_one]
  have hkey : 1 + (p - 1) * u ≤ (1 - u) ^ (1 - p) := by
    have hpow0 : (0:ℝ) < (1 - u) ^ (p - 1) := Real.rpow_pos_of_pos (by linarith) _
    have hinv : (1 - u) ^ (1 - p) = ((1 - u) ^ (p - 1))⁻¹ := by
      rw [← Real.rpow_neg (by linarith : (0:ℝ) ≤ 1 - u)]
      congr 1
      ring
    rw [hinv, le_inv_comm₀ (by positivity) hpow0]
    calc (1 - u) ^ (p - 1) ≤ 1 / (1 + (p - 1) * u) := by
          rw [le_div_iff₀ (by nlinarith [mul_nonneg (show (0:ℝ) ≤ p - 1 by linarith) hu0])]
          calc (1 - u) ^ (p - 1) * (1 + (p - 1) * u)
              = (1 + (p - 1) * u) * (1 - u) ^ (p - 1) := by ring
            _ ≤ 1 := hber
      _ = (1 + (p - 1) * u)⁻¹ := one_div _
  -- assemble: n^{1−p}(1−u)^{1−p} − n^{1−p} ≥ n^{1−p}·(p−1)u = (p−1)n^{−p}
  have hnu : (n:ℝ) * u = 1 := by
    rw [hu]
    field_simp
  have hmul := mul_le_mul_of_nonneg_left hkey
    (Real.rpow_nonneg hn0.le (1 - p))
  have hfin : ((n:ℝ)) ^ (1 - p) * ((p - 1) * u) = (p - 1) * ((n:ℝ)) ^ (-p) := by
    rw [hnp]
    calc (n:ℝ) * ((n:ℝ)) ^ (-p) * ((p - 1) * u)
        = (p - 1) * ((n:ℝ)) ^ (-p) * ((n:ℝ) * u) := by ring
      _ = (p - 1) * ((n:ℝ)) ^ (-p) := by rw [hnu, mul_one]
  nlinarith [hmul, hfin.le, hfin.ge]

/-- **The p-tail bound** (Siegel brick A2h-ii-β): for `p > 1`, `1 ≤ x`:
    `Σ_{x<n≤z} n^{−p} ≤ x^{1−p}/(p−1)` — sharp telescoping, uniform in `z`. -/
lemma rpow_tail_sum_le (p : ℝ) (hp : 1 < p) (x : ℕ) (hx : 1 ≤ x) : ∀ z : ℕ, x ≤ z →
    ∑ n ∈ Icc (x + 1) z, ((n:ℝ)) ^ (-p) ≤ ((x:ℝ)) ^ (1 - p) / (p - 1) := by
  have hp0 : (0:ℝ) < p - 1 := by linarith
  -- sharp form by induction: Σ ≤ (x^{1−p} − z^{1−p})/(p−1)
  have hsharp : ∀ z : ℕ, x ≤ z →
      ∑ n ∈ Icc (x + 1) z, ((n:ℝ)) ^ (-p)
        ≤ (((x:ℝ)) ^ (1 - p) - ((z:ℝ)) ^ (1 - p)) / (p - 1) := by
    intro z
    induction z with
    | zero =>
      intro hx0
      omega
    | succ m ihm =>
      intro hxm
      rcases Nat.lt_or_ge m x with hlt | hge
      · have hx' : x = m + 1 := by omega
        subst hx'
        simp
      · have hstep : Icc (x + 1) (m + 1) = insert (m + 1) (Icc (x + 1) m) := by
          ext k
          simp only [Finset.mem_insert, Finset.mem_Icc]
          omega
        rw [hstep, Finset.sum_insert (by simp)]
        have hterm := rpow_tail_term_le p hp (m + 1) (by omega)
        have hm1 : (m + 1 : ℕ) - 1 = m := by omega
        rw [hm1] at hterm
        have hih := ihm hge
        have hd : ((m + 1 : ℕ):ℝ) ^ (-p)
            ≤ (((m:ℝ)) ^ (1 - p) - ((m + 1 : ℕ):ℝ) ^ (1 - p)) / (p - 1) := by
          rw [le_div_iff₀ hp0]
          calc ((m + 1 : ℕ):ℝ) ^ (-p) * (p - 1) = (p - 1) * ((m + 1 : ℕ):ℝ) ^ (-p) := by ring
            _ ≤ ((m:ℝ)) ^ (1 - p) - ((m + 1 : ℕ):ℝ) ^ (1 - p) := hterm
        calc ((m + 1 : ℕ):ℝ) ^ (-p) + ∑ n ∈ Icc (x + 1) m, ((n:ℝ)) ^ (-p)
            ≤ (((m:ℝ)) ^ (1 - p) - ((m + 1 : ℕ):ℝ) ^ (1 - p)) / (p - 1)
              + (((x:ℝ)) ^ (1 - p) - ((m:ℝ)) ^ (1 - p)) / (p - 1) := add_le_add hd hih
          _ = (((x:ℝ)) ^ (1 - p) - ((m + 1 : ℕ):ℝ) ^ (1 - p)) / (p - 1) := by ring
  intro z hz
  have hzp : (0:ℝ) ≤ ((z:ℝ)) ^ (1 - p) := Real.rpow_nonneg (Nat.cast_nonneg z) _
  calc ∑ n ∈ Icc (x + 1) z, ((n:ℝ)) ^ (-p)
      ≤ (((x:ℝ)) ^ (1 - p) - ((z:ℝ)) ^ (1 - p)) / (p - 1) := hsharp z hz
    _ ≤ ((x:ℝ)) ^ (1 - p) / (p - 1) := by
        apply div_le_div_of_nonneg_right _ hp0.le
        linarith

/-- **The Euler–Maclaurin tail series is differentiable on `Re s > 9/10`**
    (Siegel brick A2h-ii-γ): `Wtail_x(s) := Σ'_n [n≥x]·((s−1)n^{−s} − (n^{1−s}−(n+1)^{1−s}))`
    is differentiable at every point of the half-plane — the continuation vehicle of the
    ζ-truncation. M-test on windows, head split off as a finite entire sum. -/
theorem wtail_differentiableAt (x : ℕ) (hx : 1 ≤ x) (s₀ : ℂ) (hs₀ : 9/10 < s₀.re) :
    DifferentiableAt ℂ (fun s : ℂ => ∑' n : ℕ, (if n < x then 0 else
      ((s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))) s₀ := by
  set σ₀ : ℝ := (9/10 + s₀.re) / 2 with hσ₀
  have hσ₀1 : 9/10 < σ₀ := by rw [hσ₀]; linarith
  have hσ₀2 : σ₀ < s₀.re := by rw [hσ₀]; linarith
  set R : ℝ := ‖s₀‖ + 1 with hR
  have hR0 : 0 < R := by
    rw [hR]
    have := norm_nonneg s₀
    linarith
  set U : Set ℂ := {s : ℂ | σ₀ < s.re} ∩ Metric.ball 0 R with hU
  have hUopen : IsOpen U := by
    apply IsOpen.inter
    · exact isOpen_lt continuous_const Complex.continuous_re
    · exact Metric.isOpen_ball
  have hs₀U : s₀ ∈ U := by
    rw [hU]
    constructor
    · exact hσ₀2
    · rw [Metric.mem_ball, dist_zero_right, hR]
      linarith
  set W : ℝ := R + 2 with hW
  set N₀ : ℕ := max x (Nat.ceil R + 4) with hN₀
  have hN₀x : x ≤ N₀ := le_max_left _ _
  have hN₀2 : 2 ≤ N₀ := le_trans (by omega) (le_max_right x (Nat.ceil R + 4))
  have hN₀W : ∀ n : ℕ, N₀ ≤ n → W ≤ (n:ℝ) := by
    intro n hn
    have h1 : Nat.ceil R + 4 ≤ n := le_trans (le_max_right x _) hn
    have h2 : ((Nat.ceil R + 4 : ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast h1
    have h3 : R ≤ (Nat.ceil R : ℝ) := Nat.le_ceil R
    push_cast at h2
    rw [hW]
    linarith
  -- the pointwise kernel bound on U, for n ≥ N₀
  have hVbound : ∀ n : ℕ, N₀ ≤ n → ∀ w : ℂ, w ∈ U →
      ‖(w - 1) * ((n:ℂ)) ^ (-w)
        - (((n:ℂ)) ^ ((1:ℂ) - w) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - w))‖
      ≤ 4 * (W + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - σ₀) := by
    intro n hn w hwU
    obtain ⟨hwre, hwball⟩ := hwU
    have hwre' : σ₀ < w.re := hwre
    have hwnorm : ‖w‖ < R := by
      rw [Metric.mem_ball, dist_zero_right] at hwball
      exact hwball
    have hn2 : 2 ≤ n := le_trans hN₀2 hn
    have hn1r : (1:ℝ) ≤ (n:ℝ) := by
      have : (1:ℕ) ≤ n := by omega
      exact_mod_cast this
    have hn0 : (0:ℝ) < (n:ℝ) := by linarith
    have hWb : ‖1 - w‖ ≤ W := by
      calc ‖1 - w‖ ≤ ‖(1:ℂ)‖ + ‖w‖ := norm_sub_le _ _
        _ = 1 + ‖w‖ := by rw [norm_one]
        _ ≤ W := by rw [hW]; linarith
    have hWn : W * (1 / (n:ℝ)) ≤ 1 := by
      rw [mul_one_div, div_le_one hn0]
      exact hN₀W n hn
    have hker := euler_maclaurin_kernel w n hn2 W hWb hWn
    have hexp : ((n:ℝ)) ^ (1 - w.re) ≤ ((n:ℝ)) ^ (1 - σ₀) := by
      apply Real.rpow_le_rpow_of_exponent_le hn1r
      linarith
    calc ‖(w - 1) * ((n:ℂ)) ^ (-w)
          - (((n:ℂ)) ^ ((1:ℂ) - w) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - w))‖
        ≤ 4 * (W + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - w.re) := hker
      _ ≤ 4 * (W + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - σ₀) := by
          apply mul_le_mul_of_nonneg_left hexp
          positivity
  -- the majorant is summable
  have husum : Summable (fun n : ℕ => if n < N₀ then (0:ℝ) else
      4 * (W + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - σ₀)) := by
    have hmajsum : Summable (fun n : ℕ => (4 * (W + 1) ^ 2) * (1 / ((n:ℝ)) ^ (σ₀ + 1))) :=
      Summable.mul_left _ (Real.summable_one_div_nat_rpow.mpr (by linarith))
    apply Summable.of_nonneg_of_le _ _ hmajsum
    · intro n
      rcases Nat.lt_or_ge n N₀ with h | h
      · rw [if_pos h]
      · rw [if_neg (not_lt.mpr h)]
        have hn0 : (0:ℝ) < (n:ℝ) := by
          have h1 : (1:ℕ) ≤ n := le_trans (le_trans hx hN₀x) h
          have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast h1
          linarith
        positivity
    · intro n
      rcases Nat.lt_or_ge n N₀ with h | h
      · rw [if_pos h]
        positivity
      · rw [if_neg (not_lt.mpr h)]
        have hn0 : (0:ℝ) < (n:ℝ) := by
          have h1 : (1:ℕ) ≤ n := le_trans (le_trans hx hN₀x) h
          have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast h1
          linarith
        have hpow2 : (1/(n:ℝ)) ^ 2 = ((n:ℝ)) ^ (-((2:ℕ):ℝ)) := by
          rw [div_pow, one_pow, one_div, ← Real.rpow_natCast (n:ℝ) 2,
            ← Real.rpow_neg hn0.le]
        have hcollect : (1/(n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - σ₀) = 1 / ((n:ℝ)) ^ (σ₀ + 1) := by
          rw [hpow2, ← Real.rpow_add hn0,
            show -((2:ℕ):ℝ) + (1 - σ₀) = -(σ₀ + 1) by push_cast; ring,
            Real.rpow_neg hn0.le, one_div]
        apply le_of_eq
        rw [← hcollect]
        ring
  -- entire terms
  have hterm : ∀ n : ℕ, 1 ≤ n → Differentiable ℂ (fun s : ℂ =>
      (s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))) := by
    intro n hn
    have hn0 : ((n:ℂ)) ≠ 0 := by
      have : n ≠ 0 := by omega
      exact_mod_cast this
    have hn10 : (((n + 1 : ℕ):ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    apply Differentiable.sub
    · apply Differentiable.mul
      · exact differentiable_id.sub (differentiable_const 1)
      · exact (Differentiable.neg differentiable_id).const_cpow (Or.inl hn0)
    · apply Differentiable.sub
      · exact ((differentiable_const 1).sub differentiable_id).const_cpow (Or.inl hn0)
      · exact ((differentiable_const 1).sub differentiable_id).const_cpow (Or.inl hn10)
  -- the tail: M-test on U
  have hgdiff : ∀ n : ℕ, DifferentiableOn ℂ (fun s : ℂ => if n < N₀ then 0 else
      ((s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))) U := by
    intro n
    rcases Nat.lt_or_ge n N₀ with h | h
    · simp only [if_pos h]
      exact differentiableOn_const 0
    · simp only [if_neg (not_lt.mpr h)]
      exact (hterm n (le_trans (le_trans hx hN₀x) h)).differentiableOn
  have hgbound : ∀ (n : ℕ) (w : ℂ), w ∈ U →
      ‖if n < N₀ then 0 else
        ((w - 1) * ((n:ℂ)) ^ (-w)
          - (((n:ℂ)) ^ ((1:ℂ) - w) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - w)))‖
      ≤ (if n < N₀ then (0:ℝ) else
          4 * (W + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - σ₀)) := by
    intro n w hwU
    rcases Nat.lt_or_ge n N₀ with h | h
    · rw [if_pos h, if_pos h, norm_zero]
    · rw [if_neg (not_lt.mpr h), if_neg (not_lt.mpr h)]
      exact hVbound n h w hwU
  have hTail : DifferentiableOn ℂ (fun s : ℂ => ∑' n : ℕ, (if n < N₀ then 0 else
      ((s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))) U :=
    Complex.differentiableOn_tsum_of_summable_norm husum hgdiff hUopen hgbound
  -- the head: a finite sum of entire functions
  have hHead : DifferentiableOn ℂ (fun s : ℂ => ∑ n ∈ range N₀, (if n < x then 0 else
      ((s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))) U := by
    have hsum : DifferentiableOn ℂ (∑ n ∈ range N₀, fun s : ℂ => (if n < x then 0 else
        ((s - 1) * ((n:ℂ)) ^ (-s)
          - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))) U := by
      apply DifferentiableOn.sum
      intro n _
      rcases Nat.lt_or_ge n x with h | h
      · simp only [if_pos h]
        exact differentiableOn_const 0
      · simp only [if_neg (not_lt.mpr h)]
        exact (hterm n (le_trans hx h)).differentiableOn
    have hfn : (fun s : ℂ => ∑ n ∈ range N₀, (if n < x then 0 else
        ((s - 1) * ((n:ℂ)) ^ (-s)
          - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))))
        = (∑ n ∈ range N₀, fun s : ℂ => (if n < x then 0 else
        ((s - 1) * ((n:ℂ)) ^ (-s)
          - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))) := by
      funext s
      rw [Finset.sum_apply]
    rw [hfn]
    exact hsum
  -- on U the full series splits as head + tail
  have hEqOn : ∀ s ∈ U, (∑' n : ℕ, (if n < x then 0 else
      ((s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))))
      = (∑ n ∈ range N₀, (if n < x then 0 else
          ((s - 1) * ((n:ℂ)) ^ (-s)
            - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))))
        + (∑' n : ℕ, (if n < N₀ then 0 else
          ((s - 1) * ((n:ℂ)) ^ (-s)
            - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))) := by
    intro s hsU
    set V : ℕ → ℂ := fun n => (s - 1) * ((n:ℂ)) ^ (-s)
      - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)) with hV
    have hgsum : Summable (fun n : ℕ => if n < N₀ then 0 else V n) := by
      apply Summable.of_norm_bounded (g := fun n : ℕ => if n < N₀ then (0:ℝ) else
        4 * (W + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - σ₀)) husum
      intro n
      exact hgbound n s hsU
    have hhsum : Summable (fun n : ℕ => if n < N₀ then (if n < x then 0 else V n) else 0) :=
      summable_of_ne_finset_zero (s := range N₀) (by
        intro n hn
        rw [Finset.mem_range] at hn
        rw [if_neg hn])
    have hsplit : ∀ n : ℕ, (if n < x then 0 else V n)
        = (if n < N₀ then (if n < x then 0 else V n) else 0)
          + (if n < N₀ then 0 else V n) := by
      intro n
      rcases Nat.lt_or_ge n N₀ with h | h
      · rw [if_pos h, if_pos h, add_zero]
      · have hnx : ¬ n < x := not_lt.mpr (le_trans hN₀x h)
        have hnN : ¬ n < N₀ := not_lt.mpr h
        rw [if_neg hnx, if_neg hnN, if_neg hnN, zero_add]
    calc ∑' n : ℕ, (if n < x then 0 else V n)
        = ∑' n : ℕ, ((if n < N₀ then (if n < x then 0 else V n) else 0)
            + (if n < N₀ then 0 else V n)) := tsum_congr hsplit
      _ = (∑' n : ℕ, (if n < N₀ then (if n < x then 0 else V n) else 0))
            + (∑' n : ℕ, (if n < N₀ then 0 else V n)) := hhsum.tsum_add hgsum
      _ = (∑ n ∈ range N₀, (if n < x then 0 else V n))
            + (∑' n : ℕ, (if n < N₀ then 0 else V n)) := by
          congr 1
          rw [tsum_eq_sum (s := range N₀) (by
            intro n hn
            rw [Finset.mem_range] at hn
            rw [if_neg hn])]
          apply Finset.sum_congr rfl
          intro n hn
          rw [Finset.mem_range] at hn
          rw [if_pos hn]
  -- assemble
  have hSum : DifferentiableOn ℂ (fun s : ℂ => ∑' n : ℕ, (if n < x then 0 else
      ((s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))) U :=
    DifferentiableOn.congr (hHead.add hTail) hEqOn
  exact hSum.differentiableAt (hUopen.mem_nhds hs₀U)

/-- **The Euler–Maclaurin tail on `Re s > 1`** (Siegel brick A2h-ii-δ):
    `Wtail_x(s) = (s−1)·(ζ(s) − Σ_{n<x} n^{−s}) − x^{1−s}` — the closed form the
    identity theorem transports to the strip. -/
theorem wtail_eq_on_gt_one (x : ℕ) (hx : 1 ≤ x) {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, (if n < x then 0 else ((s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))
    = (s - 1) * (riemannZeta s - ∑ n ∈ range x, ((n:ℂ)) ^ (-s))
        - ((x:ℂ)) ^ ((1:ℂ) - s) := by
  -- summability of the pieces
  have hzsum : Summable (fun n : ℕ => ((n:ℂ)) ^ (-s)) := by
    have h := Complex.summable_one_div_nat_cpow.mpr hs
    apply h.congr
    intro n
    rw [Complex.cpow_neg, one_div]
  have hzsum_ite : Summable (fun n : ℕ => if n < x then (0:ℂ) else ((n:ℂ)) ^ (-s)) := by
    apply Summable.of_norm_bounded (g := fun n : ℕ => ‖((n:ℂ)) ^ (-s)‖) hzsum.norm
    intro n
    rcases Nat.lt_or_ge n x with h | h
    · rw [if_pos h, norm_zero]
      exact norm_nonneg _
    · rw [if_neg (not_lt.mpr h)]
  have hhead : Summable (fun n : ℕ => if n < x then ((n:ℂ)) ^ (-s) else 0) :=
    summable_of_ne_finset_zero (s := range x) (by
      intro n hn
      rw [Finset.mem_range] at hn
      rw [if_neg hn])
  have htel_sum := tsum_cpow_telescope_summable x hx hs
  have hmul : Summable (fun n : ℕ => (s - 1) * (if n < x then (0:ℂ) else ((n:ℂ)) ^ (-s))) :=
    hzsum_ite.mul_left (s - 1)
  -- ζ splits as head + tail
  have hzeta_split : riemannZeta s = (∑ n ∈ range x, ((n:ℂ)) ^ (-s))
      + ∑' n : ℕ, (if n < x then (0:ℂ) else ((n:ℂ)) ^ (-s)) := by
    rw [zeta_eq_tsum_one_div_nat_cpow hs]
    have hconv : ∀ n : ℕ, 1 / ((n:ℂ)) ^ s = ((n:ℂ)) ^ (-s) := by
      intro n
      rw [Complex.cpow_neg, one_div]
    rw [tsum_congr hconv]
    have hsplit : ∀ n : ℕ, ((n:ℂ)) ^ (-s)
        = (if n < x then ((n:ℂ)) ^ (-s) else 0) + (if n < x then 0 else ((n:ℂ)) ^ (-s)) := by
      intro n
      rcases Nat.lt_or_ge n x with h | h
      · rw [if_pos h, if_pos h, add_zero]
      · rw [if_neg (not_lt.mpr h), if_neg (not_lt.mpr h), zero_add]
    rw [tsum_congr hsplit, hhead.tsum_add hzsum_ite]
    congr 1
    rw [tsum_eq_sum (s := range x) (by
      intro n hn
      rw [Finset.mem_range] at hn
      rw [if_neg hn])]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_range] at hn
    rw [if_pos hn]
  have hz2 : ∑' n : ℕ, (if n < x then (0:ℂ) else ((n:ℂ)) ^ (-s))
      = riemannZeta s - ∑ n ∈ range x, ((n:ℂ)) ^ (-s) := by
    rw [hzeta_split]
    ring
  -- pointwise split of the V-term
  have hVsplit : ∀ n : ℕ, (if n < x then (0:ℂ) else ((s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))
      = (s - 1) * (if n < x then (0:ℂ) else ((n:ℂ)) ^ (-s))
        - (if n < x then (0:ℂ)
            else (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))) := by
    intro n
    rcases Nat.lt_or_ge n x with h | h
    · rw [if_pos h, if_pos h, if_pos h, mul_zero, sub_zero]
    · rw [if_neg (not_lt.mpr h), if_neg (not_lt.mpr h), if_neg (not_lt.mpr h)]
  -- assemble
  rw [tsum_congr hVsplit, Summable.tsum_sub hmul htel_sum, tsum_mul_left,
    tsum_cpow_telescope x hx hs, hz2]

/-- **The ζ-truncation identity at real `β′ ∈ (9/10, 1)`** (Siegel brick A2h-ii-ε1):
    the closed form of `Wtail_x` continues through the pole-free slit — the identity
    theorem transports `wtail_eq_on_gt_one` from `Re > 1` to the strip. -/
theorem zeta_truncation_identity (x : ℕ) (hx : 1 ≤ x) {β : ℝ}
    (hβ1 : 9/10 < β) (hβ2 : β < 1) :
    ∑' n : ℕ, (if n < x then 0 else ((((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
        - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))))
    = (((β:ℂ)) - 1) * (riemannZeta (β:ℂ) - ∑ n ∈ range x, ((n:ℂ)) ^ (-(β:ℂ)))
        - ((x:ℂ)) ^ ((1:ℂ) - (β:ℂ)) := by
  have hx0 : ((x:ℂ)) ≠ 0 := by
    have : x ≠ 0 := by omega
    exact_mod_cast this
  -- differentiability of each n^{−s} term (n = 0 is locally the zero function)
  have hterm0 : ∀ n : ℕ, ∀ s : ℂ, 9/10 < s.re →
      DifferentiableAt ℂ (fun s : ℂ => ((n:ℂ)) ^ (-s)) s := by
    intro n s hs
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · apply (differentiableAt_const (0:ℂ)).congr_of_eventuallyEq
      have hopen : IsOpen {w : ℂ | 9/10 < w.re} :=
        isOpen_lt continuous_const Complex.continuous_re
      filter_upwards [hopen.mem_nhds hs] with w hw
      rw [Nat.cast_zero, Complex.zero_cpow]
      intro hc
      have hw0 : w = 0 := by
        have := neg_eq_zero.mp hc
        exact this
      rw [hw0] at hw
      simp only [Set.mem_setOf_eq, Complex.zero_re] at hw
      linarith
    · have hn0 : ((n:ℂ)) ≠ 0 := by
        have : n ≠ 0 := by omega
        exact_mod_cast this
      exact ((Differentiable.neg differentiable_id).const_cpow
        (Or.inl hn0)).differentiableAt
  -- differentiability of the finite sum
  have hgsum : ∀ s : ℂ, 9/10 < s.re →
      DifferentiableAt ℂ (fun s : ℂ => ∑ n ∈ range x, ((n:ℂ)) ^ (-s)) s := by
    intro s hs
    have h : DifferentiableAt ℂ (∑ n ∈ range x, fun s : ℂ => ((n:ℂ)) ^ (-s)) s := by
      apply DifferentiableAt.sum
      intro n _
      exact hterm0 n s hs
    have hfn : (fun s : ℂ => ∑ n ∈ range x, ((n:ℂ)) ^ (-s))
        = ∑ n ∈ range x, fun s : ℂ => ((n:ℂ)) ^ (-s) := by
      funext w
      rw [Finset.sum_apply]
    rw [hfn]
    exact h
  -- apply the identity theorem
  have h₀re : 9/10 < ((β:ℂ)).re := by
    rw [Complex.ofReal_re]
    exact hβ1
  have h₀ne : ((β:ℂ)) ≠ 1 := by
    intro h
    rw [Complex.ofReal_eq_one] at h
    linarith
  exact eqOn_slit_halfplane
    (fun s : ℂ => ∑' n : ℕ, (if n < x then 0 else ((s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))))
    (fun s : ℂ => (s - 1) * (riemannZeta s - ∑ n ∈ range x, ((n:ℂ)) ^ (-s))
        - ((x:ℂ)) ^ ((1:ℂ) - s))
    (fun s hs _ => wtail_differentiableAt x hx s hs)
    (by
      intro s hs hs1
      apply DifferentiableAt.sub
      · apply DifferentiableAt.mul
        · exact (differentiable_id.sub (differentiable_const 1)).differentiableAt
        · apply DifferentiableAt.sub
          · exact differentiableAt_riemannZeta hs1
          · exact hgsum s hs
      · exact (((differentiable_const 1).sub differentiable_id).const_cpow
          (Or.inl hx0)).differentiableAt)
    (fun s hs => wtail_eq_on_gt_one x hx hs)
    ((β:ℂ)) h₀re h₀ne

/-- **THE ζ-TRUNCATION BOUND** (Siegel brick A2h-ii-ε): at real `β′ ∈ (9/10, 1)`,
    `‖(β′−1)(ζ(β′) − Σ_{n<x}n^{−β′}) − x^{1−β′}‖ ≤ 11·x^{−β′}` for `x ≥ 2` — the
    quantitative form the Goldfeld master inequality consumes. -/
theorem zeta_truncation (x : ℕ) (hx : 2 ≤ x) {β : ℝ} (hβ1 : 9/10 < β) (hβ2 : β < 1) :
    ‖(((β:ℂ)) - 1) * (riemannZeta (β:ℂ) - ∑ n ∈ range x, ((n:ℂ)) ^ (-(β:ℂ)))
        - ((x:ℂ)) ^ ((1:ℂ) - (β:ℂ))‖ ≤ 11 * ((x:ℝ)) ^ (-β) := by
  have hx1 : 1 ≤ x := by omega
  have hx0 : (0:ℝ) < (x:ℝ) := by
    have : (0:ℕ) < x := by omega
    exact_mod_cast this
  rw [← zeta_truncation_identity x hx1 hβ1 hβ2]
  -- the pointwise kernel bound at s = β′
  have hpoint : ∀ n : ℕ, x ≤ n →
      ‖(((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
        - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))‖
      ≤ 5 * ((n:ℝ)) ^ (-(1 + β)) := by
    intro n hn
    have hn2 : 2 ≤ n := le_trans hx hn
    have hn1r : (1:ℝ) ≤ (n:ℝ) := by
      have : (1:ℕ) ≤ n := by omega
      exact_mod_cast this
    have hn0 : (0:ℝ) < (n:ℝ) := by linarith
    have hW : ‖1 - ((β:ℂ))‖ ≤ 1/10 := by
      rw [show (1:ℂ) - ((β:ℂ)) = (((1 - β : ℝ)):ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    have hWn : (1/10 : ℝ) * (1 / (n:ℝ)) ≤ 1 := by
      have h1 : (1:ℝ)/(n:ℝ) ≤ 1 := by
        rw [div_le_one hn0]
        linarith
      linarith
    have hker := euler_maclaurin_kernel ((β:ℂ)) n hn2 (1/10) hW hWn
    rw [Complex.ofReal_re] at hker
    have hcollect : (1/(n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - β) = ((n:ℝ)) ^ (-(1 + β)) := by
      have hpow2 : (1/(n:ℝ)) ^ 2 = ((n:ℝ)) ^ (-((2:ℕ):ℝ)) := by
        rw [div_pow, one_pow, one_div, ← Real.rpow_natCast (n:ℝ) 2,
          ← Real.rpow_neg hn0.le]
      rw [hpow2, ← Real.rpow_add hn0]
      congr 1
      push_cast
      ring
    calc ‖(((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
          - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))‖
        ≤ 4 * (1/10 + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - β) := hker
      _ = 4 * (1/10 + 1) ^ 2 * (((n:ℝ)) ^ (-(1 + β))) := by
          rw [← hcollect]
          ring
      _ ≤ 5 * ((n:ℝ)) ^ (-(1 + β)) := by
          have ht : (0:ℝ) ≤ ((n:ℝ)) ^ (-(1 + β)) := Real.rpow_nonneg hn0.le _
          nlinarith [ht]
  -- partial sums of the norms are uniformly ≤ 11 x^{−β}
  have hxβ : (0:ℝ) ≤ ((x:ℝ)) ^ (-β) := Real.rpow_nonneg hx0.le _
  have hpartial : ∀ z : ℕ, ∑ n ∈ range z,
      ‖if n < x then (0:ℂ) else ((((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
        - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ))))‖
      ≤ 11 * ((x:ℝ)) ^ (-β) := by
    intro z
    have hite : ∀ n ∈ range z,
        ‖if n < x then (0:ℂ) else ((((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
          - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ))))‖
        = (if x ≤ n then ‖(((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
          - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))‖ else 0) := by
      intro n _
      rcases Nat.lt_or_ge n x with h | h
      · rw [if_pos h, if_neg (by omega), norm_zero]
      · rw [if_neg (not_lt.mpr h), if_pos h]
    rw [Finset.sum_congr rfl hite, ← Finset.sum_filter]
    have hset : (range z).filter (fun n => x ≤ n) = Icc x (z - 1) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      omega
    rw [hset]
    rcases Nat.lt_or_ge (z - 1) x with hm | hm
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      positivity
    · rw [show Icc x (z - 1) = insert x (Icc (x + 1) (z - 1)) from by
        ext n
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega, Finset.sum_insert (by simp)]
      have h1 := hpoint x (le_refl x)
      have h2 : ∑ n ∈ Icc (x + 1) (z - 1),
          ‖(((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
            - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))‖
          ≤ ∑ n ∈ Icc (x + 1) (z - 1), 5 * ((n:ℝ)) ^ (-(1 + β)) := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
        exact hpoint n (by omega)
      have h3 : ∑ n ∈ Icc (x + 1) (z - 1), 5 * ((n:ℝ)) ^ (-(1 + β))
          = 5 * ∑ n ∈ Icc (x + 1) (z - 1), ((n:ℝ)) ^ (-(1 + β)) := by
        rw [Finset.mul_sum]
      have h4 := rpow_tail_sum_le (1 + β) (by linarith) x hx1 (z - 1) hm
      rw [show (1:ℝ) - (1 + β) = -β by ring, show (1:ℝ) + β - 1 = β by ring] at h4
      -- x-term: 5x^{−(1+β)} ≤ (5/2)x^{−β}
      have hxsplit : ((x:ℝ)) ^ (-(1 + β)) = ((x:ℝ)) ^ (-β) * ((x:ℝ)) ^ (-(1:ℝ)) := by
        rw [← Real.rpow_add hx0]
        congr 1
        ring
      have hxinv : ((x:ℝ)) ^ (-(1:ℝ)) ≤ 1/2 := by
        rw [Real.rpow_neg_one, ← one_div]
        apply one_div_le_one_div_of_le (by norm_num)
        exact_mod_cast hx
      have h5 : 5 * ((x:ℝ)) ^ (-(1 + β)) ≤ 5 * (((x:ℝ)) ^ (-β) * (1/2)) := by
        rw [hxsplit]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_left hxinv hxβ
      -- tail: 5·x^{−β}/β ≤ 5·x^{−β}·(10/9)
      have hβinv : (1:ℝ)/β ≤ 10/9 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]
        linarith
      have h6 : ((x:ℝ)) ^ (-β) / β ≤ ((x:ℝ)) ^ (-β) * (10/9) := by
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left hβinv hxβ
      calc ‖(((β:ℂ)) - 1) * ((x:ℂ)) ^ (-(β:ℂ))
            - (((x:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((x + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))‖
            + ∑ n ∈ Icc (x + 1) (z - 1),
              ‖(((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
                - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))‖
          ≤ 5 * ((x:ℝ)) ^ (-(1 + β))
            + 5 * (((x:ℝ)) ^ (-β) / β) := by
            have := le_trans h2 (le_of_eq h3)
            have h7 : 5 * ∑ n ∈ Icc (x + 1) (z - 1), ((n:ℝ)) ^ (-(1 + β))
                ≤ 5 * (((x:ℝ)) ^ (-β) / β) := by
              apply mul_le_mul_of_nonneg_left h4 (by norm_num)
            linarith
        _ ≤ 5 * (((x:ℝ)) ^ (-β) * (1/2)) + 5 * (((x:ℝ)) ^ (-β) * (10/9)) := by
            have h8 : 5 * (((x:ℝ)) ^ (-β) / β) ≤ 5 * (((x:ℝ)) ^ (-β) * (10/9)) :=
              mul_le_mul_of_nonneg_left h6 (by norm_num)
            linarith
        _ ≤ 11 * ((x:ℝ)) ^ (-β) := by linarith
  -- summability of the norms
  have hnorm_sum : Summable (fun n : ℕ =>
      ‖if n < x then (0:ℂ) else ((((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
        - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ))))‖) := by
    have hmaj : Summable (fun n : ℕ => (5:ℝ) * (1 / ((n:ℝ)) ^ (1 + β))) :=
      Summable.mul_left _ (Real.summable_one_div_nat_rpow.mpr (by linarith))
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ hmaj
    intro n
    rcases Nat.lt_or_ge n x with h | h
    · rw [if_pos h, norm_zero]
      positivity
    · rw [if_neg (not_lt.mpr h)]
      have hn0 : (0:ℝ) < (n:ℝ) := by
        have : (0:ℕ) < n := by omega
        exact_mod_cast this
      have heq : (5:ℝ) * (1 / ((n:ℝ)) ^ (1 + β)) = 5 * ((n:ℝ)) ^ (-(1 + β)) := by
        rw [one_div, ← Real.rpow_neg hn0.le]
      rw [heq]
      exact hpoint n h
  -- assemble
  calc ‖∑' n : ℕ, (if n < x then (0:ℂ) else ((((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
        - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))))‖
      ≤ ∑' n : ℕ, ‖if n < x then (0:ℂ) else ((((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
        - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ))))‖ :=
        norm_tsum_le_tsum_norm hnorm_sum
    _ ≤ 11 * ((x:ℝ)) ^ (-β) :=
        hnorm_sum.tsum_le_of_sum_range_le hpartial

/-- Real Abel initial-value summation (A2h-iv-a1): the ℝ twin of `abel_initial`. -/
lemma abel_initial_r (a w : ℕ → ℝ) : ∀ x : ℕ, 1 ≤ x →
    ∑ n ∈ Icc 1 x, a n * w n
      = (∑ n ∈ Icc 1 x, a n) * w x
        + ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m) * (w n - w (n + 1)) := by
  intro x
  induction x with
  | zero =>
    intro h0
    omega
  | succ p ih =>
    intro _
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp
    · have hp1 : (p + 1 : ℕ) - 1 = p := by omega
      have hnotmem : (p + 1) ∉ Icc 1 p := by
        simp only [Finset.mem_Icc]
        omega
      have hnotmem2 : p ∉ Icc 1 (p - 1) := by
        simp only [Finset.mem_Icc]
        omega
      have hins : Icc 1 (p + 1) = insert (p + 1) (Icc 1 p) := by
        ext m
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      have hins2 : Icc 1 p = insert p (Icc 1 (p - 1)) := by
        ext m
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      have hLHS : ∑ n ∈ Icc 1 (p + 1), a n * w n
          = a (p + 1) * w (p + 1) + ∑ n ∈ Icc 1 p, a n * w n := by
        rw [hins, Finset.sum_insert hnotmem]
      have hRHS2 : ∑ n ∈ Icc 1 ((p + 1) - 1), (∑ m ∈ Icc 1 n, a m) * (w n - w (n + 1))
          = (∑ m ∈ Icc 1 p, a m) * (w p - w (p + 1))
            + ∑ n ∈ Icc 1 (p - 1), (∑ m ∈ Icc 1 n, a m) * (w n - w (n + 1)) := by
        rw [hp1]
        conv_lhs => rw [hins2]
        rw [Finset.sum_insert hnotmem2]
      have hA : ∑ m ∈ Icc 1 (p + 1), a m = a (p + 1) + ∑ m ∈ Icc 1 p, a m := by
        rw [hins, Finset.sum_insert hnotmem]
      rw [hLHS, ih hp, hRHS2, hA]
      ring

/-- **The finite Abel master identity** (Siegel brick A2h-iv-a): for partial sums
    `A(y) = λy + E(y)`, against ANY weight `w`:
    `Σ_{n≤x} a(n)w(n) = λ·Σ_{n≤x}w(n) + E(x)w(x) + Σ_{n<x}E(n)(w(n)−w(n+1))` —
    the λ-part telescopes exactly; no continuation enters. -/
theorem abel_master_identity (a : ℕ → ℝ) (lam : ℝ) (E : ℕ → ℝ)
    (hAE : ∀ n : ℕ, ∑ m ∈ Icc 1 n, a m = lam * n + E n)
    (w : ℕ → ℝ) (x : ℕ) (hx : 1 ≤ x) :
    ∑ n ∈ Icc 1 x, a n * w n
    = lam * (∑ n ∈ Icc 1 x, w n) + E x * w x
      + ∑ n ∈ Icc 1 (x - 1), E n * (w n - w (n + 1)) := by
  rw [abel_initial_r a w x hx, hAE x]
  have hterm : ∀ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m) * (w n - w (n + 1))
      = (n : ℝ) * (w n - w (n + 1)) * lam + E n * (w n - w (n + 1)) := by
    intro n _
    rw [hAE n]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_mul,
    weighted_telescope w (x - 1)]
  have hxx : (x - 1 : ℕ) + 1 = x := by omega
  rw [hxx]
  have hsplit : ∑ n ∈ Icc 1 x, w n = w x + ∑ n ∈ Icc 1 (x - 1), w n := by
    rw [show Icc 1 x = insert x (Icc 1 (x - 1)) from by
      ext m
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega, Finset.sum_insert (by
        simp only [Finset.mem_Icc]
        omega)]
  rw [hsplit]
  have hcast : ((x - 1 : ℕ) : ℝ) = (x : ℝ) - 1 := by
    push_cast [Nat.cast_sub hx]
    ring
  rw [hcast]
  ring

/-- Real-cast bridge for cpow at real exponents (A2h-iv-b0). -/
lemma cpow_real_cast (n : ℕ) (β : ℝ) :
    ((n:ℂ)) ^ (-(β:ℂ)) = ((((n:ℝ)) ^ (-β) : ℝ) : ℂ) := by
  rw [show -(β:ℂ) = (((-β : ℝ)):ℂ) from by push_cast; ring,
    show ((n:ℂ)) = (((n:ℝ)):ℂ) from by push_cast; ring]
  exact (Complex.ofReal_cpow (Nat.cast_nonneg n) (-β)).symm

/-- The E-Abel term is real at real exponents (A2h-iv-b0'). -/
lemma eabel_term_real (E : ℕ → ℝ) (n : ℕ) (β : ℝ) :
    ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))
    = (((E n * (((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β)) : ℝ)) : ℂ) := by
  rw [cpow_real_cast n β, cpow_real_cast (n + 1) β]
  push_cast
  ring

/-- **The E-Abel tail bound** (Siegel brick A2h-iv-b): with `|E(n)| ≤ C·n^{3/4}(1+log n)`,
    at real `β ∈ (9/10, 1)` the series tail beyond `x` is `≤ 400C·x^{7/8−β}` — the error
    that the choice `9/10 > 7/8` makes vanish. -/
theorem eabel_tail_bound (E : ℕ → ℝ) (C : ℝ) (hC0 : 0 ≤ C) (hE0 : E 0 = 0)
    (hE : ∀ n : ℕ, 1 ≤ n → |E n| ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)))
    {β : ℝ} (hβ1 : 9/10 < β) (hβ2 : β < 1) (x : ℕ) (hx : 2 ≤ x) :
    ‖(∑' n : ℕ, ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))
      - ∑ n ∈ Icc 1 (x - 1), ((E n : ℝ) : ℂ)
          * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
    ≤ 400 * C * ((x:ℝ)) ^ (7/8 - β) := by
  have hx1 : 1 ≤ x := by omega
  have hx0 : (0:ℝ) < (x:ℝ) := by
    have : (0:ℕ) < x := by omega
    exact_mod_cast this
  have hβ0 : (0:ℝ) < β := by linarith
  have hp1 : (1:ℝ) < β + 1/8 := by linarith
  -- the pointwise majorant: ‖E(n)Δn‖ ≤ 9C·n^{−(β+1/8)} for n ≥ 1
  have hpoint : ∀ n : ℕ, 1 ≤ n →
      ‖((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
      ≤ 9 * C * ((n:ℝ)) ^ (-(β + 1/8)) := by
    intro n hn
    have hn1r : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hn0 : (0:ℝ) < (n:ℝ) := by linarith
    rw [eabel_term_real, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have hΔ0 : (0:ℝ) ≤ ((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β) := by
      have hmono : (((n + 1 : ℕ)):ℝ) ^ (-β) ≤ ((n:ℝ)) ^ (-β) := by
        apply Real.rpow_le_rpow_of_nonpos hn0 (by push_cast; linarith)
        linarith
      linarith
    have hΔle : ((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β) ≤ ((n:ℝ)) ^ (-β - 1) := by
      calc ((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β)
          ≤ β * ((n:ℝ)) ^ (-β - 1) := rpow_diff_le n hn β hβ0.le
        _ ≤ 1 * ((n:ℝ)) ^ (-β - 1) := by
            apply mul_le_mul_of_nonneg_right (by linarith)
            exact Real.rpow_nonneg hn0.le _
        _ = ((n:ℝ)) ^ (-β - 1) := one_mul _
    have hlogbound : 1 + Real.log n ≤ 9 * ((n:ℝ)) ^ ((1:ℝ)/8) := by
      have h1 : Real.log n ≤ ((n:ℝ)) ^ ((1:ℝ)/8) / (1/8) :=
        Real.log_le_rpow_div hn0.le (by norm_num)
      have h2 : ((n:ℝ)) ^ ((1:ℝ)/8) / (1/8) = 8 * ((n:ℝ)) ^ ((1:ℝ)/8) := by ring
      have h3 : (1:ℝ) ≤ ((n:ℝ)) ^ ((1:ℝ)/8) :=
        Real.one_le_rpow hn1r (by norm_num)
      linarith [h1, h2.le, h2.ge, h3]
    have hlog0 : (0:ℝ) ≤ 1 + Real.log n := by
      have := Real.log_nonneg hn1r
      linarith
    have hEn := hE n hn
    have habs : |((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β)|
        = ((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β) := abs_of_nonneg hΔ0
    rw [habs]
    have hcollect : ((n:ℝ)) ^ ((3:ℝ)/4) * ((n:ℝ)) ^ ((1:ℝ)/8) * ((n:ℝ)) ^ (-β - 1)
        = ((n:ℝ)) ^ (-(β + 1/8)) := by
      rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
      congr 1
      ring
    calc |E n| * (((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β))
        ≤ (C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n))) * (((n:ℝ)) ^ (-β - 1)) := by
          exact mul_le_mul hEn hΔle hΔ0 (by positivity)
      _ ≤ (C * (((n:ℝ)) ^ ((3:ℝ)/4) * (9 * ((n:ℝ)) ^ ((1:ℝ)/8)))) * (((n:ℝ)) ^ (-β - 1)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hn0.le _)
          apply mul_le_mul_of_nonneg_left _ hC0
          apply mul_le_mul_of_nonneg_left hlogbound (Real.rpow_nonneg hn0.le _)
      _ = 9 * C * (((n:ℝ)) ^ ((3:ℝ)/4) * ((n:ℝ)) ^ ((1:ℝ)/8) * ((n:ℝ)) ^ (-β - 1)) := by
          ring
      _ = 9 * C * ((n:ℝ)) ^ (-(β + 1/8)) := by rw [hcollect]
  -- summability of the terms
  have hsummable : Summable (fun n : ℕ => ((E n : ℝ) : ℂ)
      * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))) := by
    have hmaj : Summable (fun n : ℕ => (9 * C) * (1 / ((n:ℝ)) ^ (β + 1/8))) :=
      Summable.mul_left _ (Real.summable_one_div_nat_rpow.mpr hp1)
    apply Summable.of_norm_bounded
      (g := fun n : ℕ => (9 * C) * (1 / ((n:ℝ)) ^ (β + 1/8))) hmaj
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hE0]
      simp only [Complex.ofReal_zero, zero_mul, norm_zero]
      positivity
    · have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
      have heq : (9 * C) * (1 / ((n:ℝ)) ^ (β + 1/8))
          = 9 * C * ((n:ℝ)) ^ (-(β + 1/8)) := by
        rw [one_div, ← Real.rpow_neg hn0.le]
      rw [heq]
      exact hpoint n hn
  -- the finite sum is the range-x head (the n = 0 term vanishes)
  have hhead : ∑ n ∈ Icc 1 (x - 1), ((E n : ℝ) : ℂ)
        * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))
      = ∑ n ∈ range x, ((E n : ℝ) : ℂ)
        * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))) := by
    rw [show range x = insert 0 (Icc 1 (x - 1)) from by
      ext m
      simp only [Finset.mem_insert, Finset.mem_range, Finset.mem_Icc]
      omega, Finset.sum_insert (by
        simp only [Finset.mem_Icc]
        omega)]
    rw [hE0]
    simp
  rw [hhead]
  -- head/tail split of the tsum
  have hsplit : ∀ n : ℕ, ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))
      = (if n < x then ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))) else 0)
        + (if n < x then 0 else ((E n : ℝ) : ℂ)
            * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))) := by
    intro n
    rcases Nat.lt_or_ge n x with h | h
    · rw [if_pos h, if_pos h, add_zero]
    · rw [if_neg (not_lt.mpr h), if_neg (not_lt.mpr h), zero_add]
  have hheadsum : Summable (fun n : ℕ => (if n < x then ((E n : ℝ) : ℂ)
      * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))) else 0)) :=
    summable_of_ne_finset_zero (s := range x) (by
      intro n hn
      rw [Finset.mem_range] at hn
      rw [if_neg hn])
  have htailsum : Summable (fun n : ℕ => (if n < x then 0 else ((E n : ℝ) : ℂ)
      * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))) := by
    apply Summable.of_norm_bounded (g := fun n : ℕ =>
      ‖((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖)
      hsummable.norm
    intro n
    rcases Nat.lt_or_ge n x with h | h
    · rw [if_pos h, norm_zero]
      exact norm_nonneg _
    · rw [if_neg (not_lt.mpr h)]
  have htsum_split : (∑' n : ℕ, ((E n : ℝ) : ℂ)
        * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))
      = (∑ n ∈ range x, ((E n : ℝ) : ℂ)
          * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))
        + ∑' n : ℕ, (if n < x then 0 else ((E n : ℝ) : ℂ)
            * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))) := by
    calc ∑' n : ℕ, ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))
        = ∑' n : ℕ, ((if n < x then ((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))) else 0)
            + (if n < x then 0 else ((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))) := tsum_congr hsplit
      _ = (∑' n : ℕ, (if n < x then ((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))) else 0))
            + ∑' n : ℕ, (if n < x then 0 else ((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))) :=
          hheadsum.tsum_add htailsum
      _ = (∑ n ∈ range x, ((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))
            + ∑' n : ℕ, (if n < x then 0 else ((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))) := by
          congr 1
          rw [tsum_eq_sum (s := range x) (by
            intro n hn
            rw [Finset.mem_range] at hn
            rw [if_neg hn])]
          apply Finset.sum_congr rfl
          intro n hn
          rw [Finset.mem_range] at hn
          rw [if_pos hn]
  rw [htsum_split]
  rw [show ∀ (u v : ℂ), u + v - u = v from fun u v => by ring]
  -- bound the tail tsum by its norms
  have hxβ : (0:ℝ) ≤ ((x:ℝ)) ^ (7/8 - β) := Real.rpow_nonneg hx0.le _
  have hnormsum : Summable (fun n : ℕ => ‖if n < x then 0 else ((E n : ℝ) : ℂ)
      * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖) := htailsum.norm
  have hpartial : ∀ z : ℕ, ∑ n ∈ range z, ‖if n < x then 0 else ((E n : ℝ) : ℂ)
      * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
      ≤ 400 * C * ((x:ℝ)) ^ (7/8 - β) := by
    intro z
    have hite : ∀ n ∈ range z, ‖if n < x then (0:ℂ) else ((E n : ℝ) : ℂ)
        * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
        = (if x ≤ n then ‖((E n : ℝ) : ℂ)
          * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖ else 0) := by
      intro n _
      rcases Nat.lt_or_ge n x with h | h
      · rw [if_pos h, if_neg (by omega), norm_zero]
      · rw [if_neg (not_lt.mpr h), if_pos h]
    rw [Finset.sum_congr rfl hite, ← Finset.sum_filter]
    have hset : (range z).filter (fun n => x ≤ n) = Icc x (z - 1) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      omega
    rw [hset]
    rcases Nat.lt_or_ge (z - 1) x with hm | hm
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      positivity
    · rw [show Icc x (z - 1) = insert x (Icc (x + 1) (z - 1)) from by
        ext n
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega, Finset.sum_insert (by simp)]
      have h1 : ‖((E x : ℝ) : ℂ) * (((x:ℂ)) ^ (-(β:ℂ)) - (((x + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
          ≤ 9 * C * ((x:ℝ)) ^ (-(β + 1/8)) := hpoint x hx1
      have h2 : ∑ n ∈ Icc (x + 1) (z - 1), ‖((E n : ℝ) : ℂ)
            * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
          ≤ ∑ n ∈ Icc (x + 1) (z - 1), 9 * C * ((n:ℝ)) ^ (-(β + 1/8)) := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
        exact hpoint n (by omega)
      have h3 : ∑ n ∈ Icc (x + 1) (z - 1), 9 * C * ((n:ℝ)) ^ (-(β + 1/8))
          = 9 * C * ∑ n ∈ Icc (x + 1) (z - 1), ((n:ℝ)) ^ (-(β + 1/8)) := by
        rw [Finset.mul_sum]
      have h4 := rpow_tail_sum_le (β + 1/8) hp1 x hx1 (z - 1) hm
      rw [show (1:ℝ) - (β + 1/8) = 7/8 - β by ring,
        show β + 1/8 - 1 = β - 7/8 by ring] at h4
      have hdenom : ((x:ℝ)) ^ (7/8 - β) / (β - 7/8) ≤ 40 * ((x:ℝ)) ^ (7/8 - β) := by
        rw [div_le_iff₀ (by linarith)]
        have h5 : (1:ℝ) ≤ 40 * (β - 7/8) := by linarith
        nlinarith [hxβ]
      have hxterm : ((x:ℝ)) ^ (-(β + 1/8)) ≤ ((x:ℝ)) ^ (7/8 - β) := by
        apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hx1)
        linarith
      calc ‖((E x : ℝ) : ℂ) * (((x:ℂ)) ^ (-(β:ℂ)) - (((x + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
            + ∑ n ∈ Icc (x + 1) (z - 1), ‖((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
          ≤ 9 * C * ((x:ℝ)) ^ (-(β + 1/8))
            + 9 * C * (((x:ℝ)) ^ (7/8 - β) / (β - 7/8)) := by
            have h6 : 9 * C * ∑ n ∈ Icc (x + 1) (z - 1), ((n:ℝ)) ^ (-(β + 1/8))
                ≤ 9 * C * (((x:ℝ)) ^ (7/8 - β) / (β - 7/8)) := by
              apply mul_le_mul_of_nonneg_left h4 (by positivity)
            linarith [le_trans h2 (le_of_eq h3), h1, h6,
              le_trans (le_trans h2 (le_of_eq h3)) h6]
        _ ≤ 9 * C * ((x:ℝ)) ^ (7/8 - β) + 9 * C * (40 * ((x:ℝ)) ^ (7/8 - β)) := by
            have h7 : 9 * C * ((x:ℝ)) ^ (-(β + 1/8)) ≤ 9 * C * ((x:ℝ)) ^ (7/8 - β) :=
              mul_le_mul_of_nonneg_left hxterm (by positivity)
            have h8 : 9 * C * (((x:ℝ)) ^ (7/8 - β) / (β - 7/8))
                ≤ 9 * C * (40 * ((x:ℝ)) ^ (7/8 - β)) :=
              mul_le_mul_of_nonneg_left hdenom (by positivity)
            linarith
        _ ≤ 400 * C * ((x:ℝ)) ^ (7/8 - β) := by nlinarith [hxβ, hC0]
  calc ‖∑' n : ℕ, (if n < x then 0 else ((E n : ℝ) : ℂ)
        * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))‖
      ≤ ∑' n : ℕ, ‖if n < x then 0 else ((E n : ℝ) : ℂ)
        * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖ :=
        norm_tsum_le_tsum_norm hnormsum
    _ ≤ 400 * C * ((x:ℝ)) ^ (7/8 - β) :=
        hnormsum.tsum_le_of_sum_range_le hpartial

/-- **THE GOLDFELD MASTER INEQUALITY** (Siegel brick A2h-iv): for a nonnegative
    Dirichlet-coefficient system with `a(1) = 1` and partial sums `λy + E(y)`,
    `|E(n)| ≤ C·n^{3/4}(1+log n)`: at every real `β ∈ (9/10, 1)` and every `x ≥ 2`,
    `1 ≤ G(β).re + λ·x^{1−β}/(1−β) + 12λ·x^{−β}/(1−β) + 410C·x^{7/8−β}`
    where `G = λζ + Σ'E(n)Δn` is the analytic continuation of `Σa(n)n^{−s}`.
    At a zero of the L-product `G(β) = 0` and `x → ∞` forces `λ` large — Siegel. -/
theorem goldfeld_master_inequality (a : ℕ → ℝ) (lam : ℝ) (E : ℕ → ℝ) (C : ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (ha1 : a 1 = 1) (hlam : 0 ≤ lam)
    (hAE : ∀ n : ℕ, ∑ m ∈ Icc 1 n, a m = lam * n + E n)
    (hC0 : 0 ≤ C) (hE0 : E 0 = 0)
    (hE : ∀ n : ℕ, 1 ≤ n → |E n| ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)))
    {β : ℝ} (hβ1 : 9/10 < β) (hβ2 : β < 1) (x : ℕ) (hx : 2 ≤ x) :
    1 ≤ ((lam : ℂ) * riemannZeta ((β:ℂ))
          + ∑' n : ℕ, ((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))).re
        + lam * (((x:ℝ)) ^ (1 - β) / (1 - β))
        + 12 * lam * (((x:ℝ)) ^ (-β) / (1 - β))
        + 410 * C * ((x:ℝ)) ^ (7/8 - β) := by
  have hx1 : 1 ≤ x := by omega
  have hx0 : (0:ℝ) < (x:ℝ) := by
    have : (0:ℕ) < x := by omega
    exact_mod_cast this
  have hx1r : (1:ℝ) ≤ (x:ℝ) := by
    have : (1:ℕ) ≤ x := hx1
    exact_mod_cast this
  have h1β : (0:ℝ) < 1 - β := by linarith
  have hβ0 : (0:ℝ) < β := by linarith
  have hxβ : (0:ℝ) ≤ ((x:ℝ)) ^ (-β) := Real.rpow_nonneg hx0.le _
  have hx78 : (0:ℝ) ≤ ((x:ℝ)) ^ (7/8 - β) := Real.rpow_nonneg hx0.le _
  have hx1β : (0:ℝ) ≤ ((x:ℝ)) ^ (1 - β) := Real.rpow_nonneg hx0.le _
  -- abbreviations
  set Z : ℂ := riemannZeta ((β:ℂ)) with hZ
  set ES : ℂ := ∑' n : ℕ, ((E n : ℝ) : ℂ)
      * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))) with hES
  set SC : ℂ := ∑ n ∈ range x, ((n:ℂ)) ^ (-(β:ℂ)) with hSC
  set SF : ℂ := ∑ n ∈ Icc 1 (x - 1), ((E n : ℝ) : ℂ)
      * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))) with hSF
  -- Step 1: the unit lower bound
  have hone : (1:ℝ) ≤ ∑ n ∈ Icc 1 x, a n * ((n:ℝ)) ^ (-β) := by
    have h1mem : (1:ℕ) ∈ Icc 1 x := by
      simp only [Finset.mem_Icc]
      omega
    have hterm1 : a 1 * (((1:ℕ)):ℝ) ^ (-β) = 1 := by
      rw [ha1, Nat.cast_one, Real.one_rpow, one_mul]
    calc (1:ℝ) = a 1 * (((1:ℕ)):ℝ) ^ (-β) := hterm1.symm
      _ ≤ ∑ n ∈ Icc 1 x, a n * ((n:ℝ)) ^ (-β) := by
          apply Finset.single_le_sum (f := fun n : ℕ => a n * ((n:ℝ)) ^ (-β)) _ h1mem
          intro n _
          exact mul_nonneg (ha0 n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  -- Step 2: the finite Abel identity at w(n) = n^{−β}
  have hiden : ∑ n ∈ Icc 1 x, a n * ((n:ℝ)) ^ (-β)
      = lam * (∑ n ∈ Icc 1 x, ((n:ℝ)) ^ (-β)) + E x * ((x:ℝ)) ^ (-β)
        + ∑ n ∈ Icc 1 (x - 1), E n * (((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β)) :=
    abel_master_identity a lam E hAE (fun n => ((n:ℝ)) ^ (-β)) x hx1
  -- Step 3: the E-part vs the full E-series
  have hbridgeE : SF = ((( ∑ n ∈ Icc 1 (x - 1),
      E n * (((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β)) : ℝ)) : ℂ) := by
    rw [hSF, Finset.sum_congr rfl (fun n _ => eabel_term_real E n β),
      ← Complex.ofReal_sum]
  have hSFre : (∑ n ∈ Icc 1 (x - 1),
      E n * (((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β))) = SF.re := by
    rw [hbridgeE, Complex.ofReal_re]
  have hEtail := eabel_tail_bound E C hC0 hE0 hE hβ1 hβ2 x hx
  have hSEle : ∑ n ∈ Icc 1 (x - 1), E n * (((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β))
      ≤ ES.re + 400 * C * ((x:ℝ)) ^ (7/8 - β) := by
    have h1 : (SF - ES).re ≤ ‖SF - ES‖ := Complex.re_le_norm _
    have h2 : ‖SF - ES‖ = ‖ES - SF‖ := norm_sub_rev _ _
    have h3 : (SF - ES).re = SF.re - ES.re := Complex.sub_re _ _
    rw [hSFre]
    have h4 : ‖ES - SF‖ ≤ 400 * C * ((x:ℝ)) ^ (7/8 - β) := hEtail
    linarith [h1, h2.le, h2.ge, h3.le, h3.ge, h4]
  -- Step 4: the ζ-part
  have hztr := zeta_truncation x hx hβ1 hβ2
  have hxc : ((x:ℂ)) ^ ((1:ℂ) - (β:ℂ)) = ((((x:ℝ)) ^ (1 - β) : ℝ) : ℂ) := by
    rw [show (1:ℂ) - (β:ℂ) = (((1 - β : ℝ)):ℂ) from by push_cast; ring,
      show ((x:ℂ)) = (((x:ℝ)):ℂ) from by push_cast; ring]
    exact (Complex.ofReal_cpow hx0.le (1 - β)).symm
  have hre_expr : ((((β:ℂ)) - 1) * (Z - SC) - ((x:ℂ)) ^ ((1:ℂ) - (β:ℂ))).re
      = (β - 1) * (Z.re - SC.re) - ((x:ℝ)) ^ (1 - β) := by
    rw [hxc, show (((β:ℂ)) - 1) = (((β - 1 : ℝ)):ℂ) from by push_cast; ring,
      Complex.sub_re, Complex.re_ofReal_mul, Complex.sub_re, Complex.ofReal_re]
  have habs : |(β - 1) * (Z.re - SC.re) - ((x:ℝ)) ^ (1 - β)| ≤ 11 * ((x:ℝ)) ^ (-β) := by
    rw [← hre_expr]
    calc |((((β:ℂ)) - 1) * (Z - SC) - ((x:ℂ)) ^ ((1:ℂ) - (β:ℂ))).re|
        ≤ ‖(((β:ℂ)) - 1) * (Z - SC) - ((x:ℂ)) ^ ((1:ℂ) - (β:ℂ))‖ :=
          Complex.abs_re_le_norm _
      _ ≤ 11 * ((x:ℝ)) ^ (-β) := hztr
  -- SC is the real partial sum
  have hSCre : SC = ((( ∑ n ∈ Icc 1 (x - 1), ((n:ℝ)) ^ (-β) : ℝ)) : ℂ) := by
    rw [hSC, show range x = insert 0 (Icc 1 (x - 1)) from by
      ext m
      simp only [Finset.mem_insert, Finset.mem_range, Finset.mem_Icc]
      omega, Finset.sum_insert (by
        simp only [Finset.mem_Icc]
        omega)]
    have h0 : (((0:ℕ)):ℂ) ^ (-(β:ℂ)) = 0 := by
      rw [Nat.cast_zero, Complex.zero_cpow]
      simp only [ne_eq, neg_eq_zero, Complex.ofReal_eq_zero]
      linarith
    rw [h0, zero_add, Finset.sum_congr rfl (fun n _ => cpow_real_cast n β),
      ← Complex.ofReal_sum]
  have hSx : ∑ n ∈ Icc 1 x, ((n:ℝ)) ^ (-β) = SC.re + ((x:ℝ)) ^ (-β) := by
    rw [hSCre, Complex.ofReal_re, show Icc 1 x = insert x (Icc 1 (x - 1)) from by
      ext m
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega, Finset.sum_insert (by
        simp only [Finset.mem_Icc]
        omega)]
    ring
  -- S.re ≤ Z.re + (x^{1−β} + 11x^{−β})/(1−β)
  have hSCbound : SC.re ≤ Z.re + (((x:ℝ)) ^ (1 - β) + 11 * ((x:ℝ)) ^ (-β)) / (1 - β) := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp habs
    rw [show Z.re + (((x:ℝ)) ^ (1 - β) + 11 * ((x:ℝ)) ^ (-β)) / (1 - β)
        = Z.re + (((x:ℝ)) ^ (1 - β) + 11 * ((x:ℝ)) ^ (-β)) * (1 - β)⁻¹ from by ring]
    have hkey : (SC.re - Z.re) * (1 - β) ≤ ((x:ℝ)) ^ (1 - β) + 11 * ((x:ℝ)) ^ (-β) := by
      nlinarith [hlo, hx1β]
    have h2 : SC.re - Z.re ≤ (((x:ℝ)) ^ (1 - β) + 11 * ((x:ℝ)) ^ (-β)) * (1 - β)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ h1β]
      exact hkey
    linarith
  -- x^{−β} ≤ x^{−β}/(1−β)
  have hxββ : ((x:ℝ)) ^ (-β) ≤ ((x:ℝ)) ^ (-β) / (1 - β) := by
    rw [le_div_iff₀ h1β]
    nlinarith [hxβ, hβ0]
  -- Step 5: the boundary term
  have hlogx : 1 + Real.log x ≤ 9 * ((x:ℝ)) ^ ((1:ℝ)/8) := by
    have h1 : Real.log x ≤ ((x:ℝ)) ^ ((1:ℝ)/8) / (1/8) :=
      Real.log_le_rpow_div hx0.le (by norm_num)
    have h2 : ((x:ℝ)) ^ ((1:ℝ)/8) / (1/8) = 8 * ((x:ℝ)) ^ ((1:ℝ)/8) := by ring
    have h3 : (1:ℝ) ≤ ((x:ℝ)) ^ ((1:ℝ)/8) := Real.one_le_rpow hx1r (by norm_num)
    linarith [h1, h2.le, h2.ge, h3]
  have hEx : E x * ((x:ℝ)) ^ (-β) ≤ 9 * C * ((x:ℝ)) ^ (7/8 - β) := by
    have h1 : E x ≤ |E x| := le_abs_self _
    have h2 := hE x hx1
    have hcollect78 : ((x:ℝ)) ^ ((3:ℝ)/4) * ((x:ℝ)) ^ ((1:ℝ)/8) = ((x:ℝ)) ^ ((7:ℝ)/8) := by
      rw [← Real.rpow_add hx0]
      norm_num
    have h3 : E x ≤ 9 * C * ((x:ℝ)) ^ ((7:ℝ)/8) := by
      calc E x ≤ C * (((x:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log x)) := le_trans h1 h2
        _ ≤ C * (((x:ℝ)) ^ ((3:ℝ)/4) * (9 * ((x:ℝ)) ^ ((1:ℝ)/8))) := by
            apply mul_le_mul_of_nonneg_left _ hC0
            apply mul_le_mul_of_nonneg_left hlogx (Real.rpow_nonneg hx0.le _)
        _ = 9 * C * (((x:ℝ)) ^ ((3:ℝ)/4) * ((x:ℝ)) ^ ((1:ℝ)/8)) := by ring
        _ = 9 * C * ((x:ℝ)) ^ ((7:ℝ)/8) := by rw [hcollect78]
    have hcollect : ((x:ℝ)) ^ ((7:ℝ)/8) * ((x:ℝ)) ^ (-β) = ((x:ℝ)) ^ (7/8 - β) := by
      rw [← Real.rpow_add hx0]
      congr 1
    calc E x * ((x:ℝ)) ^ (-β) ≤ (9 * C * ((x:ℝ)) ^ ((7:ℝ)/8)) * ((x:ℝ)) ^ (-β) :=
          mul_le_mul_of_nonneg_right h3 hxβ
      _ = 9 * C * (((x:ℝ)) ^ ((7:ℝ)/8) * ((x:ℝ)) ^ (-β)) := by ring
      _ = 9 * C * ((x:ℝ)) ^ (7/8 - β) := by rw [hcollect]
  -- Step 6: assemble
  have hGre : ((lam : ℂ) * Z + ES).re = lam * Z.re + ES.re := by
    rw [Complex.add_re, Complex.re_ofReal_mul]
  rw [hGre]
  -- lam·Σ_{n≤x} n^{−β} bounded
  have hlamS : lam * (∑ n ∈ Icc 1 x, ((n:ℝ)) ^ (-β))
      ≤ lam * Z.re + lam * (((x:ℝ)) ^ (1 - β) / (1 - β))
        + 12 * lam * (((x:ℝ)) ^ (-β) / (1 - β)) := by
    rw [hSx]
    have h1 : SC.re + ((x:ℝ)) ^ (-β)
        ≤ Z.re + (((x:ℝ)) ^ (1 - β) + 11 * ((x:ℝ)) ^ (-β)) / (1 - β)
          + ((x:ℝ)) ^ (-β) / (1 - β) := by
      linarith [hSCbound, hxββ]
    have h2 : Z.re + (((x:ℝ)) ^ (1 - β) + 11 * ((x:ℝ)) ^ (-β)) / (1 - β)
          + ((x:ℝ)) ^ (-β) / (1 - β)
        = Z.re + ((x:ℝ)) ^ (1 - β) / (1 - β) + 12 * (((x:ℝ)) ^ (-β) / (1 - β)) := by
      ring
    calc lam * (SC.re + ((x:ℝ)) ^ (-β))
        ≤ lam * (Z.re + ((x:ℝ)) ^ (1 - β) / (1 - β)
            + 12 * (((x:ℝ)) ^ (-β) / (1 - β))) := by
          apply mul_le_mul_of_nonneg_left _ hlam
          rw [← h2]
          exact h1
      _ = lam * Z.re + lam * (((x:ℝ)) ^ (1 - β) / (1 - β))
            + 12 * lam * (((x:ℝ)) ^ (-β) / (1 - β)) := by ring
  have hCx : (0:ℝ) ≤ C * ((x:ℝ)) ^ (7/8 - β) := mul_nonneg hC0 hx78
  linarith [hone, hiden.le, hiden.ge, hlamS, hEx, hSEle, hCx]

/-- **The λ-extraction at a vanishing continuation** (Siegel brick A3-a): when the
    master inequality's `G(β).re` term is `≤ 0` (a zero of the L-product) and
    `x ≥ (820(C+1))^{40}` kills the error term, the main term must carry the unit:
    `1−β ≤ 26·λ·x^{1−β}`. Pure arithmetic — the quantitative heart of the dichotomy. -/
theorem siegel_lambda_extraction (lam C : ℝ) (hlam : 0 ≤ lam) (hC0 : 0 ≤ C)
    {β : ℝ} (hβ1 : 9/10 < β) (hβ2 : β < 1) (x : ℕ) (hx : 2 ≤ x)
    (hxC : ((820 * (C + 1)) ^ (40:ℕ) : ℝ) ≤ (x:ℝ))
    (Gre : ℝ) (hG : Gre ≤ 0)
    (hmaster : 1 ≤ Gre + lam * (((x:ℝ)) ^ (1 - β) / (1 - β))
        + 12 * lam * (((x:ℝ)) ^ (-β) / (1 - β))
        + 410 * C * ((x:ℝ)) ^ (7/8 - β)) :
    1 - β ≤ 26 * lam * ((x:ℝ)) ^ (1 - β) := by
  have hx0 : (0:ℝ) < (x:ℝ) := by
    have : (0:ℕ) < x := by omega
    exact_mod_cast this
  have hx1r : (1:ℝ) ≤ (x:ℝ) := by
    have : (1:ℕ) ≤ x := by omega
    exact_mod_cast this
  have h1β : (0:ℝ) < 1 - β := by linarith
  have hy0 : (0:ℝ) < 820 * (C + 1) := by linarith
  -- error term ≤ 1/2
  have herr : 410 * C * ((x:ℝ)) ^ (7/8 - β) ≤ 1/2 := by
    have h1 : ((x:ℝ)) ^ (7/8 - β) ≤ ((x:ℝ)) ^ (-(1/40 : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le hx1r
      linarith
    have h2 : (820 * (C + 1)) ≤ ((x:ℝ)) ^ ((1/40 : ℝ)) := by
      have h3 : ((820 * (C + 1)) ^ (40:ℕ) : ℝ) ^ ((1/40 : ℝ)) ≤ ((x:ℝ)) ^ ((1/40 : ℝ)) := by
        apply Real.rpow_le_rpow (by positivity) hxC (by norm_num)
      have h4 : ((820 * (C + 1)) ^ (40:ℕ) : ℝ) ^ ((1/40 : ℝ)) = 820 * (C + 1) := by
        rw [← Real.rpow_natCast (820 * (C + 1)) 40, ← Real.rpow_mul hy0.le]
        norm_num
      rw [h4] at h3
      exact h3
    have h5 : ((x:ℝ)) ^ (-(1/40 : ℝ)) ≤ 1 / (820 * (C + 1)) := by
      rw [Real.rpow_neg hx0.le, ← one_div]
      apply one_div_le_one_div_of_le hy0 h2
    have h6 : 410 * C * ((x:ℝ)) ^ (7/8 - β) ≤ 410 * C * (1 / (820 * (C + 1))) := by
      apply mul_le_mul_of_nonneg_left (le_trans h1 h5) (by positivity)
    have h7 : 410 * C * (1 / (820 * (C + 1))) ≤ 1/2 := by
      rw [mul_one_div, div_le_div_iff₀ hy0 (by norm_num)]
      linarith
    linarith
  -- x^{−β} ≤ x^{1−β}
  have hmono : ((x:ℝ)) ^ (-β) ≤ ((x:ℝ)) ^ (1 - β) := by
    apply Real.rpow_le_rpow_of_exponent_le hx1r
    linarith
  have hx1β : (0:ℝ) ≤ ((x:ℝ)) ^ (1 - β) := Real.rpow_nonneg hx0.le _
  -- main-term consolidation: 1/2 ≤ 13·λ·x^{1−β}/(1−β)
  have hmain : (1:ℝ)/2 ≤ 13 * lam * ((x:ℝ)) ^ (1 - β) / (1 - β) := by
    have h8 : 12 * lam * (((x:ℝ)) ^ (-β) / (1 - β))
        ≤ 12 * lam * (((x:ℝ)) ^ (1 - β) / (1 - β)) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact div_le_div_of_nonneg_right hmono h1β.le
    have h9 : lam * (((x:ℝ)) ^ (1 - β) / (1 - β))
        + 12 * lam * (((x:ℝ)) ^ (1 - β) / (1 - β))
        = 13 * lam * ((x:ℝ)) ^ (1 - β) / (1 - β) := by
      ring
    linarith [hmaster, hG, herr, h8]
  -- clear the denominator
  rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) h1β] at hmain
  linarith

/-- **G is the L-product on the slit** (Siegel brick A3-b): the continuation
    `G = λζ + Σ'E(n)Δn` of the Dirichlet series agrees at every real
    `β ∈ (9/10, 1)` with ANY function `P` that is analytic on the slit half-plane
    and equals the L-series on `Re > 1` — in application, `P = ζ·L₁·L₂·L₁₂`,
    which VANISHES at a real zero `β₁` of `L(·,χ₁)`. -/
theorem G_eq_P_at_real (a : ℕ → ℂ) (lam : ℝ) (E : ℕ → ℝ) (C : ℝ)
    (hAE : ∀ n : ℕ, ∑ m ∈ Icc 1 n, a m = (lam * n : ℝ) + E n)
    (hC0 : 0 ≤ C) (hE0 : E 0 = 0)
    (hE : ∀ n : ℕ, 1 ≤ n → |E n| ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)))
    (hsum : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s)
    (P : ℂ → ℂ)
    (hP : ∀ s : ℂ, 9/10 < s.re → s ≠ 1 → DifferentiableAt ℂ P s)
    (hPeq : ∀ s : ℂ, 1 < s.re → LSeries a s = P s)
    {β : ℝ} (hβ1 : 9/10 < β) (hβ2 : β < 1) :
    (lam : ℂ) * riemannZeta ((β:ℂ))
      + (∑' n : ℕ, ((E n : ℝ) : ℂ)
          * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))
    = P ((β:ℂ)) := by
  -- the linear E-bound demanded by lseries_eq_G
  have hEb : ∀ n : ℕ, |E n| ≤ (9 * C) * n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hE0]
      simp
    · have hn1r : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      have hn0 : (0:ℝ) < (n:ℝ) := by linarith
      have hlogbound : 1 + Real.log n ≤ 9 * ((n:ℝ)) ^ ((1:ℝ)/8) := by
        have h1 : Real.log n ≤ ((n:ℝ)) ^ ((1:ℝ)/8) / (1/8) :=
          Real.log_le_rpow_div hn0.le (by norm_num)
        have h2 : ((n:ℝ)) ^ ((1:ℝ)/8) / (1/8) = 8 * ((n:ℝ)) ^ ((1:ℝ)/8) := by ring
        have h3 : (1:ℝ) ≤ ((n:ℝ)) ^ ((1:ℝ)/8) := Real.one_le_rpow hn1r (by norm_num)
        linarith [h1, h2.le, h2.ge, h3]
      have hcollect : ((n:ℝ)) ^ ((3:ℝ)/4) * ((n:ℝ)) ^ ((1:ℝ)/8) = ((n:ℝ)) ^ ((7:ℝ)/8) := by
        rw [← Real.rpow_add hn0]
        norm_num
      have h78 : ((n:ℝ)) ^ ((7:ℝ)/8) ≤ (n:ℝ) := by
        calc ((n:ℝ)) ^ ((7:ℝ)/8) ≤ ((n:ℝ)) ^ ((1:ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le hn1r (by norm_num)
          _ = (n:ℝ) := Real.rpow_one _
      calc |E n| ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := hE n hn
        _ ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (9 * ((n:ℝ)) ^ ((1:ℝ)/8))) := by
            apply mul_le_mul_of_nonneg_left _ hC0
            apply mul_le_mul_of_nonneg_left hlogbound (Real.rpow_nonneg hn0.le _)
        _ = 9 * C * (((n:ℝ)) ^ ((3:ℝ)/4) * ((n:ℝ)) ^ ((1:ℝ)/8)) := by ring
        _ = 9 * C * ((n:ℝ)) ^ ((7:ℝ)/8) := by rw [hcollect]
        _ ≤ (9 * C) * (n:ℝ) := by
            apply mul_le_mul_of_nonneg_left h78 (by positivity)
  -- the identity theorem
  have h₀re : 9/10 < ((β:ℂ)).re := by
    rw [Complex.ofReal_re]
    exact hβ1
  have h₀ne : ((β:ℂ)) ≠ 1 := by
    intro h
    rw [Complex.ofReal_eq_one] at h
    linarith
  exact eqOn_slit_halfplane
    (fun s : ℂ => (lam : ℂ) * riemannZeta s
      + ∑' n : ℕ, ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)))
    P
    (by
      intro s hs hs1
      apply DifferentiableAt.add
      · exact (differentiableAt_riemannZeta hs1).const_mul _
      · exact eseries_differentiableAt E C hC0 hE0 hE s hs)
    hP
    (by
      intro s hs
      rw [← lseries_eq_G a lam E (9 * C) hAE hEb hs (hsum s hs)]
      exact hPeq s hs)
    ((β:ℂ)) h₀re h₀ne

/-- **The λ lower bound at an L-product zero** (Siegel brick A3-c): a nonnegative
    coefficient system with `a(1) = 1`, `A = λ·id + E`, whose continued L-product `P`
    VANISHES at a real `β ∈ (9/10, 1)`, forces `1−β ≤ 26·λ·x^{1−β}` for every
    admissible truncation `x ≥ (820(C+1))^{40}` — Goldfeld's engine, fully wired. -/
theorem siegel_lambda_lower (a : ℕ → ℝ) (lam : ℝ) (E : ℕ → ℝ) (C : ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (ha1 : a 1 = 1) (hlam : 0 ≤ lam)
    (hAE : ∀ n : ℕ, ∑ m ∈ Icc 1 n, a m = lam * n + E n)
    (hC0 : 0 ≤ C) (hE0 : E 0 = 0)
    (hE : ∀ n : ℕ, 1 ≤ n → |E n| ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)))
    (hsum : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => ((a n : ℝ) : ℂ)) s)
    (P : ℂ → ℂ)
    (hP : ∀ s : ℂ, 9/10 < s.re → s ≠ 1 → DifferentiableAt ℂ P s)
    (hPeq : ∀ s : ℂ, 1 < s.re → LSeries (fun n => ((a n : ℝ) : ℂ)) s = P s)
    {β : ℝ} (hβ1 : 9/10 < β) (hβ2 : β < 1) (hPzero : P ((β:ℂ)) = 0)
    (x : ℕ) (hx : 2 ≤ x) (hxC : ((820 * (C + 1)) ^ (40:ℕ) : ℝ) ≤ (x:ℝ)) :
    1 - β ≤ 26 * lam * ((x:ℝ)) ^ (1 - β) := by
  -- the complex partial-sum hypothesis
  have hAEc : ∀ n : ℕ, ∑ m ∈ Icc 1 n, ((a m : ℝ) : ℂ) = ((lam * n : ℝ) : ℂ) + ((E n : ℝ) : ℂ) := by
    intro n
    rw [← Complex.ofReal_sum, hAE n]
    push_cast
    ring
  -- G(β) = P(β) = 0
  have hGP := G_eq_P_at_real (fun n => ((a n : ℝ) : ℂ)) lam E C hAEc hC0 hE0 hE hsum
    P hP hPeq hβ1 hβ2
  have hGzero : ((lam : ℂ) * riemannZeta ((β:ℂ))
      + ∑' n : ℕ, ((E n : ℝ) : ℂ)
          * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))).re = 0 := by
    rw [hGP, hPzero]
    exact Complex.zero_re
  -- the master inequality
  have hmaster := goldfeld_master_inequality a lam E C ha0 ha1 hlam hAE hC0 hE0 hE
    hβ1 hβ2 x hx
  -- extract λ
  exact siegel_lambda_extraction lam C hlam hC0 hβ1 hβ2 x hx hxC
    (((lam : ℂ) * riemannZeta ((β:ℂ))
      + ∑' n : ℕ, ((E n : ℝ) : ℂ)
          * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))).re)
    (le_of_eq hGzero) hmaster

/-- Values of a quadratic Dirichlet character lie in `{−1, 0, 1}` (A3-d1). -/
lemma real_char_repr {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1)
    (a : ZMod q) : χ a = -1 ∨ χ a = 0 ∨ χ a = 1 := by
  by_cases hu : IsUnit a
  · have hsq : χ a * χ a = 1 := by
      have h1 : (χ ^ 2) a = 1 := by
        rw [hχ2]
        exact MulChar.one_apply hu
      rw [pow_two, MulChar.mul_apply] at h1
      exact h1
    have hfactor : (χ a - 1) * (χ a + 1) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp hfactor with h | h
    · right; right
      exact sub_eq_zero.mp h
    · left
      have := eq_neg_of_add_eq_zero_left h
      exact this
  · right; left
    exact MulChar.map_nonunit χ hu

/-- The bare real-valued function of a quadratic Dirichlet character (A3-d0). -/
noncomputable def charFn (q : ℕ) (χ : DirichletCharacter ℂ q) : ℕ → ℝ :=
  fun n => (χ ((n : ZMod q))).re

/-- `charFn` represents `χ` (A3-d2): the character IS the cast of its real values. -/
lemma charFn_repr {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1) (n : ℕ) :
    ((charFn q χ n : ℝ) : ℂ) = χ ((n : ZMod q)) := by
  rcases real_char_repr χ hχ2 ((n : ZMod q)) with h | h | h <;>
    rw [charFn, h] <;> norm_num

/-- `charFn` takes values in `{−1, 0, 1}` (A3-d3). -/
lemma charFn_values {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1) (n : ℕ) :
    charFn q χ n = -1 ∨ charFn q χ n = 0 ∨ charFn q χ n = 1 := by
  rcases real_char_repr χ hχ2 ((n : ZMod q)) with h | h | h <;>
    rw [charFn, h] <;> norm_num

/-- `charFn` is bounded by 1 (A3-d3'). -/
lemma charFn_bound {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1) (n : ℕ) :
    |charFn q χ n| ≤ 1 := by
  rcases charFn_values χ hχ2 n with h | h | h <;> rw [h] <;> norm_num

/-- `charFn` is completely multiplicative (A3-d4). -/
lemma charFn_mul {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1) (m n : ℕ) :
    charFn q χ (m * n) = charFn q χ m * charFn q χ n := by
  have hc : ((charFn q χ (m * n) : ℝ) : ℂ)
      = ((charFn q χ m * charFn q χ n : ℝ) : ℂ) := by
    rw [charFn_repr χ hχ2 (m * n), Nat.cast_mul, map_mul,
      ← charFn_repr χ hχ2 m, ← charFn_repr χ hχ2 n]
    push_cast
    ring
  exact_mod_cast hc

/-- `charFn 1 = 1` (A3-d5). -/
lemma charFn_one {q : ℕ} (χ : DirichletCharacter ℂ q) : charFn q χ 1 = 1 := by
  rw [charFn, Nat.cast_one, map_one, Complex.one_re]

/-- **Character partial sums are bounded by the modulus** (Siegel brick A3-e):
    for a nontrivial quadratic `χ mod q`, `|Σ_{n≤t} χ(n)| ≤ q` — every block of `q`
    consecutive integers hits each residue once and cancels. The `hG` input of the
    whole divisor-asymptotic ladder. -/
theorem charFn_partial_sum_bound {q : ℕ} (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q)
    (hχ2 : χ ^ 2 = 1) (hχ1 : χ ≠ 1) :
    ∀ t : ℕ, |∑ n ∈ Icc 1 t, charFn q χ n| ≤ q := by
  haveI : NeZero q := ⟨by omega⟩
  -- one full block cancels
  have hblock : ∀ m : ℕ, ∑ n ∈ Icc (m + 1) (m + q), charFn q χ n = 0 := by
    intro m
    have hinj : ∀ n₁ ∈ Icc (m + 1) (m + q), ∀ n₂ ∈ Icc (m + 1) (m + q),
        ((n₁ : ZMod q)) = ((n₂ : ZMod q)) → n₁ = n₂ := by
      intro n₁ h₁ n₂ h₂ heq
      rw [Finset.mem_Icc] at h₁ h₂
      rcases Nat.le_total n₁ n₂ with hle | hle
      · have hmod : n₁ ≡ n₂ [MOD q] := (ZMod.natCast_eq_natCast_iff _ _ _).mp heq
        have hdvd : q ∣ n₂ - n₁ := (Nat.modEq_iff_dvd' hle).mp hmod
        have hz : n₂ - n₁ = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
        omega
      · have hmod : n₂ ≡ n₁ [MOD q] := (ZMod.natCast_eq_natCast_iff _ _ _).mp heq.symm
        have hdvd : q ∣ n₁ - n₂ := (Nat.modEq_iff_dvd' hle).mp hmod
        have hz : n₁ - n₂ = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
        omega
    have himg : (Icc (m + 1) (m + q)).image (fun n : ℕ => ((n : ZMod q)))
        = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_image_of_injOn (fun n₁ h₁ n₂ h₂ heq =>
        hinj n₁ (Finset.mem_coe.mp h₁) n₂ (Finset.mem_coe.mp h₂) heq),
        Nat.card_Icc, ZMod.card]
      omega
    have hcsum : ∑ n ∈ Icc (m + 1) (m + q), χ ((n : ZMod q)) = 0 := by
      have h1 : ∑ a ∈ (Icc (m + 1) (m + q)).image (fun n : ℕ => ((n : ZMod q))), χ a
          = ∑ n ∈ Icc (m + 1) (m + q), χ ((n : ZMod q)) := Finset.sum_image hinj
      rw [← h1, himg]
      exact MulChar.sum_eq_zero_of_ne_one hχ1
    have hreal : ((∑ n ∈ Icc (m + 1) (m + q), charFn q χ n : ℝ) : ℂ)
        = ∑ n ∈ Icc (m + 1) (m + q), χ ((n : ZMod q)) := by
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl (fun n _ => charFn_repr χ hχ2 n)
    exact_mod_cast hreal.trans hcsum
  -- strong induction in blocks of q
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    rcases Nat.lt_or_ge t q with h | h
    · calc |∑ n ∈ Icc 1 t, charFn q χ n|
          ≤ ∑ n ∈ Icc 1 t, |charFn q χ n| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ n ∈ Icc 1 t, (1:ℝ) := Finset.sum_le_sum (fun n _ => charFn_bound χ hχ2 n)
        _ = t := by
            rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
            norm_num
        _ ≤ q := by
            have : t ≤ q := h.le
            exact_mod_cast this
    · have hsplit : Icc 1 t = Icc 1 (t - q) ∪ Icc (t - q + 1) t := by
        ext n
        simp only [Finset.mem_union, Finset.mem_Icc]
        omega
      have hdisj : Disjoint (Icc 1 (t - q)) (Icc (t - q + 1) t) := by
        rw [Finset.disjoint_left]
        intro n hn hn2
        rw [Finset.mem_Icc] at hn hn2
        omega
      rw [hsplit, Finset.sum_union hdisj]
      have hb := hblock (t - q)
      rw [show t - q + q = t from by omega] at hb
      rw [hb, add_zero]
      exact ih (t - q) (by omega)

/-- **The product-character bridge** (Siegel brick A3-f): the bare real function of
    the level-`q₁q₂` product character is the pointwise product of the bare
    functions — non-units die on both sides, units factor through `changeLevel`. -/
theorem charFn_mul_char {q₁ q₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁2 : χ₁ ^ 2 = 1) (hχ₂2 : χ₂ ^ 2 = 1) (n : ℕ) :
    charFn (q₁ * q₂)
      ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
        * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) n
    = charFn q₁ χ₁ n * charFn q₂ χ₂ n := by
  simp only [charFn, MulChar.mul_apply]
  by_cases hu : IsUnit ((n : ZMod (q₁ * q₂)))
  · have huc : ((hu.unit : (ZMod (q₁ * q₂))ˣ) : ZMod (q₁ * q₂)) = ((n : ZMod (q₁ * q₂))) :=
      IsUnit.unit_spec hu
    have h₁ : (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁) ((n : ZMod (q₁ * q₂)))
        = χ₁ ((n : ZMod q₁)) := by
      rw [← huc,
        DirichletCharacter.changeLevel_eq_cast_of_dvd χ₁ (dvd_mul_right q₁ q₂) hu.unit,
        huc, ZMod.cast_natCast (dvd_mul_right q₁ q₂)]
    have h₂ : (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) ((n : ZMod (q₁ * q₂)))
        = χ₂ ((n : ZMod q₂)) := by
      rw [← huc,
        DirichletCharacter.changeLevel_eq_cast_of_dvd χ₂ (dvd_mul_left q₂ q₁) hu.unit,
        huc, ZMod.cast_natCast (dvd_mul_left q₂ q₁)]
    rw [h₁, h₂]
    rcases real_char_repr χ₁ hχ₁2 ((n : ZMod q₁)) with h1 | h1 | h1 <;>
      rcases real_char_repr χ₂ hχ₂2 ((n : ZMod q₂)) with h2 | h2 | h2 <;>
      rw [h1, h2] <;> norm_num
  · rw [MulChar.map_nonunit _ hu, zero_mul, Complex.zero_re]
    have hcop : ¬ Nat.Coprime n (q₁ * q₂) := fun hc =>
      hu ((ZMod.isUnit_iff_coprime n (q₁ * q₂)).mpr hc)
    have hsplit : ¬ Nat.Coprime n q₁ ∨ ¬ Nat.Coprime n q₂ := by
      by_contra hcon
      push_neg at hcon
      exact hcop (Nat.Coprime.mul_right hcon.1 hcon.2)
    rcases hsplit with h | h
    · have hnu : ¬ IsUnit ((n : ZMod q₁)) := fun hun =>
        h ((ZMod.isUnit_iff_coprime _ _).mp hun)
      rw [MulChar.map_nonunit _ hnu, Complex.zero_re, zero_mul]
    · have hnu : ¬ IsUnit ((n : ZMod q₂)) := fun hun =>
        h ((ZMod.isUnit_iff_coprime _ _).mp hun)
      rw [MulChar.map_nonunit _ hnu, Complex.zero_re, mul_zero]

/-- Convolving a power-bounded arithmetic function with a 1-bounded bare function
    raises the power by one (A3-g1a helper). -/
lemma conv_abs_le_pow (F : ArithmeticFunction ℝ) (k : ℕ → ℝ) (t : ℕ)
    (hF : ∀ j : ℕ, |F j| ≤ ((j:ℝ)) ^ t) (hkb : ∀ j, |k j| ≤ 1) (m : ℕ) :
    |(F * toArith k) m| ≤ ((m:ℝ)) ^ (t + 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [ArithmeticFunction.map_zero, abs_zero, Nat.cast_zero, zero_pow (by omega)]
  · have hkb' : ∀ j : ℕ, |toArith k j| ≤ 1 := by
      intro j
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp [toArith]
      · rw [toArith_apply k j (by omega)]
        exact hkb j
    rw [ArithmeticFunction.mul_apply]
    calc |∑ p ∈ m.divisorsAntidiagonal, F p.1 * toArith k p.2|
        ≤ ∑ p ∈ m.divisorsAntidiagonal, |F p.1 * toArith k p.2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ m.divisorsAntidiagonal, ((m:ℝ)) ^ t := by
          apply Finset.sum_le_sum
          intro p hp
          obtain ⟨he, _⟩ := Nat.mem_divisorsAntidiagonal.mp hp
          have hp1m : p.1 ≤ m := Nat.le_of_dvd hm (Dvd.intro p.2 he)
          have hcast : ((p.1:ℝ)) ^ t ≤ ((m:ℝ)) ^ t :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hp1m) t
          rw [abs_mul]
          calc |F p.1| * |toArith k p.2| ≤ ((p.1:ℝ)) ^ t * 1 :=
                mul_le_mul (hF p.1) (hkb' p.2) (abs_nonneg _)
                  (le_trans (abs_nonneg _) (hF p.1))
            _ = ((p.1:ℝ)) ^ t := mul_one _
            _ ≤ ((m:ℝ)) ^ t := hcast
      _ = (m.divisorsAntidiagonal.card : ℝ) * ((m:ℝ)) ^ t := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((m:ℝ)) * ((m:ℝ)) ^ t := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hcard : m.divisorsAntidiagonal.card ≤ m := by
            have hmap : ∀ p ∈ m.divisorsAntidiagonal, p.1 ∈ Icc 1 m := by
              intro p hp
              obtain ⟨he, hm0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
              rw [Finset.mem_Icc]
              constructor
              · by_contra h0
                push_neg at h0
                have h1 : p.1 = 0 := by omega
                rw [h1, zero_mul] at he
                omega
              · exact Nat.le_of_dvd hm (Dvd.intro p.2 he)
            have hinj : ∀ p ∈ m.divisorsAntidiagonal, ∀ p' ∈ m.divisorsAntidiagonal,
                p.1 = p'.1 → p = p' := by
              intro p hp p' hp' hfst
              obtain ⟨he, hm0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
              obtain ⟨he', _⟩ := Nat.mem_divisorsAntidiagonal.mp hp'
              have h1 : p.1 ≠ 0 := by
                intro h0
                rw [h0, zero_mul] at he
                omega
              have h2 : p.2 = p'.2 := by
                apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h1)
                rw [he, hfst, he']
              exact Prod.ext hfst h2
            calc m.divisorsAntidiagonal.card ≤ (Icc 1 m).card :=
                  Finset.card_le_card_of_injOn (fun p => p.1)
                    (fun p hp => hmap p hp)
                    (fun p hp p' hp' h => hinj p hp p' hp' h)
              _ = m := by rw [Nat.card_Icc]; omega
          exact_mod_cast hcard
      _ = ((m:ℝ)) ^ (t + 1) := by ring

/-- The quadruple convolution is crudely cubed-bounded (A3-g1a): `|a(m)| ≤ m³`. -/
lemma quad_value_le_cube (g₁ g₂ : ℕ → ℝ)
    (h1b : ∀ n, |g₁ n| ≤ 1) (h2b : ∀ n, |g₂ n| ≤ 1) (m : ℕ) :
    |(toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
        * toArith (fun k => g₁ k * g₂ k)) m| ≤ ((m:ℝ)) ^ (3:ℕ) := by
  have h12b : ∀ n, |g₁ n * g₂ n| ≤ 1 := by
    intro n
    rw [abs_mul]
    calc |g₁ n| * |g₂ n| ≤ 1 * 1 :=
        mul_le_mul (h1b n) (h2b n) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have h1 : ∀ j : ℕ, |(toArith (fun _ => (1:ℝ))) j| ≤ ((j:ℝ)) ^ (0:ℕ) := by
    intro j
    rw [pow_zero]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [toArith]
    · rw [toArith_apply _ j (by omega)]
      norm_num
  have h2 := fun j => conv_abs_le_pow (toArith (fun _ => (1:ℝ))) g₁ 0 h1 h1b j
  have h3 := fun j => conv_abs_le_pow (toArith (fun _ => (1:ℝ)) * toArith g₁) g₂ 1 h2 h2b j
  exact conv_abs_le_pow (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂)
    (fun k => g₁ k * g₂ k) 2 h3 h12b m

/-- **The E-package** (Siegel brick A3-g1): the hyperbola asymptotic upgraded to the
    Goldfeld-shape error bound at EVERY `n ≥ 1` — `|A(n) − L₁Lk·n| ≤ C·n^{3/4}(1+log n)`
    with `C = 30(1+q₁)(1+B) + 36 + 3|L₁Lk|` (small `n` patched by the cube bound). -/
theorem quad_E_package (g₁ g₂ : ℕ → ℝ) (q₁ B L₁ Lk : ℝ)
    (h1b : ∀ n, |g₁ n| ≤ 1) (h2b : ∀ n, |g₂ n| ≤ 1)
    (hL₁ : ∀ y : ℕ, |L₁ - ∑ d ∈ Icc 1 y, g₁ d / d| ≤ 2 * q₁ / (y + 1))
    (hq₁ : 0 ≤ q₁)
    (hH : ∀ M : ℕ, 1 ≤ M →
      |∑ n ∈ Icc 1 M, (toArith (fun _ => (1:ℝ)) * toArith g₁) n - L₁ * M|
        ≤ (1 + 4 * q₁) * (Real.sqrt M + 1))
    (hKb : ∀ t : ℕ, |∑ n ∈ Icc 1 t, (toArith g₂ * toArith (fun m => g₁ m * g₂ m)) n|
        ≤ B * (Real.sqrt t + 1))
    (hLk : ∀ y : ℕ, 1 ≤ y →
      |Lk - ∑ d ∈ Icc 1 y, (toArith g₂ * toArith (fun m => g₁ m * g₂ m)) d / d|
        ≤ 7 * B / Real.sqrt y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
          * toArith (fun k => g₁ k * g₂ k)) m - L₁ * Lk * n|
        ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
  have hB0 : 0 ≤ B := by
    have h0 := hKb 0
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, abs_zero,
      Nat.cast_zero, Real.sqrt_zero, zero_add, mul_one] at h0
    exact h0
  refine ⟨30 * (1 + q₁) * (1 + B) + 36 + 3 * |L₁ * Lk|, by positivity, ?_⟩
  intro n hn
  have hn0 : (0:ℝ) < (n:ℝ) := by
    have : (0:ℕ) < n := hn
    exact_mod_cast this
  have hn1r : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have htge1 : (1:ℝ) ≤ ((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n) := by
    have h1 : (1:ℝ) ≤ ((n:ℝ)) ^ ((3:ℝ)/4) := Real.one_le_rpow hn1r (by norm_num)
    have h2 : (1:ℝ) ≤ 1 + Real.log n := by
      have := Real.log_nonneg hn1r
      linarith
    nlinarith [h1, h2]
  have ht0 : (0:ℝ) ≤ ((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n) := by linarith
  rcases Nat.lt_or_ge n 4 with h4 | h4
  · -- n ∈ {1, 2, 3}: cube bound
    have hA : |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
        * toArith (fun k => g₁ k * g₂ k)) m| ≤ 36 := by
      calc |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
            * toArith (fun k => g₁ k * g₂ k)) m|
          ≤ ∑ m ∈ Icc 1 n, |(toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
            * toArith (fun k => g₁ k * g₂ k)) m| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ m ∈ Icc 1 n, ((m:ℝ)) ^ (3:ℕ) :=
            Finset.sum_le_sum (fun m _ => quad_value_le_cube g₁ g₂ h1b h2b m)
        _ ≤ ∑ m ∈ Icc (1:ℕ) 3, ((m:ℝ)) ^ (3:ℕ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro m hm
              rw [Finset.mem_Icc] at hm ⊢
              omega
            · intro m _ _
              positivity
        _ = 36 := by
            rw [show (Icc (1:ℕ) 3 : Finset ℕ) = {1, 2, 3} by decide]
            norm_num [Finset.sum_insert, Finset.mem_insert, Finset.sum_singleton]
    have h3n : (n:ℝ) ≤ 3 := by
      have : n ≤ 3 := by omega
      exact_mod_cast this
    have hlam : |L₁ * Lk| * (n:ℝ) ≤ 3 * |L₁ * Lk| := by
      nlinarith [abs_nonneg (L₁ * Lk), h3n]
    have htri : |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
        * toArith (fun k => g₁ k * g₂ k)) m - L₁ * Lk * n|
        ≤ |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
            * toArith (fun k => g₁ k * g₂ k)) m| + |L₁ * Lk * (n:ℝ)| := by
      have h := abs_add_le (∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁
          * toArith g₂ * toArith (fun k => g₁ k * g₂ k)) m) (-(L₁ * Lk * (n:ℝ)))
      rw [abs_neg, ← sub_eq_add_neg] at h
      exact h
    have habsmul : |L₁ * Lk * (n:ℝ)| = |L₁ * Lk| * (n:ℝ) := by
      rw [abs_mul, Nat.abs_cast]
    calc |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
          * toArith (fun k => g₁ k * g₂ k)) m - L₁ * Lk * n|
        ≤ 36 + 3 * |L₁ * Lk| := by
          rw [habsmul] at htri
          linarith [htri, hA, hlam]
      _ = (36 + 3 * |L₁ * Lk|) * 1 := (mul_one _).symm
      _ ≤ (36 + 3 * |L₁ * Lk|) * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
          apply mul_le_mul_of_nonneg_left htge1 (by positivity)
      _ ≤ (30 * (1 + q₁) * (1 + B) + 36 + 3 * |L₁ * Lk|)
            * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
          apply mul_le_mul_of_nonneg_right _ ht0
          nlinarith [hq₁, hB0]
  · -- n ≥ 4: the hyperbola asymptotic
    have hmain := quad_coeff_asymptotic g₁ g₂ q₁ B L₁ Lk h1b h2b hL₁ hq₁ hH hKb hLk n h4
    have hconv : Real.sqrt n * Real.sqrt (Real.sqrt n) = ((n:ℝ)) ^ ((3:ℝ)/4) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
        ← Real.rpow_mul hn0.le, ← Real.rpow_add hn0]
      norm_num
    rw [hconv] at hmain
    calc |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
          * toArith (fun k => g₁ k * g₂ k)) m - L₁ * Lk * n|
        ≤ 30 * (1 + q₁) * (1 + B) * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := hmain
      _ ≤ (30 * (1 + q₁) * (1 + B) + 36 + 3 * |L₁ * Lk|)
            * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
          apply mul_le_mul_of_nonneg_right _ ht0
          nlinarith [abs_nonneg (L₁ * Lk)]

/-- **The character quad system** (Siegel brick A3-g2): for nontrivial quadratic
    `χ₁ mod q₁`, `χ₂ mod q₂` with nontrivial product, the Goldfeld coefficient system
    exists — `L₁, Lk` with their approach rates and the full error package. -/
theorem quad_system_for_chars {q₁ q₂ : ℕ} (hq₁ : 1 ≤ q₁) (hq₂ : 1 ≤ q₂)
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁2 : χ₁ ^ 2 = 1) (hχ₂2 : χ₂ ^ 2 = 1) (hχ₁1 : χ₁ ≠ 1) (hχ₂1 : χ₂ ≠ 1)
    (hχ₃1 : (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
        * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) ≠ 1) :
    ∃ L₁ Lk C : ℝ,
      (∀ y : ℕ, |L₁ - ∑ d ∈ Icc 1 y, charFn q₁ χ₁ d / d| ≤ 2 * (q₁:ℝ) / (y + 1))
      ∧ (∀ y : ℕ, 1 ≤ y →
          |Lk - ∑ d ∈ Icc 1 y, (toArith (charFn q₂ χ₂)
              * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) d / d|
            ≤ 7 * (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) / Real.sqrt y)
      ∧ 0 ≤ C
      ∧ ∀ n : ℕ, 1 ≤ n →
        |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith (charFn q₁ χ₁)
            * toArith (charFn q₂ χ₂)
            * toArith (fun k => charFn q₁ χ₁ k * charFn q₂ χ₂ k)) m - L₁ * Lk * n|
          ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
  have h1b := fun n => charFn_bound χ₁ hχ₁2 n
  have h2b := fun n => charFn_bound χ₂ hχ₂2 n
  have hG₁ := charFn_partial_sum_bound hq₁ χ₁ hχ₁2 hχ₁1
  have hG₂ := charFn_partial_sum_bound hq₂ χ₂ hχ₂2 hχ₂1
  obtain ⟨L₁, hL₁⟩ := log_mean_exists (charFn q₁ χ₁) ((q₁:ℝ)) hG₁
  -- hH: commute the divisor asymptotic
  have hH : ∀ M : ℕ, 1 ≤ M →
      |∑ n ∈ Icc 1 M, (toArith (fun _ => (1:ℝ)) * toArith (charFn q₁ χ₁)) n - L₁ * M|
        ≤ (1 + 4 * (q₁:ℝ)) * (Real.sqrt M + 1) := by
    intro M hM
    have hcomm : toArith (fun _ => (1:ℝ)) * toArith (charFn q₁ χ₁)
        = toArith (charFn q₁ χ₁) * toArith (fun _ => (1:ℝ)) := mul_comm _ _
    rw [hcomm]
    exact divisor_char_asymptotic (charFn q₁ χ₁) ((q₁:ℝ)) L₁ h1b hG₁ hL₁ M hM
  -- the product character is quadratic
  have hχ₃2 : ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
      * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) ^ 2 = 1 := by
    rw [mul_pow, ← map_pow, ← map_pow, hχ₁2, hχ₂2, map_one, map_one, mul_one]
  have hq₁₂ : 1 ≤ q₁ * q₂ :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hG₃ := charFn_partial_sum_bound hq₁₂ _ hχ₃2 hχ₃1
  -- the product bare function is 1-bounded with q₁q₂-bounded partial sums
  have h12b : ∀ n, |charFn q₁ χ₁ n * charFn q₂ χ₂ n| ≤ 1 := by
    intro n
    rw [abs_mul]
    calc |charFn q₁ χ₁ n| * |charFn q₂ χ₂ n| ≤ 1 * 1 :=
        mul_le_mul (h1b n) (h2b n) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hK2 : ∀ t : ℕ, |∑ n ∈ Icc 1 t, (charFn q₁ χ₁ n * charFn q₂ χ₂ n)|
      ≤ (q₁:ℝ) * (q₂:ℝ) := by
    intro t
    have heq : ∑ n ∈ Icc 1 t, (charFn q₁ χ₁ n * charFn q₂ χ₂ n)
        = ∑ n ∈ Icc 1 t, charFn (q₁ * q₂)
            ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
              * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) n :=
      Finset.sum_congr rfl (fun n _ => (charFn_mul_char χ₁ χ₂ hχ₁2 hχ₂2 n).symm)
    rw [heq]
    have h := hG₃ t
    push_cast at h
    exact h
  have hKb : ∀ t : ℕ, |∑ n ∈ Icc 1 t, (toArith (charFn q₂ χ₂)
      * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) n|
      ≤ (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) * (Real.sqrt t + 1) :=
    fun t => bounded_conv_sqrt_bound (charFn q₂ χ₂)
      (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m) ((q₂:ℝ)) ((q₁:ℝ) * (q₂:ℝ))
      h2b h12b hG₂ hK2 t
  obtain ⟨Lk, hLk⟩ := sqrt_mean_exists
    (fun d => (toArith (charFn q₂ χ₂)
      * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) d)
    (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) hKb
  obtain ⟨C, hC0, hE⟩ := quad_E_package (charFn q₁ χ₁) (charFn q₂ χ₂)
    ((q₁:ℝ)) (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) L₁ Lk h1b h2b hL₁
    (by positivity) hH hKb hLk
  exact ⟨L₁, Lk, C, hL₁, hLk, hC0, hE⟩

/-- **Nonnegative partial sums force a nonnegative density** (Siegel brick A3-g3a):
    if `A(n) ≥ 0` and `|A(n) − λn| ≤ C·n^{3/4}(1+log n)` then `λ ≥ 0` — the error is
    `o(n)`, so a negative λ would drag `A` negative. -/
theorem lam_nonneg (A : ℕ → ℝ) (lam C : ℝ) (hC0 : 0 ≤ C)
    (hA0 : ∀ n : ℕ, 0 ≤ A n)
    (hE : ∀ n : ℕ, 1 ≤ n →
      |A n - lam * n| ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n))) :
    0 ≤ lam := by
  by_contra hneg
  push_neg at hneg
  have hε : (0:ℝ) < -lam := by linarith
  set ε : ℝ := -lam with hεdef
  have hy0 : (0:ℝ) ≤ 9 * C / ε + 1 := by positivity
  -- choose n with n^{1/8} ≥ 9C/ε + 1
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge ((9 * C / ε + 1) ^ (8:ℕ))
  set n : ℕ := max n₀ 1 with hn
  have hn1 : 1 ≤ n := le_max_right _ _
  have hn1r : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
  have hnr0 : (0:ℝ) < (n:ℝ) := by linarith
  have hnbig : ((9 * C / ε + 1) ^ (8:ℕ) : ℝ) ≤ (n:ℝ) := by
    calc ((9 * C / ε + 1) ^ (8:ℕ) : ℝ) ≤ (n₀:ℝ) := hn₀
      _ ≤ (n:ℝ) := by
          have : n₀ ≤ n := le_max_left _ _
          exact_mod_cast this
  -- n^{1/8} ≥ 9C/ε + 1
  have heighth : 9 * C / ε + 1 ≤ ((n:ℝ)) ^ ((1:ℝ)/8) := by
    have h1 : ((9 * C / ε + 1) ^ (8:ℕ) : ℝ) ^ ((1:ℝ)/8) ≤ ((n:ℝ)) ^ ((1:ℝ)/8) :=
      Real.rpow_le_rpow (by positivity) hnbig (by norm_num)
    have h2 : ((9 * C / ε + 1) ^ (8:ℕ) : ℝ) ^ ((1:ℝ)/8) = 9 * C / ε + 1 := by
      rw [← Real.rpow_natCast (9 * C / ε + 1) 8, ← Real.rpow_mul hy0]
      norm_num
    rw [h2] at h1
    exact h1
  -- the E-bound at n: ε·n ≤ 9C·n^{7/8}
  have hlog : 1 + Real.log n ≤ 9 * ((n:ℝ)) ^ ((1:ℝ)/8) := by
    have h1 : Real.log n ≤ ((n:ℝ)) ^ ((1:ℝ)/8) / (1/8) :=
      Real.log_le_rpow_div hnr0.le (by norm_num)
    have h2 : ((n:ℝ)) ^ ((1:ℝ)/8) / (1/8) = 8 * ((n:ℝ)) ^ ((1:ℝ)/8) := by ring
    have h3 : (1:ℝ) ≤ ((n:ℝ)) ^ ((1:ℝ)/8) := Real.one_le_rpow hn1r (by norm_num)
    linarith [h1, h2.le, h2.ge, h3]
  have hcollect : ((n:ℝ)) ^ ((3:ℝ)/4) * ((n:ℝ)) ^ ((1:ℝ)/8) = ((n:ℝ)) ^ ((7:ℝ)/8) := by
    rw [← Real.rpow_add hnr0]
    norm_num
  have hbound : ε * (n:ℝ) ≤ 9 * C * ((n:ℝ)) ^ ((7:ℝ)/8) := by
    have h1 := (abs_le.mp (hE n hn1)).2
    have h2 : lam * n ≥ A n - C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
      linarith
    have h3 : ε * (n:ℝ) ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
      have := hA0 n
      rw [hεdef]
      nlinarith [h2, this]
    calc ε * (n:ℝ) ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := h3
      _ ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (9 * ((n:ℝ)) ^ ((1:ℝ)/8))) := by
          apply mul_le_mul_of_nonneg_left _ hC0
          apply mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hnr0.le _)
      _ = 9 * C * (((n:ℝ)) ^ ((3:ℝ)/4) * ((n:ℝ)) ^ ((1:ℝ)/8)) := by ring
      _ = 9 * C * ((n:ℝ)) ^ ((7:ℝ)/8) := by rw [hcollect]
  -- divide by n^{7/8}: ε·n^{1/8} ≤ 9C
  have hsplit : (n:ℝ) = ((n:ℝ)) ^ ((7:ℝ)/8) * ((n:ℝ)) ^ ((1:ℝ)/8) := by
    rw [← Real.rpow_add hnr0]
    norm_num
  have h78pos : (0:ℝ) < ((n:ℝ)) ^ ((7:ℝ)/8) := Real.rpow_pos_of_pos hnr0 _
  have hdiv : ε * ((n:ℝ)) ^ ((1:ℝ)/8) ≤ 9 * C := by
    have h1 : (ε * ((n:ℝ)) ^ ((1:ℝ)/8)) * ((n:ℝ)) ^ ((7:ℝ)/8)
        ≤ (9 * C) * ((n:ℝ)) ^ ((7:ℝ)/8) := by
      calc (ε * ((n:ℝ)) ^ ((1:ℝ)/8)) * ((n:ℝ)) ^ ((7:ℝ)/8)
          = ε * (((n:ℝ)) ^ ((7:ℝ)/8) * ((n:ℝ)) ^ ((1:ℝ)/8)) := by ring
        _ = ε * (n:ℝ) := by rw [← hsplit]
        _ ≤ 9 * C * ((n:ℝ)) ^ ((7:ℝ)/8) := hbound
    exact le_of_mul_le_mul_right h1 h78pos
  -- but ε·n^{1/8} ≥ ε·(9C/ε + 1) = 9C + ε
  have hlow : 9 * C + ε ≤ ε * ((n:ℝ)) ^ ((1:ℝ)/8) := by
    have h1 : ε * (9 * C / ε + 1) ≤ ε * ((n:ℝ)) ^ ((1:ℝ)/8) :=
      mul_le_mul_of_nonneg_left heighth hε.le
    have h2 : ε * (9 * C / ε + 1) = 9 * C + ε := by
      field_simp
    linarith [h1, h2.le, h2.ge]
  linarith [hdiv, hlow, hε]

open scoped LSeries.notation in
/-- The quadruple cast bridge exposed (A3-g3b-i): the ℂ-cast of the coefficient
    sequence is the triple `⍟`-convolution of the four cast factors. -/
lemma quad_cast_bridge (g₁ g₂ : ℕ → ℝ) :
    (fun n => (((toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
        * toArith (fun m => g₁ m * g₂ m)) n : ℝ) : ℂ))
    = ((castFn (fun _ => (1:ℝ)) ⍟ castFn g₁) ⍟ castFn g₂)
        ⍟ castFn (fun m => g₁ m * g₂ m) := by
  funext n
  have step1 : (((toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
      * toArith (fun m => g₁ m * g₂ m)) n : ℝ) : ℂ)
      = ((fun m => (((toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂) m : ℝ) : ℂ))
        ⍟ castFn (fun m => g₁ m * g₂ m)) n := by
    rw [ArithmeticFunction.mul_apply, LSeries.convolution_def]
    push_cast
    apply Finset.sum_congr rfl
    intro p hp
    rw [Nat.mem_divisorsAntidiagonal] at hp
    have h2 : p.2 ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hp
      exact hp.2 hp.1.symm
    rw [castFn]
  rw [step1]
  have step2 : (fun m => (((toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂) m : ℝ) : ℂ))
      = (fun m => (((toArith (fun _ => (1:ℝ)) * toArith g₁) m : ℝ) : ℂ)) ⍟ castFn g₂ := by
    funext m
    rw [ArithmeticFunction.mul_apply, LSeries.convolution_def]
    push_cast
    apply Finset.sum_congr rfl
    intro p hp
    rw [Nat.mem_divisorsAntidiagonal] at hp
    have h2 : p.2 ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hp
      exact hp.2 hp.1.symm
    rw [castFn]
  rw [step2]
  have step3 : (fun m => (((toArith (fun _ => (1:ℝ)) * toArith g₁) m : ℝ) : ℂ))
      = castFn (fun _ => (1:ℝ)) ⍟ castFn g₁ := by
    funext m
    exact castFn_conv (fun _ => (1:ℝ)) g₁ m
  rw [step3]

/-- Summability of the quadruple coefficient series on `Re s > 1` (A3-g3b-ii). -/
lemma quad_LSeriesSummable (g₁ g₂ : ℕ → ℝ)
    (h1b : ∀ n, |g₁ n| ≤ 1) (h2b : ∀ n, |g₂ n| ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (((toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
        * toArith (fun m => g₁ m * g₂ m)) n : ℝ) : ℂ)) s := by
  have honeb : ∀ n : ℕ, |(fun _ : ℕ => (1:ℝ)) n| ≤ 1 := fun n => by norm_num
  have hg12b : ∀ n, |g₁ n * g₂ n| ≤ 1 := by
    intro n
    rw [abs_mul]
    calc |g₁ n| * |g₂ n| ≤ 1 * 1 := mul_le_mul (h1b n) (h2b n) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  rw [quad_cast_bridge g₁ g₂]
  exact (((castFn_summable (fun _ => (1:ℝ)) honeb hs).convolution
    (castFn_summable g₁ h1b hs)).convolution
    (castFn_summable g₂ h2b hs)).convolution
    (castFn_summable (fun m => g₁ m * g₂ m) hg12b hs)

/-- The cast of `charFn` is the character's naive coefficient function away
    from `0` (A3-g3b-iii). -/
lemma castFn_charFn {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1)
    {n : ℕ} (hn : n ≠ 0) :
    castFn (charFn q χ) n = χ ((n : ZMod q)) := by
  show ((toArith (charFn q χ) n : ℝ) : ℂ) = χ ((n : ZMod q))
  rw [toArith_apply _ n hn, charFn_repr χ hχ2 n]

/-- **The Goldfeld product identity at characters** (Siegel brick A3-g3b): on
    `Re s > 1` the quadruple L-series IS `ζ·L(χ₁)·L(χ₂)·L(χ₁χ₂)`. -/
theorem quad_P_identity {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁2 : χ₁ ^ 2 = 1) (hχ₂2 : χ₂ ^ 2 = 1) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (((toArith (fun _ => (1:ℝ)) * toArith (charFn q₁ χ₁)
        * toArith (charFn q₂ χ₂)
        * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) n : ℝ) : ℂ)) s
    = riemannZeta s * DirichletCharacter.LFunction χ₁ s
        * DirichletCharacter.LFunction χ₂ s
        * DirichletCharacter.LFunction
            ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
              * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) s := by
  have h1b := fun n => charFn_bound χ₁ hχ₁2 n
  have h2b := fun n => charFn_bound χ₂ hχ₂2 n
  rw [quad_LSeries_eq (charFn q₁ χ₁) (charFn q₂ χ₂) h1b h2b hs]
  have hχ₃2 : ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
      * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) ^ 2 = 1 := by
    rw [mul_pow, ← map_pow, ← map_pow, hχ₁2, hχ₂2, map_one, map_one, mul_one]
  have hz : LSeries (castFn (fun _ => (1:ℝ))) s = riemannZeta s := by
    rw [← LSeries_one_eq_riemannZeta hs]
    apply LSeries_congr
    intro n hn
    show ((toArith (fun _ => (1:ℝ)) n : ℝ) : ℂ) = (1 : ℕ → ℂ) n
    rw [toArith_apply _ n hn, Pi.one_apply, Complex.ofReal_one]
  have hL1 : LSeries (castFn (charFn q₁ χ₁)) s = DirichletCharacter.LFunction χ₁ s := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ₁ hs]
    exact LSeries_congr (fun {n} hn => castFn_charFn χ₁ hχ₁2 hn) s
  have hL2 : LSeries (castFn (charFn q₂ χ₂)) s = DirichletCharacter.LFunction χ₂ s := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ₂ hs]
    exact LSeries_congr (fun {n} hn => castFn_charFn χ₂ hχ₂2 hn) s
  have hL3 : LSeries (castFn (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) s
      = DirichletCharacter.LFunction
          ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
            * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) s := by
    rw [DirichletCharacter.LFunction_eq_LSeries _ hs]
    apply LSeries_congr
    intro n hn
    show ((toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m) n : ℝ) : ℂ) = _
    rw [toArith_apply _ n hn, ← charFn_mul_char χ₁ χ₂ hχ₁2 hχ₂2 n,
      charFn_repr _ hχ₃2 n]
  rw [hz, hL1, hL2, hL3]

/-- The four-factor product is analytic on the slit half-plane (A3-g3b-iv). -/
lemma quad_P_differentiableAt {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁1 : χ₁ ≠ 1) (hχ₂1 : χ₂ ≠ 1)
    (hχ₃1 : (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
        * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) ≠ 1)
    (s : ℂ) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (fun w => riemannZeta w * DirichletCharacter.LFunction χ₁ w
      * DirichletCharacter.LFunction χ₂ w
      * DirichletCharacter.LFunction
          ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
            * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) w) s := by
  apply DifferentiableAt.mul
  · apply DifferentiableAt.mul
    · apply DifferentiableAt.mul
      · exact differentiableAt_riemannZeta hs1
      · exact (DirichletCharacter.differentiable_LFunction hχ₁1).differentiableAt
    · exact (DirichletCharacter.differentiable_LFunction hχ₂1).differentiableAt
  · exact (DirichletCharacter.differentiable_LFunction hχ₃1).differentiableAt

/-- **SIEGEL'S λ LOWER BOUND AT CHARACTERS** (Siegel brick A3-g3c): if the product
    `ζ·L(χ₁)·L(χ₂)·L(χ₁χ₂)` vanishes at a real `β ∈ (9/10, 1)` — e.g. at a real zero
    of `L(·,χ₁)` — then `λ = L₁·Lk > (1−β)/(26·x^{1−β})` for every admissible `x`,
    with `L₁, Lk` carrying their partial-sum approach rates. -/
theorem siegel_lambda_lower_for_chars {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁2 : χ₁ ^ 2 = 1) (hχ₂2 : χ₂ ^ 2 = 1) (hχ₁1 : χ₁ ≠ 1) (hχ₂1 : χ₂ ≠ 1)
    (hχ₃1 : (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
        * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) ≠ 1)
    {β : ℝ} (hβ1 : 9/10 < β) (hβ2 : β < 1)
    (hzero : DirichletCharacter.LFunction χ₁ ((β:ℂ)) = 0) :
    ∃ L₁ Lk C : ℝ, 0 ≤ L₁ * Lk ∧ 0 ≤ C
      ∧ (∀ y : ℕ, |L₁ - ∑ d ∈ Icc 1 y, charFn q₁ χ₁ d / d| ≤ 2 * (q₁:ℝ) / (y + 1))
      ∧ (∀ y : ℕ, 1 ≤ y →
          |Lk - ∑ d ∈ Icc 1 y, (toArith (charFn q₂ χ₂)
              * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) d / d|
            ≤ 7 * (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) / Real.sqrt y)
      ∧ ∀ x : ℕ, 2 ≤ x → ((820 * (C + 1)) ^ (40:ℕ) : ℝ) ≤ (x:ℝ) →
          1 - β ≤ 26 * (L₁ * Lk) * ((x:ℝ)) ^ (1 - β) := by
  have hq₁ : 1 ≤ q₁ := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₁)
  have hq₂ : 1 ≤ q₂ := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₂)
  obtain ⟨L₁, Lk, C, hr1, hr2, hC0, hEsys⟩ :=
    quad_system_for_chars hq₁ hq₂ χ₁ χ₂ hχ₁2 hχ₂2 hχ₁1 hχ₂1 hχ₃1
  obtain ⟨ha0, ha1⟩ := quad_conv_nonneg (charFn q₁ χ₁) (charFn q₂ χ₂)
    (charFn_mul χ₁ hχ₁2) (charFn_mul χ₂ hχ₂2)
    (charFn_one χ₁) (charFn_one χ₂)
    (charFn_values χ₁ hχ₁2) (charFn_values χ₂ hχ₂2)
  have h1b := fun n => charFn_bound χ₁ hχ₁2 n
  have h2b := fun n => charFn_bound χ₂ hχ₂2 n
  -- the E-function and its properties
  have hA0 : ∀ n : ℕ, 0 ≤ ∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ))
      * toArith (charFn q₁ χ₁) * toArith (charFn q₂ χ₂)
      * toArith (fun k => charFn q₁ χ₁ k * charFn q₂ χ₂ k)) m :=
    fun n => Finset.sum_nonneg (fun m _ => ha0 m)
  have hlam : 0 ≤ L₁ * Lk := by
    apply lam_nonneg (fun n => ∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ))
        * toArith (charFn q₁ χ₁) * toArith (charFn q₂ χ₂)
        * toArith (fun k => charFn q₁ χ₁ k * charFn q₂ χ₂ k)) m)
      (L₁ * Lk) C hC0 hA0
    intro n hn
    exact hEsys n hn
  refine ⟨L₁, Lk, C, hlam, hC0, hr1, hr2, ?_⟩
  intro x hx hxC
  apply siegel_lambda_lower
    (fun n => (toArith (fun _ => (1:ℝ)) * toArith (charFn q₁ χ₁)
      * toArith (charFn q₂ χ₂)
      * toArith (fun k => charFn q₁ χ₁ k * charFn q₂ χ₂ k)) n)
    (L₁ * Lk)
    (fun n => (∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith (charFn q₁ χ₁)
      * toArith (charFn q₂ χ₂)
      * toArith (fun k => charFn q₁ χ₁ k * charFn q₂ χ₂ k)) m) - L₁ * Lk * n)
    C ha0 ha1 hlam
    (fun n => by ring)
    hC0
    (by
      show (∑ m ∈ Icc 1 0, (toArith (fun _ => (1:ℝ)) * toArith (charFn q₁ χ₁)
        * toArith (charFn q₂ χ₂)
        * toArith (fun k => charFn q₁ χ₁ k * charFn q₂ χ₂ k)) m) - L₁ * Lk * (0:ℕ) = 0
      rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, Nat.cast_zero, mul_zero,
        sub_zero])
    (fun n hn => hEsys n hn)
    (fun s hs => quad_LSeriesSummable (charFn q₁ χ₁) (charFn q₂ χ₂) h1b h2b hs)
    (fun w => riemannZeta w * DirichletCharacter.LFunction χ₁ w
      * DirichletCharacter.LFunction χ₂ w
      * DirichletCharacter.LFunction
          ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
            * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) w)
    (fun s _ hs1 => quad_P_differentiableAt χ₁ χ₂ hχ₁1 hχ₂1 hχ₃1 s hs1)
    (fun s hs => quad_P_identity χ₁ χ₂ hχ₁2 hχ₂2 hs)
    hβ1 hβ2
    (by
      show riemannZeta ((β:ℂ)) * DirichletCharacter.LFunction χ₁ ((β:ℂ))
        * DirichletCharacter.LFunction χ₂ ((β:ℂ))
        * DirichletCharacter.LFunction
            ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
              * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) ((β:ℂ)) = 0
      rw [hzero, mul_zero, zero_mul, zero_mul])
    x hx hxC

/-- **The generalized Dirichlet test** (Siegel brick A5-a): `q`-bounded partial sums
    against ANY nonneg antitone weight: `|Σ_{y<d≤z} g(d)w(d)| ≤ 2q·w(y+1)` — the
    uniform-in-`s` engine for the `L(1,χ)` identifications. -/
lemma abel_tail_general (g : ℕ → ℝ) (q : ℝ) (w : ℕ → ℝ)
    (hG : ∀ t : ℕ, |∑ n ∈ Icc 1 t, g n| ≤ q)
    (hw0 : ∀ d, 0 ≤ w d) (hwa : ∀ d, w (d + 1) ≤ w d)
    (y : ℕ) : ∀ z : ℕ, y ≤ z →
    |∑ d ∈ Icc (y + 1) z, g d * w d| ≤ 2 * q * w (y + 1) := by
  have hq : 0 ≤ q := le_trans (abs_nonneg _) (hG 0)
  -- the general Abel window identity
  have hwindow : ∀ z : ℕ, y ≤ z →
      ∑ d ∈ Icc (y + 1) z, g d * w d
      = ∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * (w d - w (d + 1))
        + (∑ n ∈ Icc 1 z, g n) * w (z + 1) - (∑ n ∈ Icc 1 y, g n) * w (y + 1) := by
    intro z
    induction z with
    | zero =>
      intro hy0
      interval_cases y
      simp
    | succ m ih =>
      intro hym
      rcases Nat.lt_or_ge m y with hlt | hge
      · have hy' : y = m + 1 := by omega
        subst hy'
        have hempty : Icc (m + 1 + 1) (m + 1) = (∅ : Finset ℕ) :=
          Finset.Icc_eq_empty (by omega)
        rw [hempty, Finset.sum_empty, Finset.sum_empty]
        ring
      · have hins : Icc (y + 1) (m + 1) = insert (m + 1) (Icc (y + 1) m) := by
          ext d
          simp only [Finset.mem_insert, Finset.mem_Icc]
          omega
        have hnotmem : (m + 1) ∉ Icc (y + 1) m := by
          simp only [Finset.mem_Icc]
          omega
        rw [hins, Finset.sum_insert hnotmem, Finset.sum_insert hnotmem, ih hge]
        have hS : ∑ n ∈ Icc 1 (m + 1), g n = g (m + 1) + ∑ n ∈ Icc 1 m, g n := by
          rw [show Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) from by
            ext d
            simp only [Finset.mem_insert, Finset.mem_Icc]
            omega, Finset.sum_insert (by
              simp only [Finset.mem_Icc]
              omega)]
        rw [hS]
        ring
  -- the weight telescope
  have htel : ∀ z : ℕ, y ≤ z →
      ∑ d ∈ Icc (y + 1) z, (w d - w (d + 1)) = w (y + 1) - w (z + 1) := by
    intro z
    induction z with
    | zero =>
      intro hy0
      interval_cases y
      simp
    | succ m ih =>
      intro hym
      rcases Nat.lt_or_ge m y with hlt | hge
      · have hy' : y = m + 1 := by omega
        subst hy'
        rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
        ring
      · rw [show Icc (y + 1) (m + 1) = insert (m + 1) (Icc (y + 1) m) from by
          ext d
          simp only [Finset.mem_insert, Finset.mem_Icc]
          omega, Finset.sum_insert (by
            simp only [Finset.mem_Icc]
            omega), ih hge]
        ring
  intro z hz
  rw [hwindow z hz]
  have hterm : ∀ d ∈ Icc (y + 1) z,
      |(∑ n ∈ Icc 1 d, g n) * (w d - w (d + 1))| ≤ q * (w d - w (d + 1)) := by
    intro d _
    rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ w d - w (d + 1) from by linarith [hwa d])]
    apply mul_le_mul_of_nonneg_right (hG d)
    linarith [hwa d]
  calc |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * (w d - w (d + 1))
        + (∑ n ∈ Icc 1 z, g n) * w (z + 1) - (∑ n ∈ Icc 1 y, g n) * w (y + 1)|
      ≤ |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * (w d - w (d + 1))|
        + |(∑ n ∈ Icc 1 z, g n) * w (z + 1)| + |(∑ n ∈ Icc 1 y, g n) * w (y + 1)| := by
        have h1 := abs_add_le (∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * (w d - w (d + 1))
          + (∑ n ∈ Icc 1 z, g n) * w (z + 1)) (-((∑ n ∈ Icc 1 y, g n) * w (y + 1)))
        have h2 := abs_add_le (∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * (w d - w (d + 1)))
          ((∑ n ∈ Icc 1 z, g n) * w (z + 1))
        rw [abs_neg, ← sub_eq_add_neg] at h1
        linarith
    _ ≤ q * (w (y + 1) - w (z + 1)) + q * w (z + 1) + q * w (y + 1) := by
        have h1 : |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * (w d - w (d + 1))|
            ≤ q * (w (y + 1) - w (z + 1)) := by
          calc |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * (w d - w (d + 1))|
              ≤ ∑ d ∈ Icc (y + 1) z, |(∑ n ∈ Icc 1 d, g n) * (w d - w (d + 1))| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ d ∈ Icc (y + 1) z, q * (w d - w (d + 1)) :=
                Finset.sum_le_sum hterm
            _ = q * ∑ d ∈ Icc (y + 1) z, (w d - w (d + 1)) := by
                rw [Finset.mul_sum]
            _ = q * (w (y + 1) - w (z + 1)) := by rw [htel z hz]
        have h2 : |(∑ n ∈ Icc 1 z, g n) * w (z + 1)| ≤ q * w (z + 1) := by
          rw [abs_mul, abs_of_nonneg (hw0 _)]
          exact mul_le_mul_of_nonneg_right (hG z) (hw0 _)
        have h3 : |(∑ n ∈ Icc 1 y, g n) * w (y + 1)| ≤ q * w (y + 1) := by
          rw [abs_mul, abs_of_nonneg (hw0 _)]
          exact mul_le_mul_of_nonneg_right (hG y) (hw0 _)
        linarith
    _ ≤ 2 * q * w (y + 1) := by
        have := hw0 (z + 1)
        linarith

/-- Character sums against `d^{−s}` decay at the `s = 1` rate, uniformly in
    `s ≥ 1` (Siegel brick A5-b1). -/
lemma char_rpow_tail_rate {q : ℕ} (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q)
    (hχ2 : χ ^ 2 = 1) (hχ1 : χ ≠ 1) {s : ℝ} (hs : 1 ≤ s) (y : ℕ) :
    ∀ z : ℕ, y ≤ z →
    |∑ d ∈ Icc (y + 1) z, charFn q χ d * ((d:ℝ)) ^ (-s)| ≤ 2 * (q:ℝ) / (y + 1) := by
  intro z hz
  set w : ℕ → ℝ := fun d => if d = 0 then 1 else ((d:ℝ)) ^ (-s) with hw
  have hw0 : ∀ d, 0 ≤ w d := by
    intro d
    rw [hw]
    rcases eq_or_ne d 0 with rfl | hd
    · simp
    · simp only [if_neg hd]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hwa : ∀ d, w (d + 1) ≤ w d := by
    intro d
    rw [hw]
    rcases eq_or_ne d 0 with rfl | hd
    · norm_num [Real.one_rpow]
    · simp only [if_neg hd, if_neg (by omega : d + 1 ≠ 0)]
      have hd0 : (0:ℝ) < (d:ℝ) := by
        have : (0:ℕ) < d := by omega
        exact_mod_cast this
      apply Real.rpow_le_rpow_of_nonpos hd0 (by push_cast; linarith)
      linarith
  have hG := charFn_partial_sum_bound hq χ hχ2 hχ1
  have h := abel_tail_general (charFn q χ) ((q:ℝ)) w hG hw0 hwa y z hz
  have hcongr : ∑ d ∈ Icc (y + 1) z, charFn q χ d * w d
      = ∑ d ∈ Icc (y + 1) z, charFn q χ d * ((d:ℝ)) ^ (-s) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mem_Icc] at hd
    rw [hw]
    simp only [if_neg (by omega : d ≠ 0)]
  rw [hcongr] at h
  have hwy : w (y + 1) ≤ 1 / ((y:ℝ) + 1) := by
    rw [hw]
    simp only [if_neg (by omega : y + 1 ≠ 0)]
    have hy0 : (1:ℝ) ≤ ((y + 1 : ℕ):ℝ) := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) y]
    calc ((y + 1 : ℕ):ℝ) ^ (-s) ≤ ((y + 1 : ℕ):ℝ) ^ (-(1:ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hy0 (by linarith)
      _ = 1 / ((y:ℝ) + 1) := by
          rw [Real.rpow_neg_one, ← one_div]
          push_cast
          ring_nf
  have hq0 : (0:ℝ) ≤ (q:ℝ) := Nat.cast_nonneg q
  calc |∑ d ∈ Icc (y + 1) z, charFn q χ d * ((d:ℝ)) ^ (-s)|
      ≤ 2 * (q:ℝ) * w (y + 1) := h
    _ ≤ 2 * (q:ℝ) * (1 / ((y:ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left hwy (by positivity)
    _ = 2 * (q:ℝ) / ((y:ℝ) + 1) := by ring

/-- **The real representation of `L(s,χ)` with the uniform Abel rate**
    (Siegel brick A5-b2): for real `s > 1` there is a real value `ℓ` with
    `L(s,χ) = ℓ` and `|ℓ − Σ_{d≤y}χ(d)d^{−s}| ≤ 2q/(y+1)` for every `y`. -/
theorem LFunction_real_rate {q : ℕ} [NeZero q] (hq : 1 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1) (hχ1 : χ ≠ 1)
    {s : ℝ} (hs : 1 < s) :
    ∃ ℓ : ℝ, DirichletCharacter.LFunction χ ((s:ℂ)) = ((ℓ : ℝ) : ℂ)
      ∧ ∀ y : ℕ, |ℓ - ∑ d ∈ Icc 1 y, charFn q χ d * ((d:ℝ)) ^ (-s)| ≤ 2 * (q:ℝ) / (y + 1) := by
  -- the real partial sums are Cauchy with the explicit rate
  set S : ℕ → ℝ := fun z => ∑ d ∈ Icc 1 z, charFn q χ d * ((d:ℝ)) ^ (-s) with hS
  have hsplit : ∀ y z : ℕ, y ≤ z → S z - S y
      = ∑ d ∈ Icc (y + 1) z, charFn q χ d * ((d:ℝ)) ^ (-s) := by
    intro y z hyz
    rw [hS]
    simp only
    rw [show Icc 1 z = Icc 1 y ∪ Icc (y + 1) z from by
      ext d
      simp only [Finset.mem_union, Finset.mem_Icc]
      omega, Finset.sum_union (by
        rw [Finset.disjoint_left]
        intro d hd hd2
        rw [Finset.mem_Icc] at hd hd2
        omega)]
    ring
  have hdiff : ∀ y z : ℕ, y ≤ z → |S z - S y| ≤ 2 * (q:ℝ) / (y + 1) := by
    intro y z hyz
    rw [hsplit y z hyz]
    exact char_rpow_tail_rate hq χ hχ2 hχ1 hs.le y z hyz
  have hb0 : Tendsto (fun y : ℕ => 2 * (q:ℝ) / ((y:ℝ) + 1)) atTop (nhds 0) := by
    apply Tendsto.div_atTop tendsto_const_nhds
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hcauchy : CauchySeq S := by
    apply cauchySeq_of_le_tendsto_0 (b := fun y : ℕ => 2 * (q:ℝ) / ((y:ℝ) + 1)) _ hb0
    intro m n N hm hn
    rw [Real.dist_eq]
    rcases Nat.le_total m n with h | h
    · rw [abs_sub_comm]
      calc |S n - S m| ≤ 2 * (q:ℝ) / ((m:ℝ) + 1) := hdiff m n h
        _ ≤ 2 * (q:ℝ) / ((N:ℝ) + 1) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            push_cast
            have : (N:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
            linarith
    · calc |S m - S n| ≤ 2 * (q:ℝ) / ((n:ℝ) + 1) := hdiff n m h
        _ ≤ 2 * (q:ℝ) / ((N:ℝ) + 1) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            push_cast
            have : (N:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
            linarith
  obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨ℓ, ?_, ?_⟩
  · -- LFunction = ofReal ℓ: both are limits of ofReal ∘ S
    have hre : ((s:ℂ)).re = s := Complex.ofReal_re s
    have hs1 : 1 < ((s:ℂ)).re := by rw [hre]; exact hs
    have hLS : DirichletCharacter.LFunction χ ((s:ℂ)) = LSeries (fun n => χ ((n : ZMod q))) ((s:ℂ)) :=
      DirichletCharacter.LFunction_eq_LSeries χ hs1
    -- LSeries summability from |χ| ≤ 1
    have hχb : ∀ n : ℕ, n ≠ 0 → ‖χ ((n : ZMod q))‖ ≤ 1 := by
      intro n _
      rw [← charFn_repr χ hχ2 n, Complex.norm_real, Real.norm_eq_abs]
      exact charFn_bound χ hχ2 n
    have hsummable : LSeriesSummable (fun n => χ ((n : ZMod q))) ((s:ℂ)) :=
      LSeriesSummable_of_bounded_of_one_lt_re (m := 1) hχb hs1
    -- ℂ partial sums equal ofReal ∘ S
    have hterm_eq : ∀ n : ℕ, 1 ≤ n →
        LSeries.term (fun n => χ ((n : ZMod q))) ((s:ℂ)) n
          = ((charFn q χ n * ((n:ℝ)) ^ (-s) : ℝ) : ℂ) := by
      intro n hn
      rw [LSeries.term_of_ne_zero (by omega), div_eq_mul_inv, ← Complex.cpow_neg,
        cpow_real_cast n s, ← charFn_repr χ hχ2 n]
      push_cast
      ring
    have hpartial : Tendsto (fun z : ℕ => ((S z : ℝ) : ℂ)) atTop
        (nhds (LSeries (fun n => χ ((n : ZMod q))) ((s:ℂ)))) := by
      have h1 : Tendsto (fun z : ℕ => ∑ n ∈ range (z + 1),
          LSeries.term (fun n => χ ((n : ZMod q))) ((s:ℂ)) n) atTop
          (nhds (LSeries (fun n => χ ((n : ZMod q))) ((s:ℂ)))) := by
        have := hsummable.hasSum.tendsto_sum_nat
        exact this.comp (tendsto_add_atTop_nat 1)
      apply h1.congr
      intro z
      show ∑ n ∈ range (z + 1), LSeries.term (fun n => χ ((n : ZMod q))) ((s:ℂ)) n
        = ((∑ d ∈ Icc 1 z, charFn q χ d * ((d:ℝ)) ^ (-s) : ℝ) : ℂ)
      rw [show range (z + 1) = insert 0 (Icc 1 z) from by
        ext d
        simp only [Finset.mem_insert, Finset.mem_range, Finset.mem_Icc]
        omega, Finset.sum_insert (by
          simp only [Finset.mem_Icc]
          omega), LSeries.term_zero, zero_add, Complex.ofReal_sum]
      exact Finset.sum_congr rfl (fun n hn => by
        rw [Finset.mem_Icc] at hn
        exact hterm_eq n hn.1)
    have hofReal : Tendsto (fun z : ℕ => ((S z : ℝ) : ℂ)) atTop (nhds ((ℓ : ℂ))) :=
      (Complex.continuous_ofReal.tendsto ℓ).comp hℓ
    rw [hLS]
    exact tendsto_nhds_unique hpartial hofReal
  · -- the rate transfers to the limit
    intro y
    have h1 : ∀ z : ℕ, y ≤ z → |S z - S y| ≤ 2 * (q:ℝ) / (y + 1) := fun z hz => hdiff y z hz
    have h2 : Tendsto (fun z : ℕ => S z - S y) atTop (nhds (ℓ - S y)) :=
      hℓ.sub tendsto_const_nhds
    have h3 : |ℓ - S y| ≤ 2 * (q:ℝ) / (y + 1) := by
      apply le_of_tendsto (h2.abs)
      filter_upwards [eventually_ge_atTop y] with z hz
      exact h1 z hz
    exact h3

/-- **`L₁ = L(1,χ)`** (Siegel brick A5-c): the abstract hyperbola limit with the
    `2q/(y+1)` rate IS the analytic `L`-value at `1` — squeeze along `s → 1⁺`. -/
theorem L1_eq_LFunction_one {q : ℕ} [NeZero q] (hq : 1 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1) (hχ1 : χ ≠ 1)
    (L₁ : ℝ)
    (hr : ∀ y : ℕ, |L₁ - ∑ d ∈ Icc 1 y, charFn q χ d / d| ≤ 2 * (q:ℝ) / (y + 1)) :
    DirichletCharacter.LFunction χ 1 = ((L₁ : ℝ) : ℂ) := by
  -- Step 1: the boundary rate at s = 1
  have hy : ∀ y : ℕ, ‖DirichletCharacter.LFunction χ 1
      - ((∑ d ∈ Icc 1 y, charFn q χ d / d : ℝ) : ℂ)‖ ≤ 2 * (q:ℝ) / (y + 1) := by
    intro y
    -- the finite sum at exponent −s, as a continuous function of s
    have hcont_term : ∀ d : ℕ, d ∈ Icc 1 y →
        Continuous (fun s : ℝ => charFn q χ d * ((d:ℝ)) ^ (-s)) := by
      intro d hd
      rw [Finset.mem_Icc] at hd
      have hd0 : (0:ℝ) < (d:ℝ) := by
        have : (0:ℕ) < d := by omega
        exact_mod_cast this
      have hrw : (fun s : ℝ => ((d:ℝ)) ^ (-s))
          = fun s : ℝ => Real.exp (Real.log d * (-s)) := by
        funext s
        rw [Real.rpow_def_of_pos hd0]
      apply Continuous.mul continuous_const
      rw [hrw]
      exact Real.continuous_exp.comp (continuous_const.mul continuous_neg)
    have hcont_sum : Continuous (fun s : ℝ =>
        ∑ d ∈ Icc 1 y, charFn q χ d * ((d:ℝ)) ^ (-s)) :=
      continuous_finset_sum _ (fun d hd => hcont_term d hd)
    -- the two limits along s → 1⁺
    have hofReal1 : Tendsto (fun s : ℝ => ((s:ℝ):ℂ)) (nhdsWithin 1 (Set.Ioi 1))
        (nhds ((1:ℂ))) := by
      have h := (Complex.continuous_ofReal.tendsto (1:ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (1:ℝ)))
      simpa using h
    have htends1 : Tendsto (fun s : ℝ => DirichletCharacter.LFunction χ ((s:ℂ)))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (DirichletCharacter.LFunction χ 1)) := by
      have hc : ContinuousAt (DirichletCharacter.LFunction χ) 1 :=
        (DirichletCharacter.differentiable_LFunction hχ1).continuous.continuousAt
      exact hc.tendsto.comp hofReal1
    have htends2 : Tendsto (fun s : ℝ =>
        ((∑ d ∈ Icc 1 y, charFn q χ d * ((d:ℝ)) ^ (-s) : ℝ) : ℂ))
        (nhdsWithin 1 (Set.Ioi 1))
        (nhds ((∑ d ∈ Icc 1 y, charFn q χ d * ((d:ℝ)) ^ (-(1:ℝ)) : ℝ) : ℂ)) := by
      have h1 : Tendsto (fun s : ℝ => ∑ d ∈ Icc 1 y, charFn q χ d * ((d:ℝ)) ^ (-s))
          (nhdsWithin 1 (Set.Ioi 1))
          (nhds (∑ d ∈ Icc 1 y, charFn q χ d * ((d:ℝ)) ^ (-(1:ℝ)))) :=
        (hcont_sum.tendsto 1).mono_left nhdsWithin_le_nhds
      exact (Complex.continuous_ofReal.tendsto _).comp h1
    -- the eventual bound
    have hev : ∀ᶠ s : ℝ in nhdsWithin 1 (Set.Ioi 1),
        ‖DirichletCharacter.LFunction χ ((s:ℂ))
          - ((∑ d ∈ Icc 1 y, charFn q χ d * ((d:ℝ)) ^ (-s) : ℝ) : ℂ)‖
        ≤ 2 * (q:ℝ) / (y + 1) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [Set.mem_Ioi] at hs
      obtain ⟨ℓ, hL, hrate⟩ := LFunction_real_rate hq χ hχ2 hχ1 hs
      rw [hL, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact hrate y
    -- pass to the limit
    have hlim : Tendsto (fun s : ℝ => ‖DirichletCharacter.LFunction χ ((s:ℂ))
        - ((∑ d ∈ Icc 1 y, charFn q χ d * ((d:ℝ)) ^ (-s) : ℝ) : ℂ)‖)
        (nhdsWithin 1 (Set.Ioi 1))
        (nhds ‖DirichletCharacter.LFunction χ 1
          - ((∑ d ∈ Icc 1 y, charFn q χ d * ((d:ℝ)) ^ (-(1:ℝ)) : ℝ) : ℂ)‖) :=
      (htends1.sub htends2).norm
    have hle := le_of_tendsto hlim hev
    have hconv : ∑ d ∈ Icc 1 y, charFn q χ d * ((d:ℝ)) ^ (-(1:ℝ))
        = ∑ d ∈ Icc 1 y, charFn q χ d / d := by
      apply Finset.sum_congr rfl
      intro d _
      rw [Real.rpow_neg_one, div_eq_mul_inv]
    rw [hconv] at hle
    exact hle
  -- Step 2: combine with the abstract rate and squeeze to equality
  have hcomb : ∀ y : ℕ, ‖DirichletCharacter.LFunction χ 1 - ((L₁ : ℝ) : ℂ)‖
      ≤ 4 * (q:ℝ) / (y + 1) := by
    intro y
    have h1 := hy y
    have h2 : ‖((∑ d ∈ Icc 1 y, charFn q χ d / d : ℝ) : ℂ) - ((L₁ : ℝ) : ℂ)‖
        ≤ 2 * (q:ℝ) / (y + 1) := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      exact hr y
    calc ‖DirichletCharacter.LFunction χ 1 - ((L₁ : ℝ) : ℂ)‖
        ≤ ‖DirichletCharacter.LFunction χ 1
            - ((∑ d ∈ Icc 1 y, charFn q χ d / d : ℝ) : ℂ)‖
          + ‖((∑ d ∈ Icc 1 y, charFn q χ d / d : ℝ) : ℂ) - ((L₁ : ℝ) : ℂ)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * (q:ℝ) / (y + 1) + 2 * (q:ℝ) / (y + 1) := add_le_add h1 h2
      _ = 4 * (q:ℝ) / (y + 1) := by ring
  by_contra hne
  have hpos : 0 < ‖DirichletCharacter.LFunction χ 1 - ((L₁ : ℝ) : ℂ)‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact hne
  obtain ⟨y, hy'⟩ := exists_nat_gt (4 * (q:ℝ)
    / ‖DirichletCharacter.LFunction χ 1 - ((L₁ : ℝ) : ℂ)‖)
  have h1 := hcomb y
  have hy1 : (0:ℝ) < (y:ℝ) + 1 := by positivity
  rw [div_lt_iff₀ hpos] at hy'
  have h2 : 4 * (q:ℝ) / ((y:ℝ) + 1)
      < ‖DirichletCharacter.LFunction χ 1 - ((L₁ : ℝ) : ℂ)‖ := by
    rw [div_lt_iff₀ hy1]
    calc 4 * (q:ℝ) < (y:ℝ) * ‖DirichletCharacter.LFunction χ 1 - ((L₁ : ℝ) : ℂ)‖ := hy'
      _ ≤ ‖DirichletCharacter.LFunction χ 1 - ((L₁ : ℝ) : ℂ)‖ * ((y:ℝ) + 1) := by
          nlinarith [hpos, Nat.cast_nonneg (α := ℝ) y]
  linarith

/-- **The √-size partial sums against `d^{−s}` decay at the `1/√y` rate, uniformly
    in `s ∈ [1,2]`** (Siegel brick A5-d1) — the convolution-side twin of
    `char_rpow_tail_rate`, powering the `Lk` identification. -/
lemma conv_rpow_tail_rate (k : ℕ → ℝ) (B : ℝ)
    (hK : ∀ t : ℕ, |∑ n ∈ Icc 1 t, k n| ≤ B * (Real.sqrt t + 1))
    {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (y : ℕ) (hy1 : 1 ≤ y) :
    ∀ z : ℕ, y ≤ z →
    |∑ d ∈ Icc (y + 1) z, k d * ((d:ℝ)) ^ (-s)| ≤ 30 * B / Real.sqrt y := by
  have hB0 : 0 ≤ B := by
    have h0 := hK 0
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, abs_zero,
      Nat.cast_zero, Real.sqrt_zero, zero_add, mul_one] at h0
    exact h0
  set w : ℕ → ℝ := fun d => ((d:ℝ)) ^ (-s) with hw
  -- the Abel window identity (generic in w)
  have hwindow : ∀ z : ℕ, y ≤ z →
      ∑ d ∈ Icc (y + 1) z, k d * w d
      = ∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))
        + (∑ n ∈ Icc 1 z, k n) * w (z + 1) - (∑ n ∈ Icc 1 y, k n) * w (y + 1) := by
    intro z
    induction z with
    | zero =>
      intro hy0
      omega
    | succ m ih =>
      intro hym
      rcases Nat.lt_or_ge m y with hlt | hge
      · have hy' : y = m + 1 := by omega
        subst hy'
        have hempty : Icc (m + 1 + 1) (m + 1) = (∅ : Finset ℕ) :=
          Finset.Icc_eq_empty (by omega)
        rw [hempty, Finset.sum_empty, Finset.sum_empty]
        ring
      · have hins : Icc (y + 1) (m + 1) = insert (m + 1) (Icc (y + 1) m) := by
          ext d
          simp only [Finset.mem_insert, Finset.mem_Icc]
          omega
        have hnotmem : (m + 1) ∉ Icc (y + 1) m := by
          simp only [Finset.mem_Icc]
          omega
        rw [hins, Finset.sum_insert hnotmem, Finset.sum_insert hnotmem, ih hge]
        have hS : ∑ n ∈ Icc 1 (m + 1), k n = k (m + 1) + ∑ n ∈ Icc 1 m, k n := by
          rw [show Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) from by
            ext d
            simp only [Finset.mem_insert, Finset.mem_Icc]
            omega, Finset.sum_insert (by
              simp only [Finset.mem_Icc]
              omega)]
        rw [hS]
        ring
  -- per-term kernel bound: |S d|(w d − w(d+1)) ≤ 4B/(d√d) for d ≥ 1
  have hkernel : ∀ d : ℕ, 1 ≤ d →
      |(∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))| ≤ 4 * B * (1 / ((d:ℝ) * Real.sqrt d)) := by
    intro d hd
    have hd0 : (0:ℝ) < (d:ℝ) := by
      have : (0:ℕ) < d := hd
      exact_mod_cast this
    have hd1r : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    have hsq1 : (1:ℝ) ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1r
    have hΔ0 : 0 ≤ w d - w (d + 1) := by
      rw [hw]
      simp only
      have : (((d + 1 : ℕ)):ℝ) ^ (-s) ≤ ((d:ℝ)) ^ (-s) := by
        apply Real.rpow_le_rpow_of_nonpos hd0 (by push_cast; linarith)
        linarith
      push_cast at this ⊢
      linarith
    have hΔle : w d - w (d + 1) ≤ 2 * ((d:ℝ)) ^ (-(2:ℝ)) := by
      rw [hw]
      simp only
      have h1 := rpow_diff_le d hd s (by linarith)
      have h2 : ((d:ℝ)) ^ (-s - 1) ≤ ((d:ℝ)) ^ (-(2:ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le hd1r
        linarith
      have h3 : s * ((d:ℝ)) ^ (-s - 1) ≤ 2 * ((d:ℝ)) ^ (-(2:ℝ)) := by
        calc s * ((d:ℝ)) ^ (-s - 1) ≤ 2 * ((d:ℝ)) ^ (-s - 1) := by
              apply mul_le_mul_of_nonneg_right hs2 (Real.rpow_nonneg hd0.le _)
          _ ≤ 2 * ((d:ℝ)) ^ (-(2:ℝ)) := by
              apply mul_le_mul_of_nonneg_left h2 (by norm_num)

      push_cast at h1 ⊢
      linarith
    have hSb : |∑ n ∈ Icc 1 d, k n| ≤ 2 * B * Real.sqrt d := by
      calc |∑ n ∈ Icc 1 d, k n| ≤ B * (Real.sqrt d + 1) := hK d
        _ ≤ B * (Real.sqrt d + Real.sqrt d) := by
            apply mul_le_mul_of_nonneg_left _ hB0
            linarith
        _ = 2 * B * Real.sqrt d := by ring
    have hrpow2 : ((d:ℝ)) ^ (-(2:ℝ)) = 1 / ((d:ℝ) * (d:ℝ)) := by
      rw [show (-(2:ℝ)) = -(((2:ℕ)):ℝ) from by norm_num, Real.rpow_neg hd0.le,
        Real.rpow_natCast, pow_two, one_div]
    have hcollect : Real.sqrt d * (1 / ((d:ℝ) * (d:ℝ))) = 1 / ((d:ℝ) * Real.sqrt d) := by
      rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity), one_mul]
      calc Real.sqrt d * ((d:ℝ) * Real.sqrt d)
          = (Real.sqrt d * Real.sqrt d) * (d:ℝ) := by ring
        _ = (d:ℝ) * (d:ℝ) := by rw [Real.mul_self_sqrt hd0.le]
    rw [abs_mul, abs_of_nonneg hΔ0]
    calc |∑ n ∈ Icc 1 d, k n| * (w d - w (d + 1))
        ≤ (2 * B * Real.sqrt d) * (2 * ((d:ℝ)) ^ (-(2:ℝ))) := by
          apply mul_le_mul hSb hΔle hΔ0
          positivity
      _ = 4 * B * (Real.sqrt d * ((d:ℝ)) ^ (-(2:ℝ))) := by ring
      _ = 4 * B * (Real.sqrt d * (1 / ((d:ℝ) * (d:ℝ)))) := by rw [hrpow2]
      _ = 4 * B * (1 / ((d:ℝ) * Real.sqrt d)) := by rw [hcollect]
  intro z hz
  rw [hwindow z hz]
  have hy0 : (0:ℝ) < (y:ℝ) := by
    have : (0:ℕ) < y := hy1
    exact_mod_cast this
  have hz0 : (0:ℝ) < (z:ℝ) := by
    have : (0:ℕ) < z := by omega
    exact_mod_cast this
  have hsqy : (1:ℝ) ≤ Real.sqrt y := Real.one_le_sqrt.mpr (by exact_mod_cast hy1)
  have hsqy0 : (0:ℝ) < Real.sqrt y := by linarith
  have hsqz0 : (0:ℝ) < Real.sqrt z := Real.sqrt_pos.mpr hz0
  -- the three pieces
  have h1 : |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))|
      ≤ 8 * B / Real.sqrt y := by
    calc |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))|
        ≤ ∑ d ∈ Icc (y + 1) z, |(∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Icc (y + 1) z, 4 * B * (1 / ((d:ℝ) * Real.sqrt d)) := by
          apply Finset.sum_le_sum
          intro d hd
          rw [Finset.mem_Icc] at hd
          exact hkernel d (by omega)
      _ = 4 * B * ∑ d ∈ Icc (y + 1) z, (1 : ℝ) / (d * Real.sqrt d) := by
          rw [Finset.mul_sum]
      _ ≤ 4 * B * (2 / Real.sqrt y - 2 / Real.sqrt z) := by
          apply mul_le_mul_of_nonneg_left (sum_three_half_tail_sharp y hy1 z hz)
            (by positivity)
      _ ≤ 8 * B / Real.sqrt y := by
          have h3 : (0:ℝ) ≤ 4 * B * (2 / Real.sqrt z) := by positivity
          have heq : 4 * B * (2 / Real.sqrt y - 2 / Real.sqrt z)
              = 8 * B / Real.sqrt y - 4 * B * (2 / Real.sqrt z) := by ring
          linarith [heq.le, heq.ge]
  have hwle : ∀ t : ℕ, 1 ≤ t → w (t + 1) ≤ 1 / (t:ℝ) := by
    intro t ht
    have ht0 : (0:ℝ) < (t:ℝ) := by
      have : (0:ℕ) < t := ht
      exact_mod_cast this
    have ht1 : (1:ℝ) ≤ ((t + 1 : ℕ):ℝ) := by push_cast; linarith
    rw [hw]
    simp only
    calc ((t + 1 : ℕ):ℝ) ^ (-s) ≤ ((t + 1 : ℕ):ℝ) ^ (-(1:ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
      _ = 1 / ((t + 1 : ℕ):ℝ) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ 1 / (t:ℝ) := by
          apply one_div_le_one_div_of_le ht0
          push_cast
          linarith
  have hbz : |(∑ n ∈ Icc 1 z, k n) * w (z + 1)| ≤ 2 * B / Real.sqrt y := by
    have hw0z : 0 ≤ w (z + 1) := by
      rw [hw]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hsqzz : Real.sqrt z / (z:ℝ) = 1 / Real.sqrt z := by
      rw [eq_div_iff (ne_of_gt hsqz0)]
      field_simp
      exact Real.sq_sqrt hz0.le
    calc |(∑ n ∈ Icc 1 z, k n) * w (z + 1)|
        = |∑ n ∈ Icc 1 z, k n| * w (z + 1) := by rw [abs_mul, abs_of_nonneg hw0z]
      _ ≤ (2 * B * Real.sqrt z) * (1 / (z:ℝ)) := by
          apply mul_le_mul _ (hwle z (by omega)) hw0z (by positivity)
          calc |∑ n ∈ Icc 1 z, k n| ≤ B * (Real.sqrt z + 1) := hK z
            _ ≤ B * (Real.sqrt z + Real.sqrt z) := by
                apply mul_le_mul_of_nonneg_left _ hB0
                have : (1:ℝ) ≤ Real.sqrt z := Real.one_le_sqrt.mpr (by
                  have : (1:ℕ) ≤ z := by omega
                  exact_mod_cast this)
                linarith
            _ = 2 * B * Real.sqrt z := by ring
      _ = 2 * B * (Real.sqrt z / (z:ℝ)) := by ring
      _ = 2 * B * (1 / Real.sqrt z) := by rw [hsqzz]
      _ ≤ 2 * B / Real.sqrt y := by
          rw [mul_one_div]
          apply div_le_div_of_nonneg_left (by linarith) hsqy0
          exact Real.sqrt_le_sqrt (by exact_mod_cast hz)
  have hby : |(∑ n ∈ Icc 1 y, k n) * w (y + 1)| ≤ 2 * B / Real.sqrt y := by
    have hw0y : 0 ≤ w (y + 1) := by
      rw [hw]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hsqyy : Real.sqrt y / (y:ℝ) = 1 / Real.sqrt y := by
      rw [eq_div_iff (ne_of_gt hsqy0)]
      field_simp
      exact Real.sq_sqrt hy0.le
    calc |(∑ n ∈ Icc 1 y, k n) * w (y + 1)|
        = |∑ n ∈ Icc 1 y, k n| * w (y + 1) := by rw [abs_mul, abs_of_nonneg hw0y]
      _ ≤ (2 * B * Real.sqrt y) * (1 / (y:ℝ)) := by
          apply mul_le_mul _ (hwle y hy1) hw0y (by positivity)
          calc |∑ n ∈ Icc 1 y, k n| ≤ B * (Real.sqrt y + 1) := hK y
            _ ≤ B * (Real.sqrt y + Real.sqrt y) := by
                apply mul_le_mul_of_nonneg_left _ hB0
                linarith
            _ = 2 * B * Real.sqrt y := by ring
      _ = 2 * B * (Real.sqrt y / (y:ℝ)) := by ring
      _ = 2 * B * (1 / Real.sqrt y) := by rw [hsqyy]
      _ = 2 * B / Real.sqrt y := by rw [mul_one_div]
  calc |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))
        + (∑ n ∈ Icc 1 z, k n) * w (z + 1) - (∑ n ∈ Icc 1 y, k n) * w (y + 1)|
      ≤ |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))|
        + |(∑ n ∈ Icc 1 z, k n) * w (z + 1)| + |(∑ n ∈ Icc 1 y, k n) * w (y + 1)| := by
        have ha := abs_add_le (∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))
          + (∑ n ∈ Icc 1 z, k n) * w (z + 1)) (-((∑ n ∈ Icc 1 y, k n) * w (y + 1)))
        have hb := abs_add_le (∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1)))
          ((∑ n ∈ Icc 1 z, k n) * w (z + 1))
        rw [abs_neg, ← sub_eq_add_neg] at ha
        linarith
    _ ≤ 8 * B / Real.sqrt y + 2 * B / Real.sqrt y + 2 * B / Real.sqrt y := by
        linarith [h1, hbz, hby]
    _ ≤ 30 * B / Real.sqrt y := by
        have h30 : (12:ℝ) * B / Real.sqrt y ≤ 30 * B / Real.sqrt y := by
          apply div_le_div_of_nonneg_right _ hsqy0.le
          linarith
        have heq : 8 * B / Real.sqrt y + 2 * B / Real.sqrt y + 2 * B / Real.sqrt y
            = 12 * B / Real.sqrt y := by ring
        linarith [heq.le, heq.ge, h30]

/-- **The pair `L(s,χ₂)L(s,χ₁χ₂)` is real with the `30B/√y` Abel rate**
    (Siegel brick A5-d2): the convolution partial sums identify the product of
    the two L-values at every real `s ∈ (1,2]`. -/
theorem LFunction_pair_real_rate {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (hq₁ : 1 ≤ q₁) (hq₂ : 1 ≤ q₂)
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁2 : χ₁ ^ 2 = 1) (hχ₂2 : χ₂ ^ 2 = 1) (hχ₁1 : χ₁ ≠ 1) (hχ₂1 : χ₂ ≠ 1)
    (hχ₃1 : (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
        * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) ≠ 1)
    {s : ℝ} (hs : 1 < s) (hs2 : s ≤ 2) :
    ∃ ℓ : ℝ, DirichletCharacter.LFunction χ₂ ((s:ℂ))
        * DirichletCharacter.LFunction
            ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
              * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) ((s:ℂ)) = ((ℓ:ℝ):ℂ)
      ∧ ∀ y : ℕ, 1 ≤ y →
        |ℓ - ∑ d ∈ Icc 1 y, (toArith (charFn q₂ χ₂)
            * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) d * ((d:ℝ)) ^ (-s)|
          ≤ 30 * (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) / Real.sqrt y := by
  have h2b := fun n => charFn_bound χ₂ hχ₂2 n
  have h12b : ∀ n, |charFn q₁ χ₁ n * charFn q₂ χ₂ n| ≤ 1 := by
    intro n
    rw [abs_mul]
    calc |charFn q₁ χ₁ n| * |charFn q₂ χ₂ n| ≤ 1 * 1 :=
        mul_le_mul (charFn_bound χ₁ hχ₁2 n) (h2b n) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hχ₃2 : ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
      * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) ^ 2 = 1 := by
    rw [mul_pow, ← map_pow, ← map_pow, hχ₁2, hχ₂2, map_one, map_one, mul_one]
  have hq₁₂ : 1 ≤ q₁ * q₂ :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hG₂ := charFn_partial_sum_bound hq₂ χ₂ hχ₂2 hχ₂1
  have hG₃ := charFn_partial_sum_bound hq₁₂ _ hχ₃2 hχ₃1
  have hK2 : ∀ t : ℕ, |∑ n ∈ Icc 1 t, (charFn q₁ χ₁ n * charFn q₂ χ₂ n)|
      ≤ (q₁:ℝ) * (q₂:ℝ) := by
    intro t
    have heq : ∑ n ∈ Icc 1 t, (charFn q₁ χ₁ n * charFn q₂ χ₂ n)
        = ∑ n ∈ Icc 1 t, charFn (q₁ * q₂)
            ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
              * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) n :=
      Finset.sum_congr rfl (fun n _ => (charFn_mul_char χ₁ χ₂ hχ₁2 hχ₂2 n).symm)
    rw [heq]
    have h := hG₃ t
    push_cast at h
    exact h
  have hKb : ∀ t : ℕ, |∑ n ∈ Icc 1 t, (toArith (charFn q₂ χ₂)
      * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) n|
      ≤ (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) * (Real.sqrt t + 1) :=
    fun t => bounded_conv_sqrt_bound (charFn q₂ χ₂)
      (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m) ((q₂:ℝ)) ((q₁:ℝ) * (q₂:ℝ))
      h2b h12b hG₂ hK2 t
  set B : ℝ := 2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ) with hB
  set k : ℕ → ℝ := fun d => (toArith (charFn q₂ χ₂)
      * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) d with hk
  set S : ℕ → ℝ := fun z => ∑ d ∈ Icc 1 z, k d * ((d:ℝ)) ^ (-s) with hS
  have hsplit : ∀ y z : ℕ, y ≤ z → S z - S y
      = ∑ d ∈ Icc (y + 1) z, k d * ((d:ℝ)) ^ (-s) := by
    intro y z hyz
    rw [hS]
    simp only
    rw [show Icc 1 z = Icc 1 y ∪ Icc (y + 1) z from by
      ext d
      simp only [Finset.mem_union, Finset.mem_Icc]
      omega, Finset.sum_union (by
        rw [Finset.disjoint_left]
        intro d hd hd2
        rw [Finset.mem_Icc] at hd hd2
        omega)]
    ring
  have hdiff : ∀ y z : ℕ, 1 ≤ y → y ≤ z → |S z - S y| ≤ 30 * B / Real.sqrt y := by
    intro y z hy1 hyz
    rw [hsplit y z hyz]
    exact conv_rpow_tail_rate k B hKb hs.le hs2 y hy1 z hyz
  -- Cauchy via the shifted sequence
  have hb0 : Tendsto (fun N : ℕ => 30 * B / Real.sqrt ((N:ℝ) + 1)) atTop (nhds 0) := by
    apply Tendsto.div_atTop tendsto_const_nhds
    apply Filter.Tendsto.comp Real.tendsto_sqrt_atTop
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hcauchyT : CauchySeq (fun z : ℕ => S (z + 1)) := by
    apply cauchySeq_of_le_tendsto_0 (b := fun N : ℕ => 30 * B / Real.sqrt ((N:ℝ) + 1)) _ hb0
    intro m n N hm hn
    rw [Real.dist_eq]
    have hmono : ∀ u v : ℕ, N ≤ u → u ≤ v →
        |S (v + 1) - S (u + 1)| ≤ 30 * B / Real.sqrt ((N:ℝ) + 1) := by
      intro u v hu huv
      calc |S (v + 1) - S (u + 1)| ≤ 30 * B / Real.sqrt (((u + 1 : ℕ)):ℝ) :=
            hdiff (u + 1) (v + 1) (by omega) (by omega)
        _ ≤ 30 * B / Real.sqrt ((N:ℝ) + 1) := by
            have hB0 : (0:ℝ) ≤ B := by
              have h0 := hKb 0
              rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, abs_zero,
                Nat.cast_zero, Real.sqrt_zero, zero_add, mul_one] at h0
              exact h0
            apply div_le_div_of_nonneg_left (by linarith)
              (Real.sqrt_pos.mpr (by positivity))
            apply Real.sqrt_le_sqrt
            push_cast
            have : (N:ℝ) ≤ (u:ℝ) := by exact_mod_cast hu
            linarith
    rcases Nat.le_total m n with h | h
    · rw [abs_sub_comm]
      exact hmono m n hm h
    · exact hmono n m hn h
  obtain ⟨ℓ, hℓT⟩ := cauchySeq_tendsto_of_complete hcauchyT
  have hℓ : Tendsto S atTop (nhds ℓ) := by
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    exact hℓT
  refine ⟨ℓ, ?_, ?_⟩
  · -- the ℂ identification
    have hsc : (1:ℝ) < ((s:ℂ)).re := by
      rw [Complex.ofReal_re]
      exact hs
    have hsum2 := castFn_summable (charFn q₂ χ₂) h2b hsc
    have hsum12 := castFn_summable (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m) h12b hsc
    have hbridge : (fun n => ((k n : ℝ) : ℂ))
        = (LSeries.convolution (castFn (charFn q₂ χ₂))
            (castFn (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m))) := by
      funext n
      exact castFn_conv _ _ n
    have hsummable : LSeriesSummable (fun n => ((k n : ℝ) : ℂ)) ((s:ℂ)) := by
      rw [hbridge]
      exact hsum2.convolution hsum12
    have hprod : LSeries (fun n => ((k n : ℝ) : ℂ)) ((s:ℂ))
        = LSeries (castFn (charFn q₂ χ₂)) ((s:ℂ))
          * LSeries (castFn (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) ((s:ℂ)) := by
      rw [hbridge]
      exact LSeries_convolution' hsum2 hsum12
    have hL2 : LSeries (castFn (charFn q₂ χ₂)) ((s:ℂ))
        = DirichletCharacter.LFunction χ₂ ((s:ℂ)) := by
      rw [DirichletCharacter.LFunction_eq_LSeries χ₂ hsc]
      exact LSeries_congr (fun {n} hn => castFn_charFn χ₂ hχ₂2 hn) _
    have hL3 : LSeries (castFn (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) ((s:ℂ))
        = DirichletCharacter.LFunction
            ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
              * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) ((s:ℂ)) := by
      rw [DirichletCharacter.LFunction_eq_LSeries _ hsc]
      apply LSeries_congr
      intro n hn
      show ((toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m) n : ℝ) : ℂ) = _
      rw [toArith_apply _ n hn, ← charFn_mul_char χ₁ χ₂ hχ₁2 hχ₂2 n,
        charFn_repr _ hχ₃2 n]
    have hterm_eq : ∀ n : ℕ, 1 ≤ n →
        LSeries.term (fun n => ((k n : ℝ) : ℂ)) ((s:ℂ)) n
          = ((k n * ((n:ℝ)) ^ (-s) : ℝ) : ℂ) := by
      intro n hn
      rw [LSeries.term_of_ne_zero (by omega), div_eq_mul_inv, ← Complex.cpow_neg,
        cpow_real_cast n s]
      push_cast
      ring
    have hpartial : Tendsto (fun z : ℕ => ((S z : ℝ) : ℂ)) atTop
        (nhds (LSeries (fun n => ((k n : ℝ) : ℂ)) ((s:ℂ)))) := by
      have h1 : Tendsto (fun z : ℕ => ∑ n ∈ range (z + 1),
          LSeries.term (fun n => ((k n : ℝ) : ℂ)) ((s:ℂ)) n) atTop
          (nhds (LSeries (fun n => ((k n : ℝ) : ℂ)) ((s:ℂ)))) := by
        have := hsummable.hasSum.tendsto_sum_nat
        exact this.comp (tendsto_add_atTop_nat 1)
      apply h1.congr
      intro z
      show ∑ n ∈ range (z + 1), LSeries.term (fun n => ((k n : ℝ) : ℂ)) ((s:ℂ)) n
        = ((∑ d ∈ Icc 1 z, k d * ((d:ℝ)) ^ (-s) : ℝ) : ℂ)
      rw [show range (z + 1) = insert 0 (Icc 1 z) from by
        ext d
        simp only [Finset.mem_insert, Finset.mem_range, Finset.mem_Icc]
        omega, Finset.sum_insert (by
          simp only [Finset.mem_Icc]
          omega), LSeries.term_zero, zero_add, Complex.ofReal_sum]
      exact Finset.sum_congr rfl (fun n hn => by
        rw [Finset.mem_Icc] at hn
        exact hterm_eq n hn.1)
    have hofReal : Tendsto (fun z : ℕ => ((S z : ℝ) : ℂ)) atTop (nhds ((ℓ : ℂ))) :=
      (Complex.continuous_ofReal.tendsto ℓ).comp hℓ
    have hval : LSeries (fun n => ((k n : ℝ) : ℂ)) ((s:ℂ)) = ((ℓ : ℝ) : ℂ) :=
      tendsto_nhds_unique hpartial hofReal
    rw [← hL2, ← hL3, ← hprod, hval]
  · -- the rate at the limit
    intro y hy1
    have h2 : Tendsto (fun z : ℕ => S z - S y) atTop (nhds (ℓ - S y)) :=
      hℓ.sub tendsto_const_nhds
    have h3 : |ℓ - S y| ≤ 30 * B / Real.sqrt y := by
      apply le_of_tendsto h2.abs
      filter_upwards [eventually_ge_atTop y] with z hz
      exact hdiff y z hy1 hz
    exact h3

/-- **`Lk = L(1,χ₂)·L(1,χ₁χ₂)`** (Siegel brick A5-d3): the abstract convolution
    limit with the `7B/√y` rate IS the product of the analytic `L`-values at `1`. -/
theorem Lk_eq_LFunction_pair_one {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (hq₁ : 1 ≤ q₁) (hq₂ : 1 ≤ q₂)
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁2 : χ₁ ^ 2 = 1) (hχ₂2 : χ₂ ^ 2 = 1) (hχ₁1 : χ₁ ≠ 1) (hχ₂1 : χ₂ ≠ 1)
    (hχ₃1 : (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
        * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) ≠ 1)
    (Lk : ℝ)
    (hr : ∀ y : ℕ, 1 ≤ y →
      |Lk - ∑ d ∈ Icc 1 y, (toArith (charFn q₂ χ₂)
          * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) d / d|
        ≤ 7 * (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) / Real.sqrt y) :
    DirichletCharacter.LFunction χ₂ 1
      * DirichletCharacter.LFunction
          ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
            * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) 1
      = ((Lk : ℝ) : ℂ) := by
  set B : ℝ := 2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ) with hB
  have hB0 : (0:ℝ) ≤ B := by
    rw [hB]
    positivity
  set k : ℕ → ℝ := fun d => (toArith (charFn q₂ χ₂)
      * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) d with hk
  set P1 : ℂ := DirichletCharacter.LFunction χ₂ 1
      * DirichletCharacter.LFunction
          ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
            * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) 1 with hP1
  -- Step 1: the boundary rate at s = 1
  have hy : ∀ y : ℕ, 1 ≤ y →
      ‖P1 - ((∑ d ∈ Icc 1 y, k d / d : ℝ) : ℂ)‖ ≤ 30 * B / Real.sqrt y := by
    intro y hy1
    have hcont_term : ∀ d : ℕ, d ∈ Icc 1 y →
        Continuous (fun s : ℝ => k d * ((d:ℝ)) ^ (-s)) := by
      intro d hd
      rw [Finset.mem_Icc] at hd
      have hd0 : (0:ℝ) < (d:ℝ) := by
        have : (0:ℕ) < d := by omega
        exact_mod_cast this
      have hrw : (fun s : ℝ => ((d:ℝ)) ^ (-s))
          = fun s : ℝ => Real.exp (Real.log d * (-s)) := by
        funext s
        rw [Real.rpow_def_of_pos hd0]
      apply Continuous.mul continuous_const
      rw [hrw]
      exact Real.continuous_exp.comp (continuous_const.mul continuous_neg)
    have hcont_sum : Continuous (fun s : ℝ => ∑ d ∈ Icc 1 y, k d * ((d:ℝ)) ^ (-s)) :=
      continuous_finset_sum _ (fun d hd => hcont_term d hd)
    have hofReal1 : Tendsto (fun s : ℝ => ((s:ℝ):ℂ)) (nhdsWithin 1 (Set.Ioi 1))
        (nhds ((1:ℂ))) := by
      have h := (Complex.continuous_ofReal.tendsto (1:ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (1:ℝ)))
      simpa using h
    have htends1 : Tendsto (fun s : ℝ => DirichletCharacter.LFunction χ₂ ((s:ℂ))
        * DirichletCharacter.LFunction
            ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
              * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) ((s:ℂ)))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds P1) := by
      have hc2 : ContinuousAt (DirichletCharacter.LFunction χ₂) 1 :=
        (DirichletCharacter.differentiable_LFunction hχ₂1).continuous.continuousAt
      have hc3 : ContinuousAt (DirichletCharacter.LFunction
          ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
            * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂))) 1 :=
        (DirichletCharacter.differentiable_LFunction hχ₃1).continuous.continuousAt
      exact (hc2.tendsto.comp hofReal1).mul (hc3.tendsto.comp hofReal1)
    have htends2 : Tendsto (fun s : ℝ =>
        ((∑ d ∈ Icc 1 y, k d * ((d:ℝ)) ^ (-s) : ℝ) : ℂ))
        (nhdsWithin 1 (Set.Ioi 1))
        (nhds ((∑ d ∈ Icc 1 y, k d * ((d:ℝ)) ^ (-(1:ℝ)) : ℝ) : ℂ)) := by
      have h1 : Tendsto (fun s : ℝ => ∑ d ∈ Icc 1 y, k d * ((d:ℝ)) ^ (-s))
          (nhdsWithin 1 (Set.Ioi 1))
          (nhds (∑ d ∈ Icc 1 y, k d * ((d:ℝ)) ^ (-(1:ℝ)))) :=
        (hcont_sum.tendsto 1).mono_left nhdsWithin_le_nhds
      exact (Complex.continuous_ofReal.tendsto _).comp h1
    have hev : ∀ᶠ s : ℝ in nhdsWithin 1 (Set.Ioi 1),
        ‖DirichletCharacter.LFunction χ₂ ((s:ℂ))
            * DirichletCharacter.LFunction
                ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
                  * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) ((s:ℂ))
          - ((∑ d ∈ Icc 1 y, k d * ((d:ℝ)) ^ (-s) : ℝ) : ℂ)‖
        ≤ 30 * B / Real.sqrt y := by
      filter_upwards [self_mem_nhdsWithin,
        Ioo_mem_nhdsGT (show (1:ℝ) < 2 from by norm_num)] with s hs1 hs2
      rw [Set.mem_Ioi] at hs1
      rw [Set.mem_Ioo] at hs2
      obtain ⟨ℓ, hL, hrate⟩ := LFunction_pair_real_rate hq₁ hq₂ χ₁ χ₂ hχ₁2 hχ₂2
        hχ₁1 hχ₂1 hχ₃1 hs1 hs2.2.le
      rw [hL, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact hrate y hy1
    have hlim : Tendsto (fun s : ℝ => ‖DirichletCharacter.LFunction χ₂ ((s:ℂ))
        * DirichletCharacter.LFunction
            ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
              * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) ((s:ℂ))
        - ((∑ d ∈ Icc 1 y, k d * ((d:ℝ)) ^ (-s) : ℝ) : ℂ)‖)
        (nhdsWithin 1 (Set.Ioi 1))
        (nhds ‖P1 - ((∑ d ∈ Icc 1 y, k d * ((d:ℝ)) ^ (-(1:ℝ)) : ℝ) : ℂ)‖) :=
      (htends1.sub htends2).norm
    have hle := le_of_tendsto hlim hev
    have hconv : ∑ d ∈ Icc 1 y, k d * ((d:ℝ)) ^ (-(1:ℝ))
        = ∑ d ∈ Icc 1 y, k d / d := by
      apply Finset.sum_congr rfl
      intro d _
      rw [Real.rpow_neg_one, div_eq_mul_inv]
    rw [hconv] at hle
    exact hle
  -- Step 2: combine and pinch
  have hcomb : ∀ y : ℕ, 1 ≤ y → ‖P1 - ((Lk : ℝ) : ℂ)‖ ≤ 37 * B / Real.sqrt y := by
    intro y hy1
    have h1 := hy y hy1
    have h2 : ‖((∑ d ∈ Icc 1 y, k d / d : ℝ) : ℂ) - ((Lk : ℝ) : ℂ)‖
        ≤ 7 * B / Real.sqrt y := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      exact hr y hy1
    calc ‖P1 - ((Lk : ℝ) : ℂ)‖
        ≤ ‖P1 - ((∑ d ∈ Icc 1 y, k d / d : ℝ) : ℂ)‖
          + ‖((∑ d ∈ Icc 1 y, k d / d : ℝ) : ℂ) - ((Lk : ℝ) : ℂ)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 30 * B / Real.sqrt y + 7 * B / Real.sqrt y := add_le_add h1 h2
      _ = 37 * B / Real.sqrt y := by ring
  by_contra hne
  have hpos : 0 < ‖P1 - ((Lk : ℝ) : ℂ)‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact hne
  obtain ⟨y₀, hy₀⟩ := exists_nat_gt ((37 * B / ‖P1 - ((Lk : ℝ) : ℂ)‖) ^ (2:ℕ))
  set y : ℕ := max y₀ 1 with hydef
  have hy1 : 1 ≤ y := le_max_right _ _
  have hybig : ((37 * B / ‖P1 - ((Lk : ℝ) : ℂ)‖) ^ (2:ℕ) : ℝ) < (y:ℝ) := by
    calc ((37 * B / ‖P1 - ((Lk : ℝ) : ℂ)‖) ^ (2:ℕ) : ℝ) < (y₀:ℝ) := hy₀
      _ ≤ (y:ℝ) := by
          have : y₀ ≤ y := le_max_left _ _
          exact_mod_cast this
  have hsq : 37 * B / ‖P1 - ((Lk : ℝ) : ℂ)‖ < Real.sqrt y := by
    have h0 : (0:ℝ) ≤ 37 * B / ‖P1 - ((Lk : ℝ) : ℂ)‖ := by positivity
    rw [show (37 * B / ‖P1 - ((Lk : ℝ) : ℂ)‖ : ℝ)
        = Real.sqrt ((37 * B / ‖P1 - ((Lk : ℝ) : ℂ)‖) ^ (2:ℕ)) from
      (Real.sqrt_sq h0).symm]
    exact Real.sqrt_lt_sqrt (by positivity) hybig
  have hsqy0 : (0:ℝ) < Real.sqrt y :=
    Real.sqrt_pos.mpr (by
      have : (0:ℕ) < y := hy1
      exact_mod_cast this)
  have hfinal : 37 * B / Real.sqrt y < ‖P1 - ((Lk : ℝ) : ℂ)‖ := by
    rw [div_lt_iff₀ hsqy0]
    rw [div_lt_iff₀ hpos] at hsq
    linarith [hsq]
  have := hcomb y hy1
  linarith [this, hfinal]

/-- **The `L₁` upper bound** (Siegel brick S1a): any limit with the `2q/(y+1)` rate
    of `1`-bounded coefficient means satisfies `|L₁| ≤ 3 + log q` for `q ≥ 1`. -/
lemma rate_limit_upper_log (g : ℕ → ℝ) (q : ℕ) (hq : 1 ≤ q) (L : ℝ)
    (hgb : ∀ n, |g n| ≤ 1)
    (hr : ∀ y : ℕ, |L - ∑ d ∈ Icc 1 y, g d / d| ≤ 2 * (q:ℝ) / (y + 1)) :
    |L| ≤ 3 + Real.log q := by
  have hq0 : (0:ℝ) < (q:ℝ) := by
    have : (0:ℕ) < q := hq
    exact_mod_cast this
  have h1 := hr q
  have h2 : |∑ d ∈ Icc 1 q, g d / d| ≤ 1 + Real.log q := by
    calc |∑ d ∈ Icc 1 q, g d / d| ≤ ∑ d ∈ Icc 1 q, |g d / d| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Icc 1 q, (1:ℝ) / d := by
          apply Finset.sum_le_sum
          intro d hd
          rw [Finset.mem_Icc] at hd
          have hd0 : (0:ℝ) < (d:ℝ) := by
            have : (0:ℕ) < d := by omega
            exact_mod_cast this
          rw [abs_div, Nat.abs_cast]
          apply div_le_div_of_nonneg_right (hgb d) hd0.le
      _ ≤ 1 + Real.log q := sum_one_div_le_log q hq
  have h3 : 2 * (q:ℝ) / ((q:ℝ) + 1) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  calc |L| ≤ |L - ∑ d ∈ Icc 1 q, g d / d| + |∑ d ∈ Icc 1 q, g d / d| := by
        have := abs_add_le (L - ∑ d ∈ Icc 1 q, g d / d) (∑ d ∈ Icc 1 q, g d / d)
        simpa using this
    _ ≤ 2 * (q:ℝ) / ((q:ℝ) + 1) + (1 + Real.log q) := by
        push_cast at h1
        linarith [h1, h2]
    _ ≤ 3 + Real.log q := by linarith [h3]

/-- **The `Lk` upper bound** (Siegel brick S1b): any limit with the `7B/√y` rate of
    a convolution of `1`-bounded functions satisfies `|Lk| ≤ 7B + 1`. -/
lemma sqrt_rate_limit_upper (u v : ℕ → ℝ) (B : ℝ) (Lk : ℝ)
    (hub : ∀ n, |u n| ≤ 1) (hvb : ∀ n, |v n| ≤ 1)
    (hr : ∀ y : ℕ, 1 ≤ y →
      |Lk - ∑ d ∈ Icc 1 y, (toArith u * toArith v) d / d| ≤ 7 * B / Real.sqrt y) :
    |Lk| ≤ 7 * B + 1 := by
  have h1 := hr 1 (le_refl 1)
  have hs1 : Real.sqrt ((1:ℕ):ℝ) = 1 := by
    rw [Nat.cast_one, Real.sqrt_one]
  rw [hs1, div_one] at h1
  have h2 : ∑ d ∈ Icc 1 1, (toArith u * toArith v) d / d
      = (toArith u * toArith v) 1 := by
    rw [show (Icc 1 1 : Finset ℕ) = {1} from rfl, Finset.sum_singleton, Nat.cast_one,
      div_one]
  have h3 : |(toArith u * toArith v) 1| ≤ 1 := by
    rw [ArithmeticFunction.mul_apply, Nat.divisorsAntidiagonal_one,
      Finset.sum_singleton]
    have hu1 : |toArith u 1| ≤ 1 := by
      rw [show toArith u 1 = u 1 from by simp [toArith]]
      exact hub 1
    have hv1 : |toArith v 1| ≤ 1 := by
      rw [show toArith v 1 = v 1 from by simp [toArith]]
      exact hvb 1
    rw [abs_mul]
    calc |toArith u 1| * |toArith v 1| ≤ 1 * 1 :=
        mul_le_mul hu1 hv1 (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  calc |Lk| ≤ |Lk - ∑ d ∈ Icc 1 1, (toArith u * toArith v) d / d|
        + |∑ d ∈ Icc 1 1, (toArith u * toArith v) d / d| := by
        have := abs_add_le (Lk - ∑ d ∈ Icc 1 1, (toArith u * toArith v) d / d)
          (∑ d ∈ Icc 1 1, (toArith u * toArith v) d / d)
        simpa using this
    _ ≤ 7 * B + 1 := by
        rw [h2] at h1 ⊢
        linarith [h1, h3]

/-- Character sums against `d^{−σ}` decay at the `(y+1)^{−σ}` rate for every
    `σ ≥ 0` (Siegel brick S2a) — the sub-one extension of `char_rpow_tail_rate`. -/
lemma char_rpow_tail_rate_gen {q : ℕ} (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q)
    (hχ2 : χ ^ 2 = 1) (hχ1 : χ ≠ 1) {σ : ℝ} (hσ : 0 ≤ σ) (y : ℕ) :
    ∀ z : ℕ, y ≤ z →
    |∑ d ∈ Icc (y + 1) z, charFn q χ d * ((d:ℝ)) ^ (-σ)|
      ≤ 2 * (q:ℝ) * (((y + 1 : ℕ)):ℝ) ^ (-σ) := by
  intro z hz
  set w : ℕ → ℝ := fun d => if d = 0 then 1 else ((d:ℝ)) ^ (-σ) with hw
  have hw0 : ∀ d, 0 ≤ w d := by
    intro d
    rw [hw]
    rcases eq_or_ne d 0 with rfl | hd
    · simp
    · simp only [if_neg hd]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hwa : ∀ d, w (d + 1) ≤ w d := by
    intro d
    rw [hw]
    rcases eq_or_ne d 0 with rfl | hd
    · norm_num [Real.one_rpow]
    · simp only [if_neg hd, if_neg (by omega : d + 1 ≠ 0)]
      have hd0 : (0:ℝ) < (d:ℝ) := by
        have : (0:ℕ) < d := by omega
        exact_mod_cast this
      apply Real.rpow_le_rpow_of_nonpos hd0 (by push_cast; linarith)
      linarith
  have hG := charFn_partial_sum_bound hq χ hχ2 hχ1
  have h := abel_tail_general (charFn q χ) ((q:ℝ)) w hG hw0 hwa y z hz
  have hcongr : ∑ d ∈ Icc (y + 1) z, charFn q χ d * w d
      = ∑ d ∈ Icc (y + 1) z, charFn q χ d * ((d:ℝ)) ^ (-σ) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mem_Icc] at hd
    rw [hw]
    simp only [if_neg (by omega : d ≠ 0)]
  rw [hcongr] at h
  have hwy : w (y + 1) = (((y + 1 : ℕ)):ℝ) ^ (-σ) := by
    rw [hw]
    simp only [if_neg (by omega : y + 1 ≠ 0)]
  rw [hwy] at h
  exact h

/-- **The below-one partial-sum rate for `L(σ,χ)`** (Siegel brick S2b): at real
    `σ ∈ (9/10, 1)`, the analytically-continued `L`-value is within
    `2q(y+1)^{−σ}` of every partial sum — the representation the zero-gap
    bridge differences. -/
theorem LFunction_partial_rate_below_one {q : ℕ} [NeZero q] (hq : 1 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1) (hχ1 : χ ≠ 1)
    {σ : ℝ} (hσ1 : 9/10 < σ) (hσ2 : σ < 1) (y : ℕ) :
    ‖DirichletCharacter.LFunction χ ((σ:ℂ))
      - ((∑ d ∈ Icc 1 y, charFn q χ d * ((d:ℝ)) ^ (-σ) : ℝ) : ℂ)‖
    ≤ 2 * (q:ℝ) * (((y + 1 : ℕ)):ℝ) ^ (-σ) := by
  have hσ0 : (0:ℝ) < σ := by linarith
  -- the running character sum
  set SFn : ℕ → ℝ := fun n => ∑ m ∈ Icc 1 n, charFn q χ m with hSFn
  have hSFn0 : SFn 0 = 0 := by
    rw [hSFn]
    simp
  have hSb : ∀ n : ℕ, |SFn n| ≤ (q:ℝ) := fun n => charFn_partial_sum_bound hq χ hχ2 hχ1 n
  have hSE : ∀ n : ℕ, 1 ≤ n → |SFn n| ≤ (q:ℝ) * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
    intro n hn
    have hn1r : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have h1 : (1:ℝ) ≤ ((n:ℝ)) ^ ((3:ℝ)/4) := Real.one_le_rpow hn1r (by norm_num)
    have h2 : (1:ℝ) ≤ 1 + Real.log n := by
      have := Real.log_nonneg hn1r
      linarith
    calc |SFn n| ≤ (q:ℝ) := hSb n
      _ = (q:ℝ) * 1 := (mul_one _).symm
      _ ≤ (q:ℝ) * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
          nlinarith [h1, h2]
  -- the Abel continuation W
  set W : ℂ → ℂ := fun s => ∑' n : ℕ,
      ((SFn n : ℝ) : ℂ) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)) with hW
  -- LFunction = W at σ via the identity theorem
  have hLW : DirichletCharacter.LFunction χ ((σ:ℂ)) = W ((σ:ℂ)) := by
    apply eqOn_slit_halfplane (DirichletCharacter.LFunction χ) W
      (fun s _ _ => (DirichletCharacter.differentiable_LFunction hχ1).differentiableAt)
      (fun s hs _ => eseries_differentiableAt SFn ((q:ℝ)) (Nat.cast_nonneg q) hSFn0 hSE s hs)
      ?_ ((σ:ℂ)) (by rw [Complex.ofReal_re]; exact hσ1) (by
        intro h
        rw [Complex.ofReal_eq_one] at h
        linarith)
    intro s hs
    have hsum : LSeriesSummable (fun n => ((charFn q χ n : ℝ) : ℂ)) s := by
      apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ hs
      intro n _
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact charFn_bound χ hχ2 n
    have hC : ∀ x : ℕ, ‖∑ n ∈ Icc 1 x, ((charFn q χ n : ℝ) : ℂ)‖ ≤ (q:ℝ) * x := by
      intro x
      rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
      rcases Nat.eq_zero_or_pos x with rfl | hx
      · simp
      · have hx1r : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
        calc |∑ n ∈ Icc 1 x, charFn q χ n| ≤ (q:ℝ) :=
              charFn_partial_sum_bound hq χ hχ2 hχ1 x
          _ ≤ (q:ℝ) * x := by nlinarith [Nat.cast_nonneg (α := ℝ) q]
    have hL : DirichletCharacter.LFunction χ s
        = LSeries (fun n => ((charFn q χ n : ℝ) : ℂ)) s := by
      rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
      exact (LSeries_congr (fun {n} hn => charFn_repr χ hχ2 n) s).symm
    rw [hL, lseries_eq_tsum_abel _ ((q:ℝ)) hC hs hsum, hW]
    apply tsum_congr
    intro n
    rw [hSFn, Complex.ofReal_sum]
  -- the direct partial sums converge to W(σ)
  set D : ℕ → ℝ := fun z => ∑ d ∈ Icc 1 z, charFn q χ d * ((d:ℝ)) ^ (-σ) with hD
  have hterm_cast : ∀ d : ℕ, ((charFn q χ d * ((d:ℝ)) ^ (-σ) : ℝ) : ℂ)
      = ((charFn q χ d : ℝ) : ℂ) * ((d:ℂ)) ^ (-((σ:ℝ):ℂ)) := by
    intro d
    rw [cpow_real_cast d σ]
    push_cast
    ring
  -- summability of the W-terms at σ
  have hWsum : Summable (fun n : ℕ =>
      ((SFn n : ℝ) : ℂ) * (((n:ℂ)) ^ (-((σ:ℝ):ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-((σ:ℝ):ℂ)))) := by
    have hmaj : Summable (fun n : ℕ => (q:ℝ) * (1 / ((n:ℝ)) ^ ((19:ℝ)/10))) :=
      Summable.mul_left _ (Real.summable_one_div_nat_rpow.mpr (by norm_num))
    have hg0 : ∀ n : ℕ, 0 ≤ (if n = 0 then (0:ℝ) else
        (q:ℝ) * (1 / ((n:ℝ)) ^ ((19:ℝ)/10))) := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · rw [if_pos rfl]
      · rw [if_neg hn]
        positivity
    have hgle : ∀ n : ℕ, (if n = 0 then (0:ℝ) else
        (q:ℝ) * (1 / ((n:ℝ)) ^ ((19:ℝ)/10)))
        ≤ (q:ℝ) * (1 / ((n:ℝ)) ^ ((19:ℝ)/10)) := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · rw [if_pos rfl]
        positivity
      · rw [if_neg hn]
    apply Summable.of_norm_bounded (g := fun n : ℕ => if n = 0 then 0 else
      (q:ℝ) * (1 / ((n:ℝ)) ^ ((19:ℝ)/10))) (Summable.of_nonneg_of_le hg0 hgle hmaj)
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [hSFn0]
      simp
    · rw [if_neg hn]
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hn1r : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
      have hn0 : (0:ℝ) < (n:ℝ) := by linarith
      have hΔ : ((n:ℂ)) ^ (-((σ:ℝ):ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-((σ:ℝ):ℂ))
          = (((((n:ℝ)) ^ (-σ) - (((n + 1 : ℕ)):ℝ) ^ (-σ)) : ℝ) : ℂ) := by
        rw [cpow_real_cast n σ, cpow_real_cast (n + 1) σ]
        push_cast
        ring
      rw [hΔ, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      have hΔ0 : (0:ℝ) ≤ ((n:ℝ)) ^ (-σ) - (((n + 1 : ℕ)):ℝ) ^ (-σ) := by
        have : (((n + 1 : ℕ)):ℝ) ^ (-σ) ≤ ((n:ℝ)) ^ (-σ) := by
          apply Real.rpow_le_rpow_of_nonpos hn0 (by push_cast; linarith)
          linarith
        linarith
      have hΔle : ((n:ℝ)) ^ (-σ) - (((n + 1 : ℕ)):ℝ) ^ (-σ) ≤ ((n:ℝ)) ^ (-((19:ℝ)/10)) := by
        calc ((n:ℝ)) ^ (-σ) - (((n + 1 : ℕ)):ℝ) ^ (-σ)
            ≤ σ * ((n:ℝ)) ^ (-σ - 1) := rpow_diff_le n hn1 σ hσ0.le
          _ ≤ 1 * ((n:ℝ)) ^ (-σ - 1) := by
              apply mul_le_mul_of_nonneg_right (by linarith)
                (Real.rpow_nonneg hn0.le _)
          _ = ((n:ℝ)) ^ (-σ - 1) := one_mul _
          _ ≤ ((n:ℝ)) ^ (-((19:ℝ)/10)) := by
              apply Real.rpow_le_rpow_of_exponent_le hn1r
              linarith
      have hone : (1:ℝ) / ((n:ℝ)) ^ ((19:ℝ)/10) = ((n:ℝ)) ^ (-((19:ℝ)/10)) := by
        rw [one_div, ← Real.rpow_neg hn0.le]
      rw [abs_of_nonneg hΔ0, hone]
      exact mul_le_mul (hSb n) hΔle hΔ0 (Nat.cast_nonneg q)
  -- boundary decay
  have hbdry : Tendsto (fun z : ℕ => ((SFn z : ℝ) : ℂ) * ((z:ℂ)) ^ (-((σ:ℝ):ℂ)))
      atTop (nhds 0) := by
    have hbound : ∀ z : ℕ, ‖((SFn z : ℝ) : ℂ) * ((z:ℂ)) ^ (-((σ:ℝ):ℂ))‖
        ≤ (q:ℝ) * ((z:ℝ)) ^ (-σ) := by
      intro z
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, cpow_real_cast z σ,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg z) _)]
      exact mul_le_mul_of_nonneg_right (hSb z) (Real.rpow_nonneg (Nat.cast_nonneg z) _)
    have hg : Tendsto (fun z : ℕ => (q:ℝ) * ((z:ℝ)) ^ (-σ)) atTop (nhds 0) := by
      have h := tendsto_rpow_neg_atTop hσ0
      have hcomp := h.comp tendsto_natCast_atTop_atTop
      have h2 := hcomp.const_mul ((q:ℝ))
      simpa [Function.comp_def] using h2
    exact squeeze_zero_norm hbound hg
  -- the Icc-to-range recount of the W-partials
  have hIcc_range : ∀ z : ℕ, ∑ n ∈ Icc 1 (z - 1),
      ((SFn n : ℝ) : ℂ) * (((n:ℂ)) ^ (-((σ:ℝ):ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-((σ:ℝ):ℂ)))
      = ∑ n ∈ range z,
      ((SFn n : ℝ) : ℂ) * (((n:ℂ)) ^ (-((σ:ℝ):ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-((σ:ℝ):ℂ))) := by
    intro z
    rcases Nat.eq_zero_or_pos z with rfl | hz
    · rfl
    · rw [show range z = insert 0 (Icc 1 (z - 1)) from by
        ext d
        simp only [Finset.mem_insert, Finset.mem_range, Finset.mem_Icc]
        omega, Finset.sum_insert (by
          simp only [Finset.mem_Icc]
          omega)]
      rw [hSFn0]
      simp
  have hsum_shift : Tendsto (fun z : ℕ => ∑ n ∈ Icc 1 (z - 1),
      ((SFn n : ℝ) : ℂ) * (((n:ℂ)) ^ (-((σ:ℝ):ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-((σ:ℝ):ℂ))))
      atTop (nhds (W ((σ:ℂ)))) := by
    have h := hWsum.hasSum.tendsto_sum_nat
    apply h.congr
    intro z
    exact (hIcc_range z).symm
  -- the Abel identity links D to the W-partials
  have habel : ∀ z : ℕ, 1 ≤ z → ((D z : ℝ) : ℂ)
      = ((SFn z : ℝ) : ℂ) * ((z:ℂ)) ^ (-((σ:ℝ):ℂ))
        + ∑ n ∈ Icc 1 (z - 1),
          ((SFn n : ℝ) : ℂ) * (((n:ℂ)) ^ (-((σ:ℝ):ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-((σ:ℝ):ℂ))) := by
    intro z hz
    have h := abel_initial (fun n => ((charFn q χ n : ℝ) : ℂ))
      (fun n => ((n:ℂ)) ^ (-((σ:ℝ):ℂ))) z hz
    have hL : ((D z : ℝ) : ℂ) = ∑ n ∈ Icc 1 z,
        ((charFn q χ n : ℝ) : ℂ) * ((n:ℂ)) ^ (-((σ:ℝ):ℂ)) := by
      rw [hD]
      push_cast [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [← hterm_cast d]
      push_cast
      ring
    have hA : ∀ x : ℕ, ∑ m ∈ Icc 1 x, ((charFn q χ m : ℝ) : ℂ) = ((SFn x : ℝ) : ℂ) := by
      intro x
      rw [hSFn, Complex.ofReal_sum]
    rw [hL, h, hA z]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    rw [hA n]
  -- D converges to W(σ)
  have hDW : Tendsto (fun z : ℕ => ((D z : ℝ) : ℂ)) atTop (nhds (W ((σ:ℂ)))) := by
    have h := hbdry.add hsum_shift
    rw [zero_add] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with z hz
    exact (habel z hz).symm
  -- the tail rate transfers to the limit
  have hrate : ∀ z : ℕ, y ≤ z →
      ‖((D z : ℝ) : ℂ) - ((D y : ℝ) : ℂ)‖ ≤ 2 * (q:ℝ) * (((y + 1 : ℕ)):ℝ) ^ (-σ) := by
    intro z hz
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hsplit : D z - D y = ∑ d ∈ Icc (y + 1) z, charFn q χ d * ((d:ℝ)) ^ (-σ) := by
      rw [hD]
      simp only
      rw [show Icc 1 z = Icc 1 y ∪ Icc (y + 1) z from by
        ext d
        simp only [Finset.mem_union, Finset.mem_Icc]
        omega, Finset.sum_union (by
          rw [Finset.disjoint_left]
          intro d hd hd2
          rw [Finset.mem_Icc] at hd hd2
          omega)]
      ring
    rw [hsplit]
    exact char_rpow_tail_rate_gen hq χ hχ2 hχ1 hσ0.le y z hz
  have hfinal : ‖W ((σ:ℂ)) - ((D y : ℝ) : ℂ)‖ ≤ 2 * (q:ℝ) * (((y + 1 : ℕ)):ℝ) ^ (-σ) := by
    have h2 : Tendsto (fun z : ℕ => ‖((D z : ℝ) : ℂ) - ((D y : ℝ) : ℂ)‖) atTop
        (nhds ‖W ((σ:ℂ)) - ((D y : ℝ) : ℂ)‖) := (hDW.sub tendsto_const_nhds).norm
    apply le_of_tendsto h2
    filter_upwards [eventually_ge_atTop y] with z hz
    exact hrate z hz
  rw [hLW]
  exact hfinal

/-- **The head difference across the window** (Siegel brick S2c): moving the
    exponent from `β` to `1` across a window with `N^{1−β} ≤ 2` costs only
    `2(1−β)(1+log N)²` on partial sums of a quadratic character. -/
lemma char_head_diff_bound {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1)
    (N : ℕ) (hN : 1 ≤ N) {β : ℝ} (hβ1 : 0 < β) (hβ2 : β < 1)
    (hN2 : ((N:ℝ)) ^ (1 - β) ≤ 2) :
    |∑ d ∈ Icc 1 N, charFn q χ d / d - ∑ d ∈ Icc 1 N, charFn q χ d * ((d:ℝ)) ^ (-β)|
    ≤ 2 * (1 - β) * (1 + Real.log N) ^ 2 := by
  have hNr : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hlogN : (0:ℝ) ≤ Real.log N := Real.log_nonneg hNr
  -- per-term bound
  have hterm : ∀ d : ℕ, d ∈ Icc 1 N →
      |charFn q χ d / d - charFn q χ d * ((d:ℝ)) ^ (-β)|
      ≤ 2 * (1 - β) * (Real.log d / d) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd1r : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd.1
    have hd0 : (0:ℝ) < (d:ℝ) := by linarith
    have hlogd : (0:ℝ) ≤ Real.log d := Real.log_nonneg hd1r
    -- factor: 1/d − d^{−β} = −d^{−1}(d^{1−β} − 1)
    have hfac : charFn q χ d / d - charFn q χ d * ((d:ℝ)) ^ (-β)
        = -(charFn q χ d * (((d:ℝ)) ^ (1 - β) - 1) / d) := by
      have hrw : ((d:ℝ)) ^ (-β) = ((d:ℝ)) ^ (1 - β) / d := by
        rw [eq_div_iff (ne_of_gt hd0)]
        calc ((d:ℝ)) ^ (-β) * (d:ℝ) = ((d:ℝ)) ^ (-β) * ((d:ℝ)) ^ (1:ℝ) := by
              rw [Real.rpow_one]
          _ = ((d:ℝ)) ^ (-β + 1) := (Real.rpow_add hd0 _ _).symm
          _ = ((d:ℝ)) ^ (1 - β) := by ring_nf
      rw [hrw]
      field_simp
      ring
    rw [hfac, abs_neg, abs_div, Nat.abs_cast, abs_mul]
    -- d^{1−β} − 1 ≤ 2(1−β)log d
    have hexp : ((d:ℝ)) ^ (1 - β) - 1 ≤ 2 * (1 - β) * Real.log d := by
      have h1β : (0:ℝ) ≤ 1 - β := by linarith
      have hx0 : (0:ℝ) ≤ (1 - β) * Real.log d := mul_nonneg h1β hlogd
      have hrpow : ((d:ℝ)) ^ (1 - β) = Real.exp ((1 - β) * Real.log d) := by
        rw [Real.rpow_def_of_pos hd0]
        ring_nf
      have hEM : Real.exp ((1 - β) * Real.log d) - 1
          ≤ ((1 - β) * Real.log d) * Real.exp ((1 - β) * Real.log d) := by
        set x : ℝ := (1 - β) * Real.log d with hx
        have h1 := Real.add_one_le_exp (-x)
        have h2 : (0:ℝ) < Real.exp x := Real.exp_pos _
        have h3 : Real.exp (-x) = (Real.exp x)⁻¹ := Real.exp_neg x
        rw [h3] at h1
        have h4 : (-x + 1) * Real.exp x ≤ 1 := by
          calc (-x + 1) * Real.exp x ≤ (Real.exp x)⁻¹ * Real.exp x := by
                apply mul_le_mul_of_nonneg_right h1 h2.le
            _ = 1 := inv_mul_cancel₀ (ne_of_gt h2)

        nlinarith [h4]
      have hd2 : ((d:ℝ)) ^ (1 - β) ≤ 2 := by
        calc ((d:ℝ)) ^ (1 - β) ≤ ((N:ℝ)) ^ (1 - β) := by
              apply Real.rpow_le_rpow hd0.le _ h1β
              exact_mod_cast hd.2
          _ ≤ 2 := hN2
      calc ((d:ℝ)) ^ (1 - β) - 1
          = Real.exp ((1 - β) * Real.log d) - 1 := by rw [hrpow]
        _ ≤ ((1 - β) * Real.log d) * Real.exp ((1 - β) * Real.log d) := hEM
        _ = ((1 - β) * Real.log d) * ((d:ℝ)) ^ (1 - β) := by rw [hrpow]
        _ ≤ ((1 - β) * Real.log d) * 2 := by
            apply mul_le_mul_of_nonneg_left hd2 hx0
        _ = 2 * (1 - β) * Real.log d := by ring
    have hnn : (0:ℝ) ≤ ((d:ℝ)) ^ (1 - β) - 1 := by
      have : (1:ℝ) ≤ ((d:ℝ)) ^ (1 - β) := Real.one_le_rpow hd1r (by linarith)
      linarith
    calc |charFn q χ d| * |((d:ℝ)) ^ (1 - β) - 1| / (d:ℝ)
        ≤ 1 * (2 * (1 - β) * Real.log d) / (d:ℝ) := by
          apply div_le_div_of_nonneg_right _ hd0.le
          apply mul_le_mul (charFn_bound χ hχ2 d) _ (abs_nonneg _) zero_le_one
          rw [abs_of_nonneg hnn]
          exact hexp
      _ = 2 * (1 - β) * (Real.log d / d) := by ring
  -- sum the per-term bounds
  have hsum : ∑ d ∈ Icc 1 N, Real.log d / d ≤ (1 + Real.log N) ^ 2 := by
    calc ∑ d ∈ Icc 1 N, Real.log d / d
        ≤ ∑ d ∈ Icc 1 N, Real.log N * (1 / d) := by
          apply Finset.sum_le_sum
          intro d hd
          rw [Finset.mem_Icc] at hd
          have hd0 : (0:ℝ) < (d:ℝ) := by
            have : (0:ℕ) < d := by omega
            exact_mod_cast this
          have hlog_le : Real.log d ≤ Real.log N := by
            apply Real.log_le_log hd0
            exact_mod_cast hd.2
          rw [mul_one_div]
          apply div_le_div_of_nonneg_right hlog_le hd0.le
      _ = Real.log N * ∑ d ∈ Icc 1 N, (1:ℝ) / d := by rw [Finset.mul_sum]
      _ ≤ Real.log N * (1 + Real.log N) := by
          apply mul_le_mul_of_nonneg_left (sum_one_div_le_log N hN) hlogN
      _ ≤ (1 + Real.log N) ^ 2 := by nlinarith [hlogN]
  calc |∑ d ∈ Icc 1 N, charFn q χ d / d - ∑ d ∈ Icc 1 N, charFn q χ d * ((d:ℝ)) ^ (-β)|
      = |∑ d ∈ Icc 1 N, (charFn q χ d / d - charFn q χ d * ((d:ℝ)) ^ (-β))| := by
        rw [Finset.sum_sub_distrib]
    _ ≤ ∑ d ∈ Icc 1 N, |charFn q χ d / d - charFn q χ d * ((d:ℝ)) ^ (-β)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Icc 1 N, 2 * (1 - β) * (Real.log d / d) := Finset.sum_le_sum hterm
    _ = 2 * (1 - β) * ∑ d ∈ Icc 1 N, Real.log d / d := by rw [Finset.mul_sum]
    _ ≤ 2 * (1 - β) * (1 + Real.log N) ^ 2 := by
        apply mul_le_mul_of_nonneg_left hsum
        nlinarith [hβ2]

/-- **THE ZERO-GAP BRIDGE** (Siegel brick S2d): a real zero `β` of `L(·,χ)` inside
    the window `(1−β)·log q ≤ 1/10` forces the `L(1,χ)`-limit small:
    `|L₁| ≤ 2(1−β)(1+3log q)² + 4q^{−17/10}` — so a big `L(1,χ)` pushes zeros away. -/
theorem zero_gap_bridge {q : ℕ} [NeZero q] (hq : 3 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1) (hχ1 : χ ≠ 1)
    (L₁ : ℝ)
    (hr : ∀ y : ℕ, |L₁ - ∑ d ∈ Icc 1 y, charFn q χ d / d| ≤ 2 * (q:ℝ) / (y + 1))
    {β : ℝ} (hβ2 : β < 1) (hβw : (1 - β) * Real.log q ≤ 1/10)
    (hzero : DirichletCharacter.LFunction χ ((β:ℂ)) = 0) :
    |L₁| ≤ 2 * (1 - β) * (1 + 3 * Real.log q) ^ 2 + 4 * ((q:ℝ)) ^ (-(17:ℝ)/10) := by
  have hq1 : 1 ≤ q := by omega
  have hq0 : (0:ℝ) < (q:ℝ) := by
    have : (0:ℕ) < q := by omega
    exact_mod_cast this
  have hq3r : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  -- log q > 1
  have hlogq1 : (1:ℝ) < Real.log q := by
    have he : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) he
      _ ≤ Real.log q := Real.log_le_log (by norm_num) hq3r
  have hβ910 : (9:ℝ)/10 < β := by
    have h1 : 1 - β ≤ (1/10) / Real.log q := by
      rw [le_div_iff₀ (by linarith)]
      linarith [hβw]
    have h2 : (1/10 : ℝ) / Real.log q < 1/10 := by
      rw [div_lt_iff₀ (by linarith)]
      nlinarith [hlogq1]
    linarith
  have hβ0 : (0:ℝ) < β := by linarith
  set N : ℕ := q ^ 3 with hN
  have hN1 : 1 ≤ N := Nat.one_le_pow 3 q (by omega)
  have hNr : ((N:ℕ):ℝ) = ((q:ℝ)) ^ (3:ℕ) := by
    rw [hN]
    push_cast
    ring
  have hlogN : Real.log N = 3 * Real.log q := by
    rw [hNr, Real.log_pow]
    push_cast
    ring
  -- N^{1−β} ≤ 2
  have hN2 : ((N:ℝ)) ^ (1 - β) ≤ 2 := by
    have hN0 : (0:ℝ) < (N:ℝ) := by
      rw [hNr]
      positivity
    rw [Real.rpow_def_of_pos hN0]
    calc Real.exp (Real.log ((N:ℝ)) * (1 - β)) ≤ Real.exp (3/10) := by
          apply Real.exp_le_exp.mpr
          rw [hlogN]
          nlinarith [hβw]
      _ ≤ 2 := by
          have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
          calc Real.exp (3/10) ≤ Real.exp (Real.log 2) := by
                apply Real.exp_le_exp.mpr
                linarith
            _ = 2 := Real.exp_log (by norm_num)
  set D1 : ℝ := ∑ d ∈ Icc 1 N, charFn q χ d / d with hD1
  set Dβ : ℝ := ∑ d ∈ Icc 1 N, charFn q χ d * ((d:ℝ)) ^ (-β) with hDβ
  -- piece (a): |L₁ − D_N(1)| ≤ 2q^{−17/10}
  have ha : |L₁ - D1| ≤ 2 * ((q:ℝ)) ^ (-(17:ℝ)/10) := by
    calc |L₁ - D1| ≤ 2 * (q:ℝ) / ((N:ℝ) + 1) := hr N
      _ ≤ 2 * (q:ℝ) / ((q:ℝ)) ^ (3:ℕ) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          rw [hNr]
          linarith
      _ = 2 * ((q:ℝ)) ^ (-(2:ℝ)) := by
          rw [show (-(2:ℝ)) = -(((2:ℕ)):ℝ) from by norm_num, Real.rpow_neg hq0.le,
            Real.rpow_natCast]
          field_simp
      _ ≤ 2 * ((q:ℝ)) ^ (-(17:ℝ)/10) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Real.rpow_le_rpow_of_exponent_le (by linarith)
          norm_num
  -- piece (b): the head difference
  have hb : |D1 - Dβ| ≤ 2 * (1 - β) * (1 + 3 * Real.log q) ^ 2 := by
    have h := char_head_diff_bound χ hχ2 N hN1 hβ0 hβ2 hN2
    rw [hlogN] at h
    exact h
  -- piece (c): |D_N(β)| ≤ 2q^{−17/10} at the zero
  have hc : |Dβ| ≤ 2 * ((q:ℝ)) ^ (-(17:ℝ)/10) := by
    have h1 := LFunction_partial_rate_below_one hq1 χ hχ2 hχ1 hβ910 hβ2 N
    rw [hzero, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs] at h1
    have hN0 : (0:ℝ) < (N:ℝ) := by
      rw [hNr]
      positivity
    have h2 : (((N + 1 : ℕ)):ℝ) ^ (-β) ≤ ((N:ℝ)) ^ (-β) := by
      apply Real.rpow_le_rpow_of_nonpos hN0 (by push_cast; linarith)
      linarith
    have hq1r : (1:ℝ) ≤ (q:ℝ) := by linarith
    have h4 : ((N:ℝ)) ^ (-β) = ((q:ℝ)) ^ ((3:ℝ) * (-β)) := by
      rw [hNr, ← Real.rpow_natCast (q:ℝ) 3, ← Real.rpow_mul hq0.le]
      congr 1
    have h5 : (q:ℝ) * ((q:ℝ)) ^ ((3:ℝ) * (-β)) = ((q:ℝ)) ^ (1 + (3:ℝ) * (-β)) := by
      rw [Real.rpow_add hq0, Real.rpow_one]
    have h6 : ((q:ℝ)) ^ (1 + (3:ℝ) * (-β)) ≤ ((q:ℝ)) ^ (-(17:ℝ)/10) := by
      apply Real.rpow_le_rpow_of_exponent_le hq1r
      nlinarith [hβ910]
    calc |Dβ| ≤ 2 * (q:ℝ) * (((N + 1 : ℕ)):ℝ) ^ (-β) := h1
      _ ≤ 2 * (q:ℝ) * ((N:ℝ)) ^ (-β) := by
          apply mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 * ((q:ℝ) * ((q:ℝ)) ^ ((3:ℝ) * (-β))) := by
          rw [h4]
          ring
      _ = 2 * ((q:ℝ)) ^ (1 + (3:ℝ) * (-β)) := by rw [h5]
      _ ≤ 2 * ((q:ℝ)) ^ (-(17:ℝ)/10) := by
          apply mul_le_mul_of_nonneg_left h6 (by norm_num)
  -- triangle assembly
  have h1 := abs_add_le (L₁ - D1) (D1 - Dβ)
  have e1 : (L₁ - D1) + (D1 - Dβ) = L₁ - Dβ := by ring
  rw [e1] at h1
  have h2 := abs_add_le (L₁ - Dβ) Dβ
  have e2 : (L₁ - Dβ) + Dβ = L₁ := by ring
  rw [e2] at h2
  linarith [h1, h2, ha, hb, hc]

/-- **The explicit-C E-package** (Siegel brick S3-pre-a): `quad_E_package` with the
    constant exposed — `C = 30(1+q₁)(1+B) + 36 + 3|L₁Lk|`, ready for the
    polynomial-in-`q` bound the dichotomy needs. -/
theorem quad_E_package_explicit (g₁ g₂ : ℕ → ℝ) (q₁ B L₁ Lk : ℝ)
    (h1b : ∀ n, |g₁ n| ≤ 1) (h2b : ∀ n, |g₂ n| ≤ 1)
    (hL₁ : ∀ y : ℕ, |L₁ - ∑ d ∈ Icc 1 y, g₁ d / d| ≤ 2 * q₁ / (y + 1))
    (hq₁ : 0 ≤ q₁)
    (hH : ∀ M : ℕ, 1 ≤ M →
      |∑ n ∈ Icc 1 M, (toArith (fun _ => (1:ℝ)) * toArith g₁) n - L₁ * M|
        ≤ (1 + 4 * q₁) * (Real.sqrt M + 1))
    (hKb : ∀ t : ℕ, |∑ n ∈ Icc 1 t, (toArith g₂ * toArith (fun m => g₁ m * g₂ m)) n|
        ≤ B * (Real.sqrt t + 1))
    (hLk : ∀ y : ℕ, 1 ≤ y →
      |Lk - ∑ d ∈ Icc 1 y, (toArith g₂ * toArith (fun m => g₁ m * g₂ m)) d / d|
        ≤ 7 * B / Real.sqrt y) :
    ∀ n : ℕ, 1 ≤ n →
      |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
          * toArith (fun k => g₁ k * g₂ k)) m - L₁ * Lk * n|
        ≤ (30 * (1 + q₁) * (1 + B) + 36 + 3 * |L₁ * Lk|)
          * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
  have hB0 : 0 ≤ B := by
    have h0 := hKb 0
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, abs_zero,
      Nat.cast_zero, Real.sqrt_zero, zero_add, mul_one] at h0
    exact h0
  intro n hn
  have hn0 : (0:ℝ) < (n:ℝ) := by
    have : (0:ℕ) < n := hn
    exact_mod_cast this
  have hn1r : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have htge1 : (1:ℝ) ≤ ((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n) := by
    have h1 : (1:ℝ) ≤ ((n:ℝ)) ^ ((3:ℝ)/4) := Real.one_le_rpow hn1r (by norm_num)
    have h2 : (1:ℝ) ≤ 1 + Real.log n := by
      have := Real.log_nonneg hn1r
      linarith
    nlinarith [h1, h2]
  have ht0 : (0:ℝ) ≤ ((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n) := by linarith
  rcases Nat.lt_or_ge n 4 with h4 | h4
  · -- n ∈ {1, 2, 3}: cube bound
    have hA : |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
        * toArith (fun k => g₁ k * g₂ k)) m| ≤ 36 := by
      calc |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
            * toArith (fun k => g₁ k * g₂ k)) m|
          ≤ ∑ m ∈ Icc 1 n, |(toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
            * toArith (fun k => g₁ k * g₂ k)) m| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ m ∈ Icc 1 n, ((m:ℝ)) ^ (3:ℕ) :=
            Finset.sum_le_sum (fun m _ => quad_value_le_cube g₁ g₂ h1b h2b m)
        _ ≤ ∑ m ∈ Icc (1:ℕ) 3, ((m:ℝ)) ^ (3:ℕ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro m hm
              rw [Finset.mem_Icc] at hm ⊢
              omega
            · intro m _ _
              positivity
        _ = 36 := by
            rw [show (Icc (1:ℕ) 3 : Finset ℕ) = {1, 2, 3} by decide]
            norm_num [Finset.sum_insert, Finset.mem_insert, Finset.sum_singleton]
    have h3n : (n:ℝ) ≤ 3 := by
      have : n ≤ 3 := by omega
      exact_mod_cast this
    have hlam : |L₁ * Lk| * (n:ℝ) ≤ 3 * |L₁ * Lk| := by
      nlinarith [abs_nonneg (L₁ * Lk), h3n]
    have htri : |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
        * toArith (fun k => g₁ k * g₂ k)) m - L₁ * Lk * n|
        ≤ |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
            * toArith (fun k => g₁ k * g₂ k)) m| + |L₁ * Lk * (n:ℝ)| := by
      have h := abs_add_le (∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁
          * toArith g₂ * toArith (fun k => g₁ k * g₂ k)) m) (-(L₁ * Lk * (n:ℝ)))
      rw [abs_neg, ← sub_eq_add_neg] at h
      exact h
    have habsmul : |L₁ * Lk * (n:ℝ)| = |L₁ * Lk| * (n:ℝ) := by
      rw [abs_mul, Nat.abs_cast]
    calc |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
          * toArith (fun k => g₁ k * g₂ k)) m - L₁ * Lk * n|
        ≤ 36 + 3 * |L₁ * Lk| := by
          rw [habsmul] at htri
          linarith [htri, hA, hlam]
      _ = (36 + 3 * |L₁ * Lk|) * 1 := (mul_one _).symm
      _ ≤ (36 + 3 * |L₁ * Lk|) * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
          apply mul_le_mul_of_nonneg_left htge1 (by positivity)
      _ ≤ (30 * (1 + q₁) * (1 + B) + 36 + 3 * |L₁ * Lk|)
            * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
          apply mul_le_mul_of_nonneg_right _ ht0
          nlinarith [hq₁, hB0]
  · -- n ≥ 4: the hyperbola asymptotic
    have hmain := quad_coeff_asymptotic g₁ g₂ q₁ B L₁ Lk h1b h2b hL₁ hq₁ hH hKb hLk n h4
    have hconv : Real.sqrt n * Real.sqrt (Real.sqrt n) = ((n:ℝ)) ^ ((3:ℝ)/4) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
        ← Real.rpow_mul hn0.le, ← Real.rpow_add hn0]
      norm_num
    rw [hconv] at hmain
    calc |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
          * toArith (fun k => g₁ k * g₂ k)) m - L₁ * Lk * n|
        ≤ 30 * (1 + q₁) * (1 + B) * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := hmain
      _ ≤ (30 * (1 + q₁) * (1 + B) + 36 + 3 * |L₁ * Lk|)
            * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
          apply mul_le_mul_of_nonneg_right _ ht0
          nlinarith [abs_nonneg (L₁ * Lk)]

/-- **The bounded character quad system** (Siegel brick S3-pre-b):
    `quad_system_for_chars` with the constant polynomially controlled:
    `C ≤ 1000(1+q₁)²(1+q₂)²` — the shape the dichotomy's `x`-choice requires. -/
theorem quad_system_for_chars_bounded {q₁ q₂ : ℕ} (hq₁ : 1 ≤ q₁) (hq₂ : 1 ≤ q₂)
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁2 : χ₁ ^ 2 = 1) (hχ₂2 : χ₂ ^ 2 = 1) (hχ₁1 : χ₁ ≠ 1) (hχ₂1 : χ₂ ≠ 1)
    (hχ₃1 : (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
        * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) ≠ 1) :
    ∃ L₁ Lk C : ℝ,
      (∀ y : ℕ, |L₁ - ∑ d ∈ Icc 1 y, charFn q₁ χ₁ d / d| ≤ 2 * (q₁:ℝ) / (y + 1))
      ∧ (∀ y : ℕ, 1 ≤ y →
          |Lk - ∑ d ∈ Icc 1 y, (toArith (charFn q₂ χ₂)
              * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) d / d|
            ≤ 7 * (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) / Real.sqrt y)
      ∧ 0 ≤ C
      ∧ C ≤ 1000 * ((q₁:ℝ) + 1) ^ 2 * ((q₂:ℝ) + 1) ^ 2
      ∧ ∀ n : ℕ, 1 ≤ n →
        |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith (charFn q₁ χ₁)
            * toArith (charFn q₂ χ₂)
            * toArith (fun k => charFn q₁ χ₁ k * charFn q₂ χ₂ k)) m - L₁ * Lk * n|
          ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
  have h1b := fun n => charFn_bound χ₁ hχ₁2 n
  have h2b := fun n => charFn_bound χ₂ hχ₂2 n
  have hG₁ := charFn_partial_sum_bound hq₁ χ₁ hχ₁2 hχ₁1
  have hG₂ := charFn_partial_sum_bound hq₂ χ₂ hχ₂2 hχ₂1
  obtain ⟨L₁, hL₁⟩ := log_mean_exists (charFn q₁ χ₁) ((q₁:ℝ)) hG₁
  have hH : ∀ M : ℕ, 1 ≤ M →
      |∑ n ∈ Icc 1 M, (toArith (fun _ => (1:ℝ)) * toArith (charFn q₁ χ₁)) n - L₁ * M|
        ≤ (1 + 4 * (q₁:ℝ)) * (Real.sqrt M + 1) := by
    intro M hM
    have hcomm : toArith (fun _ => (1:ℝ)) * toArith (charFn q₁ χ₁)
        = toArith (charFn q₁ χ₁) * toArith (fun _ => (1:ℝ)) := mul_comm _ _
    rw [hcomm]
    exact divisor_char_asymptotic (charFn q₁ χ₁) ((q₁:ℝ)) L₁ h1b hG₁ hL₁ M hM
  have hχ₃2 : ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
      * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) ^ 2 = 1 := by
    rw [mul_pow, ← map_pow, ← map_pow, hχ₁2, hχ₂2, map_one, map_one, mul_one]
  have hq₁₂ : 1 ≤ q₁ * q₂ :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hG₃ := charFn_partial_sum_bound hq₁₂ _ hχ₃2 hχ₃1
  have h12b : ∀ n, |charFn q₁ χ₁ n * charFn q₂ χ₂ n| ≤ 1 := by
    intro n
    rw [abs_mul]
    calc |charFn q₁ χ₁ n| * |charFn q₂ χ₂ n| ≤ 1 * 1 :=
        mul_le_mul (h1b n) (h2b n) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hK2 : ∀ t : ℕ, |∑ n ∈ Icc 1 t, (charFn q₁ χ₁ n * charFn q₂ χ₂ n)|
      ≤ (q₁:ℝ) * (q₂:ℝ) := by
    intro t
    have heq : ∑ n ∈ Icc 1 t, (charFn q₁ χ₁ n * charFn q₂ χ₂ n)
        = ∑ n ∈ Icc 1 t, charFn (q₁ * q₂)
            ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
              * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) n :=
      Finset.sum_congr rfl (fun n _ => (charFn_mul_char χ₁ χ₂ hχ₁2 hχ₂2 n).symm)
    rw [heq]
    have h := hG₃ t
    push_cast at h
    exact h
  have hKb : ∀ t : ℕ, |∑ n ∈ Icc 1 t, (toArith (charFn q₂ χ₂)
      * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) n|
      ≤ (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) * (Real.sqrt t + 1) :=
    fun t => bounded_conv_sqrt_bound (charFn q₂ χ₂)
      (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m) ((q₂:ℝ)) ((q₁:ℝ) * (q₂:ℝ))
      h2b h12b hG₂ hK2 t
  obtain ⟨Lk, hLk⟩ := sqrt_mean_exists
    (fun d => (toArith (charFn q₂ χ₂)
      * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) d)
    (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) hKb
  have hE := quad_E_package_explicit (charFn q₁ χ₁) (charFn q₂ χ₂)
    ((q₁:ℝ)) (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) L₁ Lk h1b h2b hL₁
    (by positivity) hH hKb hLk
  refine ⟨L₁, Lk, 30 * (1 + (q₁:ℝ)) * (1 + (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ))) + 36
    + 3 * |L₁ * Lk|, hL₁, hLk, by positivity, ?_, hE⟩
  -- the polynomial bound
  have ha1 : (1:ℝ) ≤ (q₁:ℝ) := by exact_mod_cast hq₁
  have hb1 : (1:ℝ) ≤ (q₂:ℝ) := by exact_mod_cast hq₂
  have hL1u : |L₁| ≤ 3 + Real.log q₁ :=
    rate_limit_upper_log (charFn q₁ χ₁) q₁ hq₁ L₁ h1b hL₁
  have hLku : |Lk| ≤ 7 * (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) + 1 :=
    sqrt_rate_limit_upper (charFn q₂ χ₂)
      (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)
      (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) Lk h2b h12b hLk
  have hlogq : Real.log q₁ ≤ (q₁:ℝ) := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < (q₁:ℝ) by linarith)
    linarith
  have hprod : |L₁ * Lk| ≤ (3 + (q₁:ℝ)) * (7 * (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) + 1) := by
    rw [abs_mul]
    apply mul_le_mul _ hLku (abs_nonneg _) (by linarith)
    calc |L₁| ≤ 3 + Real.log q₁ := hL1u
      _ ≤ 3 + (q₁:ℝ) := by linarith
  set a : ℝ := (q₁:ℝ) with hadef
  set b : ℝ := (q₂:ℝ) with hbdef
  have hab : (1:ℝ) ≤ a * b := by nlinarith
  nlinarith [hprod, ha1, hb1, hab, sq_nonneg (a - b), sq_nonneg (a + b),
    sq_nonneg ((a + 1) * (b + 1)), mul_pos (show (0:ℝ) < a + 1 by linarith)
      (show (0:ℝ) < b + 1 by linarith),
    mul_nonneg (mul_nonneg (show (0:ℝ) ≤ a by linarith) (show (0:ℝ) ≤ b by linarith))
      (show (0:ℝ) ≤ a by linarith),
    mul_nonneg (mul_nonneg (show (0:ℝ) ≤ a by linarith) (show (0:ℝ) ≤ b by linarith))
      (show (0:ℝ) ≤ b by linarith),
    sq_nonneg (a * b - 1), sq_nonneg (a * b + 1)]

/-- **The bounded λ lower bound at characters** (Siegel brick S3a):
    `siegel_lambda_lower_for_chars` with `C ≤ 1000(1+q₁)²(1+q₂)²` carried along. -/
theorem siegel_lambda_lower_for_chars_bounded {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁2 : χ₁ ^ 2 = 1) (hχ₂2 : χ₂ ^ 2 = 1) (hχ₁1 : χ₁ ≠ 1) (hχ₂1 : χ₂ ≠ 1)
    (hχ₃1 : (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
        * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) ≠ 1)
    {β : ℝ} (hβ1 : 9/10 < β) (hβ2 : β < 1)
    (hzero : DirichletCharacter.LFunction χ₁ ((β:ℂ)) = 0) :
    ∃ L₁ Lk C : ℝ, 0 ≤ L₁ * Lk ∧ 0 ≤ C
      ∧ C ≤ 1000 * ((q₁:ℝ) + 1) ^ 2 * ((q₂:ℝ) + 1) ^ 2
      ∧ (∀ y : ℕ, |L₁ - ∑ d ∈ Icc 1 y, charFn q₁ χ₁ d / d| ≤ 2 * (q₁:ℝ) / (y + 1))
      ∧ (∀ y : ℕ, 1 ≤ y →
          |Lk - ∑ d ∈ Icc 1 y, (toArith (charFn q₂ χ₂)
              * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) d / d|
            ≤ 7 * (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) / Real.sqrt y)
      ∧ ∀ x : ℕ, 2 ≤ x → ((820 * (C + 1)) ^ (40:ℕ) : ℝ) ≤ (x:ℝ) →
          1 - β ≤ 26 * (L₁ * Lk) * ((x:ℝ)) ^ (1 - β) := by
  have hq₁ : 1 ≤ q₁ := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₁)
  have hq₂ : 1 ≤ q₂ := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₂)
  obtain ⟨L₁, Lk, C, hr1, hr2, hC0, hCB, hEsys⟩ :=
    quad_system_for_chars_bounded hq₁ hq₂ χ₁ χ₂ hχ₁2 hχ₂2 hχ₁1 hχ₂1 hχ₃1
  obtain ⟨ha0, ha1⟩ := quad_conv_nonneg (charFn q₁ χ₁) (charFn q₂ χ₂)
    (charFn_mul χ₁ hχ₁2) (charFn_mul χ₂ hχ₂2)
    (charFn_one χ₁) (charFn_one χ₂)
    (charFn_values χ₁ hχ₁2) (charFn_values χ₂ hχ₂2)
  have h1b := fun n => charFn_bound χ₁ hχ₁2 n
  have h2b := fun n => charFn_bound χ₂ hχ₂2 n
  -- the E-function and its properties
  have hA0 : ∀ n : ℕ, 0 ≤ ∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ))
      * toArith (charFn q₁ χ₁) * toArith (charFn q₂ χ₂)
      * toArith (fun k => charFn q₁ χ₁ k * charFn q₂ χ₂ k)) m :=
    fun n => Finset.sum_nonneg (fun m _ => ha0 m)
  have hlam : 0 ≤ L₁ * Lk := by
    apply lam_nonneg (fun n => ∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ))
        * toArith (charFn q₁ χ₁) * toArith (charFn q₂ χ₂)
        * toArith (fun k => charFn q₁ χ₁ k * charFn q₂ χ₂ k)) m)
      (L₁ * Lk) C hC0 hA0
    intro n hn
    exact hEsys n hn
  refine ⟨L₁, Lk, C, hlam, hC0, hCB, hr1, hr2, ?_⟩
  intro x hx hxC
  apply siegel_lambda_lower
    (fun n => (toArith (fun _ => (1:ℝ)) * toArith (charFn q₁ χ₁)
      * toArith (charFn q₂ χ₂)
      * toArith (fun k => charFn q₁ χ₁ k * charFn q₂ χ₂ k)) n)
    (L₁ * Lk)
    (fun n => (∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith (charFn q₁ χ₁)
      * toArith (charFn q₂ χ₂)
      * toArith (fun k => charFn q₁ χ₁ k * charFn q₂ χ₂ k)) m) - L₁ * Lk * n)
    C ha0 ha1 hlam
    (fun n => by ring)
    hC0
    (by
      show (∑ m ∈ Icc 1 0, (toArith (fun _ => (1:ℝ)) * toArith (charFn q₁ χ₁)
        * toArith (charFn q₂ χ₂)
        * toArith (fun k => charFn q₁ χ₁ k * charFn q₂ χ₂ k)) m) - L₁ * Lk * (0:ℕ) = 0
      rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, Nat.cast_zero, mul_zero,
        sub_zero])
    (fun n hn => hEsys n hn)
    (fun s hs => quad_LSeriesSummable (charFn q₁ χ₁) (charFn q₂ χ₂) h1b h2b hs)
    (fun w => riemannZeta w * DirichletCharacter.LFunction χ₁ w
      * DirichletCharacter.LFunction χ₂ w
      * DirichletCharacter.LFunction
          ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
            * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) w)
    (fun s _ hs1 => quad_P_differentiableAt χ₁ χ₂ hχ₁1 hχ₂1 hχ₃1 s hs1)
    (fun s hs => quad_P_identity χ₁ χ₂ hχ₁2 hχ₂2 hs)
    hβ1 hβ2
    (by
      show riemannZeta ((β:ℂ)) * DirichletCharacter.LFunction χ₁ ((β:ℂ))
        * DirichletCharacter.LFunction χ₂ ((β:ℂ))
        * DirichletCharacter.LFunction
            ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
              * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) ((β:ℂ)) = 0
      rw [hzero, mul_zero, zero_mul, zero_mul])
    x hx hxC

/-- **The λ lower bound with the concrete truncation** (Siegel brick S3b): with
    `M := 2(820(1000(1+q₁)²(1+q₂)²+1))^{40}`, a vanishing `L(β,χ₁)` at real
    `β ∈ (9/10,1)` forces `1−β ≤ 26·λ·M^{1−β}` — every quantity closed-form in
    the moduli. -/
theorem siegel_lambda_lower_concrete {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁2 : χ₁ ^ 2 = 1) (hχ₂2 : χ₂ ^ 2 = 1) (hχ₁1 : χ₁ ≠ 1) (hχ₂1 : χ₂ ≠ 1)
    (hχ₃1 : (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
        * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) ≠ 1)
    {β : ℝ} (hβ1 : 9/10 < β) (hβ2 : β < 1)
    (hzero : DirichletCharacter.LFunction χ₁ ((β:ℂ)) = 0) :
    ∃ L₁ Lk : ℝ, 0 ≤ L₁ * Lk
      ∧ (∀ y : ℕ, |L₁ - ∑ d ∈ Icc 1 y, charFn q₁ χ₁ d / d| ≤ 2 * (q₁:ℝ) / (y + 1))
      ∧ (∀ y : ℕ, 1 ≤ y →
          |Lk - ∑ d ∈ Icc 1 y, (toArith (charFn q₂ χ₂)
              * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) d / d|
            ≤ 7 * (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) / Real.sqrt y)
      ∧ 1 - β ≤ 26 * (L₁ * Lk)
          * ((2 * (820 * (1000 * ((q₁:ℝ) + 1) ^ 2 * ((q₂:ℝ) + 1) ^ 2 + 1))
              ^ ((40:ℝ)))) ^ (1 - β) := by
  obtain ⟨L₁, Lk, C, hlam, hC0, hCB, hr1, hr2, hmain⟩ :=
    siegel_lambda_lower_for_chars_bounded χ₁ χ₂ hχ₁2 hχ₂2 hχ₁1 hχ₂1 hχ₃1 hβ1 hβ2 hzero
  obtain ⟨CQ, hCQ⟩ : ∃ CQ : ℝ,
      CQ = 1000 * ((q₁:ℝ) + 1) ^ 2 * ((q₂:ℝ) + 1) ^ 2 := ⟨_, rfl⟩
  have hq1r : (1:ℝ) ≤ (q₁:ℝ) := by
    have : (1:ℕ) ≤ q₁ := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₁)
    exact_mod_cast this
  have hq2r : (1:ℝ) ≤ (q₂:ℝ) := by
    have : (1:ℕ) ≤ q₂ := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₂)
    exact_mod_cast this
  have hCQ4 : (4000:ℝ) ≤ CQ := by
    rw [hCQ]
    have h3 : (4:ℝ) ≤ ((q₁:ℝ) + 1) ^ 2 := by nlinarith [hq1r]
    have h4 : (4:ℝ) ≤ ((q₂:ℝ) + 1) ^ 2 := by nlinarith [hq2r]
    nlinarith [h3, h4]
  have hCB' : C ≤ CQ := by
    rw [hCQ]
    exact hCB
  have hbase1 : (1:ℝ) ≤ 820 * (CQ + 1) := by nlinarith [hCQ4]
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = (820 * (CQ + 1)) ^ ((40:ℝ)) := ⟨_, rfl⟩
  have hX4 : (4:ℝ) ≤ X := by
    rw [hXdef]
    calc (4:ℝ) ≤ 820 * (CQ + 1) := by nlinarith [hCQ4]
      _ = (820 * (CQ + 1)) ^ ((1:ℝ)) := (Real.rpow_one _).symm
      _ ≤ (820 * (CQ + 1)) ^ ((40:ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hbase1 (by norm_num)
  obtain ⟨x, hxdef⟩ : ∃ x : ℕ, x = Nat.ceil X + 2 := ⟨_, rfl⟩
  have hx2 : 2 ≤ x := by
    rw [hxdef]
    omega
  have hxge : X ≤ (x:ℝ) := by
    rw [hxdef]
    push_cast
    linarith [Nat.le_ceil X]
  have hxM : (x:ℝ) ≤ 2 * X := by
    rw [hxdef]
    push_cast
    have hceil := Nat.ceil_lt_add_one (show (0:ℝ) ≤ X by linarith)
    linarith [hX4]
  have hxC : ((820 * (C + 1)) ^ (40:ℕ) : ℝ) ≤ (x:ℝ) := by
    have h1 : ((820 * (C + 1)) ^ (40:ℕ) : ℝ) ≤ X := by
      rw [hXdef, show ((820 * (C + 1)) ^ (40:ℕ) : ℝ)
          = (820 * (C + 1)) ^ (((40:ℕ)):ℝ) from (Real.rpow_natCast _ 40).symm]
      rw [show (((40:ℕ)):ℝ) = (40:ℝ) from by norm_num]
      exact Real.rpow_le_rpow (by positivity) (by linarith [hCB']) (by norm_num)
    linarith
  have hstep := hmain x hx2 hxC
  have hβ0 : (0:ℝ) ≤ 1 - β := by linarith
  have hxpos : (0:ℝ) < (x:ℝ) := by
    have h1 : (0:ℕ) < x := by omega
    exact_mod_cast h1
  have hrpow : ((x:ℝ)) ^ (1 - β) ≤ ((2 * X : ℝ)) ^ (1 - β) :=
    Real.rpow_le_rpow hxpos.le hxM hβ0
  refine ⟨L₁, Lk, hlam, hr1, hr2, ?_⟩
  have hfinal : 1 - β ≤ 26 * (L₁ * Lk) * ((2 * X : ℝ)) ^ (1 - β) := by
    calc 1 - β ≤ 26 * (L₁ * Lk) * ((x:ℝ)) ^ (1 - β) := hstep
      _ ≤ 26 * (L₁ * Lk) * ((2 * X : ℝ)) ^ (1 - β) := by
          apply mul_le_mul_of_nonneg_left hrpow
          nlinarith [hlam]
  rw [hXdef, hCQ] at hfinal
  exact hfinal

/-- **The `L(1,χ₂)` lower bound at an exceptional zero** (Siegel brick S3c-a):
    a zero `β` of `L(·,χ₁)` in `(9/10,1)` forces, for every companion `χ₂`,
    `|ℓ₂| ≥ (1−β) / (26·M^{1−β}·(3+log q₁)(3+log q₁q₂))` where `ℓ₂` is the real
    value of `L(1,χ₂)` with its Abel rate — the quantity the zero-gap bridge eats. -/
theorem L_one_chi2_lower {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁2 : χ₁ ^ 2 = 1) (hχ₂2 : χ₂ ^ 2 = 1) (hχ₁1 : χ₁ ≠ 1) (hχ₂1 : χ₂ ≠ 1)
    (hχ₃1 : (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
        * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) ≠ 1)
    {β : ℝ} (hβ1 : 9/10 < β) (hβ2 : β < 1)
    (hzero : DirichletCharacter.LFunction χ₁ ((β:ℂ)) = 0) :
    ∃ ℓ₂ : ℝ,
      (∀ y : ℕ, |ℓ₂ - ∑ d ∈ Icc 1 y, charFn q₂ χ₂ d / d| ≤ 2 * (q₂:ℝ) / (y + 1))
      ∧ DirichletCharacter.LFunction χ₂ 1 = ((ℓ₂ : ℝ) : ℂ)
      ∧ (1 - β) / (26 * ((2 * (820 * (1000 * ((q₁:ℝ) + 1) ^ 2 * ((q₂:ℝ) + 1) ^ 2 + 1))
              ^ ((40:ℝ)))) ^ (1 - β)
            * (3 + Real.log q₁) * (3 + Real.log (q₁ * q₂ : ℕ)))
          ≤ |ℓ₂| := by
  have hq₁ : 1 ≤ q₁ := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₁)
  have hq₂ : 1 ≤ q₂ := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₂)
  have hq₁₂ : 1 ≤ q₁ * q₂ :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  haveI : NeZero (q₁ * q₂) := ⟨by omega⟩
  -- the engine
  obtain ⟨L₁, Lk, hlam, hr1, hr2, hmain⟩ :=
    siegel_lambda_lower_concrete χ₁ χ₂ hχ₁2 hχ₂2 hχ₁1 hχ₂1 hχ₃1 hβ1 hβ2 hzero
  -- fold the polynomial base and the tower into opaque atoms BEFORE any tactic
  obtain ⟨P, hP⟩ : ∃ P : ℝ,
      P = 1000 * ((q₁:ℝ) + 1) ^ 2 * ((q₂:ℝ) + 1) ^ 2 + 1 := ⟨_, rfl⟩
  rw [← hP] at hmain ⊢
  obtain ⟨Mv, hMv⟩ : ∃ Mv : ℝ,
      Mv = ((2 * (820 * P) ^ ((40:ℝ)))) ^ (1 - β) := ⟨_, rfl⟩
  rw [← hMv] at hmain ⊢
  have hP0 : (0:ℝ) < P := by
    rw [hP]
    positivity
  have hMv0 : (0:ℝ) < Mv := by
    rw [hMv]
    have h2 : (0:ℝ) < (820 * P) ^ ((40:ℝ)) :=
      Real.rpow_pos_of_pos (by linarith) _
    exact Real.rpow_pos_of_pos (by linarith) _
  -- the χ₂ and χ₃ values with their rates
  obtain ⟨ℓ₂, hrℓ₂⟩ := log_mean_exists (charFn q₂ χ₂) ((q₂:ℝ))
    (charFn_partial_sum_bound hq₂ χ₂ hχ₂2 hχ₂1)
  have hχ₃2 : ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
      * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) ^ 2 = 1 := by
    rw [mul_pow, ← map_pow, ← map_pow, hχ₁2, hχ₂2, map_one, map_one, mul_one]
  obtain ⟨L₃, hrL₃⟩ := log_mean_exists
    (charFn (q₁ * q₂) ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
      * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂))) (((q₁ * q₂ : ℕ)):ℝ)
    (charFn_partial_sum_bound hq₁₂ _ hχ₃2 hχ₃1)
  -- identifications at s = 1
  have hI2 : DirichletCharacter.LFunction χ₂ 1 = ((ℓ₂ : ℝ) : ℂ) :=
    L1_eq_LFunction_one hq₂ χ₂ hχ₂2 hχ₂1 ℓ₂ hrℓ₂
  have hI3 : DirichletCharacter.LFunction
      ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
        * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) 1
      = ((L₃ : ℝ) : ℂ) :=
    L1_eq_LFunction_one hq₁₂ _ hχ₃2 hχ₃1 L₃ hrL₃
  have hIk : DirichletCharacter.LFunction χ₂ 1
      * DirichletCharacter.LFunction
          ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
            * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) 1
      = ((Lk : ℝ) : ℂ) :=
    Lk_eq_LFunction_pair_one hq₁ hq₂ χ₁ χ₂ hχ₁2 hχ₂2 hχ₁1 hχ₂1 hχ₃1 Lk hr2
  have hLkprod : Lk = ℓ₂ * L₃ := by
    have h1 : ((Lk : ℝ) : ℂ) = ((ℓ₂ * L₃ : ℝ) : ℂ) := by
      rw [← hIk, hI2, hI3]
      push_cast
      ring
    exact_mod_cast h1
  have hL₁u : |L₁| ≤ 3 + Real.log q₁ :=
    rate_limit_upper_log (charFn q₁ χ₁) q₁ hq₁ L₁ (fun n => charFn_bound χ₁ hχ₁2 n) hr1
  have hL₃u : |L₃| ≤ 3 + Real.log ((q₁ * q₂ : ℕ)) :=
    rate_limit_upper_log _ (q₁ * q₂) hq₁₂ L₃ (fun n => charFn_bound _ hχ₃2 n) hrL₃
  have hβ0 : (0:ℝ) < 1 - β := by linarith
  have hq₁r : (1:ℝ) ≤ (q₁:ℝ) := by exact_mod_cast hq₁
  have hq₁₂r : (1:ℝ) ≤ ((q₁ * q₂ : ℕ):ℝ) := by exact_mod_cast hq₁₂
  have hlog₁ : (0:ℝ) ≤ Real.log q₁ := Real.log_nonneg hq₁r
  have hlog₃ : (0:ℝ) ≤ Real.log ((q₁ * q₂ : ℕ)) := Real.log_nonneg hq₁₂r
  have hden₁ : (0:ℝ) < 3 + Real.log q₁ := by linarith
  have hden₃ : (0:ℝ) < 3 + Real.log ((q₁ * q₂ : ℕ)) := by linarith
  have hlampos : (0:ℝ) < L₁ * Lk := by
    by_contra hcon
    push_neg at hcon
    have h1 : 26 * (L₁ * Lk) * Mv ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg _ hMv0.le
      nlinarith [hcon]
    linarith [hmain, hβ0]
  refine ⟨ℓ₂, hrℓ₂, hI2, ?_⟩
  have hLk_abs : |Lk| = |ℓ₂| * |L₃| := by
    rw [hLkprod, abs_mul]
  have hlam_le2 : L₁ * Lk ≤ (3 + Real.log q₁) * (3 + Real.log ((q₁ * q₂ : ℕ))) * |ℓ₂| := by
    calc L₁ * Lk ≤ |L₁ * Lk| := le_abs_self _
      _ = |L₁| * |Lk| := abs_mul _ _
      _ ≤ (3 + Real.log q₁) * |Lk| := by
          apply mul_le_mul_of_nonneg_right hL₁u (abs_nonneg _)
      _ = (3 + Real.log q₁) * (|ℓ₂| * |L₃|) := by rw [hLk_abs]
      _ ≤ (3 + Real.log q₁) * (|ℓ₂| * (3 + Real.log ((q₁ * q₂ : ℕ)))) := by
          apply mul_le_mul_of_nonneg_left _ hden₁.le
          apply mul_le_mul_of_nonneg_left hL₃u (abs_nonneg _)
      _ = (3 + Real.log q₁) * (3 + Real.log ((q₁ * q₂ : ℕ))) * |ℓ₂| := by ring
  have hdenpos : (0:ℝ) < 26 * Mv * (3 + Real.log q₁) * (3 + Real.log ((q₁ * q₂ : ℕ))) := by
    have h1 : (0:ℝ) < 26 * Mv := by linarith
    exact mul_pos (mul_pos h1 hden₁) hden₃
  rw [div_le_iff₀ hdenpos]
  have h26Mv : (0:ℝ) ≤ 26 * Mv := by linarith
  calc 1 - β ≤ 26 * (L₁ * Lk) * Mv := hmain
    _ = L₁ * Lk * (26 * Mv) := by ring
    _ ≤ ((3 + Real.log q₁) * (3 + Real.log ((q₁ * q₂ : ℕ))) * |ℓ₂|) * (26 * Mv) := by
        apply mul_le_mul_of_nonneg_right hlam_le2 h26Mv
    _ = |ℓ₂| * (26 * Mv * (3 + Real.log q₁) * (3 + Real.log ((q₁ * q₂ : ℕ)))) := by
        ring

/-- **The two-zero inequality** (Siegel brick S3c-b): an exceptional zero `β₁` of
    `χ₁` and any windowed zero `β₂` of a companion `χ₂` squeeze `|L(1,χ₂)|` from
    both sides — the inequality the dichotomy solves for `1−β₂`. -/
theorem chi2_zero_gap {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂] (hq₂3 : 3 ≤ q₂)
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁2 : χ₁ ^ 2 = 1) (hχ₂2 : χ₂ ^ 2 = 1) (hχ₁1 : χ₁ ≠ 1) (hχ₂1 : χ₂ ≠ 1)
    (hχ₃1 : (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
        * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) ≠ 1)
    {β₁ : ℝ} (hβ₁1 : 9/10 < β₁) (hβ₁2 : β₁ < 1)
    (hzero₁ : DirichletCharacter.LFunction χ₁ ((β₁:ℂ)) = 0)
    {β₂ : ℝ} (hβ₂2 : β₂ < 1) (hβ₂w : (1 - β₂) * Real.log q₂ ≤ 1/10)
    (hzero₂ : DirichletCharacter.LFunction χ₂ ((β₂:ℂ)) = 0) :
    (1 - β₁) / (26 * ((2 * (820 * (1000 * ((q₁:ℝ) + 1) ^ 2 * ((q₂:ℝ) + 1) ^ 2 + 1))
            ^ ((40:ℝ)))) ^ (1 - β₁)
          * (3 + Real.log q₁) * (3 + Real.log (q₁ * q₂ : ℕ)))
      ≤ 2 * (1 - β₂) * (1 + 3 * Real.log q₂) ^ 2 + 4 * ((q₂:ℝ)) ^ (-(17:ℝ)/10) := by
  obtain ⟨ℓ₂, hr, hI, hlow⟩ :=
    L_one_chi2_lower χ₁ χ₂ hχ₁2 hχ₂2 hχ₁1 hχ₂1 hχ₃1 hβ₁1 hβ₁2 hzero₁
  have hup := zero_gap_bridge hq₂3 χ₂ hχ₂2 hχ₂1 ℓ₂ hr hβ₂2 hβ₂w hzero₂
  linarith [hlow, hup]

/-- **The fixed-character gap** (Siegel brick S3c-c): a FIXED nontrivial `χ` has a
    positive zero-free interval below `1` — pure continuity from `L(1,χ) ≠ 0`. -/
theorem fixed_char_gap {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ β : ℝ, 1 - δ ≤ β → β < 1 →
      DirichletCharacter.LFunction χ ((β:ℂ)) ≠ 0 := by
  have hcont : ContinuousAt (DirichletCharacter.LFunction χ) 1 :=
    (DirichletCharacter.differentiable_LFunction hχ1).continuous.continuousAt
  have hne : DirichletCharacter.LFunction χ 1 ≠ 0 :=
    DirichletCharacter.LFunction_apply_one_ne_zero hχ1
  have hev : ∀ᶠ s in nhds (1:ℂ), DirichletCharacter.LFunction χ s ≠ 0 :=
    hcont.eventually_ne hne
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε0, hball⟩ := hev
  refine ⟨ε / 2, by linarith, ?_⟩
  intro β hβ1 hβ2
  apply hball
  rw [Complex.dist_eq, show ((β:ℂ)) - 1 = (((β - 1 : ℝ)):ℂ) from by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  linarith

/-- **Zero transfer when the product trivializes** (Siegel brick S3c-g): if
    `χ₁χ₂ = 1` at level `q₁q₂` then a real zero of `χ₂` in `(0,1)` is a zero of
    `χ₁` — the Euler factors of `changeLevel` never vanish on `(0,1)`. -/
theorem zero_transfer_of_product_trivial {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁2 : χ₁ ^ 2 = 1) (hχ₂2 : χ₂ ^ 2 = 1) (hχ₁1 : χ₁ ≠ 1) (hχ₂1 : χ₂ ≠ 1)
    (htriv : (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
        * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) = 1)
    {β : ℝ} (hβ0 : 0 < β) (hβ2 : β < 1)
    (hzero : DirichletCharacter.LFunction χ₂ ((β:ℂ)) = 0) :
    DirichletCharacter.LFunction χ₁ ((β:ℂ)) = 0 := by
  haveI : NeZero (q₁ * q₂) := ⟨Nat.mul_ne_zero (NeZero.ne q₁) (NeZero.ne q₂)⟩
  set cl₁ := DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁ with hcl₁
  set cl₂ := DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂ with hcl₂
  -- cl₂ = cl₁ by pure monoid algebra
  have h1 : cl₁ * cl₁ = 1 := by
    have h2 : cl₁ ^ 2 = 1 := by
      rw [hcl₁, ← map_pow, hχ₁2, map_one]
    rw [← pow_two]
    exact h2
  have hcl : cl₂ = cl₁ := by
    calc cl₂ = 1 * cl₂ := (one_mul _).symm
      _ = (cl₁ * cl₁) * cl₂ := by rw [h1]
      _ = cl₁ * (cl₁ * cl₂) := mul_assoc _ _ _
      _ = cl₁ * 1 := by rw [htriv]
      _ = cl₁ := mul_one _
  -- β is not 1
  have hβne : ((β:ℂ)) ≠ 1 := by
    intro h
    rw [Complex.ofReal_eq_one] at h
    linarith
  -- the Euler factors never vanish on (0,1)
  have hfac : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 →
      ∀ p ∈ (q₁ * q₂).primeFactors, (1 : ℂ) - χ ((p : ZMod q)) * ((p:ℂ)) ^ (-((β:ℝ):ℂ)) ≠ 0 := by
    intro q χ hχ2 p hp hzero'
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hp1r : (1:ℝ) < (p:ℝ) := by
      have h : (1:ℕ) < p := hp2
      exact_mod_cast h
    have hz : (1:ℂ) = χ ((p : ZMod q)) * ((p:ℂ)) ^ (-((β:ℝ):ℂ)) := sub_eq_zero.mp hzero'
    have hnorm : (1:ℝ) = ‖χ ((p : ZMod q))‖ * ‖((p:ℂ)) ^ (-((β:ℝ):ℂ))‖ := by
      calc (1:ℝ) = ‖(1:ℂ)‖ := norm_one.symm
        _ = ‖χ ((p : ZMod q)) * ((p:ℂ)) ^ (-((β:ℝ):ℂ))‖ := by rw [← hz]
        _ = ‖χ ((p : ZMod q))‖ * ‖((p:ℂ)) ^ (-((β:ℝ):ℂ))‖ := norm_mul _ _
    have hχn : ‖χ ((p : ZMod q))‖ ≤ 1 := by
      rcases real_char_repr χ hχ2 ((p : ZMod q)) with h | h | h <;> rw [h] <;> norm_num
    have hpn : ‖((p:ℂ)) ^ (-((β:ℝ):ℂ))‖ = ((p:ℝ)) ^ (-β) := by
      rw [cpow_real_cast p β, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    have hlt : ((p:ℝ)) ^ (-β) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hp1r (by linarith)
    have hle : ‖χ ((p : ZMod q))‖ * ‖((p:ℂ)) ^ (-((β:ℝ):ℂ))‖
        ≤ ‖((p:ℂ)) ^ (-((β:ℝ):ℂ))‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hχn
    rw [hpn] at hle hnorm
    linarith [hnorm.le, hnorm.ge, hle, hlt]
  -- transfer through the changeLevel factorizations
  have hL2big : DirichletCharacter.LFunction cl₂ ((β:ℂ))
      = DirichletCharacter.LFunction χ₂ ((β:ℂ))
        * ∏ p ∈ (q₁ * q₂).primeFactors,
            (1 - χ₂ ((p : ZMod q₂)) * ((p:ℂ)) ^ (-((β:ℝ):ℂ))) :=
    DirichletCharacter.LFunction_changeLevel (dvd_mul_left q₂ q₁) χ₂ (Or.inr hβne)
  have hL1big : DirichletCharacter.LFunction cl₁ ((β:ℂ))
      = DirichletCharacter.LFunction χ₁ ((β:ℂ))
        * ∏ p ∈ (q₁ * q₂).primeFactors,
            (1 - χ₁ ((p : ZMod q₁)) * ((p:ℂ)) ^ (-((β:ℝ):ℂ))) :=
    DirichletCharacter.LFunction_changeLevel (dvd_mul_right q₁ q₂) χ₁ (Or.inr hβne)
  have hz2 : DirichletCharacter.LFunction cl₂ ((β:ℂ)) = 0 := by
    rw [hL2big, hzero, zero_mul]
  rw [hcl, hL1big] at hz2
  rcases mul_eq_zero.mp hz2 with h | h
  · exact h
  · exfalso
    have hne : ∏ p ∈ (q₁ * q₂).primeFactors,
        ((1:ℂ) - χ₁ ((p : ZMod q₁)) * ((p:ℂ)) ^ (-((β:ℝ):ℂ))) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun p hp => hfac q₁ χ₁ hχ₁2 p hp)
    exact hne h

/-- **The dichotomy gap estimate** (Siegel brick S3c-e): with the exceptional zero
    in the `ε/320`-window, the whole denominator of `chi2_zero_gap` is at most
    `K(ε,q₁)·q₂^{ε/2}` — all `q₂`-growth tamed to an arbitrarily small power. -/
theorem dichotomy_gap_estimate (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1/100)
    (q₁ : ℕ) (hq₁ : 1 ≤ q₁) {β₁ : ℝ} (hβw : 1 - β₁ ≤ ε / 320) (hβpos : 0 ≤ 1 - β₁) :
    ∃ K : ℝ, 0 < K ∧ ∀ q₂ : ℕ, 1 ≤ q₂ →
      26 * ((2 * (820 * (1000 * ((q₁:ℝ) + 1) ^ 2 * ((q₂:ℝ) + 1) ^ 2 + 1))
          ^ ((40:ℝ)))) ^ (1 - β₁)
        * (3 + Real.log q₁) * (3 + Real.log ((q₁ * q₂ : ℕ)))
      ≤ K * ((q₂:ℝ)) ^ (ε / 2) := by
  have hq₁r : (1:ℝ) ≤ (q₁:ℝ) := by exact_mod_cast hq₁
  have hA1 : (2:ℝ) ≤ (q₁:ℝ) + 1 := by linarith
  have hlogq₁ : (0:ℝ) ≤ Real.log q₁ := Real.log_nonneg hq₁r
  refine ⟨(260 / ε) * Real.exp (112802 + 80 * Real.log ((q₁:ℝ) + 1))
    * (3 + Real.log q₁) ^ 2, by positivity, ?_⟩
  intro q₂ hq₂
  have hq₂r : (1:ℝ) ≤ (q₂:ℝ) := by exact_mod_cast hq₂
  have hq₂0 : (0:ℝ) < (q₂:ℝ) := by linarith
  have hB1 : (2:ℝ) ≤ (q₂:ℝ) + 1 := by linarith
  have hlogq₂ : (0:ℝ) ≤ Real.log q₂ := Real.log_nonneg hq₂r
  -- name the pieces
  obtain ⟨P, hP⟩ : ∃ P : ℝ,
      P = 1000 * ((q₁:ℝ) + 1) ^ 2 * ((q₂:ℝ) + 1) ^ 2 + 1 := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ((2 * (820 * P) ^ ((40:ℝ)))) ^ (1 - β₁) := ⟨_, rfl⟩
  rw [← hP, ← hT]
  have hP1 : (1:ℝ) ≤ P := by
    rw [hP]
    have h0 : (0:ℝ) ≤ 1000 * ((q₁:ℝ) + 1) ^ 2 * ((q₂:ℝ) + 1) ^ 2 := by positivity
    linarith
  have hP0 : (0:ℝ) < P := by linarith
  have h820P : (0:ℝ) < 820 * P := by linarith
  have hinner0 : (0:ℝ) < (820 * P) ^ ((40:ℝ)) := Real.rpow_pos_of_pos h820P _
  have hbase0 : (0:ℝ) < 2 * (820 * P) ^ ((40:ℝ)) := by linarith
  -- log P ≤ log 2000 + 2 log A + 2 log B ≤ 2000 + 2 log A + 2 log B
  have hlogP : Real.log P ≤ 2000 + 2 * Real.log ((q₁:ℝ) + 1) + 2 * Real.log ((q₂:ℝ) + 1) := by
    have h1 : P ≤ 2000 * ((q₁:ℝ) + 1) ^ 2 * ((q₂:ℝ) + 1) ^ 2 := by
      rw [hP]
      have hA2 : (4:ℝ) ≤ ((q₁:ℝ) + 1) ^ 2 := by nlinarith [hA1]
      have hB2 : (4:ℝ) ≤ ((q₂:ℝ) + 1) ^ 2 := by nlinarith [hB1]
      nlinarith [hA2, hB2]
    have h2 : Real.log P ≤ Real.log (2000 * ((q₁:ℝ) + 1) ^ 2 * ((q₂:ℝ) + 1) ^ 2) :=
      Real.log_le_log hP0 h1
    have h3 : Real.log (2000 * ((q₁:ℝ) + 1) ^ 2 * ((q₂:ℝ) + 1) ^ 2)
        = Real.log 2000 + 2 * Real.log ((q₁:ℝ) + 1) + 2 * Real.log ((q₂:ℝ) + 1) := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow]
      push_cast
      ring
    have h4 : Real.log 2000 ≤ 2000 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2000 by norm_num)
      linarith
    linarith
  -- log T ≤ (1−β₁)(112802 + 80 log A) + (1−β₁)·80·log B
  have hlogT : Real.log T ≤ (112802 + 80 * Real.log ((q₁:ℝ) + 1))
      + (ε / 4) * Real.log ((q₂:ℝ) + 1) := by
    rw [hT, Real.log_rpow hbase0]
    have h1 : Real.log (2 * (820 * P) ^ ((40:ℝ)))
        = Real.log 2 + 40 * Real.log (820 * P) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hinner0), Real.log_rpow h820P]
    have h2 : Real.log (820 * P) = Real.log 820 + Real.log P := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hP0)]
    have h3 : Real.log 820 ≤ 820 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 820 by norm_num)
      linarith
    have h4 : Real.log 2 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
      linarith
    have hlogB0 : (0:ℝ) ≤ Real.log ((q₂:ℝ) + 1) := Real.log_nonneg (by linarith)
    have hlogA0 : (0:ℝ) ≤ Real.log ((q₁:ℝ) + 1) := Real.log_nonneg (by linarith)
    have h5 : Real.log (2 * (820 * P) ^ ((40:ℝ)))
        ≤ 112802 + 80 * Real.log ((q₁:ℝ) + 1) + 80 * Real.log ((q₂:ℝ) + 1) := by
      rw [h1, h2]
      linarith [hlogP]
    have h6 : (1 - β₁) * Real.log (2 * (820 * P) ^ ((40:ℝ)))
        ≤ 1 * (112802 + 80 * Real.log ((q₁:ℝ) + 1))
          + (1 - β₁) * (80 * Real.log ((q₂:ℝ) + 1)) := by
      have h7 : (1 - β₁) * Real.log (2 * (820 * P) ^ ((40:ℝ)))
          ≤ (1 - β₁) * (112802 + 80 * Real.log ((q₁:ℝ) + 1)
            + 80 * Real.log ((q₂:ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left h5 hβpos
      have h8 : (1 - β₁) ≤ 1 := by
        have : (0:ℝ) < ε / 320 := by linarith
        linarith [hβw, hε1]
      nlinarith [h7, h8, hlogA0, hlogB0, hβpos]
    have h9 : (1 - β₁) * (80 * Real.log ((q₂:ℝ) + 1))
        ≤ (ε / 4) * Real.log ((q₂:ℝ) + 1) := by
      have : (1 - β₁) * 80 ≤ ε / 4 := by linarith [hβw]
      nlinarith [hlogB0, this, hβpos]
    linarith [h6, h9]
  -- T ≤ K₁ · (q₂+1)^{ε/4}
  have hT0 : (0:ℝ) < T := by
    rw [hT]
    exact Real.rpow_pos_of_pos hbase0 _
  have hTle : T ≤ Real.exp (112802 + 80 * Real.log ((q₁:ℝ) + 1))
      * ((q₂:ℝ) + 1) ^ (ε / 4) := by
    have h1 : T = Real.exp (Real.log T) := (Real.exp_log hT0).symm
    rw [h1]
    have h2 : ((q₂:ℝ) + 1) ^ (ε / 4)
        = Real.exp ((ε / 4) * Real.log ((q₂:ℝ) + 1)) := by
      rw [Real.rpow_def_of_pos (by linarith), mul_comm]
    rw [h2, ← Real.exp_add]
    exact Real.exp_le_exp.mpr hlogT
  -- (q₂+1)^{ε/4} ≤ 2·q₂^{ε/4}
  have hBpow : ((q₂:ℝ) + 1) ^ (ε / 4) ≤ 2 * ((q₂:ℝ)) ^ (ε / 4) := by
    calc ((q₂:ℝ) + 1) ^ (ε / 4) ≤ (2 * (q₂:ℝ)) ^ (ε / 4) := by
          apply Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
      _ = (2:ℝ) ^ (ε / 4) * ((q₂:ℝ)) ^ (ε / 4) :=
          Real.mul_rpow (by norm_num) hq₂0.le
      _ ≤ 2 * ((q₂:ℝ)) ^ (ε / 4) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hq₂0.le _)
          calc (2:ℝ) ^ (ε / 4) ≤ (2:ℝ) ^ ((1:ℝ)) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 2 := Real.rpow_one 2
  -- 3 + log(q₁q₂) ≤ (3+log q₁)·(5/ε)·q₂^{ε/4}
  have hlogsplit : Real.log ((q₁ * q₂ : ℕ)) = Real.log q₁ + Real.log q₂ := by
    push_cast
    rw [Real.log_mul (by linarith) (by linarith)]
  have hlogq₂' : Real.log q₂ ≤ (4 / ε) * ((q₂:ℝ)) ^ (ε / 4) := by
    have h1 : Real.log q₂ ≤ ((q₂:ℝ)) ^ (ε / 4) / (ε / 4) :=
      Real.log_le_rpow_div hq₂0.le (by linarith)
    have h2 : ((q₂:ℝ)) ^ (ε / 4) / (ε / 4) = (4 / ε) * ((q₂:ℝ)) ^ (ε / 4) := by
      field_simp
    linarith [h1, h2.le, h2.ge]
  have hpow1 : (1:ℝ) ≤ ((q₂:ℝ)) ^ (ε / 4) := Real.one_le_rpow hq₂r (by linarith)
  have hfac : 3 + Real.log ((q₁ * q₂ : ℕ))
      ≤ (3 + Real.log q₁) * ((5 / ε) * ((q₂:ℝ)) ^ (ε / 4)) := by
    rw [hlogsplit, ← add_assoc]
    have h1 : 3 + Real.log q₁ + Real.log q₂
        ≤ (3 + Real.log q₁) * (1 + (4 / ε) * ((q₂:ℝ)) ^ (ε / 4)) := by
      have h2 : (1:ℝ) ≤ 3 + Real.log q₁ := by linarith
      nlinarith [hlogq₂', h2, hlogq₂]
    have h3 : (1:ℝ) + (4 / ε) * ((q₂:ℝ)) ^ (ε / 4) ≤ (5 / ε) * ((q₂:ℝ)) ^ (ε / 4) := by
      have h4 : (1:ℝ) ≤ (1 / ε) * ((q₂:ℝ)) ^ (ε / 4) := by
        have h5 : (1:ℝ) ≤ 1 / ε := by
          rw [le_div_iff₀ hε0]
          linarith
        nlinarith [hpow1, h5]
      have h6 : (4 / ε) * ((q₂:ℝ)) ^ (ε / 4) + (1 / ε) * ((q₂:ℝ)) ^ (ε / 4)
          = (5 / ε) * ((q₂:ℝ)) ^ (ε / 4) := by ring
      linarith
    have h7 : (0:ℝ) ≤ 3 + Real.log q₁ := by linarith
    calc 3 + Real.log q₁ + Real.log q₂
        ≤ (3 + Real.log q₁) * (1 + (4 / ε) * ((q₂:ℝ)) ^ (ε / 4)) := h1
      _ ≤ (3 + Real.log q₁) * ((5 / ε) * ((q₂:ℝ)) ^ (ε / 4)) :=
          mul_le_mul_of_nonneg_left h3 h7
  -- assemble
  have hpowmul : ((q₂:ℝ)) ^ (ε / 4) * ((q₂:ℝ)) ^ (ε / 4) = ((q₂:ℝ)) ^ (ε / 2) := by
    rw [← Real.rpow_add hq₂0]
    congr 1
    ring
  have hden₁ : (0:ℝ) < 3 + Real.log q₁ := by linarith
  have hK₁0 : (0:ℝ) < Real.exp (112802 + 80 * Real.log ((q₁:ℝ) + 1)) := Real.exp_pos _
  calc 26 * T * (3 + Real.log q₁) * (3 + Real.log ((q₁ * q₂ : ℕ)))
      ≤ 26 * (Real.exp (112802 + 80 * Real.log ((q₁:ℝ) + 1))
          * (2 * ((q₂:ℝ)) ^ (ε / 4))) * (3 + Real.log q₁)
        * ((3 + Real.log q₁) * ((5 / ε) * ((q₂:ℝ)) ^ (ε / 4))) := by
        have hT2 : T ≤ Real.exp (112802 + 80 * Real.log ((q₁:ℝ) + 1))
            * (2 * ((q₂:ℝ)) ^ (ε / 4)) := by
          calc T ≤ Real.exp (112802 + 80 * Real.log ((q₁:ℝ) + 1))
              * ((q₂:ℝ) + 1) ^ (ε / 4) := hTle
            _ ≤ Real.exp (112802 + 80 * Real.log ((q₁:ℝ) + 1))
                * (2 * ((q₂:ℝ)) ^ (ε / 4)) := by
                apply mul_le_mul_of_nonneg_left hBpow hK₁0.le
        have h30 : (0:ℝ) ≤ 3 + Real.log ((q₁ * q₂ : ℕ)) := by
          have := Real.log_nonneg (show (1:ℝ) ≤ ((q₁ * q₂ : ℕ):ℝ) from by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))
          linarith
        have hfac0 : (0:ℝ) ≤ (3 + Real.log q₁) * ((5 / ε) * ((q₂:ℝ)) ^ (ε / 4)) := by
          positivity
        calc 26 * T * (3 + Real.log q₁) * (3 + Real.log ((q₁ * q₂ : ℕ)))
            ≤ 26 * T * (3 + Real.log q₁)
              * ((3 + Real.log q₁) * ((5 / ε) * ((q₂:ℝ)) ^ (ε / 4))) := by
              apply mul_le_mul_of_nonneg_left hfac
              positivity
          _ ≤ 26 * (Real.exp (112802 + 80 * Real.log ((q₁:ℝ) + 1))
                * (2 * ((q₂:ℝ)) ^ (ε / 4))) * (3 + Real.log q₁)
              * ((3 + Real.log q₁) * ((5 / ε) * ((q₂:ℝ)) ^ (ε / 4))) := by
              apply mul_le_mul_of_nonneg_right _ hfac0
              apply mul_le_mul_of_nonneg_right _ hden₁.le
              apply mul_le_mul_of_nonneg_left hT2 (by norm_num)
    _ = ((260 / ε) * Real.exp (112802 + 80 * Real.log ((q₁:ℝ) + 1))
          * (3 + Real.log q₁) ^ 2) * (((q₂:ℝ)) ^ (ε / 4) * ((q₂:ℝ)) ^ (ε / 4)) := by
        ring
    _ = ((260 / ε) * Real.exp (112802 + 80 * Real.log ((q₁:ℝ) + 1))
          * (3 + Real.log q₁) ^ 2) * ((q₂:ℝ)) ^ (ε / 2) := by
        rw [hpowmul]

/-- **The small-modulus gap** (Siegel brick S3c-f): below any threshold `Q₀` there
    are finitely many characters, so a single `c > 0` clears a zero-free interval
    below `1` for all of them at once. -/
theorem small_q_gap (Q₀ : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q → q < Q₀ →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ β : ℝ, 1 - c ≤ β → β < 1 →
        DirichletCharacter.LFunction χ ((β:ℂ)) ≠ 0 := by
  induction Q₀ with
  | zero =>
    exact ⟨1, one_pos, fun q _ _ hq0 => absurd hq0 (by omega)⟩
  | succ Q ih =>
    obtain ⟨c', hc'0, hc'⟩ := ih
    rcases Nat.lt_or_ge Q 3 with hQ3 | hQ3
    · -- the new modulus Q is below 3: nothing new to cover
      refine ⟨c', hc'0, ?_⟩
      intro q _ hq3 hqlt χ hχ1 β hβ1 hβ2
      have hqQ : q < Q := by omega
      exact hc' q hq3 hqQ χ hχ1 β hβ1 hβ2
    · -- take the min over the finitely many characters mod Q
      haveI : NeZero Q := ⟨by omega⟩
      haveI : Finite (DirichletCharacter ℂ Q) :=
        inferInstanceAs (Finite (MulChar (ZMod Q) ℂ))
      haveI := Fintype.ofFinite (DirichletCharacter ℂ Q)
      have hF : ∀ χ : DirichletCharacter ℂ Q, ∃ δ : ℝ, 0 < δ ∧
          (χ ≠ 1 → ∀ β : ℝ, 1 - δ ≤ β → β < 1 →
            DirichletCharacter.LFunction χ ((β:ℂ)) ≠ 0) := by
        intro χ
        by_cases h : χ = 1
        · exact ⟨1, one_pos, fun h1 => absurd h h1⟩
        · obtain ⟨δ, hδ0, hδ⟩ := fixed_char_gap χ h
          exact ⟨δ, hδ0, fun _ => hδ⟩
      choose δf hδf0 hδf using hF
      have hne : (Finset.univ : Finset (DirichletCharacter ℂ Q)).Nonempty :=
        ⟨1, Finset.mem_univ 1⟩
      refine ⟨min c' (Finset.univ.inf' hne δf), ?_, ?_⟩
      · apply lt_min hc'0
        rw [Finset.lt_inf'_iff]
        exact fun χ _ => hδf0 χ
      · intro q _ hq3 hqlt χ hχ1 β hβ1 hβ2
        rcases Nat.lt_or_ge q Q with h | h
        · apply hc' q hq3 h χ hχ1 β _ hβ2
          have := min_le_left c' (Finset.univ.inf' hne δf)
          linarith
        · have hqeq : q = Q := by omega
          subst hqeq
          apply hδf χ hχ1 β _ hβ2
          have h1 := Finset.inf'_le δf (Finset.mem_univ χ)
          have h2 := min_le_right c' (Finset.univ.inf' hne δf)
          linarith

/-- **SIEGEL'S THEOREM (auxiliary form, `ε ≤ 1/100`)** (Siegel brick S3c-h). -/
theorem siegel_zero_free_aux (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1/100) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ ^ 2 = 1 → χ ≠ 1 →
      ∀ β : ℝ, β < 1 → DirichletCharacter.LFunction χ ((β:ℂ)) = 0 →
      β ≤ 1 - c * ((q:ℝ)) ^ (-ε) := by
  by_cases hex : ∃ (q₁ : ℕ) (_ : NeZero q₁) (χ₁ : DirichletCharacter ℂ q₁),
      3 ≤ q₁ ∧ χ₁ ^ 2 = 1 ∧ χ₁ ≠ 1 ∧ ∃ β₁ : ℝ, 9/10 < β₁ ∧ β₁ < 1 ∧
        1 - β₁ ≤ ε / 320 ∧ DirichletCharacter.LFunction χ₁ ((β₁:ℂ)) = 0
  case neg =>
    -- no exceptional zero: the window itself is zero-free
    refine ⟨min (1/10) (ε / 320), by positivity, ?_⟩
    intro q _ hq3 χ hχ2 hχ1 β hβ2 hzero
    by_contra hcon
    push_neg at hcon
    have hq1r : (1:ℝ) ≤ (q:ℝ) := by
      have : (1:ℕ) ≤ q := by omega
      exact_mod_cast this
    have hqe : ((q:ℝ)) ^ (-ε) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hq1r (by linarith)
    have hc1 : min (1/10) (ε / 320) * ((q:ℝ)) ^ (-ε) ≤ min (1/10) (ε / 320) := by
      have h0 : (0:ℝ) ≤ min (1/10) (ε / 320) := by positivity
      nlinarith [hqe, h0]
    apply hex
    refine ⟨q, ⟨by omega⟩, χ, hq3, hχ2, hχ1, β, ?_, hβ2, ?_, hzero⟩
    · have := min_le_left (1/10 : ℝ) (ε / 320)
      linarith
    · have := min_le_right (1/10 : ℝ) (ε / 320)
      linarith
  case pos =>
    obtain ⟨q₁, i₁, χ₁, hq₁3, hχ₁2, hχ₁1, β₁, hβ₁910, hβ₁lt, hβ₁win, hzero₁⟩ := hex
    haveI := i₁
    have hβ₁pos : (0:ℝ) < 1 - β₁ := by linarith
    obtain ⟨K, hK0, hKest⟩ :=
      dichotomy_gap_estimate ε hε0 hε1 q₁ (by omega) hβ₁win (by linarith)
    obtain ⟨δ₁, hδ₁0, hδ₁⟩ := fixed_char_gap χ₁ hχ₁1
    have hp0 : (0:ℝ) < (17:ℝ)/10 - ε/2 := by linarith
    obtain ⟨Q₀, hQ₀⟩ : ∃ Q₀ : ℕ,
        Q₀ = Nat.ceil ((8 * K / (1 - β₁)) ^ ((((17:ℝ)/10 - ε/2))⁻¹)) + 1 := ⟨_, rfl⟩
    obtain ⟨cs, hcs0, hcs⟩ := small_q_gap Q₀
    obtain ⟨cc, hcc⟩ : ∃ cc : ℝ, cc = (1 - β₁) * ε ^ 2 / (676 * K) := ⟨_, rfl⟩
    have hcc0 : (0:ℝ) < cc := by
      rw [hcc]
      positivity
    refine ⟨min (min (1/10) (ε / 10)) (min cs (min cc δ₁)), by positivity, ?_⟩
    intro q _ hq3 χ hχ2 hχ1 β hβ2 hzero
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = min (min (1/10) (ε / 10)) (min cs (min cc δ₁)) := ⟨_, rfl⟩
    rw [← hc]
    have hc0 : (0:ℝ) < c := by
      rw [hc]
      positivity
    have hq1r : (1:ℝ) ≤ (q:ℝ) := by
      have : (1:ℕ) ≤ q := by omega
      exact_mod_cast this
    have hq3r : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq3
    have hqe0 : (0:ℝ) < ((q:ℝ)) ^ (-ε) := Real.rpow_pos_of_pos (by linarith) _
    have hqe1 : ((q:ℝ)) ^ (-ε) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hq1r (by linarith)
    have hlogq : (1:ℝ) < Real.log q := by
      have he : Real.exp 1 < 3 := by
        have := Real.exp_one_lt_d9
        linarith
      calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) he
        _ ≤ Real.log q := Real.log_le_log (by norm_num) hq3r
    -- generic closer: from 1 − β ≥ c_br and c ≤ c_br
    have hclose_const : ∀ cbr : ℝ, c ≤ cbr → 1 - β ≥ cbr → β ≤ 1 - c * ((q:ℝ)) ^ (-ε) := by
      intro cbr hle hge
      have h1 : c * ((q:ℝ)) ^ (-ε) ≤ cbr := by
        calc c * ((q:ℝ)) ^ (-ε) ≤ c * 1 := by
              apply mul_le_mul_of_nonneg_left hqe1 hc0.le
          _ = c := mul_one c
          _ ≤ cbr := hle
      linarith
    have hclose_rpow : ∀ cbr : ℝ, 0 ≤ cbr → c ≤ cbr →
        1 - β ≥ cbr * ((q:ℝ)) ^ (-ε) → β ≤ 1 - c * ((q:ℝ)) ^ (-ε) := by
      intro cbr h0 hle hge
      have h1 : c * ((q:ℝ)) ^ (-ε) ≤ cbr * ((q:ℝ)) ^ (-ε) :=
        mul_le_mul_of_nonneg_right hle hqe0.le
      linarith
    -- branch: β ≤ 9/10
    by_cases hb : β ≤ 9/10
    · apply hclose_const (1/10)
      · rw [hc]
        exact le_trans (min_le_left _ _) (min_le_left _ _)
      · linarith
    push_neg at hb
    have hβ0 : (0:ℝ) < β := by linarith
    -- branch: outside the window
    by_cases hwin : (1 - β) * Real.log q ≤ 1/10
    swap
    · push_neg at hwin
      apply hclose_rpow (ε / 10) (by linarith) _ _
      · rw [hc]
        exact le_trans (min_le_left _ _) (min_le_right _ _)
      · have h1 : 1 / (10 * Real.log q) < 1 - β := by
          rw [div_lt_iff₀ (by linarith)]
          linarith [hwin]
        have h2 : Real.log q ≤ ((q:ℝ)) ^ ε / ε :=
          Real.log_le_rpow_div (by linarith) hε0
        have h3 : (ε / 10) * ((q:ℝ)) ^ (-ε) ≤ 1 / (10 * Real.log q) := by
          have h4 : ((q:ℝ)) ^ (-ε) * ((q:ℝ)) ^ ε = 1 := by
            rw [← Real.rpow_add (by linarith : (0:ℝ) < (q:ℝ))]
            simp
          have h5 : Real.log q * ε ≤ ((q:ℝ)) ^ ε := by
            rw [← le_div_iff₀ hε0]
            exact h2
          rw [le_div_iff₀ (by linarith : (0:ℝ) < 10 * Real.log q)]
          have h6 : ε / 10 * ((q:ℝ)) ^ (-ε) * (10 * Real.log q)
              = (Real.log q * ε) * ((q:ℝ)) ^ (-ε) := by ring
          rw [h6]
          calc (Real.log q * ε) * ((q:ℝ)) ^ (-ε)
              ≤ ((q:ℝ)) ^ ε * ((q:ℝ)) ^ (-ε) :=
                mul_le_mul_of_nonneg_right h5 hqe0.le
            _ = 1 := by rw [mul_comm]; exact h4
        linarith
    -- in the window: split on the product character
    by_cases hprod : (DirichletCharacter.changeLevel (dvd_mul_right q₁ q) χ₁)
        * (DirichletCharacter.changeLevel (dvd_mul_left q q₁) χ) = 1
    · -- product trivial: transfer the zero to χ₁ and use its fixed gap
      have hz1 := zero_transfer_of_product_trivial χ₁ χ hχ₁2 hχ2 hχ₁1 hχ1 hprod
        hβ0 hβ2 hzero
      apply hclose_const δ₁
      · rw [hc]
        exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
      · by_contra hcon2
        push_neg at hcon2
        exact hδ₁ β (by linarith) hβ2 hz1
    · by_cases hbig : Q₀ ≤ q
      swap
      · -- small q: the finite-min constant
        push_neg at hbig
        apply hclose_const cs
        · rw [hc]
          exact le_trans (min_le_right _ _) (min_le_left _ _)
        · by_contra hcon2
          push_neg at hcon2
          exact hcs q hq3 hbig χ hχ1 β (by linarith) hβ2 hzero
      · -- THE MAIN CHAIN
        have hgap := chi2_zero_gap (q₂ := q) hq3 χ₁ χ hχ₁2 hχ2 hχ₁1 hχ1 hprod
          hβ₁910 hβ₁lt hzero₁ hβ2 hwin hzero
        have hKq := hKest q (by omega)
        obtain ⟨BIG, hBIG⟩ : ∃ B : ℝ, B = 26 * ((2 * (820 * (1000 * ((q₁:ℝ) + 1) ^ 2
            * ((q:ℝ) + 1) ^ 2 + 1)) ^ ((40:ℝ)))) ^ (1 - β₁)
            * (3 + Real.log q₁) * (3 + Real.log (q₁ * q : ℕ)) := ⟨_, rfl⟩
        rw [← hBIG] at hgap hKq
        have hBIG0 : (0:ℝ) < BIG := by
          rw [hBIG]
          obtain ⟨P, hP⟩ : ∃ P : ℝ,
              P = 1000 * ((q₁:ℝ) + 1) ^ 2 * ((q:ℝ) + 1) ^ 2 + 1 := ⟨_, rfl⟩
          rw [← hP]
          have hP0 : (0:ℝ) < P := by
            rw [hP]
            positivity
          have h1 : (0:ℝ) < (820 * P) ^ ((40:ℝ)) :=
            Real.rpow_pos_of_pos (by linarith) _
          have h2 : (0:ℝ) < ((2 * (820 * P) ^ ((40:ℝ)))) ^ (1 - β₁) :=
            Real.rpow_pos_of_pos (by linarith) _
          have h3 : (0:ℝ) < 3 + Real.log q₁ := by
            have := Real.log_nonneg (show (1:ℝ) ≤ (q₁:ℝ) from by
              exact_mod_cast (show (1:ℕ) ≤ q₁ from by omega))
            linarith
          have h4 : (0:ℝ) < 3 + Real.log ((q₁ * q : ℕ)) := by
            have h5 : (1:ℕ) ≤ q₁ * q :=
              Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
            have := Real.log_nonneg (show (1:ℝ) ≤ ((q₁ * q : ℕ):ℝ) from by
              exact_mod_cast h5)
            linarith
          have h26 : (0:ℝ) < (26:ℝ) := by norm_num
          exact mul_pos (mul_pos (mul_pos h26 h2) h3) h4
        have hqpos : (0:ℝ) < (q:ℝ) := by linarith
        have hthresh : 4 * ((q:ℝ)) ^ (-(17:ℝ)/10)
            ≤ (1 - β₁) / (2 * K * ((q:ℝ)) ^ (ε/2)) := by
          have hR0 : (0:ℝ) < 8 * K / (1 - β₁) := by positivity
          have hq_ge : (8 * K / (1 - β₁)) ^ ((((17:ℝ)/10 - ε/2))⁻¹) ≤ (q:ℝ) := by
            have h1 : (Q₀:ℝ) ≤ (q:ℝ) := by exact_mod_cast hbig
            rw [hQ₀] at h1
            push_cast at h1
            linarith [Nat.le_ceil ((8 * K / (1 - β₁)) ^ ((((17:ℝ)/10 - ε/2))⁻¹))]
          have h2 : 8 * K / (1 - β₁) ≤ ((q:ℝ)) ^ ((17:ℝ)/10 - ε/2) := by
            calc 8 * K / (1 - β₁)
                = ((8 * K / (1 - β₁)) ^ ((((17:ℝ)/10 - ε/2))⁻¹)) ^ ((17:ℝ)/10 - ε/2) := by
                  rw [← Real.rpow_mul hR0.le, inv_mul_cancel₀ (ne_of_gt hp0),
                    Real.rpow_one]
              _ ≤ ((q:ℝ)) ^ ((17:ℝ)/10 - ε/2) :=
                  Real.rpow_le_rpow (Real.rpow_nonneg hR0.le _) hq_ge hp0.le
          have h3 : ((q:ℝ)) ^ ((17:ℝ)/10 - ε/2)
              = ((q:ℝ)) ^ ((17:ℝ)/10) * ((q:ℝ)) ^ (-(ε/2)) := by
            rw [← Real.rpow_add hqpos]
            congr 1
          have hc17 : ((q:ℝ)) ^ (-(17:ℝ)/10) * ((q:ℝ)) ^ ((17:ℝ)/10) = 1 := by
            rw [← Real.rpow_add hqpos]
            norm_num
          have hce2 : ((q:ℝ)) ^ (-(ε/2)) * ((q:ℝ)) ^ (ε/2) = 1 := by
            rw [← Real.rpow_add hqpos]
            simp
          rw [le_div_iff₀ (by positivity)]
          rw [div_le_iff₀ hβ₁pos, h3] at h2
          have h4 := mul_le_mul_of_nonneg_right h2
            (show (0:ℝ) ≤ ((q:ℝ)) ^ (-(17:ℝ)/10) * ((q:ℝ)) ^ (ε/2) by positivity)
          have h5 : ((q:ℝ)) ^ ((17:ℝ)/10) * ((q:ℝ)) ^ (-(ε/2)) * (1 - β₁)
              * (((q:ℝ)) ^ (-(17:ℝ)/10) * ((q:ℝ)) ^ (ε/2))
              = (1 - β₁) * ((((q:ℝ)) ^ (-(17:ℝ)/10) * ((q:ℝ)) ^ ((17:ℝ)/10))
                * (((q:ℝ)) ^ (-(ε/2)) * ((q:ℝ)) ^ (ε/2))) := by ring
          rw [h5, hc17, hce2] at h4
          have h6 : 8 * K * (((q:ℝ)) ^ (-(17:ℝ)/10) * ((q:ℝ)) ^ (ε/2))
              = 4 * ((q:ℝ)) ^ (-(17:ℝ)/10) * (2 * K * ((q:ℝ)) ^ (ε/2)) := by ring
          rw [h6] at h4
          simpa using h4
        have hchain : (1 - β₁) / (K * ((q:ℝ)) ^ (ε/2))
            ≤ 2 * (1 - β) * (1 + 3 * Real.log q) ^ 2 + 4 * ((q:ℝ)) ^ (-(17:ℝ)/10) := by
          calc (1 - β₁) / (K * ((q:ℝ)) ^ (ε/2)) ≤ (1 - β₁) / BIG :=
              div_le_div_of_nonneg_left hβ₁pos.le hBIG0 hKq
            _ ≤ _ := hgap
        have hhalf : (1 - β₁) / (K * ((q:ℝ)) ^ (ε/2))
            = 2 * ((1 - β₁) / (2 * K * ((q:ℝ)) ^ (ε/2))) := by
          field_simp
        have hmain2 : (1 - β₁) / (2 * K * ((q:ℝ)) ^ (ε/2))
            ≤ 2 * (1 - β) * (1 + 3 * Real.log q) ^ 2 := by
          linarith [hchain, hthresh, hhalf.le, hhalf.ge]
        have hlog2 : (1 + 3 * Real.log q) ^ 2 ≤ (169 / ε ^ 2) * ((q:ℝ)) ^ (ε/2) := by
          have h1 : Real.log q ≤ ((q:ℝ)) ^ (ε/4) / (ε/4) :=
            Real.log_le_rpow_div hqpos.le (by linarith)
          have hp1 : (1:ℝ) ≤ ((q:ℝ)) ^ (ε/4) := Real.one_le_rpow hq1r (by linarith)
          have h2 : 1 + 3 * Real.log q ≤ (13 / ε) * ((q:ℝ)) ^ (ε/4) := by
            have h1' : Real.log q * (ε/4) ≤ ((q:ℝ)) ^ (ε/4) := by
              rwa [← le_div_iff₀ (by linarith : (0:ℝ) < ε/4)]
            rw [div_mul_eq_mul_div, le_div_iff₀ hε0]
            nlinarith [h1', hp1, hε1, hε0]
          have h7 : (0:ℝ) ≤ 1 + 3 * Real.log q := by
            have := Real.log_nonneg hq1r
            linarith
          calc (1 + 3 * Real.log q) ^ 2 ≤ ((13 / ε) * ((q:ℝ)) ^ (ε/4)) ^ 2 := by
                nlinarith [h2, h7]
            _ = (169 / ε ^ 2) * (((q:ℝ)) ^ (ε/4) * ((q:ℝ)) ^ (ε/4)) := by ring
            _ = (169 / ε ^ 2) * ((q:ℝ)) ^ (ε/2) := by
                rw [← Real.rpow_add hqpos]
                congr 2
                ring
        apply hclose_rpow cc hcc0.le _ _
        · rw [hc]
          exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
        · have hq2 : (0:ℝ) < ((q:ℝ)) ^ (ε/2) := Real.rpow_pos_of_pos hqpos _
          have h1 : (1 - β₁) / (2 * K * ((q:ℝ)) ^ (ε/2))
              ≤ 2 * (1 - β) * ((169 / ε ^ 2) * ((q:ℝ)) ^ (ε/2)) := by
            calc (1 - β₁) / (2 * K * ((q:ℝ)) ^ (ε/2))
                ≤ 2 * (1 - β) * (1 + 3 * Real.log q) ^ 2 := hmain2
              _ ≤ 2 * (1 - β) * ((169 / ε ^ 2) * ((q:ℝ)) ^ (ε/2)) := by
                  apply mul_le_mul_of_nonneg_left hlog2 (by linarith)
          have hqeq : ((q:ℝ)) ^ (ε/2) * ((q:ℝ)) ^ (ε/2) = ((q:ℝ)) ^ ε := by
            rw [← Real.rpow_add hqpos]
            congr 1
            ring
          have hqinv : ((q:ℝ)) ^ (-ε) * ((q:ℝ)) ^ ε = 1 := by
            rw [← Real.rpow_add hqpos]
            simp
          rw [div_le_iff₀ (by positivity)] at h1
          have h2 : 2 * (1 - β) * ((169 / ε ^ 2) * ((q:ℝ)) ^ (ε/2))
              * (2 * K * ((q:ℝ)) ^ (ε/2))
              = (676 * K / ε ^ 2) * (1 - β) * (((q:ℝ)) ^ (ε/2) * ((q:ℝ)) ^ (ε/2)) := by
            ring
          rw [h2, hqeq] at h1
          have h3 := mul_le_mul_of_nonneg_right h1
            (show (0:ℝ) ≤ (ε ^ 2 / (676 * K)) * ((q:ℝ)) ^ (-ε) by positivity)
          have h4 : (676 * K / ε ^ 2) * (1 - β) * ((q:ℝ)) ^ ε
              * ((ε ^ 2 / (676 * K)) * ((q:ℝ)) ^ (-ε))
              = (1 - β) * (((q:ℝ)) ^ (-ε) * ((q:ℝ)) ^ ε)
                * ((676 * K / ε ^ 2) * (ε ^ 2 / (676 * K))) := by ring
          have h5 : (676 * K / ε ^ 2) * (ε ^ 2 / (676 * K)) = 1 := by
            field_simp
          rw [h4, hqinv, h5, mul_one, mul_one] at h3
          have h6 : (1 - β₁) * ((ε ^ 2 / (676 * K)) * ((q:ℝ)) ^ (-ε))
              = ((1 - β₁) * ε ^ 2 / (676 * K)) * ((q:ℝ)) ^ (-ε) := by ring
          rw [h6] at h3
          rw [hcc]
          linarith [h3]

/-- **SIEGEL'S THEOREM** (Siegel brick S3c-h, final form): for every `ε > 0` there
    is `c(ε) > 0` (ineffective) with: every real zero `β < 1` of every quadratic
    nontrivial Dirichlet character mod `q ≥ 3` satisfies `β ≤ 1 − c·q^{−ε}`. -/
theorem siegel_zero_free (ε : ℝ) (hε0 : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ ^ 2 = 1 → χ ≠ 1 →
      ∀ β : ℝ, β < 1 → DirichletCharacter.LFunction χ ((β:ℂ)) = 0 →
      β ≤ 1 - c * ((q:ℝ)) ^ (-ε) := by
  rcases le_or_gt ε (1/100) with hε1 | hε1
  · exact siegel_zero_free_aux ε hε0 hε1
  · obtain ⟨c, hc0, hc⟩ := siegel_zero_free_aux (1/100) (by norm_num) (le_refl _)
    refine ⟨c, hc0, ?_⟩
    intro q _ hq3 χ hχ2 hχ1 β hβ2 hzero
    have h1 := hc q hq3 χ hχ2 hχ1 β hβ2 hzero
    have hq1r : (1:ℝ) ≤ (q:ℝ) := by
      have : (1:ℕ) ≤ q := by omega
      exact_mod_cast this
    have h2 : ((q:ℝ)) ^ (-ε) ≤ ((q:ℝ)) ^ (-(1/100:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hq1r (by linarith)
    have h3 : c * ((q:ℝ)) ^ (-ε) ≤ c * ((q:ℝ)) ^ (-(1/100:ℝ)) :=
      mul_le_mul_of_nonneg_left h2 hc0.le
    linarith [h1, h3]

/-! ### ================= THE FINAL MERGE (S4b) ================= -/

/-- **THE FINAL ZERO-FREE REGION** (SW brick S4b): for every `ε > 0` there is
    `c(ε) > 0` (ineffective, via Siegel) with: EVERY zero `β + iγ` of EVERY
    nontrivial Dirichlet L-function mod `N` satisfies
    `β ≤ 1 − c·N^{−ε}/(log(N(4|γ|+7)) + 20)`.
    Non-quadratic: de la Vallée-Poussin uniform. Quadratic off-axis: the
    conjugate-pair/damped-3-4-1 region. Quadratic real zeros: Siegel. -/
theorem zero_free_region_final (ε : ℝ) (hε0 : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      ∀ β γ : ℝ, DirichletCharacter.LFunction χ ((β:ℂ) + γ*Complex.I) = 0 →
      β ≤ 1 - c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*|γ|+7)) + 20) := by
  obtain ⟨C₁, hC₁1, hC₁⟩ := dvp_zero_free_uniform
  obtain ⟨C₂, hC₂1, hC₂⟩ := dvp_zero_free_uniform_quadratic
  obtain ⟨c₃, hc₃0, hc₃⟩ := siegel_zero_free ε hε0
  obtain ⟨c, hcdef⟩ : ∃ x : ℝ,
      x = min (min (1/(335*(1360+C₁))) (1/C₂)) (min (20*c₃) 1) := ⟨_, rfl⟩
  have hA0 : (0:ℝ) < 1/(335*(1360+C₁)) := by
    apply div_pos one_pos
    nlinarith [hC₁1]
  have hB0 : (0:ℝ) < 1/C₂ := by
    apply div_pos one_pos
    linarith
  have hc0 : 0 < c := by
    rw [hcdef]
    apply lt_min (lt_min hA0 hB0)
    apply lt_min (by linarith) one_pos
  refine ⟨c, hc0, ?_⟩
  intro N _ χ hχ1 β γ hzero
  have hN1r : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hg0 : (0:ℝ) ≤ |γ| := abs_nonneg γ
  have harg1 : (1:ℝ) ≤ (N:ℝ) * (4*|γ|+7) := by nlinarith
  have hL0 : (0:ℝ) ≤ Real.log ((N:ℝ)*(4*|γ|+7)) := Real.log_nonneg harg1
  obtain ⟨L₀, hL₀def⟩ : ∃ Lv : ℝ, Lv = Real.log ((N:ℝ)*(4*|γ|+7)) + 20 := ⟨_, rfl⟩
  rw [← hL₀def]
  have hL20 : 20 ≤ L₀ := by rw [hL₀def]; linarith
  have hNe1 : ((N:ℝ))^(-ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1r (by linarith)
  have hNe0 : (0:ℝ) < ((N:ℝ))^(-ε) := Real.rpow_pos_of_pos (by linarith) _
  have hclose : ∀ K : ℝ, c * ((N:ℝ))^(-ε) ≤ K*L₀ → β ≤ 1 - K →
      β ≤ 1 - c*((N:ℝ))^(-ε)/L₀ := by
    intro K hK hβ
    have h1 : c*((N:ℝ))^(-ε)/L₀ ≤ K := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < L₀)]
      linarith [hK]
    linarith [h1, hβ]
  by_cases hquad : χ^2 = 1
  · by_cases hγ : γ = 0
    · -- Siegel: the real zero of a quadratic character
      subst hγ
      simp only [Complex.ofReal_zero, zero_mul, add_zero] at hzero
      by_cases hN3 : 3 ≤ N
      · have hβ1 : β < 1 := by
          by_contra hβ'
          push_neg at hβ'
          have hre : (1:ℝ) ≤ (((β:ℝ):ℂ)).re := by
            rw [Complex.ofReal_re]
            linarith
          exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) hre hzero
        have h1 := hc₃ N hN3 χ hquad hχ1 β hβ1 hzero
        apply hclose (c₃ * ((N:ℝ))^(-ε)) _ h1
        have h2 : c ≤ 20*c₃ := by
          rw [hcdef]
          exact le_trans (min_le_right _ _) (min_le_left _ _)
        have h3 : 20*c₃ ≤ c₃*L₀ := by nlinarith [hc₃0, hL20]
        have h4 := mul_le_mul_of_nonneg_right (le_trans h2 h3) hNe0.le
        have h5 : (c₃*L₀)*((N:ℝ))^(-ε) = (c₃*((N:ℝ))^(-ε))*L₀ := by ring
        linarith [h4, h5.le, h5.ge]
      · -- no nontrivial character below modulus 3
        push_neg at hN3
        exfalso
        apply hχ1
        have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
        interval_cases N
        · -- N = 1
          apply MulChar.ext
          intro a
          have ha : ∀ b : (ZMod 1)ˣ, b = 1 := by decide
          rw [ha a]
          simp
        · -- N = 2
          apply MulChar.ext
          intro a
          have ha : ∀ b : (ZMod 2)ˣ, b = 1 := by decide
          rw [ha a]
          simp
    · -- quadratic, off the real axis
      have h1 := hC₂ N χ hχ1 hquad β γ hγ hzero
      rw [← hL₀def] at h1
      apply hclose (1/(C₂*L₀)) _ h1
      have h2 : c ≤ 1/C₂ := by
        rw [hcdef]
        exact le_trans (min_le_left _ _) (min_le_right _ _)
      have h3 : c*((N:ℝ))^(-ε) ≤ c := by nlinarith [hNe1, hNe0.le, hc0]
      have hC₂0 : C₂ ≠ 0 := by linarith
      have hL₀ne : L₀ ≠ 0 := by linarith
      have h4 : (1/(C₂*L₀))*L₀ = 1/C₂ := by
        field_simp
      linarith [h2, h3, h4.le, h4.ge]
  · -- non-quadratic: de la Vallée-Poussin
    have h1 := hC₁ N χ hχ1 hquad β γ hzero
    rw [← hL₀def] at h1
    apply hclose (1/(335*(1360+C₁)*L₀)) _ h1
    have h2 : c ≤ 1/(335*(1360+C₁)) := by
      rw [hcdef]
      exact le_trans (min_le_left _ _) (min_le_left _ _)
    have h3 : c*((N:ℝ))^(-ε) ≤ c := by nlinarith [hNe1, hNe0.le, hc0]
    have hden : (335:ℝ)*(1360+C₁) ≠ 0 := by nlinarith [hC₁1]
    have hL₀ne : L₀ ≠ 0 := by linarith
    have h4 : (1/(335*(1360+C₁)*L₀))*L₀ = 1/(335*(1360+C₁)) := by
      field_simp
    linarith [h2, h3, h4.le, h4.ge]

