module

public import Aliquot1054

@[expose] public section


/-!
# Parity classification of cofactor-two aliquot sums in Erdős #1054

Proves the exact parity characterization for divisor sums $\sigma(n)$ and
cofactor-two aliquot sums $s(2d) = F(2, d)$: $s(2d)$ is odd if and only if
$d = s^2$ or $d = 2s^2$ for some $s \ge 1$. Consequently, the odd values in the
cofactor-two range have count at most $2(\lfloor\sqrt{X}\rfloor + 1)$ up to $X$
and natural density zero, while odd primes $p$ give represented even integers
$N = p + 3 = s(2p)$ with $0 < f(N) \le 2p < 2N$.
-/

open Finset Filter Asymptotics
open scoped ArithmeticFunction

namespace Erdos1054.CofactorParity

/-- If every odd prime has even valuation, its divisor sum is odd.  The prime
two contributes an odd geometric sum regardless of its valuation. -/
theorem sigma_odd_of_even_odd_prime_factorization {n : ℕ} (hn : n ≠ 0)
    (hvaluation : ∀ p ∈ n.primeFactors, p ≠ 2 → Even (n.factorization p)) :
    Odd (ArithmeticFunction.sigma 1 n) := by
  classical
  rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn]
  apply Finset.prod_induction
    (fun p => ∑ i ∈ Finset.range (n.factorization p + 1), p ^ (i * 1)) Odd
    (fun _ _ ha hb => ha.mul hb) odd_one
  intro p hp
  by_cases hp2 : p = 2
  · subst p
    rw [Nat.odd_iff, Finset.sum_nat_mod]
    simp [Nat.pow_mod, Finset.sum_range_succ']
  · have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hpprime.odd_of_ne_two hp2)
    have heven : n.factorization p % 2 = 0 :=
      Nat.even_iff.mp (hvaluation p hp hp2)
    rw [Nat.odd_iff, Finset.sum_nat_mod]
    simp [Nat.pow_mod, hpodd, Nat.add_mod, heven]

/-- The divisor sum of every nonzero square is odd. -/
theorem sigma_odd_of_square {s : ℕ} (hs : 0 < s) :
    Odd (ArithmeticFunction.sigma 1 (s ^ 2)) := by
  apply sigma_odd_of_even_odd_prime_factorization (by positivity)
  intro p _ _
  rw [Nat.factorization_pow, Finsupp.smul_apply]
  exact even_two_mul (s.factorization p)

/-- The divisor sum of every nonzero twice-square is odd. -/
theorem sigma_odd_of_twice_square {s : ℕ} (hs : 0 < s) :
    Odd (ArithmeticFunction.sigma 1 (2 * s ^ 2)) := by
  apply sigma_odd_of_even_odd_prime_factorization (by positivity)
  intro p _ hp2
  rw [Nat.factorization_mul (by decide) (by positivity), Finsupp.add_apply,
    Nat.Prime.factorization Nat.prime_two, Finsupp.single_apply,
    ite_eq_right (Ne.symm hp2), zero_add, Nat.factorization_pow, Finsupp.smul_apply]
  exact even_two_mul (s.factorization p)

/-- Exact divisor-sum parity, including the normally omitted zero endpoint:
the square root must be positive because `σ(0) = 0`. -/
theorem sigma_odd_iff_square_or_twice_square (n : ℕ) :
    Odd (ArithmeticFunction.sigma 1 n) ↔
      ∃ s : ℕ, 0 < s ∧ (n = s ^ 2 ∨ n = 2 * s ^ 2) := by
  constructor
  · intro hodd
    have hn : 0 < n := by
      have hsigmapos : 0 < ArithmeticFunction.sigma 1 n := by
        obtain ⟨k, hk⟩ := hodd
        omega
      exact ArithmeticFunction.sigma_pos_iff.mp hsigmapos
    obtain ⟨s, hs⟩ := _root_.Represented.sigma_odd_imp_sq_or_twosq n hn hodd
    refine ⟨s, ?_, hs⟩
    rcases hs with hs | hs <;> nlinarith
  · rintro ⟨s, hs, rfl | rfl⟩
    · exact sigma_odd_of_square hs
    · exact sigma_odd_of_twice_square hs

/-- Divisor sums split into the aliquot sum and the integer itself, even at
the zero endpoint. -/
theorem sigma_eq_aliquot_add (n : ℕ) :
    ArithmeticFunction.sigma 1 n = _root_.Erdos1054.Aliquot.aliquot n + n := by
  rw [ArithmeticFunction.sigma_one_apply,
    Nat.sum_divisors_eq_sum_properDivisors_add_self]
  rfl

/-- Subtracting an even modulus leaves divisor-sum parity unchanged. -/
theorem odd_aliquot_iff_sigma_of_even {n : ℕ} (hn : Even n) :
    Odd (_root_.Erdos1054.Aliquot.aliquot n) ↔
      Odd (ArithmeticFunction.sigma 1 n) := by
  rw [sigma_eq_aliquot_add, Nat.odd_add]
  simp [hn]

/-- The exact cofactor-two parity classification, with no exceptional
zero-modulus loophole: an even aliquot input has odd output precisely when
its half is a positive square or a positive twice-square. -/
theorem odd_aliquot_iff_square_or_twice_square (d : ℕ) :
    Odd (_root_.Erdos1054.Aliquot.aliquot (2 * d)) ↔
      ∃ s : ℕ, 0 < s ∧ (d = s ^ 2 ∨ d = 2 * s ^ 2) := by
  rw [odd_aliquot_iff_sigma_of_even (even_two_mul d),
    sigma_odd_iff_square_or_twice_square]
  constructor
  · rintro ⟨s, hs, hsquare | htwice⟩
    · have hseven : Even s :=
        (Nat.even_pow' (by decide : (2 : ℕ) ≠ 0)).mp
          (hsquare ▸ even_two_mul d)
      obtain ⟨t, ht⟩ := hseven
      have hst : s = 2 * t := by omega
      refine ⟨t, by omega, Or.inr ?_⟩
      rw [hst] at hsquare
      nlinarith
    · exact ⟨s, hs, Or.inl (by omega)⟩
  · rintro ⟨s, hs, rfl | rfl⟩
    · exact ⟨s, hs, Or.inr rfl⟩
    · refine ⟨2 * s, by omega, Or.inl ?_⟩
      ring

/-- The same exact classification for the upstream cofactor-two divisor
prefix, not merely for an informal aliquot surrogate. -/
theorem odd_F_two_iff_square_or_twice_square (d : ℕ) :
    Odd (_root_.Represented.F 2 d) ↔
      ∃ s : ℕ, 0 < s ∧ (d = s ^ 2 ∨ d = 2 * s ^ 2) := by
  rw [_root_.Erdos1054.Aliquot.F_two_eq_aliquot,
    odd_aliquot_iff_square_or_twice_square]

/-- Equivalently, the cofactor-two output is even exactly off the sparse
positive square/twice-square parameter set. -/
theorem even_aliquot_iff_not_square_or_twice_square (d : ℕ) :
    Even (_root_.Erdos1054.Aliquot.aliquot (2 * d)) ↔
      ¬ ∃ s : ℕ, 0 < s ∧ (d = s ^ 2 ∨ d = 2 * s ^ 2) := by
  rw [← Nat.not_odd_iff_even, odd_aliquot_iff_square_or_twice_square]

/-- The half-modulus is itself a proper divisor, so it never exceeds its
aliquot value; the zero and modulus-two endpoints are included. -/
theorem half_le_aliquot (d : ℕ) :
    d ≤ _root_.Erdos1054.Aliquot.aliquot (2 * d) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [_root_.Erdos1054.Aliquot.aliquot]
  · have hmem : d ∈ (2 * d).properDivisors :=
      Nat.mem_properDivisors.mpr ⟨by simp, by omega⟩
    exact Finset.single_le_sum (fun q _ => Nat.zero_le q) hmem

/-- Odd cofactor-two *values* up to `X` inject into the image of sparse
square/twice-square half-moduli up to the same bound.  This is a value-range
bound, not merely a statement about the density of input parameters. -/
theorem odd_aliquot_value_count_le_square_count (X : ℕ) :
    _root_.Represented.countUpTo
        (fun N : ℕ => Odd N ∧ ∃ d : ℕ, 0 < d ∧
          N = _root_.Erdos1054.Aliquot.aliquot (2 * d)) X ≤
      _root_.Represented.countUpTo
        (fun d : ℕ => ∃ s : ℕ, d = s ^ 2 ∨ d = 2 * s ^ 2) X := by
  have hfin :
      (_root_.Represented.setUpTo
        (fun d : ℕ => ∃ s : ℕ, d = s ^ 2 ∨ d = 2 * s ^ 2) X).Finite :=
    Set.Finite.subset (Set.finite_Iic X) (fun n hn => hn.1)
  have hsub :
      _root_.Represented.setUpTo
          (fun N : ℕ => Odd N ∧ ∃ d : ℕ, 0 < d ∧
            N = _root_.Erdos1054.Aliquot.aliquot (2 * d)) X ⊆
        (fun d : ℕ => _root_.Erdos1054.Aliquot.aliquot (2 * d)) ''
          _root_.Represented.setUpTo
            (fun d : ℕ => ∃ s : ℕ, d = s ^ 2 ∨ d = 2 * s ^ 2) X := by
    intro N hN
    obtain ⟨hNX, hNodd, d, hdpos, hd⟩ := hN
    obtain ⟨s, _, hs⟩ :=
      (odd_aliquot_iff_square_or_twice_square d).mp (hd ▸ hNodd)
    have hdX : d ≤ X := calc
      d ≤ _root_.Erdos1054.Aliquot.aliquot (2 * d) := half_le_aliquot d
      _ = N := hd.symm
      _ ≤ X := hNX
    exact ⟨d, ⟨hdX, s, hs⟩, hd.symm⟩
  calc
    (_root_.Represented.setUpTo
        (fun N : ℕ => Odd N ∧ ∃ d : ℕ, 0 < d ∧
          N = _root_.Erdos1054.Aliquot.aliquot (2 * d)) X).ncard
        ≤ ((fun d : ℕ => _root_.Erdos1054.Aliquot.aliquot (2 * d)) ''
          _root_.Represented.setUpTo
            (fun d : ℕ => ∃ s : ℕ, d = s ^ 2 ∨ d = 2 * s ^ 2) X).ncard :=
          Set.ncard_le_ncard hsub (hfin.image _)
    _ ≤ (_root_.Represented.setUpTo
          (fun d : ℕ => ∃ s : ℕ, d = s ^ 2 ∨ d = 2 * s ^ 2) X).ncard :=
          Set.ncard_image_le hfin

/-- A completely explicit square-root bound on distinct odd cofactor-two
values, independently of collisions between different aliquot preimages. -/
theorem odd_aliquot_value_count_le (X : ℕ) :
    _root_.Represented.countUpTo
        (fun N : ℕ => Odd N ∧ ∃ d : ℕ, 0 < d ∧
          N = _root_.Erdos1054.Aliquot.aliquot (2 * d)) X ≤
      2 * (Nat.sqrt X + 1) := by
  refine (odd_aliquot_value_count_le_square_count X).trans ?_
  have hsub :
      _root_.Represented.setUpTo
          (fun d : ℕ => ∃ s : ℕ, d = s ^ 2 ∨ d = 2 * s ^ 2) X ⊆
        ↑((Finset.range (Nat.sqrt X + 1)).image (fun s : ℕ => s ^ 2) ∪
          (Finset.range (Nat.sqrt X + 1)).image (fun s : ℕ => 2 * s ^ 2)) := by
    intro d hd
    obtain ⟨hdX, s, hs | hs⟩ := hd
    · exact Finset.mem_coe.mpr (Finset.mem_union_left _
        (Finset.mem_image.mpr
          ⟨s, Finset.mem_range.mpr
            (Nat.lt_succ_iff.mpr (Nat.le_sqrt'.mpr (hs ▸ hdX))), hs.symm⟩))
    · exact Finset.mem_coe.mpr (Finset.mem_union_right _
        (Finset.mem_image.mpr
          ⟨s, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr
            (Nat.le_sqrt'.mpr (by nlinarith [hdX]))), hs.symm⟩))
  calc
    (_root_.Represented.setUpTo
        (fun d : ℕ => ∃ s : ℕ, d = s ^ 2 ∨ d = 2 * s ^ 2) X).ncard
        ≤ ((Finset.range (Nat.sqrt X + 1)).image (fun s : ℕ => s ^ 2) ∪
          (Finset.range (Nat.sqrt X + 1)).image (fun s : ℕ => 2 * s ^ 2)).card := by
          simpa only [Set.ncard_coe_finset] using
            (Set.ncard_le_ncard hsub (Finset.finite_toSet _))
    _ ≤ 2 * (Nat.sqrt X + 1) := by
      have hfirst := Finset.card_image_le
        (s := Finset.range (Nat.sqrt X + 1)) (f := fun s : ℕ => s ^ 2)
      have hsecond := Finset.card_image_le
        (s := Finset.range (Nat.sqrt X + 1)) (f := fun s : ℕ => 2 * s ^ 2)
      have hunion := Finset.card_union_le
        ((Finset.range (Nat.sqrt X + 1)).image (fun s : ℕ => s ^ 2))
        ((Finset.range (Nat.sqrt X + 1)).image (fun s : ℕ => 2 * s ^ 2))
      simp only [Finset.card_range] at hfirst hsecond
      omega

/-- The odd part of the cofactor-two **value range** has natural density zero.
This proves one full direction of the informal aliquot-range
symmetric-difference obstruction without an external aliquot-density input. -/
theorem odd_aliquot_value_littleO :
    _root_.Represented.CountIsLittleO
      (fun N : ℕ => Odd N ∧ ∃ d : ℕ, 0 < d ∧
        N = _root_.Erdos1054.Aliquot.aliquot (2 * d)) := by
  refine Asymptotics.IsBigO.trans_isLittleO ?_
    _root_.Represented.sq_or_twosq_littleO
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, Filter.Eventually.of_forall (fun X => ?_)⟩
  rw [Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (by positivity), one_mul]
  exact_mod_cast odd_aliquot_value_count_le_square_count X

/-- The precise natural-density-zero conclusion for distinct odd aliquot
values with a positive even preimage. -/
theorem odd_aliquot_value_density_zero :
    Filter.Tendsto
      (fun X : ℕ =>
        (_root_.Represented.countUpTo
          (fun N : ℕ => Odd N ∧ ∃ d : ℕ, 0 < d ∧
            N = _root_.Erdos1054.Aliquot.aliquot (2 * d)) X : ℝ) / X)
      Filter.atTop (nhds 0) :=
  odd_aliquot_value_littleO.tendsto_div

/-- Every odd prime gives the completely explicit even aliquot value
`s(2p) = p + 3`; this uses divisor-sum multiplicativity, not a conjecture
about aliquot ranges or Goldbach representations. -/
theorem aliquot_two_mul_odd_prime {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    _root_.Erdos1054.Aliquot.aliquot (2 * p) = p + 3 := by
  have hcop : Nat.Coprime 2 p := (hp.odd_of_ne_two hp2).coprime_two_left
  have hsigma_two : ArithmeticFunction.sigma 1 2 = 3 := by
    rw [ArithmeticFunction.sigma_one_apply,
      Nat.Prime.divisors Nat.prime_two]
    norm_num
  have hsigma_p : ArithmeticFunction.sigma 1 p = p + 1 := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.Prime.divisors hp,
      Finset.sum_pair hp.one_lt.ne]
    omega
  have hsigma : ArithmeticFunction.sigma 1 (2 * p) =
      ArithmeticFunction.sigma 1 2 * ArithmeticFunction.sigma 1 p :=
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
  rw [sigma_eq_aliquot_add, hsigma_two, hsigma_p] at hsigma
  omega

/-- On the infinite explicit even family `N = p + 3`, the literal official
zero-padded minimizer has the sharp witnessed bound `f(N) ≤ 2p = 2N - 6`.
No claim that `2p` is the *minimal* witness is made. -/
theorem official_f_prime_plus_three_le {p : ℕ}
    (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    _root_.Erdos1054.OriginalNth.f (p + 3) ≤ 2 * p := by
  rw [← aliquot_two_mul_odd_prime hp hp2]
  exact _root_.Erdos1054.Aliquot.official_f_even_aliquot_le hp.pos

/-- There are arbitrarily large represented **even** integers on the
bounded-ratio opposite tail, unconditionally.  This infinitude assertion
neither proves positive density nor resolves the even large-ratio limsup. -/
theorem arbitrarily_large_even_bounded_ratio (B : ℕ) :
    ∃ N : ℕ, B ≤ N ∧ Even N ∧ N ∈ _root_.Represented.R ∧
      _root_.Erdos1054.OriginalNth.f N < 2 * N := by
  obtain ⟨p, hpbound, hp⟩ := Nat.exists_infinite_primes (max B 3)
  have hp2 : p ≠ 2 := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨k, hk⟩ := hpodd
  have hpeven : Even (p + 3) := by
    refine ⟨k + 2, ?_⟩
    omega
  have hrepresented : p + 3 ∈ _root_.Represented.R := by
    rw [← aliquot_two_mul_odd_prime hp hp2]
    exact _root_.Erdos1054.Aliquot.even_aliquot_represented hp.pos
  refine ⟨p + 3, by omega, hpeven, hrepresented, ?_⟩
  have hbound := official_f_prime_plus_three_le hp hp2
  omega

end Erdos1054.CofactorParity
