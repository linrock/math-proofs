module

public import OriginalNth1054

@[expose] public section


/-!
# Cofactor-two divisor prefixes and aliquot sums in Erdős #1054

For an even modulus $m = 2d$, the divisors of $2d$ not exceeding $d$ are
precisely the proper divisors of $2d$. Thus the cofactor-two divisor-prefix sum
$F(2, d)$ equals the classical aliquot sum $s(2d) = \sum_{q \mid 2d,\, q < 2d} q$,
and for $2d \ge 4$ the proper divisors $1$ and $d$ yield $f(s(2d)) \le 2d < 2 s(2d)$.
-/

open Finset

namespace Erdos1054.Aliquot

/-- The classical aliquot sum: the sum of all proper positive divisors. -/
def aliquot (m : ℕ) : ℕ := ∑ q ∈ m.properDivisors, q

/-- For every even modulus, including zero, its divisors below its halfway
point are exactly its proper divisors. -/
theorem even_divisor_prefix_eq_properDivisors (d : ℕ) :
    (2 * d).divisors.filter (fun q => q ≤ d) =
      (2 * d).properDivisors := by
  classical
  by_cases hd : d = 0
  · subst d
    simp
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    ext q
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.mem_properDivisors]
    constructor
    · rintro ⟨⟨hq, _⟩, hqd⟩
      exact ⟨hq, by omega⟩
    · rintro ⟨hq, hqproper⟩
      refine ⟨⟨hq, by omega⟩, ?_⟩
      have hqpos : 0 < q := Nat.pos_of_dvd_of_pos hq (by omega)
      obtain ⟨k, hk⟩ := hq
      have hklarge : 2 ≤ k := by
        by_contra hnot
        have hkcases : k = 0 ∨ k = 1 := by omega
        rcases hkcases with rfl | rfl <;> simp_all
      have htwice : q * 2 ≤ 2 * d := calc
        q * 2 ≤ q * k := Nat.mul_le_mul_left q hklarge
        _ = 2 * d := hk.symm
      omega

/-- The cofactor-two divisor-prefix sum is exactly the even aliquot sum. -/
theorem F_two_eq_aliquot (d : ℕ) :
    _root_.Represented.F 2 d = aliquot (2 * d) := by
  unfold _root_.Represented.F aliquot
  rw [even_divisor_prefix_eq_properDivisors]

/-- The proper-divisor convention agrees exactly with `σ(m) - m`. -/
theorem aliquot_eq_sigma_sub (m : ℕ) :
    aliquot m = ArithmeticFunction.sigma 1 m - m := by
  rw [ArithmeticFunction.sigma_one_apply,
    Nat.sum_divisors_eq_sum_properDivisors_add_self]
  simp [aliquot]

/-- The even aliquot sum is represented by its actual positive even modulus. -/
theorem even_aliquot_represented {d : ℕ} (hd : 0 < d) :
    aliquot (2 * d) ∈ _root_.Represented.R := by
  rw [_root_.Represented.mem_R_iff_exists_F]
  exact ⟨2, d, by omega, hd, (F_two_eq_aliquot d).symm⟩

/-- The *official*, zero-padded `Nat.nth`/`Nat.find` minimizer is bounded by
the concrete even modulus giving the aliquot-prefix representation. -/
theorem official_f_even_aliquot_le {d : ℕ} (hd : 0 < d) :
    _root_.Erdos1054.OriginalNth.f (aliquot (2 * d)) ≤ 2 * d := by
  rw [_root_.Erdos1054.OriginalNth.f_eq_supported, _root_.Represented.f]
  apply Nat.sInf_le
  rw [_root_.Represented.f_set_eq]
  exact ⟨2, d, by omega, hd, rfl, (F_two_eq_aliquot d).symm⟩

/-- The distinct proper divisors `1` and `d` force a strictly better bound
than the non-strict half-modulus estimate. -/
theorem one_add_half_le_aliquot {d : ℕ} (hd : 2 ≤ d) :
    1 + d ≤ aliquot (2 * d) := by
  have hone : 1 ∈ (2 * d).properDivisors :=
    Nat.mem_properDivisors.mpr ⟨by simp, by omega⟩
  have hhalf : d ∈ (2 * d).properDivisors :=
    Nat.mem_properDivisors.mpr ⟨by simp, by omega⟩
  have hsubset : ({1, d} : Finset ℕ) ⊆ (2 * d).properDivisors := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact hone
    · exact hhalf
  calc
    1 + d = ∑ q ∈ ({1, d} : Finset ℕ), q := by
      simp [show (1 : ℕ) ≠ d by omega]
    _ ≤ ∑ q ∈ (2 * d).properDivisors, q :=
      Finset.sum_le_sum_of_subset hsubset
    _ = aliquot (2 * d) := rfl

/-- Every even modulus at least four is strictly less than twice its aliquot
sum; the excluded modulus two attains equality. -/
theorem even_lt_two_aliquot {d : ℕ} (hd : 2 ≤ d) :
    2 * d < 2 * aliquot (2 * d) := by
  have h := one_add_half_le_aliquot hd
  omega

/-- Every even modulus at least four gives an exact official divisor-prefix
witness with `f(s(m)) ≤ m < 2 * s(m)`. -/
theorem official_even_aliquot_bounds (m : ℕ) (heven : Even m)
    (hm : 4 ≤ m) :
    _root_.Erdos1054.OriginalNth.f (aliquot m) ≤ m ∧
      m < 2 * aliquot m := by
  obtain ⟨d, hd⟩ := heven
  have hmform : m = 2 * d := by omega
  rw [hmform] at hm ⊢
  have hdlarge : 2 ≤ d := by omega
  exact ⟨official_f_even_aliquot_le (by omega),
    even_lt_two_aliquot hdlarge⟩

/-- An even modulus at least four therefore produces a represented official
value lying on the bounded-ratio, opposite tail. -/
theorem official_even_aliquot_lt_two (m : ℕ) (heven : Even m)
    (hm : 4 ≤ m) :
    aliquot m ∈ _root_.Represented.R ∧
      _root_.Erdos1054.OriginalNth.f (aliquot m) < 2 * aliquot m := by
  obtain ⟨d, hd⟩ := heven
  have hmform : m = 2 * d := by omega
  rw [hmform] at hm ⊢
  have hdlarge : 2 ≤ d := by omega
  exact ⟨even_aliquot_represented (by omega),
    lt_of_le_of_lt (official_f_even_aliquot_le (by omega))
      (even_lt_two_aliquot hdlarge)⟩

/-- Deficiency is exactly the strict lower side of the aliquot/modulus
sandwich; it is not needed for the upper factor-two bound. -/
theorem deficient_aliquot_lt {m : ℕ} (hm : Nat.Deficient m) :
    aliquot m < m := by
  simpa only [aliquot, Nat.Deficient] using hm

/-- The precise analytic input relevant to the even opposite tail: positive
lower density of *even values* with even deficient preimages at least four.
No external density theorem is introduced as an axiom. -/
def EvenDeficientAliquotValue (n : ℕ) : Prop :=
  Even n ∧ ∃ m : ℕ, Even m ∧ 4 ≤ m ∧ Nat.Deficient m ∧ n = aliquot m

/-- An explicit Luca–Pomerance-type density input transfers to positive lower
density of represented *even* integers whose official minimizer is less than
twice the integer.  The source theorem remains an ordinary explicit hypothesis. -/
theorem positiveLowerDensity_even_opposite_tail
    (hLucaPomerance :
      _root_.Erdos1054.PositiveLowerDensity EvenDeficientAliquotValue) :
    _root_.Erdos1054.PositiveLowerDensity
      (fun n : ℕ => Even n ∧ n ∈ _root_.Represented.R ∧
        _root_.Erdos1054.OriginalNth.f n < 2 * n) := by
  apply _root_.Erdos1054.positiveLowerDensity_mono
    (P := EvenDeficientAliquotValue)
    (Q := fun n : ℕ => Even n ∧ n ∈ _root_.Represented.R ∧
      _root_.Erdos1054.OriginalNth.f n < 2 * n)
  · intro n hn
    obtain ⟨hneven, m, hmeven, hm4, _, rfl⟩ := hn
    exact ⟨hneven, official_even_aliquot_lt_two m hmeven hm4⟩
  · exact hLucaPomerance

end Erdos1054.Aliquot
