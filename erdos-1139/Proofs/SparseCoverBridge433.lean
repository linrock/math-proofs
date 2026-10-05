module

public import Mathlib

@[expose] public section


/-!
# Exact finite sparse-covering bridge for Erdős problem #1139

The historical problem enumerates positive integers with at most two prime
factors, counted with multiplicity.  This module preserves that exact predicate
and proves the finite implication from a twofold covering by *distinct* prime
moduli to an interval on which every integer has at least three prime factors.

The logarithmic-cost estimate needed to solve #1139 is deliberately not assumed
or asserted here: the full-prime covering supplied by #689 has linear, rather
than sublinear, logarithmic cost.
-/

open Finset
open scoped ArithmeticFunction.Omega Topology

namespace Erdos1139

/-- Exactly the positive-integer predicate occurring in the upstream
`Nat.nth` statement of Erdős problem #1139. -/
def AlmostPrime (n : ℕ) : Prop := 0 < n ∧ Ω n ≤ 2

/-- A finite prime-subset double covering.  Every modulus is a genuine prime
at most the interval length, and the cardinality counts distinct primes. -/
def PrimeDoubleCover (y : ℕ) (P : Finset ℕ) (a : ℕ → ℕ) : Prop :=
  (∀ p ∈ P, p.Prime ∧ p ≤ y) ∧
    ∀ h ∈ Finset.Icc 1 y,
      2 ≤ (P.filter fun p => a p ≡ h [MOD p]).card

/-- The optional second occurrence of a selected prime is paid for by its
genuine square modulus, not by counting one congruence twice. -/
def selectedPrimeExponent (squared : Finset ℕ) (p : ℕ) : ℕ :=
  if p ∈ squared then 2 else 1

/-- Exact CRT conductor of a prime that is either used once or squared. -/
def selectedPrimePower (squared : Finset ℕ) (p : ℕ) : ℕ :=
  p ^ selectedPrimeExponent squared p

/-- A multiplicity-faithful mixed prime/prime-square covering.  Every selected
prime contributes its broad residue hit; an optionally squared prime earns a
second hit only on its genuinely narrower residue modulo `p²`. -/
def PrimeSquareDoubleCover
    (y : ℕ) (P squared : Finset ℕ) (a : ℕ → ℕ) : Prop :=
  (∀ p ∈ P, p.Prime ∧ p ≤ y) ∧ squared ⊆ P ∧
    ∀ h ∈ Finset.Icc 1 y,
      2 ≤ (P.filter fun p => a p ≡ h [MOD p]).card +
        (squared.filter fun p => a p ≡ h [MOD p ^ 2]).card

/-- The original almost-prime sequence begins with the positive integer one. -/
theorem almostPrime_one : AlmostPrime 1 := by
  simp [AlmostPrime]

/-- Every prime is an almost-prime under the original multiplicity predicate. -/
theorem almostPrime_of_prime {p : ℕ} (hp : p.Prime) : AlmostPrime p := by
  refine ⟨hp.pos, ?_⟩
  simp [ArithmeticFunction.cardFactors_apply_prime hp]

/-- The exact upstream `Nat.nth` predicate has infinite support; Euclid's
theorem supplies primes, so no hidden sequence-existence hypothesis is used. -/
theorem almostPrime_infinite : {n : ℕ | AlmostPrime n}.Infinite := by
  refine Nat.infinite_setOfPred_prime.mono ?_
  intro p hp
  exact almostPrime_of_prime hp

/-- A proper divisor that is the product of two genuine primes forces a third
prime factor.  The two primes need not be distinct: this also handles the
essential nested-prime-square branch of the almost-prime problem. -/
theorem omega_ge_three_of_prime_product_dvd_lt
    {m p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hproduct : p * q ∣ m) (hproper : p * q < m) :
    3 ≤ Ω m := by
  obtain ⟨r, rfl⟩ := hproduct
  have hr : 1 < r := by
    by_contra hnot
    have hle : r ≤ 1 := Nat.le_of_not_gt hnot
    interval_cases r <;> simp_all
  have hrzero : r ≠ 0 := by omega
  rw [ArithmeticFunction.cardFactors_mul
    (mul_ne_zero hp.ne_zero hq.ne_zero) hrzero,
    ArithmeticFunction.cardFactors_mul hp.ne_zero hq.ne_zero,
    ArithmeticFunction.cardFactors_apply_prime hp,
    ArithmeticFunction.cardFactors_apply_prime hq]
  have hpositive : 0 < Ω r :=
    ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hr
  omega

/-- Two *distinct* prime divisors provide their product as a genuine divisor;
the same prime may not be counted twice without a prime-square divisibility
hypothesis. -/
theorem omega_ge_three_of_distinct_prime_dvd_lt
    {m p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hpdvd : p ∣ m) (hqdvd : q ∣ m) (hproper : p * q < m) :
    3 ≤ Ω m :=
  omega_ge_three_of_prime_product_dvd_lt hp hq
    (Nat.Prime.dvd_mul_of_dvd_ne hne hp hq hpdvd hqdvd) hproper

/-- A genuine selected square supplies both prime factors itself.  Its
strictly larger cofactor supplies the indispensable third factor. -/
theorem omega_ge_three_of_prime_square_dvd_lt
    {m p : ℕ} (hp : p.Prime) (hsquare : p ^ 2 ∣ m)
    (hproper : p ^ 2 < m) :
    3 ≤ Ω m := by
  apply omega_ge_three_of_prime_product_dvd_lt hp hp
  · simpa [pow_two] using hsquare
  · simpa [pow_two] using hproper

/-- A modulus divides its complementary residue plus the original integer. -/
theorem complementary_residue_add_dvd (p t : ℕ) (hp : 0 < p) :
    p ∣ (p - t % p) + t := by
  have hle : t % p ≤ p := (Nat.mod_lt t hp).le
  conv_rhs =>
    rhs
    rw [← Nat.mod_add_div t p]
  rw [← Nat.add_assoc, Nat.sub_add_cancel hle]
  exact dvd_add (dvd_refl p) (dvd_mul_right p (t / p))

/-- A cardinality-two covering provides two *distinct* genuine covering
primes, avoiding the invalid step of counting the same modulus twice. -/
theorem double_cover_has_two_distinct_primes
    {y h : ℕ} {P : Finset ℕ} {a : ℕ → ℕ}
    (hcover : PrimeDoubleCover y P a) (hh : h ∈ Finset.Icc 1 y) :
    ∃ p ∈ P, ∃ q ∈ P,
      p ≠ q ∧ p.Prime ∧ q.Prime ∧ p ≤ y ∧ q ≤ y ∧
      a p ≡ h [MOD p] ∧ a q ≡ h [MOD q] := by
  have hcard : 1 < (P.filter fun p => a p ≡ h [MOD p]).card := by
    have htwo := hcover.2 h hh
    omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hcard
  obtain ⟨hpP, hpclass⟩ := Finset.mem_filter.mp hp
  obtain ⟨hqP, hqclass⟩ := Finset.mem_filter.mp hq
  obtain ⟨hpprime, hpy⟩ := hcover.1 p hpP
  obtain ⟨hqprime, hqy⟩ := hcover.1 q hqP
  exact ⟨p, hpP, q, hqP, hpq, hpprime, hqprime, hpy, hqy,
    hpclass, hqclass⟩

/-- Finite CRT with arbitrary positive, pairwise coprime moduli gives a
representative strictly above the baseline and at most one genuine modulus
period beyond it.  This includes both prime and prime-square conductors. -/
theorem exists_bounded_coprime_crt_shift
    (P : Finset ℕ) (modulus a : ℕ → ℕ) (B : ℕ)
    (hpositive : ∀ p ∈ P, 0 < modulus p)
    (hpair : Set.Pairwise (↑P : Set ℕ)
      (fun p q : ℕ => Nat.Coprime (modulus p) (modulus q))) :
    ∃ N : ℕ, B < N ∧ N ≤ B + ∏ p ∈ P, modulus p ∧
      ∀ p ∈ P, modulus p ∣ N + a p := by
  classical
  let Q := ∏ p ∈ P, modulus p
  have hQ : 0 < Q := by
    dsimp [Q]
    exact Finset.prod_pos hpositive
  have hnonzero : ∀ p ∈ P, modulus p ≠ 0 :=
    fun p hp => (hpositive p hp).ne'
  let residues : ℕ → ℕ := fun p => modulus p - (B + a p) % modulus p
  let witness := Nat.chineseRemainderOfFinset residues modulus
    P hnonzero hpair
  have hwitness : (witness : ℕ) < Q := by
    simpa [Q, witness] using
      (Nat.chineseRemainderOfFinset_lt_prod residues modulus
        hnonzero hpair)
  let shift := if (witness : ℕ) = 0 then Q else (witness : ℕ)
  have hshiftpositive : 0 < shift := by
    dsimp [shift]
    split_ifs with hzero
    · exact hQ
    · exact Nat.pos_of_ne_zero hzero
  have hshiftbound : shift ≤ Q := by
    dsimp [shift]
    split_ifs with hzero
    · exact le_rfl
    · exact hwitness.le
  refine ⟨B + shift, Nat.lt_add_of_pos_right hshiftpositive, ?_, ?_⟩
  · exact Nat.add_le_add_left hshiftbound B
  · intro p hp
    have hpQ : modulus p ∣ Q := by
      dsimp [Q]
      exact Finset.dvd_prod_of_mem modulus hp
    have hshift : shift ≡ (witness : ℕ) [MOD modulus p] := by
      dsimp [shift]
      split_ifs with hzero
      · simpa [hzero] using (Nat.modEq_zero_iff_dvd.mpr hpQ)
      · exact Nat.ModEq.rfl
    have hcrt : (witness : ℕ) ≡ residues p [MOD modulus p] :=
      witness.property p hp
    have hcongruence : B + shift + a p ≡ B + residues p + a p
        [MOD modulus p] :=
      (Nat.ModEq.rfl.add (hshift.trans hcrt)).add Nat.ModEq.rfl
    have hright : modulus p ∣ B + residues p + a p := by
      simpa [residues, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        complementary_residue_add_dvd (modulus p) (B + a p) (hpositive p hp)
    exact Nat.modEq_zero_iff_dvd.mp
      (hcongruence.trans (Nat.modEq_zero_iff_dvd.mpr hright))

/-- The squarefree specialization preserves the exact original one-period
prime-product bound. -/
theorem exists_bounded_prime_crt_shift
    (P : Finset ℕ) (a : ℕ → ℕ) (B : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) :
    ∃ N : ℕ, B < N ∧ N ≤ B + ∏ p ∈ P, p ∧
      ∀ p ∈ P, p ∣ N + a p := by
  have hpair : Set.Pairwise (↑P : Set ℕ)
      (fun p q : ℕ => Nat.Coprime p q) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq
  exact exists_bounded_coprime_crt_shift P (fun p : ℕ => p) a B
    (fun p hp => (hprime p hp).pos) hpair

/-- Transport a selected residue hit through the genuine CRT congruence. -/
theorem shifted_divisor_of_cover_residue
    {N p residue h : ℕ} (hshift : p ∣ N + residue)
    (hhit : residue ≡ h [MOD p]) :
    p ∣ N + h := by
  exact Nat.modEq_zero_iff_dvd.mp
    ((Nat.ModEq.rfl.add hhit).symm.trans
      (Nat.modEq_zero_iff_dvd.mpr hshift))

/-- The exact finite sparse double-covering bridge: after shifting strictly
past `y²`, every point in the original closed interval has at least three
prime factors, with multiplicity.  The shift costs at most one actual CRT
prime-product period. -/
theorem double_cover_forces_three_factor_interval
    {y : ℕ} {P : Finset ℕ} {a : ℕ → ℕ}
    (hcover : PrimeDoubleCover y P a) :
    ∃ N : ℕ, y ^ 2 < N ∧ N ≤ y ^ 2 + ∏ p ∈ P, p ∧
      ∀ h ∈ Finset.Icc 1 y, 3 ≤ Ω (N + h) := by
  obtain ⟨N, hNlower, hNupper, hcrt⟩ :=
    exists_bounded_prime_crt_shift P a (y ^ 2)
      (fun p hp => (hcover.1 p hp).1)
  refine ⟨N, hNlower, hNupper, ?_⟩
  intro h hh
  obtain ⟨p, hpP, q, hqP, hpq, hpprime, hqprime, hpy, hqy,
    hphit, hqhit⟩ := double_cover_has_two_distinct_primes hcover hh
  have hpdiv : p ∣ N + h :=
    shifted_divisor_of_cover_residue (hcrt p hpP) hphit
  have hqdiv : q ∣ N + h :=
    shifted_divisor_of_cover_residue (hcrt q hqP) hqhit
  have hproduct : p * q ≤ y ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hpy hqy
  have hproper : p * q < N + h :=
    lt_of_le_of_lt hproduct (lt_of_lt_of_le hNlower (Nat.le_add_right N h))
  exact omega_ge_three_of_distinct_prime_dvd_lt
    hpprime hqprime hpq hpdiv hqdiv hproper

/-- Equivalent interval formulation using precisely the official positive
almost-prime predicate; neither primes nor semiprimes survive. -/
theorem double_cover_forces_almost_prime_free_interval
    {y : ℕ} {P : Finset ℕ} {a : ℕ → ℕ}
    (hcover : PrimeDoubleCover y P a) :
    ∃ N : ℕ, y ^ 2 < N ∧ N ≤ y ^ 2 + ∏ p ∈ P, p ∧
      ∀ h ∈ Finset.Icc 1 y, ¬ AlmostPrime (N + h) := by
  obtain ⟨N, hlower, hupper, hthree⟩ :=
    double_cover_forces_three_factor_interval hcover
  refine ⟨N, hlower, hupper, ?_⟩
  intro h hh halmost
  change 0 < N + h ∧ Ω (N + h) ≤ 2 at halmost
  have hge := hthree h hh
  omega

/-- Every sufficiently covered point either has a genuine selected square
hit or has two distinct broad prime hits.  This dichotomy is exactly what
distinguishes the almost-prime problem from the prime-only #689 covering. -/
theorem square_double_cover_has_square_or_distinct_primes
    {y h : ℕ} {P squared : Finset ℕ} {a : ℕ → ℕ}
    (hcover : PrimeSquareDoubleCover y P squared a)
    (hh : h ∈ Finset.Icc 1 y) :
    (∃ p ∈ squared, p.Prime ∧ p ≤ y ∧ a p ≡ h [MOD p ^ 2]) ∨
      (∃ p ∈ P, ∃ q ∈ P,
        p ≠ q ∧ p.Prime ∧ q.Prime ∧ p ≤ y ∧ q ≤ y ∧
        a p ≡ h [MOD p] ∧ a q ≡ h [MOD q]) := by
  classical
  by_cases hsquare : ∃ p ∈ squared, a p ≡ h [MOD p ^ 2]
  · obtain ⟨p, hp, hhit⟩ := hsquare
    obtain ⟨hpprime, hpbound⟩ := hcover.1 p (hcover.2.1 hp)
    exact Or.inl ⟨p, hp, hpprime, hpbound, hhit⟩
  · have hzero :
        (squared.filter fun p => a p ≡ h [MOD p ^ 2]).card = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hpositive
      obtain ⟨p, hp⟩ := Finset.card_pos.mp hpositive
      obtain ⟨hpsquared, hphit⟩ := Finset.mem_filter.mp hp
      exact hsquare ⟨p, hpsquared, hphit⟩
    have hcard : 1 < (P.filter fun p => a p ≡ h [MOD p]).card := by
      have htwo := hcover.2.2 h hh
      omega
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hcard
    obtain ⟨hpP, hpclass⟩ := Finset.mem_filter.mp hp
    obtain ⟨hqP, hqclass⟩ := Finset.mem_filter.mp hq
    obtain ⟨hpprime, hpy⟩ := hcover.1 p hpP
    obtain ⟨hqprime, hqy⟩ := hcover.1 q hqP
    exact Or.inr ⟨p, hpP, q, hqP, hpq, hpprime, hqprime,
      hpy, hqy, hpclass, hqclass⟩

/-- The COMPLETE mixed-conductor interval bridge, retaining the true CRT cost
`∏ p^(1 or 2)`.  Nested `p²` hits and two distinct broad-prime hits are both
handled; thus the prime-only #689 finite obstruction is not wrongly imposed
on genuine almost-prime square covers. -/
theorem square_double_cover_forces_three_factor_interval
    {y : ℕ} {P squared : Finset ℕ} {a : ℕ → ℕ}
    (hcover : PrimeSquareDoubleCover y P squared a) :
    ∃ N : ℕ, y ^ 2 < N ∧
      N ≤ y ^ 2 + ∏ p ∈ P, selectedPrimePower squared p ∧
      ∀ h ∈ Finset.Icc 1 y, 3 ≤ Ω (N + h) := by
  classical
  have hpositive : ∀ p ∈ P, 0 < selectedPrimePower squared p := by
    intro p hp
    exact pow_pos (hcover.1 p hp).1.pos _
  have hpair : Set.Pairwise (↑P : Set ℕ)
      (fun p q : ℕ => Nat.Coprime
        (selectedPrimePower squared p) (selectedPrimePower squared q)) := by
    intro p hp q hq hpq
    exact Nat.Coprime.pow _ _
      ((Nat.coprime_primes (hcover.1 p hp).1 (hcover.1 q hq).1).mpr hpq)
  obtain ⟨N, hlower, hupper, hcrt⟩ :=
    exists_bounded_coprime_crt_shift P (selectedPrimePower squared)
      a (y ^ 2) hpositive hpair
  refine ⟨N, hlower, hupper, ?_⟩
  intro h hh
  rcases square_double_cover_has_square_or_distinct_primes hcover hh with
    ⟨p, hpsquared, hpprime, hpbound, hphit⟩ |
    ⟨p, hpP, q, hqP, hpq, hpprime, hqprime, hpbound, hqbound,
      hphit, hqhit⟩
  · have hpP : p ∈ P := hcover.2.1 hpsquared
    have hsquared : p ^ 2 ∣ N + a p := by
      simpa [selectedPrimePower, selectedPrimeExponent, hpsquared] using
        hcrt p hpP
    have hdivides : p ^ 2 ∣ N + h :=
      shifted_divisor_of_cover_residue hsquared hphit
    have hbound : p ^ 2 ≤ y ^ 2 := by
      simpa [pow_two] using Nat.mul_le_mul hpbound hpbound
    have hproper : p ^ 2 < N + h :=
      lt_of_le_of_lt hbound (lt_of_lt_of_le hlower (Nat.le_add_right N h))
    exact omega_ge_three_of_prime_square_dvd_lt hpprime hdivides hproper
  · have hpconductor : p ∣ selectedPrimePower squared p := by
      unfold selectedPrimePower selectedPrimeExponent
      split_ifs <;> simp [pow_two]
    have hqconductor : q ∣ selectedPrimePower squared q := by
      unfold selectedPrimePower selectedPrimeExponent
      split_ifs <;> simp [pow_two]
    have hpdiv : p ∣ N + h :=
      shifted_divisor_of_cover_residue
        (dvd_trans hpconductor (hcrt p hpP)) hphit
    have hqdiv : q ∣ N + h :=
      shifted_divisor_of_cover_residue
        (dvd_trans hqconductor (hcrt q hqP)) hqhit
    have hproduct : p * q ≤ y ^ 2 := by
      simpa [pow_two] using Nat.mul_le_mul hpbound hqbound
    have hproper : p * q < N + h :=
      lt_of_le_of_lt hproduct (lt_of_lt_of_le hlower (Nat.le_add_right N h))
    exact omega_ge_three_of_distinct_prime_dvd_lt
      hpprime hqprime hpq hpdiv hqdiv hproper

/-- An actual almost-prime-free interval produces a gap in precisely the
upstream `Nat.nth` sequence, with the predecessor index bounded by the
interval's location.  This is the finite bridge needed before introducing
the logarithmic-cost normalization. -/
theorem almost_prime_free_interval_forces_sequence_gap
    {N y : ℕ} (hN : 0 < N)
    (hfree : ∀ h ∈ Finset.Icc 1 y, ¬ AlmostPrime (N + h)) :
    ∃ k : ℕ,
      k ≤ N ∧ Nat.nth AlmostPrime k ≤ N ∧
      N + y < Nat.nth AlmostPrime (k + 1) ∧
      y < Nat.nth AlmostPrime (k + 1) - Nat.nth AlmostPrime k := by
  classical
  have hcount : 0 < Nat.count AlmostPrime (N + 1) := by
    rw [Nat.count_eq_card_filter_range]
    apply Finset.card_pos.mpr
    refine ⟨1, Finset.mem_filter.mpr ⟨?_, almostPrime_one⟩⟩
    exact Finset.mem_range.mpr (by omega)
  let k := Nat.count AlmostPrime (N + 1) - 1
  have hk : k + 1 = Nat.count AlmostPrime (N + 1) := by
    dsimp [k]
    omega
  have hindex : k ≤ N := by
    have hbound : Nat.count AlmostPrime (N + 1) ≤ N + 1 :=
      Nat.count_le AlmostPrime
    omega
  have hprevious : Nat.nth AlmostPrime k ≤ N := by
    have hless : k < Nat.count AlmostPrime (N + 1) := by omega
    have hnth := Nat.nth_lt_of_lt_count hless
    omega
  have hnextlower : N < Nat.nth AlmostPrime (k + 1) := by
    have hnext := Nat.le_nth_count almostPrime_infinite (N + 1)
    change N + 1 ≤ Nat.nth AlmostPrime (Nat.count AlmostPrime (N + 1)) at hnext
    rw [← hk] at hnext
    omega
  have hnextmember : AlmostPrime (Nat.nth AlmostPrime (k + 1)) :=
    Nat.nth_mem_of_infinite almostPrime_infinite (k + 1)
  have hnext : N + y < Nat.nth AlmostPrime (k + 1) := by
    by_contra hnot
    have hupper : Nat.nth AlmostPrime (k + 1) ≤ N + y :=
      Nat.le_of_not_gt hnot
    let offset := Nat.nth AlmostPrime (k + 1) - N
    have hoffset : offset ∈ Finset.Icc 1 y := by
      apply Finset.mem_Icc.mpr
      dsimp [offset]
      omega
    have heq : N + offset = Nat.nth AlmostPrime (k + 1) := by
      dsimp [offset]
      omega
    exact hfree offset hoffset (heq.symm ▸ hnextmember)
  refine ⟨k, hindex, hprevious, hnext, ?_⟩
  omega

/-- Composition of the genuine mixed-conductor covering, its true one-period
CRT shift, and an actual gap in the exact original almost-prime sequence. -/
theorem square_double_cover_forces_original_sequence_gap
    {y : ℕ} {P squared : Finset ℕ} {a : ℕ → ℕ}
    (hcover : PrimeSquareDoubleCover y P squared a) :
    ∃ N k : ℕ,
      y ^ 2 < N ∧ N ≤ y ^ 2 + ∏ p ∈ P, selectedPrimePower squared p ∧
      k ≤ N ∧ Nat.nth AlmostPrime k ≤ N ∧
      N + y < Nat.nth AlmostPrime (k + 1) ∧
      y < Nat.nth AlmostPrime (k + 1) - Nat.nth AlmostPrime k := by
  obtain ⟨N, hlower, hupper, hthree⟩ :=
    square_double_cover_forces_three_factor_interval hcover
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hlower
  have hfree : ∀ h ∈ Finset.Icc 1 y, ¬ AlmostPrime (N + h) := by
    intro h hh halmost
    change 0 < N + h ∧ Ω (N + h) ≤ 2 at halmost
    have hlarge := hthree h hh
    omega
  obtain ⟨k, hk, hprevious, hnext, hgap⟩ :=
    almost_prime_free_interval_forces_sequence_gap hN hfree
  exact ⟨N, k, hlower, hupper, hk, hprevious, hnext, hgap⟩

/-- The exact finite prime family used by the first genuine nested-square
counterexample to a prime-only transfer obstruction. -/
def sevenCoveringPrimes : Finset ℕ := {2, 3, 5, 7}

/-- One coherent square residue is chosen for each of the four prime bases. -/
def sevenCoveringResidue (p : ℕ) : ℕ :=
  if p = 2 then 1 else if p = 3 then 6 else if p = 5 then 2 else 4

/-- A true almost-prime covering already exists at interval length seven,
because square divisibility supplies a legitimate repeated prime factor. -/
theorem seven_square_double_cover :
    PrimeSquareDoubleCover 7 sevenCoveringPrimes
      sevenCoveringPrimes sevenCoveringResidue := by
  constructor
  · intro p hp
    simp [sevenCoveringPrimes] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  · constructor
    · exact Finset.Subset.refl _
    · intro h hh
      obtain ⟨hlower, hupper⟩ := Finset.mem_Icc.mp hh
      interval_cases h <;> decide

/-- The exact conductor includes every selected square, so the certificate
does not silently undercount its CRT logarithmic cost. -/
theorem seven_square_conductor :
    (∏ p ∈ sevenCoveringPrimes,
      selectedPrimePower sevenCoveringPrimes p) = 44100 := by
  decide

/-- The explicit independently supplied CRT representative satisfies all four
genuine square congruences and lies within the proved one-period interval. -/
theorem seven_square_explicit_crt_shift :
    7 ^ 2 < 40323 ∧ 40323 ≤ 7 ^ 2 + 44100 ∧
      ∀ p ∈ sevenCoveringPrimes,
        p ^ 2 ∣ 40323 + sevenCoveringResidue p := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro p hp
  simp [sevenCoveringPrimes] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> decide

/-- The original closed prime set has exactly the classical primorial as its
CRT product; endpoint zero does not contribute a prime. -/
theorem closed_prime_product_eq_primorial (y : ℕ) :
    (∏ p ∈ ((Finset.Icc 1 y).filter Nat.Prime), p) = primorial y := by
  unfold primorial
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range,
    Nat.lt_succ_iff]
  constructor
  · rintro ⟨⟨_, hbound⟩, hprime⟩
    exact ⟨hbound, hprime⟩
  · rintro ⟨hbound, hprime⟩
    exact ⟨⟨hprime.one_le, hbound⟩, hprime⟩

/-- A single exact historical #689 covering supplies the distinct-prime
covering predicate required by the finite #1139 bridge. -/
theorem prime_double_cover_of_full_prime_cover
    {y : ℕ} {a : ℕ → ℕ}
    (hcover : ∀ h ∈ Finset.Icc 1 y,
      2 ≤ ((Finset.Icc 1 y).filter
        fun p => p.Prime ∧ a p ≡ h [MOD p]).card) :
    PrimeDoubleCover y ((Finset.Icc 1 y).filter Nat.Prime) a := by
  constructor
  · intro p hp
    obtain ⟨hinterval, hprime⟩ := Finset.mem_filter.mp hp
    exact ⟨hprime, (Finset.mem_Icc.mp hinterval).2⟩
  · intro h hh
    simpa [Finset.filter_filter, and_assoc] using hcover h hh

/-- EXACT eventual consequence of the historical #689 covering proposition:
for every sufficiently large length there is a genuine almost-prime-free
interval whose location is bounded by `y² + primorial y`.  This does not
claim the sublinear logarithmic cost required to solve #1139. -/
theorem eventual_three_factor_intervals_of_eventual_prime_double_cover
    (hcover : ∀ᶠ y : ℕ in Filter.atTop, ∃ a : ℕ → ℕ,
      ∀ h ∈ Finset.Icc 1 y,
        2 ≤ ((Finset.Icc 1 y).filter
          fun p => p.Prime ∧ a p ≡ h [MOD p]).card) :
    ∀ᶠ y : ℕ in Filter.atTop,
      ∃ N : ℕ, y ^ 2 < N ∧ N ≤ y ^ 2 + primorial y ∧
        ∀ h ∈ Finset.Icc 1 y, 3 ≤ Ω (N + h) := by
  filter_upwards [hcover] with y hy
  obtain ⟨a, ha⟩ := hy
  obtain ⟨N, hlower, hupper, hthree⟩ :=
    double_cover_forces_three_factor_interval
      (prime_double_cover_of_full_prime_cover ha)
  rw [closed_prime_product_eq_primorial] at hupper
  exact ⟨N, hlower, hupper, hthree⟩

/-- The prime-subset covering is monotone when all missing primes up to the
same endpoint are restored with arbitrary preassigned residues. -/
theorem double_cover_extends_all_primes
    {y : ℕ} {P : Finset ℕ} {a : ℕ → ℕ}
    (hcover : PrimeDoubleCover y P a) :
    ∀ h ∈ Finset.Icc 1 y,
      2 ≤ ((Finset.Icc 1 y).filter
        fun p => p.Prime ∧ a p ≡ h [MOD p]).card := by
  intro h hh
  refine le_trans (hcover.2 h hh) (Finset.card_le_card ?_)
  intro p hp
  obtain ⟨hpP, hpclass⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpprime, hpbound⟩ := hcover.1 p hpP
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hpprime.one_le, hpbound⟩, hpprime, hpclass⟩


end Erdos1139
