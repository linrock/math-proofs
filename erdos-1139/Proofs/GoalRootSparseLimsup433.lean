module

public import SparseCoverBridge433

@[expose] public section


/-!
# The exact infinite-limsup consequence of sparse mixed square coverings

The existing finite CRT bridge proves that any genuine mixed prime/prime-square
double covering creates a gap in the exact historical almost-prime sequence.
This file closes the previously missing asymptotic and extended-real bridge:
arbitrarily sparse actual CRT conductors imply the literal original Erdős
#1139 assertion.  The covering-existence proposition remains an explicit
hypothesis; no analytic prime-pattern theorem or full solution is asserted.
-/

open Finset Filter
open scoped ArithmeticFunction.Omega Topology

namespace Erdos1139

/-- Arbitrarily long nested-prime-square covers whose *actual* CRT location
has arbitrarily small logarithmic cost per covered integer.  The polynomial
baseline, successor, selected square exponents, distinct prime support, and
exact closed target interval are all retained. -/
def HasArbitrarilySparseSquareCovers : Prop :=
  ∀ (A : ℝ), 0 < A → ∀ Y₀ : ℕ,
    ∃ (y : ℕ) (P squared : Finset ℕ) (a : ℕ → ℕ),
      Y₀ ≤ y ∧ PrimeSquareDoubleCover y P squared a ∧
        A * Real.log
          (((y ^ 2 + ∏ p ∈ P, selectedPrimePower squared p) + 1 : ℕ) : ℝ)
          ≤ (y : ℝ)

/-- The sparse-cover hypothesis forces genuinely late, arbitrarily large
normalized gaps in the exact `Nat.nth` almost-prime sequence. -/
theorem arbitrarily_large_normalized_gaps_of_sparse_square_covers
    (hsparse : HasArbitrarilySparseSquareCovers)
    (A : ℝ) (hA : 0 < A) (K : ℕ) :
    ∃ k : ℕ, K ≤ k ∧
      A <
        ((Nat.nth AlmostPrime (k + 1) : ℝ) -
          (Nat.nth AlmostPrime k : ℝ)) /
          Real.log ((k : ℝ) + 1) := by
  obtain ⟨y, P, squared, a, hy, hcover, hcost⟩ :=
    hsparse A hA (Nat.nth AlmostPrime (K + 2) + 1)
  obtain ⟨N, k, _hlower, hupper, hkN, _hprevious, _hnext, hgap⟩ :=
    square_double_cover_forces_original_sequence_gap hcover
  have hylarge : Nat.nth AlmostPrime (K + 2) < y := by omega
  have hgapupper :
      Nat.nth AlmostPrime (k + 1) - Nat.nth AlmostPrime k ≤
        Nat.nth AlmostPrime (k + 1) := Nat.sub_le _ _
  have hnthlarge :
      Nat.nth AlmostPrime (K + 2) < Nat.nth AlmostPrime (k + 1) := by
    omega
  have hindexlarge : K + 2 < k + 1 :=
    (Nat.nth_lt_nth almostPrime_infinite).mp hnthlarge
  have hkpositive : 0 < k := by omega
  have hkinitial : K ≤ k := by omega
  refine ⟨k, hkinitial, ?_⟩
  have hlocation :
      k + 1 ≤ (y ^ 2 + ∏ p ∈ P, selectedPrimePower squared p) + 1 := by
    omega
  have hcast :
      (k : ℝ) + 1 ≤
        (((y ^ 2 + ∏ p ∈ P, selectedPrimePower squared p) + 1 : ℕ) : ℝ) := by
    exact_mod_cast hlocation
  have hsmallpositive : 0 < (k : ℝ) + 1 := by positivity
  have hlargepositive :
      0 < (((y ^ 2 + ∏ p ∈ P, selectedPrimePower squared p) + 1 : ℕ) : ℝ) := by
    positivity
  have hlog := Real.strictMonoOn_log.monotoneOn
    hsmallpositive hlargepositive hcast
  have hscaled : A * Real.log ((k : ℝ) + 1) ≤ (y : ℝ) :=
    (mul_le_mul_of_nonneg_left hlog hA.le).trans hcost
  have hdenominator : 0 < Real.log ((k : ℝ) + 1) := by
    apply Real.log_pos
    have hsuccessor : 1 < k + 1 := by omega
    exact_mod_cast hsuccessor
  have hmonotone : Nat.nth AlmostPrime k ≤ Nat.nth AlmostPrime (k + 1) :=
    (Nat.nth_monotone almostPrime_infinite) (by omega)
  have hgapreal :
      (y : ℝ) < (Nat.nth AlmostPrime (k + 1) : ℝ) -
        (Nat.nth AlmostPrime k : ℝ) := by
    have hcastgap : (y : ℝ) <
        (Nat.nth AlmostPrime (k + 1) - Nat.nth AlmostPrime k : ℕ) := by
      exact_mod_cast hgap
    simpa [Nat.cast_sub hmonotone] using hcastgap
  exact (lt_div_iff₀ hdenominator).mpr (hscaled.trans_lt hgapreal)

/-- Exact upstream Erdős #1139 conclusion from one explicit sparse mixed-cover
hypothesis.  The almost-prime predicate, index, logarithmic denominator, and
extended-real limsup are definitionally identical to the historical formal
statement.  This is conditional on actual sparse coverings, not a claim that
the proposed analytic construction has been formalized. -/
theorem original_normalized_limsup_top_of_sparse_square_covers
    (hsparse : HasArbitrarilySparseSquareCovers) :
    Filter.atTop.limsup
      (fun k : ℕ =>
        (((Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) (k + 1) : ℝ) -
           (Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) k : ℝ)) /
          Real.log ((k : ℝ) + 1) : EReal)) = ⊤ := by
  change
    Filter.atTop.limsup
      (fun k : ℕ =>
        (((Nat.nth AlmostPrime (k + 1) : ℝ) -
           (Nat.nth AlmostPrime k : ℝ)) /
          Real.log ((k : ℝ) + 1) : EReal)) = ⊤
  apply top_unique
  apply (le_limsup_iff).2
  intro b hb
  obtain ⟨a, hba, _⟩ := EReal.exists_between_coe_real hb
  let A : ℝ := max a 1
  have hApositive : 0 < A := lt_of_lt_of_le (by norm_num) (le_max_right a 1)
  have haA : a ≤ A := le_max_left a 1
  apply Filter.frequently_atTop.mpr
  intro K
  obtain ⟨k, hk, hratio⟩ :=
    arbitrarily_large_normalized_gaps_of_sparse_square_covers
      hsparse A hApositive K
  refine ⟨k, hk, ?_⟩
  have haratio :
      a <
        ((Nat.nth AlmostPrime (k + 1) : ℝ) -
          (Nat.nth AlmostPrime k : ℝ)) /
          Real.log ((k : ℝ) + 1) := haA.trans_lt hratio
  exact hba.trans (EReal.coe_lt_coe_iff.mpr haratio)

/-- A genuine mixed prime/prime-square double cover with completely
unrestricted prime sizes.  In particular, reserve primes above the covered
interval are permitted, provided their full conductor is paid for. -/
def UnrestrictedPrimeSquareDoubleCover
    (y : ℕ) (P squared : Finset ℕ) (a : ℕ → ℕ) : Prop :=
  (∀ p ∈ P, p.Prime) ∧ squared ⊆ P ∧
    ∀ h ∈ Finset.Icc 1 y,
      2 ≤ (P.filter fun p => a p ≡ h [MOD p]).card +
        (squared.filter fun p => a p ≡ h [MOD p ^ 2]).card

/-- The restricted mixed cover is also an unrestricted cover; only the
redundant prime-size assumptions are discarded. -/
theorem unrestricted_square_cover_of_bounded
    {y : ℕ} {P squared : Finset ℕ} {a : ℕ → ℕ}
    (hcover : PrimeSquareDoubleCover y P squared a) :
    UnrestrictedPrimeSquareDoubleCover y P squared a := by
  exact ⟨fun p hp => (hcover.1 p hp).1, hcover.2⟩

/-- A prime strictly larger than the whole covered interval can genuinely
provide both required hits through its nested square residue.  This concrete
control witnesses that the unrestricted definition is strictly stronger than
the previously formalized bounded-prime interface. -/
theorem unrestricted_square_cover_with_above_interval_prime :
    UnrestrictedPrimeSquareDoubleCover 1 {2} {2} (fun _ : ℕ => 1) := by
  constructor
  · intro p hp
    have hp' : p = 2 := Finset.mem_singleton.mp hp
    simpa [hp'] using (by norm_num : Nat.Prime 2)
  constructor
  · exact fun _ hp => hp
  intro h hh
  have hh' : h = 1 := by simpa using hh
  subst h
  norm_num [Nat.ModEq]

/-- The exact same valid reserve-prime example is forbidden by the old
`p ≤ y` cover hypothesis, proving that the new bridge is not a mere
restatement of the existing finite theorem. -/
theorem above_interval_prime_not_bounded_square_cover :
    ¬ PrimeSquareDoubleCover 1 {2} {2} (fun _ : ℕ => 1) := by
  intro hcover
  have hbound := (hcover.1 2 (by simp)).2
  omega

/-- An unrestricted mixed cover still gives either a true nested square hit
or two genuinely distinct broad-prime hits. -/
theorem unrestricted_square_cover_has_square_or_distinct_primes
    {y h : ℕ} {P squared : Finset ℕ} {a : ℕ → ℕ}
    (hcover : UnrestrictedPrimeSquareDoubleCover y P squared a)
    (hh : h ∈ Finset.Icc 1 y) :
    (∃ p ∈ squared, p.Prime ∧ a p ≡ h [MOD p ^ 2]) ∨
      (∃ p ∈ P, ∃ q ∈ P,
        p ≠ q ∧ p.Prime ∧ q.Prime ∧
        a p ≡ h [MOD p] ∧ a q ≡ h [MOD q]) := by
  classical
  by_cases hsquare : ∃ p ∈ squared, a p ≡ h [MOD p ^ 2]
  · obtain ⟨p, hp, hhit⟩ := hsquare
    exact Or.inl ⟨p, hp, hcover.1 p (hcover.2.1 hp), hhit⟩
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
    exact Or.inr ⟨p, hpP, q, hqP, hpq,
      hcover.1 p hpP, hcover.1 q hqP, hpclass, hqclass⟩

/-- The exact unrestricted CRT bridge.  Starting strictly above the actual
conductor makes every selected two-prime divisor proper, even when some
reserve primes exceed the covered interval.  The resulting location is at
most twice the true mixed prime-power conductor. -/
theorem unrestricted_square_double_cover_forces_three_factor_interval
    {y : ℕ} {P squared : Finset ℕ} {a : ℕ → ℕ}
    (hcover : UnrestrictedPrimeSquareDoubleCover y P squared a) :
    ∃ N : ℕ,
      (∏ p ∈ P, selectedPrimePower squared p) < N ∧
      N ≤ 2 * (∏ p ∈ P, selectedPrimePower squared p) ∧
        ∀ h ∈ Finset.Icc 1 y, 3 ≤ Ω (N + h) := by
  classical
  let Q := ∏ p ∈ P, selectedPrimePower squared p
  have hpositive : ∀ p ∈ P, 0 < selectedPrimePower squared p := by
    intro p hp
    exact pow_pos (hcover.1 p hp).pos _
  have hQ : 0 < Q := by
    dsimp [Q]
    exact Finset.prod_pos hpositive
  have hpair : Set.Pairwise (↑P : Set ℕ)
      (fun p q : ℕ => Nat.Coprime
        (selectedPrimePower squared p) (selectedPrimePower squared q)) := by
    intro p hp q hq hpq
    exact Nat.Coprime.pow _ _
      ((Nat.coprime_primes (hcover.1 p hp) (hcover.1 q hq)).mpr hpq)
  obtain ⟨N, hlower, hupper, hcrt⟩ :=
    exists_bounded_coprime_crt_shift P (selectedPrimePower squared)
      a Q hpositive hpair
  refine ⟨N, hlower, ?_, ?_⟩
  · simpa [two_mul, Q] using hupper
  · intro h hh
    rcases unrestricted_square_cover_has_square_or_distinct_primes
      hcover hh with
      ⟨p, hpsquared, hpprime, hphit⟩ |
      ⟨p, hpP, q, hqP, hpq, hpprime, hqprime, hphit, hqhit⟩
    · have hpP : p ∈ P := hcover.2.1 hpsquared
      have hpconductor : selectedPrimePower squared p ∣ Q := by
        dsimp [Q]
        exact Finset.dvd_prod_of_mem (selectedPrimePower squared) hpP
      have hpsquareQ : p ^ 2 ∣ Q := by
        simpa [selectedPrimePower, selectedPrimeExponent, hpsquared] using
          hpconductor
      have hpsquareN : p ^ 2 ∣ N + a p := by
        simpa [selectedPrimePower, selectedPrimeExponent, hpsquared] using
          hcrt p hpP
      have hdivides : p ^ 2 ∣ N + h :=
        shifted_divisor_of_cover_residue hpsquareN hphit
      have hproper : p ^ 2 < N + h := by
        have hbound : p ^ 2 ≤ Q := Nat.le_of_dvd hQ hpsquareQ
        omega
      exact omega_ge_three_of_prime_square_dvd_lt hpprime hdivides hproper
    · have hpselected : p ∣ selectedPrimePower squared p := by
        unfold selectedPrimePower selectedPrimeExponent
        split_ifs <;> simp [pow_two]
      have hqselected : q ∣ selectedPrimePower squared q := by
        unfold selectedPrimePower selectedPrimeExponent
        split_ifs <;> simp [pow_two]
      have hpconductor : selectedPrimePower squared p ∣ Q := by
        dsimp [Q]
        exact Finset.dvd_prod_of_mem (selectedPrimePower squared) hpP
      have hqconductor : selectedPrimePower squared q ∣ Q := by
        dsimp [Q]
        exact Finset.dvd_prod_of_mem (selectedPrimePower squared) hqP
      have hpQ : p ∣ Q := dvd_trans hpselected hpconductor
      have hqQ : q ∣ Q := dvd_trans hqselected hqconductor
      have hproductQ : p * q ∣ Q :=
        Nat.Prime.dvd_mul_of_dvd_ne hpq hpprime hqprime hpQ hqQ
      have hproductbound : p * q ≤ Q := Nat.le_of_dvd hQ hproductQ
      have hpdiv : p ∣ N + h :=
        shifted_divisor_of_cover_residue
          (dvd_trans hpselected (hcrt p hpP)) hphit
      have hqdiv : q ∣ N + h :=
        shifted_divisor_of_cover_residue
          (dvd_trans hqselected (hcrt q hqP)) hqhit
      have hproper : p * q < N + h := by omega
      exact omega_ge_three_of_distinct_prime_dvd_lt
        hpprime hqprime hpq hpdiv hqdiv hproper

/-- The unrestricted mixed-conductor cover creates a gap in the literal
historical almost-prime sequence at location at most twice its conductor. -/
theorem unrestricted_square_double_cover_forces_original_sequence_gap
    {y : ℕ} {P squared : Finset ℕ} {a : ℕ → ℕ}
    (hcover : UnrestrictedPrimeSquareDoubleCover y P squared a) :
    ∃ N k : ℕ,
      (∏ p ∈ P, selectedPrimePower squared p) < N ∧
      N ≤ 2 * (∏ p ∈ P, selectedPrimePower squared p) ∧
      k ≤ N ∧ Nat.nth AlmostPrime k ≤ N ∧
      N + y < Nat.nth AlmostPrime (k + 1) ∧
      y < Nat.nth AlmostPrime (k + 1) - Nat.nth AlmostPrime k := by
  obtain ⟨N, hlower, hupper, hthree⟩ :=
    unrestricted_square_double_cover_forces_three_factor_interval hcover
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hlower
  have hfree : ∀ h ∈ Finset.Icc 1 y, ¬ AlmostPrime (N + h) := by
    intro h hh halmost
    change 0 < N + h ∧ Ω (N + h) ≤ 2 at halmost
    have hlarge := hthree h hh
    omega
  obtain ⟨k, hk, hprevious, hnext, hgap⟩ :=
    almost_prime_free_interval_forces_sequence_gap hN hfree
  exact ⟨N, k, hlower, hupper, hk, hprevious, hnext, hgap⟩

/-- Exactly the sparse-conductor input used by the proposed matching proof:
prime labels, including reserve primes above the covered interval, have one
coherent prime or prime-square residue and sublinear logarithmic CRT cost. -/
def HasArbitrarilySparseUnrestrictedSquareCovers : Prop :=
  ∀ (A : ℝ), 0 < A → ∀ Y₀ : ℕ,
    ∃ (y : ℕ) (P squared : Finset ℕ) (a : ℕ → ℕ),
      Y₀ ≤ y ∧ UnrestrictedPrimeSquareDoubleCover y P squared a ∧
        A * Real.log
          (((2 * (∏ p ∈ P, selectedPrimePower squared p)) + 1 : ℕ) : ℝ)
          ≤ (y : ℝ)

/-- The natural analytic obstruction is merely `log Q = o(y)` along
arbitrarily long genuine covers, where `Q` is the ACTUAL mixed conductor.
Unlike the CRT-normalized hypothesis above, this proposition contains no
artificial factor of two, successor, or logarithmic baseline. -/
def HasSublinearUnrestrictedConductorCovers : Prop :=
  ∀ (ε : ℝ), 0 < ε → ∀ Y₀ : ℕ,
    ∃ (y : ℕ) (P squared : Finset ℕ) (a : ℕ → ℕ),
      Y₀ ≤ y ∧ UnrestrictedPrimeSquareDoubleCover y P squared a ∧
        Real.log
          ((∏ p ∈ P, selectedPrimePower squared p : ℕ) : ℝ)
          ≤ ε * (y : ℝ)

/-- The manuscript's literal sublinear-actual-conductor condition implies
the exact stronger-looking CRT-location normalization.  The fixed factor
and successor are absorbed using arbitrarily long covered intervals. -/
theorem sparse_unrestricted_covers_of_sublinear_conductors
    (hsublinear : HasSublinearUnrestrictedConductorCovers) :
    HasArbitrarilySparseUnrestrictedSquareCovers := by
  intro A hA Y₀
  obtain ⟨B, hB⟩ := exists_nat_ge (2 * A * Real.log (3 : ℝ))
  have hε : 0 < (1 : ℝ) / (2 * A) := by positivity
  obtain ⟨y, P, squared, a, hy, hcover, hcost⟩ :=
    hsublinear (1 / (2 * A)) hε (max Y₀ B)
  refine ⟨y, P, squared, a,
    le_trans (Nat.le_max_left Y₀ B) hy, hcover, ?_⟩
  let Q : ℕ := ∏ p ∈ P, selectedPrimePower squared p
  have hQnat : 0 < Q := by
    dsimp [Q]
    exact Finset.prod_pos (fun p hp => pow_pos (hcover.1 p hp).pos _)
  have hQreal : 0 < (Q : ℝ) := by exact_mod_cast hQnat
  have hyBnat : B ≤ y := le_trans (Nat.le_max_right Y₀ B) hy
  have hyB : 2 * A * Real.log (3 : ℝ) ≤ (y : ℝ) :=
    hB.trans (by exact_mod_cast hyBnat)
  have hargpositive : 0 < (((2 * Q + 1 : ℕ) : ℝ)) := by positivity
  have hthreepositive : 0 < (3 : ℝ) * (Q : ℝ) := by positivity
  have hargbound : (((2 * Q + 1 : ℕ) : ℝ)) ≤ (3 : ℝ) * (Q : ℝ) := by
    have hnat : 2 * Q + 1 ≤ 3 * Q := by omega
    exact_mod_cast hnat
  have hlog := Real.strictMonoOn_log.monotoneOn
    hargpositive hthreepositive hargbound
  rw [Real.log_mul (by norm_num) (ne_of_gt hQreal)] at hlog
  change Real.log (Q : ℝ) ≤ (1 / (2 * A)) * (y : ℝ) at hcost
  have hvariable : A * Real.log (Q : ℝ) ≤ (y : ℝ) / 2 := by
    calc
      A * Real.log (Q : ℝ) ≤ A * ((1 / (2 * A)) * (y : ℝ)) :=
        mul_le_mul_of_nonneg_left hcost hA.le
      _ = (y : ℝ) / 2 := by field_simp
  have hfixed : A * Real.log (3 : ℝ) ≤ (y : ℝ) / 2 := by
    linarith
  change A * Real.log (((2 * Q + 1 : ℕ) : ℝ)) ≤ (y : ℝ)
  calc
    A * Real.log (((2 * Q + 1 : ℕ) : ℝ)) ≤
        A * (Real.log (3 : ℝ) + Real.log (Q : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog hA.le
    _ = A * Real.log (3 : ℝ) + A * Real.log (Q : ℝ) := by ring
    _ ≤ (y : ℝ) := by linarith

/-- Conversely the normalized CRT-cost proposition implies the literal
sublinear logarithm of the actual selected prime-power conductor. -/
theorem sublinear_conductors_of_sparse_unrestricted_covers
    (hsparse : HasArbitrarilySparseUnrestrictedSquareCovers) :
    HasSublinearUnrestrictedConductorCovers := by
  intro ε hε Y₀
  have hinverse : 0 < (1 : ℝ) / ε := by positivity
  obtain ⟨y, P, squared, a, hy, hcover, hcost⟩ :=
    hsparse (1 / ε) hinverse Y₀
  refine ⟨y, P, squared, a, hy, hcover, ?_⟩
  let Q : ℕ := ∏ p ∈ P, selectedPrimePower squared p
  have hQnat : 0 < Q := by
    dsimp [Q]
    exact Finset.prod_pos (fun p hp => pow_pos (hcover.1 p hp).pos _)
  have hQreal : 0 < (Q : ℝ) := by exact_mod_cast hQnat
  have hargpositive : 0 < (((2 * Q + 1 : ℕ) : ℝ)) := by positivity
  have hargbound : (Q : ℝ) ≤ (((2 * Q + 1 : ℕ) : ℝ)) := by
    have hnat : Q ≤ 2 * Q + 1 := by omega
    exact_mod_cast hnat
  have hlog := Real.strictMonoOn_log.monotoneOn
    hQreal hargpositive hargbound
  change (1 / ε) * Real.log (((2 * Q + 1 : ℕ) : ℝ)) ≤ (y : ℝ) at hcost
  have hscaled : (1 / ε) * Real.log (Q : ℝ) ≤ (y : ℝ) :=
    (mul_le_mul_of_nonneg_left hlog hinverse.le).trans hcost
  change Real.log (Q : ℝ) ≤ ε * (y : ℝ)
  calc
    Real.log (Q : ℝ) = ε * ((1 / ε) * Real.log (Q : ℝ)) := by field_simp
    _ ≤ ε * (y : ℝ) := mul_le_mul_of_nonneg_left hscaled hε.le

/-- The exact published-proof input is equivalent to the exact formal
CRT-location hypothesis; fixed location constants hide no analytic burden. -/
theorem sublinear_unrestricted_conductors_iff_sparse_covers :
    HasSublinearUnrestrictedConductorCovers ↔
      HasArbitrarilySparseUnrestrictedSquareCovers :=
  ⟨sparse_unrestricted_covers_of_sublinear_conductors,
    sublinear_conductors_of_sparse_unrestricted_covers⟩

/-- Unrestricted sparse covers force late gaps larger than every prescribed
multiple of the exact original logarithmic denominator. -/
theorem arbitrarily_large_normalized_gaps_of_unrestricted_sparse_covers
    (hsparse : HasArbitrarilySparseUnrestrictedSquareCovers)
    (A : ℝ) (hA : 0 < A) (K : ℕ) :
    ∃ k : ℕ, K ≤ k ∧
      A <
        ((Nat.nth AlmostPrime (k + 1) : ℝ) -
          (Nat.nth AlmostPrime k : ℝ)) /
          Real.log ((k : ℝ) + 1) := by
  obtain ⟨y, P, squared, a, hy, hcover, hcost⟩ :=
    hsparse A hA (Nat.nth AlmostPrime (K + 2) + 1)
  obtain ⟨N, k, _hlower, hupper, hkN, _hprevious, _hnext, hgap⟩ :=
    unrestricted_square_double_cover_forces_original_sequence_gap hcover
  have hylarge : Nat.nth AlmostPrime (K + 2) < y := by omega
  have hgapupper :
      Nat.nth AlmostPrime (k + 1) - Nat.nth AlmostPrime k ≤
        Nat.nth AlmostPrime (k + 1) := Nat.sub_le _ _
  have hnthlarge :
      Nat.nth AlmostPrime (K + 2) < Nat.nth AlmostPrime (k + 1) := by
    omega
  have hindexlarge : K + 2 < k + 1 :=
    (Nat.nth_lt_nth almostPrime_infinite).mp hnthlarge
  have hkpositive : 0 < k := by omega
  have hkinitial : K ≤ k := by omega
  refine ⟨k, hkinitial, ?_⟩
  have hlocation :
      k + 1 ≤ (2 * (∏ p ∈ P, selectedPrimePower squared p)) + 1 := by
    omega
  have hcast :
      (k : ℝ) + 1 ≤
        (((2 * (∏ p ∈ P, selectedPrimePower squared p)) + 1 : ℕ) : ℝ) := by
    exact_mod_cast hlocation
  have hsmallpositive : 0 < (k : ℝ) + 1 := by positivity
  have hlargepositive :
      0 < (((2 * (∏ p ∈ P, selectedPrimePower squared p)) + 1 : ℕ) : ℝ) := by
    positivity
  have hlog := Real.strictMonoOn_log.monotoneOn
    hsmallpositive hlargepositive hcast
  have hscaled : A * Real.log ((k : ℝ) + 1) ≤ (y : ℝ) :=
    (mul_le_mul_of_nonneg_left hlog hA.le).trans hcost
  have hdenominator : 0 < Real.log ((k : ℝ) + 1) := by
    apply Real.log_pos
    have hsuccessor : 1 < k + 1 := by omega
    exact_mod_cast hsuccessor
  have hmonotone : Nat.nth AlmostPrime k ≤ Nat.nth AlmostPrime (k + 1) :=
    (Nat.nth_monotone almostPrime_infinite) (by omega)
  have hgapreal :
      (y : ℝ) < (Nat.nth AlmostPrime (k + 1) : ℝ) -
        (Nat.nth AlmostPrime k : ℝ) := by
    have hcastgap : (y : ℝ) <
        (Nat.nth AlmostPrime (k + 1) - Nat.nth AlmostPrime k : ℕ) := by
      exact_mod_cast hgap
    simpa [Nat.cast_sub hmonotone] using hcastgap
  exact (lt_div_iff₀ hdenominator).mpr (hscaled.trans_lt hgapreal)

/-- EXACT original Erdős #1139 assertion from the single concrete unrestricted
sparse-cover proposition supplied by the proposed Green--Tao--Kahn argument.
All reserve primes, square exponents, CRT costs, sequence indices, and the
extended-real limsup are retained.  Only the sparse-cover proposition itself
remains unproved; no external analytic theorem is silently introduced. -/
theorem original_normalized_limsup_top_of_unrestricted_sparse_covers
    (hsparse : HasArbitrarilySparseUnrestrictedSquareCovers) :
    Filter.atTop.limsup
      (fun k : ℕ =>
        (((Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) (k + 1) : ℝ) -
           (Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) k : ℝ)) /
          Real.log ((k : ℝ) + 1) : EReal)) = ⊤ := by
  change
    Filter.atTop.limsup
      (fun k : ℕ =>
        (((Nat.nth AlmostPrime (k + 1) : ℝ) -
           (Nat.nth AlmostPrime k : ℝ)) /
          Real.log ((k : ℝ) + 1) : EReal)) = ⊤
  apply top_unique
  apply (le_limsup_iff).2
  intro b hb
  obtain ⟨a, hba, _⟩ := EReal.exists_between_coe_real hb
  let A : ℝ := max a 1
  have hApositive : 0 < A := lt_of_lt_of_le (by norm_num) (le_max_right a 1)
  have haA : a ≤ A := le_max_left a 1
  apply Filter.frequently_atTop.mpr
  intro K
  obtain ⟨k, hk, hratio⟩ :=
    arbitrarily_large_normalized_gaps_of_unrestricted_sparse_covers
      hsparse A hApositive K
  refine ⟨k, hk, ?_⟩
  exact hba.trans (EReal.coe_lt_coe_iff.mpr (haA.trans_lt hratio))

/-- Exact-original #1139 conclusion from precisely the manuscript's natural
`log Q = o(y)` covering proposition, with all prime-power conductor costs and
unrestricted reserve primes retained explicitly. -/
theorem original_normalized_limsup_top_of_sublinear_unrestricted_conductors
    (hsublinear : HasSublinearUnrestrictedConductorCovers) :
    Filter.atTop.limsup
      (fun k : ℕ =>
        (((Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) (k + 1) : ℝ) -
           (Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) k : ℝ)) /
          Real.log ((k : ℝ) + 1) : EReal)) = ⊤ :=
  original_normalized_limsup_top_of_unrestricted_sparse_covers
    (sparse_unrestricted_covers_of_sublinear_conductors hsublinear)


end Erdos1139
