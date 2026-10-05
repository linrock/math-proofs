module

public import Integration1054

@[expose] public section


/-!
# Equivalence with the Formal Conjectures `Nat.nth` formulation of Erdős #1054

The Formal Conjectures statement defines $f(n)$ using zero-padded `Nat.nth`
divisor prefixes and `Nat.find`, whereas the divisor-prefix reduction in
`Erdos1054Conditional` uses bounded sorted-list prefixes and `sInf`. This
module proves that the two definitions agree at every natural number $n$,
including the zero modulus and prefix lengths exceeding the number of divisors.
-/

open Finset Filter Asymptotics

namespace Erdos1054.OriginalNth

noncomputable def prefixSum (m k : ℕ) : ℕ :=
  ∑ i ∈ Finset.Iio k, Nat.nth (fun d => d ∈ m.divisors) i

def Witness (n m : ℕ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ n = prefixSum m k

noncomputable def f (n : ℕ) : ℕ :=
  open scoped Classical in
  if h : ∃ m : ℕ, Witness n m then
    Nat.find h
  else 0

/-- Summing zero-padded list lookups is exactly summing its truncated prefix. -/
theorem sum_getD_eq_take_sum (l : List ℕ) (k : ℕ) :
    (∑ i ∈ Finset.range k, l.getD i 0) = (l.take k).sum := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero,
        List.take_succ_cons, List.sum_cons]
      rw [ih]
      omega

/-- The official zero-padded `Nat.nth` sum equals the supported sorted-list
prefix for every modulus and every prefix length, even beyond the divisor
count. -/
theorem prefixSum_eq_sorted (m k : ℕ) :
    prefixSum m k = _root_.Represented.prefixSumDivisors m k := by
  classical
  let hfinite : {d : ℕ | d ∈ m.divisors}.Finite :=
    Set.finite_mem_finset m.divisors
  have hfinset : hfinite.toFinset = m.divisors := by
    ext d
    simp
  unfold prefixSum _root_.Represented.prefixSumDivisors
  rw [Nat.Iio_eq_range]
  simp_rw [Nat.nth_eq_getD_sort hfinite]
  rw [hfinset]
  exact sum_getD_eq_take_sum _ k

/-- Prefix lengths greater than the number of divisors contribute only zeros;
the canonical supported prefix is their minimum with the divisor count. -/
theorem sorted_prefix_min_card (m k : ℕ) :
    _root_.Represented.prefixSumDivisors m k =
      _root_.Represented.prefixSumDivisors m (min k m.divisors.card) := by
  unfold _root_.Represented.prefixSumDivisors
  have htake := List.take_eq_take_min (l := m.divisors.sort (· ≤ ·)) (i := k)
  simpa only [Finset.length_sort] using congrArg List.sum htake

/-- For a positive modulus, the official unrestricted-prefix witness is
equivalent to the supported positive, divisor-count-bounded witness. -/
theorem witness_iff_supported {n m : ℕ} (hm : 0 < m) :
    Witness n m ↔ _root_.Represented.IsRep n m := by
  constructor
  · rintro ⟨k, hk, hn⟩
    have hcard : 0 < m.divisors.card := Finset.card_pos.mpr
      ⟨1, Nat.one_mem_divisors.mpr (Nat.ne_of_gt hm)⟩
    refine ⟨min k m.divisors.card, le_min hk hcard,
      min_le_right _ _, ?_⟩
    calc
      n = prefixSum m k := hn
      _ = _root_.Represented.prefixSumDivisors m k := prefixSum_eq_sorted m k
      _ = _root_.Represented.prefixSumDivisors m
        (min k m.divisors.card) := sorted_prefix_min_card m k
  · rintro ⟨k, hk, _, hn⟩
    exact ⟨k, hk, hn.trans (prefixSum_eq_sorted m k).symm⟩

/-- The modulus-zero official witness exists exactly at integer zero. -/
theorem witness_zero_modulus_iff (n : ℕ) : Witness n 0 ↔ n = 0 := by
  constructor
  · rintro ⟨k, _, hn⟩
    simpa [prefixSum, Nat.nth, Nat.divisors_zero] using hn
  · rintro rfl
    refine ⟨1, by omega, ?_⟩
    simp [prefixSum, Nat.nth, Nat.divisors_zero]

/-- The two representation predicates really differ at zero; this prevents a
spurious unconditional equivalence. -/
theorem zero_is_officially_witnessed : Witness 0 0 :=
  (witness_zero_modulus_iff 0).mpr rfl

/-- A positive represented integer cannot use the official zero modulus. -/
theorem witness_modulus_pos {n m : ℕ} (hn : 0 < n)
    (h : Witness n m) : 0 < m := by
  by_contra hm
  have hmzero : m = 0 := by omega
  subst m
  have := (witness_zero_modulus_iff n).mp h
  omega

/-- For positive integers, official witnesses are exactly the supported
positive-modulus representation witnesses. -/
theorem witness_iff_positive_supported {n : ℕ} (hn : 0 < n) (m : ℕ) :
    Witness n m ↔ 1 ≤ m ∧ _root_.Represented.IsRep n m := by
  constructor
  · intro h
    have hm := witness_modulus_pos hn h
    exact ⟨hm, (witness_iff_supported hm).mp h⟩
  · rintro ⟨hm, hrep⟩
    exact (witness_iff_supported hm).mpr hrep

/-- Zero has no positive-modulus supported representation. -/
theorem not_supported_zero : 0 ∉ _root_.Represented.R := by
  rw [_root_.Represented.mem_R_iff_exists_F]
  rintro ⟨e, d, he, hd, hzero⟩
  have hlower := _root_.Represented.F_ge e d he hd
  omega

/-- The literal official `Nat.find` minimizer agrees at every integer with the
supported sorted-prefix `sInf` minimizer, including the exceptional zero case. -/
theorem f_eq_supported (n : ℕ) : f n = _root_.Represented.f n := by
  classical
  by_cases hn : n = 0
  · subst n
    have hofficial : ∃ m, Witness 0 m := ⟨0, zero_is_officially_witnessed⟩
    have hfzero : f 0 = 0 := by
      unfold f
      rw [dite_eq_left hofficial]
      exact (Nat.find_eq_zero hofficial).mpr zero_is_officially_witnessed
    have hempty : {m : ℕ | 1 ≤ m ∧ _root_.Represented.IsRep 0 m} = ∅ := by
      ext m
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hm
      exact not_supported_zero ⟨m, hm⟩
    rw [hfzero, _root_.Represented.f, hempty]
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    unfold f _root_.Represented.f
    split_ifs with hofficial
    · have hsupported :
          {m : ℕ | 1 ≤ m ∧ _root_.Represented.IsRep n m}.Nonempty := by
        obtain ⟨m, hm⟩ := hofficial
        exact ⟨m, (witness_iff_positive_supported hnpos m).mp hm⟩
      apply Nat.le_antisymm
      · have hminimum :
            1 ≤ sInf {m : ℕ | 1 ≤ m ∧ _root_.Represented.IsRep n m} ∧
              _root_.Represented.IsRep n
                (sInf {m : ℕ | 1 ≤ m ∧ _root_.Represented.IsRep n m}) := by
          simpa only [Set.mem_ofPred_eq] using Nat.sInf_mem hsupported
        exact Nat.find_min' hofficial
          ((witness_iff_positive_supported hnpos _).mpr hminimum)
      · apply Nat.sInf_le
        exact (witness_iff_positive_supported hnpos _).mp
          (Nat.find_spec hofficial)
    · have hempty :
          {m : ℕ | 1 ≤ m ∧ _root_.Represented.IsRep n m} = ∅ := by
        ext m
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hm
        exact hofficial ⟨m, (witness_iff_positive_supported hnpos m).mpr hm⟩
      rw [hempty]
      simp

/-- The local definition is extensionally the literal zero-padded
`Nat.nth`/`Nat.find` body in the official formal-conjectures statement. -/
theorem f_eq_official_formula (n : ℕ) :
    f n =
      (open scoped Classical in
        if h : ∃ m : ℕ, ∃ k : ℕ, 1 ≤ k ∧
            n = ∑ i ∈ Finset.Iio k,
              Nat.nth (fun d => d ∈ m.divisors) i then
          Nat.find h
        else 0) := by
  unfold f Witness prefixSum
  rfl

/-- The literal official minimizer also agrees with the exact comparator's
cofactor/cutoff minimizer at every integer, not merely represented ones. -/
theorem f_eq_comparator (n : ℕ) : f n = _root_.Erdos1054.f n := by
  rw [f_eq_supported, _root_.Erdos1054.f_eq]

/-- The exact positive-density statement with the official `Nat.nth`/`Nat.find`
function, retaining almost-all Goldbach as its sole explicit theorem input. -/
theorem official_main_of_goldbach
    (hGoldbach : _root_.Erdos1054.DensityZero
      _root_.Erdos1054.notSumOfTwoPrimes)
    (A : ℕ) (hA : 1 ≤ A) :
    _root_.Erdos1054.PositiveLowerDensity
      (fun n => n ∈ _root_.Represented.R ∧ A * n < f n) := by
  simpa only [_root_.Erdos1054.represented_iff_memR,
    _root_.Erdos1054.f_eq, f_eq_supported] using
    _root_.Erdos1054.erdos1054_main_of_goldbach hGoldbach A hA

/-- The first official Erdős #1054 question has negative answer for the exact
`Nat.nth`/`Nat.find` function. -/
theorem official_not_littleO_of_goldbach
    (hGoldbach : _root_.Erdos1054.DensityZero
      _root_.Erdos1054.notSumOfTwoPrimes) :
    ¬ (fun n : ℕ => (f n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  intro hlittle
  have hevent : ∀ᶠ n : ℕ in atTop,
      ‖(f n : ℝ)‖ ≤ (1 : ℝ) * ‖(n : ℝ)‖ :=
    (Asymptotics.isLittleO_iff.mp hlittle) (by norm_num)
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨B, hB⟩ := hevent
  obtain ⟨n, hBn, _, hlarge⟩ :=
    _root_.Erdos1054.erdos1054_late_witness_of_goldbach
      hGoldbach 1 B (by norm_num)
  have hbound := hB n hBn
  have hfnnonneg : (0 : ℝ) ≤ (f n : ℝ) := by positivity
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
  rw [Real.norm_of_nonneg hfnnonneg,
    Real.norm_of_nonneg hnnonneg, one_mul] at hbound
  have hstrict : (n : ℝ) < (f n : ℝ) := by
    rw [f_eq_comparator]
    exact_mod_cast (by simpa using hlarge)
  exact (not_le_of_gt hstrict) hbound

/-- The second official Erdős #1054 question also has negative answer for the
literal `Nat.nth`/`Nat.find` function.  Both the density-one quantifier and
the little-o filter on the set subtype retain their original meanings. -/
theorem official_not_almost_everywhere_littleO_of_goldbach
    (hGoldbach : _root_.Erdos1054.DensityZero
      _root_.Erdos1054.notSumOfTwoPrimes) :
    ¬ ∃ S : Set ℕ, _root_.Erdos1054.HasDensityOne S ∧
      (fun n : S => (f (n : ℕ) : ℝ)) =o[atTop]
        (fun n : S => ((n : ℕ) : ℝ)) := by
  simpa only [f_eq_comparator] using
    _root_.Erdos1054.erdos1054_not_almost_everywhere_littleO_of_goldbach
      hGoldbach

/-- The exact extended-real limsup formulation for the literal official
`Nat.nth`/`Nat.find` function; no representation convention is weakened. -/
theorem official_limsup_top_of_goldbach
    (hGoldbach : _root_.Erdos1054.DensityZero
      _root_.Erdos1054.notSumOfTwoPrimes) :
    atTop.limsup (fun n : ℕ => (f n : EReal) / n) = ⊤ := by
  simpa only [f_eq_supported, _root_.Erdos1054.f_eq] using
    _root_.Erdos1054.erdos1054_limsup_top_of_goldbach hGoldbach

/-- The complete third official proposition, including its redundant
existential quantifier over a density-one set. -/
theorem official_limsup_exists_density_one_of_goldbach
    (hGoldbach : _root_.Erdos1054.DensityZero
      _root_.Erdos1054.notSumOfTwoPrimes) :
    ∃ S : Set ℕ, _root_.Erdos1054.HasDensityOne S ∧
      atTop.limsup (fun n : ℕ => (f n : EReal) / n) = ⊤ :=
  ⟨Set.univ, _root_.Erdos1054.hasDensityOne_univ,
    official_limsup_top_of_goldbach hGoldbach⟩

end Erdos1054.OriginalNth
