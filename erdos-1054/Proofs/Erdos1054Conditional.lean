module

/- Compatibility-port notice: this file adapts erdos1054/Erdos1054Conditional.lean from https://github.com/antoshashakov/Principia-Math-Solutions at c9910942522fbd3a07c034ac57947f56df6f0f6d to Lean 4.35.0-rc2; see third_party/PRINCIPIA-LICENSE.txt and THIRD_PARTY.md. -/
public import Mathlib

@[expose] public section


/-!
# Unbounded ratios in Erdős Problem 1054 — paper-faithful third-moment formalization

This file formalizes the proof in *Unbounded ratios in Erdős Problem 1054* through its
third-moment argument.  Its mathematical organization follows the paper:

* divisor-prefix parametrization and reflection identity;
* the density-zero lemma for `q ∤ σ(n)` and the thin-set transfer lemma;
* bounded-cofactor exclusion and the sifted-set density estimate;
* the third-moment estimate `T₃(e)`, its `e^(-5/2)` tail, and the large-cofactor bound;
* the almost-all Goldbach representation lemma;
* the positive-lower-density theorem and the resulting unbounded ratio.

## Analytic inputs

* (A1) Reciprocal-prime divergence in the class `-1 mod q` is proved from Mathlib in
  `primes_neg_one_div_diverges`.
* (A2) The Mertens product lower bound is proved in this file as `mertens_third_lower`, using
  the fully formalized Mertens development transplanted from `Erdos1054Complete.lean`.
* (A3) The classical almost-all binary Goldbach theorem is the sole deep external hypothesis.
  It is represented by the single field `DeepInputs.goldbach_ae` and is used only in
  `odd_represented`.

The Tao–Kovač second-moment density-obstruction development is intentionally not included here:
it is a separate result and is not part of the attached third-moment paper.

Toolchain recorded by the source development: Lean 4.31.0 and Mathlib v4.31.0.
-/

open Finset Filter Asymptotics
open scoped Topology ENNReal ArithmeticFunction

namespace Represented


/-! ## Section 3 -- Reflection identity (paper Lemma 3.1): F e d = e*d * g e (e*d). -/


/-- The divisor-prefix sum of `e*d` whose final divisor is `d`:
    the sum of all divisors of `e*d` that are `≤ d`. -/
def F (e d : ℕ) : ℕ := ∑ q ∈ (e * d).divisors.filter (· ≤ d), q

/-- `g e n = ∑_{r ∣ n, r ≥ e} 1/r` (as a real number). -/
noncomputable def g (e n : ℕ) : ℝ := ∑ r ∈ n.divisors.filter (e ≤ ·), (1 : ℝ) / r

/-- Reflection identity: `F e d = (e*d) * g e (e*d)`. -/
theorem reflection (e d : ℕ) (he : 1 ≤ e) (hd : 1 ≤ d) :
    (F e d : ℝ) = (e * d : ℝ) * g e (e * d) := by
  set m := e * d with hm
  have hmpos : 0 < m := by rw [hm]; exact Nat.mul_pos he hd
  -- F as a sum over all divisors with an indicator
  have hF : (F e d : ℝ) = ∑ r ∈ m.divisors, (if r ≤ d then (r : ℝ) else 0) := by
    rw [F, ← hm, Nat.cast_sum, Finset.sum_filter]
  -- (m) * g as a sum over all divisors with an indicator
  have hg : (m : ℝ) * g e m = ∑ r ∈ m.divisors, (if e ≤ r then (m : ℝ) / r else 0) := by
    simp only [g, Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    split_ifs with h
    · rw [mul_one_div]
    · rw [mul_zero]
  -- the reflection of the indicator sum
  have hrefl :
      (∑ r ∈ m.divisors, (if (m / r) ≤ d then ((m / r : ℕ) : ℝ) else 0))
        = ∑ r ∈ m.divisors, (if r ≤ d then (r : ℝ) else 0) :=
    Nat.sum_div_divisors m (fun r => if r ≤ d then (r : ℝ) else 0)
  -- termwise: reflected F-indicator = g-indicator
  have hterm : (∑ r ∈ m.divisors, (if (m / r) ≤ d then ((m / r : ℕ) : ℝ) else 0))
        = ∑ r ∈ m.divisors, (if e ≤ r then (m : ℝ) / r else 0) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [Nat.mem_divisors] at hr
    obtain ⟨hdvd, _⟩ := hr
    have hrpos : 0 < r := Nat.pos_of_dvd_of_pos hdvd hmpos
    have hrne : (r : ℝ) ≠ 0 := by exact_mod_cast hrpos.ne'
    have hval : ((m / r : ℕ) : ℝ) = (m : ℝ) / r := Nat.cast_div hdvd hrne
    have hmul : m / r * r = m := Nat.div_mul_cancel hdvd
    have hcond : (m / r ≤ d) ↔ (e ≤ r) := by
      constructor
      · intro h
        have h1 : m / r * r ≤ d * r := by gcongr
        rw [hmul] at h1
        have h2 : e * d ≤ r * d := by rw [hm, mul_comm d r] at h1; exact h1
        exact le_of_mul_le_mul_right h2 (by omega)
      · intro h
        have h1 : e * d ≤ r * d := by gcongr
        have h2 : m / r * r ≤ d * r := by rw [hmul, hm, mul_comm d r]; exact h1
        exact le_of_mul_le_mul_right h2 hrpos
    by_cases h : e ≤ r
    · rw [if_pos (hcond.mpr h), if_pos h, hval]
    · rw [if_neg (fun hc => h (hcond.mp hc)), if_neg h]
  rw [hF, ← hrefl, hterm, ← hg, hm]
  push_cast
  ring



/-! ## Section 1 -- Represented integers: R, f, prefix-sum divisors; N in R iff exists e d, N = F e d. -/


/-- Sum of the `k` smallest divisors of `m`. -/
noncomputable def prefixSumDivisors (m k : ℕ) : ℕ :=
  ((m.divisors.sort (· ≤ ·)).take k).sum

/-- `N` is a divisor-prefix sum of `m`: the sum of the first `k` divisors, `1 ≤ k ≤ τ(m)`. -/
def IsRep (N m : ℕ) : Prop :=
  ∃ k, 1 ≤ k ∧ k ≤ m.divisors.card ∧ N = prefixSumDivisors m k

/-- The set of represented integers. -/
def R : Set ℕ := {N | ∃ m, 1 ≤ m ∧ IsRep N m}

/-- `f N` = least `m` representing `N` (`0` if none; finiteness is recovered from `N ∈ R`). -/
noncomputable def f (N : ℕ) : ℕ := sInf {m | 1 ≤ m ∧ IsRep N m}

/-- Sum of divisors of `m` that are `≤ d`. -/
def Fdiv (m d : ℕ) : ℕ := ∑ q ∈ m.divisors.filter (· ≤ d), q

lemma F_eq_Fdiv {m d : ℕ} (hd : d ∣ m) : F (m / d) d = Fdiv m d := by
  unfold F Fdiv
  rw [Nat.div_mul_cancel hd]

/-- The `toFinset` of the first `k` sorted divisors is exactly the divisors `≤` the `k`-th one. -/
lemma take_sort_toFinset (m k : ℕ) (hidx : k - 1 < (m.divisors.sort (· ≤ ·)).length) (hk1 : 1 ≤ k) :
    ((m.divisors.sort (· ≤ ·)).take k).toFinset
      = m.divisors.filter (· ≤ (m.divisors.sort (· ≤ ·))[k - 1]) := by
  classical
  have hslt : (m.divisors.sort (· ≤ ·)).SortedLT := Finset.sortedLT_sort m.divisors
  ext a
  simp only [List.mem_toFinset, Finset.mem_filter, List.mem_take_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hiL : i < (m.divisors.sort (· ≤ ·)).length := lt_of_lt_of_le hi (min_le_right _ _)
    have hik : i ≤ k - 1 := by have := lt_of_lt_of_le hi (min_le_left _ _); omega
    refine ⟨by rw [← Finset.mem_sort (· ≤ ·)]; exact List.getElem_mem hiL, ?_⟩
    rw [hslt.getElem_le_getElem_iff]; exact hik
  · rintro ⟨haD, hale⟩
    have haL : a ∈ m.divisors.sort (· ≤ ·) := by rw [Finset.mem_sort]; exact haD
    obtain ⟨i, hiL, rfl⟩ := List.getElem_of_mem haL
    have hik : i ≤ k - 1 := by rw [← hslt.getElem_le_getElem_iff (hi := hiL) (hj := hidx)]; exact hale
    refine ⟨i, lt_of_le_of_lt hik (by omega), ?_⟩
    simp

/-- For a nodup list, the list sum equals the `Finset` sum over its `toFinset`. -/
lemma list_sum_eq_toFinset_sum : ∀ {l : List ℕ}, l.Nodup → l.sum = ∑ q ∈ l.toFinset, q := by
  classical
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
    intro h
    rw [List.sum_cons, List.toFinset_cons,
      Finset.sum_insert (by simpa using (List.nodup_cons.1 h).1), ih (List.nodup_cons.1 h).2]

/-- **Sorted-prefix bridge (forward).** -/
lemma prefixSumDivisors_eq_Fdiv (m k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ m.divisors.card) :
    ∃ d, d ∈ m.divisors ∧ prefixSumDivisors m k = Fdiv m d := by
  classical
  have hlen : (m.divisors.sort (· ≤ ·)).length = m.divisors.card := Finset.length_sort _
  have hidx : k - 1 < (m.divisors.sort (· ≤ ·)).length := by rw [hlen]; omega
  refine ⟨(m.divisors.sort (· ≤ ·))[k - 1], ?_, ?_⟩
  · rw [← Finset.mem_sort (· ≤ ·)]; exact List.getElem_mem hidx
  · rw [prefixSumDivisors, Fdiv, ← take_sort_toFinset m k hidx hk1,
      list_sum_eq_toFinset_sum ((m.divisors.sort_nodup (· ≤ ·)).take)]

/-- **Sorted-prefix bridge (backward).** -/
lemma Fdiv_eq_prefixSumDivisors (m d : ℕ) (hd : d ∈ m.divisors) :
    ∃ k, 1 ≤ k ∧ k ≤ m.divisors.card ∧ Fdiv m d = prefixSumDivisors m k := by
  classical
  have hdL : d ∈ m.divisors.sort (· ≤ ·) := by rw [Finset.mem_sort]; exact hd
  obtain ⟨i, hiL, hdi⟩ := List.getElem_of_mem hdL
  have hlen : (m.divisors.sort (· ≤ ·)).length = m.divisors.card := Finset.length_sort _
  refine ⟨i + 1, by omega, by rw [← hlen]; omega, ?_⟩
  have hidx : (i + 1) - 1 < (m.divisors.sort (· ≤ ·)).length := by omega
  have hdeq : (m.divisors.sort (· ≤ ·))[(i + 1) - 1] = d := by simp [hdi]
  rw [prefixSumDivisors, Fdiv, ← hdeq, ← take_sort_toFinset m (i + 1) hidx (by omega),
    list_sum_eq_toFinset_sum ((m.divisors.sort_nodup (· ≤ ·)).take)]

/-- A prefix representation of `N` by `m` is exactly `N = F (m/d) d` for a divisor `d ∣ m`. -/
lemma isRep_iff_exists_divisor (N m : ℕ) (hm : 1 ≤ m) :
    IsRep N m ↔ ∃ d, d ∈ m.divisors ∧ N = F (m / d) d := by
  constructor
  · rintro ⟨k, hk1, hk2, hN⟩
    obtain ⟨d, hd, hpd⟩ := prefixSumDivisors_eq_Fdiv m k hk1 hk2
    exact ⟨d, hd, by rw [hN, hpd, F_eq_Fdiv (Nat.dvd_of_mem_divisors hd)]⟩
  · rintro ⟨d, hd, hN⟩
    obtain ⟨k, hk1, hk2, hpd⟩ := Fdiv_eq_prefixSumDivisors m d hd
    exact ⟨k, hk1, hk2, by rw [hN, F_eq_Fdiv (Nat.dvd_of_mem_divisors hd), hpd]⟩

/-- The `f`-minimisation set, re-expressed via the `F e d` parametrisation. -/
lemma f_set_eq (N : ℕ) :
    {m | 1 ≤ m ∧ IsRep N m}
      = {m | ∃ e d, 1 ≤ e ∧ 1 ≤ d ∧ m = e * d ∧ N = F e d} := by
  ext m
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hm, hrep⟩
    rw [isRep_iff_exists_divisor N m hm] at hrep
    obtain ⟨d, hd, hN⟩ := hrep
    have hdvd := Nat.dvd_of_mem_divisors hd
    have hdpos := Nat.pos_of_mem_divisors hd
    refine ⟨m / d, d, ?_, hdpos, (Nat.div_mul_cancel hdvd).symm, hN⟩
    exact Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hdpos
  · rintro ⟨e, d, he, hd, hme, hN⟩
    subst hme
    have hpos : 0 < e * d := Nat.mul_pos he hd
    have hed : (e * d) / d = e := by
      rw [Nat.mul_div_assoc e (dvd_refl d), Nat.div_self (by omega), mul_one]
    refine ⟨hpos, ?_⟩
    rw [isRep_iff_exists_divisor N (e * d) hpos]
    refine ⟨d, ?_, ?_⟩
    · rw [Nat.mem_divisors]; exact ⟨dvd_mul_left d e, hpos.ne'⟩
    · rw [hed, hN]

/-- Membership in `R` is exactly the `F e d` parametrisation. -/
theorem mem_R_iff_exists_F (N : ℕ) :
    N ∈ R ↔ ∃ e d, 1 ≤ e ∧ 1 ≤ d ∧ N = F e d := by
  constructor
  · rintro ⟨m, hm, hrep⟩
    have hmem : m ∈ {m | 1 ≤ m ∧ IsRep N m} := ⟨hm, hrep⟩
    rw [f_set_eq] at hmem
    obtain ⟨e, d, he, hd, _, hN⟩ := hmem
    exact ⟨e, d, he, hd, hN⟩
  · rintro ⟨e, d, he, hd, hN⟩
    have hpos : 0 < e * d := Nat.mul_pos he hd
    have hmem : (e * d) ∈ {m | 1 ≤ m ∧ IsRep N m} := by
      rw [f_set_eq]; exact ⟨e, d, he, hd, rfl, hN⟩
    exact ⟨e * d, hpos, hmem.2⟩

/-- For represented `N`, the minimiser `f N` is realised by a concrete pair `(e, d)`. -/
lemma f_mem_Fform (N : ℕ) (hN : N ∈ R) :
    ∃ e d, 1 ≤ e ∧ 1 ≤ d ∧ f N = e * d ∧ N = F e d := by
  have hne : {m | 1 ≤ m ∧ IsRep N m}.Nonempty := hN
  have hmem : f N ∈ {m | 1 ≤ m ∧ IsRep N m} := Nat.sInf_mem hne
  rw [f_set_eq] at hmem
  exact hmem



/-! ## Density infrastructure: countUpTo, CountIsLittleO (density zero), lowerDensity, union-bound combinator. -/


/-- The set of `n ≤ X` satisfying `P`. -/
def setUpTo (P : ℕ → Prop) (X : ℕ) : Set ℕ := {n | n ≤ X ∧ P n}

/-- The number of `n ≤ X` satisfying `P`. -/
noncomputable def countUpTo (P : ℕ → Prop) (X : ℕ) : ℕ := (setUpTo P X).ncard

/-- A predicate that holds only on a density-zero set: `#{n ≤ X : P n} = o(X)`. -/
def CountIsLittleO (P : ℕ → Prop) : Prop :=
  (fun X : ℕ => (countUpTo P X : ℝ)) =o[atTop] (fun X : ℕ => (X : ℝ))

/-- Lower asymptotic density `liminf_{X→∞} #{n ≤ X : P n} / X`. -/
noncomputable def lowerDensity (P : ℕ → Prop) : ℝ :=
  liminf (fun X : ℕ => (countUpTo P X : ℝ) / (X : ℝ)) atTop

lemma setUpTo_finite (P : ℕ → Prop) (X : ℕ) : (setUpTo P X).Finite :=
  (Set.finite_Iic X).subset (fun _ hn => hn.1)

@[simp] lemma countUpTo_nonneg (P : ℕ → Prop) (X : ℕ) : 0 ≤ (countUpTo P X : ℝ) := by
  positivity

/-- `#{n ≤ X : P n} ≤ X + 1`. -/
lemma countUpTo_le (P : ℕ → Prop) (X : ℕ) : countUpTo P X ≤ X + 1 := by
  unfold countUpTo setUpTo
  calc ({n | n ≤ X ∧ P n}).ncard
      ≤ (Set.Iic X).ncard :=
        Set.ncard_le_ncard (fun n hn => hn.1) (Set.finite_Iic X)
    _ = X + 1 := Set.ncard_Iic_nat X

/-- `#{n ≤ X : P n}/X ≤ 2`. -/
lemma countUpTo_div_le_two (P : ℕ → Prop) (X : ℕ) : (countUpTo P X : ℝ) / X ≤ 2 := by
  rcases Nat.eq_zero_or_pos X with hX | hX
  · subst hX; rw [Nat.cast_zero, div_zero]; norm_num
  · have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
    have hle : (countUpTo P X : ℝ) ≤ (X : ℝ) + 1 := by exact_mod_cast countUpTo_le P X
    have h1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
    rw [div_le_iff₀ hXpos]
    nlinarith [hle, h1]

/-- Monotonicity of `countUpTo` in the predicate. -/
lemma countUpTo_mono {P Q : ℕ → Prop} (h : ∀ n, P n → Q n) (X : ℕ) :
    countUpTo P X ≤ countUpTo Q X :=
  Set.ncard_le_ncard (fun n hn => ⟨hn.1, h n hn.2⟩) (setUpTo_finite Q X)

/-- The "or" of two predicates is counted by at most the sum of counts. -/
lemma countUpTo_or_le (P Q : ℕ → Prop) (X : ℕ) :
    countUpTo (fun n => P n ∨ Q n) X ≤ countUpTo P X + countUpTo Q X := by
  unfold countUpTo setUpTo
  have heq : {n | n ≤ X ∧ (P n ∨ Q n)} = {n | n ≤ X ∧ P n} ∪ {n | n ≤ X ∧ Q n} := by
    ext n; constructor
    · rintro ⟨hle, hP | hQ⟩
      · exact Or.inl ⟨hle, hP⟩
      · exact Or.inr ⟨hle, hQ⟩
    · rintro (⟨hle, hP⟩ | ⟨hle, hQ⟩)
      · exact ⟨hle, Or.inl hP⟩
      · exact ⟨hle, Or.inr hQ⟩
  rw [heq]
  exact Set.ncard_union_le _ _

/-- Filtering by `G ∧ ¬B` removes at most the `B`-count from the `G`-count. -/
lemma countUpTo_and_not_ge (G B : ℕ → Prop) (X : ℕ) :
    countUpTo G X ≤ countUpTo (fun n => G n ∧ ¬ B n) X + countUpTo B X := by
  unfold countUpTo setUpTo
  have hsub : {n | n ≤ X ∧ G n} ⊆
      {n | n ≤ X ∧ (G n ∧ ¬ B n)} ∪ {n | n ≤ X ∧ B n} := by
    intro n hn
    by_cases hB : B n
    · exact Or.inr ⟨hn.1, hB⟩
    · exact Or.inl ⟨hn.1, hn.2, hB⟩
  calc ({n | n ≤ X ∧ G n}).ncard
      ≤ ({n | n ≤ X ∧ (G n ∧ ¬ B n)} ∪ {n | n ≤ X ∧ B n}).ncard :=
        Set.ncard_le_ncard hsub ((setUpTo_finite _ X).union (setUpTo_finite _ X))
    _ ≤ _ := Set.ncard_union_le _ _

/-- A predicate implied by an `o(X)` predicate is itself `o(X)`. -/
lemma CountIsLittleO.mono {P Q : ℕ → Prop} (h : ∀ n, P n → Q n) (hQ : CountIsLittleO Q) :
    CountIsLittleO P := by
  have hbound : (fun X : ℕ => (countUpTo P X : ℝ)) =O[atTop]
      (fun X : ℕ => (countUpTo Q X : ℝ)) := by
    refine Asymptotics.isBigO_of_le atTop (fun X => ?_)
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    exact_mod_cast countUpTo_mono h X
  exact hbound.trans_isLittleO hQ

/-- Union bound for `o(X)` predicates. -/
lemma CountIsLittleO.or {P Q : ℕ → Prop}
    (hP : CountIsLittleO P) (hQ : CountIsLittleO Q) :
    CountIsLittleO (fun n => P n ∨ Q n) := by
  have hbound : (fun X : ℕ => (countUpTo (fun n => P n ∨ Q n) X : ℝ)) =O[atTop]
      (fun X : ℕ => (countUpTo P X : ℝ) + (countUpTo Q X : ℝ)) := by
    refine Asymptotics.isBigO_of_le atTop (fun X => ?_)
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    exact_mod_cast countUpTo_or_le P Q X
  exact hbound.trans_isLittleO (hP.add hQ)

/-- A `CountIsLittleO` predicate implies its count divided by `X` tends to `0`. -/
lemma CountIsLittleO.tendsto_div {B : ℕ → Prop} (hB : CountIsLittleO B) :
    Tendsto (fun X : ℕ => (countUpTo B X : ℝ) / (X : ℝ)) atTop (nhds 0) :=
  hB.tendsto_div_nhds_zero

/-- **Union-bound combinator.** Removing a density-zero set from a set of lower
density `≥ d` leaves a set of lower density `≥ d`. -/
lemma lowerDensity_and_not {G B : ℕ → Prop} {d : ℝ}
    (hG : d ≤ lowerDensity G) (hB : CountIsLittleO B) :
    d ≤ lowerDensity (fun n => G n ∧ ¬ B n) := by
  have hbtend : Tendsto (fun X : ℕ => (countUpTo B X : ℝ) / X) atTop (nhds 0) := hB.tendsto_div
  -- the `G`-density is bounded above (needed for `eventually_lt_of_lt_liminf`)
  have hcbdd : IsBoundedUnder (· ≥ ·) atTop (fun X : ℕ => (countUpTo G X : ℝ) / X) := by
    refine ⟨0, ?_⟩
    rw [eventually_map]
    filter_upwards with X
    positivity
  rw [lowerDensity]
  apply le_of_forall_pos_le_add
  intro ε hε
  have hc : ∀ᶠ X : ℕ in atTop, d - ε / 2 < (countUpTo G X : ℝ) / X :=
    eventually_lt_of_lt_liminf (lt_of_lt_of_le (by linarith) hG) hcbdd
  have hbb : ∀ᶠ X : ℕ in atTop, (countUpTo B X : ℝ) / X < ε / 2 :=
    hbtend (Iio_mem_nhds (by linarith : (0 : ℝ) < ε / 2))
  have hcnt : ∀ᶠ X : ℕ in atTop,
      d - ε ≤ (countUpTo (fun n => G n ∧ ¬ B n) X : ℝ) / X := by
    filter_upwards [hc, hbb, eventually_gt_atTop 0] with X hcX hbX hX
    have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
    have hcount : (countUpTo G X : ℝ)
        ≤ (countUpTo (fun n => G n ∧ ¬ B n) X : ℝ) + (countUpTo B X : ℝ) := by
      exact_mod_cast countUpTo_and_not_ge G B X
    have hc_le : (countUpTo G X : ℝ) / X
        ≤ (countUpTo (fun n => G n ∧ ¬ B n) X : ℝ) / X + (countUpTo B X : ℝ) / X := by
      rw [← add_div]
      exact (div_le_div_iff_of_pos_right hXpos).2 hcount
    linarith [hcX, hbX, hc_le]
  have hacobdd : IsCoboundedUnder (· ≥ ·) atTop
      (fun X : ℕ => (countUpTo (fun n => G n ∧ ¬ B n) X : ℝ) / X) := by
    refine ⟨2, fun z hz => ?_⟩
    rw [eventually_map] at hz
    obtain ⟨X, hX⟩ := hz.exists
    exact le_trans hX (countUpTo_div_le_two _ X)
  have hfin : d - ε ≤
      liminf (fun X : ℕ => (countUpTo (fun n => G n ∧ ¬ B n) X : ℝ) / X) atTop :=
    le_liminf_of_le hacobdd hcnt
  linarith [hfin]

/-- Removing a set of upper density `≤ β` lowers the lower density by at most `β`. -/
lemma lowerDensity_and_not_le {G B : ℕ → Prop} {d β : ℝ}
    (hB : ∀ X : ℕ, (countUpTo B X : ℝ) ≤ β * X) (hG : d ≤ lowerDensity G) :
    d - β ≤ lowerDensity (fun n => G n ∧ ¬ B n) := by
  have hcbdd : IsBoundedUnder (· ≥ ·) atTop (fun X : ℕ => (countUpTo G X : ℝ) / X) := by
    refine ⟨0, ?_⟩
    rw [eventually_map]
    filter_upwards with X
    positivity
  rw [lowerDensity]
  apply le_of_forall_pos_le_add
  intro ε hε
  have hc : ∀ᶠ X : ℕ in atTop, d - ε < (countUpTo G X : ℝ) / X :=
    eventually_lt_of_lt_liminf (lt_of_lt_of_le (by linarith) hG) hcbdd
  have hcnt : ∀ᶠ X : ℕ in atTop,
      d - β - ε ≤ (countUpTo (fun n => G n ∧ ¬ B n) X : ℝ) / X := by
    filter_upwards [hc, eventually_gt_atTop 0] with X hcX hX
    have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
    have hcount : (countUpTo G X : ℝ)
        ≤ (countUpTo (fun n => G n ∧ ¬ B n) X : ℝ) + (countUpTo B X : ℝ) := by
      exact_mod_cast countUpTo_and_not_ge G B X
    have hbβ : (countUpTo B X : ℝ) / X ≤ β := by
      rw [div_le_iff₀ hXpos]; exact hB X
    have hc_le : (countUpTo G X : ℝ) / X
        ≤ (countUpTo (fun n => G n ∧ ¬ B n) X : ℝ) / X + (countUpTo B X : ℝ) / X := by
      rw [← add_div]; exact (div_le_div_iff_of_pos_right hXpos).2 hcount
    linarith [hcX, hbβ, hc_le]
  have hacobdd : IsCoboundedUnder (· ≥ ·) atTop
      (fun X : ℕ => (countUpTo (fun n => G n ∧ ¬ B n) X : ℝ) / X) := by
    refine ⟨2, fun z hz => ?_⟩
    rw [eventually_map] at hz
    obtain ⟨X, hX⟩ := hz.exists
    exact le_trans hX (countUpTo_div_le_two _ X)
  have hfin : d - β - ε ≤
      liminf (fun X : ℕ => (countUpTo (fun n => G n ∧ ¬ B n) X : ℝ) / X) atTop :=
    le_liminf_of_le hacobdd hcnt
  linarith [hfin]

/-- Lower density is monotone in the predicate. -/
lemma lowerDensity_mono {G H : ℕ → Prop} (h : ∀ n, G n → H n) :
    lowerDensity G ≤ lowerDensity H := by
  have hHcobdd : IsCoboundedUnder (· ≥ ·) atTop (fun X : ℕ => (countUpTo H X : ℝ) / X) := by
    refine ⟨2, fun z hz => ?_⟩
    rw [eventually_map] at hz
    obtain ⟨X, hX⟩ := hz.exists
    exact le_trans hX (countUpTo_div_le_two _ X)
  have hGbdd : IsBoundedUnder (· ≥ ·) atTop (fun X : ℕ => (countUpTo G X : ℝ) / X) := by
    refine ⟨0, ?_⟩
    rw [eventually_map]
    filter_upwards with X
    positivity
  apply liminf_le_liminf _ hGbdd hHcobdd
  filter_upwards [eventually_gt_atTop 0] with X hX
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
  exact (div_le_div_iff_of_pos_right hXpos).2 (by exact_mod_cast countUpTo_mono h X)



/-! ## Analytic input (A2): a fully formalized Mertens product lower bound. -/

/-
The following development is transplanted from `Erdos1054Complete.lean`.  Its final theorem,
`mertens_third_lower`, has exactly the lower-bound form used in paper Lemma 5.4:

  ∃ c₀ > 0, ∀ y ≥ 2,
    c₀ / log(2y) ≤ ∏_{p ≤ y, p prime} (1 - 1/p).

It contains no `sorry`, `admit`, or additional axiom.
-/

section MertensThirdProof

open Finset ArithmeticFunction Real
open scoped BigOperators

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

noncomputable section

/-- ψ(n) = Σ_{m=1}^{n} Λ(m), the first Chebyshev function. -/
def chebyshevPsi (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (n + 1), vonMangoldt m

/-- L_n = lcm(1, 2, ..., n). -/
def lcmRange (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm _root_.id

/-- S(n) = Σ_{m=2}^{n} Λ(m)/m. -/
def sumS (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 n, vonMangoldt m / m

/-- T(n) = Σ_{m=2}^{n} Λ(m)/(m * log m). -/
def sumT (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 n, vonMangoldt m / (m * Real.log m)

/-- P(n) = ∏_{p ≤ n, p prime} (1 - 1/p). -/
def prodP (n : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

end

noncomputable section

/-! # Lemma: Central Binomial Coefficient Bounds -/

lemma centralBinom_le_four_pow (r : ℕ) (hr : 1 ≤ r) :
    Nat.choose (2 * r) r ≤ 4 ^ r := by
  rw [show 4 ^ r = (2 : ℕ) ^ (2 * r) by norm_num [pow_mul]]
  rw [← Nat.sum_range_choose]
  exact Finset.single_le_sum (fun x _ => Nat.zero_le _)
    (Finset.mem_range.mpr (by linarith))

lemma choose_odd_le_four_pow (r : ℕ) (_hr : 1 ≤ r) :
    Nat.choose (2 * r + 1) r ≤ 4 ^ r := by
  exact Nat.choose_middle_le_pow r

/-! # LCM helpers -/

lemma lcmRange_pos (n : ℕ) (_hn : 1 ≤ n) : 0 < lcmRange n := by
  exact Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) )

lemma lcmRange_dvd_of_le {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    m ∣ lcmRange n := by
  exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ hm, hmn ⟩ )

/-! # LCM Divisibility Lemmas -/

lemma lcmRange_dvd_even (r : ℕ) (hr : 1 ≤ r) :
    lcmRange (2 * r) ∣ lcmRange r * Nat.choose (2 * r) r := by
  -- By definition of lcmRange, we need to show that for every prime power $p^a$ dividing $m \in (1, 2r]$, $p^a$ divides $lcmRange(r) * \binom{2r}{r}$.
  have h_div : ∀ m ∈ Finset.Icc 1 (2 * r), ∀ p ∈ Nat.primeFactors m, p ^ Nat.factorization m p ∣ lcmRange r * Nat.choose (2 * r) r := by
    intro m hm p hp
    by_cases hpa : p ^ Nat.factorization m p ≤ r;
    · exact dvd_mul_of_dvd_left ( Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ ( Nat.pos_of_mem_primeFactors hp ), hpa ⟩ ) ) _;
    · -- Since $p^a > r$, we have $p^{a-1} \leq r$.
      have hpa_minus_one : p ^ (Nat.factorization m p - 1) ≤ r := by
        rcases k : Nat.factorization m p with ( _ | k ) <;> simp_all +decide [ -Nat.factorization_def, pow_succ' ];
        nlinarith [ hp.1.two_le, Nat.le_of_dvd hm.1 ( Nat.ordProj_dvd m p ), Nat.le_of_dvd hm.1 ( Nat.ordProj_dvd m p ), show m ≥ p ^ ( Nat.factorization m p ) from Nat.le_of_dvd hm.1 ( Nat.ordProj_dvd m p ), show p ^ ( Nat.factorization m p ) = p * p ^ ‹_› from by rw [ ← pow_succ', k ] ];
      -- Since $p^{a-1} \leq r$, we have $p^{a-1} \mid lcmRange(r)$.
      have hpa_minus_one_div : p ^ (Nat.factorization m p - 1) ∣ lcmRange r := by
        exact lcmRange_dvd_of_le ( pow_pos ( Nat.pos_of_mem_primeFactors hp ) _ ) hpa_minus_one;
      -- Since $p^a > r$, we have $p \mid \binom{2r}{r}$.
      have hpa_div_choose : p ∣ Nat.choose (2 * r) r := by
        have hpa_div_choose : Nat.factorization (Nat.choose (2 * r) r) p ≥ 1 := by
          have hpa_div_choose : Nat.factorization (Nat.choose (2 * r) r) p = (∑ k ∈ Finset.Ico 1 (Nat.log p (2 * r) + 1), (Nat.floor ((2 * r) / p ^ k) - 2 * Nat.floor (r / p ^ k))) := by
            haveI := Fact.mk ( Nat.prime_of_mem_primeFactors hp ) ; rw [ Nat.factorization_def ];
            · rw [ padicValNat_choose ];
              any_goals exact Nat.lt_succ_self _;
              · norm_num [ two_mul, Nat.add_div ];
                rw [ Finset.card_filter ];
                refine' Finset.sum_congr rfl fun x hx => _;
                rw [ Nat.add_div ( pow_pos ( Nat.Prime.pos ( Nat.prime_of_mem_primeFactors hp ) ) _ ) ] ; aesop;
              · linarith;
            · exact Nat.prime_of_mem_primeFactors hp;
          rw [hpa_div_choose];
          refine' le_trans _ ( Finset.single_le_sum ( fun x hx => Nat.zero_le _ ) ( Finset.mem_Ico.mpr ⟨ Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ( show m.factorization p ≠ 0 from Finsupp.mem_support_iff.mp hp ) ), Nat.lt_succ_of_le ( Nat.le_log_of_pow_le ( Nat.Prime.one_lt ( Nat.prime_of_mem_primeFactors hp ) ) ( show p ^ m.factorization p ≤ 2 * r from _ ) ) ⟩ ) );
          · norm_num [ Nat.div_eq_of_lt ( show r < p ^ m.factorization p from lt_of_not_ge hpa ) ];
            exact Nat.div_pos ( by linarith [ Finset.mem_Icc.mp hm, Nat.le_of_dvd ( by linarith [ Finset.mem_Icc.mp hm ] ) ( Nat.ordProj_dvd m p ) ] ) ( pow_pos ( Nat.pos_of_mem_primeFactors hp ) _ );
          · exact le_trans ( Nat.le_of_dvd ( by linarith [ Finset.mem_Icc.mp hm ] ) ( Nat.ordProj_dvd _ _ ) ) ( by linarith [ Finset.mem_Icc.mp hm ] );
        exact Nat.dvd_trans ( dvd_pow_self _ ( by linarith ) ) ( Nat.ordProj_dvd _ _ );
      convert Nat.mul_dvd_mul hpa_minus_one_div hpa_div_choose using 1 ; rw [ ← pow_succ, Nat.sub_add_cancel ( Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp hp ) ) ) ];
  -- Since every prime power in the lcm divides the product, the lcm itself must divide the product.
  have h_lcm_div : ∀ m ∈ Finset.Icc 1 (2 * r), m ∣ lcmRange r * Nat.choose (2 * r) r := by
    intro m hm
    have h_prod_div : ∏ p ∈ Nat.primeFactors m, p ^ Nat.factorization m p ∣ lcmRange r * Nat.choose (2 * r) r := by
      convert Finset.lcm_dvd fun p hp => h_div m hm p hp using 1 <;> try rfl;
      -- The least common multiple of a set of numbers is equal to their product divided by their greatest common divisor.
      have h_lcm_prod : ∀ {S : Finset ℕ} {f : ℕ → ℕ}, (∀ p ∈ S, Nat.Prime p) → (∀ p q : ℕ, p ∈ S → q ∈ S → p ≠ q → Nat.gcd (p ^ f p) (q ^ f q) = 1) → Finset.lcm S (fun p => p ^ f p) = ∏ p ∈ S, p ^ f p := by
        intros S f hprime hgcd; induction S using Finset.induction <;> simp_all +decide ;
        exact Nat.Coprime.lcm_eq_mul <| Nat.Coprime.prod_right fun p hp => hgcd _ _ ( Or.inl rfl ) ( Or.inr hp ) <| by aesop;
      rw [ h_lcm_prod ( fun p hp => Nat.prime_of_mem_primeFactors hp ) ( fun p q hp hq hpq => by simpa [ hpq ] using Nat.coprime_pow_primes _ _ ( Nat.prime_of_mem_primeFactors hp ) ( Nat.prime_of_mem_primeFactors hq ) ) ];
    rwa [ ← Nat.factorization_prod_pow_eq_self ( by linarith [ Finset.mem_Icc.mp hm ] : m ≠ 0 ) ];
  exact Finset.lcm_dvd h_lcm_div

lemma lcmRange_dvd_odd (r : ℕ) (hr : 1 ≤ r) :
    lcmRange (2 * r + 1) ∣ lcmRange (r + 1) * Nat.choose (2 * r + 1) r := by
  -- For any prime power $p^a \leq 2r+1$, we need to show that $p^a$ divides $lcmRange(r+1) * (2r+1 choose r)$.
  have h_prime_power : ∀ p a : ℕ, Nat.Prime p → p^a ≤ 2 * r + 1 → p^a ∣ lcmRange (r + 1) * Nat.choose (2 * r + 1) r := by
    intro p a hp ha
    by_cases hpa : p^a ≤ r + 1;
    · refine' dvd_mul_of_dvd_left _ _;
      exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ hp.pos, hpa ⟩ );
    · -- Since $p^a > r + 1$, we have $p^{a-1} \leq r$.
      have hpa_minus_one : p^(a-1) ≤ r := by
        rcases a <;> simp_all +decide [ -Nat.factorization_def, pow_succ' ];
        nlinarith [ hp.two_le ];
      -- Since $p^{a-1} \leq r$, we have $p^a \mid \binom{2r+1}{r}$.
      have hpa_div_choose : p^a ∣ Nat.choose (2 * r + 1) r * p^(a-1) := by
        have hpa_div_choose : padicValNat p (Nat.choose (2 * r + 1) r) ≥ 1 := by
          haveI := Fact.mk hp; rw [ padicValNat_choose ];
          any_goals exact Nat.lt_succ_self _;
          · refine' Finset.card_pos.mpr ⟨ a, _ ⟩ ; norm_num;
            exact ⟨ ⟨ Nat.pos_of_ne_zero ( by rintro rfl; linarith ), Nat.le_log_of_pow_le hp.one_lt ha ⟩, by rw [ Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] <;> omega ⟩;
          · linarith;
        have hpa_div_choose : p ∣ Nat.choose (2 * r + 1) r := by
          contrapose! hpa_div_choose; simp_all +decide ;
        rcases a with ( _ | a ) <;> simp_all +decide [ pow_succ', mul_dvd_mul ];
      -- Since $p^{a-1} \leq r$, we have $p^{a-1} \mid lcmRange(r+1)$.
      have hpa_minus_one_div_lcm : p^(a-1) ∣ lcmRange (r + 1) := by
        have hpa_minus_one_div_lcm : p^(a-1) ∈ Finset.Icc 1 (r + 1) := by
          exact Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ hp.pos, by linarith ⟩;
        exact Finset.dvd_lcm hpa_minus_one_div_lcm;
      exact dvd_trans hpa_div_choose ( by rw [ mul_comm ] ; exact mul_dvd_mul hpa_minus_one_div_lcm dvd_rfl );
  -- By definition of lcmRange, lcmRange (2 * r + 1) divides the product of all numbers in the range 1 to 2r+1.
  have h_lcm_div : ∀ m ∈ Finset.Icc 1 (2 * r + 1), m ∣ lcmRange (r + 1) * Nat.choose (2 * r + 1) r := by
    intro m hm; rw [ ← Nat.factorization_le_iff_dvd ] <;> norm_num;
    · intro p; by_cases hp : Nat.Prime p <;> by_cases hp' : p ∣ m <;> simp_all +decide [ -Nat.factorization_def, Nat.factorization_eq_zero_of_not_dvd ] ;
      have := h_prime_power p ( Nat.factorization m p ) hp ( Nat.le_trans ( Nat.le_of_dvd hm.1 ( Nat.ordProj_dvd _ _ ) ) hm.2 ) ; rw [ ← Nat.factorization_le_iff_dvd ] at this <;> simp_all +decide [ -Nat.factorization_def ] ;
      exact ⟨ Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop, Nat.ne_of_gt <| Nat.choose_pos <| by linarith ⟩;
    · linarith [ Finset.mem_Icc.mp hm ];
    · exact ⟨ Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop, Nat.ne_of_gt <| Nat.choose_pos <| by linarith ⟩;
  exact Finset.lcm_dvd fun x hx => h_lcm_div x hx

/-! # LCM Bound: L_n ≤ 4^n -/

lemma lcmRange_le_four_pow (n : ℕ) (hn : 1 ≤ n) :
    lcmRange n ≤ 4 ^ n := by
  induction' n using Nat.strong_induction_on with n ih;
  by_cases h₂ : n ≤ 4;
  · interval_cases n <;> decide;
  · rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩;
    · -- By lcmRange_dvd_even, lcmRange(2k) | lcmRange(k) * choose(2k,k).
      have h_div : lcmRange (2 * k) ∣ lcmRange k * Nat.choose (2 * k) k := by
        exact lcmRange_dvd_even k ( by linarith );
      -- Since $\binom{2k}{k} \leq 4^k$, we have $lcmRange (2 * k) \leq lcmRange k * 4^k$.
      have h_bound : lcmRange (2 * k) ≤ lcmRange k * 4 ^ k := by
        refine' le_trans ( Nat.le_of_dvd ( Nat.mul_pos ( lcmRange_pos k ( by linarith ) ) ( Nat.choose_pos ( by linarith ) ) ) h_div ) _;
        exact Nat.mul_le_mul_left _ ( centralBinom_le_four_pow k ( by linarith ) );
      exact h_bound.trans ( by rw [ pow_mul' ] ; exact Nat.mul_le_mul_right _ ( ih k ( by linarith ) ( by linarith ) ) |> le_trans <| by ring_nf; norm_num );
    · -- By lcmRange_dvd_odd, lcmRange(2k+1) | lcmRange(k+1) * choose(2k+1,k).
      have h_div : lcmRange (2 * k + 1) ∣ lcmRange (k + 1) * Nat.choose (2 * k + 1) k := by
        convert lcmRange_dvd_odd k ( by linarith ) using 1;
      -- By choose_odd_le_four_pow, choose(2k+1,k) ≤ 4^k.
      have h_choose : Nat.choose (2 * k + 1) k ≤ 4 ^ k := by
        convert choose_odd_le_four_pow k ( by linarith ) using 1;
      refine' le_trans ( Nat.le_of_dvd _ h_div ) _;
      · exact mul_pos ( lcmRange_pos _ ( by linarith ) ) ( Nat.choose_pos ( by linarith ) );
      · exact le_trans ( Nat.mul_le_mul ( ih _ ( by linarith ) ( by linarith ) ) h_choose ) ( by ring_nf; norm_num )

/-! # Chebyshev ψ bound -/

lemma chebyshevPsi_eq_log_lcmRange (n : ℕ) (hn : 1 ≤ n) :
    chebyshevPsi n = Real.log (lcmRange n) := by
  -- By definition of ψ, we know that ψ(n) = Σ_{m=0}^n Λ(m)
  have h_psi_def : chebyshevPsi n = ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), Nat.log p n * Real.log p := by
    have h_psi_def : chebyshevPsi n = ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), (∑ k ∈ Finset.Icc 1 (Nat.log p n), Real.log p) := by
      unfold chebyshevPsi;
      have h_sum_floor : ∑ m ∈ Finset.range (n + 1), (ArithmeticFunction.vonMangoldt m) = ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (ArithmeticFunction.vonMangoldt (p ^ k)) := by
        have h_sum_floor : Finset.filter (fun m => ArithmeticFunction.vonMangoldt m ≠ 0) (Finset.range (n + 1)) = Finset.biUnion (Finset.filter Nat.Prime (Finset.range (n + 1))) (fun p => Finset.image (fun k => p ^ k) (Finset.Icc 1 (Nat.log p n))) := by
          ext m;
          simp [ArithmeticFunction.vonMangoldt];
          constructor;
          · intro hm;
            obtain ⟨ p, k, hp, hk, rfl ⟩ := hm.2.1;
            exact ⟨ p, ⟨ by linarith [ Nat.le_self_pow hk.ne' p ], hp.nat_prime ⟩, k, ⟨ hk, Nat.le_log_of_pow_le hp.nat_prime.one_lt hm.1 ⟩, rfl ⟩;
          · rintro ⟨ p, ⟨ hp₁, hp₂ ⟩, k, ⟨ hk₁, hk₂ ⟩, rfl ⟩;
            exact ⟨ Nat.pow_le_of_le_log ( by linarith ) hk₂, hp₂.isPrimePow.pow ( by linarith ), Nat.ne_of_gt ( Nat.minFac_pos _ ), ne_of_gt ( one_lt_pow₀ hp₂.one_lt ( by linarith ) ), by linarith ⟩;
        rw [ ← Finset.sum_filter_ne_zero, h_sum_floor, Finset.sum_biUnion ];
        · exact Finset.sum_congr rfl fun p hp => Finset.sum_image <| fun a ha b hb h => Nat.pow_right_injective ( Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2 ) h;
        · intros p hp q hq hpq; simp_all +decide [ Finset.disjoint_left ];
          intro a x hx₁ hx₂ hx₃ y hy₁ hy₂ hy₃; subst_vars; have := Nat.Prime.dvd_of_dvd_pow hp.2 ( hy₃.symm ▸ dvd_pow_self _ ( by linarith ) ) ; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;
      convert h_sum_floor using 3;
      rw [ ArithmeticFunction.vonMangoldt_apply ];
      rw [ if_pos ];
      · rw [ Nat.Prime.pow_minFac ] <;> aesop;
      · exact Nat.Prime.isPrimePow ( Finset.mem_filter.mp ‹_› |>.2 ) |> fun h => h.pow ( by linarith [ Finset.mem_Icc.mp ‹_› ] );
    aesop;
  -- By definition of $lcmRange$, we know that $lcmRange n = \prod_{p \leq n} p^{e_p(n)}$ where $e_p(n) = \lfloor \log_p n \rfloor$.
  have h_lcm_def : lcmRange n = ∏ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), p ^ (Nat.log p n) := by
    clear h_psi_def;
    -- By definition of lcmRange, we know that lcmRange n = ∏ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), p ^ (Nat.log p n).
    have h_lcmRange_def : ∀ m ∈ Finset.Icc 1 n, m ∣ ∏ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), p ^ (Nat.log p n) := by
      intro m hm; rw [ ← Nat.factorization_prod_pow_eq_self ( by linarith [ Finset.mem_Icc.mp hm ] : m ≠ 0 ) ] ;
      rw [ ← Finset.prod_sdiff <| show m.primeFactors ⊆ Finset.filter Nat.Prime ( Finset.range ( n + 1 ) ) from fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr <| Nat.lt_succ_of_le <| Nat.le_trans ( Nat.le_of_mem_primeFactors hp ) <| Finset.mem_Icc.mp hm |>.2, Nat.prime_of_mem_primeFactors hp ⟩ ];
      exact dvd_mul_of_dvd_right ( Finset.prod_dvd_prod_of_dvd _ _ fun p hp => pow_dvd_pow p <| Nat.le_log_of_pow_le ( Nat.prime_of_mem_primeFactors hp |> Nat.Prime.one_lt ) <| Nat.le_trans ( Nat.le_of_dvd ( by linarith [ Finset.mem_Icc.mp hm ] ) <| Nat.ordProj_dvd _ _ ) <| Finset.mem_Icc.mp hm |>.2 ) _;
    refine' Nat.dvd_antisymm _ _;
    · exact Finset.lcm_dvd fun x hx => h_lcmRange_def x hx;
    · -- By definition of lcmRange, we know that lcmRange n is divisible by each prime power p^k where p is prime and k is such that p^k ≤ n.
      have h_lcmRange_div : ∀ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), p ^ (Nat.log p n) ∣ lcmRange n := by
        intros p hp
        have h_div : p ^ (Nat.log p n) ≤ n := by
          exact Nat.pow_log_le_self p ( by linarith );
        exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ), h_div ⟩ );
      convert Finset.lcm_dvd h_lcmRange_div using 1 <;> try rfl;
      -- The least common multiple of a set of numbers is equal to the product of the highest powers of all primes dividing any of the numbers.
      have h_lcm_eq_prod : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p) → Finset.lcm S (fun p => p ^ (Nat.log p n)) = ∏ p ∈ S, p ^ (Nat.log p n) := by
        intros S hS; induction S using Finset.induction <;> simp_all +decide ;
        exact Nat.Coprime.lcm_eq_mul <| Nat.Coprime.prod_right fun p hp => Nat.Coprime.pow _ _ <| hS.1.coprime_iff_not_dvd.mpr fun h => ‹¬_› <| by have := Nat.prime_dvd_prime_iff_eq hS.1 ( hS.2 p hp ) ; aesop;
      rw [ h_lcm_eq_prod fun p hp => Finset.mem_filter.mp hp |>.2 ];
  rw [ h_psi_def, h_lcm_def, Nat.cast_prod, Real.log_prod ] <;> aesop

lemma chebyshevPsi_le (n : ℕ) (hn : 1 ≤ n) :
    chebyshevPsi n ≤ 2 * n * Real.log 2 := by
  have h_log : Real.log (lcmRange n) ≤ Real.log (4 ^ n) := by
    gcongr;
    · exact_mod_cast lcmRange_pos n hn;
    · exact_mod_cast lcmRange_le_four_pow n hn;
  rw [ show ( 4 : ℝ ) = 2 ^ 2 by norm_num, pow_right_comm ] at h_log ; norm_num at *;
  rw [ chebyshevPsi_eq_log_lcmRange n hn ] ; linarith

/-! # S(n) Upper Bound -/

/-
S(n) ≤ (log(n!) + ψ(n)) / n
-/
lemma sumS_le_basic (n : ℕ) (hn : 2 ≤ n) :
    sumS n ≤ (Real.log (n.factorial) + chebyshevPsi n) / n := by
  -- By the properties of logarithms and the definition of S(n), we can rewrite the inequality.
  have h_rewrite : ∑ m ∈ Finset.Icc 2 n, (vonMangoldt m / m : ℝ) * n ≤ Real.log (Nat.factorial n) + ∑ m ∈ Finset.Icc 1 n, vonMangoldt m := by
    -- We'll use that $\sum_{m=1}^n \Lambda(m) \left\lfloor \frac{n}{m} \right\rfloor = \log(n!)$.
    have h_log_factorial : ∑ m ∈ Finset.Icc 1 n, (vonMangoldt m : ℝ) * Nat.floor (n / m) = Real.log (Nat.factorial n) := by
      -- By definition of von Mangoldt function, we know that $\sum_{d \mid m} \Lambda(d) = \log m$.
      have h_von_mangoldt : ∀ m : ℕ, 1 ≤ m → ∑ d ∈ Nat.divisors m, (ArithmeticFunction.vonMangoldt d : ℝ) = Real.log m := by
        exact fun m a => vonMangoldt_sum;
      -- Applying the definition of von Mangoldt function to the sum.
      have h_sum_von_mangoldt : ∑ m ∈ Finset.Icc 1 n, ∑ d ∈ Nat.divisors m, (ArithmeticFunction.vonMangoldt d : ℝ) = ∑ d ∈ Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt d : ℝ) * Nat.floor (n / d) := by
        have h_sum_von_mangoldt : ∑ m ∈ Finset.Icc 1 n, ∑ d ∈ Nat.divisors m, (ArithmeticFunction.vonMangoldt d : ℝ) = ∑ d ∈ Finset.Icc 1 n, ∑ m ∈ Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt d : ℝ) * (if d ∣ m then 1 else 0) := by
          rw [ Finset.sum_comm, Finset.sum_congr rfl ];
          simp +zetaDelta at *;
          intro x hx₁ hx₂; rw [ ← Finset.sum_filter ] ; congr; ext; simp +decide [ Nat.mem_divisors ] ;
          exact ⟨ fun h => ⟨ ⟨ Nat.pos_of_dvd_of_pos h.1 hx₁, Nat.le_trans ( Nat.le_of_dvd hx₁ h.1 ) hx₂ ⟩, h.1 ⟩, fun h => ⟨ h.2, by linarith ⟩ ⟩;
        simp_all +decide [ Finset.sum_ite ];
        refine' Finset.sum_congr rfl fun x hx => _;
        rw [ mul_comm, show Finset.filter ( fun y => x ∣ y ) ( Finset.Icc 1 n ) = Finset.image ( fun y => x * y ) ( Finset.Icc 1 ( n / x ) ) from ?_, Finset.card_image_of_injective _ fun y z h => mul_left_cancel₀ ( by linarith [ Finset.mem_Icc.mp hx ] ) h ];
        · norm_num;
        · ext y; simp [Finset.mem_image];
          exact ⟨ fun h => ⟨ y / x, ⟨ Nat.div_pos ( Nat.le_of_dvd h.1.1 h.2 ) ( Finset.mem_Icc.mp hx |>.1 ), Nat.div_le_div_right h.1.2 ⟩, Nat.mul_div_cancel' h.2 ⟩, by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ by nlinarith [ Finset.mem_Icc.mp hx |>.1 ], by nlinarith [ Finset.mem_Icc.mp hx |>.2, Nat.div_mul_le_self n x ] ⟩, by simp +decide ⟩ ⟩;
      rw [ ← h_sum_von_mangoldt, Finset.sum_congr rfl fun m hm => h_von_mangoldt m <| Finset.mem_Icc.mp hm |>.1 ];
      erw [ ← Real.log_prod ] <;> norm_cast <;> norm_num;
      · erw [ ← Nat.cast_prod, Finset.prod_Ico_id_eq_factorial ];
      · grind;
    -- Applying the inequality $\frac{n}{m} \leq \left\lfloor \frac{n}{m} \right\rfloor + 1$ to each term in the sum, we get:
    have h_ineq : ∀ m ∈ Finset.Icc 2 n, (vonMangoldt m : ℝ) * (n / m) ≤ (vonMangoldt m : ℝ) * Nat.floor (n / m) + (vonMangoldt m : ℝ) := by
      intros m hm
      have h_floor : (n / m : ℝ) ≤ Nat.floor (n / m) + 1 := by
        rw [ div_le_iff₀ ] <;> norm_cast <;> nlinarith [ Nat.div_add_mod n m, Nat.mod_lt n ( by linarith [ Finset.mem_Icc.mp hm ] : 0 < m ), Nat.lt_floor_add_one ( n / m ) ];
      simpa only [ mul_add, mul_one ] using mul_le_mul_of_nonneg_left h_floor <| by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by rw [ ArithmeticFunction.vonMangoldt_apply ] ; positivity ) ) ) ) ) ) ) ) ;
    refine le_trans ( Finset.sum_le_sum fun m hm => by simpa only [ div_mul_eq_mul_div, mul_div_assoc ] using h_ineq m hm ) ?_;
    rw [ ← h_log_factorial, Finset.sum_add_distrib ];
    exact add_le_add ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.Icc_subset_Icc ( by norm_num ) le_rfl ) fun _ _ _ => mul_nonneg ( by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg ) ( Nat.cast_nonneg _ ) ) ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.Icc_subset_Icc ( by norm_num ) le_rfl ) fun _ _ _ => by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg );
  convert div_le_div_of_nonneg_right h_rewrite ( Nat.cast_nonneg n ) using 2 <;> try rfl;
  · rw [ Finset.sum_div _ _ _ ] ; exact Finset.sum_congr rfl fun _ _ => by rw [ mul_div_cancel_right₀ _ ( by positivity ) ] ;
  · unfold chebyshevPsi;
    erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num

/-
log(n!) ≤ n*log(n) - n + 1 + log(n)
-/
lemma log_factorial_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial) ≤ n * Real.log n - n + 1 + Real.log n := by
  induction hn <;> simp_all +decide [ Nat.factorial_succ ];
  rw [ Real.log_mul ( by positivity ) ( by positivity ), add_comm ];
  have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( ↑‹ℕ› : ℝ ) / ( ↑‹ℕ› + 1 ) );
  rw [ Real.log_div ] at this <;> first | positivity | nlinarith [ mul_div_cancel₀ ( ( ↑‹ℕ› : ℝ ) : ℝ ) ( by positivity : ( ↑‹ℕ› + 1 : ℝ ) ≠ 0 ) ] ;

lemma sumS_le_logn_plus (n : ℕ) (hn : 200 ≤ n) :
    sumS n ≤ Real.log n + 0.418 := by
  -- By combining the results from the previous steps, we conclude the proof.
  have h_final : Real.log (n.factorial) + chebyshevPsi n ≤ n * Real.log n + 2 * n * Real.log 2 - n + 1 + Real.log n := by
    linarith [ log_factorial_le n ( by linarith ), chebyshevPsi_le n ( by linarith ) ];
  -- Divide both sides by $n$ and simplify the expression.
  have h_div : sumS n ≤ Real.log n + 2 * Real.log 2 - 1 + (Real.log n + 1) / n := by
    convert sumS_le_basic n ( by linarith ) |> le_trans <| div_le_div_of_nonneg_right ( h_final ) ( Nat.cast_nonneg _ ) using 1 <;> try rfl;
    ring_nf;
    simpa [ show n ≠ 0 by linarith ] using by ring;
  -- We'll use that $Real.log n + 1 \leq Real.log 200 + 1$ for $n \geq 200$.
  have h_log_bound : (Real.log n + 1) / n ≤ (Real.log 200 + 1) / 200 := by
    rw [ div_le_div_iff₀ ] <;> try positivity;
    have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( n : ℝ ) / 200 );
    rw [ Real.log_div ] at this <;> norm_num at * <;> nlinarith [ ( by norm_cast : ( 200 :ℝ ) ≤ n ), Real.le_log_iff_exp_le ( by positivity : ( 0 :ℝ ) < 200 ) |>.2 <| show ( Real.exp 1 :ℝ ) ≤ 200 by exact le_of_lt <| Real.exp_one_lt_d9.trans_le <| by norm_num ];
  -- We'll use that $Real.log 200 < 5.3$.
  have h_log_200 : Real.log 200 < 5.3 := by
    norm_num [ Real.log_lt_iff_lt_exp ];
    -- We can raise both sides to the power of 10 to remove the fraction.
    suffices h_exp : (200 : ℝ) ^ 10 < Real.exp 53 by
      contrapose! h_exp;
      exact le_trans ( by norm_num [ ← Real.exp_nat_mul ] ) ( pow_le_pow_left₀ ( by positivity ) h_exp 10 );
    have := Real.exp_one_gt_d9.le ; norm_num at * ; rw [ show Real.exp 53 = ( Real.exp 1 ) ^ 53 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_lt_of_le ( by norm_num ) ( pow_le_pow_left₀ ( by positivity ) this _ );
  have := Real.log_two_lt_d9 ; norm_num at * ; linarith

/-! # Tail bound -/

/-
-log P(n) ≤ T(n) + 1/10 via log series truncation
-/
lemma neg_log_prodP_le_sumT_plus (n : ℕ) (hn : 200 ≤ n) :
    -Real.log (prodP n) ≤ sumT n + 1/10 := by
  -- Let's rewrite the sum in terms of the prime number theorem and the bound we have.
  have h_sum_bound : ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), (-Real.log (1 - 1 / (p : ℝ)) - ∑ k ∈ Finset.Icc 1 (Nat.log p n), 1 / (k * (p : ℝ) ^ k)) ≤ 1 / 10 := by
    -- For each prime $p$, the tail $\sum_{k > \lfloor \log_p n \rfloor} \frac{1}{k p^k}$ is bounded by $\frac{1}{(K+1)(p-1)p^K}$ where $K = \lfloor \log_p n \rfloor$.
    have h_tail_bound : ∀ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), -Real.log (1 - 1 / (p : ℝ)) - ∑ k ∈ Finset.Icc 1 (Nat.log p n), 1 / (k * (p : ℝ) ^ k) ≤ 1 / ((Nat.log p n + 1) * (p - 1) * (p : ℝ) ^ (Nat.log p n)) := by
      intro p hp
      have h_tail_bound : -Real.log (1 - 1 / (p : ℝ)) - ∑ k ∈ Finset.Icc 1 (Nat.log p n), 1 / (k * (p : ℝ) ^ k) ≤ ∑' k : ℕ, 1 / ((Nat.log p n + k + 1) * (p : ℝ) ^ (Nat.log p n + k + 1)) := by
        have h_tail_bound : -Real.log (1 - 1 / (p : ℝ)) = ∑' k : ℕ, 1 / ((k + 1) * (p : ℝ) ^ (k + 1)) := by
          have := @Real.hasSum_pow_div_log_of_abs_lt_one ( 1 / ( p : ℝ ) ) ?_ <;> norm_num at *;
          · exact this.tsum_eq.symm ▸ rfl;
          · exact inv_lt_one_of_one_lt₀ <| mod_cast hp.2.one_lt;
        erw [ h_tail_bound, ← Summable.sum_add_tsum_nat_add ( Nat.log p n ) ];
        · erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ add_comm, add_left_comm, add_assoc ];
          norm_num [ Finset.sum_range_succ' ];
        · norm_num +zetaDelta at *;
          exact Summable.of_nonneg_of_le ( fun _ => by positivity ) ( fun k => mul_le_of_le_one_right ( by positivity ) <| inv_le_one_of_one_le₀ <| by linarith ) <| by simpa using summable_nat_add_iff 1 |>.2 <| summable_geometric_of_lt_one ( by positivity ) <| inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.2 hp.2.one_lt;
      -- We'll use the fact that $\sum_{k=K+1}^{\infty} \frac{1}{k p^k} \leq \frac{1}{(K+1)p^K} \sum_{k=0}^{\infty} \frac{1}{p^k}$.
      have h_sum_bound : ∑' k : ℕ, 1 / ((Nat.log p n + k + 1) * (p : ℝ) ^ (Nat.log p n + k + 1)) ≤ 1 / ((Nat.log p n + 1) * (p : ℝ) ^ (Nat.log p n + 1)) * ∑' k : ℕ, (1 / (p : ℝ)) ^ k := by
        rw [ ← tsum_mul_left ];
        refine' Summable.tsum_le_tsum _ _ _;
        · intro i; rw [ div_pow ] ; rw [ div_mul_div_comm ] ; rw [ div_le_div_iff₀ ] <;> norm_cast <;> ring_nf <;> norm_num;
          · exact Or.inr ⟨ ⟨ Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ), pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) _ ⟩, pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) _ ⟩;
          · exact Or.inr ⟨ ⟨ Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ), pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) _ ⟩, pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) _ ⟩;
        · refine Summable.of_nonneg_of_le ( fun k => by positivity ) ( fun k => ?_ ) ( (summable_nat_add_iff 1).mpr <| summable_geometric_of_lt_one ( by positivity ) ( inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr ( Finset.mem_filter.mp hp |>.2.one_lt ) ) );
          rw [ inv_pow, one_div ];
          refine inv_anti₀ ( pow_pos ( by exact_mod_cast ( Finset.mem_filter.mp hp |>.2.pos ) ) _ ) ?_;
          have hmid : ((p : ℝ)) ^ (k + 1) ≤ ((p : ℝ)) ^ (Nat.log p n + k + 1) :=
            pow_le_pow_right₀ ( by exact_mod_cast ( Finset.mem_filter.mp hp |>.2.one_lt.le ) ) ( by omega );
          exact le_trans hmid ( le_mul_of_one_le_left ( by positivity ) ( le_add_of_nonneg_left ( by positivity ) ) );
        · exact Summable.mul_left _ <| summable_geometric_of_lt_one ( by positivity ) <| by simpa using inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2;
      convert h_tail_bound.trans h_sum_bound using 1 <;> try rfl;
      rw [ tsum_geometric_of_lt_one ( by positivity ) ( by simpa using inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2 ) ] ; ring_nf;
      rw [ ← mul_inv ] ; congr ; nlinarith only [ inv_mul_cancel_left₀ ( show ( p : ℝ ) ≠ 0 by norm_cast; exact Nat.Prime.ne_zero ( Finset.mem_filter.mp hp |>.2 ) ) ( p ^ Nat.log p n ), inv_mul_cancel₀ ( show ( p : ℝ ) ≠ 0 by norm_cast; exact Nat.Prime.ne_zero ( Finset.mem_filter.mp hp |>.2 ) ), show ( p : ℝ ) ≥ 2 by norm_cast; exact Nat.Prime.two_le ( Finset.mem_filter.mp hp |>.2 ) ] ;
    -- Split the sum into two parts: one for primes $p \leq 13$ and one for primes $p > 13$.
    have h_split_sum : ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), (-Real.log (1 - 1 / (p : ℝ)) - ∑ k ∈ Finset.Icc 1 (Nat.log p n), 1 / (k * (p : ℝ) ^ k)) ≤ (∑ p ∈ Finset.filter Nat.Prime (Finset.range 14), 1 / ((Nat.log p n + 1) * (p - 1) * (p : ℝ) ^ (Nat.log p n))) + (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 17 (n)), 1 / ((1 + 1) * (p - 1) * (p : ℝ) ^ 1)) := by
      refine le_trans ( Finset.sum_le_sum h_tail_bound ) ?_;
      have h_split_sum : Finset.filter Nat.Prime (Finset.range (n + 1)) ⊆ Finset.filter Nat.Prime (Finset.range 14) ∪ Finset.filter Nat.Prime (Finset.Icc 17 n) := by
        simp +decide [ Finset.subset_iff ];
        exact fun p hp₁ hp₂ => if h : p < 14 then Or.inl ⟨ h, hp₂ ⟩ else Or.inr ⟨ ⟨ not_lt.mp fun h' => by interval_cases p <;> trivial, hp₁ ⟩, hp₂ ⟩;
      refine le_trans ( Finset.sum_le_sum_of_subset_of_nonneg h_split_sum ?_ ) ?_;
      · exact fun _ _ _ => one_div_nonneg.mpr ( mul_nonneg ( mul_nonneg ( by positivity ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( Nat.Prime.pos ( by aesop ) ) ) ) ) ( by positivity ) );
      · rw [ Finset.sum_union ];
        · gcongr;
          all_goals norm_num at *;
          any_goals linarith [ Nat.Prime.one_lt ( by tauto ) ];
          · exact mul_pos ( mul_pos two_pos ( sub_pos.mpr ( Nat.one_lt_cast.mpr ( by linarith ) ) ) ) ( Nat.cast_pos.mpr ( by linarith ) );
          · exact mul_nonneg ( by positivity ) ( sub_nonneg_of_le ( mod_cast Nat.Prime.pos ( by tauto ) ) );
          · exact Nat.le_log_of_pow_le ( by linarith ) ( by linarith );
          · exact Nat.le_log_of_pow_le ( by linarith ) ( by linarith );
        · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_range.mp ( Finset.mem_filter.mp hx₁ |>.1 ), Finset.mem_Icc.mp ( Finset.mem_filter.mp hx₂ |>.1 ) ] ;
    -- For primes $p \leq 13$, we can bound the sum individually.
    have h_small_primes : ∑ p ∈ Finset.filter Nat.Prime (Finset.range 14), 1 / ((Nat.log p n + 1) * (p - 1) * (p : ℝ) ^ (Nat.log p n)) ≤ 1 / 50 := by
      norm_num [ Finset.sum_filter, Finset.sum_range_succ ];
      -- Since $n \geq 200$, we have $\log_2 n \geq 7$, $\log_3 n \geq 4$, $\log_5 n \geq 3$, $\log_7 n \geq 2$, $\log_{11} n \geq 2$, and $\log_{13} n \geq 2$.
      have h_log_bounds : Nat.log 2 n ≥ 7 ∧ Nat.log 3 n ≥ 4 ∧ Nat.log 5 n ≥ 3 ∧ Nat.log 7 n ≥ 2 ∧ Nat.log 11 n ≥ 2 ∧ Nat.log 13 n ≥ 2 := by
        exact ⟨ Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ), Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ), Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ), Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ), Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ), Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ) ⟩;
      refine' le_trans ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 2 n : ℝ ) + 1 ≥ 8 by norm_cast; linarith ) ) ( by positivity ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 3 n : ℝ ) + 1 ≥ 5 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 5 n : ℝ ) + 1 ≥ 4 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 7 n : ℝ ) + 1 ≥ 3 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 11 n : ℝ ) + 1 ≥ 3 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 13 n : ℝ ) + 1 ≥ 3 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) _ ; norm_num;
      exact le_trans ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.1 ) ) ( by positivity ) ) ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.2.1 ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.2.2.1 ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.2.2.2.1 ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.2.2.2.2.1 ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.2.2.2.2.2 ) ) ( by positivity ) ) ) ( by norm_num );
    -- For primes $p > 13$, we can bound the sum using the fact that $\sum_{p \geq 17} \frac{1}{p(p-1)} \leq \frac{1}{32}$.
    have h_large_primes : ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 17 (n)), 1 / ((1 + 1) * (p - 1) * (p : ℝ)) ≤ 1 / 32 := by
      -- We'll use the fact that $\sum_{p \geq 17} \frac{1}{p(p-1)} \leq \frac{1}{32}$.
      have h_large_primes_bound : ∑ p ∈ Finset.Icc 17 n, (1 / ((p - 1) * (p : ℝ))) ≤ 1 / 16 := by
        -- We'll use the fact that $\sum_{p \geq 17} \frac{1}{p(p-1)}$ is a telescoping series.
        have h_telescoping : ∀ m : ℕ, 17 ≤ m → ∑ p ∈ Finset.Icc 17 m, (1 / ((p - 1) * (p : ℝ))) = 1 / 16 - 1 / (m : ℝ) := by
          intro m hm; induction hm <;> norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] at *;
          rw [ Finset.sum_Ioc_succ_top ( by linarith ), ‹∑ x ∈ Ioc 16 _, _ = _› ] ; norm_num;
          -- Combine and simplify the terms on the left-hand side.
          field_simp
          ring;
        exact h_telescoping n ( by linarith ) ▸ sub_le_self _ ( by positivity );
      norm_num [ ← mul_assoc, ← Finset.sum_mul _ _ _ ] at *;
      exact le_trans ( mul_le_mul_of_nonneg_right ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => mul_nonneg ( inv_nonneg.2 ( Nat.cast_nonneg _ ) ) ( inv_nonneg.2 ( sub_nonneg.2 ( Nat.one_le_cast.2 ( by linarith [ Finset.mem_Icc.1 ‹_› ] ) ) ) ) ) ( by norm_num ) ) ( by linarith );
    norm_num at * ; linarith;
  convert add_le_add_left h_sum_bound ( ∑ p ∈ Finset.filter Nat.Prime ( Finset.range ( n + 1 ) ), ∑ k ∈ Finset.Icc 1 ( Nat.log p n ), 1 / ( k * ( p : ℝ ) ^ k ) ) using 1;
  · unfold prodP; rw [ Real.log_prod ] <;> norm_num;
    exact fun p hp hp' => sub_ne_zero_of_ne <| by aesop;
  · rw [ add_comm, sumT ];
    -- Let's rewrite the sum $\sum_{m=2}^n \frac{\Lambda(m)}{m \log m}$ using the definition of $\Lambda$.
    have h_sum_eq : ∑ m ∈ Finset.Icc 2 n, (ArithmeticFunction.vonMangoldt m : ℝ) / (m * Real.log m) = ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (ArithmeticFunction.vonMangoldt (p^k) : ℝ) / (p^k * Real.log (p^k)) := by
      have h_sum_eq : Finset.filter (fun m => ArithmeticFunction.vonMangoldt m ≠ 0) (Finset.Icc 2 n) = Finset.biUnion (Finset.filter Nat.Prime (Finset.range (n + 1))) (fun p => Finset.image (fun k => p^k) (Finset.Icc 1 (Nat.log p n))) := by
        ext m; simp [ArithmeticFunction.vonMangoldt];
        constructor;
        · rintro ⟨ ⟨ hm₁, hm₂ ⟩, hm₃, hm₄, hm₅, hm₆ ⟩;
          obtain ⟨ p, k, hp, hk, rfl ⟩ := hm₃;
          exact ⟨ p, ⟨ by linarith [ Nat.le_self_pow hk.ne' p ], hp.nat_prime ⟩, k, ⟨ hk, Nat.le_log_of_pow_le hp.nat_prime.one_lt hm₂ ⟩, rfl ⟩;
        · rintro ⟨ p, ⟨ hp₁, hp₂ ⟩, k, ⟨ hk₁, hk₂ ⟩, rfl ⟩;
          exact ⟨ ⟨ one_lt_pow₀ hp₂.one_lt ( by linarith ), Nat.pow_le_of_le_log ( by linarith ) hk₂ ⟩, hp₂.isPrimePow.pow ( by linarith ), Nat.ne_of_gt ( Nat.minFac_pos _ ), ne_of_gt ( one_lt_pow₀ hp₂.one_lt ( by linarith ) ), by linarith ⟩;
      have h_sum_eq : ∑ m ∈ Finset.Icc 2 n, (ArithmeticFunction.vonMangoldt m : ℝ) / (m * Real.log m) = ∑ m ∈ Finset.filter (fun m => ArithmeticFunction.vonMangoldt m ≠ 0) (Finset.Icc 2 n), (ArithmeticFunction.vonMangoldt m : ℝ) / (m * Real.log m) := by
        rw [ Finset.sum_filter_of_ne ] ; aesop;
      rw [ h_sum_eq, ‹ { m ∈ Icc 2 n | Λ m ≠ 0 } = _ ›, Finset.sum_biUnion ];
      · exact Finset.sum_congr rfl fun p hp => by rw [ Finset.sum_image <| by intros a ha b hb hab; exact Nat.pow_right_injective ( Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2 ) hab ] ; norm_cast;
      · intros p hp q hq hpq; simp_all +decide [ Finset.disjoint_left ];
        intro a x hx₁ hx₂ hx₃ y hy₁ hy₂ hy₃; subst_vars; have := Nat.Prime.dvd_of_dvd_pow hp.2 ( hy₃.symm ▸ dvd_pow_self _ ( by linarith ) ) ; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;
    rw [ h_sum_eq ];
    refine' congr rfl ( Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun k hk => _ );
    rw [ ArithmeticFunction.vonMangoldt_apply ];
    rw [ if_pos ];
    · rw [ Nat.pow_minFac ] <;> norm_num [ Nat.Prime.ne_zero ( Finset.mem_filter.mp hp |>.2 ) ];
      · rw [ Nat.Prime.minFac_eq ( Finset.mem_filter.mp hp |>.2 ) ] ; ring_nf;
        rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( Nat.one_lt_cast.mpr ( Nat.Prime.one_lt ( Finset.mem_filter.mp hp |>.2 ) ) ) ) ), one_mul ];
      · grind;
    · exact Nat.Prime.isPrimePow ( Finset.mem_filter.mp hp |>.2 ) |> fun h => h.pow ( by linarith [ Finset.mem_Icc.mp hk ] )

/-! ### Helper lemmas for sumT_sub_199_bound -/

lemma log_factorial_ge' (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial) ≥ n * Real.log n - n + 1 := by
  induction hn <;> simp_all +decide [ Nat.factorial ]
  rw [ Real.log_mul ( by positivity ) ( by positivity ) ]
  have h_log : ∀ m : ℕ, 1 ≤ m → Real.log (m + 1) ≤ Real.log m + 1 / m := by
    intro m hm; rw [ Real.log_le_iff_le_exp ( by positivity ) ] ; rw [ Real.exp_add, Real.exp_log ( by positivity ) ]
    nlinarith [ Real.add_one_le_exp ( 1 / ( m : ℝ ) ), one_div_mul_cancel ( by positivity : ( m : ℝ ) ≠ 0 ) ]
  have := h_log _ ‹_›; norm_num at *; nlinarith [ inv_mul_cancel₀ ( by positivity : ( ( Nat.cast:ℕ →ℝ ) ‹_› ) ≠ 0 ) ]

lemma sumS_ge_log_sub_one (n : ℕ) (hn : 2 ≤ n) :
    sumS n ≥ Real.log n - 1 := by
  have h_sum_floor : ∑ m ∈ Finset.Icc 1 n, vonMangoldt m * Nat.floor (n / m) = Real.log (Nat.factorial n) := by
    have h_sum_floor : ∑ k ∈ Finset.Icc 1 n, ∑ d ∈ Nat.divisors k, vonMangoldt d = Real.log (Nat.factorial n) := by
      have h_sum_floor : ∀ k ∈ Finset.Icc 1 n, ∑ d ∈ Nat.divisors k, vonMangoldt d = Real.log k := by
        exact fun _ _ => vonMangoldt_sum
      rw [ Finset.sum_congr rfl h_sum_floor ]
      exact Nat.recOn n ( by norm_num ) fun n ih => by simp_all +decide [ Nat.factorial_succ, Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] ; rw [ Real.log_mul ( by positivity ) ( by positivity ) ] ; linarith
    have h_interchange : ∑ k ∈ Finset.Icc 1 n, ∑ d ∈ Nat.divisors k, vonMangoldt d = ∑ d ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, vonMangoldt d * (if d ∣ k then 1 else 0) := by
      rw [ Finset.sum_comm, Finset.sum_congr rfl ]
      simp +contextual [ Finset.sum_ite ]
      intro x hx₁ hx₂; rw [ ← Finset.sum_subset ( show x.divisors ⊆ Finset.filter ( fun d => d ∣ x ) ( Finset.Icc 1 n ) from fun y hy => Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ Nat.pos_of_mem_divisors hy, Nat.le_trans ( Nat.le_of_dvd hx₁ <| Nat.dvd_of_mem_divisors hy ) hx₂ ⟩, Nat.dvd_of_mem_divisors hy ⟩ ) ] ; aesop
    have h_inner : ∀ d ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, (if d ∣ k then 1 else 0) = Nat.floor (n / d) := by
      intros d hd
      have h_divisors : Finset.filter (fun k => d ∣ k) (Finset.Icc 1 n) = Finset.image (fun k => d * k) (Finset.Icc 1 (n / d)) := by
        ext k; simp [Finset.mem_image]
        exact ⟨ fun h => ⟨ k / d, ⟨ Nat.div_pos ( Nat.le_of_dvd h.1.1 h.2 ) ( Finset.mem_Icc.mp hd |>.1 ), Nat.div_le_div_right h.1.2 ⟩, Nat.mul_div_cancel' h.2 ⟩, by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ by nlinarith [ Finset.mem_Icc.mp hd |>.1 ], by nlinarith [ Finset.mem_Icc.mp hd |>.2, Nat.div_mul_le_self n d ] ⟩, by norm_num ⟩ ⟩
      simp_all +decide [ Finset.sum_ite ]
      rw [ Finset.card_image_of_injective _ fun x y hxy => mul_left_cancel₀ ( by linarith ) hxy ] ; aesop
    simp_all +decide [ Finset.sum_ite ]
    exact Eq.trans ( Finset.sum_congr rfl fun x hx => by rw [ h_inner x ( Finset.mem_Icc.mp hx |>.1 ) ( Finset.mem_Icc.mp hx |>.2 ) ] ; ring ) h_sum_floor
  have h_floor_le : ∑ m ∈ Finset.Icc 1 n, vonMangoldt m * Nat.floor (n / m) ≤ n * ∑ m ∈ Finset.Icc 1 n, vonMangoldt m / (m : ℝ) := by
    rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_le_sum fun x hx => _ ; rcases eq_or_ne x 0 with rfl | hx' <;> simp_all +decide ; ring_nf
    rw [ mul_assoc ] ; exact mul_le_mul_of_nonneg_left ( by rw [ ← div_eq_mul_inv ] ; exact ( by rw [ le_div_iff₀ ( by positivity ) ] ; norm_cast; linarith [ Nat.div_mul_le_self n x ] ) ) ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact by rw [ ArithmeticFunction.vonMangoldt_apply ] ; positivity ) ) ) ) ) ) ) ) ) ) ) ) ) ) )
  have h_sum_eq : ∑ m ∈ Finset.Icc 1 n, vonMangoldt m / (m : ℝ) = sumS n := by
    rw [ Finset.Icc_eq_cons_Ioc ( by linarith ), Finset.sum_cons ] ; aesop
  nlinarith [ show ( n : ℝ ) ≥ 2 by norm_cast, Real.log_le_sub_one_of_pos ( by positivity : 0 < ( n : ℝ ) ), log_factorial_ge' n ( by linarith ) ]

lemma sumS_mono {a b : ℕ} (h : a ≤ b) : sumS a ≤ sumS b := by
  exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.Icc_subset_Icc_right h ) fun _ _ _ ↦ div_nonneg ( by
    exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg ) ( by norm_cast; linarith [ Finset.mem_Icc.mp ‹_› ] )

lemma div_sub_le_log_sub' {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) / b ≤ Real.log b - Real.log a := by
  have h_mul : b - a ≤ b * (Real.log b - Real.log a) := by
    have := Real.log_le_sub_one_of_pos ( div_pos ha ( show 0 < b by linarith ) )
    rw [ Real.log_div ] at this <;> nlinarith [ mul_div_cancel₀ a ( by linarith : b ≠ 0 ) ]
  rwa [ div_le_iff₀' ( by linarith ) ]

lemma sum_log_ratio_le_log_log' (a n : ℕ) (ha : 3 ≤ a) (hn : a ≤ n) :
    ∑ m ∈ Finset.Ico a n,
      (Real.log (↑m + 1) - Real.log m) / Real.log (↑m + 1) ≤
    Real.log (Real.log n) - Real.log (Real.log a) := by
  have h_term : ∀ m ∈ Finset.Ico a n, (Real.log (m + 1) - Real.log m) / Real.log (m + 1) ≤ Real.log (Real.log (m + 1)) - Real.log (Real.log m) := by
    intro m hm
    rw [ ← Real.log_div ( ne_of_gt <| Real.log_pos <| by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) ( ne_of_gt <| Real.log_pos <| by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) ]
    convert Real.one_sub_inv_le_log_of_pos _ using 1
    · rw [ inv_div, sub_div, div_self <| ne_of_gt <| Real.log_pos <| by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ]
    · exact div_pos ( Real.log_pos ( by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) ) ( Real.log_pos ( by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) )
  refine le_trans ( Finset.sum_le_sum h_term ) ( le_of_eq ?_ )
  clear h_term
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ N hN ih => rw [ Finset.sum_Ico_succ_top hN, ih ]; push_cast; ring

lemma log_200_ge' : Real.log 200 ≥ 1418 / 270 := by
  have h_log_200 : Real.log 200 = 3 * Real.log 2 + 2 * Real.log 5 := by
    norm_num [ ← Real.log_rpow, ← Real.log_mul ]
  rw [ h_log_200, show ( 5 : ℝ ) = 2 ^ 2 * 1.25 by norm_num, Real.log_mul, Real.log_pow ] <;> ring_nf <;> norm_num
  have := Real.log_two_gt_d9 ; norm_num at * ; have := Real.log_inv ( 5 / 4 ) ; norm_num at * ; linarith [ Real.log_le_sub_one_of_pos ( show 0 < 4 / 5 by norm_num ) ]

lemma abel_identity_sumT (n : ℕ) (hn : 200 ≤ n) :
    ∑ m ∈ Finset.Icc 200 n, (Λ m) / (m * Real.log m) = ((sumS n) - (sumS 199)) / Real.log n + ∑ m ∈ Finset.Ico 200 n, ((sumS m) - (sumS 199)) * (1 / Real.log m - 1 / Real.log (m + 1)) := by
  induction' hn with k hk
  · simp only [Finset.Icc_self, Finset.sum_singleton, Finset.Ico_self, Finset.sum_empty, add_zero]
    unfold sumS
    rw [Finset.sum_Icc_succ_top (by norm_num : 2 ≤ 200)]
    push_cast
    ring
  · simp_all +decide [(Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc)]
    rw [ Finset.sum_Ioc_succ_top ( by linarith ), ‹∑ x ∈ Ioc 199 k, _ = _› ]
    rw [ Finset.sum_Ico_succ_top ( by linarith ), show sumS ( k + 1 ) = sumS k + Λ ( k + 1 ) / ( k + 1 : ℝ ) from ?_ ]
    · norm_num [ div_eq_mul_inv ] ; ring
    · exact_mod_cast Finset.sum_Ioc_succ_top ( by linarith ) _

/-
T(n) - T(199) ≤ log(log n) - log(log 199) + 27/100, using Abel summation and S(m) ≤ log m + 0.418
-/
lemma sumT_sub_199_bound (n : ℕ) (hn : 200 ≤ n) :
    sumT n ≤ sumT 199 + Real.log (Real.log ↑n) - Real.log (Real.log 199) + 27/100 := by
  -- Step 1: Split sumT
  have h_split : sumT n = sumT 199 + ∑ m ∈ Finset.Icc 200 n, vonMangoldt m / (m * Real.log m) := by
    unfold sumT; erw [ Finset.sum_Ico_consecutive ] <;> norm_cast ; linarith
  rw [h_split]
  -- Step 2: Abel summation identity
  have h_identity := abel_identity_sumT n hn
  -- Step 3: Bound the Abel sum terms
  have h_bound : (∑ m ∈ Finset.Ico 200 n, ((sumS m) - (sumS 199)) * (1 / Real.log m - 1 / Real.log (m + 1))) ≤ (∑ m ∈ Finset.Ico 200 n, ((Real.log m - Real.log 199 + 1.418) * (1 / Real.log m - 1 / Real.log (m + 1)))) := by
    refine Finset.sum_le_sum fun m hm => mul_le_mul_of_nonneg_right ?_ ?_ <;> norm_num at *
    · have := sumS_le_logn_plus m ( by linarith ) ; ( have := sumS_ge_log_sub_one 199 ( by norm_num ) ; ( norm_num at * ; linarith ) )
    · exact inv_anti₀ ( Real.log_pos <| by norm_cast; linarith ) ( Real.log_le_log ( by norm_cast; linarith ) <| by linarith )
  -- Step 4: Expand and telescope the sum
  have h_expand : ∑ m ∈ Finset.Ico 200 n, ((Real.log m - Real.log 199 + 1.418) * (1 / Real.log m - 1 / Real.log (m + 1))) = ∑ m ∈ Finset.Ico 200 n, ((Real.log (m + 1) - Real.log m) / Real.log (m + 1)) + (1.418 - Real.log 199) * (1 / Real.log 200 - 1 / Real.log n) := by
    have h_expand : ∀ m ∈ Finset.Ico 200 n, ((Real.log m - Real.log 199 + 1.418) * (1 / Real.log m - 1 / Real.log (m + 1))) = ((Real.log (m + 1) - Real.log m) / Real.log (m + 1)) + (1.418 - Real.log 199) * (1 / Real.log m - 1 / Real.log (m + 1)) := by
      intro m hm; ring_nf
      rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) ) ) ] ; ring
    rw [ Finset.sum_congr rfl h_expand, Finset.sum_add_distrib ]
    norm_num [ Finset.sum_Ico_eq_sum_range ]
    rw [ ← Finset.mul_sum _ _ _ ]
    exact congrArg _ ( by convert Finset.sum_range_sub' _ _ using 3 <;> push_cast [ Nat.cast_sub hn ] <;> ring_nf )
  -- Step 5: Apply log ratio telescoping bound
  have h_log_ratio : ∑ m ∈ Finset.Ico 200 n, ((Real.log (m + 1) - Real.log m) / Real.log (m + 1)) ≤ Real.log (Real.log n) - Real.log (Real.log 200) := by
    convert sum_log_ratio_le_log_log' 200 n ( by norm_num ) hn using 1 <;> norm_num
  -- Step 6: Bound the boundary term
  have h_sumS_le : (sumS n - sumS 199) / Real.log n ≤ (Real.log n + 0.418 - (Real.log 199 - 1)) / Real.log n := by
    gcongr
    · exact sumS_le_logn_plus n hn
    · exact sumS_ge_log_sub_one 199 ( by norm_num )
  -- Step 7: Numerical bound
  have h_num : 1 + (1.418 - Real.log 199) / Real.log 200 + Real.log (Real.log 199) - Real.log (Real.log 200) ≤ 27 / 100 := by
    have h_log_diff : Real.log (Real.log 200) - Real.log (Real.log 199) ≥ (Real.log 200 - Real.log 199) / Real.log 200 := by
      exact div_sub_le_log_sub' ( show 0 < Real.log 199 by positivity ) ( show Real.log 199 ≤ Real.log 200 by gcongr ; norm_num )
    ring_nf at *
    nlinarith [ inv_mul_cancel₀ ( show Real.log 200 ≠ 0 by positivity ), Real.log_pos ( show 199 > 1 by norm_num ), Real.log_lt_log ( by norm_num ) ( show 200 > 199 by norm_num ), show Real.log 200 ≥ 1418 / 270 from log_200_ge' ]
  -- Step 8: Combine all bounds
  ring_nf at *
  nlinarith [ inv_pos.mpr ( Real.log_pos ( show ( n : ℝ ) > 1 by norm_cast; linarith ) ), inv_pos.mpr ( Real.log_pos ( show ( 200 : ℝ ) > 1 by norm_num ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show ( n : ℝ ) > 1 by norm_cast; linarith ) ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show ( 200 : ℝ ) > 1 by norm_num ) ) ), Real.log_pos ( show ( n : ℝ ) > 1 by norm_cast; linarith ), Real.log_pos ( show ( 200 : ℝ ) > 1 by norm_num ) ]

/-
Computational upper bound on T(199)
-/
lemma sumT_199_lt : sumT 199 < 23/10 := by
  -- By definition of sumT, we can rewrite the sum as a sum over prime powers.
  have h_sum_prime_powers : ∀ n : ℕ, sumT n = ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 n), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (1 / (p^k * k : ℝ)) := by
    intro n
    have h_sumT_prime_powers : ∀ m ∈ Finset.Icc 2 n, vonMangoldt m = ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 n), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (if m = p^k then Real.log p else 0) := by
      intro m hm
      by_cases hm_prime_power : ∃ p k : ℕ, Nat.Prime p ∧ k ≥ 1 ∧ m = p^k ∧ p^k ≤ n;
      · obtain ⟨ p, k, hp, hk, rfl, hk' ⟩ := hm_prime_power; simp +decide [Finset.sum_ite] ;
        rw [ Finset.sum_eq_single p ];
        · rw [ Finset.card_eq_one.mpr ] <;> norm_num [ hp, hk ];
          · rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega), ArithmeticFunction.vonMangoldt_apply_prime hp];
          · exact ⟨ k, Finset.eq_singleton_iff_unique_mem.mpr ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hk, Nat.le_log_of_pow_le hp.one_lt hk' ⟩, rfl ⟩, fun x hx => Nat.pow_right_injective hp.one_lt <| Finset.mem_filter.mp hx |>.2.symm ⟩ ⟩;
        · intro q hq hqp; simp_all +decide [ Finset.ext_iff ] ;
          exact Or.inl fun a ha₁ ha₂ ha₃ => hqp <| by have := congr_arg ( ·.factorization ( q : ℕ ) ) ha₃; norm_num at this; have := congr_arg ( ·.factorization ( p : ℕ ) ) ha₃; norm_num at this; aesop;
        · exact fun h => False.elim <| h <| Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hp.two_le, by linarith [ pow_le_pow_right₀ hp.one_lt.le hk ] ⟩, hp ⟩;
      · rw [ ArithmeticFunction.vonMangoldt_apply ];
        rw [ if_neg ];
        · exact Eq.symm ( Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun k hk => if_neg fun h => hm_prime_power ⟨ p, k, Finset.mem_filter.mp hp |>.2, Finset.mem_Icc.mp hk |>.1, h, by linarith [ Finset.mem_Icc.mp hm, Finset.mem_Icc.mp hk |>.2, Nat.pow_log_le_self p ( show m ≠ 0 by linarith [ Finset.mem_Icc.mp hm ] ) ] ⟩ );
        · contrapose! hm_prime_power;
          rw [ isPrimePow_nat_iff ] at hm_prime_power ; aesop;
    -- By interchanging the order of summation, we can rewrite the sum.
    have h_interchange : ∑ m ∈ Finset.Icc 2 n, (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 n), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (if m = p^k then Real.log p else 0)) / (m * Real.log m) = ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 n), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (Real.log p) / (p^k * Real.log (p^k)) := by
      simp +decide only [Finset.sum_div _ _ _];
      rw [ Finset.sum_comm, Finset.sum_congr rfl ];
      intro p hp; rw [ Finset.sum_comm ] ; simp +decide [ div_eq_mul_inv ] ;
      exact Finset.sum_congr rfl fun x hx => if_pos ⟨ le_trans ( Nat.Prime.two_le ( Finset.mem_filter.mp hp |>.2 ) ) ( Nat.le_self_pow ( by linarith [ Finset.mem_Icc.mp hx ] ) _ ), Nat.pow_le_of_le_log ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ) ] ) ( by linarith [ Finset.mem_Icc.mp hx ] ) ⟩;
    convert h_interchange using 2;
    · exact Finset.sum_congr rfl fun x hx => h_sumT_prime_powers x hx ▸ rfl;
    · norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
      exact Finset.sum_congr rfl fun _ _ => by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( Nat.one_lt_cast.mpr ( Nat.Prime.one_lt ( by aesop ) ) ) ) ) ] ; ring;
  rw [ h_sum_prime_powers ]; clear h_sum_prime_powers
  have hq : (∑ p ∈ (Finset.Icc 2 199).filter Nat.Prime,
      ∑ k ∈ Finset.Icc 1 (Nat.log p 199), (1 / ((p : ℚ) ^ k * (k : ℚ)))) < 23 / 10 := by
    decide +kernel
  have hR : ((∑ p ∈ (Finset.Icc 2 199).filter Nat.Prime,
      ∑ k ∈ Finset.Icc 1 (Nat.log p 199), (1 / ((p : ℚ) ^ k * (k : ℚ))) : ℚ) : ℝ) < ((23 / 10 : ℚ) : ℝ) := by
    exact_mod_cast hq
  push_cast at hR
  exact hR

/-
Lower bound on log(log 199)
-/
lemma log_log_199_gt : Real.log (Real.log 199) > 163/100 := by
  -- We'll use that $Real.log 199 > 5.11$.
  have h_log_199 : Real.log 199 > 5.11 := by
    norm_num [ Real.lt_log_iff_exp_lt ];
    -- We can raise both sides to the power of 100 to remove the fraction.
    suffices h_exp : Real.exp 511 < 199 ^ 100 by
      contrapose! h_exp;
      exact le_trans ( pow_le_pow_left₀ ( by norm_num ) h_exp 100 ) ( by norm_num [ ← Real.exp_nat_mul ] );
    have := Real.exp_one_lt_d9.le;
    -- We can raise both sides to the power of 511 to remove the fraction.
    have : Real.exp 511 ≤ (2.7182818286 : ℝ) ^ 511 := by
      exact le_trans ( by norm_num [ ← Real.exp_nat_mul ] ) ( pow_le_pow_left₀ ( by positivity ) this _ );
    grind;
  refine' lt_of_lt_of_le _ ( Real.log_le_log ( by positivity ) h_log_199.le );
  rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
  have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 163 = ( Real.exp 1 ) ^ 163 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num )

lemma neg_log_prodP_bound (n : ℕ) (hn : 200 ≤ n) :
    -Real.log (prodP n) < Real.log (Real.log n) + 1.095 := by
  have h1 := neg_log_prodP_le_sumT_plus n hn
  have h2 := sumT_sub_199_bound n hn
  have h3 := sumT_199_lt
  have h4 := log_log_199_gt
  -- -log P(n) ≤ T(n) + 1/10
  --           ≤ T(199) + log(log n) - log(log 199) + 27/100 + 1/10
  --           < 23/10 + log(log n) - 163/100 + 27/100 + 1/10
  --           = log(log n) + (2300 + 270 + 100 - 1630)/1000
  --           = log(log n) + 1040/1000 = log(log n) + 1.04
  --           < log(log n) + 1.095
  linarith

/-! # Finite Check -/

lemma prodP_le_of_le {m n : ℕ} (h : m ≤ n) : prodP n ≤ prodP m := by
  unfold prodP;
  rw [ ← Finset.prod_sdiff ( Finset.filter_subset_filter _ <| Finset.range_mono <| Nat.succ_le_succ h ) ];
  exact mul_le_of_le_one_left ( Finset.prod_nonneg fun _ _ => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop ) <| Finset.prod_le_one₀ ( fun _ _ => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop ) fun _ _ => sub_le_self _ <| by positivity;

lemma mertens_finite_check (n : ℕ) (hn3 : 3 ≤ n) (hn199 : n ≤ 199) :
    1 / (3 * Real.log n) ≤ prodP n := by
  by_cases hn : n ≤ 10;
  · interval_cases n <;> norm_num [ Finset.prod_filter, Finset.prod_range_succ, prodP ];
    any_goals rw [ inv_mul_le_iff₀ ( by positivity ) ];
    any_goals rw [ inv_le_comm₀ ] <;> norm_num [ Real.le_log_iff_exp_le ];
    any_goals rw [ ← div_le_iff₀ ] <;> norm_num [ Real.le_log_iff_exp_le ];
    any_goals positivity;
    any_goals have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show ( 5 : ℝ ) / 4 = 1 + 1 / 4 by norm_num, Real.exp_add ] ; nlinarith [ Real.exp_pos ( 1 / 4 ), Real.exp_neg ( 1 / 4 ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( 1 / 4 ) ) ), Real.add_one_le_exp ( 1 / 4 ), Real.add_one_le_exp ( - ( 1 / 4 ) ) ];
    any_goals have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show ( 35 / 24 : ℝ ) = 1 + 11 / 24 by norm_num, Real.exp_add ] ; nlinarith [ Real.exp_pos ( 11 / 24 ), Real.exp_neg ( 11 / 24 ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( 11 / 24 ) ) ), Real.add_one_le_exp ( 11 / 24 ), Real.add_one_le_exp ( - ( 11 / 24 ) ) ];
    · exact Real.exp_one_lt_d9.le.trans <| by norm_num;
    · exact Real.exp_one_lt_d9.le.trans ( by norm_num );
  · by_cases hn : n ≤ 30;
    · -- For $11 \leq n \leq 30$, we use the fact that $prodP(n) \geq prodP(30)$ and $prodP(30) \geq 1/7$.
      have h_prod_bound : prodP n ≥ prodP 30 := by
        exact prodP_le_of_le hn
      have h_prod_30 : prodP 30 ≥ 1 / 7 := by
        unfold prodP
        have hq : (1 / 7 : ℚ) ≤ ∏ p ∈ (Finset.range (30 + 1)).filter Nat.Prime, (1 - 1 / (p : ℚ)) := by
          decide +kernel
        have hR : ((1 / 7 : ℚ) : ℝ) ≤ ((∏ p ∈ (Finset.range (30 + 1)).filter Nat.Prime, (1 - 1 / (p : ℚ)) : ℚ) : ℝ) := by
          exact_mod_cast hq
        push_cast at hR
        exact hR
      have h_log_bound : 7 ≤ 3 * Real.log 11 := by
        norm_num [ ← Real.log_rpow, Real.le_log_iff_exp_le ] at *;
        have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 7 = ( Real.exp 1 ) ^ 7 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num ) ;
      have h_final : 1 / (3 * Real.log n) ≤ 1 / 7 := by
        exact one_div_le_one_div_of_le ( by positivity ) ( by linarith [ Real.log_le_log ( by positivity ) ( show ( n : ℝ ) ≥ 11 by norm_cast; linarith ) ] )
      exact le_trans h_final (le_trans h_prod_30 h_prod_bound);
    · have h_prodP_199 : prodP 199 ≥ 1 / 10 := by
        unfold prodP
        have hq : (1 / 10 : ℚ) ≤ ∏ p ∈ (Finset.range (199 + 1)).filter Nat.Prime, (1 - 1 / (p : ℚ)) := by
          decide +kernel
        have hR : ((1 / 10 : ℚ) : ℝ) ≤ ((∏ p ∈ (Finset.range (199 + 1)).filter Nat.Prime, (1 - 1 / (p : ℚ)) : ℚ) : ℝ) := by
          exact_mod_cast hq
        push_cast at hR
        exact hR
      have h_log_bound : Real.log n ≥ 10 / 3 := by
        rw [ ge_iff_le, div_le_iff₀' ] <;> norm_num;
        rw [ ← Real.log_rpow, Real.le_log_iff_exp_le ] <;> norm_cast <;> try linarith;
        · exact le_trans ( by have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show Real.exp 10 = ( Real.exp 1 ) ^ 10 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num ) ) ( Nat.cast_le.mpr ( Nat.pow_le_pow_left ( show n ≥ 31 by linarith ) 3 ) );
        · positivity;
      exact le_trans ( by rw [ div_le_iff₀ ] <;> linarith ) ( h_prodP_199.trans ( prodP_le_of_le ( by linarith ) ) )

/-! # Main Theorem -/

theorem mertens_third_theorem (n : ℕ) (hn : 3 ≤ n) :
    1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
  by_cases hn2 : n ≥ 200;
  · have := neg_log_prodP_bound n hn2;
    -- Exponentiating both sides, we get $prodP n > \frac{1}{3 \log n}$.
    have h_exp : prodP n > 1 / (3 * Real.log n) := by
      have h_exp : Real.log (prodP n) > -Real.log (3 * Real.log n) := by
        rw [ Real.log_mul ] <;> norm_num;
        · have h_log3 : Real.log 3 > 1.095 := by
            norm_num [ Real.log_lt_log ];
            rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
            have hexp1 := Real.exp_one_lt_d9.le ; norm_num1 at hexp1 ⊢ ; rw [ show Real.exp 219 = ( Real.exp 1 ) ^ 219 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) hexp1 _ ) ( by norm_num );
          linarith;
        · grind;
      rw [ gt_iff_lt, Real.lt_log_iff_exp_lt ] at h_exp;
      · simpa [ Real.exp_neg, Real.exp_log ( show 0 < 3 * Real.log n by exact mul_pos zero_lt_three ( Real.log_pos ( by norm_cast; linarith ) ) ) ] using h_exp;
      · exact Finset.prod_pos fun p hp => sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith [ Finset.mem_filter.mp hp, Nat.Prime.two_le <| Finset.mem_filter.mp hp |>.2 ] ;
    exact h_exp.le;
  · -- Apply the finite check lemma to conclude the proof.
    apply mertens_finite_check n hn (by linarith)


end

end MertensThirdProof

/-- (A2) **Mertens' third theorem** (lower-bound form used by the paper) —
    now a THEOREM, derived from `mertens_third_theorem` above with `c₀ = 1/3`:
    the `y = 2` case is a direct computation (`∏ = 1/2`, `log 4 > 2/3`), and
    `y ≥ 3` follows from the main bound plus `log y ≤ log (2y)`. -/
theorem mertens_third_lower :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ y : ℕ, 2 ≤ y →
      c₀ / Real.log (2 * (y : ℝ)) ≤
        ∏ p ∈ (Finset.range (y + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
  refine ⟨1/3, by norm_num, fun y hy => ?_⟩
  have hy2r : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlog2y : (0 : ℝ) < Real.log (2 * (y : ℝ)) := by
    apply Real.log_pos; nlinarith
  rcases Nat.lt_or_ge y 3 with h3 | h3
  · -- y = 2: the product over primes ≤ 2 is 1/2 and log 4 > 2/3
    have hy2 : y = 2 := le_antisymm (Nat.lt_succ_iff.mp h3) hy
    subst hy2
    have hprod : ∏ p ∈ (Finset.range 3).filter Nat.Prime, (1 - 1 / (p : ℝ)) = 1/2 := by
      norm_num [Finset.prod_filter, Finset.prod_range_succ]
    rw [hprod]
    have hlog4 : Real.log (2 * ((2 : ℕ) : ℝ)) ≥ 2/3 := by
      have h24 : (2 * ((2 : ℕ) : ℝ)) = 4 := by norm_num
      rw [h24, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have hl2 := Real.log_two_gt_d9
      push_cast; nlinarith
    rw [div_le_iff₀ hlog2y]
    nlinarith [hlog4]
  · -- y ≥ 3: Woett's bound + log monotonicity
    have h1 := mertens_third_theorem y h3
    have hy1 : (1 : ℝ) < (y : ℝ) := by exact_mod_cast (by linarith : 1 < y)
    have hlogy : (0 : ℝ) < Real.log (y : ℝ) := Real.log_pos hy1
    have hmono : Real.log (y : ℝ) ≤ Real.log (2 * (y : ℝ)) :=
      Real.log_le_log (by linarith) (by linarith)
    have step : (1 : ℝ)/3 / Real.log (2 * (y : ℝ)) ≤ 1 / (3 * Real.log (y : ℝ)) := by
      rw [show (1 : ℝ)/3 / Real.log (2 * (y : ℝ)) = 1 / (3 * Real.log (2 * (y : ℝ))) by ring]
      apply one_div_le_one_div_of_le
      · linarith
      · linarith
    exact le_trans step h1


/-! ## The sole deep external input (A3): almost-all binary Goldbach. -/

/-- The only deep input not formalized in this file.  It is precisely the paper's statement that
the exceptional set of even integers which are not sums of two primes has density zero. -/
structure DeepInputs : Prop where
  goldbach_ae :
      CountIsLittleO
        (fun n => Even n ∧ ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q)


/-! ## Section 4.2 + (A1) -- sigma-avoidance: (A1) sum over primes p == -1 (mod q) of 1/p diverges (from Mathlib); then the set of n with q not dividing sigma(n) has density 0. -/


/-- `Bq q n` holds when `q ∤ σ(n)`. -/
def Bq (q n : ℕ) : Prop := ¬ (q ∣ ArithmeticFunction.sigma 1 n)

open ArithmeticFunction ArithmeticFunction.vonMangoldt LSeries in
/-- **Foundation for (A1)**: the prime-restricted residue-class log–Dirichlet series
`Q(x) = ∑_{p≡-1} log p / pˣ` exceeds the L-function pole `(1/φ(q))/(x-1) − C` on `(1,2]`.
Obtained from Mathlib's `LSeries_residueClass_lower_bound` after discarding the (bounded)
prime-power `k ≥ 2` contribution. -/
lemma Q_ge_pole (q : ℕ) [NeZero q] (ha : IsUnit (-1 : ZMod q)) :
    ∃ C : ℝ, ∀ x : ℝ, x ∈ Set.Ioc 1 2 →
      (q.totient : ℝ)⁻¹ / (x - 1) - C ≤
        ∑' n : ℕ, (if n.Prime then residueClass (-1 : ZMod q) n else 0) / (n : ℝ) ^ x := by
  obtain ⟨C', hC'⟩ := LSeries_residueClass_lower_bound (a := (-1 : ZMod q)) ha
  refine ⟨C' + ∑' n : ℕ, (if n.Prime then 0 else residueClass (-1 : ZMod q) n) / (n : ℝ),
    fun x hx => ?_⟩
  have hx1 : (1 : ℝ) < x := hx.1
  have hrcnn : ∀ n : ℕ, 0 ≤ residueClass (-1 : ZMod q) n := residueClass_nonneg _
  have hxnn : ∀ n : ℕ, (0 : ℝ) ≤ (n : ℝ) ^ x := fun n => Real.rpow_nonneg (by positivity) x
  have hD : Summable (fun n : ℕ => residueClass (-1 : ZMod q) n / (n : ℝ) ^ x) :=
    summable_real_of_abscissaOfAbsConv_lt
      ((abscissaOfAbsConv_residueClass_le_one _).trans_lt (by exact_mod_cast hx1))
  have hQ : Summable (fun n : ℕ =>
      (if n.Prime then residueClass (-1 : ZMod q) n else 0) / (n : ℝ) ^ x) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hD
    · split_ifs with h
      · exact div_nonneg (hrcnn n) (hxnn n)
      · simp
    · gcongr
      split_ifs with h
      · exact le_rfl
      · exact hrcnn n
  have hNP : Summable (fun n : ℕ =>
      (if n.Prime then 0 else residueClass (-1 : ZMod q) n) / (n : ℝ) ^ x) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hD
    · split_ifs with h
      · simp
      · exact div_nonneg (hrcnn n) (hxnn n)
    · gcongr
      split_ifs with h
      · exact hrcnn n
      · exact le_rfl
  have hsplit : (∑' n : ℕ, residueClass (-1 : ZMod q) n / (n : ℝ) ^ x)
      = (∑' n : ℕ, (if n.Prime then residueClass (-1 : ZMod q) n else 0) / (n : ℝ) ^ x)
        + ∑' n : ℕ, (if n.Prime then 0 else residueClass (-1 : ZMod q) n) / (n : ℝ) ^ x := by
    rw [← Summable.tsum_add hQ hNP]
    exact tsum_congr (fun n => by split_ifs <;> ring)
  have hNPle : (∑' n : ℕ, (if n.Prime then 0 else residueClass (-1 : ZMod q) n) / (n : ℝ) ^ x)
      ≤ ∑' n : ℕ, (if n.Prime then 0 else residueClass (-1 : ZMod q) n) / (n : ℝ) := by
    refine Summable.tsum_le_tsum (fun n => ?_) hNP (summable_residueClass_non_primes_div _)
    rcases n.eq_zero_or_pos with rfl | hn
    · simp
    · have hnum : (0 : ℝ) ≤ (if n.Prime then 0 else residueClass (-1 : ZMod q) n) := by
        split_ifs with h
        · exact le_rfl
        · exact hrcnn n
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hnx : (n : ℝ) ≤ (n : ℝ) ^ x := by
        calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (n : ℝ) ^ x := Real.rpow_le_rpow_of_exponent_le hn1 hx1.le
      exact div_le_div_of_nonneg_left hnum (by exact_mod_cast hn) hnx
  have hpoleD := hC' hx
  rw [hsplit] at hpoleD
  linarith [hpoleD, hNPle]

/-- `P(x) = ∑_{p ≡ -1 (q)} 1/pˣ`, the prime-restricted residue-class zeta-type series. -/
noncomputable def Pfun (q : ℕ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, (if n.Prime ∧ (n : ZMod q) = -1 then (1 : ℝ) else 0) / (n : ℝ) ^ x

/-- Termwise integral: `∫ₓ² n⁻ᵗ dt = (n⁻ˣ − n⁻²)/log n` for `n ≥ 2`. -/
lemma rpow_neg_intervalIntegral (n : ℕ) (hn : 2 ≤ n) (x : ℝ) :
    ∫ t in x..2, (n : ℝ) ^ (-t)
      = ((n : ℝ) ^ (-x) - (n : ℝ) ^ (-(2 : ℝ))) / Real.log n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
  have hlog : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  have hderiv : ∀ t ∈ Set.uIcc x (2 : ℝ),
      HasDerivAt (fun s => (-(Real.log n)⁻¹) * (n : ℝ) ^ (-s)) ((n : ℝ) ^ (-t)) t := by
    intro t _
    have hb : HasDerivAt (fun s : ℝ => (n : ℝ) ^ (-s)) (-(Real.log n) * (n : ℝ) ^ (-t)) t := by
      simpa [mul_comm] using HasDerivAt.rpow (hasDerivAt_const t (n : ℝ)) (hasDerivAt_id t).neg hn0
    have hd : (-(Real.log n)⁻¹) * (-(Real.log n) * (n : ℝ) ^ (-t)) = (n : ℝ) ^ (-t) := by
      rw [← mul_assoc, neg_mul_neg, inv_mul_cancel₀ hlog, one_mul]
    exact hd ▸ hb.const_mul (-(Real.log n)⁻¹)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (Continuous.intervalIntegrable
      (Continuous.rpow continuous_const continuous_id.neg (fun _ => Or.inl hn0.ne')) x 2)]
  field_simp
  ring

open ArithmeticFunction ArithmeticFunction.vonMangoldt MeasureTheory in
/-- Per-term integral: `∫ₓ² qₙ = (Pfun-summand x) − (Pfun-summand 2)` (the `Λ(p)=log p` weight
cancels the `1/log n` from the exponential integral). -/
lemma Q_term_integral (q : ℕ) [NeZero q] {x : ℝ} (hx2 : x ≤ 2) (n : ℕ) :
    (∫ t in Set.Ioc x 2, (if n.Prime then residueClass (-1 : ZMod q) n else 0) / (n : ℝ) ^ t)
      = (if n.Prime ∧ (n : ZMod q) = -1 then (1 : ℝ) else 0) / (n : ℝ) ^ x
        - (if n.Prime ∧ (n : ZMod q) = -1 then (1 : ℝ) else 0) / (n : ℝ) ^ (2 : ℝ) := by
  by_cases hp : n.Prime
  · by_cases hr : (n : ZMod q) = -1
    · have hn2 : 2 ≤ n := hp.two_le
      have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
      have hlog : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn2))
      have hrc : residueClass (-1 : ZMod q) n = Real.log n := by
        rw [residueClass, Set.indicator_of_mem (show n ∈ {m : ℕ | (m : ZMod q) = -1} from hr),
          vonMangoldt_apply_prime hp]
      rw [if_pos hp, if_pos ⟨hp, hr⟩, hrc, ← intervalIntegral.integral_of_le hx2]
      have hcalc : (∫ t in x..2, Real.log (n : ℝ) / (n : ℝ) ^ t)
          = Real.log (n : ℝ) * ∫ t in x..2, (n : ℝ) ^ (-t) := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr (fun t _ => ?_)
        rw [Real.rpow_neg hn0.le, div_eq_mul_inv]
      rw [hcalc, rpow_neg_intervalIntegral n hn2, Real.rpow_neg hn0.le, Real.rpow_neg hn0.le]
      field_simp
    · have hrc : residueClass (-1 : ZMod q) n = 0 := by
        rw [residueClass, Set.indicator_of_notMem (show n ∉ {m : ℕ | (m : ZMod q) = -1} from hr)]
      simp [hp, hr, hrc]
  · simp [hp]

/-- `Pfun q x` is summable for `x > 1` (sub-series of the zeta `p`-series). -/
lemma Pfun_summable (q : ℕ) {x : ℝ} (hx : 1 < x) :
    Summable (fun n : ℕ => (if n.Prime ∧ (n : ZMod q) = -1 then (1 : ℝ) else 0) / (n : ℝ) ^ x) := by
  refine Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) (fun n => ?_)
    (Real.summable_one_div_nat_rpow.mpr hx)
  split_ifs with h
  · exact le_rfl
  · rw [zero_div]; positivity

open ArithmeticFunction ArithmeticFunction.vonMangoldt MeasureTheory in
/-- **Integral identity**: `∫ₓ² Q = Pfun x − Pfun 2` (Tonelli via `integral_tsum`). -/
lemma integral_Q_eq (q : ℕ) [NeZero q] {x : ℝ} (hx1 : 1 < x) (hx2 : x ≤ 2) :
    (∫ t in Set.Ioc x 2,
        (∑' n : ℕ, (if n.Prime then residueClass (-1 : ZMod q) n else 0) / (n : ℝ) ^ t))
      = Pfun q x - Pfun q 2 := by
  have hcont : ∀ n : ℕ, Continuous
      (fun t : ℝ => (if n.Prime then residueClass (-1 : ZMod q) n else 0) / (n : ℝ) ^ t) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hne
    · simpa [Nat.not_prime_zero] using continuous_const
    · exact continuous_const.div
        (Continuous.rpow continuous_const continuous_id (fun _ => Or.inl (by exact_mod_cast hne)))
        (fun t => (Real.rpow_pos_of_pos (by positivity) t).ne')
  have hnn : ∀ (n : ℕ) (t : ℝ),
      0 ≤ (if n.Prime then residueClass (-1 : ZMod q) n else 0) / (n : ℝ) ^ t := by
    intro n t; split_ifs with h
    · exact div_nonneg (residueClass_nonneg _ _) (by positivity)
    · simp
  have hint : ∀ n : ℕ, IntegrableOn
      (fun t : ℝ => (if n.Prime then residueClass (-1 : ZMod q) n else 0) / (n : ℝ) ^ t)
      (Set.Ioc x 2) := fun n => (hcont n).integrableOn_Ioc
  have hpnn : ∀ n : ℕ, 0 ≤ (if n.Prime ∧ (n : ZMod q) = -1 then (1 : ℝ) else 0) / (n : ℝ) ^ x
      - (if n.Prime ∧ (n : ZMod q) = -1 then (1 : ℝ) else 0) / (n : ℝ) ^ (2 : ℝ) := by
    intro n; rw [← Q_term_integral q hx2 n]; exact setIntegral_nonneg measurableSet_Ioc (fun t _ => hnn n t)
  have hsummdiff : Summable (fun n : ℕ =>
      (if n.Prime ∧ (n : ZMod q) = -1 then (1 : ℝ) else 0) / (n : ℝ) ^ x
        - (if n.Prime ∧ (n : ZMod q) = -1 then (1 : ℝ) else 0) / (n : ℝ) ^ (2 : ℝ)) :=
    (Pfun_summable q hx1).sub (Pfun_summable q (by norm_num))
  have hfin : (∑' n : ℕ, ∫⁻ t in Set.Ioc x 2,
      ‖(if n.Prime then residueClass (-1 : ZMod q) n else 0) / (n : ℝ) ^ t‖₊) ≠ ⊤ := by
    have hterm : ∀ n : ℕ, (∫⁻ t in Set.Ioc x 2,
        ‖(if n.Prime then residueClass (-1 : ZMod q) n else 0) / (n : ℝ) ^ t‖₊)
        = ENNReal.ofReal ((if n.Prime ∧ (n : ZMod q) = -1 then (1 : ℝ) else 0) / (n : ℝ) ^ x
          - (if n.Prime ∧ (n : ZMod q) = -1 then (1 : ℝ) else 0) / (n : ℝ) ^ (2 : ℝ)) := by
      intro n
      rw [← Q_term_integral q hx2 n, lintegral_coe_eq_integral _ (hint n).norm]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
      rw [coe_nnnorm, Real.norm_of_nonneg (hnn n t)]
    rw [tsum_congr hterm, ← ENNReal.ofReal_tsum_of_nonneg hpnn hsummdiff]
    exact ENNReal.ofReal_ne_top
  rw [integral_tsum (fun n => (hcont n).aestronglyMeasurable) hfin, tsum_congr (Q_term_integral q hx2)]
  exact Summable.tsum_sub (Pfun_summable q hx1) (Pfun_summable q (by norm_num))

open ArithmeticFunction ArithmeticFunction.vonMangoldt MeasureTheory LSeries in
/-- `Q` is integrable on `(x,2]` for `x > 1` (the difference series is summable). -/
lemma Q_integrableOn (q : ℕ) [NeZero q] {x : ℝ} (hx1 : 1 < x) (hx2 : x ≤ 2) :
    IntegrableOn
      (fun t => ∑' n : ℕ, (if n.Prime then residueClass (-1 : ZMod q) n else 0) / (n : ℝ) ^ t)
      (Set.Ioc x 2) := by
  have hcont : ∀ n : ℕ, Continuous
      (fun t : ℝ => (if n.Prime then residueClass (-1 : ZMod q) n else 0) / (n : ℝ) ^ t) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hne
    · simpa [Nat.not_prime_zero] using continuous_const
    · exact continuous_const.div
        (Continuous.rpow continuous_const continuous_id (fun _ => Or.inl (by exact_mod_cast hne)))
        (fun t => (Real.rpow_pos_of_pos (by positivity) t).ne')
  have hnn : ∀ (n : ℕ) (t : ℝ),
      0 ≤ (if n.Prime then residueClass (-1 : ZMod q) n else 0) / (n : ℝ) ^ t := by
    intro n t; split_ifs with h
    · exact div_nonneg (residueClass_nonneg _ _) (by positivity)
    · simp
  have hint : ∀ n : ℕ, IntegrableOn
      (fun t : ℝ => (if n.Prime then residueClass (-1 : ZMod q) n else 0) / (n : ℝ) ^ t)
      (Set.Ioc x 2) := fun n => (hcont n).integrableOn_Ioc
  have hpnn : ∀ n : ℕ, 0 ≤ (if n.Prime ∧ (n : ZMod q) = -1 then (1 : ℝ) else 0) / (n : ℝ) ^ x
      - (if n.Prime ∧ (n : ZMod q) = -1 then (1 : ℝ) else 0) / (n : ℝ) ^ (2 : ℝ) := by
    intro n; rw [← Q_term_integral q hx2 n]
    exact setIntegral_nonneg measurableSet_Ioc (fun t _ => hnn n t)
  have hsummdiff : Summable (fun n : ℕ =>
      (if n.Prime ∧ (n : ZMod q) = -1 then (1 : ℝ) else 0) / (n : ℝ) ^ x
        - (if n.Prime ∧ (n : ZMod q) = -1 then (1 : ℝ) else 0) / (n : ℝ) ^ (2 : ℝ)) :=
    (Pfun_summable q hx1).sub (Pfun_summable q (by norm_num))
  have hu : Summable (fun n : ℕ =>
      (if n.Prime then residueClass (-1 : ZMod q) n else 0) / (n : ℝ) ^ x) := by
    refine Summable.of_nonneg_of_le (fun n => hnn n x) (fun n => ?_)
      (summable_real_of_abscissaOfAbsConv_lt
        ((abscissaOfAbsConv_residueClass_le_one (-1 : ZMod q)).trans_lt (by exact_mod_cast hx1)))
    gcongr
    split_ifs with h
    · exact le_rfl
    · exact residueClass_nonneg _ _
  refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
  refine continuousOn_tsum (fun n => (hcont n).continuousOn) hu (fun n t ht => ?_)
  rw [Real.norm_of_nonneg (hnn n t)]
  rcases eq_or_ne n 0 with rfl | hne
  · simp [Nat.not_prime_zero]
  · rw [Set.mem_Icc] at ht
    refine div_le_div_of_nonneg_left ?_ (Real.rpow_pos_of_pos (by positivity) x)
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne) ht.1)
    split_ifs with h
    · exact residueClass_nonneg _ _
    · exact le_rfl

open ArithmeticFunction ArithmeticFunction.vonMangoldt MeasureTheory in
/-- `Pfun q x → ∞` as `x → 1⁺`: it exceeds any bound on `(1,2]`. -/
lemma P_unbounded (q : ℕ) [NeZero q] (ha : IsUnit (-1 : ZMod q)) (B : ℝ) :
    ∃ x : ℝ, x ∈ Set.Ioc 1 2 ∧ B < Pfun q x := by
  obtain ⟨C, hC⟩ := Q_ge_pole q ha
  have hφ : (0 : ℝ) < (q.totient : ℝ)⁻¹ :=
    inv_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q)))
  have hlb : ∀ x : ℝ, x ∈ Set.Ioc 1 2 →
      Pfun q 2 + ((q.totient : ℝ)⁻¹ * (-(Real.log (x - 1))) - C * (2 - x)) ≤ Pfun q x := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hpoleII : IntervalIntegrable (fun t => (q.totient : ℝ)⁻¹ / (t - 1) - C) volume x 2 := by
      apply ContinuousOn.intervalIntegrable
      refine (ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
        (fun t ht => ?_)).sub continuousOn_const
      rw [Set.uIcc_of_le hx2, Set.mem_Icc] at ht
      change t - 1 ≠ 0
      have : (1 : ℝ) < t := lt_of_lt_of_le hx1 ht.1
      linarith
    have hpoleint : (∫ t in Set.Ioc x 2, ((q.totient : ℝ)⁻¹ / (t - 1) - C))
        = (q.totient : ℝ)⁻¹ * (-(Real.log (x - 1))) - C * (2 - x) := by
      rw [← intervalIntegral.integral_of_le hx2,
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := (fun t => (q.totient : ℝ)⁻¹ * Real.log (t - 1)) - (fun t => C * t))
          (fun t ht => ?_) hpoleII]
      · simp only [Pi.sub_apply]
        rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.log_one]; ring
      · rw [Set.uIcc_of_le hx2, Set.mem_Icc] at ht
        have h1 : (t : ℝ) - 1 ≠ 0 := by
          have : (1 : ℝ) < t := lt_of_lt_of_le hx1 ht.1; linarith
        have hd := (((Real.hasDerivAt_log h1).comp t ((hasDerivAt_id t).sub_const 1)).const_mul
          ((q.totient : ℝ)⁻¹)).sub ((hasDerivAt_id t).const_mul C)
        simpa [div_eq_mul_inv] using hd
    have hmono := setIntegral_mono_on
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hx2).mp hpoleII)
      (Q_integrableOn q hx1 hx2) measurableSet_Ioc
      (fun t ht => hC t ⟨lt_trans hx1 ht.1, ht.2⟩)
    rw [hpoleint, integral_Q_eq q hx1 hx2] at hmono
    linarith [hmono]
  -- pick `x = 1 + ε` with `ε` small enough; abstract `|C|` as `Cb` so `linarith` sees only atoms
  obtain ⟨Cb, -, hCb⟩ : ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → C * (1 - δ) ≤ Cb :=
    ⟨|C|, abs_nonneg C, fun δ hδ0 hδ1 => by
      calc C * (1 - δ) ≤ |C * (1 - δ)| := le_abs_self _
        _ = |C| * (1 - δ) := by rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hδ1)]
        _ ≤ |C| := mul_le_of_le_one_right (abs_nonneg C) (sub_le_self 1 hδ0)⟩
  set ε : ℝ := min 1 (Real.exp (-((B - Pfun q 2 + Cb + 1) / (q.totient : ℝ)⁻¹))) with hε
  have hε0 : 0 < ε := lt_min one_pos (Real.exp_pos _)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hxmem : 1 + ε ∈ Set.Ioc 1 2 := ⟨by linarith, by linarith⟩
  refine ⟨1 + ε, hxmem, ?_⟩
  have hlbx := hlb (1 + ε) hxmem
  rw [show (1 + ε) - 1 = ε by ring, show (2 : ℝ) - (1 + ε) = 1 - ε by ring] at hlbx
  have hloge : (B - Pfun q 2 + Cb + 1) / (q.totient : ℝ)⁻¹ ≤ -(Real.log ε) := by
    have hle : ε ≤ Real.exp (-((B - Pfun q 2 + Cb + 1) / (q.totient : ℝ)⁻¹)) := min_le_right _ _
    have := Real.log_le_log hε0 hle
    rw [Real.log_exp] at this; linarith
  have hφloge : B - Pfun q 2 + Cb + 1 ≤ (q.totient : ℝ)⁻¹ * (-(Real.log ε)) := by
    rw [mul_comm]; exact (div_le_iff₀ hφ).mp hloge
  linarith [hlbx, hφloge, hCb ε hε0.le hε1]

/-- **(A1)** Divergence of `∑_{p ≡ -1 (q)} 1/p`. -/
theorem primes_neg_one_div_diverges (q : ℕ) (hq : q.Prime) (hq2 : 2 ≤ q) :
    ¬ Summable (fun p : {p : ℕ // p.Prime ∧ (p : ZMod q) = -1} => (1 : ℝ) / (p : ℕ)) := by
  haveI : NeZero q := ⟨by omega⟩
  intro hsum
  have hind : Summable ((Set.indicator {n : ℕ | n.Prime ∧ (n : ZMod q) = -1}
      (fun n : ℕ => (1 : ℝ) / (n : ℝ)))) :=
    (summable_subtype_iff_indicator (s := {n : ℕ | n.Prime ∧ (n : ZMod q) = -1})
      (f := fun n : ℕ => (1 : ℝ) / (n : ℝ))).mp hsum
  have hP1eq : (fun n : ℕ => (if n.Prime ∧ (n : ZMod q) = -1 then (1 : ℝ) else 0) / (n : ℝ) ^ (1 : ℝ))
      = Set.indicator {n : ℕ | n.Prime ∧ (n : ZMod q) = -1} (fun n : ℕ => (1 : ℝ) / (n : ℝ)) := by
    funext n
    rw [Real.rpow_one, Set.indicator_apply]
    by_cases h : n.Prime ∧ (n : ZMod q) = -1 <;> simp [Set.mem_setOf_eq, h]
  have hP1summ : Summable (fun n : ℕ =>
      (if n.Prime ∧ (n : ZMod q) = -1 then (1 : ℝ) else 0) / (n : ℝ) ^ (1 : ℝ)) := by
    rw [hP1eq]; exact hind
  have hterm : ∀ (n : ℕ) (x : ℝ), 1 ≤ x →
      (if n.Prime ∧ (n : ZMod q) = -1 then (1 : ℝ) else 0) / (n : ℝ) ^ x
        ≤ (if n.Prime ∧ (n : ZMod q) = -1 then (1 : ℝ) else 0) / (n : ℝ) ^ (1 : ℝ) := by
    intro n x hx1
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [Nat.not_prime_zero]
    · by_cases h : n.Prime ∧ (n : ZMod q) = -1
      · simp only [h]
        exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by exact_mod_cast hn) 1)
          (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hx1)
      · simp [h]
  obtain ⟨x, hx, hxB⟩ := P_unbounded q isUnit_one.neg (Pfun q 1)
  have hxsumm : Summable (fun n : ℕ =>
      (if n.Prime ∧ (n : ZMod q) = -1 then (1 : ℝ) else 0) / (n : ℝ) ^ x) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
      (fun n => hterm n x hx.1.le) hP1summ
  have hmono : Pfun q x ≤ Pfun q 1 :=
    Summable.tsum_le_tsum (fun n => hterm n x hx.1.le) hxsumm hP1summ
  exact absurd hxB (not_lt.mpr hmono)

/-- **Forced σ-factor** (paper Lemma 4.2 key step): if `p ≡ -1 (mod q)` is a prime exactly
dividing `n` (i.e. `p ∣ n` but `p² ∤ n`), then `q ∣ σ(n)`. -/
lemma forced_sigma_factor (q p n : ℕ) (hq2 : 2 ≤ q) (hp : p.Prime) (hpq : (p : ZMod q) = -1)
    (hpn : p ∣ n) (hp2n : ¬ p ^ 2 ∣ n) : q ∣ ArithmeticFunction.sigma 1 n := by
  haveI : NeZero q := ⟨by omega⟩
  obtain ⟨m, rfl⟩ := hpn
  have hpm : ¬ p ∣ m := fun h => by
    obtain ⟨k, rfl⟩ := h; exact hp2n ⟨k, by ring⟩
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
  have hqp1 : q ∣ (p + 1) := by
    rw [← CharP.cast_eq_zero_iff (ZMod q) q]; push_cast; rw [hpq]; ring
  have hsp : ArithmeticFunction.sigma 1 p = p + 1 := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.Prime.divisors hp, Finset.sum_pair hp.one_lt.ne]
    omega
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hsp]
  exact Dvd.dvd.mul_right hqp1 _

/-- Divergence of `∑_{p ≡ -1 (q)} (1/p − 1/p²)` (drives the sieve product to `0`):
from A1 (`∑ 1/p = ∞`) and `∑ 1/p² < ∞`. -/
lemma recip_sub_sq_diverges (q : ℕ) (hq : q.Prime) (hq2 : 2 ≤ q) :
    ¬ Summable (fun p : {p : ℕ // p.Prime ∧ (p : ZMod q) = -1} =>
      (1 : ℝ) / (p : ℕ) - 1 / (p : ℕ) ^ 2) := by
  intro h
  have hsq : Summable (fun p : {p : ℕ // p.Prime ∧ (p : ZMod q) = -1} => (1 : ℝ) / (p : ℕ) ^ 2) :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).subtype _
  exact primes_neg_one_div_diverges q hq hq2 ((h.add hsq).congr (fun p => by ring))

/-- The sieve density product `∏_{p∈s}(1 − 1/p + 1/p²)` can be made smaller than any `ε > 0`
by choosing a large enough finite set `s` of primes `≡ -1 (mod q)`. -/
lemma sieve_prod_small (q : ℕ) (hq : q.Prime) (hq2 : 2 ≤ q) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset {p : ℕ // p.Prime ∧ (p : ZMod q) = -1},
      ∏ p ∈ s, (1 - ((1 : ℝ) / (p : ℕ) - 1 / (p : ℕ) ^ 2)) ≤ ε := by
  have hann : ∀ p : {p : ℕ // p.Prime ∧ (p : ZMod q) = -1},
      (0 : ℝ) ≤ (1 : ℝ) / (p : ℕ) - 1 / (p : ℕ) ^ 2 := by
    intro p
    have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.1.two_le
    rw [sub_nonneg]
    apply one_div_le_one_div_of_le (by linarith)
    nlinarith
  obtain ⟨s, hs⟩ : ∃ s : Finset {p : ℕ // p.Prime ∧ (p : ZMod q) = -1},
      -Real.log ε ≤ ∑ p ∈ s, ((1 : ℝ) / (p : ℕ) - 1 / (p : ℕ) ^ 2) := by
    by_contra hcon
    push_neg at hcon
    exact recip_sub_sq_diverges q hq hq2 (summable_of_sum_le hann (fun s => (hcon s).le))
  refine ⟨s, ?_⟩
  calc ∏ p ∈ s, (1 - ((1 : ℝ) / (p : ℕ) - 1 / (p : ℕ) ^ 2))
      ≤ ∏ p ∈ s, Real.exp (-((1 : ℝ) / (p : ℕ) - 1 / (p : ℕ) ^ 2)) :=
        Finset.prod_le_prod₀ (fun p _ => by
          have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.1.two_le
          have h1p : (1 : ℝ) / (p : ℕ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
          have h2p : (0 : ℝ) ≤ 1 / (p : ℕ) ^ 2 := by positivity
          linarith) (fun p _ => Real.one_sub_le_exp_neg _)
    _ = Real.exp (-∑ p ∈ s, ((1 : ℝ) / (p : ℕ) - 1 / (p : ℕ) ^ 2)) := by
        rw [← Real.exp_sum, ← Finset.sum_neg_distrib]
    _ ≤ Real.exp (Real.log ε) := Real.exp_le_exp.mpr (by linarith [hs])
    _ = ε := Real.exp_log hε

/-- **CRT count is multiplicative over coprime moduli.**  If `Pa` is periodic mod `a` and `Pb`
periodic mod `b` (with `a, b` coprime), the count of `n < a·b` with `Pa n ∧ Pb n` is the product
of the per-modulus counts.  Proof: the map `n ↦ (n % a, n % b)` is a bijection from
`range (a·b)` to `range a ×ˢ range b` (Chinese remainder), carrying good residues to good
residues. -/
lemma crt_count_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b)
    (Pa Pb : ℕ → Prop) [DecidablePred Pa] [DecidablePred Pb]
    (hPa : Function.Periodic Pa a) (hPb : Function.Periodic Pb b) :
    (a * b).count (fun n => Pa n ∧ Pb n) = a.count Pa * b.count Pb := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range,
    Nat.count_eq_card_filter_range, ← Finset.card_product, ← Finset.filter_product]
  refine Finset.card_nbij' (fun n => (n % a, n % b))
    (fun x => (Nat.chineseRemainder hab x.1 x.2 : ℕ)) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnlt, hPan, hPbn⟩ := hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    refine ⟨⟨Nat.mod_lt _ (Nat.pos_of_ne_zero ha), Nat.mod_lt _ (Nat.pos_of_ne_zero hb)⟩, ?_, ?_⟩
    · rw [hPa.map_mod_nat]; exact hPan
    · rw [hPb.map_mod_nat]; exact hPbn
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx
    obtain ⟨⟨hx1, hx2⟩, hPax, hPbx⟩ := hx
    have hka : (Nat.chineseRemainder hab x.1 x.2 : ℕ) % a = x.1 := by
      have h2 : (Nat.chineseRemainder hab x.1 x.2 : ℕ) % a = x.1 % a :=
        (Nat.chineseRemainder hab x.1 x.2).prop.1
      rwa [Nat.mod_eq_of_lt hx1] at h2
    have hkb : (Nat.chineseRemainder hab x.1 x.2 : ℕ) % b = x.2 := by
      have h2 : (Nat.chineseRemainder hab x.1 x.2 : ℕ) % b = x.2 % b :=
        (Nat.chineseRemainder hab x.1 x.2).prop.2
      rwa [Nat.mod_eq_of_lt hx2] at h2
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.chineseRemainder_lt_mul hab x.1 x.2 ha hb, ?_, ?_⟩
    · rw [← hPa.map_mod_nat, hka]; exact hPax
    · rw [← hPb.map_mod_nat, hkb]; exact hPbx
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnlt, -, -⟩ := hn
    show (Nat.chineseRemainder hab (n % a) (n % b) : ℕ) = n
    have hca : (Nat.chineseRemainder hab (n % a) (n % b) : ℕ) ≡ n [MOD a] :=
      (Nat.chineseRemainder hab (n % a) (n % b)).prop.1.trans (Nat.mod_modEq n a)
    have hcb : (Nat.chineseRemainder hab (n % a) (n % b) : ℕ) ≡ n [MOD b] :=
      (Nat.chineseRemainder hab (n % a) (n % b)).prop.2.trans (Nat.mod_modEq n b)
    have hcab : (Nat.chineseRemainder hab (n % a) (n % b) : ℕ) ≡ n [MOD a * b] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hab).mp ⟨hca, hcb⟩
    have hclt : (Nat.chineseRemainder hab (n % a) (n % b) : ℕ) < a * b :=
      Nat.chineseRemainder_lt_mul hab (n % a) (n % b) ha hb
    have hmod := Nat.mod_eq_of_modEq hcab hnlt
    rwa [Nat.mod_eq_of_lt hclt] at hmod
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_range] at hx
    obtain ⟨⟨hx1, hx2⟩, -, -⟩ := hx
    have hka : (Nat.chineseRemainder hab x.1 x.2 : ℕ) % a = x.1 := by
      have h2 : (Nat.chineseRemainder hab x.1 x.2 : ℕ) % a = x.1 % a :=
        (Nat.chineseRemainder hab x.1 x.2).prop.1
      rwa [Nat.mod_eq_of_lt hx1] at h2
    have hkb : (Nat.chineseRemainder hab x.1 x.2 : ℕ) % b = x.2 := by
      have h2 : (Nat.chineseRemainder hab x.1 x.2 : ℕ) % b = x.2 % b :=
        (Nat.chineseRemainder hab x.1 x.2).prop.2
      rwa [Nat.mod_eq_of_lt hx2] at h2
    show ((Nat.chineseRemainder hab x.1 x.2 : ℕ) % a, (Nat.chineseRemainder hab x.1 x.2 : ℕ) % b) = x
    rw [hka, hkb]

/-- The "exactly divides" predicate `¬ (p ∣ n ∧ ¬ p² ∣ n)` is periodic with period `p²`. -/
lemma single_prime_periodic (p : ℕ) :
    Function.Periodic (fun n => ¬ (p ∣ n ∧ ¬ p ^ 2 ∣ n)) (p ^ 2) := by
  intro n
  have e1 : p ∣ n + p ^ 2 ↔ p ∣ n := by
    rw [add_comm]; exact Nat.dvd_add_right (dvd_pow_self p two_ne_zero)
  have e2 : p ^ 2 ∣ n + p ^ 2 ↔ p ^ 2 ∣ n := Nat.dvd_add_self_right
  simp only [e1, e2]

/-- The conjunction over `s` of "exactly divides" predicates is periodic mod `∏ p²`. -/
lemma good_periodic {q : ℕ} (s : Finset {p : ℕ // p.Prime ∧ (p : ZMod q) = -1}) :
    Function.Periodic (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n))
      (∏ p ∈ s, ((p : ℕ)) ^ 2) := by
  intro n
  simp only [eq_iff_iff]
  refine forall_congr' fun p => imp_congr_right fun hp => ?_
  have hpdvd : ((p : ℕ)) ^ 2 ∣ ∏ p ∈ s, ((p : ℕ)) ^ 2 := Finset.dvd_prod_of_mem _ hp
  have e1 : (p : ℕ) ∣ n + ∏ p ∈ s, ((p : ℕ)) ^ 2 ↔ (p : ℕ) ∣ n := by
    rw [add_comm]
    exact Nat.dvd_add_right (dvd_trans (dvd_pow_self (p : ℕ) two_ne_zero) hpdvd)
  have e2 : ((p : ℕ)) ^ 2 ∣ n + ∏ p ∈ s, ((p : ℕ)) ^ 2 ↔ ((p : ℕ)) ^ 2 ∣ n := by
    rw [add_comm]; exact Nat.dvd_add_right hpdvd
  simp only [e1, e2]

/-- **Single-prime good-residue count**: among `0 ≤ r < p²` there are exactly `p² − (p−1)`
residues not exactly divisible by the prime `p` (the `p−1` bad ones are `p, 2p, …, (p−1)p`). -/
lemma single_prime_count (p : ℕ) (hp : p.Prime) :
    (p ^ 2).count (fun n => ¬ (p ∣ n ∧ ¬ p ^ 2 ∣ n)) = p ^ 2 - (p - 1) := by
  have hp0 : 0 < p := hp.pos
  -- count the *bad* residues, then complement
  have hbad : (p ^ 2).count (fun n => p ∣ n ∧ ¬ p ^ 2 ∣ n) = p - 1 := by
    rw [Nat.count_eq_card_filter_range]
    have hset : (Finset.range (p ^ 2)).filter (fun n => p ∣ n ∧ ¬ p ^ 2 ∣ n)
        = (Finset.Ico 1 p).image (fun k => k * p) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_Ico]
      constructor
      · rintro ⟨hnlt, ⟨k, rfl⟩, hns⟩
        refine ⟨k, ⟨?_, ?_⟩, by ring⟩
        · rcases Nat.eq_zero_or_pos k with rfl | hkpos
          · exact absurd (show p ^ 2 ∣ p * 0 from ⟨0, by ring⟩) hns
          · exact hkpos
        · by_contra hge
          push_neg at hge
          have hmul : p * p ≤ p * k := Nat.mul_le_mul (le_refl p) hge
          rw [pow_two] at hnlt
          omega
      · rintro ⟨k, ⟨hk1, hkp⟩, rfl⟩
        refine ⟨?_, ⟨k, by ring⟩, ?_⟩
        · rw [pow_two]; exact mul_lt_mul_of_pos_right hkp hp0
        · intro hdvd
          rw [pow_two] at hdvd
          have hpk : p ∣ k := (mul_dvd_mul_iff_right hp0.ne').mp hdvd
          have := Nat.le_of_dvd (by omega) hpk
          omega
    rw [hset, Finset.card_image_of_injective _
      (fun x y h => Nat.eq_of_mul_eq_mul_right hp0 h), Nat.card_Ico]
  have hcompl : (p ^ 2).count (fun n => ¬ (p ∣ n ∧ ¬ p ^ 2 ∣ n))
      + (p ^ 2).count (fun n => p ∣ n ∧ ¬ p ^ 2 ∣ n) = p ^ 2 := by
    rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range, add_comm,
      Finset.card_filter_add_card_filter_not, Finset.card_range]
  omega

/-- **Good-residue count factorizes (CRT).**  The number of residues `0 ≤ r < ∏ p²` exactly
avoiding every `p ∈ s` is `∏ (p² − (p−1))`.  Induction on `s`, with the insert step handled by
`crt_count_mul` (the new prime's modulus `p²` is coprime to `∏` over the rest). -/
lemma good_count_eq {q : ℕ} (s : Finset {p : ℕ // p.Prime ∧ (p : ZMod q) = -1}) :
    (∏ p ∈ s, ((p : ℕ)) ^ 2).count (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n))
      = ∏ p ∈ s, (((p : ℕ)) ^ 2 - ((p : ℕ) - 1)) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, Nat.count_eq_card_filter_range,
      Finset.filter_true_of_mem (fun x _ => by simp), Finset.card_range]
  | @insert p₀ s hp₀ ih =>
    have ha : ((p₀ : ℕ)) ^ 2 ≠ 0 := pow_ne_zero _ p₀.2.1.pos.ne'
    have hb : (∏ p ∈ s, ((p : ℕ)) ^ 2) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun p _ => pow_ne_zero _ p.2.1.pos.ne'
    have hcop : ((p₀ : ℕ)) ^ 2 |>.Coprime (∏ p ∈ s, ((p : ℕ)) ^ 2) := by
      refine Nat.Coprime.prod_right fun p hp => ?_
      have hne : (p₀ : ℕ) ≠ (p : ℕ) := by
        intro h
        exact hp₀ (by rw [Subtype.ext h]; exact hp)
      exact ((Nat.coprime_primes p₀.2.1 p.2.1).mpr hne).pow 2 2
    rw [Finset.prod_insert hp₀, Finset.prod_insert hp₀]
    have hbridge2 :
        ((p₀ : ℕ) ^ 2 * ∏ p ∈ s, ((p : ℕ)) ^ 2).count
            (fun n => ∀ p ∈ insert p₀ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n))
          = ((p₀ : ℕ) ^ 2 * ∏ p ∈ s, ((p : ℕ)) ^ 2).count
              (fun n => (fun n => ¬ ((p₀ : ℕ) ∣ n ∧ ¬ (p₀ : ℕ) ^ 2 ∣ n)) n
                ∧ (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n)) n) := by
      rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
      exact congrArg Finset.card (Finset.filter_congr (fun n _ => by
        simp only [Finset.forall_mem_insert]))
    rw [hbridge2, crt_count_mul ha hb hcop
        (fun n => ¬ ((p₀ : ℕ) ∣ n ∧ ¬ (p₀ : ℕ) ^ 2 ∣ n))
        (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n))
        (single_prime_periodic (p₀ : ℕ)) (good_periodic s),
      single_prime_count (p₀ : ℕ) p₀.2.1, ih]

/-- **CRT periodic-density bound**: the count of `n ≤ X` with no `p ∈ s` exactly dividing `n`
(`p ∥ n` means `p ∣ n ∧ ¬ p² ∣ n`) is at most `X · ∏(1 − 1/p + 1/p²) + ∏ p²`, the `+∏p²`
being the single-period error.  (Periodic mod `∏ p²`; per-prime good residues `p²−(p−1)`.) -/
lemma density_S_le (q : ℕ) (s : Finset {p : ℕ // p.Prime ∧ (p : ZMod q) = -1}) (X : ℕ) :
    (countUpTo (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n)) X : ℝ)
      ≤ (X : ℝ) * ∏ p ∈ s, (1 - ((1 : ℝ) / (p : ℕ) - 1 / (p : ℕ) ^ 2))
        + ∏ p ∈ s, ((p : ℕ) : ℝ) ^ 2 := by
  -- abbreviations (kept defeq, written out so external lemmas match syntactically)
  have hM0 : 0 < ∏ p ∈ s, ((p : ℕ)) ^ 2 := Finset.prod_pos fun p _ => pow_pos p.2.1.pos 2
  set M : ℕ := ∏ p ∈ s, ((p : ℕ)) ^ 2 with hMdef
  -- (a) bridge: `countUpTo P X = (X+1).count P`
  have hbridge : countUpTo (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n)) X
      = (X + 1).count (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n)) := by
    rw [Nat.count_eq_card_filter_range]
    unfold countUpTo setUpTo
    rw [← Set.ncard_coe_finset]
    congr 1
    ext n
    simp
  -- (c1) periodic count: `(B*M).count P = B*K`
  have hperiodM : Function.Periodic
      (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n)) M := by
    rw [hMdef]; exact good_periodic s
  have hblock : ∀ B : ℕ, (B * M).count (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n))
      = B * M.count (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n)) := by
    intro B
    induction B with
    | zero => simp
    | succ B ihB =>
      have hcongr :
          M.count (fun k => (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n)) (B * M + k))
            = M.count (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n)) := by
        rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
        refine congrArg Finset.card (Finset.filter_congr (fun k _ => ?_))
        have hh := (hperiodM.nat_mul B) k
        simp only [Nat.cast_id] at hh
        rw [add_comm k (B * M)] at hh
        exact hh.to_iff
      rw [add_mul, one_mul, Nat.count_add, hcongr, ihB]
      ring
  -- (c2) bound `X+1 ≤ (X/M + 1)*M`, then monotone count
  have hXle : X + 1 ≤ (X / M + 1) * M := by
    have h1 : M * (X / M) + X % M = X := Nat.div_add_mod X M
    have h2 : X % M < M := Nat.mod_lt _ hM0
    calc X + 1 ≤ M * (X / M) + M := by omega
      _ = (X / M + 1) * M := by ring
  have hcountle : (X + 1).count (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n))
      ≤ (X / M + 1) * M.count (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n)) := by
    calc (X + 1).count (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n))
        ≤ ((X / M + 1) * M).count (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n)) :=
          Nat.count_monotone _ hXle
      _ = (X / M + 1) * M.count (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n)) :=
          hblock _
  -- (b) `K ≤ M`
  have hKM : M.count (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n)) ≤ M :=
    Nat.count_le _
  -- (d) the CRT product identity in ℝ: `(K:ℝ) = M * ∏(1 - (1/p - 1/p²))`
  have hKreal : (M.count (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n)) : ℝ)
      = (M : ℝ) * ∏ p ∈ s, (1 - ((1 : ℝ) / (p : ℕ) - 1 / (p : ℕ) ^ 2)) := by
    rw [hMdef, good_count_eq, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.1.two_le
    have hp0 : (0 : ℝ) < (p : ℕ) := by linarith
    have hpne : ((p : ℕ) : ℝ) ≠ 0 := ne_of_gt hp0
    have hcastsub : (((p : ℕ)) ^ 2 - ((p : ℕ) - 1) : ℕ)
        = ((p : ℕ) : ℝ) ^ 2 - (((p : ℕ) : ℝ) - 1) := by
      have hle1 : 1 ≤ (p : ℕ) := p.2.1.one_lt.le
      have hle2 : (p : ℕ) - 1 ≤ ((p : ℕ)) ^ 2 :=
        le_trans (Nat.sub_le _ _) (Nat.le_self_pow (by norm_num) _)
      rw [Nat.cast_sub hle2, Nat.cast_pow, Nat.cast_sub hle1, Nat.cast_one]
    rw [hcastsub]
    push_cast
    field_simp
    try ring
  -- assemble in ℝ
  have hMR0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM0
  have hMcast : (M : ℝ) = ∏ p ∈ s, ((p : ℕ) : ℝ) ^ 2 := by
    rw [hMdef, Nat.cast_prod]; exact Finset.prod_congr rfl fun p _ => by push_cast; ring
  have hcountleR :
      ((countUpTo (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n)) X : ℕ) : ℝ)
        ≤ ((X / M + 1) * M.count (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n)) : ℕ) := by
    rw [hbridge]; exact_mod_cast hcountle
  have hdivle : ((X / M : ℕ) : ℝ) ≤ (X : ℝ) / (M : ℝ) := Nat.cast_div_le
  calc ((countUpTo (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n)) X : ℕ) : ℝ)
      ≤ ((X / M + 1) * M.count (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n)) : ℕ) :=
        hcountleR
    _ = ((X / M : ℕ) : ℝ) * (M.count (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n)) : ℝ)
          + (M.count (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n)) : ℝ) := by
        push_cast; ring
    _ ≤ (X : ℝ) / (M : ℝ)
            * (M.count (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n)) : ℝ) + (M : ℝ) := by
        have hKnn : (0 : ℝ) ≤ (M.count (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n)) : ℝ) :=
          Nat.cast_nonneg _
        have hk : ((X / M : ℕ) : ℝ)
              * (M.count (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n)) : ℝ)
            ≤ (X : ℝ) / (M : ℝ)
              * (M.count (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n)) : ℝ) :=
          mul_le_mul_of_nonneg_right hdivle hKnn
        have hm : (M.count (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n)) : ℝ) ≤ (M : ℝ) := by
          exact_mod_cast hKM
        linarith
    _ = (X : ℝ)
          * ((M.count (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n)) : ℝ) / (M : ℝ))
          + (M : ℝ) := by ring
    _ = (X : ℝ) * (((M : ℝ) * ∏ p ∈ s, (1 - ((1 : ℝ) / (p : ℕ) - 1 / (p : ℕ) ^ 2))) / (M : ℝ))
          + (M : ℝ) := by rw [hKreal]
    _ = (X : ℝ) * ∏ p ∈ s, (1 - ((1 : ℝ) / (p : ℕ) - 1 / (p : ℕ) ^ 2)) + (M : ℝ) := by
        rw [mul_div_cancel_left₀ _ (ne_of_gt hMR0)]
    _ = (X : ℝ) * ∏ p ∈ s, (1 - ((1 : ℝ) / (p : ℕ) - 1 / (p : ℕ) ^ 2))
          + ∏ p ∈ s, ((p : ℕ) : ℝ) ^ 2 := by rw [hMcast]

/-- **σ density-zero** (paper Lemma 4.2): for prime `q`, `{n : q ∤ σ(n)}` has density `0`. -/
theorem sigma_avoid (q : ℕ) (hq : q.Prime) : CountIsLittleO (Bq q) := by
  have hq2 : 2 ≤ q := hq.two_le
  refine Asymptotics.isLittleO_iff.mpr ?_
  intro c hc
  obtain ⟨s, hs⟩ := sieve_prod_small q hq hq2 (half_pos hc)
  set M : ℝ := ∏ p ∈ s, ((p : ℕ) : ℝ) ^ 2 with hM
  filter_upwards [eventually_ge_atTop ⌈2 * M / c⌉₊] with X hX
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  have hXR : 2 * M / c ≤ (X : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hX)
  have hMX : M ≤ c / 2 * (X : ℝ) := by
    have h2 : 2 * M ≤ (X : ℝ) * c := by rwa [div_le_iff₀ hc] at hXR
    nlinarith [h2]
  have hred : countUpTo (Bq q) X ≤
      countUpTo (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n)) X := by
    apply Set.ncard_le_ncard _ (setUpTo_finite _ _)
    rintro n ⟨hnX, hBq⟩
    exact ⟨hnX, fun p _ h => hBq (forced_sigma_factor q (p : ℕ) n hq2 p.2.1 p.2.2 h.1 h.2)⟩
  calc (↑(countUpTo (Bq q) X) : ℝ)
      ≤ (↑(countUpTo (fun n => ∀ p ∈ s, ¬ ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ^ 2 ∣ n)) X) : ℝ) := by
        exact_mod_cast hred
    _ ≤ (X : ℝ) * ∏ p ∈ s, (1 - ((1 : ℝ) / (p : ℕ) - 1 / (p : ℕ) ^ 2)) + M :=
        density_S_le q s X
    _ ≤ (X : ℝ) * (c / 2) + M := by
        have : (X : ℝ) * ∏ p ∈ s, (1 - ((1 : ℝ) / (p : ℕ) - 1 / (p : ℕ) ^ 2))
            ≤ (X : ℝ) * (c / 2) := mul_le_mul_of_nonneg_left hs (by positivity)
        linarith
    _ ≤ (X : ℝ) * (c / 2) + c / 2 * (X : ℝ) := by linarith [hMX]
    _ = c * (X : ℝ) := by ring



/-! ## Section 4.3 -- Thin-set transfer lemma. -/


/-- **Thin-set transfer** (paper Lemma 4.3). -/
theorem thinSet_transfer (Aset : ℕ → Prop) [DecidablePred Aset] (B : ℕ → ℝ)
    (hBpos : ∀ n, 0 ≤ B n) (hBle : ∀ n, B n ≤ n)
    (hBo : (fun n : ℕ => B n) =o[atTop] (fun n : ℕ => (n : ℝ)))
    (hAsum : Summable (fun a : {a : ℕ // Aset a} => (1 : ℝ) / a)) :
    (fun X : ℕ => ∑ a ∈ (Finset.range (X + 1)).filter Aset, B (X / a))
      =o[atTop] (fun X : ℕ => (X : ℝ)) := by
  classical
  -- indicator form of the reciprocal sum, and its summability
  set g : ℕ → ℝ := Set.indicator {a | Aset a} (fun n => (1 : ℝ) / n) with hgdef
  have hg : Summable g := summable_subtype_iff_indicator.mp hAsum
  have hgnn : ∀ n, 0 ≤ g n := fun n => by
    rw [hgdef]; exact Set.indicator_nonneg (fun i _ => by positivity) n
  have hgval : ∀ n, Aset n → g n = (1 : ℝ) / n := fun n hn => by
    rw [hgdef, Set.indicator_of_mem (show n ∈ {x | Aset x} from hn)]
  -- elementary bound `↑(X/a) ≤ ↑X/↑a`
  have hcastdiv : ∀ X a : ℕ, ((X / a : ℕ) : ℝ) ≤ (X : ℝ) / a := by
    intro X a
    rcases Nat.eq_zero_or_pos a with rfl | ha'
    · simp
    · rw [le_div_iff₀ (by exact_mod_cast ha')]
      exact_mod_cast Nat.div_mul_le_self X a
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  -- pick a cutoff `T` so the tail of `g` beyond `range T` is `< c/2`
  have h0 : Tendsto (fun N => ∑' n, g n - ∑ n ∈ Finset.range N, g n) atTop (𝓝 0) := by
    have h1 := hg.hasSum.tendsto_sum_nat
    simpa using (tendsto_const_nhds (x := ∑' n, g n)).sub h1
  obtain ⟨T, hT⟩ := (h0.eventually (Iio_mem_nhds (show (0 : ℝ) < c / 2 by linarith))).exists
  -- the head is `o(X)`: a finite sum of per-divisor `o(X)` terms
  have hhead : (fun X : ℕ => ∑ a ∈ (Finset.range T).filter Aset, B (X / a))
      =o[atTop] (fun X : ℕ => (X : ℝ)) := by
    have hterms : ∀ a ∈ (Finset.range T).filter Aset,
        (fun X : ℕ => B (X / a)) =o[atTop] (fun X : ℕ => (X : ℝ)) := by
      intro a _
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · have hB0 : B 0 = 0 := le_antisymm (by simpa using hBle 0) (hBpos 0)
        simp only [Nat.div_zero, hB0]
        exact isLittleO_zero _ _
      · have hk : Tendsto (fun X => X / a) atTop atTop := by
          rw [tendsto_atTop_atTop]
          exact fun b => ⟨b * a, fun X hX => by rw [Nat.le_div_iff_mul_le ha]; exact hX⟩
        refine (hBo.comp_tendsto hk).trans_isBigO ?_
        refine Asymptotics.isBigO_of_le atTop (fun X => ?_)
        show ‖((X / a : ℕ) : ℝ)‖ ≤ ‖(X : ℝ)‖
        rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
        exact_mod_cast Nat.div_le_self X a
    have hfun : (fun X : ℕ => ∑ a ∈ (Finset.range T).filter Aset, B (X / a)) =
        ∑ a ∈ (Finset.range T).filter Aset, (fun X : ℕ => B (X / a)) := by
      ext X
      simp
    rw [hfun]
    exact IsLittleO.sum hterms
  rw [Asymptotics.isLittleO_iff] at hhead
  filter_upwards [hhead (show (0 : ℝ) < c / 2 by linarith), eventually_ge_atTop T] with X hXhead hXT
  have hXnn : (0 : ℝ) ≤ X := by positivity
  -- split the index set at `T`
  have hsplit : (Finset.range (X + 1)).filter Aset
      = (Finset.range T).filter Aset ∪ (Finset.Ico T (X + 1)).filter Aset := by
    rw [← Finset.filter_union]
    congr 1
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      Finset.Ico_union_Ico_eq_Ico (Nat.zero_le T) (by omega)]
  have hdisj : Disjoint ((Finset.range T).filter Aset) ((Finset.Ico T (X + 1)).filter Aset) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_filter, Finset.mem_range] at ha
    rw [Finset.mem_filter, Finset.mem_Ico] at hb
    omega
  -- head bound
  have hheadbound : ∑ a ∈ (Finset.range T).filter Aset, B (X / a) ≤ c / 2 * X := by
    rwa [Real.norm_of_nonneg (Finset.sum_nonneg fun a _ => hBpos _),
      Real.norm_of_nonneg hXnn] at hXhead
  -- tail bound
  have htailbound : ∑ a ∈ (Finset.Ico T (X + 1)).filter Aset, B (X / a) ≤ c / 2 * X := by
    have hstep : ∑ a ∈ (Finset.Ico T (X + 1)).filter Aset, B (X / a)
        ≤ (X : ℝ) * ∑ a ∈ Finset.Ico T (X + 1), g a := by
      calc ∑ a ∈ (Finset.Ico T (X + 1)).filter Aset, B (X / a)
          ≤ ∑ a ∈ (Finset.Ico T (X + 1)).filter Aset, (X : ℝ) * g a := by
            apply Finset.sum_le_sum
            intro a ha
            rw [Finset.mem_filter] at ha
            rw [hgval a ha.2, mul_one_div]
            exact le_trans (hBle _) (hcastdiv X a)
        _ ≤ ∑ a ∈ Finset.Ico T (X + 1), (X : ℝ) * g a :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun i _ _ => mul_nonneg hXnn (hgnn i))
        _ = (X : ℝ) * ∑ a ∈ Finset.Ico T (X + 1), g a := by rw [Finset.mul_sum]
    have htg : ∑ a ∈ Finset.Ico T (X + 1), g a ≤ c / 2 := by
      have hadd : ∑ n ∈ Finset.range T, g n + ∑ a ∈ Finset.Ico T (X + 1), g a
          = ∑ n ∈ Finset.range (X + 1), g n := by
        rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
          ← Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive 0 T (X + 1)),
          Finset.Ico_union_Ico_eq_Ico (Nat.zero_le T) (by omega)]
      have hub : ∑ n ∈ Finset.range (X + 1), g n ≤ ∑' n, g n :=
        Summable.sum_le_tsum _ (fun i _ => hgnn i) hg
      linarith [hadd, hub, hT]
    calc ∑ a ∈ (Finset.Ico T (X + 1)).filter Aset, B (X / a)
        ≤ (X : ℝ) * ∑ a ∈ Finset.Ico T (X + 1), g a := hstep
      _ ≤ (X : ℝ) * (c / 2) := by
          apply mul_le_mul_of_nonneg_left htg hXnn
      _ = c / 2 * X := by ring
  -- combine
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun a _ => hBpos _), Real.norm_of_nonneg hXnn,
    hsplit, Finset.sum_union hdisj]
  linarith [hheadbound, htailbound]



/-! ## Section 5.1-5.2 -- Smooth-rough identity (Lem 5.1) and forced prime divisor (Lem 5.2). -/


/-- `H_e(a) = σ(e*a) - F_e(a)`. -/
def Hfun (e a : ℕ) : ℕ := ArithmeticFunction.sigma 1 (e * a) - F e a

/-- The active set `{r : 1 ≤ r < e, r ∣ e*a}`. -/
def activeSet (e a : ℕ) : Finset ℕ := (e * a).divisors.filter (· < e)

/-- **Smooth–rough identity** (paper Lemma 5.1, eq. 5.1). -/
theorem smooth_rough (e a b : ℕ) (he : 2 ≤ e)
    (hsmooth : ∀ p, p ∣ a → p.Prime → p ≤ e)
    (hrough : ∀ p, p ∣ b → p.Prime → e < p) :
    F e (a * b)
      = ArithmeticFunction.sigma 1 (e * a) * ArithmeticFunction.sigma 1 b - Hfun e a * b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [F, Hfun]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [F, Hfun]
  have hea : 0 < e * a := Nat.mul_pos (by omega) ha
  -- coprimality of `e*a` and `b`
  have hcop : (e * a).Coprime b := by
    apply Nat.coprime_of_dvd
    intro k hk hkea hkb
    have hke : k ≤ e := by
      rcases (Nat.Prime.dvd_mul hk).1 hkea with h | h
      · exact Nat.le_of_dvd (by omega) h
      · exact hsmooth k h hk
    exact absurd (hrough k hkb hk) (by omega)
  -- `b ≤ σ b` and `F e a ≤ σ(ea)`
  have hbσ : b ≤ ArithmeticFunction.sigma 1 b := by
    rw [ArithmeticFunction.sigma_one_apply]
    exact Finset.single_le_sum (fun i _ => Nat.zero_le i) (Nat.mem_divisors_self b (by omega))
  have hFle : F e a ≤ ArithmeticFunction.sigma 1 (e * a) := by
    rw [F, ArithmeticFunction.sigma_one_apply]
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  -- reindexing over the coprime product
  have key : ∀ f : ℕ → ℕ, ∑ d ∈ (e * a * b).divisors, f d
      = ∑ x ∈ (e * a).divisors, ∑ y ∈ b.divisors, f (x * y) := by
    intro f
    rw [Nat.divisors_mul, Finset.mul_def,
      Finset.sum_image (fun p hp q hq h =>
        hcop.mul_injOn_divisors (Finset.mem_coe.2 hp) (Finset.mem_coe.2 hq) h),
      Finset.sum_product]
  -- the additive form, proved per `x` by splitting `y = b` off
  have hadd : F e (a * b) + ArithmeticFunction.sigma 1 (e * a) * b
      = F e a * b + ArithmeticFunction.sigma 1 (e * a) * ArithmeticFunction.sigma 1 b := by
    have hFab : F e (a * b)
        = ∑ x ∈ (e * a).divisors, ∑ y ∈ b.divisors, (if x * y ≤ a * b then x * y else 0) := by
      rw [F, ← mul_assoc, Finset.sum_filter, key]
    have hσσ : ArithmeticFunction.sigma 1 (e * a) * ArithmeticFunction.sigma 1 b
        = ∑ x ∈ (e * a).divisors, ∑ y ∈ b.divisors, x * y := by
      rw [ArithmeticFunction.sigma_one_apply, ArithmeticFunction.sigma_one_apply,
        Finset.sum_mul_sum]
    have hσb : ArithmeticFunction.sigma 1 (e * a) * b
        = ∑ x ∈ (e * a).divisors, x * b := by
      rw [ArithmeticFunction.sigma_one_apply, Finset.sum_mul]
    have hFeab : F e a * b = ∑ x ∈ (e * a).divisors, (if x ≤ a then x * b else 0) := by
      rw [F, Finset.sum_filter, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ≤ a <;> simp [hx]
    rw [hFab, hσb, hFeab, hσσ, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Nat.mem_divisors] at hx
    have hxea : x ≤ e * a := Nat.le_of_dvd hea hx.1
    -- the per-`x` identity, splitting `y = b`
    have hbmem : b ∈ b.divisors := Nat.mem_divisors_self b (by omega)
    have hyb : (if x * b ≤ a * b then x * b else 0) = (if x ≤ a then x * b else 0) := by
      have hiff : x * b ≤ a * b ↔ x ≤ a := by
        constructor
        · intro h; exact le_of_mul_le_mul_right h hb
        · intro h; gcongr
      simp only [hiff]
    -- for `y ∈ erase b`, the product is `≤ a*b`
    have hsmall : ∀ y ∈ (b.divisors).erase b, (if x * y ≤ a * b then x * y else 0) = x * y := by
      intro y hy
      rw [Finset.mem_erase, Nat.mem_divisors] at hy
      obtain ⟨hyne, hydvd, _⟩ := hy
      have hypos : 0 < y := Nat.pos_of_dvd_of_pos hydvd hb
      have hyltb : y < b := lt_of_le_of_ne (Nat.le_of_dvd hb hydvd) hyne
      set c := b / y with hc
      have hcy : c * y = b := Nat.div_mul_cancel hydvd
      have hc1 : 1 < c := by
        rcases Nat.lt_or_ge c 2 with h | h
        · interval_cases c <;> omega
        · omega
      have hce : e < c := by
        have hcpos : 0 < c := by omega
        have hmf : c.minFac ∣ b := dvd_trans (Nat.minFac_dvd c) (by rw [← hcy]; exact Dvd.intro y rfl)
        have := hrough c.minFac hmf (Nat.minFac_prime (by omega))
        have hle : c.minFac ≤ c := Nat.minFac_le hcpos
        omega
      have hxyle : x * y ≤ a * b := by
        have h1 : x * y ≤ e * a * y := by gcongr
        have h2 : e * a * y * c = a * b * e := by rw [mul_assoc, mul_comm y c, hcy]; ring
        nlinarith [h1, h2, mul_le_mul_of_nonneg_left hce.le (Nat.zero_le (e * a * y)), he, ha, hb]
      rw [if_pos hxyle]
    rw [← Finset.add_sum_erase _ _ hbmem, ← Finset.add_sum_erase _ (fun y => x * y) hbmem,
      Finset.sum_congr rfl hsmall, hyb]
    ring
  -- derive the subtractive statement
  have hHb : Hfun e a * b
      = ArithmeticFunction.sigma 1 (e * a) * b - F e a * b := by
    rw [Hfun, Nat.sub_mul]
  have h1 : F e a * b ≤ ArithmeticFunction.sigma 1 (e * a) * b := by gcongr
  have h2 : ArithmeticFunction.sigma 1 (e * a) * b
      ≤ ArithmeticFunction.sigma 1 (e * a) * ArithmeticFunction.sigma 1 b := by gcongr
  omega

/-- **Forced prime divisor** (paper Lemma 5.2, eq. 5.2): rational form of `H_e(a)/a`. -/
theorem H_rational (e a : ℕ) (he : 2 ≤ e) :
    (Hfun e a : ℝ) / a = e * ∑ r ∈ activeSet e a, (1 : ℝ) / r := by
  simp only [activeSet]
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp [Hfun, F, Nat.divisors_zero]
  · set m := e * a with hm
    have hmpos : 0 < m := by rw [hm]; positivity
    have hsig : (ArithmeticFunction.sigma 1 m : ℝ) = ∑ x ∈ m.divisors, (x : ℝ) := by
      rw [ArithmeticFunction.sigma_one_apply]; push_cast; rfl
    have hFr : (F e a : ℝ) = ∑ x ∈ m.divisors.filter (· ≤ a), (x : ℝ) := by
      rw [F, ← hm]; push_cast; rfl
    have hFle : F e a ≤ ArithmeticFunction.sigma 1 m := by
      rw [F, ArithmeticFunction.sigma_one_apply, ← hm]
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    -- (H : ℝ) = ∑_{x ∣ m, a < x} x
    have hHr : (Hfun e a : ℝ) = ∑ x ∈ m.divisors.filter (a < ·), (x : ℝ) := by
      rw [Hfun, ← hm, Nat.cast_sub hFle, hsig, hFr,
        ← Finset.sum_filter_add_sum_filter_not m.divisors (· ≤ a) (fun x => (x : ℝ)),
        add_sub_cancel_left]
      simp only [not_le]
    -- reflection `x ↦ m/x`: ∑_{a < x} x = ∑_{r < e} (m/r)
    have hrefl : (∑ x ∈ m.divisors.filter (a < ·), (x : ℝ))
        = ∑ r ∈ m.divisors.filter (· < e), ((m / r : ℕ) : ℝ) := by
      rw [Finset.sum_filter, Finset.sum_filter,
        ← Nat.sum_div_divisors m (fun x => if a < x then (x : ℝ) else 0)]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Nat.mem_divisors] at hr
      obtain ⟨hdvd, _⟩ := hr
      have hrpos : 0 < r := Nat.pos_of_dvd_of_pos hdvd hmpos
      have hmul : m / r * r = m := Nat.div_mul_cancel hdvd
      have hcond0 : (m / r ≤ a) ↔ (e ≤ r) := by
        constructor
        · intro h
          have h1 : m / r * r ≤ a * r := by gcongr
          rw [hmul] at h1
          have h2 : e * a ≤ r * a := by rw [hm, mul_comm a r] at h1; exact h1
          exact le_of_mul_le_mul_right h2 ha
        · intro h
          have h1 : e * a ≤ r * a := by gcongr
          have h2 : m / r * r ≤ a * r := by rw [hmul, hm, mul_comm a r]; exact h1
          exact le_of_mul_le_mul_right h2 hrpos
      have hcond : (a < m / r) ↔ (r < e) := by
        rw [← not_le, ← not_le]; exact not_congr hcond0
      show (if a < m / r then ((m / r : ℕ) : ℝ) else 0)
          = (if r < e then ((m / r : ℕ) : ℝ) else 0)
      by_cases h : a < m / r
      · rw [if_pos h, if_pos (hcond.mp h)]
      · rw [if_neg h, if_neg (fun hc => h (hcond.mpr hc))]
    -- (H : ℝ) = m * ∑_{r < e} 1/r
    have hH2 : (Hfun e a : ℝ)
        = (m : ℝ) * ∑ r ∈ m.divisors.filter (· < e), (1 : ℝ) / r := by
      rw [hHr, hrefl, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mem_filter, Nat.mem_divisors] at hr
      obtain ⟨⟨hdvd, _⟩, _⟩ := hr
      have hrpos : 0 < r := Nat.pos_of_dvd_of_pos hdvd hmpos
      rw [Nat.cast_div hdvd (by exact_mod_cast hrpos.ne'), mul_one_div]
    -- divide by a, using m = e*a
    have hme : (m : ℝ) = (e : ℝ) * a := by rw [hm]; push_cast; ring
    have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
    rw [hH2]
    set S := ∑ r ∈ m.divisors.filter (· < e), (1 : ℝ) / r with hS
    rw [hme, show (e : ℝ) * a * S = e * S * a by ring, mul_div_assoc, div_self ha', mul_one]



/-! ## Section 5.3-5.4 -- Sieve modulus Q_E; density lower bound (Lem 5.4); bounded-cofactor exclusion (Prop 5.3). -/


/-- Reduced numerator of `e * ∑_{r ∈ R} 1/r`. -/
def Aval (e : ℕ) (R : Finset ℕ) : ℕ := ((e : ℚ) * ∑ r ∈ R, (1 : ℚ) / r).num.natAbs

/-- Chosen prime divisor of `Aval e R`. -/
def qER (e : ℕ) (R : Finset ℕ) : ℕ := (Aval e R).minFac

/-- The sieve prime set `S_E` (over `e ≤ E` and all candidate active sets `R ⊆ [1,e)`). -/
def S (E : ℕ) : Finset ℕ :=
  insert 2 ((Finset.Icc 2 E).biUnion (fun e =>
    ((Finset.Ico 1 e).powerset).image (fun R => qER e R)))

/-- The squarefree sieve modulus `Q_E = ∏_{q ∈ S_E} q`. -/
def Qpr (E : ℕ) : ℕ := ∏ q ∈ S E, q

/-- `δ_E = φ(Q_E)/Q_E`. -/
noncomputable def δ (E : ℕ) : ℝ := (Nat.totient (Qpr E) : ℝ) / (Qpr E : ℝ)

/-- **Forced prime divisor** (paper Lemma 5.2, second part): the chosen prime `qER` for the
active set divides `H_e(a)`. -/
lemma forced_prime (e a : ℕ) (he : 2 ≤ e) (ha : 1 ≤ a) :
    qER e (activeSet e a) ∣ Hfun e a := by
  set R := activeSet e a with hR
  set V : ℚ := (e : ℚ) * ∑ r ∈ R, (1 : ℚ) / r with hV
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  -- the rational identity `(Hfun : ℚ) = a * V` (cast of `H_rational`)
  have hr : (Hfun e a : ℝ) / a = (e : ℝ) * ∑ r ∈ R, (1 : ℝ) / r := H_rational e a he
  have hQ : (Hfun e a : ℚ) = a * V := by
    have hcast : ((a : ℚ) * V : ℝ) = (Hfun e a : ℝ) := by
      push_cast [hV]
      rw [← hr]
      field_simp
    exact_mod_cast hcast.symm
  -- cross-multiplication `a * V.num = Hfun * V.den`
  have hden : (V.den : ℚ) ≠ 0 := by exact_mod_cast V.den_nz
  have hcross : (a : ℤ) * V.num = (V.den : ℤ) * Hfun e a := by
    have h1 : (a : ℚ) * ((V.num : ℚ) / (V.den : ℚ)) = (Hfun e a : ℚ) := by
      rw [Rat.num_div_den]; exact hQ.symm
    field_simp at h1
    exact_mod_cast h1
  -- coprimality of numerator and denominator gives `V.num ∣ Hfun`
  have hcop : IsCoprime V.num (V.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd]
    simpa using V.reduced
  have hdvd : V.num ∣ (Hfun e a : ℤ) :=
    hcop.dvd_of_dvd_mul_left ⟨a, hcross.symm.trans (mul_comm (a : ℤ) V.num)⟩
  -- conclude `qER ∣ Aval ∣ Hfun`
  have hAvaldvd : Aval e R ∣ Hfun e a := by
    rw [Aval, ← hV, ← Int.natAbs_natCast (Hfun e a)]
    exact Int.natAbs_dvd_natAbs.mpr hdvd
  rw [qER]
  exact dvd_trans (Nat.minFac_dvd _) hAvaldvd

/-- **Smooth–rough factorization.** Every `d ≥ 1` splits as `d = a * b` with `a` the `e`-smooth
part (prime factors `≤ e`) and `b` the `e`-rough part (prime factors `> e`), coprime. -/
lemma smooth_rough_factor (e d : ℕ) (hd : 1 ≤ d) :
    ∃ a b : ℕ, d = a * b ∧ a.Coprime b ∧ 1 ≤ a ∧ 1 ≤ b ∧
      (∀ p, p ∣ a → p.Prime → p ≤ e) ∧ (∀ p, p ∣ b → p.Prime → e < p) := by
  classical
  have hd0 : d ≠ 0 := by omega
  set a := ∏ p ∈ d.primeFactors.filter (· ≤ e), p ^ d.factorization p with ha
  set b := ∏ p ∈ d.primeFactors.filter (fun p => ¬ p ≤ e), p ^ d.factorization p with hb
  have hsplit : d = ∏ p ∈ d.primeFactors, p ^ d.factorization p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hd0]
    rw [Finsupp.prod, Nat.support_factorization]
  have hab : d = a * b := by
    rw [ha, hb, Finset.prod_filter_mul_prod_filter_not, ← hsplit]
  have hapos : 0 < a := by
    rw [ha]; exact Finset.prod_pos (fun p hp => by
      rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
      exact pow_pos hp.1.1.pos _)
  have hbpos : 0 < b := by
    rw [hb]; exact Finset.prod_pos (fun p hp => by
      rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
      exact pow_pos hp.1.1.pos _)
  have hprimea : ∀ p, p ∣ a → p.Prime → p ≤ e := by
    intro p hpa hp
    obtain ⟨q, hq, hpq⟩ := (hp.prime).exists_mem_finset_dvd (by rw [← ha]; exact hpa)
    rw [Finset.mem_filter] at hq
    have : p = q := (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hq.1)).mp
      (hp.dvd_of_dvd_pow hpq)
    rw [this]; exact hq.2
  have hprimeb : ∀ p, p ∣ b → p.Prime → e < p := by
    intro p hpb hp
    obtain ⟨q, hq, hpq⟩ := (hp.prime).exists_mem_finset_dvd (by rw [← hb]; exact hpb)
    rw [Finset.mem_filter] at hq
    have : p = q := (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hq.1)).mp
      (hp.dvd_of_dvd_pow hpq)
    rw [this]; omega
  refine ⟨a, b, hab, ?_, hapos, hbpos, hprimea, hprimeb⟩
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hgcd
  obtain ⟨p, hp, hpab⟩ := Nat.exists_prime_and_dvd hgcd
  have hpa : p ∣ a := hpab.trans (Nat.gcd_dvd_left a b)
  have hpb : p ∣ b := hpab.trans (Nat.gcd_dvd_right a b)
  exact absurd (hprimea p hpa hp) (by have := hprimeb p hpb hp; omega)

/-- `Nat.sqrt X = o(X)`. -/
lemma nat_sqrt_isLittleO :
    (fun X : ℕ => (Nat.sqrt X : ℝ)) =o[atTop] (fun X : ℕ => (X : ℝ)) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  filter_upwards [eventually_gt_atTop (Nat.ceil (1 / ε ^ 2))] with X hX
  have hXr : (1 : ℝ) / ε ^ 2 < X := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hX)
  have hsqrt : (Nat.sqrt X : ℝ) ≤ Real.sqrt X := by
    rw [show (Nat.sqrt X : ℝ) = Real.sqrt ((Nat.sqrt X : ℝ) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.sqrt_le' X)
  have hε2 : 1 < ε ^ 2 * X := by rw [mul_comm]; exact (div_lt_iff₀ (by positivity)).mp hXr
  have h2 : Real.sqrt X ≤ ε * X := by
    rw [show ε * (X : ℝ) = Real.sqrt ((ε * X) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [hε2, (Nat.cast_nonneg X : (0:ℝ) ≤ X)])
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  linarith [hsqrt, h2]

/-- The squares and twice-squares form a density-zero set (`O(√X)`). -/
lemma sq_or_twosq_littleO :
    CountIsLittleO (fun d => ∃ s, d = s ^ 2 ∨ d = 2 * s ^ 2) := by
  have hcard : ∀ X : ℕ, countUpTo (fun d => ∃ s, d = s ^ 2 ∨ d = 2 * s ^ 2) X
      ≤ 2 * (Nat.sqrt X + 1) := by
    intro X
    unfold countUpTo
    have hsub : setUpTo (fun d => ∃ s, d = s ^ 2 ∨ d = 2 * s ^ 2) X ⊆
        ↑((Finset.range (Nat.sqrt X + 1)).image (· ^ 2) ∪
          (Finset.range (Nat.sqrt X + 1)).image (fun s => 2 * s ^ 2)) := by
      intro n hn
      unfold setUpTo at hn
      rw [Set.mem_setOf_eq] at hn
      obtain ⟨hnX, s, hs⟩ := hn
      simp only [Finset.coe_union, Finset.coe_image, Finset.coe_range, Set.mem_union,
        Set.mem_image, Set.mem_Iio]
      rcases hs with hs | hs
      · exact Or.inl ⟨s, Nat.lt_succ_iff.mpr (Nat.le_sqrt'.mpr (hs ▸ hnX)), hs.symm⟩
      · exact Or.inr ⟨s, Nat.lt_succ_iff.mpr (Nat.le_sqrt'.mpr
          (le_trans (Nat.le_mul_of_pos_left (s ^ 2) (by norm_num)) (hs ▸ hnX))), hs.symm⟩
    calc (setUpTo (fun d => ∃ s, d = s ^ 2 ∨ d = 2 * s ^ 2) X).ncard
        ≤ _ := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = _ := Set.ncard_coe_finset _
      _ ≤ 2 * (Nat.sqrt X + 1) := by
          refine (Finset.card_union_le _ _).trans ?_
          have h1 := Finset.card_image_le (s := Finset.range (Nat.sqrt X + 1)) (f := (· ^ 2))
          have h2 := Finset.card_image_le (s := Finset.range (Nat.sqrt X + 1))
            (f := fun s => 2 * s ^ 2)
          simp only [Finset.card_range] at h1 h2
          omega
  have hg : (fun X : ℕ => 4 * (Nat.sqrt X : ℝ)) =o[atTop] (fun X : ℕ => (X : ℝ)) :=
    nat_sqrt_isLittleO.const_mul_left 4
  refine Asymptotics.IsBigO.trans_isLittleO ?_ hg
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with X hX1
  have hsqrt1 : (1 : ℝ) ≤ (Nat.sqrt X : ℝ) := by
    have : 1 ≤ Nat.sqrt X := Nat.le_sqrt'.mpr (by simpa using hX1)
    exact_mod_cast this
  have hcd : (countUpTo (fun d => ∃ s, d = s ^ 2 ∨ d = 2 * s ^ 2) X : ℝ)
      ≤ 2 * ((Nat.sqrt X : ℝ) + 1) := by exact_mod_cast hcard X
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  nlinarith [hcd, hsqrt1]

open ArithmeticFunction in
/-- **σ-parity (forward).** If `σ(d)` is odd then `d` is a square or twice a square. -/
lemma sigma_odd_imp_sq_or_twosq (d : ℕ) (hd : 1 ≤ d) (hodd : Odd (sigma 1 d)) :
    ∃ s, d = s ^ 2 ∨ d = 2 * s ^ 2 := by
  classical
  have hd0 : d ≠ 0 := by omega
  -- (1) every odd prime factor has even valuation
  have hev : ∀ p ∈ d.primeFactors, p ≠ 2 → Even (d.factorization p) := by
    intro p hp hp2
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hpp.odd_of_ne_two hp2)
    have hdvd : sigma 1 (p ^ d.factorization p) ∣ sigma 1 d := by
      conv_rhs => rw [isMultiplicative_sigma.multiplicative_factorization _ hd0, Finsupp.prod]
      exact Finset.dvd_prod_of_mem (fun q => sigma 1 (q ^ d.factorization q))
        (by rw [Nat.support_factorization]; exact hp)
    have hfac : Odd (sigma 1 (p ^ d.factorization p)) := by
      obtain ⟨c, hc⟩ := hdvd
      have h := hodd
      rw [hc, Nat.odd_mul] at h
      exact h.1
    rw [sigma_one_apply_prime_pow hpp] at hfac
    have hsum : (∑ j ∈ Finset.range (d.factorization p + 1), p ^ j) % 2
        = (d.factorization p + 1) % 2 := by
      rw [Finset.sum_nat_mod,
        Finset.sum_congr rfl (fun j _ => by rw [Nat.pow_mod, hpodd, one_pow])]
      simp
    rw [Nat.odd_iff, hsum] at hfac
    rw [Nat.even_iff]; omega
  -- (2) split off the 2-part: `d = 2 ^ a * o` with `o` odd
  set a := d.factorization 2 with ha
  have hdvd2 : 2 ^ a ∣ d := Nat.ordProj_dvd d 2
  set o := d / 2 ^ a with ho
  have hdeq : d = 2 ^ a * o := (Nat.mul_div_cancel' hdvd2).symm
  have ho0 : o ≠ 0 := by rintro h; rw [h, mul_zero] at hdeq; exact hd0 hdeq
  have h2a0 : (2 : ℕ) ^ a ≠ 0 := by positivity
  have hod : o ∣ d := ⟨2 ^ a, by rw [hdeq, mul_comm]⟩
  have hoodd : ¬ (2 ∣ o) := Nat.not_dvd_ordCompl Nat.prime_two hd0
  have hfacto : ∀ p, p ≠ 2 → o.factorization p = d.factorization p := by
    intro p hp2
    rw [hdeq, Nat.factorization_mul h2a0 ho0, Finsupp.add_apply, Nat.factorization_pow,
      Finsupp.smul_apply, Nat.Prime.factorization Nat.prime_two, Finsupp.single_apply,
      if_neg (Ne.symm hp2), smul_zero, zero_add]
  -- (3) `o` is a perfect square
  have hosq : ∃ s, o = s ^ 2 := by
    refine ⟨∏ p ∈ o.primeFactors, p ^ (o.factorization p / 2), ?_⟩
    rw [← Finset.prod_pow]
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self ho0, Finsupp.prod,
      Nat.support_factorization]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hp2 : p ≠ 2 := fun h => hoodd (h ▸ Nat.dvd_of_mem_primeFactors hp)
    have hpd : p ∈ d.primeFactors := Nat.primeFactors_mono hod hd0 hp
    have heven : Even (o.factorization p) := by rw [hfacto p hp2]; exact hev p hpd hp2
    rw [← pow_mul, Nat.div_mul_cancel heven.two_dvd]
  -- (4) assemble
  obtain ⟨s, hs⟩ := hosq
  rcases Nat.even_or_odd a with ⟨b, hb⟩ | ⟨b, hb⟩
  · exact ⟨2 ^ b * s, Or.inl (by rw [hdeq, hs, hb]; ring)⟩
  · exact ⟨2 ^ b * s, Or.inr (by rw [hdeq, hs, hb]; ring)⟩

/-- `2 ∣ Q_E`, so every integer coprime to `Q_E` is odd. -/
theorem two_dvd_Qpr (E : ℕ) (_hE : 2 ≤ E) : 2 ∣ Qpr E := by
  unfold Qpr S
  exact Finset.dvd_prod_of_mem _ (Finset.mem_insert_self 2 _)

open ArithmeticFunction in
/-- `F 1 d = σ d` (with `e = 1`, every divisor of `d` is `≤ d`). -/
lemma F_one_eq_sigma (d : ℕ) : F 1 d = sigma 1 d := by
  rw [F, one_mul, sigma_one_apply]
  refine Finset.sum_congr (Finset.filter_true_of_mem (fun q hq => ?_)) (fun _ _ => rfl)
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hq).2) (Nat.mem_divisors.mp hq).1

open ArithmeticFunction in
/-- **`e = 1` case of Prop 5.3.** Coprime-to-`Q_E` values `σ(d)` are odd, hence `d` is a square
or twice a square, a density-zero set. -/
lemma small_e_one_littleO (E : ℕ) (hE : 2 ≤ E) :
    CountIsLittleO (fun N => Nat.Coprime N (Qpr E) ∧ ∃ d, N = F 1 d) := by
  have hfin : ∀ X, (setUpTo (fun d => ∃ s, d = s ^ 2 ∨ d = 2 * s ^ 2) X).Finite :=
    fun X => Set.Finite.subset (Set.finite_Iic X) (fun n hn => hn.1)
  have hbound : ∀ X, countUpTo (fun N => Nat.Coprime N (Qpr E) ∧ ∃ d, N = F 1 d) X
      ≤ countUpTo (fun d => ∃ s, d = s ^ 2 ∨ d = 2 * s ^ 2) X := by
    intro X
    have hsub : setUpTo (fun N => Nat.Coprime N (Qpr E) ∧ ∃ d, N = F 1 d) X ⊆
        sigma 1 '' setUpTo (fun d => ∃ s, d = s ^ 2 ∨ d = 2 * s ^ 2) X := by
      intro N hN
      obtain ⟨hNX, hcop, d, hd⟩ := hN
      rw [F_one_eq_sigma] at hd
      have hN0 : N ≠ 0 := by
        rintro rfl
        rw [Nat.coprime_zero_left] at hcop
        exact absurd (two_dvd_Qpr E hE) (by rw [hcop]; decide)
      have hd0 : d ≠ 0 := by rintro rfl; rw [hd] at hN0; simp at hN0
      have hNodd : Odd N :=
        (Nat.Coprime.coprime_dvd_right (two_dvd_Qpr E hE) hcop).odd_of_right
      have hdle : d ≤ X := by
        have : d ≤ sigma 1 d := by
          rw [sigma_one_apply]
          exact Finset.single_le_sum (fun i _ => Nat.zero_le i)
            (Nat.mem_divisors_self d hd0)
        omega
      refine ⟨d, ⟨hdle, sigma_odd_imp_sq_or_twosq d (by omega) (hd ▸ hNodd)⟩, hd.symm⟩
    calc (setUpTo (fun N => Nat.Coprime N (Qpr E) ∧ ∃ d, N = F 1 d) X).ncard
        ≤ (sigma 1 '' setUpTo (fun d => ∃ s, d = s ^ 2 ∨ d = 2 * s ^ 2) X).ncard :=
          Set.ncard_le_ncard hsub ((hfin X).image _)
      _ ≤ _ := Set.ncard_image_le (hfin X)
  refine Asymptotics.IsBigO.trans_isLittleO ?_ sq_or_twosq_littleO
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, Filter.Eventually.of_forall (fun X => ?_)⟩
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul]
  exact_mod_cast hbound X

/-- The reciprocals of `k`-smooth numbers are summable (Euler product over primes `< k`). -/
lemma smooth_recip_summable (k : ℕ) :
    Summable (fun a : Nat.smoothNumbers k => (1 : ℝ) / (a : ℕ)) := by
  induction k with
  | zero =>
    have hfin : (Nat.smoothNumbers 0).Finite := by
      rw [Nat.smoothNumbers_zero]; exact Set.finite_singleton 1
    exact hfin.summable (fun n : ℕ => (1 : ℝ) / (n : ℝ))
  | succ p ih =>
    by_cases hp : p.Prime
    · rw [← (Nat.equivProdNatSmoothNumbers hp).summable_iff]
      have heq : (fun a : Nat.smoothNumbers (p + 1) => (1 : ℝ) / (a : ℕ)) ∘
          (Nat.equivProdNatSmoothNumbers hp)
          = fun x : ℕ × Nat.smoothNumbers p => (1 / (p : ℝ)) ^ x.1 * (1 / (x.2 : ℕ)) := by
        funext x
        simp only [Function.comp_apply, Nat.equivProdNatSmoothNumbers_apply', Nat.cast_mul,
          Nat.cast_pow, one_div, mul_inv, inv_pow]
      rw [heq]
      have hgeo : Summable (fun e : ℕ => (1 / (p : ℝ)) ^ e) := by
        apply summable_geometric_of_lt_one (by positivity)
        rw [div_lt_one (by exact_mod_cast hp.pos)]
        exact_mod_cast hp.one_lt
      exact hgeo.mul_of_nonneg ih (fun _ => by positivity) (fun _ => by positivity)
    · rw [Nat.smoothNumbers_succ hp]
      exact ih

/-- The always-false predicate has count `o(X)`. -/
lemma CountIsLittleO_false : CountIsLittleO (fun _ : ℕ => False) := by
  have hz : ∀ X, countUpTo (fun _ : ℕ => False) X = 0 := by
    intro X
    simp only [countUpTo]
    convert Set.ncard_empty ℕ
    ext n; simp [setUpTo]
  unfold CountIsLittleO
  simp only [hz, Nat.cast_zero]
  exact Asymptotics.isLittleO_zero _ _

/-- A finite union of density-zero sets is density-zero. -/
lemma CountIsLittleO_biUnion {ι : Type*} (s : Finset ι) (P : ι → ℕ → Prop)
    (h : ∀ i ∈ s, CountIsLittleO (P i)) :
    CountIsLittleO (fun N => ∃ i ∈ s, P i N) := by
  classical
  induction s using Finset.induction with
  | empty =>
    exact CountIsLittleO.mono (fun n hn => by simpa using hn) CountIsLittleO_false
  | @insert a t ha ih =>
    have hcong : (fun N => ∃ i ∈ insert a t, P i N) = (fun N => P a N ∨ ∃ i ∈ t, P i N) := by
      funext N; simp only [Finset.exists_mem_insert]
    rw [hcong]
    exact (h a (Finset.mem_insert_self a t)).or
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- The chosen prime `qER e (activeSet e a)` is genuinely prime (`Aval ≥ 2` since `1 ∈ activeSet`). -/
lemma qER_prime (e a : ℕ) (he : 2 ≤ e) (ha : 1 ≤ a) :
    (qER e (activeSet e a)).Prime := by
  rw [qER]
  apply Nat.minFac_prime
  set R := activeSet e a with hR
  have hea : e * a ≠ 0 := by positivity
  have h1R : (1 : ℕ) ∈ R := by
    rw [hR, activeSet, Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨one_dvd _, hea⟩, by omega⟩
  have hsum1 : (1 : ℚ) ≤ ∑ r ∈ R, (1 : ℚ) / r :=
    le_trans (by norm_num) (Finset.single_le_sum (fun i _ => by positivity) h1R)
  have hge2 : (2 : ℚ) ≤ (e : ℚ) * ∑ r ∈ R, (1 : ℚ) / r := by
    calc (2 : ℚ) ≤ (e : ℚ) := by exact_mod_cast he
      _ = (e : ℚ) * 1 := (mul_one _).symm
      _ ≤ (e : ℚ) * ∑ r ∈ R, (1 : ℚ) / r := mul_le_mul_of_nonneg_left hsum1 (by positivity)
  intro h1
  rw [Aval] at h1
  set q : ℚ := (e : ℚ) * ∑ r ∈ R, (1 : ℚ) / r with hq
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hge2
  have hnum1 : q.num = 1 := by
    have hnpos : 0 < q.num := Rat.num_pos.mpr hqpos
    omega
  have hle1 : q ≤ 1 := by
    rw [← Rat.num_div_den q, hnum1, div_le_one (by exact_mod_cast q.den_pos)]
    exact_mod_cast q.den_pos
  linarith [hge2]

open ArithmeticFunction in
/-- **Mod-`q` deduction (`e ≥ 2`).** If `N = F e (a*b)` (smooth–rough split) is coprime to `Q_E`,
then the rough part `b` lies in `B_q` for `q = qER e (activeSet e a)`. -/
lemma e_ge_two_forces_Bq (e a b E : ℕ) (he : 2 ≤ e) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hsmooth : ∀ p, p ∣ a → p.Prime → p ≤ e) (hrough : ∀ p, p ∣ b → p.Prime → e < p)
    (hqS : qER e (activeSet e a) ∈ S E)
    (hcop : Nat.Coprime (F e (a * b)) (Qpr E)) :
    Bq (qER e (activeSet e a)) b := by
  set q := qER e (activeSet e a) with hq
  have hqp : q.Prime := qER_prime e a he ha
  have hqHfun : q ∣ Hfun e a := forced_prime e a he ha
  have hqQ : q ∣ Qpr E := Finset.dvd_prod_of_mem _ hqS
  have hqN : ¬ q ∣ F e (a * b) := by
    intro hqd
    exact hqp.ne_one (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hqd hqQ))
  have hsr := smooth_rough e a b he hsmooth hrough
  have hble : b ≤ sigma 1 b := by
    rw [sigma_one_apply]
    exact Finset.single_le_sum (fun i _ => Nat.zero_le i) (Nat.mem_divisors_self b (by omega))
  have hmul : Hfun e a * b ≤ sigma 1 (e * a) * sigma 1 b :=
    Nat.mul_le_mul (by rw [Hfun]; exact Nat.sub_le _ _) hble
  have hadd : sigma 1 (e * a) * sigma 1 b = F e (a * b) + Hfun e a * b := by rw [hsr]; omega
  intro hqb
  have hqss : q ∣ sigma 1 (e * a) * sigma 1 b := hqb.mul_left _
  rw [hadd] at hqss
  exact hqN ((Nat.dvd_add_right (hqHfun.mul_right b)).mp (by rwa [add_comm] at hqss))

/-- `d ≤ F e d` (the divisor `d` itself is one of the summands). -/
lemma F_ge (e d : ℕ) (he : 1 ≤ e) (hd : 1 ≤ d) : d ≤ F e d := by
  rw [F]
  refine Finset.single_le_sum (fun i _ => Nat.zero_le i) ?_
  rw [Finset.mem_filter, Nat.mem_divisors]
  exact ⟨⟨dvd_mul_left d e, by positivity⟩, le_refl d⟩

/-- `countUpTo` as a `Finset.card`. -/
lemma countUpTo_eq_card (P : ℕ → Prop) [DecidablePred P] (X : ℕ) :
    countUpTo P X = ((Finset.range (X + 1)).filter P).card := by
  unfold countUpTo setUpTo
  rw [← Set.ncard_coe_finset]
  congr 1
  ext n
  simp [Nat.lt_succ_iff]

open Classical in
/-- Count bound feeding `thinSet_transfer`: values `F e (a*b)` with `a` smooth, `b ∈ B_q`,
counted by smooth part `a`. -/
lemma count_Fe_le_sum (e q X : ℕ) (he : 1 ≤ e) :
    countUpTo (fun N => ∃ a b, a ∈ Nat.smoothNumbers (e + 1) ∧ 1 ≤ b ∧ Bq q b ∧ N = F e (a * b)) X
      ≤ ∑ a ∈ (Finset.range (X + 1)).filter (· ∈ Nat.smoothNumbers (e + 1)),
          countUpTo (Bq q) (X / a) := by
  rw [countUpTo_eq_card]
  simp_rw [countUpTo_eq_card]
  calc ((Finset.range (X + 1)).filter
          (fun N => ∃ a b, a ∈ Nat.smoothNumbers (e + 1) ∧ 1 ≤ b ∧ Bq q b ∧ N = F e (a * b))).card
      ≤ (((Finset.range (X + 1)).filter (· ∈ Nat.smoothNumbers (e + 1))).biUnion (fun a =>
          ((Finset.range (X / a + 1)).filter (Bq q)).image (fun b => F e (a * b)))).card :=
        Finset.card_le_card (by
          intro N hN
          rw [Finset.mem_filter, Finset.mem_range] at hN
          obtain ⟨hNX, a, b, hsm, hb1, hbq, hNeq⟩ := hN
          have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr hsm.1
          have hab1 : 1 ≤ a * b :=
            Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
          have habX : a * b ≤ X :=
            le_trans (le_trans (F_ge e (a * b) he hab1) hNeq.ge) (by omega)
          rw [Finset.mem_biUnion]
          refine ⟨a, ?_, ?_⟩
          · rw [Finset.mem_filter, Finset.mem_range]
            exact ⟨lt_of_le_of_lt (le_trans (Nat.le_mul_of_pos_right a (by omega)) habX)
              (by omega), hsm⟩
          · rw [Finset.mem_image]
            refine ⟨b, ?_, hNeq.symm⟩
            rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, Nat.le_div_iff_mul_le ha1]
            exact ⟨by rwa [mul_comm] at habX, hbq⟩)
    _ ≤ ∑ a ∈ (Finset.range (X + 1)).filter (· ∈ Nat.smoothNumbers (e + 1)),
          (((Finset.range (X / a + 1)).filter (Bq q)).image (fun b => F e (a * b))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ a ∈ (Finset.range (X + 1)).filter (· ∈ Nat.smoothNumbers (e + 1)),
          ((Finset.range (X / a + 1)).filter (Bq q)).card :=
        Finset.sum_le_sum (fun a _ => Finset.card_image_le)

open Classical in
/-- For fixed `e ≥ 1` and prime `q`, the set of `F e (a*b)` (`a` smooth, `b ∈ B_q`) is density-zero. -/
lemma per_q_littleO (e q : ℕ) (he : 1 ≤ e) (hq : q.Prime) :
    CountIsLittleO (fun N => ∃ a b,
      a ∈ Nat.smoothNumbers (e + 1) ∧ 1 ≤ b ∧ Bq q b ∧ N = F e (a * b)) := by
  have hBle0 : ∀ n, countUpTo (Bq q) n ≤ n := by
    intro n
    have h0 : (0 : ℕ) ∉ setUpTo (Bq q) n := fun h0 => h0.2 (by simp)
    calc countUpTo (Bq q) n
        ≤ (↑(Finset.Icc 1 n) : Set ℕ).ncard :=
          Set.ncard_le_ncard (fun m hm => by
            rw [Finset.coe_Icc, Set.mem_Icc]
            exact ⟨Nat.one_le_iff_ne_zero.mpr (fun h => h0 (h ▸ hm)), hm.1⟩)
            (Finset.finite_toSet _)
      _ = (Finset.Icc 1 n).card := Set.ncard_coe_finset _
      _ = n := by rw [Nat.card_Icc]; omega
  have hthin := thinSet_transfer (fun a => a ∈ Nat.smoothNumbers (e + 1))
    (fun n => (countUpTo (Bq q) n : ℝ)) (fun n => countUpTo_nonneg _ n)
    (fun n => by exact_mod_cast hBle0 n) (sigma_avoid q hq) (smooth_recip_summable (e + 1))
  refine Asymptotics.IsBigO.trans_isLittleO ?_ hthin
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, Filter.Eventually.of_forall (fun X => ?_)⟩
  rw [Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (Finset.sum_nonneg (fun a _ => countUpTo_nonneg _ _)), one_mul]
  exact_mod_cast count_Fe_le_sum e q X he

open Classical in
/-- The `e ≥ 2` case of Prop 5.3 (density-zero via the mod-`q` deduction + `thinSet_transfer`). -/
lemma e_ge_two_littleO (E e : ℕ) (he2 : 2 ≤ e) (heE : e ≤ E) :
    CountIsLittleO (fun N => Nat.Coprime N (Qpr E) ∧ ∃ d, N = F e d) := by
  refine CountIsLittleO.mono (Q := fun N => ∃ q ∈ (S E).filter Nat.Prime, ∃ a b,
    a ∈ Nat.smoothNumbers (e + 1) ∧ 1 ≤ b ∧ Bq q b ∧ N = F e (a * b)) ?_ ?_
  · rintro N ⟨hcop, d, hd⟩
    have hN0 : N ≠ 0 := by
      rintro rfl
      rw [Nat.coprime_zero_left] at hcop
      exact absurd (two_dvd_Qpr E (by omega)) (by rw [hcop]; decide)
    have hd1 : 1 ≤ d := by
      rcases Nat.eq_zero_or_pos d with rfl | h
      · exact absurd (show N = 0 by rw [hd]; simp [F]) hN0
      · exact h
    obtain ⟨a, b, hdab, _, ha1, hb1, hsm, hro⟩ := smooth_rough_factor e d hd1
    have hqS : qER e (activeSet e a) ∈ S E := by
      rw [S, Finset.mem_insert]
      refine Or.inr (Finset.mem_biUnion.mpr ⟨e, Finset.mem_Icc.mpr ⟨he2, heE⟩,
        Finset.mem_image.mpr ⟨activeSet e a, Finset.mem_powerset.mpr (fun r hr => ?_), rfl⟩⟩)
      rw [activeSet, Finset.mem_filter, Nat.mem_divisors] at hr
      rw [Finset.mem_Ico]
      exact ⟨Nat.one_le_iff_ne_zero.mpr (fun h => hr.1.2 (zero_dvd_iff.mp (h ▸ hr.1.1))), hr.2⟩
    have hcopab : Nat.Coprime (F e (a * b)) (Qpr E) := by rw [hd, hdab] at hcop; exact hcop
    refine ⟨qER e (activeSet e a), Finset.mem_filter.mpr ⟨hqS, qER_prime e a he2 ha1⟩,
      a, b, ?_, hb1, e_ge_two_forces_Bq e a b E he2 ha1 hb1 hsm hro hqS hcopab, by rw [hd, hdab]⟩
    rw [Nat.mem_smoothNumbers]
    refine ⟨by omega, fun p hp => ?_⟩
    have := hsm p (Nat.dvd_of_mem_primeFactorsList hp) (Nat.prime_of_mem_primeFactorsList hp)
    omega
  · exact CountIsLittleO_biUnion _ _ (fun q hq => per_q_littleO e q (by omega)
      (Finset.mem_filter.mp hq).2)

/-- **Bounded-cofactor exclusion** (paper Prop 5.3). -/
theorem small_e_exclusion (E : ℕ) (hE : 2 ≤ E) :
    CountIsLittleO
      (fun N => Nat.Coprime N (Qpr E) ∧ ∃ e d, 1 ≤ e ∧ e ≤ E ∧ N = F e d) := by
  refine CountIsLittleO.mono (Q := fun N => (Nat.Coprime N (Qpr E) ∧ ∃ d, N = F 1 d) ∨
    (∃ e ∈ Finset.Icc 2 E, Nat.Coprime N (Qpr E) ∧ ∃ d, N = F e d)) ?_ ?_
  · rintro N ⟨hcop, e, d, h1e, heE, hd⟩
    rcases Nat.lt_or_ge e 2 with he1 | he2
    · exact Or.inl ⟨hcop, d, by rwa [show e = 1 by omega] at hd⟩
    · exact Or.inr ⟨e, Finset.mem_Icc.mpr ⟨he2, heE⟩, hcop, d, hd⟩
  · exact (small_e_one_littleO E hE).or (CountIsLittleO_biUnion _ _ (fun e he =>
      e_ge_two_littleO E e (Finset.mem_Icc.mp he).1 (Finset.mem_Icc.mp he).2))

/-- All elements of `S E` are positive. -/
lemma S_pos (E : ℕ) : ∀ q ∈ S E, 0 < q := by
  intro q hq
  rw [S, Finset.mem_insert] at hq
  rcases hq with rfl | hq
  · norm_num
  · simp only [Finset.mem_biUnion, Finset.mem_image] at hq
    obtain ⟨e, _, R, _, rfl⟩ := hq
    rw [qER]; exact Nat.minFac_pos _

lemma Qpr_pos (E : ℕ) : 0 < Qpr E := Finset.prod_pos (S_pos E)

/-- `δ_E = ∏_{p ∣ Q_E} (1 - 1/p)` (Euler product form of the totient density). -/
lemma delta_eq_prod (E : ℕ) :
    δ E = ∏ p ∈ (Qpr E).primeFactors, (1 - 1 / (p : ℝ)) := by
  have hQ0 : (Qpr E : ℝ) ≠ 0 := by have := Qpr_pos E; positivity
  rw [δ]
  have hr : (Nat.totient (Qpr E) : ℝ)
      = (Qpr E : ℝ) * ∏ p ∈ (Qpr E).primeFactors, (1 - (p : ℝ)⁻¹) := by
    have hcast := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors (Qpr E))
    push_cast at hcast
    exact hcast
  rw [hr, mul_comm (Qpr E : ℝ), mul_div_assoc, div_self hQ0, mul_one]
  apply Finset.prod_congr rfl
  intro p _
  rw [one_div]

/-- The reduced numerator `Aval e R` is bounded by `E^(E+2)` (the lowest-terms numerator
divides the common-denominator numerator `e·∑ (E-1)!/r`). -/
lemma Aval_le (E e : ℕ) (R : Finset ℕ) (he : e ≤ E) (hR : R ⊆ Finset.Ico 1 e) :
    Aval e R ≤ E ^ (E + 2) := by
  rcases Nat.eq_zero_or_pos e with rfl | hepos
  · simp [Aval]
  set Dn : ℕ := Nat.factorial (E - 1) with hDn
  have hDnpos : 0 < Dn := Nat.factorial_pos (E - 1)
  have hrdvd : ∀ r ∈ R, r ∣ Dn := fun r hr => by
    have hmem := hR hr; rw [Finset.mem_Ico] at hmem
    exact Nat.dvd_factorial (by omega) (by omega)
  set An : ℕ := e * ∑ r ∈ R, Dn / r with hAn
  have hDn0 : (Dn : ℚ) ≠ 0 := by exact_mod_cast hDnpos.ne'
  have hVeq : (e : ℚ) * ∑ r ∈ R, (1 : ℚ) / r = Rat.divInt (An : ℤ) (Dn : ℤ) := by
    rw [Rat.divInt_eq_div, Int.cast_natCast, Int.cast_natCast,
      eq_div_iff (by exact_mod_cast hDnpos.ne' : (Dn : ℚ) ≠ 0), hAn]
    push_cast
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl (fun r hr => ?_)
    have hr0 : (r : ℚ) ≠ 0 := by
      have hmem := hR hr; rw [Finset.mem_Ico] at hmem
      exact Nat.cast_ne_zero.mpr (by omega)
    rw [Nat.cast_div (hrdvd r hr) hr0, one_div, inv_mul_eq_div]
  have hAval_le_An : Aval e R ≤ An := by
    rcases Nat.eq_zero_or_pos An with hA0 | hApos
    · rw [Aval, hVeq, hA0]; simp
    · have hdvd : (Aval e R : ℤ) ∣ (An : ℤ) := by
        rw [Aval]
        have hnd := Rat.num_dvd (An : ℤ) (b := (Dn : ℤ)) (by exact_mod_cast hDnpos.ne')
        rw [← hVeq] at hnd
        rwa [Int.natAbs_dvd]
      exact Nat.le_of_dvd hApos (by exact_mod_cast hdvd)
  have hAn_le : An ≤ E ^ (E + 2) := by
    rw [hAn]
    calc e * ∑ r ∈ R, Dn / r
        ≤ E * (R.card * Dn) := by
          refine Nat.mul_le_mul he ?_
          calc ∑ r ∈ R, Dn / r ≤ ∑ _r ∈ R, Dn := Finset.sum_le_sum (fun r _ => Nat.div_le_self _ _)
            _ = R.card * Dn := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ E * (E * E ^ E) := by
          refine Nat.mul_le_mul_left _ (Nat.mul_le_mul ?_ ?_)
          · calc R.card ≤ (Finset.Ico 1 e).card := Finset.card_le_card hR
              _ = e - 1 := by rw [Nat.card_Ico]
              _ ≤ E := by omega
          · calc Dn ≤ (E - 1) ^ (E - 1) := Nat.factorial_le_pow _
              _ ≤ E ^ E := le_trans (Nat.pow_le_pow_left (by omega) (E - 1))
                  (Nat.pow_le_pow_right (by omega) (by omega))
      _ = E ^ (E + 2) := by ring
  omega

/-- The chosen prime `qER e R` is bounded by `E^(E+2)`. -/
lemma qER_le (E e : ℕ) (R : Finset ℕ) (hE : 2 ≤ E) (he : e ≤ E) (hR : R ⊆ Finset.Ico 1 e) :
    qER e R ≤ E ^ (E + 2) := by
  rw [qER]
  rcases Nat.eq_zero_or_pos (Aval e R) with h0 | hpos
  · rw [h0, Nat.minFac_zero]
    calc 2 ≤ E := hE
      _ ≤ E ^ (E + 2) := Nat.le_self_pow (by omega) E
  · exact le_trans (Nat.minFac_le hpos) (Aval_le E e R he hR)

/-- Every prime factor of `Q_E` is at most `E^(E+2)`. -/
lemma primeFactors_Qpr_le (E : ℕ) (hE : 2 ≤ E) :
    ∀ p ∈ (Qpr E).primeFactors, p ≤ E ^ (E + 2) := by
  intro p hp
  obtain ⟨hpp, hpdvd, _⟩ := Nat.mem_primeFactors.1 hp
  rw [Qpr] at hpdvd
  obtain ⟨q, hqS, hpq⟩ := hpp.prime.exists_mem_finset_dvd hpdvd
  have hqle : q ≤ E ^ (E + 2) := by
    rw [S, Finset.mem_insert] at hqS
    rcases hqS with rfl | hqS
    · calc 2 ≤ E := hE
        _ ≤ E ^ (E + 2) := Nat.le_self_pow (by omega) E
    · simp only [Finset.mem_biUnion, Finset.mem_image] at hqS
      obtain ⟨e, hemem, R, hRmem, rfl⟩ := hqS
      rw [Finset.mem_Icc] at hemem
      rw [Finset.mem_powerset] at hRmem
      exact qER_le E e R hE hemem.2 hRmem
  exact le_trans (Nat.le_of_dvd (S_pos E q hqS) hpq) hqle

/-- **Density of the sifted set, lower bound** (paper Lemma 5.4). -/
theorem sift_density_lb :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ E : ℕ, 2 ≤ E →
      c₁ / ((E : ℝ) * Real.log (2 * E)) ≤ δ E := by
  obtain ⟨c₀, hc₀, hmertens⟩ := mertens_third_lower
  refine ⟨c₀ / 3, by positivity, fun E hE => ?_⟩
  have hE2R : (2 : ℝ) ≤ E := by exact_mod_cast hE
  have hY2 : 2 ≤ E ^ (E + 2) := by
    calc 2 ≤ E := hE
      _ ≤ E ^ (E + 2) := Nat.le_self_pow (by omega) E
  have hYR : (2 : ℝ) ≤ (E ^ (E + 2) : ℕ) := by exact_mod_cast hY2
  have hsub : (Qpr E).primeFactors ⊆ (Finset.range (E ^ (E + 2) + 1)).filter Nat.Prime := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := primeFactors_Qpr_le E hE p hp; omega, (Nat.mem_primeFactors.1 hp).1⟩
  have hmono : ∏ p ∈ (Finset.range (E ^ (E + 2) + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))
      ≤ ∏ p ∈ (Qpr E).primeFactors, (1 - 1 / (p : ℝ)) := by
    rw [← Finset.prod_sdiff hsub]
    apply mul_le_of_le_one_left
    · apply Finset.prod_nonneg
      intro p hp
      have hpp := (Nat.mem_primeFactors.1 hp).1
      have hp1 : (1 : ℝ) ≤ p := by have := hpp.two_le; exact_mod_cast (show 1 ≤ p by omega)
      have : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hp1
      linarith
    · apply Finset.prod_le_one₀
      · intro p hp
        have hpp : p.Prime := (Finset.mem_filter.1 (Finset.mem_sdiff.1 hp).1).2
        have hp1 : (1 : ℝ) ≤ p := by have := hpp.two_le; exact_mod_cast (show 1 ≤ p by omega)
        have : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hp1
        linarith
      · intro p hp
        have hpp : p.Prime := (Finset.mem_filter.1 (Finset.mem_sdiff.1 hp).1).2
        have hppos : (0 : ℝ) < p := by have := hpp.pos; exact_mod_cast this
        have : 0 ≤ 1 / (p : ℝ) := by positivity
        linarith
  have hA2 := hmertens (E ^ (E + 2)) hY2
  have hElogpos : 0 < (E : ℝ) * Real.log (2 * E) := by
    apply mul_pos (by linarith)
    exact Real.log_pos (by nlinarith [hE2R])
  have hlogYpos : 0 < Real.log (2 * (E ^ (E + 2) : ℕ)) :=
    Real.log_pos (by nlinarith [hYR])
  have hlog : Real.log (2 * (E ^ (E + 2) : ℕ)) ≤ 3 * ((E : ℝ) * Real.log (2 * E)) := by
    have hElog : Real.log (2 * (E : ℝ)) = Real.log 2 + Real.log E :=
      Real.log_mul (by norm_num) (by positivity)
    have hYlog : Real.log (2 * (E ^ (E + 2) : ℕ)) = Real.log 2 + (E + 2 : ℝ) * Real.log E := by
      push_cast
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast; ring
    rw [hYlog, hElog]
    have hlogE : 0 ≤ Real.log (E : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ E by omega))
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith [hlogE, hlog2, hE2R]
  rw [delta_eq_prod]
  calc c₀ / 3 / ((E : ℝ) * Real.log (2 * E))
      = c₀ / (3 * ((E : ℝ) * Real.log (2 * E))) := by rw [div_div]
    _ ≤ c₀ / Real.log (2 * (E ^ (E + 2) : ℕ)) := by
        rw [div_le_div_iff₀ (by linarith) hlogYpos]
        exact mul_le_mul_of_nonneg_left hlog hc₀.le
    _ ≤ ∏ p ∈ (Finset.range (E ^ (E + 2) + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)) := hA2
    _ ≤ ∏ p ∈ (Qpr E).primeFactors, (1 - 1 / (p : ℝ)) := hmono

/-- The sifted set has lower density at least `δ_E` (paper Lemma 5.4, counting). -/
theorem sift_lowerDensity (E : ℕ) (hE : 2 ≤ E) :
    δ E ≤ lowerDensity (fun N => Nat.Coprime N (Qpr E)) := by
  have hSpos : ∀ q ∈ S E, 0 < q := by
    intro q hq
    rw [S, Finset.mem_insert] at hq
    rcases hq with rfl | hq
    · norm_num
    · simp only [Finset.mem_biUnion, Finset.mem_image] at hq
      obtain ⟨e, _, R, _, rfl⟩ := hq
      rw [qER]; exact Nat.minFac_pos _
  have hQpos : 0 < Qpr E := Finset.prod_pos hSpos
  have hQR : (0 : ℝ) < Qpr E := by exact_mod_cast hQpos
  have hφpos : 0 < Nat.totient (Qpr E) := Nat.totient_pos.2 hQpos
  -- counting via finsets
  have hcard : ∀ X, countUpTo (fun n => Nat.Coprime n (Qpr E)) X
      = ((Finset.range (X + 1)).filter (fun n => Nat.Coprime n (Qpr E))).card := by
    intro X
    have hset : setUpTo (fun n => Nat.Coprime n (Qpr E)) X
        = ↑((Finset.range (X + 1)).filter (fun n => Nat.Coprime n (Qpr E))) := by
      ext n
      simp only [setUpTo, Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_range, Nat.lt_succ_iff]
    unfold countUpTo
    rw [hset, Set.ncard_coe_finset]
  -- per-block count: each block of length `Q` has exactly `φ Q` coprimes
  have hblock : ∀ B : ℕ,
      ((Finset.range (Qpr E * B)).filter (fun n => Nat.Coprime n (Qpr E))).card
        = B * Nat.totient (Qpr E) := by
    intro B
    induction B with
    | zero => simp
    | succ b ih =>
      have hu : Finset.range (Qpr E * (b + 1))
          = Finset.range (Qpr E * b) ∪ Finset.Ico (Qpr E * b) (Qpr E * b + Qpr E) := by
        rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
          Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (by omega), Nat.mul_succ]
      have hdisj : Disjoint (Finset.range (Qpr E * b))
          (Finset.Ico (Qpr E * b) (Qpr E * b + Qpr E)) := by
        rw [Finset.range_eq_Ico]
        exact Finset.Ico_disjoint_Ico_consecutive 0 (Qpr E * b) (Qpr E * b + Qpr E)
      have hbk : ((Finset.Ico (Qpr E * b) (Qpr E * b + Qpr E)).filter
          (fun n => Nat.Coprime n (Qpr E))).card = Nat.totient (Qpr E) := by
        rw [← Nat.filter_coprime_Ico_eq_totient (Qpr E) (Qpr E * b)]
        congr 1
        apply Finset.filter_congr
        intro x _
        exact ⟨fun h => Nat.coprime_comm.1 h, fun h => Nat.coprime_comm.1 h⟩
      rw [hu, Finset.filter_union,
        Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj), ih, hbk]
      ring
  -- lower bound on the count, for `X ≥ 1`
  have hlb : ∀ X : ℕ, 1 ≤ X →
      δ E - (Nat.totient (Qpr E) : ℝ) / X
        ≤ (countUpTo (fun n => Nat.Coprime n (Qpr E)) X : ℝ) / X := by
    intro X hX1
    have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
    have hdm := Nat.div_add_mod (X + 1) (Qpr E)
    have hmod : (X + 1) % Qpr E < Qpr E := Nat.mod_lt _ hQpos
    have hQBle : Qpr E * ((X + 1) / Qpr E) ≤ X + 1 := by
      rw [mul_comm]; exact Nat.div_mul_le_self _ _
    have hcountlb : (X + 1) / Qpr E * Nat.totient (Qpr E)
        ≤ countUpTo (fun n => Nat.Coprime n (Qpr E)) X := by
      rw [hcard, ← hblock ((X + 1) / Qpr E)]
      apply Finset.card_le_card
      intro n hn
      rw [Finset.mem_filter, Finset.mem_range] at hn ⊢
      exact ⟨lt_of_lt_of_le hn.1 hQBle, hn.2⟩
    have hcountlb' : ((X + 1) / Qpr E : ℕ) * (Nat.totient (Qpr E) : ℝ)
        ≤ (countUpTo (fun n => Nat.Coprime n (Qpr E)) X : ℝ) := by exact_mod_cast hcountlb
    have hXle : (X : ℝ) ≤ (Qpr E : ℝ) * (((X + 1) / Qpr E : ℕ) + 1) := by
      have : X + 1 < Qpr E * ((X + 1) / Qpr E + 1) := by rw [Nat.mul_succ]; omega
      have h2 : (X : ℝ) + 1 < (Qpr E : ℝ) * (((X + 1) / Qpr E : ℕ) + 1) := by exact_mod_cast this
      linarith
    rw [δ]
    rw [div_sub_div _ _ (ne_of_gt hQR) (ne_of_gt hXpos), div_le_div_iff₀ (by positivity) hXpos]
    have hφR : (0 : ℝ) ≤ (Nat.totient (Qpr E) : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hXle (mul_nonneg hφR hXpos.le),
      mul_le_mul_of_nonneg_left hcountlb' (mul_nonneg hQR.le hXpos.le), hXpos, hQR, hφR]
  -- conclude `δ E ≤ liminf (count / X)`
  rw [lowerDensity]
  apply le_of_forall_pos_le_add
  intro ε hε
  have hφtend : Tendsto (fun X : ℕ => (Nat.totient (Qpr E) : ℝ) / X) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (Nat.totient (Qpr E) : ℝ))).div_atTop
      tendsto_natCast_atTop_atTop
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop
      (fun X : ℕ => (countUpTo (fun n => Nat.Coprime n (Qpr E)) X : ℝ) / X) := by
    refine ⟨2, fun z hz => ?_⟩
    rw [eventually_map] at hz
    obtain ⟨X, hX⟩ := hz.exists
    exact le_trans hX (countUpTo_div_le_two _ X)
  have hev : ∀ᶠ X : ℕ in atTop,
      δ E - ε ≤ (countUpTo (fun n => Nat.Coprime n (Qpr E)) X : ℝ) / X := by
    filter_upwards [hφtend (Iio_mem_nhds hε), eventually_ge_atTop 1] with X hφX hX1
    have hh := hlb X hX1
    simp only [Set.mem_preimage, Set.mem_Iio] at hφX
    linarith [hh, hφX]
  have hfin : δ E - ε ≤
      liminf (fun X : ℕ => (countUpTo (fun n => Nat.Coprime n (Qpr E)) X : ℝ) / X) atTop :=
    le_liminf_of_le hcobdd hev
  linarith [hfin]



/-! ## Section 6 -- Third moment (Lem 6.1) and large-cofactor bound (Prop 6.3; counts PAIRS, not values). -/


/-- The third-moment constant `T₃(e) = ∑_{r,s,t ≥ e} 1/(rst·lcm(r,s,t))`. -/
noncomputable def T3 (e : ℕ) : ℝ≥0∞ :=
  ∑' t : ℕ × ℕ × ℕ,
    (if e ≤ t.1 ∧ e ≤ t.2.1 ∧ e ≤ t.2.2 then
      ENNReal.ofReal
        (1 / ((t.1 * t.2.1 * t.2.2 * Nat.lcm t.1 (Nat.lcm t.2.1 t.2.2) : ℕ) : ℝ))
    else 0)

/-- The third-moment constant is finite (crude bound: `lcm(r,s,t)³ ≥ rst`, so each term is
`≤ (rst)^{-4/3}`, and `∑ (rst)^{-4/3} = ζ(4/3)³ < ∞`). -/
lemma T3_lt_top (e : ℕ) : T3 e < ⊤ := by
  have hf : ∀ r : ℕ, (0 : ℝ) ≤ (r : ℝ) ^ (-(4 / 3 : ℝ)) := fun r => Real.rpow_nonneg (by positivity) _
  have hsum : Summable (fun r : ℕ => (r : ℝ) ^ (-(4 / 3 : ℝ))) := by
    have heq : (fun r : ℕ => (r : ℝ) ^ (-(4 / 3 : ℝ))) = (fun r : ℕ => 1 / (r : ℝ) ^ (4 / 3 : ℝ)) := by
      funext r; rw [Real.rpow_neg (by positivity), one_div]
    rw [heq]; exact (Real.summable_one_div_nat_rpow).mpr (by norm_num)
  let f : ℕ → ℝ≥0∞ := fun r => ENNReal.ofReal ((r : ℝ) ^ (-(4 / 3 : ℝ)))
  have hMfin : (∑' r : ℕ, f r) ≠ ⊤ := by
    rw [show (∑' r : ℕ, f r) = ∑' r : ℕ, ENNReal.ofReal ((r : ℝ) ^ (-(4 / 3 : ℝ))) from rfl,
      ← ENNReal.ofReal_tsum_of_nonneg hf hsum]
    exact ENNReal.ofReal_ne_top
  -- factorize the triple sum into a product of three single sums
  have hfactor : (∑' p : ℕ × ℕ × ℕ, f p.1 * f p.2.1 * f p.2.2)
      = (∑' r, f r) * (∑' s, f s) * (∑' t, f t) := by
    rw [ENNReal.tsum_prod']
    rw [show (∑' r, ∑' q : ℕ × ℕ, f r * f q.1 * f q.2)
          = ∑' r, f r * (∑' q : ℕ × ℕ, f q.1 * f q.2) from
        tsum_congr (fun r => by rw [← ENNReal.tsum_mul_left]; exact tsum_congr (fun q => by ring))]
    rw [ENNReal.tsum_mul_right, mul_assoc]
    congr 1
    rw [ENNReal.tsum_prod']
    rw [show (∑' s, ∑' t, f s * f t) = ∑' s, f s * (∑' t, f t) from
        tsum_congr (fun s => ENNReal.tsum_mul_left)]
    rw [ENNReal.tsum_mul_right]
  have hbound : T3 e ≤ ∑' p : ℕ × ℕ × ℕ, f p.1 * f p.2.1 * f p.2.2 := by
    rw [T3]
    refine ENNReal.tsum_le_tsum (fun p => ?_)
    obtain ⟨r, s, t⟩ := p
    by_cases hc : e ≤ r ∧ e ≤ s ∧ e ≤ t
    · rw [if_pos hc]
      show ENNReal.ofReal (1 / ((r * s * t * Nat.lcm r (Nat.lcm s t) : ℕ) : ℝ))
          ≤ ENNReal.ofReal ((r : ℝ) ^ (-(4 / 3 : ℝ)))
            * ENNReal.ofReal ((s : ℝ) ^ (-(4 / 3 : ℝ)))
            * ENNReal.ofReal ((t : ℝ) ^ (-(4 / 3 : ℝ)))
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp [Real.zero_rpow (show -(4 / 3 : ℝ) ≠ 0 by norm_num)]
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · simp [Real.zero_rpow (show -(4 / 3 : ℝ) ≠ 0 by norm_num)]
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · simp [Real.zero_rpow (show -(4 / 3 : ℝ) ≠ 0 by norm_num)]
      rw [← ENNReal.ofReal_mul (hf r), ← ENNReal.ofReal_mul (mul_nonneg (hf r) (hf s))]
      apply ENNReal.ofReal_le_ofReal
      rw [← Real.mul_rpow (by positivity) (by positivity),
        ← Real.mul_rpow (by positivity) (by positivity)]
      have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
      have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
      have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
      have hLpos : 0 < Nat.lcm r (Nat.lcm s t) :=
        Nat.pos_of_ne_zero (by simp only [ne_eq, Nat.lcm_eq_zero_iff]; omega)
      have hrst0 : (0 : ℝ) < (r : ℝ) * s * t := by positivity
      have hrL : (r : ℝ) ≤ (Nat.lcm r (Nat.lcm s t) : ℝ) := by
        exact_mod_cast Nat.le_of_dvd hLpos (Nat.dvd_lcm_left _ _)
      have hsL : (s : ℝ) ≤ (Nat.lcm r (Nat.lcm s t) : ℝ) := by
        exact_mod_cast Nat.le_of_dvd hLpos
          (dvd_trans (Nat.dvd_lcm_left s t) (Nat.dvd_lcm_right r _))
      have htL : (t : ℝ) ≤ (Nat.lcm r (Nat.lcm s t) : ℝ) := by
        exact_mod_cast Nat.le_of_dvd hLpos
          (dvd_trans (Nat.dvd_lcm_right s t) (Nat.dvd_lcm_right r _))
      have hcube : (r : ℝ) * s * t ≤ (Nat.lcm r (Nat.lcm s t) : ℝ) ^ 3 := by
        have h1 : (r : ℝ) * s ≤ (Nat.lcm r (Nat.lcm s t) : ℝ) * (Nat.lcm r (Nat.lcm s t) : ℝ) :=
          mul_le_mul hrL hsL (by positivity) (by positivity)
        calc (r : ℝ) * s * t
            ≤ (Nat.lcm r (Nat.lcm s t) : ℝ) * (Nat.lcm r (Nat.lcm s t) : ℝ)
              * (Nat.lcm r (Nat.lcm s t) : ℝ) := mul_le_mul h1 htL (by positivity) (by positivity)
          _ = (Nat.lcm r (Nat.lcm s t) : ℝ) ^ 3 := by ring
      have h13 : ((r : ℝ) * s * t) ^ (1 / 3 : ℝ) ≤ (Nat.lcm r (Nat.lcm s t) : ℝ) := by
        have hLrpow : (Nat.lcm r (Nat.lcm s t) : ℝ)
            = ((Nat.lcm r (Nat.lcm s t) : ℝ) ^ 3) ^ (1 / 3 : ℝ) := by
          rw [← Real.rpow_natCast (Nat.lcm r (Nat.lcm s t) : ℝ) 3, ← Real.rpow_mul (by positivity)]
          norm_num
        rw [hLrpow]
        exact Real.rpow_le_rpow (by positivity) hcube (by norm_num)
      have hcast : ((r * s * t * Nat.lcm r (Nat.lcm s t) : ℕ) : ℝ)
          = (r : ℝ) * s * t * (Nat.lcm r (Nat.lcm s t) : ℝ) := by push_cast; ring
      rw [hcast, Real.rpow_neg (by positivity), ← one_div]
      apply one_div_le_one_div_of_le (by positivity)
      calc ((r : ℝ) * s * t) ^ (4 / 3 : ℝ)
          = (r : ℝ) * s * t * ((r : ℝ) * s * t) ^ (1 / 3 : ℝ) := by
            rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, Real.rpow_add hrst0, Real.rpow_one]
        _ ≤ (r : ℝ) * s * t * (Nat.lcm r (Nat.lcm s t) : ℝ) :=
            mul_le_mul_of_nonneg_left h13 (le_of_lt hrst0)
    · rw [if_neg hc]; exact zero_le'
  calc T3 e ≤ ∑' p : ℕ × ℕ × ℕ, f p.1 * f p.2.1 * f p.2.2 := hbound
    _ = (∑' r, f r) * (∑' s, f s) * (∑' t, f t) := hfactor
    _ < ⊤ := ENNReal.mul_lt_top
        (ENNReal.mul_lt_top hMfin.lt_top hMfin.lt_top) hMfin.lt_top

/-- Cube of a finite sum as a sum over the triple product. -/
lemma sum_cube_eq_prod {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (∑ r ∈ s, a r) ^ 3 = ∑ p ∈ s ×ˢ s ×ˢ s, a p.1 * a p.2.1 * a p.2.2 := by
  simp only [Finset.sum_product]
  rw [pow_three, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  ring

/-- **Third moment** (paper Lemma 6.1). -/
theorem moment_le (e Z : ℕ) :
    (∑ n ∈ Finset.range (Z + 1), (g e n) ^ 3) ≤ (Z : ℝ) * (T3 e).toReal := by
  classical
  set ind : ℕ → ℕ → ℝ := fun r n => if e ≤ r ∧ r ∣ n ∧ 1 ≤ n then (1 : ℝ) / r else 0 with hind
  -- (1) `g e n` as a sum over the fixed range with divisor indicators
  have hg : ∀ n ∈ Finset.range (Z + 1), g e n = ∑ r ∈ Finset.range (Z + 1), ind r n := by
    intro n hn
    rw [Finset.mem_range] at hn
    rw [g]
    simp only [hind]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext r
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_range]
    constructor
    · rintro ⟨⟨hdvd, hn0⟩, her⟩
      exact ⟨lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd) hn, her, hdvd,
        Nat.pos_of_ne_zero hn0⟩
    · rintro ⟨_, her, hdvd, h1n⟩
      exact ⟨⟨hdvd, by omega⟩, her⟩
  -- (2) cube + swap to a sum over the triple product, then over `n` innermost
  set R3 := Finset.range (Z + 1) ×ˢ Finset.range (Z + 1) ×ˢ Finset.range (Z + 1) with hR3
  have hswap : (∑ n ∈ Finset.range (Z + 1), (g e n) ^ 3)
      = ∑ p ∈ R3, ∑ n ∈ Finset.range (Z + 1), ind p.1 n * ind p.2.1 n * ind p.2.2 n := by
    rw [Finset.sum_congr rfl (fun n hn => by rw [hg n hn, sum_cube_eq_prod])]
    rw [Finset.sum_comm]
  rw [hswap]
  -- (3) bound each `p`-term by `Z * (third-moment summand)`
  have hpbound : ∀ p ∈ R3,
      (∑ n ∈ Finset.range (Z + 1), ind p.1 n * ind p.2.1 n * ind p.2.2 n)
      ≤ (Z : ℝ) * (if e ≤ p.1 ∧ e ≤ p.2.1 ∧ e ≤ p.2.2 then
          (1 : ℝ) / ((p.1 * p.2.1 * p.2.2 * Nat.lcm p.1 (Nat.lcm p.2.1 p.2.2) : ℕ) : ℝ) else 0) := by
    rintro ⟨r, s, t⟩ _
    by_cases hc : e ≤ r ∧ e ≤ s ∧ e ≤ t
    · -- the indicator product collapses to a single divisibility condition
      have hterm : ∀ n, ind r n * ind s n * ind t n
          = if Nat.lcm r (Nat.lcm s t) ∣ n ∧ 1 ≤ n then (1 : ℝ) / (r * s * t) else 0 := by
        intro n
        simp only [hind]
        by_cases hd : Nat.lcm r (Nat.lcm s t) ∣ n ∧ 1 ≤ n
        · rw [Nat.lcm_dvd_iff, Nat.lcm_dvd_iff] at hd
          rw [if_pos ⟨hc.1, hd.1.1, hd.2⟩, if_pos ⟨hc.2.1, hd.1.2.1, hd.2⟩,
            if_pos ⟨hc.2.2, hd.1.2.2, hd.2⟩, if_pos ?_]
          · push_cast; ring
          · rw [Nat.lcm_dvd_iff, Nat.lcm_dvd_iff]; exact hd
        · rw [if_neg hd]
          rw [Nat.lcm_dvd_iff, Nat.lcm_dvd_iff] at hd
          by_cases h1 : e ≤ r ∧ r ∣ n ∧ 1 ≤ n
          · by_cases h2 : e ≤ s ∧ s ∣ n ∧ 1 ≤ n
            · rw [if_pos h1, if_pos h2,
                if_neg (fun h3 => hd ⟨⟨h1.2.1, h2.2.1, h3.2.1⟩, h1.2.2⟩)]; ring
            · rw [if_pos h1, if_neg h2]; ring
          · rw [if_neg h1]; ring
      rw [Finset.sum_congr rfl (fun n _ => hterm n)]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      rw [if_pos hc]
      have hcount : ((Finset.range (Z + 1)).filter
          (fun n => Nat.lcm r (Nat.lcm s t) ∣ n ∧ 1 ≤ n)).card
          ≤ Z / Nat.lcm r (Nat.lcm s t) := by
        rw [← Nat.card_multiples' Z (Nat.lcm r (Nat.lcm s t))]
        apply Finset.card_le_card
        intro n hn
        rw [Finset.mem_filter] at hn ⊢
        obtain ⟨hr, hd, h1⟩ := hn
        exact ⟨hr, by omega, hd⟩
      have hcountR : (((Finset.range (Z + 1)).filter
          (fun n => Nat.lcm r (Nat.lcm s t) ∣ n ∧ 1 ≤ n)).card : ℝ)
          ≤ (Z : ℝ) / (Nat.lcm r (Nat.lcm s t) : ℝ) := by
        have h1 : (((Finset.range (Z + 1)).filter
            (fun n => Nat.lcm r (Nat.lcm s t) ∣ n ∧ 1 ≤ n)).card : ℝ)
            ≤ ((Z / Nat.lcm r (Nat.lcm s t) : ℕ) : ℝ) := by exact_mod_cast hcount
        exact h1.trans Nat.cast_div_le
      refine le_trans (mul_le_mul_of_nonneg_right hcountR (by positivity)) (le_of_eq ?_)
      push_cast; ring
    · rw [if_neg hc, mul_zero]
      refine le_of_eq (Finset.sum_eq_zero (fun n _ => ?_))
      rcases not_and_or.mp hc with hnr | hnst
      · have h0 : ind r n = 0 := by simp only [hind]; exact if_neg (fun h => hnr h.1)
        rw [h0]; ring
      · rcases not_and_or.mp hnst with hns | hnt
        · have h0 : ind s n = 0 := by simp only [hind]; exact if_neg (fun h => hns h.1)
          rw [h0]; ring
        · have h0 : ind t n = 0 := by simp only [hind]; exact if_neg (fun h => hnt h.1)
          rw [h0]; ring
  -- (4) sum the per-`p` bounds and bridge the finite sum to the `T3` tsum
  calc ∑ p ∈ R3, ∑ n ∈ Finset.range (Z + 1), ind p.1 n * ind p.2.1 n * ind p.2.2 n
      ≤ ∑ p ∈ R3, (Z : ℝ) * (if e ≤ p.1 ∧ e ≤ p.2.1 ∧ e ≤ p.2.2 then
          (1 : ℝ) / ((p.1 * p.2.1 * p.2.2 * Nat.lcm p.1 (Nat.lcm p.2.1 p.2.2) : ℕ) : ℝ) else 0) :=
        Finset.sum_le_sum hpbound
    _ = (Z : ℝ) * ∑ p ∈ R3, (if e ≤ p.1 ∧ e ≤ p.2.1 ∧ e ≤ p.2.2 then
          (1 : ℝ) / ((p.1 * p.2.1 * p.2.2 * Nat.lcm p.1 (Nat.lcm p.2.1 p.2.2) : ℕ) : ℝ) else 0) := by
        rw [Finset.mul_sum]
    _ ≤ (Z : ℝ) * (T3 e).toReal := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← ENNReal.toReal_ofReal (Finset.sum_nonneg (fun p _ => by positivity))]
        refine ENNReal.toReal_mono (T3_lt_top e).ne ?_
        rw [ENNReal.ofReal_sum_of_nonneg (fun p _ => by positivity)]
        calc ∑ p ∈ R3, ENNReal.ofReal (if e ≤ p.1 ∧ e ≤ p.2.1 ∧ e ≤ p.2.2 then
                (1 : ℝ) / ((p.1 * p.2.1 * p.2.2 * Nat.lcm p.1 (Nat.lcm p.2.1 p.2.2) : ℕ) : ℝ) else 0)
            = ∑ p ∈ R3, (if e ≤ p.1 ∧ e ≤ p.2.1 ∧ e ≤ p.2.2 then ENNReal.ofReal
                ((1 : ℝ) / ((p.1 * p.2.1 * p.2.2 * Nat.lcm p.1 (Nat.lcm p.2.1 p.2.2) : ℕ) : ℝ))
                else 0) :=
              Finset.sum_congr rfl (fun p _ => by rw [apply_ite ENNReal.ofReal, ENNReal.ofReal_zero])
          _ ≤ T3 e := by
              rw [T3]
              exact ENNReal.sum_le_tsum R3

open MeasureTheory in
/-- A finite sum of `n^(-5/2)` over `(E, M]` is at most `(2/3)·E^(-3/2)` (integral comparison). -/
lemma rpow_partial_tail_le (E M : ℕ) (hE : 1 ≤ E) :
    ∑ i ∈ Finset.Ico E M, ((i : ℝ) + 1) ^ (-(5 / 2 : ℝ)) ≤ (2 / 3) * (E : ℝ) ^ (-(3 / 2 : ℝ)) := by
  rcases Nat.lt_or_ge M E with hME | hEM
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]; positivity
  have hE0 : (0 : ℝ) < E := by exact_mod_cast hE
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-(5 / 2 : ℝ))) (Set.Icc (E : ℝ) (M : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hE0 hx.1) hxy (by norm_num)
  have hstep := hanti.sum_le_integral_Ico (by exact_mod_cast hEM)
  refine le_trans (by exact_mod_cast hstep) ?_
  rw [integral_rpow (Or.inr ⟨by norm_num, by
    simp only [Set.uIcc_of_le (by exact_mod_cast hEM : (E:ℝ) ≤ M), Set.mem_Icc, not_and, not_le]
    intro h; linarith [hE0]⟩)]
  have hexp : (-(5 / 2 : ℝ) + 1) = -(3 / 2 : ℝ) := by norm_num
  rw [hexp, div_le_iff_of_neg (by norm_num : (-(3 / 2 : ℝ)) < 0)]
  nlinarith [Real.rpow_nonneg hM0.le (-(3 / 2 : ℝ))]

/-- Finset tail: any finite set of integers `> E` has `∑ n^(-5/2) ≤ (2/3)·E^(-3/2)`. -/
lemma rpow_finset_tail_le (E : ℕ) (hE : 1 ≤ E) (T : Finset ℕ) (hT : ∀ n ∈ T, E < n) :
    ∑ n ∈ T, (n : ℝ) ^ (-(5 / 2 : ℝ)) ≤ (2 / 3) * (E : ℝ) ^ (-(3 / 2 : ℝ)) := by
  classical
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
    (t := (Finset.Ico E (T.sup id + 1)).image (· + 1)) (fun n hn => ?_)
    (fun n _ _ => by positivity)) ?_
  · have hn1 : E < n := hT n hn
    have hn2 : n ≤ T.sup id := Finset.le_sup (f := id) hn
    rw [Finset.mem_image]
    exact ⟨n - 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
  · rw [Finset.sum_image (fun a _ b _ h => by omega)]
    refine le_trans (le_of_eq (Finset.sum_congr rfl (fun i _ => ?_))) (rpow_partial_tail_le E _ hE)
    rw [Nat.cast_add, Nat.cast_one]

/-- Single-variable `p`-series in `ℝ≥0∞`: `Sp p = ∑' n, ofReal (n^{-p})`. -/
noncomputable def Sp (p : ℝ) : ℝ≥0∞ := ∑' n : ℕ, ENNReal.ofReal ((n : ℝ) ^ (-p))

/-- For `1 < p`, the `p`-series is finite. -/
lemma Sp_ne_top {p : ℝ} (hp : 1 < p) : Sp p ≠ ⊤ := by
  have hf : ∀ r : ℕ, (0 : ℝ) ≤ (r : ℝ) ^ (-p) := fun r => Real.rpow_nonneg (by positivity) _
  have hsum : Summable (fun r : ℕ => (r : ℝ) ^ (-p)) := by
    have heq : (fun r : ℕ => (r : ℝ) ^ (-p)) = (fun r : ℕ => 1 / (r : ℝ) ^ p) := by
      funext r; rw [Real.rpow_neg (by positivity), one_div]
    rw [heq]; exact (Real.summable_one_div_nat_rpow).mpr hp
  rw [Sp, ← ENNReal.ofReal_tsum_of_nonneg hf hsum]
  exact ENNReal.ofReal_ne_top

/-- The `p`-series is strictly positive (the `n = 1` term is `1`). -/
lemma Sp_pos {p : ℝ} : 0 < Sp p := by
  rw [Sp]
  refine lt_of_lt_of_le ?_ (ENNReal.le_tsum 1)
  rw [Nat.cast_one, Real.one_rpow]
  simp

/-- Two-factor product `tsum` factorization. -/
lemma tsum_mul_prod {α β : Type*} (f : α → ℝ≥0∞) (g : β → ℝ≥0∞) :
    (∑' p : α × β, f p.1 * g p.2) = (∑' a, f a) * (∑' b, g b) := by
  rw [ENNReal.tsum_prod']
  rw [show (∑' (a : α) (b : β), f a * g b) = ∑' (a : α), f a * (∑' b, g b) from
    tsum_congr (fun a => ENNReal.tsum_mul_left)]
  rw [ENNReal.tsum_mul_right]

/-- Factorization of a seven-fold `tsum` into a product of single-variable sums
(right-associated). -/
lemma tsum7 (f₁ f₂ f₃ : ℕ → ℝ≥0∞) :
    (∑' p : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ,
      f₁ p.1 * f₂ p.2.1 * f₂ p.2.2.1 * f₂ p.2.2.2.1 * f₃ p.2.2.2.2.1
        * f₃ p.2.2.2.2.2.1 * f₃ p.2.2.2.2.2.2)
      = (∑' a, f₁ a) * ((∑' a, f₂ a) * ((∑' a, f₂ a) * ((∑' a, f₂ a)
          * ((∑' a, f₃ a) * ((∑' a, f₃ a) * (∑' a, f₃ a)))))) := by
  have e1 : (∑' p : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ,
      f₁ p.1 * f₂ p.2.1 * f₂ p.2.2.1 * f₂ p.2.2.2.1 * f₃ p.2.2.2.2.1
        * f₃ p.2.2.2.2.2.1 * f₃ p.2.2.2.2.2.2)
      = ∑' p : ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ),
        f₁ p.1 * (f₂ p.2.1 * f₂ p.2.2.1 * f₂ p.2.2.2.1 * f₃ p.2.2.2.2.1
          * f₃ p.2.2.2.2.2.1 * f₃ p.2.2.2.2.2.2) := tsum_congr (fun p => by ring)
  have e2 : (∑' q : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ,
      f₂ q.1 * f₂ q.2.1 * f₂ q.2.2.1 * f₃ q.2.2.2.1 * f₃ q.2.2.2.2.1 * f₃ q.2.2.2.2.2)
      = ∑' q : ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ),
        f₂ q.1 * (f₂ q.2.1 * f₂ q.2.2.1 * f₃ q.2.2.2.1 * f₃ q.2.2.2.2.1 * f₃ q.2.2.2.2.2) :=
    tsum_congr (fun q => by ring)
  have e3 : (∑' q : ℕ × ℕ × ℕ × ℕ × ℕ,
      f₂ q.1 * f₂ q.2.1 * f₃ q.2.2.1 * f₃ q.2.2.2.1 * f₃ q.2.2.2.2)
      = ∑' q : ℕ × (ℕ × ℕ × ℕ × ℕ),
        f₂ q.1 * (f₂ q.2.1 * f₃ q.2.2.1 * f₃ q.2.2.2.1 * f₃ q.2.2.2.2) :=
    tsum_congr (fun q => by ring)
  have e4 : (∑' q : ℕ × ℕ × ℕ × ℕ, f₂ q.1 * f₃ q.2.1 * f₃ q.2.2.1 * f₃ q.2.2.2)
      = ∑' q : ℕ × (ℕ × ℕ × ℕ),
        f₂ q.1 * (f₃ q.2.1 * f₃ q.2.2.1 * f₃ q.2.2.2) :=
    tsum_congr (fun q => by ring)
  have e5 : (∑' q : ℕ × ℕ × ℕ, f₃ q.1 * f₃ q.2.1 * f₃ q.2.2)
      = ∑' q : ℕ × (ℕ × ℕ), f₃ q.1 * (f₃ q.2.1 * f₃ q.2.2) :=
    tsum_congr (fun q => by ring)
  rw [e1, tsum_mul_prod f₁ (fun q : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ =>
        f₂ q.1 * f₂ q.2.1 * f₂ q.2.2.1 * f₃ q.2.2.2.1 * f₃ q.2.2.2.2.1 * f₃ q.2.2.2.2.2)]
  rw [e2, tsum_mul_prod f₂ (fun q : ℕ × ℕ × ℕ × ℕ × ℕ =>
        f₂ q.1 * f₂ q.2.1 * f₃ q.2.2.1 * f₃ q.2.2.2.1 * f₃ q.2.2.2.2)]
  rw [e3, tsum_mul_prod f₂ (fun q : ℕ × ℕ × ℕ × ℕ =>
        f₂ q.1 * f₃ q.2.1 * f₃ q.2.2.1 * f₃ q.2.2.2)]
  rw [e4, tsum_mul_prod f₂ (fun q : ℕ × ℕ × ℕ => f₃ q.1 * f₃ q.2.1 * f₃ q.2.2)]
  rw [e5, tsum_mul_prod f₃ (fun q : ℕ × ℕ => f₃ q.1 * f₃ q.2)]
  rw [tsum_mul_prod f₃ f₃]

/-- The gcd-decomposition map `(r,s,t) ↦ (h,u,v,w,R,S,T)` recovering the seven-variable
gcd/lcm structure: `h = gcd(r,s,t)`, `u,v,w` the pairwise extra-gcd parts, `R,S,T` the
coprime remainders. -/
noncomputable def decomp (r s t : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  let h := Nat.gcd r (Nat.gcd s t)
  let u := Nat.gcd r s / h
  let v := Nat.gcd r t / h
  let w := Nat.gcd s t / h
  (h, u, v, w, r / (h * u * v), s / (h * u * w), t / (h * v * w))

/-- **The seven-variable gcd/lcm decomposition** (paper §6.2, the `7 → 3` injection).
For positive `(r,s,t)`, the components `(h,u,v,w,R,S,T) = decomp r s t` satisfy the
multiplicative identities `r = huvR`, `s = huwS`, `t = hvwT`, are all positive, and
recombine to the lcm: `h·u·v·w·R·S·T = lcm r (lcm s t)`.

This is the prime-by-prime/factorization identity at the heart of the bound, proved by
comparing `p`-adic valuations (`min`/`max` of exponents) via `Nat.eq_of_factorization_eq`. -/
lemma decomp_spec {r s t : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    let d := decomp r s t
    1 ≤ d.1 ∧ 1 ≤ d.2.1 ∧ 1 ≤ d.2.2.1 ∧ 1 ≤ d.2.2.2.1 ∧
      1 ≤ d.2.2.2.2.1 ∧ 1 ≤ d.2.2.2.2.2.1 ∧ 1 ≤ d.2.2.2.2.2.2 ∧
      r = d.1 * d.2.1 * d.2.2.1 * d.2.2.2.2.1 ∧
      s = d.1 * d.2.1 * d.2.2.2.1 * d.2.2.2.2.2.1 ∧
      t = d.1 * d.2.2.1 * d.2.2.2.1 * d.2.2.2.2.2.2 ∧
      d.1 * d.2.1 * d.2.2.1 * d.2.2.2.1 * d.2.2.2.2.1 * d.2.2.2.2.2.1 * d.2.2.2.2.2.2
        = Nat.lcm r (Nat.lcm s t) := by
  simp only [decomp]
  have hr0 : r ≠ 0 := by omega
  have hs0 : s ≠ 0 := by omega
  have ht0 : t ≠ 0 := by omega
  have hgw0 : Nat.gcd s t ≠ 0 := by simp only [ne_eq, Nat.gcd_eq_zero_iff]; omega
  have hgu0 : Nat.gcd r s ≠ 0 := by simp only [ne_eq, Nat.gcd_eq_zero_iff]; omega
  have hgv0 : Nat.gcd r t ≠ 0 := by simp only [ne_eq, Nat.gcd_eq_zero_iff]; omega
  set h := Nat.gcd r (Nat.gcd s t) with hh_def
  have hh0 : h ≠ 0 := by rw [hh_def]; simp only [ne_eq, Nat.gcd_eq_zero_iff]; omega
  have hdh_r : h ∣ r := Nat.gcd_dvd_left _ _
  have hdh_gst : h ∣ Nat.gcd s t := Nat.gcd_dvd_right _ _
  have hdh_s : h ∣ s := hdh_gst.trans (Nat.gcd_dvd_left _ _)
  have hdh_t : h ∣ t := hdh_gst.trans (Nat.gcd_dvd_right _ _)
  have hdh_gu : h ∣ Nat.gcd r s := Nat.dvd_gcd hdh_r hdh_s
  have hdh_gv : h ∣ Nat.gcd r t := Nat.dvd_gcd hdh_r hdh_t
  set u := Nat.gcd r s / h with hu_def
  set v := Nat.gcd r t / h with hv_def
  set w := Nat.gcd s t / h with hw_def
  have hu0 : u ≠ 0 := by
    rw [hu_def]
    exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hgu0) hdh_gu)
      (Nat.pos_of_ne_zero hh0)).ne'
  have hv0 : v ≠ 0 := by
    rw [hv_def]
    exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hgv0) hdh_gv)
      (Nat.pos_of_ne_zero hh0)).ne'
  have hw0 : w ≠ 0 := by
    rw [hw_def]
    exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hgw0) hdh_gst)
      (Nat.pos_of_ne_zero hh0)).ne'
  -- per-prime factorizations
  have hfh : ∀ p, h.factorization p
      = min (r.factorization p) (min (s.factorization p) (t.factorization p)) := by
    intro p
    rw [hh_def, Nat.factorization_gcd hr0 hgw0, Finsupp.inf_apply,
      Nat.factorization_gcd hs0 ht0, Finsupp.inf_apply]
  have hfu : ∀ p, u.factorization p = (Nat.gcd r s).factorization p - h.factorization p := by
    intro p; rw [hu_def, Nat.factorization_div hdh_gu, Finsupp.tsub_apply]
  have hfv : ∀ p, v.factorization p = (Nat.gcd r t).factorization p - h.factorization p := by
    intro p; rw [hv_def, Nat.factorization_div hdh_gv, Finsupp.tsub_apply]
  have hfw : ∀ p, w.factorization p = (Nat.gcd s t).factorization p - h.factorization p := by
    intro p; rw [hw_def, Nat.factorization_div hdh_gst, Finsupp.tsub_apply]
  have hfgu : ∀ p, (Nat.gcd r s).factorization p
      = min (r.factorization p) (s.factorization p) := by
    intro p; rw [Nat.factorization_gcd hr0 hs0, Finsupp.inf_apply]
  have hfgv : ∀ p, (Nat.gcd r t).factorization p
      = min (r.factorization p) (t.factorization p) := by
    intro p; rw [Nat.factorization_gcd hr0 ht0, Finsupp.inf_apply]
  have hfgw : ∀ p, (Nat.gcd s t).factorization p
      = min (s.factorization p) (t.factorization p) := by
    intro p; rw [Nat.factorization_gcd hs0 ht0, Finsupp.inf_apply]
  -- the three key divisibilities
  have key_huv : h * u * v ∣ r := by
    rw [← Nat.factorization_le_iff_dvd (mul_ne_zero (mul_ne_zero hh0 hu0) hv0) hr0, Finsupp.le_def]
    intro p
    rw [Nat.factorization_mul (mul_ne_zero hh0 hu0) hv0,
      Nat.factorization_mul hh0 hu0, Finsupp.add_apply, Finsupp.add_apply,
      hfu p, hfv p, hfh p, hfgu p, hfgv p]
    omega
  have key_huw : h * u * w ∣ s := by
    rw [← Nat.factorization_le_iff_dvd (mul_ne_zero (mul_ne_zero hh0 hu0) hw0) hs0, Finsupp.le_def]
    intro p
    rw [Nat.factorization_mul (mul_ne_zero hh0 hu0) hw0,
      Nat.factorization_mul hh0 hu0, Finsupp.add_apply, Finsupp.add_apply,
      hfu p, hfw p, hfh p, hfgu p, hfgw p]
    omega
  have key_hvw : h * v * w ∣ t := by
    rw [← Nat.factorization_le_iff_dvd (mul_ne_zero (mul_ne_zero hh0 hv0) hw0) ht0, Finsupp.le_def]
    intro p
    rw [Nat.factorization_mul (mul_ne_zero hh0 hv0) hw0,
      Nat.factorization_mul hh0 hv0, Finsupp.add_apply, Finsupp.add_apply,
      hfv p, hfw p, hfh p, hfgv p, hfgw p]
    omega
  set R := r / (h * u * v) with hR_def
  set S := s / (h * u * w) with hS_def
  set T := t / (h * v * w) with hT_def
  have hR0 : R ≠ 0 := by
    rw [hR_def]
    exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hr0) key_huv)
      (Nat.pos_of_ne_zero (mul_ne_zero (mul_ne_zero hh0 hu0) hv0))).ne'
  have hS0 : S ≠ 0 := by
    rw [hS_def]
    exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hs0) key_huw)
      (Nat.pos_of_ne_zero (mul_ne_zero (mul_ne_zero hh0 hu0) hw0))).ne'
  have hT0 : T ≠ 0 := by
    rw [hT_def]
    exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ht0) key_hvw)
      (Nat.pos_of_ne_zero (mul_ne_zero (mul_ne_zero hh0 hv0) hw0))).ne'
  -- identities
  have hrid : r = h * u * v * R := by rw [hR_def, Nat.mul_div_cancel' key_huv]
  have hsid : s = h * u * w * S := by rw [hS_def, Nat.mul_div_cancel' key_huw]
  have htid : t = h * v * w * T := by rw [hT_def, Nat.mul_div_cancel' key_hvw]
  -- factorizations of R, S, T
  have hfR : ∀ p, R.factorization p
      = r.factorization p - (h.factorization p + u.factorization p + v.factorization p) := by
    intro p
    rw [hR_def, Nat.factorization_div key_huv, Finsupp.tsub_apply,
      Nat.factorization_mul (mul_ne_zero hh0 hu0) hv0, Nat.factorization_mul hh0 hu0,
      Finsupp.add_apply, Finsupp.add_apply]
  have hfS : ∀ p, S.factorization p
      = s.factorization p - (h.factorization p + u.factorization p + w.factorization p) := by
    intro p
    rw [hS_def, Nat.factorization_div key_huw, Finsupp.tsub_apply,
      Nat.factorization_mul (mul_ne_zero hh0 hu0) hw0, Nat.factorization_mul hh0 hu0,
      Finsupp.add_apply, Finsupp.add_apply]
  have hfT : ∀ p, T.factorization p
      = t.factorization p - (h.factorization p + v.factorization p + w.factorization p) := by
    intro p
    rw [hT_def, Nat.factorization_div key_hvw, Finsupp.tsub_apply,
      Nat.factorization_mul (mul_ne_zero hh0 hv0) hw0, Nat.factorization_mul hh0 hv0,
      Finsupp.add_apply, Finsupp.add_apply]
  -- the lcm identity
  have hlcm : h * u * v * w * R * S * T = Nat.lcm r (Nat.lcm s t) := by
    apply Nat.eq_of_factorization_eq
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        hh0 hu0) hv0) hw0) hR0) hS0) hT0)
      (by simp only [ne_eq, Nat.lcm_eq_zero_iff]; omega)
    intro p
    rw [Nat.factorization_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        hh0 hu0) hv0) hw0) hR0) hS0) hT0,
      Nat.factorization_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        hh0 hu0) hv0) hw0) hR0) hS0,
      Nat.factorization_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero
        hh0 hu0) hv0) hw0) hR0,
      Nat.factorization_mul (mul_ne_zero (mul_ne_zero hh0 hu0) hv0) hw0,
      Nat.factorization_mul (mul_ne_zero hh0 hu0) hv0,
      Nat.factorization_mul hh0 hu0]
    simp only [Finsupp.add_apply]
    rw [hfR p, hfS p, hfT p, hfu p, hfv p, hfw p, hfh p, hfgu p, hfgv p, hfgw p,
      Nat.factorization_lcm hr0 (by simp only [ne_eq, Nat.lcm_eq_zero_iff]; omega),
      Finsupp.sup_apply, Nat.factorization_lcm hs0 ht0, Finsupp.sup_apply]
    omega
  -- positivity in the final shape
  refine ⟨Nat.one_le_iff_ne_zero.mpr hh0, Nat.one_le_iff_ne_zero.mpr hu0,
    Nat.one_le_iff_ne_zero.mpr hv0, Nat.one_le_iff_ne_zero.mpr hw0,
    Nat.one_le_iff_ne_zero.mpr hR0, Nat.one_le_iff_ne_zero.mpr hS0,
    Nat.one_le_iff_ne_zero.mpr hT0, hrid, hsid, htid, hlcm⟩

/-- The pointwise power-saving estimate, given the seven-variable decomposition data. -/
lemma decomp_pointwise {e r s t h u v w R S T : ℕ}
    (he : 1 ≤ e) (hre : e ≤ r) (hse : e ≤ s) (hte : e ≤ t)
    (hh : 1 ≤ h) (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w)
    (hR : 1 ≤ R) (hS : 1 ≤ S) (hT : 1 ≤ T)
    (hrid : r = h * u * v * R) (hsid : s = h * u * w * S) (htid : t = h * v * w * T)
    (hlcm : h * u * v * w * R * S * T = Nat.lcm r (Nat.lcm s t)) :
    (1 : ℝ) / ((r * s * t * Nat.lcm r (Nat.lcm s t) : ℕ) : ℝ)
      ≤ (e : ℝ) ^ (-(5 / 2 : ℝ)) *
          ((h : ℝ) ^ (-(3 / 2 : ℝ)) * (u : ℝ) ^ (-(4 / 3 : ℝ)) * (v : ℝ) ^ (-(4 / 3 : ℝ))
            * (w : ℝ) ^ (-(4 / 3 : ℝ)) * (R : ℝ) ^ (-(7 / 6 : ℝ)) * (S : ℝ) ^ (-(7 / 6 : ℝ))
            * (T : ℝ) ^ (-(7 / 6 : ℝ))) := by
  -- real positivity facts
  have heR : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have hhR : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have huR : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  have hvR : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
  have hwR : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have hRR : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hSR : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
  have hTR : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have he0 : (0 : ℝ) < (e : ℝ) := by linarith
  have hh0 : (0 : ℝ) < (h : ℝ) := by linarith
  have hu0 : (0 : ℝ) < (u : ℝ) := by linarith
  have hv0 : (0 : ℝ) < (v : ℝ) := by linarith
  have hw0 : (0 : ℝ) < (w : ℝ) := by linarith
  have hR0 : (0 : ℝ) < (R : ℝ) := by linarith
  have hS0 : (0 : ℝ) < (S : ℝ) := by linarith
  have hT0 : (0 : ℝ) < (T : ℝ) := by linarith
  -- the lcm is positive
  have hLpos : 0 < Nat.lcm r (Nat.lcm s t) :=
    Nat.pos_of_ne_zero (by simp only [ne_eq, Nat.lcm_eq_zero_iff]; omega)
  have hL0 : (0 : ℝ) < (Nat.lcm r (Nat.lcm s t) : ℝ) := by exact_mod_cast hLpos
  -- `r*s*t = Q := h^3 u^2 v^2 w^2 R S T`
  set Q : ℝ := (h : ℝ) ^ 3 * (u : ℝ) ^ 2 * (v : ℝ) ^ 2 * (w : ℝ) ^ 2 * R * S * T with hQdef
  have hrstQ : (r : ℝ) * s * t = Q := by
    have : (r : ℝ) = (h : ℝ) * u * v * R := by exact_mod_cast hrid
    have hs' : (s : ℝ) = (h : ℝ) * u * w * S := by exact_mod_cast hsid
    have ht' : (t : ℝ) = (h : ℝ) * v * w * T := by exact_mod_cast htid
    rw [this, hs', ht', hQdef]; ring
  -- `e^3 ≤ r*s*t = Q`
  have hrste3 : (e : ℝ) ^ 3 ≤ Q := by
    rw [← hrstQ]
    have : (e : ℝ) ^ 3 = (e : ℝ) * e * e := by ring
    rw [this]
    have h1 : (e : ℝ) * e ≤ (r : ℝ) * s := by
      apply mul_le_mul (by exact_mod_cast hre) (by exact_mod_cast hse) he0.le
      linarith [(by exact_mod_cast hre : (e:ℝ) ≤ r)]
    apply mul_le_mul h1 (by exact_mod_cast hte) he0.le
    nlinarith [(by exact_mod_cast hre : (e:ℝ) ≤ r), (by exact_mod_cast hse : (e:ℝ) ≤ s)]
  -- `G := h^4 u^3 v^3 w^3 R^2 S^2 T^2 ≤ r*s*t*lcm`
  set G : ℝ := (h : ℝ) ^ 4 * (u : ℝ) ^ 3 * (v : ℝ) ^ 3 * (w : ℝ) ^ 3
      * (R : ℝ) ^ 2 * (S : ℝ) ^ 2 * (T : ℝ) ^ 2 with hGdef
  have hLeq : (Nat.lcm r (Nat.lcm s t) : ℝ)
      = (h : ℝ) * u * v * w * R * S * T := by
    have : ((h * u * v * w * R * S * T : ℕ) : ℝ) = (Nat.lcm r (Nat.lcm s t) : ℝ) := by
      exact_mod_cast hlcm
    rw [← this]; push_cast; ring
  have hGle : G ≤ (r : ℝ) * s * t * (Nat.lcm r (Nat.lcm s t) : ℝ) := by
    rw [hrstQ, hLeq, hGdef, hQdef]; apply le_of_eq; ring
  -- `B := e^{5/2}·P_pos`, the denominator we compare against; `B ≤ G`
  set Ppos : ℝ := (h : ℝ) ^ (3 / 2 : ℝ) * (u : ℝ) ^ (4 / 3 : ℝ) * (v : ℝ) ^ (4 / 3 : ℝ)
      * (w : ℝ) ^ (4 / 3 : ℝ) * (R : ℝ) ^ (7 / 6 : ℝ) * (S : ℝ) ^ (7 / 6 : ℝ)
      * (T : ℝ) ^ (7 / 6 : ℝ) with hPposdef
  set B : ℝ := (e : ℝ) ^ (5 / 2 : ℝ) * Ppos with hBdef
  have hBpos : 0 < B := by
    rw [hBdef, hPposdef]; positivity
  -- `M := e^15 h^9 u^8 v^8 w^8 R^7 S^7 T^7` (all natural powers), and `B = M^{1/6}`
  set M : ℝ := (e : ℝ) ^ 15 * (h : ℝ) ^ 9 * (u : ℝ) ^ 8 * (v : ℝ) ^ 8 * (w : ℝ) ^ 8
      * (R : ℝ) ^ 7 * (S : ℝ) ^ 7 * (T : ℝ) ^ 7 with hMdef
  have hsixth : ∀ (x : ℝ) (k : ℕ) (c : ℝ), 0 ≤ x → (k : ℝ) * (1 / 6) = c →
      (x ^ k) ^ (1 / 6 : ℝ) = x ^ c := by
    intro x k c hx hc
    rw [← Real.rpow_natCast x k, ← Real.rpow_mul hx, hc]
  have hBM : B = M ^ (1 / 6 : ℝ) := by
    rw [hMdef]
    rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity)]
    rw [hsixth _ 15 (5 / 2) he0.le (by norm_num), hsixth _ 9 (3 / 2) hh0.le (by norm_num),
        hsixth _ 8 (4 / 3) hu0.le (by norm_num), hsixth _ 8 (4 / 3) hv0.le (by norm_num),
        hsixth _ 8 (4 / 3) hw0.le (by norm_num), hsixth _ 7 (7 / 6) hR0.le (by norm_num),
        hsixth _ 7 (7 / 6) hS0.le (by norm_num), hsixth _ 7 (7 / 6) hT0.le (by norm_num)]
    rw [hBdef, hPposdef]; ring
  -- `M ≤ G^6`, hence `B = M^{1/6} ≤ (G^6)^{1/6} = G`
  have hMG : M ≤ G ^ 6 := by
    have hK : (0 : ℝ) ≤ (h : ℝ) ^ 9 * (u : ℝ) ^ 8 * (v : ℝ) ^ 8 * (w : ℝ) ^ 8
        * (R : ℝ) ^ 7 * (S : ℝ) ^ 7 * (T : ℝ) ^ 7 := by positivity
    have hMK : M = (e : ℝ) ^ 15 * ((h : ℝ) ^ 9 * (u : ℝ) ^ 8 * (v : ℝ) ^ 8 * (w : ℝ) ^ 8
        * (R : ℝ) ^ 7 * (S : ℝ) ^ 7 * (T : ℝ) ^ 7) := by rw [hMdef]; ring
    have hG6K : G ^ 6 = Q ^ 5 * ((h : ℝ) ^ 9 * (u : ℝ) ^ 8 * (v : ℝ) ^ 8 * (w : ℝ) ^ 8
        * (R : ℝ) ^ 7 * (S : ℝ) ^ 7 * (T : ℝ) ^ 7) := by rw [hGdef, hQdef]; ring
    rw [hMK, hG6K]
    refine mul_le_mul_of_nonneg_right ?_ hK
    calc (e : ℝ) ^ 15 = ((e : ℝ) ^ 3) ^ 5 := by ring
      _ ≤ Q ^ 5 := pow_le_pow_left₀ (by positivity) hrste3 5
  have hG0 : (0 : ℝ) ≤ G := by rw [hGdef]; positivity
  have hBG : B ≤ G := by
    rw [hBM]
    calc M ^ (1 / 6 : ℝ) ≤ (G ^ 6) ^ (1 / 6 : ℝ) :=
          Real.rpow_le_rpow (by rw [hMdef]; positivity) hMG (by norm_num)
      _ = G := by rw [hsixth _ 6 (1 : ℝ) hG0 (by norm_num), Real.rpow_one]
  -- chain: `B ≤ G ≤ r*s*t*lcm`, so `1/(r*s*t*lcm) ≤ 1/B`
  have hBD : B ≤ (r : ℝ) * s * t * (Nat.lcm r (Nat.lcm s t) : ℝ) := le_trans hBG hGle
  have hDpos : (0 : ℝ) < (r : ℝ) * s * t * (Nat.lcm r (Nat.lcm s t) : ℝ) := by
    have hr0 : (0:ℝ) < r := by exact_mod_cast (by omega : 0 < r)
    have hs0 : (0:ℝ) < s := by exact_mod_cast (by omega : 0 < s)
    have ht0 : (0:ℝ) < t := by exact_mod_cast (by omega : 0 < t)
    positivity
  -- the target RHS equals `1/B`
  have hRHS : (e : ℝ) ^ (-(5 / 2 : ℝ)) *
      ((h : ℝ) ^ (-(3 / 2 : ℝ)) * (u : ℝ) ^ (-(4 / 3 : ℝ)) * (v : ℝ) ^ (-(4 / 3 : ℝ))
        * (w : ℝ) ^ (-(4 / 3 : ℝ)) * (R : ℝ) ^ (-(7 / 6 : ℝ)) * (S : ℝ) ^ (-(7 / 6 : ℝ))
        * (T : ℝ) ^ (-(7 / 6 : ℝ))) = 1 / B := by
    rw [hBdef, hPposdef]
    rw [Real.rpow_neg he0.le, Real.rpow_neg hh0.le, Real.rpow_neg hu0.le, Real.rpow_neg hv0.le,
        Real.rpow_neg hw0.le, Real.rpow_neg hR0.le, Real.rpow_neg hS0.le, Real.rpow_neg hT0.le]
    ring
  rw [hRHS]
  -- finally compare reciprocals
  have hcast : ((r * s * t * Nat.lcm r (Nat.lcm s t) : ℕ) : ℝ)
      = (r : ℝ) * s * t * (Nat.lcm r (Nat.lcm s t) : ℝ) := by push_cast; ring
  rw [hcast]
  exact one_div_le_one_div_of_le hBpos hBD

/-- **Power-saving tail** (paper Lemma 6.2, first part). -/
theorem T3_power_saving :
    ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ e : ℕ, 1 ≤ e → (T3 e).toReal ≤ C₃ * (e : ℝ) ^ (-(5 / 2 : ℝ)) := by
  classical
  -- single-variable summands and the (e-independent) finite constant
  set g₁ : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal ((n : ℝ) ^ (-(3 / 2 : ℝ))) with hg1
  set g₂ : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal ((n : ℝ) ^ (-(4 / 3 : ℝ))) with hg2
  set g₃ : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal ((n : ℝ) ^ (-(7 / 6 : ℝ))) with hg3
  have hS1 : (∑' n, g₁ n) = Sp (3 / 2) := rfl
  have hS2 : (∑' n, g₂ n) = Sp (4 / 3) := rfl
  have hS3 : (∑' n, g₃ n) = Sp (7 / 6) := rfl
  set Cen : ℝ≥0∞ := Sp (3 / 2) * Sp (4 / 3) * Sp (4 / 3) * Sp (4 / 3)
      * Sp (7 / 6) * Sp (7 / 6) * Sp (7 / 6) with hCen
  have hCtop : Cen ≠ ⊤ := by
    rw [hCen]
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ?_) ?_) ?_) ?_) ?_) ?_
    all_goals first
      | exact Sp_ne_top (by norm_num)
  have hCpos : 0 < Cen := by
    rw [hCen, pos_iff_ne_zero]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_)
      ?_) ?_) ?_) ?_
    all_goals exact Sp_pos.ne'
  refine ⟨Cen.toReal, ENNReal.toReal_pos hCpos.ne' hCtop, fun e he => ?_⟩
  -- the bound function on seven-tuples
  set b : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ → ℝ≥0∞ := fun d =>
    ENNReal.ofReal ((e : ℝ) ^ (-(5 / 2 : ℝ))) *
      (g₁ d.1 * g₂ d.2.1 * g₂ d.2.2.1 * g₂ d.2.2.2.1 * g₃ d.2.2.2.2.1
        * g₃ d.2.2.2.2.2.1 * g₃ d.2.2.2.2.2.2) with hb
  -- restrict `T3` to the constrained subtype
  set Sset : Set (ℕ × ℕ × ℕ) := {p | e ≤ p.1 ∧ e ≤ p.2.1 ∧ e ≤ p.2.2} with hSset
  set fS : ℕ × ℕ × ℕ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (1 / ((p.1 * p.2.1 * p.2.2 * Nat.lcm p.1 (Nat.lcm p.2.1 p.2.2) : ℕ) : ℝ))
    with hfS
  have hT3eq : T3 e = ∑' p : Sset, fS p := by
    have h1 : T3 e = ∑' x : ℕ × ℕ × ℕ, Sset.indicator fS x := by
      rw [T3]
      refine tsum_congr (fun p => ?_)
      rw [Set.indicator_apply]
      simp only [hSset, hfS, Set.mem_setOf_eq]
    rw [h1]; exact (tsum_subtype Sset fS).symm
  -- the injection from the subtype to seven-tuples
  set F : Sset → ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ := fun p => decomp p.1.1 p.1.2.1 p.1.2.2 with hF
  have hFinj : Function.Injective F := by
    intro a c hac
    have ha := a.2; have hc' := c.2
    simp only [hSset, Set.mem_setOf_eq] at ha hc'
    obtain ⟨har, has, hat⟩ := ha
    obtain ⟨hcr, hcs, hct⟩ := hc'
    have spa := decomp_spec (r := a.1.1) (s := a.1.2.1) (t := a.1.2.2)
      (by omega) (by omega) (by omega)
    have spc := decomp_spec (r := c.1.1) (s := c.1.2.1) (t := c.1.2.2)
      (by omega) (by omega) (by omega)
    simp only at spa spc
    obtain ⟨_, _, _, _, _, _, _, hra, hsa, hta, _⟩ := spa
    obtain ⟨_, _, _, _, _, _, _, hrc, hsc, htc, _⟩ := spc
    simp only [hF] at hac
    -- recompose both sides from the (equal) decompositions
    apply Subtype.ext
    apply Prod.ext
    · rw [hra, hrc, hac]
    apply Prod.ext
    · rw [hsa, hsc, hac]
    · rw [hta, htc, hac]
  -- pointwise bound on the subtype: `fS p ≤ b (F p)`
  have hpt : ∀ p : Sset, fS p ≤ b (F p) := by
    rintro p
    have hp := p.2
    simp only [hSset, Set.mem_setOf_eq] at hp
    obtain ⟨hpr, hps, hpt'⟩ := hp
    have sp := decomp_spec (r := p.1.1) (s := p.1.2.1) (t := p.1.2.2)
      (by omega) (by omega) (by omega)
    simp only at sp
    obtain ⟨hh, hu, hv, hw, hRR, hSS, hTT, hrid, hsid, htid, hlcm⟩ := sp
    have hpw := decomp_pointwise (e := e) (r := p.1.1) (s := p.1.2.1) (t := p.1.2.2)
      (h := (decomp p.1.1 p.1.2.1 p.1.2.2).1)
      (u := (decomp p.1.1 p.1.2.1 p.1.2.2).2.1)
      (v := (decomp p.1.1 p.1.2.1 p.1.2.2).2.2.1)
      (w := (decomp p.1.1 p.1.2.1 p.1.2.2).2.2.2.1)
      (R := (decomp p.1.1 p.1.2.1 p.1.2.2).2.2.2.2.1)
      (S := (decomp p.1.1 p.1.2.1 p.1.2.2).2.2.2.2.2.1)
      (T := (decomp p.1.1 p.1.2.1 p.1.2.2).2.2.2.2.2.2)
      he hpr hps hpt' hh hu hv hw hRR hSS hTT hrid hsid htid hlcm
    simp only [hfS, hF, hb, hg1, hg2, hg3]
    refine le_trans (ENNReal.ofReal_le_ofReal hpw) (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by positivity)]
  -- assemble
  rw [hT3eq]
  have hchain : (∑' p : Sset, fS p) ≤ ENNReal.ofReal ((e : ℝ) ^ (-(5 / 2 : ℝ))) * Cen := by
    calc (∑' p : Sset, fS p) ≤ ∑' p : Sset, b (F p) := ENNReal.tsum_le_tsum hpt
      _ ≤ ∑' d, b d := ENNReal.tsum_comp_le_tsum_of_injective hFinj b
      _ = ENNReal.ofReal ((e : ℝ) ^ (-(5 / 2 : ℝ))) *
            (∑' d : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ,
              g₁ d.1 * g₂ d.2.1 * g₂ d.2.2.1 * g₂ d.2.2.2.1 * g₃ d.2.2.2.2.1
                * g₃ d.2.2.2.2.2.1 * g₃ d.2.2.2.2.2.2) := by
            simp only [hb]; rw [← ENNReal.tsum_mul_left]
      _ = ENNReal.ofReal ((e : ℝ) ^ (-(5 / 2 : ℝ))) * Cen := by
            rw [tsum7 g₁ g₂ g₃, hS1, hS2, hS3, hCen]; ring
  refine le_trans (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCtop) hchain) ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  exact le_of_eq (mul_comm _ _)

/-- **Tail sum** (paper Lemma 6.2, second part). -/
theorem T3_tail_sum :
    ∃ C₄ : ℝ, 0 < C₄ ∧ ∀ E : ℕ, 1 ≤ E →
      (∑' e : {e : ℕ // E < e}, (T3 (e : ℕ)).toReal) ≤ C₄ * (E : ℝ) ^ (-(3 / 2 : ℝ)) := by
  classical
  obtain ⟨C₃, hC₃pos, hC₃⟩ := T3_power_saving
  refine ⟨2 / 3 * C₃, by positivity, fun E hE => ?_⟩
  refine Real.tsum_le_of_sum_le (fun e => ENNReal.toReal_nonneg) (fun s => ?_)
  calc ∑ e ∈ s, (T3 (e : ℕ)).toReal
      ≤ ∑ e ∈ s, C₃ * (e : ℝ) ^ (-(5 / 2 : ℝ)) := Finset.sum_le_sum (fun e _ => hC₃ e (by omega))
    _ = C₃ * ∑ n ∈ s.image Subtype.val, (n : ℝ) ^ (-(5 / 2 : ℝ)) := by
        rw [Finset.mul_sum, Finset.sum_image (fun a _ b _ h => Subtype.ext h)]
    _ ≤ C₃ * (2 / 3 * (E : ℝ) ^ (-(3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (rpow_finset_tail_le E hE _ (fun n hn => by
          obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hn; exact e.2)) hC₃pos.le
    _ = 2 / 3 * C₃ * (E : ℝ) ^ (-(3 / 2 : ℝ)) := by ring

/-- `H_{A,E}` membership: a representation with cofactor `> E` and modulus `≤ A·N`.
The `1 ≤ d` ensures `N = F e d ≥ 1` (the degenerate `d = 0`, `N = 0` is excluded). -/
def Hset (A : ℝ) (E : ℕ) (N : ℕ) : Prop :=
  ∃ e d, E < e ∧ 1 ≤ d ∧ N = F e d ∧ (e * d : ℝ) ≤ A * N

/-- Finite version of the `T3` tail: a finite set of cofactors `> E` sums to `≤ C₄·E^(-3/2)`. -/
lemma T3_finset_tail_le {C₄ : ℝ}
    (htail : ∀ E : ℕ, 1 ≤ E →
      (∑' e : {e : ℕ // E < e}, (T3 (e : ℕ)).toReal) ≤ C₄ * (E : ℝ) ^ (-(3 / 2 : ℝ)))
    (hsumm : ∀ E : ℕ, Summable (fun e : {e : ℕ // E < e} => (T3 (e : ℕ)).toReal))
    (E : ℕ) (hE : 1 ≤ E) (s : Finset ℕ) (hs : ∀ e ∈ s, E < e) :
    ∑ e ∈ s, (T3 e).toReal ≤ C₄ * (E : ℝ) ^ (-(3 / 2 : ℝ)) := by
  set f : ℕ → ℝ := {e : ℕ | E < e}.indicator (fun e => (T3 e).toReal) with hfdef
  have hind : Summable f := summable_subtype_iff_indicator.mp (hsumm E)
  have heq : ∑ e ∈ s, (T3 e).toReal = ∑ e ∈ s, f e :=
    Finset.sum_congr rfl (fun e he => by
      rw [hfdef, Set.indicator_of_mem (show e ∈ {e : ℕ | E < e} from hs e he)])
  rw [heq]
  refine le_trans (Summable.sum_le_tsum s (fun e _ => ?_) hind) ?_
  · exact Set.indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) e
  · rw [hfdef, ← _root_.tsum_subtype]; exact htail E hE

/-- **Large-cofactor bound** (paper Prop 6.3). Counts **pairs** `(m,e)` (not values `N`): the
inner `∑_{e>E}` carries the multiplicity from `reflection`, `moment_le`, and `T3_tail_sum`. -/
theorem large_e_bound :
    ∃ C₅ : ℝ, 0 < C₅ ∧ ∀ (A : ℝ), 1 ≤ A → ∀ E : ℕ, 1 ≤ E → ∀ X : ℕ,
      (countUpTo (Hset A E) X : ℝ) ≤ C₅ * A ^ 4 * (E : ℝ) ^ (-(3 / 2 : ℝ)) * X := by
  classical
  obtain ⟨C₄, hC₄pos, hC₄⟩ := T3_tail_sum
  obtain ⟨C₃, hC₃pos, hC₃⟩ := T3_power_saving
  have hsumm : ∀ E : ℕ, Summable (fun e : {e : ℕ // E < e} => (T3 (e : ℕ)).toReal) := fun E =>
    Summable.of_nonneg_of_le (fun e => ENNReal.toReal_nonneg) (fun e => hC₃ e (by omega))
      (((Real.summable_nat_rpow.mpr (by norm_num : (-(5 / 2 : ℝ)) < -1)).subtype _).mul_left C₃)
  refine ⟨C₄, hC₄pos, fun A hA E hE X => ?_⟩
  have hA0 : (0 : ℝ) < A := by linarith
  set M := ⌊A * (X : ℝ)⌋₊ with hMdef
  set pairs := (Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter
    (fun p => p.2 ∣ p.1 ∧ E < p.2 ∧ (1 : ℝ) / A ≤ g p.2 p.1) with hpairs
  -- Step 1: `countUpTo (Hset A E) X ≤ pairs.card` via `(m,e) ↦ F e (m/e)`
  have hstep1 : (countUpTo (Hset A E) X : ℝ) ≤ (pairs.card : ℝ) := by
    have hsub : setUpTo (Hset A E) X ⊆ ↑(pairs.image (fun p => F p.2 (p.1 / p.2))) := by
      rintro N ⟨hNX, e, d, hEe, hd1, hN, hle⟩
      have he1 : 1 ≤ e := by omega
      have hgN : (N : ℝ) = ((e * d : ℕ) : ℝ) * g e (e * d) := by
        rw [hN]; exact_mod_cast reflection e d he1 hd1
      have hgpos : (1 : ℝ) / A ≤ g e (e * d) := by
        have hmpos : (0 : ℝ) < ((e * d : ℕ) : ℝ) := by positivity
        have hgnn : 0 ≤ g e (e * d) := by
          rw [g]; exact Finset.sum_nonneg (fun r _ => by positivity)
        have hcast : ((e * d : ℕ) : ℝ) ≤ A * N := by exact_mod_cast hle
        rw [hgN] at hcast
        rw [div_le_iff₀ hA0]; nlinarith [hcast, hmpos, hgnn]
      have hmle : e * d ≤ M := by
        rw [hMdef]; apply Nat.le_floor
        calc ((e * d : ℕ) : ℝ) ≤ A * N := by exact_mod_cast hle
          _ ≤ A * X := by
              apply mul_le_mul_of_nonneg_left _ hA0.le; exact_mod_cast hNX
      have hele : e ≤ M := le_trans (Nat.le_mul_of_pos_right e (by omega : 0 < d)) hmle
      rw [Finset.coe_image, Set.mem_image]
      refine ⟨(e * d, e), ?_, ?_⟩
      · rw [Finset.mem_coe, hpairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
          Finset.mem_range]
        exact ⟨⟨by omega, by omega⟩, dvd_mul_right e d, hEe, hgpos⟩
      · simp only [Nat.mul_div_cancel_left d (by omega : 0 < e)]; exact hN.symm
    calc (countUpTo (Hset A E) X : ℝ)
        ≤ ((pairs.image (fun p => F p.2 (p.1 / p.2))).card : ℝ) := by
          rw [countUpTo]
          exact_mod_cast le_trans (Set.ncard_le_ncard hsub (Finset.finite_toSet _))
            (le_of_eq (Set.ncard_coe_finset _))
      _ ≤ (pairs.card : ℝ) := by exact_mod_cast Finset.card_image_le
  -- Step 2: `pairs.card ≤ A³ · ∑ g³ ≤ A³ · M · C₄ E^{-3/2}`
  have hstep2 : (pairs.card : ℝ) ≤ A ^ 3 * (M * (C₄ * (E : ℝ) ^ (-(3 / 2 : ℝ)))) := by
    have hmarkov : (pairs.card : ℝ) ≤ A ^ 3 * ∑ p ∈ pairs, (g p.2 p.1) ^ 3 := by
      rw [Finset.mul_sum, Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_le_sum (fun p hp => ?_)
      rw [hpairs, Finset.mem_filter] at hp
      have h1 : (1 : ℝ) ≤ A * g p.2 p.1 := by
        have := (div_le_iff₀ hA0).mp hp.2.2.2; linarith [this]
      calc ((1 : ℕ) : ℝ) = 1 := by norm_num
        _ ≤ (A * g p.2 p.1) ^ 3 := one_le_pow₀ h1
        _ = A ^ 3 * (g p.2 p.1) ^ 3 := by rw [mul_pow]
    refine le_trans hmarkov (mul_le_mul_of_nonneg_left ?_ (by positivity))
    -- `∑_{pairs} g³ ≤ M · C₄ E^{-3/2}`
    have hreorg : ∑ p ∈ pairs, (g p.2 p.1) ^ 3
        ≤ ∑ e ∈ (Finset.range (M + 1)).filter (E < ·), ∑ m ∈ Finset.range (M + 1), (g e m) ^ 3 := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
        (t := Finset.range (M + 1) ×ˢ ((Finset.range (M + 1)).filter (E < ·)))
        (fun p hp => ?_)
        (fun i _ _ => pow_nonneg (by rw [g]; exact Finset.sum_nonneg fun r _ => by positivity) 3))
        (le_of_eq ?_)
      · simp only [hpairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
        simp only [Finset.mem_product, Finset.mem_range, Finset.mem_filter]
        exact ⟨hp.1.1, hp.1.2, hp.2.2.1⟩
      · rw [Finset.sum_product, Finset.sum_comm]
    refine le_trans hreorg ?_
    calc ∑ e ∈ (Finset.range (M + 1)).filter (E < ·), ∑ m ∈ Finset.range (M + 1), (g e m) ^ 3
        ≤ ∑ e ∈ (Finset.range (M + 1)).filter (E < ·), (M : ℝ) * (T3 e).toReal :=
          Finset.sum_le_sum (fun e _ => moment_le e M)
      _ = (M : ℝ) * ∑ e ∈ (Finset.range (M + 1)).filter (E < ·), (T3 e).toReal := by
          rw [Finset.mul_sum]
      _ ≤ (M : ℝ) * (C₄ * (E : ℝ) ^ (-(3 / 2 : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact T3_finset_tail_le hC₄ hsumm E hE _ (fun e he => (Finset.mem_filter.mp he).2)
  -- combine
  refine le_trans hstep1 (le_trans hstep2 ?_)
  have hMle : (M : ℝ) ≤ A * X := by rw [hMdef]; exact Nat.floor_le (by positivity)
  have hT3nn : (0 : ℝ) ≤ C₄ * (E : ℝ) ^ (-(3 / 2 : ℝ)) := by positivity
  rw [show C₄ * A ^ 4 * (E : ℝ) ^ (-(3 / 2 : ℝ)) * X = A ^ 3 * ((A * X) * (C₄ * (E : ℝ) ^ (-(3 / 2 : ℝ)))) by ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_right hMle hT3nn



/-! ## Section 7 -- Almost every odd integer is represented (Lem 7.1; uses A3 -- see the N \ {2,5} note at top). -/


/-- The divisors of a product of two distinct primes. -/
lemma divisors_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (p * q).divisors = {1, p, q, p * q} := by
  rw [Nat.divisors_mul, hp.divisors, hq.divisors]
  ext x
  simp only [Finset.mem_mul, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp
  · rintro (h | h | h | h)
    · exact ⟨1, by simp, 1, by simp, by simp [h]⟩
    · exact ⟨p, by simp, 1, by simp, by simp [h]⟩
    · exact ⟨1, by simp, q, by simp, by simp [h]⟩
    · exact ⟨p, by simp, q, by simp, by simp [h]⟩

/-- For distinct primes `p < q`, `F p q = 1 + p + q` (divisors of `pq` that are `≤ q`
are `1, p, q`). -/
lemma F_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    F p q = 1 + p + q := by
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := hq.two_le
  have hqlt : q < p * q := by
    calc q < 2 * q := by omega
      _ ≤ p * q := by gcongr
  have hfilter : ({1, p, q, p * q} : Finset ℕ).filter (· ≤ q) = {1, p, q} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h, hle⟩
      rcases h with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · omega
    · rintro (rfl | rfl | rfl)
      · exact ⟨Or.inl rfl, by omega⟩
      · exact ⟨Or.inr (Or.inl rfl), by omega⟩
      · exact ⟨Or.inr (Or.inr (Or.inl rfl)), le_rfl⟩
  have h1 : (1 : ℕ) ∉ ({p, q} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h2 : p ∉ ({q} : Finset ℕ) := by
    simp only [Finset.mem_singleton]; omega
  rw [F, divisors_two_primes hp hq (by omega), hfilter, Finset.sum_insert h1,
    Finset.sum_insert h2, Finset.sum_singleton]
  omega

open Topology in
/-- The prime counting function is `o(n)` (Chebyshev's upper bound). -/
lemma primeCounting_isLittleO :
    (fun n : ℕ => (Nat.primeCounting n : ℝ)) =o[Filter.atTop] (fun n : ℕ => (n : ℝ)) := by
  rw [Asymptotics.isLittleO_iff_tendsto']
  · have hsqrt : Filter.Tendsto (fun n : ℕ => Real.sqrt n) Filter.atTop Filter.atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have hlogsqrt : Filter.Tendsto (fun n : ℕ => Real.log (Real.sqrt n))
        Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp hsqrt
    have hU : Filter.Tendsto
        (fun n : ℕ => Real.log 4 / Real.log (Real.sqrt n) + 1 / Real.sqrt n)
        Filter.atTop (𝓝 0) := by
      have h1 := Filter.Tendsto.div_atTop (tendsto_const_nhds (x := Real.log 4)) hlogsqrt
      have h2 := Filter.Tendsto.div_atTop (tendsto_const_nhds (x := (1 : ℝ))) hsqrt
      simpa using h1.add h2
    refine squeeze_zero' (Filter.Eventually.of_forall fun n => by positivity) ?_ hU
    filter_upwards [Filter.eventually_gt_atTop 1] with n hn
    have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by positivity
    have hpi := Chebyshev.pi_le_log4_mul_div hn1
    rw [Nat.floor_natCast] at hpi
    rw [div_le_iff₀ hnpos]
    calc (Nat.primeCounting n : ℝ)
        ≤ Real.log 4 * n / Real.log (Real.sqrt n) + Real.sqrt n := hpi
      _ = (Real.log 4 / Real.log (Real.sqrt n) + 1 / Real.sqrt n) * n := by
          rw [add_mul, div_mul_eq_mul_div, one_div, inv_mul_eq_div, Real.div_sqrt]
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn h
    exact absurd h (Nat.cast_pos.mpr hn).ne'

/-- Shifting a predicate by `-1` changes the count by at most `1`. -/
lemma countUpTo_pred_le (Q : ℕ → Prop) (X : ℕ) :
    countUpTo (fun N => Q (N - 1)) X ≤ countUpTo Q X + 1 := by
  unfold countUpTo
  have hsub : setUpTo (fun N => Q (N - 1)) X ⊆ insert 0 (Nat.succ '' setUpTo Q X) := by
    rintro N ⟨hNX, hQ⟩
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨N - 1, ⟨by omega, hQ⟩, by omega⟩
  calc (setUpTo (fun N => Q (N - 1)) X).ncard
      ≤ (insert 0 (Nat.succ '' setUpTo Q X)).ncard :=
        Set.ncard_le_ncard hsub ((Set.Finite.image _ (setUpTo_finite Q X)).insert 0)
    _ ≤ (Nat.succ '' setUpTo Q X).ncard + 1 := Set.ncard_insert_le _ _
    _ = (setUpTo Q X).ncard + 1 := by
        rw [Set.ncard_image_of_injective _ Nat.succ_injective]

/-- A density-zero predicate stays density-zero after a `-1` shift. -/
lemma CountIsLittleO.pred {Q : ℕ → Prop} (hQ : CountIsLittleO Q) :
    CountIsLittleO (fun N => Q (N - 1)) := by
  have hconst : (fun (_ : ℕ) => (1 : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)) := by
    apply Asymptotics.isLittleO_const_left.2
    right
    refine tendsto_atTop_mono (fun X => ?_) tendsto_natCast_atTop_atTop
    show (X : ℝ) ≤ ‖(X : ℝ)‖
    rw [Real.norm_eq_abs]; exact le_abs_self _
  have hbound : (fun X : ℕ => (countUpTo (fun N => Q (N - 1)) X : ℝ)) =O[Filter.atTop]
      (fun X : ℕ => (countUpTo Q X : ℝ) + 1) := by
    refine Asymptotics.isBigO_of_le Filter.atTop (fun X => ?_)
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    have hle : (countUpTo (fun N => Q (N - 1)) X : ℝ) ≤ (countUpTo Q X : ℝ) + 1 := by
      exact_mod_cast countUpTo_pred_le Q X
    linarith [hle]
  exact hbound.trans_isLittleO (hQ.add hconst)

/-- `#{n ≤ X : n prime}` is the prime counting function. -/
lemma countUpTo_prime_eq (X : ℕ) : countUpTo Nat.Prime X = Nat.primeCounting X := by
  rw [countUpTo, Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range,
    ← Set.ncard_coe_finset]
  congr 1
  ext n
  simp only [setUpTo, Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_range, Nat.lt_succ_iff]

/-- The integers `2p+1` (`p` prime) up to `X` inject into the primes up to `X`. -/
lemma countTwoP1_le_prime (X : ℕ) :
    countUpTo (fun N => ∃ p, p.Prime ∧ N = 2 * p + 1) X ≤ countUpTo Nat.Prime X := by
  unfold countUpTo
  refine Set.ncard_le_ncard_of_injOn (fun N => (N - 1) / 2) ?_ ?_ (setUpTo_finite _ X)
  · rintro N ⟨hNX, p, hp, rfl⟩
    simp only [setUpTo, Set.mem_setOf_eq]
    have hpe : (2 * p + 1 - 1) / 2 = p := by omega
    rw [hpe]
    exact ⟨by omega, hp⟩
  · rintro N ⟨hNX, p, hp, rfl⟩ M ⟨hMX, q, hq, rfl⟩ h
    simp only [] at h
    omega

/-- The set `{2p+1 : p prime}` has density zero. -/
lemma twoP1_littleO : CountIsLittleO (fun N => ∃ p, p.Prime ∧ N = 2 * p + 1) := by
  have hP : CountIsLittleO Nat.Prime := by
    have heq : (fun X : ℕ => (countUpTo Nat.Prime X : ℝ))
        = (fun X => (Nat.primeCounting X : ℝ)) := by
      funext X; rw [countUpTo_prime_eq]
    rw [CountIsLittleO, heq]; exact primeCounting_isLittleO
  have hbound : (fun X : ℕ => (countUpTo (fun N => ∃ p, p.Prime ∧ N = 2 * p + 1) X : ℝ))
      =O[Filter.atTop] (fun X : ℕ => (countUpTo Nat.Prime X : ℝ)) := by
    refine Asymptotics.isBigO_of_le Filter.atTop (fun X => ?_)
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    exact_mod_cast countTwoP1_le_prime X
  exact hbound.trans_isLittleO hP

/-- **Almost every odd integer is represented** (paper Lemma 7.1). -/
theorem odd_represented (hDeep : DeepInputs) :
    CountIsLittleO (fun N => Odd N ∧ N ∉ R) := by
  refine CountIsLittleO.mono ?_ ((hDeep.goldbach_ae.pred).or twoP1_littleO)
  rintro N ⟨hodd, hNR⟩
  obtain ⟨k, hk⟩ := hodd
  by_cases hg : ∃ p q, p.Prime ∧ q.Prime ∧ N - 1 = p + q
  · obtain ⟨p, q, hp, hq, hpq⟩ := hg
    rcases eq_or_ne p q with rfl | hne
    · exact Or.inr ⟨p, hp, by omega⟩
    · exfalso
      apply hNR
      rw [mem_R_iff_exists_F]
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact ⟨p, q, hp.pos, hq.pos, by rw [F_two_primes hp hq hlt]; omega⟩
      · exact ⟨q, p, hq.pos, hp.pos, by rw [F_two_primes hq hp hgt]; omega⟩
  · exact Or.inl ⟨⟨k, by omega⟩, hg⟩



/-! ## Section 8 -- Main theorem (Thm 1.1): positive lower density of N in R with f(N) > A*N; hence limsup f(N)/N is infinite. -/


/-- **Main theorem** (paper Theorem 1.1): for each `A ≥ 1`, the set of represented `N`
with `f N > A·N` has positive lower density. -/
theorem main (hDeep : DeepInputs) (A : ℝ) (hA : 1 ≤ A) :
    ∃ c : ℝ, 0 < c ∧
      c ≤ lowerDensity (fun N => N ∈ R ∧ (A * N : ℝ) < (f N : ℝ)) := by
  obtain ⟨c₁, hc₁pos, hsift⟩ := sift_density_lb
  obtain ⟨C₅, hC₅pos, hlarge⟩ := large_e_bound
  obtain ⟨E, hE2, hEchoice⟩ :
      ∃ E : ℕ, 2 ≤ E ∧ C₅ * A ^ 4 * (E : ℝ) ^ (-(3 / 2 : ℝ)) ≤ δ E / 4 := by
    set K : ℝ := 16 * (2 : ℝ) ^ (1 / 4 : ℝ) * (C₅ * A ^ 4) with hK
    have htend : Tendsto (fun E : ℕ => K * (E : ℝ) ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) := by
      have h2 : Tendsto (fun E : ℕ => (E : ℝ) ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
      simpa using h2.const_mul K
    obtain ⟨E, hKlt, hE2⟩ :=
      ((htend.eventually (Iio_mem_nhds hc₁pos)).and (eventually_ge_atTop 2)).exists
    refine ⟨E, hE2, ?_⟩
    have hE0 : (0 : ℝ) < E := by exact_mod_cast (by omega : 0 < E)
    have hlog0 : (0 : ℝ) < Real.log (2 * E) := by
      apply Real.log_pos
      have h2E : (2 : ℝ) ≤ E := by exact_mod_cast hE2
      linarith
    -- log(2E) ≤ 4 (2E)^{1/4}
    have hlog : Real.log (2 * E) ≤ 4 * (2 * (E : ℝ)) ^ (1 / 4 : ℝ) := by
      have h := Real.log_le_rpow_div (x := 2 * (E : ℝ)) (by positivity) (show (0 : ℝ) < 1 / 4 by norm_num)
      have h4 : (2 * (E : ℝ)) ^ (1 / 4 : ℝ) / (1 / 4) = 4 * (2 * (E : ℝ)) ^ (1 / 4 : ℝ) := by ring
      rw [h4] at h; exact h
    -- the rpow identity `E^{-1/2} · (2E)^{1/4} = 2^{1/4} · E^{-1/4}`
    have hrpow : (E : ℝ) ^ (-(1 / 2 : ℝ)) * (2 * (E : ℝ)) ^ (1 / 4 : ℝ)
        = (2 : ℝ) ^ (1 / 4 : ℝ) * (E : ℝ) ^ (-(1 / 4 : ℝ)) := by
      rw [Real.mul_rpow (by norm_num) hE0.le,
        show (E : ℝ) ^ (-(1 / 2 : ℝ)) * ((2 : ℝ) ^ (1 / 4 : ℝ) * (E : ℝ) ^ (1 / 4 : ℝ))
          = (2 : ℝ) ^ (1 / 4 : ℝ) * ((E : ℝ) ^ (-(1 / 2 : ℝ)) * (E : ℝ) ^ (1 / 4 : ℝ)) by ring,
        ← Real.rpow_add hE0, show (-(1 / 2 : ℝ) + 1 / 4) = -(1 / 4 : ℝ) by norm_num]
    -- key bound: `4 C₅A⁴ E^{-1/2} log(2E) ≤ K E^{-1/4} < c₁`
    have hkey : 4 * (C₅ * A ^ 4) * (E : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log (2 * E) ≤ c₁ := by
      have hle : 4 * (C₅ * A ^ 4) * (E : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log (2 * E)
          ≤ K * (E : ℝ) ^ (-(1 / 4 : ℝ)) := by
        calc 4 * (C₅ * A ^ 4) * (E : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log (2 * E)
            ≤ 4 * (C₅ * A ^ 4) * (E : ℝ) ^ (-(1 / 2 : ℝ)) * (4 * (2 * (E : ℝ)) ^ (1 / 4 : ℝ)) := by
              apply mul_le_mul_of_nonneg_left hlog (by positivity)
          _ = K * (E : ℝ) ^ (-(1 / 4 : ℝ)) := by
              have hcollect : 4 * (C₅ * A ^ 4) * (E : ℝ) ^ (-(1 / 2 : ℝ)) *
                    (4 * (2 * (E : ℝ)) ^ (1 / 4 : ℝ))
                  = 16 * (C₅ * A ^ 4) *
                    ((E : ℝ) ^ (-(1 / 2 : ℝ)) * (2 * (E : ℝ)) ^ (1 / 4 : ℝ)) := by ring
              rw [hcollect, hrpow, hK]; ring
      linarith [hle, hKlt]
    -- convert `hkey` into the modulus inequality, then use `hsift`
    have hElog2 : (0 : ℝ) < 4 * (E : ℝ) * Real.log (2 * E) := by positivity
    have hstep : C₅ * A ^ 4 * (E : ℝ) ^ (-(3 / 2 : ℝ)) ≤ c₁ / (4 * (E : ℝ) * Real.log (2 * E)) := by
      rw [le_div_iff₀ hElog2]
      calc C₅ * A ^ 4 * (E : ℝ) ^ (-(3 / 2 : ℝ)) * (4 * (E : ℝ) * Real.log (2 * E))
          = 4 * (C₅ * A ^ 4) * ((E : ℝ) ^ (-(3 / 2 : ℝ)) * (E : ℝ)) * Real.log (2 * E) := by ring
        _ = 4 * (C₅ * A ^ 4) * (E : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log (2 * E) := by
            have hEE : (E : ℝ) ^ (-(3 / 2 : ℝ)) * (E : ℝ) = (E : ℝ) ^ (-(1 / 2 : ℝ)) := by
              have h := (Real.rpow_add hE0 (-(3 / 2 : ℝ)) 1).symm
              rw [Real.rpow_one] at h
              rw [h, show (-(3 / 2 : ℝ) + 1) = -(1 / 2 : ℝ) by norm_num]
            rw [hEE]
        _ ≤ c₁ := hkey
    refine le_trans hstep ?_
    rw [show 4 * (E : ℝ) * Real.log (2 * E) = ((E : ℝ) * Real.log (2 * E)) * 4 by ring, ← div_div]
    exact (div_le_div_iff_of_pos_right (by norm_num)).2 (hsift E hE2)
  -- `δ E > 0`
  have hElog : (0 : ℝ) < (E : ℝ) * Real.log (2 * E) := by
    have h1 : (0 : ℝ) < (E : ℝ) := by exact_mod_cast (by omega : 0 < E)
    have h2 : (0 : ℝ) < Real.log (2 * E) := by
      apply Real.log_pos
      have : (2 : ℝ) ≤ E := by exact_mod_cast hE2
      linarith
    positivity
  have hδpos : 0 < δ E := lt_of_lt_of_le (div_pos hc₁pos hElog) (hsift E hE2)
  refine ⟨δ E / 2, by positivity, ?_⟩
  -- coprime to `Q_E` ⟹ odd
  have hodd : ∀ N, Nat.Coprime N (Qpr E) → Odd N := by
    intro N hN
    rcases Nat.even_or_odd N with he | ho
    · have hgcd : Nat.gcd N (Qpr E) = 1 := hN
      have : (2 : ℕ) ∣ 1 := hgcd ▸ Nat.dvd_gcd he.two_dvd (two_dvd_Qpr E hE2)
      exact absurd this (by decide)
    · exact ho
  -- density chain: start at `δ E`, remove the two `o(X)` sets, then the `≤ δ E/4` set
  have step0 : δ E ≤ lowerDensity (fun N => Nat.Coprime N (Qpr E)) := sift_lowerDensity E hE2
  have step1 : δ E ≤ lowerDensity
      (fun N => Nat.Coprime N (Qpr E) ∧
        ¬ (Nat.Coprime N (Qpr E) ∧ ∃ e d, 1 ≤ e ∧ e ≤ E ∧ N = F e d)) :=
    lowerDensity_and_not step0 (small_e_exclusion E hE2)
  have hB1 : CountIsLittleO (fun N => Nat.Coprime N (Qpr E) ∧ N ∉ R) :=
    CountIsLittleO.mono (fun N hN => ⟨hodd N hN.1, hN.2⟩) (odd_represented hDeep)
  have step2 : δ E ≤ lowerDensity
      (fun N => (Nat.Coprime N (Qpr E) ∧
          ¬ (Nat.Coprime N (Qpr E) ∧ ∃ e d, 1 ≤ e ∧ e ≤ E ∧ N = F e d)) ∧
        ¬ (Nat.Coprime N (Qpr E) ∧ N ∉ R)) :=
    lowerDensity_and_not step1 hB1
  have hHbound : ∀ X : ℕ, (countUpTo (Hset A E) X : ℝ) ≤ δ E / 4 * X := by
    intro X
    calc (countUpTo (Hset A E) X : ℝ)
        ≤ C₅ * A ^ 4 * (E : ℝ) ^ (-(3 / 2 : ℝ)) * X := hlarge A hA E (by omega) X
      _ ≤ δ E / 4 * X := mul_le_mul_of_nonneg_right hEchoice (by positivity)
  have step3 : δ E - δ E / 4 ≤ lowerDensity
      (fun N => ((Nat.Coprime N (Qpr E) ∧
          ¬ (Nat.Coprime N (Qpr E) ∧ ∃ e d, 1 ≤ e ∧ e ≤ E ∧ N = F e d)) ∧
        ¬ (Nat.Coprime N (Qpr E) ∧ N ∉ R)) ∧ ¬ Hset A E N) :=
    lowerDensity_and_not_le hHbound step2
  -- survivors satisfy `N ∈ R` and `f N > A·N`
  have hmono : ∀ N, (((Nat.Coprime N (Qpr E) ∧
          ¬ (Nat.Coprime N (Qpr E) ∧ ∃ e d, 1 ≤ e ∧ e ≤ E ∧ N = F e d)) ∧
        ¬ (Nat.Coprime N (Qpr E) ∧ N ∉ R)) ∧ ¬ Hset A E N) →
      N ∈ R ∧ (A * N : ℝ) < (f N : ℝ) := by
    intro N hgood
    obtain ⟨⟨⟨hQc, hnsmall⟩, hnunrep⟩, hnHset⟩ := hgood
    have hNR : N ∈ R := by
      by_contra hNR; exact hnunrep ⟨hQc, hNR⟩
    refine ⟨hNR, ?_⟩
    by_contra hle
    rw [not_lt] at hle
    obtain ⟨e, d, he, hd, hfeq, hNF⟩ := f_mem_Fform N hNR
    by_cases heE : e ≤ E
    · exact hnsmall ⟨hQc, e, d, he, heE, hNF⟩
    · rw [not_le] at heE
      refine hnHset ⟨e, d, heE, hd, hNF, ?_⟩
      have hcast : (e : ℝ) * d = (f N : ℝ) := by rw [← Nat.cast_mul, ← hfeq]
      rw [hcast]; exact hle
  calc δ E / 2
      ≤ δ E - δ E / 4 := by linarith
    _ ≤ lowerDensity
        (fun N => ((Nat.Coprime N (Qpr E) ∧
            ¬ (Nat.Coprime N (Qpr E) ∧ ∃ e d, 1 ≤ e ∧ e ≤ E ∧ N = F e d)) ∧
          ¬ (Nat.Coprime N (Qpr E) ∧ N ∉ R)) ∧ ¬ Hset A E N) := step3
    _ ≤ lowerDensity (fun N => N ∈ R ∧ (A * N : ℝ) < (f N : ℝ)) := lowerDensity_mono hmono

/-- **Unbounded ratio** (paper Theorem 1.1, limsup form): for every `A` there is a
represented `N` with `f N / N > A`. -/
theorem ratio_unbounded (hDeep : DeepInputs) (A : ℝ) :
    ∃ N : ℕ, N ∈ R ∧ A < (f N : ℝ) / (N : ℝ) := by
  obtain ⟨c, hcpos, hc⟩ := main hDeep (max A 1) (le_max_right A 1)
  -- positivity of the lower density forces the set to be nonempty
  have hne : ∃ N, N ∈ R ∧ (max A 1 * (N : ℝ)) < (f N : ℝ) := by
    by_contra h
    push_neg at h
    have hc0 : ∀ X, countUpTo (fun N => N ∈ R ∧ (max A 1 * (N : ℝ)) < (f N : ℝ)) X = 0 := by
      intro X
      have hemp : setUpTo (fun N => N ∈ R ∧ (max A 1 * (N : ℝ)) < (f N : ℝ)) X = ∅ :=
        Set.eq_empty_iff_forall_notMem.2 (fun n hn => absurd hn.2.2 (not_lt.2 (h n hn.2.1)))
      unfold countUpTo
      rw [hemp, Set.ncard_empty]
    have hzero : lowerDensity (fun N => N ∈ R ∧ (max A 1 * (N : ℝ)) < (f N : ℝ)) = 0 := by
      rw [lowerDensity]
      simp only [hc0, Nat.cast_zero, zero_div]
      exact liminf_const 0
    rw [hzero] at hc
    linarith
  obtain ⟨N, hNR, hN⟩ := hne
  refine ⟨N, hNR, ?_⟩
  -- represented integers are `≥ 1`
  have hN1 : 1 ≤ N := by
    obtain ⟨e, d, he, hd, hNeq⟩ := (mem_R_iff_exists_F N).1 hNR
    rw [hNeq, F]
    have hdmem : d ∈ (e * d).divisors.filter (· ≤ d) := by
      rw [Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨dvd_mul_left d e, (Nat.mul_pos (by omega) (by omega)).ne'⟩, le_refl d⟩
    calc 1 ≤ d := hd
      _ ≤ ∑ q ∈ (e * d).divisors.filter (· ≤ d), q :=
          Finset.single_le_sum (fun i _ => Nat.zero_le i) hdmem
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [lt_div_iff₀ hNpos]
  calc A * N ≤ max A 1 * N := by gcongr; exact le_max_left A 1
    _ < (f N : ℝ) := hN

end Represented
