module

public import Unconditional1054

@[expose] public section


/-!
# Subtype-restricted limsup and unrepresented exceptions for Erdős #1054

Proves that the extended-real ratio $f(n)/n$ has infinite $\limsup$ when
restricted to the subtype of *every* natural-density-one set $S \subseteq \mathbb{N}$,
characterizes the support $\{n : 0 < f(n)\} = R$, and establishes the two
unrepresented base cases $f(2) = 0$ and $f(5) = 0$.
-/

open Filter Asymptotics
open scoped Topology

namespace Erdos1054.StatementAudit

/-- The two official textbook proofs use this elementary lemma from
`FormalConjecturesForMathlib`. Reprove its Apache-2.0 argument locally so no
conjectural official module enters the trusted import closure. -/
lemma nth_divisors_zero {n : ℕ} (hn : n ≠ 0) :
    Nat.nth (fun d => d ∈ n.divisors) 0 = 1 := by
  rw [Nat.nth_zero]
  exact IsLeast.csInf_eq
    ⟨Nat.one_mem_divisors.mpr hn, fun y hy => Nat.pos_of_mem_divisors hy⟩

/-- The second official textbook helper, independently rebuilt from its
Apache-2.0 `FormalConjecturesForMathlib` proof. -/
lemma two_le_nth_divisors {n : ℕ} (hn : n ≠ 0) {i : ℕ}
    (hi : i ≠ 0) (h : Nat.nth (fun d => d ∈ n.divisors) i ≠ 0) :
    2 ≤ Nat.nth (fun d => d ∈ n.divisors) i := by
  have hfinite : (Set.ofPred (fun d => d ∈ n.divisors)).Finite :=
    Set.finite_mem_finset n.divisors
  have hpositive : 1 ≤ Nat.nth (fun d => d ∈ n.divisors) i :=
    Nat.pos_of_mem_divisors (Nat.nth_mem_of_ne_zero h)
  rcases hpositive.lt_or_eq with htwo | hone
  · omega
  · exact absurd
      (Nat.nth_injOn hfinite
        (Set.mem_Iio.mpr (Nat.lt_card_toFinset_of_nth_ne_zero h hfinite))
        (Set.mem_Iio.mpr (Nat.lt_card_toFinset_of_nth_ne_zero
          (show Nat.nth (fun d => d ∈ n.divisors) 0 ≠ 0 by
            rw [nth_divisors_zero hn]
            omega)
          hfinite))
        (by rw [nth_divisors_zero hn]; omega)) hi

/-- The official junk value is positive exactly when its argument is genuinely
represented; neither an undefined positive integer nor zero can fake a witness. -/
theorem official_f_pos_iff_represented (n : ℕ) :
    0 < _root_.Erdos1054.OriginalNth.f n ↔ n ∈ _root_.Represented.R := by
  rw [_root_.Erdos1054.OriginalNth.f_eq_supported]
  constructor
  · intro hpositive
    by_contra hnot
    have hempty :
        {m : ℕ | 1 ≤ m ∧ _root_.Represented.IsRep n m} = ∅ := by
      ext m
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hm
      exact hnot ⟨m, hm⟩
    unfold _root_.Represented.f at hpositive
    rw [hempty] at hpositive
    simp at hpositive
  · intro hrepresented
    obtain ⟨e, d, he, hd, hminimum, _⟩ :=
      _root_.Represented.f_mem_Fform n hrepresented
    rw [hminimum]
    exact Nat.mul_pos he hd

/-- Zero is exactly the official sentinel for nonrepresentation, including
the degenerate zero-modulus witness at the integer zero itself. -/
theorem official_f_zero_iff_not_represented (n : ℕ) :
    _root_.Erdos1054.OriginalNth.f n = 0 ↔ n ∉ _root_.Represented.R := by
  rw [← official_f_pos_iff_represented]
  omega

/-- The first named exception in the authenticated official statement also
holds for its clean recreation, without importing that statement's conjectural
declarations.  This proof adapts the official Apache-2.0 textbook proof. -/
theorem official_f_undefined_at_two :
    _root_.Erdos1054.OriginalNth.f 2 = 0 := by
  rw [_root_.Erdos1054.OriginalNth.f, dite_eq_right]
  rintro ⟨m, k, hk, hsum⟩
  change 2 = ∑ i ∈ Finset.Iio k,
    Nat.nth (fun d => d ∈ m.divisors) i at hsum
  rcases eq_or_ne m 0 with rfl | hm
  · simp at hsum
  · have hk0 : (0 : ℕ) ∈ Finset.Iio k :=
      Finset.mem_Iio.mpr (by omega)
    rw [← Finset.add_sum_erase _ _ hk0,
      nth_divisors_zero hm] at hsum
    obtain ⟨i, hi_mem, hi_ne⟩ :=
      Finset.exists_ne_zero_of_sum_ne_zero
        (s := (Finset.Iio k).erase 0)
        (f := Nat.nth (fun d => d ∈ m.divisors)) (by omega)
    have htwo := two_le_nth_divisors hm
      (Finset.ne_of_mem_erase hi_mem) hi_ne
    have := htwo.trans
      (Finset.single_le_sum (fun j _ => Nat.zero_le _) hi_mem)
    omega

/-- The second named official exception is five (the upstream declaration is
misleadingly named `f_undefined_at_3`).  This independently replays its
Apache-2.0 textbook argument without the conjectural upstream imports. -/
theorem official_f_undefined_at_five :
    _root_.Erdos1054.OriginalNth.f 5 = 0 := by
  rw [_root_.Erdos1054.OriginalNth.f, dite_eq_right]
  rintro ⟨m, k, hk, hsum⟩
  change 5 = ∑ i ∈ Finset.Iio k,
    Nat.nth (fun d => d ∈ m.divisors) i at hsum
  rcases eq_or_ne m 0 with rfl | hm
  · simp at hsum
  · set p : ℕ → Prop := fun x => x ∈ m.divisors with hpdef
    change 5 = ∑ i ∈ Finset.Iio k, Nat.nth p i at hsum
    have hfinite : (Set.ofPred p).Finite := Set.finite_mem_finset m.divisors
    have hfirst : Nat.nth p 0 = 1 := nth_divisors_zero hm
    have hlower : ∀ j, j < hfinite.toFinset.card → j + 1 ≤ Nat.nth p j := by
      intro j
      induction j with
      | zero => intro _; omega
      | succ n ih =>
        intro hj
        have hstrict := Nat.nth_lt_nth_of_lt_card hfinite
          (show n < n + 1 by omega)
          (show n + 1 < hfinite.toFinset.card by omega)
        have hprevious := ih (by omega)
        omega
    have hnotfour : Nat.nth p 1 ≠ 4 := by
      intro hfour
      have hnonzero : Nat.nth p 1 ≠ 0 := by rw [hfour]; norm_num
      have hcard : 1 < hfinite.toFinset.card := by
        by_contra hnot
        push Not at hnot
        exact hnonzero (Nat.nth_eq_zero.mpr (Or.inr ⟨hfinite, hnot⟩))
      have hmember : p (Nat.nth p 1) :=
        Nat.nth_mem_of_lt_card hfinite hcard
      rw [hfour] at hmember
      have hfourdiv : (4 : ℕ) ∣ m := (Nat.mem_divisors.mp hmember).1
      have htwodiv : (2 : ℕ) ∣ m := dvd_trans (by norm_num) hfourdiv
      have htwomember : p 2 := by
        simp [hpdef, Nat.mem_divisors, htwodiv, hm]
      have hcount : Nat.count p 2 = 1 := by
        simp [hpdef, Nat.count_succ, Nat.count_zero, Nat.mem_divisors, hm]
      have hindex := Nat.nth_count (p := p) htwomember
      rw [hcount, hfour] at hindex
      norm_num at hindex
    rcases lt_or_ge k 3 with hshort | hlong
    · interval_cases k
      · rw [Nat.Iio_eq_range, Finset.sum_range_one, hfirst] at hsum
        omega
      · rw [Nat.Iio_eq_range, Finset.sum_range_succ,
          Finset.sum_range_one, hfirst] at hsum
        exact hnotfour (by omega)
    · rcases eq_or_ne (Nat.nth p 2) 0 with hthird | hthird
      · have hzero : ∀ i, 2 ≤ i → Nat.nth p i = 0 := by
          rcases Nat.nth_eq_zero.mp hthird with ⟨hzero, _⟩ | ⟨hfinite', hcard⟩
          · exact absurd hzero (by simp [hpdef, Nat.mem_divisors])
          · intro i hi
            refine Nat.nth_eq_zero.mpr (Or.inr ⟨hfinite, ?_⟩)
            have hequal : hfinite'.toFinset.card = hfinite.toFinset.card := by
              congr 1
            omega
        rw [← Finset.sum_subset (s₁ := Finset.Iio 2)
          (s₂ := Finset.Iio k)] at hsum
        · rw [Nat.Iio_eq_range, Finset.sum_range_succ,
            Finset.sum_range_one, hfirst] at hsum
          exact hnotfour (by omega)
        · intro x hx
          simp only [Finset.mem_Iio] at *
          omega
        · intro x hx hx2
          simp only [Finset.mem_Iio] at *
          exact hzero x (by omega)
      · have hcard : 2 < hfinite.toFinset.card := by
          by_contra hnot
          push Not at hnot
          exact hthird (Nat.nth_eq_zero.mpr (Or.inr ⟨hfinite, hnot⟩))
        have hsecond := hlower 1 (by omega)
        have hthird' := hlower 2 (by omega)
        have hsubset :
            ∑ i ∈ Finset.Iio 3, Nat.nth p i ≤
              ∑ i ∈ Finset.Iio k, Nat.nth p i := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            simp only [Finset.mem_Iio] at *
            omega
          · intros
            positivity
        rw [Nat.Iio_eq_range, Finset.sum_range_succ,
          Finset.sum_range_succ, Finset.sum_range_one, hfirst] at hsubset
        omega

/-- Positive lower density at every real threshold survives restriction to
any density-one set; every surviving witness is genuinely represented. -/
theorem positive_lower_density_on_density_one
    (S : Set ℕ) (hS : _root_.Erdos1054.HasDensityOne S)
    (A : ℝ) (hA : 1 ≤ A) :
    _root_.Erdos1054.PositiveLowerDensity
      (fun n : ℕ => n ∈ S ∧ n ∈ _root_.Represented.R ∧
        A * (n : ℝ) < (_root_.Erdos1054.OriginalNth.f n : ℝ)) := by
  classical
  obtain ⟨c, hc, hlarge⟩ :=
    _root_.Represented.main
      (_root_.Erdos1054.goldbach_of_matching_density
        _root_.Erdos1054.Unconditional.almost_all_binary_goldbach)
      A hA
  have hremaining :
      c ≤ _root_.Represented.lowerDensity
        (fun n : ℕ =>
          (n ∈ _root_.Represented.R ∧
            A * (n : ℝ) < (_root_.Represented.f n : ℝ)) ∧
            ¬ n ∉ S) :=
    _root_.Represented.lowerDensity_and_not hlarge
      (_root_.Erdos1054.densityOne_complement_littleO hS)
  apply _root_.Erdos1054.positiveLowerDensity_mono
    (P := fun n : ℕ =>
      (n ∈ _root_.Represented.R ∧
        A * (n : ℝ) < (_root_.Represented.f n : ℝ)) ∧ ¬ n ∉ S)
  · intro n hn
    refine ⟨Classical.byContradiction hn.2, hn.1.1, ?_⟩
    simpa only [_root_.Erdos1054.OriginalNth.f_eq_supported] using hn.1.2
  · exact _root_.Erdos1054.lowerDensity_to_positiveLowerDensity _
      ⟨c, hc, hremaining⟩

/-- The positive-density witnesses are arbitrarily late in the actual
density-one subtype, not merely among unrestricted natural numbers. -/
theorem frequently_on_density_one
    (S : Set ℕ) (hS : _root_.Erdos1054.HasDensityOne S)
    (A : ℝ) (hA : 1 ≤ A) :
    ∃ᶠ n : S in atTop,
      (n : ℕ) ∈ _root_.Represented.R ∧
        A * ((n : ℕ) : ℝ) <
          (_root_.Erdos1054.OriginalNth.f (n : ℕ) : ℝ) := by
  classical
  obtain ⟨a, ha⟩ := _root_.Erdos1054.densityOne_nonempty hS
  let : Nonempty S := ⟨⟨a, ha⟩⟩
  have hfrequent := _root_.Erdos1054.positiveLowerDensity_frequently
    (positive_lower_density_on_density_one S hS A hA)
  rw [frequently_atTop]
  intro n
  obtain ⟨m, hnm, hmS, hm⟩ :=
    frequently_atTop.mp hfrequent (n : ℕ)
  exact ⟨⟨m, hmS⟩, hnm, hm⟩

/-- The genuine density-one-subsequence strengthening of the official third
question: *every* density-one subtype has infinite extended-real limsup. -/
theorem limsup_on_every_density_one
    (S : Set ℕ) (hS : _root_.Erdos1054.HasDensityOne S) :
    (atTop : Filter S).limsup
      (fun n : S =>
        (_root_.Erdos1054.OriginalNth.f (n : ℕ) : EReal) /
          (n : ℕ)) = ⊤ := by
  classical
  obtain ⟨a₀, ha₀⟩ := _root_.Erdos1054.densityOne_nonempty hS
  let : Nonempty S := ⟨⟨a₀, ha₀⟩⟩
  apply top_unique
  apply (le_limsup_iff).2
  intro y hy
  obtain ⟨a, hya, _⟩ := EReal.exists_between_coe_real hy
  let A : ℝ := max a 1
  have haA : a ≤ A := le_max_left a 1
  have hA : 1 ≤ A := le_max_right a 1
  have hfrequent := frequently_on_density_one S hS A hA
  refine hfrequent.mono (fun n hn => ?_)
  have hnpositive : (0 : ℝ) < ((n : ℕ) : ℝ) := by
    exact_mod_cast _root_.Erdos1054.represented_pos
      ((_root_.Erdos1054.represented_iff_memR (n : ℕ)).mpr hn.1)
  have hratio : A <
      (_root_.Erdos1054.OriginalNth.f (n : ℕ) : ℝ) /
        ((n : ℕ) : ℝ) :=
    (lt_div_iff₀ hnpositive).mpr hn.2
  calc
    y < (a : EReal) := hya
    _ < (((_root_.Erdos1054.OriginalNth.f (n : ℕ) : ℝ) /
      ((n : ℕ) : ℝ) : ℝ) : EReal) :=
      EReal.coe_lt_coe_iff.mpr (haA.trans_lt hratio)
    _ = (_root_.Erdos1054.OriginalNth.f (n : ℕ) : EReal) /
      (n : ℕ) := by
      rw [EReal.coe_div]
      rfl

end Erdos1054.StatementAudit
