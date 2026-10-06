module

public import CycleNoCopyBase
public import CycleDeletionPalette
public import CycleWeakCombined
public import CycleBlockArithmetic

@[expose] public section

/-!
Strong-induction upper bound for the anti-Ramsey number of `cycleGraph k`
(`k ≥ 4`), parameterized by the high-new-color weak-block decomposition
property `HighNewWeakStructure k` (proved for `k = 4` in
`CycleFourHighNewStructure` and for `k ≥ 5` in
`CycleOriginalHighNewStructureV5`).
-/

namespace ErdosProblems.AntiRamseyConditionalCycleUpper

open Finset SimpleGraph
open ErdosProblems.AntiRamseyCycleBase
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyWeakCount
open ErdosProblems.AntiRamseyCycleBlockCount
open ErdosProblems.AntiRamseyTriangle

/-- The exact real coefficient in the cycle part of Erdős #1105. -/
noncomputable def cycleSlope (k : ℕ) : ℝ :=
  ((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)

/-- Choi's Lemma 3.2.3 weak-block decomposition property for `C_k`-free host
colorings in which every vertex has at least two private ("NEW") colors and
every pair of distinct vertices has at least `k - 1` private colors in total. -/
def HighNewWeakStructure (k : ℕ) : Prop :=
  ∀ {n q : ℕ} (_hn : k ≤ n)
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (_hfree : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    (_hnew : ∀ v : Fin n, 2 ≤ (newColors χ v).card)
    (_hpair : ∀ x y : Fin n, x ≠ y →
      k - 1 ≤ (newColors χ x).card + (newColors χ y).card),
    ∃ (t : ℕ) (b : Fin n → Fin t)
      (ψ : TopEdgeLabeling (Fin t) (Fin q)),
      1 ≤ t ∧
      (∀ (a d : Fin n) (had : a ≠ d) (hbd : b a ≠ b d),
        χ.get a d had = ψ.get (b a) (b d) hbd) ∧
      NoRainbowTriangle ψ ∧
      (∀ i : Fin t, 1 ≤ (blockFiber b i).card) ∧
      (∀ i : Fin t, (blockFiber b i).card ≤ k - 1) ∧
      (∑ i : Fin t, (blockFiber b i).card = n)

theorem cycleSlope_nonneg (k : ℕ) (hk : 4 ≤ k) :
    0 ≤ cycleSlope k := by
  have hkreal : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hden : 0 < (k : ℝ) - 1 := by linarith
  have hrec : 0 ≤ 1 / ((k : ℝ) - 1) :=
    le_of_lt (one_div_pos.mpr hden)
  unfold cycleSlope
  linarith

theorem new_le_cycleSlope_of_low (k a : ℕ) (hk : 4 ≤ k)
    (ha : a ≤ (k - 2) / 2) : (a : ℝ) ≤ cycleSlope k := by
  have hnat : 2 * a ≤ k - 2 := by
    have hdiv := Nat.div_mul_le_self (k - 2) 2
    omega
  have hreal : (2 : ℝ) * (a : ℝ) ≤ ((k - 2 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  rw [Nat.cast_sub (by omega : 2 ≤ k)] at hreal
  have hkreal : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hden : 0 < (k : ℝ) - 1 := by linarith
  have hrec : 0 ≤ 1 / ((k : ℝ) - 1) :=
    le_of_lt (one_div_pos.mpr hden)
  have hreal' : (2 : ℝ) * (a : ℝ) ≤ (k : ℝ) - 2 := by
    simpa only [Nat.cast_ofNat] using hreal
  have hhalf : (a : ℝ) ≤ ((k : ℝ) - 2) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    simpa only [mul_comm] using hreal'
  unfold cycleSlope
  exact le_trans hhalf (le_add_of_nonneg_right hrec)

theorem cycleSlope_base_identity (k : ℕ) (hk : 4 ≤ k) :
    cycleSlope k * ((k - 1 : ℕ) : ℝ) =
      (((k - 1).choose 2 : ℕ) : ℝ) + 1 := by
  unfold cycleSlope
  rw [cycle_coefficient_eq_block_coefficient k (by omega)]
  exact full_block_coefficient (k - 1) (by omega)

/-- Under the one explicit high-new-color structure premise, every
surjective palette avoiding a rainbow `C_k` has the claimed upper count.
The first induction state is `n = k - 1`, not `n = k`. -/
theorem admissible_palette_le_cycle_linear (k n : ℕ) (hk : 4 ≤ k)
    (hn : k - 1 ≤ n) (hstructure : HighNewWeakStructure k)
    {q : ℕ} (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ)
    (hfree : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ) :
    (q : ℝ) ≤ cycleSlope k * (n : ℝ) - 1 := by
  have hstrong : ∀ N : ℕ, k - 1 ≤ N →
      ∀ {Q : ℕ} (ψ : TopEdgeLabeling (Fin N) (Fin Q)),
        Function.Surjective ψ →
        (∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin N)),
          ¬IsRainbow f.toHom ψ) →
        (Q : ℝ) ≤ cycleSlope k * (N : ℝ) - 1 := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro hN Q ψ hψ hno
      by_cases hbase : N = k - 1
      · subst N
        have hused : (usedColors ψ).card = Q := by
          rw [usedColors, Finset.image_univ_of_surjective hψ]
          simp
        have hq : Q ≤ (k - 1).choose 2 := by
          have hbound := usedColors_card_le_antiRamseyNum
            (cycleGraph k) ψ hno
          rw [hused, antiRamseyNum_cycleGraph_induction_base k hk] at hbound
          exact hbound
        have hqreal : (Q : ℝ) ≤ (((k - 1).choose 2 : ℕ) : ℝ) := by
          exact_mod_cast hq
        have hcoeff := cycleSlope_base_identity k hk
        linarith
      · have hkN : k ≤ N := by omega
        cases N with
        | zero => omega
        | succ M =>
          have hM : k - 1 ≤ M := by omega
          by_cases hlow : ∃ v : Fin (M + 1),
              (newColors ψ v).card ≤ (k - 2) / 2
          · obtain ⟨v, hv⟩ := hlow
            obtain ⟨φ, hφ, hφfree⟩ :=
              deletedPalette_witness (cycleGraph k) ψ hno v
            have hp := ih M (by omega) hM φ hφ hφfree
            have hqrec := surjective_color_count_delete_add_new ψ hψ v
            have hqreal : (Q : ℝ) =
                ((colorsAfterDeleting ψ v).card : ℝ) +
                ((newColors ψ v).card : ℝ) := by
              exact_mod_cast hqrec
            have hvreal := new_le_cycleSlope_of_low k
              (newColors ψ v).card hk hv
            have hstep : cycleSlope k * ((M + 1 : ℕ) : ℝ) =
                cycleSlope k * (M : ℝ) + cycleSlope k := by
              push_cast
              ring
            linarith
          · have hlarge : ∀ v : Fin (M + 1),
                (k - 2) / 2 < (newColors ψ v).card := by
              intro v
              have hv : ¬(newColors ψ v).card ≤ (k - 2) / 2 := by
                intro h
                exact hlow ⟨v, h⟩
              omega
            have hnew : ∀ v : Fin (M + 1),
                2 ≤ (newColors ψ v).card := by
              intro v
              have hv := hlarge v
              omega
            have hpair : ∀ x y : Fin (M + 1), x ≠ y →
                k - 1 ≤ (newColors ψ x).card +
                  (newColors ψ y).card := by
              intro x y _
              have hx := hlarge x
              have hy := hlarge y
              omega
            obtain ⟨t, b, φ, ht, hcross, htri, hspos, hsupper, hsum⟩ :=
              hstructure hkN ψ hno hnew hpair
            have hcount := realized_colors_le_cycle_linear_of_weak_blocks
              k t (M + 1) (by omega) ht ψ b φ
              hcross htri hspos hsupper hsum
            have hused : (Finset.univ.image ψ).card = Q := by
              rw [Finset.image_univ_of_surjective hψ]
              simp
            simpa only [hused, cycleSlope] using hcount
  exact hstrong n hn χ hχ hfree

/-- Upper bound on `antiRamseyNum (cycleGraph k) n` for `k ≥ 4` and `n ≥ k - 1`
given `HighNewWeakStructure k`. -/
theorem antiRamseyNum_le_cycle_linear (k n : ℕ) (hk : 4 ≤ k)
    (hn : k - 1 ≤ n) (hstructure : HighNewWeakStructure k) :
    (antiRamseyNum (cycleGraph k) n : ℝ) ≤
      cycleSlope k * (n : ℝ) - 1 := by
  classical
  let A : Set ℕ :=
    {q | ∃ χ : TopEdgeLabeling (Fin n) (Fin q), Function.Surjective χ ∧
      ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
        ¬IsRainbow f.toHom χ}
  have hbounded : BddAbove A := by
    refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin n)).edgeSet), ?_⟩
    intro q hq
    obtain ⟨χ, hχ, _⟩ := hq
    simpa using Fintype.card_le_of_surjective χ hχ
  change ((sSup A : ℕ) : ℝ) ≤ cycleSlope k * (n : ℝ) - 1
  by_cases hnonempty : A.Nonempty
  · have hmem : sSup A ∈ A := Nat.sSup_mem hnonempty hbounded
    obtain ⟨χ, hχ, hfree⟩ := hmem
    exact admissible_palette_le_cycle_linear k n hk hn hstructure
      χ hχ hfree
  · have hA : A = ∅ := by
      ext q
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hq
      exact hnonempty ⟨q, hq⟩
    have hsup : sSup A = 0 := by simp [hA]
    rw [hsup]
    have hnreal : ((k - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hmul := mul_le_mul_of_nonneg_left hnreal
      (cycleSlope_nonneg k hk)
    have hcoeff := cycleSlope_base_identity k hk
    have hchoose : (0 : ℝ) ≤ (((k - 1).choose 2 : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    norm_num at hmul ⊢
    linarith

end ErdosProblems.AntiRamseyConditionalCycleUpper
