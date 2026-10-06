module

public import PathLemmaFourScalarV3
public import PathLemmaFourEnvelopeV2

@[expose] public section

/-!
Pure scalar caller for the actual all-short component
charge. The target is the existing PathLemmaFourScalar.pathFormula n k,
including its literal natural subtraction, choose, division and Odd epsilon. No all-short graph hypothesis, component-size bound, connected sharp head cap
or induction conclusion is assumed or proved in this file.

For k>=6, d=(k-2)/2>=2, p>=d+1 and k=p+d+1. The clique head satisfies
choose(p,2)>=c_d*p, so the existing envelope gives the stronger c_d*n<=F(n,k). At k=6 this clique comparison is equality (d=2,p=3). The k=5 formula identity
supports the separate actual no-edge component argument; this file does not
derive that graph branch.
-/

namespace ErdosProblems.PathUpperReduction

open ErdosProblems.PathLemmaFourScalar

/-- The existing arbitrary-tail envelope bounds the all-short density in the
full host regime, without a path-order comparison or a supplied head cap. -/
theorem all_short_density_le_pathFormula (k n : ℕ)
    (hk : 6 ≤ k) (hkn : k ≤ n) :
    let d : ℕ := (k - 2) / 2
    (((d : ℝ) - 1) / 2 + 1 / (d : ℝ)) * (n : ℝ) ≤
      (pathFormula n k : ℝ) := by
  let d : ℕ := (k - 2) / 2
  let p : ℕ := k - d - 1
  let c : ℝ := ((d : ℝ) - 1) / 2 + 1 / (d : ℝ)
  change c * (n : ℝ) ≤ (pathFormula n k : ℝ)
  have hd : 2 ≤ d := by dsimp [d]; omega
  have hdp : d + 1 ≤ p := by dsimp [p, d]; omega
  have hpk : p + d + 1 = k := by dsimp [p, d]; omega
  have hpn : p ≤ n := by omega
  have hsum : p + (n - p) = n := by omega
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpR : (d : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hdp
  have hinv : 1 / (d : ℝ) ≤ (1 : ℝ) / 2 :=
    one_div_le_one_div_of_le (by norm_num) hdR
  have hc : c ≤ ((p : ℝ) - 1) / 2 := by
    dsimp [c]
    linarith
  have hmul := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
  have hchoose : c * (p : ℝ) ≤ (p.choose 2 : ℝ) := by
    rw [Nat.cast_choose_two ℝ p]
    nlinarith only [hmul]
  have henv := ErdosProblems.PathLemmaFourEnvelope.scalar_affine_envelope
    p d p (n - p) (by omega) hd (le_refl p) (by omega)
  change (ErdosProblems.PathLemmaFourEnvelope.scalarCap p p : ℝ) +
      c * ((n - p : ℕ) : ℝ) ≤
    (pathFormula (p + (n - p)) (p + d + 1) : ℝ) at henv
  simp only [ErdosProblems.PathLemmaFourEnvelope.scalarCap,
    ite_eq_left (le_refl p)] at henv
  rw [hsum, hpk] at henv
  have hsub : ((n - p : ℕ) : ℝ) = (n : ℝ) - (p : ℝ) := Nat.cast_sub hpn
  rw [hsub] at henv
  calc
    c * (n : ℝ) = c * (p : ℝ) + c * ((n : ℝ) - (p : ℝ)) := by ring
    _ ≤ (p.choose 2 : ℝ) + c * ((n : ℝ) - (p : ℝ)) :=
      add_le_add hchoose (le_refl _)
    _ ≤ (pathFormula n k : ℝ) := henv

/-- An actual summed all-short charge implies the literal original numerical
upper bound. Deriving this charge from the actual component family is separate. -/
theorem all_short_color_count_le_pathFormula (k n q : ℕ)
    (hk : 6 ≤ k) (hkn : k ≤ n)
    (hcharge : let d : ℕ := (k - 2) / 2
      (q : ℝ) + 2 ≤
        (((d : ℝ) - 1) / 2 + 1 / (d : ℝ)) * (n : ℝ)) :
    q ≤ pathFormula n k := by
  have hdensity := all_short_density_le_pathFormula k n hk hkn
  have hreal : (q : ℝ) ≤ (pathFormula n k : ℝ) := by
    dsimp only at hcharge hdensity
    linarith
  exact_mod_cast hreal

/-- Literal k=5 formula in its full host domain. The separate actual no-edge
branch can use this identity without extending the d>=2 density envelope. -/
theorem pathFormula_five_eq_host (n : ℕ) (hn : 5 ≤ n) :
    pathFormula n 5 = n := by
  have hodd : Odd (5 : ℕ) := ⟨2, by decide⟩
  have hform : pathFormula n 5 = max 4 (n - 2 + 2) := by
    norm_num [pathFormula, hodd, Nat.add_assoc]
  have hsub : n - 2 + 2 = n := by omega
  rw [hform, hsub]
  exact max_eq_right (by omega)

end ErdosProblems.PathUpperReduction

