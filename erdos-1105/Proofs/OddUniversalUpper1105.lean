module

public import OddConnectedOriginalUpper1105
public import PathOriginalConnectedStep1105

@[expose] public section

namespace ErdosProblems.PathUpperReduction.OddUniversalUpper1105

open SimpleGraph

/-- Literal original anti-Ramsey upper bound on every complete host, for every
odd path order k>=9. No supplied connectivity, family, degree or IH premise. -/
theorem antiRamseyNum_odd_path_le_formula (k n : ℕ)
    (hk : 9 ≤ k) (hodd : Odd k) (hkn : k ≤ n) :
    antiRamseyNum (pathGraph k) n ≤
      max ((k - 2).choose 2 + 1)
        (((k - 1) / 2 - 1).choose 2 +
          ((k - 1) / 2 - 1) * (n - (k - 1) / 2 + 1) + 1) := by
  let ell : ℕ := (k - 1) / 2
  have hparity := Nat.odd_iff.mp hodd
  have hkEq : k = 2 * ell + 1 := by dsimp only [ell]; omega
  have hell : 4 ≤ ell := by omega
  have hsteps : ∀ u : ℕ, OriginalConnectedPathStep k u := by
    intro u q χ R hku hconn hno _hIH
    have hku' : 2 * ell + 1 ≤ u := by omega
    have hno' : ∀ P : (pathGraph (2 * ell + 1)).Copy
        (⊤ : SimpleGraph (Fin u)), ¬ IsRainbow P.toHom χ := by
      rw [← hkEq]
      exact hno
    have hbound :=
      OddConnectedOriginalUpper1105.original_connected_odd_palette_upper
        hell hku' χ R hconn hno'
    have hhalf : (k - 1) / 2 = ell := rfl
    have hpred : k - 2 = 2 * ell - 1 := by omega
    simpa only [ErdosProblems.PathLemmaFourScalar.pathFormula,
      hhalf, hpred, ite_eq_left hodd] using hbound
  have hupper := antiRamseyNum_path_le_formula_of_connected_steps
    k (by omega) hsteps n hkn
  simpa only [ErdosProblems.PathLemmaFourScalar.pathFormula, ite_eq_left hodd] using hupper

end ErdosProblems.PathUpperReduction.OddUniversalUpper1105
