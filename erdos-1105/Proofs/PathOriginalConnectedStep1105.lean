module

public import PathProperFirst1105

@[expose] public section

/-!
Reduces the general path anti-Ramsey upper bound by strong induction on the
host size `n` to the connected representative step (`ConnectedOriginalStep`),
handling the disconnected proper-first-component branch via `PathProperFirst1105`.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

/-- Remaining connected original-color step at one host size. Its IH concerns
only strictly smaller complete hosts, including every allowed smaller size. -/
def OriginalConnectedPathStep (k n : ℕ) : Prop :=
  ∀ (q : ℕ) (χ : TopEdgeLabeling (Fin n) (Fin q))
    (R : RepresentativeChoice χ), k ≤ n →
    (selectedGraph χ R).Connected →
    (∀ P : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow P.toHom χ) →
    OriginalFullSmallerHostIH k n →
    q ≤ ErdosProblems.PathLemmaFourScalar.pathFormula n k

/-- Construct the actual full family. Both its connected and proper-first exits
receive the SAME genuine current-host FULL smaller-host induction hypothesis. -/
theorem original_color_count_le_formula_of_connected_step_and_full_IH
    {k n q : ℕ} (hk : 8 ≤ k) (hkn : k ≤ n)
    (hstep : OriginalConnectedPathStep k n)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (hχ : Function.Surjective χ)
    (hno : ∀ P : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow P.toHom χ)
    (hIH : OriginalFullSmallerHostIH k n) :
    q ≤ ErdosProblems.PathLemmaFourScalar.pathFormula n k := by
  classical
  obtain ⟨R, roots, F, _hgreedy, _hpieces, _hcount, _hT, _hS, hcover, _hdisjoint⟩ :=
    exists_full_original_cut_family χ (choiceOfSurjective χ hχ)
  cases roots with
  | nil =>
      obtain ⟨x, hx, _⟩ := hcover (⟨0, by omega⟩ : Fin n)
      simp at hx
  | cons x xs =>
      by_cases hwhole : componentSupport χ R x = Set.univ
      · have hconn : (selectedGraph χ R).Connected := by
          apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
          refine ⟨x, fun v => ?_⟩
          apply (mem_componentSupport χ R x v).mp
          rw [hwhole]
          exact Set.mem_univ v
        exact hstep q χ R hkn hconn hno hIH
      · exact F.original_color_count_le_formula_of_proper_first_component
          hwhole hk hkn hno hIH

/-- Strong induction constructs FULL IH from strictly smaller proven hosts,
then applies the pointwise connected step only at the current host. -/
theorem antiRamseyNum_path_le_formula_of_connected_steps
    (k : ℕ) (hk : 8 ≤ k)
    (hsteps : ∀ n : ℕ, OriginalConnectedPathStep k n) :
    ∀ n : ℕ, k ≤ n →
      antiRamseyNum (pathGraph k) n ≤
        ErdosProblems.PathLemmaFourScalar.pathFormula n k := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hkn
      classical
      let admissible : Set ℕ :=
        {q | ∃ χ : TopEdgeLabeling (Fin n) (Fin q), Function.Surjective χ ∧
          ∀ P : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
            ¬ IsRainbow P.toHom χ}
      have hbounded : BddAbove admissible := by
        refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin n)).edgeSet), ?_⟩
        intro q hq
        obtain ⟨χ, hχ, _⟩ := hq
        simpa using Fintype.card_le_of_surjective χ hχ
      change sSup admissible ≤ _
      apply (csSup_le_iff' hbounded).2
      intro q hq
      obtain ⟨χ, hχ, hno⟩ := hq
      have hIH : OriginalFullSmallerHostIH k n := by
        intro m hkm hmn
        exact ih m hmn hkm
      exact original_color_count_le_formula_of_connected_step_and_full_IH
        hk hkn (hsteps n) χ hχ hno hIH

/-- All current-host steps are equivalent to the full original upper bound.
No step is manufactured by assuming its own conclusion as an induction IH. -/
theorem original_connected_path_steps_iff_full_upper
    (k : ℕ) (hk : 8 ≤ k) :
    (∀ n : ℕ, OriginalConnectedPathStep k n) ↔
      ∀ n : ℕ, k ≤ n →
        antiRamseyNum (pathGraph k) n ≤
          ErdosProblems.PathLemmaFourScalar.pathFormula n k := by
  constructor
  · exact antiRamseyNum_path_le_formula_of_connected_steps k hk
  · intro hupper n q χ R hkn _hconn hno _hIH
    have hχ : Function.Surjective χ := by
      intro c
      exact ⟨R.edge c, R.color_eq c⟩
    exact (original_surjective_noRainbow_color_count_le_antiRamseyNum
      (pathGraph k) χ hχ hno).trans (hupper n hkn)

end ErdosProblems.PathUpperReduction
