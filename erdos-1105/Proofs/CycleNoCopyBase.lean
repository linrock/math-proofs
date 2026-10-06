module

public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-!
The exact Formal Conjectures anti-Ramsey count when the host is too small
to contain an injective copy of the forbidden graph. The cycle
specialization is Choi's n = k - 1 induction base, not an n ≥ k upper bound.
-/

namespace ErdosProblems.AntiRamseyCycleBase

open SimpleGraph

/-- A graph with more vertices than the complete host has no injective copy. -/
theorem noCopy_of_card_gt {α : Type*} [Fintype α]
    (H : SimpleGraph α) (n : ℕ) (hn : n < Fintype.card α) :
    ∀ _ : H.Copy (⊤ : SimpleGraph (Fin n)), False := by
  intro f
  have hcard : Fintype.card α ≤ n := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective (f : α → Fin n) f.injective
  exact (not_lt_of_ge hcard) hn

/-- With no possible injective `H` copy, every host edge can use its own
color and no admissible coloring can use more colors than host edges. -/
theorem antiRamseyNum_eq_edgeCount_of_card_gt {α : Type*} [Fintype α]
    (H : SimpleGraph α) (n : ℕ) (hn : n < Fintype.card α) :
    antiRamseyNum H n =
      Fintype.card ((⊤ : SimpleGraph (Fin n)).edgeSet) := by
  classical
  let A : Set ℕ :=
    {q | ∃ χ : TopEdgeLabeling (Fin n) (Fin q), Function.Surjective χ ∧
      ∀ f : H.Copy (⊤ : SimpleGraph (Fin n)), ¬IsRainbow f.toHom χ}
  have hbounded : BddAbove A := by
    refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin n)).edgeSet), ?_⟩
    intro q hq
    obtain ⟨χ, hχ, _⟩ := hq
    simpa using Fintype.card_le_of_surjective χ hχ
  have hmem : Fintype.card ((⊤ : SimpleGraph (Fin n)).edgeSet) ∈ A := by
    let efin := Fintype.equivFin ((⊤ : SimpleGraph (Fin n)).edgeSet)
    let χ : TopEdgeLabeling (Fin n)
        (Fin (Fintype.card ((⊤ : SimpleGraph (Fin n)).edgeSet))) :=
      fun e => efin e
    refine ⟨χ, ?_, ?_⟩
    · intro c
      obtain ⟨e, he⟩ := efin.surjective c
      exact ⟨e, he⟩
    · intro f
      exact (noCopy_of_card_gt H n hn f).elim
  change sSup A = Fintype.card ((⊤ : SimpleGraph (Fin n)).edgeSet)
  apply le_antisymm
  · refine (csSup_le_iff' hbounded).2 ?_
    intro q hq
    obtain ⟨χ, hχ, _⟩ := hq
    simpa using Fintype.card_le_of_surjective χ hχ
  · exact le_csSup hbounded hmem

/-- Choi's exact `n = k - 1` base for the first `n = k` induction step,
under the current Formal Conjectures injective-copy definition. -/
theorem antiRamseyNum_cycleGraph_induction_base (k : ℕ) (hk : 4 ≤ k) :
    antiRamseyNum (cycleGraph k) (k - 1) = (k - 1).choose 2 := by
  have hsmall : k - 1 < Fintype.card (Fin k) := by
    simp only [Fintype.card_fin]
    omega
  calc
    antiRamseyNum (cycleGraph k) (k - 1) =
        Fintype.card ((⊤ : SimpleGraph (Fin (k - 1))).edgeSet) :=
      antiRamseyNum_eq_edgeCount_of_card_gt (cycleGraph k) (k - 1) hsmall
    _ = (k - 1).choose 2 := by
      rw [SimpleGraph.card_edgeSet,
        SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
      simp

end ErdosProblems.AntiRamseyCycleBase
