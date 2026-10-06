module

public import PathMaxLower
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Tactic

@[expose] public section

/-! Finite original-parameter palette collapse for Erdős #1105 path k=n=6. The eight-color no-rainbow exclusion is an explicit hypothesis. -/

namespace ErdosProblems.AntiRamseyPathSixSixConditionalCollapse

open SimpleGraph

def admissible (q : ℕ) : Prop :=
  ∃ χ : TopEdgeLabeling (Fin 6) (Fin q), Function.Surjective χ ∧
    ∀ f : (pathGraph 6).Copy (⊤ : SimpleGraph (Fin 6)),
      ¬ IsRainbow f.toHom χ

def collapse {q : ℕ} : Fin q → Fin 8 :=
  fun i => ⟨min i.val 7, by omega⟩

theorem collapse_surjective {q : ℕ} (hq : 8 ≤ q) :
    Function.Surjective (collapse : Fin q → Fin 8) := by
  intro j
  have hj : j.val ≤ 7 := by
    have := j.isLt
    omega
  refine ⟨⟨j.val, by omega⟩, ?_⟩
  apply Fin.ext
  change min j.val 7 = j.val
  exact Nat.min_eq_left hj

/-- A surjective q-color host with no rainbow P6 would collapse to an
eight-color one. Rainbow after collapse implies rainbow before collapse. -/
theorem admissible_collapse {q : ℕ} (hq : 8 ≤ q) :
    admissible q → admissible 8 := by
  rintro ⟨χ, hsurj, hno⟩
  let ψ : TopEdgeLabeling (Fin 6) (Fin 8) := fun e => collapse (χ e)
  refine ⟨ψ, ?_, ?_⟩
  · intro j
    obtain ⟨i, hi⟩ := collapse_surjective hq j
    obtain ⟨e, he⟩ := hsurj i
    refine ⟨e, ?_⟩
    simpa [ψ, he] using hi
  · intro f hψ
    apply hno f
    intro e₁ e₂ heq
    apply hψ
    exact congrArg collapse heq

theorem admissible_bddAbove :
    BddAbove {q : ℕ | admissible q} := by
  refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin 6)).edgeSet), ?_⟩
  intro q hq
  obtain ⟨χ, hsurj, _⟩ := hq
  simpa using Fintype.card_le_of_surjective χ hsurj

/-- Exact Formal Conjectures anti-Ramsey number upper bound at n=k=6,
conditional on an independently verified eight-color exclusion. -/
theorem antiRamseyNum_pathGraph_six_six_le_seven_of_eight_exclusion
    (h8 : ¬ ∃ χ : TopEdgeLabeling (Fin 6) (Fin 8),
      Function.Surjective χ ∧
      ∀ f : (pathGraph 6).Copy (⊤ : SimpleGraph (Fin 6)),
        ¬ IsRainbow f.toHom χ) :
    antiRamseyNum (pathGraph 6) 6 ≤ 7 := by
  have hno : ¬ admissible 8 := h8
  change sSup {q : ℕ | admissible q} ≤ 7
  refine (csSup_le_iff' admissible_bddAbove).2 ?_
  intro q hq
  by_contra hle
  have hq8 : 8 ≤ q := by omega
  exact hno (admissible_collapse hq8 hq)

/-- Conditional first original P6 equality. The checked all-parameter
path lower theorem supplies the reverse direction at (6,6). -/
theorem antiRamseyNum_pathGraph_six_six_eq_seven_of_eight_exclusion
    (h8 : ¬ ∃ χ : TopEdgeLabeling (Fin 6) (Fin 8),
      Function.Surjective χ ∧
      ∀ f : (pathGraph 6).Copy (⊤ : SimpleGraph (Fin 6)),
        ¬ IsRainbow f.toHom χ) :
    antiRamseyNum (pathGraph 6) 6 = 7 := by
  have hupper :=
    antiRamseyNum_pathGraph_six_six_le_seven_of_eight_exclusion h8
  have hlower :=
    ErdosProblems.PathSetLower.pathMaxLower 6 6 (by decide) (by decide)
  norm_num at hlower
  exact Nat.le_antisymm hupper hlower.2

end ErdosProblems.AntiRamseyPathSixSixConditionalCollapse
