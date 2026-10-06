module

public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Data.Fin.Tuple.Basic
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
This is the common-neighborhood
and chord-splice adapter; no desired larger path is supplied.
-/

namespace ErdosProblems.PathUpperReduction.EndpointAttachment1105

open SimpleGraph

/-- Two distinct fresh endpoint contacts extend a path by two vertices. -/
theorem attach_two_to_pathCopy {V : Type*} (G : SimpleGraph V) (m : ℕ)
    (P : (pathGraph (m + 1)).Copy G) (z z' : V)
    (hz : z ∉ Set.range P) (hz' : z' ∉ Set.range P) (hne : z ≠ z')
    (hleft : G.Adj z (P 0)) (hright : G.Adj (P (Fin.last m)) z') :
    (pathGraph (m + 3)) ⊑ G := by
  classical
  let Q : Fin (m + 2) → V := Fin.cons z P
  let W : Fin (m + 3) → V := Fin.snoc Q z'
  have hQinj : Function.Injective Q :=
    Fin.cons_injective_of_injective hz P.injective
  have hz'Q : z' ∉ Set.range Q := by
    rintro ⟨i, hi⟩
    cases i using Fin.cases with
    | zero =>
        apply hne
        simpa only [Q, Fin.cons_zero] using hi
    | succ j =>
        apply hz'
        exact ⟨j, by simpa only [Q, Fin.cons_succ] using hi⟩
  have hWinj : Function.Injective W :=
    Fin.snoc_injective_of_injective hQinj hz'Q
  have hQmap (i j : Fin (m + 2)) (hij : i.val + 1 = j.val) :
      G.Adj (Q i) (Q j) := by
    by_cases hi0 : i.val = 0
    · have hi : i = 0 := Fin.ext hi0
      have hj : j = (0 : Fin (m + 1)).succ := Fin.ext (by simp; omega)
      rw [hi, hj]
      simpa only [Q, Fin.cons_zero, Fin.cons_succ] using hleft
    · let ii : Fin (m + 1) := ⟨i.val - 1, by have hi := i.isLt; omega⟩
      let jj : Fin (m + 1) := ⟨j.val - 1, by have hj := j.isLt; omega⟩
      have hi : i = ii.succ := Fin.ext (by dsimp [ii]; omega)
      have hj : j = jj.succ := Fin.ext (by dsimp [jj]; omega)
      have hadj : (pathGraph (m + 1)).Adj ii jj :=
        pathGraph_adj.mpr (Or.inl (by dsimp [ii, jj]; omega))
      rw [hi, hj]
      simpa only [Q, Fin.cons_succ, Copy.toHom_apply] using P.toHom.map_adj hadj
  have hforward (i j : Fin (m + 3)) (hij : i.val + 1 = j.val) :
      G.Adj (W i) (W j) := by
    by_cases hjlast : j.val = m + 2
    · have hj : j = Fin.last (m + 2) := Fin.ext hjlast
      have hi : i = (Fin.last (m + 1)).castSucc := Fin.ext (by simp; omega)
      have hlast : Fin.last (m + 1) = (Fin.last m).succ := Fin.ext (by simp)
      rw [hi, hj]
      simpa only [W, Fin.snoc_castSucc, Fin.snoc_last, hlast,
        Q, Fin.cons_succ] using hright
    · let ii : Fin (m + 2) := ⟨i.val, by have hi := i.isLt; omega⟩
      let jj : Fin (m + 2) := ⟨j.val, by have hj := j.isLt; omega⟩
      have hi : i = ii.castSucc := Fin.ext rfl
      have hj : j = jj.castSucc := Fin.ext rfl
      rw [hi, hj]
      simp only [W, Fin.snoc_castSucc]
      exact hQmap ii jj hij
  let phi : (pathGraph (m + 3)) →g G := ⟨W, by
    intro i j hij
    rcases pathGraph_adj.mp hij with h | h
    · exact hforward i j h
    · exact (hforward j i h).symm⟩
  exact ⟨⟨phi, hWinj⟩⟩

/-- Original path-freedom excludes those two actual fresh endpoint contacts. -/
theorem endpoint_contacts_incompatible_of_free {V : Type*} (G : SimpleGraph V)
    (m : ℕ) (hfree : (pathGraph (m + 3)).Free G)
    (P : (pathGraph (m + 1)).Copy G) (z z' : V)
    (hz : z ∉ Set.range P) (hz' : z' ∉ Set.range P) (hne : z ≠ z') :
    ¬(G.Adj z (P 0) ∧ G.Adj (P (Fin.last m)) z') := by
  rintro ⟨hleft, hright⟩
  exact hfree (attach_two_to_pathCopy G m P z z' hz hz' hne hleft hright)

end ErdosProblems.PathUpperReduction.EndpointAttachment1105
