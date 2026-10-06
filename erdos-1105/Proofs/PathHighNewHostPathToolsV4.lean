module

public import CycleNewChoiceExchange
public import CycleOrderedEdges
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-! Input colors retain the same original χ. -/

namespace ErdosProblems.PathHighNewStageOne

open SimpleGraph

variable {n : ℕ} {C : Type*}

/-- Join two original rainbow host paths using one fresh literal endpoint edge.
The output preserves both input vertex orders, including singleton paths. -/
theorem rainbow_path_of_original_disjoint_paths_and_fresh_join
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (χ : TopEdgeLabeling (Fin n) C)
    (A : (pathGraph a).Copy (⊤ : SimpleGraph (Fin n)))
    (B : (pathGraph b).Copy (⊤ : SimpleGraph (Fin n)))
    (hA : IsRainbow A.toHom χ) (hB : IsRainbow B.toHom χ)
    (hdis : Disjoint (Set.range fun i : Fin a => A i)
      (Set.range fun j : Fin b => B j))
    (hpal : ∀ e : (pathGraph a).edgeSet, ∀ d : (pathGraph b).edgeSet,
      χ (A.toHom.mapEdgeSet e) ≠ χ (B.toHom.mapEdgeSet d))
    (join : (⊤ : SimpleGraph (Fin n)).edgeSet)
    (hjoin : join.val = s(A ⟨a - 1, by omega⟩, B ⟨0, by omega⟩))
    (hfreshA : ∀ e : (pathGraph a).edgeSet,
      χ (A.toHom.mapEdgeSet e) ≠ χ join)
    (hfreshB : ∀ d : (pathGraph b).edgeSet,
      χ (B.toHom.mapEdgeSet d) ≠ χ join) :
    ∃ f : (pathGraph (a + b)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ ∧
      (∀ i : Fin a, f (Fin.castAdd b i) = A i) ∧
      (∀ j : Fin b, f (Fin.natAdd a j) = B j) := by
  let Q : Fin (a + b) → Fin n := Fin.append (fun i => A i) (fun j => B j)
  have hQ : Function.Injective Q := Fin.append_injective_iff.mpr
    ⟨A.injective, B.injective, fun i j heq =>
      (Set.disjoint_left.mp hdis) ⟨i, rfl⟩ ⟨j, heq.symm⟩⟩
  let f : (pathGraph (a + b)).Copy (⊤ : SimpleGraph (Fin n)) :=
    (SimpleGraph.Embedding.completeGraph (⟨Q, hQ⟩ : Fin (a + b) ↪ Fin n)).toCopy.comp
      (Copy.ofLE (pathGraph (a + b)) (⊤ : SimpleGraph (Fin (a + b))) le_top)
  have hforward : ∀ i j : Fin (a + b), i.val + 1 = j.val →
      (∃ d : (pathGraph a).edgeSet,
        s(Q i, Q j) = (A.toHom.mapEdgeSet d).val) ∨
      s(Q i, Q j) = join.val ∨
      (∃ d : (pathGraph b).edgeSet,
        s(Q i, Q j) = (B.toHom.mapEdgeSet d).val) := by
    intro i j hij
    by_cases hjA : j.val < a
    · have hiA : i.val < a := by omega
      let iA : Fin a := ⟨i.val, hiA⟩
      let jA : Fin a := ⟨j.val, hjA⟩
      have hi : i = Fin.castAdd b iA := Fin.ext rfl
      have hj : j = Fin.castAdd b jA := Fin.ext rfl
      let d : (pathGraph a).edgeSet :=
        ⟨s(iA, jA), pathGraph_adj.mpr (Or.inl hij)⟩
      left
      refine ⟨d, ?_⟩
      change s(Q i, Q j) = s(A iA, A jA)
      simp only [Q, hi, hj, Fin.append_left]
    · by_cases hiA : i.val < a
      · have hi : i = Fin.castAdd b (⟨a - 1, by omega⟩ : Fin a) := by
          apply Fin.ext
          change i.val = a - 1
          omega
        have hj : j = Fin.natAdd a (⟨0, by omega⟩ : Fin b) := by
          apply Fin.ext
          change j.val = a + 0
          omega
        right
        left
        simp only [Q, hi, hj, Fin.append_left, Fin.append_right, hjoin]
      · have hibound := i.isLt
        have hjbound := j.isLt
        let iB : Fin b := ⟨i.val - a, by omega⟩
        let jB : Fin b := ⟨j.val - a, by omega⟩
        have hi : i = Fin.natAdd a iB := by
          apply Fin.ext
          change i.val = a + (i.val - a)
          omega
        have hj : j = Fin.natAdd a jB := by
          apply Fin.ext
          change j.val = a + (j.val - a)
          omega
        have hadj : (pathGraph b).Adj iB jB := by
          apply pathGraph_adj.mpr
          left
          change (i.val - a) + 1 = j.val - a
          omega
        let d : (pathGraph b).edgeSet := ⟨s(iB, jB), hadj⟩
        right
        right
        refine ⟨d, ?_⟩
        change s(Q i, Q j) = s(B iB, B jB)
        simp only [Q, hi, hj, Fin.append_right]
  have hcases : ∀ e : (pathGraph (a + b)).edgeSet,
      (∃ d : (pathGraph a).edgeSet,
        f.toHom.mapEdgeSet e = A.toHom.mapEdgeSet d) ∨
      f.toHom.mapEdgeSet e = join ∨
      (∃ d : (pathGraph b).edgeSet,
        f.toHom.mapEdgeSet e = B.toHom.mapEdgeSet d) := by
    intro e
    obtain ⟨q, hq⟩ := e
    induction q using Sym2.inductionOn with
    | _ i j =>
      have hadj : (pathGraph (a + b)).Adj i j := hq
      have hs :
          (∃ d : (pathGraph a).edgeSet,
            s(Q i, Q j) = (A.toHom.mapEdgeSet d).val) ∨
          s(Q i, Q j) = join.val ∨
          (∃ d : (pathGraph b).edgeSet,
            s(Q i, Q j) = (B.toHom.mapEdgeSet d).val) := by
        rcases pathGraph_adj.mp hadj with h | h
        · exact hforward i j h
        · simpa only [Sym2.eq_swap] using hforward j i h
      rcases hs with ⟨d, hd⟩ | hd | ⟨d, hd⟩
      · exact Or.inl ⟨d, Subtype.ext hd⟩
      · exact Or.inr (Or.inl (Subtype.ext hd))
      · exact Or.inr (Or.inr ⟨d, Subtype.ext hd⟩)
  have hrainbow : IsRainbow f.toHom χ := by
    intro e d heq
    change χ (f.toHom.mapEdgeSet e) = χ (f.toHom.mapEdgeSet d) at heq
    apply f.mapEdgeSet.injective
    change f.toHom.mapEdgeSet e = f.toHom.mapEdgeSet d
    rcases hcases e with ⟨eA, heA⟩ | heJ | ⟨eB, heB⟩ <;>
      rcases hcases d with ⟨dA, hdA⟩ | hdJ | ⟨dB, hdB⟩
    · have h : eA = dA := hA (by simpa only [EdgeLabeling.pullback_apply, heA, hdA] using heq)
      simp only [heA, hdA, h]
    · exact False.elim (hfreshA eA (by simpa only [heA, hdJ] using heq))
    · exact False.elim (hpal eA dB (by simpa only [heA, hdB] using heq))
    · exact False.elim (hfreshA dA (by simpa only [heJ, hdA] using heq.symm))
    · simp only [heJ, hdJ]
    · exact False.elim (hfreshB dB (by simpa only [heJ, hdB] using heq.symm))
    · exact False.elim (hpal dA eB (by simpa only [heB, hdA] using heq.symm))
    · exact False.elim (hfreshB eB (by simpa only [heB, hdJ] using heq))
    · have h : eB = dB := hB (by simpa only [EdgeLabeling.pullback_apply, heB, hdB] using heq)
      simp only [heB, hdB, h]
  refine ⟨f, hrainbow, ?_, ?_⟩
  · intro i
    change Q (Fin.castAdd b i) = A i
    simp only [Q, Fin.append_left]
  · intro j
    change Q (Fin.natAdd a j) = B j
    simp only [Q, Fin.append_right]

end ErdosProblems.PathHighNewStageOne

