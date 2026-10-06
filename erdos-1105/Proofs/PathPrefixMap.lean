module

public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Tactic

@[expose] public section

/-!
The initial `r` vertices of `Fin n` form a canonical copy of the complete graph
on `Fin r`. Its mapped edges have both endpoints below `r`.
-/

namespace ErdosProblems.PathCliqueLower

open SimpleGraph

/-- The complete graph on the first `r` vertices of `Fin n`. -/
def prefixCopy {r n : ℕ} (h : r ≤ n) :
    (⊤ : SimpleGraph (Fin r)).Copy (⊤ : SimpleGraph (Fin n)) :=
  (SimpleGraph.Embedding.completeGraph (Fin.castLEEmb h)).toCopy

@[simp] theorem prefixCopy_apply {r n : ℕ} (h : r ≤ n) (i : Fin r) :
    prefixCopy h i = Fin.castLE h i := rfl

/-- The canonical injection from the smaller complete graph's edge set. -/
def prefixEdgeMap {r n : ℕ} (h : r ≤ n) :
    (⊤ : SimpleGraph (Fin r)).edgeSet ↪ (⊤ : SimpleGraph (Fin n)).edgeSet :=
  (prefixCopy h).mapEdgeSet

theorem prefixEdgeMap_injective {r n : ℕ} (h : r ≤ n) :
    Function.Injective (prefixEdgeMap h) :=
  (prefixEdgeMap h).injective

/-- An edge with an endpoint outside the first `r` vertices is not mapped from the clique. -/
theorem prefix_edge_not_range {r n : ℕ} (h : r ≤ n)
    (a b : Fin n) (hab : a ≠ b) (hout : r ≤ a.val ∨ r ≤ b.val) :
    ¬∃ x : (⊤ : SimpleGraph (Fin r)).edgeSet,
      (prefixCopy h).mapEdgeSet x =
        ⟨s(a, b), (SimpleGraph.top_adj a b).2 hab⟩ := by
  rintro ⟨x, hx⟩
  have hxval := congrArg Subtype.val hx
  change Sym2.map (Fin.castLE h) x.val = s(a, b) at hxval
  have ha : a.val < r := by
    have haMem : a ∈ Sym2.map (Fin.castLE h) x.val :=
      hxval.symm ▸ Sym2.mem_mk_left a b
    obtain ⟨u, _, hu⟩ := Sym2.mem_map.mp haMem
    have huval : u.val < r := u.isLt
    have heq := congrArg Fin.val hu
    simpa only [Fin.val_castLE] using heq.symm ▸ huval
  have hb : b.val < r := by
    have hbMem : b ∈ Sym2.map (Fin.castLE h) x.val :=
      hxval.symm ▸ Sym2.mem_mk_right a b
    obtain ⟨u, _, hu⟩ := Sym2.mem_map.mp hbMem
    have huval : u.val < r := u.isLt
    have heq := congrArg Fin.val hu
    simpa only [Fin.val_castLE] using heq.symm ▸ huval
  omega

/-- An explicit edge between vertices `r` and `r + 1`, both outside the prefix clique. -/
def outsideEdge {r n : ℕ} (h : r + 2 ≤ n) :
    (⊤ : SimpleGraph (Fin n)).edgeSet := by
  let a : Fin n := ⟨r, by omega⟩
  let b : Fin n := ⟨r + 1, by omega⟩
  have hab : a ≠ b := by
    intro heq
    have heqval := congrArg Fin.val heq
    dsimp [a, b] at heqval
    omega
  exact ⟨s(a, b), (SimpleGraph.top_adj a b).2 hab⟩

theorem outsideEdge_not_range {r n : ℕ} (h : r + 2 ≤ n) :
    ¬∃ x : (⊤ : SimpleGraph (Fin r)).edgeSet,
      (prefixCopy (by omega : r ≤ n)).mapEdgeSet x = outsideEdge h := by
  let a : Fin n := ⟨r, by omega⟩
  let b : Fin n := ⟨r + 1, by omega⟩
  have hab : a ≠ b := by
    intro heq
    have heqval := congrArg Fin.val heq
    dsimp [a, b] at heqval
    omega
  simpa only [outsideEdge] using
    (prefix_edge_not_range (by omega : r ≤ n) a b hab (Or.inl le_rfl))

end ErdosProblems.PathCliqueLower
