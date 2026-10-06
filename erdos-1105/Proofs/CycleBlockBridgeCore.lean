module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import CycleBlockCut

@[expose] public section

/-!
The ordered-block cycle obstruction transferred through an injective copy of
`cycleGraph k`.  This core statement uses the same pullback on source edges as
Formal Conjectures' `IsRainbow`, while leaving its import to a small facade.
-/

namespace ErdosProblems.AntiRamseyCycle

open SimpleGraph

/-- A simple cycle is not contained in a block smaller than its length. -/
theorem cycle_spans_blocks_of_small_fibers {n t : ℕ} {u : Fin n}
    (p : (⊤ : SimpleGraph (Fin n)).Walk u u) (hp : p.IsCycle)
    (π : Fin n → Fin t)
    (hsmall : ∀ b : Fin t,
      (Finset.univ.filter (fun x : Fin n => π x = b)).card < p.length) :
    ∃ x ∈ p.support, ∃ y ∈ p.support, π x ≠ π y := by
  classical
  by_contra hspan
  have hconst : ∀ x ∈ p.support, π x = π u := by
    intro x hx
    by_contra hne
    apply hspan
    exact ⟨u, p.start_mem_support, x, hx, Ne.symm hne⟩
  have hsubset : p.support.tail.toFinset ⊆
      Finset.univ.filter (fun x : Fin n => π x = π u) := by
    intro x hx
    have hx' : x ∈ p.support.tail := List.mem_toFinset.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hconst x ((p.mem_support_iff).mpr (Or.inr hx'))⟩
  have hlen : p.support.tail.length = p.length := by
    have h := p.length_support
    rw [← p.cons_tail_support] at h
    simp only [List.length_cons] at h
    omega
  have hcard : p.support.tail.toFinset.card = p.length := by
    rw [List.toFinset_card_of_nodup hp.support_nodup, hlen]
  have hle := Finset.card_le_card hsubset
  rw [hcard] at hle
  exact (Nat.not_le_of_gt (hsmall (π u))) hle

/-- Injective source-edge pullback forces the raw host coloring to be injective
on all edges of the mapped walk. -/
theorem injOn_mapped_walk_edges_of_injective_pullback
    {V W C : Type*} {H : SimpleGraph V} {G : SimpleGraph W}
    {u : V} (f : H →g G) (p : H.Walk u u)
    (c : Sym2 W → C)
    (hinj : Function.Injective
      (fun e : H.edgeSet => c (f.mapEdgeSet e).val)) :
    Set.InjOn c {e | e ∈ (p.map f).edges} := by
  intro e₁ he₁ e₂ he₂ hcolor
  simp only [Walk.edges_map, List.mem_map] at he₁ he₂
  obtain ⟨a, ha, rfl⟩ := he₁
  obtain ⟨b, hb, rfl⟩ := he₂
  let ea : H.edgeSet := ⟨a, p.edges_subset_edgeSet ha⟩
  let eb : H.edgeSet := ⟨b, p.edges_subset_edgeSet hb⟩
  have hpull : c (f.mapEdgeSet ea).val = c (f.mapEdgeSet eb).val := by
    simpa [ea, eb, Hom.mapEdgeSet] using hcolor
  have hab : ea = eb := hinj hpull
  have hab' : a = b := congrArg Subtype.val hab
  simp [hab']

/-- The raw ordered-block coloring pulled back along a copy of `C_k` cannot be
injective when every block contains fewer than `k` vertices. -/
theorem not_injective_raw_orderedBlockColor_pullback
    {k n t : ℕ} (hk : 3 ≤ k) (hn : k ≤ n)
    (π : Fin n → Fin t)
    (hsmall : ∀ b : Fin t,
      (Finset.univ.filter (fun x : Fin n => π x = b)).card < k)
    (f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n))) :
    ¬ Function.Injective
      (fun e : (cycleGraph k).edgeSet =>
        orderedBlockColor π (f.toHom.mapEdgeSet e).val) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  let p₀ : (cycleGraph (m + 3)).Walk 0 0 := cycleGraph.cycle m
  let p : (⊤ : SimpleGraph (Fin n)).Walk (f 0) (f 0) := p₀.map f.toHom
  have hp : p.IsCycle :=
    (Walk.isCycle_map_iff_of_injective f.injective).mpr cycleGraph.isCycle_cycle
  have hlen : p.length = m + 3 := by simp [p, p₀]
  have hsmall' : ∀ b : Fin t,
      (Finset.univ.filter (fun x : Fin n => π x = b)).card < p.length := by
    intro b
    simpa [hlen] using hsmall b
  have hspan := cycle_spans_blocks_of_small_fibers p hp π hsmall'
  intro hinj
  have hinjOn : Set.InjOn (orderedBlockColor π) {e | e ∈ p.edges} := by
    simpa [p] using
      (injOn_mapped_walk_edges_of_injective_pullback f.toHom p₀
        (orderedBlockColor π) hinj)
  exact (not_injOn_cycle_edges_of_spanning_blocks p hp π hspan) hinjOn

end ErdosProblems.AntiRamseyCycle
