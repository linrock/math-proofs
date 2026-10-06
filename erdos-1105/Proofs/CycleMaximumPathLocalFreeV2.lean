module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Tactic

@[expose] public section

/-!
For the variable current-order graph step in the #1105
same-component seed reduction. No NEW or colouring hypothesis is introduced.
-/

namespace ErdosProblems.AntiRamseyCycleMaximumPathLocalFree

open SimpleGraph

/-- In a larger connected graph, the image of a maximum-length path cannot
contain a cycle spanning all of its vertices. -/
theorem maximum_path_cycle_free_on_image
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (hconn : H.Connected)
    (u v : V) (p : H.Walk u v) (hp : p.IsPath)
    (hmax : ∀ (a b : V) (w : H.Walk a b),
      w.IsPath → w.length ≤ p.length)
    (hlen : 2 ≤ p.length)
    (hlarge : p.length + 1 < Fintype.card V) :
    (cycleGraph (p.length + 1)).Free
      (H.comap (fun i : Fin (p.length + 1) => p.getVert i.val)) := by
  classical
  let q : Fin (p.length + 1) → V := fun i => p.getVert i.val
  have hq : Function.Injective q := by
    intro i j hij
    apply Fin.ext
    exact hp.getVert_injOn (by exact Nat.le_of_lt_succ i.isLt)
      (by exact Nat.le_of_lt_succ j.isLt) hij
  have hq_not_surjective : ¬Function.Surjective q := by
    intro hsurj
    have hcard : Fintype.card V ≤ p.length + 1 := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective q hsurj
    exact (Nat.not_le_of_gt hlarge) hcard
  obtain ⟨z, hz⟩ := not_forall.mp hq_not_surjective
  have hzrange : z ∉ Set.range q := hz
  intro hcontained
  obtain ⟨a, c, hc, hclength⟩ :=
    (cycleGraph_isContained_iff (by omega : 2 < p.length + 1)).mp hcontained
  have hham : c.IsHamiltonianCycle :=
    SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr
      ⟨hc, by simpa only [Fintype.card_fin] using hclength⟩
  let f : H.comap q →g H := SimpleGraph.Hom.comap q H
  have hf : Function.Injective f := by
    change Function.Injective q
    exact hq
  let cc : H.Walk (q a) (q a) := c.map f
  have hcc : cc.IsCycle :=
    (SimpleGraph.Walk.isCycle_map_iff_of_injective hf).mpr hc
  have hcclength : cc.length = p.length + 1 := by
    exact (SimpleGraph.Walk.length_map f c).trans hclength
  have hsupport (x : V) : x ∈ cc.support ↔ x ∈ Set.range q := by
    change x ∈ (c.map f).support ↔ x ∈ Set.range q
    rw [SimpleGraph.Walk.support_map]
    constructor
    · intro hx
      obtain ⟨i, _, hi⟩ := List.mem_map.mp hx
      exact ⟨i, hi⟩
    · rintro ⟨i, rfl⟩
      exact List.mem_map.mpr ⟨i, hham.mem_support i, rfl⟩
  obtain ⟨w⟩ := hconn (q a) z
  obtain ⟨d, _, hdinside, hdoutside⟩ :=
    w.exists_boundary_dart (Set.range q) ⟨a, rfl⟩ hzrange
  have hdmem : d.fst ∈ cc.support := (hsupport d.fst).mpr hdinside
  let rot : H.Walk d.fst d.fst := cc.rotate d.fst hdmem
  have hrot : rot.IsCycle := hcc.rotate hdmem
  have hdnot_dropLast : d.snd ∉ rot.dropLast.support := by
    intro hd
    rw [rot.support_dropLast hrot.not_nil] at hd
    have hdrot : d.snd ∈ rot.support := List.mem_of_mem_dropLast hd
    have hdcc : d.snd ∈ cc.support :=
      (cc.mem_support_rotate_iff d.fst hdmem).mp hdrot
    exact hdoutside ((hsupport d.snd).mp hdcc)
  let longer := SimpleGraph.Walk.cons d.adj.symm rot.dropLast
  have hlonger : longer.IsPath := hrot.isPath_dropLast.cons hdnot_dropLast
  have hlonger_length : longer.length = p.length + 1 := by
    change rot.dropLast.length + 1 = p.length + 1
    calc
      rot.dropLast.length + 1 = rot.length :=
        SimpleGraph.Walk.length_dropLast_add_one hrot.not_nil
      _ = cc.length := SimpleGraph.Walk.length_rotate cc d.fst hdmem
      _ = p.length + 1 := hcclength
  have hbound := hmax _ _ longer hlonger
  rw [hlonger_length] at hbound
  omega

end ErdosProblems.AntiRamseyCycleMaximumPathLocalFree

