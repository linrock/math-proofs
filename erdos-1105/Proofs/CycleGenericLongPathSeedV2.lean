module

public import CycleMaximumPathLocalFreeV2
public import CyclePathOre

@[expose] public section

/-!
generic long-path seed candidate for the #1105 same-component
reduction. No coloring, NEW, component transport, fixed shorter-cycle exclusion or
universal anti-Ramsey theorem is asserted.
-/

namespace ErdosProblems.AntiRamseyCycleGenericLongPathSeed

open SimpleGraph
open ErdosProblems.AntiRamseyCycleMaximumPathLocalFree
open ErdosProblems.AntiRamseyCyclePathOre

/-- A larger connected finite graph with the supplied minimum and pair degree
bounds contains an injective ordered k-vertex path. The contradiction uses
the cycle order of the actual maximum path, not a fixed shorter cycle order. -/
theorem exists_ordered_path_of_degree_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (hk : 4 ≤ k)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hcard : k ≤ Fintype.card V)
    (hmin : ∀ x : V, 2 ≤ G.degree x)
    (hpair : ∀ x y : V, x ≠ y → k - 1 ≤ G.degree x + G.degree y) :
    ∃ q : Fin k → V, Function.Injective q ∧
      ∀ a b : Fin k, a.val + 1 = b.val → G.Adj (q a) (q b) := by
  classical
  let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨u, v, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  have hlen : 2 ≤ p.length := by
    have hmany : 1 < (G.neighborFinset u).card := by
      have hdegree := hmin u
      change 2 ≤ (G.neighborFinset u).card at hdegree
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hmany
    have hua : G.Adj u a := (G.mem_neighborFinset u a).mp ha
    have hub : G.Adj u b := (G.mem_neighborFinset u b).mp hb
    let one : G.Walk u b := SimpleGraph.Walk.cons hub SimpleGraph.Walk.nil
    have hone : one.IsPath := by
      apply SimpleGraph.Walk.IsPath.nil.cons
      simpa only [SimpleGraph.Walk.support_nil, List.mem_singleton] using hub.ne
    let two : G.Walk a b := SimpleGraph.Walk.cons hua.symm one
    have htwo : two.IsPath := by
      apply hone.cons
      intro hmem
      change a ∈ u :: [b] at hmem
      rcases List.mem_cons.mp hmem with heq | heq
      · exact hua.ne heq.symm
      · exact hab (List.mem_singleton.mp heq)
    have hbound := hmax a b two htwo
    change 2 ≤ p.length at hbound
    exact hbound
  have hleft : ∀ x : V, G.Adj u x → x ∈ p.support := by
    intro x hx
    by_contra hout
    let longer : G.Walk x v := SimpleGraph.Walk.cons hx.symm p
    have hlonger : longer.IsPath := hp.cons hout
    have hbound := hmax x v longer hlonger
    change p.length + 1 ≤ p.length at hbound
    omega
  have hright : ∀ x : V, G.Adj v x → x ∈ p.support := by
    intro x hx
    by_contra hout
    have houtReverse : x ∉ p.reverse.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hout
    let longer : G.Walk x u := SimpleGraph.Walk.cons hx.symm p.reverse
    have hlonger : longer.IsPath := hp.reverse.cons houtReverse
    have hbound := hmax x u longer hlonger
    change p.reverse.length + 1 ≤ p.length at hbound
    rw [SimpleGraph.Walk.length_reverse] at hbound
    omega
  let order : Fin (p.length + 1) → V := fun i => p.getVert i.val
  have horder : Function.Injective order := by
    intro i j hij
    apply Fin.ext
    exact hp.getVert_injOn (Nat.le_of_lt_succ i.isLt)
      (Nat.le_of_lt_succ j.isLt) hij
  have hzero : order 0 = u := p.getVert_zero
  have hlast : order (Fin.last p.length) = v := p.getVert_length
  have huv : u ≠ v := by
    intro heq
    have hi := horder (hzero.trans (heq.trans hlast.symm))
    have hval := congrArg Fin.val hi
    change 0 = p.length at hval
    omega
  have hlong : k ≤ p.length + 1 := by
    by_contra hshort
    have hshortLength : p.length + 1 < k := Nat.lt_of_not_ge hshort
    have hlarge : p.length + 1 < Fintype.card V :=
      lt_of_lt_of_le hshortLength hcard
    let H : SimpleGraph (Fin (p.length + 1)) := G.comap order
    have hHpath : ∀ a b : Fin (p.length + 1),
        a.val + 1 = b.val → H.Adj a b := by
      intro a b hab
      change G.Adj (p.getVert a.val) (p.getVert b.val)
      have hb := b.isLt
      have hadj := p.adj_getVert_succ (i := a.val) (by omega)
      rw [hab] at hadj
      exact hadj
    have hfree : (cycleGraph (p.length + 1)).Free H :=
      maximum_path_cycle_free_on_image G hconn u v p hp hmax hlen hlarge
    have hneighbors (i : Fin (p.length + 1))
        (hall : ∀ x : V, G.Adj (order i) x → x ∈ p.support) :
        G.neighborFinset (order i) = (H.neighborFinset i).image order := by
      ext x
      constructor
      · intro hx
        have hadj : G.Adj (order i) x := (G.mem_neighborFinset (order i) x).mp hx
        obtain ⟨a, ha, halength⟩ :=
          SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hall x hadj)
        let j : Fin (p.length + 1) := ⟨a, by omega⟩
        refine Finset.mem_image.mpr ⟨j, ?_, ha⟩
        apply (H.mem_neighborFinset i j).mpr
        change G.Adj (order i) (p.getVert a)
        rw [ha]
        exact hadj
      · intro hx
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
        apply (G.mem_neighborFinset (order i) (order j)).mpr
        exact (show G.Adj (order i) (order j) from
          (H.mem_neighborFinset i j).mp hj)
    have hdegree (i : Fin (p.length + 1))
        (hall : ∀ x : V, G.Adj (order i) x → x ∈ p.support) :
        G.degree (order i) = H.degree i := by
      calc
        G.degree (order i) = (G.neighborFinset (order i)).card := rfl
        _ = ((H.neighborFinset i).image order).card :=
          congrArg Finset.card (hneighbors i hall)
        _ = (H.neighborFinset i).card :=
          Finset.card_image_of_injective _ horder
        _ = H.degree i := rfl
    have hdegreeZero := hdegree 0 (by
      intro x hx
      rw [hzero] at hx
      exact hleft x hx)
    rw [hzero] at hdegreeZero
    have hdegreeLast := hdegree (Fin.last p.length) (by
      intro x hx
      rw [hlast] at hx
      exact hright x hx)
    rw [hlast] at hdegreeLast
    have hdeficit := path_endpoint_degree_sum_lt hlen H hHpath hfree
    rw [← hdegreeZero, ← hdegreeLast] at hdeficit
    have hpairEnds := hpair u v huv
    omega
  let q : Fin k → V := fun i => p.getVert i.val
  refine ⟨q, ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    exact hp.getVert_injOn
      (Nat.le_of_lt_succ (lt_of_lt_of_le i.isLt hlong))
      (Nat.le_of_lt_succ (lt_of_lt_of_le j.isLt hlong)) hij
  · intro a b hab
    change G.Adj (p.getVert a.val) (p.getVert b.val)
    have hb := b.isLt
    have hadj := p.adj_getVert_succ (i := a.val) (by omega)
    rw [hab] at hadj
    exact hadj

end ErdosProblems.AntiRamseyCycleGenericLongPathSeed
