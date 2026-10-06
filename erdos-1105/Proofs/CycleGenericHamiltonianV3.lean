module

public import CycleMaximumPathLocalFreeV2
public import CyclePathOre

@[expose] public section

/-!
generic Hamiltonicity candidate for the #1105 selected-component
reduction. No coloring, NEW, component order upper bound or weak quotient is asserted.
-/

namespace ErdosProblems.AntiRamseyCycleGenericHamiltonian

open SimpleGraph
open ErdosProblems.AntiRamseyCycleMaximumPathLocalFree
open ErdosProblems.AntiRamseyCyclePathOre

/-- A connected finite graph of order at least three whose distinct vertex
degrees sum at least to its order contains a non-induced spanning cycle Copy. -/
theorem contains_spanning_cycle_of_degree_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hcard : 3 ≤ Fintype.card V)
    (hpair : ∀ x y : V, x ≠ y →
      Fintype.card V ≤ G.degree x + G.degree y) :
    (cycleGraph (Fintype.card V)) ⊑ G := by
  classical
  have htwoVertices : 1 < (Finset.univ : Finset V).card := by
    simpa only [Finset.card_univ] using (show 1 < Fintype.card V by omega)
  obtain ⟨a, _, b, _, hab⟩ := Finset.one_lt_card.mp htwoVertices
  let : Nonempty V := ⟨a⟩
  have hsomeDegree : ∃ x : V, 2 ≤ G.degree x := by
    have hsum := hpair a b hab
    by_cases ha : 2 ≤ G.degree a
    · exact ⟨a, ha⟩
    · exact ⟨b, by omega⟩
  obtain ⟨u, v, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  have hlen : 2 ≤ p.length := by
    obtain ⟨x, hxdegree⟩ := hsomeDegree
    have hmany : 1 < (G.neighborFinset x).card := by
      change 2 ≤ (G.neighborFinset x).card at hxdegree
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hmany
    have hxa : G.Adj x a := (G.mem_neighborFinset x a).mp ha
    have hxb : G.Adj x b := (G.mem_neighborFinset x b).mp hb
    let one : G.Walk x b := SimpleGraph.Walk.cons hxb SimpleGraph.Walk.nil
    have hone : one.IsPath := by
      apply SimpleGraph.Walk.IsPath.nil.cons
      simpa only [SimpleGraph.Walk.support_nil, List.mem_singleton] using hxb.ne
    let two : G.Walk a b := SimpleGraph.Walk.cons hxa.symm one
    have htwo : two.IsPath := by
      apply hone.cons
      intro hmem
      change a ∈ x :: [b] at hmem
      rcases List.mem_cons.mp hmem with heq | heq
      · exact hxa.ne heq.symm
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
  have horderCard : p.length + 1 ≤ Fintype.card V := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective order horder
  let H : SimpleGraph (Fin (p.length + 1)) := G.comap order
  have hHpath : ∀ a b : Fin (p.length + 1),
      a.val + 1 = b.val → H.Adj a b := by
    intro a b hab
    change G.Adj (p.getVert a.val) (p.getVert b.val)
    have hb := b.isLt
    have hadj := p.adj_getVert_succ (i := a.val) (by omega)
    rw [hab] at hadj
    exact hadj
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
      _ = (H.neighborFinset i).card := Finset.card_image_of_injective _ horder
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
  have hcycle : (cycleGraph (p.length + 1)) ⊑ H := by
    by_contra hfree
    have hdeficit := path_endpoint_degree_sum_lt hlen H hHpath hfree
    rw [← hdegreeZero, ← hdegreeLast] at hdeficit
    have hsum := hpair u v huv
    omega
  have hspan : p.length + 1 = Fintype.card V := by
    apply Nat.le_antisymm horderCard
    by_contra hshort
    have hlarge : p.length + 1 < Fintype.card V := Nat.lt_of_not_ge hshort
    have hfree := maximum_path_cycle_free_on_image G hconn u v p hp hmax hlen hlarge
    exact hfree hcycle
  let e : Fin (p.length + 1) ↪ V := ⟨order, horder⟩
  obtain ⟨f⟩ := hcycle
  have hwhole : (cycleGraph (p.length + 1)) ⊑ G :=
    ⟨(SimpleGraph.Embedding.comap e G).toCopy.comp f⟩
  exact hspan ▸ hwhole

/-- The same generic degree premise supplies a literal Hamiltonian walk,
through Mathlib's existing cycle-Copy and cycle-length equivalences. -/
theorem exists_hamiltonian_cycle_of_degree_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hcard : 3 ≤ Fintype.card V)
    (hpair : ∀ x y : V, x ≠ y →
      Fintype.card V ≤ G.degree x + G.degree y) :
    ∃ (u : V) (c : G.Walk u u), c.IsHamiltonianCycle := by
  obtain ⟨u, c, hc, hlength⟩ :=
    (SimpleGraph.cycleGraph_isContained_iff (by omega : 2 < Fintype.card V)).mp
      (contains_spanning_cycle_of_degree_sum G hconn hcard hpair)
  exact ⟨u, c, SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr
    ⟨hc, hlength⟩⟩

end ErdosProblems.AntiRamseyCycleGenericHamiltonian
