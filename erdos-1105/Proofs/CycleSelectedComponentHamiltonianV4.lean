module

public import CycleSelectedComponentOrderV5
public import CycleGenericHamiltonianV3

@[expose] public section

/-!
size and Hamiltonicity application on the same selected component. Arbitrary valid NEW choices and original
coloring/NEW quantifiers are preserved; this file asserts no verification.
-/

namespace ErdosProblems.AntiRamseyCycleSelectedComponentHamiltonian

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleNewChoiceDegree
open ErdosProblems.AntiRamseyCycleSelectedComponentOrder
open ErdosProblems.AntiRamseyCycleGenericHamiltonian

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- The original high-NEW and distinct-pair conditions give both size bounds
and a spanning selected cycle in each component of the same arbitrary choice.
The Hamiltonian walk is on its actual component support subtype. -/
theorem selected_component_size_bounds_and_hamiltonian_cycle {k : ℕ} (hk : 5 ≤ k)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (hnew : ∀ v : Fin n, 2 ≤ (newColors χ v).card)
    (hpair : ∀ u v : Fin n, u ≠ v →
      k - 1 ≤ (newColors χ u).card + (newColors χ v).card)
    (hno : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (D : (selectedGraph χ r).ConnectedComponent) :
    3 ≤ D.supp.ncard ∧
    k + 1 ≤ 2 * D.supp.ncard ∧
    D.supp.ncard ≤ k - 1 ∧
    (cycleGraph D.supp.ncard) ⊑ D.toSimpleGraph ∧
    ∃ (u : D) (c : D.toSimpleGraph.Walk u u), c.IsHamiltonianCycle := by
  classical
  let G : SimpleGraph (Fin n) := selectedGraph χ r
  let H : SimpleGraph D := D.toSimpleGraph
  let : DecidableRel H.Adj := fun x y => Classical.propDecidable (H.Adj x y)
  let (x : D) : Fintype (H.neighborSet x) :=
    Subtype.fintype (Membership.mem (H.neighborSet x))
  have hdegree (x : D) : H.degree x = G.degree x.val := by
    have hsubset : G.neighborSet x.val ⊆ D.supp := by
      intro y hy
      exact D.mem_supp_of_adj_mem_supp x.property hy
    have hcanonical := SimpleGraph.degree_induce_of_neighborSet_subset
      (G := G) (s := D.supp) (v := x) hsubset
    exact (congrArg
      (fun f : Fintype ((G.induce D.supp).neighborSet x) =>
        @SimpleGraph.degree _ (G.induce D.supp) x f)
      (Subsingleton.elim _ _)).trans
      (hcanonical.trans (congrArg
        (fun f : Fintype (G.neighborSet x.val) => @SimpleGraph.degree _ G x.val f)
        (Subsingleton.elim _ _)))
  have hnewdegree (x : D) : (newColors χ x.val).card ≤ H.degree x := by
    rw [hdegree x]
    exact newChoice_degree_ge_newColors χ r x.val
  have hcardEq : Fintype.card D = D.supp.ncard := by
    calc
      Fintype.card D = Nat.card D := Fintype.card_eq_nat_card
      _ = D.supp.ncard := Nat.card_coe_set_eq D.supp
  have hcard3 : 3 ≤ Fintype.card D := by
    obtain ⟨x⟩ := D.connected_toSimpleGraph.nonempty
    have hxnew := hnew x.val
    have hxdegree := hnewdegree x
    have hlt := H.degree_lt_card_verts x
    omega
  have hsmall : k + 1 ≤ 2 * Fintype.card D := by
    obtain ⟨x, y, hxy⟩ := Fintype.exists_pair_of_one_lt_card
      (show 1 < Fintype.card D by omega)
    have hval : x.val ≠ y.val := fun heq => hxy (Subtype.ext heq)
    have hsum := hpair x.val y.val hval
    have hx := hnewdegree x
    have hy := hnewdegree y
    have hxlt := H.degree_lt_card_verts x
    have hylt := H.degree_lt_card_verts y
    omega
  have hupper := selected_component_order_le_original hk χ r hnew hpair hno D
  have hupperCard : Fintype.card D ≤ k - 1 := by
    rw [hcardEq]
    exact hupper
  have hdegreepair : ∀ x y : D, x ≠ y →
      Fintype.card D ≤ H.degree x + H.degree y := by
    intro x y hxy
    have hval : x.val ≠ y.val := fun heq => hxy (Subtype.ext heq)
    have hsum := hpair x.val y.val hval
    have hx := hnewdegree x
    have hy := hnewdegree y
    omega
  have hspanning := contains_spanning_cycle_of_degree_sum
    H D.connected_toSimpleGraph hcard3 hdegreepair
  have hhamiltonian := exists_hamiltonian_cycle_of_degree_sum
    H D.connected_toSimpleGraph hcard3 hdegreepair
  refine ⟨?_, ?_, hupper, ?_, hhamiltonian⟩
  · simpa only [hcardEq] using hcard3
  · simpa only [hcardEq] using hsmall
  · exact hcardEq ▸ hspanning

end ErdosProblems.AntiRamseyCycleSelectedComponentHamiltonian
