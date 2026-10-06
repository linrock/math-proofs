module

public import CycleClaimOneCycleComponent
public import CycleNewChoiceDegreeV2
public import CycleGenericLongPathSeedV2
public import CycleRotatingClaimTwoV4

@[expose] public section

/-!
Upper bound `≤ k - 1` on the vertex count of every connected component of the
selected NEW representative graph for `k ≥ 5` when the host coloring avoids
rainbow `C_k` copies and satisfies the high-NEW degree conditions.
-/

namespace ErdosProblems.AntiRamseyCycleSelectedComponentOrder

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleNewChoiceDegree
open ErdosProblems.AntiRamseyCycleClaimOneCycleComponent
open ErdosProblems.AntiRamseyCycleGenericLongPathSeed
open ErdosProblems.AntiRamseyCycleRotatingClaimTwo

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Under the original high-NEW, distinct-pair NEW and host no-rainbow
conditions, every component of the same arbitrary selected graph has at
most the old cycle order. The oversized branch derives its old-cycle
exclusion in that component, then obtains its path inside that component. -/
theorem selected_component_order_le {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (hnew : ∀ v : Fin n, 2 ≤ (newColors χ v).card)
    (hpair : ∀ u v : Fin n, u ≠ v →
      m + 2 ≤ (newColors χ u).card + (newColors χ v).card)
    (hno : ∀ f : (cycleGraph (m + 3)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (D : (selectedGraph χ r).ConnectedComponent) :
    D.supp.ncard ≤ m + 2 := by
  classical
  by_contra hsmall
  have hlarge : m + 2 < D.supp.ncard := Nat.lt_of_not_ge hsmall
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
  have hcard : m + 3 ≤ Fintype.card D := by
    rw [hcardEq]
    omega
  have hmin : ∀ x : D, 2 ≤ H.degree x := by
    intro x
    exact le_trans (hnew x.val) (hnewdegree x)
  have hpairD : ∀ x y : D, x ≠ y →
      (m + 3) - 1 ≤ H.degree x + H.degree y := by
    intro x y hxy
    have hval : x.val ≠ y.val := fun heq => hxy (Subtype.ext heq)
    have hsum := hpair x.val y.val hval
    have hx := hnewdegree x
    have hy := hnewdegree y
    omega
  obtain ⟨q, hq, hqpath⟩ := exists_ordered_path_of_degree_bounds
    (k := m + 3) (by omega) H D.connected_toSimpleGraph hcard hmin hpairD
  let p : Fin (m + 2) → Fin n := fun i => (q (Fin.castSucc i)).val
  have hp : Function.Injective p := by
    intro i j hij
    have hsub : q (Fin.castSucc i) = q (Fin.castSucc j) := Subtype.ext hij
    exact Fin.castSucc_injective _ (hq hsub)
  have hpath : ∀ i : Fin (m + 1),
      (selectedGraph χ r).Adj (p (Fin.castSucc i)) (p (Fin.succ i)) := by
    intro i
    exact hqpath (Fin.castSucc (Fin.castSucc i)) (Fin.castSucc (Fin.succ i)) rfl
  have hpD : ∀ i : Fin (m + 2), p i ∈ D.supp.toFinset := by
    intro i
    exact Set.mem_toFinset.mpr (q (Fin.castSucc i)).property
  have hnoD : ∀ cyc : (cycleGraph (m + 2)).Copy (selectedGraph χ r),
      ¬ (∀ i : Fin (m + 2), cyc i ∈ D.supp.toFinset) := by
    intro cyc hinside
    apply oversized_component_excludes_selected_cycle (m := m + 1)
      (by omega) χ r hnew hno D hlarge cyc
    intro i
    exact Set.mem_toFinset.mp (hinside i)
  have hclosed : ∀ v : Fin n, v ∈ D.supp.toFinset → ∀ w : Fin n,
      (selectedGraph χ r).Adj v w → w ∈ D.supp.toFinset := by
    intro v hv w hvw
    exact Set.mem_toFinset.mpr
      (D.mem_supp_of_adj_mem_supp (Set.mem_toFinset.mp hv) hvw)
  exact ordered_path_contradiction hm χ r p hp hpath hno
    D.supp.toFinset hpD hnoD hpair hclosed

/-- The same bound stated with the original cycle parameter k >= 5. -/
theorem selected_component_order_le_original {k : ℕ} (hk : 5 ≤ k)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (hnew : ∀ v : Fin n, 2 ≤ (newColors χ v).card)
    (hpair : ∀ u v : Fin n, u ≠ v →
      k - 1 ≤ (newColors χ u).card + (newColors χ v).card)
    (hno : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (D : (selectedGraph χ r).ConnectedComponent) :
    D.supp.ncard ≤ k - 1 := by
  have hm : 2 ≤ k - 3 := by omega
  have hpairm : ∀ u v : Fin n, u ≠ v →
      (k - 3) + 2 ≤ (newColors χ u).card + (newColors χ v).card := by
    intro u v huv
    have hbound := hpair u v huv
    omega
  have horder : (k - 3) + 3 = k := by omega
  have hnom : ∀ f : (cycleGraph ((k - 3) + 3)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ := by
    exact horder.symm ▸ hno
  have hbound := selected_component_order_le hm χ r hnew hpairm hnom D
  omega

end ErdosProblems.AntiRamseyCycleSelectedComponentOrder
