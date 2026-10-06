module

public import CycleSelectedComponentHamiltonianV4
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-!
Spanning component copies give host cyclic indices
covering their exact component support, and comap degrees equal original
selected degrees. Distinct actual components give every cross-index vertex
inequality and the original cross-degree lower bound. No Claim3 constancy
or original numerical anti-Ramsey conclusion is asserted.
-/

namespace ErdosProblems.AntiRamseyCycleComponentCyclicIndex

open SimpleGraph
open scoped Classical
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleNewChoiceDegree
open ErdosProblems.AntiRamseyCycleSelectedComponentHamiltonian

/-- An injective index map onto an actual component preserves the full
original degree at every indexed vertex. Component closure supplies every
original neighbor; degree equality is proved rather than assumed. -/
theorem degree_comap_eq_of_component_range
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (D : G.ConnectedComponent) {t : ℕ} (A : Fin t → V)
    (hinj : Function.Injective A) (hrange : Set.range A = D.supp)
    (i : Fin t) :
    (G.comap A).degree i = G.degree (A i) := by
  classical
  let f : G.comap A ↪g G := SimpleGraph.Embedding.comap ⟨A, hinj⟩ G
  let e : G.comap A ≃g G.induce (Set.range A) := f.isoInduceRange
  have hsubset : G.neighborSet (e i).val ⊆ Set.range A := by
    intro v hv
    rw [hrange]
    have hi : (e i).val ∈ D.supp := by
      rw [← hrange]
      exact (e i).property
    exact D.mem_supp_of_adj_mem_supp hi hv
  have hcanonical := SimpleGraph.degree_induce_of_neighborSet_subset
    (G := G) (s := Set.range A) (v := e i) hsubset
  have hfull : (G.induce (Set.range A)).degree (e i) =
      G.degree (e i).val := by
    exact (congrArg
      (fun inst : Fintype ((G.induce (Set.range A)).neighborSet (e i)) =>
        @SimpleGraph.degree _ (G.induce (Set.range A)) (e i) inst)
      (Subsingleton.elim _ _)).trans
      (hcanonical.trans (congrArg
        (fun inst : Fintype (G.neighborSet (e i).val) =>
          @SimpleGraph.degree _ G (e i).val inst)
        (Subsingleton.elim _ _)))
  exact (e.degree_eq i).symm.trans hfull

/-- A copy whose order equals the actual finite component order covers the
whole component. Its original host map supplies a cyclic order and the exact
full-degree comap graph, for an arbitrary finite original graph. -/
theorem spanning_component_copy_host_index
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (D : G.ConnectedComponent)
    (c : (cycleGraph D.supp.ncard).Copy D.toSimpleGraph) :
    ∃ A : Fin D.supp.ncard → V,
      Function.Injective A ∧
      (∀ x : D, ∃ i : Fin D.supp.ncard, A i = x.val) ∧
      Set.range A = D.supp ∧
      cycleGraph D.supp.ncard ≤ G.comap A ∧
      ∀ i : Fin D.supp.ncard, (G.comap A).degree i = G.degree (A i) := by
  classical
  let : Fintype D := Fintype.ofFinite D
  have hcard : Fintype.card D = D.supp.ncard := by
    calc
      Fintype.card D = Nat.card D := Fintype.card_eq_nat_card
      _ = D.supp.ncard := Nat.card_coe_set_eq D.supp
  have hbij : Function.Bijective (c : Fin D.supp.ncard → D) :=
    (Fintype.bijective_iff_injective_and_card c).mpr
      ⟨c.injective, by simpa only [Fintype.card_fin] using hcard.symm⟩
  let A : Fin D.supp.ncard → V := fun i => (c i).val
  have hinj : Function.Injective A := by
    intro i j hij
    exact c.injective (Subtype.ext hij)
  have honto : ∀ x : D, ∃ i : Fin D.supp.ncard, A i = x.val := by
    intro x
    obtain ⟨i, hi⟩ := hbij.2 x
    exact ⟨i, congrArg Subtype.val hi⟩
  have hrange : Set.range A = D.supp := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact (c i).property
    · intro hv
      obtain ⟨i, hi⟩ := honto ⟨v, hv⟩
      exact ⟨i, hi⟩
  have hcycle : cycleGraph D.supp.ncard ≤ G.comap A := by
    intro i j hij
    exact c.toHom.map_rel hij
  refine ⟨A, hinj, honto, hrange, hcycle, ?_⟩
  intro i
  exact degree_comap_eq_of_component_range G D A hinj hrange i

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- The original selected-component hypotheses furnish its literal host
cyclic index and indexed NEW-to-degree lower bound, with all original size
bounds. The choice and coloring are arbitrary. -/
theorem selected_component_cyclic_index
    {k : ℕ} (hk : 5 ≤ k)
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
    ∃ A : Fin D.supp.ncard → Fin n,
      Function.Injective A ∧
      (∀ x : D, ∃ i : Fin D.supp.ncard, A i = x.val) ∧
      Set.range A = D.supp ∧
      cycleGraph D.supp.ncard ≤ (selectedGraph χ r).comap A ∧
      (∀ i : Fin D.supp.ncard,
        ((selectedGraph χ r).comap A).degree i = (selectedGraph χ r).degree (A i)) ∧
      ∀ i : Fin D.supp.ncard,
        (newColors χ (A i)).card ≤ ((selectedGraph χ r).comap A).degree i := by
  obtain ⟨h3, hlower, hupper, ⟨c⟩, _⟩ :=
    selected_component_size_bounds_and_hamiltonian_cycle hk χ r hnew hpair hno D
  obtain ⟨A, hinj, honto, hrange, hcycle, hdegree⟩ :=
    spanning_component_copy_host_index (selectedGraph χ r) D c
  refine ⟨h3, hlower, hupper, A, hinj, honto, hrange, hcycle, hdegree, ?_⟩
  intro i
  rw [hdegree i]
  exact newChoice_degree_ge_newColors χ r (A i)

/-- Two distinct actual selected components yield two whole-support cyclic
host maps. Every cross-index vertex pair is distinct, so the original NEW
pair bound gives the full indexed cross-degree bound without an added degree,
surjectivity, component-disjointness or cyclic-order premise. -/
theorem distinct_components_cyclic_indices_cross_degree
    {k : ℕ} (hk : 5 ≤ k)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (hnew : ∀ v : Fin n, 2 ≤ (newColors χ v).card)
    (hpair : ∀ u v : Fin n, u ≠ v →
      k - 1 ≤ (newColors χ u).card + (newColors χ v).card)
    (hno : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (D E : (selectedGraph χ r).ConnectedComponent) (hDE : D ≠ E) :
    3 ≤ D.supp.ncard ∧ D.supp.ncard ≤ k - 1 ∧
    k + 1 ≤ 2 * D.supp.ncard ∧
    3 ≤ E.supp.ncard ∧ E.supp.ncard ≤ k - 1 ∧
    k + 1 ≤ 2 * E.supp.ncard ∧
    ∃ (A : Fin D.supp.ncard → Fin n) (B : Fin E.supp.ncard → Fin n),
      Function.Injective A ∧ Function.Injective B ∧
      (∀ x : D, ∃ i : Fin D.supp.ncard, A i = x.val) ∧
      (∀ y : E, ∃ j : Fin E.supp.ncard, B j = y.val) ∧
      Set.range A = D.supp ∧ Set.range B = E.supp ∧
      cycleGraph D.supp.ncard ≤ (selectedGraph χ r).comap A ∧
      cycleGraph E.supp.ncard ≤ (selectedGraph χ r).comap B ∧
      (∀ i : Fin D.supp.ncard,
        ((selectedGraph χ r).comap A).degree i = (selectedGraph χ r).degree (A i)) ∧
      (∀ j : Fin E.supp.ncard,
        ((selectedGraph χ r).comap B).degree j = (selectedGraph χ r).degree (B j)) ∧
      (∀ i : Fin D.supp.ncard, ∀ j : Fin E.supp.ncard, A i ≠ B j) ∧
      ∀ i : Fin D.supp.ncard, ∀ j : Fin E.supp.ncard,
        k - 1 ≤ ((selectedGraph χ r).comap A).degree i +
          ((selectedGraph χ r).comap B).degree j := by
  obtain ⟨h3A, hlowerA, hupperA, A, hinjA, hontoA, hrangeA, hcycleA, hdegreeA,
      hnewdegreeA⟩ := selected_component_cyclic_index hk χ r hnew hpair hno D
  obtain ⟨h3B, hlowerB, hupperB, B, hinjB, hontoB, hrangeB, hcycleB, hdegreeB,
      hnewdegreeB⟩ := selected_component_cyclic_index hk χ r hnew hpair hno E
  have hdistinct : ∀ i : Fin D.supp.ncard, ∀ j : Fin E.supp.ncard, A i ≠ B j := by
    intro i j hij
    have hi : A i ∈ D.supp := by
      rw [← hrangeA]
      exact ⟨i, rfl⟩
    have hj : B j ∈ E.supp := by
      rw [← hrangeB]
      exact ⟨j, rfl⟩
    exact hDE (SimpleGraph.ConnectedComponent.eq_of_common_vertex hi (hij.symm ▸ hj))
  have hcross : ∀ i : Fin D.supp.ncard, ∀ j : Fin E.supp.ncard,
      k - 1 ≤ ((selectedGraph χ r).comap A).degree i +
        ((selectedGraph χ r).comap B).degree j := by
    intro i j
    have hsum := hpair (A i) (B j) (hdistinct i j)
    have hi := hnewdegreeA i
    have hj := hnewdegreeB j
    omega
  exact ⟨h3A, hupperA, hlowerA, h3B, hupperB, hlowerB,
    A, B, hinjA, hinjB, hontoA, hontoB, hrangeA, hrangeB,
    hcycleA, hcycleB, hdegreeA, hdegreeB, hdistinct, hcross⟩

end ErdosProblems.AntiRamseyCycleComponentCyclicIndex
