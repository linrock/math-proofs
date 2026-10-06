module

public import EvenFiniteCarrierAdapter1105
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Copy

@[expose] public section

/-!
Actual induced-carrier transport, including every vertex
of W and every isolate. The original graph, its support and its canonical
unordered edge filters are used literally. The restoration insertion ledger is a separate caller obligation.
-/

noncomputable section

namespace ErdosProblems.PathUpperReduction.EvenInducedCarrier1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.TightCoreBlockEdgeLedger1105

variable {V : Type*} [Fintype V]

local instance : DecidableEq V := Classical.decEq V

noncomputable instance graph_neighborSet_fintype {A : Type*} [Finite A]
    (G : SimpleGraph A) (x : A) : Fintype (G.neighborSet x) := Fintype.ofFinite _

/-- Lift an actual ambient support to the whole induced carrier W. -/
noncomputable def liftSupport (W A : Finset V) : Finset (W : Set V) := by
  classical
  exact Finset.univ.filter (fun x => x.val ∈ A)

omit [Fintype V] in
@[simp] theorem mem_liftSupport (W A : Finset V) (x : (W : Set V)) :
    x ∈ liftSupport W A ↔ x.val ∈ A := by
  classical
  simp only [liftSupport, Finset.mem_filter, Finset.mem_univ, true_and]

omit [Fintype V] in
@[simp] theorem liftSupport_self (W : Finset V) :
    liftSupport W W = Finset.univ := by
  classical
  ext x
  constructor
  · intro _hx
    exact Finset.mem_univ x
  · intro _hx
    exact (mem_liftSupport W W x).mpr x.property

omit [Fintype V] in
theorem liftSupport_sdiff (W A B : Finset V) :
    liftSupport W (A \ B) = liftSupport W A \ liftSupport W B := by
  classical
  ext x
  simp only [mem_liftSupport, Finset.mem_sdiff]

omit [Fintype V] in
/-- Projection is a genuine bijection onto A when A is inside W. -/
theorem liftSupport_map (W A : Finset V) (hAW : A ⊆ W) :
    (liftSupport W A).map (Function.Embedding.subtype (· ∈ (W : Set V))) = A := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact (mem_liftSupport W A y).mp hy
  · intro hx
    exact Finset.mem_map.mpr
      ⟨⟨x, hAW hx⟩, (mem_liftSupport W A ⟨x, hAW hx⟩).mpr hx, rfl⟩

omit [Fintype V] in
theorem liftSupport_card (W A : Finset V) (hAW : A ⊆ W) :
    (liftSupport W A).card = A.card := by
  classical
  have h := congrArg Finset.card (liftSupport_map W A hAW)
  rw [Finset.card_map] at h
  exact h

omit [Fintype V] in
/-- The full induced carrier has its actual support cardinality. -/
theorem induced_carrier_card (W : Finset V) :
    Fintype.card (W : Set V) = W.card := Fintype.card_coe W

omit [Fintype V] in
theorem clique_lift (G : SimpleGraph V) (W S : Finset V)
    (hclique : G.IsClique (S : Set V)) :
    (G.induce (W : Set V)).IsClique (liftSupport W S : Set (W : Set V)) := by
  classical
  intro u hu v hv huv
  exact hclique ((mem_liftSupport W S u).mp hu) ((mem_liftSupport W S v).mp hv)
    (fun hval => huv (Subtype.ext hval))

omit [Fintype V] in
/-- Noninduced copy freedom is inherited through the actual subtype projection. -/
theorem cycle_free_induce (G : SimpleGraph V) (W : Finset V) (m : ℕ)
    (hfree : (cycleGraph m).Free G) :
    (cycleGraph m).Free (G.induce (W : Set V)) := by
  rintro ⟨f⟩
  exact hfree ⟨(SimpleGraph.Copy.induce G (W : Set V)).comp f⟩

/-- Actual restricted degree is the ambient original neighbor filter count. -/
theorem degree_induce_eq_withinDegree (G : SimpleGraph V) (W : Finset V)
    (u : (W : Set V)) :
    (G.induce (W : Set V)).degree u = withinDegree G W u.val := by
  classical
  change ((G.induce (W : Set V)).neighborFinset u).card =
    (W.filter (fun z => G.Adj u.val z)).card
  apply Finset.card_bij (fun v _hv => v.val)
  · intro v hv
    have hadj : (G.induce (W : Set V)).Adj u v :=
      (SimpleGraph.mem_neighborFinset (G.induce (W : Set V)) u v).mp hv
    exact Finset.mem_filter.mpr ⟨v.property, hadj⟩
  · intro v₁ _hv₁ v₂ _hv₂ hval
    exact Subtype.ext hval
  · intro z hz
    obtain ⟨hzW, hadj⟩ := Finset.mem_filter.mp hz
    let v : (W : Set V) := ⟨z, hzW⟩
    have hv : v ∈ (G.induce (W : Set V)).neighborFinset u :=
      (SimpleGraph.mem_neighborFinset (G.induce (W : Set V)) u v).mpr hadj
    exact ⟨v, hv, rfl⟩

omit [Fintype V] in
/-- Contacts in the induced graph have an actual ORIGINAL witness in W.
This does not equate them to ambient contacts witnessed outside W. -/
theorem actualContacts_lift_iff (G : SimpleGraph V) (W S : Finset V)
    (u : (W : Set V)) :
    u ∈ EvenFiniteCarrierAdapter1105.actualContacts
        (G.induce (W : Set V)) (liftSupport W S) ↔
      u.val ∈ S ∧ ∃ v ∈ W, v ∉ S ∧ G.Adj v u.val := by
  classical
  unfold EvenFiniteCarrierAdapter1105.actualContacts
  simp only [Finset.mem_filter]
  constructor
  · intro hu
    rcases hu with ⟨huS, v, hvS, hvu⟩
    refine ⟨(mem_liftSupport W S u).mp huS, v.val, v.property, ?_, hvu⟩
    exact fun hv => hvS ((mem_liftSupport W S v).mpr hv)
  · rintro ⟨huS, v, hvW, hvS, hvu⟩
    exact ⟨(mem_liftSupport W S u).mpr huS,
      ⟨v, hvW⟩, (fun hv => hvS ((mem_liftSupport W S ⟨v, hvW⟩).mp hv)), hvu⟩

omit [Fintype V] in
theorem projected_edge_subset_iff (W A : Finset V)
    (e : Sym2 (W : Set V)) :
    (∀ z ∈ (Function.Embedding.subtype (· ∈ (W : Set V))).sym2Map e, z ∈ A) ↔
      (∀ z ∈ e, z ∈ liftSupport W A) := by
  refine Sym2.inductionOn e ?_
  intro x y
  simp only [Function.Embedding.sym2Map_apply, Sym2.map_mk, Sym2.mem_iff,
    mem_liftSupport]
  constructor
  · intro h z hz
    rcases hz with hzx | hzy
    · rw [hzx]; exact h x.val (Or.inl rfl)
    · rw [hzy]; exact h y.val (Or.inr rfl)
  · intro h z hz
    rcases hz with hzx | hzy
    · rw [hzx]; exact h x (Or.inl rfl)
    · rw [hzy]; exact h y (Or.inr rfl)

/-- Projection of an actual induced within-support edge population is exactly
the ambient original population, not just an inequality of counts. -/
theorem withinEdges_lift_map (G : SimpleGraph V) (W A : Finset V)
    (hAW : A ⊆ W) :
    (withinEdges (G.induce (W : Set V)) (liftSupport W A)).map
        (Function.Embedding.subtype (· ∈ (W : Set V))).sym2Map = withinEdges G A := by
  classical
  unfold withinEdges
  ext e
  simp only [Finset.mem_map, Finset.mem_filter, mem_edgeFinset,
    Finset.subset_iff, Sym2.mem_toFinset]
  constructor
  · rintro ⟨t, ⟨htG, htA⟩, rfl⟩
    refine ⟨?_, (projected_edge_subset_iff W A t).mpr htA⟩
    revert htG
    refine Sym2.inductionOn t ?_
    intro u v huv
    exact huv
  · revert e
    intro e
    refine Sym2.inductionOn e ?_
    intro x y
    rintro ⟨hxy, hsub⟩
    have hxA : x ∈ A := hsub (Sym2.mem_iff.mpr (Or.inl rfl))
    have hyA : y ∈ A := hsub (Sym2.mem_iff.mpr (Or.inr rfl))
    let u : (W : Set V) := ⟨x, hAW hxA⟩
    let v : (W : Set V) := ⟨y, hAW hyA⟩
    refine ⟨s(u, v), ⟨hxy, ?_⟩, rfl⟩
    exact (projected_edge_subset_iff W A s(u, v)).mp hsub

theorem withinEdges_lift_card (G : SimpleGraph V) (W A : Finset V)
    (hAW : A ⊆ W) :
    (withinEdges (G.induce (W : Set V)) (liftSupport W A)).card =
      (withinEdges G A).card := by
  classical
  have h := congrArg Finset.card (withinEdges_lift_map G W A hAW)
  rw [Finset.card_map] at h
  exact h

/-- Canonical original unordered cross edges project exactly, with BOTH
exclusion filters preserved on the actual supports. -/
theorem coreCrossEdges_lift_map (G : SimpleGraph V) (W S U : Finset V)
    (_hSW : S ⊆ W) (hUW : U ⊆ W) :
    (coreCrossEdges (G.induce (W : Set V)) (liftSupport W S) (liftSupport W U)).map
        (Function.Embedding.subtype (· ∈ (W : Set V))).sym2Map =
      coreCrossEdges G S U := by
  classical
  let f := Function.Embedding.subtype (· ∈ (W : Set V))
  let H := G.induce (W : Set V)
  have hdiff (e : Sym2 (W : Set V)) :
      (∀ z ∈ f.sym2Map e, z ∈ U ∧ z ∉ S) ↔
        (∀ z ∈ e, z ∈ liftSupport W U ∧ z ∉ liftSupport W S) := by
    have hp := projected_edge_subset_iff W (U \ S) e
    simpa only [liftSupport_sdiff, Finset.mem_sdiff] using hp
  ext e
  unfold coreCrossEdges nonCoreEdges
  simp only [Finset.mem_map, Finset.mem_filter, Finset.subset_iff, Sym2.mem_toFinset,
    Finset.mem_sdiff]
  constructor
  · intro he
    rcases he with ⟨t, ⟨⟨htWithin, htNotCore⟩, htNotOutside⟩, rfl⟩
    have hmappedWithin : f.sym2Map t ∈ withinEdges G U := by
      rw [← withinEdges_lift_map G W U hUW]
      exact Finset.mem_map.mpr ⟨t, htWithin, rfl⟩
    have hmappedNotCore : ¬ ∀ z ∈ f.sym2Map t, z ∈ S := by
      intro hS
      exact htNotCore ((projected_edge_subset_iff W S t).mp hS)
    have hmappedNotOutside : ¬ ∀ z ∈ f.sym2Map t, z ∈ U ∧ z ∉ S := by
      intro hO
      exact htNotOutside ((hdiff t).mp hO)
    exact ⟨⟨hmappedWithin, hmappedNotCore⟩, hmappedNotOutside⟩
  · intro he
    rcases he with ⟨⟨heWithin, heNotCore⟩, heNotOutside⟩
    rw [← withinEdges_lift_map G W U hUW] at heWithin
    obtain ⟨t, htWithin, rfl⟩ := Finset.mem_map.mp heWithin
    have htNotCore : ¬ ∀ z ∈ t, z ∈ liftSupport W S := by
      intro htS
      exact heNotCore ((projected_edge_subset_iff W S t).mpr htS)
    have htNotOutside : ¬ ∀ z ∈ t, z ∈ liftSupport W U ∧ z ∉ liftSupport W S := by
      intro htO
      exact heNotOutside ((hdiff t).mpr htO)
    exact ⟨t, ⟨⟨htWithin, htNotCore⟩, htNotOutside⟩, rfl⟩

theorem coreCrossEdges_lift_card (G : SimpleGraph V) (W S U : Finset V)
    (hSW : S ⊆ W) (hUW : U ⊆ W) :
    (coreCrossEdges (G.induce (W : Set V)) (liftSupport W S) (liftSupport W U)).card =
      (coreCrossEdges G S U).card := by
  classical
  have h := congrArg Finset.card (coreCrossEdges_lift_map G W S U hSW hUW)
  rw [Finset.card_map] at h
  exact h

/-- The exact original suffix population in the induced carrier, with no
supplied transport equality or duplicated outside-edge incidence count. -/
theorem suffix_ledger_induce (G : SimpleGraph V) (W S : Finset V)
    (hSW : S ⊆ W) :
    (coreCrossEdges (G.induce (W : Set V)) (liftSupport W S) Finset.univ).card +
        (withinEdges (G.induce (W : Set V))
          (Finset.univ \ liftSupport W S)).card =
      (coreCrossEdges G S W).card + (withinEdges G (W \ S)).card := by
  classical
  have hcross := coreCrossEdges_lift_card G W S W hSW (Finset.Subset.refl W)
  rw [liftSupport_self] at hcross
  have hout := withinEdges_lift_card G W (W \ S) Finset.sdiff_subset
  rw [liftSupport_sdiff, liftSupport_self] at hout
  rw [hcross, hout]

end ErdosProblems.PathUpperReduction.EvenInducedCarrier1105
