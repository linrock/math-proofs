module

public import TightCoreEqualityOrdering1105
public import TightCoreBlockEdgeLedger1105
public import EvenInducedCarrier1105
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
Classify the SAME actual suffix carrier from its complete
exact deletion certificate. Containment, outsider degrees, carrier cardinality
and the original unordered d^2 population are derived, not supplied.
-/

noncomputable section

namespace ErdosProblems.PathUpperReduction.EvenActualSuffixClassification1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.TightCoreEqualityOrdering1105
open ErdosProblems.PathUpperReduction.TightCoreBlockEdgeLedger1105
open ErdosProblems.PathUpperReduction.EvenInducedCarrier1105

variable {V : Type*} [Fintype V]

local instance : DecidableEq V := Classical.decEq V

omit [Fintype V] in
/-- Every complete same-G certificate retains the entire terminal core. -/
theorem certificate_core_subset {G : SimpleGraph V} {d : ℕ}
    {S T : Finset V} (hcertificate : ExactCoreDeletion G d S T) : S ⊆ T := by
  classical
  induction hcertificate with
  | stop => exact fun _ hx => hx
  | delete T x hx hxS hdegree tail ih =>
      intro z hz
      exact (Finset.mem_erase.mp (ih hz)).2

omit [Fintype V] in
/-- Exact forward degrees imply the actual inside-carrier lower bound for
every outsider, including outsiders removed later in the certificate. -/
theorem certificate_outsider_degree_ge {G : SimpleGraph V} {d : ℕ}
    {S T : Finset V} (hcertificate : ExactCoreDeletion G d S T) :
    ∀ x ∈ T, x ∉ S → d ≤ withinDegree G T x := by
  classical
  induction hcertificate with
  | stop =>
      intro x hx hxS
      exact False.elim (hxS hx)
  | delete T y hy hyS hdegree tail ih =>
      intro x hx hxS
      by_cases hxy : x = y
      · subst x
        exact le_of_eq hdegree.symm
      · have hxTail : x ∈ T.erase y := Finset.mem_erase.mpr ⟨hxy, hx⟩
        have htailDegree := ih x hxTail hxS
        have hmono : withinDegree G (T.erase y) x ≤ withinDegree G T x := by
          unfold withinDegree
          exact Finset.card_le_card (Finset.filter_subset_filter
            (fun z => G.Adj x z) (Finset.erase_subset y T))
        exact htailDegree.trans hmono

/-- The actual last d outsiders have one common d-element core neighborhood
and no internal edges. The original full certificate supplies every degree
and edge-ledger premise of the finite classifier on the induced carrier T.
All adjacency conclusions concern the original G and pairs actually in T. -/
theorem actual_suffix_classification (G : SimpleGraph V) (d : ℕ)
    (S T : Finset V) (hd : 2 ≤ d)
    (hcertificate : ExactCoreDeletion G d S T)
    (hScard : S.card = d + 3) (hclique : G.IsClique (S : Set V))
    (houtside : (T \ S).card = d)
    (hfree : (cycleGraph (2 * d + 3)).Free G) :
    ∃ C : Finset V, C ⊆ S ∧ C.card = d ∧
      ∀ u ∈ T, ∀ v ∈ T, G.Adj u v ↔ u ≠ v ∧
        ((u ∈ S ∧ v ∈ S) ∨
          (u ∉ S ∧ v ∈ C) ∨
          (v ∉ S ∧ u ∈ C)) := by
  classical
  have hST : S ⊆ T := certificate_core_subset hcertificate
  have hTcard : T.card = 2 * d + 3 := by
    have hcard := Finset.card_sdiff_add_card_eq_card hST
    rw [houtside, hScard] at hcard
    omega
  let H := G.induce (T : Set V)
  let S' := liftSupport T S
  have hN : Fintype.card (T : Set V) = 2 * d + 3 := by
    rw [induced_carrier_card, hTcard]
  have hS'card : S'.card = d + 3 := by
    change (liftSupport T S).card = d + 3
    rw [liftSupport_card T S hST, hScard]
  have hclique' : H.IsClique (S' : Set (T : Set V)) :=
    clique_lift G T S hclique
  have houtsider' : ∀ x, x ∉ S' → d ≤ H.degree x := by
    intro x hxS'
    have hxS : x.val ∉ S := by
      intro hxS
      exact hxS' ((mem_liftSupport T S x).mpr hxS)
    change d ≤ (G.induce (T : Set V)).degree x
    rw [degree_induce_eq_withinDegree G T x]
    exact certificate_outsider_degree_ge hcertificate x.val x.property hxS
  have hfree' : (cycleGraph (2 * d + 3)).Free H :=
    cycle_free_induce G T (2 * d + 3) hfree
  have hledger := last_block_cross_edge_ledger hST hcertificate houtside
  have hledger' : d * d ≤ (coreCrossEdges H S' Finset.univ).card +
      (withinEdges H (Finset.univ \ S')).card := by
    have htransport := suffix_ledger_induce G T S hST
    change (coreCrossEdges H S' Finset.univ).card +
        (withinEdges H (Finset.univ \ S')).card =
      (coreCrossEdges G S T).card + (withinEdges G (T \ S)).card at htransport
    rw [htransport, hledger]
  have hsdiffEq : @SDiff.sdiff (Finset (T : Set V))
      (@Finset.instSDiff (T : Set V) (Classical.decEq _)) Finset.univ S' =
      Finset.univ \ S' := by
    ext x; simp only [Finset.mem_sdiff]
  rw [← hsdiffEq] at hledger'
  obtain ⟨hCcard, hCS, _hthree, _hOcard, hAdj⟩ :=
    EvenFiniteCarrierAdapter1105.actual_finite_contact_rigidity
      (by omega : 1 ≤ d) H hN S' hS'card hclique' houtsider' hfree' hledger'
  let C' := EvenFiniteCarrierAdapter1105.actualContacts H S'
  let f := Function.Embedding.subtype (· ∈ (T : Set V))
  let C := C'.map f
  have hmemC (x : (T : Set V)) : x.val ∈ C ↔ x ∈ C' := by
    change f x ∈ C'.map f ↔ x ∈ C'
    exact Finset.mem_map' f
  have hCsub : C ⊆ S := by
    intro z hzC
    obtain ⟨x, hxC, hxz⟩ := Finset.mem_map.mp hzC
    have hxS' : x ∈ S' := hCS hxC
    have hxS : x.val ∈ S := (mem_liftSupport T S x).mp hxS'
    change x.val = z at hxz
    exact hxz ▸ hxS
  have hCcount : C.card = d := by
    change (C'.map f).card = d
    rw [Finset.card_map]
    exact hCcard
  refine ⟨C, hCsub, hCcount, ?_⟩
  intro u hu v hv
  let u' : (T : Set V) := ⟨u, hu⟩
  let v' : (T : Set V) := ⟨v, hv⟩
  have hne : u' ≠ v' ↔ u ≠ v := by
    constructor
    · intro h huv
      apply h
      exact Subtype.ext huv
    · intro h huv
      exact h (congrArg Subtype.val huv)
  have hSu : u' ∈ S' ↔ u ∈ S := mem_liftSupport T S u'
  have hSv : v' ∈ S' ↔ v ∈ S := mem_liftSupport T S v'
  have hCu : u' ∈ C' ↔ u ∈ C := (hmemC u').symm
  have hCv : v' ∈ C' ↔ v ∈ C := (hmemC v').symm
  have h := hAdj u' v'
  change G.Adj u v ↔ u' ≠ v' ∧
    ((u' ∈ S' ∧ v' ∈ S') ∨
      (u' ∉ S' ∧ v' ∈ C') ∨
      (v' ∉ S' ∧ u' ∈ C')) at h
  simpa only [hne, hSu, hSv, hCu, hCv] using h

end ErdosProblems.PathUpperReduction.EvenActualSuffixClassification1105
