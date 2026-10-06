module

public import PathUpperOriginalCutFamilyV2

@[expose] public section

/-!
Preserve every original color owner in the processed
whole prefix once the FULL selected tail, before any later cuts, is edgeless. No proper-prefix conclusion, cardinal lower bound, numeric induction, connected
full representative or original anti-Ramsey upper bound is asserted.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- With the literal FULL tail edgeless, all selected
owners of every original color lie wholly in the earlier vertices or current
WHOLE component. Earlier and current cut colors are included without exception. Only the exact original slot partition and actual component definition are used. -/
theorem original_owner_inside_processed_prefix_of_edgeless_tail
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ R U W) (x : Fin n)
    (htail : (selectedGraph χ R).induce (W \ componentSupport χ R x) = ⊥)
    (c : Fin q) :
    EdgeInside (Wᶜ ∪ componentSupport χ R x) (R.edge c).val := by
  by_cases hc : c ∈ U
  · intro z hz
    exact Or.inl (hpartition.removed_outside c hc z hz)
  · have hinside : EdgeInside W (R.edge c).val :=
      hpartition.eligible_inside c hc
    have hselected : (R.edge c).val ∈ (selectedGraph χ R).edgeSet := by
      rw [selectedGraph_edgeSet]
      exact ⟨c, rfl⟩
    obtain ⟨⟨u, v⟩, huv⟩ := Sym2.mk_surjective (R.edge c).val
    have hadj : (selectedGraph χ R).Adj u v := by
      rw [← huv] at hselected
      exact hselected
    have huOwner : u ∈ (R.edge c).val := by
      rw [← huv]
      exact Sym2.mem_mk_left u v
    have hvOwner : v ∈ (R.edge c).val := by
      rw [← huv]
      exact Sym2.mem_mk_right u v
    have huW : u ∈ W := hinside u huOwner
    have hvW : v ∈ W := hinside v hvOwner
    have hcomponent : u ∈ componentSupport χ R x ↔
        v ∈ componentSupport χ R x := by
      change u ∈ ((selectedGraph χ R).connectedComponentMk x).supp ↔
        v ∈ ((selectedGraph χ R).connectedComponentMk x).supp
      exact ((selectedGraph χ R).connectedComponentMk x).mem_supp_congr_adj hadj
    by_cases huX : u ∈ componentSupport χ R x
    · have hvX : v ∈ componentSupport χ R x := hcomponent.mp huX
      rw [← huv]
      intro z hz
      apply Or.inr
      rcases Sym2.mem_iff.mp hz with hzu | hzv
      · rw [hzu]
        exact huX
      · rw [hzv]
        exact hvX
    · have hvX : v ∉ componentSupport χ R x :=
        fun hv => huX (hcomponent.mpr hv)
      let uT : {z : Fin n // z ∈ W \ componentSupport χ R x} := ⟨u, huW, huX⟩
      let vT : {z : Fin n // z ∈ W \ componentSupport χ R x} := ⟨v, hvW, hvX⟩
      have htailAdj : ((selectedGraph χ R).induce
          (W \ componentSupport χ R x)).Adj uT vT := by
        change (selectedGraph χ R).Adj u v
        exact hadj
      have hfalse : False := by
        simp only [htail, SimpleGraph.bot_adj] at htailAdj
      exact hfalse.elim

/-- Stage method spelling for the same exact confinement. The premise concerns the FULL selected graph on the unprocessed tail, not the
final globally cut graph. Its source can be the uncut-tail endpoint theorem. -/
theorem OriginalResidualCutStage.owner_inside_processed_prefix
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x)
    (htail : (selectedGraph χ R).induce (W \ componentSupport χ R x) = ⊥)
    (c : Fin q) :
    EdgeInside (Wᶜ ∪ componentSupport χ R x) (R.edge c).val :=
  original_owner_inside_processed_prefix_of_edgeless_tail
    χ R U W S.partition x htail c

/-- Every SAME original color is realized by a literal
original complete-host edge wholly in the processed prefix. No reduced palette
or cardinality assumption occurs. Properness and m ≥ k are separate obligations. -/
theorem OriginalResidualCutStage.every_color_in_processed_prefix
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x)
    (htail : (selectedGraph χ R).induce (W \ componentSupport χ R x) = ⊥)
    (c : Fin q) :
    ∃ e : HostEdge n,
      EdgeInside (Wᶜ ∪ componentSupport χ R x) e.val ∧ χ e = c :=
  ⟨R.edge c, S.owner_inside_processed_prefix htail c, R.color_eq c⟩

end ErdosProblems.PathUpperReduction
