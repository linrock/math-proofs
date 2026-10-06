module

public import PathUpperOriginalUncutTailJoin

@[expose] public section

/-!
Original full-R whole-component ordering and the earlier
retained-edgeless interface. No component order, earlier acyclicity, favorable
palette, NEW color, induction domain or numerical formula is assumed.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- The admissible identity choice preserves ALL original slots. -/
theorem OriginalResidualCutStage.component_size_ge_of_mem_residual
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x)
    (y : Fin n) (hy : y ∈ W) :
    (componentSupport χ R y).ncard ≤ S.rootSupport.ncard := by
  let identityChoice : OriginalResidualChoice χ R U W :=
    { choice := R
      prefix_eq := by
        intro _ _
        rfl
      eligible_inside := S.partition.eligible_inside }
  simpa only [identityChoice, OriginalResidualCutStage.rootSupport] using
    S.maximum.1 identityChoice y hy

/-- Every later WHOLE selected component lies in this stage's literal uncut
tail, from the actual greedy sequence's unchanged whole-prefix recursion. -/
theorem OriginalResidualCutStage.later_component_support_subset
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {xs : List (Fin n)}
    (S : OriginalResidualCutStage χ R U W x)
    (hsequence : ResidualGreedySequence χ R U W (x :: xs))
    {y : Fin n} (hy : y ∈ xs) :
    componentSupport χ R y ⊆ W \ S.rootSupport := by
  have htail := hsequence.2.2.2
  have hcover := residualGreedySequence_covers χ R
    (U ∪ residualSelectedComponentColors χ R x)
    (W \ componentSupport χ R x) xs htail
  intro v hv
  exact (hcover v).mpr ⟨y, hy, hv⟩

/-- Actual later whole-component sizes are nonincreasing; no manufactured
ordering or desired component-size premise is supplied. -/
theorem OriginalResidualCutStage.later_component_size_le
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {xs : List (Fin n)}
    (S : OriginalResidualCutStage χ R U W x)
    (hsequence : ResidualGreedySequence χ R U W (x :: xs))
    {y : Fin n} (hy : y ∈ xs) :
    (componentSupport χ R y).ncard ≤ S.rootSupport.ncard := by
  have hyY : y ∈ componentSupport χ R y :=
    (mem_componentSupport χ R y y).mpr (SimpleGraph.Reachable.refl y)
  have hyW : y ∈ W := (S.later_component_support_subset hsequence hy hyY).1
  exact S.component_size_ge_of_mem_residual y hyW

/-- A FULL selected uncut-tail P(k-2), together with original no-rainbow Pk,
forces the earlier retained graph to be edgeless. The full original chi/R and
arbitrary U/W remain unchanged. No earlier edgelessness or tree is assumed. -/
theorem OriginalResidualCutStage.retained_edgeless_of_uncut_tail_path_order
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {k : ℕ}
    (S : OriginalResidualCutStage χ R U W x) (hk : 3 ≤ k)
    (hno : ∀ F : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow F.toHom χ)
    (Q : (pathGraph (k - 2)).Copy (selectedGraph χ R))
    (hQ : Set.range (fun v => Q v) ⊆ W \ S.rootSupport) :
    S.retainedGraph = ⊥ := by
  classical
  apply SimpleGraph.eq_bot_iff_forall_not_adj.mpr
  intro u v huv
  have hne : u ≠ v := S.retainedGraph.ne_of_adj huv
  let f : Fin 2 → componentSupport χ R x := fun i => if i = 0 then u else v
  let P : (pathGraph 2).Copy S.retainedGraph :=
    { toHom :=
        { toFun := f
          map_rel' := by
            intro i j hij
            fin_cases i <;> fin_cases j
            · have h := pathGraph_adj.mp hij
              omega
            · simpa [f] using huv
            · simpa [f] using huv.symm
            · have h := pathGraph_adj.mp hij
              omega }
      injective' := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · exact False.elim (hne (by simpa [f] using hij))
        · exact False.elim (hne (by simpa [f] using hij.symm))
        · rfl }
  have hlt := S.uncut_tail_path_order_lt hno (a := 2) (b := k - 2)
    (by omega) (by omega) P Q hQ
  omega

/-- Any actual later-stage retained long path already supplies the FULL
uncut-tail path needed to derive this earlier stage's retained edgelessness.
The later stage uses the SAME original full R; its own U/W are not reset. -/
theorem OriginalResidualCutStage.retained_edgeless_of_later_component_path_order
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {xs : List (Fin n)}
    (S : OriginalResidualCutStage χ R U W x)
    (hsequence : ResidualGreedySequence χ R U W (x :: xs))
    {y : Fin n} (hy : y ∈ xs)
    {V : Set (Fin q)} {Z : Set (Fin n)} {k : ℕ}
    (T : OriginalResidualCutStage χ R V Z y) (hk : 3 ≤ k)
    (P : (pathGraph (k - 2)).Copy T.retainedGraph)
    (hno : ∀ F : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow F.toHom χ) :
    S.retainedGraph = ⊥ := by
  let Q : (pathGraph (k - 2)).Copy (selectedGraph χ R) :=
    { toHom :=
        { toFun := fun u => (P u).val
          map_rel' := by
            intro u v huv
            exact (SimpleGraph.deleteEdges_adj.mp (P.toHom.map_rel' huv)).1 }
      injective' := by
        intro u v huv
        apply P.injective
        exact Subtype.ext huv }
  have hQ : Set.range (fun v => Q v) ⊆ W \ S.rootSupport := by
    rintro z ⟨v, rfl⟩
    exact S.later_component_support_subset hsequence hy (P v).property
  exact S.retained_edgeless_of_uncut_tail_path_order hk hno Q hQ

end ErdosProblems.PathUpperReduction
