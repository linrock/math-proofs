module

public import CycleNewChoiceExchange
public import CycleOrderedEdges

@[expose] public section

/-!
original-host chain closing interface for Claim3 path joining. The chain may contain an unselected cross edge. Palette injection and
separation from the same named original-host closing edge are explicit inputs. The Copy is a direct application of Mathlib's complete-graph embedding and
Copy composition, followed by the checked ordinary cycle-edge classification.
-/

namespace ErdosProblems.AntiRamseyCycleHostChainClosing

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleOrderedEdges

variable {n : ℕ} {C : Type*}

/-- An arbitrary original-host ordered rainbow chain closes to a literal
rainbow cycle when every chain color differs from the named closing color.
No selected-graph membership or valid NewChoice is assumed. -/
theorem ordered_host_chain_closes_rainbow
    {t : ℕ} (ht : 2 ≤ t)
    (χ : TopEdgeLabeling (Fin n) C)
    (q : Fin (t + 1) → Fin n) (hq : Function.Injective q)
    (chain : Fin t → HostEdge n)
    (hchain : ∀ i : Fin t,
      (chain i).val = s(q (Fin.castSucc i), q (Fin.succ i)))
    (hcolors : Function.Injective (fun i : Fin t => χ (chain i)))
    (closing : HostEdge n)
    (hclosing : closing.val = s(q 0, q (Fin.last t)))
    (hne : ∀ i : Fin t, χ (chain i) ≠ χ closing) :
    ∃ f : (cycleGraph (t + 1)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  let e : Fin (t + 1) ↪ Fin n := ⟨q, hq⟩
  let f : (cycleGraph (t + 1)).Copy (⊤ : SimpleGraph (Fin n)) :=
    (SimpleGraph.Embedding.completeGraph e).toCopy.comp
      (SimpleGraph.Copy.ofLE (cycleGraph (t + 1))
        (⊤ : SimpleGraph (Fin (t + 1))) le_top)
  have hstep (i : Fin t) :
      (EdgeLabeling.pullback χ f.toHom) (sourceStep i) = χ (chain i) := by
    change χ (f.toHom.mapEdgeSet (sourceStep i)) = χ (chain i)
    apply congrArg χ
    apply Subtype.ext
    change Sym2.map q (sourceStep i).val = (chain i).val
    simp only [sourceStep, Sym2.map_mk, hchain]
  have hclose :
      (EdgeLabeling.pullback χ f.toHom) (sourceClosing t ht) = χ closing := by
    change χ (f.toHom.mapEdgeSet (sourceClosing t ht)) = χ closing
    apply congrArg χ
    apply Subtype.ext
    change Sym2.map q (sourceClosing t ht).val = closing.val
    simp only [sourceClosing, Sym2.map_mk, hclosing]
  refine ⟨f, ?_⟩
  intro e₁ e₂ heq
  rcases sourceEdge_cases ht e₁ with ⟨i, hi⟩ | hi <;>
    rcases sourceEdge_cases ht e₂ with ⟨j, hj⟩ | hj
  · subst e₁
    subst e₂
    have hij : i = j := hcolors (by simpa only [hstep] using heq)
    subst j
    rfl
  · subst e₁
    subst e₂
    exact False.elim (hne i (by simpa only [hstep, hclose] using heq))
  · subst e₁
    subst e₂
    exact False.elim (hne j (by simpa only [hstep, hclose] using heq.symm))
  · subst e₁
    subst e₂
    rfl

end ErdosProblems.AntiRamseyCycleHostChainClosing
