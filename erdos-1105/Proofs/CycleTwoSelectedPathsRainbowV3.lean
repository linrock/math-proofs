module

public import CycleHostChainClosing
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Set.Disjoint

@[expose] public section

/-!
# Two disjoint selected paths joined by two original-host cross edges

positive Claim3 interface. The joining and closing edges are the same
literal original-host edges supplied by the caller, with explicit palette
separation from the full NEW union and different original χ colors. No graph component, cyclic lift, degree, finite-color, surjectivity, or
no-rainbow hypothesis is added.
-/

namespace ErdosProblems.AntiRamseyTwoSelectedPathsRainbow

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleOrderedEdges

variable {n : ℕ} {C : Type*} [DecidableEq C]

theorem append_of_lt {α : Type*} {L T : ℕ}
    (A : Fin L → α) (B : Fin T → α) (i : Fin (L + T)) (hi : i.val < L) :
    Fin.append A B i = A ⟨i.val, hi⟩ := by
  have heq : i = Fin.castAdd T (⟨i.val, hi⟩ : Fin L) := Fin.val_injective rfl
  calc
    Fin.append A B i = Fin.append A B (Fin.castAdd T (⟨i.val, hi⟩ : Fin L)) :=
      congrArg (Fin.append A B) heq
    _ = A ⟨i.val, hi⟩ := Fin.append_left A B _

theorem append_of_ge {α : Type*} {L T : ℕ}
    (A : Fin L → α) (B : Fin T → α) (i : Fin (L + T)) (hi : L ≤ i.val) :
    Fin.append A B i = B ⟨i.val - L, by have _h := i.isLt; omega⟩ := by
  have heq : i = Fin.natAdd L (⟨i.val - L, by have h := i.isLt; omega⟩ : Fin T) := by
    apply Fin.val_injective
    change i.val = L + (i.val - L)
    omega
  calc
    Fin.append A B i =
        Fin.append A B (Fin.natAdd L (⟨i.val - L, by have h := i.isLt; omega⟩ : Fin T)) :=
      congrArg (Fin.append A B) heq
    _ = B ⟨i.val - L, by have h := i.isLt; omega⟩ := Fin.append_right A B _

/-- The literal concatenation A followed by B closes to a rainbow host cycle
using the original joining/closing edges and the original χ labeling. -/
theorem two_disjoint_selected_paths_close_rainbow
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    {L T : ℕ} (hL : 2 ≤ L) (hT : 2 ≤ T)
    (A : Fin L → Fin n) (B : Fin T → Fin n)
    (hA : Function.Injective A) (hB : Function.Injective B)
    (hdisjoint : Disjoint (Set.range A) (Set.range B))
    (hApath : ∀ x y : Fin L, x.val + 1 = y.val →
      (selectedGraph χ r).Adj (A x) (A y))
    (hBpath : ∀ x y : Fin T, x.val + 1 = y.val →
      (selectedGraph χ r).Adj (B x) (B y))
    (between closing : HostEdge n)
    (hbetween : between.val =
      s(A ⟨L - 1, by omega⟩, B ⟨0, by omega⟩))
    (hclosing : closing.val =
      s(A ⟨0, by omega⟩, B ⟨T - 1, by omega⟩))
    (hbetweenOutside : χ between ∉ newColorUnion χ)
    (hclosingOutside : χ closing ∉ newColorUnion χ)
    (hdifferent : χ between ≠ χ closing) :
    ∃ f : (cycleGraph (L + T)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  let t : ℕ := L + T - 1
  have ht : 2 ≤ t := by dsimp [t]; omega
  have hcount : t + 1 = L + T := by dsimp [t]; omega
  have happend : Function.Injective (Fin.append A B) :=
    Fin.append_injective_iff.mpr ⟨hA, hB, Set.disjoint_range_iff.mp hdisjoint⟩
  let q : Fin (t + 1) → Fin n :=
    fun i => Fin.append A B ⟨i.val, by have hi := i.isLt; omega⟩
  have hq : Function.Injective q := by
    intro i j hij
    have hpos := happend hij
    apply Fin.val_injective
    exact congrArg (fun i : Fin (L + T) => i.val) hpos
  have hqA (i : Fin (t + 1)) (hi : i.val < L) :
      q i = A ⟨i.val, hi⟩ := by
    exact append_of_lt A B ⟨i.val, by have hi' := i.isLt; omega⟩ hi
  have hqB (i : Fin (t + 1)) (hi : L ≤ i.val) :
      q i = B ⟨i.val - L, by have hi' := i.isLt; omega⟩ := by
    exact append_of_ge A B ⟨i.val, by have hi' := i.isLt; omega⟩ hi
  let chain : Fin t → HostEdge n := fun i =>
    ⟨s(q (Fin.castSucc i), q (Fin.succ i)), by
      apply (SimpleGraph.mem_edgeSet _).mpr
      apply (top_adj _ _).mpr
      intro heq
      have hpos := hq heq
      have hval := congrArg Fin.val hpos
      simp only [Fin.val_castSucc, Fin.val_succ] at hval
      omega⟩
  have hchain (i : Fin t) :
      (chain i).val = s(q (Fin.castSucc i), q (Fin.succ i)) := rfl
  have hchainInj : Function.Injective chain := by
    intro i j hij
    have hv := congrArg Subtype.val hij
    rw [hchain i, hchain j] at hv
    change Sym2.map q (sourceStep i).val = Sym2.map q (sourceStep j).val at hv
    have hsource : sourceStep i = sourceStep j :=
      Subtype.ext (Sym2.map.injective hq hv)
    exact sourceStep_injective hsource

  have hselectedOrBetween (i : Fin t) :
      (chain i).val ∈ (selectedGraph χ r).edgeSet ∨ chain i = between := by
    by_cases hleft : i.val + 1 < L
    · left
      rw [hchain i, hqA (Fin.castSucc i) (by
        change i.val < L
        omega), hqA (Fin.succ i) (by
        change i.val + 1 < L
        exact hleft)]
      apply (SimpleGraph.mem_edgeSet _).mpr
      apply hApath
      change i.val + 1 = i.val + 1
      rfl
    · by_cases hjoin : i.val = L - 1
      · right
        have hleftq : q (Fin.castSucc i) = A ⟨L - 1, by omega⟩ := by
          rw [hqA (Fin.castSucc i) (by change i.val < L; omega)]
          apply congrArg A
          apply Fin.val_injective
          change i.val = L - 1
          exact hjoin
        have hrightq : q (Fin.succ i) = B ⟨0, by omega⟩ := by
          rw [hqB (Fin.succ i) (by change L ≤ i.val + 1; omega)]
          apply congrArg B
          apply Fin.val_injective
          change i.val + 1 - L = 0
          omega
        apply Subtype.ext
        rw [hchain i, hleftq, hrightq, hbetween]
      · left
        have hright : L ≤ i.val := by omega
        rw [hchain i, hqB (Fin.castSucc i) (by
          change L ≤ i.val
          exact hright), hqB (Fin.succ i) (by
          change L ≤ i.val + 1
          omega)]
        apply (SimpleGraph.mem_edgeSet _).mpr
        apply hBpath
        change i.val - L + 1 = i.val + 1 - L
        omega

  have hselectedUnion (e : HostEdge n)
      (he : e.val ∈ (selectedGraph χ r).edgeSet) :
      χ e ∈ newColorUnion χ := by
    rw [selectedGraph_edgeSet χ r] at he
    obtain ⟨c, hc⟩ := he
    have heq : e = r.edge c := Subtype.ext hc.symm
    rw [heq, r.color_eq]
    exact c.property
  have hselectedEq (e₁ e₂ : HostEdge n)
      (he₁ : e₁.val ∈ (selectedGraph χ r).edgeSet)
      (he₂ : e₂.val ∈ (selectedGraph χ r).edgeSet)
      (heq : χ e₁ = χ e₂) : e₁ = e₂ := by
    let s₁ : (selectedGraph χ r).edgeSet := ⟨e₁.val, he₁⟩
    let s₂ : (selectedGraph χ r).edgeSet := ⟨e₂.val, he₂⟩
    have hrestricted : restrictedColor χ r s₁ = restrictedColor χ r s₂ := by
      change χ e₁ = χ e₂
      exact heq
    have hs := restrictedColor_injective χ r hrestricted
    exact Subtype.ext (congrArg (fun e : (selectedGraph χ r).edgeSet => e.val) hs)
  have hcolors : Function.Injective (fun i : Fin t => χ (chain i)) := by
    intro i j heq
    rcases hselectedOrBetween i with hi | hi <;>
      rcases hselectedOrBetween j with hj | hj
    · exact hchainInj (hselectedEq (chain i) (chain j) hi hj heq)
    · have hmem := hselectedUnion (chain i) hi
      have hcolor : χ (chain i) = χ between := heq.trans (congrArg χ hj)
      rw [hcolor] at hmem
      exact False.elim (hbetweenOutside hmem)
    · have hmem := hselectedUnion (chain j) hj
      have hcolor : χ (chain j) = χ between := heq.symm.trans (congrArg χ hi)
      rw [hcolor] at hmem
      exact False.elim (hbetweenOutside hmem)
    · exact hchainInj (hi.trans hj.symm)
  have hne (i : Fin t) : χ (chain i) ≠ χ closing := by
    intro heq
    rcases hselectedOrBetween i with hi | hi
    · have hmem := hselectedUnion (chain i) hi
      rw [heq] at hmem
      exact hclosingOutside hmem
    · exact hdifferent ((congrArg χ hi).symm.trans heq)

  have hqzero : q 0 = A ⟨0, by omega⟩ := by
    exact hqA 0 (by change 0 < L; omega)
  have hqlast : q (Fin.last t) = B ⟨T - 1, by omega⟩ := by
    rw [hqB (Fin.last t) (by change L ≤ t; omega)]
    apply congrArg B
    apply Fin.val_injective
    change t - L = T - 1
    omega
  have hclose : closing.val = s(q 0, q (Fin.last t)) := by
    rw [hqzero, hqlast]
    exact hclosing
  have hresult :=
    ErdosProblems.AntiRamseyCycleHostChainClosing.ordered_host_chain_closes_rainbow
      ht χ q hq chain hchain hcolors closing hclose hne
  exact hcount ▸ hresult

end ErdosProblems.AntiRamseyTwoSelectedPathsRainbow
