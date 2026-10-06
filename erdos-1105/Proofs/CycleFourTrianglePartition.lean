module

public import CycleFourNewTriangle
public import CycleFourTriangleQuotient
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic

@[expose] public section

/-!
It assumes the literal host no-rainbow C4.Copy and
two NEW colors at every vertex. The wedge source's component theorem makes
every selected connected component a triangle; their finite quotient gives
the block map.
-/

namespace ErdosProblems.AntiRamseyCycleFourTrianglePartition

open SimpleGraph Finset
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleFourNewWedge
open ErdosProblems.AntiRamseyCycleFourNewTriangle
open ErdosProblems.AntiRamseyCycleFourTriangleQuotient
open ErdosProblems.AntiRamseyWeakCount

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Two distinct vertices in one selected connected component are joined
by one of its three selected triangle edges. -/
theorem selected_adj_of_same_component
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    (hnew : ∀ z : Fin n, 2 ≤ (newColors χ z).card)
    {a d : Fin n} (had : a ≠ d)
    (hcomp : (newColorRepresentative χ).connectedComponentMk a =
      (newColorRepresentative χ).connectedComponentMk d) :
    (newColorRepresentative χ).Adj a d := by
  classical
  let G : SimpleGraph (Fin n) := newColorRepresentative χ
  let D : G.ConnectedComponent := G.connectedComponentMk a
  obtain ⟨u, v, w, _, _, _, hD, huv, huw, hvw⟩ :=
    selected_component_is_triangle χ hno hnew D
  have haD : a ∈ D.supp := ConnectedComponent.connectedComponentMk_mem
  have hdD : d ∈ D.supp := by
    rw [ConnectedComponent.mem_supp_iff]
    exact hcomp.symm
  have ha : a = u ∨ a = v ∨ a = w := by
    simpa [hD] using haD
  have hd : d = u ∨ d = v ∨ d = w := by
    simpa [hD] using hdD
  rcases ha with rfl | rfl | rfl
  · rcases hd with rfl | rfl | rfl
    · exact False.elim (had rfl)
    · exact huv
    · exact huw
  · rcases hd with rfl | rfl | rfl
    · exact huv.symm
    · exact False.elim (had rfl)
    · exact hvw
  · rcases hd with rfl | rfl | rfl
    · exact huw.symm
    · exact hvw.symm
    · exact False.elim (had rfl)

/-- The checked k=4 wedge component statement yields a total partition
into selected three-vertex blocks. Every internal host color is NEW at both
ends. The `4≤n` premise is inherited from `HighNewWeakStructure 4` and
ensures a positive number of blocks. -/
theorem selected_triangle_component_partition
    (χ : TopEdgeLabeling (Fin n) C)
    (hn : 4 ≤ n)
    (hno : ∀ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    (hnew : ∀ z : Fin n, 2 ≤ (newColors χ z).card) :
    ∃ (t : ℕ) (b : Fin n → Fin t),
      1 ≤ t ∧
      (∀ i : Fin t, (blockFiber b i).card = 3) ∧
      (∀ (a d : Fin n) (_had : a ≠ d), b a = b d →
        (newColorRepresentative χ).Adj a d) ∧
      TriangleBlockOwnColors χ b ∧
      (∑ i : Fin t, (blockFiber b i).card = n) := by
  classical
  let G : SimpleGraph (Fin n) := newColorRepresentative χ
  let t : ℕ := Fintype.card G.ConnectedComponent
  let e : G.ConnectedComponent ≃ Fin t := Fintype.equivFin G.ConnectedComponent
  let b : Fin n → Fin t := fun v => e (G.connectedComponentMk v)
  have hn0 : 0 < n := by omega
  let z : Fin n := ⟨0, hn0⟩
  have htpos : 0 < t := by
    dsimp [t]
    exact Finset.card_pos.mpr ⟨G.connectedComponentMk z, Finset.mem_univ _⟩
  have ht : 1 ≤ t := by omega
  have hfiber (i : Fin t) : blockFiber b i = (e.symm i).supp.toFinset := by
    ext v
    simpa [blockFiber, b, ConnectedComponent.mem_supp_iff] using
      (e.eq_symm_apply (x := i) (y := G.connectedComponentMk v)).symm
  have hsize (i : Fin t) : (blockFiber b i).card = 3 := by
    calc
      (blockFiber b i).card = (e.symm i).supp.toFinset.card :=
        congrArg Finset.card (hfiber i)
      _ = (e.symm i).supp.ncard :=
        (Set.ncard_eq_toFinset_card' (e.symm i).supp).symm
      _ = 3 := selected_component_card_three χ hno hnew (e.symm i)
  have hselected (a d : Fin n) (had : a ≠ d) (hbd : b a = b d) :
      G.Adj a d := by
    have hcomp : G.connectedComponentMk a = G.connectedComponentMk d :=
      e.injective hbd
    exact selected_adj_of_same_component χ hno hnew had hcomp
  have hown : TriangleBlockOwnColors χ b := by
    intro a d had hbd
    have hadj : G.Adj a d := hselected a d had hbd
    have hcol : selectedEdgeColor χ hadj = χ.get a d had := rfl
    have hboth := selected_edge_color_new_both χ hno hnew hadj
    rw [hcol] at hboth
    exact hboth
  have hsum : ∑ i : Fin t, (blockFiber b i).card = n := by
    have h : (Finset.univ : Finset (Fin n)).card =
        ∑ i : Fin t, ((Finset.univ : Finset (Fin n)).filter
          (fun v => b v = i)).card :=
      Finset.card_eq_sum_card_fiberwise (by simp)
    simpa [blockFiber] using h.symm
  exact ⟨t, b, ht, hsize, hselected, hown, hsum⟩

end ErdosProblems.AntiRamseyCycleFourTrianglePartition
