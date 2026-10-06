module

public import CycleHostChainClosing
public import CycleQuotientTriangleLengths
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

/-!
# Original-host three-component triangle splice

The literal order is A0 followed by a
B prefix and a D prefix; either prefix may have one vertex. The original χ,
arbitrary valid NewChoice, actual whole components, spanning selected cyclic
orders, and full NEW-union palette are retained. No joined-rainbow interface
or prescribed endpoint path is assumed.
-/

namespace ErdosProblems.AntiRamseyCycleQuotientTriangleSplice

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleOrderedEdges
open ErdosProblems.AntiRamseyCycleQuotientTriangleLengths

variable {n : ℕ} {C : Type*} [DecidableEq C]

def triangleOrder {b c L T : ℕ}
    (x : Fin n) (B : Fin b → Fin n) (D : Fin c → Fin n)
    (hLb : L ≤ b) (hTc : T ≤ c) : Fin (L + T + 1) → Fin n := fun i =>
  if hzero : i.val = 0 then x
  else if hB : i.val ≤ L then B ⟨i.val - 1, by omega⟩
  else D ⟨i.val - (L + 1), by have hi := i.isLt; omega⟩

theorem triangleOrder_zero {b c L T : ℕ}
    (x : Fin n) (B : Fin b → Fin n) (D : Fin c → Fin n)
    (hLb : L ≤ b) (hTc : T ≤ c) (i : Fin (L + T + 1))
    (hzero : i.val = 0) : triangleOrder x B D hLb hTc i = x := by
  simp only [triangleOrder, dite_eq_left hzero]

theorem triangleOrder_B {b c L T : ℕ}
    (x : Fin n) (B : Fin b → Fin n) (D : Fin c → Fin n)
    (hLb : L ≤ b) (hTc : T ≤ c) (i : Fin (L + T + 1))
    (hpos : 0 < i.val) (hB : i.val ≤ L) :
    triangleOrder x B D hLb hTc i = B ⟨i.val - 1, by omega⟩ := by
  simp only [triangleOrder, dite_eq_right (by omega : ¬ i.val = 0), dite_eq_left hB]

theorem triangleOrder_D {b c L T : ℕ}
    (x : Fin n) (B : Fin b → Fin n) (D : Fin c → Fin n)
    (hLb : L ≤ b) (hTc : T ≤ c) (i : Fin (L + T + 1))
    (hD : L < i.val) :
    triangleOrder x B D hLb hTc i =
      D ⟨i.val - (L + 1), by have _hi := i.isLt; omega⟩ := by
  simp only [triangleOrder, dite_eq_right (by omega : ¬ i.val = 0),
    dite_eq_right (by omega : ¬ i.val ≤ L)]

theorem triangleOrder_injective {b c L T : ℕ}
    (x : Fin n) (B : Fin b → Fin n) (D : Fin c → Fin n)
    (hLb : L ≤ b) (hTc : T ≤ c)
    (hB : Function.Injective B) (hD : Function.Injective D)
    (hxB : ∀ i : Fin b, x ≠ B i) (hxD : ∀ i : Fin c, x ≠ D i)
    (hBD : ∀ (i : Fin b) (j : Fin c), B i ≠ D j) :
    Function.Injective (triangleOrder x B D hLb hTc) := by
  intro i j hij
  by_cases hi0 : i.val = 0
  · by_cases hj0 : j.val = 0
    · apply Fin.val_injective
      omega
    · by_cases hjB : j.val ≤ L
      · rw [triangleOrder_zero x B D hLb hTc i hi0,
          triangleOrder_B x B D hLb hTc j (by omega) hjB] at hij
        exact False.elim (hxB _ hij)
      · rw [triangleOrder_zero x B D hLb hTc i hi0,
          triangleOrder_D x B D hLb hTc j (by omega)] at hij
        exact False.elim (hxD _ hij)
  · by_cases hj0 : j.val = 0
    · by_cases hiB : i.val ≤ L
      · rw [triangleOrder_B x B D hLb hTc i (by omega) hiB,
          triangleOrder_zero x B D hLb hTc j hj0] at hij
        exact False.elim (hxB _ hij.symm)
      · rw [triangleOrder_D x B D hLb hTc i (by omega),
          triangleOrder_zero x B D hLb hTc j hj0] at hij
        exact False.elim (hxD _ hij.symm)
    · by_cases hiB : i.val ≤ L
      · by_cases hjB : j.val ≤ L
        · rw [triangleOrder_B x B D hLb hTc i (by omega) hiB,
            triangleOrder_B x B D hLb hTc j (by omega) hjB] at hij
          have hidx := congrArg Fin.val (hB hij)
          change i.val - 1 = j.val - 1 at hidx
          apply Fin.val_injective
          omega
        · rw [triangleOrder_B x B D hLb hTc i (by omega) hiB,
            triangleOrder_D x B D hLb hTc j (by omega)] at hij
          exact False.elim (hBD _ _ hij)
      · by_cases hjB : j.val ≤ L
        · rw [triangleOrder_D x B D hLb hTc i (by omega),
            triangleOrder_B x B D hLb hTc j (by omega) hjB] at hij
          exact False.elim (hBD _ _ hij.symm)
        · rw [triangleOrder_D x B D hLb hTc i (by omega),
            triangleOrder_D x B D hLb hTc j (by omega)] at hij
          have hidx := congrArg Fin.val (hD hij)
          change i.val - (L + 1) = j.val - (L + 1) at hidx
          apply Fin.val_injective
          omega

/-- Three whole selected components with the supplied spanning cyclic orders
and original constant cross colors cannot have three pairwise different
quotient labels under the literal original-host no-rainbow-Ck premise. -/
theorem three_components_cross_labels_repeat
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    {k a b c : ℕ} (hk : 5 ≤ k) (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c)
    (_haLower : k + 1 ≤ 2 * a) (hbLower : k + 1 ≤ 2 * b)
    (hcLower : k + 1 ≤ 2 * c)
    (_haUpper : a ≤ k - 1) (_hbUpper : b ≤ k - 1) (_hcUpper : c ≤ k - 1)
    (DA DB DD : (selectedGraph χ r).ConnectedComponent)
    (hAB : DA ≠ DB) (hBD : DB ≠ DD) (hDA : DD ≠ DA)
    (A : Fin a → Fin n) (B : Fin b → Fin n) (D : Fin c → Fin n)
    (_hA : Function.Injective A) (hB : Function.Injective B)
    (hD : Function.Injective D)
    (hAspan : Set.range A = DA.supp) (hBspan : Set.range B = DB.supp)
    (hDspan : Set.range D = DD.supp)
    (_hAcycle : ∀ i j : Fin a, (cycleGraph a).Adj i j →
      (selectedGraph χ r).Adj (A i) (A j))
    (hBcycle : ∀ i j : Fin b, (cycleGraph b).Adj i j →
      (selectedGraph χ r).Adj (B i) (B j))
    (hDcycle : ∀ i j : Fin c, (cycleGraph c).Adj i j →
      (selectedGraph χ r).Adj (D i) (D j))
    (α β γ : C)
    (hABcolor : ∀ (x y : Fin n) (e : HostEdge n),
      x ∈ DA.supp → y ∈ DB.supp → e.val = s(x, y) → χ e = α)
    (hBDcolor : ∀ (x y : Fin n) (e : HostEdge n),
      x ∈ DB.supp → y ∈ DD.supp → e.val = s(x, y) → χ e = β)
    (hDAcolor : ∀ (x y : Fin n) (e : HostEdge n),
      x ∈ DD.supp → y ∈ DA.supp → e.val = s(x, y) → χ e = γ)
    (hαOutside : α ∉ newColorUnion χ) (hβOutside : β ∉ newColorUnion χ)
    (hγOutside : γ ∉ newColorUnion χ)
    (hno : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ) :
    α = β ∨ β = γ ∨ γ = α := by
  by_contra htriangle
  have hαβ : α ≠ β := fun h => htriangle (Or.inl h)
  have hβγ : β ≠ γ := fun h => htriangle (Or.inr (Or.inl h))
  have hγα : γ ≠ α := fun h => htriangle (Or.inr (Or.inr h))
  let L := trianglePathL k b
  let T := trianglePathT k b
  obtain ⟨hL, hLb, hT, hTc, hcount⟩ :=
    triangle_path_lengths_of_component_lower_bounds hk hb hc hbLower hcLower
  change 1 ≤ L at hL
  change L ≤ b at hLb
  change 1 ≤ T at hT
  change T ≤ c at hTc
  change L + T + 1 = k at hcount
  have ht : 2 ≤ L + T := by omega
  have hAmem (i : Fin a) : A i ∈ DA.supp := by
    rw [← hAspan]
    exact ⟨i, rfl⟩
  have hBmem (i : Fin b) : B i ∈ DB.supp := by
    rw [← hBspan]
    exact ⟨i, rfl⟩
  have hDmem (i : Fin c) : D i ∈ DD.supp := by
    rw [← hDspan]
    exact ⟨i, rfl⟩
  let a0 : Fin a := ⟨0, by omega⟩
  let x := A a0
  have hxB (i : Fin b) : x ≠ B i := by
    intro heq
    apply hAB
    exact ConnectedComponent.eq_of_common_vertex (hAmem a0) (by
      change x ∈ DB.supp
      rw [heq]
      exact hBmem i)
  have hxD (i : Fin c) : x ≠ D i := by
    intro heq
    apply hDA
    exact ConnectedComponent.eq_of_common_vertex (hDmem i) (by
      rw [← heq]
      exact hAmem a0)
  have hBDne (i : Fin b) (j : Fin c) : B i ≠ D j := by
    intro heq
    apply hBD
    exact ConnectedComponent.eq_of_common_vertex (hBmem i) (by
      rw [heq]
      exact hDmem j)
  let q := triangleOrder x B D hLb hTc
  have hq : Function.Injective q :=
    triangleOrder_injective x B D hLb hTc hB hD hxB hxD hBDne
  have hqzero (i : Fin (L + T + 1)) (hi : i.val = 0) : q i = x :=
    triangleOrder_zero x B D hLb hTc i hi
  have hqB (i : Fin (L + T + 1)) (hpos : 0 < i.val) (hi : i.val ≤ L) :
      q i = B ⟨i.val - 1, by omega⟩ :=
    triangleOrder_B x B D hLb hTc i hpos hi
  have hqD (i : Fin (L + T + 1)) (hi : L < i.val) :
      q i = D ⟨i.val - (L + 1), by have hi' := i.isLt; omega⟩ :=
    triangleOrder_D x B D hLb hTc i hi
  let chain : Fin (L + T) → HostEdge n := fun i =>
    ⟨s(q (Fin.castSucc i), q (Fin.succ i)), by
      apply (SimpleGraph.mem_edgeSet _).mpr
      apply (top_adj _ _).mpr
      intro heq
      have hval := congrArg Fin.val (hq heq)
      simp only [Fin.val_castSucc, Fin.val_succ] at hval
      omega⟩
  have hchain (i : Fin (L + T)) :
      (chain i).val = s(q (Fin.castSucc i), q (Fin.succ i)) := rfl
  have hchainInj : Function.Injective chain := by
    intro i j hij
    have hv := congrArg Subtype.val hij
    rw [hchain i, hchain j] at hv
    change Sym2.map q (sourceStep i).val = Sym2.map q (sourceStep j).val at hv
    have hsource : sourceStep i = sourceStep j :=
      Subtype.ext (Sym2.map.injective hq hv)
    exact sourceStep_injective hsource
  have hclass (i : Fin (L + T)) :
      (chain i).val ∈ (selectedGraph χ r).edgeSet ∨
        (i.val = 0 ∧ χ (chain i) = α) ∨
        (i.val = L ∧ χ (chain i) = β) := by
    by_cases hi0 : i.val = 0
    · right; left
      refine ⟨hi0, ?_⟩
      have hleft : q (Fin.castSucc i) = x := hqzero _ hi0
      have hright := hqB (Fin.succ i) (by change 0 < i.val + 1; omega)
        (by change i.val + 1 ≤ L; omega)
      apply hABcolor x _ (chain i) (hAmem a0) (hBmem _)
      rw [hchain i, hleft, hright]
    · by_cases hiL : i.val = L
      · right; right
        refine ⟨hiL, ?_⟩
        have hleft := hqB (Fin.castSucc i) (by change 0 < i.val; omega)
          (by change i.val ≤ L; omega)
        have hright := hqD (Fin.succ i) (by change L < i.val + 1; omega)
        apply hBDcolor _ _ (chain i) (hBmem _) (hDmem _)
        rw [hchain i, hleft, hright]
      · left
        by_cases hiB : i.val < L
        · rw [hchain i, hqB (Fin.castSucc i) (by change 0 < i.val; omega)
            (by change i.val ≤ L; omega),
            hqB (Fin.succ i) (by change 0 < i.val + 1; omega)
              (by change i.val + 1 ≤ L; omega)]
          apply (SimpleGraph.mem_edgeSet _).mpr
          apply hBcycle
          apply pathGraph_le_cycleGraph
          rw [pathGraph_adj]
          left
          change i.val - 1 + 1 = i.val + 1 - 1
          omega
        · rw [hchain i, hqD (Fin.castSucc i) (by change L < i.val; omega),
            hqD (Fin.succ i) (by change L < i.val + 1; omega)]
          apply (SimpleGraph.mem_edgeSet _).mpr
          apply hDcycle
          apply pathGraph_le_cycleGraph
          rw [pathGraph_adj]
          left
          change i.val - (L + 1) + 1 = i.val + 1 - (L + 1)
          omega
  have hselectedUnion (e : HostEdge n)
      (he : e.val ∈ (selectedGraph χ r).edgeSet) : χ e ∈ newColorUnion χ := by
    rw [selectedGraph_edgeSet χ r] at he
    obtain ⟨c', hc'⟩ := he
    have heq : e = r.edge c' := Subtype.ext hc'.symm
    rw [heq, r.color_eq]
    exact c'.property
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
  have hcolors : Function.Injective (fun i : Fin (L + T) => χ (chain i)) := by
    intro i j heq
    change χ (chain i) = χ (chain j) at heq
    rcases hclass i with hi | ⟨hi0, hiα⟩ | ⟨hiL, hiβ⟩ <;>
      rcases hclass j with hj | ⟨hj0, hjα⟩ | ⟨hjL, hjβ⟩
    · exact hchainInj (hselectedEq (chain i) (chain j) hi hj heq)
    · have hmem := hselectedUnion (chain i) hi
      rw [heq, hjα] at hmem
      exact False.elim (hαOutside hmem)
    · have hmem := hselectedUnion (chain i) hi
      rw [heq, hjβ] at hmem
      exact False.elim (hβOutside hmem)
    · have hmem := hselectedUnion (chain j) hj
      rw [← heq, hiα] at hmem
      exact False.elim (hαOutside hmem)
    · apply Fin.val_injective
      omega
    · rw [hiα, hjβ] at heq
      exact False.elim (hαβ heq)
    · have hmem := hselectedUnion (chain j) hj
      rw [← heq, hiβ] at hmem
      exact False.elim (hβOutside hmem)
    · rw [hiβ, hjα] at heq
      exact False.elim (hαβ heq.symm)
    · apply Fin.val_injective
      omega
  have hqfirst : q 0 = x := hqzero _ rfl
  have hqlast : q (Fin.last (L + T)) = D ⟨T - 1, by omega⟩ := by
    rw [hqD (Fin.last (L + T)) (by change L < L + T; omega)]
    apply congrArg D
    apply Fin.val_injective
    change L + T - (L + 1) = T - 1
    omega
  let closing : HostEdge n :=
    ⟨s(q 0, q (Fin.last (L + T))), by
      apply (SimpleGraph.mem_edgeSet _).mpr
      apply (top_adj _ _).mpr
      intro heq
      have hval := congrArg Fin.val (hq heq)
      simp only [Fin.val_zero, Fin.val_last] at hval
      omega⟩
  have hclosing : closing.val = s(q 0, q (Fin.last (L + T))) := rfl
  have hclosingColor : χ closing = γ := by
    apply hDAcolor _ x closing (hDmem _) (hAmem a0)
    rw [hclosing, hqfirst, hqlast]
    exact Sym2.eq_swap
  have hne (i : Fin (L + T)) : χ (chain i) ≠ χ closing := by
    intro heq
    rcases hclass i with hi | ⟨_hi0, hiα⟩ | ⟨_hiL, hiβ⟩
    · have hmem := hselectedUnion (chain i) hi
      rw [heq, hclosingColor] at hmem
      exact hγOutside hmem
    · rw [hiα, hclosingColor] at heq
      exact hγα heq.symm
    · rw [hiβ, hclosingColor] at heq
      exact hβγ heq
  have hcopy :=
    ErdosProblems.AntiRamseyCycleHostChainClosing.ordered_host_chain_closes_rainbow
      ht χ q hq chain hchain hcolors closing hclosing hne
  have hcopyk : ∃ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by exact hcount ▸ hcopy
  obtain ⟨f, hf⟩ := hcopyk
  exact hno f hf

end ErdosProblems.AntiRamseyCycleQuotientTriangleSplice
