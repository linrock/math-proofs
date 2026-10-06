module

public import UniformCone1105
public import EvenExceptionOrdinaryCopyV3
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Set

@[expose] public section

/-!
Remove the actual apex from an actual cone
classification, derive the three original-vertex support cardinalities, and
construct the entire finite relabelling internally. The conclusion is a
literal comap equality with the existing exceptional familyGraph; no new
graph family, favorable bijection, color or owner is supplied.
-/

noncomputable section

namespace ErdosProblems.PathUpperReduction.EvenSelectedFamilyIdentification1105

open SimpleGraph
open ErdosProblems.EvenExceptionExchange

/-- An actual cone classification identifies the SAME original graph with
the existing exceptional family. The apex really belongs to C, and is
removed internally; every original host vertex appears in the bijection. -/
theorem exists_family_pullback_of_actual_cone_classification (n d : ℕ)
    (M : SimpleGraph (Fin n)) (S C : Finset (Option (Fin n)))
    (hd : 2 ≤ d) (hnd : 2 * d + 2 ≤ n)
    (hCS : C ⊆ S) (hScard : S.card = d + 3) (hCcard : C.card = d)
    (hapex : none ∈ C)
    (hclass : ∀ u v, (UniformCone1105.cone M).Adj u v ↔ u ≠ v ∧
      ((u ∈ S ∧ v ∈ S) ∨ (u ∉ S ∧ v ∈ C) ∨ (v ∉ S ∧ u ∈ C))) :
    ∃ phi : Vertex (d - 1) (n - d - 2) ≃ Fin n,
      M.comap phi = familyGraph (d - 1) (n - d - 2) := by
  classical
  let U : Finset (Fin n) := Finset.univ.filter (fun v => some v ∈ S)
  let A : Finset (Fin n) := Finset.univ.filter (fun v => some v ∈ C)
  let B : Finset (Fin n) := U \ A
  let D : Finset (Fin n) := Finset.univ \ U
  let f : Fin n ↪ Option (Fin n) := ⟨some, Option.some_injective _⟩
  have hapexS : none ∈ S := hCS hapex
  have hAU : A ⊆ U := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v,
      hCS (Finset.mem_filter.mp hv).2⟩
  have hmapA : A.map f = C.erase none := by
    ext v
    cases v with
    | none => simp [f]
    | some v => simp [A, f]
  have hmapU : U.map f = S.erase none := by
    ext v
    cases v with
    | none => simp [f]
    | some v => simp [U, f]
  have hAcard : A.card = d - 1 := by
    have h := congrArg Finset.card hmapA
    rw [Finset.card_map, Finset.card_erase_of_mem hapex, hCcard] at h
    exact h
  have hUcard : U.card = d + 2 := by
    have h := congrArg Finset.card hmapU
    rw [Finset.card_map, Finset.card_erase_of_mem hapexS, hScard] at h
    omega
  have hBcard : B.card = 3 := by
    have h := Finset.card_sdiff_add_card_eq_card hAU
    change B.card + A.card = U.card at h
    rw [hAcard, hUcard] at h
    omega
  have hDcard : D.card = n - d - 2 := by
    have h := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ U)
    change D.card + U.card = (Finset.univ : Finset (Fin n)).card at h
    rw [hUcard, Finset.card_univ, Fintype.card_fin] at h
    have hdn : d + 2 ≤ n :=
      Nat.le_trans (by omega : d + 2 ≤ 2 * d + 2) hnd
    omega
  let eA : Fin (d - 1) ≃ (A : Set (Fin n)) :=
    (Finset.equivFinOfCardEq hAcard).symm
  let eB : Fin 3 ≃ (B : Set (Fin n)) :=
    (Finset.equivFinOfCardEq hBcard).symm
  let eD : Fin (n - d - 2) ≃ (D : Set (Fin n)) :=
    (Finset.equivFinOfCardEq hDcard).symm
  have hAUset : (A : Set (Fin n)) ⊆ (U : Set (Fin n)) := hAU
  let eBD : (B : Set (Fin n)) ≃
      ↥((U : Set (Fin n)) \ (A : Set (Fin n))) :=
    Set.equivOfEq (by ext v; simp [B])
  let eDC : (D : Set (Fin n)) ≃ ↥((U : Set (Fin n))ᶜ) :=
    Set.equivOfEq (by ext v; simp [D])
  let eParts : (A : Set (Fin n)) ⊕
      ((B : Set (Fin n)) ⊕ (D : Set (Fin n))) ≃ Fin n :=
    (Equiv.sumCongr (Equiv.refl _)
      (Equiv.sumCongr eBD eDC)).trans
      ((Equiv.sumAssoc _ _ _).symm.trans
        ((Equiv.sumCongr (Equiv.Set.sumDiffSubset hAUset)
          (Equiv.refl _)).trans (Equiv.Set.sumCompl (U : Set (Fin n)))))
  let phi : Vertex (d - 1) (n - d - 2) ≃ Fin n :=
    (Equiv.sumCongr eA (Equiv.sumCongr eB eD)).trans eParts
  have hphiA (i : Fin (d - 1)) : phi (Sum.inl i) = (eA i).val := rfl
  have hphiB (i : Fin 3) : phi (Sum.inr (Sum.inl i)) = (eB i).val := rfl
  have hphiD (i : Fin (n - d - 2)) :
      phi (Sum.inr (Sum.inr i)) = (eD i).val := rfl
  have hAC (i : Fin (d - 1)) : some (phi (Sum.inl i)) ∈ C := by
    rw [hphiA]
    exact (Finset.mem_filter.mp (eA i).property).2
  have hAS (i : Fin (d - 1)) : some (phi (Sum.inl i)) ∈ S := hCS (hAC i)
  have hBS (i : Fin 3) : some (phi (Sum.inr (Sum.inl i))) ∈ S := by
    rw [hphiB]
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (eB i).property).1).2
  have hBC (i : Fin 3) : some (phi (Sum.inr (Sum.inl i))) ∉ C := by
    rw [hphiB]
    intro hiC
    exact (Finset.mem_sdiff.mp (eB i).property).2
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiC⟩)
  have hDS (i : Fin (n - d - 2)) :
      some (phi (Sum.inr (Sum.inr i))) ∉ S := by
    rw [hphiD]
    intro hiS
    exact (Finset.mem_sdiff.mp (eD i).property).2
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiS⟩)
  have hDC (i : Fin (n - d - 2)) :
      some (phi (Sum.inr (Sum.inr i))) ∉ C := fun h => hDS i (hCS h)
  generalize hphi : phi = φ at hAS hAC hBS hBC hDS hDC
  clear hphiA hphiB hphiD hphi eA eB eD eBD eDC eParts phi
  have hM (u v : Fin n) : M.Adj u v ↔ u ≠ v ∧
      ((some u ∈ S ∧ some v ∈ S) ∨
        (some u ∉ S ∧ some v ∈ C) ∨ (some v ∉ S ∧ some u ∈ C)) := by
    have h := hclass (some u) (some v)
    change M.Adj u v ↔ some u ≠ some v ∧
      ((some u ∈ S ∧ some v ∈ S) ∨
        (some u ∉ S ∧ some v ∈ C) ∨ (some v ∉ S ∧ some u ∈ C)) at h
    simpa only [ne_eq, Option.some_inj] using h
  refine ⟨φ, ?_⟩
  ext u v
  change M.Adj (φ u) (φ v) ↔
    (familyGraph (d - 1) (n - d - 2)).Adj u v
  rw [hM]
  have hne : φ u ≠ φ v ↔ u ≠ v := by
    constructor
    · intro h hUV
      exact h (congrArg φ hUV)
    · intro h hUV
      exact h (φ.injective hUV)
  rw [hne]
  rcases u with i | (j | k) <;> rcases v with i' | (j' | k')
  · change _ ↔ (_ ∧ (True ∨ True ∨ (False ∧ False)))
    have hi := hAS i
    have hi' := hAS i'
    have hc := hAC i
    have hc' := hAC i'
    tauto
  · change _ ↔ (_ ∧ (True ∨ False ∨ (False ∧ True)))
    have hi := hAS i
    have hj := hBS j'
    have hc := hAC i
    have hc' := hBC j'
    tauto
  · change _ ↔ (_ ∧ (True ∨ False ∨ (False ∧ False)))
    have hi := hAS i
    have hk := hDS k'
    have hc := hAC i
    have hc' := hDC k'
    tauto
  · change _ ↔ (_ ∧ (False ∨ True ∨ (True ∧ False)))
    have hj := hBS j
    have hi := hAS i'
    have hc := hBC j
    have hc' := hAC i'
    tauto
  · change _ ↔ (_ ∧ (False ∨ False ∨ (True ∧ True)))
    have hj := hBS j
    have hj' := hBS j'
    have hc := hBC j
    have hc' := hBC j'
    tauto
  · change _ ↔ (_ ∧ (False ∨ False ∨ (True ∧ False)))
    have hj := hBS j
    have hk := hDS k'
    have hc := hBC j
    have hc' := hDC k'
    tauto
  · change _ ↔ (_ ∧ (False ∨ True ∨ (False ∧ False)))
    have hk := hDS k
    have hi := hAS i'
    have hc := hDC k
    have hc' := hAC i'
    tauto
  · change _ ↔ (_ ∧ (False ∨ False ∨ (False ∧ True)))
    have hk := hDS k
    have hj := hBS j'
    have hc := hDC k
    have hc' := hBC j'
    tauto
  · change _ ↔ (_ ∧ (False ∨ False ∨ (False ∧ False)))
    have hk := hDS k
    have hk' := hDS k'
    have hc := hDC k
    have hc' := hDC k'
    tauto

end ErdosProblems.PathUpperReduction.EvenSelectedFamilyIdentification1105
