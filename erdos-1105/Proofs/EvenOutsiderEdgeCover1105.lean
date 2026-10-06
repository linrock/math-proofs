module

public import EvenLastBlockRigidity1105

@[expose] public section

/-!
Constructs a disjoint path cover of the outsiders from a single outsider edge
together with singleton paths on the remaining outsiders, and applies
`EvenLastBlockRigidity1105`.
-/

namespace ErdosProblems.PathUpperReduction.EvenOutsiderEdgeCover1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.EvenLastBlockRigidity1105

/-- In the corrected d+3-core/d-outsider last block, an actual ORIGINAL
outsider edge and filled outsider/contact pairs force a spanning cycle in F.
The edge endpoints' distinctness follows from actual simple-graph adjacency. -/
theorem cycle_of_actual_outsider_edge {d : ℕ} (hd : 1 ≤ d)
    (G F : SimpleGraph (Fin (2 * d + 3))) (hGF : G ≤ F)
    (S C : Finset (Fin (2 * d + 3))) (hScard : S.card = d + 3)
    (hclique : G.IsClique (S : Set (Fin (2 * d + 3)))) (hCS : C ⊆ S)
    (hCcard : C.card = d)
    (hfilled : ∀ x, x ∉ S → ∀ a, a ∈ C → F.Adj x a)
    (hedge : ∃ x y, x ∉ S ∧ y ∉ S ∧ G.Adj x y) :
    cycleGraph (2 * d + 3) ⊑ F := by
  classical
  obtain ⟨x, y, hxS, hyS, hxy⟩ := hedge
  have hne : x ≠ y := hxy.ne
  let O : Finset (Fin (2 * d + 3)) := Finset.univ \ S
  have hOcard : O.card = d := by
    have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    change O.card + S.card = (Finset.univ : Finset (Fin (2 * d + 3))).card at hcard
    rw [Finset.card_univ, Fintype.card_fin, hScard] at hcard
    omega
  have hxO : x ∈ O := by
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxS⟩
  have hyO : y ∈ O := by
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hyS⟩
  let R : Finset (Fin (2 * d + 3)) := (O.erase x).erase y
  have hxR : x ∉ R := by simp [R]
  have hyR : y ∉ R := by simp [R]
  have hRO : R ⊆ O := by
    intro z hz
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz)
  have hyErase : y ∈ O.erase x := Finset.mem_erase.mpr ⟨hne.symm, hyO⟩
  have hRcard : R.card + 2 = d := by
    have hxcard := Finset.card_erase_add_one hxO
    have hycard := Finset.card_erase_add_one hyErase
    change R.card + 1 = (O.erase x).card at hycard
    omega
  let cover : List (List (Fin (2 * d + 3))) :=
    [x, y] :: R.toList.map (fun z => [z])
  have hflatten : cover.flatten = x :: y :: R.toList := by
    change [x, y] ++ (R.toList.map (fun z => [z])).flatten = x :: y :: R.toList
    rw [← List.flatMap_def, List.flatMap_singleton']
    rfl
  have hnonempty : ∀ p, p ∈ cover → p ≠ [] := by
    intro p hp
    rcases List.mem_cons.mp hp with hpair | hsingleton
    · subst p
      simp
    · obtain ⟨z, _, rfl⟩ := List.mem_map.mp hsingleton
      simp
  have hpaths : ∀ p, p ∈ cover → p.IsChain G.Adj := by
    intro p hp
    rcases List.mem_cons.mp hp with hpair | hsingleton
    · subst p
      exact List.isChain_pair.mpr hxy
    · obtain ⟨z, _, rfl⟩ := List.mem_map.mp hsingleton
      exact List.IsChain.singleton (R := G.Adj) z
  have hdisjoint : cover.flatten.Nodup := by
    rw [hflatten]
    apply List.nodup_cons.mpr
    refine ⟨?_, List.nodup_cons.mpr ⟨?_, R.nodup_toList⟩⟩
    · simp only [List.mem_cons, not_or, Finset.mem_toList]
      exact ⟨hne, hxR⟩
    · simpa only [Finset.mem_toList] using hyR
  have hcovers : ∀ z, z ∈ cover.flatten ↔ z ∉ S := by
    intro z
    rw [hflatten]
    constructor
    · intro hz
      rcases List.mem_cons.mp hz with hzx | hz
      · exact hzx.symm ▸ hxS
      · rcases List.mem_cons.mp hz with hzy | hzR
        · exact hzy.symm ▸ hyS
        · exact (Finset.mem_sdiff.mp (hRO (Finset.mem_toList.mp hzR))).2
    · intro hzS
      by_cases hzx : z = x
      · exact List.mem_cons.mpr (Or.inl hzx)
      by_cases hzy : z = y
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl hzy)))
      have hzO : z ∈ O := Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hzS⟩
      have hzR : z ∈ R := Finset.mem_erase.mpr
        ⟨hzy, Finset.mem_erase.mpr ⟨hzx, hzO⟩⟩
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
        (Or.inr (Finset.mem_toList.mpr hzR))))
  have hcoverPlus : cover.length + 1 = d := by
    simp only [cover, List.length_cons, List.length_map, Finset.length_toList]
    omega
  have hcoverLength : cover.length = d - 1 := by omega
  have hcapacity : cover.length + 1 ≤ C.card := by
    rw [hcoverLength, hCcard]
    omega
  exact cycle_of_actual_outsider_path_cover hd G F hGF S C hScard
    hclique hCS cover hnonempty hpaths hdisjoint hcovers hcapacity hfilled

end ErdosProblems.PathUpperReduction.EvenOutsiderEdgeCover1105
