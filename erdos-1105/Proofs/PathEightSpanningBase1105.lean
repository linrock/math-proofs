module

public import PathUpperDenseConnectedRepresentativeV2
public import PathDegreeClosedSupergraph
public import PathUpperSpanningDegreeSlots
public import PathAOneSlotS1
public import PathS1ContainerCountBridge
public import ActualK8Rigidity1105
public import PathSelectedS3MotifExtractor
public import PathSelectedC6FourthLeafRainbow
public import PathMaxLower
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
Unconditional proof of the spanning base `antiRamseyNum (pathGraph 8) 8 = 16`
for `P_8` on `K_8` (`k = 8, n = 8`), combining:
- `exists_connected_representative_of_dense_palette` (`q ≥ 17`),
- `exists_degree_closed_path_free_supergraph` and `spanning_degree_slots_and_edge_count` (`a ∈ {1, 2, 3}`),
- `a = 1`: `a_one_slots_force_s1` and `rainbow_path_of_representative_s1_container`,
- `a = 2`: `17 ≤ 16` contradiction,
- `a = 3`: `actual_three_hub_rigidity`, `selected_c6_fourth_leaf_of_seventeen_edges_in_three_hub`,
  and `rainbow_path_eight_of_representative_c6_and_fourth_leaf`.
-/

noncomputable section

namespace ErdosProblems.PathUpperReduction.PathEightSpanningBase1105

open SimpleGraph
open ErdosProblems.PathUpperReduction
open ErdosProblems.PathS1ContainerCountBridge
open ErdosProblems.PathSelectedC6FourthLeaf
open ErdosProblems.PathSelectedS3MotifExtractor

/-- Any connected representative `selectedGraph χ r` on `Fin 8` with no rainbow
`P_8` has `q ≤ 16`. -/
theorem palette_le_sixteen_of_connected_no_rainbow_path_eight {q : ℕ}
    (χ : TopEdgeLabeling (Fin 8) (Fin q)) (r : RepresentativeChoice χ)
    (hconn : (selectedGraph χ r).Connected)
    (hno : ∀ f : (pathGraph 8).Copy (⊤ : SimpleGraph (Fin 8)),
      ¬ IsRainbow f.toHom χ) : q ≤ 16 := by
  classical
  by_contra hlarge
  have hq : 17 ≤ q := by omega
  let G : SimpleGraph (Fin 8) := selectedGraph χ r
  have hGfree : (pathGraph 8).Free G := selectedGraph_free (pathGraph 8) χ r hno
  have hGcount : G.edgeFinset.card = q := selectedGraph_card_edgeFinset χ r
  obtain ⟨H, hGH, hHfree, hclosure⟩ :=
    ErdosProblems.PathDegreeClosedSupergraph.exists_degree_closed_path_free_supergraph
      (by decide : 3 ≤ 8) G hGfree
  have hHconn : H.Connected := SimpleGraph.Connected.mono hGH hconn
  have hHedges : 17 ≤ H.edgeFinset.card := by
    calc
      17 ≤ q := hq
      _ = G.edgeFinset.card := hGcount.symm
      _ ≤ H.edgeFinset.card := Finset.card_le_card (SimpleGraph.edgeFinset_mono hGH)
  have hneTop : H ≠ ⊤ := by
    intro htop
    apply hHfree
    rw [htop]
    exact ⟨Copy.ofLE (pathGraph 8) (⊤ : SimpleGraph (Fin 8)) le_top⟩
  have hclosureLocal : ∀ x y : Fin 8, x ≠ y → ¬ H.Adj x y →
      @SimpleGraph.degree (Fin 8) H x (Subtype.fintype (· ∈ H.neighborSet x)) +
      @SimpleGraph.degree (Fin 8) H y (Subtype.fintype (· ∈ H.neighborSet y)) ≤ 8 - 2 := by
    intro x y hxy hnon
    have h := hclosure x y hxy hnon
    have hx : @SimpleGraph.degree (Fin 8) H x (Subtype.fintype (· ∈ H.neighborSet x)) = H.degree x := by
      congr 1; exact Subsingleton.elim _ _
    have hy : @SimpleGraph.degree (Fin 8) H y (Subtype.fintype (· ∈ H.neighborSet y)) = H.degree y := by
      congr 1; exact Subsingleton.elim _ _
    rw [hx, hy]
    exact h
  obtain ⟨a, L, ha, htwice, hLcard, hLdegree, hCap⟩ :=
    spanning_degree_slots_and_edge_count 8 (by decide) H hHconn hneTop hclosureLocal
  have hcases : a = 1 ∨ a = 2 ∨ a = 3 := by omega
  rcases hcases with rfl | rfl | rfl
  · -- Branch `a = 1`: `H` is the `S_1` graph (`K_6` with two leaves at hub `w`).
    have hc62 : (8 - 2 : ℕ).choose 2 + 2 ≤ H.edgeFinset.card := by
      have hc : (8 - 2 : ℕ).choose 2 = 15 := by decide
      omega
    obtain ⟨w, hwNotL, _hLdeg1, _hHcard17, _hCoreTop, _hLind, hHadj⟩ :=
      a_one_slots_force_s1 8 (by decide) H hHconn hclosureLocal L hLcard hLdegree hc62
    let C : Finset (Fin 8) := Lᶜ
    have hCcard : C.card = 6 := by
      simpa only [C, Fintype.card_fin, hLcard] using Finset.card_compl L
    have hwC : w ∈ C := Finset.mem_compl.mpr hwNotL
    let eC0 : Fin 6 ≃ C := (Finset.equivFinOfCardEq hCcard).symm
    let eC : Fin 6 ≃ C := (Equiv.swap 0 (eC0.symm ⟨w, hwC⟩)).trans eC0
    let eL : Fin 2 ≃ L := (Finset.equivFinOfCardEq hLcard).symm
    let core : Fin 6 → Fin 8 := fun i => (eC i).val
    let leaf : Fin 2 → Fin 8 := fun j => (eL j).val
    have hcore0 : core 0 = w := by
      dsimp [core, eC]
      rw [Equiv.swap_apply_left, Equiv.apply_symm_apply]
    have hinj : Function.Injective (Sum.elim core leaf) := by
      intro x y hxy
      rcases x with i | j <;> rcases y with i' | j'
      · exact congrArg Sum.inl (eC.injective (Subtype.ext hxy))
      · exfalso
        have hiC : core i ∈ C := (eC i).property
        have hjL : leaf j' ∈ L := (eL j').property
        change core i = leaf j' at hxy
        exact (Finset.mem_compl.mp hiC) (hxy ▸ hjL)
      · exfalso
        have hjL : leaf j ∈ L := (eL j).property
        have hiC : core i' ∈ C := (eC i').property
        change leaf j = core i' at hxy
        exact (Finset.mem_compl.mp hiC) (hxy.symm ▸ hjL)
      · exact congrArg Sum.inr (eL.injective (Subtype.ext hxy))
    have hcover : Function.Surjective (Sum.elim core leaf) :=
      ((Fintype.bijective_iff_injective_and_card (Sum.elim core leaf)).mpr
        ⟨hinj, by decide⟩).2
    have hsub : G ≤ s1Container core leaf 0 := by
      intro u v huv
      have hHuv : H.Adj u v := hGH huv
      obtain ⟨hne, hbranch⟩ := (hHadj u v).mp hHuv
      apply (SimpleGraph.fromEdgeSet_adj _).mpr
      refine ⟨?_, hne⟩
      rcases hbranch with ⟨huNotL, hvNotL⟩ | ⟨huL, rfl⟩ | ⟨hvL, rfl⟩
      · left
        let iu : Fin 6 := eC.symm ⟨u, Finset.mem_compl.mpr huNotL⟩
        let iv : Fin 6 := eC.symm ⟨v, Finset.mem_compl.mpr hvNotL⟩
        have hcoreu : core iu = u := congrArg Subtype.val (eC.apply_symm_apply _)
        have hcorev : core iv = v := congrArg Subtype.val (eC.apply_symm_apply _)
        have hiuv : iu ≠ iv := fun h => hne (hcoreu.symm.trans ((congrArg core h).trans hcorev))
        refine ⟨s(iu, iv), (SimpleGraph.mem_edgeSet (⊤ : SimpleGraph (Fin 6))).mpr hiuv, ?_⟩
        simp only [Sym2.map_mk, hcoreu, hcorev]
      · right
        let ju : Fin 2 := eL.symm ⟨u, huL⟩
        have hleafu : leaf ju = u := congrArg Subtype.val (eL.apply_symm_apply _)
        refine ⟨ju, ?_⟩
        dsimp only
        rw [hcore0, hleafu, Sym2.eq_swap]
      · right
        let jv : Fin 2 := eL.symm ⟨v, hvL⟩
        have hleafv : leaf jv = v := congrArg Subtype.val (eL.apply_symm_apply _)
        refine ⟨jv, ?_⟩
        dsimp only
        rw [hcore0, hleafv]
    have hq17 : (6 : ℕ).choose 2 + 2 ≤ q := by
      have hc : (6 : ℕ).choose 2 = 15 := by decide
      omega
    obtain ⟨f, hf⟩ :=
      rainbow_path_of_representative_s1_container
        (by decide : 4 ≤ 6) (by decide : 2 ≤ 2) (by decide : 2 * 2 ≤ 6) rfl
        χ r core leaf hinj hcover hsub hq17
    exact hno f hf
  · -- Branch `a = 2`: `H.edgeFinset.card ≤ 16`, contradicting `17 ≤ H.edgeFinset.card`.
    have hc52 : (8 - 1 - 2 : ℕ).choose 2 = 10 := by decide
    omega
  · -- Branch `a = 3`: `H` is `K_3` joined to `I_5`.
    obtain ⟨U, hUcard, _hHcard18, _hUuniv, _hOthree, hHadj⟩ :=
      ActualK8Rigidity1105.actual_three_hub_rigidity H L hLcard hLdegree hclosureLocal hHedges
    have hG17 : 17 ≤ (@SimpleGraph.edgeFinset (Fin 8) G G.fintypeEdgeSet).card := by
      have heq : (@SimpleGraph.edgeFinset (Fin 8) G G.fintypeEdgeSet).card = G.edgeFinset.card := by
        congr 2; exact Subsingleton.elim _ _
      omega
    obtain ⟨u, hu, hmotif⟩ :=
      selected_c6_fourth_leaf_of_seventeen_edges_in_three_hub G H hGH hG17 U hUcard hHadj
    obtain ⟨f, hf⟩ :=
      rainbow_path_eight_of_representative_c6_and_fourth_leaf χ r u hu hmotif
    exact hno f hf

/-- Every surjective coloring of `K_8` avoiding a rainbow `P_8` uses at most 16 colors. -/
theorem palette_le_sixteen_of_no_rainbow_path_eight {q : ℕ}
    (χ : TopEdgeLabeling (Fin 8) (Fin q)) (hχ : Function.Surjective χ)
    (hno : ∀ f : (pathGraph 8).Copy (⊤ : SimpleGraph (Fin 8)),
      ¬ IsRainbow f.toHom χ) : q ≤ 16 := by
  classical
  by_contra hlarge
  have hdense : (8 - 2).choose 2 + 2 ≤ q := by
    have hc62 : (8 - 2 : ℕ).choose 2 = 15 := by decide
    omega
  obtain ⟨r, hconn⟩ := exists_connected_representative_of_dense_palette
    χ hχ (by decide : 0 < 8) hdense
  have hle := palette_le_sixteen_of_connected_no_rainbow_path_eight χ r hconn hno
  omega

/-- Upper bound `antiRamseyNum (pathGraph 8) 8 ≤ 16`. -/
theorem antiRamseyNum_path_eight_eight_le_sixteen :
    antiRamseyNum (pathGraph 8) 8 ≤ 16 := by
  unfold antiRamseyNum
  apply csSup_le'
  rintro q ⟨χ, hχ, hno⟩
  exact palette_le_sixteen_of_no_rainbow_path_eight χ hχ hno

/-- Exact value `antiRamseyNum (pathGraph 8) 8 = 16`. -/
theorem antiRamseyNum_path_eight_eight_eq_sixteen :
    antiRamseyNum (pathGraph 8) 8 = 16 := by
  apply Nat.le_antisymm antiRamseyNum_path_eight_eight_le_sixteen
  have hlower := ErdosProblems.PathSetLower.pathMaxLower 8 8 (by decide) (by decide)
  have hnotOdd : ¬ Odd (8 : ℕ) := by decide
  have hc62 : (8 - 2 : ℕ).choose 2 = 15 := by decide
  have hc22 : (((8 - 1 : ℕ) / 2) - 1).choose 2 = 1 := by decide
  simp only [hnotOdd, ite_false] at hlower
  omega

end ErdosProblems.PathUpperReduction.PathEightSpanningBase1105
