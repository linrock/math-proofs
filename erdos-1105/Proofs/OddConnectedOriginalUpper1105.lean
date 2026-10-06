module

public import ConnectedOddCore1105
public import ConeFiniteContainer1105
public import PathS1ContainerCountBridge
public import PaletteWindow1105

@[expose] public section

/-!
prospective complete original connected odd upper bound. The same original chi/full R is retained throughout. All structural container,
capacity, window, degree and color-exit inputs are derived, not supplied.
-/

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis
open ErdosProblems.PathS1ContainerCountBridge

namespace ErdosProblems.PathUpperReduction.OddConnectedOriginalUpper1105

/-- Full original connected-step conclusion for every odd k=2*ell+1, ell>=4.
No supplied core, container, window, selected clique, favorable owner or IH. -/
theorem original_connected_odd_palette_upper {ell n q : ℕ}
    (hell : 4 ≤ ell) (hn : 2 * ell + 1 ≤ n)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (hconn : (selectedGraph χ R).Connected)
    (hno : ∀ P : (pathGraph (2 * ell + 1)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow P.toHom χ) :
    q ≤ max ((2 * ell - 1).choose 2 + 1)
      ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + 1) := by
  classical
  by_contra hbound
  have hq : max ((2 * ell - 1).choose 2 + 1)
      ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + 1) < q :=
    Nat.lt_of_not_ge hbound
  let M := selectedGraph χ R
  obtain ⟨H, _hConeSub, hfree, hdelete, _hsat, _hdensity, hclique, hcard,
      _hapex, _hapexmem, hConeEq, hSelectedSub⟩ :=
    ConnectedOddCore1105.exists_connected_odd_saturated_large_core
      hell hn χ R hconn hno hq
  let J := H.comap (some : Fin n → Option (Fin n))
  let S := degreeCore H ell
  have hSameCone : H = ConeCoreApplication1105.cone J := hConeEq
  have hK : 5 ≤ 2 * ell + 2 := by omega
  have hScard : S.card = (2 * ell + 2) - 2 := by
    dsimp only [S]
    rw [hcard]
    omega
  have hSclique : (ConeCoreApplication1105.cone J).IsClique
      (S : Set (Option (Fin n))) := by
    rw [← hSameCone]
    exact hclique
  have hJfree : ∀ r, 2 * ell + 2 ≤ r →
      (cycleGraph r).Free (ConeCoreApplication1105.cone J) := by
    intro r hr
    rw [← hSameCone]
    exact hfree r hr
  have hJdelete : ∀ z : Option (Fin n),
      ((ConeCoreApplication1105.cone J).induce {w | w ≠ z}).Connected := by
    intro z
    rw [← hSameCone]
    exact hdelete z
  have hcompl : 1 < Sᶜ.card := by
    rw [Finset.card_compl, hScard]
    simp only [Fintype.card_option, Fintype.card_fin]
    omega
  have houtside : ∃ u v : Option (Fin n), u ∉ S ∧ v ∉ S ∧ u ≠ v := by
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hcompl
    exact ⟨u, v, Finset.mem_compl.mp hu, Finset.mem_compl.mp hv, huv⟩
  have hContainer := ConeFiniteContainer1105.cone_finite_container
    J S hK hScard hSclique hJfree hJdelete houtside
  dsimp only at hContainer
  let m : ℕ := (2 * ell + 2) - 3
  let l : ℕ := n - m
  obtain ⟨_hm2, hl, hsum, _hTcard, _b, e, _hb, _hezero, _heleft,
    _heright, headj⟩ := hContainer
  have hm : 4 ≤ m := by dsimp only [m]; omega
  have hnSum : n = m + l := hsum.symm
  let core : Fin m → Fin n := fun i => e (Sum.inl i)
  let leaf : Fin l → Fin n := fun j => e (Sum.inr j)
  let z : Fin m := ⟨0, by omega⟩
  have hEnum : Sum.elim core leaf = e := by
    funext x
    cases x <;> rfl
  have hinj : Function.Injective (Sum.elim core leaf) := by
    rw [hEnum]
    exact e.injective
  have hcover : Function.Surjective (Sum.elim core leaf) := by
    rw [hEnum]
    exact e.surjective
  have hsubMJ : M ≤ J := hSelectedSub
  have hsub : M ≤ s1Container core leaf z := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := e.surjective x
    obtain ⟨b, rfl⟩ := e.surjective y
    have hc := (headj a b).mp (hsubMJ hxy)
    cases a with
    | inl i =>
        cases b with
        | inl j =>
            change i ≠ j at hc
            change (s1Container core leaf z).Adj (core i) (core j)
            apply (SimpleGraph.fromEdgeSet_adj _).mpr
            refine ⟨Or.inl ⟨s(i, j), ?_, ?_⟩, hxy.ne⟩
            · exact (SimpleGraph.mem_edgeSet (G := (⊤ : SimpleGraph (Fin m)))).mpr hc
            · simp only [Sym2.map_mk]
        | inr j =>
            change i.val = 0 at hc
            have hi : i = z := by apply Fin.ext; exact hc
            subst i
            change (s1Container core leaf z).Adj (core z) (leaf j)
            exact (SimpleGraph.fromEdgeSet_adj _).mpr ⟨Or.inr ⟨j, rfl⟩, hxy.ne⟩
    | inr i =>
        cases b with
        | inl j =>
            change j.val = 0 at hc
            have hj : j = z := by apply Fin.ext; exact hc
            subst j
            change (s1Container core leaf z).Adj (leaf i) (core z)
            exact (SimpleGraph.fromEdgeSet_adj _).mpr
              ⟨Or.inr ⟨i, Sym2.eq_swap⟩, hxy.ne⟩
        | inr j => exact hc.elim
  -- Actual selected-edge capacity; the private equality ledger is unnecessary.
  let A := (⊤ : SimpleGraph (Fin m)).edgeFinset.image (Sym2.map core)
  let B := (Finset.univ : Finset (Fin l)).image (fun j => s(core z, leaf j))
  have hEdgeSubset : M.edgeFinset ⊆ A ∪ B := by
    intro d
    refine Sym2.inductionOn d ?_
    intro x y hd
    have hxy : M.Adj x y := SimpleGraph.mem_edgeFinset.mp hd
    have hs := ((SimpleGraph.fromEdgeSet_adj _).mp (hsub hxy)).1
    rcases hs with ⟨t, ht, hte⟩ | ⟨j, hje⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨t, SimpleGraph.mem_edgeFinset.mpr ht, hte⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨j, Finset.mem_univ _, hje⟩)
  have hCount : Nat.card M.edgeSet = q := by
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using
      selectedGraph_card_edgeFinset χ R
  have hCapacity : q ≤ m.choose 2 + l := by
    calc
      q = Nat.card M.edgeSet := hCount.symm
      _ = M.edgeFinset.card := by
        rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
      _ ≤ (A ∪ B).card := Finset.card_le_card hEdgeSubset
      _ ≤ A.card + B.card := Finset.card_union_le A B
      _ ≤ (⊤ : SimpleGraph (Fin m)).edgeFinset.card +
          (Finset.univ : Finset (Fin l)).card :=
        Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ = m.choose 2 + l := by
        simp only [SimpleGraph.card_edgeFinset_top_eq_card_choose_two,
          Fintype.card_fin, Finset.card_univ]
  have hkm : (2 * ell + 1) - 2 = m := by dsimp only [m]; omega
  have hL : n - (2 * ell + 1) + 2 = l := by dsimp only [l, m]; omega
  have hhalf : ((2 * ell + 1) - 1) / 2 = ell := by omega
  have hodd : Odd (2 * ell + 1) := Nat.odd_iff.mpr (by omega)
  have hqLiteral : max (((2 * ell + 1) - 2).choose 2 + 1)
      ((((2 * ell + 1) - 1) / 2 - 1).choose 2 +
        (((2 * ell + 1) - 1) / 2 - 1) *
          (n - ((2 * ell + 1) - 1) / 2 + 1) +
        (if Odd (2 * ell + 1) then 1 else 2)) < q := by
    have hkpred : (2 * ell + 1) - 2 = 2 * ell - 1 := by omega
    simpa only [hkpred, hhalf, ite_eq_left hodd] using hq
  have hCapacityLiteral : q ≤ ((2 * ell + 1) - 2).choose 2 +
      (n - (2 * ell + 1) + 2) := by
    simpa only [hkm, hL] using hCapacity
  obtain ⟨hmargin, hcases⟩ :=
    WindowNumerics1105.original_palette_implies_window_or_full_four
      (2 * ell + 1) n q (by omega) hn hqLiteral hCapacityLiteral
  have hmargin' : m.choose 2 + 2 ≤ q := by
    simpa only [hkm] using hmargin
  have hwindow : 2 * l ≤ m := by
    rcases hcases with hwindow | ⟨hsix, _hfull⟩
    · simpa only [hkm, hL] using hwindow
    · omega
  have hRainbow := rainbow_path_of_representative_s1_container
    hm hl hwindow hnSum χ R core leaf hinj hcover hsub hmargin'
  have hPathOrder : m + 2 = 2 * ell + 1 := by dsimp only [m]; omega
  rw [hPathOrder] at hRainbow
  obtain ⟨P, hP⟩ := hRainbow
  exact hno P hP

end ErdosProblems.PathUpperReduction.OddConnectedOriginalUpper1105
