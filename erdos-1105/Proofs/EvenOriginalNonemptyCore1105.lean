module

public import EvenOriginalBackwardRestoration1105
public import SecondCoreCount1105
public import UniformConeStructure1105
public import ConeFiniteContainer1105
public import PathS1ContainerCountBridge
public import PaletteWindow1105
public import PathUpperRainbowBridge
public import EvenIntermediateCoreScalar1105
public import EvenSelectedFamilyIdentification1105
public import EvenFamilyRainbowExitV2

@[expose] public section

/-!
Eliminates the nonempty first-core branch for connected even-path
representatives by combining the large first-core `S1` exit, the small
first-core tight backward restoration, and the intermediate-core exceptional
family exchange.
-/

noncomputable section

namespace ErdosProblems.PathUpperReduction.EvenOriginalNonemptyCore1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis
open ErdosProblems.PathUpperReduction.UniformCone1105 (cone)
open ErdosProblems.PathS1ContainerCountBridge

theorem actual_universal_cone {n : ℕ}
    (H : SimpleGraph (Option (Fin n))) (ha : H.IsUniversal none) :
    H = ConeCoreApplication1105.cone
      (H.comap (some : Fin n → Option (Fin n))) := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  cases u with
  | none =>
      cases v with
      | none =>
          change H.Adj none none ↔ False
          exact ⟨H.loopless.irrefl _, False.elim⟩
      | some v =>
          change H.Adj none (some v) ↔ True
          exact ⟨fun _ => True.intro, fun _ => ha (by simp)⟩
  | some u =>
      cases v with
      | none =>
          change H.Adj (some u) none ↔ True
          exact ⟨fun _ => True.intro, fun _ => (ha (by simp)).symm⟩
      | some v => rfl

theorem top_core_impossible {d n q : ℕ}
    (hd : 3 ≤ d) (hn : 2 * d + 2 ≤ n)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (hno : ∀ P : (pathGraph (2 * d + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow P.toHom χ)
    (hq : max ((2 * d).choose 2 + 1)
      ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 2) < q)
    (H : SimpleGraph (Option (Fin n)))
    (hCH : cone (selectedGraph χ R) ≤ H)
    (hfree : ∀ m, 2 * d + 3 ≤ m → (cycleGraph m).Free H)
    (hdelete : ∀ z, (H.induce {w | w ≠ z}).Connected)
    (S : Finset (Option (Fin n)))
    (hclique : H.IsClique (S : Set (Option (Fin n))))
    (hcard : S.card = 2 * d + 1) : False := by
  classical
  let M := selectedGraph χ R
  let J := H.comap (some : Fin n → Option (Fin n))
  have ha : H.IsUniversal none := by
    intro v hne
    exact hCH (UniformConeStructure1105.cone_apex_isUniversal M hne)
  have hSameCone : H = ConeCoreApplication1105.cone J :=
    actual_universal_cone H ha
  have hSelectedSub : M ≤ J := by
    intro u v huv
    exact hCH huv
  have hK : 5 ≤ 2 * d + 3 := by omega
  have hScard : S.card = (2 * d + 3) - 2 := by rw [hcard]; omega
  have hSclique : (ConeCoreApplication1105.cone J).IsClique
      (S : Set (Option (Fin n))) := by
    rw [← hSameCone]
    exact hclique
  have hJfree : ∀ m, 2 * d + 3 ≤ m →
      (cycleGraph m).Free (ConeCoreApplication1105.cone J) := by
    intro m hm
    rw [← hSameCone]
    exact hfree m hm
  have hJdelete : ∀ z : Option (Fin n),
      ((ConeCoreApplication1105.cone J).induce {w | w ≠ z}).Connected := by
    intro z
    rw [← hSameCone]
    exact hdelete z
  have hcompl : 1 < Sᶜ.card := by
    rw [Finset.card_compl, hcard]
    simp only [Fintype.card_option, Fintype.card_fin]
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hcompl
  have houtside : ∃ u v : Option (Fin n), u ∉ S ∧ v ∉ S ∧ u ≠ v :=
    ⟨u, v, Finset.mem_compl.mp hu, Finset.mem_compl.mp hv, huv⟩
  have hContainer := ConeFiniteContainer1105.cone_finite_container
    J S hK hScard hSclique hJfree hJdelete houtside
  dsimp only at hContainer
  let m : ℕ := (2 * d + 3) - 3
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
  have hsub : M ≤ s1Container core leaf z := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := e.surjective x
    obtain ⟨b, rfl⟩ := e.surjective y
    have hc := (headj a b).mp (hSelectedSub hxy)
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
  let A := (⊤ : SimpleGraph (Fin m)).edgeFinset.image (Sym2.map core)
  let B := (Finset.univ : Finset (Fin l)).image (fun j => s(core z, leaf j))
  have hEdgeSubset : M.edgeFinset ⊆ A ∪ B := by
    intro f
    refine Sym2.inductionOn f ?_
    intro x y hf
    have hxy : M.Adj x y := SimpleGraph.mem_edgeFinset.mp hf
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
  have hkm : (2 * d + 2) - 2 = m := by dsimp only [m]; omega
  have hL : n - (2 * d + 2) + 2 = l := by dsimp only [l, m]; omega
  have hhalf : ((2 * d + 2) - 1) / 2 = d := by omega
  have hnotodd : ¬ Odd (2 * d + 2) := by
    simp only [Nat.odd_iff]
    omega
  have hqLiteral : max (((2 * d + 2) - 2).choose 2 + 1)
      ((((2 * d + 2) - 1) / 2 - 1).choose 2 +
        (((2 * d + 2) - 1) / 2 - 1) *
          (n - ((2 * d + 2) - 1) / 2 + 1) +
        (if Odd (2 * d + 2) then 1 else 2)) < q := by
    have hkpred : (2 * d + 2) - 2 = 2 * d := by omega
    simpa only [hkpred, hhalf, ite_eq_right hnotodd] using hq
  have hCapacityLiteral : q ≤ ((2 * d + 2) - 2).choose 2 +
      (n - (2 * d + 2) + 2) := by
    simpa only [hkm, hL] using hCapacity
  obtain ⟨hmargin, hcases⟩ :=
    WindowNumerics1105.original_palette_implies_window_or_full_four
      (2 * d + 2) n q (by omega) hn hqLiteral hCapacityLiteral
  have hmargin' : m.choose 2 + 2 ≤ q := by simpa only [hkm] using hmargin
  have hwindow : 2 * l ≤ m := by
    rcases hcases with hwindow | ⟨hsix, _hfull⟩
    · simpa only [hkm, hL] using hwindow
    · omega
  have hRainbow := rainbow_path_of_representative_s1_container
    hm hl hwindow hnSum χ R core leaf hinj hcover hsub hmargin'
  have hPathOrder : m + 2 = 2 * d + 2 := by dsimp only [m]; omega
  rw [hPathOrder] at hRainbow
  obtain ⟨P, hP⟩ := hRainbow
  exact hno P hP

/-- The actual small-core count is the first forbidden EVEN linear palette
plus the n apex edges; all natural subtractions retain their domain guards. -/
theorem small_core_count_eq_even_linear (d n : ℕ) (hd : 3 ≤ d)
    (hn : 2 * d + 2 ≤ n) :
    (d + 3).choose 2 + d * (n + 1 - (d + 3)) =
      n + ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 3) := by
  let a := d - 1
  let b := n - d - 2
  have ha : d = a + 1 := by dsimp [a]; omega
  have hb : n + 1 - (d + 3) = b := by dsimp [b]; omega
  have hn' : n = a + b + 3 := by dsimp [a, b]; omega
  have ht : n - d + 1 = b + 3 := by dsimp [b]; omega
  have hstep (u : ℕ) : (u + 1).choose 2 = u + u.choose 2 := by
    simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' u 1
  have hchoose : (d + 3).choose 2 = a.choose 2 + 4 * a + 6 := by
    have he : d + 3 = (((a + 1) + 1) + 1) + 1 := by omega
    rw [he, hstep, hstep, hstep, hstep]
    ring
  calc
    (d + 3).choose 2 + d * (n + 1 - (d + 3)) =
        a.choose 2 + 4 * a + 6 + (a + 1) * b := by rw [hchoose, hb, ha]
    _ = (a + b + 3) + (a.choose 2 + a * (b + 3) + 3) := by ring
    _ = n + ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 3) := by
      rw [← hn', ← ht]

theorem small_core_original_classification {d n q : ℕ}
    (hd : 3 ≤ d) (hn : 2 * d + 2 ≤ n)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (hq : max ((2 * d).choose 2 + 1)
      ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 2) < q)
    (H : SimpleGraph (Option (Fin n)))
    (hCH : cone (selectedGraph χ R) ≤ H)
    (hfree : ∀ m, 2 * d + 3 ≤ m → (cycleGraph m).Free H)
    (hdelete : ∀ z, (H.induce {w | w ≠ z}).Connected)
    (hsat : ∀ u v, u ≠ v → ¬ H.Adj u v →
      ∃ m, 2 * d + 3 ≤ m ∧ Nonempty ((cycleGraph m).Copy
        (H ⊔ fromEdgeSet {s(u, v)})))
    (hlower : n + q ≤ Nat.card H.edgeSet)
    (hsmall : (degreeCore H (d + 1)).card = d + 3) :
    H = cone (selectedGraph χ R) ∧
      ∃ C : Finset (Option (Fin n)), C ⊆ degreeCore H (d + 1) ∧
        C.card = d ∧ none ∈ C ∧
        ∀ u v, (cone (selectedGraph χ R)).Adj u v ↔ u ≠ v ∧
          ((u ∈ degreeCore H (d + 1) ∧ v ∈ degreeCore H (d + 1)) ∨
            (u ∉ degreeCore H (d + 1) ∧ v ∈ C) ∨
            (v ∉ degreeCore H (d + 1) ∧ u ∈ C)) := by
  classical
  let S := degreeCore H (d + 1)
  have hK : 5 ≤ 2 * d + 3 := by omega
  have hN : Fintype.card (Option (Fin n)) = n + 1 := by simp
  have hKN : 2 * d + 3 ≤ Fintype.card (Option (Fin n)) := by rw [hN]; omega
  have hhalf : (2 * d + 3 - 1) / 2 = d + 1 := by omega
  have hnonempty : (degreeCore H ((2 * d + 3 - 1) / 2)).Nonempty := by
    rw [hhalf]
    exact Finset.card_pos.mp (by rw [hsmall]; omega)
  have hsecond := SecondCoreCount1105.saturated_second_core_eq
    H hK hKN hfree hdelete hsat hnonempty
  rw [hhalf] at hsecond
  have hthreshold : 2 * d + 3 - (degreeCore H (d + 1)).card = d := by
    rw [hsmall]
    omega
  rw [hthreshold] at hsecond
  have hcore : degreeCore H d = S := hsecond
  have hupper := SecondCoreCount1105.nonempty_core_edge_bound
    H hK hKN hfree hdelete hsat hnonempty
  rw [hhalf, hsmall, hN] at hupper
  have hsubtraction : 2 * d + 3 - (d + 3) = d := by omega
  rw [hsubtraction, small_core_count_eq_even_linear d n hd hn] at hupper
  have hlinear : (d - 1).choose 2 + (d - 1) * (n - d + 1) + 3 ≤ q := by
    have hlt := lt_of_le_of_lt (le_max_right _ _) hq
    omega
  have htight : Nat.card H.edgeSet =
      S.card.choose 2 + d * (Nat.card (Option (Fin n)) - S.card) := by
    have hnat : Nat.card (Option (Fin n)) = n + 1 := by
      rw [Nat.card_eq_fintype_card, hN]
    change Nat.card H.edgeSet =
      (degreeCore H (d + 1)).card.choose 2 +
        d * (Nat.card (Option (Fin n)) - (degreeCore H (d + 1)).card)
    rw [hsmall, hnat, small_core_count_eq_even_linear d n hd hn]
    omega
  have hMcount : (selectedGraph χ R).edgeFinset.card = q :=
    selectedGraph_card_edgeFinset χ R
  have hConeCount : (cone (selectedGraph χ R)).edgeFinset.card = n + q := by
    rw [UniformConeStructure1105.finite_cone_edgeFinset_card]
    have hEq : @SimpleGraph.edgeFinset _ (selectedGraph χ R) (selectedGraph χ R).fintypeEdgeSet =
        @SimpleGraph.edgeFinset _ (selectedGraph χ R) (selectedGraph_edgeSet_fintype χ R) := by
      congr 1; exact Subsingleton.elim _ _
    rw [hEq, hMcount]
    omega
  have hHnat : Nat.card H.edgeSet = H.edgeFinset.card := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
  have hCardEquality : H.edgeFinset.card = (cone (selectedGraph χ R)).edgeFinset.card := by
    rw [← hHnat, hConeCount]
    omega
  have hOriginalCone : H = cone (selectedGraph χ R) := by
    apply SimpleGraph.edgeFinset_inj.mp
    symm
    exact Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono hCH)
      (le_of_eq hCardEquality)
  have hapex : ∀ z : Option (Fin n), z ≠ none → H.Adj z none := by
    intro z hne
    exact (hCH (UniformConeStructure1105.cone_apex_isUniversal
      (selectedGraph χ R) hne.symm)).symm
  have hOutside : d ≤ Nat.card (Option (Fin n)) - S.card := by
    rw [Nat.card_eq_fintype_card, hN]
    change d ≤ n + 1 - (degreeCore H (d + 1)).card
    rw [hsmall]
    omega
  obtain ⟨C, hCS, hCcard, hnone, hclass⟩ :=
    EvenOriginalBackwardRestoration1105.classify_tight_actual_core_with_apex
      H d S none (by omega) hcore hsmall htight hOutside hapex
      (hfree (2 * d + 3) le_rfl)
  refine ⟨hOriginalCone, C, hCS, hCcard, hnone, ?_⟩
  intro u v
  rw [← hOriginalCone]
  exact hclass u v

/-- Original-color nonempty-core reduction, with no supplied structural
premise. The actual saturated cone is constructed from the SAME selected
graph. A nonempty first core has forced size d+3: its large endpoint uses the
SAME coloring's rainbow obstruction, and every middle size violates the
actual count. All original-cone classification data are then derived. -/
theorem original_even_saturated_nonempty_core_reduction {d n q : ℕ}
    (hd : 3 ≤ d) (hn : 2 * d + 2 ≤ n)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (hconn : (selectedGraph χ R).Connected)
    (hno : ∀ P : (pathGraph (2 * d + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow P.toHom χ)
    (hq : max ((2 * d).choose 2 + 1)
      ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 2) < q) :
    ∃ H : SimpleGraph (Option (Fin n)),
      cone (selectedGraph χ R) ≤ H ∧
      (∀ m, 2 * d + 3 ≤ m → (cycleGraph m).Free H) ∧
      (∀ z, (H.induce {w | w ≠ z}).Connected) ∧
      (∀ u v, u ≠ v → ¬ H.Adj u v →
        ∃ m, 2 * d + 3 ≤ m ∧ Nonempty ((cycleGraph m).Copy
          (H ⊔ fromEdgeSet {s(u, v)}))) ∧
      n + q ≤ Nat.card H.edgeSet ∧
      ((degreeCore H (d + 1)).Nonempty →
        (degreeCore H (d + 1)).card = d + 3 ∧
        H = cone (selectedGraph χ R) ∧
        ∃ C : Finset (Option (Fin n)), C ⊆ degreeCore H (d + 1) ∧
          C.card = d ∧ none ∈ C ∧
          ∀ u v, (cone (selectedGraph χ R)).Adj u v ↔ u ≠ v ∧
            ((u ∈ degreeCore H (d + 1) ∧ v ∈ degreeCore H (d + 1)) ∨
              (u ∉ degreeCore H (d + 1) ∧ v ∈ C) ∨
              (v ∉ degreeCore H (d + 1) ∧ u ∈ C))) := by
  classical
  let M := selectedGraph χ R
  have hk : 5 ≤ 2 * d + 2 := by omega
  have hMfree : (pathGraph (2 * d + 2)).Free M :=
    selectedGraph_free (pathGraph (2 * d + 2)) χ R hno
  have hc := UniformConeStructure1105.finite_connected_path_free_cone
    M hk hn hconn hMfree
  have hN : Fintype.card (Option (Fin n)) = n + 1 := by simp
  have hK : 5 ≤ 2 * d + 3 := by omega
  have hKN : 2 * d + 3 ≤ Fintype.card (Option (Fin n)) := by rw [hN]; omega
  have hCfree : ∀ m, 2 * d + 3 ≤ m → (cycleGraph m).Free (cone M) := by
    intro m hm
    exact hc.2.2.1 m (by omega)
  have hCdelete : ∀ z, ((cone M).induce {w | w ≠ z}).Connected := by
    intro z
    exact hc.2.1 z
  obtain ⟨H, hCH, hfree, hdelete, hsat, hclique, _hupper⟩ :=
    CoreSizeUpper1105.exists_saturated_small_core
      (cone M) hK hKN hCfree hCdelete
  have hhalf : (2 * d + 3 - 1) / 2 = d + 1 := by omega
  rw [hhalf] at hclique
  have hMcount : Nat.card M.edgeSet = q := by
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using
      selectedGraph_card_edgeFinset χ R
  have hConeCount : Nat.card (cone M).edgeSet = Nat.card M.edgeSet + n := by
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hc.2.2.2
  have hEdges : Nat.card (cone M).edgeSet ≤ Nat.card H.edgeSet := by
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using
      (Finset.card_le_card (SimpleGraph.edgeFinset_mono hCH))
  have hlower : n + q ≤ Nat.card H.edgeSet := by
    calc
      n + q = Nat.card M.edgeSet + n := by rw [hMcount]; omega
      _ = Nat.card (cone M).edgeSet := hConeCount.symm
      _ ≤ Nat.card H.edgeSet := hEdges
  have hinterval : (degreeCore H (d + 1)).Nonempty →
      d + 3 ≤ (degreeCore H (d + 1)).card ∧
      (degreeCore H (d + 1)).card ≤ 2 * d := by
    intro hnonempty
    have hnonempty' : (degreeCore H ((2 * d + 3 - 1) / 2)).Nonempty := by
      rwa [hhalf]
    have hsize := CoreSizeUpper1105.nonempty_core_size_interval
      H hK hKN hfree hdelete hsat hnonempty'
    rw [hhalf] at hsize
    have htop : (degreeCore H (d + 1)).card ≠ 2 * d + 1 := by
      intro heq
      exact top_core_impossible hd hn χ R hno hq H hCH hfree hdelete
        (degreeCore H (d + 1)) hclique heq
    constructor <;> omega
  refine ⟨H, hCH, hfree, hdelete, hsat, hlower, ?_⟩
  intro hnonempty
  have hrange := hinterval hnonempty
  have hsmall : (degreeCore H (d + 1)).card = d + 3 := by
    by_contra hne
    have hrLower : d + 4 ≤ (degreeCore H (d + 1)).card := by omega
    have hd4 : 4 ≤ d := by omega
    have hnonempty' : (degreeCore H ((2 * d + 3 - 1) / 2)).Nonempty := by
      rwa [hhalf]
    have hcount := SecondCoreCount1105.nonempty_core_edge_bound
      H hK hKN hfree hdelete hsat hnonempty'
    rw [hhalf, hN] at hcount
    have hscalar := EvenIntermediateCoreScalar1105.intermediate_core_count_le_original_even_threshold
      d n (degreeCore H (d + 1)).card hd4 hn hrLower hrange.2
    have hbound : Nat.card H.edgeSet ≤ n + max ((2 * d).choose 2 + 1)
        ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 2) :=
      le_trans hcount hscalar
    omega
  exact ⟨hsmall, small_core_original_classification hd hn χ R hq H hCH hfree
    hdelete hsat hlower hsmall⟩

/-- The original SAME-color nonempty first-core branch is impossible above
the literal even threshold. The original exceptional-family equivalence and
the two actual independent-side vertices are derived internally; the removed
representative edge remains the actual owner of the inserted original color.
No claim is made here for the empty first-core branch. -/
theorem original_even_saturated_first_core_empty {d n q : ℕ}
    (hd : 3 ≤ d) (hn : 2 * d + 2 ≤ n)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (hconn : (selectedGraph χ R).Connected)
    (hno : ∀ P : (pathGraph (2 * d + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow P.toHom χ)
    (hq : max ((2 * d).choose 2 + 1)
      ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 2) < q) :
    ∃ H : SimpleGraph (Option (Fin n)),
      cone (selectedGraph χ R) ≤ H ∧
      (∀ m, 2 * d + 3 ≤ m → (cycleGraph m).Free H) ∧
      (∀ z, (H.induce {w | w ≠ z}).Connected) ∧
      (∀ u v, u ≠ v → ¬ H.Adj u v →
        ∃ m, 2 * d + 3 ≤ m ∧ Nonempty ((cycleGraph m).Copy
          (H ⊔ fromEdgeSet {s(u, v)}))) ∧
      n + q ≤ Nat.card H.edgeSet ∧ degreeCore H (d + 1) = ∅ := by
  classical
  obtain ⟨H, hCH, hfree, hdelete, hsat, hlower, hnonempty⟩ :=
    original_even_saturated_nonempty_core_reduction hd hn χ R hconn hno hq
  refine ⟨H, hCH, hfree, hdelete, hsat, hlower, ?_⟩
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hfirst
  obtain ⟨hScard, _hConeEq, C, hCS, hCcard, hapex, hclass⟩ := hnonempty hfirst
  obtain ⟨phi, hselected⟩ :=
    EvenSelectedFamilyIdentification1105.exists_family_pullback_of_actual_cone_classification
      n d (selectedGraph χ R) (degreeCore H (d + 1)) C (by omega)
      hn hCS hScard hCcard hapex hclass
  let u : Fin (n - d - 2) := ⟨0, by omega⟩
  let v : Fin (n - d - 2) := ⟨1, by omega⟩
  have huv : u ≠ v := by
    intro heq
    have hval := congrArg Fin.val heq
    change 0 = 1 at hval
    omega
  have hRainbow := ErdosProblems.EvenExceptionExchange.exists_original_rainbow_path_of_selected_comap_eq_family
    (d - 1) (n - d - 2) (by omega) (by omega) χ R phi hselected u v huv
  have hpath : 2 * (d - 1) + 4 = 2 * d + 2 := by omega
  rw [hpath] at hRainbow
  obtain ⟨P, hP⟩ := hRainbow
  exact hno P hP

end ErdosProblems.PathUpperReduction.EvenOriginalNonemptyCore1105
