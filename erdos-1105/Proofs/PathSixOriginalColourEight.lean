module

public import PathUpperDenseConnectedRepresentativeV2
public import PathDegreeClosedSupergraph
public import PathSpanningNonuniversalSlots
public import PathAOneSlotS1
public import FinSixNonuniversalTwoJoin
public import FinSixActualK23Extractor
public import PathSixRepresentativeTransfer
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic

@[expose] public section

/-! Composition for the original six-vertex host. No all-host assertion. -/

namespace ErdosProblems.PathSixOriginalColourEight

open SimpleGraph
open ErdosProblems.PathUpperReduction
open ErdosProblems.AntiRamseyPathSixTransfer
open ErdosProblems.AntiRamseyPathSixK23Transfer

theorem starCore_of_actual_s1_shape
    (H : SimpleGraph (Fin 6)) (L : Finset (Fin 6)) (hL : L.card = 2)
    (w : Fin 6) (hw : w ∉ L)
    (hshape : ∀ x y, H.Adj x y ↔ x ≠ y ∧
      ((x ∉ L ∧ y ∉ L) ∨ (x ∈ L ∧ y = w) ∨ (y ∈ L ∧ x = w))) :
    ∃ u : Fin 6 → Fin 6, Function.Injective u ∧ RepresentativeStarCoreOn H u := by
  classical
  let C : Finset (Fin 6) := Lᶜ
  have hC : C.card = 4 := by
    simpa only [Fintype.card_fin, hL] using Finset.card_compl L
  have hwC : w ∈ C := Finset.mem_compl.mpr hw
  let T := C.erase w
  have hT : T.card = 3 := by
    simpa only [hC] using Finset.card_erase_of_mem hwC
  let leaves : Fin 2 → Fin 6 := fun i => ((Finset.equivFinOfCardEq hL).symm i).val
  let others : Fin 3 → Fin 6 := fun i => ((Finset.equivFinOfCardEq hT).symm i).val
  have hLeavesL (i : Fin 2) : leaves i ∈ L :=
    ((Finset.equivFinOfCardEq hL).symm i).property
  have hOthersT (i : Fin 3) : others i ∈ T :=
    ((Finset.equivFinOfCardEq hT).symm i).property
  have hLeaves : Function.Injective leaves := by
    intro i j heq
    apply (Finset.equivFinOfCardEq hL).symm.injective
    exact Subtype.ext heq
  have hOthers : Function.Injective others := by
    intro i j heq
    apply (Finset.equivFinOfCardEq hT).symm.injective
    exact Subtype.ext heq
  let hub : Fin 1 → Fin 6 := fun _ => w
  have hHub : Function.Injective hub := fun _i _j _h => Subsingleton.elim _ _
  let core : Fin 4 → Fin 6 := Fin.append hub others
  have hCore : Function.Injective core := by
    apply Fin.append_injective_iff.mpr
    refine ⟨hHub, hOthers, ?_⟩
    intro i j heq
    exact (Finset.mem_erase.mp (hOthersT j)).1 heq.symm
  have hCoreC (i : Fin 4) : core i ∈ C := by
    refine Fin.addCases (m := 1) (n := 3) (fun j => ?_) (fun j => ?_) i
    · simpa only [core, Fin.append_left, hub] using hwC
    · simpa only [core, Fin.append_right] using (Finset.mem_erase.mp (hOthersT j)).2
  have hCoreEdge (i j : Fin 4) (hij : i ≠ j) : H.Adj (core i) (core j) :=
    (hshape _ _).mpr ⟨hCore.ne hij,
      Or.inl ⟨Finset.mem_compl.mp (hCoreC i), Finset.mem_compl.mp (hCoreC j)⟩⟩
  have hLeafEdge (i : Fin 2) : H.Adj (leaves i) w := by
    apply (hshape _ _).mpr
    refine ⟨?_, Or.inr (Or.inl ⟨hLeavesL i, rfl⟩)⟩
    intro heq
    exact hw (heq ▸ hLeavesL i)
  let u : Fin 6 → Fin 6 := Fin.append leaves core
  have hu : Function.Injective u := by
    apply Fin.append_injective_iff.mpr
    refine ⟨hLeaves, hCore, ?_⟩
    intro i j heq
    exact (Finset.mem_compl.mp (hCoreC j)) (heq ▸ hLeavesL i)
  refine ⟨u, hu, ?_⟩
  constructor
  · change H.Adj (core 0) (core 1)
    exact hCoreEdge 0 1 (by decide)
  · change H.Adj (core 0) (core 2)
    exact hCoreEdge 0 2 (by decide)
  · change H.Adj (core 0) (core 3)
    exact hCoreEdge 0 3 (by decide)
  · change H.Adj (core 1) (core 2)
    exact hCoreEdge 1 2 (by decide)
  · change H.Adj (core 1) (core 3)
    exact hCoreEdge 1 3 (by decide)
  · change H.Adj (core 2) (core 3)
    exact hCoreEdge 2 3 (by decide)
  · change H.Adj (leaves 0) w
    exact hLeafEdge 0
  · change H.Adj (leaves 1) w
    exact hLeafEdge 1

/-- The original six-vertex coloring cannot have eight or more colors and
avoid every rainbow six-vertex path. All graph/owner witnesses are derived. -/
theorem no_surjective_no_rainbow_path_six_palette_ge_eight
    {q : ℕ} (hq : 8 ≤ q)
    (χ : TopEdgeLabeling (Fin 6) (Fin q)) (hχ : Function.Surjective χ)
    (hno : ∀ f : (pathGraph 6).Copy (⊤ : SimpleGraph (Fin 6)),
      ¬ IsRainbow f.toHom χ) : False := by
  classical
  have hDensity : (6 - 2).choose 2 + 2 ≤ q := by change 8 ≤ q; exact hq
  obtain ⟨r, hGconn⟩ := exists_connected_representative_of_dense_palette χ hχ
    (by decide) hDensity
  let G := selectedGraph χ r
  have hGfree : (pathGraph 6).Free G := selectedGraph_free (pathGraph 6) χ r hno
  have hGcount : G.edgeFinset.card = q := selectedGraph_card_edgeFinset χ r
  have hGedges : 8 ≤ G.edgeFinset.card := by rw [hGcount]; exact hq
  obtain ⟨H, hGH, hHfree, hclosed⟩ :=
    ErdosProblems.PathDegreeClosedSupergraph.exists_degree_closed_path_free_supergraph
      (by decide : 3 ≤ 6) G hGfree
  have hHconn : H.Connected := SimpleGraph.Connected.mono hGH hGconn
  have hHedges : 8 ≤ H.edgeFinset.card :=
    hGedges.trans (Finset.card_le_card (SimpleGraph.edgeFinset_mono hGH))
  have hneTop : H ≠ ⊤ := by
    intro htop
    apply hHfree
    rw [htop]
    exact ⟨Copy.ofLE (pathGraph 6) (⊤ : SimpleGraph (Fin 6)) le_top⟩
  obtain ⟨a, L, ha, htwo, hLcard, hLdeg, _hCount, hCap⟩ :=
    spanning_degree_slots_with_nonuniversal_cap 6 (by decide) H hHconn hneTop
      (by
        intro x y hxy hnon
        convert hclosed x y hxy hnon using 1
        congr 2 <;> exact Subsingleton.elim _ _)
  have hcases : a = 1 ∨ a = 2 := by omega
  rcases hcases with haOne | haTwo
  · subst a
    have hLtwo : L.card = 2 := by simpa using hLcard
    have hHthreshold : (6 - 2).choose 2 + 2 ≤ H.edgeFinset.card := hHedges
    obtain ⟨w, hw, _hDegreeOne, hHcount, _hCoreTop, _hIndependent, hShape⟩ :=
      a_one_slots_force_s1 6 (by decide) H hHconn
        (by
          intro x y hxy hnon
          convert hclosed x y hxy hnon using 1
          congr 2 <;> exact Subsingleton.elim _ _)
        L hLtwo hLdeg hHthreshold
    change H.edgeFinset.card = 8 at hHcount
    have hEdgeEq : G.edgeFinset = H.edgeFinset :=
      Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono hGH) (by omega)
    have hGeqH : G = H := SimpleGraph.edgeFinset_inj.mp hEdgeEq
    obtain ⟨u, hu, hStarH⟩ := starCore_of_actual_s1_shape H L hLtwo w hw hShape
    have hStarG : RepresentativeStarCoreOn (selectedGraph χ r) u := by
      change RepresentativeStarCoreOn G u
      rw [hGeqH]
      exact hStarH
    obtain ⟨f, hf⟩ := rainbow_path_six_of_representative_starCore χ r u hu hStarG
    exact hno f hf
  · subst a
    obtain ⟨U, _hUniversals, hUtwo, _hNeighbors, hShape, hHcount⟩ :=
      ErdosProblems.PathUpperFinSixJoin.fin_six_join_of_nonuniversal_degree_cap
        H hneTop hHedges (by intro x hx; exact hCap x hx)
    obtain ⟨u, hu, hK23⟩ :=
      ErdosProblems.PathUpperFinSixExtractor.representative_k23_of_dense_fin_six_join
        G H hGH
        (by
          convert hGedges using 1
          (congr 2; exact Subsingleton.elim _ _))
        U hUtwo hShape hHcount
    obtain ⟨f, hf⟩ := rainbow_path_six_of_representative_k23 χ r u hu hK23
    exact hno f hf

end ErdosProblems.PathSixOriginalColourEight

