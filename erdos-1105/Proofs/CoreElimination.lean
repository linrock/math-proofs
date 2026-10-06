module

public import CountCoreBasis
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.SetTheory.Cardinal.Finite
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Actual greatest-core elimination. -/

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis

namespace ErdosProblems.PathUpperReduction.CoreElimination

variable {V : Type*} [Fintype V]

noncomputable def withinEdges (G : SimpleGraph V) (S : Finset V) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter (fun e => e.toFinset ⊆ S)

noncomputable def withinDegree (G : SimpleGraph V) (S : Finset V) (x : V) : ℕ := by
  classical
  exact (S.filter (fun z => G.Adj x z)).card

theorem withinEdges_card_le_choose (G : SimpleGraph V) (S : Finset V) :
    (withinEdges G S).card ≤ S.card.choose 2 := by
  classical
  unfold withinEdges
  rw [G.card_filter_edgeFinset_toFinset_subset S]
  have hcard : Fintype.card (↑S : Set V) = S.card := by
    exact Fintype.card_coe S
  simpa only [hcard] using
    (G.induce (↑S : Set V)).card_edgeFinset_le_card_choose_two

section Erase

theorem withinEdges_erase_eq_filter (G : SimpleGraph V) (S : Finset V) (x : V) :
    letI : DecidableEq V := Classical.decEq V
    withinEdges G (S.erase x) = (withinEdges G S).filter (fun e => x ∉ e) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨heG, hsub⟩ := Finset.mem_filter.mp he
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨heG, ?_⟩, ?_⟩
    · exact hsub.trans (Finset.erase_subset x S)
    · intro hxe
      have hxErase := hsub (Sym2.mem_toFinset.mpr hxe)
      simp at hxErase
  · intro he
    obtain ⟨heS, hnot⟩ := Finset.mem_filter.mp he
    obtain ⟨heG, hsub⟩ := Finset.mem_filter.mp heS
    refine Finset.mem_filter.mpr ⟨heG, ?_⟩
    intro z hz
    refine Finset.mem_erase.mpr ⟨?_, hsub hz⟩
    intro hzx
    exact hnot (hzx ▸ Sym2.mem_toFinset.mp hz)

theorem withinEdges_erase_ledger (G : SimpleGraph V) (S : Finset V) (x : V)
    (hx : x ∈ S) :
    letI : DecidableEq V := Classical.decEq V
    (withinEdges G S).card =
      (withinEdges G (S.erase x)).card + withinDegree G S x := by
  classical
  have hIncident :
      ((withinEdges G S).filter (fun e => x ∈ e)).card =
        (S.filter (fun z => G.Adj x z)).card := by
    symm
    apply Finset.card_bij (fun z _hz => s(x, z))
    · intro z hz
      obtain ⟨hzS, hxz⟩ := Finset.mem_filter.mp hz
      refine Finset.mem_filter.mpr ⟨?_, Sym2.mem_mk_left _ _⟩
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · simpa only [mem_edgeFinset, mem_edgeSet] using hxz
      · rw [Sym2.toFinset_mk_eq]
        exact Finset.insert_subset_iff.mpr ⟨hx, Finset.singleton_subset_iff.mpr hzS⟩
    · intro z₁ _hz₁ z₂ _hz₂ hpair
      exact Sym2.congr_right.mp hpair
    · intro e he
      obtain ⟨heS, hxe⟩ := Finset.mem_filter.mp he
      obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.mp hxe
      obtain ⟨heG, hsub⟩ := Finset.mem_filter.mp heS
      have hzS : z ∈ S := hsub (by simp [Sym2.toFinset_mk_eq])
      have hxz : G.Adj x z := by simpa only [mem_edgeFinset, mem_edgeSet] using heG
      exact ⟨z, Finset.mem_filter.mpr ⟨hzS, hxz⟩, rfl⟩
  have hPartition := (withinEdges G S).card_filter_add_card_filter_not
    (fun e => x ∈ e)
  rw [hIncident, ← withinEdges_erase_eq_filter G S x] at hPartition
  simpa only [withinDegree, Nat.add_comm] using hPartition.symm

end Erase

theorem outside_core_low_degree (G : SimpleGraph V) (d : ℕ) (S : Finset V)
    (hC : degreeCore G d ⊆ S)
    (hlarge : max d (degreeCore G d).card < S.card) :
    ∃ x, x ∈ S ∧ x ∉ degreeCore G d ∧ withinDegree G S x ≤ d := by
  classical
  by_contra hnone
  have hgood : GoodCore G d S := by
    intro x hxS
    change d < withinDegree G S x
    by_cases hxC : x ∈ degreeCore G d
    · have hCore : d < withinDegree G (degreeCore G d) x := by
        simpa only [withinDegree] using degree_core_good G d x hxC
      have hmono : withinDegree G (degreeCore G d) x ≤ withinDegree G S x := by
        unfold withinDegree
        apply Finset.card_le_card
        intro z hz
        obtain ⟨hzC, hxz⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨hC hzC, hxz⟩
      exact hCore.trans_le hmono
    · have hnot : ¬ withinDegree G S x ≤ d := by
        intro hlow
        exact hnone ⟨x, hxS, hxC, hlow⟩
      omega
  have hSC : S ⊆ degreeCore G d := good_subset_core G d S hgood
  have hcard : S.card ≤ (degreeCore G d).card := Finset.card_le_card hSC
  have hmax : (degreeCore G d).card ≤ max d (degreeCore G d).card :=
    Nat.le_max_right _ _
  omega

theorem core_induced_edge_bound (G : SimpleGraph V) (d : ℕ) (S : Finset V)
    (hC : degreeCore G d ⊆ S)
    (hM : max d (degreeCore G d).card ≤ S.card) :
    (withinEdges G S).card ≤
      (max d (degreeCore G d).card).choose 2 +
        d * (S.card - max d (degreeCore G d).card) := by
  classical
  let C := degreeCore G d
  let M := max d C.card
  let P : Finset V → Prop := fun T => C ⊆ T → M ≤ T.card →
    (withinEdges G T).card ≤ M.choose 2 + d * (T.card - M)
  have hP : ∀ T, P T := by
    intro T
    refine Finset.strongInductionOn T ?_
    intro T ih
    dsimp only [P]
    intro hCT hMT
    by_cases hbase : T.card = M
    · have hclique := withinEdges_card_le_choose G T
      simpa only [hbase, Nat.sub_self, Nat.mul_zero, Nat.add_zero] using hclique
    · have hlarge : M < T.card := by omega
      obtain ⟨x, hxT, hxC, hlow⟩ := outside_core_low_degree G d T hCT hlarge
      have hCerase : C ⊆ T.erase x := by
        intro z hzC
        apply Finset.mem_erase.mpr
        refine ⟨?_, hCT hzC⟩
        intro hzx
        exact hxC (hzx ▸ hzC)
      have hcardErase : (T.erase x).card = T.card - 1 :=
        Finset.card_erase_of_mem hxT
      have hMerase : M ≤ (T.erase x).card := by omega
      have hIH := ih (T.erase x) (Finset.erase_ssubset hxT) hCerase hMerase
      have hledger := withinEdges_erase_ledger G T x hxT
      have hsteps : ((T.erase x).card - M) + 1 = T.card - M := by omega
      calc
        (withinEdges G T).card =
            (withinEdges G (T.erase x)).card + withinDegree G T x := hledger
        _ ≤ (M.choose 2 + d * ((T.erase x).card - M)) + d :=
          Nat.add_le_add hIH hlow
        _ = M.choose 2 + d * (((T.erase x).card - M) + 1) := by
          rw [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
        _ = M.choose 2 + d * (T.card - M) := by rw [hsteps]
  exact hP S hC hM

theorem degree_core_edge_bound (G : SimpleGraph V) (d : ℕ)
    (hd : d ≤ Nat.card V) :
    Nat.card G.edgeSet ≤
      (max d (degreeCore G d).card).choose 2 +
        d * (Nat.card V - max d (degreeCore G d).card) := by
  classical
  have hdUniv : d ≤ (Finset.univ : Finset V).card := by
    simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using hd
  have hCoreUniv : degreeCore G d ⊆ (Finset.univ : Finset V) :=
    Finset.subset_univ _
  have hMUniv : max d (degreeCore G d).card ≤ (Finset.univ : Finset V).card :=
    max_le hdUniv (Finset.card_le_card hCoreUniv)
  have hbound := core_induced_edge_bound G d Finset.univ hCoreUniv hMUniv
  have hEdgesUniv : withinEdges G Finset.univ = G.edgeFinset := by
    ext e
    simp [withinEdges]
  simpa only [hEdgesUniv, Finset.card_univ, Nat.card_eq_fintype_card, G.card_edgeSet]
    using hbound

end ErdosProblems.PathUpperReduction.CoreElimination
