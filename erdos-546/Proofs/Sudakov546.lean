module

public import Amplification546
public import Initialization546
public import PairIteration546
public import PairRamsey546
public import SudakovScalars546
public import SudakovScalarsSuccessor546


@[expose] public section

/-! Candidate assembly of Sudakov's uniform sparse Ramsey theorem.
This file and its entire dependency cone require canonical compilation and
transitive axiom audit before any complete formal proof is claimed. The
larger constant pays all natural ceiling and weakened-cut losses. -/

namespace Erdos546

open SimpleGraph Finset

theorem sparse_graph_ramsey_witness {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) (hm : 64 ≤ m)
    (hedges : G.edgeSet.ncard = m) (hvertices : Fintype.card V ≤ 2 * m) :
    GraphRamseyWitness G G (Nat.ceil ((2 : ℝ)^(2000 * Real.sqrt m))) := by
  classical
  intro H
  by_contra hnot
  have hfree : ¬ G.IsContained H := fun hc => hnot (Or.inl hc)
  have hfree_compl : ¬ G.IsContained Hᶜ := fun hc => hnot (Or.inr hc)
  let W := Fin (Nat.ceil ((2 : ℝ)^(2000 * Real.sqrt m)))
  let State := Finset W × Finset W
  let valid : State → Prop := fun σ => MonoPair H σ.1 σ.2 ∨ MonoPair Hᶜ σ.1 σ.2
  let clique : State → ℝ := fun σ => σ.1.card
  let reservoir : State → ℝ := fun σ => σ.2.card
  let A := finalAmplificationParameter546 m
  have hA : 3 ≤ A := finalAmplificationParameter546_ge_three m hm
  have hhost : (2 : ℝ)^(2000 * Real.sqrt m) ≤ Fintype.card W := by
    simpa [W] using Nat.le_ceil ((2 : ℝ)^(2000 * Real.sqrt m))
  obtain ⟨X, Y, hmono, hclique, hreservoir⟩ := initial_pair_for_sparse_ramsey H m hm hhost
  have hnext : ∀ a, 3 ≤ a → a < nextAmplificationParameter546 a := by
    intro a ha
    dsimp [nextAmplificationParameter546]
    omega
  have hcube : ∀ a, 3 ≤ a →
      (nextAmplificationParameter546 a : ℝ)^3 ≤ (2 : ℝ)^(2 * a) := by
    intro a ha
    exact_mod_cast nat_rounded_amplification_growth a ha
  have hamp : ∀ (a : ℕ) (σ : State), 3 ≤ a → a ≤ A → valid σ →
      (a : ℝ)^3 * Real.sqrt m ≤ clique σ →
      (2 : ℝ)^(500 * Real.sqrt m / a) ≤ reservoir σ →
      ∃ τ, valid τ ∧ (2 : ℝ)^(2 * a) * Real.sqrt m ≤ clique τ ∧
        reservoir σ * (2 : ℝ)^(-400 * Real.sqrt m / a) ≤ reservoir τ := by
    intro a σ ha haA hv hc hr
    rcases hv with hv | hv
    · obtain ⟨P, Q, _, _, hPQ, hPc, hQr⟩ := quantitative_monoPair_amplification
        G H m a hm hedges hvertices ha haA hv hfree hc hr
      exact ⟨(P, Q), hPQ, hPc, hQr⟩
    · obtain ⟨P, Q, _, _, hPQ, hPc, hQr⟩ := quantitative_monoPair_amplification
        G Hᶜ m a hm hedges hvertices ha haA hv hfree_compl hc hr
      refine ⟨(P, Q), ?_, hPc, hQr⟩
      rcases hPQ with hPQ | hPQ
      · exact Or.inr hPQ
      · exact Or.inl (by simpa using hPQ)
  obtain ⟨τ, hτ, hτc⟩ := amplification_iteration valid clique reservoir A 500 400
    (Real.sqrt m) nextAmplificationParameter546 hA (by norm_num) (by norm_num)
    (Real.sqrt_nonneg _) hnext (fun a _ => nextAmplificationParameter546_ge a)
    hcube (X, Y) hmono hclique hreservoir hamp
  have hcardR : (Fintype.card V : ℝ) ≤ τ.1.card := by
    calc
      (Fintype.card V : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hvertices
      _ ≤ (2 : ℝ)^(2 * A) * Real.sqrt m := finalAmplificationParameter546_clique_size m hm
      _ ≤ τ.1.card := hτc
  have hcard : Fintype.card V ≤ τ.1.card := by exact_mod_cast hcardR
  rcases hτ with hτ | hτ
  · exact hfree (isContained_of_clique G H τ.1 hτ.2.1 hcard)
  · exact hfree_compl (isContained_of_clique G Hᶜ τ.1 hτ.2.1 hcard)

theorem sudakov_sparse_bound {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ)
    (hno : ∀ v, 0 < G.degree v) (hedges : G.edgeSet.ncard = m) :
    (SimpleGraph.diagonalGraphRamsey G : ℝ) ≤ (2 : ℝ)^(4000 * Real.sqrt m) := by
  classical
  by_cases hsmall : m ≤ 3600
  · exact (sparse_bound_small_edges G m hno hedges hsmall).trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
        nlinarith [Real.sqrt_nonneg (m : ℝ)]))
  have hm : 64 ≤ m := by omega
  have hvertices := card_vertices_le_twice_edges G (fun v => (G.degree_pos v).mp (hno v))
  have he : G.edgeFinset.card = m := by
    rw [← hedges, ← G.coe_edgeFinset, Set.ncard_coe_finset]
  rw [he] at hvertices
  have hnat := diagonalGraphRamsey_le_of_witness
    (sparse_graph_ramsey_witness G m hm hedges hvertices)
  let s : ℝ := Real.sqrt m
  let P : ℝ := (2 : ℝ)^(2000 * s)
  have hs : (1 : ℝ) ≤ s := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact_mod_cast (show 1 ≤ m by omega)
  have hP1 : 1 ≤ P := by
    calc
      (1 : ℝ) = (2 : ℝ)^((0 : ℝ)) := by simp
      _ ≤ P := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by positivity)
  have hceil : (Nat.ceil P : ℝ) < P + 1 := Nat.ceil_lt_add_one (by linarith)
  calc
    (SimpleGraph.diagonalGraphRamsey G : ℝ) ≤ Nat.ceil P := by exact_mod_cast hnat
    _ ≤ 2 * P := by linarith
    _ = (2 : ℝ)^(2000 * s + 1) := by
      rw [Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    _ ≤ (2 : ℝ)^(4000 * s) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- The original uniform quantifiers; `True` is the expansion of `answer(True)`.
The definitions in RamseyBasics546 retain the upstream attribution. -/
theorem erdos_546 : True ↔ SparseRamseyStatement := by
  constructor
  · intro _
    refine ⟨4000, by norm_num, ?_⟩
    intro m V _ G _ hno hedges
    exact sudakov_sparse_bound G m hno hedges
  · intro _
    trivial

#print axioms sparse_graph_ramsey_witness
#print axioms sudakov_sparse_bound
#print axioms erdos_546

end Erdos546
