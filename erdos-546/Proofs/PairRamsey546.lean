module

public import MonochromaticPairs546
public import RamseyBasics546
public import DegreeDeletion546
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt


@[expose] public section

/-! The exact finite Ramsey bridge and the elementary small-edge baseline.
These are ingredients of the sparse bound, not its missing amplification step. -/

namespace Erdos546

open SimpleGraph Finset

theorem graphRamseyWitness_choose {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    GraphRamseyWitness G H ((Fintype.card V + Fintype.card W).choose (Fintype.card V)) := by
  classical
  intro C
  rcases exists_monoPair C (Fintype.card V) (Fintype.card W) 0 univ (by simp) with hG | hH
  · rcases hG with ⟨X, Y, _, _, hp, hX, _⟩
    exact Or.inl (isContained_of_clique G C X hp.2.1 (by omega))
  · rcases hH with ⟨X, Y, _, _, hp, hX, _⟩
    exact Or.inr (isContained_of_clique H Cᶜ X hp.2.1 (by omega))

theorem graphRamsey_le_choose {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    SimpleGraph.graphRamsey G H ≤ (Fintype.card V + Fintype.card W).choose (Fintype.card V) :=
  graphRamsey_le_of_witness (graphRamseyWitness_choose G H)

theorem graphRamseyWitness {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    GraphRamseyWitness G H (SimpleGraph.graphRamsey G H) :=
  graphRamsey_witness_of_exists ⟨_, graphRamseyWitness_choose G H⟩

theorem graphRamsey_le_two_pow {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    SimpleGraph.graphRamsey G H ≤ 2 ^ (Fintype.card V + Fintype.card W) :=
  (graphRamsey_le_choose G H).trans (Nat.choose_le_two_pow _ _)

theorem diagonalGraphRamsey_le_two_pow {V : Type*} [Fintype V]
    (G : SimpleGraph V) :
    SimpleGraph.diagonalGraphRamsey G ≤ 2 ^ (2 * Fintype.card V) := by
  simpa [SimpleGraph.diagonalGraphRamsey, two_mul] using graphRamsey_le_two_pow G G

theorem diagonalGraphRamsey_le_two_pow_edges {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hno : ∀ v, 0 < G.degree v) :
    SimpleGraph.diagonalGraphRamsey G ≤ 2 ^ (4 * G.edgeSet.ncard) := by
  have hcard := card_vertices_le_twice_edges G (fun v => (G.degree_pos v).mp (hno v))
  have he : G.edgeFinset.card = G.edgeSet.ncard := by
    rw [← G.coe_edgeFinset, Set.ncard_coe_finset]
  rw [he] at hcard
  exact (diagonalGraphRamsey_le_two_pow G).trans
    (Nat.pow_le_pow_right (by decide) (by omega))

/-- The exact quantifiers requested in the Formal Conjectures #546 theorem. -/
def SparseRamseyStatement : Prop :=
  ∃ C > (0 : ℝ), ∀ (m : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v, 0 < G.degree v) → G.edgeSet.ncard = m →
      (SimpleGraph.diagonalGraphRamsey G : ℝ) ≤ 2 ^ (C * Real.sqrt m)

/-- Complete-graph Ramsey handles targets with at most `K sqrt(m)` vertices.
The no-isolated-vertex hypothesis alone does not provide this size bound. -/
theorem sparse_bound_of_vertex_bound {V : Type*} [Fintype V]
    (G : SimpleGraph V) (m : ℕ) {K : ℝ}
    (hcard : (Fintype.card V : ℝ) ≤ K * Real.sqrt m) :
    (SimpleGraph.diagonalGraphRamsey G : ℝ) ≤ 2 ^ ((2 * K) * Real.sqrt m) := by
  calc
    (SimpleGraph.diagonalGraphRamsey G : ℝ) ≤
        (2 : ℝ) ^ (2 * Fintype.card V) := by
      exact_mod_cast diagonalGraphRamsey_le_two_pow G
    _ = (2 : ℝ) ^ ((2 * Fintype.card V : ℕ) : ℝ) :=
      (Real.rpow_natCast _ _).symm
    _ ≤ 2 ^ ((2 * K) * Real.sqrt m) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; nlinarith)

/-- The elementary Ramsey bound closes the finite small-edge branch of
Sudakov's argument. It includes `m = 0` with the same statement. -/
theorem sparse_bound_small_edges {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ)
    (hno : ∀ v, 0 < G.degree v) (hedges : G.edgeSet.ncard = m)
    (hm : m ≤ 3600) :
    (SimpleGraph.diagonalGraphRamsey G : ℝ) ≤ 2 ^ ((240 : ℝ) * Real.sqrt m) := by
  have hnat := diagonalGraphRamsey_le_two_pow_edges G hno
  rw [hedges] at hnat
  have hs0 := Real.sqrt_nonneg (m : ℝ)
  have hsq := Real.sq_sqrt (Nat.cast_nonneg m)
  have hmreal : (m : ℝ) ≤ 3600 := by exact_mod_cast hm
  have hs60 : Real.sqrt (m : ℝ) ≤ 60 := by nlinarith
  have hprod : 0 ≤ Real.sqrt (m : ℝ) * (60 - Real.sqrt (m : ℝ)) :=
    mul_nonneg hs0 (by linarith)
  calc
    (SimpleGraph.diagonalGraphRamsey G : ℝ) ≤ (2 : ℝ) ^ (4 * m) := by
      exact_mod_cast hnat
    _ = (2 : ℝ) ^ ((4 * m : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ 2 ^ ((240 : ℝ) * Real.sqrt m) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; nlinarith)

#print axioms graphRamseyWitness_choose
#print axioms graphRamsey_le_choose
#print axioms graphRamseyWitness
#print axioms graphRamsey_le_two_pow
#print axioms diagonalGraphRamsey_le_two_pow
#print axioms diagonalGraphRamsey_le_two_pow_edges
#print axioms sparse_bound_of_vertex_bound
#print axioms sparse_bound_small_edges

end Erdos546
