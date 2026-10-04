module

public import ActualRightVertexFinal433

@[expose] public section


/-!
# Exact reduction of the complete manuscript degree bound to fixed left vertices

The actual fixed-right graph degree is now proved unconditionally with
absolute constant `243`; the actual prime-label degree is independently
proved with constant `122`.  Thus the original three-coordinate degree
proposition is equivalent to its genuine fixed-left graph coordinate alone.
The sole remaining degree constant precedes all support and strip parameters.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos689

/-- The sole remaining genuine manuscript graph-degree obligation.  Its
absolute constant is chosen before the switched support, assignment, and
strip parameters, exactly as in the original three-coordinate proposition. -/
def FixedModulusLeftVertexDegreeBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (S : Finset ℕ) (b : ℕ → ℕ) (τ ell : ℝ),
      (∀ s ∈ S, s.Prime ∧ 3 < s ∧ b s % s ≠ 0) →
      0 < τ → 0 < ell → τ + ell < 1 / 10 →
        ∀ᶠ n : ℕ in Filter.atTop, ∀ E : Finset TripleEdge,
          (∀ e ∈ E, manuscriptEdge S b n τ ell e) →
          (∀ x : ℕ, ((E.filter fun e => e.1 = x).card : ℝ) ≤
            C * n / (Real.log n) ^ 2)

/-- The original three-coordinate graph-degree theorem trivially implies its
genuine fixed-left graph restriction. -/
theorem fixedModulusLeftVertexDegreeBound_of_full_degree
    (hdegree : FixedModulusTwoFormDegreeBound) :
    FixedModulusLeftVertexDegreeBound := by
  obtain ⟨C, hC, hdegree⟩ := hdegree
  refine ⟨C, hC, ?_⟩
  intro S b τ ell hsupport hτ hell hstrip
  filter_upwards [hdegree S b τ ell hsupport hτ hell hstrip] with n hn
  intro E hactual
  exact (hn E hactual).1

/-- The sole genuine fixed-left graph-degree bound implies the COMPLETE
original three-coordinate bound: the fixed right and prime-label coordinates
are inserted from their independent unconditional theorems.  One universal
constant `max C 243` suffices for all three coordinates. -/
theorem fixedModulusTwoFormDegreeBound_of_left_vertex_degree
    (hleft : FixedModulusLeftVertexDegreeBound) :
    FixedModulusTwoFormDegreeBound := by
  obtain ⟨C, hC, hleft⟩ := hleft
  let C' : ℝ := max C 243
  have hC' : 0 < C' := lt_of_lt_of_le hC (le_max_left _ _)
  refine ⟨C', hC', ?_⟩
  intro S b τ ell hsupport hτ hell hstrip
  have hprimes : ∀ p ∈ S, p.Prime ∧ 3 < p := by
    intro p hp
    exact ⟨(hsupport p hp).1, (hsupport p hp).2.1⟩
  have hb : ∀ p ∈ S, ¬ p ∣ b p := by
    intro p hp hdivisor
    exact (hsupport p hp).2.2 (Nat.mod_eq_zero_of_dvd hdivisor)
  filter_upwards
    [hleft S b τ ell hsupport hτ hell hstrip,
      manuscriptEdge_actual_right_degree_eventually_le
        S b τ ell hprimes hb hτ,
      manuscriptEdge_actual_label_degree_eventually_le
        S b τ ell hprimes hb hτ] with n hlefts hrights hlabels
  intro E hactual
  refine ⟨?_, ?_, ?_⟩
  · intro x
    calc
      ((E.filter fun e => e.1 = x).card : ℝ) ≤
          C * n / (Real.log n) ^ 2 := hlefts E hactual x
      _ ≤ C' * n / (Real.log n) ^ 2 := by
        dsimp [C']
        gcongr
        exact le_max_left _ _
  · intro y
    calc
      ((E.filter fun e => e.2.1 = y).card : ℝ) ≤
          (243 : ℝ) * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) :=
        hrights E hactual y
      _ = (243 : ℝ) * n / (Real.log n) ^ 2 := by ring
      _ ≤ C' * n / (Real.log n) ^ 2 := by
        dsimp [C']
        gcongr
        exact le_max_right _ _
  · intro z
    calc
      ((E.filter fun e => e.2.2 = z).card : ℝ) ≤
          (122 : ℝ) * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) :=
        hlabels E hactual z
      _ = (122 : ℝ) * n / (Real.log n) ^ 2 := by ring
      _ ≤ C' * n / (Real.log n) ^ 2 := by
        dsimp [C']
        gcongr
        exact (by norm_num : (122 : ℝ) ≤ 243).trans
          (le_max_right _ _)

/-- Exact equivalence: the only unproved coordinate of the original
three-coordinate manuscript graph-degree theorem is the actual fixed-left
vertex bound; neither right vertices nor prime labels remain assumptions. -/
theorem fixedModulusTwoFormDegreeBound_iff_left_vertex_degree :
    FixedModulusTwoFormDegreeBound ↔ FixedModulusLeftVertexDegreeBound :=
  ⟨fixedModulusLeftVertexDegreeBound_of_full_degree,
    fixedModulusTwoFormDegreeBound_of_left_vertex_degree⟩

#print axioms Erdos689.fixedModulusLeftVertexDegreeBound_of_full_degree
#print axioms Erdos689.fixedModulusTwoFormDegreeBound_of_left_vertex_degree
#print axioms Erdos689.fixedModulusTwoFormDegreeBound_iff_left_vertex_degree

end Erdos689
