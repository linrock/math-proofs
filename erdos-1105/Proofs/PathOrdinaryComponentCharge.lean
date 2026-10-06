module

public import PathErdosGallai
public import PathCliqueEGDensityV2
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
A thin ordinary finite-graph caller for the EXISTING
clique/EG density arithmetic. No connectedness, coloring, desired edge cap or
tail packing is a public premise; positive cardinality retains all isolates.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

/-- Every positive finite ordinary P(d+1)-free graph has
the precise multiplied per-component edge-plus-one charge. The elementary
charge arithmetic is reused, rather than reproved here. -/
theorem ordinary_component_charge
    {V : Type*} [Finite V] (G : SimpleGraph V) (d : ℕ)
    (hd : 2 ≤ d) (hv : 1 ≤ Nat.card V)
    (hfree : (pathGraph (d + 1)).Free G) :
    2 * d * (Nat.card G.edgeSet + 1) ≤
      ((d - 1) * d + 2) * Nat.card V := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  have hclique : Nat.card G.edgeSet ≤ (Nat.card V).choose 2 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, G.card_edgeSet]
    exact G.card_edgeFinset_le_card_choose_two
  have hEG := ErdosProblems.PathErdosGallai.erdos_gallai_edge_bound G d hd hfree
  have hcharge := ErdosProblems.PathCliqueEGDensity.clique_eg_density
    d (Nat.card V) (Nat.card G.edgeSet) hd hv hclique hEG
  calc
    2 * d * (Nat.card G.edgeSet + 1) ≤
        (d * (d - 1) + 2) * Nat.card V := hcharge
    _ = ((d - 1) * d + 2) * Nat.card V := by
      rw [Nat.mul_comm d (d - 1)]

/-- The same actual graph charge in the exact real
coefficient used by the arbitrary-tail affine envelope and component sum. This only divides the reused multiplied charge by positive2d. -/
theorem ordinary_component_charge_real
    {V : Type*} [Finite V] (G : SimpleGraph V) (d : ℕ)
    (hd : 2 ≤ d) (hv : 1 ≤ Nat.card V)
    (hfree : (pathGraph (d + 1)).Free G) :
    (Nat.card G.edgeSet : ℝ) + 1 ≤
      (((d : ℝ) - 1) / 2 + 1 / (d : ℝ)) * (Nat.card V : ℝ) := by
  have hcharge := ordinary_component_charge G d hd hv hfree
  have hdsub : (d - 1) + 1 = d := by omega
  have hdsubR : ((d - 1 : ℕ) : ℝ) + 1 = (d : ℝ) := by
    exact_mod_cast hdsub
  have hsub : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by linarith
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast (show 0 < d by omega)
  have hcast : 2 * (d : ℝ) * ((Nat.card G.edgeSet : ℝ) + 1) ≤
      (((d - 1 : ℕ) : ℝ) * (d : ℝ) + 2) * (Nat.card V : ℝ) := by
    exact_mod_cast hcharge
  rw [hsub] at hcast
  apply (mul_le_mul_iff_of_pos_left (by positivity : (0 : ℝ) < 2 * (d : ℝ))).mp
  calc
    2 * (d : ℝ) * ((Nat.card G.edgeSet : ℝ) + 1) ≤
        (((d : ℝ) - 1) * (d : ℝ) + 2) * (Nat.card V : ℝ) := hcast
    _ = 2 * (d : ℝ) *
        ((((d : ℝ) - 1) / 2 + 1 / (d : ℝ)) * (Nat.card V : ℝ)) := by
      field_simp [ne_of_gt hdpos]

end ErdosProblems.PathUpperReduction
