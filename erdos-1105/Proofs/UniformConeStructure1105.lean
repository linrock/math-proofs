module

/- Same-host cone structure used to transfer cycle bounds to path-free graphs. It supplies no sharp cycle bound, stability classification or rainbow exit. -/
public import UniformCone1105
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Fintype.Option
public import Lean.Elab.Tactic.Omega

@[expose] public section

noncomputable section
namespace ErdosProblems.PathUpperReduction.UniformConeStructure1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.UniformCone1105 (cone)
attribute [local instance] Classical.propDecidable

/-- Deleting the apex recovers the entire original carrier and adjacency. -/
def oldVertexIso {V : Type*} (G : SimpleGraph V) :
    G ≃g (cone G).induce ({(none : Option V)}ᶜ : Set (Option V)) where
  toFun v := ⟨some v, by simp⟩
  invFun x := match x with
    | ⟨some v, _⟩ => v
    | ⟨none, h⟩ => False.elim (by simp at h)
  left_inv v := rfl
  right_inv x := by
    rcases x with ⟨x, hx⟩
    cases x with
    | none => simp at hx
    | some v => rfl
  map_rel_iff' := by
    intro u v
    rfl

theorem cone_apex_isUniversal {V : Type*} (G : SimpleGraph V) :
    (cone G).IsUniversal none := by
  intro w hne
  cases w with
  | none => exact False.elim (hne rfl)
  | some v => trivial

theorem cone_connected {V : Type*} (G : SimpleGraph V) :
    (cone G).Connected :=
  Connected.of_isUniversal (cone_apex_isUniversal G)

/-- Deleting an old vertex preserves the actual universal apex. -/
theorem cone_delete_old_connected {V : Type*} (G : SimpleGraph V) (v : V) :
    ((cone G).induce ({(some v : Option V)}ᶜ : Set (Option V))).Connected := by
  let apex : ({(some v : Option V)}ᶜ : Set (Option V)) := ⟨none, by simp⟩
  apply Connected.of_isUniversal (v := apex)
  intro x hne
  change (cone G).Adj none x.val
  rcases x with ⟨x, hx⟩
  cases x with
  | none => exact False.elim (hne (Subtype.ext rfl))
  | some w => trivial

/-- Apex deletion needs exactly original connectedness, not G-v connectedness. -/
theorem cone_delete_apex_connected {V : Type*} (G : SimpleGraph V)
    (hG : G.Connected) :
    ((cone G).induce ({(none : Option V)}ᶜ : Set (Option V))).Connected :=
  (oldVertexIso G).connected_iff.mp hG

theorem cone_all_vertex_deletions_connected {V : Type*} (G : SimpleGraph V)
    (hG : G.Connected) (z : Option V) :
    ((cone G).induce ({z}ᶜ : Set (Option V))).Connected := by
  cases z with
  | none => exact cone_delete_apex_connected G hG
  | some v => exact cone_delete_old_connected G v

theorem cone_neighborFinset_none {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (cone G).neighborFinset none = Finset.univ.image (some : V → Option V) := by
  ext v
  rw [(cone G).mem_neighborFinset]
  cases v <;> simp [cone]

theorem cone_degree_none {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (cone G).degree none = Fintype.card V := by
  change ((cone G).neighborFinset none).card = _
  rw [cone_neighborFinset_none,
    Finset.card_image_of_injective _ (Option.some_injective V)]
  exact Finset.card_univ

/-- Count actual unordered edges and guard the natural subtraction. -/
theorem cone_edgeFinset_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (cone G).edgeFinset.card = G.edgeFinset.card + Fintype.card V := by
  let attached := cone G
  have hold := (oldVertexIso G).card_edgeFinset_eq
  have hinduced := SimpleGraph.card_edgeFinset_induce_compl_singleton attached none
  have hdeleted := SimpleGraph.card_edgeFinset_deleteIncidenceSet attached none
  have hdegree := cone_degree_none G
  have hle := attached.degree_le_card_edgeFinset (v := none)
  change G.edgeFinset.card =
    (attached.induce ({(none : Option V)}ᶜ : Set (Option V))).edgeFinset.card at hold
  change attached.degree none = Fintype.card V at hdegree
  change attached.edgeFinset.card = G.edgeFinset.card + Fintype.card V
  omega

theorem finite_cone_edgeFinset_card {n : ℕ} (G : SimpleGraph (Fin n)) :
    (cone G).edgeFinset.card = G.edgeFinset.card + n := by
  simpa only [Fintype.card_fin] using cone_edgeFinset_card G

/-- All cycle-bound inputs concern the same cone of the whole original graph. -/
theorem finite_connected_path_free_cone {n k : ℕ} (G : SimpleGraph (Fin n))
    (hk : 5 ≤ k) (hkn : k ≤ n) (hG : G.Connected)
    (hfree : (pathGraph k).Free G) :
    (cone G).Connected ∧
    (∀ z : Option (Fin n),
      ((cone G).induce ({z}ᶜ : Set (Option (Fin n)))).Connected) ∧
    (∀ m : ℕ, k + 1 ≤ m → (cycleGraph m).Free (cone G)) ∧
    (cone G).edgeFinset.card = G.edgeFinset.card + n := by
  refine ⟨cone_connected G, cone_all_vertex_deletions_connected G hG, ?_,
    finite_cone_edgeFinset_card G⟩
  exact ErdosProblems.PathUpperReduction.UniformCone1105.finite_cone_all_long_cycle_free
    G hkn hk hfree

end ErdosProblems.PathUpperReduction.UniformConeStructure1105

