module

/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

public import Mathlib

@[expose] public section

noncomputable section
open scoped BigOperators Topology Classical
open Finset SimpleGraph Asymptotics Filter

namespace Erdos600.Challenge

/-- The triangles of `G` containing the edge `uv`, that is, the `3`-cliques of `G` whose vertex
set contains both endpoints of `uv`. -/
noncomputable def trianglesContaining {α : Type*} [Fintype α] (G : SimpleGraph α)
    (uv : Sym2 α) : Finset (Finset α) :=
  (G.cliqueFinset 3).filter (fun t ↦ uv.toFinset ⊆ t)

/-- Let $e(n,r)$ be minimal such that every graph on $n$ vertices with at least $e(n,r)$ edges,
each edge contained in at least one triangle, must have an edge contained in at least
$r$ triangles. -/
def Erdos600Prop (n : ℕ) (e : ℕ) (r : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), G.edgeFinset.card ≥ e →
  (∀ uv ∈ G.edgeFinset, (trianglesContaining G uv).Nonempty) →
  ∃ uv ∈ G.edgeFinset, r ≤ (trianglesContaining G uv).card

noncomputable def eFunction (n : ℕ) (r : ℕ) : ℕ := sInf {e : ℕ | Erdos600Prop n e r}

noncomputable def maxAdmissibleEdges (n r : ℕ) : ℕ := eFunction n r - 1

def statement_erdos_600_parts_i : Prop :=
  ∀ r : ℕ, 2 ≤ r →
    Tendsto (fun (n : ℕ) ↦ (eFunction n (r + 1) : ℝ) - (eFunction n r : ℝ)) atTop atTop

def statement_erdos_600_parts_ii : Prop :=
  ∀ r : ℕ, 2 ≤ r →
    Tendsto (fun (n : ℕ) ↦ (eFunction n (r + 1) : ℝ) / (eFunction n r : ℝ)) atTop (𝓝 1)

def statement_erdos_600_variants_ruzsa_szemeredi_upper_bound : Prop :=
  ∀ r : ℕ, (fun (n : ℕ) ↦ (eFunction n r : ℝ)) =o[atTop] (fun (n : ℕ) ↦ (n : ℝ)^2)

def statement_eFunction_two_eq : Prop :=
  ∀ n : ℕ, eFunction n 2 = 3 * ruzsaSzemerediNumberNat n + 1

def statement_maxAdmissibleEdges_le_mul_add_sub_one_div_four : Prop :=
  ∀ (n : ℕ) {r : ℕ}, 1 ≤ r → maxAdmissibleEdges n r ≤ (n * (n + r - 1)) / 4

def statement_sq_mul_maxAdmissibleEdges_le_maxAdmissibleEdges_mul : Prop :=
  ∀ (m : ℕ) {r c : ℕ}, 1 ≤ c → 1 ≤ r →
    c ^ 2 * maxAdmissibleEdges m r ≤ maxAdmissibleEdges (c * m) (c * (r - 1) + 1)

end Erdos600.Challenge
end
