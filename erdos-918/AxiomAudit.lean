module

/-
Copyright 2025-2026 The Formal Conjectures Authors.
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

public import Solution
public import Statement

@[expose] public section

universe u

open SimpleGraph
open scoped Cardinal Ordinal

namespace Erdos918

theorem statement_erdos_hajnal_fidelity :
    Erdos918.statement_erdos_hajnal.{u} :=
  Erdos918.variants.erdos_hajnal.{u}

theorem statement_eq_aleph_0_parts_i_fidelity :
    Erdos918.statement_eq_aleph_0_parts_i.{u} :=
  Erdos918.variants.eq_aleph_0.parts.i.{u}

theorem statement_eq_aleph_0_all_subgraphs_parts_i_fidelity :
    Erdos918.statement_eq_aleph_0_all_subgraphs_parts_i.{u} :=
  Erdos918.variants.eq_aleph_0_all_subgraphs.parts.i.{u}

theorem statement_eq_aleph_0_parts_ii_fidelity :
    Erdos918.statement_eq_aleph_0_parts_ii.{u} :=
  Erdos918.variants.eq_aleph_0.parts.ii.{u}

theorem statement_eq_aleph_0_all_subgraphs_parts_ii_fidelity :
    Erdos918.statement_eq_aleph_0_all_subgraphs_parts_ii.{u} :=
  Erdos918.variants.eq_aleph_0_all_subgraphs.parts.ii.{u}

theorem nonvacuity_shiftGraph_nat_countable :
    (ShiftGraph 1 ℕ).chromaticCardinal ≤ ℵ₀ := by
  rw [Erdos918.variants.chromatic_shiftGraph_le_iff_card_le_iteratedTwoPow 1 ℕ le_rfl]
  simp [iteratedTwoPow]
  exact le_of_lt (Cardinal.cantor ℵ₀)

end Erdos918

#print Erdos918.variants.erdos_hajnal
#print Erdos918.variants.eq_aleph_0.parts.i
#print Erdos918.variants.eq_aleph_0_all_subgraphs.parts.i
#print Erdos918.variants.eq_aleph_0.parts.ii
#print Erdos918.variants.eq_aleph_0_all_subgraphs.parts.ii
#print Erdos918.variants.induced_eq_aleph0_parts_ii_negation_iff_one_le
#print Erdos918.variants.chromatic_shiftGraph_le_iff_card_le_iteratedTwoPow
#print axioms Erdos918.variants.erdos_hajnal
#print axioms Erdos918.variants.eq_aleph_0.parts.i
#print axioms Erdos918.variants.eq_aleph_0_all_subgraphs.parts.i
#print axioms Erdos918.variants.eq_aleph_0.parts.ii
#print axioms Erdos918.variants.eq_aleph_0_all_subgraphs.parts.ii
#print axioms Erdos918.variants.induced_eq_aleph0_parts_ii_negation_iff_one_le
#print axioms Erdos918.variants.chromatic_shiftGraph_le_iff_card_le_iteratedTwoPow
