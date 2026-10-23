module

public import Layer1058

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

public section

/-! ## Finite Gyárfás configurations

The finite Gyárfás structural theorem, assembled from actual graph lemmas.
No structural or saturation premise remains in the theorem statement.
-/

universe u

namespace Erdos58

open SimpleGraph

theorem finite_gyarfas : FiniteGyarfas.{u} := by
  intro V _ G k hk hG hdel hmin hfin hcount
  have hne : G.oddCycleLengths.Nonempty := (Set.ncard_pos hfin).mp (by omega)
  have hsaturated : SaturatedExteriorImpossible G := by
    intro x a b c hc hodd hmax S hS hs havoid hcoverA hcoverB
      m hm hfin' hcard heq hcontacts hdiagA hdiagB
    exact saturated_exterior_path_impossible c hc hodd hmax S hS hs havoid
      hcoverA hcoverB m hm hfin' hcard heq hcontacts hdiagA hdiagB
  exact finite_structural_clique_of_saturated_impossible hsaturated k
    (Nat.succ_le_iff.mpr hk) hG hdel hmin hfin hcount.le hne

end Erdos58
