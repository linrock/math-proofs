module

/-
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

public import ScaleAdaptiveConstruction1139

@[expose] public section


/-!
# Target-supported weighted pattern options and hit loads for Erdős #1139

This module defines the target-support condition
`WeightedActualPatternOptionsSupported` and the color-aware target hit load
`weightedActualPatternHitLoad` used by the scale-adaptive prime-pattern moment
and budget transfer modules.
-/

open Finset
open scoped BigOperators

namespace Erdos1139

/-- A genuinely target-supported weighted pattern option for its selected
color. A target-hitting option is represented by an actual target; an edge
with no retained target is retained as a dummy option so its probability mass
and exact label normalization are preserved. -/
def WeightedActualPatternOptionsSupported
    {k : ℕ} (R lowTargets highTargets : Finset ℕ)
    (color : ↥R → Fin k → Bool)
    (residue : ↥R → Fin k → ℕ) : Prop :=
  ∀ (p : ↥R) (option : Fin k),
    (color p option = false →
      residue p option ∈ lowTargets ∨
        ∀ h ∈ lowTargets, ¬ residue p option ≡ h [MOD (p : ℕ)]) ∧
    (color p option = true →
      residue p option ∈ highTargets ∨
        ∀ h ∈ highTargets, ¬ residue p option ≡ h [MOD (p : ℕ)])

/-- The color-aware target hit load of a rationally weighted pattern-edge
distribution. -/
noncomputable def weightedActualPatternHitLoad
    {k : ℕ} (R : Finset ℕ)
    (color : ↥R → Fin k → Bool)
    (residue : ↥R → Fin k → ℕ)
    (wanted : Bool) (h : ℕ) : ℝ :=
  ∑ p : ↥R, scaleAdaptiveColorHitFraction R color residue wanted h p

/-- Every weighted pattern hit load is nonnegative. -/
theorem weightedActualPatternHitLoad_nonnegative
    {k : ℕ} (positive : 0 < k) (R : Finset ℕ)
    (color : ↥R → Fin k → Bool)
    (residue : ↥R → Fin k → ℕ)
    (wanted : Bool) (h : ℕ) :
    0 ≤ weightedActualPatternHitLoad R color residue wanted h := by
  unfold weightedActualPatternHitLoad
  apply Finset.sum_nonneg
  intro p _
  exact (scaleAdaptiveColorHitFraction_mem_unitInterval
    positive R color residue wanted h p).1

end Erdos1139
