module

/-
Copyright 2025 The Formal Conjectures Authors.
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

public import CoveringSystem2
public import Mathlib.RingTheory.Ideal.Span


@[expose] public section

/-!
The exact Erdős #2 statement, using the Apache-2.0 Formal Conjectures covering
structures in `CoveringSystem2`. This is a proposition definition, with no
admitted theorem. The elaborated `answer(False)` is written as `False`.
-/

namespace Erdos2.Challenge

def statement : Prop :=
  False ↔
    ∀ B : ℕ, ∃ c : StrictCoveringSystem ℤ, ∀ i, ∃ m : ℕ,
      c.moduli i = Ideal.span {(m : ℤ)} ∧ B < m

end Erdos2.Challenge
