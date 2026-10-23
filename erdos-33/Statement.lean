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

public import Mathlib

@[expose] public section

open Filter

namespace Erdos33.Challenge

def AdditiveBasisCondition (A : Set ℕ) : Prop :=
  ∀ (k : ℕ), ∃ (n : ℕ) (a : ℕ), a ∈ A ∧ k = a + n ^ 2

def statement_one_mem_lowerBounds : Prop :=
  1 < ⨅ A : {A : Set ℕ | AdditiveBasisCondition A}, Filter.atTop.limsup (fun N : ℕ =>
    ((A.1 ∩ Set.Icc 1 N).ncard : EReal) / (Real.sqrt (N : ℝ) : EReal))

def statement_vanDoorn : Prop :=
  (⨅ A : {A : Set ℕ | AdditiveBasisCondition A}, Filter.atTop.limsup (fun N : ℕ =>
    ((A.1 ∩ Set.Icc 1 N).ncard : EReal) / (Real.sqrt (N : ℝ) : EReal))) ≤
      ((2 * Real.goldenRatio ^ ((5 : ℝ) / 2) : ℝ) : EReal)

end Erdos33.Challenge
