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

public import Erdos726Unified435
public import SmallPrimeTailReflectionDiscrepancy726
public import AbelSummationPrimeCountVariation726
public import LogDensityTrapezoidalDefectDecomposition726
public import Blueprint726

@[expose] public section

noncomputable section
open scoped BigOperators Topology Asymptotics
open Nat Filter Finset

namespace Erdos726.Challenge

open Erdos726

/-- Canonical `FormalConjectures.ErdosProblems.«726»` open statement (`erdos_726` with `answer(True)` elaborated as `True`). -/
abbrev statement_erdos_726 : Prop :=
  True ↔
    (fun n : ℕ ↦ ∑ p ∈ (range (n + 1)).filter
        (fun p : ℕ ↦ p.Prime ∧ (p : ℝ) / 2 < ((n % p : ℕ) : ℝ)),
      (1 : ℝ) / (p : ℝ))
    ~[atTop] (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / 2)

theorem statement_variants_mertens_estimate :
    (fun n : ℕ ↦ ∑ p ∈ (range (n + 1)).filter (fun p ↦ p.Prime), (1 : ℝ) / ((p : ℕ) : ℝ))
    ~[atTop] (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) :=
  erdos_726_variants_mertens_estimate

end Erdos726.Challenge

end
