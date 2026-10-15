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

open Filter
open scoped Topology BigOperators

namespace Erdos36.Challenge

def Overlap (A B : Finset ℤ) (k : ℤ) : ℕ :=
  ((A.product B).filter <| fun (a, b) => a - b = k).card

noncomputable def MaxOverlap (A B : Finset ℤ) : ℕ :=
  iSup <| Overlap A B

noncomputable def M (n : ℕ) : ℕ :=
  sInf {MaxOverlap A B | (A : Finset ℤ) (B : Finset ℤ)
    (_disjoint : Disjoint A B)
    (_union : A ∪ B = Finset.Icc (1 : ℤ) (2 * n))
    (_same_card : A.card = B.card)}

noncomputable def MinOverlapQuotient (N : ℕ) : ℝ :=
  (M N : ℝ) / N

def statement_scherk_1955 : Prop :=
  1 - (Real.sqrt 2)⁻¹ < atTop.liminf MinOverlapQuotient

def statement_swierczkowski_1958 : Prop :=
  (4 - 6 ^ ((1 : ℝ) / 2)) / 5 < atTop.liminf MinOverlapQuotient

def statement_exists_limit : Prop :=
  ∃ c : ℝ, atTop.Tendsto MinOverlapQuotient (𝓝 c)

end Erdos36.Challenge
