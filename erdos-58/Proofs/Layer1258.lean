module

public import Layer1158

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

/-! ## The full graph case -/

/-! The original Erdős #58 statement, including its equality characterization,
for arbitrary vertex types. The finite structural theorem is proved in the
imported development, and finite-target coloring compactness removes the
finite-vertex restriction. -/

universe u_1

namespace Erdos58

open SimpleGraph

/-- Both clauses of the original theorem, with no finite structural premise. -/
theorem full_statement : Statement.{u_1} :=
  statement_of_finite_gyarfas finite_gyarfas

end Erdos58
