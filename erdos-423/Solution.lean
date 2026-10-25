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

public import Erdos423Unified435
public import EventualStabilizationObstructionAndUnbounded423
public import CompletedSquareDiscriminantAndSmallThresholdObstruction423
public import Blueprint423

/-!
The exported theorems are proved in the imported proof modules under the namespace `Erdos423`
and are re-exported here unchanged. The three Formal Conjectures variants
`Erdos423.erdos_423.variants.nondecreasing`, `Erdos423.erdos_423.variants.unbounded`, and
`Erdos423.erdos_423.variants.infinite_complement` carry canonical upstream names (with
`nondecreasing` documented as a re-proof of Anatolii Ohorodnyk's independent formalization in
`lean-fc-proofs`, and `unbounded` and `infinite_complement` as new formalizations); the remaining
public results use `Erdos423.<name>`, including three conditional tower-reduction theorems.
-/
