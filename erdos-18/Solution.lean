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

public import FactorialPracticalUpperBound18

@[expose] public section

namespace Erdos18.Palomar

open Filter

theorem factorial_isPractical (n : ℕ) : Nat.IsPractical n.factorial :=
  Erdos18.factorial_isPractical n

theorem erdos_18_upper_bound :
    ∀ᶠ n : ℕ in atTop, Erdos18.practicalH (Nat.factorial n) < n :=
  Erdos18.erdos_18_upper_bound

end Erdos18.Palomar
