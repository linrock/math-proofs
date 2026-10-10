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

public import Definitions261
public import TwoRepresentations261
public import CertificateEngine261

@[expose] public section

/-!
# Erdős Problem 261: Solution Entrypoint

This module exports the proved theorems matching `Challenge.lean` in the
`Erdos261.Palomar` namespace as well as the literal `FormalConjectures/ErdosProblems/261.lean`
declarations in the `Erdos261` namespace.
-/

open scoped BigOperators Cardinal

namespace Erdos261

theorem erdos_261.variants.borwein_loring (m : ℕ) (hm : 0 < m) :
    let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ) :=
  Erdos261.borwein_loring m hm

theorem erdos_261.variants.borwein_loring_property (m : ℕ) (hm : 2 ≤ m) :
    Erdos261Prop (2 ^ (m + 1) - m - 2) :=
  Erdos261.borwein_loring_property m hm

theorem erdos_261.parts.i : True ↔ {n : ℕ | 0 < n ∧ Erdos261Prop n}.Infinite :=
  Erdos261.erdos_261_parts_i

theorem erdos_261.variants.le_10000 {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000) :
    Erdos261Prop n :=
  Erdos261.le_10000 hn_pos hn

theorem erdos_261.variants.two_representations : True ↔ ∃ x : ℚ,
    2 ≤ #{a : ℕ → ℕ | Erdos261InfiniteRepresentation x a} :=
  Erdos261.two_representations

namespace Palomar

/-- A natural number $n$ is said to have property `Erdos261Prop` if there exist $t \ge 2$
pairwise distinct positive integers $a_1, \ldots, a_t$ such that
$n / 2^n = \sum_{1 \le k \le t} a_k / 2^{a_k}$. -/
def Erdos261Prop (n : ℕ) : Prop := ∃ᵉ (t ≥ 2) (a : Fin t → ℕ), a.Injective ∧
  (1 ≤ a) ∧ n / (2 ^ n : ℚ) = ∑ k, (a k) / (2 ^ (a k) : ℚ)

/-- A canonical infinite representation of a rational number $x$ by positive integers. The
denominators are strictly increasing so that reorderings are not counted as different
representations. -/
def Erdos261InfiniteRepresentation (x : ℚ) (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧ (1 ≤ a) ∧ Summable (fun k => (a k) / (2 ^ (a k) : ℚ)) ∧
    x = ∑' k, (a k) / (2 ^ (a k) : ℚ)

theorem borwein_loring (m : ℕ) (hm : 0 < m) :
    let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ) :=
  Erdos261.borwein_loring m hm

theorem borwein_loring_property (m : ℕ) (hm : 2 ≤ m) :
    Erdos261Prop (2 ^ (m + 1) - m - 2) :=
  Erdos261.borwein_loring_property m hm

theorem erdos_261_parts_i : True ↔ {n : ℕ | 0 < n ∧ Erdos261Prop n}.Infinite :=
  Erdos261.erdos_261_parts_i

theorem le_10000 {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000) :
    Erdos261Prop n :=
  Erdos261.le_10000 hn_pos hn

theorem two_representations : True ↔ ∃ x : ℚ,
    2 ≤ #{a : ℕ → ℕ | Erdos261InfiniteRepresentation x a} :=
  Erdos261.two_representations

theorem infinite_rationals_two_pow_reps (m : ℕ) :
    {x : ℚ | (2 ^ m : Cardinal) ≤ #{a : ℕ → ℕ | Erdos261InfiniteRepresentation x a}}.Infinite :=
  Erdos261.infinite_rationals_two_pow_reps m

theorem max_n_bound {n t : ℕ} (ht : 2 ≤ t) (a : Fin t → ℕ)
    (hinj : Function.Injective a) (ha_pos : 1 ≤ a)
    (hsum : n / (2 ^ n : ℚ) = ∑ k, (a k) / (2 ^ (a k) : ℚ)) :
    n ≤ 2 ^ (t + 1) - t - 2 :=
  Erdos261.max_n_bound ht a hinj ha_pos hsum

theorem exists_term_le_add_three {n t : ℕ} (hn : 1 ≤ n) (ht : 2 ≤ t) (a : Fin t → ℕ)
    (hinj : Function.Injective a) (ha_pos : 1 ≤ a)
    (hsum : n / (2 ^ n : ℚ) = ∑ k, (a k) / (2 ^ (a k) : ℚ)) :
    ∃ k : Fin t, n + 1 ≤ a k ∧ a k ≤ n + 3 :=
  Erdos261.exists_term_le_add_three hn ht a hinj ha_pos hsum

theorem last_term_gap_dvd {n t : ℕ} (a : Fin (t + 2) → ℕ)
    (hmono : StrictMono a) (ha_pos : 1 ≤ a)
    (hsum : n / (2 ^ n : ℚ) = ∑ k, (a k) / (2 ^ (a k) : ℚ)) :
    2 ^ (a (Fin.last (t + 1)) - a (Fin.castSucc (Fin.last t))) ∣ a (Fin.last (t + 1)) :=
  Erdos261.last_term_gap_dvd a hmono ha_pos hsum

theorem borwein_loring_unique {t : ℕ} (ht : 2 ≤ t) (a : Fin t → ℕ)
    (hmono : StrictMono a) (ha_pos : 1 ≤ a)
    (hsum : (2 ^ (t + 1) - t - 2 : ℕ) / (2 ^ (2 ^ (t + 1) - t - 2) : ℚ) =
      ∑ k, (a k) / (2 ^ (a k) : ℚ)) :
    ∀ k : Fin t, a k = (2 ^ (t + 1) - t - 2) + 1 + k.val :=
  Erdos261.borwein_loring_unique ht a hmono ha_pos hsum

theorem punctured_family_erdos261Prop (k : ℕ) (hk : 1 ≤ k) :
    Erdos261Prop ((2 ^ (4 * k + 2) + 1) / 5 - 4 * k) :=
  Erdos261.punctured_family_erdos261Prop k hk

theorem arbitrary_length_rep_of_all_erdos261Prop
    (hall : ∀ m : ℕ, 0 < m → Erdos261Prop m) {n : ℕ} (hn : 0 < n) (L : ℕ) :
    ∃ᵉ (t ≥ max 2 L) (a : Fin t → ℕ), a.Injective ∧
      (1 ≤ a) ∧ n / (2 ^ n : ℚ) = ∑ k, (a k) / (2 ^ (a k) : ℚ) :=
  Erdos261.arbitrary_length_rep_of_all_erdos261Prop hall hn L

end Palomar
end Erdos261
