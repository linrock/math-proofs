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

Adaptation notice: Linmiao Xu adapted the Erdős 2 covering-system definitions
and statement from google-deepmind/formal-conjectures
(`FormalConjectures/ErdosProblems/2.lean` and
`FormalConjecturesForMathlib/NumberTheory/CoveringSystem.lean`, commit
`1f3951b7b0eb81f6b33ebc9bbe2b2c1feaf422d1`) and added the direct disproof
`not_arbitrarilyLarge_ideal_coverings`, the uniform numerical bound
`minimum_modulus_bound`, and the finite-set noncoverage theorem
`finite_noncoverage_bound` for this standalone Lean 4.35.0-rc2 benchmark in
2026. This file imports only Mathlib.
-/

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Span


@[expose] public section

/-!
# Independent statements for Erdős Problem 2: minimum modulus of covering systems

A finite covering system of the integers is a finite collection of congruence
classes $z \equiv r_i \pmod{m_i}$ whose union covers $\mathbb{Z}$. A covering
system is **strict** (or **distinct**) if all moduli $m_i > 1$ are pairwise
distinct. Erdős Problem 2 (Erdős, 1950) asked whether the minimum modulus
$\min_i m_i$ of a finite distinct covering system can be arbitrarily large.

Bob Hough (*Annals of Mathematics* 181 (2015), 361–382) resolved this question
in the negative, and Paul Balister, Béla Bollobás, Robert Morris, Julian
Sahasrabudhe, and Marius Tiba (arXiv:1811.03547, 2018) gave a streamlined
proof via a recursive probability sieve.

This Mathlib-only Challenge file reproduces the exact definitions
(`CoveringSystem`, `StrictCoveringSystem`) and theorem statement from
`google-deepmind/formal-conjectures` (`FormalConjectures/ErdosProblems/2.lean`,
commit `1f3951b7b0eb81f6b33ebc9bbe2b2c1feaf422d1`), together with four
theorem targets:
1. `Erdos2.Standalone.erdos_2`: the literal Formal Conjectures ideal statement
   with `answer(False)` elaborated as `False`.
2. `Erdos2.Standalone.not_arbitrarilyLarge_ideal_coverings`: the direct
   negation of the existence of strict covering systems with arbitrarily large
   minimum modulus.
3. `Erdos2.Standalone.minimum_modulus_bound`: the uniform numerical bound
   showing that one universal natural constant $B$ bounds at least one modulus
   in every finite covering of $\mathbb{Z}$ by distinct positive moduli.
4. `Erdos2.Standalone.finite_noncoverage_bound`: the finite-set noncoverage
   theorem showing that any finite set $D$ of moduli all exceeding $B$ leaves
   some integer $z \in \mathbb{Z}$ uncovered for every choice of residues.

The four intentional `sorry` placeholders below are matched by proved
declarations in `Solution.lean`; `Solution.lean` does not import this module.
-/

open Pointwise

/-- A covering system of a semiring `R` is a finite set of cosets of non-zero
proper ideals whose union covers the whole ring. When `R = ℤ`, this corresponds
to finitely many congruence classes covering every integer. -/
structure CoveringSystem (R : Type*) [CommSemiring R] where
  ι : Type
  [fintypeIndex : Fintype ι]
  residue : ι → R
  moduli : ι → Ideal R
  unionCovers : ⋃ i, ({residue i} : Set R) + (moduli i : Set R) = @Set.univ R
  ne_bot : ∀ i, moduli i ≠ ⊥
  ne_top : ∀ i, moduli i ≠ ⊤

/-- A covering system is strict if its moduli are pairwise distinct ideals. -/
structure StrictCoveringSystem (R : Type*) [CommSemiring R] extends CoveringSystem R where
  injective_moduli : moduli.Injective

namespace CoveringSystem

variable {R : Type*} [CommSemiring R]

def coset (c : CoveringSystem R) (i : c.ι) : Set R :=
  {c.residue i} + c.moduli i

@[simp]
theorem iUnion_cosets (c : CoveringSystem R) : ⋃ i, c.coset i = Set.univ :=
  c.unionCovers

end CoveringSystem

namespace Erdos2.Standalone

/-- The literal Formal Conjectures statement for Erdős Problem 2, with
`answer(False)` elaborated as `False`. -/
theorem erdos_2 :
    False ↔
      ∀ B : ℕ, ∃ c : StrictCoveringSystem ℤ, ∀ i, ∃ m : ℕ,
        c.moduli i = Ideal.span {(m : ℤ)} ∧ B < m := by
  sorry

/-- Direct disproof of arbitrarily large minimum moduli in strict ideal
covering systems of `ℤ`. -/
theorem not_arbitrarilyLarge_ideal_coverings :
    ¬ ∀ B : ℕ, ∃ c : StrictCoveringSystem ℤ, ∀ i, ∃ m : ℕ,
        c.moduli i = Ideal.span {(m : ℤ)} ∧ B < m := by
  sorry

/-- Every finite covering by distinct positive natural moduli contains a
modulus bounded by one universal constant. Residues may be signed integers. -/
theorem minimum_modulus_bound :
    ∃ B : ℕ, ∀ {ι : Type} [Fintype ι] (m : ι → ℕ) (r : ι → ℤ),
      Function.Injective m → (∀ i, 0 < m i) →
      (∀ z : ℤ, ∃ i, Int.ModEq (m i : ℤ) (r i) z) →
      ∃ i, m i ≤ B := by
  sorry

/-- Distinct sufficiently large moduli cannot cover all integers, regardless
of the chosen residues. -/
theorem finite_noncoverage_bound :
    ∃ B : ℕ, ∀ D : Finset ℕ, (∀ d ∈ D, B < d) → ∀ r : ℕ → ℤ,
      ∃ z : ℤ, ∀ d ∈ D, ¬ Int.ModEq (d : ℤ) (r d) z := by
  sorry

end Erdos2.Standalone
