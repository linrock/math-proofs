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

noncomputable section
open scoped BigOperators Topology Asymptotics
open Nat Filter Finset

namespace Erdos726

open Erdos726

/-- Primes `p ≤ n` whose least residue `n % p` lies in the upper half `(p / 2, p)`. -/
def upperHalfPrimes (n : ℕ) : Finset ℕ :=
  (range (n + 1)).filter (fun p : ℕ ↦ p.Prime ∧ (p : ℝ) / 2 < ((n % p : ℕ) : ℝ))

/-- Upper-half prime reciprocal sum `∑_{p ≤ n, p/2 < n % p} 1 / p`. -/
def upperHalfPrimeSum (n : ℕ) : ℝ :=
  ∑ p ∈ upperHalfPrimes n, (1 : ℝ) / (p : ℝ)

/-- Primes `p ≤ n`. -/
def primeRange (n : ℕ) : Finset ℕ :=
  (range (n + 1)).filter (fun p : ℕ ↦ p.Prime)

/-- The prime-counting function `π(m) = (primeRange m).card`. -/
def primeCount (m : ℕ) : ℕ :=
  (primeRange m).card

/-- Primes `p ≤ n` whose least residue `n % p` does not lie in that upper half. -/
def lowerComplementPrimes (n : ℕ) : Finset ℕ :=
  (range (n + 1)).filter
    (fun p : ℕ ↦ p.Prime ∧ ¬((p : ℝ) / 2 < ((n % p : ℕ) : ℝ)))

/-- Lower-complement prime reciprocal sum. -/
def lowerComplementPrimeSum (n : ℕ) : ℝ :=
  ∑ p ∈ lowerComplementPrimes n, (1 : ℝ) / (p : ℝ)

/-- A normalized arithmetical-function remainder relative to the PNT approximation. -/
def pntRemainder (M : ℕ → ℝ) (m : ℕ) : ℝ :=
  (primeCount m : ℝ) - M m

/-- The sharp large-prime majorant used in the cutoff proof. -/
def largePrimeWindowMajorant (n K : ℕ) (δ : ℝ) : ℝ :=
  ((K : ℝ) * ((K : ℝ) + 2) / (n : ℝ)) * (1 / Real.log ((n / (K + 1) : ℕ) : ℝ)) +
    Real.log ((K : ℝ) + 2) / (Real.log ((n / (K + 1) : ℕ) : ℝ) * Real.log (n : ℝ)) +
    4 * (K : ℝ) * δ +
    ((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) / (n : ℝ)

/-- Primes in the upper cutoff tail. -/
def upperSmallPrimeTail (n K : ℕ) : Finset ℕ :=
  (upperHalfPrimes n).filter (fun p : ℕ ↦ K + 1 ≤ n / p)

/-- Upper cutoff-tail reciprocal sum. -/
def upperSmallPrimeTailSum (n K : ℕ) : ℝ :=
  ∑ p ∈ upperSmallPrimeTail n K, (1 : ℝ) / (p : ℝ)

/-- Primes in the lower cutoff tail. -/
def lowerSmallPrimeTail (n K : ℕ) : Finset ℕ :=
  (lowerComplementPrimes n).filter (fun p : ℕ ↦ K + 1 ≤ n / p)

/-- Lower cutoff-tail reciprocal sum. -/
def lowerSmallPrimeTailSum (n K : ℕ) : ℝ :=
  ∑ p ∈ lowerSmallPrimeTail n K, (1 : ℝ) / (p : ℝ)

/-- Odd primes in a bounded window. -/
def oddPrimeRange (n : ℕ) : Finset ℕ :=
  (range (n + 1)).filter (fun p : ℕ ↦ Nat.Prime p ∧ p % 2 = 1)

/-- Primes `p ≤ B` whose remainder `n % p` lies in the upper half `(p / 2, p)`. -/
def upperBoundedPrimes (B n : ℕ) : Finset ℕ :=
  (primeRange B).filter (fun p : ℕ ↦ (p : ℝ) / 2 < ((n % p : ℕ) : ℝ))

/-- Bounded-window upper prime reciprocal sum. -/
def upperBoundedPrimeSum (B n : ℕ) : ℝ :=
  ∑ p ∈ upperBoundedPrimes B n,
    (1 : ℝ) / (p : ℝ)

/-- Odd primes `p ≤ B` dividing `n`. -/
def dividingOddBoundedPrimes (B n : ℕ) : Finset ℕ :=
  (oddPrimeRange B).filter (fun p : ℕ ↦ p ∣ n)

/-- Sum over bounded-window odd primes divisible by `n / B`. -/
def dividingOddBoundedSum (B n : ℕ) : ℝ :=
  ∑ p ∈ dividingOddBoundedPrimes B n,
    (1 : ℝ) / (p : ℝ)

theorem variants.mertens_estimate :
    (fun n : ℕ ↦ ∑ p ∈ (range (n + 1)).filter (fun p ↦ p.Prime), (1 : ℝ) / ((p : ℕ) : ℝ))
    ~[atTop] (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) := by sorry

theorem asymptotic_iff_discrepancy_isLittleO :
    ((fun n : ℕ ↦ ∑ p ∈ (range (n + 1)).filter
        (fun p : ℕ ↦ p.Prime ∧ (p : ℝ) / 2 < ((n % p : ℕ) : ℝ)),
      (1 : ℝ) / (p : ℝ))
    ~[atTop] (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / 2)) ↔
    (fun n : ℕ ↦ upperHalfPrimeSum n - lowerComplementPrimeSum n)
      =o[atTop] (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) := by sorry

theorem iff_smallPrimeTail_of_log_add_two_bounds (K : ℕ → ℕ) (δ : ℕ → ℝ) (N₀ : ℕ)
    (hδ : ∀ n ≥ N₀, 0 ≤ δ n)
    (h2 : ∀ n ≥ N₀, 2 ≤ n / (K n + 1))
    (hK : ∀ n ≥ N₀, K n + 1 ≤ n / (K n + 1))
    (hR : ∀ n ≥ N₀, ∀ m ≤ n,
      |pntRemainder (fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ)) m| ≤ δ n * (m : ℝ))
    (hmaj : Filter.Tendsto
      (fun n : ℕ ↦ largePrimeWindowMajorant n (K n) (δ n) / Real.log (Real.log (n : ℝ)))
      atTop (nhds 0)) :
    ((fun n : ℕ ↦ ∑ p ∈ (range (n + 1)).filter
        (fun p : ℕ ↦ p.Prime ∧ (p : ℝ) / 2 < ((n % p : ℕ) : ℝ)),
      (1 : ℝ) / (p : ℝ))
    ~[atTop] (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / 2)) ↔
    Filter.Tendsto
      (fun n : ℕ ↦ (upperSmallPrimeTailSum n (K n) - lowerSmallPrimeTailSum n (K n)) /
        Real.log (Real.log (n : ℝ))) atTop (nhds 0) := by sorry

theorem of_smallPrimeTail_and_log_add_two_bounds (K : ℕ → ℕ) (δ : ℕ → ℝ) (N₀ : ℕ)
    (hδ : ∀ n ≥ N₀, 0 ≤ δ n)
    (h2 : ∀ n ≥ N₀, 2 ≤ n / (K n + 1))
    (hK : ∀ n ≥ N₀, K n + 1 ≤ n / (K n + 1))
    (hR : ∀ n ≥ N₀, ∀ m ≤ n,
      |pntRemainder (fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ)) m| ≤ δ n * (m : ℝ))
    (hmaj : Filter.Tendsto
      (fun n : ℕ ↦ largePrimeWindowMajorant n (K n) (δ n) / Real.log (Real.log (n : ℝ)))
      atTop (nhds 0))
    (htail : Filter.Tendsto
      (fun n : ℕ ↦ (upperSmallPrimeTailSum n (K n) - lowerSmallPrimeTailSum n (K n)) /
        Real.log (Real.log (n : ℝ))) atTop (nhds 0)) :
    (fun n : ℕ ↦ ∑ p ∈ (range (n + 1)).filter
        (fun p : ℕ ↦ p.Prime ∧ (p : ℝ) / 2 < ((n % p : ℕ) : ℝ)),
      (1 : ℝ) / (p : ℝ))
    ~[atTop] (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / 2) := by sorry

theorem of_modular_reflection_and_log_add_two_bounds (K M : ℕ → ℕ) (δ : ℕ → ℝ) (N₀ : ℕ)
    (hδ : ∀ n ≥ N₀, 0 ≤ δ n)
    (h2 : ∀ n ≥ N₀, 2 ≤ n / (K n + 1))
    (hK : ∀ n ≥ N₀, K n + 1 ≤ n / (K n + 1))
    (hle : ∀ n ≥ N₀, n ≤ M n)
    (hM : ∀ n ≥ N₀, ∀ p ∈ oddPrimeRange (n / (K n + 1)), p ∣ M n)
    (hR : ∀ n ≥ N₀, ∀ m ≤ n,
      |pntRemainder (fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ)) m| ≤ δ n * (m : ℝ))
    (hmaj : Filter.Tendsto
      (fun n : ℕ ↦ largePrimeWindowMajorant n (K n) (δ n) / Real.log (Real.log (n : ℝ)))
      atTop (nhds 0))
    (hrefl : Filter.Tendsto
      (fun n : ℕ ↦
        (|upperBoundedPrimeSum (n / (K n + 1)) n -
            upperBoundedPrimeSum (n / (K n + 1)) (M n - n)| +
          dividingOddBoundedSum (n / (K n + 1)) n + 1 / 2) /
          Real.log (Real.log (n : ℝ)))
      atTop (nhds 0)) :
    (fun n : ℕ ↦ ∑ p ∈ (range (n + 1)).filter
        (fun p : ℕ ↦ p.Prime ∧ (p : ℝ) / 2 < ((n % p : ℕ) : ℝ)),
      (1 : ℝ) / (p : ℝ))
    ~[atTop] (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / 2) := by sorry

end Erdos726

end
