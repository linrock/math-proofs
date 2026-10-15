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

namespace Erdos726

open Erdos726

theorem variants.mertens_estimate :
    (fun n : ℕ ↦ ∑ p ∈ (range (n + 1)).filter (fun p ↦ p.Prime), (1 : ℝ) / ((p : ℕ) : ℝ))
    ~[atTop] (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) :=
  Erdos726.erdos_726_variants_mertens_estimate

theorem asymptotic_iff_discrepancy_isLittleO :
    ((fun n : ℕ ↦ ∑ p ∈ (range (n + 1)).filter
        (fun p : ℕ ↦ p.Prime ∧ (p : ℝ) / 2 < ((n % p : ℕ) : ℝ)),
      (1 : ℝ) / (p : ℝ))
    ~[atTop] (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / 2)) ↔
    (fun n : ℕ ↦ upperHalfPrimeSum n - lowerComplementPrimeSum n)
      =o[atTop] (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) :=
  Erdos726.erdos_726_asymptotic_iff_discrepancy_isLittleO

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
        Real.log (Real.log (n : ℝ))) atTop (nhds 0) :=
  Erdos726.erdos_726_iff_smallPrimeTail_of_log_add_two_bounds K δ N₀ hδ h2 hK hR hmaj

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
    ~[atTop] (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / 2) :=
  Erdos726.erdos_726_of_smallPrimeTail_and_log_add_two_bounds K δ N₀ hδ h2 hK hR hmaj htail

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
    ~[atTop] (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / 2) :=
  Erdos726.erdos_726_of_modular_reflection_and_log_add_two_bounds K M δ N₀ hδ h2 hK hle hM hR hmaj hrefl

end Erdos726

end
