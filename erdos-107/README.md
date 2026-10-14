# Erdős 107: Convex polygons in planar point sets

A Lean 4.35.0-rc2 formalization of the Erdős–Szekeres convex polygon problem, including the cup–cap theorem, Klein's five-point theorem, and the eight-point pentagon-free construction. Erdős and Szekeres proved the binomial upper bound in 1935 and the exponential lower bound in 1960/61; the formalization additionally certifies the exact values `f(3) = 3` and `f(4) = 5`, with the eight-point construction giving `f(5) ≥ 9` against the binomial upper bound `f(5) ≤ 21`. It proves that a suitable finite point set always exists for every `n ≥ 3` and establishes the corresponding binomial upper bound. The exact conjectured value `2^(n-2) + 1` remains open for `n ≥ 6`.

## Exported Theorems

- `Erdos107.Palomar.nonempty_cardSet`: `∀ n ≥ 3, (cardSet n).Nonempty`.
- `Erdos107.Palomar.f_le_erdosSzekeresUpper`: `∀ n ≥ 3, f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1`.
- `Erdos107.Palomar.f_eq_conjectured_of_le_four`: `∀ n, 3 ≤ n → n ≤ 4 → f n = 2 ^ (n - 2) + 1`.
- `Erdos107.Palomar.ersz_bounds_of_le_five`: `∀ n, 3 ≤ n → n ≤ 5 → 2 ^ (n - 2) + 1 ≤ f n ∧ f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1`.
