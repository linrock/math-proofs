module

public import PathLemmaFourScalarV3
public import PathUpperOriginalLeafDomain

@[expose] public section

/-!
Exact original FC(ii) numerical induction interface. The existing public PathLemmaFourScalar.pathFormula n k is reused verbatim;
its argument order is HOST n then PATH k. This source proves its elementary
all-natural host monotonicity and first-branch lower bound, exposes the exact
literal FC syntax by rfl, and applies an EXPLICIT full smaller-host upper IH. The IH is an input proposition, not an axiom or a completed global upper bound. Actual proper-prefix/leaf domains and original q<=antiRamseyNum restrictions
are supplied by their separate already checked original-color branch APIs.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph
open ErdosProblems.PathLemmaFourScalar

/-- The exact literal formula is nondecreasing in the complete-host order for
ALL natural parameters, including truncated subtraction below its usual regime. -/
theorem pathFormula_host_mono (k : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    pathFormula m k ≤ pathFormula n k := by
  dsimp only [pathFormula]
  let ell : ℕ := (k - 1) / 2
  let epsilon : ℕ := if Odd k then 1 else 2
  have hsub : m - ell + 1 ≤ n - ell + 1 :=
    Nat.add_le_add_right (Nat.sub_le_sub_right hmn ell) 1
  have hmul : (ell - 1) * (m - ell + 1) ≤
      (ell - 1) * (n - ell + 1) := Nat.mul_le_mul_left (ell - 1) hsub
  exact max_le_max (le_refl _)
    (Nat.add_le_add_right (Nat.add_le_add_left hmul ((ell - 1).choose 2)) epsilon)

/-- The original first term is below the exact maximum, without any graph,
positivity, parity or induction-domain assumption. -/
theorem pathFormula_first_term_le (k n : ℕ) :
    (k - 2).choose 2 + 1 ≤ pathFormula n k := by
  dsimp only [pathFormula]
  exact le_max_left _ _

/-- Exact literal FC(ii) syntax: no shifted or rational surrogate expression. -/
theorem pathFormula_eq_literal_fc (k n : ℕ) :
    pathFormula n k =
      (let ell := (k - 1) / 2
       let epsilon := if Odd k then 1 else 2
       max ((k - 2).choose 2 + 1)
         ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + epsilon)) := rfl

/-- FULL smaller COMPLETE-host upper induction hypothesis at the fixed path
order k. The entire antiRamseyNum is bounded; no favorable coloring or selected
graph variant occurs. This is an explicit conditional input, not a new axiom. -/
def OriginalFullSmallerHostIH (k n : ℕ) : Prop :=
  ∀ m : ℕ, k ≤ m → m < n →
    antiRamseyNum (pathGraph k) m ≤ pathFormula m k

/-- An actual all-original-q smaller-host restriction in its genuine induction
domain combines with the FULL IH and exact host monotonicity. -/
theorem original_color_count_le_formula_of_full_smaller_host_IH
    (k n m q : ℕ) (hIH : OriginalFullSmallerHostIH k n)
    (hkm : k ≤ m) (hmn : m < n)
    (hq : q ≤ antiRamseyNum (pathGraph k) m) :
    q ≤ pathFormula n k :=
  hq.trans ((hIH m hkm hmn).trans (pathFormula_host_mono k hmn.le))

/-- The SAME original high palette contradicts an actual smaller-host
restriction in the FULL numerical induction domain. -/
theorem original_high_color_count_false_of_full_smaller_host_IH
    (k n m q : ℕ) (hIH : OriginalFullSmallerHostIH k n)
    (hkm : k ≤ m) (hmn : m < n)
    (hq : q ≤ antiRamseyNum (pathGraph k) m)
    (hhigh : pathFormula n k < q) : False :=
  (not_lt_of_ge (original_color_count_le_formula_of_full_smaller_host_IH
    k n m q hIH hkm hmn hq)) hhigh

end ErdosProblems.PathUpperReduction
