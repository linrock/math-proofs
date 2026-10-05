module

public import GoldbachChainMaster
public import OriginalNth1054

@[expose] public section


/-!
# Unconditional resolution of all three parts of Erdős #1054

Composes the unconditional almost-all binary Goldbach theorem
(`GoldbachChain.GoldbachReduction.almost_all_binary_goldbach_proven`) with the
`Nat.nth`/`Nat.find` equivalence from `OriginalNth1054.lean` to resolve all
three parts of Erdős Problem 1054 without external hypotheses.
-/

open Filter Asymptotics
open scoped Topology

namespace Erdos1054.Unconditional

/-- The full, independently checked Goldbach theorem is definitionally the
exact almost-all hypothesis used by the supported divisor-prefix reduction. -/
theorem almost_all_binary_goldbach :
    _root_.Erdos1054.DensityZero _root_.Erdos1054.notSumOfTwoPrimes := by
  exact GoldbachChain.GoldbachReduction.almost_all_binary_goldbach_proven

/-- At every fixed threshold, a positive lower density of represented integers
has an official minimal modulus larger than that threshold times the integer. -/
theorem positive_lower_density (A : ℕ) (hA : 1 ≤ A) :
    _root_.Erdos1054.PositiveLowerDensity
      (fun n => n ∈ _root_.Represented.R ∧
        A * n < _root_.Erdos1054.OriginalNth.f n) :=
  _root_.Erdos1054.OriginalNth.official_main_of_goldbach
    almost_all_binary_goldbach A hA

/-- The positive-density conclusion also holds for every real threshold,
matching the asymptotic regime of the informal quantitative strengthening. -/
theorem positive_lower_density_real (A : ℝ) (hA : 1 ≤ A) :
    _root_.Erdos1054.PositiveLowerDensity
      (fun n => _root_.Erdos1054.Represented n ∧
        A * (n : ℝ) < (_root_.Erdos1054.OriginalNth.f n : ℝ)) := by
  simpa only [_root_.Erdos1054.OriginalNth.f_eq_comparator] using
    _root_.Erdos1054.erdos1054_main_real_of_goldbach
      almost_all_binary_goldbach A hA

/-- The answer to the first official question is NO. -/
theorem answer_i :
    ¬ (fun n : ℕ => (_root_.Erdos1054.OriginalNth.f n : ℝ))
      =o[atTop] (fun n : ℕ => (n : ℝ)) :=
  _root_.Erdos1054.OriginalNth.official_not_littleO_of_goldbach
    almost_all_binary_goldbach

/-- The answer to the second official question is NO, with the exact
density-one quantifier and the little-o order filter on its subtype. -/
theorem answer_ii :
    ¬ ∃ S : Set ℕ, _root_.Erdos1054.HasDensityOne S ∧
      (fun n : S => (_root_.Erdos1054.OriginalNth.f (n : ℕ) : ℝ))
        =o[atTop] (fun n : S => ((n : ℕ) : ℝ)) :=
  _root_.Erdos1054.OriginalNth.official_not_almost_everywhere_littleO_of_goldbach
    almost_all_binary_goldbach

/-- The same negative answer with the official partial-density expression
expanded literally, including both intersections with `Set.univ`. -/
theorem answer_ii_official_density :
    ¬ ∃ S : Set ℕ,
      Tendsto
          (fun b : ℕ =>
            ((((S ∩ Set.univ) ∩ Set.Iio b).ncard : ℝ) /
              ((Set.univ ∩ Set.Iio b).ncard : ℝ)))
          atTop (𝓝 1) ∧
        (fun n : S => (_root_.Erdos1054.OriginalNth.f (n : ℕ) : ℝ))
          =o[atTop] (fun n : S => ((n : ℕ) : ℝ)) := by
  rintro ⟨S, hS, hsmall⟩
  exact answer_ii ⟨S,
    (_root_.Erdos1054.hasDensityOne_iff_official_formula S).mpr hS,
    hsmall⟩

/-- The answer to the third official question is YES: its actual
extended-real limsup is infinite. -/
theorem answer_iii_limsup :
    atTop.limsup
      (fun n : ℕ => (_root_.Erdos1054.OriginalNth.f n : EReal) / n) = ⊤ :=
  _root_.Erdos1054.OriginalNth.official_limsup_top_of_goldbach
    almost_all_binary_goldbach

/-- The literal official third question additionally, and redundantly,
quantifies over a density-one set; the entire natural numbers provide it. -/
theorem answer_iii :
    ∃ S : Set ℕ, _root_.Erdos1054.HasDensityOne S ∧
      atTop.limsup
        (fun n : ℕ => (_root_.Erdos1054.OriginalNth.f n : EReal) / n) = ⊤ :=
  ⟨Set.univ, _root_.Erdos1054.hasDensityOne_univ, answer_iii_limsup⟩

/-- The exact official expanded partial-density expression also holds for
the redundant density-one witness in the third question. -/
theorem answer_iii_official_density :
    ∃ S : Set ℕ,
      Tendsto
          (fun b : ℕ =>
            ((((S ∩ Set.univ) ∩ Set.Iio b).ncard : ℝ) /
              ((Set.univ ∩ Set.Iio b).ncard : ℝ)))
          atTop (𝓝 1) ∧
        atTop.limsup
          (fun n : ℕ => (_root_.Erdos1054.OriginalNth.f n : EReal) / n) = ⊤ :=
  ⟨Set.univ,
    (_root_.Erdos1054.hasDensityOne_iff_official_formula Set.univ).mp
      _root_.Erdos1054.hasDensityOne_univ,
    answer_iii_limsup⟩

end Erdos1054.Unconditional
