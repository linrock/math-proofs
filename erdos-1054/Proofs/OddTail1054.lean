module

public import Unconditional1054

@[expose] public section


/-!
# Odd large-ratio witnesses and relative odd-density transfer for Erdős #1054

Because the sieve modulus $Q_E$ is always even, every sifted integer coprime to
$Q_E$ is odd. Retaining this parity invariant yields a positive lower density of
odd integers $n$ satisfying $f(n) > A n$ for every $A \ge 1$. Moreover,
deleting any set of odd integers of natural density zero (`HasOddDensityOne S`)
preserves both the lower and upper asymptotic densities of every odd-supported
predicate.
-/

open Finset Filter Asymptotics
open scoped Topology

namespace Represented

/-- The sifted proof of the original main theorem actually produces a
positive-lower-density set consisting entirely of odd represented integers.

The threshold-selection and density-removal arguments are adapted from the
pinned Apache-2.0 `Erdos1054Conditional.lean`; unlike its `main` theorem, the
final inclusion retains the already-proved parity of every survivor. -/
theorem main_odd (hDeep : DeepInputs) (A : ℝ) (hA : 1 ≤ A) :
    ∃ c : ℝ, 0 < c ∧
      c ≤ lowerDensity
        (fun N => Odd N ∧ N ∈ R ∧ (A * N : ℝ) < (f N : ℝ)) := by
  obtain ⟨c₁, hc₁pos, hsift⟩ := sift_density_lb
  obtain ⟨C₅, hC₅pos, hlarge⟩ := large_e_bound
  obtain ⟨E, hE2, hEchoice⟩ :
      ∃ E : ℕ, 2 ≤ E ∧
        C₅ * A ^ 4 * (E : ℝ) ^ (-(3 / 2 : ℝ)) ≤ δ E / 4 := by
    set K : ℝ := 16 * (2 : ℝ) ^ (1 / 4 : ℝ) * (C₅ * A ^ 4) with hK
    have htend : Tendsto (fun E : ℕ => K * (E : ℝ) ^ (-(1 / 4 : ℝ)))
        atTop (𝓝 0) := by
      have h2 : Tendsto (fun E : ℕ => (E : ℝ) ^ (-(1 / 4 : ℝ)))
          atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (by norm_num)).comp
          tendsto_natCast_atTop_atTop
      simpa using h2.const_mul K
    obtain ⟨E, hKlt, hE2⟩ :=
      ((htend.eventually (Iio_mem_nhds hc₁pos)).and
        (eventually_ge_atTop 2)).exists
    refine ⟨E, hE2, ?_⟩
    have hE0 : (0 : ℝ) < E := by exact_mod_cast (by omega : 0 < E)
    have hlog0 : (0 : ℝ) < Real.log (2 * E) := by
      apply Real.log_pos
      have h2E : (2 : ℝ) ≤ E := by exact_mod_cast hE2
      linarith
    have hlog : Real.log (2 * E) ≤ 4 * (2 * (E : ℝ)) ^ (1 / 4 : ℝ) := by
      have h := Real.log_le_rpow_div (x := 2 * (E : ℝ)) (by positivity)
        (show (0 : ℝ) < 1 / 4 by norm_num)
      have h4 : (2 * (E : ℝ)) ^ (1 / 4 : ℝ) / (1 / 4) =
          4 * (2 * (E : ℝ)) ^ (1 / 4 : ℝ) := by ring
      rw [h4] at h
      exact h
    have hrpow : (E : ℝ) ^ (-(1 / 2 : ℝ)) * (2 * (E : ℝ)) ^ (1 / 4 : ℝ) =
        (2 : ℝ) ^ (1 / 4 : ℝ) * (E : ℝ) ^ (-(1 / 4 : ℝ)) := by
      rw [Real.mul_rpow (by norm_num) hE0.le,
        show (E : ℝ) ^ (-(1 / 2 : ℝ)) *
            ((2 : ℝ) ^ (1 / 4 : ℝ) * (E : ℝ) ^ (1 / 4 : ℝ)) =
          (2 : ℝ) ^ (1 / 4 : ℝ) *
            ((E : ℝ) ^ (-(1 / 2 : ℝ)) * (E : ℝ) ^ (1 / 4 : ℝ)) by ring,
        ← Real.rpow_add hE0,
        show (-(1 / 2 : ℝ) + 1 / 4) = -(1 / 4 : ℝ) by norm_num]
    have hkey :
        4 * (C₅ * A ^ 4) * (E : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log (2 * E) ≤ c₁ := by
      have hle :
          4 * (C₅ * A ^ 4) * (E : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log (2 * E) ≤
            K * (E : ℝ) ^ (-(1 / 4 : ℝ)) := by
        calc
          4 * (C₅ * A ^ 4) * (E : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log (2 * E)
              ≤ 4 * (C₅ * A ^ 4) * (E : ℝ) ^ (-(1 / 2 : ℝ)) *
                  (4 * (2 * (E : ℝ)) ^ (1 / 4 : ℝ)) := by
                    exact mul_le_mul_of_nonneg_left hlog (by positivity)
          _ = K * (E : ℝ) ^ (-(1 / 4 : ℝ)) := by
            have hcollect :
                4 * (C₅ * A ^ 4) * (E : ℝ) ^ (-(1 / 2 : ℝ)) *
                    (4 * (2 * (E : ℝ)) ^ (1 / 4 : ℝ)) =
                  16 * (C₅ * A ^ 4) *
                    ((E : ℝ) ^ (-(1 / 2 : ℝ)) *
                      (2 * (E : ℝ)) ^ (1 / 4 : ℝ)) := by ring
            rw [hcollect, hrpow, hK]
            ring
      linarith [hle, hKlt]
    have hElog2 : (0 : ℝ) < 4 * (E : ℝ) * Real.log (2 * E) := by positivity
    have hstep : C₅ * A ^ 4 * (E : ℝ) ^ (-(3 / 2 : ℝ)) ≤
        c₁ / (4 * (E : ℝ) * Real.log (2 * E)) := by
      rw [le_div_iff₀ hElog2]
      calc
        C₅ * A ^ 4 * (E : ℝ) ^ (-(3 / 2 : ℝ)) *
              (4 * (E : ℝ) * Real.log (2 * E)) =
            4 * (C₅ * A ^ 4) *
              ((E : ℝ) ^ (-(3 / 2 : ℝ)) * (E : ℝ)) * Real.log (2 * E) := by ring
        _ = 4 * (C₅ * A ^ 4) * (E : ℝ) ^ (-(1 / 2 : ℝ)) *
              Real.log (2 * E) := by
          have hEE : (E : ℝ) ^ (-(3 / 2 : ℝ)) * (E : ℝ) =
              (E : ℝ) ^ (-(1 / 2 : ℝ)) := by
            have h := (Real.rpow_add hE0 (-(3 / 2 : ℝ)) 1).symm
            rw [Real.rpow_one] at h
            rw [h, show (-(3 / 2 : ℝ) + 1) = -(1 / 2 : ℝ) by norm_num]
          rw [hEE]
        _ ≤ c₁ := hkey
    refine le_trans hstep ?_
    rw [show 4 * (E : ℝ) * Real.log (2 * E) =
      ((E : ℝ) * Real.log (2 * E)) * 4 by ring, ← div_div]
    exact (div_le_div_iff_of_pos_right (by norm_num)).2 (hsift E hE2)
  have hElog : (0 : ℝ) < (E : ℝ) * Real.log (2 * E) := by
    have h1 : (0 : ℝ) < (E : ℝ) := by exact_mod_cast (by omega : 0 < E)
    have h2 : (0 : ℝ) < Real.log (2 * E) := by
      apply Real.log_pos
      have hEreal : (2 : ℝ) ≤ E := by exact_mod_cast hE2
      linarith
    positivity
  have hδpos : 0 < δ E :=
    lt_of_lt_of_le (div_pos hc₁pos hElog) (hsift E hE2)
  refine ⟨δ E / 2, by positivity, ?_⟩
  have hodd : ∀ N, Nat.Coprime N (Qpr E) → Odd N := by
    intro N hN
    rcases Nat.even_or_odd N with he | ho
    · have hgcd : Nat.gcd N (Qpr E) = 1 := hN
      have hdvd : (2 : ℕ) ∣ 1 :=
        hgcd ▸ Nat.dvd_gcd he.two_dvd (two_dvd_Qpr E hE2)
      exact absurd hdvd (by decide)
    · exact ho
  have step0 : δ E ≤ lowerDensity (fun N => Nat.Coprime N (Qpr E)) :=
    sift_lowerDensity E hE2
  have step1 : δ E ≤ lowerDensity
      (fun N => Nat.Coprime N (Qpr E) ∧
        ¬ (Nat.Coprime N (Qpr E) ∧
          ∃ e d, 1 ≤ e ∧ e ≤ E ∧ N = F e d)) :=
    lowerDensity_and_not step0 (small_e_exclusion E hE2)
  have hB1 : CountIsLittleO
      (fun N => Nat.Coprime N (Qpr E) ∧ N ∉ R) :=
    CountIsLittleO.mono
      (fun N hN => ⟨hodd N hN.1, hN.2⟩) (odd_represented hDeep)
  have step2 : δ E ≤ lowerDensity
      (fun N => (Nat.Coprime N (Qpr E) ∧
          ¬ (Nat.Coprime N (Qpr E) ∧
            ∃ e d, 1 ≤ e ∧ e ≤ E ∧ N = F e d)) ∧
        ¬ (Nat.Coprime N (Qpr E) ∧ N ∉ R)) :=
    lowerDensity_and_not step1 hB1
  have hHbound : ∀ X : ℕ,
      (countUpTo (Hset A E) X : ℝ) ≤ δ E / 4 * X := by
    intro X
    calc
      (countUpTo (Hset A E) X : ℝ) ≤
          C₅ * A ^ 4 * (E : ℝ) ^ (-(3 / 2 : ℝ)) * X :=
        hlarge A hA E (by omega) X
      _ ≤ δ E / 4 * X :=
        mul_le_mul_of_nonneg_right hEchoice (by positivity)
  have step3 : δ E - δ E / 4 ≤ lowerDensity
      (fun N => ((Nat.Coprime N (Qpr E) ∧
          ¬ (Nat.Coprime N (Qpr E) ∧
            ∃ e d, 1 ≤ e ∧ e ≤ E ∧ N = F e d)) ∧
        ¬ (Nat.Coprime N (Qpr E) ∧ N ∉ R)) ∧ ¬ Hset A E N) :=
    lowerDensity_and_not_le hHbound step2
  have hmono : ∀ N,
      (((Nat.Coprime N (Qpr E) ∧
          ¬ (Nat.Coprime N (Qpr E) ∧
            ∃ e d, 1 ≤ e ∧ e ≤ E ∧ N = F e d)) ∧
        ¬ (Nat.Coprime N (Qpr E) ∧ N ∉ R)) ∧ ¬ Hset A E N) →
          Odd N ∧ N ∈ R ∧ (A * N : ℝ) < (f N : ℝ) := by
    intro N hgood
    obtain ⟨⟨⟨hQc, hnsmall⟩, hnunrep⟩, hnHset⟩ := hgood
    have hNR : N ∈ R := by
      by_contra hNR
      exact hnunrep ⟨hQc, hNR⟩
    refine ⟨hodd N hQc, hNR, ?_⟩
    by_contra hle
    rw [not_lt] at hle
    obtain ⟨e, d, he, hd, hfeq, hNF⟩ := f_mem_Fform N hNR
    by_cases heE : e ≤ E
    · exact hnsmall ⟨hQc, e, d, he, heE, hNF⟩
    · rw [not_le] at heE
      refine hnHset ⟨e, d, heE, hd, hNF, ?_⟩
      have hcast : (e : ℝ) * d = (f N : ℝ) := by
        rw [← Nat.cast_mul, ← hfeq]
      rw [hcast]
      exact hle
  calc
    δ E / 2 ≤ δ E - δ E / 4 := by linarith
    _ ≤ lowerDensity
        (fun N => ((Nat.Coprime N (Qpr E) ∧
            ¬ (Nat.Coprime N (Qpr E) ∧
              ∃ e d, 1 ≤ e ∧ e ≤ E ∧ N = F e d)) ∧
          ¬ (Nat.Coprime N (Qpr E) ∧ N ∉ R)) ∧ ¬ Hset A E N) := step3
    _ ≤ lowerDensity
        (fun N => Odd N ∧ N ∈ R ∧ (A * N : ℝ) < (f N : ℝ)) :=
      lowerDensity_mono hmono

end Represented

namespace Erdos1054.OddTail

/-- `S` contains every odd natural number except a density-zero exceptional
set.  Its even members are completely unrestricted, so this hypothesis is
strictly weaker than requiring `S` itself to have natural density one. -/
def HasOddDensityOne (S : Set ℕ) : Prop :=
  _root_.Represented.CountIsLittleO (fun n : ℕ => Odd n ∧ n ∉ S)

/-- Global natural density one implies the weaker odd-only hypothesis. -/
theorem density_one_has_odd_density_one
    (S : Set ℕ) (hS : _root_.Erdos1054.HasDensityOne S) :
    HasOddDensityOne S := by
  apply _root_.Represented.CountIsLittleO.mono
    (fun n hn => hn.2)
  exact _root_.Erdos1054.densityOne_complement_littleO hS

/-- Keeping exactly the odd integers already satisfies the odd-only
hypothesis; in particular, no even integer needs to be retained. -/
theorem odds_have_odd_density_one :
    HasOddDensityOne {n : ℕ | Odd n} := by
  unfold HasOddDensityOne _root_.Represented.CountIsLittleO
  have hempty (X : ℕ) :
      _root_.Represented.countUpTo
        (fun n : ℕ => Odd n ∧ n ∉ {m : ℕ | Odd m}) X = 0 := by
    unfold _root_.Represented.countUpTo _root_.Represented.setUpTo
    have hset :
        {n : ℕ | n ≤ X ∧ Odd n ∧ n ∉ {m : ℕ | Odd m}} = ∅ := by
      ext n
      simp
    rw [hset]
    exact Set.ncard_empty ℕ
  simp_rw [hempty]
  simp

/-- The exact number of odd natural numbers in the official half-open
initial interval is `b / 2`, including both endpoint parities. -/
theorem odd_Iio_ncard (b : ℕ) :
    (({n : ℕ | Odd n} ∩ Set.Iio b).ncard) = b / 2 := by
  have hset :
      ({n : ℕ | Odd n} ∩ Set.Iio b) =
        (fun k : ℕ => 2 * k + 1) '' Set.Iio (b / 2) := by
    ext n
    constructor
    · rintro ⟨hodd, hn⟩
      obtain ⟨k, hk⟩ := hodd
      refine ⟨k, ?_, ?_⟩
      · change k < b / 2
        change n < b at hn
        omega
      · change 2 * k + 1 = n
        omega
    · rintro ⟨k, hk, rfl⟩
      refine ⟨?_, ?_⟩
      · change Odd (2 * k + 1)
        exact ⟨k, by omega⟩
      · change 2 * k + 1 < b
        change k < b / 2 at hk
        omega
  rw [hset, Set.ncard_image_of_injective _ (fun _ _ h => by omega),
    Set.ncard_Iio_nat]

/-- The odd integers have exact natural density `1 / 2`, using the literal
official partial-density formula with both intersections with `Set.univ`. -/
theorem odds_density_one_half :
    Tendsto
      (fun b : ℕ =>
        (((({n : ℕ | Odd n} ∩ Set.univ) ∩ Set.Iio b).ncard : ℝ) /
          ((Set.univ ∩ Set.Iio b).ncard : ℝ)))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hmod : Tendsto
      (fun n : ℕ => ((n % 2 : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 0) :=
    tendsto_mod_div_atTop_nhds_zero_nat (by norm_num)
  have hlim : Tendsto
      (fun n : ℕ => (1 - ((n % 2 : ℕ) : ℝ) / (n : ℝ)) / 2)
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hmod).div_const 2
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with b hb
  simp only [Set.inter_univ, Set.univ_inter, Set.ncard_Iio_nat,
    odd_Iio_ncard]
  have hbreal : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hdecomp : ((b % 2 : ℕ) : ℝ) +
      2 * ((b / 2 : ℕ) : ℝ) = (b : ℝ) := by
    exact_mod_cast Nat.mod_add_div b 2
  field_simp
  linarith

/-- Every admissible set, after restriction to its actual odd members, has
exact natural density `1 / 2` in the literal official partial-density
formula.  Its unrestricted even membership is irrelevant. -/
theorem odd_full_intersection_density_one_half
    (S : Set ℕ) (hS : HasOddDensityOne S) :
    Tendsto
      (fun b : ℕ =>
        (((((S ∩ {n : ℕ | Odd n}) ∩ Set.univ) ∩ Set.Iio b).ncard : ℝ) /
          ((Set.univ ∩ Set.Iio b).ncard : ℝ)))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  let B : ℕ → Set ℕ := fun b =>
    {n : ℕ | Odd n ∧ n ∉ S} ∩ Set.Iio b
  have hbadzero : Tendsto
      (fun b : ℕ => ((B b).ncard : ℝ) / (b : ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero
      (fun b => div_nonneg (by positivity) (by positivity))
      (fun b => ?_)
      hS.tendsto_div
    have hcount : (B b).ncard ≤
        _root_.Represented.countUpTo
          (fun n : ℕ => Odd n ∧ n ∉ S) b := by
      exact Set.ncard_le_ncard
        (s := B b)
        (t := _root_.Represented.setUpTo
          (fun n : ℕ => Odd n ∧ n ∉ S) b)
        (fun n hn => ⟨Nat.le_of_lt hn.2, hn.1⟩)
        (_root_.Represented.setUpTo_finite _ b)
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcount)
      (by positivity)
  have hodd : Tendsto
      (fun b : ℕ =>
        ((({n : ℕ | Odd n} ∩ Set.Iio b).ncard : ℝ) / (b : ℝ)))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [Set.inter_univ, Set.univ_inter, Set.ncard_Iio_nat] using
      odds_density_one_half
  have hlim : Tendsto
      (fun b : ℕ =>
        ((({n : ℕ | Odd n} ∩ Set.Iio b).ncard : ℝ) / (b : ℝ)) -
          ((B b).ncard : ℝ) / (b : ℝ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa using hodd.sub hbadzero
  refine hlim.congr' (Filter.Eventually.of_forall (fun b => ?_))
  simp only [Set.inter_univ, Set.univ_inter, Set.ncard_Iio_nat]
  let U := {n : ℕ | Odd n} ∩ Set.Iio b
  have hgood : U ∩ S = (S ∩ {n : ℕ | Odd n}) ∩ Set.Iio b := by
    ext n
    simp [U, and_assoc, and_comm, and_left_comm]
  have hbad : U \ S = B b := by
    ext n
    simp [U, B, and_assoc, and_comm, and_left_comm]
  have hpartition := Set.ncard_inter_add_ncard_sdiff_eq_ncard U S
    ((Set.finite_Iio b).subset (fun _ hn => hn.2))
  rw [hgood, hbad] at hpartition
  have hreal :
      (((S ∩ {n : ℕ | Odd n}) ∩ Set.Iio b).ncard : ℝ) +
        ((B b).ncard : ℝ) = (U.ncard : ℝ) := by
    exact_mod_cast hpartition
  dsimp [U] at hreal
  rw [← sub_div]
  congr 1
  linarith

/-- Relative to the odd integers themselves, every admissible set retains
asymptotically all of them.  The denominator is the actual number of odd
integers below the same cutoff, not the number of all natural numbers. -/
theorem retained_relative_odd_density_one
    (S : Set ℕ) (hS : HasOddDensityOne S) :
    Tendsto
      (fun b : ℕ =>
        ((((S ∩ {n : ℕ | Odd n}) ∩ Set.Iio b).ncard : ℝ) /
          (({n : ℕ | Odd n} ∩ Set.Iio b).ncard : ℝ)))
      atTop (𝓝 (1 : ℝ)) := by
  have hretained : Tendsto
      (fun b : ℕ =>
        ((((S ∩ {n : ℕ | Odd n}) ∩ Set.Iio b).ncard : ℝ) /
          (b : ℝ)))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [Set.inter_univ, Set.univ_inter, Set.ncard_Iio_nat] using
      odd_full_intersection_density_one_half S hS
  have hodd : Tendsto
      (fun b : ℕ =>
        ((({n : ℕ | Odd n} ∩ Set.Iio b).ncard : ℝ) /
          (b : ℝ)))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [Set.inter_univ, Set.univ_inter, Set.ncard_Iio_nat] using
      odds_density_one_half
  have hratio : Tendsto
      (fun b : ℕ =>
        ((((S ∩ {n : ℕ | Odd n}) ∩ Set.Iio b).ncard : ℝ) /
          (b : ℝ)) /
        ((({n : ℕ | Odd n} ∩ Set.Iio b).ncard : ℝ) /
          (b : ℝ)))
      atTop (𝓝 (1 : ℝ)) := by
    convert hretained.div hodd (by norm_num : (1 / 2 : ℝ) ≠ 0)
      using 1
    norm_num
  refine hratio.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with b hb
  have hbreal : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  exact div_div_div_cancel_right₀ hbreal _ _

/-- The missing-odd `o(X)` condition is exactly relative density one among
the odd integers.  Both directions use the actual odd-count denominator;
the proof handles its finite zero endpoints and the half-open/closed shift. -/
theorem has_odd_density_one_iff_relative (S : Set ℕ) :
    HasOddDensityOne S ↔
      Tendsto
        (fun b : ℕ =>
          ((((S ∩ {n : ℕ | Odd n}) ∩ Set.Iio b).ncard : ℝ) /
            (({n : ℕ | Odd n} ∩ Set.Iio b).ncard : ℝ)))
        atTop (𝓝 (1 : ℝ)) := by
  constructor
  · exact retained_relative_odd_density_one S
  · intro hS
    let U : ℕ → Set ℕ := fun b => {n : ℕ | Odd n} ∩ Set.Iio b
    let G : ℕ → Set ℕ := fun b => (S ∩ {n : ℕ | Odd n}) ∩ Set.Iio b
    let B : ℕ → Set ℕ := fun b => {n : ℕ | Odd n ∧ n ∉ S} ∩ Set.Iio b
    have hodd : Tendsto (fun b : ℕ => ((U b).ncard : ℝ) / (b : ℝ))
        atTop (𝓝 (1 / 2 : ℝ)) := by
      simpa only [Set.inter_univ, Set.univ_inter, Set.ncard_Iio_nat] using
        odds_density_one_half
    have hgood : Tendsto (fun b : ℕ => ((G b).ncard : ℝ) / (b : ℝ))
        atTop (𝓝 (1 / 2 : ℝ)) := by
      have hprod := hS.mul hodd
      simp only [one_mul] at hprod
      refine hprod.congr' ?_
      filter_upwards [eventually_ge_atTop (2 : ℕ)] with b hb
      have hUpos : 0 < (U b).ncard := by
        dsimp [U]
        rw [odd_Iio_ncard]
        omega
      have hUreal : ((U b).ncard : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hUpos)
      change ((G b).ncard : ℝ) / ((U b).ncard : ℝ) *
        (((U b).ncard : ℝ) / (b : ℝ)) = _
      field_simp
    have hbad : Tendsto (fun b : ℕ => ((B b).ncard : ℝ) / (b : ℝ))
        atTop (𝓝 (0 : ℝ)) := by
      have hsub := hodd.sub hgood
      simp only [sub_self] at hsub
      refine hsub.congr' (Filter.Eventually.of_forall (fun b => ?_))
      have hg : U b ∩ S = G b := by
        ext n
        simp [U, G, and_assoc, and_comm, and_left_comm]
      have hbadset : U b \ S = B b := by
        ext n
        simp [U, B, and_assoc, and_comm, and_left_comm]
      have hpart := Set.ncard_inter_add_ncard_sdiff_eq_ncard (U b) S
        ((Set.finite_Iio b).subset (fun _ hn => hn.2))
      rw [hg, hbadset] at hpart
      have hreal : ((G b).ncard : ℝ) + ((B b).ncard : ℝ) =
          ((U b).ncard : ℝ) := by exact_mod_cast hpart
      rw [← sub_div]
      congr 1
      linarith
    have hshift : Tendsto
        (fun X : ℕ => ((B (X + 1)).ncard : ℝ) / ((X + 1 : ℕ) : ℝ))
        atTop (𝓝 (0 : ℝ)) :=
      hbad.comp (tendsto_add_atTop_nat 1)
    have hprod : Tendsto
        (fun X : ℕ =>
          (((B (X + 1)).ncard : ℝ) / ((X + 1 : ℕ) : ℝ)) *
            (((X + 1 : ℕ) : ℝ) / (X : ℝ)))
        atTop (𝓝 (0 : ℝ)) := by
      simpa using hshift.mul Erdos1054.shifted_nat_ratio_tendsto_one
    have hratio : Tendsto
        (fun X : ℕ =>
          (_root_.Represented.countUpTo (fun n => Odd n ∧ n ∉ S) X : ℝ) /
            (X : ℝ)) atTop (𝓝 (0 : ℝ)) := by
      refine hprod.congr' (Filter.Eventually.of_forall (fun X => ?_))
      have hcount : _root_.Represented.countUpTo (fun n => Odd n ∧ n ∉ S) X =
          (B (X + 1)).ncard := by
        unfold _root_.Represented.countUpTo _root_.Represented.setUpTo
        congr 1
        ext n
        simp [B, and_comm, and_left_comm]
      dsimp only
      rw [hcount]
      have hXp : ((X + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
    rw [HasOddDensityOne, _root_.Represented.CountIsLittleO]
    refine (isLittleO_iff_tendsto' ?_).mpr hratio
    filter_upwards [eventually_gt_atTop 0] with X hX
    intro hzero
    have hpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
    exact (hpos.ne' hzero).elim

/-- The odd integers fail the old global-density-one hypothesis. Together
with `odds_have_odd_density_one`, this proves the new hypothesis is strictly
weaker, not merely an alternative presentation of density one. -/
theorem odds_not_density_one :
    ¬ _root_.Erdos1054.HasDensityOne {n : ℕ | Odd n} := by
  intro hone
  have hhalf : Tendsto
      (fun b : ℕ => (({n : ℕ | Odd n} ∩ Set.Iio b).ncard : ℝ) / (b : ℝ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [Set.inter_univ, Set.univ_inter, Set.ncard_Iio_nat]
      using odds_density_one_half
  have hcontra : (1 : ℝ) = 1 / 2 :=
    tendsto_nhds_unique hone hhalf
  norm_num at hcontra

/-- Deleting a density-zero subset of the odd integers preserves the *exact*
lower density of every odd-supported predicate, not merely positivity or a
particular quantitative lower bound.  The values on even integers play no
role. -/
theorem lower_density_odd_inter_eq
    (S : Set ℕ) (hS : HasOddDensityOne S) (P : ℕ → Prop) :
    _root_.Represented.lowerDensity
        (fun n : ℕ => n ∈ S ∧ Odd n ∧ P n) =
      _root_.Represented.lowerDensity (fun n : ℕ => Odd n ∧ P n) := by
  apply le_antisymm
  · exact _root_.Represented.lowerDensity_mono
      (fun _ hn => ⟨hn.2.1, hn.2.2⟩)
  · have hsurvive := _root_.Represented.lowerDensity_and_not
      (le_refl (_root_.Represented.lowerDensity
        (fun n : ℕ => Odd n ∧ P n))) hS
    refine hsurvive.trans (_root_.Represented.lowerDensity_mono ?_)
    intro n hn
    refine ⟨?_, hn.1.1, hn.1.2⟩
    by_contra hnS
    exact hn.2 ⟨hn.1.1, hnS⟩

/-- Exact finite partition of any odd-supported counting function into the
retained witnesses and the witnesses removed from `S`. -/
theorem odd_count_partition (S : Set ℕ) (P : ℕ → Prop) (X : ℕ) :
    _root_.Represented.countUpTo (fun n : ℕ => Odd n ∧ P n) X =
      _root_.Represented.countUpTo
          (fun n : ℕ => n ∈ S ∧ Odd n ∧ P n) X +
        _root_.Represented.countUpTo
          (fun n : ℕ => Odd n ∧ P n ∧ n ∉ S) X := by
  classical
  let U := _root_.Represented.setUpTo (fun n : ℕ => Odd n ∧ P n) X
  have hgood : U ∩ S =
      _root_.Represented.setUpTo
        (fun n : ℕ => n ∈ S ∧ Odd n ∧ P n) X := by
    ext n
    simp [U, _root_.Represented.setUpTo, and_assoc, and_comm, and_left_comm]
  have hbad : U \ S =
      _root_.Represented.setUpTo
        (fun n : ℕ => Odd n ∧ P n ∧ n ∉ S) X := by
    ext n
    simp [U, _root_.Represented.setUpTo, and_assoc]
  have hpartition := Set.ncard_inter_add_ncard_sdiff_eq_ncard U S
    (_root_.Represented.setUpTo_finite (fun n : ℕ => Odd n ∧ P n) X)
  rw [hgood, hbad] at hpartition
  exact hpartition.symm

/-- The loss in the actual finite counting function of *every* odd-supported
predicate is `o(X)` after deleting an admissible exceptional set. -/
theorem odd_count_loss_little_o
    (S : Set ℕ) (hS : HasOddDensityOne S) (P : ℕ → Prop) :
    (fun X : ℕ =>
      (_root_.Represented.countUpTo (fun n : ℕ => Odd n ∧ P n) X : ℝ) -
        (_root_.Represented.countUpTo
          (fun n : ℕ => n ∈ S ∧ Odd n ∧ P n) X : ℝ))
      =o[atTop] (fun X : ℕ => (X : ℝ)) := by
  have hbad : _root_.Represented.CountIsLittleO
      (fun n : ℕ => Odd n ∧ P n ∧ n ∉ S) :=
    _root_.Represented.CountIsLittleO.mono
      (fun _ hn => ⟨hn.1, hn.2.2⟩) hS
  unfold _root_.Represented.CountIsLittleO at hbad
  have heq :
      (fun X : ℕ =>
        (_root_.Represented.countUpTo (fun n : ℕ => Odd n ∧ P n) X : ℝ) -
          (_root_.Represented.countUpTo
            (fun n : ℕ => n ∈ S ∧ Odd n ∧ P n) X : ℝ)) =
        (fun X : ℕ =>
          (_root_.Represented.countUpTo
            (fun n : ℕ => Odd n ∧ P n ∧ n ∉ S) X : ℝ)) := by
    funext X
    rw [odd_count_partition S P X, Nat.cast_add]
    ring
  rw [heq]
  exact hbad

/-- The complete normalized finite counting profiles of an odd predicate
before and after admissible deletion differ by a quantity tending to zero. -/
theorem odd_partial_density_difference_tends_zero
    (S : Set ℕ) (hS : HasOddDensityOne S) (P : ℕ → Prop) :
    Tendsto
      (fun X : ℕ =>
        (_root_.Represented.countUpTo (fun n : ℕ => Odd n ∧ P n) X : ℝ) /
            (X : ℝ) -
          (_root_.Represented.countUpTo
            (fun n : ℕ => n ∈ S ∧ Odd n ∧ P n) X : ℝ) / (X : ℝ))
      atTop (𝓝 0) := by
  simpa only [sub_div] using
    (odd_count_loss_little_o S hS P).tendsto_div_nhds_zero

/-- Deleting a density-zero odd exceptional set also preserves the *exact
upper density* of every odd-supported predicate, even when no natural
density exists.  Combined with `lower_density_odd_inter_eq`, both
asymptotic endpoints are unchanged. -/
theorem upper_density_odd_inter_eq
    (S : Set ℕ) (hS : HasOddDensityOne S) (P : ℕ → Prop) :
    limsup
        (fun X : ℕ =>
          (_root_.Represented.countUpTo
            (fun n : ℕ => n ∈ S ∧ Odd n ∧ P n) X : ℝ) / (X : ℝ)) atTop =
      limsup
        (fun X : ℕ =>
          (_root_.Represented.countUpTo
            (fun n : ℕ => Odd n ∧ P n) X : ℝ) / (X : ℝ)) atTop := by
  let u : ℕ → ℝ := fun X =>
    (_root_.Represented.countUpTo
      (fun n : ℕ => n ∈ S ∧ Odd n ∧ P n) X : ℝ) / (X : ℝ)
  let v : ℕ → ℝ := fun X =>
    (_root_.Represented.countUpTo
      (fun n : ℕ => Odd n ∧ P n ∧ n ∉ S) X : ℝ) / (X : ℝ)
  have hbad : _root_.Represented.CountIsLittleO
      (fun n : ℕ => Odd n ∧ P n ∧ n ∉ S) :=
    _root_.Represented.CountIsLittleO.mono
      (fun _ hn => ⟨hn.1, hn.2.2⟩) hS
  have hvzero : Tendsto v atTop (𝓝 0) := by
    exact hbad.tendsto_div
  have huabove : IsBoundedUnder (· ≤ ·) atTop u := by
    refine ⟨2, Filter.eventually_map.2 ?_⟩
    exact Filter.Eventually.of_forall
      (fun X => _root_.Represented.countUpTo_div_le_two _ X)
  have hubelow : IsBoundedUnder (· ≥ ·) atTop u := by
    refine ⟨0, Filter.eventually_map.2 ?_⟩
    exact Filter.Eventually.of_forall (fun X => by positivity)
  have hvabove : IsBoundedUnder (· ≤ ·) atTop v := by
    refine ⟨2, Filter.eventually_map.2 ?_⟩
    exact Filter.Eventually.of_forall
      (fun X => _root_.Represented.countUpTo_div_le_two _ X)
  have hvbelow : IsBoundedUnder (· ≥ ·) atTop v := by
    refine ⟨0, Filter.eventually_map.2 ?_⟩
    exact Filter.Eventually.of_forall (fun X => by positivity)
  have hupper : limsup (u + v) atTop ≤ limsup u atTop + limsup v atTop :=
    limsup_add_le hubelow huabove hvbelow.isCoboundedUnder_le hvabove
  have hlower : limsup u atTop + liminf v atTop ≤ limsup (u + v) atTop :=
    le_limsup_add huabove hubelow.isCoboundedUnder_le hvabove hvbelow
  rw [hvzero.limsup_eq, add_zero] at hupper
  rw [hvzero.liminf_eq, add_zero] at hlower
  have hsum : limsup (u + v) atTop = limsup u atTop :=
    le_antisymm hupper hlower
  have heq : u + v =
      (fun X : ℕ =>
        (_root_.Represented.countUpTo
          (fun n : ℕ => Odd n ∧ P n) X : ℝ) / (X : ℝ)) := by
    funext X
    simp only [Pi.add_apply]
    dsimp [u, v]
    rw [← add_div, ← Nat.cast_add, ← odd_count_partition S P X]
  rw [heq] at hsum
  exact hsum.symm

/-- At every real threshold, the exact official minimizer exceeds that
threshold on a positive-lower-density set of odd represented integers. -/
theorem positive_lower_density_real (A : ℝ) (hA : 1 ≤ A) :
    _root_.Erdos1054.PositiveLowerDensity
      (fun n : ℕ => Odd n ∧ n ∈ _root_.Represented.R ∧
        A * (n : ℝ) < (_root_.Erdos1054.OriginalNth.f n : ℝ)) := by
  apply _root_.Erdos1054.lowerDensity_to_positiveLowerDensity
  obtain ⟨c, hc0, hc⟩ := _root_.Represented.main_odd
    (_root_.Erdos1054.goldbach_of_matching_density
      _root_.Erdos1054.Unconditional.almost_all_binary_goldbach) A hA
  refine ⟨c, hc0, ?_⟩
  simpa only [_root_.Erdos1054.OriginalNth.f_eq_supported] using hc

/-- The odd positive-lower-density conclusion at each natural threshold,
with the literal official zero-padded minimizer. -/
theorem positive_lower_density (A : ℕ) (hA : 1 ≤ A) :
    _root_.Erdos1054.PositiveLowerDensity
      (fun n : ℕ => Odd n ∧ n ∈ _root_.Represented.R ∧
        A * n < _root_.Erdos1054.OriginalNth.f n) := by
  have hAreal : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  apply _root_.Erdos1054.positiveLowerDensity_mono
    (P := fun n : ℕ => Odd n ∧ n ∈ _root_.Represented.R ∧
      (A : ℝ) * (n : ℝ) < (_root_.Erdos1054.OriginalNth.f n : ℝ))
  · intro n hn
    exact ⟨hn.1, hn.2.1, by exact_mod_cast hn.2.2⟩
  · exact positive_lower_density_real A hAreal

/-- Removing only a density-zero subset of the odd integers preserves
positive lower density of the odd represented large-ratio witnesses.
There is no hypothesis whatsoever on the retained even integers. -/
theorem positive_lower_density_real_in_odd_density_one
    (S : Set ℕ) (hS : HasOddDensityOne S)
    (A : ℝ) (hA : 1 ≤ A) :
    _root_.Erdos1054.PositiveLowerDensity
      (fun n : ℕ => n ∈ S ∧ Odd n ∧ n ∈ _root_.Represented.R ∧
        A * (n : ℝ) < (_root_.Erdos1054.OriginalNth.f n : ℝ)) := by
  classical
  apply _root_.Erdos1054.lowerDensity_to_positiveLowerDensity
  obtain ⟨c, hc0, hc⟩ := _root_.Represented.main_odd
    (_root_.Erdos1054.goldbach_of_matching_density
      _root_.Erdos1054.Unconditional.almost_all_binary_goldbach) A hA
  refine ⟨c, hc0, ?_⟩
  refine (_root_.Represented.lowerDensity_and_not hc hS).trans
    (_root_.Represented.lowerDensity_mono ?_)
  intro n hn
  refine ⟨?_, hn.1.1, hn.1.2.1, ?_⟩
  · by_contra hnS
    exact hn.2 ⟨hn.1.1, hnS⟩
  · simpa only [_root_.Erdos1054.OriginalNth.f_eq_supported] using
      hn.1.2.2

/-- Deleting an arbitrary density-zero exceptional set from the odd large-ratio
tail preserves positive lower density.  Equivalently every density-one set
still contains a positive-lower-density set of these odd witnesses. -/
theorem positive_lower_density_real_in_density_one
    (S : Set ℕ) (hS : _root_.Erdos1054.HasDensityOne S)
    (A : ℝ) (hA : 1 ≤ A) :
    _root_.Erdos1054.PositiveLowerDensity
      (fun n : ℕ => n ∈ S ∧ Odd n ∧ n ∈ _root_.Represented.R ∧
        A * (n : ℝ) < (_root_.Erdos1054.OriginalNth.f n : ℝ)) := by
  apply _root_.Erdos1054.lowerDensity_to_positiveLowerDensity
  obtain ⟨c, hc0, hc⟩ := _root_.Represented.main_odd
    (_root_.Erdos1054.goldbach_of_matching_density
      _root_.Erdos1054.Unconditional.almost_all_binary_goldbach) A hA
  refine ⟨c, hc0, ?_⟩
  have hsurvive := _root_.Represented.lowerDensity_and_not hc
    (_root_.Erdos1054.densityOne_complement_littleO hS)
  simpa only [_root_.Erdos1054.OriginalNth.f_eq_supported,
    not_not, and_assoc, and_comm, and_left_comm] using hsurvive

/-- The density-one survival statement also holds at every natural threshold
without changing the exact official minimizer. -/
theorem positive_lower_density_in_density_one
    (S : Set ℕ) (hS : _root_.Erdos1054.HasDensityOne S)
    (A : ℕ) (hA : 1 ≤ A) :
    _root_.Erdos1054.PositiveLowerDensity
      (fun n : ℕ => n ∈ S ∧ Odd n ∧ n ∈ _root_.Represented.R ∧
        A * n < _root_.Erdos1054.OriginalNth.f n) := by
  have hAreal : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  apply _root_.Erdos1054.positiveLowerDensity_mono
    (P := fun n : ℕ => n ∈ S ∧ Odd n ∧ n ∈ _root_.Represented.R ∧
      (A : ℝ) * (n : ℝ) < (_root_.Erdos1054.OriginalNth.f n : ℝ))
  · intro n hn
    exact ⟨hn.1, hn.2.1, hn.2.2.1,
      by exact_mod_cast hn.2.2.2⟩
  · exact positive_lower_density_real_in_density_one S hS A hAreal

/-- Arbitrarily far out, an odd represented integer exceeds any prescribed
natural ratio threshold. -/
theorem late_witness (A B : ℕ) (hA : 1 ≤ A) :
    ∃ n : ℕ, B ≤ n ∧ Odd n ∧ n ∈ _root_.Represented.R ∧
      A * n < _root_.Erdos1054.OriginalNth.f n := by
  obtain ⟨n, hn, hgood⟩ := Filter.frequently_atTop.mp
    (_root_.Erdos1054.positiveLowerDensity_frequently
      (positive_lower_density A hA)) B
  exact ⟨n, hn, hgood⟩

/-- The actual extended-real limsup along the odd subsequence is infinite.
The corresponding even-subsequence assertion is not proved here. -/
theorem odd_subsequence_limsup :
    Filter.atTop.limsup
      (fun n : ℕ =>
        (_root_.Erdos1054.OriginalNth.f (2 * n + 1) : EReal) /
          (2 * n + 1)) = ⊤ := by
  apply top_unique
  apply (le_limsup_iff).2
  intro y hy
  obtain ⟨a, hya, _⟩ := EReal.exists_between_coe_real hy
  let A : ℝ := max a 1
  have haA : a ≤ A := le_max_left a 1
  have hA : 1 ≤ A := le_max_right a 1
  have hfreq : ∃ᶠ N : ℕ in Filter.atTop,
      Odd N ∧ N ∈ _root_.Represented.R ∧
        A * (N : ℝ) < (_root_.Erdos1054.OriginalNth.f N : ℝ) :=
    _root_.Erdos1054.positiveLowerDensity_frequently
      (positive_lower_density_real A hA)
  rw [Filter.frequently_atTop] at hfreq ⊢
  intro B
  obtain ⟨N, hBN, hodd, hNR, hlarge⟩ := hfreq (2 * B + 1)
  obtain ⟨k, hk⟩ := hodd
  refine ⟨k, by omega, ?_⟩
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have hNnat : 0 < N :=
      _root_.Erdos1054.represented_pos
        ((_root_.Erdos1054.represented_iff_memR N).mpr hNR)
    exact_mod_cast hNnat
  have hratio : A <
      (_root_.Erdos1054.OriginalNth.f N : ℝ) / (N : ℝ) :=
    (lt_div_iff₀ hNpos).mpr hlarge
  have ha_ratio : a <
      (_root_.Erdos1054.OriginalNth.f N : ℝ) / (N : ℝ) :=
    haA.trans_lt hratio
  have htarget : y <
      (_root_.Erdos1054.OriginalNth.f N : EReal) / N := by
    calc
      y < (a : EReal) := hya
      _ < (((_root_.Erdos1054.OriginalNth.f N : ℝ) /
            (N : ℝ) : ℝ) : EReal) := EReal.coe_lt_coe_iff.mpr ha_ratio
      _ = (_root_.Erdos1054.OriginalNth.f N : EReal) / N := by
        rw [EReal.coe_div]
        rfl
  have hNk : N = 2 * k + 1 := by omega
  simpa [hNk, EReal.natCast_mul] using htarget

/-- The exact extended-real limsup is infinite on the actual ordered subtype
of the surviving odd integers after deleting any density-zero set of odds.
Unlike the official density-one witness, the subtype occurs in the filter
itself, and unlike the density-one strengthening, all evens may be absent. -/
theorem limsup_on_odd_density_one_subtype
    (S : Set ℕ) (hS : HasOddDensityOne S) :
    (atTop : Filter {n : ℕ // n ∈ S ∧ Odd n}).limsup
      (fun n : {n : ℕ // n ∈ S ∧ Odd n} =>
        (_root_.Erdos1054.OriginalNth.f (n : ℕ) : EReal) /
          (n : ℕ)) = ⊤ := by
  classical
  have hone : ∃ᶠ n : ℕ in atTop,
      n ∈ S ∧ Odd n ∧ n ∈ _root_.Represented.R ∧
        (1 : ℝ) * (n : ℝ) <
          (_root_.Erdos1054.OriginalNth.f n : ℝ) :=
    _root_.Erdos1054.positiveLowerDensity_frequently
      (positive_lower_density_real_in_odd_density_one
        S hS 1 (le_refl 1))
  obtain ⟨n₀, _, hn₀⟩ := frequently_atTop.mp hone 0
  let _ : Nonempty {n : ℕ // n ∈ S ∧ Odd n} :=
    ⟨⟨n₀, hn₀.1, hn₀.2.1⟩⟩
  apply top_unique
  apply (le_limsup_iff).2
  intro y hy
  obtain ⟨a, hya, _⟩ := EReal.exists_between_coe_real hy
  let A : ℝ := max a 1
  have haA : a ≤ A := le_max_left a 1
  have hA : 1 ≤ A := le_max_right a 1
  have hfrequent : ∃ᶠ n : ℕ in atTop,
      n ∈ S ∧ Odd n ∧ n ∈ _root_.Represented.R ∧
        A * (n : ℝ) <
          (_root_.Erdos1054.OriginalNth.f n : ℝ) :=
    _root_.Erdos1054.positiveLowerDensity_frequently
      (positive_lower_density_real_in_odd_density_one S hS A hA)
  have hsubtype : ∃ᶠ n : {n : ℕ // n ∈ S ∧ Odd n} in atTop,
      (n : ℕ) ∈ _root_.Represented.R ∧
        A * ((n : ℕ) : ℝ) <
          (_root_.Erdos1054.OriginalNth.f (n : ℕ) : ℝ) := by
    rw [frequently_atTop]
    intro n
    obtain ⟨m, hnm, hmS, hmOdd, hmR, hmlarge⟩ :=
      frequently_atTop.mp hfrequent (n : ℕ)
    exact ⟨⟨m, hmS, hmOdd⟩, hnm, hmR, hmlarge⟩
  refine hsubtype.mono (fun n hn => ?_)
  have hnpositive : (0 : ℝ) < ((n : ℕ) : ℝ) := by
    exact_mod_cast _root_.Erdos1054.represented_pos
      ((_root_.Erdos1054.represented_iff_memR (n : ℕ)).mpr hn.1)
  have hratio : A <
      (_root_.Erdos1054.OriginalNth.f (n : ℕ) : ℝ) /
        ((n : ℕ) : ℝ) :=
    (lt_div_iff₀ hnpositive).mpr hn.2
  calc
    y < (a : EReal) := hya
    _ < (((_root_.Erdos1054.OriginalNth.f (n : ℕ) : ℝ) /
      ((n : ℕ) : ℝ) : ℝ) : EReal) :=
      EReal.coe_lt_coe_iff.mpr (haA.trans_lt hratio)
    _ = (_root_.Erdos1054.OriginalNth.f (n : ℕ) : EReal) /
      (n : ℕ) := by
      rw [EReal.coe_div]
      rfl

end Erdos1054.OddTail
