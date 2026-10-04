module

public import DeficiencyPrimePower433
public import DeficiencyFiniteMass433
public import DeficiencyMainTail433

@[expose] public section


/-!
# Assembly of the actual initial-deficiency asymptotic

The genuine moving smooth-core/reduced-prime-progression family is split into
fixed small cores, middle cores, and large cores.  Fixed-core arithmetic-
progression PNT and the audited total admissible coefficient bound control the
first part; the unconditional fixed-support Rankin bound removes the last.

The remaining middle-core condition is stated solely in terms of the actual
explicit prime-progression family.  It contains no covering or deficiency
predicate and no assumption of the asymptotic being proved.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos689

/-- Actual admissible core/residue pairs below a fixed core cutoff. -/
noncomputable def initialDeficiencySmallCoreFamily
    (S : Finset ℕ) (b : ℕ → ℕ) (n R : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (initialDeficiencySmoothCoreFamily S b n).filter
    fun v => v.1 ≤ R

/-- Actual admissible core/residue pairs in the moving middle window. -/
noncomputable def initialDeficiencyMiddleCoreFamily
    (S : Finset ℕ) (b : ℕ → ℕ) (n R : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (initialDeficiencySmoothCoreFamily S b n).filter
    fun v => R < v.1 ∧ (v.1 : ℝ) < Real.sqrt (n : ℝ)

/-- Actual admissible core/residue pairs above the moving square-root cutoff. -/
noncomputable def initialDeficiencyLargeCoreFamily
    (S : Finset ℕ) (b : ℕ → ℕ) (n R : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (initialDeficiencySmoothCoreFamily S b n).filter
    fun v => R < v.1 ∧ Real.sqrt (n : ℝ) ≤ (v.1 : ℝ)

/-- Once the endpoint exceeds a fixed cutoff, its actual small-core family is
exactly the fixed finite admissible family at that cutoff. -/
theorem initialDeficiencySmallCoreFamily_eq_fixed
    (S : Finset ℕ) (b : ℕ → ℕ) {n R : ℕ} (hRn : R ≤ n) :
    initialDeficiencySmallCoreFamily S b n R =
      initialDeficiencySmoothCoreFamily S b R := by
  classical
  ext ⟨c, r⟩
  change
    (c, r) ∈ (initialDeficiencySmoothCoreFamily S b n).filter
      (fun v => v.1 ≤ R) ↔
      (c, r) ∈ initialDeficiencySmoothCoreFamily S b R
  constructor
  · intro hv
    obtain ⟨hbase, hcutoff⟩ := Finset.mem_filter.mp hv
    change (c, r) ∈
      ((Finset.Icc 1 n).product (Finset.range (∏ s ∈ S, s))).filter
        (admissibleSmoothDeficiencyCore S b) at hbase
    obtain ⟨hpair, hadmissible⟩ := Finset.mem_filter.mp hbase
    obtain ⟨hcore, hresidue⟩ := Finset.mem_product.mp hpair
    have hpositive := (Finset.mem_Icc.mp hcore).1
    change (c, r) ∈
      ((Finset.Icc 1 R).product (Finset.range (∏ s ∈ S, s))).filter
        (admissibleSmoothDeficiencyCore S b)
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hpositive, hcutoff⟩, hresidue⟩,
        hadmissible⟩
  · intro hv
    change (c, r) ∈
      ((Finset.Icc 1 R).product (Finset.range (∏ s ∈ S, s))).filter
        (admissibleSmoothDeficiencyCore S b) at hv
    obtain ⟨hpair, hadmissible⟩ := Finset.mem_filter.mp hv
    obtain ⟨hcore, hresidue⟩ := Finset.mem_product.mp hpair
    obtain ⟨hpositive, hcutoff⟩ := Finset.mem_Icc.mp hcore
    apply Finset.mem_filter.mpr
    constructor
    · change (c, r) ∈
        ((Finset.Icc 1 n).product (Finset.range (∏ s ∈ S, s))).filter
          (admissibleSmoothDeficiencyCore S b)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨hpositive, hcutoff.trans hRn⟩, hresidue⟩,
            hadmissible⟩
    · exact hcutoff

/-- Exact three-way partition of the actual prime-progression main count. -/
theorem initialDeficiencyMainPrimeStratumCount_eq_small_add_middle_add_large
    (S : Finset ℕ) (b : ℕ → ℕ) (n R : ℕ) :
    initialDeficiencyMainPrimeStratumCount S b n =
      (∑ v ∈ initialDeficiencySmallCoreFamily S b n R,
        (smoothDeficiencyPrimeStratum S v.1 v.2 n).card) +
      (∑ v ∈ initialDeficiencyMiddleCoreFamily S b n R,
        (smoothDeficiencyPrimeStratum S v.1 v.2 n).card) +
      (∑ v ∈ initialDeficiencyLargeCoreFamily S b n R,
        (smoothDeficiencyPrimeStratum S v.1 v.2 n).card) := by
  classical
  let F := initialDeficiencySmoothCoreFamily S b n
  let f : ℕ × ℕ → ℕ :=
    fun v => (smoothDeficiencyPrimeStratum S v.1 v.2 n).card
  have hfirst := Finset.sum_filter_add_sum_filter_not
    F (fun v : ℕ × ℕ => v.1 ≤ R) f
  have hsecond := Finset.sum_filter_add_sum_filter_not
    (F.filter fun v : ℕ × ℕ => ¬ v.1 ≤ R)
    (fun v : ℕ × ℕ => (v.1 : ℝ) < Real.sqrt (n : ℝ)) f
  have hsmall :
      F.filter (fun v : ℕ × ℕ => v.1 ≤ R) =
        initialDeficiencySmallCoreFamily S b n R := rfl
  have hmiddle :
      (F.filter fun v : ℕ × ℕ => ¬ v.1 ≤ R).filter
        (fun v : ℕ × ℕ => (v.1 : ℝ) < Real.sqrt (n : ℝ)) =
        initialDeficiencyMiddleCoreFamily S b n R := by
    ext v
    simp [initialDeficiencyMiddleCoreFamily, F, and_assoc]
  have hlarge :
      (F.filter fun v : ℕ × ℕ => ¬ v.1 ≤ R).filter
        (fun v : ℕ × ℕ => ¬ (v.1 : ℝ) < Real.sqrt (n : ℝ)) =
        initialDeficiencyLargeCoreFamily S b n R := by
    ext v
    simp [initialDeficiencyLargeCoreFamily, F, and_assoc]
  change (∑ v ∈ F, f v) = _
  rw [← hfirst, ← hsecond, hsmall, hmiddle, hlarge]
  simp [f, Nat.add_assoc]

/-- Every fixed small-core truncation has eventual normalized upper bound one,
using the genuine finite-family progression PNT and total admissible mass. -/
theorem initialDeficiencySmallCoreFamily_eventual_normalized_le_one_add
    (S : Finset ℕ) (b : ℕ → ℕ) (R : ℕ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hodd : 2 ∉ S)
    (hb : ∀ s ∈ S, Nat.Coprime (b s) s)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ((∑ v ∈ initialDeficiencySmallCoreFamily S b n R,
        (smoothDeficiencyPrimeStratum S v.1 v.2 n).card) : ℝ) /
          ((n : ℝ) / Real.log n) ≤ 1 + ε := by
  let F := initialDeficiencySmoothCoreFamily S b R
  have hfamily : ∀ v ∈ F, admissibleSmoothDeficiencyCore S b v :=
    fun _ hv => initialDeficiencySmoothCoreFamily_admissible hv
  have hlimit := finiteSmoothDeficiencyFamily_asymptotic
    S b F hsupport hfamily
  have hmass := initialDeficiencySmoothCoreFamily_weight_le_one
    S b R hsupport hodd hb
  have hstrict :
      (∑ v ∈ F,
        (1 / (((∏ s ∈ S, s).totient : ℕ) : ℝ)) *
          ((v.1 : ℝ)⁻¹)) < 1 + ε := by
    change (∑ v ∈ initialDeficiencySmoothCoreFamily S b R,
      (1 / (((∏ s ∈ S, s).totient : ℕ) : ℝ)) *
        ((v.1 : ℝ)⁻¹)) < 1 + ε
    linarith
  have hevent := (tendsto_order.mp hlimit).2 (1 + ε) hstrict
  filter_upwards [hevent, eventually_ge_atTop R] with n hn hRn
  rw [initialDeficiencySmallCoreFamily_eq_fixed S b hRn]
  exact le_of_lt hn

/-- All actual admissible cores above the moving square-root cutoff have zero
normalized prime-progression mass, uniformly in the fixed smaller cutoff. -/
theorem initialDeficiencyLargeCoreFamily_normalized_tendsto_zero
    (S : Finset ℕ) (b : ℕ → ℕ) (R : ℕ) :
    Tendsto
      (fun n : ℕ =>
        ((∑ v ∈ initialDeficiencyLargeCoreFamily S b n R,
          (smoothDeficiencyPrimeStratum S v.1 v.2 n).card) : ℝ) /
            ((n : ℝ) / Real.log n))
      atTop (nhds 0) := by
  apply smoothCorePair_large_prime_sum_normalized_tendsto_zero
    S (insert 2 S)
    (fun n => initialDeficiencyLargeCoreFamily S b n R)
    (∏ s ∈ S, s)
  · intro n v hv
    have hbase := (Finset.mem_filter.mp hv).1
    exact (initialDeficiencySmoothCoreFamily_admissible hbase).2.1
  · intro n v hv
    have hbase := (Finset.mem_filter.mp hv).1
    exact deficiencySmoothCoefficient_mem_factoredNumbers
      (initialDeficiencySmoothCoreFamily_admissible hbase).1
  · intro n v hv
    exact (Finset.mem_filter.mp hv).2.2

/-- The only analytic condition remaining in the complete asymptotic assembly:
uniform vanishing of actual smooth-core prime strata in the middle window.
This statement contains no deficiency, covering, or target-count predicate. -/
def InitialDeficiencyMiddleCoreUniformlyNegligible
    (S : Finset ℕ) (b : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℕ,
    ∀ᶠ n : ℕ in atTop,
      ((∑ v ∈ initialDeficiencyMiddleCoreFamily S b n R,
        (smoothDeficiencyPrimeStratum S v.1 v.2 n).card) : ℝ) /
          ((n : ℝ) / Real.log n) ≤ ε

/-- The actual moving middle-core prime-progression family is uniformly
negligible.  The proof uses only the established uniform Chebyshev estimate,
finite residue multiplicity, and the half-power fixed-support Rankin tail. -/
theorem initialDeficiencyMiddleCoreUniformlyNegligible
    (S : Finset ℕ) (b : ℕ → ℕ) :
    InitialDeficiencyMiddleCoreUniformlyNegligible S b := by
  intro ε hε
  let W : ℕ := ∏ s ∈ S, s
  let E : ℝ :=
    ∏ p ∈ insert 2 S with p.Prime,
      (1 - (p : ℝ) ^ (-(1 - (1 / 2 : ℝ))))⁻¹
  let K : ℝ := (W : ℝ) * (2 * (Real.log 4 + 1)) * E
  have hdecay : Tendsto
      (fun R : ℕ => K * (R : ℝ) ^ (-(1 / 2 : ℝ)))
      atTop (nhds 0) := by
    have hreal := tendsto_rpow_neg_atTop
      (by norm_num : (0 : ℝ) < 1 / 2)
    have hnat := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [Function.comp_def] using hnat.const_mul K
  have hsmall := (tendsto_order.mp hdecay).2 ε hε
  have hboth :
      ∀ᶠ R : ℕ in atTop,
        0 < R ∧ K * (R : ℝ) ^ (-(1 / 2 : ℝ)) < ε :=
    (eventually_gt_atTop 0).and hsmall
  obtain ⟨R, hRpos, hRsmall⟩ := hboth.exists
  refine ⟨R, ?_⟩
  have hRreal : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hRpos
  let G : ℕ → Finset (ℕ × ℕ) :=
    fun n => initialDeficiencyMiddleCoreFamily S b n R
  have hresidue : ∀ n v, v ∈ G n → v.2 < W := by
    intro n v hv
    have hbase := (Finset.mem_filter.mp hv).1
    exact (initialDeficiencySmoothCoreFamily_admissible hbase).2.1
  have hsmooth : ∀ n v, v ∈ G n →
      v.1 ∈ Nat.factoredNumbers (insert 2 S) := by
    intro n v hv
    have hbase := (Finset.mem_filter.mp hv).1
    exact deficiencySmoothCoefficient_mem_factoredNumbers
      (initialDeficiencySmoothCoreFamily_admissible hbase).1
  have hlarge : ∀ n v, v ∈ G n → (R : ℝ) ≤ (v.1 : ℝ) := by
    intro n v hv
    exact_mod_cast (Nat.le_of_lt (Finset.mem_filter.mp hv).2.1)
  have hupper : ∀ n v, v ∈ G n →
      (v.1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    intro n v hv
    exact le_of_lt (Finset.mem_filter.mp hv).2.2
  have hbound := smoothCorePair_middle_prime_sum_eventually_le
    S (insert 2 S) G W hRreal hresidue hsmooth hlarge hupper
  filter_upwards [hbound] with n hn
  calc
    ((∑ v ∈ initialDeficiencyMiddleCoreFamily S b n R,
        (smoothDeficiencyPrimeStratum S v.1 v.2 n).card) : ℝ) /
          ((n : ℝ) / Real.log n) ≤
      (W : ℝ) * (2 * (Real.log 4 + 1)) *
        (R : ℝ) ^ (-(1 / 2 : ℝ)) * E := hn
    _ = K * (R : ℝ) ^ (-(1 / 2 : ℝ)) := by
      dsimp [K]
      ring
    _ ≤ ε := le_of_lt hRsmall

/-- Under precisely the explicit middle-core estimate, the full actual
prime-progression main term has eventual normalized upper bound one. -/
theorem initialDeficiencyMainPrimeStratum_eventual_normalized_le_one_add
    (S : Finset ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hodd : 2 ∉ S)
    (hb : ∀ s ∈ S, Nat.Coprime (b s) s)
    (hmiddle : InitialDeficiencyMiddleCoreUniformlyNegligible S b)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (initialDeficiencyMainPrimeStratumCount S b n : ℝ) /
        ((n : ℝ) / Real.log n) ≤ 1 + ε := by
  obtain ⟨R, hmid⟩ := hmiddle (ε / 3) (by linarith)
  have hsmall := initialDeficiencySmallCoreFamily_eventual_normalized_le_one_add
    S b R hsupport hodd hb (by linarith : 0 < ε / 3)
  have hlarge_limit := initialDeficiencyLargeCoreFamily_normalized_tendsto_zero
    S b R
  have hlarge := (tendsto_order.mp hlarge_limit).2
    (ε / 3) (by linarith : (0 : ℝ) < ε / 3)
  filter_upwards [hsmall, hmid, hlarge] with n hs hm hl
  rw [initialDeficiencyMainPrimeStratumCount_eq_small_add_middle_add_large
    S b n R]
  push_cast
  rw [add_div, add_div]
  linarith

/-- Exact full initial-deficiency asymptotic from the sole noncircular,
explicit moving-middle-core prime-progression estimate. -/
theorem initial_deficiency_asymptotic_of_middleCoreUniformlyNegligible
    (S : Finset ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hodd : 2 ∉ S)
    (hb : ∀ s ∈ S, Nat.Coprime (b s) s)
    (hmiddle : InitialDeficiencyMiddleCoreUniformlyNegligible S b) :
    Tendsto
      (fun n : ℕ =>
        (deficiency n (initialAssignment S b) : ℝ) /
          ((n : ℝ) / Real.log n))
      atTop (nhds 1) := by
  apply tendsto_order.2
  constructor
  · intro x hx
    have hε : 0 < (1 - x) / 2 := by linarith
    have hlower := initial_deficiency_eventual_one_lower
      S b hsupport hodd hb ((1 - x) / 2) hε
    filter_upwards [hlower] with n hn
    linarith
  · intro x hx
    have hε : 0 < (x - 1) / 3 := by linarith
    have hmain := initialDeficiencyMainPrimeStratum_eventual_normalized_le_one_add
      S b hsupport hodd hb hmiddle hε
    have hfree := (tendsto_order.mp
      (initialDeficiencyExternalFreeWeight_normalized_tendsto_zero S b)).2
        ((x - 1) / 3) hε
    have hpower := (tendsto_order.mp
      (initialDeficiencyPrimePowerTargets_normalized_tendsto_zero S b)).2
        ((x - 1) / 3) hε
    filter_upwards [hmain, hfree, hpower,
      eventually_ge_atTop (S.sup id), eventually_ge_atTop 2]
      with n hm hf hp hsupport_large hn
    have havailable : ∀ s ∈ S, s.Prime ∧ s ≤ n := by
      intro s hs
      exact ⟨hsupport s hs,
        (Finset.le_sup (f := @id ℕ) hs).trans hsupport_large⟩
    rw [initial_deficiency_eq_externalFreeWeight_add_mainPrimeStratum_add_primePower
      S b havailable hodd hn]
    push_cast
    rw [add_div, add_div]
    linarith

/-- Complete unconditional asymptotic for the *actual* initial deficiency.
The finite support consists of odd primes and every switched residue is a
unit modulo its support prime, exactly as in the prime-congruence covering
construction.  No uniform PNT, prime-pattern hypothesis, deficiency-tail
assumption, or extra mathematical axiom is used. -/
theorem initial_deficiency_asymptotic
    (S : Finset ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hodd : 2 ∉ S)
    (hb : ∀ s ∈ S, Nat.Coprime (b s) s) :
    Tendsto
      (fun n : ℕ =>
        (deficiency n (initialAssignment S b) : ℝ) /
          ((n : ℝ) / Real.log n))
      atTop (nhds 1) :=
  initial_deficiency_asymptotic_of_middleCoreUniformlyNegligible
    S b hsupport hodd hb
    (initialDeficiencyMiddleCoreUniformlyNegligible S b)

/-- The complete actual moving even-smooth-core/reduced-prime-progression
sum has exact leading coefficient one. -/
theorem initialDeficiencyMainPrimeStratum_asymptotic
    (S : Finset ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hodd : 2 ∉ S)
    (hb : ∀ s ∈ S, Nat.Coprime (b s) s) :
    Tendsto
      (fun n : ℕ =>
        (initialDeficiencyMainPrimeStratumCount S b n : ℝ) /
          ((n : ℝ) / Real.log n))
      atTop (nhds 1) :=
  (initial_deficiency_asymptotic_iff_mainPrimeStratum
    S b hsupport hodd).mp
      (initial_deficiency_asymptotic S b hsupport hodd hb)

end Erdos689

#print axioms Erdos689.initialDeficiencySmallCoreFamily_eq_fixed
#print axioms Erdos689.initialDeficiencyMainPrimeStratumCount_eq_small_add_middle_add_large
#print axioms Erdos689.initialDeficiencySmallCoreFamily_eventual_normalized_le_one_add
#print axioms Erdos689.initialDeficiencyLargeCoreFamily_normalized_tendsto_zero
#print axioms Erdos689.initialDeficiencyMiddleCoreUniformlyNegligible
#print axioms Erdos689.initialDeficiencyMainPrimeStratum_eventual_normalized_le_one_add
#print axioms Erdos689.initial_deficiency_asymptotic_of_middleCoreUniformlyNegligible
#print axioms Erdos689.initial_deficiency_asymptotic
#print axioms Erdos689.initialDeficiencyMainPrimeStratum_asymptotic
