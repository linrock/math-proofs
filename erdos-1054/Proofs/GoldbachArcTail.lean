module

public import GoldbachMajorArc
public import GoldbachRatedWindow

@[expose] public section

set_option maxHeartbeats 4000000

namespace GoldbachChain
open MinorArc MajorArcMainTerm Finset
section B1
open MeasureTheory

-- ==== verbatim defs from HarcArcTail.lean ====



noncomputable def arc (Q : ℕ) (pq : ℕ × ℤ) : Set ℝ :=
  Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (Q + 1))) ∩ Set.Ioc (0:ℝ) 1

noncomputable def redRes (q : ℕ) : Finset ℕ := (Finset.range q).filter (fun a => Nat.gcd a q = 1)

noncomputable def PsiIdeal (N P : ℕ) (α : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 P, ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) ^ 2
    * ∑ a ∈ redRes q, (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (a : ℝ) / (q : ℝ)))) ^ 2

noncomputable def PhiArc (N P Q : ℕ) (α : ℝ) : ℂ :=
  ∑ pq ∈ anchors P, (arc Q pq).indicator
    (fun α => ((ArithmeticFunction.moebius pq.1 : ℂ) / (Nat.totient pq.1 : ℂ)) ^ 2
      * (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2) α

-- ==== stubs of banked helpers (HarcArcTail.lean) ====

/-- Integer shift invariance of the kernel character (proven, not stubbed:
    generalizes HarcArcTail's `e_shift_one` to arbitrary integer shifts). -/
lemma e_int_shift (k : ℕ) (β : ℝ) (m : ℤ) :
    e ((k : ℝ) * (β + (m : ℝ))) = e ((k : ℝ) * β) := by
  have h : (k:ℝ) * (β + (m:ℝ)) = (k:ℝ) * β + (((k : ℤ) * m : ℤ) : ℝ) := by
    push_cast
    ring
  rw [h, e, e, Complex.ofReal_add, mul_add, Complex.exp_add]
  have h2 : Complex.exp (2 * Real.pi * Complex.I * ((((k : ℤ) * m : ℤ) : ℝ) : ℂ)) = 1 := by
    rw [show (2 * Real.pi * Complex.I * ((((k : ℤ) * m : ℤ) : ℝ) : ℂ))
        = ((k : ℤ) * m : ℤ) * (2 * Real.pi * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [h2, mul_one]

-- ==== B1: the matched-arc set and the decomposition ====

/-- The anchors matching canonical residue `(q, a₀)`: same modulus, congruent numerator. -/
noncomputable def matchedAnchors (P q a₀ : ℕ) : Finset (ℕ × ℤ) :=
  (anchors P).filter (fun pq => pq.1 = q ∧ (pq.2 : ℤ) % (q : ℤ) = (a₀ : ℤ))

/-- The tail domain of `(q, a₀)`: the period minus its matched arcs. -/
noncomputable def tailSet (P Q q a₀ : ℕ) : Set ℝ :=
  Set.Ioc (0:ℝ) 1 \ ⋃ pq ∈ matchedAnchors P q a₀, arc Q pq


/-- Disjoint indicator collapse: for a finset of pairwise-disjoint sets, the sum of
    indicators of a fixed function is the indicator of the union. -/
lemma sum_indicator_disjoint {ι : Type*} (s : Finset ι) (t : ι → Set ℝ) (g : ℝ → ℂ)
    (hdis : (s : Set ι).Pairwise (Function.onFun Disjoint t)) (α : ℝ) :
    ∑ i ∈ s, (t i).indicator g α = (⋃ i ∈ s, t i).indicator g α := by
  by_cases hmem : α ∈ ⋃ i ∈ s, t i
  · obtain ⟨i, hi, hαi⟩ := Set.mem_iUnion₂.mp hmem
    rw [Set.indicator_of_mem hmem]
    rw [Finset.sum_eq_single i]
    · rw [Set.indicator_of_mem hαi]
    · intro j hj hji
      apply Set.indicator_of_notMem
      intro hαj
      exact (Set.disjoint_left.mp (hdis hj hi hji)) hαj hαi
    · intro hni
      exact absurd hi hni
  · rw [Set.indicator_of_notMem hmem]
    apply Finset.sum_eq_zero
    intro i hi
    apply Set.indicator_of_notMem
    intro hαi
    exact hmem (Set.mem_iUnion₂.mpr ⟨i, hi, hαi⟩)

/-- Same-class arcs are pairwise disjoint (centers >= 1 apart, radii sum < 1). -/
lemma matched_arcs_disjoint (P Q q a₀ : ℕ) (hq : 1 ≤ q) (hQ : 2 ≤ Q) :
    ((matchedAnchors P q a₀ : Finset (ℕ × ℤ)) : Set (ℕ × ℤ)).Pairwise
      (Function.onFun Disjoint (arc Q)) := by
  intro pq hpq pq' hpq' hne
  simp only [matchedAnchors, Finset.coe_filter, Set.mem_setOf_eq] at hpq hpq'
  obtain ⟨_, hq1, hm1⟩ := hpq
  obtain ⟨_, hq1', hm1'⟩ := hpq'
  have hqq : pq.1 = pq'.1 := by rw [hq1, hq1']
  have hane : pq.2 ≠ pq'.2 := fun h => hne (Prod.ext hqq h)
  have hcong : (pq.2 - pq'.2) % (q : ℤ) = 0 := by
    rw [Int.sub_emod, hm1, hm1', sub_self, Int.zero_emod]
  have hdvd : (q : ℤ) ∣ (pq.2 - pq'.2) := Int.dvd_of_emod_eq_zero hcong
  have hne0 : pq.2 - pq'.2 ≠ 0 := sub_ne_zero.mpr hane
  have hdiff : (q : ℤ) ≤ |pq.2 - pq'.2| :=
    Int.le_of_dvd (abs_pos.mpr hne0) ((dvd_abs _ _).mpr hdvd)
  have hq0R : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hQ1R : (0:ℝ) < (Q:ℝ) + 1 := by positivity
  -- center distance >= 1
  have hcdist : (1:ℝ) ≤ |((pq.2 : ℝ) / (pq.1 : ℕ)) - ((pq'.2 : ℝ) / (pq'.1 : ℕ))| := by
    rw [hq1, hq1']
    have h1 : ((pq.2 : ℝ) / (q : ℝ)) - ((pq'.2 : ℝ) / (q : ℝ))
        = ((pq.2 - pq'.2 : ℤ) : ℝ) / (q : ℝ) := by
      push_cast
      ring
    rw [h1, abs_div, abs_of_pos hq0R, le_div_iff₀ hq0R, one_mul]
    calc (q:ℝ) ≤ ((|pq.2 - pq'.2| : ℤ) : ℝ) := by exact_mod_cast hdiff
      _ = |((pq.2 - pq'.2 : ℤ) : ℝ)| := by rw [Int.cast_abs]
  -- radii sum < 1
  have hrad : 1 / ((pq.1:ℝ) * (Q + 1)) + 1 / ((pq'.1:ℝ) * (Q + 1)) < 1 := by
    rw [hq1, hq1']
    have h3 : (3:ℝ) ≤ (q:ℝ) * ((Q:ℝ) + 1) := by
      have hq1R : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
      have hQ2R : (2:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ
      nlinarith
    have h2 : 1 / ((q:ℝ) * ((Q:ℝ) + 1)) ≤ 1 / 3 :=
      one_div_le_one_div_of_le (by norm_num) h3
    have h5 : (0:ℝ) < (q:ℝ) * ((Q:ℝ) + 1) := by positivity
    push_cast
    linarith
  -- disjoint closed balls => disjoint arcs
  apply Set.disjoint_of_subset Set.inter_subset_left Set.inter_subset_left
  apply Metric.closedBall_disjoint_closedBall
  rw [Real.dist_eq]
  linarith [hcdist, hrad]

/-- **harc brick B1 (skeleton): the Ψ−Φ tail decomposition.** On the period, the ideal-minus-arc
    difference is the sum of tail-restricted full kernels over canonical residues. -/
lemma psi_sub_phi_eq (N P Q : ℕ) (hP : 1 ≤ P) (hPQ : 2 * P ^ 2 < Q + 1)
    (α : ℝ) (hα : α ∈ Set.Ioc (0:ℝ) 1) :
    PsiIdeal N P α - PhiArc N P Q α
      = ∑ q ∈ Finset.Icc 1 P, ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) ^ 2
          * ∑ a₀ ∈ redRes q,
            (tailSet P Q q a₀).indicator
              (fun β => (∑ k ∈ Finset.range N, e ((k : ℝ) * (β - (a₀ : ℝ) / (q : ℝ)))) ^ 2) α := by
  classical
  -- Step 1: within a residue fiber, every anchor's kernel equals the canonical one (everywhere)
  have hker : ∀ pq ∈ anchors P,
      (fun β => (∑ k ∈ Finset.range N, e ((k:ℝ) * (β - (pq.2:ℝ) / (pq.1:ℕ)))) ^ 2)
      = (fun β => (∑ k ∈ Finset.range N,
          e ((k:ℝ) * (β - (((pq.2 % (pq.1:ℤ)).toNat : ℕ):ℝ) / ((pq.1:ℕ):ℝ)))) ^ 2) := by
    intro pq hpq
    have hq0 : 0 < pq.1 := by
      simp only [anchors, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hpq
      omega
    have hq0Z : (0:ℤ) < (pq.1:ℤ) := by exact_mod_cast hq0
    have hq0R : ((pq.1:ℕ):ℝ) ≠ 0 := by
      exact_mod_cast hq0.ne'
    have hres : ((pq.2 % (pq.1:ℤ)).toNat : ℤ) = pq.2 % (pq.1:ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ hq0Z.ne')
    have hsplitZ : pq.2 = ((pq.2 % (pq.1:ℤ)).toNat : ℤ) + (pq.1:ℤ) * (pq.2 / (pq.1:ℤ)) := by
      rw [hres]
      exact (Int.emod_add_mul_ediv pq.2 (pq.1 : ℤ)).symm
    have hsplit : (pq.2 : ℝ)
        = (((pq.2 % (pq.1:ℤ)).toNat : ℕ) : ℝ) + ((pq.1:ℕ):ℝ) * ((pq.2 / (pq.1:ℤ) : ℤ):ℝ) := by
      exact_mod_cast congrArg (Int.cast : ℤ → ℝ) hsplitZ
    funext β
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    have hdiv : (pq.2:ℝ) / ((pq.1:ℕ):ℝ)
        = (((pq.2 % (pq.1:ℤ)).toNat : ℕ):ℝ) / ((pq.1:ℕ):ℝ) + ((pq.2 / (pq.1:ℤ) : ℤ):ℝ) := by
      rw [hsplit]
      field_simp
    have harg : (k:ℝ) * (β - (pq.2:ℝ) / ((pq.1:ℕ):ℝ))
        = (k:ℝ) * ((β - (((pq.2 % (pq.1:ℤ)).toNat : ℕ):ℝ) / ((pq.1:ℕ):ℝ))
            + ((-(pq.2 / (pq.1:ℤ)) : ℤ):ℝ)) := by
      rw [hdiv]
      push_cast
      ring
    rw [harg, e_int_shift k _ (-(pq.2 / (pq.1:ℤ)))]
  -- Step 2: hypotheses distilled
  have hQ2 : 2 ≤ Q := by nlinarith [hPQ, hP]
  -- the fiber map into (q, canonical residue)
  have hmapsto : ∀ pq ∈ anchors P,
      (⟨pq.1, (pq.2 % (pq.1 : ℤ)).toNat⟩ : (_ : ℕ) × ℕ)
        ∈ (Finset.Icc 1 P).sigma (fun q => redRes q) := by
    intro pq hpq
    have hmem := hpq
    simp only [anchors, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hmem
    obtain ⟨⟨⟨hq1, hqP⟩, -⟩, hgcd⟩ := hmem
    have hq0Z : (0:ℤ) < (pq.1 : ℤ) := by exact_mod_cast hq1
    rw [Finset.mem_sigma]
    dsimp only
    constructor
    · exact Finset.mem_Icc.mpr ⟨hq1, hqP⟩
    · rw [redRes, Finset.mem_filter, Finset.mem_range]
      constructor
      · have h1 : pq.2 % (pq.1 : ℤ) < (pq.1 : ℤ) := Int.emod_lt_of_pos _ hq0Z
        have h2 : (0:ℤ) ≤ pq.2 % (pq.1 : ℤ) := Int.emod_nonneg _ hq0Z.ne'
        omega
      · -- gcd of the residue with q equals gcd of the numerator with q, = 1
        have h3 : Int.gcd (pq.2 % (pq.1 : ℤ)) (pq.1 : ℤ) = Int.gcd pq.2 (pq.1 : ℤ) := by
          have h : pq.2 % (pq.1 : ℤ) = pq.2 + (-(pq.2 / (pq.1 : ℤ))) * (pq.1 : ℤ) := by
            rw [Int.emod_def]
            ring
          rw [h, Int.gcd_add_mul_right_left]
        have h4 : ((pq.2 % (pq.1 : ℤ)).toNat : ℤ) = pq.2 % (pq.1 : ℤ) :=
          Int.toNat_of_nonneg (Int.emod_nonneg _ hq0Z.ne')
        have h5 : Nat.gcd (pq.2 % (pq.1 : ℤ)).toNat pq.1
            = Int.gcd (pq.2 % (pq.1 : ℤ)) (pq.1 : ℤ) := by
          have e1 : (pq.2 % (pq.1 : ℤ)).toNat = (pq.2 % (pq.1 : ℤ)).natAbs := by omega
          have e2 : pq.1 = ((pq.1 : ℤ)).natAbs := by simp
          show Nat.gcd (pq.2 % (pq.1 : ℤ)).toNat pq.1
            = Nat.gcd (pq.2 % (pq.1 : ℤ)).natAbs ((pq.1 : ℤ)).natAbs
          rw [e1, ← e2]
        rw [h5, h3, hgcd]
  -- Step 3: PhiArc regrouped fiberwise, kernels canonicalized, indicators collapsed
  have hphi : PhiArc N P Q α
      = ∑ q ∈ Finset.Icc 1 P, ∑ a₀ ∈ redRes q,
          ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) ^ 2
            * (⋃ pq ∈ matchedAnchors P q a₀, arc Q pq).indicator
                (fun β => (∑ k ∈ Finset.range N, e ((k : ℝ) * (β - (a₀ : ℝ) / (q : ℝ)))) ^ 2) α := by
    rw [PhiArc, ← Finset.sum_fiberwise_of_maps_to
      (g := fun pq : ℕ × ℤ => (⟨pq.1, (pq.2 % (pq.1 : ℤ)).toNat⟩ : (_ : ℕ) × ℕ)) hmapsto,
      Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro a₀ ha₀
    -- the fiber over ⟨q, a₀⟩ is matchedAnchors
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have ha₀q : a₀ < q := by
      have := (Finset.mem_filter.mp ha₀).1
      exact Finset.mem_range.mp this
    have hfiber : (anchors P).filter
        (fun pq => (⟨pq.1, (pq.2 % (pq.1 : ℤ)).toNat⟩ : (_ : ℕ) × ℕ) = ⟨q, a₀⟩)
        = matchedAnchors P q a₀ := by
      rw [matchedAnchors]
      apply Finset.filter_congr
      intro pq hpq
      have hq0 : 0 < pq.1 := by
        simp only [anchors, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hpq
        omega
      have hq0Z : (0:ℤ) < (pq.1 : ℤ) := by exact_mod_cast hq0
      constructor
      · intro h
        obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
        have h3 : (pq.2 % (pq.1 : ℤ)).toNat = a₀ := eq_of_heq h2
        have h4 : ((pq.2 % (pq.1 : ℤ)).toNat : ℤ) = pq.2 % (pq.1 : ℤ) :=
          Int.toNat_of_nonneg (Int.emod_nonneg _ hq0Z.ne')
        rw [h1] at h3 h4
        exact ⟨h1, by omega⟩
      · rintro ⟨h1, h2⟩
        subst h1
        have h4 : (pq.2 % (pq.1 : ℤ)).toNat = a₀ := by
          have h5 : (0:ℤ) ≤ pq.2 % (pq.1 : ℤ) := Int.emod_nonneg _ hq0Z.ne'
          omega
        show (⟨pq.1, (pq.2 % (pq.1 : ℤ)).toNat⟩ : (_ : ℕ) × ℕ) = ⟨pq.1, a₀⟩
        rw [h4]
    rw [hfiber]
    -- canonicalize kernels + collapse indicators over the disjoint matched arcs
    have hterm : ∀ pq ∈ matchedAnchors P q a₀,
        (arc Q pq).indicator
          (fun β => ((ArithmeticFunction.moebius pq.1 : ℂ) / (Nat.totient pq.1 : ℂ)) ^ 2
            * (∑ k ∈ Finset.range N, e ((k : ℝ) * (β - (pq.2 : ℝ) / (pq.1 : ℕ)))) ^ 2) α
        = (arc Q pq).indicator
            (fun β => ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) ^ 2
              * (∑ k ∈ Finset.range N, e ((k : ℝ) * (β - (a₀ : ℝ) / (q : ℝ)))) ^ 2) α := by
      intro pq hpq
      obtain ⟨hpqA, hpq1, hpq2⟩ := Finset.mem_filter.mp hpq
      have hq0Z : (0:ℤ) < (q : ℤ) := by exact_mod_cast hq1
      have ha₀' : (pq.2 % (pq.1 : ℤ)).toNat = a₀ := by
        rw [hpq1]
        omega
      have hkerpq := hker pq hpqA
      rw [ha₀'] at hkerpq
      congr 1
      funext β
      rw [hpq1]
      have := congrFun hkerpq β
      rw [hpq1] at this
      rw [this]
    rw [Finset.sum_congr rfl hterm,
      sum_indicator_disjoint (matchedAnchors P q a₀) (arc Q)
        (fun β => ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) ^ 2
          * (∑ k ∈ Finset.range N, e ((k : ℝ) * (β - (a₀ : ℝ) / (q : ℝ)))) ^ 2)
        (matched_arcs_disjoint P Q q a₀ hq1 hQ2) α,
      Set.indicator_const_mul]
  -- Step 4: subtract and convert 1 − 1_⋃ into the tail indicator, pointwise at α ∈ Ioc
  rw [hphi, PsiIdeal, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a₀ ha₀
  rw [← mul_sub]
  congr 1
  -- pointwise: D²(α) − 1_⋃(α)·D²(α) = 1_{Ioc∖⋃}(α)·D²(α)
  have hsub : (⋃ pq ∈ matchedAnchors P q a₀, arc Q pq) ⊆ Set.Ioc (0:ℝ) 1 := by
    intro x hx
    obtain ⟨pq, _, hxpq⟩ := Set.mem_iUnion₂.mp hx
    exact hxpq.2
  by_cases hmem : α ∈ ⋃ pq ∈ matchedAnchors P q a₀, arc Q pq
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_notMem (by
      rw [tailSet]
      exact fun h => h.2 hmem)]
    ring
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_mem (by
      rw [tailSet]
      exact ⟨hα, hmem⟩)]
    ring

end B1

section B2
open MeasureTheory


/-- The two in-period integer translates of the canonical fraction are matched anchors. -/
lemma translate_mem_matched (P q a₀ : ℕ) (hqP : q ∈ Finset.Icc 1 P) (ha₀ : a₀ ∈ redRes q)
    (m : ℕ) (hm : m ≤ 1) :
    ((q, (a₀ : ℤ) + m * q) : ℕ × ℤ) ∈ matchedAnchors P q a₀ := by
  obtain ⟨hq1, hqP'⟩ := Finset.mem_Icc.mp hqP
  obtain ⟨ha_rng, ha_gcd⟩ := Finset.mem_filter.mp ha₀
  have ha_lt : a₀ < q := Finset.mem_range.mp ha_rng
  have hq0Z : (0:ℤ) < (q : ℤ) := by exact_mod_cast hq1
  rw [matchedAnchors, Finset.mem_filter]
  refine ⟨?_, rfl, ?_⟩
  · rw [anchors, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨⟨hq1, hqP'⟩, ?_, ?_⟩, ?_⟩
    · -- −P ≤ a₀ + mq
      have : (0:ℤ) ≤ (a₀ : ℤ) + m * q := by positivity
      omega
    · -- a₀ + mq ≤ 2P
      have h1 : (a₀ : ℤ) + m * q ≤ (q - 1) + 1 * q := by
        have : (a₀ : ℤ) ≤ (q : ℤ) - 1 := by exact_mod_cast Nat.le_sub_one_of_lt ha_lt
        have hm' : (m : ℤ) ≤ 1 := by exact_mod_cast hm
        nlinarith [hq0Z]
      have h2 : (q : ℤ) - 1 + 1 * q ≤ 2 * P := by
        have : (q : ℤ) ≤ (P : ℤ) := by exact_mod_cast hqP'
        omega
      omega
    · -- gcd(a₀ + mq, q) = gcd(a₀, q) = 1
      have h3 : Int.gcd ((a₀ : ℤ) + m * q) (q : ℤ) = Int.gcd (a₀ : ℤ) (q : ℤ) := by
        rw [show (a₀ : ℤ) + m * q = (a₀ : ℤ) + (m : ℤ) * (q : ℤ) by push_cast; ring,
          Int.gcd_add_mul_right_left]
      rw [h3]
      exact_mod_cast ha_gcd
  · -- residue: (a₀ + mq) % q = a₀
    have h4 : ((a₀ : ℤ) + (m : ℤ) * (q : ℤ)) % (q : ℤ) = (a₀ : ℤ) % (q : ℤ) := by
      rw [Int.add_mul_emod_self_right]
    have h5 : ((a₀ : ℤ) + m * q) = ((a₀ : ℤ) + (m : ℤ) * (q : ℤ)) := by push_cast; ring
    rw [h5, h4, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast ha_lt)]

/-- **B2a: tail distance** — on the tail set, the kernel argument `x = α − a₀/q` is at
    circle distance `> δ_q = 1/(q(Q+1))` from every integer. -/
lemma tail_dist (P Q q a₀ : ℕ) (hqP : q ∈ Finset.Icc 1 P) (ha₀ : a₀ ∈ redRes q)
    (hQ2 : 2 ≤ Q) (α : ℝ) (hα : α ∈ tailSet P Q q a₀) :
    1 / ((q : ℝ) * ((Q : ℝ) + 1))
      < |(α - (a₀ : ℝ) / (q : ℝ)) - round (α - (a₀ : ℝ) / (q : ℝ))| := by
  obtain ⟨hq1, hqP'⟩ := Finset.mem_Icc.mp hqP
  have ha_lt : a₀ < q := Finset.mem_range.mp (Finset.mem_filter.mp ha₀).1
  have hq0R : (0:ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hQ0R : (0:ℝ) < (Q : ℝ) + 1 := by positivity
  set δ : ℝ := 1 / ((q : ℝ) * ((Q : ℝ) + 1)) with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδq : δ < 1 / (q : ℝ) := by
    rw [hδdef, div_lt_div_iff₀ (by positivity) hq0R]
    have hQ0 : (0:ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 0 < Q)
    nlinarith [mul_pos hq0R hQ0]
  obtain ⟨hαIoc, hαarc⟩ := hα
  set x : ℝ := α - (a₀ : ℝ) / (q : ℝ) with hxdef
  by_contra hcon
  push_neg at hcon
  set m : ℤ := round x with hmdef
  -- x ∈ (−1, 1], so m ∈ {−1, 0, 1} — actually m ∈ {0, 1} since m = −1 forces α < 0
  have hc01 : 0 ≤ (a₀ : ℝ) / (q : ℝ) ∧ (a₀ : ℝ) / (q : ℝ) ≤ 1 - 1 / (q : ℝ) := by
    constructor
    · positivity
    · rw [div_le_iff₀ hq0R]
      have h6 : (a₀ : ℝ) ≤ (q : ℝ) - 1 := by exact_mod_cast Nat.le_sub_one_of_lt ha_lt
      have h7 : (1 - 1 / (q:ℝ)) * (q:ℝ) = (q:ℝ) - 1 := by field_simp
      linarith
  have hxrange : -1 + 1 / (q : ℝ) ≤ x ∧ x ≤ 1 := by
    constructor
    · rw [hxdef]
      have := hαIoc.1
      linarith [hc01.2]
    · rw [hxdef]
      have := hαIoc.2
      linarith [hc01.1]
  have hmge : (0 : ℤ) ≤ m := by
    by_contra hneg
    push_neg at hneg
    have hm1 : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
    have habs := abs_le.mp hcon
    have hx_le : x ≤ (m : ℝ) + δ := by linarith [habs.2]
    linarith [hxrange.1, hδq, hx_le, hm1]
  have hmle : m ≤ 1 := by
    rw [hmdef]
    by_contra hbig
    push_neg at hbig
    have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hbig
    have habs := abs_le.mp hcon
    have : (m : ℝ) - δ ≤ x := by linarith [habs.1]
    have : (2:ℝ) - δ ≤ x := by linarith
    linarith [hxrange.2, hδ0, hδq, (by positivity : (0:ℝ) < 1 / (q:ℝ))]
  -- so α lies in the ball around the matched translate (a₀ + mq)/q — a matched arc
  have hmem : α ∈ arc Q ((q, (a₀ : ℤ) + m.toNat * q)) := by
    constructor
    · rw [Metric.mem_closedBall, Real.dist_eq]
      have hcenter : (((a₀ : ℤ) + m.toNat * q : ℤ) : ℝ) / ((q : ℕ) : ℝ)
          = (a₀ : ℝ) / (q : ℝ) + (m : ℝ) := by
        have hmt : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hmge
        have hmtR : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by exact_mod_cast hmt
        have h1 : (((a₀ : ℤ) + m.toNat * q : ℤ) : ℝ) = (a₀ : ℝ) + (m : ℝ) * (q : ℝ) := by
          push_cast
          rw [hmtR]
        rw [h1]
        field_simp
      rw [hcenter]
      have habs := abs_le.mp hcon
      rw [abs_le]
      constructor
      · have := habs.1
        rw [hxdef] at this
        push_cast
        linarith
      · have := habs.2
        rw [hxdef] at this
        push_cast
        linarith
    · exact hαIoc
  exact hαarc (Set.mem_iUnion₂.mpr
    ⟨(q, (a₀ : ℤ) + m.toNat * q),
     translate_mem_matched P q a₀ hqP ha₀ m.toNat (by omega), hmem⟩)

/-- **harc brick B2 (statement): the per-tail L⁴ bound** with the 3-center constant. -/
lemma tail_L4_bound (N P Q q a₀ : ℕ) (hqP : q ∈ Finset.Icc 1 P) (ha₀ : a₀ ∈ redRes q)
    (hQ2 : 2 ≤ Q) :
    ∫ α in tailSet P Q q a₀,
      ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (a₀ : ℝ) / (q : ℝ)))) ^ 2‖ ^ 2
      ≤ ((q : ℝ) * ((Q : ℝ) + 1)) ^ 3 / 8 := by
  classical
  obtain ⟨hq1, hqP'⟩ := Finset.mem_Icc.mp hqP
  have ha_lt : a₀ < q := Finset.mem_range.mp (Finset.mem_filter.mp ha₀).1
  have hq0R : (0:ℝ) < (q : ℝ) := by exact_mod_cast hq1
  set c : ℝ := (a₀ : ℝ) / (q : ℝ) with hcdef
  set δ : ℝ := 1 / ((q : ℝ) * ((Q : ℝ) + 1)) with hδdef
  have hδ0 : (0:ℝ) < δ := by positivity
  -- the even one-center tail majorant
  set h : ℝ → ℝ := fun u => Set.indicator {u : ℝ | δ < |u|} (fun u => 1 / (16 * u ^ 4)) u
    with hhdef
  have hh_nonneg : ∀ u, 0 ≤ h u := by
    intro u
    rw [hhdef]
    apply Set.indicator_nonneg
    intro v _
    positivity
  -- tail is measurable and inside the period
  have htail_meas : MeasurableSet (tailSet P Q q a₀) := by
    apply MeasurableSet.diff measurableSet_Ioc
    apply MeasurableSet.biUnion (Set.to_countable _)
    intro pq _
    exact (Metric.isClosed_closedBall.measurableSet).inter measurableSet_Ioc
  have htail_sub : tailSet P Q q a₀ ⊆ Set.Ioc (0:ℝ) 1 := fun α hα => hα.1
  -- pointwise domination on the tail by the three shifted majorants
  have hpt : ∀ α ∈ tailSet P Q q a₀,
      ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - c))) ^ 2‖ ^ 2
        ≤ h (α - (c + (-1))) + h (α - (c + 0)) + h (α - (c + 1)) := by
    intro α hα
    have hd := tail_dist P Q q a₀ hqP ha₀ hQ2 α hα
    rw [← hcdef, ← hδdef] at hd
    set x : ℝ := α - c with hxdef
    set m : ℤ := round x with hmdef
    have hsin : Real.sin (Real.pi * x) ≠ 0 := by
      intro hzero
      obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hzero
      have hxn : x = (n : ℝ) := by
        have h2 : Real.pi * (x - (n : ℝ)) = 0 := by ring_nf; linarith [hn]
        rcases mul_eq_zero.mp h2 with h | h
        · exact absurd h Real.pi_ne_zero
        · linarith
      have hzero' : |x - (round x : ℝ)| = 0 := by
        rw [hxn, round_intCast]
        simp
      rw [hzero'] at hd
      linarith [hδ0]
    have hbound := dirichlet_pow4_pt N x hsin
    -- round x ∈ {−1, 0, 1} from x ∈ (−1, 1]
    have hαIoc := htail_sub hα
    have hc0 : 0 ≤ c := by rw [hcdef]; positivity
    have hc1 : c ≤ 1 := by
      rw [hcdef, div_le_one hq0R]
      exact_mod_cast ha_lt.le
    have hx_lb : -1 < x := by rw [hxdef]; linarith [hαIoc.1]
    have hx_ub : x ≤ 1 := by rw [hxdef]; linarith [hαIoc.2, hc0]
    have hm_lb : -1 ≤ m := by
      rw [hmdef, round_eq]
      have : (-1 : ℝ) ≤ x + 1/2 := by linarith
      exact_mod_cast Int.le_floor.mpr (by push_cast; linarith)
    have hm_ub : m ≤ 1 := by
      rw [hmdef, round_eq]
      have : x + 1/2 < 2 := by linarith
      have h2 : ⌊x + 1/2⌋ < 2 := Int.floor_lt.mpr (by push_cast; linarith)
      omega
    -- the m-th majorant equals the Dirichlet bound; the others are ≥ 0
    have hmain : h (x - (m : ℝ)) = 1 / (16 * (x - (m : ℝ)) ^ 4) := by
      rw [hhdef]
      apply Set.indicator_of_mem
      rw [Set.mem_setOf_eq]
      calc δ < |x - round x| := hd
        _ = |x - (m : ℝ)| := by rw [hmdef]
    have habs4 : |x - round x| ^ 4 = (x - (m : ℝ)) ^ 4 := by
      rw [hmdef, ← abs_pow, abs_of_nonneg (by positivity)]
    have hle : ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * x)) ^ 2‖ ^ 2 ≤ h (x - (m : ℝ)) := by
      rw [hmain]
      calc ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * x)) ^ 2‖ ^ 2
          ≤ 1 / (16 * |x - round x| ^ 4) := hbound
        _ = 1 / (16 * (x - (m : ℝ)) ^ 4) := by rw [habs4]
    -- x − m appears among the three shifts α − (c + j), j ∈ {−1,0,1}
    have hxm : x - (m : ℝ) = α - (c + (m : ℝ)) := by rw [hxdef]; ring
    interval_cases m
    · calc ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * x)) ^ 2‖ ^ 2
          ≤ h (x - ((-1 : ℤ) : ℝ)) := hle
        _ = h (α - (c + (-1))) := by rw [hxm]; norm_num
        _ ≤ h (α - (c + (-1))) + h (α - (c + 0)) + h (α - (c + 1)) := by
            have := hh_nonneg (α - (c + 0))
            have := hh_nonneg (α - (c + 1))
            linarith
    · calc ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * x)) ^ 2‖ ^ 2
          ≤ h (x - ((0 : ℤ) : ℝ)) := hle
        _ = h (α - (c + 0)) := by rw [hxm]; norm_num
        _ ≤ h (α - (c + (-1))) + h (α - (c + 0)) + h (α - (c + 1)) := by
            have := hh_nonneg (α - (c + (-1)))
            have := hh_nonneg (α - (c + 1))
            linarith
    · calc ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * x)) ^ 2‖ ^ 2
          ≤ h (x - ((1 : ℤ) : ℝ)) := hle
        _ = h (α - (c + 1)) := by rw [hxm]; norm_num
        _ ≤ h (α - (c + (-1))) + h (α - (c + 0)) + h (α - (c + 1)) := by
            have := hh_nonneg (α - (c + (-1)))
            have := hh_nonneg (α - (c + 0))
            linarith
  -- ==== integral assembly ====
  -- the integrand is continuous, hence integrable on the (measurable, bounded) tail
  have hcont : Continuous (fun α : ℝ =>
      ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - c))) ^ 2‖ ^ 2) := by
    simp only [e]
    fun_prop
  have hint1 : IntegrableOn (fun α : ℝ =>
      ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - c))) ^ 2‖ ^ 2) (tailSet P Q q a₀) :=
    (hcont.integrableOn_Ioc (a := 0) (b := 1)).mono_set htail_sub
  -- h is measurable and globally integrable (two rpow tails)
  have hSeq : {u : ℝ | δ < |u|} = Set.Iio (-δ) ∪ Set.Ioi δ := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
    rw [lt_abs]
    constructor
    · rintro (h | h)
      · right; exact h
      · left; linarith
    · rintro (h | h)
      · right; linarith
      · left; exact h
  have hSmeas : MeasurableSet {u : ℝ | δ < |u|} := by
    rw [hSeq]
    exact measurableSet_Iio.union measurableSet_Ioi
  have hIoi_int : IntegrableOn (fun u : ℝ => 1 / (16 * u ^ 4)) (Set.Ioi δ) := by
    have h1 : IntegrableOn (fun u : ℝ => u ^ (-4 : ℝ)) (Set.Ioi δ) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) hδ0
    have h2 : IntegrableOn (fun u : ℝ => (1/16) * u ^ (-4 : ℝ)) (Set.Ioi δ) := h1.const_mul _
    apply h2.congr_fun _ measurableSet_Ioi
    intro u hu
    have hu0 : (0:ℝ) < u := lt_trans hδ0 hu
    show (1:ℝ)/16 * u ^ (-4 : ℝ) = 1 / (16 * u ^ 4)
    rw [Real.rpow_neg hu0.le, show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  have hIio_int : IntegrableOn (fun u : ℝ => 1 / (16 * u ^ 4)) (Set.Iio (-δ)) := by
    have h1 : IntegrableOn (fun u : ℝ => 1 / (16 * (-u) ^ 4)) (-(Set.Ioi δ)) :=
      hIoi_int.comp_neg
    rw [Set.neg_Ioi] at h1
    apply h1.congr_fun _ measurableSet_Iio
    intro u _
    show (1:ℝ) / (16 * (-u) ^ 4) = 1 / (16 * u ^ 4)
    ring_nf
  have hh_int : Integrable h := by
    rw [hhdef, integrable_indicator_iff hSmeas]
    rw [hSeq, integrableOn_union]
    exact ⟨hIio_int, hIoi_int⟩
  -- each shifted majorant is integrable, with ∫_tail ≤ ∫_ℝ = ∫ h
  have hshift : ∀ s : ℝ, ∫ α in tailSet P Q q a₀, h (α - s) ≤ ∫ u, h u := by
    intro s
    have hInt : Integrable (fun α : ℝ => h (α - s)) := by
      have := hh_int.comp_sub_right s
      exact this
    calc ∫ α in tailSet P Q q a₀, h (α - s)
        ≤ ∫ α, h (α - s) := by
          apply setIntegral_le_integral hInt
          filter_upwards with α using hh_nonneg _
      _ = ∫ u, h u := integral_sub_right_eq_self h s
  have hshift_int : ∀ s : ℝ, IntegrableOn (fun α : ℝ => h (α - s)) (tailSet P Q q a₀) :=
    fun s => (hh_int.comp_sub_right s).integrableOn
  -- the master chain
  have hδcube : (0:ℝ) < δ ^ 3 := by positivity
  have hIval : ∫ u, h u ≤ 1 / (24 * δ ^ 3) := by
    have hdisj : Disjoint (Set.Iio (-δ)) (Set.Ioi δ) := by
      apply Set.disjoint_left.mpr
      intro u hu1 hu2
      rw [Set.mem_Iio] at hu1
      rw [Set.mem_Ioi] at hu2
      linarith
    have hIoi_val : ∫ u in Set.Ioi δ, (1 : ℝ) / (16 * u ^ 4) = 1 / (48 * δ ^ 3) := by
      have hcongr : ∫ u in Set.Ioi δ, (1 : ℝ) / (16 * u ^ 4)
          = ∫ u in Set.Ioi δ, (1/16 : ℝ) * u ^ (-4 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        have hu0 : (0:ℝ) < u := lt_trans hδ0 hu
        show (1:ℝ) / (16 * u ^ 4) = 1/16 * u ^ (-4 : ℝ)
        rw [Real.rpow_neg hu0.le, show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
        field_simp
      rw [hcongr, MeasureTheory.integral_const_mul,
        integral_Ioi_rpow_of_lt (by norm_num : (-4:ℝ) < -1) hδ0]
      have hδ3 : δ ^ ((-4 : ℝ) + 1) = 1 / δ ^ 3 := by
        rw [show (-4 : ℝ) + 1 = -((3:ℕ) : ℝ) by norm_num, Real.rpow_neg hδ0.le,
          Real.rpow_natCast]
        rw [one_div]
      rw [hδ3]
      have hδne : δ ≠ 0 := hδ0.ne'
      field_simp
      try ring
    have hIio_val : ∫ u in Set.Iio (-δ), (1 : ℝ) / (16 * u ^ 4) = 1 / (48 * δ ^ 3) := by
      have hrefl : ∫ u in Set.Iio (-δ), (1 : ℝ) / (16 * u ^ 4)
          = ∫ u in Set.Ioi δ, (1 : ℝ) / (16 * (-u) ^ 4) := by
        rw [show (∫ u in Set.Iio (-δ), (1 : ℝ) / (16 * u ^ 4))
            = ∫ u in Set.Iic (-δ), (1 : ℝ) / (16 * u ^ 4) from
          MeasureTheory.integral_Iic_eq_integral_Iio.symm]
        rw [← integral_comp_neg_Ioi]
      rw [hrefl]
      have hcongr2 : ∫ u in Set.Ioi δ, (1 : ℝ) / (16 * (-u) ^ 4)
          = ∫ u in Set.Ioi δ, (1 : ℝ) / (16 * u ^ 4) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u _
        show (1:ℝ) / (16 * (-u) ^ 4) = 1 / (16 * u ^ 4)
        ring_nf
      rw [hcongr2, hIoi_val]
    calc ∫ u, h u
        = ∫ u in {u : ℝ | δ < |u|}, (1 : ℝ) / (16 * u ^ 4) := by
          rw [hhdef, MeasureTheory.integral_indicator hSmeas]
      _ = ∫ u in Set.Iio (-δ) ∪ Set.Ioi δ, (1 : ℝ) / (16 * u ^ 4) := by
          rw [hSeq]
      _ = (∫ u in Set.Iio (-δ), (1 : ℝ) / (16 * u ^ 4))
          + ∫ u in Set.Ioi δ, (1 : ℝ) / (16 * u ^ 4) := by
          rw [MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hIio_int hIoi_int]
      _ = 1 / (48 * δ ^ 3) + 1 / (48 * δ ^ 3) := by rw [hIio_val, hIoi_val]
      _ ≤ 1 / (24 * δ ^ 3) := by
          apply le_of_eq
          have hδne : δ ≠ 0 := hδ0.ne'
          field_simp
          try ring
  calc ∫ α in tailSet P Q q a₀,
      ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - c))) ^ 2‖ ^ 2
      ≤ ∫ α in tailSet P Q q a₀,
          (h (α - (c + (-1))) + h (α - (c + 0)) + h (α - (c + 1))) := by
        apply setIntegral_mono_on hint1 _ htail_meas hpt
        exact ((hshift_int _).add (hshift_int _)).add (hshift_int _)
    _ = (∫ α in tailSet P Q q a₀, (h (α - (c + (-1))) + h (α - (c + 0))))
        + (∫ α in tailSet P Q q a₀, h (α - (c + 1))) :=
        integral_add ((hshift_int _).add (hshift_int _)) (hshift_int _)
    _ = (∫ α in tailSet P Q q a₀, h (α - (c + (-1))))
        + (∫ α in tailSet P Q q a₀, h (α - (c + 0)))
        + (∫ α in tailSet P Q q a₀, h (α - (c + 1))) := by
        rw [integral_add (hshift_int _) (hshift_int _)]
    _ ≤ (∫ u, h u) + (∫ u, h u) + (∫ u, h u) :=
        add_le_add (add_le_add (hshift _) (hshift _)) (hshift _)
    _ = 3 * ∫ u, h u := by ring
    _ ≤ 3 * (1 / (24 * δ ^ 3)) := by
        apply mul_le_mul_of_nonneg_left hIval (by norm_num)
    _ = 1 / (8 * δ ^ 3) := by ring
    _ = ((q : ℝ) * ((Q : ℝ) + 1)) ^ 3 / 8 := by
        rw [hδdef]
        have hqQ : (0:ℝ) < (q : ℝ) * ((Q : ℝ) + 1) := by positivity
        field_simp
        try ring

end B2

section B3

/-- `q³/φ(q)³ ≤ 8·q^{3/2}` for squarefree `q` (B0 squared-and-cubed, no rpow gymnastics:
    `q³ ≤ 8·q^{3/2}·φ³` ⟸ `(q^{3/2})² = q³ ≤ (4φ²)³ = (8φ³)²`). -/
lemma cube_totient_ratio (q : ℕ) (hq1 : 1 ≤ q) (hsq : Squarefree q) :
    (q : ℝ) ^ 3 / (Nat.totient q : ℝ) ^ 3 ≤ 8 * (q : ℝ) ^ ((3 : ℝ) / 2) := by
  have hq0R : (0:ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hφ1 : 1 ≤ q.totient := Nat.totient_pos.mpr (by omega)
  have hφ0R : (0:ℝ) < (q.totient : ℝ) := by exact_mod_cast hφ1
  have hB0 := sqfree_totient_linear q hsq
  set x : ℝ := (q : ℝ) ^ ((3 : ℝ) / 2) with hxdef
  have hx0 : 0 ≤ x := Real.rpow_nonneg hq0R.le _
  have hxsq : x ^ 2 = (q : ℝ) ^ 3 := by
    rw [hxdef, ← Real.rpow_natCast ((q:ℝ) ^ ((3:ℝ)/2)) 2, ← Real.rpow_mul hq0R.le]
    norm_num
    try rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hy0 : (0:ℝ) ≤ 8 * (q.totient : ℝ) ^ 3 := by positivity
  have hsq_le : x ^ 2 ≤ (8 * (q.totient : ℝ) ^ 3) ^ 2 := by
    rw [hxsq]
    have h1 : (q : ℝ) ^ 3 ≤ (4 * (q.totient : ℝ) ^ 2) ^ 3 := by
      apply pow_le_pow_left₀ hq0R.le hB0
    calc (q : ℝ) ^ 3 ≤ (4 * (q.totient : ℝ) ^ 2) ^ 3 := h1
      _ = (8 * (q.totient : ℝ) ^ 3) ^ 2 := by ring
  have hxle : x ≤ 8 * (q.totient : ℝ) ^ 3 := by
    by_contra hcon
    push_neg at hcon
    have : (8 * (q.totient : ℝ) ^ 3) ^ 2 < x ^ 2 := by
      apply pow_lt_pow_left₀ hcon hy0
      norm_num
    linarith
  rw [div_le_iff₀ (by positivity : (0:ℝ) < (q.totient : ℝ) ^ 3)]
  calc (q : ℝ) ^ 3 = x ^ 2 := hxsq.symm
    _ = x * x := by ring
    _ ≤ x * (8 * (q.totient : ℝ) ^ 3) := by
        apply mul_le_mul_of_nonneg_left hxle hx0
    _ = 8 * x * (q.totient : ℝ) ^ 3 := by ring

/-- **harc brick B3: the diagonal sum** ≤ (Q+1)³·8·P^{5/2}. -/
lemma diagonal_bound (P Q : ℕ) (hP : 1 ≤ P) :
    ∑ q ∈ Finset.Icc 1 P, ∑ _a₀ ∈ redRes q,
      ‖((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) ^ 2‖ ^ 2
        * (((q : ℝ) * ((Q : ℝ) + 1)) ^ 3 / 8)
      ≤ ((Q : ℝ) + 1) ^ 3 * (8 * (P : ℝ) ^ ((5 : ℝ) / 2)) := by
  classical
  have hper : ∀ q ∈ Finset.Icc 1 P,
      (∑ _a₀ ∈ redRes q,
        ‖((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) ^ 2‖ ^ 2
          * (((q : ℝ) * ((Q : ℝ) + 1)) ^ 3 / 8))
      ≤ ((Q : ℝ) + 1) ^ 3 * (q : ℝ) ^ ((3 : ℝ) / 2) := by
    intro q hq
    obtain ⟨hq1, hqP⟩ := Finset.mem_Icc.mp hq
    have hq0R : (0:ℝ) < (q : ℝ) := by exact_mod_cast hq1
    rw [Finset.sum_const, nsmul_eq_mul]
    by_cases hsq : Squarefree q
    · have hφ1 : 1 ≤ q.totient := Nat.totient_pos.mpr (by omega)
      have hφ0R : (0:ℝ) < (q.totient : ℝ) := by exact_mod_cast hφ1
      -- coefficient: ‖(μ/φ)²‖² ≤ 1/φ⁴
      have hμ : ‖((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) ^ 2‖ ^ 2
          ≤ 1 / (q.totient : ℝ) ^ 4 := by
        have h0 : ‖((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) ^ 2‖ ^ 2
            = ‖((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ))‖ ^ 4 := by
          rw [norm_pow]
          ring
        rw [h0, norm_div, Complex.norm_intCast, Complex.norm_natCast]
        have hμ1 : |(ArithmeticFunction.moebius q : ℤ)| ≤ 1 :=
          ArithmeticFunction.abs_moebius_le_one
        have hμ1R : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ 1 := by
          rw [← Int.cast_abs]
          exact_mod_cast hμ1
        have h2 : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| / (q.totient : ℝ)
            ≤ 1 / (q.totient : ℝ) := by
          apply div_le_div_of_nonneg_right hμ1R hφ0R.le
        calc (|((ArithmeticFunction.moebius q : ℤ) : ℝ)| / (q.totient : ℝ)) ^ 4
            ≤ (1 / (q.totient : ℝ)) ^ 4 := by
              apply pow_le_pow_left₀ (by positivity) h2
          _ = 1 / (q.totient : ℝ) ^ 4 := by
              rw [div_pow, one_pow]
      -- count: |redRes q| = φ(q)
      have hcard : ((redRes q).card : ℝ) = (q.totient : ℝ) := by
        have h1 : (redRes q).card = q.totient := by
          rw [redRes, Nat.totient]
          congr 1
          apply Finset.filter_congr
          intro a _
          simp [Nat.Coprime, Nat.gcd_comm]
        rw [h1]
      have hratio := cube_totient_ratio q hq1 hsq
      calc ((redRes q).card : ℝ)
            * (‖((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) ^ 2‖ ^ 2
              * (((q : ℝ) * ((Q : ℝ) + 1)) ^ 3 / 8))
          ≤ (q.totient : ℝ) * ((1 / (q.totient : ℝ) ^ 4) * (((q : ℝ) * ((Q : ℝ) + 1)) ^ 3 / 8)) := by
            rw [hcard]
            apply mul_le_mul_of_nonneg_left _ hφ0R.le
            apply mul_le_mul_of_nonneg_right hμ (by positivity)
        _ = ((Q : ℝ) + 1) ^ 3 * ((q : ℝ) ^ 3 / (q.totient : ℝ) ^ 3) / 8 := by
            field_simp
            try ring
        _ ≤ ((Q : ℝ) + 1) ^ 3 * (8 * (q : ℝ) ^ ((3:ℝ)/2)) / 8 := by
            apply div_le_div_of_nonneg_right _ (by norm_num)
            apply mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = ((Q : ℝ) + 1) ^ 3 * (q : ℝ) ^ ((3:ℝ)/2) := by ring
    · have hμ0 : ArithmeticFunction.moebius q = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
      rw [hμ0]
      simp
      positivity
  calc ∑ q ∈ Finset.Icc 1 P, ∑ _a₀ ∈ redRes q,
        ‖((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) ^ 2‖ ^ 2
          * (((q : ℝ) * ((Q : ℝ) + 1)) ^ 3 / 8)
      ≤ ∑ q ∈ Finset.Icc 1 P, ((Q : ℝ) + 1) ^ 3 * (q : ℝ) ^ ((3 : ℝ) / 2) :=
        Finset.sum_le_sum hper
    _ ≤ ∑ _q ∈ Finset.Icc 1 P, ((Q : ℝ) + 1) ^ 3 * (P : ℝ) ^ ((3 : ℝ) / 2) := by
        apply Finset.sum_le_sum
        intro q hq
        obtain ⟨hq1, hqP⟩ := Finset.mem_Icc.mp hq
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow (by positivity) (by exact_mod_cast hqP) (by norm_num)
    _ ≤ (P : ℝ) * (((Q : ℝ) + 1) ^ 3 * (P : ℝ) ^ ((3 : ℝ) / 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have h1 : P + 1 - 1 = P := by omega
        rw [h1]
    _ ≤ ((Q : ℝ) + 1) ^ 3 * (8 * (P : ℝ) ^ ((5 : ℝ) / 2)) := by
        have hP0 : (0:ℝ) < (P : ℝ) := by exact_mod_cast hP
        have h1 : (P : ℝ) * (P : ℝ) ^ ((3 : ℝ) / 2) = (P : ℝ) ^ ((5 : ℝ) / 2) := by
          nth_rewrite 1 [show (P : ℝ) = (P : ℝ) ^ (1 : ℝ) from (Real.rpow_one _).symm]
          rw [← Real.rpow_add hP0]
          norm_num
        calc (P : ℝ) * (((Q : ℝ) + 1) ^ 3 * (P : ℝ) ^ ((3 : ℝ) / 2))
            = ((Q : ℝ) + 1) ^ 3 * ((P : ℝ) * (P : ℝ) ^ ((3 : ℝ) / 2)) := by ring
          _ = ((Q : ℝ) + 1) ^ 3 * (P : ℝ) ^ ((5 : ℝ) / 2) := by rw [h1]
          _ ≤ ((Q : ℝ) + 1) ^ 3 * (8 * (P : ℝ) ^ ((5 : ℝ) / 2)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              nlinarith [Real.rpow_nonneg hP0.le ((5:ℝ)/2)]

end B3

section B4
open MeasureTheory

/-- **B4a: Farey separation for distinct canonical fractions** — distinct reduced fractions
    `a₀/q ≠ a₀'/q'` are at distance `≥ 1/(qq')` (integer numerator `|a₀q' − a₀'q| ≥ 1`). -/
lemma redRes_sep (q q' a₀ a₀' : ℕ) (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hne : (a₀ : ℝ) / (q : ℝ) ≠ (a₀' : ℝ) / (q' : ℝ)) :
    1 / ((q : ℝ) * (q' : ℝ)) ≤ |(a₀ : ℝ) / (q : ℝ) - (a₀' : ℝ) / (q' : ℝ)| := by
  have hq0 : (0:ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq'0 : (0:ℝ) < (q' : ℝ) := by exact_mod_cast hq'
  have hval : (a₀ : ℝ) / (q : ℝ) - (a₀' : ℝ) / (q' : ℝ)
      = (((a₀ : ℤ) * q' - (a₀' : ℤ) * q : ℤ) : ℝ) / ((q : ℝ) * (q' : ℝ)) := by
    push_cast
    field_simp
  have hnum : (a₀ : ℤ) * q' - (a₀' : ℤ) * q ≠ 0 := by
    intro h0
    apply hne
    rw [div_eq_div_iff hq0.ne' hq'0.ne']
    have h1 : (a₀ : ℤ) * q' = (a₀' : ℤ) * q := by omega
    exact_mod_cast h1
  rw [hval, abs_div, abs_of_pos (by positivity : (0:ℝ) < (q : ℝ) * (q' : ℝ))]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h1 : (1 : ℤ) ≤ |(a₀ : ℤ) * q' - (a₀' : ℤ) * q| := Int.one_le_abs hnum
  calc (1:ℝ) = ((1:ℤ) : ℝ) := by norm_num
    _ ≤ ((|(a₀ : ℤ) * q' - (a₀' : ℤ) * q| : ℤ) : ℝ) := by exact_mod_cast h1
    _ = |(((a₀ : ℤ) * q' - (a₀' : ℤ) * q : ℤ) : ℝ)| := by rw [Int.cast_abs]

/-- **B4a′: circle separation** — distinct canonical fractions in `[0,1)` separate by
    `≥ 1/(qq')` from every integer translate `m ∈ {−1,0,1}` of each other (the same
    integer-numerator argument per translate). -/
lemma redRes_sep_circle (q q' a₀ a₀' : ℕ) (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (ha : a₀ < q) (ha' : a₀' < q')
    (hne : (a₀ : ℝ) / (q : ℝ) ≠ (a₀' : ℝ) / (q' : ℝ)) (m : ℤ) (hm : m.natAbs ≤ 1) :
    1 / ((q : ℝ) * (q' : ℝ)) ≤ |(a₀ : ℝ) / (q : ℝ) - (a₀' : ℝ) / (q' : ℝ) - (m : ℝ)| := by
  have hq0 : (0:ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq'0 : (0:ℝ) < (q' : ℝ) := by exact_mod_cast hq'
  have hval : (a₀ : ℝ) / (q : ℝ) - (a₀' : ℝ) / (q' : ℝ) - (m : ℝ)
      = (((a₀ : ℤ) * q' - (a₀' : ℤ) * q - m * (q * q') : ℤ) : ℝ) / ((q : ℝ) * (q' : ℝ)) := by
    push_cast
    field_simp
  have hnum : (a₀ : ℤ) * q' - (a₀' : ℤ) * q - m * (q * q') ≠ 0 := by
    intro h0
    have hm1 : -1 ≤ m := by omega
    have hm2 : m ≤ 1 := by omega
    interval_cases m
    · -- m = −1: a₀q' − a₀'q = −qq' → a₀/q − a₀'/q' = −1, impossible since both ∈ [0,1)
      have h1 : (a₀ : ℤ) * q' + q * q' = (a₀' : ℤ) * q := by omega
      have h2 : (a₀' : ℤ) * q < q * q' := by
        have : (a₀' : ℤ) < q' := by exact_mod_cast ha'
        have hqZ : (0:ℤ) < (q:ℤ) := by exact_mod_cast hq
        nlinarith
      have h3 : (0:ℤ) ≤ (a₀ : ℤ) * q' := by positivity
      omega
    · -- m = 0: the plain separation numerator
      apply absurd _ hne
      rw [div_eq_div_iff hq0.ne' hq'0.ne']
      have h1 : (a₀ : ℤ) * q' = (a₀' : ℤ) * q := by omega
      exact_mod_cast h1
    · -- m = 1: symmetric to m = −1
      have h1 : (a₀ : ℤ) * q' = (a₀' : ℤ) * q + q * q' := by omega
      have h2 : (a₀ : ℤ) * q' < q * q' := by
        have : (a₀ : ℤ) < q := by exact_mod_cast ha
        have hq'Z : (0:ℤ) < (q':ℤ) := by exact_mod_cast hq'
        nlinarith
      have h3 : (0:ℤ) ≤ (a₀' : ℤ) * q := by positivity
      omega
  rw [hval, abs_div, abs_of_pos (by positivity : (0:ℝ) < (q : ℝ) * (q' : ℝ))]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h1 : (1 : ℤ) ≤ |(a₀ : ℤ) * q' - (a₀' : ℤ) * q - m * (q * q')| := Int.one_le_abs hnum
  calc (1:ℝ) = ((1:ℤ) : ℝ) := by norm_num
    _ ≤ ((|(a₀ : ℤ) * q' - (a₀' : ℤ) * q - m * (q * q')| : ℤ) : ℝ) := by exact_mod_cast h1
    _ = |(((a₀ : ℤ) * q' - (a₀' : ℤ) * q - m * (q * q') : ℤ) : ℝ)| := by rw [Int.cast_abs]


/-- **B4c: the near-kernel L¹ tail integral** — over its own tail, the single kernel
    integrates (in L¹) to `≤ (3/2)·q(Q+1)`: the B2 3-center domination at exponent 2. -/
lemma tail_L1_bound (N P Q q a₀ : ℕ) (hqP : q ∈ Finset.Icc 1 P) (ha₀ : a₀ ∈ redRes q)
    (hQ2 : 2 ≤ Q) :
    ∫ α in tailSet P Q q a₀,
      ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (a₀ : ℝ) / (q : ℝ)))) ^ 2‖
      ≤ (3 / 2) * ((q : ℝ) * ((Q : ℝ) + 1)) := by
  classical
  obtain ⟨hq1, hqP'⟩ := Finset.mem_Icc.mp hqP
  have ha_lt : a₀ < q := Finset.mem_range.mp (Finset.mem_filter.mp ha₀).1
  have hq0R : (0:ℝ) < (q : ℝ) := by exact_mod_cast hq1
  set c : ℝ := (a₀ : ℝ) / (q : ℝ) with hcdef
  set δ : ℝ := 1 / ((q : ℝ) * ((Q : ℝ) + 1)) with hδdef
  have hδ0 : (0:ℝ) < δ := by positivity
  set h : ℝ → ℝ := fun u => Set.indicator {u : ℝ | δ < |u|} (fun u => 1 / (4 * u ^ 2)) u
    with hhdef
  have hh_nonneg : ∀ u, 0 ≤ h u := by
    intro u
    rw [hhdef]
    apply Set.indicator_nonneg
    intro v _
    positivity
  have htail_meas : MeasurableSet (tailSet P Q q a₀) := by
    apply MeasurableSet.diff measurableSet_Ioc
    apply MeasurableSet.biUnion (Set.to_countable _)
    intro pq _
    exact (Metric.isClosed_closedBall.measurableSet).inter measurableSet_Ioc
  have htail_sub : tailSet P Q q a₀ ⊆ Set.Ioc (0:ℝ) 1 := fun α hα => hα.1
  -- pointwise domination by the three shifted majorants (exponent 2)
  have hpt : ∀ α ∈ tailSet P Q q a₀,
      ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - c))) ^ 2‖
        ≤ h (α - (c + (-1))) + h (α - (c + 0)) + h (α - (c + 1)) := by
    intro α hα
    have hd := tail_dist P Q q a₀ hqP ha₀ hQ2 α hα
    rw [← hcdef, ← hδdef] at hd
    set x : ℝ := α - c with hxdef
    set m : ℤ := round x with hmdef
    have hsin : Real.sin (Real.pi * x) ≠ 0 := by
      intro hzero
      obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hzero
      have hxn : x = (n : ℝ) := by
        have h2 : Real.pi * (x - (n : ℝ)) = 0 := by ring_nf; linarith [hn]
        rcases mul_eq_zero.mp h2 with h | h
        · exact absurd h Real.pi_ne_zero
        · linarith
      have hzero' : |x - (round x : ℝ)| = 0 := by
        rw [hxn, round_intCast]
        simp
      rw [hzero'] at hd
      linarith [hδ0]
    have hbound : ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * x)) ^ 2‖
        ≤ 1 / (4 * |x - round x| ^ 2) := by
      rw [norm_pow]
      have hb := exp_sum_bound x hsin N
      calc ‖∑ k ∈ Finset.range N, e ((k : ℝ) * x)‖ ^ 2
          ≤ (1 / (2 * |x - round x|)) ^ 2 := by
            apply pow_le_pow_left₀ (norm_nonneg _) hb
        _ = 1 / (4 * |x - round x| ^ 2) := by
            rw [div_pow, one_pow, mul_pow]
            norm_num
    have hαIoc := htail_sub hα
    have hc0 : 0 ≤ c := by rw [hcdef]; positivity
    have hc1 : c ≤ 1 := by
      rw [hcdef, div_le_one hq0R]
      exact_mod_cast ha_lt.le
    have hx_lb : -1 < x := by rw [hxdef]; linarith [hαIoc.1]
    have hx_ub : x ≤ 1 := by rw [hxdef]; linarith [hαIoc.2, hc0]
    have hm_lb : -1 ≤ m := by
      rw [hmdef, round_eq]
      exact_mod_cast Int.le_floor.mpr (by push_cast; linarith)
    have hm_ub : m ≤ 1 := by
      rw [hmdef, round_eq]
      have h2 : ⌊x + 1/2⌋ < 2 := Int.floor_lt.mpr (by push_cast; linarith)
      omega
    have hmain : h (x - (m : ℝ)) = 1 / (4 * (x - (m : ℝ)) ^ 2) := by
      rw [hhdef]
      apply Set.indicator_of_mem
      rw [Set.mem_setOf_eq]
      calc δ < |x - round x| := hd
        _ = |x - (m : ℝ)| := by rw [hmdef]
    have habs2 : |x - round x| ^ 2 = (x - (m : ℝ)) ^ 2 := by
      rw [hmdef, ← abs_pow, abs_of_nonneg (by positivity)]
    have hle : ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * x)) ^ 2‖ ≤ h (x - (m : ℝ)) := by
      rw [hmain]
      calc ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * x)) ^ 2‖
          ≤ 1 / (4 * |x - round x| ^ 2) := hbound
        _ = 1 / (4 * (x - (m : ℝ)) ^ 2) := by rw [habs2]
    have hxm : x - (m : ℝ) = α - (c + (m : ℝ)) := by rw [hxdef]; ring
    interval_cases m
    · calc ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * x)) ^ 2‖
          ≤ h (x - ((-1 : ℤ) : ℝ)) := hle
        _ = h (α - (c + (-1))) := by rw [hxm]; norm_num
        _ ≤ h (α - (c + (-1))) + h (α - (c + 0)) + h (α - (c + 1)) := by
            have := hh_nonneg (α - (c + 0))
            have := hh_nonneg (α - (c + 1))
            linarith
    · calc ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * x)) ^ 2‖
          ≤ h (x - ((0 : ℤ) : ℝ)) := hle
        _ = h (α - (c + 0)) := by rw [hxm]; norm_num
        _ ≤ h (α - (c + (-1))) + h (α - (c + 0)) + h (α - (c + 1)) := by
            have := hh_nonneg (α - (c + (-1)))
            have := hh_nonneg (α - (c + 1))
            linarith
    · calc ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * x)) ^ 2‖
          ≤ h (x - ((1 : ℤ) : ℝ)) := hle
        _ = h (α - (c + 1)) := by rw [hxm]; norm_num
        _ ≤ h (α - (c + (-1))) + h (α - (c + 0)) + h (α - (c + 1)) := by
            have := hh_nonneg (α - (c + (-1)))
            have := hh_nonneg (α - (c + 0))
            linarith
  -- integral assembly (exponent-2 tails)
  have hcont : Continuous (fun α : ℝ =>
      ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - c))) ^ 2‖) := by
    simp only [e]
    fun_prop
  have hint1 : IntegrableOn (fun α : ℝ =>
      ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - c))) ^ 2‖) (tailSet P Q q a₀) :=
    (hcont.integrableOn_Ioc (a := 0) (b := 1)).mono_set htail_sub
  have hSeq : {u : ℝ | δ < |u|} = Set.Iio (-δ) ∪ Set.Ioi δ := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
    rw [lt_abs]
    constructor
    · rintro (h | h)
      · right; exact h
      · left; linarith
    · rintro (h | h)
      · right; linarith
      · left; exact h
  have hSmeas : MeasurableSet {u : ℝ | δ < |u|} := by
    rw [hSeq]
    exact measurableSet_Iio.union measurableSet_Ioi
  have hIoi_int : IntegrableOn (fun u : ℝ => 1 / (4 * u ^ 2)) (Set.Ioi δ) := by
    have h1 : IntegrableOn (fun u : ℝ => u ^ (-2 : ℝ)) (Set.Ioi δ) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) hδ0
    have h2 : IntegrableOn (fun u : ℝ => (1/4) * u ^ (-2 : ℝ)) (Set.Ioi δ) := h1.const_mul _
    apply h2.congr_fun _ measurableSet_Ioi
    intro u hu
    have hu0 : (0:ℝ) < u := lt_trans hδ0 hu
    show (1:ℝ)/4 * u ^ (-2 : ℝ) = 1 / (4 * u ^ 2)
    rw [Real.rpow_neg hu0.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  have hIio_int : IntegrableOn (fun u : ℝ => 1 / (4 * u ^ 2)) (Set.Iio (-δ)) := by
    have h1 : IntegrableOn (fun u : ℝ => 1 / (4 * (-u) ^ 2)) (-(Set.Ioi δ)) :=
      hIoi_int.comp_neg
    rw [Set.neg_Ioi] at h1
    apply h1.congr_fun _ measurableSet_Iio
    intro u _
    show (1:ℝ) / (4 * (-u) ^ 2) = 1 / (4 * u ^ 2)
    ring_nf
  have hh_int : Integrable h := by
    rw [hhdef, integrable_indicator_iff hSmeas]
    rw [hSeq, integrableOn_union]
    exact ⟨hIio_int, hIoi_int⟩
  have hshift : ∀ s : ℝ, ∫ α in tailSet P Q q a₀, h (α - s) ≤ ∫ u, h u := by
    intro s
    have hInt : Integrable (fun α : ℝ => h (α - s)) := hh_int.comp_sub_right s
    calc ∫ α in tailSet P Q q a₀, h (α - s)
        ≤ ∫ α, h (α - s) := by
          apply setIntegral_le_integral hInt
          filter_upwards with α using hh_nonneg _
      _ = ∫ u, h u := integral_sub_right_eq_self h s
  have hshift_int : ∀ s : ℝ, IntegrableOn (fun α : ℝ => h (α - s)) (tailSet P Q q a₀) :=
    fun s => (hh_int.comp_sub_right s).integrableOn
  have hIval : ∫ u, h u ≤ 1 / (2 * δ) := by
    have hdisj : Disjoint (Set.Iio (-δ)) (Set.Ioi δ) := by
      apply Set.disjoint_left.mpr
      intro u hu1 hu2
      rw [Set.mem_Iio] at hu1
      rw [Set.mem_Ioi] at hu2
      linarith
    have hIoi_val : ∫ u in Set.Ioi δ, (1 : ℝ) / (4 * u ^ 2) = 1 / (4 * δ) := by
      have hcongr : ∫ u in Set.Ioi δ, (1 : ℝ) / (4 * u ^ 2)
          = ∫ u in Set.Ioi δ, (1/4 : ℝ) * u ^ (-2 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        have hu0 : (0:ℝ) < u := lt_trans hδ0 hu
        show (1:ℝ) / (4 * u ^ 2) = 1/4 * u ^ (-2 : ℝ)
        rw [Real.rpow_neg hu0.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
        field_simp
      rw [hcongr, MeasureTheory.integral_const_mul,
        integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hδ0]
      have hδ1 : δ ^ ((-2 : ℝ) + 1) = 1 / δ := by
        rw [show (-2 : ℝ) + 1 = -((1:ℕ) : ℝ) by norm_num, Real.rpow_neg hδ0.le,
          Real.rpow_natCast]
        rw [one_div, pow_one]
      rw [hδ1]
      have hδne : δ ≠ 0 := hδ0.ne'
      norm_num
      field_simp
      try ring
    have hIio_val : ∫ u in Set.Iio (-δ), (1 : ℝ) / (4 * u ^ 2) = 1 / (4 * δ) := by
      have hrefl : ∫ u in Set.Iio (-δ), (1 : ℝ) / (4 * u ^ 2)
          = ∫ u in Set.Ioi δ, (1 : ℝ) / (4 * (-u) ^ 2) := by
        rw [show (∫ u in Set.Iio (-δ), (1 : ℝ) / (4 * u ^ 2))
            = ∫ u in Set.Iic (-δ), (1 : ℝ) / (4 * u ^ 2) from
          MeasureTheory.integral_Iic_eq_integral_Iio.symm]
        rw [← integral_comp_neg_Ioi]
      rw [hrefl]
      have hcongr2 : ∫ u in Set.Ioi δ, (1 : ℝ) / (4 * (-u) ^ 2)
          = ∫ u in Set.Ioi δ, (1 : ℝ) / (4 * u ^ 2) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u _
        show (1:ℝ) / (4 * (-u) ^ 2) = 1 / (4 * u ^ 2)
        ring_nf
      rw [hcongr2, hIoi_val]
    calc ∫ u, h u
        = ∫ u in {u : ℝ | δ < |u|}, (1 : ℝ) / (4 * u ^ 2) := by
          rw [hhdef, MeasureTheory.integral_indicator hSmeas]
      _ = ∫ u in Set.Iio (-δ) ∪ Set.Ioi δ, (1 : ℝ) / (4 * u ^ 2) := by
          rw [hSeq]
      _ = (∫ u in Set.Iio (-δ), (1 : ℝ) / (4 * u ^ 2))
          + ∫ u in Set.Ioi δ, (1 : ℝ) / (4 * u ^ 2) := by
          rw [MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hIio_int hIoi_int]
      _ = 1 / (4 * δ) + 1 / (4 * δ) := by rw [hIio_val, hIoi_val]
      _ ≤ 1 / (2 * δ) := by
          apply le_of_eq
          have hδne : δ ≠ 0 := hδ0.ne'
          field_simp
          try ring
  calc ∫ α in tailSet P Q q a₀,
      ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - c))) ^ 2‖
      ≤ ∫ α in tailSet P Q q a₀,
          (h (α - (c + (-1))) + h (α - (c + 0)) + h (α - (c + 1))) := by
        apply setIntegral_mono_on hint1 _ htail_meas hpt
        exact ((hshift_int _).add (hshift_int _)).add (hshift_int _)
    _ = (∫ α in tailSet P Q q a₀, (h (α - (c + (-1))) + h (α - (c + 0))))
        + (∫ α in tailSet P Q q a₀, h (α - (c + 1))) :=
        integral_add ((hshift_int _).add (hshift_int _)) (hshift_int _)
    _ = (∫ α in tailSet P Q q a₀, h (α - (c + (-1))))
        + (∫ α in tailSet P Q q a₀, h (α - (c + 0)))
        + (∫ α in tailSet P Q q a₀, h (α - (c + 1))) := by
        rw [integral_add (hshift_int _) (hshift_int _)]
    _ ≤ (∫ u, h u) + (∫ u, h u) + (∫ u, h u) :=
        add_le_add (add_le_add (hshift _) (hshift _)) (hshift _)
    _ = 3 * ∫ u, h u := by ring
    _ ≤ 3 * (1 / (2 * δ)) := by
        apply mul_le_mul_of_nonneg_left hIval (by norm_num)
    _ = (3 / 2) * (1 / δ) := by ring
    _ = (3 / 2) * ((q : ℝ) * ((Q : ℝ) + 1)) := by
        rw [hδdef]
        have hqQ : (0:ℝ) < (q : ℝ) * ((Q : ℝ) + 1) := by positivity
        field_simp

/-- **Round minimality**: `|w − round w| ≤ |w − m|` for every integer `m`. -/
lemma abs_sub_round_min (w : ℝ) (m : ℤ) : |w - round w| ≤ |w - (m : ℝ)| := by
  by_cases hm : m = round w
  · rw [hm]
  · have h1 : |w - round w| ≤ 1/2 := abs_sub_round w
    have h2 : (1:ℝ) ≤ |((m : ℝ)) - (round w : ℝ)| := by
      have hne : ((m : ℝ)) - (round w : ℝ) ≠ 0 := by
        intro h0
        apply hm
        have : (m : ℝ) = (round w : ℝ) := by linarith
        exact_mod_cast this
      have h3 : (1 : ℤ) ≤ |m - round w| := Int.one_le_abs (by
        intro h0
        apply hm
        omega)
      calc (1:ℝ) = ((1:ℤ) : ℝ) := by norm_num
        _ ≤ ((|m - round w| : ℤ) : ℝ) := by exact_mod_cast h3
        _ = |((m - round w : ℤ) : ℝ)| := by rw [Int.cast_abs]
        _ = |((m : ℝ)) - (round w : ℝ)| := by push_cast; ring_nf
    have h4 : |((m : ℝ)) - (round w : ℝ)| ≤ |w - (m : ℝ)| + |w - round w| := by
      calc |((m : ℝ)) - (round w : ℝ)| = |(w - (round w : ℝ)) - (w - (m : ℝ))| := by ring_nf
        _ ≤ |w - (round w : ℝ)| + |w - (m : ℝ)| := abs_sub _ _
        _ = |w - (m : ℝ)| + |w - round w| := by ring
    linarith

/-- **Circle-distance triangle inequality**:
    `|y+z − round(y+z)| ≤ |y − round y| + |z − round z|`. -/
lemma circle_dist_triangle (y z : ℝ) :
    |y + z - round (y + z)| ≤ |y - round y| + |z - round z| := by
  calc |y + z - round (y + z)|
      ≤ |y + z - ((round y + round z : ℤ) : ℝ)| := abs_sub_round_min _ _
    _ = |(y - round y) + (z - round z)| := by push_cast; ring_nf
    _ ≤ |y - round y| + |z - round z| := abs_add_le _ _

/-- **harc brick B4b (skeleton): the per-pair cross-term bound.** For distinct canonical
    fractions, the product of tail-restricted kernel norms integrates to
    `≤ (qq')²·(Q+1)·(q+q')` — the midline split: the far kernel is `≤ (qq')²` pointwise
    (separation ≥ 1/(qq'), so the far distance is ≥ 1/(2qq')), the near kernel's tail
    integral is `≤ q(Q+1)` (resp. `q'(Q+1)`). -/
lemma cross_pair_bound (N P Q q q' a₀ a₀' : ℕ)
    (hqP : q ∈ Finset.Icc 1 P) (hq'P : q' ∈ Finset.Icc 1 P)
    (ha₀ : a₀ ∈ redRes q) (ha₀' : a₀' ∈ redRes q') (hQ2 : 2 ≤ Q)
    (hne : (a₀ : ℝ) / (q : ℝ) ≠ (a₀' : ℝ) / (q' : ℝ)) :
    ∫ α in tailSet P Q q a₀ ∩ tailSet P Q q' a₀',
      ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (a₀ : ℝ) / (q : ℝ)))) ^ 2‖
        * ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (a₀' : ℝ) / (q' : ℝ)))) ^ 2‖
      ≤ 6 * ((q : ℝ) * (q' : ℝ)) ^ 2 * (((Q : ℝ) + 1) * ((q : ℝ) + (q' : ℝ))) := by
  classical
  obtain ⟨hq1, hqP'⟩ := Finset.mem_Icc.mp hqP
  obtain ⟨hq'1, hq'P'⟩ := Finset.mem_Icc.mp hq'P
  have ha_lt : a₀ < q := Finset.mem_range.mp (Finset.mem_filter.mp ha₀).1
  have ha'_lt : a₀' < q' := Finset.mem_range.mp (Finset.mem_filter.mp ha₀').1
  have hq0R : (0:ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hq'0R : (0:ℝ) < (q' : ℝ) := by exact_mod_cast hq'1
  set x : ℝ := (a₀ : ℝ) / (q : ℝ) with hxdef
  set x' : ℝ := (a₀' : ℝ) / (q' : ℝ) with hx'def
  set s : ℝ := 1 / ((q : ℝ) * (q' : ℝ)) with hsdef
  have hs0 : (0:ℝ) < s := by positivity
  -- the two fractions lie in [0,1)
  have hx01 : 0 ≤ x ∧ x < 1 := by
    constructor
    · rw [hxdef]; positivity
    · rw [hxdef, div_lt_one hq0R]; exact_mod_cast ha_lt
  have hx'01 : 0 ≤ x' ∧ x' < 1 := by
    constructor
    · rw [hx'def]; positivity
    · rw [hx'def, div_lt_one hq'0R]; exact_mod_cast ha'_lt
  -- circle separation of the two fractions
  have hsep : s ≤ |(x - x') - round (x - x')| := by
    have hd_lb : (-1:ℝ) < x - x' := by linarith [hx01.1, hx'01.2]
    have hd_ub : x - x' < 1 := by linarith [hx01.2, hx'01.1]
    set m : ℤ := round (x - x') with hmdef
    have hm_lb : -1 ≤ m := by
      rw [hmdef, round_eq]
      exact_mod_cast Int.le_floor.mpr (by push_cast; linarith)
    have hm_ub : m ≤ 1 := by
      rw [hmdef, round_eq]
      have h2 : ⌊(x - x') + 1/2⌋ < 2 := Int.floor_lt.mpr (by push_cast; linarith)
      omega
    have := redRes_sep_circle q q' a₀ a₀' hq1 hq'1 ha_lt ha'_lt hne m (by omega)
    rw [hsdef, hxdef, hx'def]
    calc 1 / ((q : ℝ) * (q' : ℝ))
        ≤ |(a₀ : ℝ) / (q : ℝ) - (a₀' : ℝ) / (q' : ℝ) - (m : ℝ)| := this
      _ = |((a₀ : ℝ) / (q : ℝ) - (a₀' : ℝ) / (q' : ℝ)) - (m : ℝ)| := by ring_nf
  -- circle distance is symmetric under negation
  have hdC_neg : ∀ w : ℝ, |(-w) - round (-w)| = |w - round w| := by
    intro w
    apply le_antisymm
    · calc |(-w) - round (-w)| ≤ |(-w) - ((-(round w) : ℤ) : ℝ)| := abs_sub_round_min _ _
        _ = |w - round w| := by push_cast; rw [← abs_neg]; ring_nf
    · calc |w - round w| ≤ |w - ((-(round (-w)) : ℤ) : ℝ)| := abs_sub_round_min _ _
        _ = |(-w) - round (-w)| := by push_cast; rw [← abs_neg]; ring_nf
  -- pointwise either-or on the intersection: f·g ≤ s⁻²·(f + g)
  have hpt : ∀ α ∈ tailSet P Q q a₀ ∩ tailSet P Q q' a₀',
      ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x))) ^ 2‖
        * ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x'))) ^ 2‖
      ≤ (4 / s ^ 2) * (‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x))) ^ 2‖
          + ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x'))) ^ 2‖) := by
    intro α hα
    obtain ⟨hαT, hαT'⟩ := hα
    have hd := tail_dist P Q q a₀ hqP ha₀ hQ2 α hαT
    have hd' := tail_dist P Q q' a₀' hq'P ha₀' hQ2 α hαT'
    rw [← hxdef] at hd
    rw [← hx'def] at hd'
    set d : ℝ := |(α - x) - round (α - x)| with hddef
    set d' : ℝ := |(α - x') - round (α - x')| with hd'def
    have hd0 : 0 < d := lt_of_le_of_lt (by positivity) hd
    have hd'0 : 0 < d' := lt_of_le_of_lt (by positivity) hd'
    -- the kernels are bounded by 1/(4·dist²)
    have hker : ∀ (c : ℝ), 0 < |(α - c) - round (α - c)| →
        ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - c))) ^ 2‖
          ≤ 1 / (4 * |(α - c) - round (α - c)| ^ 2) := by
      intro c hc0
      have hsin : Real.sin (Real.pi * (α - c)) ≠ 0 := by
        intro hzero
        obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hzero
        have hxn : α - c = (n : ℝ) := by
          have h2 : Real.pi * ((α - c) - (n : ℝ)) = 0 := by ring_nf; linarith [hn]
          rcases mul_eq_zero.mp h2 with h | h
          · exact absurd h Real.pi_ne_zero
          · linarith
        rw [hxn, round_intCast] at hc0
        simp at hc0
      rw [norm_pow]
      have hb := exp_sum_bound (α - c) hsin N
      calc ‖∑ k ∈ Finset.range N, e ((k : ℝ) * (α - c))‖ ^ 2
          ≤ (1 / (2 * |(α - c) - round (α - c)|)) ^ 2 := by
            apply pow_le_pow_left₀ (norm_nonneg _) hb
        _ = 1 / (4 * |(α - c) - round (α - c)| ^ 2) := by
            rw [div_pow, one_pow, mul_pow]
            norm_num
    -- the separation forces max(d, d') ≥ s/2
    have hmax : s ≤ d + d' := by
      have htri : |(x - x') - round (x - x')| ≤ d' + d := by
        have h1 := circle_dist_triangle (α - x') (x - α)
        have h2 : (α - x') + (x - α) = x - x' := by ring
        rw [h2] at h1
        have h3 : |(x - α) - round (x - α)| = d := by
          have := hdC_neg (α - x)
          rw [show -(α - x) = x - α by ring] at this
          rw [this, hddef]
        rw [h3, ← hd'def] at h1
        exact h1
      linarith [hsep, htri]
    have hf0 : 0 ≤ ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x))) ^ 2‖ := norm_nonneg _
    have hg0 : 0 ≤ ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x'))) ^ 2‖ := norm_nonneg _
    rcases le_or_gt (s / 2) d' with hfar | hnear
    · -- x' is far: g ≤ 1/(4d'²) ≤ 1/s²
      have hg_bound : ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x'))) ^ 2‖ ≤ 1 / s ^ 2 := by
        calc ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x'))) ^ 2‖
            ≤ 1 / (4 * d' ^ 2) := hker x' hd'0
          _ ≤ 1 / s ^ 2 := by
              apply div_le_div_of_nonneg_left _ _ _
              · norm_num
              · positivity
              · nlinarith [hfar, hs0]
      calc ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x))) ^ 2‖
            * ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x'))) ^ 2‖
          ≤ ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x))) ^ 2‖ * (1 / s ^ 2) := by
            apply mul_le_mul_of_nonneg_left hg_bound hf0
        _ ≤ (4 / s ^ 2) * (‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x))) ^ 2‖
              + ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x'))) ^ 2‖) := by
            have hs2 : (0:ℝ) < s ^ 2 := by positivity
            rw [div_mul_eq_mul_div, mul_comm, ← div_mul_eq_mul_div]
            have h4 : (1:ℝ) / s ^ 2 ≤ 4 / s ^ 2 := by
              apply div_le_div_of_nonneg_right _ hs2.le
              norm_num
            nlinarith [hf0, hg0, hs2]
    · -- x is far: d ≥ s/2 by hmax
      have hdfar : s / 2 ≤ d := by linarith
      have hf_bound : ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x))) ^ 2‖ ≤ 1 / s ^ 2 := by
        calc ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x))) ^ 2‖
            ≤ 1 / (4 * d ^ 2) := hker x hd0
          _ ≤ 1 / s ^ 2 := by
              apply div_le_div_of_nonneg_left _ _ _
              · norm_num
              · positivity
              · nlinarith [hdfar, hs0]
      calc ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x))) ^ 2‖
            * ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x'))) ^ 2‖
          ≤ (1 / s ^ 2) * ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x'))) ^ 2‖ := by
            apply mul_le_mul_of_nonneg_right hf_bound hg0
        _ ≤ (4 / s ^ 2) * (‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x))) ^ 2‖
              + ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x'))) ^ 2‖) := by
            have hs2 : (0:ℝ) < s ^ 2 := by positivity
            have h4 : (1:ℝ) / s ^ 2 ≤ 4 / s ^ 2 := by
              apply div_le_div_of_nonneg_right _ hs2.le
              norm_num
            nlinarith [hf0, hg0, hs2]
  -- integral assembly: monotone + the two one-center L¹ bounds
  have hmeasT : MeasurableSet (tailSet P Q q a₀) := by
    apply MeasurableSet.diff measurableSet_Ioc
    apply MeasurableSet.biUnion (Set.to_countable _)
    intro pq _
    exact (Metric.isClosed_closedBall.measurableSet).inter measurableSet_Ioc
  have hmeasT' : MeasurableSet (tailSet P Q q' a₀') := by
    apply MeasurableSet.diff measurableSet_Ioc
    apply MeasurableSet.biUnion (Set.to_countable _)
    intro pq _
    exact (Metric.isClosed_closedBall.measurableSet).inter measurableSet_Ioc
  have hcontf : Continuous (fun α : ℝ =>
      ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x))) ^ 2‖) := by
    simp only [e]; fun_prop
  have hcontg : Continuous (fun α : ℝ =>
      ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x'))) ^ 2‖) := by
    simp only [e]; fun_prop
  have hsubIoc : tailSet P Q q a₀ ∩ tailSet P Q q' a₀' ⊆ Set.Ioc (0:ℝ) 1 :=
    fun α hα => hα.1.1
  have hintfg : IntegrableOn (fun α : ℝ =>
      ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x))) ^ 2‖
        * ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x'))) ^ 2‖)
      (tailSet P Q q a₀ ∩ tailSet P Q q' a₀') :=
    ((hcontf.mul hcontg).integrableOn_Ioc (a := 0) (b := 1)).mono_set hsubIoc
  have hintf : IntegrableOn (fun α : ℝ =>
      ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x))) ^ 2‖)
      (tailSet P Q q a₀ ∩ tailSet P Q q' a₀') :=
    (hcontf.integrableOn_Ioc (a := 0) (b := 1)).mono_set hsubIoc
  have hintg : IntegrableOn (fun α : ℝ =>
      ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x'))) ^ 2‖)
      (tailSet P Q q a₀ ∩ tailSet P Q q' a₀') :=
    (hcontg.integrableOn_Ioc (a := 0) (b := 1)).mono_set hsubIoc
  have hmeasI : MeasurableSet (tailSet P Q q a₀ ∩ tailSet P Q q' a₀') :=
    hmeasT.inter hmeasT'
  have hfI : ∫ α in tailSet P Q q a₀ ∩ tailSet P Q q' a₀',
      ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x))) ^ 2‖
      ≤ (3 / 2) * ((q : ℝ) * ((Q : ℝ) + 1)) := by
    refine le_trans (setIntegral_mono_set
      ((hcontf.integrableOn_Ioc (a := 0) (b := 1)).mono_set (fun α hα => hα.1))
      ?_ (HasSubset.Subset.eventuallyLE Set.inter_subset_left)) ?_
    · filter_upwards with α using norm_nonneg _
    · rw [hxdef]
      exact tail_L1_bound N P Q q a₀ hqP ha₀ hQ2
  have hgI : ∫ α in tailSet P Q q a₀ ∩ tailSet P Q q' a₀',
      ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x'))) ^ 2‖
      ≤ (3 / 2) * ((q' : ℝ) * ((Q : ℝ) + 1)) := by
    refine le_trans (setIntegral_mono_set
      ((hcontg.integrableOn_Ioc (a := 0) (b := 1)).mono_set (fun α hα => hα.1))
      ?_ (HasSubset.Subset.eventuallyLE Set.inter_subset_right)) ?_
    · filter_upwards with α using norm_nonneg _
    · rw [hx'def]
      exact tail_L1_bound N P Q q' a₀' hq'P ha₀' hQ2
  have hs2inv : 4 / s ^ 2 = 4 * ((q : ℝ) * (q' : ℝ)) ^ 2 := by
    rw [hsdef]
    have h1 : (0:ℝ) < (q : ℝ) * (q' : ℝ) := by positivity
    field_simp
  calc ∫ α in tailSet P Q q a₀ ∩ tailSet P Q q' a₀',
      ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (a₀ : ℝ) / (q : ℝ)))) ^ 2‖
        * ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (a₀' : ℝ) / (q' : ℝ)))) ^ 2‖
      ≤ ∫ α in tailSet P Q q a₀ ∩ tailSet P Q q' a₀',
          (4 / s ^ 2) * (‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x))) ^ 2‖
            + ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x'))) ^ 2‖) := by
        apply setIntegral_mono_on _ _ hmeasI _
        · rw [← hxdef, ← hx'def]
          exact hintfg
        · exact ((hintf.add hintg).const_mul _)
        · intro α hα
          rw [← hxdef, ← hx'def]
          exact hpt α hα
    _ = (4 / s ^ 2) * ((∫ α in tailSet P Q q a₀ ∩ tailSet P Q q' a₀',
          ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x))) ^ 2‖)
        + ∫ α in tailSet P Q q a₀ ∩ tailSet P Q q' a₀',
          ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - x'))) ^ 2‖) := by
        rw [MeasureTheory.integral_const_mul, integral_add hintf hintg]
    _ ≤ (4 / s ^ 2) * ((3 / 2) * ((q : ℝ) * ((Q : ℝ) + 1))
          + (3 / 2) * ((q' : ℝ) * ((Q : ℝ) + 1))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add hfI hgI
    _ = 4 * ((q : ℝ) * (q' : ℝ)) ^ 2 * ((3 / 2) * (((Q : ℝ) + 1) * ((q : ℝ) + (q' : ℝ)))) := by
        rw [hs2inv]
        ring
    _ = 6 * ((q : ℝ) * (q' : ℝ)) ^ 2 * (((Q : ℝ) + 1) * ((q : ℝ) + (q' : ℝ))) := by ring

/-- The flattened anchor index set: canonical residues `(q, a₀)`, `q ≤ P`, `a₀ ∈ redRes q`. -/
noncomputable def canonAnchors (P : ℕ) : Finset ((_ : ℕ) × ℕ) :=
  (Finset.Icc 1 P).sigma (fun q => redRes q)

/-- **harc brick B5a: the pointwise cross-term expansion.** On the period, the squared
    deviation is bounded by the full double sum of coefficient-weighted tail-indicator
    kernel products over pairs of canonical anchors. -/
lemma psi_sub_phi_sq_pointwise (N P Q : ℕ) (hP : 1 ≤ P) (hPQ : 2 * P ^ 2 < Q + 1)
    (α : ℝ) (hα : α ∈ Set.Ioc (0:ℝ) 1) :
    ‖PsiIdeal N P α - PhiArc N P Q α‖ ^ 2
      ≤ ∑ x ∈ canonAnchors P, ∑ y ∈ canonAnchors P,
          ‖((ArithmeticFunction.moebius x.1 : ℂ) / (Nat.totient x.1 : ℂ)) ^ 2‖
            * ‖((ArithmeticFunction.moebius y.1 : ℂ) / (Nat.totient y.1 : ℂ)) ^ 2‖
            * (tailSet P Q x.1 x.2 ∩ tailSet P Q y.1 y.2).indicator
                (fun β =>
                  ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (β - (x.2 : ℝ) / (x.1 : ℝ)))) ^ 2‖
                    * ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (β - (y.2 : ℝ) / (y.1 : ℝ)))) ^ 2‖) α := by
  classical
  rw [psi_sub_phi_eq N P Q hP hPQ α hα]
  -- flatten the double sum to the sigma index
  have hflat : ∑ q ∈ Finset.Icc 1 P,
      ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) ^ 2
        * ∑ a₀ ∈ redRes q,
          (tailSet P Q q a₀).indicator
            (fun β => (∑ k ∈ Finset.range N, e ((k : ℝ) * (β - (a₀ : ℝ) / (q : ℝ)))) ^ 2) α
      = ∑ x ∈ canonAnchors P,
          ((ArithmeticFunction.moebius x.1 : ℂ) / (Nat.totient x.1 : ℂ)) ^ 2
            * (tailSet P Q x.1 x.2).indicator
              (fun β => (∑ k ∈ Finset.range N, e ((k : ℝ) * (β - (x.2 : ℝ) / (x.1 : ℝ)))) ^ 2) α := by
    rw [canonAnchors, Finset.sum_sigma]
    exact Finset.sum_congr rfl (fun q _ => by rw [Finset.mul_sum])
  rw [hflat]
  -- triangle inequality on the norm, then expand the square of the sum
  have htri : ‖∑ x ∈ canonAnchors P,
      ((ArithmeticFunction.moebius x.1 : ℂ) / (Nat.totient x.1 : ℂ)) ^ 2
        * (tailSet P Q x.1 x.2).indicator
          (fun β => (∑ k ∈ Finset.range N, e ((k : ℝ) * (β - (x.2 : ℝ) / (x.1 : ℝ)))) ^ 2) α‖
      ≤ ∑ x ∈ canonAnchors P,
          ‖((ArithmeticFunction.moebius x.1 : ℂ) / (Nat.totient x.1 : ℂ)) ^ 2‖
            * (tailSet P Q x.1 x.2).indicator
              (fun β => ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (β - (x.2 : ℝ) / (x.1 : ℝ)))) ^ 2‖) α := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun x _ => ?_))
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [norm_indicator_eq_indicator_norm]
  have h0 : (0:ℝ) ≤ ∑ x ∈ canonAnchors P,
      ‖((ArithmeticFunction.moebius x.1 : ℂ) / (Nat.totient x.1 : ℂ)) ^ 2‖
        * (tailSet P Q x.1 x.2).indicator
          (fun β => ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (β - (x.2 : ℝ) / (x.1 : ℝ)))) ^ 2‖) α := by
    apply Finset.sum_nonneg
    intro x _
    apply mul_nonneg (norm_nonneg _)
    exact Set.indicator_nonneg (fun β _ => norm_nonneg _) α
  calc ‖∑ x ∈ canonAnchors P,
      ((ArithmeticFunction.moebius x.1 : ℂ) / (Nat.totient x.1 : ℂ)) ^ 2
        * (tailSet P Q x.1 x.2).indicator
          (fun β => (∑ k ∈ Finset.range N, e ((k : ℝ) * (β - (x.2 : ℝ) / (x.1 : ℝ)))) ^ 2) α‖ ^ 2
      ≤ (∑ x ∈ canonAnchors P,
          ‖((ArithmeticFunction.moebius x.1 : ℂ) / (Nat.totient x.1 : ℂ)) ^ 2‖
            * (tailSet P Q x.1 x.2).indicator
              (fun β => ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (β - (x.2 : ℝ) / (x.1 : ℝ)))) ^ 2‖) α) ^ 2 := by
        apply pow_le_pow_left₀ (norm_nonneg _) htri
    _ = ∑ x ∈ canonAnchors P, ∑ y ∈ canonAnchors P,
          (‖((ArithmeticFunction.moebius x.1 : ℂ) / (Nat.totient x.1 : ℂ)) ^ 2‖
            * (tailSet P Q x.1 x.2).indicator
              (fun β => ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (β - (x.2 : ℝ) / (x.1 : ℝ)))) ^ 2‖) α)
          * (‖((ArithmeticFunction.moebius y.1 : ℂ) / (Nat.totient y.1 : ℂ)) ^ 2‖
            * (tailSet P Q y.1 y.2).indicator
              (fun β => ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (β - (y.2 : ℝ) / (y.1 : ℝ)))) ^ 2‖) α) := by
        rw [sq, Finset.sum_mul_sum]
    _ = ∑ x ∈ canonAnchors P, ∑ y ∈ canonAnchors P,
          ‖((ArithmeticFunction.moebius x.1 : ℂ) / (Nat.totient x.1 : ℂ)) ^ 2‖
            * ‖((ArithmeticFunction.moebius y.1 : ℂ) / (Nat.totient y.1 : ℂ)) ^ 2‖
            * (tailSet P Q x.1 x.2 ∩ tailSet P Q y.1 y.2).indicator
                (fun β =>
                  ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (β - (x.2 : ℝ) / (x.1 : ℝ)))) ^ 2‖
                    * ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (β - (y.2 : ℝ) / (y.1 : ℝ)))) ^ 2‖) α := by
        refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
        rw [Set.inter_indicator_mul]
        ring

/-- **harc brick B5b: canonical fractions are injective.** Two reduced canonical residues
    with equal real fractions coincide: `a₀/q = a₀'/q'` with `a₀ ∈ redRes q`, `a₀' ∈ redRes q'`
    forces `q = q'` and `a₀ = a₀'`. -/
lemma canon_fraction_injective (q q' a₀ a₀' : ℕ) (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (ha : a₀ ∈ redRes q) (ha' : a₀' ∈ redRes q')
    (heq : (a₀ : ℝ) / (q : ℝ) = (a₀' : ℝ) / (q' : ℝ)) : q = q' ∧ a₀ = a₀' := by
  have hgcd : Nat.gcd a₀ q = 1 := (Finset.mem_filter.mp ha).2
  have hgcd' : Nat.gcd a₀' q' = 1 := (Finset.mem_filter.mp ha').2
  have hq0R : ((q : ℝ)) ≠ 0 := by positivity
  have hq'0R : ((q' : ℝ)) ≠ 0 := by positivity
  have hcross : a₀ * q' = a₀' * q := by
    have h := (div_eq_div_iff hq0R hq'0R).mp heq
    exact_mod_cast h
  have hdvd : q ∣ q' := by
    have h1 : q ∣ a₀ * q' := by rw [hcross]; exact dvd_mul_left q a₀'
    exact (Nat.coprime_comm.mp hgcd).dvd_of_dvd_mul_left h1
  have hdvd' : q' ∣ q := by
    have h1 : q' ∣ a₀' * q := by rw [← hcross]; exact dvd_mul_left q' a₀
    exact (Nat.coprime_comm.mp hgcd').dvd_of_dvd_mul_left h1
  have hqq : q = q' := Nat.dvd_antisymm hdvd hdvd'
  refine ⟨hqq, ?_⟩
  subst hqq
  exact Nat.eq_of_mul_eq_mul_right (by omega) hcross

lemma continuous_e : Continuous e := by
  unfold e
  fun_prop

lemma kernel_norm_continuous (N : ℕ) (c : ℝ) :
    Continuous fun β : ℝ => ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (β - c))) ^ 2‖ := by
  apply Continuous.norm
  apply Continuous.pow
  apply continuous_finset_sum
  intro k _
  exact continuous_e.comp (by fun_prop)

lemma tailSet_measurable (P Q q a₀ : ℕ) : MeasurableSet (tailSet P Q q a₀) := by
  apply MeasurableSet.diff measurableSet_Ioc
  apply MeasurableSet.biUnion (Set.to_countable _)
  intro pq _
  exact (Metric.isClosed_closedBall.measurableSet).inter measurableSet_Ioc

lemma tailSet_subset_Ioc (P Q q a₀ : ℕ) : tailSet P Q q a₀ ⊆ Set.Ioc (0:ℝ) 1 :=
  Set.diff_subset

/-- **harc brick B5c: the integral expansion.** The period L² of Ψ−Φ splits into the
    coefficient-weighted tail-intersection integrals of kernel-norm products. -/
lemma psi_sub_phi_L2_expand (N P Q : ℕ) (hP : 1 ≤ P) (hPQ : 2 * P ^ 2 < Q + 1) :
    ∫ α in Set.Ioc (0:ℝ) 1, ‖PsiIdeal N P α - PhiArc N P Q α‖ ^ 2
      ≤ ∑ x ∈ canonAnchors P, ∑ y ∈ canonAnchors P,
          ‖((ArithmeticFunction.moebius x.1 : ℂ) / (Nat.totient x.1 : ℂ)) ^ 2‖
            * ‖((ArithmeticFunction.moebius y.1 : ℂ) / (Nat.totient y.1 : ℂ)) ^ 2‖
            * ∫ α in tailSet P Q x.1 x.2 ∩ tailSet P Q y.1 y.2,
                ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (x.2 : ℝ) / (x.1 : ℝ)))) ^ 2‖
                  * ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (y.2 : ℝ) / (y.1 : ℝ)))) ^ 2‖ := by
  classical
  -- the summand functions and their integrability on the period
  set F : (Σ _ : ℕ, ℕ) → (Σ _ : ℕ, ℕ) → ℝ → ℝ := fun x y α =>
    ‖((ArithmeticFunction.moebius x.1 : ℂ) / (Nat.totient x.1 : ℂ)) ^ 2‖
      * ‖((ArithmeticFunction.moebius y.1 : ℂ) / (Nat.totient y.1 : ℂ)) ^ 2‖
      * (tailSet P Q x.1 x.2 ∩ tailSet P Q y.1 y.2).indicator
          (fun β =>
            ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (β - (x.2 : ℝ) / (x.1 : ℝ)))) ^ 2‖
              * ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (β - (y.2 : ℝ) / (y.1 : ℝ)))) ^ 2‖) α
    with hFdef
  have hmeasI : ∀ x y : (Σ _ : ℕ, ℕ),
      MeasurableSet (tailSet P Q x.1 x.2 ∩ tailSet P Q y.1 y.2) := fun x y =>
    (tailSet_measurable P Q x.1 x.2).inter (tailSet_measurable P Q y.1 y.2)
  have hFint : ∀ x y : (Σ _ : ℕ, ℕ), IntegrableOn (F x y) (Set.Ioc (0:ℝ) 1) := by
    intro x y
    apply Integrable.const_mul
    apply Integrable.indicator _ (hmeasI x y)
    exact ((kernel_norm_continuous N _).mul (kernel_norm_continuous N _)).integrableOn_Ioc
  -- integrability of the double sum
  have hsum_int : IntegrableOn
      (fun α => ∑ x ∈ canonAnchors P, ∑ y ∈ canonAnchors P, F x y α) (Set.Ioc (0:ℝ) 1) := by
    apply integrable_finset_sum
    intro x _
    exact integrable_finset_sum _ (fun y _ => hFint x y)
  -- the LHS integrand is a.e.-measurable and dominated by the double sum
  have hterm_cont : ∀ pq : ℕ × ℤ, Continuous (fun α : ℝ =>
      ((ArithmeticFunction.moebius pq.1 : ℂ) / (Nat.totient pq.1 : ℂ)) ^ 2
        * (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2) := by
    intro pq
    apply Continuous.mul continuous_const
    apply Continuous.pow
    apply continuous_finset_sum
    intro k _
    exact continuous_e.comp (by fun_prop)
  have hphi_meas : AEStronglyMeasurable (fun α => PhiArc N P Q α)
      (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    have hsm : StronglyMeasurable (fun α => PhiArc N P Q α) := by
      have hrw : (fun α => PhiArc N P Q α)
          = ∑ pq ∈ anchors P, (arc Q pq).indicator
              (fun α => ((ArithmeticFunction.moebius pq.1 : ℂ) / (Nat.totient pq.1 : ℂ)) ^ 2
                * (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2) := by
        funext α
        rw [Finset.sum_apply]
        rfl
      rw [hrw]
      apply Finset.stronglyMeasurable_sum
      intro pq _
      exact ((hterm_cont pq).stronglyMeasurable).indicator
        ((Metric.isClosed_closedBall.measurableSet).inter measurableSet_Ioc)
    exact hsm.aestronglyMeasurable
  have hpsi_cont : Continuous (fun α => PsiIdeal N P α) := by
    apply continuous_finset_sum
    intro q _
    apply Continuous.mul continuous_const
    apply continuous_finset_sum
    intro a _
    apply Continuous.pow
    apply continuous_finset_sum
    intro k _
    exact continuous_e.comp (by fun_prop)
  have hlhs_meas : AEStronglyMeasurable
      (fun α => ‖PsiIdeal N P α - PhiArc N P Q α‖ ^ 2)
      (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    ((hpsi_cont.aestronglyMeasurable.sub hphi_meas).norm.pow 2)
  have hlhs_int : IntegrableOn
      (fun α => ‖PsiIdeal N P α - PhiArc N P Q α‖ ^ 2) (Set.Ioc (0:ℝ) 1) := by
    apply Integrable.mono' hsum_int hlhs_meas
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with α hα
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact psi_sub_phi_sq_pointwise N P Q hP hPQ α hα
  -- monotone step
  have hmono : ∫ α in Set.Ioc (0:ℝ) 1, ‖PsiIdeal N P α - PhiArc N P Q α‖ ^ 2
      ≤ ∫ α in Set.Ioc (0:ℝ) 1, ∑ x ∈ canonAnchors P, ∑ y ∈ canonAnchors P, F x y α := by
    apply setIntegral_mono_on hlhs_int hsum_int measurableSet_Ioc
    intro α hα
    exact psi_sub_phi_sq_pointwise N P Q hP hPQ α hα
  refine hmono.trans (le_of_eq ?_)
  -- swap sum and integral
  rw [integral_finset_sum _ (fun x _ => integrable_finset_sum _ (fun y _ => hFint x y))]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [integral_finset_sum _ (fun y _ => hFint x y)]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  -- per-term: pull the constant, collapse the indicator to a set integral
  rw [hFdef]
  simp only
  rw [integral_const_mul, MeasureTheory.integral_indicator (hmeasI x y),
    Measure.restrict_restrict (hmeasI x y),
    Set.inter_eq_self_of_subset_left
      ((Set.inter_subset_left).trans (tailSet_subset_Ioc P Q x.1 x.2))]

/-- The Möbius-totient coefficient is `≤ 4/q` (zero off squarefree; B0 on squarefree). -/
lemma coef_le (q : ℕ) (hq : 1 ≤ q) :
    ‖((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) ^ 2‖ ≤ 4 / (q : ℝ) := by
  have hq0R : (0:ℝ) < (q : ℝ) := by exact_mod_cast hq
  by_cases hsq : Squarefree q
  · have hφ1 : 1 ≤ q.totient := Nat.totient_pos.mpr (by omega)
    have hφ0R : (0:ℝ) < (q.totient : ℝ) := by exact_mod_cast hφ1
    have hμ1 : |(ArithmeticFunction.moebius q : ℤ)| ≤ 1 :=
      ArithmeticFunction.abs_moebius_le_one
    have hnorm : ‖((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) ^ 2‖
        ≤ 1 / (q.totient : ℝ) ^ 2 := by
      rw [norm_pow, norm_div, Complex.norm_intCast, Complex.norm_natCast]
      have hμ1R : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ 1 := by
        rw [← Int.cast_abs]
        exact_mod_cast hμ1
      calc (|((ArithmeticFunction.moebius q : ℤ) : ℝ)| / (q.totient : ℝ)) ^ 2
          ≤ (1 / (q.totient : ℝ)) ^ 2 := by
            apply pow_le_pow_left₀ (by positivity)
            apply div_le_div_of_nonneg_right hμ1R hφ0R.le
        _ = 1 / (q.totient : ℝ) ^ 2 := by rw [div_pow, one_pow]
    refine hnorm.trans ?_
    rw [div_le_div_iff₀ (by positivity) hq0R]
    have := sqfree_totient_linear q hsq
    nlinarith [this]
  · have hμ0 : ArithmeticFunction.moebius q = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
    rw [hμ0]
    simp
    positivity

/-- The canonical anchor count is at most `P²`. -/
lemma canonAnchors_card_le (P : ℕ) : (canonAnchors P).card ≤ P ^ 2 := by
  rw [canonAnchors, Finset.card_sigma]
  calc ∑ q ∈ Finset.Icc 1 P, (redRes q).card
      ≤ ∑ _q ∈ Finset.Icc 1 P, P := by
        apply Finset.sum_le_sum
        intro q hq
        have h1 : (redRes q).card ≤ q := by
          calc (redRes q).card ≤ (Finset.range q).card := Finset.card_filter_le _ _
            _ = q := Finset.card_range q
        exact h1.trans (Finset.mem_Icc.mp hq).2
    _ = P * P := by rw [Finset.sum_const, Nat.card_Icc]; simp [Nat.smul_one_eq_cast]
    _ = P ^ 2 := (sq P).symm

/-- **harc brick B5d: the total arc-tail L² bound.**
    `∫_{(0,1]} ‖Ψ−Φ‖² ≤ 8(Q+1)³P^{5/2} + 192(Q+1)P⁷`. -/
lemma psi_sub_phi_L2_total (N P Q : ℕ) (hP : 1 ≤ P) (hQ2 : 2 ≤ Q)
    (hPQ : 2 * P ^ 2 < Q + 1) :
    ∫ α in Set.Ioc (0:ℝ) 1, ‖PsiIdeal N P α - PhiArc N P Q α‖ ^ 2
      ≤ ((Q : ℝ) + 1) ^ 3 * (8 * (P : ℝ) ^ ((5 : ℝ) / 2))
        + 192 * ((Q : ℝ) + 1) * (P : ℝ) ^ 7 := by
  classical
  refine (psi_sub_phi_L2_expand N P Q hP hPQ).trans ?_
  have hPR : (0:ℝ) < (P : ℝ) := by exact_mod_cast hP
  -- split every inner sum at y = x
  have hsplit : ∑ x ∈ canonAnchors P, ∑ y ∈ canonAnchors P,
      ‖((ArithmeticFunction.moebius x.1 : ℂ) / (Nat.totient x.1 : ℂ)) ^ 2‖
        * ‖((ArithmeticFunction.moebius y.1 : ℂ) / (Nat.totient y.1 : ℂ)) ^ 2‖
        * ∫ α in tailSet P Q x.1 x.2 ∩ tailSet P Q y.1 y.2,
            ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (x.2 : ℝ) / (x.1 : ℝ)))) ^ 2‖
              * ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (y.2 : ℝ) / (y.1 : ℝ)))) ^ 2‖
      = (∑ x ∈ canonAnchors P,
          ‖((ArithmeticFunction.moebius x.1 : ℂ) / (Nat.totient x.1 : ℂ)) ^ 2‖
            * ‖((ArithmeticFunction.moebius x.1 : ℂ) / (Nat.totient x.1 : ℂ)) ^ 2‖
            * ∫ α in tailSet P Q x.1 x.2 ∩ tailSet P Q x.1 x.2,
                ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (x.2 : ℝ) / (x.1 : ℝ)))) ^ 2‖
                  * ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (x.2 : ℝ) / (x.1 : ℝ)))) ^ 2‖)
        + ∑ x ∈ canonAnchors P, ∑ y ∈ (canonAnchors P).erase x,
            ‖((ArithmeticFunction.moebius x.1 : ℂ) / (Nat.totient x.1 : ℂ)) ^ 2‖
              * ‖((ArithmeticFunction.moebius y.1 : ℂ) / (Nat.totient y.1 : ℂ)) ^ 2‖
              * ∫ α in tailSet P Q x.1 x.2 ∩ tailSet P Q y.1 y.2,
                  ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (x.2 : ℝ) / (x.1 : ℝ)))) ^ 2‖
                    * ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (y.2 : ℝ) / (y.1 : ℝ)))) ^ 2‖ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    exact (Finset.add_sum_erase _ _ hx).symm
  rw [hsplit]
  have hmemfacts : ∀ x ∈ canonAnchors P, x.1 ∈ Finset.Icc 1 P ∧ x.2 ∈ redRes x.1 := by
    intro x hx
    exact ⟨(Finset.mem_sigma.mp hx).1, (Finset.mem_sigma.mp hx).2⟩
  -- diagonal part
  have hdiag : ∑ x ∈ canonAnchors P,
      ‖((ArithmeticFunction.moebius x.1 : ℂ) / (Nat.totient x.1 : ℂ)) ^ 2‖
        * ‖((ArithmeticFunction.moebius x.1 : ℂ) / (Nat.totient x.1 : ℂ)) ^ 2‖
        * ∫ α in tailSet P Q x.1 x.2 ∩ tailSet P Q x.1 x.2,
            ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (x.2 : ℝ) / (x.1 : ℝ)))) ^ 2‖
              * ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (x.2 : ℝ) / (x.1 : ℝ)))) ^ 2‖
      ≤ ((Q : ℝ) + 1) ^ 3 * (8 * (P : ℝ) ^ ((5 : ℝ) / 2)) := by
    have hper : ∀ x ∈ canonAnchors P,
        ‖((ArithmeticFunction.moebius x.1 : ℂ) / (Nat.totient x.1 : ℂ)) ^ 2‖
          * ‖((ArithmeticFunction.moebius x.1 : ℂ) / (Nat.totient x.1 : ℂ)) ^ 2‖
          * ∫ α in tailSet P Q x.1 x.2 ∩ tailSet P Q x.1 x.2,
              ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (x.2 : ℝ) / (x.1 : ℝ)))) ^ 2‖
                * ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (x.2 : ℝ) / (x.1 : ℝ)))) ^ 2‖
        ≤ ‖((ArithmeticFunction.moebius x.1 : ℂ) / (Nat.totient x.1 : ℂ)) ^ 2‖ ^ 2
            * (((x.1 : ℝ) * ((Q : ℝ) + 1)) ^ 3 / 8) := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := hmemfacts x hx
      have hint : ∫ α in tailSet P Q x.1 x.2 ∩ tailSet P Q x.1 x.2,
          ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (x.2 : ℝ) / (x.1 : ℝ)))) ^ 2‖
            * ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (x.2 : ℝ) / (x.1 : ℝ)))) ^ 2‖
          ≤ ((x.1 : ℝ) * ((Q : ℝ) + 1)) ^ 3 / 8 := by
        rw [Set.inter_self]
        have h := tail_L4_bound N P Q x.1 x.2 hx1 hx2 hQ2
        refine le_trans (le_of_eq ?_) h
        apply setIntegral_congr_fun (by
          apply MeasurableSet.diff measurableSet_Ioc
          apply MeasurableSet.biUnion (Set.to_countable _)
          intro pq _
          exact (Metric.isClosed_closedBall.measurableSet).inter measurableSet_Ioc)
        intro α _
        dsimp only
        exact (pow_two _).symm
      rw [← pow_two]
      apply mul_le_mul_of_nonneg_left hint (by positivity)
    refine (Finset.sum_le_sum hper).trans ?_
    rw [canonAnchors, Finset.sum_sigma]
    exact diagonal_bound P Q hP
  -- cross part
  have hcross : ∑ x ∈ canonAnchors P, ∑ y ∈ (canonAnchors P).erase x,
      ‖((ArithmeticFunction.moebius x.1 : ℂ) / (Nat.totient x.1 : ℂ)) ^ 2‖
        * ‖((ArithmeticFunction.moebius y.1 : ℂ) / (Nat.totient y.1 : ℂ)) ^ 2‖
        * ∫ α in tailSet P Q x.1 x.2 ∩ tailSet P Q y.1 y.2,
            ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (x.2 : ℝ) / (x.1 : ℝ)))) ^ 2‖
              * ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (y.2 : ℝ) / (y.1 : ℝ)))) ^ 2‖
      ≤ 192 * ((Q : ℝ) + 1) * (P : ℝ) ^ 7 := by
    have hterm : ∀ x ∈ canonAnchors P, ∀ y ∈ (canonAnchors P).erase x,
        ‖((ArithmeticFunction.moebius x.1 : ℂ) / (Nat.totient x.1 : ℂ)) ^ 2‖
          * ‖((ArithmeticFunction.moebius y.1 : ℂ) / (Nat.totient y.1 : ℂ)) ^ 2‖
          * ∫ α in tailSet P Q x.1 x.2 ∩ tailSet P Q y.1 y.2,
              ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (x.2 : ℝ) / (x.1 : ℝ)))) ^ 2‖
                * ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (y.2 : ℝ) / (y.1 : ℝ)))) ^ 2‖
        ≤ 192 * ((Q : ℝ) + 1) * (P : ℝ) ^ 3 := by
      intro x hx y hy
      obtain ⟨hx1, hx2⟩ := hmemfacts x hx
      obtain ⟨hy1, hy2⟩ := hmemfacts y ((Finset.erase_subset _ _) hy)
      obtain ⟨hxq1, hxqP⟩ := Finset.mem_Icc.mp hx1
      obtain ⟨hyq1, hyqP⟩ := Finset.mem_Icc.mp hy1
      have hxy : x ≠ y := fun h => (Finset.ne_of_mem_erase hy) h.symm
      have hne : (x.2 : ℝ) / (x.1 : ℝ) ≠ (y.2 : ℝ) / (y.1 : ℝ) := by
        intro heq
        obtain ⟨hq, ha⟩ := canon_fraction_injective x.1 y.1 x.2 y.2 hxq1 hyq1 hx2 hy2 heq
        apply hxy
        cases x with | mk xq xa => cases y with | mk yq ya =>
          simp only at hq ha
          subst hq
          subst ha
          rfl
      have hI := cross_pair_bound N P Q x.1 y.1 x.2 y.2 hx1 hy1 hx2 hy2 hQ2 hne
      have hI0 : (0:ℝ) ≤ ∫ α in tailSet P Q x.1 x.2 ∩ tailSet P Q y.1 y.2,
          ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (x.2 : ℝ) / (x.1 : ℝ)))) ^ 2‖
            * ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (y.2 : ℝ) / (y.1 : ℝ)))) ^ 2‖ :=
        integral_nonneg (fun α => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      have hcx := coef_le x.1 hxq1
      have hcy := coef_le y.1 hyq1
      have hqx0 : (0:ℝ) < (x.1 : ℝ) := by exact_mod_cast hxq1
      have hqy0 : (0:ℝ) < (y.1 : ℝ) := by exact_mod_cast hyq1
      have hqxP : (x.1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hxqP
      have hqyP : (y.1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hyqP
      calc ‖((ArithmeticFunction.moebius x.1 : ℂ) / (Nat.totient x.1 : ℂ)) ^ 2‖
            * ‖((ArithmeticFunction.moebius y.1 : ℂ) / (Nat.totient y.1 : ℂ)) ^ 2‖
            * ∫ α in tailSet P Q x.1 x.2 ∩ tailSet P Q y.1 y.2,
                ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (x.2 : ℝ) / (x.1 : ℝ)))) ^ 2‖
                  * ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (y.2 : ℝ) / (y.1 : ℝ)))) ^ 2‖
          ≤ (4 / (x.1 : ℝ)) * (4 / (y.1 : ℝ))
              * (6 * ((x.1 : ℝ) * (y.1 : ℝ)) ^ 2 * (((Q : ℝ) + 1) * ((x.1 : ℝ) + (y.1 : ℝ)))) := by
            apply mul_le_mul
            · exact mul_le_mul hcx hcy (norm_nonneg _) (by positivity)
            · exact hI
            · exact hI0
            · positivity
        _ = 96 * ((x.1 : ℝ) * (y.1 : ℝ) * (((x.1 : ℝ) + (y.1 : ℝ)) * ((Q : ℝ) + 1))) := by
            field_simp
            ring
        _ ≤ 96 * ((P : ℝ) * (P : ℝ) * ((2 * (P : ℝ)) * ((Q : ℝ) + 1))) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            have hQ0 : (0:ℝ) ≤ (Q : ℝ) + 1 := by positivity
            apply mul_le_mul (mul_le_mul hqxP hqyP hqy0.le hPR.le)
            · apply mul_le_mul _ le_rfl hQ0 (by positivity)
              linarith
            · positivity
            · positivity
        _ = 192 * ((Q : ℝ) + 1) * (P : ℝ) ^ 3 := by ring
    have hcount : ((canonAnchors P).card : ℝ) ≤ (P : ℝ) ^ 2 := by
      calc ((canonAnchors P).card : ℝ) ≤ ((P ^ 2 : ℕ) : ℝ) := by
            exact_mod_cast canonAnchors_card_le P
        _ = (P : ℝ) ^ 2 := by push_cast; rfl
    have hQ0 : (0:ℝ) ≤ 192 * ((Q : ℝ) + 1) * (P : ℝ) ^ 3 := by positivity
    calc ∑ x ∈ canonAnchors P, ∑ y ∈ (canonAnchors P).erase x,
        ‖((ArithmeticFunction.moebius x.1 : ℂ) / (Nat.totient x.1 : ℂ)) ^ 2‖
          * ‖((ArithmeticFunction.moebius y.1 : ℂ) / (Nat.totient y.1 : ℂ)) ^ 2‖
          * ∫ α in tailSet P Q x.1 x.2 ∩ tailSet P Q y.1 y.2,
              ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (x.2 : ℝ) / (x.1 : ℝ)))) ^ 2‖
                * ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (y.2 : ℝ) / (y.1 : ℝ)))) ^ 2‖
        ≤ ∑ x ∈ canonAnchors P, ((canonAnchors P).card : ℝ)
            * (192 * ((Q : ℝ) + 1) * (P : ℝ) ^ 3) := by
          apply Finset.sum_le_sum
          intro x hx
          calc ∑ y ∈ (canonAnchors P).erase x, _
              ≤ ∑ _y ∈ (canonAnchors P).erase x, 192 * ((Q : ℝ) + 1) * (P : ℝ) ^ 3 :=
                Finset.sum_le_sum (hterm x hx)
            _ = ((canonAnchors P).erase x).card * (192 * ((Q : ℝ) + 1) * (P : ℝ) ^ 3) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ ((canonAnchors P).card : ℝ) * (192 * ((Q : ℝ) + 1) * (P : ℝ) ^ 3) := by
                apply mul_le_mul_of_nonneg_right _ hQ0
                exact_mod_cast Finset.card_le_card (Finset.erase_subset _ _)
      _ = ((canonAnchors P).card : ℝ) * ((canonAnchors P).card : ℝ)
            * (192 * ((Q : ℝ) + 1) * (P : ℝ) ^ 3) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ (P : ℝ) ^ 2 * (P : ℝ) ^ 2 * (192 * ((Q : ℝ) + 1) * (P : ℝ) ^ 3) := by
          apply mul_le_mul_of_nonneg_right _ hQ0
          exact mul_le_mul hcount hcount (by positivity) (by positivity)
      _ = 192 * ((Q : ℝ) + 1) * (P : ℝ) ^ 7 := by ring
  linarith [hdiag, hcross]


/-- **harc brick B5e: the arc-tail RHS is eventually `≤ εN³`** at `P = ⌊(log N)⁹⌋₊`,
    `Q = N/P`: term 1 is `64N³/√P` (needs `√P ≥ 128/ε`), term 2 is `384N·(log N)⁵⁴`
    (polylog vs `N²`). -/
lemma arc_tail_rhs_small (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (((N / Nat.floor ((Real.log N) ^ 9) : ℕ) : ℝ) + 1) ^ 3
          * (8 * ((Nat.floor ((Real.log N) ^ 9) : ℕ) : ℝ) ^ ((5 : ℝ) / 2))
        + 192 * (((N / Nat.floor ((Real.log N) ^ 9) : ℕ) : ℝ) + 1)
          * ((Nat.floor ((Real.log N) ^ 9) : ℕ) : ℝ) ^ 7
      ≤ ε * (N : ℝ) ^ 3 := by
  set C : ℝ := max 2 ((128 / ε) ^ 2 + 1) with hCdef
  have hC2 : (2:ℝ) ≤ C := le_max_left _ _
  obtain ⟨N₁, hN₁⟩ := polylog_le_self 9 1 (by norm_num)
  obtain ⟨N₂, hN₂⟩ := polylog_le_self 54 (768 / ε) (by positivity)
  refine ⟨max (Nat.ceil (Real.exp C) + 1) (max 1 (max N₁ N₂)), fun N hN => ?_⟩
  have hNe : Nat.ceil (Real.exp C) + 1 ≤ N := le_trans (le_max_left _ _) hN
  have hN1nat : 1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN1' : N₁ ≤ N :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hN
  have hN2' : N₂ ≤ N :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hN
  have hN0R : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN1nat
  have hN1R : (1:ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1nat
  set L : ℝ := Real.log N with hLdef
  -- log N ≥ C from N ≥ ⌈exp C⌉ + 1
  have hNR : Real.exp C ≤ (N : ℝ) := by
    calc Real.exp C ≤ (Nat.ceil (Real.exp C) : ℝ) := Nat.le_ceil _
      _ ≤ (N : ℝ) := by exact_mod_cast le_trans (Nat.le_succ _) hNe
  have hLC : C ≤ L := (Real.le_log_iff_exp_le hN0R).mpr hNR
  have hL1 : (1:ℝ) ≤ L := le_trans (by linarith) hLC
  have hL9C : C ≤ L ^ 9 := hLC.trans (le_self_pow₀ hL1 (by norm_num))
  set P : ℕ := Nat.floor (L ^ 9) with hPdef
  have hfloor_gt : L ^ 9 < (P : ℝ) + 1 := by
    have := Nat.lt_floor_add_one (L ^ 9)
    exact_mod_cast this
  have hPlb : C - 1 ≤ (P : ℝ) := by linarith
  have hP1R : (1:ℝ) ≤ (P : ℝ) := by linarith
  have hP0R : (0:ℝ) < (P : ℝ) := by linarith
  have hPsq : (128 / ε) ^ 2 ≤ (P : ℝ) := by
    have h1 : (128 / ε) ^ 2 + 1 ≤ C := le_max_right _ _
    linarith
  have hPleL9 : (P : ℝ) ≤ L ^ 9 := Nat.floor_le (by positivity)
  have hPleN : (P : ℝ) ≤ (N : ℝ) := by
    have := hN₁ N hN1'
    rw [one_mul] at this
    exact hPleL9.trans this
  have hPleNnat : P ≤ N := by exact_mod_cast hPleN
  set Q : ℕ := N / P with hQdef
  have hQP : (Q + 1) * P ≤ 2 * N := by
    have h1 : Q * P ≤ N := Nat.div_mul_le_self N P
    have h2 : (Q + 1) * P = Q * P + P := by ring
    omega
  have hQPR : ((Q : ℝ) + 1) * (P : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hQP
  have hQ0R : (0:ℝ) ≤ (Q : ℝ) + 1 := by positivity
  have hsqrtP0 : 0 < Real.sqrt (P : ℝ) := Real.sqrt_pos.mpr hP0R
  have hsqrtP : 128 / ε ≤ Real.sqrt (P : ℝ) := by
    rw [show (128 / ε) = Real.sqrt ((128 / ε) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt hPsq
  -- P^{5/2} = P³/√P
  have hrpow : (P : ℝ) ^ ((5 : ℝ) / 2) = (P : ℝ) ^ 3 / Real.sqrt (P : ℝ) := by
    rw [eq_div_iff (ne_of_gt hsqrtP0), Real.sqrt_eq_rpow, ← Real.rpow_add hP0R]
    rw [show (5 : ℝ) / 2 + 1 / 2 = ((3 : ℕ) : ℝ) by norm_num]
    exact Real.rpow_natCast _ 3
  -- term 1: ≤ 64N³/√P ≤ (ε/2)N³
  have hterm1 : ((Q : ℝ) + 1) ^ 3 * (8 * (P : ℝ) ^ ((5 : ℝ) / 2)) ≤ ε / 2 * (N : ℝ) ^ 3 := by
    rw [hrpow]
    have hcube : ((Q : ℝ) + 1) ^ 3 * (P : ℝ) ^ 3 ≤ 8 * (N : ℝ) ^ 3 := by
      calc ((Q : ℝ) + 1) ^ 3 * (P : ℝ) ^ 3 = (((Q : ℝ) + 1) * (P : ℝ)) ^ 3 := by ring
        _ ≤ (2 * (N : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) hQPR 3
        _ = 8 * (N : ℝ) ^ 3 := by ring
    have hchain : ((Q : ℝ) + 1) ^ 3 * (8 * ((P : ℝ) ^ 3 / Real.sqrt (P : ℝ)))
        = 8 * (((Q : ℝ) + 1) ^ 3 * (P : ℝ) ^ 3) / Real.sqrt (P : ℝ) := by ring
    rw [hchain]
    rw [div_le_iff₀ hsqrtP0]
    have h64 : 64 ≤ ε / 2 * Real.sqrt (P : ℝ) := by
      calc (64:ℝ) = ε / 2 * (128 / ε) := by field_simp; norm_num
        _ ≤ ε / 2 * Real.sqrt (P : ℝ) := by
            apply mul_le_mul_of_nonneg_left hsqrtP (by positivity)
    have hN3 : (0:ℝ) ≤ (N : ℝ) ^ 3 := by positivity
    calc 8 * (((Q : ℝ) + 1) ^ 3 * (P : ℝ) ^ 3)
        ≤ 8 * (8 * (N : ℝ) ^ 3) := by linarith
      _ = (N : ℝ) ^ 3 * 64 := by ring
      _ ≤ (N : ℝ) ^ 3 * (ε / 2 * Real.sqrt (P : ℝ)) :=
          mul_le_mul_of_nonneg_left h64 hN3
      _ = ε / 2 * (N : ℝ) ^ 3 * Real.sqrt (P : ℝ) := by ring
  -- term 2: ≤ 384N·L⁵⁴ ≤ (ε/2)N³
  have hterm2 : 192 * ((Q : ℝ) + 1) * (P : ℝ) ^ 7 ≤ ε / 2 * (N : ℝ) ^ 3 := by
    have hL54 : 768 / ε * L ^ 54 ≤ (N : ℝ) := hN₂ N hN2'
    have hP6 : (P : ℝ) ^ 6 ≤ (L ^ 9) ^ 6 := pow_le_pow_left₀ (by positivity) hPleL9 6
    calc 192 * ((Q : ℝ) + 1) * (P : ℝ) ^ 7
        = 192 * ((((Q : ℝ) + 1) * (P : ℝ)) * (P : ℝ) ^ 6) := by ring
      _ ≤ 192 * ((2 * (N : ℝ)) * (L ^ 9) ^ 6) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul hQPR hP6 (by positivity) (by positivity)
      _ = 384 * (N : ℝ) * L ^ 54 := by ring
      _ ≤ ε / 2 * (N : ℝ) ^ 3 := by
          have hL54' : L ^ 54 ≤ ε * (N : ℝ) / 768 := by
            have h := mul_le_mul_of_nonneg_left hL54 (by positivity : (0:ℝ) ≤ ε / 768)
            have hne : ε ≠ 0 := ne_of_gt hε
            calc L ^ 54 = ε / 768 * (768 / ε * L ^ 54) := by field_simp
              _ ≤ ε / 768 * (N : ℝ) := h
              _ = ε * (N : ℝ) / 768 := by ring
          have h1 : 384 * (N : ℝ) * L ^ 54 ≤ 384 * (N : ℝ) * (ε * (N : ℝ) / 768) :=
            mul_le_mul_of_nonneg_left hL54' (by positivity)
          have h2 : 384 * (N : ℝ) * (ε * (N : ℝ) / 768) = ε / 2 * (N : ℝ) ^ 2 := by ring
          have h3 : ε / 2 * (N : ℝ) ^ 2 ≤ ε / 2 * (N : ℝ) ^ 3 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            nlinarith [hN1R]
          linarith
  linarith [hterm1, hterm2]

noncomputable def cRamC (q n : ℕ) : ℂ := ∑ a ∈ redRes q, e (-((n : ℝ) * ((a : ℝ) / (q : ℝ))))

noncomputable def singSeriesC (P n : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 P, ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) ^ 2 * cRamC q n




lemma e_neg_conj (x : ℝ) : e (-x) = starRingEnd ℂ (e x) := by
  rw [e, e, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  push_cast
  ring

/-- **harc brick 84a: `cRamC` is the integer Ramanujan sum.** The `e(−na/q)` form is the
    conjugate of `ramSum`, which is real (`ramSum_eq_cRam`). -/
lemma cRamC_eq_cRam (q n : ℕ) (hq : 0 < q) : cRamC q n = (cRam q n : ℂ) := by
  have hconj : cRamC q n = starRingEnd ℂ (ramSum q n) := by
    rw [cRamC, ramSum, map_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [← e_neg_conj]
    congr 1
    ring
  rw [hconj, ramSum_eq_cRam q n hq]
  simp

/-- **harc brick 84b: the real part of the truncated singular series** is the real
    `∑_{q≤P} μ(q)²·c_q(n)/φ(q)²` (the `Tarith` partial sum of the truncation half). -/
lemma singSeriesC_re (P n : ℕ) :
    (singSeriesC P n).re
      = ∑ q ∈ Finset.Icc 1 P,
          (ArithmeticFunction.moebius q : ℝ) ^ 2 * (cRam q n : ℝ) / (Nat.totient q : ℝ) ^ 2 := by
  rw [singSeriesC, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
  rw [cRamC_eq_cRam q n hq1]
  have hcast : ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) ^ 2 * (cRam q n : ℂ)
      = (((ArithmeticFunction.moebius q : ℝ) ^ 2 * (cRam q n : ℝ) / (Nat.totient q : ℝ) ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.ofReal_re]

















lemma e_zero : e 0 = 1 := by
  rw [e]
  simp

lemma continuous_e' : Continuous e := by
  unfold e
  fun_prop

/-- **Bessel on `(0,1]` for `f` with integrable square** — no continuity and no
    measurability hypothesis (a non-measurable `f` yields junk-zero coefficients and the
    bound holds trivially). Discharges HarcArcTail's `bessel_Ioc` axiom verbatim. -/
lemma bessel_Ioc_proven (f : ℝ → ℂ)
    (hf : IntegrableOn (fun α => ‖f α‖ ^ 2) (Set.Ioc (0:ℝ) 1)) (M : ℕ) :
    ∑ n ∈ Finset.range M, ‖∫ α in Set.Ioc (0:ℝ) 1, f α * e (-((n : ℝ) * α))‖ ^ 2
      ≤ ∫ α in Set.Ioc (0:ℝ) 1, ‖f α‖ ^ 2 := by
  classical
  have hRHS0 : (0:ℝ) ≤ ∫ α in Set.Ioc (0:ℝ) 1, ‖f α‖ ^ 2 :=
    integral_nonneg (fun α => sq_nonneg _)
  have hecont : ∀ n : ℕ, Continuous fun α : ℝ => e (-((n : ℝ) * α)) := by
    intro n
    exact continuous_e'.comp (by fun_prop)
  by_cases hmeas : AEStronglyMeasurable f (volume.restrict (Set.Ioc (0:ℝ) 1))
  swap
  · -- non-measurable: every coefficient integral is the junk value 0
    have hczero : ∀ n : ℕ,
        (∫ α in Set.Ioc (0:ℝ) 1, f α * e (-((n : ℝ) * α))) = 0 := by
      intro n
      apply integral_undef
      intro hInt
      apply hmeas
      have h2 : AEStronglyMeasurable
          (fun α => (f α * e (-((n : ℝ) * α))) * e ((n : ℝ) * α))
          (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
        hInt.aestronglyMeasurable.mul
          (continuous_e'.comp (by fun_prop : Continuous fun α : ℝ => (n : ℝ) * α)).aestronglyMeasurable
      have hid : (fun α => (f α * e (-((n : ℝ) * α))) * e ((n : ℝ) * α)) = f := by
        funext α
        rw [mul_assoc, e_add]
        simp [e_zero]
      rwa [hid] at h2
    calc ∑ n ∈ Finset.range M, ‖∫ α in Set.Ioc (0:ℝ) 1, f α * e (-((n : ℝ) * α))‖ ^ 2
        = ∑ n ∈ Finset.range M, (0:ℝ) := by
          apply Finset.sum_congr rfl
          intro n _
          rw [hczero n]
          simp
      _ = 0 := Finset.sum_const_zero
      _ ≤ _ := hRHS0
  -- measurable case: f is integrable, then the projection trick
  have hfint : IntegrableOn f (Set.Ioc (0:ℝ) 1) := by
    apply Integrable.mono'
      (g := fun α => (1 + ‖f α‖ ^ 2) / 2)
      ((((integrable_const (1:ℝ)).add hf).div_const 2)) hmeas
    apply Filter.Eventually.of_forall
    intro α
    nlinarith [sq_nonneg (‖f α‖ - 1), norm_nonneg (f α)]
  set c : ℕ → ℂ := fun n => ∫ α in Set.Ioc (0:ℝ) 1, f α * e (-((n : ℝ) * α)) with hc
  set T : ℝ → ℂ := fun α => ∑ n ∈ Finset.range M, c n * e ((n : ℝ) * α) with hT
  have hTcont : Continuous T := by
    rw [hT]
    apply continuous_finset_sum
    intro n _
    exact continuous_const.mul (continuous_e'.comp (by fun_prop))
  -- integrability workhorses (f integrable × bounded measurable factor)
  have hInt_fe : ∀ n : ℕ, IntegrableOn (fun α => f α * e (-((n : ℝ) * α)))
      (Set.Ioc (0:ℝ) 1) := by
    intro n
    have hm1 : AEStronglyMeasurable (fun α => f α * e (-((n : ℝ) * α)))
        (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
      hmeas.mul (hecont n).aestronglyMeasurable
    apply Integrable.mono' hfint.norm hm1
    apply Filter.Eventually.of_forall
    intro α
    rw [norm_mul, e_norm, mul_one]
  have hTbound : ∀ α : ℝ, ‖T α‖ ≤ ∑ n ∈ Finset.range M, ‖c n‖ := by
    intro α
    rw [hT]
    refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
    apply Finset.sum_congr rfl
    intro n _
    rw [norm_mul, e_norm, mul_one]
  have hInt_fT : IntegrableOn (fun α => f α * (starRingEnd ℂ) (T α))
      (Set.Ioc (0:ℝ) 1) := by
    have hm2 : AEStronglyMeasurable (fun α => f α * (starRingEnd ℂ) (T α))
        (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
      hmeas.mul (Complex.continuous_conj.comp hTcont).aestronglyMeasurable
    apply Integrable.mono' (hfint.norm.mul_const (∑ n ∈ Finset.range M, ‖c n‖)) hm2
    apply Filter.Eventually.of_forall
    intro α
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [RCLike.norm_conj]
    exact hTbound α
  -- Key 1: ∫ f·conj T = ∑ c n · conj (c n)
  have hkey1 : (∫ α in Set.Ioc (0:ℝ) 1, f α * (starRingEnd ℂ) (T α))
      = ∑ n ∈ Finset.range M, c n * (starRingEnd ℂ) (c n) := by
    have hexp : ∀ α : ℝ, f α * (starRingEnd ℂ) (T α)
        = ∑ n ∈ Finset.range M, (starRingEnd ℂ) (c n) * (f α * e (-((n : ℝ) * α))) := by
      intro α
      rw [hT]
      dsimp only
      rw [map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [map_mul, e_conj]
      ring
    calc (∫ α in Set.Ioc (0:ℝ) 1, f α * (starRingEnd ℂ) (T α))
        = ∫ α in Set.Ioc (0:ℝ) 1,
            ∑ n ∈ Finset.range M, (starRingEnd ℂ) (c n) * (f α * e (-((n : ℝ) * α))) := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro α _
          exact hexp α
      _ = ∑ n ∈ Finset.range M,
            ∫ α in Set.Ioc (0:ℝ) 1, (starRingEnd ℂ) (c n) * (f α * e (-((n : ℝ) * α))) := by
          apply integral_finset_sum
          intro n _
          exact (hInt_fe n).const_mul _
      _ = ∑ n ∈ Finset.range M,
            (starRingEnd ℂ) (c n) * ∫ α in Set.Ioc (0:ℝ) 1, f α * e (-((n : ℝ) * α)) := by
          apply Finset.sum_congr rfl
          intro n _
          exact integral_const_mul _ _
      _ = ∑ n ∈ Finset.range M, c n * (starRingEnd ℂ) (c n) := by
          apply Finset.sum_congr rfl
          intro n _
          have hfold : (∫ α in Set.Ioc (0:ℝ) 1, f α * e (-((n : ℝ) * α))) = c n := rfl
          rw [hfold]
          ring
  -- Key 2: the expansion of ∫ ‖f − T‖²
  have hptwise : ∀ α : ℝ, ‖f α - T α‖ ^ 2
      = ‖f α‖ ^ 2 - 2 * (f α * (starRingEnd ℂ) (T α)).re + ‖T α‖ ^ 2 := by
    intro α
    have h1 : (‖f α - T α‖ : ℝ) ^ 2 = ((f α - T α) * (starRingEnd ℂ) (f α - T α)).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have h2 : (‖f α‖ : ℝ) ^ 2 = (f α * (starRingEnd ℂ) (f α)).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have h3 : (‖T α‖ : ℝ) ^ 2 = (T α * (starRingEnd ℂ) (T α)).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have hconjswap : (T α * (starRingEnd ℂ) (f α)).re = (f α * (starRingEnd ℂ) (T α)).re := by
      have : T α * (starRingEnd ℂ) (f α) = (starRingEnd ℂ) (f α * (starRingEnd ℂ) (T α)) := by
        rw [map_mul, Complex.conj_conj]
        ring
      rw [this, Complex.conj_re]
    rw [h1, h2, h3]
    have hexpand : (f α - T α) * (starRingEnd ℂ) (f α - T α)
        = f α * (starRingEnd ℂ) (f α) - f α * (starRingEnd ℂ) (T α)
          - T α * (starRingEnd ℂ) (f α) + T α * (starRingEnd ℂ) (T α) := by
      rw [map_sub]
      ring
    rw [hexpand]
    simp only [Complex.add_re, Complex.sub_re]
    rw [hconjswap]
    ring
  have hIfT : IntegrableOn (fun α => (f α * (starRingEnd ℂ) (T α)).re)
      (Set.Ioc (0:ℝ) 1) volume := hInt_fT.re
  have hIT2 : IntegrableOn (fun α => ‖T α‖ ^ 2) (Set.Ioc (0:ℝ) 1) volume :=
    (hTcont.norm.pow 2).integrableOn_Ioc
  have hkey2 : (∫ α in Set.Ioc (0:ℝ) 1, ‖f α - T α‖ ^ 2)
      = (∫ α in Set.Ioc (0:ℝ) 1, ‖f α‖ ^ 2)
        - 2 * (∫ α in Set.Ioc (0:ℝ) 1, f α * (starRingEnd ℂ) (T α)).re
        + ∫ α in Set.Ioc (0:ℝ) 1, ‖T α‖ ^ 2 := by
    have hre : (∫ α in Set.Ioc (0:ℝ) 1, (f α * (starRingEnd ℂ) (T α)).re)
        = (∫ α in Set.Ioc (0:ℝ) 1, f α * (starRingEnd ℂ) (T α)).re := by
      have h := integral_re hInt_fT
      simpa [RCLike.re_to_complex] using h
    calc (∫ α in Set.Ioc (0:ℝ) 1, ‖f α - T α‖ ^ 2)
        = ∫ α in Set.Ioc (0:ℝ) 1,
            (‖f α‖ ^ 2 - 2 * (f α * (starRingEnd ℂ) (T α)).re + ‖T α‖ ^ 2) := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro α _
          exact hptwise α
      _ = (∫ α in Set.Ioc (0:ℝ) 1, (‖f α‖ ^ 2 - 2 * (f α * (starRingEnd ℂ) (T α)).re))
          + ∫ α in Set.Ioc (0:ℝ) 1, ‖T α‖ ^ 2 := by
          apply integral_add _ hIT2
          exact hf.sub (hIfT.const_mul 2)
      _ = (∫ α in Set.Ioc (0:ℝ) 1, ‖f α‖ ^ 2)
          - (∫ α in Set.Ioc (0:ℝ) 1, 2 * (f α * (starRingEnd ℂ) (T α)).re)
          + ∫ α in Set.Ioc (0:ℝ) 1, ‖T α‖ ^ 2 := by
          rw [integral_sub hf (hIfT.const_mul 2)]
      _ = (∫ α in Set.Ioc (0:ℝ) 1, ‖f α‖ ^ 2)
          - 2 * (∫ α in Set.Ioc (0:ℝ) 1, f α * (starRingEnd ℂ) (T α)).re
          + ∫ α in Set.Ioc (0:ℝ) 1, ‖T α‖ ^ 2 := by
          rw [integral_const_mul, hre]
  -- Key 3: ∫_{(0,1]} ‖T‖² = ∑ ‖c n‖² (Parseval — the sub-arc is the whole period)
  have hkey3 : (∫ α in Set.Ioc (0:ℝ) 1, ‖T α‖ ^ 2) = ∑ n ∈ Finset.range M, ‖c n‖ ^ 2 := by
    rw [hT]
    rw [← intervalIntegral.integral_of_le zero_le_one]
    exact parseval c M
  -- the cross term is the coefficient mass
  have hcross : (∫ α in Set.Ioc (0:ℝ) 1, f α * (starRingEnd ℂ) (T α)).re
      = ∑ n ∈ Finset.range M, ‖c n‖ ^ 2 := by
    rw [hkey1, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hnonneg : (0:ℝ) ≤ ∫ α in Set.Ioc (0:ℝ) 1, ‖f α - T α‖ ^ 2 := by
    apply integral_nonneg
    intro α
    positivity
  rw [hkey2, hcross, hkey3] at hnonneg
  have hfinal : ∑ n ∈ Finset.range M, ‖c n‖ ^ 2 ≤ ∫ α in Set.Ioc (0:ℝ) 1, ‖f α‖ ^ 2 := by
    linarith
  exact hfinal

end B4

-- ==== harc-chain shims (v3) ====

/-- `bessel_Ioc` discharge: the integrable-`f` Bessel proven in HarcArcTailBound. -/
theorem bessel_Ioc (f : ℝ → ℂ)
    (hf : MeasureTheory.IntegrableOn (fun α => ‖f α‖ ^ 2) (Set.Ioc (0:ℝ) 1)) (M : ℕ) :
    ∑ n ∈ Finset.range M, ‖∫ α in Set.Ioc (0:ℝ) 1, f α * e (-((n : ℝ) * α))‖ ^ 2
      ≤ ∫ α in Set.Ioc (0:ℝ) 1, ‖f α‖ ^ 2 := bessel_Ioc_proven f hf M

/-- `arcs_disjoint` discharge from the pairwise `farey_disjoint`. -/
theorem arcs_disjoint (P Q : ℕ) (hPQ : 2 * P ^ 2 < Q + 1) :
    ((anchors P : Finset (ℕ × ℤ)) : Set (ℕ × ℤ)).Pairwise (Function.onFun Disjoint (arc Q)) := by
  intro pq hpq pq' hpq' hne
  have hmem := Finset.mem_filter.mp (Finset.mem_coe.mp hpq)
  have hmem' := Finset.mem_filter.mp (Finset.mem_coe.mp hpq')
  have hq := (Finset.mem_Icc.mp (Finset.mem_product.mp hmem.1).1)
  have hq' := (Finset.mem_Icc.mp (Finset.mem_product.mp hmem'.1).1)
  have hball := farey_disjoint P Q hPQ pq.2 pq'.2 pq.1 pq'.1
    (by omega) (by omega) hq.2 hq'.2 hmem.2 hmem'.2
    (by
      intro ⟨ha, hqeq⟩
      exact hne (Prod.ext hqeq ha))
  exact Disjoint.mono Set.inter_subset_left Set.inter_subset_left hball

/-!
# harc ARC-TAIL half (major-arc model evaluation → singular-series × kernel)

The second (deepest) half of `harc`, split out to check fast. The arc-tail sub-error is
`l2_error_triangle`'s input `h1 = f − g` with `f = Re coeffModel`, `g = 𝔖_P·r_N`:
`∑_{n∈(X/2,X]}(Re coeffModel − 𝔖_P·r_N)² ≤ εX³`. It evaluates the anchor-window model integral.

Route: per anchor, factor `∑_r e(ra/q)λ = μ(q)/φ(q)` out (`anchor_integrand_eq`), leaving the pure
Dirichlet-kernel arc integral `∫_arc D_N(α−a/q)²e(-nα)`; change variables `β = α−a/q`, giving
`e(-na/q)·(∫_full D_N²e(-nβ) − arc-tail)` = `e(-na/q)·(r_N(n) − ρ_q(n))` [`dirichlet_full`]; sum over
`a` gives the Ramanujan sum `∑_a e(-na/q) = c_q(n)`, so `coeffModel = 𝔖_P·r_N − ∑_q(μ/φ)²∑_a e(-na/q)ρ_q`;
the error `∑_n(⋯ρ_q)² ≤ εX³` via `∫|D_N|⁴` Bessel + Farey almost-orthogonality.

`e`, `lambdaModel`, `anchors`, `coeffModel` are the identical top-level definitions from
`RatedWindow.lean`; `lambdaModel_coeff` / `dirichlet_full` enter as labeled cross-file inputs
(PROVEN in `MinorArcExpSum.lean` / `MajorArcMainTerm.lean`), discharged at Phase-F concatenation.
-/

open MeasureTheory





section Inputs


end Inputs

end GoldbachChain
