import ManuscriptLocal

/-!
# Actual manuscript vertex fibers reduce to two-prime affine parameter counts

The required degree estimate concerns the genuine three-partite manuscript
edge set, not an abstract family of two affine forms.  Fixing a left vertex
produces the prime forms `q` and `2 * d * q - x`; fixing a right vertex
produces the prime forms `q` and `y - a * q`.  The coefficient divisors are
summed explicitly, so uniqueness of their representations is not assumed.

These finite reductions are unconditional.  They do not assert the remaining
uniform Selberg estimate or a solution to Erdős problem #689.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos689

/-- The increasing two-prime parameter family of a fixed left vertex. -/
def leftFiberPrimeParameters (n x d : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun q =>
    q.Prime ∧ (2 * d * q - x).Prime

/-- The decreasing two-prime parameter family of a fixed right vertex. -/
def rightFiberPrimeParameters (n y a : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun q =>
    q.Prime ∧ (y - a * q).Prime

/-- The two-prime parameter family of a fixed label and coefficient pair. -/
noncomputable def labelFiberPrimeParameters (n z a d : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 n).filter fun q =>
    q.Prime ∧ ∃ r ∈ Finset.Icc 1 n,
      r.Prime ∧ 2 * d * r = a * q + z

/-- Left-fiber prime pairs retaining both exact switched-residue selectors. -/
def leftFiberSwitchedPrimeParameters
    (S : Finset ℕ) (b : ℕ → ℕ) (n x d : ℕ) : Finset ℕ :=
  (leftFiberPrimeParameters n x d).filter fun q =>
    switchedHits S b (2 * x) = 0 ∧
      switchedHits S b (4 * d * q) = 0

/-- Right-fiber prime pairs retaining both exact switched-residue selectors. -/
def rightFiberSwitchedPrimeParameters
    (S : Finset ℕ) (b : ℕ → ℕ) (n y a : ℕ) : Finset ℕ :=
  (rightFiberPrimeParameters n y a).filter fun q =>
    switchedHits S b (2 * a * q) = 0 ∧
      switchedHits S b (2 * y) = 0

/-- Label-fiber prime pairs retaining both exact switched-residue selectors. -/
noncomputable def labelFiberSwitchedPrimeParameters
    (S : Finset ℕ) (b : ℕ → ℕ) (n z a d : ℕ) : Finset ℕ := by
  classical
  exact (labelFiberPrimeParameters n z a d).filter fun q =>
    switchedHits S b (2 * a * q) = 0 ∧
      switchedHits S b (2 * (a * q + z)) = 0

/-- Once the left endpoint is fixed, the right endpoint determines the whole edge. -/
theorem manuscriptEdge_right_injective_on_left_fiber
    {S : Finset ℕ} {b : ℕ → ℕ} {n : ℕ} {τ ell : ℝ}
    (E : Finset TripleEdge) (x : ℕ)
    (hactual : ∀ e ∈ E, manuscriptEdge S b n τ ell e) :
    Set.InjOn (fun e : TripleEdge => e.2.1)
      (↑(E.filter fun e => e.1 = x) : Set TripleEdge) := by
  intro e he f hf hright
  obtain ⟨heE, hex⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp he)
  obtain ⟨hfE, hfx⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hf)
  change e.2.1 = f.2.1 at hright
  have hleft : e.1 = f.1 := hex.trans hfx.symm
  have herelation := (hactual e heE).2.1
  have hfrelation := (hactual f hfE).2.1
  have hlabel : e.2.2 = f.2.2 := by omega
  exact Prod.ext hleft (Prod.ext hright hlabel)

/-- Once the right endpoint is fixed, the left endpoint determines the whole edge. -/
theorem manuscriptEdge_left_injective_on_right_fiber
    {S : Finset ℕ} {b : ℕ → ℕ} {n : ℕ} {τ ell : ℝ}
    (E : Finset TripleEdge) (y : ℕ)
    (hactual : ∀ e ∈ E, manuscriptEdge S b n τ ell e) :
    Set.InjOn (fun e : TripleEdge => e.1)
      (↑(E.filter fun e => e.2.1 = y) : Set TripleEdge) := by
  intro e he f hf hleft
  obtain ⟨heE, hey⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp he)
  obtain ⟨hfE, hfy⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hf)
  change e.1 = f.1 at hleft
  have hright : e.2.1 = f.2.1 := hey.trans hfy.symm
  have herelation := (hactual e heE).2.1
  have hfrelation := (hactual f hfE).2.1
  have hlabel : e.2.2 = f.2.2 := by omega
  exact Prod.ext hleft (Prod.ext hright hlabel)

/-- Once the prime label is fixed, the left endpoint determines the whole edge. -/
theorem manuscriptEdge_left_injective_on_label_fiber
    {S : Finset ℕ} {b : ℕ → ℕ} {n : ℕ} {τ ell : ℝ}
    (E : Finset TripleEdge) (z : ℕ)
    (hactual : ∀ e ∈ E, manuscriptEdge S b n τ ell e) :
    Set.InjOn (fun e : TripleEdge => e.1)
      (↑(E.filter fun e => e.2.2 = z) : Set TripleEdge) := by
  intro e he f hf hleft
  obtain ⟨heE, hez⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp he)
  obtain ⟨hfE, hfz⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hf)
  change e.1 = f.1 at hleft
  have hlabel : e.2.2 = f.2.2 := hez.trans hfz.symm
  have herelation := (hactual e heE).2.1
  have hfrelation := (hactual f hfE).2.1
  have hright : e.2.1 = f.2.1 := by omega
  exact Prod.ext hleft (Prod.ext hright hlabel)

/-- The actual left degree is bounded by its explicit increasing two-prime sums. -/
theorem manuscriptEdge_left_fiber_card_le_prime_parameter_sum
    {S : Finset ℕ} {b : ℕ → ℕ} {n : ℕ} {τ ell : ℝ}
    (E : Finset TripleEdge) (x : ℕ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hactual : ∀ e ∈ E, manuscriptEdge S b n τ ell e) :
    (E.filter fun e => e.1 = x).card ≤
      ∑ d ∈ (∏ s ∈ S, s).divisors,
        (leftFiberPrimeParameters n x d).card := by
  classical
  let W := ∏ s ∈ S, s
  let fiber := E.filter fun e => e.1 = x
  let parameterVertices : ℕ → Finset ℕ := fun d =>
    (leftFiberPrimeParameters n x d).image (fun q => 2 * d * q)
  have hW : 0 < W := by
    exact Finset.prod_pos fun s hs => (hsupport s hs).pos
  have hinjective : Set.InjOn (fun e : TripleEdge => e.2.1)
      (↑fiber : Set TripleEdge) :=
    manuscriptEdge_right_injective_on_left_fiber E x hactual
  have hsubset : fiber.image (fun e : TripleEdge => e.2.1) ⊆
      W.divisors.biUnion parameterVertices := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨heE, hex⟩ := Finset.mem_filter.mp he
    have hedge := hactual e heE
    obtain ⟨hlabelprime, hrelation, _, hrightbound, _, _, _, _, _,
      ⟨d, q, hd, hq, hrepr⟩⟩ := hedge
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hW
    have hqright : q ≤ e.2.1 := by
      rw [hrepr]
      simpa [mul_assoc] using
        (Nat.le_mul_of_pos_left q (Nat.mul_pos (by norm_num) hdpos))
    have hqn : q ≤ n := by omega
    have hlabel : 2 * d * q - x = e.2.2 := by
      omega
    apply Finset.mem_biUnion.mpr
    refine ⟨d, Nat.mem_divisors.mpr ⟨hd, Nat.ne_of_gt hW⟩, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨q, Finset.mem_filter.mpr ?_, hrepr.symm⟩
    exact ⟨Finset.mem_Icc.mpr ⟨hq.one_le, hqn⟩,
      hq, hlabel.symm ▸ hlabelprime⟩
  calc
    fiber.card = (fiber.image fun e : TripleEdge => e.2.1).card :=
      (Finset.card_image_iff.mpr hinjective).symm
    _ ≤ (W.divisors.biUnion parameterVertices).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ d ∈ W.divisors, (parameterVertices d).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ d ∈ W.divisors, (leftFiberPrimeParameters n x d).card := by
      apply Finset.sum_le_sum
      intro d _
      exact Finset.card_image_le

/-- The actual right degree is bounded by its explicit decreasing two-prime sums. -/
theorem manuscriptEdge_right_fiber_card_le_prime_parameter_sum
    {S : Finset ℕ} {b : ℕ → ℕ} {n : ℕ} {τ ell : ℝ}
    (E : Finset TripleEdge) (y : ℕ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hactual : ∀ e ∈ E, manuscriptEdge S b n τ ell e) :
    (E.filter fun e => e.2.1 = y).card ≤
      ∑ a ∈ (∏ s ∈ S, s).divisors,
        (rightFiberPrimeParameters n y a).card := by
  classical
  let W := ∏ s ∈ S, s
  let fiber := E.filter fun e => e.2.1 = y
  let parameterVertices : ℕ → Finset ℕ := fun a =>
    (rightFiberPrimeParameters n y a).image (fun q => a * q)
  have hW : 0 < W := by
    exact Finset.prod_pos fun s hs => (hsupport s hs).pos
  have hinjective : Set.InjOn (fun e : TripleEdge => e.1)
      (↑fiber : Set TripleEdge) :=
    manuscriptEdge_left_injective_on_right_fiber E y hactual
  have hsubset : fiber.image (fun e : TripleEdge => e.1) ⊆
      W.divisors.biUnion parameterVertices := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨heE, hey⟩ := Finset.mem_filter.mp he
    have hedge := hactual e heE
    obtain ⟨hlabelprime, hrelation, hleftbound, _, _, _, _, _,
      ⟨a, q, ha, hq, hrepr⟩, _⟩ := hedge
    have hapos : 0 < a := Nat.pos_of_dvd_of_pos ha hW
    have hqleft : q ≤ e.1 := by
      rw [hrepr]
      exact Nat.le_mul_of_pos_left q hapos
    have hqn : q ≤ n := by omega
    have hlabel : y - a * q = e.2.2 := by
      omega
    apply Finset.mem_biUnion.mpr
    refine ⟨a, Nat.mem_divisors.mpr ⟨ha, Nat.ne_of_gt hW⟩, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨q, Finset.mem_filter.mpr ?_, hrepr.symm⟩
    exact ⟨Finset.mem_Icc.mpr ⟨hq.one_le, hqn⟩,
      hq, hlabel.symm ▸ hlabelprime⟩
  calc
    fiber.card = (fiber.image fun e : TripleEdge => e.1).card :=
      (Finset.card_image_iff.mpr hinjective).symm
    _ ≤ (W.divisors.biUnion parameterVertices).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ a ∈ W.divisors, (parameterVertices a).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ a ∈ W.divisors, (rightFiberPrimeParameters n y a).card := by
      apply Finset.sum_le_sum
      intro a _
      exact Finset.card_image_le

/-- The actual label degree reduces to coefficient-summed two-prime equations. -/
theorem manuscriptEdge_label_fiber_card_le_prime_parameter_sum
    {S : Finset ℕ} {b : ℕ → ℕ} {n : ℕ} {τ ell : ℝ}
    (E : Finset TripleEdge) (z : ℕ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hactual : ∀ e ∈ E, manuscriptEdge S b n τ ell e) :
    (E.filter fun e => e.2.2 = z).card ≤
      ∑ c ∈ ((∏ s ∈ S, s).divisors.product
          (∏ s ∈ S, s).divisors),
        (labelFiberPrimeParameters n z c.1 c.2).card := by
  classical
  let W := ∏ s ∈ S, s
  let fiber := E.filter fun e => e.2.2 = z
  let coefficients := W.divisors.product W.divisors
  let parameterVertices : (ℕ × ℕ) → Finset ℕ := fun c =>
    (labelFiberPrimeParameters n z c.1 c.2).image (fun q => c.1 * q)
  have hW : 0 < W := by
    exact Finset.prod_pos fun s hs => (hsupport s hs).pos
  have hinjective : Set.InjOn (fun e : TripleEdge => e.1)
      (↑fiber : Set TripleEdge) :=
    manuscriptEdge_left_injective_on_label_fiber E z hactual
  have hsubset : fiber.image (fun e : TripleEdge => e.1) ⊆
      coefficients.biUnion parameterVertices := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨heE, hez⟩ := Finset.mem_filter.mp he
    have hedge := hactual e heE
    obtain ⟨_, hrelation, hleftbound, hrightbound, _, _, _, _,
      ⟨a, q, ha, hq, hleftrepr⟩,
      ⟨d, r, hd, hr, hrightrepr⟩⟩ := hedge
    have hapos : 0 < a := Nat.pos_of_dvd_of_pos ha hW
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hW
    have hqleft : q ≤ e.1 := by
      rw [hleftrepr]
      exact Nat.le_mul_of_pos_left q hapos
    have hrright : r ≤ e.2.1 := by
      rw [hrightrepr]
      simpa [mul_assoc] using
        (Nat.le_mul_of_pos_left r (Nat.mul_pos (by norm_num) hdpos))
    have hqn : q ≤ n := by omega
    have hrn : r ≤ n := by omega
    have hequation : 2 * d * r = a * q + z := by omega
    apply Finset.mem_biUnion.mpr
    refine ⟨(a, d), Finset.mem_product.mpr
      ⟨Nat.mem_divisors.mpr ⟨ha, Nat.ne_of_gt hW⟩,
        Nat.mem_divisors.mpr ⟨hd, Nat.ne_of_gt hW⟩⟩, ?_⟩
    apply Finset.mem_image.mpr
    have hqmember : q ∈ labelFiberPrimeParameters n z a d := by
      simp only [labelFiberPrimeParameters, Finset.mem_filter]
      exact ⟨Finset.mem_Icc.mpr ⟨hq.one_le, hqn⟩, hq,
        r, Finset.mem_Icc.mpr ⟨hr.one_le, hrn⟩, hr, hequation⟩
    exact ⟨q, hqmember, hleftrepr.symm⟩
  calc
    fiber.card = (fiber.image fun e : TripleEdge => e.1).card :=
      (Finset.card_image_iff.mpr hinjective).symm
    _ ≤ (coefficients.biUnion parameterVertices).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ c ∈ coefficients, (parameterVertices c).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ c ∈ coefficients,
        (labelFiberPrimeParameters n z c.1 c.2).card := by
      apply Finset.sum_le_sum
      intro c _
      exact Finset.card_image_le

/-- Left-degree reduction preserving the exact support-dependent residue selectors. -/
theorem manuscriptEdge_left_fiber_card_le_switched_parameter_sum
    {S : Finset ℕ} {b : ℕ → ℕ} {n : ℕ} {τ ell : ℝ}
    (E : Finset TripleEdge) (x : ℕ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hactual : ∀ e ∈ E, manuscriptEdge S b n τ ell e) :
    (E.filter fun e => e.1 = x).card ≤
      ∑ d ∈ (∏ s ∈ S, s).divisors,
        (leftFiberSwitchedPrimeParameters S b n x d).card := by
  classical
  let W := ∏ s ∈ S, s
  let fiber := E.filter fun e => e.1 = x
  let parameterVertices : ℕ → Finset ℕ := fun d =>
    (leftFiberSwitchedPrimeParameters S b n x d).image
      (fun q => 2 * d * q)
  have hW : 0 < W := Finset.prod_pos fun s hs => (hsupport s hs).pos
  have hinjective := manuscriptEdge_right_injective_on_left_fiber E x hactual
  have hsubset : fiber.image (fun e : TripleEdge => e.2.1) ⊆
      W.divisors.biUnion parameterVertices := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨heE, hex⟩ := Finset.mem_filter.mp he
    obtain ⟨hlabelprime, hrelation, _, hrightbound, hleftmiss,
      hrightmiss, _, _, _, ⟨d, q, hd, hq, hrepr⟩⟩ := hactual e heE
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hW
    have hqright : q ≤ e.2.1 := by
      rw [hrepr]
      simpa [mul_assoc] using
        (Nat.le_mul_of_pos_left q (Nat.mul_pos (by norm_num) hdpos))
    have hqn : q ≤ n := by omega
    have hlabel : 2 * d * q - x = e.2.2 := by omega
    have hrighttarget : 2 * e.2.1 = 4 * d * q := by
      rw [hrepr]
      ring
    rw [hex] at hleftmiss
    rw [hrighttarget] at hrightmiss
    apply Finset.mem_biUnion.mpr
    refine ⟨d, Nat.mem_divisors.mpr ⟨hd, Nat.ne_of_gt hW⟩, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨q, Finset.mem_filter.mpr ?_, hrepr.symm⟩
    exact ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hq.one_le, hqn⟩,
        hq, hlabel.symm ▸ hlabelprime⟩, hleftmiss, hrightmiss⟩
  calc
    fiber.card = (fiber.image fun e : TripleEdge => e.2.1).card :=
      (Finset.card_image_iff.mpr hinjective).symm
    _ ≤ (W.divisors.biUnion parameterVertices).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ d ∈ W.divisors, (parameterVertices d).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ d ∈ W.divisors,
        (leftFiberSwitchedPrimeParameters S b n x d).card := by
      apply Finset.sum_le_sum
      intro d _
      exact Finset.card_image_le

/-- Right-degree reduction preserving the exact support-dependent residue selectors. -/
theorem manuscriptEdge_right_fiber_card_le_switched_parameter_sum
    {S : Finset ℕ} {b : ℕ → ℕ} {n : ℕ} {τ ell : ℝ}
    (E : Finset TripleEdge) (y : ℕ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hactual : ∀ e ∈ E, manuscriptEdge S b n τ ell e) :
    (E.filter fun e => e.2.1 = y).card ≤
      ∑ a ∈ (∏ s ∈ S, s).divisors,
        (rightFiberSwitchedPrimeParameters S b n y a).card := by
  classical
  let W := ∏ s ∈ S, s
  let fiber := E.filter fun e => e.2.1 = y
  let parameterVertices : ℕ → Finset ℕ := fun a =>
    (rightFiberSwitchedPrimeParameters S b n y a).image
      (fun q => a * q)
  have hW : 0 < W := Finset.prod_pos fun s hs => (hsupport s hs).pos
  have hinjective := manuscriptEdge_left_injective_on_right_fiber E y hactual
  have hsubset : fiber.image (fun e : TripleEdge => e.1) ⊆
      W.divisors.biUnion parameterVertices := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨heE, hey⟩ := Finset.mem_filter.mp he
    obtain ⟨hlabelprime, hrelation, hleftbound, _, hleftmiss,
      hrightmiss, _, _, ⟨a, q, ha, hq, hrepr⟩, _⟩ := hactual e heE
    have hapos : 0 < a := Nat.pos_of_dvd_of_pos ha hW
    have hqleft : q ≤ e.1 := by
      rw [hrepr]
      exact Nat.le_mul_of_pos_left q hapos
    have hqn : q ≤ n := by omega
    have hlabel : y - a * q = e.2.2 := by omega
    have hlefttarget : 2 * e.1 = 2 * a * q := by
      rw [hrepr]
      ring
    rw [hlefttarget] at hleftmiss
    rw [hey] at hrightmiss
    apply Finset.mem_biUnion.mpr
    refine ⟨a, Nat.mem_divisors.mpr ⟨ha, Nat.ne_of_gt hW⟩, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨q, Finset.mem_filter.mpr ?_, hrepr.symm⟩
    exact ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hq.one_le, hqn⟩,
        hq, hlabel.symm ▸ hlabelprime⟩, hleftmiss, hrightmiss⟩
  calc
    fiber.card = (fiber.image fun e : TripleEdge => e.1).card :=
      (Finset.card_image_iff.mpr hinjective).symm
    _ ≤ (W.divisors.biUnion parameterVertices).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ a ∈ W.divisors, (parameterVertices a).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ a ∈ W.divisors,
        (rightFiberSwitchedPrimeParameters S b n y a).card := by
      apply Finset.sum_le_sum
      intro a _
      exact Finset.card_image_le

/-- Label-degree reduction preserving both exact switched-residue selectors. -/
theorem manuscriptEdge_label_fiber_card_le_switched_parameter_sum
    {S : Finset ℕ} {b : ℕ → ℕ} {n : ℕ} {τ ell : ℝ}
    (E : Finset TripleEdge) (z : ℕ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hactual : ∀ e ∈ E, manuscriptEdge S b n τ ell e) :
    (E.filter fun e => e.2.2 = z).card ≤
      ∑ c ∈ ((∏ s ∈ S, s).divisors.product
          (∏ s ∈ S, s).divisors),
        (labelFiberSwitchedPrimeParameters S b n z c.1 c.2).card := by
  classical
  let W := ∏ s ∈ S, s
  let fiber := E.filter fun e => e.2.2 = z
  let coefficients := W.divisors.product W.divisors
  let parameterVertices : (ℕ × ℕ) → Finset ℕ := fun c =>
    (labelFiberSwitchedPrimeParameters S b n z c.1 c.2).image
      (fun q => c.1 * q)
  have hW : 0 < W := Finset.prod_pos fun s hs => (hsupport s hs).pos
  have hinjective := manuscriptEdge_left_injective_on_label_fiber E z hactual
  have hsubset : fiber.image (fun e : TripleEdge => e.1) ⊆
      coefficients.biUnion parameterVertices := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨heE, hez⟩ := Finset.mem_filter.mp he
    obtain ⟨_, hrelation, hleftbound, hrightbound,
      hleftmiss, hrightmiss, _, _,
      ⟨a, q, ha, hq, hleftrepr⟩,
      ⟨d, r, hd, hr, hrightrepr⟩⟩ := hactual e heE
    have hapos : 0 < a := Nat.pos_of_dvd_of_pos ha hW
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hW
    have hqleft : q ≤ e.1 := by
      rw [hleftrepr]
      exact Nat.le_mul_of_pos_left q hapos
    have hrright : r ≤ e.2.1 := by
      rw [hrightrepr]
      simpa [mul_assoc] using
        (Nat.le_mul_of_pos_left r (Nat.mul_pos (by norm_num) hdpos))
    have hqn : q ≤ n := by omega
    have hrn : r ≤ n := by omega
    have hequation : 2 * d * r = a * q + z := by omega
    have hlefttarget : 2 * e.1 = 2 * a * q := by
      rw [hleftrepr]
      ring
    have hrighttarget : 2 * e.2.1 = 2 * (a * q + z) := by omega
    rw [hlefttarget] at hleftmiss
    rw [hrighttarget] at hrightmiss
    apply Finset.mem_biUnion.mpr
    refine ⟨(a, d), Finset.mem_product.mpr
      ⟨Nat.mem_divisors.mpr ⟨ha, Nat.ne_of_gt hW⟩,
        Nat.mem_divisors.mpr ⟨hd, Nat.ne_of_gt hW⟩⟩, ?_⟩
    apply Finset.mem_image.mpr
    have hqmember : q ∈ labelFiberSwitchedPrimeParameters S b n z a d := by
      simp only [labelFiberSwitchedPrimeParameters,
        labelFiberPrimeParameters, Finset.mem_filter]
      exact ⟨⟨Finset.mem_Icc.mpr ⟨hq.one_le, hqn⟩,
        hq, r, Finset.mem_Icc.mpr ⟨hr.one_le, hrn⟩,
          hr, hequation⟩, hleftmiss, hrightmiss⟩
    exact ⟨q, hqmember, hleftrepr.symm⟩
  calc
    fiber.card = (fiber.image fun e : TripleEdge => e.1).card :=
      (Finset.card_image_iff.mpr hinjective).symm
    _ ≤ (coefficients.biUnion parameterVertices).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ c ∈ coefficients, (parameterVertices c).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ c ∈ coefficients,
        (labelFiberSwitchedPrimeParameters S b n z c.1 c.2).card := by
      apply Finset.sum_le_sum
      intro c _
      exact Finset.card_image_le

/-- The exact three selector-preserving two-prime sums needed for global degree. -/
def SelectorPreservingTwoPrimeDegreeEstimate : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (S : Finset ℕ) (b : ℕ → ℕ) (τ ell : ℝ),
      (∀ s ∈ S, s.Prime ∧ 3 < s ∧ b s % s ≠ 0) →
      0 < τ → 0 < ell → τ + ell < 1 / 10 →
        ∀ᶠ n : ℕ in Filter.atTop,
          (∀ x : ℕ,
            (∃ e : TripleEdge, manuscriptEdge S b n τ ell e ∧ e.1 = x) →
              ((∑ d ∈ (∏ s ∈ S, s).divisors,
                (leftFiberSwitchedPrimeParameters S b n x d).card : ℕ) : ℝ) ≤
                  C * n / (Real.log n) ^ 2) ∧
          (∀ y : ℕ,
            (∃ e : TripleEdge, manuscriptEdge S b n τ ell e ∧ e.2.1 = y) →
              ((∑ a ∈ (∏ s ∈ S, s).divisors,
                (rightFiberSwitchedPrimeParameters S b n y a).card : ℕ) : ℝ) ≤
                  C * n / (Real.log n) ^ 2) ∧
          (∀ z : ℕ,
            (∃ e : TripleEdge, manuscriptEdge S b n τ ell e ∧ e.2.2 = z) →
              ((∑ c ∈ ((∏ s ∈ S, s).divisors.product
                    (∏ s ∈ S, s).divisors),
                (labelFiberSwitchedPrimeParameters
                  S b n z c.1 c.2).card : ℕ) : ℝ) ≤
                    C * n / (Real.log n) ^ 2)

/-- Bounding those exact analytic sums proves the entire unrestricted degree input. -/
theorem fixedModulusTwoFormDegreeBound_of_selector_preserving_estimate
    (hestimate : SelectorPreservingTwoPrimeDegreeEstimate) :
    FixedModulusTwoFormDegreeBound := by
  obtain ⟨C, hC, hestimate⟩ := hestimate
  refine ⟨C, hC, ?_⟩
  intro S b τ ell hsupport hτ hell hstrip
  have hprimes : ∀ s ∈ S, s.Prime := fun s hs => (hsupport s hs).1
  filter_upwards [hestimate S b τ ell hsupport hτ hell hstrip] with n hn
  intro E hactual
  refine ⟨?_, ?_, ?_⟩
  · intro x
    by_cases hnonempty : (E.filter fun e => e.1 = x).Nonempty
    · obtain ⟨e, he⟩ := hnonempty
      obtain ⟨heE, hex⟩ := Finset.mem_filter.mp he
      have hfinite := manuscriptEdge_left_fiber_card_le_switched_parameter_sum
        E x hprimes hactual
      have hreal :
          ((E.filter fun f => f.1 = x).card : ℝ) ≤
            ((∑ d ∈ (∏ s ∈ S, s).divisors,
              (leftFiberSwitchedPrimeParameters S b n x d).card : ℕ) : ℝ) := by
        exact_mod_cast hfinite
      exact hreal.trans (hn.1 x ⟨e, hactual e heE, hex⟩)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hnonempty]
      simp
      positivity
  · intro y
    by_cases hnonempty : (E.filter fun e => e.2.1 = y).Nonempty
    · obtain ⟨e, he⟩ := hnonempty
      obtain ⟨heE, hey⟩ := Finset.mem_filter.mp he
      have hfinite := manuscriptEdge_right_fiber_card_le_switched_parameter_sum
        E y hprimes hactual
      have hreal :
          ((E.filter fun f => f.2.1 = y).card : ℝ) ≤
            ((∑ a ∈ (∏ s ∈ S, s).divisors,
              (rightFiberSwitchedPrimeParameters S b n y a).card : ℕ) : ℝ) := by
        exact_mod_cast hfinite
      exact hreal.trans (hn.2.1 y ⟨e, hactual e heE, hey⟩)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hnonempty]
      simp
      positivity
  · intro z
    by_cases hnonempty : (E.filter fun e => e.2.2 = z).Nonempty
    · obtain ⟨e, he⟩ := hnonempty
      obtain ⟨heE, hez⟩ := Finset.mem_filter.mp he
      have hfinite := manuscriptEdge_label_fiber_card_le_switched_parameter_sum
        E z hprimes hactual
      have hreal :
          ((E.filter fun f => f.2.2 = z).card : ℝ) ≤
            ((∑ c ∈ ((∏ s ∈ S, s).divisors.product
                  (∏ s ∈ S, s).divisors),
              (labelFiberSwitchedPrimeParameters
                S b n z c.1 c.2).card : ℕ) : ℝ) := by
        exact_mod_cast hfinite
      exact hreal.trans (hn.2.2 z ⟨e, hactual e heE, hez⟩)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hnonempty]
      simp
      positivity

end Erdos689

#print axioms Erdos689.manuscriptEdge_right_injective_on_left_fiber
#print axioms Erdos689.manuscriptEdge_left_injective_on_right_fiber
#print axioms Erdos689.manuscriptEdge_left_injective_on_label_fiber
#print axioms Erdos689.manuscriptEdge_left_fiber_card_le_prime_parameter_sum
#print axioms Erdos689.manuscriptEdge_right_fiber_card_le_prime_parameter_sum
#print axioms Erdos689.manuscriptEdge_label_fiber_card_le_prime_parameter_sum
#print axioms Erdos689.manuscriptEdge_left_fiber_card_le_switched_parameter_sum
#print axioms Erdos689.manuscriptEdge_right_fiber_card_le_switched_parameter_sum
#print axioms Erdos689.manuscriptEdge_label_fiber_card_le_switched_parameter_sum
#print axioms Erdos689.fixedModulusTwoFormDegreeBound_of_selector_preserving_estimate
