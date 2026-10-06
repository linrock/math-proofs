module

public import SeedFirstPathFill1105
public import ResidualForestStar1105
public import ActualInducedDegree1105
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.FinCases
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
Generalization of the whole-support vertex-cover construction from `h = 3`
(`|K| = d + 3`) to all small kernels `4 ≤ h ≤ d` (`d + 4 ≤ |K| ≤ 2 * d`),
and elimination of the entire `|K| ≤ 2 * d` regime for connected representatives.
-/

noncomputable section

namespace ErdosProblems.PathUpperReduction.SmallKernelWholeSupport1105

open SimpleGraph
open ErdosProblems.PathUpperReduction
open ErdosProblems.PathUpperReduction.CountCoreBasis
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.ActualInducedDegree1105
open ErdosProblems.PathUpperReduction.FixedCarrierFillGuards1105
open ErdosProblems.PathUpperReduction.SeedFirstPathFill1105
open ErdosProblems.PathUpperReduction.ResidualForestStar1105

local instance (priority := 100) carrierDecidableEq (V : Type*) : DecidableEq V :=
  Classical.decEq V

local instance (priority := 100) carrierDecidableAdj {V : Type*} (G : SimpleGraph V) :
    DecidableRel G.Adj := fun _ _ => Classical.propDecidable _

/-- General weaving lemma: an injective path of length `L ≥ 1` outside a universal
subset `U` of size `k` with `L + 2 * k = N` extends to a spanning `P_N`. -/
theorem spanning_path_of_residual_path {N L k : ℕ}
    (_hL : 1 ≤ L) (hN : L + 2 * k = N)
    (G : SimpleGraph (Fin N)) (U : Finset (Fin N)) (hU : U.card = k)
    (huniv : ∀ u ∈ U, ∀ v, u ≠ v → G.Adj u v)
    (p : Fin L → Fin N) (hpinj : Function.Injective p)
    (hpnotU : ∀ i : Fin L, p i ∉ U)
    (hpadj : ∀ (i j : Fin L), i.val + 1 = j.val → G.Adj (p i) (p j)) :
    (pathGraph N).IsContained G := by
  classical
  let A : Finset (Fin N) := Finset.univ.image p
  have hAcard : A.card = L := by
    rw [Finset.card_image_of_injective _ hpinj, Finset.card_univ, Fintype.card_fin]
  have hpA (i : Fin L) : p i ∈ A :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hUA : Disjoint U A := by
    apply Finset.disjoint_left.mpr
    intro v hvU hvA
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hvA
    exact hpnotU i hvU
  let T : Finset (Fin N) := Finset.univ \ (U ∪ A)
  have hTcard : T.card = k := by
    dsimp [T]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin, Finset.card_union_of_disjoint hUA,
      hU, hAcard]
    omega
  let ew : Fin k ≃ U := (Finset.equivFinOfCardEq hU).symm
  let et : Fin k ≃ T := (Finset.equivFinOfCardEq hTcard).symm
  let w : Fin k → Fin N := fun i => (ew i).val
  let t : Fin k → Fin N := fun i => (et i).val
  have hwinj : Function.Injective w := Subtype.val_injective.comp ew.injective
  have htinj : Function.Injective t := Subtype.val_injective.comp et.injective
  have hwU (i : Fin k) : w i ∈ U := (ew i).property
  have htT (i : Fin k) : t i ∈ T := (et i).property
  have htU (i : Fin k) : t i ∉ U := by
    have hn := (Finset.mem_sdiff.mp (htT i)).2
    exact fun hm => hn (Finset.mem_union.mpr (Or.inl hm))
  have htA (i : Fin k) : t i ∉ A := by
    have hn := (Finset.mem_sdiff.mp (htT i)).2
    exact fun hm => hn (Finset.mem_union.mpr (Or.inr hm))
  have hpw (i : Fin L) (j : Fin k) : p i ≠ w j := by
    intro he
    exact hpnotU i (he.symm ▸ hwU j)
  have hpt (i : Fin L) (j : Fin k) : p i ≠ t j := by
    intro he
    exact htA j (he ▸ hpA i)
  have hwt (i j : Fin k) : w i ≠ t j := by
    intro he
    exact htU j (he ▸ hwU i)
  let ix (i : Fin N) (hi : ¬ i.val < L) : Fin k :=
    ⟨(i.val - L) / 2, by have hi := i.isLt; omega⟩
  let q : Fin N → Fin N := fun i =>
    if hi : i.val < L then p ⟨i.val, hi⟩
    else if (i.val - L) % 2 = 0 then w (ix i hi) else t (ix i hi)
  have hqP (i : Fin N) (hi : i.val < L) :
      q i = p ⟨i.val, hi⟩ := by simp only [q, dite_eq_left hi]
  have hqW (i : Fin N) (hi : ¬ i.val < L)
      (hr : (i.val - L) % 2 = 0) : q i = w (ix i hi) := by
    simp only [q, dite_eq_right hi, ite_eq_left hr]
  have hqT (i : Fin N) (hi : ¬ i.val < L)
      (hr : ¬ (i.val - L) % 2 = 0) : q i = t (ix i hi) := by
    simp only [q, dite_eq_right hi, ite_eq_right hr]
  have hqinj : Function.Injective q := by
    intro i j he
    by_cases hi : i.val < L
    · by_cases hj : j.val < L
      · rw [hqP i hi, hqP j hj] at he
        exact Fin.ext (congrArg (fun x : Fin L => x.val) (hpinj he))
      · by_cases hjr : (j.val - L) % 2 = 0
        · rw [hqP i hi, hqW j hj hjr] at he
          exact (hpw _ _ he).elim
        · rw [hqP i hi, hqT j hj hjr] at he
          exact (hpt _ _ he).elim
    · by_cases hj : j.val < L
      · by_cases hir : (i.val - L) % 2 = 0
        · rw [hqW i hi hir, hqP j hj] at he
          exact (hpw _ _ he.symm).elim
        · rw [hqT i hi hir, hqP j hj] at he
          exact (hpt _ _ he.symm).elim
      · by_cases hir : (i.val - L) % 2 = 0
        · by_cases hjr : (j.val - L) % 2 = 0
          · rw [hqW i hi hir, hqW j hj hjr] at he
            have hix := congrArg Fin.val (hwinj he)
            change (i.val - L) / 2 = (j.val - L) / 2 at hix
            apply Fin.ext
            omega
          · rw [hqW i hi hir, hqT j hj hjr] at he
            exact (hwt _ _ he).elim
        · by_cases hjr : (j.val - L) % 2 = 0
          · rw [hqT i hi hir, hqW j hj hjr] at he
            exact (hwt _ _ he.symm).elim
          · rw [hqT i hi hir, hqT j hj hjr] at he
            have hix := congrArg Fin.val (htinj he)
            change (i.val - L) / 2 = (j.val - L) / 2 at hix
            have him := Nat.mod_lt (i.val - L) (by omega : 0 < 2)
            have hjm := Nat.mod_lt (j.val - L) (by omega : 0 < 2)
            apply Fin.ext
            omega
  have hforward (i j : Fin N) (hij : i.val + 1 = j.val) :
      G.Adj (q i) (q j) := by
    have hne : q i ≠ q j := by
      intro he
      have hv := congrArg Fin.val (hqinj he)
      omega
    by_cases hi : i.val < L
    · by_cases hj : j.val < L
      · rw [hqP i hi, hqP j hj]
        exact hpadj ⟨i.val, hi⟩ ⟨j.val, hj⟩ hij
      · have hjr : (j.val - L) % 2 = 0 := by omega
        have hadj := huniv (w (ix j hj)) (hwU _) (q i) (by
          rw [← hqW j hj hjr]
          exact Ne.symm hne)
        rw [hqW j hj hjr]
        exact hadj.symm
    · have hj : ¬ j.val < L := by omega
      by_cases hir : (i.val - L) % 2 = 0
      · have hadj := huniv (w (ix i hi)) (hwU _) (q j) (by
          rw [← hqW i hi hir]
          exact hne)
        rw [hqW i hi hir]
        exact hadj
      · have hjr : (j.val - L) % 2 = 0 := by
          have him := Nat.mod_lt (i.val - L) (by omega : 0 < 2)
          omega
        have hadj := huniv (w (ix j hj)) (hwU _) (q i) (by
          rw [← hqW j hj hjr]
          exact Ne.symm hne)
        rw [hqW j hj hjr]
        exact hadj.symm
  let f : (pathGraph N) →g G := ⟨q, by
    intro i j hij
    rcases pathGraph_adj.mp hij with h | h
    · exact hforward i j h
    · exact (hforward j i h).symm⟩
  exact ⟨⟨f, hqinj⟩⟩

/-- An injective `P_3 + P_2` outside `W` (`|W| = d - 1`) in a graph where `W` is
universal yields a spanning `P_{2d+2}`. -/
theorem spanning_path_of_residual_p3_p2 {d : ℕ} (hd : 3 ≤ d)
    (G : SimpleGraph (Fin (2 * d + 2))) (W : Finset (Fin (2 * d + 2)))
    (hW : W.card = d - 1)
    (huniv : ∀ w ∈ W, ∀ v, w ≠ v → G.Adj w v)
    (p : Fin 5 → Fin (2 * d + 2)) (hpinj : Function.Injective p)
    (hpnotW : ∀ i : Fin 5, p i ∉ W)
    (h01 : G.Adj (p 0) (p 1)) (h12 : G.Adj (p 1) (p 2)) (h34 : G.Adj (p 3) (p 4)) :
    (pathGraph (2 * d + 2)).IsContained G := by
  classical
  obtain ⟨w0, hw0⟩ := Finset.card_pos.mp (by omega : 0 < W.card)
  let U : Finset (Fin (2 * d + 2)) := W.erase w0
  have hUcard : U.card = d - 2 := by
    dsimp [U]
    rw [Finset.card_erase_of_mem hw0, hW]
    omega
  have hUuniv : ∀ u ∈ U, ∀ v, u ≠ v → G.Adj u v := by
    intro u hu v hne
    exact huniv u (Finset.mem_erase.mp hu).2 v hne
  have hpw0 (i : Fin 5) : p i ≠ w0 := by
    intro he
    exact hpnotW i (he.symm ▸ hw0)
  let p6 : Fin 6 → Fin (2 * d + 2) := ![p 0, p 1, p 2, w0, p 3, p 4]
  have hp6inj : Function.Injective p6 := by
    intro i j he
    have h01ne : p 0 ≠ p 1 := fun h => by have := hpinj h; revert this; decide
    have h02ne : p 0 ≠ p 2 := fun h => by have := hpinj h; revert this; decide
    have h03ne : p 0 ≠ p 3 := fun h => by have := hpinj h; revert this; decide
    have h04ne : p 0 ≠ p 4 := fun h => by have := hpinj h; revert this; decide
    have h12ne : p 1 ≠ p 2 := fun h => by have := hpinj h; revert this; decide
    have h13ne : p 1 ≠ p 3 := fun h => by have := hpinj h; revert this; decide
    have h14ne : p 1 ≠ p 4 := fun h => by have := hpinj h; revert this; decide
    have h23ne : p 2 ≠ p 3 := fun h => by have := hpinj h; revert this; decide
    have h24ne : p 2 ≠ p 4 := fun h => by have := hpinj h; revert this; decide
    have h34ne : p 3 ≠ p 4 := fun h => by have := hpinj h; revert this; decide
    have hw00 := hpw0 0; have hw01 := hpw0 1; have hw02 := hpw0 2
    have hw03 := hpw0 3; have hw04 := hpw0 4
    fin_cases i <;> fin_cases j <;>
      simp [p6, h01ne, h01ne.symm, h02ne, h02ne.symm, h03ne, h03ne.symm,
        h04ne, h04ne.symm, h12ne, h12ne.symm, h13ne, h13ne.symm,
        h14ne, h14ne.symm, h23ne, h23ne.symm, h24ne, h24ne.symm,
        h34ne, h34ne.symm, hw00, hw00.symm, hw01, hw01.symm,
        hw02, hw02.symm, hw03, hw03.symm, hw04, hw04.symm] at he ⊢
  have hp6notU : ∀ i : Fin 6, p6 i ∉ U := by
    intro i
    have hn0 := hpnotW 0; have hn1 := hpnotW 1; have hn2 := hpnotW 2
    have hn3 := hpnotW 3; have hn4 := hpnotW 4
    fin_cases i <;> simp [p6, U, hn0, hn1, hn2, hn3, hn4]
  have hp6adj : ∀ (i j : Fin 6), i.val + 1 = j.val → G.Adj (p6 i) (p6 j) := by
    have h2w : G.Adj (p 2) w0 := (huniv w0 hw0 (p 2) (hpw0 2).symm).symm
    have hw3 : G.Adj w0 (p 3) := huniv w0 hw0 (p 3) (hpw0 3).symm
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [p6]
  exact spanning_path_of_residual_path (by omega) (by omega) G U hUcard hUuniv
    p6 hp6inj hp6notU hp6adj

/-- Three vertex-disjoint edges outside `W` (`|W| = d - 1`) in a graph where `W`
is universal yield a spanning `P_{2d+2}`. -/
theorem spanning_path_of_residual_3p2 {d : ℕ} (hd : 3 ≤ d)
    (G : SimpleGraph (Fin (2 * d + 2))) (W : Finset (Fin (2 * d + 2)))
    (hW : W.card = d - 1)
    (huniv : ∀ w ∈ W, ∀ v, w ≠ v → G.Adj w v)
    (p : Fin 6 → Fin (2 * d + 2)) (hpinj : Function.Injective p)
    (hpnotW : ∀ i : Fin 6, p i ∉ W)
    (h01 : G.Adj (p 0) (p 1)) (h23 : G.Adj (p 2) (p 3)) (h45 : G.Adj (p 4) (p 5)) :
    (pathGraph (2 * d + 2)).IsContained G := by
  classical
  obtain ⟨w0, hw0⟩ := Finset.card_pos.mp (by omega : 0 < W.card)
  let W1 : Finset (Fin (2 * d + 2)) := W.erase w0
  have hW1card : W1.card = d - 2 := by
    dsimp [W1]
    rw [Finset.card_erase_of_mem hw0, hW]
    omega
  obtain ⟨w1, hw1W1⟩ := Finset.card_pos.mp (by omega : 0 < W1.card)
  have hw1ne0 : w1 ≠ w0 := (Finset.mem_erase.mp hw1W1).1
  have hw1 : w1 ∈ W := (Finset.mem_erase.mp hw1W1).2
  let U : Finset (Fin (2 * d + 2)) := W1.erase w1
  have hUcard : U.card = d - 3 := by
    dsimp [U]
    rw [Finset.card_erase_of_mem hw1W1, hW1card]
    omega
  have hUuniv : ∀ u ∈ U, ∀ v, u ≠ v → G.Adj u v := by
    intro u hu v hne
    exact huniv u (Finset.mem_erase.mp (Finset.mem_erase.mp hu).2).2 v hne
  have hpw0 (i : Fin 6) : p i ≠ w0 := fun he => hpnotW i (he.symm ▸ hw0)
  have hpw1 (i : Fin 6) : p i ≠ w1 := fun he => hpnotW i (he.symm ▸ hw1)
  let p8 : Fin 8 → Fin (2 * d + 2) := ![p 0, p 1, w0, p 2, p 3, w1, p 4, p 5]
  have hp8inj : Function.Injective p8 := by
    intro i j he
    have h01ne : p 0 ≠ p 1 := fun h => by have := hpinj h; revert this; decide
    have h02ne : p 0 ≠ p 2 := fun h => by have := hpinj h; revert this; decide
    have h03ne : p 0 ≠ p 3 := fun h => by have := hpinj h; revert this; decide
    have h04ne : p 0 ≠ p 4 := fun h => by have := hpinj h; revert this; decide
    have h05ne : p 0 ≠ p 5 := fun h => by have := hpinj h; revert this; decide
    have h12ne : p 1 ≠ p 2 := fun h => by have := hpinj h; revert this; decide
    have h13ne : p 1 ≠ p 3 := fun h => by have := hpinj h; revert this; decide
    have h14ne : p 1 ≠ p 4 := fun h => by have := hpinj h; revert this; decide
    have h15ne : p 1 ≠ p 5 := fun h => by have := hpinj h; revert this; decide
    have h23ne : p 2 ≠ p 3 := fun h => by have := hpinj h; revert this; decide
    have h24ne : p 2 ≠ p 4 := fun h => by have := hpinj h; revert this; decide
    have h25ne : p 2 ≠ p 5 := fun h => by have := hpinj h; revert this; decide
    have h34ne : p 3 ≠ p 4 := fun h => by have := hpinj h; revert this; decide
    have h35ne : p 3 ≠ p 5 := fun h => by have := hpinj h; revert this; decide
    have h45ne : p 4 ≠ p 5 := fun h => by have := hpinj h; revert this; decide
    have hw00 := hpw0 0; have hw01 := hpw0 1; have hw02 := hpw0 2
    have hw03 := hpw0 3; have hw04 := hpw0 4; have hw05 := hpw0 5
    have hw10 := hpw1 0; have hw11 := hpw1 1; have hw12 := hpw1 2
    have hw13 := hpw1 3; have hw14 := hpw1 4; have hw15 := hpw1 5
    fin_cases i <;> fin_cases j <;>
      simp [p8, h01ne, h01ne.symm, h02ne, h02ne.symm, h03ne, h03ne.symm,
        h04ne, h04ne.symm, h05ne, h05ne.symm, h12ne, h12ne.symm,
        h13ne, h13ne.symm, h14ne, h14ne.symm, h15ne, h15ne.symm,
        h23ne, h23ne.symm, h24ne, h24ne.symm, h25ne, h25ne.symm,
        h34ne, h34ne.symm, h35ne, h35ne.symm, h45ne, h45ne.symm,
        hw00, hw00.symm, hw01, hw01.symm, hw02, hw02.symm,
        hw03, hw03.symm, hw04, hw04.symm, hw05, hw05.symm,
        hw10, hw10.symm, hw11, hw11.symm, hw12, hw12.symm,
        hw13, hw13.symm, hw14, hw14.symm, hw15, hw15.symm,
        hw1ne0, hw1ne0.symm] at he ⊢
  have hp8notU : ∀ i : Fin 8, p8 i ∉ U := by
    intro i
    have hn0 := hpnotW 0; have hn1 := hpnotW 1; have hn2 := hpnotW 2
    have hn3 := hpnotW 3; have hn4 := hpnotW 4; have hn5 := hpnotW 5
    fin_cases i <;> simp [p8, U, W1, hn0, hn1, hn2, hn3, hn4, hn5]
  have hp8adj : ∀ (i j : Fin 8), i.val + 1 = j.val → G.Adj (p8 i) (p8 j) := by
    have h1w0 : G.Adj (p 1) w0 := (huniv w0 hw0 (p 1) (hpw0 1).symm).symm
    have hw02 : G.Adj w0 (p 2) := huniv w0 hw0 (p 2) (hpw0 2).symm
    have h3w1 : G.Adj (p 3) w1 := (huniv w1 hw1 (p 3) (hpw1 3).symm).symm
    have hw14 : G.Adj w1 (p 4) := huniv w1 hw1 (p 4) (hpw1 4).symm
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [p8]
  exact spanning_path_of_residual_path (by omega) (by omega) G U hUcard hUuniv
    p8 hp8inj hp8notU hp8adj

section StarCenter

local instance (priority := 3000) subtypeNeighborSetFintype {A : Type*} [Fintype A]
    (G : SimpleGraph A) [DecidableRel G.Adj] (x : A) : Fintype (G.neighborSet x) :=
  Subtype.fintype (Membership.mem (G.neighborSet x))

/-- Every vertex in `K \ W` has at least one neighbor in `K \ W` because its degree
in `K` is at least `d` and `|W| = d - 1`. -/
theorem residual_min_degree_one {V : Type*} [Fintype V]
    (G : SimpleGraph V) (d : ℕ) (K W : Finset V)
    (hd : 1 ≤ d) (hWcard : W.card = d - 1)
    (hseed : ∀ x ∈ K, d ≤ withinDegree G K x) :
    ∀ u : (↑(K \ W) : Set V),
      1 ≤ (G.induce (↑(K \ W) : Set V)).degree u := by
  intro u
  have huK : u.val ∈ K := (Finset.mem_sdiff.mp u.property).1
  have hdegK : d ≤ (K.filter (G.Adj u.val)).card := hseed u.val huK
  have hsub : K.filter (G.Adj u.val) ⊆ W ∪ (K \ W).filter (G.Adj u.val) := by
    intro z hz
    obtain ⟨hzK, huz⟩ := Finset.mem_filter.mp hz
    by_cases hzW : z ∈ W
    · exact Finset.mem_union.mpr (Or.inl hzW)
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨hzK, hzW⟩, huz⟩))
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hpos : 0 < ((K \ W).filter (G.Adj u.val)).card := by omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
  obtain ⟨hzR, huz⟩ := Finset.mem_filter.mp hz
  have hadj : (G.induce (↑(K \ W) : Set V)).Adj u ⟨z, hzR⟩ := huz
  exact hadj.degree_pos_left

end StarCenter

/-- When `b ∈ K \ W` is adjacent in `G` to every vertex of `(K \ W) \ {b}`, adding
`W × K` pairs is identical to adding `(insert b W) × K` pairs. -/
theorem fillSeedPairs_insert_center_eq {n : ℕ}
    (G : SimpleGraph (Fin n)) (K W : Finset (Fin n)) (b : Fin n)
    (hb : b ∈ K \ W) (hcenter : ∀ x ∈ K \ W, x ≠ b → G.Adj b x) :
    fillSeedPairs G K (insert b W) = fillSeedPairs G K W := by
  classical
  have hbK : b ∈ K := (Finset.mem_sdiff.mp hb).1
  apply le_antisymm
  · apply sup_le le_sup_left
    intro u v huv
    change (fillSeedPairs G K W).Adj u v
    obtain ⟨⟨w, hw, x, hxK, hne, heq⟩, _⟩ := (SimpleGraph.fromEdgeSet_adj _).mp huv
    rcases Finset.mem_insert.mp hw with rfl | hwW
    · by_cases hxW : x ∈ W
      · have hadj : (fillSeedPairs G K W).Adj x w :=
          filled_seed_adj G K W x w hxW hbK hne.symm
        rcases Sym2.eq_iff.mp heq with h | h
        · simpa only [h.1, h.2] using (fillSeedPairs G K W).adj_symm hadj
        · simpa only [h.1, h.2] using hadj
      · have hxKW : x ∈ K \ W := Finset.mem_sdiff.mpr ⟨hxK, hxW⟩
        have hadjG : G.Adj w x := hcenter x hxKW hne.symm
        have hadj : (fillSeedPairs G K W).Adj w x :=
          (le_sup_left : G ≤ fillSeedPairs G K W) hadjG
        rcases Sym2.eq_iff.mp heq with h | h
        · simpa only [h.1, h.2] using hadj
        · simpa only [h.1, h.2] using (fillSeedPairs G K W).adj_symm hadj
    · have hadj : (fillSeedPairs G K W).Adj w x :=
        filled_seed_adj G K W w x hwW hxK hne
      rcases Sym2.eq_iff.mp heq with h | h
      · simpa only [h.1, h.2] using hadj
      · simpa only [h.1, h.2] using (fillSeedPairs G K W).adj_symm hadj
  · apply sup_le le_sup_left
    intro u v huv
    change (fillSeedPairs G K (insert b W)).Adj u v
    obtain ⟨⟨w, hwW, x, hxK, hne, heq⟩, _⟩ := (SimpleGraph.fromEdgeSet_adj _).mp huv
    have hadj : (fillSeedPairs G K (insert b W)).Adj w x :=
      filled_seed_adj G K (insert b W) w x (Finset.mem_insert_of_mem hwW) hxK hne
    rcases Sym2.eq_iff.mp heq with h | h
    · simpa only [h.1, h.2] using hadj
    · simpa only [h.1, h.2] using (fillSeedPairs G K (insert b W)).adj_symm hadj

/-! ### Additive-guard generalizations (valid for all `h ≥ 3`, including `h = d + 1, d + 2`) -/

/-- Additive-guard version of `restoration_pair_guard`: no upper bound `h ≤ d` is needed. -/
theorem restoration_pair_guard_additive {d h : ℕ}
    (G J : SimpleGraph (Fin (2 * d + 2)))
    (K W : Finset (Fin (2 * d + 2))) (w x : Fin (2 * d + 2))
    (hlow : 3 ≤ h) (horder : K.card = d + h) (hWK : W ⊆ K)
    (hw : w ∈ W) (hfill : fillSeedPairs G K W ≤ J)
    (hpeeled : d + 2 ≤ G.degree x + h) :
    2 * d + 2 - 1 ≤ J.degree w + J.degree x := by
  have hGJ : G ≤ J := le_trans le_sup_left hfill
  have hwdegree := seed_fill_degree_lower G J K W w hw (hWK hw) hfill
  rw [horder] at hwdegree
  have hxdegree : G.degree x ≤ J.degree x := G.degree_le_of_le (v := x) hGJ
  omega

/-- An edge outside a size-`d` universal set `H` (`3 ≤ d`) extends to a spanning `P_{2d+2}`. -/
theorem spanning_path_of_residual_edge_ge_three {d : ℕ} (hd : 3 ≤ d)
    (G : SimpleGraph (Fin (2 * d + 2))) (H : Finset (Fin (2 * d + 2)))
    (hHcard : H.card = d)
    (huniv : ∀ h ∈ H, ∀ x, h ≠ x → G.Adj h x)
    (u v : Fin (2 * d + 2)) (hu : u ∉ H) (hv : v ∉ H)
    (hEdge : G.Adj u v) : (pathGraph (2 * d + 2)).IsContained G := by
  classical
  have huv : u ≠ v := hEdge.ne
  obtain ⟨h0, hh0⟩ := Finset.card_pos.mp (by omega : 0 < H.card)
  let W : Finset (Fin (2 * d + 2)) := H.erase h0
  have hWcard : W.card = d - 1 := by
    dsimp only [W]
    rw [Finset.card_erase_of_mem hh0, hHcard]
  have hWuniv : ∀ w ∈ W, ∀ x, w ≠ x → G.Adj w x := by
    intro w hw x hne
    exact huniv w (Finset.mem_erase.mp hw).2 x hne
  let R : Finset (Fin (2 * d + 2)) := Finset.univ \ H
  have hRcard : R.card = d + 2 := by
    dsimp only [R]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin, hHcard]
    omega
  have huR : u ∈ R := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hu⟩
  have hvR : v ∈ R := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩
  have hvErase : v ∈ R.erase u := Finset.mem_erase.mpr ⟨huv.symm, hvR⟩
  let T : Finset (Fin (2 * d + 2)) := (R.erase u).erase v
  have hTcard : T.card = d := by
    dsimp only [T]
    rw [Finset.card_erase_of_mem hvErase, Finset.card_erase_of_mem huR, hRcard]
    omega
  obtain ⟨z, hzT⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  have hzv : z ≠ v := (Finset.mem_erase.mp hzT).1
  have hzEu : z ∈ R.erase u := (Finset.mem_erase.mp hzT).2
  have hzu : z ≠ u := (Finset.mem_erase.mp hzEu).1
  have hzR : z ∈ R := (Finset.mem_erase.mp hzEu).2
  have hzH : z ∉ H := (Finset.mem_sdiff.mp hzR).2
  have huh0 : u ≠ h0 := fun he => hu (he.symm ▸ hh0)
  have hvh0 : v ≠ h0 := fun he => hv (he.symm ▸ hh0)
  have hzh0 : z ≠ h0 := fun he => hzH (he.symm ▸ hh0)
  let p : Fin 4 → Fin (2 * d + 2) := ![u, v, h0, z]
  have hpinj : Function.Injective p := by
    intro i j he
    fin_cases i <;> fin_cases j <;>
      simp [p, huv, huv.symm, huh0, huh0.symm, hzu, hzu.symm,
        hvh0, hvh0.symm, hzv, hzv.symm, hzh0, hzh0.symm] at he ⊢
  have hpnotW : ∀ i : Fin 4, p i ∉ W := by
    intro i
    fin_cases i <;> simp [p, W, hu, hv, hzH]
  have hpadj : ∀ (i j : Fin 4), i.val + 1 = j.val → G.Adj (p i) (p j) := by
    have h12 : G.Adj v h0 := (huniv h0 hh0 v hvh0.symm).symm
    have h23 : G.Adj h0 z := huniv h0 hh0 z hzh0.symm
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [p]
  exact spanning_path_of_residual_path (by omega) (by omega) G W hWcard hWuniv
    p hpinj hpnotW hpadj

/-- Additive-guard single restoration step. -/
theorem path_free_after_missing_restoration_pair_additive {d h : ℕ}
    (hd : 3 ≤ d) (hlow : 3 ≤ h) (G J : SimpleGraph (Fin (2 * d + 2)))
    (K W : Finset (Fin (2 * d + 2))) (w x : Fin (2 * d + 2))
    (horder : K.card = d + h) (hWK : W ⊆ K)
    (hw : w ∈ W) (hx : x ∉ K)
    (hfill : fillSeedPairs G K W ≤ J)
    (hpeeled : d + 2 ≤ G.degree x + h)
    (hfree : (pathGraph (2 * d + 2)).Free J) (hmissing : ¬ J.Adj w x) :
    (pathGraph (2 * d + 2)).Free
      (ErdosProblems.PathSpanningNonedgeDeficit.augment J w x) := by
  have hne : w ≠ x := fun heq => hx (heq ▸ hWK hw)
  exact GenericPathMissingPairClosure1105.pathGraph_free_after_adding_missing_pair
    (by omega) J hfree w x hne hmissing
    (restoration_pair_guard_additive G J K W w x hlow horder hWK hw hfill hpeeled)

/-- Additive-guard two-phase seed-first path filling on `Fin (2*d+2)`, valid for all `h ≥ 3`. -/
theorem seed_first_path_free_additive {d h : ℕ} (hd : 3 ≤ d) (hlow : 3 ≤ h)
    (G : SimpleGraph (Fin (2 * d + 2)))
    (K W : Finset (Fin (2 * d + 2))) (horder : K.card = d + h) (hWK : W ⊆ K)
    (hmin : ∀ v ∈ K, d ≤ originalSeedDegree G K v)
    (hhigh : ∀ w ∈ W, d + 1 ≤ originalSeedDegree G K w)
    (hrestored : ∀ x, x ∉ K → d + 2 ≤ G.degree x + h)
    (hfree : (pathGraph (2 * d + 2)).Free G) :
    (pathGraph (2 * d + 2)).Free (seedFirstFilled G K W) ∧
      G ≤ seedFirstFilled G K W ∧
      (∀ w ∈ W, ∀ v, w ≠ v → (seedFirstFilled G K W).Adj w v) ∧
      (∀ u, u ∉ W → ∀ v, v ∉ W →
        ((seedFirstFilled G K W).Adj u v ↔ G.Adj u v)) := by
  classical
  have hfirst : (pathGraph (2 * d + 2)).Free (seedFilled G K W) := by
    have haux : ∀ L : List (Fin (2 * d + 2) × Fin (2 * d + 2)),
        (∀ p ∈ L, p ∈ seedPairs K W) →
        ∀ J : SimpleGraph (Fin (2 * d + 2)), G ≤ J →
          (pathGraph (2 * d + 2)).Free J →
          (pathGraph (2 * d + 2)).Free (fillOrdered J L) := by
      intro L
      induction L with
      | nil => intro _ J _ hfreeJ; exact hfreeJ
      | cons p ps ih =>
          intro hmem J hGJ hfreeJ
          have hp : p ∈ seedPairs K W := hmem p (by simp)
          simp only [seedPairs, Finset.mem_filter, Finset.mem_product] at hp
          obtain ⟨⟨hw, hv⟩, hne⟩ := hp
          have hstep : (pathGraph (2 * d + 2)).Free
              (ErdosProblems.PathSpanningNonedgeDeficit.augment J p.1 p.2) := by
            by_cases hadj : J.Adj p.1 p.2
            · have heq : ErdosProblems.PathSpanningNonedgeDeficit.augment J p.1 p.2 = J := by
                apply le_antisymm _ le_sup_left
                apply sup_le le_rfl
                intro x y hxy
                obtain ⟨hpair, _⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
                rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp hpair) with h | h
                · simpa only [h.1, h.2] using hadj
                · simpa only [h.1, h.2] using J.adj_symm hadj
              simpa only [heq] using hfreeJ
            · exact GenericPathMissingPairClosure1105.pathGraph_free_after_adding_missing_pair
                (by omega) J hfreeJ p.1 p.2 hne hadj
                (seed_pair_guard G J K p.1 p.2 hGJ (hhigh p.1 hw) (hmin p.2 hv))
          exact ih (fun q hq => hmem q (List.mem_cons_of_mem p hq))
            (ErdosProblems.PathSpanningNonedgeDeficit.augment J p.1 p.2)
            (le_trans hGJ le_sup_left) hstep
    exact haux (seedPairs K W).toList (fun p hp => Finset.mem_toList.mp hp) G le_rfl hfree
  have hsecond : (pathGraph (2 * d + 2)).Free (seedFirstFilled G K W) := by
    have haux : ∀ L : List (Fin (2 * d + 2) × Fin (2 * d + 2)),
        (∀ p ∈ L, p ∈ restoredPairs K W) →
        ∀ J : SimpleGraph (Fin (2 * d + 2)), seedFilled G K W ≤ J →
          (pathGraph (2 * d + 2)).Free J →
          (pathGraph (2 * d + 2)).Free (fillOrdered J L) := by
      intro L
      induction L with
      | nil => intro _ J _ hfreeJ; exact hfreeJ
      | cons p ps ih =>
          intro hmem J hseedJ hfreeJ
          have hp : p ∈ restoredPairs K W := hmem p (by simp)
          simp only [restoredPairs, Finset.mem_filter, Finset.mem_product,
            Finset.mem_sdiff, Finset.mem_univ, true_and] at hp
          obtain ⟨⟨hw, hx⟩, _hne⟩ := hp
          have hfill : fillSeedPairs G K W ≤ J := by
            rw [← seedFilled_eq]
            exact hseedJ
          have hstep : (pathGraph (2 * d + 2)).Free
              (ErdosProblems.PathSpanningNonedgeDeficit.augment J p.1 p.2) := by
            by_cases hadj : J.Adj p.1 p.2
            · have heq : ErdosProblems.PathSpanningNonedgeDeficit.augment J p.1 p.2 = J := by
                apply le_antisymm _ le_sup_left
                apply sup_le le_rfl
                intro x y hxy
                obtain ⟨hpair, _⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
                rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp hpair) with h | h
                · simpa only [h.1, h.2] using hadj
                · simpa only [h.1, h.2] using J.adj_symm hadj
              simpa only [heq] using hfreeJ
            · exact path_free_after_missing_restoration_pair_additive hd hlow G J K W p.1 p.2
                horder hWK hw hx hfill (hrestored p.2 hx) hfreeJ hadj
          exact ih (fun q hq => hmem q (List.mem_cons_of_mem p hq))
            (ErdosProblems.PathSpanningNonedgeDeficit.augment J p.1 p.2)
            (le_trans hseedJ le_sup_left) hstep
    exact haux (restoredPairs K W).toList (fun p hp => Finset.mem_toList.mp hp)
      (seedFilled G K W) le_rfl hfirst
  refine ⟨hsecond, le_trans (le_fillOrdered G _) (le_fillOrdered (seedFilled G K W) _), ?_, ?_⟩
  · intro w hw v hne
    rw [seedFirstFilled_eq]
    exact filled_seed_adj G Finset.univ W w v hw (Finset.mem_univ v) hne
  · intro u hu v hv
    exact residual_original G K W u v hu hv

/-- Additive-guard residual forest exclusions on any finite carrier of size `2*d+2`. -/
theorem original_residual_forest_free_of_finite_carrier_additive
    {V : Type*} [Fintype V] {d h : ℕ}
    (hd : 3 ≤ d) (hlow : 3 ≤ h)
    (G : SimpleGraph V) (hcard : Fintype.card V = 2 * d + 2)
    (K W : Finset V)
    (horder : K.card = d + h) (hW : W.card = d - 1) (hWK : W ⊆ K)
    (hmin : ∀ v ∈ K, d ≤ (K.filter (G.Adj v)).card)
    (hhigh : ∀ w ∈ W, d + 1 ≤ (K.filter (G.Adj w)).card)
    (hrestored : ∀ x, x ∉ K → d + 2 ≤ G.degree x + h)
    (hfree : (pathGraph (2 * d + 2)).Free G) :
    (∀ p : Fin 4 → V, Function.Injective p → (∀ i, p i ∈ K ∧ p i ∉ W) →
      G.Adj (p 0) (p 1) → G.Adj (p 1) (p 2) → G.Adj (p 2) (p 3) → False) ∧
    (∀ p : Fin 5 → V, Function.Injective p → (∀ i, p i ∈ K ∧ p i ∉ W) →
      G.Adj (p 0) (p 1) → G.Adj (p 1) (p 2) → G.Adj (p 3) (p 4) → False) ∧
    (∀ p : Fin 6 → V, Function.Injective p → (∀ i, p i ∈ K ∧ p i ∉ W) →
      G.Adj (p 0) (p 1) → G.Adj (p 2) (p 3) → G.Adj (p 4) (p 5) → False) := by
  classical
  let J : SimpleGraph (Fin (2 * d + 2)) := G.overFin hcard
  let e : G ≃g J := G.overFinIso hcard
  let Kf : Finset (Fin (2 * d + 2)) := K.map e.toEquiv.toEmbedding
  let Wf : Finset (Fin (2 * d + 2)) := W.map e.toEquiv.toEmbedding
  have hKcard : Kf.card = d + h := by simpa only [Kf, Finset.card_map] using horder
  have hWcard : Wf.card = d - 1 := by simpa only [Wf, Finset.card_map] using hW
  have hWKf : Wf ⊆ Kf := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hz
    exact Finset.mem_map.mpr ⟨u, hWK hu, rfl⟩
  have hseed (u : V) :
      originalSeedDegree J Kf (e u) = (K.filter (G.Adj u)).card := by
    change ((K.map e.toEquiv.toEmbedding).filter (J.Adj (e u))).card =
      (K.filter (G.Adj u)).card
    rw [Finset.filter_map]
    change ((K.filter (fun v => J.Adj (e u) (e v))).map
      e.toEquiv.toEmbedding).card = (K.filter (G.Adj u)).card
    have hfilters : K.filter (fun v => J.Adj (e u) (e v)) =
        K.filter (G.Adj u) := by
      ext v
      simp only [Finset.mem_filter, e.map_adj_iff]
    rw [hfilters, Finset.card_map]
  have hminf : ∀ z ∈ Kf, d ≤ originalSeedDegree J Kf z := by
    intro z hz
    obtain ⟨u, hu, he⟩ := Finset.mem_map.mp hz
    change e u = z at he
    rw [← he, hseed u]
    exact hmin u hu
  have hhighf : ∀ z ∈ Wf, d + 1 ≤ originalSeedDegree J Kf z := by
    intro z hz
    obtain ⟨u, hu, he⟩ := Finset.mem_map.mp hz
    change e u = z at he
    rw [← he, hseed u]
    exact hhigh u hu
  have hrestf : ∀ z, z ∉ Kf → d + 2 ≤ J.degree z + h := by
    intro z hz
    have hnot : e.symm z ∉ K := by
      intro hm
      apply hz
      exact Finset.mem_map.mpr ⟨e.symm z, hm, e.apply_symm_apply z⟩
    have hdeg := e.degree_eq (e.symm z)
    rw [e.apply_symm_apply] at hdeg
    rw [hdeg]
    exact hrestored (e.symm z) hnot
  have hfreef : (pathGraph (2 * d + 2)).Free J :=
    (SimpleGraph.free_congr_right e).mp hfree
  obtain ⟨hFfree, hJF, hWuniv, _houtside⟩ :=
    seed_first_path_free_additive hd hlow J Kf Wf hKcard hWKf hminf hhighf hrestf hfreef
  let F := seedFirstFilled J Kf Wf
  refine ⟨?_, ?_, ?_⟩
  · intro p hpinj hpKW h01 h12 h23
    let pf : Fin 4 → Fin (2 * d + 2) := fun i => e (p i)
    have hpfinj : Function.Injective pf := e.injective.comp hpinj
    have hpfnotW : ∀ i : Fin 4, pf i ∉ Wf := by
      intro i hmem
      obtain ⟨u, huW, he⟩ := Finset.mem_map.mp hmem
      change e u = e (p i) at he
      exact (hpKW i).2 ((e.injective he) ▸ huW)
    have hf01 : F.Adj (pf 0) (pf 1) := hJF (e.map_adj_iff.mpr h01)
    have hf12 : F.Adj (pf 1) (pf 2) := hJF (e.map_adj_iff.mpr h12)
    have hf23 : F.Adj (pf 2) (pf 3) := hJF (e.map_adj_iff.mpr h23)
    have hpadj : ∀ (i j : Fin 4), i.val + 1 = j.val → F.Adj (pf i) (pf j) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    exact hFfree (spanning_path_of_residual_path (by omega) (by omega)
      F Wf hWcard hWuniv pf hpfinj hpfnotW hpadj)
  · intro p hpinj hpKW h01 h12 h34
    let pf : Fin 5 → Fin (2 * d + 2) := fun i => e (p i)
    have hpfinj : Function.Injective pf := e.injective.comp hpinj
    have hpfnotW : ∀ i : Fin 5, pf i ∉ Wf := by
      intro i hmem
      obtain ⟨u, huW, he⟩ := Finset.mem_map.mp hmem
      change e u = e (p i) at he
      exact (hpKW i).2 ((e.injective he) ▸ huW)
    have hf01 : F.Adj (pf 0) (pf 1) := hJF (e.map_adj_iff.mpr h01)
    have hf12 : F.Adj (pf 1) (pf 2) := hJF (e.map_adj_iff.mpr h12)
    have hf34 : F.Adj (pf 3) (pf 4) := hJF (e.map_adj_iff.mpr h34)
    exact hFfree (spanning_path_of_residual_p3_p2 hd F Wf hWcard hWuniv
      pf hpfinj hpfnotW hf01 hf12 hf34)
  · intro p hpinj hpKW h01 h23 h45
    let pf : Fin 6 → Fin (2 * d + 2) := fun i => e (p i)
    have hpfinj : Function.Injective pf := e.injective.comp hpinj
    have hpfnotW : ∀ i : Fin 6, pf i ∉ Wf := by
      intro i hmem
      obtain ⟨u, huW, he⟩ := Finset.mem_map.mp hmem
      change e u = e (p i) at he
      exact (hpKW i).2 ((e.injective he) ▸ huW)
    have hf01 : F.Adj (pf 0) (pf 1) := hJF (e.map_adj_iff.mpr h01)
    have hf23 : F.Adj (pf 2) (pf 3) := hJF (e.map_adj_iff.mpr h23)
    have hf45 : F.Adj (pf 4) (pf 5) := hJF (e.map_adj_iff.mpr h45)
    exact hFfree (spanning_path_of_residual_3p2 hd F Wf hWcard hWuniv
      pf hpfinj hpfnotW hf01 hf23 hf45)

/-- Actual-carrier wrapper for all three linear forest exclusions under the additive guard. -/
theorem original_residual_forest_free_of_actual_carrier_additive
    {V : Type*} [Fintype V] {d h : ℕ}
    (hd : 3 ≤ d) (hlow : 3 ≤ h)
    (H : SimpleGraph V) (D K W : Finset V)
    (hDcard : D.card = 2 * d + 2) (hKD : K ⊆ D) (hWK : W ⊆ K)
    (hKcard : K.card = d + h) (hWcard : W.card = d - 1)
    (hmin : ∀ v ∈ K, d ≤ withinDegree H K v)
    (hhigh : ∀ w ∈ W, d + 1 ≤ withinDegree H K w)
    (hrestored : ∀ x ∈ D, x ∉ K → d + 2 ≤ withinDegree H D x + h)
    (hfree : (pathGraph (2 * d + 2)).Free H) :
    (pathGraph 4).Free (H.induce (↑(K \ W) : Set V)) ∧
      NoP3AndP2 (H.induce (↑(K \ W) : Set V)) ∧
      NoThreeP2 (H.induce (↑(K \ W) : Set V)) := by
  let J : SimpleGraph (↑D : Set V) := H.induce (↑D : Set V)
  let KD : Finset (↑D : Set V) := K.subtype (fun x => x ∈ D)
  let WD : Finset (↑D : Set V) := W.subtype (fun x => x ∈ D)
  have hDtype : Fintype.card (↑D : Set V) = 2 * d + 2 := by
    have hc : Fintype.card (↑D : Set V) = D.card :=
      Fintype.card_of_finset' (p := (↑D : Set V)) D (fun _ => Iff.rfl)
    exact hc.trans hDcard
  have hKDmap : KD.map (Function.Embedding.subtype _) = K :=
    Finset.subtype_map_of_mem (p := fun x => x ∈ D) (fun _ hx => hKD hx)
  have hWDmap : WD.map (Function.Embedding.subtype _) = W :=
    Finset.subtype_map_of_mem (p := fun x => x ∈ D) (fun _ hx => hKD (hWK hx))
  have hKDcard : KD.card = d + h := by
    have hc := congrArg Finset.card hKDmap
    simp only [Finset.card_map] at hc
    exact hc.trans hKcard
  have hWDcard : WD.card = d - 1 := by
    have hc := congrArg Finset.card hWDmap
    simp only [Finset.card_map] at hc
    exact hc.trans hWcard
  have hWKD : WD ⊆ KD := by
    intro u hu
    exact Finset.mem_subtype.mpr (hWK (Finset.mem_subtype.mp hu))
  have hseed (u : (↑D : Set V)) :
      (KD.filter (J.Adj u)).card = withinDegree H K u.val := by
    change (KD.filter (J.Adj u)).card = (K.filter (H.Adj u.val)).card
    have hf : (KD.filter (J.Adj u)).map (Function.Embedding.subtype _) =
        K.filter (H.Adj u.val) := by
      rw [← hKDmap, Finset.filter_map]
      rfl
    have hc := congrArg Finset.card hf
    simpa only [Finset.card_map] using hc
  have hminD : ∀ u ∈ KD, d ≤ (KD.filter (J.Adj u)).card := by
    intro u hu
    rw [hseed u]
    exact hmin u.val (Finset.mem_subtype.mp hu)
  have hhighD : ∀ u ∈ WD, d + 1 ≤ (KD.filter (J.Adj u)).card := by
    intro u hu
    rw [hseed u]
    exact hhigh u.val (Finset.mem_subtype.mp hu)
  have hrestoredD : ∀ u, u ∉ KD → d + 2 ≤ J.degree u + h := by
    intro u hu
    have hdeg := ActualInducedDegree1105.degree_induce_eq_withinDegree H D u
    change J.degree u = withinDegree H D u.val at hdeg
    rw [hdeg]
    apply hrestored u.val u.property
    intro huK
    exact hu (Finset.mem_subtype.mpr huK)
  have hfreeD : (pathGraph (2 * d + 2)).Free J := by
    intro hp
    obtain ⟨P⟩ := hp
    let E : J.Copy H := (SimpleGraph.Embedding.induce (↑D : Set V)).toCopy
    exact hfree ⟨E.comp P⟩
  obtain ⟨hP4D, hP3P2D, h3P2D⟩ :=
    original_residual_forest_free_of_finite_carrier_additive
      hd hlow J hDtype KD WD hKDcard hWDcard hWKD
      hminD hhighD hrestoredD hfreeD
  let lift : (↑(K \ W) : Set V) → (↑D : Set V) := fun u =>
    ⟨u.val, hKD (Finset.mem_sdiff.mp u.property).1⟩
  have hliftInj : Function.Injective lift := by
    intro u v huv
    apply Subtype.ext
    exact congrArg (fun z : (↑D : Set V) => z.val) huv
  have hliftKW (u : (↑(K \ W) : Set V)) : lift u ∈ KD ∧ lift u ∉ WD := by
    obtain ⟨huK, huW⟩ := Finset.mem_sdiff.mp u.property
    exact ⟨Finset.mem_subtype.mpr (by change (lift u).val ∈ K; exact huK),
      fun h => huW (Finset.mem_subtype.mp h : (lift u).val ∈ W)⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨P⟩
    have h01 : (pathGraph 4).Adj 0 1 := pathGraph_adj.mpr (Or.inl rfl)
    have h12 : (pathGraph 4).Adj 1 2 := pathGraph_adj.mpr (Or.inl rfl)
    have h23 : (pathGraph 4).Adj 2 3 := pathGraph_adj.mpr (Or.inl rfl)
    exact hP4D (lift ∘ P) (hliftInj.comp P.injective) (fun i => hliftKW (P i))
      (P.toHom.map_rel' h01) (P.toHom.map_rel' h12) (P.toHom.map_rel' h23)
  · intro p hpinj h01 h12 h34
    exact hP3P2D (lift ∘ p) (hliftInj.comp hpinj) (fun i => hliftKW (p i)) h01 h12 h34
  · intro p hpinj h01 h23 h45
    exact h3P2D (lift ∘ p) (hliftInj.comp hpinj) (fun i => hliftKW (p i)) h01 h23 h45

section StarCenterAdditive

local instance (priority := 3000) subtypeNeighborSetFintypeAdditive {A : Type*} [Fintype A]
    (G : SimpleGraph A) [DecidableRel G.Adj] (x : A) : Fintype (G.neighborSet x) :=
  Subtype.fintype (Membership.mem (G.neighborSet x))

/-- For any `h ≥ 4` (including `h = d + 1` and `h = d + 2`), if `K` fits inside a
carrier `D` of size `2*d+2` with the additive restored-degree guard, `G.induce (K \ W)`
is a spanning star with center `b ∈ K \ W`. -/
theorem exists_residual_star_center_of_carrier_additive
    {V : Type*} [Fintype V] {d h : ℕ}
    (hd : 3 ≤ d) (hlow : 4 ≤ h)
    (G : SimpleGraph V) (D K W : Finset V)
    (hDcard : D.card = 2 * d + 2) (hKD : K ⊆ D) (hWK : W ⊆ K)
    (hKcard : K.card = d + h) (hWcard : W.card = d - 1)
    (hmin : ∀ v ∈ K, d ≤ withinDegree G K v)
    (hhigh : ∀ w ∈ W, d + 1 ≤ withinDegree G K w)
    (hrestored : ∀ x ∈ D, x ∉ K → d + 2 ≤ withinDegree G D x + h)
    (hfree : (pathGraph (2 * d + 2)).Free G) :
    ∃ b ∈ K \ W,
      (∀ x ∈ K \ W, x ≠ b → G.Adj b x) ∧
      (∀ x ∈ K \ W, x ≠ b → ∀ y ∈ K \ W, y ≠ b → ¬ G.Adj x y) := by
  let R := G.induce (↑(K \ W) : Set V)
  have hKWcard : (K \ W).card = h + 1 := by
    rw [Finset.card_sdiff_of_subset hWK, hKcard, hWcard]
    omega
  have hRcard : 5 ≤ Fintype.card (↑(K \ W) : Set V) := by
    have hc : Fintype.card (↑(K \ W) : Set V) = (K \ W).card :=
      Fintype.card_of_finset' (p := (↑(K \ W) : Set V)) (K \ W) (fun _ => Iff.rfl)
    omega
  have hRmin := residual_min_degree_one G d K W (by omega) hWcard hmin
  obtain ⟨hP4, hP3P2, h3P2⟩ :=
    original_residual_forest_free_of_actual_carrier_additive
      hd (by omega) G D K W hDcard hKD hWK hKcard hWcard hmin hhigh hrestored hfree
  obtain ⟨b, hcenter, hleaves, _hcover⟩ :=
    exists_center_of_min_degree_and_no_three_edge_linear_forest
      R hRcard hRmin hP4 hP3P2 h3P2
  refine ⟨b.val, b.property, ?_, ?_⟩
  · intro x hx hxb
    have hne : (⟨x, hx⟩ : (↑(K \ W) : Set V)) ≠ b := fun he => hxb (congrArg Subtype.val he)
    exact hcenter ⟨x, hx⟩ hne
  · intro x hx hxb y hy hyb
    have hnex : (⟨x, hx⟩ : (↑(K \ W) : Set V)) ≠ b := fun he => hxb (congrArg Subtype.val he)
    have hney : (⟨y, hy⟩ : (↑(K \ W) : Set V)) ≠ b := fun he => hyb (congrArg Subtype.val he)
    exact hleaves ⟨x, hx⟩ hnex ⟨y, hy⟩ hney

end StarCenterAdditive

/-- Additive-guard version of `finite_carrier_cover_of_star_center`. -/
theorem finite_carrier_cover_of_star_center_additive {d h : ℕ}
    (hd : 3 ≤ d) (hlow : 3 ≤ h)
    (G : SimpleGraph (Fin (2 * d + 2)))
    (K W : Finset (Fin (2 * d + 2))) (b : Fin (2 * d + 2))
    (hKcard : K.card = d + h) (hWcard : W.card = d - 1) (hWK : W ⊆ K)
    (hb : b ∈ K \ W) (hcenter : ∀ x ∈ K \ W, x ≠ b → G.Adj b x)
    (hmin : ∀ v ∈ K, d ≤ originalSeedDegree G K v)
    (hhigh : ∀ w ∈ W, d + 1 ≤ originalSeedDegree G K w)
    (hrestored : ∀ x, x ∉ K → d + 2 ≤ G.degree x + h)
    (hfree : (pathGraph (2 * d + 2)).Free G) :
    ∀ u v, G.Adj u v → u ∈ insert b W ∨ v ∈ insert b W := by
  classical
  let H : Finset (Fin (2 * d + 2)) := insert b W
  have hbK : b ∈ K := (Finset.mem_sdiff.mp hb).1
  have hbW : b ∉ W := (Finset.mem_sdiff.mp hb).2
  have hHK : H ⊆ K := Finset.insert_subset_iff.mpr ⟨hbK, hWK⟩
  have hHcard : H.card = d := by
    dsimp [H]
    rw [Finset.card_insert_of_notMem hbW, hWcard]
    omega
  obtain ⟨hFilledFreeW, _hGW, _hWuniv, _hWres⟩ :=
    seed_first_path_free_additive hd hlow G K W hKcard hWK hmin hhigh hrestored hfree
  have hseedEq : seedFilled G K H = seedFilled G K W := by
    rw [seedFilled_eq, seedFilled_eq]
    exact fillSeedPairs_insert_center_eq G K W b hb hcenter
  have hfirstW : (pathGraph (2 * d + 2)).Free (seedFilled G K W) := by
    intro hp
    obtain ⟨P⟩ := hp
    have hle : seedFilled G K W ≤ seedFirstFilled G K W :=
      le_fillOrdered (seedFilled G K W) (restoredPairs K W).toList
    exact hFilledFreeW ⟨(SimpleGraph.Copy.ofLE _ _ hle).comp P⟩
  have hfirstH : (pathGraph (2 * d + 2)).Free (seedFilled G K H) := by
    rw [hseedEq]
    exact hfirstW
  have hsecondH : (pathGraph (2 * d + 2)).Free (seedFirstFilled G K H) := by
    have haux : ∀ L : List (Fin (2 * d + 2) × Fin (2 * d + 2)),
        (∀ p ∈ L, p ∈ restoredPairs K H) →
        ∀ J : SimpleGraph (Fin (2 * d + 2)), seedFilled G K H ≤ J →
          (pathGraph (2 * d + 2)).Free J →
          (pathGraph (2 * d + 2)).Free (fillOrdered J L) := by
      intro L
      induction L with
      | nil => intro _ J _ hfreeJ; exact hfreeJ
      | cons p ps ih =>
          intro hmem J hHJ hfreeJ
          have hp : p ∈ restoredPairs K H := hmem p (by simp)
          simp only [restoredPairs, Finset.mem_filter, Finset.mem_product,
            Finset.mem_sdiff, Finset.mem_univ, true_and] at hp
          obtain ⟨⟨hp1H, hp2notK⟩, _hne⟩ := hp
          have hfill : fillSeedPairs G K H ≤ J := by
            rw [← seedFilled_eq]
            exact hHJ
          have hstep : (pathGraph (2 * d + 2)).Free
              (ErdosProblems.PathSpanningNonedgeDeficit.augment J p.1 p.2) := by
            by_cases hadj : J.Adj p.1 p.2
            · have heq : ErdosProblems.PathSpanningNonedgeDeficit.augment J p.1 p.2 = J := by
                apply le_antisymm _ le_sup_left
                apply sup_le le_rfl
                intro x y hxy
                obtain ⟨hpair, _⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
                rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp hpair) with h | h
                · simpa only [h.1, h.2] using hadj
                · simpa only [h.1, h.2] using J.adj_symm hadj
              simpa only [heq] using hfreeJ
            · exact path_free_after_missing_restoration_pair_additive hd hlow G J K H p.1 p.2
                hKcard hHK hp1H hp2notK hfill (hrestored p.2 hp2notK) hfreeJ hadj
          exact ih (fun q hq => hmem q (List.mem_cons_of_mem p hq))
            (ErdosProblems.PathSpanningNonedgeDeficit.augment J p.1 p.2)
            (le_trans hHJ le_sup_left) hstep
    exact haux (restoredPairs K H).toList (fun p hp => Finset.mem_toList.mp hp)
      (seedFilled G K H) le_rfl hfirstH
  have hHuniv : ∀ w ∈ H, ∀ v, w ≠ v → (seedFirstFilled G K H).Adj w v := by
    intro w hw v hne
    rw [seedFirstFilled_eq]
    exact filled_seed_adj G Finset.univ H w v hw (Finset.mem_univ v) hne
  intro u v huv
  by_cases hu : u ∈ H
  · exact Or.inl hu
  by_cases hv : v ∈ H
  · exact Or.inr hv
  have hFilledEdge : (seedFirstFilled G K H).Adj u v :=
    (residual_original G K H u v hu hv).mpr huv
  exact False.elim (hsecondH (spanning_path_of_residual_edge_ge_three hd
    (seedFirstFilled G K H) H hHcard hHuniv u v hu hv hFilledEdge))

/-- Additive-guard transport over any finite type `V` of size `2*d+2`. -/
theorem finite_carrier_cover_of_star_center_over_fintype_additive
    {V : Type*} [Fintype V] {d h : ℕ}
    (hd : 3 ≤ d) (hlow : 3 ≤ h)
    (G : SimpleGraph V) (hcard : Fintype.card V = 2 * d + 2)
    (K W : Finset V) (b : V)
    (hKcard : K.card = d + h) (hWcard : W.card = d - 1) (hWK : W ⊆ K)
    (hb : b ∈ K ∧ b ∉ W) (hcenter : ∀ x ∈ K, x ∉ W → x ≠ b → G.Adj b x)
    (hmin : ∀ x ∈ K, d ≤ withinDegree G K x)
    (hhigh : ∀ x ∈ W, d + 1 ≤ withinDegree G K x)
    (hrestored : ∀ x, x ∉ K → d + 2 ≤ G.degree x + h)
    (hfree : (pathGraph (2 * d + 2)).Free G) :
    ∀ x y, G.Adj x y → (x = b ∨ x ∈ W) ∨ (y = b ∨ y ∈ W) := by
  classical
  let J : SimpleGraph (Fin (2 * d + 2)) := G.overFin hcard
  let e : G ≃g J := G.overFinIso hcard
  let Kf : Finset (Fin (2 * d + 2)) := K.map e.toEquiv.toEmbedding
  let Wf : Finset (Fin (2 * d + 2)) := W.map e.toEquiv.toEmbedding
  let bf : Fin (2 * d + 2) := e b
  have hKcardf : Kf.card = d + h := by simpa only [Kf, Finset.card_map] using hKcard
  have hWcardf : Wf.card = d - 1 := by simpa only [Wf, Finset.card_map] using hWcard
  have hWKf : Wf ⊆ Kf := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hz
    exact Finset.mem_map.mpr ⟨u, hWK hu, rfl⟩
  have hbf : bf ∈ Kf \ Wf := by
    obtain ⟨hbK, hbW⟩ := hb
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_map.mpr ⟨b, hbK, rfl⟩, ?_⟩
    intro hm
    obtain ⟨u, huW, he⟩ := Finset.mem_map.mp hm
    change e u = e b at he
    exact hbW ((e.injective he) ▸ huW)
  have hcenterf : ∀ z ∈ Kf \ Wf, z ≠ bf → J.Adj bf z := by
    intro z hz hne
    obtain ⟨hzK, hzW⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨u, huK, rfl⟩ := Finset.mem_map.mp hzK
    have huW : u ∉ W := fun h => hzW (Finset.mem_map.mpr ⟨u, h, rfl⟩)
    have hub : u ≠ b := fun h => hne (congrArg e h)
    exact e.map_adj_iff.mpr (hcenter u huK huW hub)
  have hseed (u : V) :
      originalSeedDegree J Kf (e u) = withinDegree G K u := by
    change ((K.map e.toEquiv.toEmbedding).filter (J.Adj (e u))).card =
      (K.filter (G.Adj u)).card
    rw [Finset.filter_map]
    change ((K.filter (fun v => J.Adj (e u) (e v))).map
      e.toEquiv.toEmbedding).card = (K.filter (G.Adj u)).card
    have hfilters : K.filter (fun v => J.Adj (e u) (e v)) =
        K.filter (G.Adj u) := by
      ext v
      simp only [Finset.mem_filter, e.map_adj_iff]
    rw [hfilters, Finset.card_map]
  have hminf : ∀ z ∈ Kf, d ≤ originalSeedDegree J Kf z := by
    intro z hz
    obtain ⟨u, hu, he⟩ := Finset.mem_map.mp hz
    change e u = z at he
    rw [← he, hseed u]
    exact hmin u hu
  have hhighf : ∀ z ∈ Wf, d + 1 ≤ originalSeedDegree J Kf z := by
    intro z hz
    obtain ⟨u, hu, he⟩ := Finset.mem_map.mp hz
    change e u = z at he
    rw [← he, hseed u]
    exact hhigh u hu
  have hrestf : ∀ z, z ∉ Kf → d + 2 ≤ J.degree z + h := by
    intro z hz
    have hnot : e.symm z ∉ K := by
      intro hm
      apply hz
      exact Finset.mem_map.mpr ⟨e.symm z, hm, e.apply_symm_apply z⟩
    have hdeg := e.degree_eq (e.symm z)
    rw [e.apply_symm_apply] at hdeg
    rw [hdeg]
    exact hrestored (e.symm z) hnot
  have hfreef : (pathGraph (2 * d + 2)).Free J :=
    (SimpleGraph.free_congr_right e).mp hfree
  have hcover := finite_carrier_cover_of_star_center_additive hd hlow J Kf Wf bf
    hKcardf hWcardf hWKf hbf hcenterf hminf hhighf hrestf hfreef
  intro x y hxy
  have hxyf : J.Adj (e x) (e y) := e.map_adj_iff.mpr hxy
  rcases hcover (e x) (e y) hxyf with hx | hy
  · rcases Finset.mem_insert.mp hx with hxb | hxW
    · exact Or.inl (Or.inl (e.injective hxb))
    · obtain ⟨u, huW, he⟩ := Finset.mem_map.mp hxW
      change e u = e x at he
      exact Or.inl (Or.inr ((e.injective he) ▸ huW))
  · rcases Finset.mem_insert.mp hy with hyb | hyW
    · exact Or.inr (Or.inl (e.injective hyb))
    · obtain ⟨u, huW, he⟩ := Finset.mem_map.mp hyW
      change e u = e y at he
      exact Or.inr (Or.inr ((e.injective he) ▸ huW))

/-- Additive-guard actual-carrier cover: valid for all `h ≥ 3`, including `h = d + 1`
(`|K| = 2*d+1`) and `h = d + 2` (`|K| = 2*d+2`). -/
theorem actual_carrier_cover_of_star_center_additive
    {V : Type*} [Fintype V] {d h : ℕ}
    (hd : 3 ≤ d) (hlow : 3 ≤ h)
    (G : SimpleGraph V) (D K W : Finset V) (b : V)
    (hDcard : D.card = 2 * d + 2) (hKD : K ⊆ D) (hWK : W ⊆ K)
    (hKcard : K.card = d + h) (hWcard : W.card = d - 1)
    (hb : b ∈ K \ W) (hcenter : ∀ x ∈ K \ W, x ≠ b → G.Adj b x)
    (hmin : ∀ x ∈ K, d ≤ withinDegree G K x)
    (hhigh : ∀ x ∈ W, d + 1 ≤ withinDegree G K x)
    (hrestored : ∀ x ∈ D, x ∉ K → d + 2 ≤ withinDegree G D x + h)
    (hfree : (pathGraph (2 * d + 2)).Free G) :
    ∀ x ∈ D, ∀ y ∈ D, G.Adj x y → x ∈ insert b W ∨ y ∈ insert b W := by
  let J : SimpleGraph (↑D : Set V) := G.induce (↑D : Set V)
  let KD : Finset (↑D : Set V) := K.subtype (fun x => x ∈ D)
  let WD : Finset (↑D : Set V) := W.subtype (fun x => x ∈ D)
  have hbK : b ∈ K := (Finset.mem_sdiff.mp hb).1
  have hbW : b ∉ W := (Finset.mem_sdiff.mp hb).2
  let bD : (↑D : Set V) := ⟨b, hKD hbK⟩
  have hDtype : Fintype.card (↑D : Set V) = 2 * d + 2 := by
    have hc : Fintype.card (↑D : Set V) = D.card :=
      Fintype.card_of_finset' (p := (↑D : Set V)) D (fun _ => Iff.rfl)
    exact hc.trans hDcard
  have hKDmap : KD.map (Function.Embedding.subtype _) = K :=
    Finset.subtype_map_of_mem (p := fun x => x ∈ D) (fun _ hx => hKD hx)
  have hWDmap : WD.map (Function.Embedding.subtype _) = W :=
    Finset.subtype_map_of_mem (p := fun x => x ∈ D) (fun _ hx => hKD (hWK hx))
  have hKDcard : KD.card = d + h := by
    have hc := congrArg Finset.card hKDmap
    simp only [Finset.card_map] at hc
    exact hc.trans hKcard
  have hWDcard : WD.card = d - 1 := by
    have hc := congrArg Finset.card hWDmap
    simp only [Finset.card_map] at hc
    exact hc.trans hWcard
  have hWKD : WD ⊆ KD := by
    intro u hu
    exact Finset.mem_subtype.mpr (hWK (Finset.mem_subtype.mp hu))
  have hbD : bD ∈ KD ∧ bD ∉ WD :=
    ⟨Finset.mem_subtype.mpr hbK, fun hm => hbW (Finset.mem_subtype.mp hm : bD.val ∈ W)⟩
  have hcenterD : ∀ u ∈ KD, u ∉ WD → u ≠ bD → J.Adj bD u := by
    intro u huK huW hne
    have huK' : u.val ∈ K := Finset.mem_subtype.mp huK
    have huW' : u.val ∉ W := fun h => huW (Finset.mem_subtype.mpr h)
    have hub : u.val ≠ b := fun h => hne (Subtype.ext h)
    exact hcenter u.val (Finset.mem_sdiff.mpr ⟨huK', huW'⟩) hub
  have hseed (u : (↑D : Set V)) :
      withinDegree J KD u = withinDegree G K u.val := by
    change (KD.filter (J.Adj u)).card = (K.filter (G.Adj u.val)).card
    have hf : (KD.filter (J.Adj u)).map (Function.Embedding.subtype _) =
        K.filter (G.Adj u.val) := by
      rw [← hKDmap, Finset.filter_map]
      rfl
    have hc := congrArg Finset.card hf
    simpa only [Finset.card_map] using hc
  have hminD : ∀ u ∈ KD, d ≤ withinDegree J KD u := by
    intro u hu
    rw [hseed u]
    exact hmin u.val (Finset.mem_subtype.mp hu)
  have hhighD : ∀ u ∈ WD, d + 1 ≤ withinDegree J KD u := by
    intro u hu
    rw [hseed u]
    exact hhigh u.val (Finset.mem_subtype.mp hu)
  have hrestoredD : ∀ u, u ∉ KD → d + 2 ≤ J.degree u + h := by
    intro u hu
    have hdeg := ActualInducedDegree1105.degree_induce_eq_withinDegree G D u
    change J.degree u = withinDegree G D u.val at hdeg
    rw [hdeg]
    apply hrestored u.val u.property
    intro huK
    exact hu (Finset.mem_subtype.mpr huK)
  have hfreeD : (pathGraph (2 * d + 2)).Free J := by
    intro hp
    obtain ⟨P⟩ := hp
    let E : J.Copy G := (SimpleGraph.Embedding.induce (↑D : Set V)).toCopy
    exact hfree ⟨E.comp P⟩
  have hcover := finite_carrier_cover_of_star_center_over_fintype_additive hd hlow
    J hDtype KD WD bD hKDcard hWDcard hWKD hbD hcenterD hminD hhighD hrestoredD hfreeD
  intro x hx y hy hxy
  have hxyD : J.Adj (⟨x, hx⟩ : (↑D : Set V)) ⟨y, hy⟩ := hxy
  rcases hcover ⟨x, hx⟩ ⟨y, hy⟩ hxyD with hxH | hyH
  · rcases hxH with hxb | hxW
    · exact Or.inl (Finset.mem_insert.mpr (Or.inl (congrArg Subtype.val hxb)))
    · exact Or.inl (Finset.mem_insert.mpr (Or.inr
        (Finset.mem_subtype.mp hxW : (⟨x, hx⟩ : (↑D : Set V)).val ∈ W)))
  · rcases hyH with hyb | hyW
    · exact Or.inr (Finset.mem_insert.mpr (Or.inl (congrArg Subtype.val hyb)))
    · exact Or.inr (Finset.mem_insert.mpr (Or.inr
        (Finset.mem_subtype.mp hyW : (⟨y, hy⟩ : (↑D : Set V)).val ∈ W)))

end ErdosProblems.PathUpperReduction.SmallKernelWholeSupport1105
