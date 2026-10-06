module

public import CycleComponentCyclicIndex
public import CycleOriginalCrossComponentPaletteExclusionV3
public import CycleCyclicCrossMatrixTranslationsV6
public import CycleAdjacentMatrixTranslationsV2
public import CycleChordPathWindowV2
public import CycleEvenCheckerboardDegree
public import CycleEvenChordRotationV2

@[expose] public section

/-!
Original high-NEW Claim3 caller. Reapply translations to the literally rotated order rather
than transporting parity through cyclic addition. No Copy is reconstructed.
-/

namespace ErdosProblems.AntiRamseyCycleOriginalCrossComponentConstancy

open SimpleGraph
open scoped Classical Fin.CommRing
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleCyclicCrossMatrixTranslations
open ErdosProblems.AntiRamseyAdjacentMatrixTranslations
open ErdosProblems.AntiRamseyChordPathWindow
open ErdosProblems.AntiRamseyEvenCheckerboardDegree
open ErdosProblems.AntiRamseyEvenChordRotation
open ErdosProblems.AntiRamseyCycleComponentCyclicIndex
open ErdosProblems.AntiRamseyCycleOriginalCrossComponentPaletteExclusion

variable {n : ℕ} {C : Type*} [DecidableEq C]

theorem cross_matrix_forms
    {k a b : ℕ} (hk : 5 ≤ k) (ha : 3 ≤ a ∧ a ≤ k - 1)
    (hb : 3 ≤ b ∧ b ≤ k - 1) (hsum : k + 1 ≤ a + b)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (A : Fin a → Fin n) (B : Fin b → Fin n)
    (hA : Function.Injective A) (hB : Function.Injective B)
    (hdisjoint : Disjoint (Set.range A) (Set.range B))
    (hAcycle : cycleGraph a ≤ (selectedGraph χ r).comap A)
    (hBcycle : cycleGraph b ≤ (selectedGraph χ r).comap B)
    (hpalette : ∀ i j, χ (cyclicCrossEdge A B hdisjoint i j) ∉ newColorUnion χ)
    (hno : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ) :
    let M := liftedCrossColor χ A B (by omega) (by omega) hdisjoint
    (∀ i j : ℤ, M i j = M ((i + j) % 2) 0) ∧
      ((¬ Even a ∨ ¬ Even b ∨ ¬ Even k) → ∀ i j : ℤ, M i j = M 0 0) := by
  let : NeZero a := ⟨by omega⟩
  let : NeZero b := ⟨by omega⟩
  have hAsucc (i : Fin a) :
      (selectedGraph χ r).Adj (A i) (A (cyclicSuccessor (by omega) i)) := by
    apply hAcycle
    rw [cycleGraph_adj']
    right
    change ((i + 1) - i).val = 1
    rw [add_sub_cancel_left, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < a)]
  have hBsucc (j : Fin b) :
      (selectedGraph χ r).Adj (B j) (B (cyclicSuccessor (by omega) j)) := by
    apply hBcycle
    rw [cycleGraph_adj']
    right
    change ((j + 1) - j).val = 1
    rw [add_sub_cancel_left, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < b)]
  have hnone : ¬ ∃ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
    rintro ⟨f, hf⟩
    exact hno f hf
  let L : ℕ := max 2 (k - b)
  let d : ℤ := (L : ℤ) - 1
  let e : ℤ := (k : ℤ) - L - 1
  let M := liftedCrossColor χ A B (by omega) (by omega) hdisjoint
  have htrans := cyclic_cross_matrix_has_adjacent_translations hk ha hb hsum
    χ r A B hA hB hdisjoint hAsucc hBsucc hpalette hnone
  change ∀ i j : ℤ,
    M i j = M (i + d) (j + e) ∧
    M i j = M (i + d + 1) (j + e - 1) ∧
    M i j = M (i + d) (j - e) ∧
    M i j = M (i + d + 1) (j - e + 1) at htrans
  have hde (i j : ℤ) : M i j = M (i + d) (j + e) := (htrans i j).1
  have hnext (i j : ℤ) : M i j = M (i + (d + 1)) (j + (e - 1)) := by
    simpa only [add_assoc, add_sub_assoc] using (htrans i j).2.1
  have hreverse (i j : ℤ) : M i j = M (i + d) (j + (-e)) := by
    simpa only [sub_eq_add_neg] using (htrans i j).2.2.1
  have hreverseNext (i j : ℤ) :
      M i j = M (i + (d + 1)) (j + (-e + 1)) := by
    simpa only [sub_eq_add_neg, add_assoc] using (htrans i j).2.2.2
  obtain ⟨hpa, hpb⟩ := liftedCrossColor_periodic χ A B (by omega) (by omega) hdisjoint
  have hsumInt : d + e = (k : ℤ) - 2 := by dsimp only [d, e]; omega
  constructor
  · exact parity_normal_form_of_adjacent_translations M d e
      hde hnext hreverse hreverseNext
  · intro hodd
    exact constant_of_not_all_even_of_adjacent_translations M d e
      hde hnext hreverse hreverseNext a b k
      (fun i j => (hpa i j).symm) (fun i j => (hpb i j).symm) hsumInt hodd

theorem constant_of_first_same_parity_chord
    {k a b : ℕ} (hk : 5 ≤ k) (ha : 3 ≤ a ∧ a ≤ k - 1)
    (hb : 3 ≤ b ∧ b ≤ k - 1) (hsum : k + 1 ≤ a + b)
    (hkEven : Even k) (haEven : Even a) (hbEven : Even b)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (A : Fin a → Fin n) (B : Fin b → Fin n)
    (hA : Function.Injective A) (hB : Function.Injective B)
    (hdisjoint : Disjoint (Set.range A) (Set.range B))
    (hAcycle : cycleGraph a ≤ (selectedGraph χ r).comap A)
    (hBcycle : cycleGraph b ≤ (selectedGraph χ r).comap B)
    (hpalette : ∀ i j, χ (cyclicCrossEdge A B hdisjoint i j) ∉ newColorUnion χ)
    (hno : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (x y : Fin a) (hxy : ((selectedGraph χ r).comap A).Adj x y)
    (hparity : x.val % 2 = y.val % 2) :
    ∃ c : C, ∀ i j, χ (cyclicCrossEdge A B hdisjoint i j) = c := by
  let : NeZero a := ⟨by omega⟩
  let : NeZero b := ⟨by omega⟩
  obtain ⟨hrotInj, _hrotZero, _hrotLast, hdEven, hd2, hdad, hchord, hrotCycle⟩ :=
    normalized_even_chord_rotation ha.1 haEven ((selectedGraph χ r).comap A)
      x y hxy hparity
  let rot := cyclicRotation x
  let A' : Fin a → Fin n := fun i => A (rot i)
  let d : ℕ := (chordOffset x y).val
  have hA' : Function.Injective A' := hA.comp hrotInj
  have hdisjoint' : Disjoint (Set.range A') (Set.range B) := by
    apply Set.disjoint_range_iff.mpr
    intro i j
    exact Set.disjoint_range_iff.mp hdisjoint (rot i) j
  have hAcycle' : cycleGraph a ≤ (selectedGraph χ r).comap A' := by
    intro i j hij
    exact hAcycle ((hrotCycle i j).mpr hij)
  have hpalette' (i : Fin a) (j : Fin b) :
      χ (cyclicCrossEdge A' B hdisjoint' i j) ∉ newColorUnion χ := by
    change χ (cyclicCrossEdge A B hdisjoint (rot i) j) ∉ newColorUnion χ
    exact hpalette (rot i) j
  let M := liftedCrossColor χ A' B (by omega) (by omega) hdisjoint'
  have hform : ∀ i j : ℤ, M i j = M ((i + j) % 2) 0 :=
    (cross_matrix_forms hk ha hb hsum χ r A' B hA' hB hdisjoint'
      hAcycle' hBcycle hpalette' hno).1
  have hlift (i : Fin a) (j : Fin b) :
      M (i.val : ℤ) (j.val : ℤ) = χ (cyclicCrossEdge A' B hdisjoint' i j) := by
    simp only [M, liftedCrossColor, Int.cast_natCast, Fin.cast_val_eq_self]
  have hkmod := Nat.even_iff.mp hkEven
  have hbmod := Nat.even_iff.mp hbEven
  have hbStrict : b ≤ k - 2 := by omega
  let L : ℕ := k - b + 1
  let T : ℕ := b - 1
  have hL2 : 2 ≤ L := by dsimp only [L]; omega
  have hT2 : 2 ≤ T := by dsimp only [T]; omega
  have hLa : L ≤ a := by dsimp only [L]; omega
  have hTb : T ≤ b := by dsimp only [T]; omega
  have hcount : L + T = k := by dsimp only [L, T]; omega
  have hLmod : (L : ℤ) % 2 = 1 := by dsimp only [L]; omega
  have hTmod : ((T - 1 : ℕ) : ℤ) % 2 = 0 := by dsimp only [T]; omega
  have hconsecutive (i j : Fin a) (hij : i.val + 1 = j.val) :
      ((selectedGraph χ r).comap A').Adj i j := by
    apply hAcycle'
    apply pathGraph_le_cycleGraph
    exact pathGraph_adj.mpr (Or.inl hij)
  have hchord' : ((selectedGraph χ r).comap A').Adj
      (⟨0, by omega⟩ : Fin a) (⟨d, by have hdlt := (chordOffset x y).isLt; omega⟩ : Fin a) := by
    exact hchord
  let P : Fin L → Fin n := fun i => A' (windowOrder d hdad hLa i)
  let J : Fin T → Fin b := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hTb⟩
  let Q : Fin T → Fin n := fun j => B (J j)
  have hP : Function.Injective P := hA'.comp (windowOrder_injective d hdad hLa)
  have hJ : Function.Injective J := by
    intro i j hij
    exact Fin.ext (congrArg (fun j : Fin b => j.val) hij)
  have hQ : Function.Injective Q := hB.comp hJ
  have hPQ : Disjoint (Set.range P) (Set.range Q) := by
    apply Set.disjoint_range_iff.mpr
    intro i j
    exact Set.disjoint_range_iff.mp hdisjoint' (windowOrder d hdad hLa i) (J j)
  have hPpath : ∀ i j : Fin L, i.val + 1 = j.val →
      (selectedGraph χ r).Adj (P i) (P j) :=
    windowOrder_ordered_adj ((selectedGraph χ r).comap A') d hd2 hdad hLa
      hconsecutive hchord'
  have hQpath (i j : Fin T) (hij : i.val + 1 = j.val) :
      (selectedGraph χ r).Adj (Q i) (Q j) := by
    apply hBcycle
    apply pathGraph_le_cycleGraph
    exact pathGraph_adj.mpr (Or.inl hij)
  let p0 : Fin a := windowOrder d hdad hLa ⟨0, by omega⟩
  let p1 : Fin a := windowOrder d hdad hLa ⟨L - 1, by omega⟩
  let q0 : Fin b := J ⟨0, by omega⟩
  let q1 : Fin b := J ⟨T - 1, by omega⟩
  let between := cyclicCrossEdge A' B hdisjoint' p1 q0
  let closing := cyclicCrossEdge A' B hdisjoint' p0 q1
  have hbetween : between.val = s(P ⟨L - 1, by omega⟩, Q ⟨0, by omega⟩) := rfl
  have hclosing : closing.val = s(P ⟨0, by omega⟩, Q ⟨T - 1, by omega⟩) := rfl
  have hcolorsEq : χ between = χ closing := by
    by_contra hdifferent
    have hresult :=
      ErdosProblems.AntiRamseyTwoSelectedPathsRainbow.two_disjoint_selected_paths_close_rainbow
        χ r hL2 hT2 P Q hP hQ hPQ hPpath hQpath between closing
        hbetween hclosing (hpalette' p1 q0) (hpalette' p0 q1) hdifferent
    have hresultk : ∃ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
        IsRainbow f.toHom χ := hcount ▸ hresult
    obtain ⟨f, hf⟩ := hresultk
    exact hno f hf
  have hpSum : ((p1.val : ℤ) + (p0.val : ℤ)) % 2 = 1 :=
    (window_endpoint_sum_emod_two hd2 hdad hL2 hLa hdEven).trans hLmod
  have hq0 : q0.val = 0 := rfl
  have hq1 : q1.val = T - 1 := rfl
  have hparityNe : ((p1.val : ℤ) + (q0.val : ℤ)) % 2 ≠
      ((p0.val : ℤ) + (q1.val : ℤ)) % 2 := by
    rw [hq0, hq1]
    omega
  have hbetweenForm : χ between = M (((p1.val : ℤ) + (q0.val : ℤ)) % 2) 0 :=
    (hlift p1 q0).symm.trans (hform _ _)
  have hclosingForm : χ closing = M (((p0.val : ℤ) + (q1.val : ℤ)) % 2) 0 :=
    (hlift p0 q1).symm.trans (hform _ _)
  have h01 : M 0 0 = M 1 0 := by
    have hp := Int.emod_two_eq_zero_or_one ((p1.val : ℤ) + (q0.val : ℤ))
    have hq := Int.emod_two_eq_zero_or_one ((p0.val : ℤ) + (q1.val : ℤ))
    rw [hbetweenForm, hclosingForm] at hcolorsEq
    rcases hp with hp | hp
    · have hq1 : ((p0.val : ℤ) + (q1.val : ℤ)) % 2 = 1 := by omega
      simpa only [hp, hq1] using hcolorsEq
    · have hq0 : ((p0.val : ℤ) + (q1.val : ℤ)) % 2 = 0 := by omega
      simpa only [hp, hq0] using hcolorsEq.symm
  have hconstant (i j : ℤ) : M i j = M 0 0 := by
    have hf := hform i j
    rcases Int.emod_two_eq_zero_or_one (i + j) with hzero | hone
    · simpa only [hzero] using hf
    · have hf1 : M i j = M 1 0 := by simpa only [hone] using hf
      exact hf1.trans h01.symm
  refine ⟨M 0 0, ?_⟩
  intro i j
  let i' : Fin a := i - x
  have hrot : rot i' = i := add_sub_cancel x i
  have hedge : cyclicCrossEdge A B hdisjoint i j =
      cyclicCrossEdge A' B hdisjoint' i' j := by
    apply Subtype.ext
    change s(A i, B j) = s(A (rot i'), B j)
    rw [hrot]
  rw [hedge]
  exact (hlift i' j).symm.trans (hconstant _ _)

theorem cross_colors_constant_of_indexed_bounds
    {k a b : ℕ} (hk : 5 ≤ k) (ha : 3 ≤ a ∧ a ≤ k - 1)
    (hb : 3 ≤ b ∧ b ≤ k - 1) (hsum : k + 1 ≤ a + b)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (A : Fin a → Fin n) (B : Fin b → Fin n)
    (hA : Function.Injective A) (hB : Function.Injective B)
    (hdisjoint : Disjoint (Set.range A) (Set.range B))
    (hAcycle : cycleGraph a ≤ (selectedGraph χ r).comap A)
    (hBcycle : cycleGraph b ≤ (selectedGraph χ r).comap B)
    (hpalette : ∀ i j, χ (cyclicCrossEdge A B hdisjoint i j) ∉ newColorUnion χ)
    (hno : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (hpair : ∀ i j, k - 1 ≤ ((selectedGraph χ r).comap A).degree i +
      ((selectedGraph χ r).comap B).degree j) :
    ∃ c : C, ∀ i j, χ (cyclicCrossEdge A B hdisjoint i j) = c := by
  let : NeZero a := ⟨by omega⟩
  let : NeZero b := ⟨by omega⟩
  by_cases hodd : ¬ Even a ∨ ¬ Even b ∨ ¬ Even k
  · let M := liftedCrossColor χ A B (by omega) (by omega) hdisjoint
    have hconstant : ∀ i j : ℤ, M i j = M 0 0 :=
      (cross_matrix_forms hk ha hb hsum χ r A B hA hB hdisjoint
        hAcycle hBcycle hpalette hno).2 hodd
    refine ⟨M 0 0, ?_⟩
    intro i j
    have h := hconstant (i.val : ℤ) (j.val : ℤ)
    simpa only [M, liftedCrossColor, Int.cast_natCast, Fin.cast_val_eq_self] using h
  · have haEven : Even a := by
      by_contra h
      exact hodd (Or.inl h)
    have hbEven : Even b := by
      by_contra h
      exact hodd (Or.inr (Or.inl h))
    have hkEven : Even k := by
      by_contra h
      exact hodd (Or.inr (Or.inr h))
    rcases exists_same_parity_edge_of_cross_degree_sum hk hkEven
        ha.1 haEven ha.2 hb.1 hbEven hb.2
        ((selectedGraph χ r).comap A) ((selectedGraph χ r).comap B) (by
          intro i j
          exact Eq.mp
            (congrArg₂ (fun da db : ℕ => k - 1 ≤ da + db)
              (congrArg
                (fun inst : Fintype (((selectedGraph χ r).comap A).neighborSet i) =>
                  @SimpleGraph.degree _ ((selectedGraph χ r).comap A) i inst)
                (Subsingleton.elim _ _))
              (congrArg
                (fun inst : Fintype (((selectedGraph χ r).comap B).neighborSet j) =>
                  @SimpleGraph.degree _ ((selectedGraph χ r).comap B) j inst)
                (Subsingleton.elim _ _)))
            (hpair i j)) with
      ⟨x, y, hxy, hparity⟩ | ⟨x, y, hxy, hparity⟩
    · exact constant_of_first_same_parity_chord hk ha hb hsum hkEven haEven hbEven
        χ r A B hA hB hdisjoint hAcycle hBcycle hpalette hno x y hxy hparity
    · have hdisjointBA := hdisjoint.symm
      have hedge (i : Fin b) (j : Fin a) :
          cyclicCrossEdge B A hdisjointBA i j = cyclicCrossEdge A B hdisjoint j i := by
        apply Subtype.ext
        exact Sym2.eq_swap
      have hpaletteBA (i : Fin b) (j : Fin a) :
          χ (cyclicCrossEdge B A hdisjointBA i j) ∉ newColorUnion χ := by
        rw [hedge]
        exact hpalette j i
      obtain ⟨c, hc⟩ := constant_of_first_same_parity_chord hk hb ha (by omega)
        hkEven hbEven haEven χ r B A hB hA hdisjointBA hBcycle hAcycle
        hpaletteBA hno x y hxy hparity
      refine ⟨c, ?_⟩
      intro i j
      exact (congrArg χ (hedge j i)).symm.trans (hc j i)

/-- Original high-NEW assumptions force one original host color on every
edge between two distinct WHOLE selected components, for every valid choice.
No cyclic order, palette, degree, chord or joined-rainbow premise is added. -/
theorem cross_component_colors_constant
    {k : ℕ} (hk : 5 ≤ k)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (hnew : ∀ v : Fin n, 2 ≤ (newColors χ v).card)
    (hpair : ∀ u v : Fin n, u ≠ v →
      k - 1 ≤ (newColors χ u).card + (newColors χ v).card)
    (hno : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (D E : (selectedGraph χ r).ConnectedComponent) (hDE : D ≠ E) :
    ∃ c : C, ∀ u v : Fin n, u ∈ D.supp → v ∈ E.supp →
      ∀ e : HostEdge n, e.val = s(u, v) → χ e = c := by
  obtain ⟨ha, haUpper, haLower, hb, hbUpper, hbLower,
      A, B, hA, hB, hontoA, hontoB, hrangeA, hrangeB,
      hcycleA, hcycleB, _hdegreeA, _hdegreeB, hdistinct, hcross⟩ :=
    distinct_components_cyclic_indices_cross_degree hk χ r hnew hpair hno D E hDE
  have hdisjoint : Disjoint (Set.range A) (Set.range B) :=
    Set.disjoint_range_iff.mpr hdistinct
  have hAmem (i) : A i ∈ D.supp := by
    rw [← hrangeA]
    exact ⟨i, rfl⟩
  have hBmem (j) : B j ∈ E.supp := by
    rw [← hrangeB]
    exact ⟨j, rfl⟩
  have hpalette (i j) : χ (cyclicCrossEdge A B hdisjoint i j) ∉ newColorUnion χ :=
    cross_edge_color_not_new_union hk χ r hnew hpair hno D E hDE
      (A i) (B j) (hAmem i) (hBmem j) (cyclicCrossEdge A B hdisjoint i j) rfl
  obtain ⟨c, hc⟩ := cross_colors_constant_of_indexed_bounds hk
    ⟨ha, haUpper⟩ ⟨hb, hbUpper⟩ (by omega) χ r A B hA hB hdisjoint
    hcycleA hcycleB hpalette hno hcross
  refine ⟨c, ?_⟩
  intro u v hu hv e he
  obtain ⟨i, hi⟩ := hontoA ⟨u, hu⟩
  obtain ⟨j, hj⟩ := hontoB ⟨v, hv⟩
  have hedge : e = cyclicCrossEdge A B hdisjoint i j := by
    apply Subtype.ext
    change e.val = s(A i, B j)
    rw [hi, hj]
    exact he
  rw [hedge]
  exact hc i j

end ErdosProblems.AntiRamseyCycleOriginalCrossComponentConstancy
