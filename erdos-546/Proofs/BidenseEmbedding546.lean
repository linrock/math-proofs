module

public import Mathlib


@[expose] public section

/-!
# Greedy bounded-degree embedding and sparse-cut contrapositive

Formalizes the bounded-degree embedding argument underlying Sudakov's Lemma 2.4:
partitioning a graph of maximum degree $\Delta$ into $\Delta + 1$ independent
color classes, splitting the host into equal disjoint reservoirs, and embedding
vertices greedily unless a pair of subsets violates local density.
-/

namespace Erdos546

open Finset
open scoped Classical

variable {V W : Type*} [Fintype V] [Fintype W]

/-- Greedy vertex coloring with one more color than a degree upper bound. -/
theorem colorable_of_degree_le (G : SimpleGraph V) (Δ : ℕ)
    (hdegree : ∀ v, G.degree v ≤ Δ) : G.Colorable (Δ + 1) := by
  classical
  have hpartial : ∀ s : Finset V, ∃ f : V → Fin (Δ + 1),
      ∀ a ∈ s, ∀ b ∈ s, G.Adj a b → f a ≠ f b := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨fun _ => ⟨0, by omega⟩, by simp⟩
    | @insert v s hv ih =>
      obtain ⟨f, hadj⟩ := ih
      let B : Finset (Fin (Δ + 1)) := (s.filter fun u => G.Adj v u).image f
      have hB : B.card ≤ Δ := by
        calc
          B.card ≤ (s.filter fun u => G.Adj v u).card := Finset.card_image_le
          _ ≤ (G.neighborFinset v).card := Finset.card_le_card (by
            intro u hu
            exact (G.mem_neighborFinset v u).mpr (Finset.mem_filter.mp hu).2)
          _ = G.degree v := G.card_neighborFinset_eq_degree v
          _ ≤ Δ := hdegree v
      have hlt : B.card < (Finset.univ : Finset (Fin (Δ + 1))).card := by
        simp only [Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨x, _, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      let f' : V → Fin (Δ + 1) := Function.update f v x
      have hf' : f' v = x := by simp [f']
      have hfs : ∀ u ∈ s, f' u = f u := by
        intro u hu
        have huv : u ≠ v := by rintro rfl; exact hv hu
        exact Function.update_of_ne huv x f
      have hfx : ∀ u ∈ s, G.Adj v u → x ≠ f u := by
        intro u hu h vu
        exact hx (Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, h⟩, vu.symm⟩)
      refine ⟨f', ?_⟩
      intro a ha b hb hab
      simp only [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact (hab.ne rfl).elim
      · rw [hf', hfs b hb]
        exact hfx b hb hab
      · rw [hfs a ha, hf']
        exact (hfx a ha hab.symm).symm
      · rw [hfs a ha, hfs b hb]
        exact hadj a ha b hb hab
  obtain ⟨f, hf⟩ := hpartial Finset.univ
  exact ⟨{
    toFun := f
    map_rel' := fun {a b} hab => by
      simpa using hf a (Finset.mem_univ a) b (Finset.mem_univ b) hab }⟩

/-- Equal disjoint reservoirs with exact integral sizes. The finite remainder
of the host is left unused. -/
theorem exists_equal_disjoint_reservoirs (c q : ℕ)
    (hsize : c * q ≤ Fintype.card W) :
    ∃ A : Fin c → Finset W, (∀ j, (A j).card = q) ∧
      ∀ i j, i ≠ j → Disjoint (A i) (A j) := by
  classical
  obtain ⟨e⟩ : Nonempty ((Fin c × Fin q) ↪ W) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hsize)
  let A : Fin c → Finset W := fun j =>
    Finset.univ.image fun k : Fin q => e (j, k)
  refine ⟨A, ?_, ?_⟩
  · intro j
    have hinj : Function.Injective (fun k : Fin q => e (j, k)) := by
      intro k l h
      exact (Prod.mk.inj (e.injective h)).2
    simpa [A] using Finset.card_image_of_injective (Finset.univ : Finset (Fin q)) hinj
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hxi
    obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hxj
    exact hij (Prod.mk.inj (e.injective (hk.trans hl.symm))).1

theorem greedy_small_pow_budget (ε : ℝ) (hε : 0 ≤ ε)
    (hhalf : ε ≤ 1 / 2) (r : ℕ) : ((r : ℝ) + 1) * ε ^ r ≤ 1 := by
  have hhalfpower : ((r : ℝ) + 1) * (1 / 2 : ℝ) ^ r ≤ 1 := by
    induction r with
    | zero => norm_num
    | succ r ih =>
      have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      have hp : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ r := pow_nonneg (by norm_num) r
      simp only [Nat.cast_succ, pow_succ]
      nlinarith
  exact le_trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hε hhalf r) (by positivity)) hhalfpower

theorem greedy_power_margin (ε : ℝ) (hε : 0 ≤ ε)
    (hhalf : ε ≤ 1 / 2) (Δ b r : ℕ) (hbr : b + r ≤ Δ) :
    (r : ℝ) * ε ^ Δ + ε ^ Δ ≤ ε ^ b := by
  have hεone : ε ≤ 1 := by linarith
  have hpow : ε ^ Δ ≤ ε ^ (b + r) :=
    pow_le_pow_of_le_one hε hεone hbr
  have hbudget := greedy_small_pow_budget ε hε hhalf r
  have hmul := mul_le_mul_of_nonneg_left hbudget (pow_nonneg hε b)
  have hscaled := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ (r : ℝ) + 1 by positivity)
  rw [pow_add] at hscaled
  nlinarith

omit [Fintype W] in
/-- The actual candidate-set embedding theorem. The host condition explicitly
bounds the low-degree vertices between distinct reservoirs. It is a local
bidensity condition, rather than an assumed embedding or a graph-theory axiom.
The sparse-cut contrapositive requires deriving this condition by averaging. -/
theorem copy_of_reservoir_bad_set_bounds (G : SimpleGraph V) (H : SimpleGraph W)
    (Δ q : ℕ) (ε : ℝ) (hε : 0 < ε) (hhalf : ε ≤ 1 / 2)
    (hdegree : ∀ v, G.degree v ≤ Δ)
    (c : G.Coloring (Fin (Δ + 1))) (A : Fin (Δ + 1) → Finset W)
    (hAcard : ∀ j, (A j).card = q)
    (hn : (Fintype.card V : ℝ) ≤ ε ^ Δ * q)
    (hbad : ∀ i j : Fin (Δ + 1), i ≠ j → ∀ C D : Finset W,
      C ⊆ A i → D ⊆ A j → ε ^ (Δ - 1) * q ≤ (D.card : ℝ) →
      ((C.filter fun z =>
        (((D.filter fun w => H.Adj z w).card : ℝ) < ε * D.card)).card : ℝ) ≤
        ε ^ Δ * q) :
    Nonempty (SimpleGraph.Copy G H) := by
  classical
  by_cases hV : Fintype.card V = 0
  · let _ : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    exact ⟨{
      toHom := { toFun := isEmptyElim, map_rel' := fun {a} => isEmptyElim a }
      injective' := fun a => isEmptyElim a }⟩
  have hεnonneg : 0 ≤ ε := le_of_lt hε
  have hεone : ε ≤ 1 := by linarith
  have hq : 0 < q := by
    by_contra h
    have hqzero : q = 0 := Nat.eq_zero_of_not_pos h
    simp only [hqzero, Nat.cast_zero, mul_zero] at hn
    have hcard : (0 : ℝ) < Fintype.card V := by exact_mod_cast Nat.pos_of_ne_zero hV
    linarith
  obtain ⟨w, _⟩ : (A ⟨0, by omega⟩).Nonempty :=
    Finset.card_pos.mp (by simpa [hAcard] using hq)
  let b : Finset V → V → ℕ := fun s y => (G.neighborFinset y ∩ s).card
  have hpartial : ∀ s : Finset V, ∃ (f : V → W) (C : V → Finset W),
      Set.InjOn f (s : Set V) ∧
      (∀ a ∈ s, ∀ a' ∈ s, G.Adj a a' → H.Adj (f a) (f a')) ∧
      ∀ y ∉ s, C y ⊆ A (c y) ∧
        (∀ u ∈ s, G.Adj y u → ∀ z ∈ C y, H.Adj z (f u)) ∧
        ε ^ b s y * q ≤ ((C y).card : ℝ) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨fun _ => w, fun y => A (c y), by simp [Set.InjOn], by simp, ?_⟩
      intro y _
      exact ⟨Subset.rfl, by simp, by simp [b, hAcard]⟩
    | @insert x s hx ih =>
      obtain ⟨f, C, hinj, hadj, hC⟩ := ih
      obtain ⟨hxA, hxadj, hxcard⟩ := hC x hx
      let R : Finset V := G.neighborFinset x \ s
      have hR : ∀ y ∈ R, y ∉ s ∧ G.Adj x y := by
        intro y hy
        exact ⟨(Finset.mem_sdiff.mp hy).2,
          (G.mem_neighborFinset x y).mp (Finset.mem_sdiff.mp hy).1⟩
      have hbr : b s x + R.card ≤ Δ := by
        have h := Finset.card_inter_add_card_sdiff (G.neighborFinset x) s
        simpa [b, R, G.card_neighborFinset_eq_degree] using h.le.trans (hdegree x)
      have hCmin : ∀ y ∈ R, ε ^ (Δ - 1) * q ≤ ((C y).card : ℝ) := by
        intro y hy
        obtain ⟨hys, hxy⟩ := hR y hy
        have hby : b s y + 1 ≤ Δ := by
          have hnot : x ∉ G.neighborFinset y ∩ s := by
            exact fun h => hx (Finset.mem_inter.mp h).2
          have hsub : insert x (G.neighborFinset y ∩ s) ⊆ G.neighborFinset y := by
            intro u hu
            rcases Finset.mem_insert.mp hu with rfl | hu
            · exact (G.mem_neighborFinset y _).mpr hxy.symm
            · exact (Finset.mem_inter.mp hu).1
          have hcount := Finset.card_le_card hsub
          rw [Finset.card_insert_of_notMem hnot, G.card_neighborFinset_eq_degree] at hcount
          exact hcount.trans (hdegree y)
        have hpow : ε ^ (Δ - 1) ≤ ε ^ b s y :=
          pow_le_pow_of_le_one hεnonneg hεone (by omega)
        exact (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg q)).trans (hC y hys).2.2
      let B : V → Finset W := fun y => (C x).filter fun z =>
        (((C y).filter fun w => H.Adj z w).card : ℝ) < ε * (C y).card
      have hB : ∀ y ∈ R, ((B y).card : ℝ) ≤ ε ^ Δ * q := by
        intro y hy
        obtain ⟨hys, hxy⟩ := hR y hy
        exact hbad (c x) (c y) (c.valid hxy) (C x) (C y) hxA
          (hC y hys).1 (hCmin y hy)
      have hsum : (∑ y ∈ R, ((B y).card : ℝ)) ≤ (R.card : ℝ) * (ε ^ Δ * q) := by
        calc
          (∑ y ∈ R, ((B y).card : ℝ)) ≤ ∑ y ∈ R, ε ^ Δ * q :=
            Finset.sum_le_sum hB
          _ = (R.card : ℝ) * (ε ^ Δ * q) := by simp
      have hs : s.card < Fintype.card V := by
        have hle := Finset.card_le_univ (insert x s)
        rw [Finset.card_insert_of_notMem hx] at hle
        omega
      have hus : ((s.image f).card : ℝ) < Fintype.card V := by
        exact_mod_cast lt_of_le_of_lt Finset.card_image_le hs
      have hmargin := mul_le_mul_of_nonneg_right
        (greedy_power_margin ε hεnonneg hhalf Δ (b s x) R.card hbr)
        (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
      have hbudget : ((s.image f).card : ℝ) + (∑ y ∈ R, ((B y).card : ℝ)) <
          ((C x).card : ℝ) := by nlinarith
      have hlt : ((s.image f) ∪ R.biUnion B).card < (C x).card := by
        have hbound := Finset.card_union_le (s.image f) (R.biUnion B)
        have hbound' := Finset.card_biUnion_le (s := R) (t := B)
        have hbudget' : (s.image f).card + (∑ y ∈ R, (B y).card) < (C x).card := by
          exact_mod_cast hbudget
        omega
      obtain ⟨z, hzC, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      have hzf : ∀ u ∈ s, f u ≠ z := by
        intro u hu huz
        exact hz (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, hu, huz⟩))
      have hzdegree : ∀ y ∈ R, ε * (C y).card ≤
          (((C y).filter fun w => H.Adj z w).card : ℝ) := by
        intro y hy
        by_contra h
        have hzB : z ∈ B y := Finset.mem_filter.mpr ⟨hzC, lt_of_not_ge h⟩
        exact hz (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨y, hy, hzB⟩))
      let f' : V → W := Function.update f x z
      let C' : V → Finset W := fun y =>
        if G.Adj y x then (C y).filter (fun w => H.Adj w z) else C y
      have hf' : f' x = z := by simp [f']
      have hfs : ∀ u ∈ s, f' u = f u := by
        intro u hu
        have hux : u ≠ x := by rintro rfl; exact hx hu
        exact Function.update_of_ne hux z f
      refine ⟨f', C', ?_, ?_, ?_⟩
      · intro a ha a' ha' heq
        simp only [Finset.mem_coe, Finset.mem_insert] at ha ha'
        rcases ha with rfl | ha <;> rcases ha' with rfl | ha'
        · rfl
        · rw [hf', hfs a' ha'] at heq
          exact (hzf a' ha' heq.symm).elim
        · rw [hfs a ha, hf'] at heq
          exact (hzf a ha heq).elim
        · apply hinj ha ha'
          simpa only [hfs a ha, hfs a' ha'] using heq
      · intro a ha a' ha' hab
        simp only [Finset.mem_insert] at ha ha'
        rcases ha with rfl | ha <;> rcases ha' with rfl | ha'
        · exact (hab.ne rfl).elim
        · rw [hf', hfs a' ha']
          exact hxadj a' ha' hab z hzC
        · rw [hfs a ha, hf']
          exact (hxadj a ha hab.symm z hzC).symm
        · rw [hfs a ha, hfs a' ha']
          exact hadj a ha a' ha' hab
      · intro y hy
        have hys : y ∉ s := fun h => hy (Finset.mem_insert_of_mem h)
        obtain ⟨hyA, hyadj, hycard⟩ := hC y hys
        have hCsub : C' y ⊆ C y := by
          simp only [C']
          split_ifs
          · exact Finset.filter_subset _ _
          · exact Subset.rfl
        refine ⟨hCsub.trans hyA, ?_, ?_⟩
        · intro u hu hyu w hw
          rcases Finset.mem_insert.mp hu with rfl | hu
          · rw [hf']
            have : C' y = (C y).filter fun w => H.Adj w z := by simp [C', hyu]
            have hw' : w ∈ (C y).filter (fun v => H.Adj v z) := by
              simpa only [this] using hw
            exact (Finset.mem_filter.mp hw').2
          · rw [hfs u hu]
            exact hyadj u hu hyu w (hCsub hw)
        · by_cases hyx : G.Adj y x
          · have hyR : y ∈ R := Finset.mem_sdiff.mpr
              ⟨(G.mem_neighborFinset x y).mpr hyx.symm, hys⟩
            have hnot : x ∉ G.neighborFinset y ∩ s :=
              fun h => hx (Finset.mem_inter.mp h).2
            have hb : b (insert x s) y = b s y + 1 := by
              dsimp [b]
              have hinter : G.neighborFinset y ∩ insert x s =
                  insert x (G.neighborFinset y ∩ s) := by
                ext u
                simp only [Finset.mem_inter, Finset.mem_insert]
                constructor
                · rintro ⟨hu, rfl | hu'⟩
                  · exact Or.inl rfl
                  · exact Or.inr ⟨hu, hu'⟩
                · rintro (rfl | hu)
                  · exact ⟨(G.mem_neighborFinset y _).mpr hyx, Or.inl rfl⟩
                  · exact ⟨hu.1, Or.inr hu.2⟩
              rw [hinter, Finset.card_insert_of_notMem hnot]
            have hfilter : ((C y).filter fun w => H.Adj w z) =
                ((C y).filter fun w => H.Adj z w) := by
              ext w
              simp only [Finset.mem_filter]
              exact and_congr_right (fun _ => H.adj_comm w z)
            simp only [C', hyx, ↓reduceIte, hb, pow_succ]
            rw [hfilter]
            have hscaled := mul_le_mul_of_nonneg_left hycard hεnonneg
            exact le_trans (by nlinarith : ε ^ b s y * ε * q ≤ ε * (C y).card)
              (hzdegree y hyR)
          · have hb : b (insert x s) y = b s y := by
              dsimp [b]
              congr 1
              ext u
              simp only [Finset.mem_inter, Finset.mem_insert]
              constructor
              · rintro ⟨hu, rfl | hu'⟩
                · exact (hyx ((G.mem_neighborFinset y _).mp hu)).elim
                · exact ⟨hu, hu'⟩
              · exact fun hu => ⟨hu.1, Or.inr hu.2⟩
            simpa [C', hyx, hb] using hycard
  obtain ⟨f, _, hinj, hadj, _⟩ := hpartial Finset.univ
  exact ⟨{
    toHom := {
      toFun := f
      map_rel' := fun {a a'} hab => hadj a (Finset.mem_univ a) a'
        (Finset.mem_univ a') hab }
    injective' := fun a a' hab => hinj (Finset.mem_univ a) (Finset.mem_univ a') hab }⟩

omit [Fintype W] in
/-- Absence of an unequal sparse cut bounds the bad vertices in disjoint
reservoirs. All cross-edge counting is exact. -/
theorem reservoir_bad_set_bound_of_no_sparse_cut (H : SimpleGraph W)
    (Δ q : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (A : Fin (Δ + 1) → Finset W)
    (hAdisjoint : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hcut : ∀ X Y : Finset W, Disjoint X Y →
      ε ^ Δ * q ≤ (X.card : ℝ) → ε ^ Δ * q ≤ (Y.card : ℝ) →
      ε * X.card * Y.card < ((H.interedges X Y).card : ℝ)) :
    ∀ i j : Fin (Δ + 1), i ≠ j → ∀ C D : Finset W,
      C ⊆ A i → D ⊆ A j → ε ^ (Δ - 1) * q ≤ (D.card : ℝ) →
      ((C.filter fun z =>
        (((D.filter fun w => H.Adj z w).card : ℝ) < ε * D.card)).card : ℝ) ≤
        ε ^ Δ * q := by
  classical
  intro i j hij C D hC hD hDcard
  let B : Finset W := C.filter fun z =>
    (((D.filter fun w => H.Adj z w).card : ℝ) < ε * D.card)
  by_contra h
  have hBcard : ε ^ Δ * q < (B.card : ℝ) := lt_of_not_ge h
  have hthreshold : 0 ≤ ε ^ Δ * (q : ℝ) := by positivity
  have hBpos : 0 < B.card := by
    have h : (0 : ℝ) < B.card := lt_of_le_of_lt hthreshold hBcard
    exact_mod_cast h
  have hdisjoint : Disjoint B D :=
    Finset.disjoint_of_subset_left ((Finset.filter_subset _ _).trans hC)
      (Finset.disjoint_of_subset_right hD (hAdisjoint i j hij))
  have hDlarge : ε ^ Δ * q ≤ (D.card : ℝ) :=
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one hε hεone (Nat.sub_le Δ 1))
      (Nat.cast_nonneg q)).trans hDcard
  have hcross := hcut B D hdisjoint hBcard.le hDlarge
  have heq : ((H.interedges B D).card : ℝ) =
      ∑ z ∈ B, ((D.filter fun w => H.Adj z w).card : ℝ) := by
    have heqNat : (H.interedges B D).card =
        ∑ z ∈ B, (D.filter fun w => H.Adj z w).card := by
      simp only [SimpleGraph.interedges_def, Finset.card_eq_sum_ones,
        Finset.sum_filter, Finset.sum_product]
    exact_mod_cast heqNat
  have hsum : (∑ z ∈ B, ((D.filter fun w => H.Adj z w).card : ℝ)) <
      ε * B.card * D.card := by
    calc
      (∑ z ∈ B, ((D.filter fun w => H.Adj z w).card : ℝ)) <
          ∑ _z ∈ B, ε * D.card :=
        Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp hBpos)
          (fun z hz => (Finset.mem_filter.mp hz).2)
      _ = ε * B.card * D.card := by simp; ring
  linarith

/-- A rounded finite version of the bounded-degree contrapositive, with
explicit natural reservoir size. The two sparse sides may have unequal
cardinalities; exact finite averaging is required to make them equal. -/
theorem sparse_unequal_pair_of_no_copy (G : SimpleGraph V) (H : SimpleGraph W)
    (Δ q : ℕ) (ε : ℝ) (hε : 0 < ε) (hhalf : ε ≤ 1 / 2)
    (hdegree : ∀ v, G.degree v ≤ Δ)
    (hsize : (Δ + 1) * q ≤ Fintype.card W)
    (hn : (Fintype.card V : ℝ) ≤ ε ^ Δ * q)
    (hfree : ¬ Nonempty (SimpleGraph.Copy G H)) :
    ∃ X Y : Finset W, Disjoint X Y ∧
      ε ^ Δ * q ≤ (X.card : ℝ) ∧ ε ^ Δ * q ≤ (Y.card : ℝ) ∧
      ((H.interedges X Y).card : ℝ) ≤ ε * X.card * Y.card := by
  classical
  obtain ⟨c⟩ := colorable_of_degree_le G Δ hdegree
  obtain ⟨A, hAcard, hAdisjoint⟩ := exists_equal_disjoint_reservoirs (W := W)
    (Δ + 1) q hsize
  by_contra h
  push Not at h
  have hcut : ∀ X Y : Finset W, Disjoint X Y →
      ε ^ Δ * q ≤ (X.card : ℝ) → ε ^ Δ * q ≤ (Y.card : ℝ) →
      ε * X.card * Y.card < ((H.interedges X Y).card : ℝ) := h
  have hbad := reservoir_bad_set_bound_of_no_sparse_cut H Δ q ε hε.le
    (by linarith) A hAdisjoint hcut
  exact hfree (copy_of_reservoir_bad_set_bounds G H Δ q ε hε hhalf hdegree
    c A hAcard hn hbad)

theorem half_host_le_floor_reservoir (N c : ℕ) (hc : 0 < c)
    (hN : c ≤ N) : N ≤ 2 * c * (N / c) := by
  have hq : 1 ≤ N / c := (Nat.le_div_iff_mul_le hc).mpr (by simpa using hN)
  have hmod : N % c < c := Nat.mod_lt N hc
  have hrem : N % c ≤ c * (N / c) :=
    hmod.le.trans (by simpa using Nat.mul_le_mul_left c hq)
  have hdiv := Nat.div_add_mod N c
  nlinarith

/-- Host-size version with a factor of two to absorb all integral reservoir
rounding. The size hypothesis is written after multiplication by `ε^Δ`,
which is equivalent to the usual inverse-power hypothesis for positive `ε`.
The remaining equal-size extraction is an independent averaging step. -/
theorem sparse_unequal_pair_of_no_copy_large_host (G : SimpleGraph V)
    (H : SimpleGraph W) (Δ : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hhalf : ε ≤ 1 / 2) (hdegree : ∀ v, G.degree v ≤ Δ)
    (hlarge : 2 * (Δ + 1 : ℝ) * Fintype.card V ≤ ε ^ Δ * Fintype.card W)
    (hfree : ¬ Nonempty (SimpleGraph.Copy G H)) :
    ∃ X Y : Finset W, Disjoint X Y ∧
      ε ^ Δ * Fintype.card W / (2 * (Δ + 1 : ℝ)) ≤ (X.card : ℝ) ∧
      ε ^ Δ * Fintype.card W / (2 * (Δ + 1 : ℝ)) ≤ (Y.card : ℝ) ∧
      ((H.interedges X Y).card : ℝ) ≤ ε * X.card * Y.card := by
  classical
  have hnpos : 0 < Fintype.card V := by
    by_contra h
    have hzero : Fintype.card V = 0 := Nat.eq_zero_of_not_pos h
    let _ : IsEmpty V := Fintype.card_eq_zero_iff.mp hzero
    exact hfree ⟨{
      toHom := { toFun := isEmptyElim, map_rel' := fun {a} => isEmptyElim a }
      injective' := fun a => isEmptyElim a }⟩
  let N := Fintype.card W
  let c := Δ + 1
  let q := N / c
  have hc : 0 < c := by dsimp [c]; omega
  have hp : 0 ≤ ε ^ Δ := pow_nonneg hε.le _
  have hpone : ε ^ Δ ≤ 1 := pow_le_one₀ hε.le (by linarith)
  have hnreal : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hnpos
  have hNreal : (c : ℝ) ≤ N := by
    dsimp [c, N]
    simp only [Nat.cast_add, Nat.cast_one]
    have hmul := mul_le_mul_of_nonneg_right hpone
      (Nat.cast_nonneg (Fintype.card W) : (0 : ℝ) ≤ Fintype.card W)
    have hleft := mul_le_mul_of_nonneg_left hnreal
      (show (0 : ℝ) ≤ 2 * (Δ + 1 : ℝ) by positivity)
    nlinarith
  have hN : c ≤ N := by exact_mod_cast hNreal
  have hfloor : N ≤ 2 * c * q := half_host_le_floor_reservoir N c hc hN
  have hfloorreal : (N : ℝ) ≤ 2 * c * q := by exact_mod_cast hfloor
  have hsize : (Δ + 1) * q ≤ Fintype.card W := by
    dsimp [q, c, N]
    exact Nat.mul_div_le _ _
  have hn : (Fintype.card V : ℝ) ≤ ε ^ Δ * q := by
    have hmul := mul_le_mul_of_nonneg_left hfloorreal hp
    have hcreal : (0 : ℝ) < c := by exact_mod_cast hc
    dsimp [c, N] at hmul hcreal
    simp only [Nat.cast_add, Nat.cast_one] at hmul hcreal
    apply le_of_mul_le_mul_left (a := 2 * (Δ + 1 : ℝ))
      (show 2 * (Δ + 1 : ℝ) * Fintype.card V ≤
        2 * (Δ + 1 : ℝ) * (ε ^ Δ * q) by nlinarith)
    positivity
  obtain ⟨X, Y, hdisjoint, hX, hY, hcross⟩ :=
    sparse_unequal_pair_of_no_copy G H Δ q ε hε hhalf hdegree hsize hn hfree
  have hthreshold : ε ^ Δ * Fintype.card W / (2 * (Δ + 1 : ℝ)) ≤ ε ^ Δ * q := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (Δ + 1 : ℝ))).mpr
    have hmul := mul_le_mul_of_nonneg_left hfloorreal hp
    dsimp [c, N] at hmul
    simp only [Nat.cast_add, Nat.cast_one] at hmul
    nlinarith
  exact ⟨X, Y, hdisjoint, hthreshold.trans hX, hthreshold.trans hY, hcross⟩

end Erdos546
