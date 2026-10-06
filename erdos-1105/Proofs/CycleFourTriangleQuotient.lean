module

public import CycleNewRepresentative
public import CycleWeakCount
public import CycleFourCopies
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Tactic

@[expose] public section

/-!
Conditional `k = 4` triangle-block color quotient.
-/

namespace ErdosProblems.AntiRamseyCycleFourTriangleQuotient

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyWeakCount
open ErdosProblems.AntiRamseyCycleFour

/-- Explicit conditional interface: each color on an edge internal to a
block is NEW at both endpoints. Its host occurrence is then unique. -/
def TriangleBlockOwnColors {n t : ℕ} {C : Type*} [DecidableEq C]
    (χ : TopEdgeLabeling (Fin n) C) (b : Fin n → Fin t) : Prop :=
  ∀ (a d : Fin n) (had : a ≠ d), b a = b d →
    χ.get a d had ∈ newColors χ a ∧ χ.get a d had ∈ newColors χ d

/-- Bridge from the explicit two-NEW premise to the
globally unique host occurrence of an internal edge color. -/
theorem within_block_color_unique_edge {n t : ℕ} {C : Type*} [DecidableEq C]
    (χ : TopEdgeLabeling (Fin n) C) (b : Fin n → Fin t)
    (hown : TriangleBlockOwnColors χ b)
    (a d : Fin n) (had : a ≠ d) (hbd : b a = b d)
    (e : (⊤ : SimpleGraph (Fin n)).edgeSet)
    (he : χ e = χ.get a d had) : e.val = s(a, d) := by
  obtain ⟨ha, hd⟩ := hown a d had hbd
  exact shared_newColor_unique_edge χ a d had ha hd e he

/-- Rewriting of the unique-host-color conclusion for
the `get` form of a second edge. -/
theorem within_block_color_collision_pair {n t : ℕ} {C : Type*}
    [DecidableEq C] (χ : TopEdgeLabeling (Fin n) C)
    (b : Fin n → Fin t) (hown : TriangleBlockOwnColors χ b)
    (a d : Fin n) (had : a ≠ d) (hbd : b a = b d)
    (u v : Fin n) (huv : u ≠ v)
    (hcolor : χ.get u v huv = χ.get a d had) :
    s(u, v) = s(a, d) := by
  let e : (⊤ : SimpleGraph (Fin n)).edgeSet :=
    ⟨s(u, v), (top_adj _ _).mpr huv⟩
  have he : χ e = χ.get a d had := by
    change χ.get u v huv = χ.get a d had
    exact hcolor
  exact within_block_color_unique_edge χ b hown a d had hbd e he

/-- Opposite cross-grid equalities on a pair of sets
with third points force every entry to be equal. The third-point hypotheses
are later supplied by three-vertex block fibers. -/
theorem opposite_cross_matrix_constant {A B C : Type*} (M : A → B → C)
    (hthirdA : ∀ a a' : A, ∃ a'' : A, a'' ≠ a ∧ a'' ≠ a')
    (hthirdB : ∀ b b' : B, ∃ b'' : B, b'' ≠ b ∧ b'' ≠ b')
    (hopp : ∀ (a a' : A) (b b' : B), a ≠ a' → b ≠ b' →
      M a b = M a' b') :
    ∀ (a a' : A) (b b' : B), M a b = M a' b' := by
  intro a a' b b'
  by_cases haa : a = a'
  · subst a'
    by_cases hbb : b = b'
    · subst b'
      rfl
    · obtain ⟨a'', haother, _⟩ := hthirdA a a
      obtain ⟨b'', hbother, hb'other⟩ := hthirdB b b'
      calc
        M a b = M a'' b'' := hopp a a'' b b'' haother.symm hbother.symm
        _ = M a b' := (hopp a a'' b' b'' haother.symm hb'other.symm).symm
  · by_cases hbb : b = b'
    · subst b'
      obtain ⟨a'', haother, ha'other⟩ := hthirdA a a'
      obtain ⟨b'', hbother, _⟩ := hthirdB b b
      calc
        M a b = M a'' b'' := hopp a a'' b b'' haother.symm hbother.symm
        _ = M a' b := (hopp a' a'' b b'' ha'other.symm hbother.symm).symm
    · exact hopp a a' b b' haa hbb

/-- Finite version of the third-point premise. -/
theorem third_vertex_of_three_le_card {A : Type*} [DecidableEq A]
    (S : Finset A) (hcard : 3 ≤ S.card) (a d : A) :
    ∃ z ∈ S, z ≠ a ∧ z ≠ d := by
  have hlt : 2 < S.card := by omega
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ :=
    Finset.two_lt_card.mp hlt
  by_cases hpa : p ≠ a ∧ p ≠ d
  · exact ⟨p, hp, hpa.1, hpa.2⟩
  by_cases hqa : q ≠ a ∧ q ≠ d
  · exact ⟨q, hq, hqa.1, hqa.2⟩
  push Not at hpa hqa
  exact ⟨r, hr, by grind, by grind⟩

def squareMap {n : ℕ} (x u v y : Fin n) (i : Fin 4) : Fin n :=
  if i = 0 then x else if i = 1 then u else if i = 2 then v else y

theorem squareMap_injective {n : ℕ} {x u v y : Fin n}
    (hxu : x ≠ u) (hxv : x ≠ v) (hxy : x ≠ y)
    (huv : u ≠ v) (huy : u ≠ y) (hvy : v ≠ y) :
    Function.Injective (squareMap x u v y) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [squareMap] at hij ⊢ <;> grind

/-- Generic host-square constructor. Six unequal edge
labels on four distinct host vertices produce a literal rainbow ordinary
`C₄.Copy`. -/
theorem rainbow_square_of_six_color_inequalities {n : ℕ} {C : Type*}
    (χ : TopEdgeLabeling (Fin n) C) {x u v y : Fin n}
    (hxu : x ≠ u) (hxv : x ≠ v) (hxy : x ≠ y)
    (huv : u ≠ v) (huy : u ≠ y) (hvy : v ≠ y)
    (h01_12 : χ.get x u hxu ≠ χ.get u v huv)
    (h01_23 : χ.get x u hxu ≠ χ.get v y hvy)
    (h01_30 : χ.get x u hxu ≠ χ.get y x hxy.symm)
    (h12_23 : χ.get u v huv ≠ χ.get v y hvy)
    (h12_30 : χ.get u v huv ≠ χ.get y x hxy.symm)
    (h23_30 : χ.get v y hvy ≠ χ.get y x hxy.symm) :
    ∃ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  have hρ : Function.Injective (squareMap x u v y) :=
    squareMap_injective hxu hxv hxy huv huy hvy
  let φ : (cycleGraph 4) →g (⊤ : SimpleGraph (Fin n)) :=
    ⟨squareMap x u v y, by
      intro i j hij
      exact (top_adj _ _).mpr (hρ.ne ((cycleGraph 4).ne_of_adj hij))⟩
  let f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)) := ⟨φ, hρ⟩
  have hcol01 : (EdgeLabeling.pullback χ f.toHom) sourceEdge01 =
      χ.get x u hxu := by
    change χ (f.toHom.mapEdgeSet sourceEdge01) = χ.get x u hxu
    apply congrArg χ
    apply Subtype.ext
    change Sym2.map (squareMap x u v y) (s((0 : Fin 4), 1)) = s(x, u)
    rw [Sym2.map_mk]
    simp [squareMap]
  have hcol12 : (EdgeLabeling.pullback χ f.toHom) sourceEdge12 =
      χ.get u v huv := by
    change χ (f.toHom.mapEdgeSet sourceEdge12) = χ.get u v huv
    apply congrArg χ
    apply Subtype.ext
    change Sym2.map (squareMap x u v y) (s((1 : Fin 4), 2)) = s(u, v)
    rw [Sym2.map_mk]
    simp [squareMap]
  have hcol23 : (EdgeLabeling.pullback χ f.toHom) sourceEdge23 =
      χ.get v y hvy := by
    change χ (f.toHom.mapEdgeSet sourceEdge23) = χ.get v y hvy
    apply congrArg χ
    apply Subtype.ext
    change Sym2.map (squareMap x u v y) (s((2 : Fin 4), 3)) = s(v, y)
    rw [Sym2.map_mk]
    simp [squareMap]
  have hcol30 : (EdgeLabeling.pullback χ f.toHom) sourceEdge30 =
      χ.get y x hxy.symm := by
    change χ (f.toHom.mapEdgeSet sourceEdge30) = χ.get y x hxy.symm
    apply congrArg χ
    apply Subtype.ext
    change Sym2.map (squareMap x u v y) (s((3 : Fin 4), 0)) = s(y, x)
    rw [Sym2.map_mk]
    simp [squareMap]
  refine ⟨f, ?_⟩
  intro e₁ e₂ heq
  rcases sourceEdge_cases e₁ with h₁ | h₁ | h₁ | h₁ <;>
    rcases sourceEdge_cases e₂ with h₂ | h₂ | h₂ | h₂ <;>
    subst e₁ <;> subst e₂ <;>
    simp_all

/-- Two same-block internal edges with globally unique
colors force the opposite pair of cross edges to have the same color. No selected adjacency is assumed for the two cross edges. -/
theorem opposite_cross_colors_eq {n t : ℕ} {C : Type*} [DecidableEq C]
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    (b : Fin n → Fin t) (hown : TriangleBlockOwnColors χ b)
    {x u v y : Fin n}
    (hxu : x ≠ u) (hxv : x ≠ v) (hxy : x ≠ y)
    (huv : u ≠ v) (huy : u ≠ y) (hvy : v ≠ y)
    (hblockA : b x = b u) (hblockB : b v = b y) :
    χ.get u v huv = χ.get y x hxy.symm := by
  have h01_12 : χ.get x u hxu ≠ χ.get u v huv := by
    intro hcolor
    have hp := within_block_color_collision_pair χ b hown
      x u hxu hblockA u v huv hcolor.symm
    rcases Sym2.eq_iff.mp hp with h | h <;> grind
  have h01_23 : χ.get x u hxu ≠ χ.get v y hvy := by
    intro hcolor
    have hp := within_block_color_collision_pair χ b hown
      x u hxu hblockA v y hvy hcolor.symm
    rcases Sym2.eq_iff.mp hp with h | h <;> grind
  have h01_30 : χ.get x u hxu ≠ χ.get y x hxy.symm := by
    intro hcolor
    have hp := within_block_color_collision_pair χ b hown
      x u hxu hblockA y x hxy.symm hcolor.symm
    rcases Sym2.eq_iff.mp hp with h | h <;> grind
  have h12_23 : χ.get u v huv ≠ χ.get v y hvy := by
    intro hcolor
    have hp := within_block_color_collision_pair χ b hown
      v y hvy hblockB u v huv hcolor
    rcases Sym2.eq_iff.mp hp with h | h <;> grind
  have h23_30 : χ.get v y hvy ≠ χ.get y x hxy.symm := by
    intro hcolor
    have hp := within_block_color_collision_pair χ b hown
      v y hvy hblockB y x hxy.symm hcolor.symm
    rcases Sym2.eq_iff.mp hp with h | h <;> grind
  by_contra h12_30
  obtain ⟨f, hf⟩ := rainbow_square_of_six_color_inequalities χ
    hxu hxv hxy huv huy hvy h01_12 h01_23 h01_30
    h12_23 h12_30 h23_30
  exact hno f hf

/-- All cross edges between two three-vertex fibers
have the same color. The opposite-corner equalities are transported to
the two fiber subtype index sets before applying the pure matrix lemma. -/
theorem cross_color_constant_on_triangle_blocks {n t : ℕ}
    {C : Type*} [DecidableEq C]
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    (b : Fin n → Fin t)
    (hsize : ∀ i : Fin t, (blockFiber b i).card = 3)
    (hown : TriangleBlockOwnColors χ b)
    (i j : Fin t) (hij : i ≠ j)
    (a d : Fin n) (had : a ≠ d) (ha : b a = i) (hd : b d = j)
    (a' d' : Fin n) (had' : a' ≠ d') (ha' : b a' = i)
    (hd' : b d' = j) :
    χ.get a d had = χ.get a' d' had' := by
  let A : Type := {v : Fin n // b v = i}
  let B : Type := {v : Fin n // b v = j}
  have hcross : ∀ (x : A) (y : B), x.val ≠ y.val := by
    intro x y heq
    apply hij
    calc
      i = b x.val := x.property.symm
      _ = b y.val := congrArg b heq
      _ = j := y.property
  let M : A → B → C := fun x y => χ.get x.val y.val (hcross x y)
  have hThirdA : ∀ x x' : A, ∃ z : A, z ≠ x ∧ z ≠ x' := by
    intro x x'
    obtain ⟨z, hz, hzx, hzx'⟩ :=
      third_vertex_of_three_le_card (blockFiber b i)
        (by simp [hsize i]) x.val x'.val
    have hzblock : b z = i := by simpa [blockFiber] using hz
    refine ⟨⟨z, hzblock⟩, ?_, ?_⟩
    · intro heq
      exact hzx (congrArg Subtype.val heq)
    · intro heq
      exact hzx' (congrArg Subtype.val heq)
  have hThirdB : ∀ y y' : B, ∃ z : B, z ≠ y ∧ z ≠ y' := by
    intro y y'
    obtain ⟨z, hz, hzy, hzy'⟩ :=
      third_vertex_of_three_le_card (blockFiber b j)
        (by simp [hsize j]) y.val y'.val
    have hzblock : b z = j := by simpa [blockFiber] using hz
    refine ⟨⟨z, hzblock⟩, ?_, ?_⟩
    · intro heq
      exact hzy (congrArg Subtype.val heq)
    · intro heq
      exact hzy' (congrArg Subtype.val heq)
  have hOpp : ∀ (x x' : A) (y y' : B), x ≠ x' → y ≠ y' →
      M x y = M x' y' := by
    intro x x' y y' hxx' hyy'
    have hxx'val : x.val ≠ x'.val := by
      intro heq
      exact hxx' (Subtype.ext heq)
    have hyy'val : y.val ≠ y'.val := by
      intro heq
      exact hyy' (Subtype.ext heq)
    have hop : χ.get x.val y.val (hcross x y) =
        χ.get y'.val x'.val (hcross x' y').symm :=
      opposite_cross_colors_eq χ hno b hown
        hxx'val.symm (hcross x' y) (hcross x' y')
        (hcross x y) (hcross x y') hyy'val
        (x'.property.trans x.property.symm)
        (y.property.trans y'.property.symm)
    change χ.get x.val y.val (hcross x y) =
      χ.get x'.val y'.val (hcross x' y')
    calc
      χ.get x.val y.val (hcross x y) =
          χ.get y'.val x'.val (hcross x' y').symm := hop
      _ = χ.get x'.val y'.val (hcross x' y') := by
        simpa using (SimpleGraph.EdgeLabeling.get_comm (C := χ)
          x'.val y'.val (hcross x' y').symm)
  have hconstant := opposite_cross_matrix_constant M hThirdA hThirdB hOpp
  let aa : A := ⟨a, ha⟩
  let aa' : A := ⟨a', ha'⟩
  let dd : B := ⟨d, hd⟩
  let dd' : B := ⟨d', hd'⟩
  simpa [M, aa, aa', dd, dd'] using hconstant aa aa' dd dd'

/-- Conditional `k = 4` color quotient from an explicit partition into
three-vertex fibers whose internal edge colors are NEW at both endpoints.
The selected-triangle component-to-fiber construction is separate. -/
theorem triangle_block_quotient {n t : ℕ} {C : Type*} [DecidableEq C]
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    (b : Fin n → Fin t) (_ht : 1 ≤ t)
    (hsize : ∀ i : Fin t, (blockFiber b i).card = 3)
    (hown : TriangleBlockOwnColors χ b) :
    ∃ ψ : TopEdgeLabeling (Fin t) C,
      (∀ (a d : Fin n) (had : a ≠ d) (hbd : b a ≠ b d),
        χ.get a d had = ψ.get (b a) (b d) hbd) ∧
      ErdosProblems.AntiRamseyTriangle.NoRainbowTriangle ψ := by
  classical
  have hnonempty : ∀ i : Fin t, ∃ a : Fin n, b a = i := by
    intro i
    have hpos : 0 < (blockFiber b i).card := by simp [hsize i]
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
    exact ⟨a, by simpa [blockFiber] using ha⟩
  choose r hr using hnonempty
  have hinj : Function.Injective r := by
    intro i j heq
    calc
      i = b (r i) := (hr i).symm
      _ = b (r j) := congrArg b heq
      _ = j := hr j
  let emb : Fin t ↪ Fin n := ⟨r, hinj⟩
  let ψ : TopEdgeLabeling (Fin t) C := TopEdgeLabeling.pullback χ emb
  have hpull : ∀ (i j : Fin t) (hij : i ≠ j),
      ψ.get i j hij = χ.get (r i) (r j) (hinj.ne hij) := by
    intro i j hij
    simp [ψ, emb, TopEdgeLabeling.pullback, EdgeLabeling.get,
      EdgeLabeling.pullback_apply, Hom.mapEdgeSet, Sym2.map_mk]
  have hcrosslabel : ∀ (a d : Fin n) (had : a ≠ d)
      (hbd : b a ≠ b d),
      χ.get a d had = ψ.get (b a) (b d) hbd := by
    intro a d had hbd
    have hrepne : r (b a) ≠ r (b d) := hinj.ne hbd
    have hconst := cross_color_constant_on_triangle_blocks χ hno b
      hsize hown (b a) (b d) hbd
      a d had rfl rfl (r (b a)) (r (b d)) hrepne
      (hr (b a)) (hr (b d))
    calc
      χ.get a d had = χ.get (r (b a)) (r (b d)) hrepne := hconst
      _ = ψ.get (b a) (b d) hbd := (hpull (b a) (b d) hbd).symm
  have htriple : ErdosProblems.AntiRamseyTriangle.NoRainbowTriangle ψ := by
    intro i j k hij hjk hki
    by_contra hrepeat
    have hdiff12_23 : ψ.get i j hij ≠ ψ.get j k hjk := by
      intro heq
      exact hrepeat (Or.inl heq)
    have hdiff23_30 : ψ.get j k hjk ≠ ψ.get k i hki := by
      intro heq
      exact hrepeat (Or.inr (Or.inl heq))
    have hdiff30_12 : ψ.get k i hki ≠ ψ.get i j hij := by
      intro heq
      exact hrepeat (Or.inr (Or.inr heq))
    obtain ⟨z, hz, hzr, _⟩ :=
      third_vertex_of_three_le_card (blockFiber b i)
        (by simp [hsize i]) (r i) (r i)
    have hzi : b z = i := by simpa [blockFiber] using hz
    have hzrj : z ≠ r j := by
      intro heq
      apply hij
      calc
        i = b z := hzi.symm
        _ = b (r j) := congrArg b heq
        _ = j := hr j
    have hzrk : z ≠ r k := by
      intro heq
      apply hki
      calc
        k = b (r k) := (hr k).symm
        _ = b z := congrArg b heq.symm
        _ = i := hzi
    have hrij : r i ≠ r j := hinj.ne hij
    have hrik : r i ≠ r k := hinj.ne hki.symm
    have hrjk : r j ≠ r k := hinj.ne hjk
    have hcol12 : χ.get (r i) (r j) hrij = ψ.get i j hij := by
      have hbd : b (r i) ≠ b (r j) := by simpa [hr i, hr j] using hij
      simpa [hr i, hr j] using hcrosslabel (r i) (r j) hrij hbd
    have hcol23 : χ.get (r j) (r k) hrjk = ψ.get j k hjk := by
      have hbd : b (r j) ≠ b (r k) := by simpa [hr j, hr k] using hjk
      simpa [hr j, hr k] using hcrosslabel (r j) (r k) hrjk hbd
    have hcol30 : χ.get (r k) z hzrk.symm = ψ.get k i hki := by
      have hbd : b (r k) ≠ b z := by simpa [hr k, hzi] using hki
      simpa [hr k, hzi] using hcrosslabel (r k) z hzrk.symm hbd
    have hblock : b z = b (r i) := hzi.trans (hr i).symm
    have h01_12 : χ.get z (r i) hzr ≠ χ.get (r i) (r j) hrij := by
      intro heq
      have hp := within_block_color_collision_pair χ b hown
        z (r i) hzr hblock (r i) (r j) hrij heq.symm
      rcases Sym2.eq_iff.mp hp with h | h <;> grind
    have h01_23 : χ.get z (r i) hzr ≠ χ.get (r j) (r k) hrjk := by
      intro heq
      have hp := within_block_color_collision_pair χ b hown
        z (r i) hzr hblock (r j) (r k) hrjk heq.symm
      rcases Sym2.eq_iff.mp hp with h | h <;> grind
    have h01_30 : χ.get z (r i) hzr ≠ χ.get (r k) z hzrk.symm := by
      intro heq
      have hp := within_block_color_collision_pair χ b hown
        z (r i) hzr hblock (r k) z hzrk.symm heq.symm
      rcases Sym2.eq_iff.mp hp with h | h <;> grind
    have h12_23 : χ.get (r i) (r j) hrij ≠
        χ.get (r j) (r k) hrjk := by
      simpa only [hcol12, hcol23] using hdiff12_23
    have h12_30 : χ.get (r i) (r j) hrij ≠
        χ.get (r k) z hzrk.symm := by
      simpa only [hcol12, hcol30] using hdiff30_12.symm
    have h23_30 : χ.get (r j) (r k) hrjk ≠
        χ.get (r k) z hzrk.symm := by
      simpa only [hcol23, hcol30] using hdiff23_30
    obtain ⟨f, hf⟩ := rainbow_square_of_six_color_inequalities χ
      hzr hzrj hzrk hrij hrik hrjk h01_12 h01_23 h01_30
      h12_23 h12_30 h23_30
    exact hno f hf
  exact ⟨ψ, hcrosslabel, htriple⟩

end ErdosProblems.AntiRamseyCycleFourTriangleQuotient
