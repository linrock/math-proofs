module

public import Layer258
public import Mathlib.Combinatorics.SimpleGraph.Finsubgraph

/-
Copyright 2025-2026 The Formal Conjectures Authors.
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

public section

/-! ## Back edges -/

namespace Erdos58

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Closing a simple path of length at least two by an edge gives a cycle. -/
theorem cycle_of_path_and_edge {u v : V} (p : G.Walk u v)
    (hp : p.IsPath) (h : G.Adj v u) (hlen : 2 ≤ p.length) :
    (Walk.cons h p).IsCycle := by
  rw [Walk.isCycle_iff_isPath_tail_and_le_length]
  constructor
  · simpa using hp
  · simp only [Walk.length_cons]
    omega

/-- An edge between vertices of equal depth parity closes an actual odd cycle. -/
theorem same_parity_back_edge (D : NormalDepth G) {u v : V}
    (h : G.Adj u v) (hlt : D.depth u < D.depth v)
    (hpar : D.depth u % 2 = D.depth v % 2) :
    D.depth v - D.depth u + 1 ∈ G.oddCycleLengths := by
  obtain ⟨p, hp, hlen⟩ := D.back_path h hlt
  have htwo : 2 ≤ p.length := by omega
  exact mem_oddCycleLengths_intro
    (cycle_of_path_and_edge p hp h.symm htwo)
    (by simp [hlen]) (by
      rw [Nat.odd_iff]
      have hu := Nat.mod_two_eq_zero_or_one (D.depth u)
      have hv := Nat.mod_two_eq_zero_or_one (D.depth v)
      omega)

def earlierParityNeighbors (D : NormalDepth G) (v : V) : Set V :=
  {u | G.Adj u v ∧ D.depth u < D.depth v ∧ D.depth u % 2 = D.depth v % 2}

/-- Earlier same-parity neighbors inject into the set of odd cycle lengths. -/
theorem earlier_parity_neighbors_bound [Finite V] (D : NormalDepth G)
    (hfin : G.oddCycleLengths.Finite) (v : V) :
    (earlierParityNeighbors D v).ncard ≤ G.oddCycleLengths.ncard := by
  classical
  let f : V → ℕ := fun u ↦ D.depth v - D.depth u + 1
  have hmaps : Set.MapsTo f (earlierParityNeighbors D v) G.oddCycleLengths := by
    intro u hu
    exact same_parity_back_edge D hu.1 hu.2.1 hu.2.2
  have hinj : Set.InjOn f (earlierParityNeighbors D v) := by
    intro u hu w hw heq
    apply D.earlier_injective hu.1 hw.1 hu.2.1 hw.2.1
    dsimp [f] at heq
    have hu_lt : D.depth u < D.depth v := hu.2.1
    have hw_lt : D.depth w < D.depth v := hw.2.1
    omega
  exact Set.ncard_le_ncard_of_injOn f hmaps hinj hfin

/-! ## Compactness of the configuration space

Finite-to-infinite reduction for the exact Erdős #58 statement.
The finite graph theorem is an explicit premise throughout; this module does
not assume Gyárfás's structural theorem as an axiom or assert that it is proved.
-/

end Erdos58

universe u v

namespace SimpleGraph.Copy

variable {V : Type u} {W : Type v} {G : SimpleGraph V} {H : SimpleGraph W}

theorem cycleLengths_subset (f : SimpleGraph.Copy H G) :
    H.cycleLengths ⊆ G.cycleLengths := by
  intro n hn
  obtain ⟨a, w, hw, hlen⟩ := Erdos58.mem_cycleLengths hn
  exact Erdos58.mem_cycleLengths_intro (hw.map f.injective)
    (by rw [w.length_map f.toHom]; exact hlen)

theorem oddCycleLengths_subset (f : SimpleGraph.Copy H G) :
    H.oddCycleLengths ⊆ G.oddCycleLengths := by
  intro n hn
  obtain ⟨a, w, hw, hlen, hodd⟩ := Erdos58.mem_oddCycleLengths_elim hn
  exact Erdos58.mem_oddCycleLengths_intro
    (p := w.map f.toHom) (hw.map f.injective)
    (by rw [w.length_map f.toHom]; exact hlen) hodd

theorem oddCycleLengths_finite (f : SimpleGraph.Copy H G)
    (hG : G.oddCycleLengths.Finite) : H.oddCycleLengths.Finite :=
  hG.subset f.oddCycleLengths_subset

theorem oddCycleLengths_ncard_le (f : SimpleGraph.Copy H G)
    (hG : G.oddCycleLengths.Finite) :
    H.oddCycleLengths.ncard ≤ G.oddCycleLengths.ncard :=
  Set.ncard_le_ncard f.oddCycleLengths_subset hG

end SimpleGraph.Copy

namespace Erdos58

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

/-- The existing finite-target homomorphism compactness theorem specializes
directly to graph colorings, including zero colors and empty vertex types. -/
theorem colorable_of_finite_subgraphs {n : ℕ}
    (h : ∀ H : G.Subgraph, H.verts.Finite → H.coe.Colorable n) : G.Colorable n := by
  classical
  exact nonempty_hom_of_forall_finite_subgraph_hom (fun H hH => (h H hH).some)

theorem exists_finite_subgraph_not_colorable {n : ℕ}
    (hG : ¬ G.Colorable n) :
    ∃ H : G.Subgraph, H.verts.Finite ∧ ¬ H.coe.Colorable n := by
  by_contra! h
  exact hG (colorable_of_finite_subgraphs h)

/-- Erdős #58 restricted to finite vertex types. -/
public def FiniteStatement : Prop :=
  ∀ {W : Type u} [Finite W] (H : SimpleGraph W) (k : ℕ),
    H.oddCycleLengths.Finite → H.oddCycleLengths.ncard ≤ k →
      H.chromaticNumber ≤ ((2 * k + 2 : ℕ) : ℕ∞) ∧
      (H.chromaticNumber = ((2 * k + 2 : ℕ) : ℕ∞) ↔
        (completeGraph (Fin (2 * k + 2))).IsContained H)

/-- The exact unrestricted statement, with the upstream cycle definitions. -/
public def Statement : Prop :=
  ∀ {W : Type u} (H : SimpleGraph W) (k : ℕ),
    H.oddCycleLengths.Finite → H.oddCycleLengths.ncard ≤ k →
      H.chromaticNumber ≤ ((2 * k + 2 : ℕ) : ℕ∞) ∧
      (H.chromaticNumber = ((2 * k + 2 : ℕ) : ℕ∞) ↔
        (completeGraph (Fin (2 * k + 2))).IsContained H)

theorem statement_apply (h : Statement.{u}) {W : Type u}
    (H : SimpleGraph W) (k : ℕ)
    (hH : H.oddCycleLengths.Finite) (hk : H.oddCycleLengths.ncard ≤ k) :
    H.chromaticNumber ≤ ((2 * k + 2 : ℕ) : ℕ∞) ∧
      (H.chromaticNumber = ((2 * k + 2 : ℕ) : ℕ∞) ↔
        (completeGraph (Fin (2 * k + 2))).IsContained H) :=
  h H k hH hk

theorem statement_intro {f : ∀ {W : Type u} (H : SimpleGraph W) (k : ℕ),
    H.oddCycleLengths.Finite → H.oddCycleLengths.ncard ≤ k →
      H.chromaticNumber ≤ ((2 * k + 2 : ℕ) : ℕ∞) ∧
      (H.chromaticNumber = ((2 * k + 2 : ℕ) : ℕ∞) ↔
        (completeGraph (Fin (2 * k + 2))).IsContained H)} :
    Statement.{u} :=
  f

theorem finiteStatement_intro (f : ∀ {W : Type u} [Finite W] (H : SimpleGraph W) (k : ℕ),
    H.oddCycleLengths.Finite → H.oddCycleLengths.ncard ≤ k →
      H.chromaticNumber ≤ ((2 * k + 2 : ℕ) : ℕ∞) ∧
      (H.chromaticNumber = ((2 * k + 2 : ℕ) : ℕ∞) ↔
        (completeGraph (Fin (2 * k + 2))).IsContained H)) :
    FiniteStatement.{u} := f

/-- Only the finite upper bound is needed to lift the upper bound. -/
theorem chromatic_bound_of_finite
    (hfinite : ∀ {W : Type u} [Finite W] (H : SimpleGraph W) (k : ℕ),
      H.oddCycleLengths.Finite → H.oddCycleLengths.ncard ≤ k →
        H.chromaticNumber ≤ ((2 * k + 2 : ℕ) : ℕ∞))
    (G : SimpleGraph V) (k : ℕ) (hG : G.oddCycleLengths.Finite)
    (hk : G.oddCycleLengths.ncard ≤ k) :
    G.chromaticNumber ≤ ((2 * k + 2 : ℕ) : ℕ∞) := by
  apply chromaticNumber_le_iff_colorable.mpr
  apply colorable_of_finite_subgraphs
  intro H hH
  let := hH.fintype
  apply chromaticNumber_le_iff_colorable.mp
  exact hfinite H.coe k (H.coeCopy.oddCycleLengths_finite hG)
    ((H.coeCopy.oddCycleLengths_ncard_le hG).trans hk)

/-- A finite proof suffices for arbitrary graphs. Equality supplies a finite
obstruction to one fewer color, to which the finite equality theorem applies. -/
theorem statement_of_finite (hfinite : FiniteStatement.{u}) : Statement.{u} := by
  classical
  intro V G k hG hk
  have hbound : G.chromaticNumber ≤ ((2 * k + 2 : ℕ) : ℕ∞) :=
    chromatic_bound_of_finite (fun H k hH hcard => (hfinite H k hH hcard).1) G k hG hk
  refine ⟨hbound, ⟨?_, ?_⟩⟩
  · intro heq
    have hnot : ¬ G.Colorable (2 * k + 1) := by
      intro hc
      have hle := hc.chromaticNumber_le
      rw [heq] at hle
      norm_cast at hle
      omega
    obtain ⟨H, hH, hnotH⟩ := exists_finite_subgraph_not_colorable hnot
    let := hH.fintype
    obtain ⟨hboundH, heqH⟩ := hfinite H.coe k
      (H.coeCopy.oddCycleLengths_finite hG)
      ((H.coeCopy.oddCycleLengths_ncard_le hG).trans hk)
    have hchiH : H.coe.chromaticNumber = ((2 * k + 2 : ℕ) : ℕ∞) := by
      have hcolorH : H.coe.Colorable ((2 * k + 1) + 1) := by
        simpa only [Nat.add_assoc] using chromaticNumber_le_iff_colorable.mp hboundH
      simpa [Nat.cast_add, Nat.cast_mul, add_assoc, one_add_one_eq_two] using
        (chromaticNumber_eq_iff_colorable_not_colorable (G := H.coe)
          (n := 2 * k + 1)).mpr ⟨hcolorH, hnotH⟩
    exact (heqH.mp hchiH).trans H.coe_isContained
  · intro hclique
    apply le_antisymm hbound
    have hle := chromaticNumber_mono_of_hom hclique.some.toHom
    simpa only [completeGraph_eq_top, chromaticNumber_top, Fintype.card_fin] using hle

/-- The remaining mathematical obligation is exactly the finite graph case. -/
theorem statement_iff_finite : Statement.{u} ↔ FiniteStatement.{u} := by
  constructor
  · intro h V hV G k hG hk
    exact h G k hG hk
  · exact statement_of_finite

/-! ## Critical graphs

Finite vertex-critical induced cores for the equality direction of Erdős #58.
This module supplies minimality and the required lower bound on every degree.
It does not assert the remaining Gyárfás structural theorem.
-/

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

/-- Deleting any one vertex allows `n` colors, but the full graph does not. -/
structure VertexCritical (G : SimpleGraph V) (n : ℕ) : Prop where
  not_colorable : ¬ G.Colorable n
  deleted_colorable : ∀ v : V, (G.induce {w | w ≠ v}).Colorable n

/-- A coloring extends across a vertex with fewer neighbors than colors. -/
theorem colorable_of_deleted_vertex [Finite V] (v : V)
    (hdeleted : (G.induce {w | w ≠ v}).Colorable n)
    (hdegree : (G.neighborSet v).ncard < n) : G.Colorable n := by
  classical
  have hn : 0 < n := by omega
  obtain ⟨c⟩ := hdeleted
  let c' : V → Fin n := fun w =>
    if hw : w ≠ v then c ⟨w, hw⟩ else ⟨0, hn⟩
  have hcard : (c' '' G.neighborSet v).ncard < n :=
    (Set.ncard_image_le (s := G.neighborSet v) (f := c')).trans_lt hdegree
  have hex : ∃ a : Fin n, a ∉ c' '' G.neighborSet v := by
    by_contra! hall
    have heq : c' '' G.neighborSet v = Set.univ := Set.eq_univ_iff_forall.mpr hall
    rw [heq] at hcard
    simp only [Set.ncard_univ, Nat.card_fin] at hcard
    omega
  obtain ⟨a, ha⟩ := hex
  have havoid : ∀ w, G.Adj v w → c' w ≠ a := by
    intro w hvw heq
    exact ha ⟨w, hvw, heq⟩
  refine ⟨Coloring.mk (fun w => if w = v then a else c' w) ?_⟩
  intro x y hxy
  by_cases hx : x = v
  · subst x
    have hy : y ≠ v := hxy.ne.symm
    simpa only [ite_eq_left rfl, ite_eq_right hy, ite_true] using (havoid y hxy).symm
  · by_cases hy : y = v
    · subst y
      simpa only [ite_eq_right hx, ite_eq_left rfl, ite_true] using havoid x hxy.symm
    · simpa only [ite_eq_right hx, ite_eq_right hy, c', dite_eq_left hx, dite_eq_left hy] using
        c.valid (show (G.induce {w | w ≠ v}).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy)

theorem VertexCritical.neighbor_ncard_ge [Finite V] (h : VertexCritical G n) (v : V) :
    n ≤ (G.neighborSet v).ncard := by
  by_contra! hdegree
  exact h.not_colorable (colorable_of_deleted_vertex v (h.deleted_colorable v) hdegree)

/-- A finite noncolorable graph has an induced subgraph for which every proper
induced vertex subset is colorable. No chromatic or connectivity assumption is needed. -/
theorem exists_minimal_not_colorable_induce [Finite V] (hG : ¬ G.Colorable n) :
    ∃ s : Set V, ¬ (G.induce s).Colorable n ∧
      ∀ t : Set V, t ⊂ s → (G.induce t).Colorable n := by
  classical
  let family : Set (Set V) := {s | ¬ (G.induce s).Colorable n}
  have hfamily : family.Nonempty := by
    refine ⟨Set.univ, ?_⟩
    intro hc
    exact hG (hc.of_hom G.induceUnivIso.symm.toHom)
  obtain ⟨s, hs, hmin⟩ := Set.exists_min_image family Set.ncard (Set.toFinite family) hfamily
  refine ⟨s, hs, ?_⟩
  intro t hts
  by_contra hnot
  have hle := hmin t hnot
  have hlt := Set.ncard_lt_ncard hts (Set.toFinite s)
  omega

/-- A minimal induced vertex subset is vertex-critical in its own vertex type. -/
theorem exists_vertex_critical_induce [Finite V] (hG : ¬ G.Colorable n) :
    ∃ s : Set V, VertexCritical (G.induce s) n := by
  classical
  obtain ⟨s, hs, hminimal⟩ := exists_minimal_not_colorable_induce hG
  refine ⟨s, ⟨hs, ?_⟩⟩
  intro v
  have hproper : s \ {v.val} ⊂ s := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨Set.sdiff_subset, ?_⟩
    intro heq
    have hv : v.val ∈ s \ {v.val} := heq.symm ▸ v.property
    exact hv.2 (by simp)
  have hcolor := hminimal (s \ {v.val}) hproper
  let f : (G.induce s).induce {w | w ≠ v} →g G.induce (s \ {v.val}) := {
    toFun := fun w => ⟨w.val.val, w.val.property, by
      intro heq
      apply w.property
      apply Subtype.ext
      simpa only [Set.mem_singleton_iff] using heq⟩
    map_rel' := fun h => h }
  exact hcolor.of_hom f

/-- The finite critical core and minimum-degree input needed by the original
equality theorem, with `n = 2*k+1`. The remaining structural conclusion is separate. -/
theorem exists_induced_degree_core [Finite V] (hG : ¬ G.Colorable n) :
    ∃ s : Set V, VertexCritical (G.induce s) n ∧
      ∀ v : s, n ≤ ((G.induce s).neighborSet v).ncard := by
  obtain ⟨s, hs⟩ := exists_vertex_critical_induce hG
  exact ⟨s, hs, fun v => hs.neighbor_ncard_ge v⟩

/-- Every proper induced vertex subset of a vertex-critical graph is colorable. -/
theorem VertexCritical.colorable_induce_of_ne_univ (h : VertexCritical G n)
    (s : Set V) (hs : s ≠ Set.univ) : (G.induce s).Colorable n := by
  classical
  obtain ⟨v, hv⟩ := (Set.ne_univ_iff_exists_notMem s).mp hs
  have hsubset : s ⊆ {w | w ≠ v} := by
    intro w hw heq
    exact hv (heq ▸ hw)
  exact (h.deleted_colorable v).of_hom (G.induceHomOfLE hsubset).toHom

theorem VertexCritical.connected (h : VertexCritical G n) : G.Connected := by
  classical
  have : Nonempty V := by
    by_contra hnonempty
    have : IsEmpty V := not_nonempty_iff.mp hnonempty
    exact h.not_colorable (Colorable.of_isEmpty n)
  refine ⟨?_⟩
  by_contra hpre
  apply h.not_colorable
  apply colorable_iff_forall_connectedComponent.mpr
  intro c
  have hc : c.supp ≠ Set.univ := by
    intro heq
    apply hpre
    intro x y
    exact c.reachable_of_mem_supp (by rw [heq]; trivial) (by rw [heq]; trivial)
  exact h.colorable_induce_of_ne_univ c.supp hc

namespace CutColoring

variable (G : SimpleGraph V) (root : V)

abbrev Deleted := {w : V | w ≠ root}
abbrev deletedGraph : SimpleGraph (Deleted root) := G.induce {w | w ≠ root}

/-- One component after deletion, together with the deleted vertex. -/
def piece (c : (deletedGraph G root).ConnectedComponent) : Set V :=
  {w | w = root ∨ ∃ hw : w ≠ root, (deletedGraph G root).connectedComponentMk ⟨w, hw⟩ = c}

theorem piece_ne_univ (hpre : ¬ (deletedGraph G root).Preconnected)
    (c : (deletedGraph G root).ConnectedComponent) : piece G root c ≠ Set.univ := by
  intro heq
  apply hpre
  intro x y
  have hcomp (w : Deleted root) : (deletedGraph G root).connectedComponentMk w = c := by
    have hw : w.val ∈ piece G root c := by rw [heq]; trivial
    rcases hw with hw | ⟨hne, hc⟩
    · exact (w.property hw).elim
    · exact hc
  exact ConnectedComponent.eq.mp ((hcomp x).trans (hcomp y).symm)

/-- Normalize each piece coloring at the root and then glue it. -/
theorem colorable_of_pieces (hn : 0 < n)
    (hcolors : ∀ c : (deletedGraph G root).ConnectedComponent,
      (G.induce (piece G root c)).Colorable n) : G.Colorable n := by
  classical
  let zero : Fin n := ⟨0, hn⟩
  have hnormalized : ∀ c : (deletedGraph G root).ConnectedComponent,
      ∃ C : (G.induce (piece G root c)).Coloring (Fin n),
        C ⟨root, Or.inl rfl⟩ = zero := by
    intro c
    obtain ⟨C⟩ := hcolors c
    let p := Equiv.swap (C ⟨root, Or.inl rfl⟩) zero
    let C' : (G.induce (piece G root c)).Coloring (Fin n) :=
      Coloring.mk (fun w => p (C w)) (fun hxy heq => C.valid hxy (p.injective heq))
    refine ⟨C', ?_⟩
    exact Equiv.swap_apply_left _ _
  choose C hC using hnormalized
  let palette : (deletedGraph G root).ConnectedComponent → V → Fin n := fun c w =>
    if hw : w ∈ piece G root c then C c ⟨w, hw⟩ else zero
  have hpalette_root (c : (deletedGraph G root).ConnectedComponent) :
      palette c root = zero := by
    simpa only [palette, dite_eq_left (show root ∈ piece G root c from Or.inl rfl)] using hC c
  have hpalette_valid (c : (deletedGraph G root).ConnectedComponent) {x y : V}
      (hx : x ∈ piece G root c) (hy : y ∈ piece G root c) (hxy : G.Adj x y) :
      palette c x ≠ palette c y := by
    simpa only [palette, dite_eq_left hx, dite_eq_left hy] using
      (C c).valid (show (G.induce (piece G root c)).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy)
  let color : V → Fin n := fun w => if hw : w = root then zero else
    palette ((deletedGraph G root).connectedComponentMk ⟨w, hw⟩) w
  refine ⟨Coloring.mk color ?_⟩
  intro x y hxy
  by_cases hx : x = root
  · subst x
    have hy : y ≠ root := hxy.ne.symm
    let c := (deletedGraph G root).connectedComponentMk ⟨y, hy⟩
    have hne := hpalette_valid c (Or.inl rfl) (Or.inr ⟨hy, rfl⟩) hxy
    rw [hpalette_root c] at hne
    simpa only [color, dite_eq_left rfl, dite_eq_right hy, dite_true] using hne
  · by_cases hy : y = root
    · subst y
      let c := (deletedGraph G root).connectedComponentMk ⟨x, hx⟩
      have hne := hpalette_valid c (Or.inr ⟨hx, rfl⟩) (Or.inl rfl) hxy
      rw [hpalette_root c] at hne
      simpa only [color, dite_eq_left rfl, dite_eq_right hx, dite_true] using hne
    · have hcomp : (deletedGraph G root).connectedComponentMk ⟨x, hx⟩ =
          (deletedGraph G root).connectedComponentMk ⟨y, hy⟩ :=
        ConnectedComponent.connectedComponentMk_eq_of_adj
          (show (deletedGraph G root).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy)
      let c := (deletedGraph G root).connectedComponentMk ⟨y, hy⟩
      have hne := hpalette_valid c (Or.inr ⟨hx, hcomp⟩) (Or.inr ⟨hy, rfl⟩) hxy
      simpa only [color, dite_eq_right hx, dite_eq_right hy, c, hcomp] using hne

end CutColoring

theorem VertexCritical.deleted_preconnected (h : VertexCritical G n) (hn : 0 < n)
    (root : V) : (G.induce {w | w ≠ root}).Preconnected := by
  by_contra hpre
  apply h.not_colorable
  apply CutColoring.colorable_of_pieces G root hn
  intro c
  exact h.colorable_induce_of_ne_univ (CutColoring.piece G root c)
    (CutColoring.piece_ne_univ G root hpre c)

theorem VertexCritical.deleted_connected [Finite V] (h : VertexCritical G n) (hn : 0 < n)
    (root : V) : (G.induce {w | w ≠ root}).Connected := by
  have hdegree := h.neighbor_ncard_ge root
  have hpos : 0 < (G.neighborSet root).ncard := hn.trans_le hdegree
  obtain ⟨v, hv⟩ := (Set.ncard_pos (Set.toFinite (G.neighborSet root))).mp hpos
  have : Nonempty {w : V | w ≠ root} := ⟨⟨v, (show G.Adj root v from hv).ne.symm⟩⟩
  exact ⟨h.deleted_preconnected hn root⟩

/-- The critical core supplies the connectivity and degree hypotheses for
Gyárfás's structural theorem; the structural theorem itself is not assumed. -/
theorem exists_induced_connected_degree_core [Finite V] (hG : ¬ G.Colorable n)
    (hn : 0 < n) :
    ∃ s : Set V, VertexCritical (G.induce s) n ∧ (G.induce s).Connected ∧
      (∀ v : s, ((G.induce s).induce {w | w ≠ v}).Connected) ∧
      ∀ v : s, n ≤ ((G.induce s).neighborSet v).ncard := by
  obtain ⟨s, hs⟩ := exists_vertex_critical_induce hG
  exact ⟨s, hs, hs.connected, fun v => hs.deleted_connected hn v,
    fun v => hs.neighbor_ncard_ge v⟩

/-! ## Fan cycles

Actual fan cycles, indexed by positions on a simple graph path. Every
witness consists of the interval path and two edges from a vertex outside
the path; the resulting length is exact, and the vertices remain distinct.
-/

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {a b x : V}

/-- Delete the root and its two incident cycle edges, preserving the actual
path through every other cycle vertex. -/
def cycleWithoutRoot (c : G.Walk x x) (_hc : c.IsCycle) :
    G.Walk c.snd c.tail.penultimate := c.tail.dropLast

theorem cycleWithoutRoot_eq (c : G.Walk x x) (hc : c.IsCycle) :
    cycleWithoutRoot c hc = c.tail.dropLast := by
  simp [cycleWithoutRoot]

theorem cycleWithoutRoot_isPath (c : G.Walk x x) (hc : c.IsCycle) :
    (cycleWithoutRoot c hc).IsPath := hc.isPath_tail.dropLast

theorem cycleWithoutRoot_tail_notNil (c : G.Walk x x) (hc : c.IsCycle) :
    ¬c.tail.Nil := by
  rw [Walk.not_nil_iff_lt_length, Walk.length_tail]
  have := hc.three_le_length
  omega

theorem cycleWithoutRoot_root_notMem (c : G.Walk x x) (hc : c.IsCycle) :
    x ∉ (cycleWithoutRoot c hc).support := by
  have ht := cycleWithoutRoot_tail_notNil c hc
  have hNodup : ((cycleWithoutRoot c hc).support ++ [x]).Nodup := by
    rw [cycleWithoutRoot, Walk.support_dropLast_concat ht]
    exact hc.isPath_tail.support_nodup
  intro hx
  exact (List.nodup_append.mp hNodup).2.2 x hx x (by simp) rfl

theorem cycleWithoutRoot_length (c : G.Walk x x) (hc : c.IsCycle) :
    (cycleWithoutRoot c hc).length = c.length - 2 := by
  simp [cycleWithoutRoot, Walk.length_dropLast, Walk.length_tail, Nat.sub_sub]

theorem cycleWithoutRoot_first_edge (c : G.Walk x x) (hc : c.IsCycle) :
    G.Adj x c.snd := c.adj_snd hc.not_nil

theorem cycleWithoutRoot_last_edge (c : G.Walk x x) (hc : c.IsCycle) :
    G.Adj x c.tail.penultimate :=
  (c.tail.adj_penultimate (cycleWithoutRoot_tail_notNil c hc)).symm

theorem cycleWithoutRoot_mem_of_ne (c : G.Walk x x) (hc : c.IsCycle)
    {u : V} (hux : u ≠ x) (hu : u ∈ c.support) :
    u ∈ (cycleWithoutRoot c hc).support := by
  rw [← Walk.cons_support_tail hc.not_nil] at hu
  rcases List.mem_cons.mp hu with hEq | hu
  · exact (hux hEq).elim
  · rw [← Walk.support_dropLast_concat (cycleWithoutRoot_tail_notNil c hc)] at hu
    simpa [cycleWithoutRoot, hux] using hu

theorem cycleWithoutRoot_covers_neighbors (c : G.Walk x x) (hc : c.IsCycle)
    (hcover : ∀ u, G.Adj x u → u ∈ c.support) :
    ∀ u, G.Adj x u → u ∈ (cycleWithoutRoot c hc).support := by
  intro u hu
  exact cycleWithoutRoot_mem_of_ne c hc hu.ne.symm (hcover u hu)

/-- All path positions adjacent to an external vertex. -/
noncomputable def pathNeighborPositions (p : G.Walk a b) (x : V) : Finset ℕ := by
  classical
  exact (Finset.range (p.length + 1)).filter (fun i ↦ G.Adj x (p.getVert i))

@[simp] theorem mem_pathNeighborPositions (p : G.Walk a b) (x : V) (i : ℕ) :
    i ∈ pathNeighborPositions p x ↔ i ≤ p.length ∧ G.Adj x (p.getVert i) := by
  classical
  simp [pathNeighborPositions]

/-- Covering the entire neighborhood by a simple path preserves its exact
cardinality when vertices are replaced by their unique path positions. -/
theorem pathNeighborPositions_card (p : G.Walk a b) (hp : p.IsPath)
    (hcover : ∀ u, G.Adj x u → u ∈ p.support) :
    (pathNeighborPositions p x).card = (G.neighborSet x).ncard := by
  have hBij : Set.BijOn p.getVert (pathNeighborPositions p x : Set ℕ)
      (G.neighborSet x) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      exact (mem_pathNeighborPositions p x i).mp hi |>.2
    · intro i hi j hj hEq
      exact hp.getVert_injOn
        ((mem_pathNeighborPositions p x i).mp hi).1
        ((mem_pathNeighborPositions p x j).mp hj).1 hEq
    · intro u hu
      obtain ⟨i, hGet, hi⟩ := Walk.mem_support_iff_exists_getVert.mp (hcover u hu)
      refine ⟨i, (mem_pathNeighborPositions p x i).mpr ⟨hi, ?_⟩, hGet⟩
      simpa [hGet] using hu
  simpa using hBij.ncard_eq

/-- The interval from position i to position j, with the original endpoint
vertices rather than endpoints of an intermediate take/drop operation. -/
public def pathInterval (p : G.Walk a b) (i j : ℕ) (hij : i ≤ j) :
    G.Walk (p.getVert i) (p.getVert j) :=
  ((p.take j).drop i).copy
    (by simp [Walk.take_getVert, Nat.min_eq_right hij]) rfl

theorem pathInterval_isPath (p : G.Walk a b) (hp : p.IsPath)
    (i j : ℕ) (hij : i ≤ j) : (pathInterval p i j hij).IsPath := by
  exact (Walk.isPath_copy _ _ _).mpr ((hp.take j).drop i)

theorem pathInterval_length (p : G.Walk a b) (i j : ℕ) (hij : i ≤ j)
    (hj : j ≤ p.length) : (pathInterval p i j hij).length = j - i := by
  simp [pathInterval, Walk.drop_length, Walk.take_length, Nat.min_eq_left hj]

theorem pathInterval_support_subset (p : G.Walk a b) (i j : ℕ) (hij : i ≤ j) :
    (pathInterval p i j hij).support ⊆ p.support := by
  intro y hy
  simp only [pathInterval, Walk.support_copy, Walk.drop_support_eq_support_drop_min,
    Walk.support_take] at hy
  exact List.mem_of_mem_take (List.mem_of_mem_drop hy)

/-- Pointwise characterization of a copied path segment. -/
theorem pathInterval_getVert (p : G.Walk a b) (i j : ℕ) (hij : i ≤ j) (t : ℕ) :
    (i + t ≤ j) → (pathInterval p i j hij).getVert t = p.getVert (i + t) := by
  intro hijt
  simp [pathInterval, Walk.drop_getVert, Walk.take_getVert,
    Nat.min_eq_right hijt]

/-- A segment of an actual cycle is a simple path, including the degenerate
one-vertex segment used by external attachments. -/
theorem pathInterval_isPath_cycle (c : G.Walk x x) (hc : c.IsCycle)
    (i j : ℕ) (hij : i ≤ j) (hj : j < c.length) :
    (pathInterval c i j hij).IsPath := by
  exact (Walk.isPath_copy _ _ _).mpr ((hc.isPath_take hj).drop i)

/-- Two neighbors of an outside vertex, at distinct path positions,
give an actual simple cycle of length j-i+2. -/
theorem fan_cycle_witness (p : G.Walk a b) (hp : p.IsPath)
    (hx : x ∉ p.support) {i j : ℕ} (hij : i < j) (hj : j ≤ p.length)
    (hxi : G.Adj x (p.getVert i)) (hxj : G.Adj x (p.getVert j)) :
    ∃ q : G.Walk (p.getVert j) (p.getVert j),
      q.IsCycle ∧ q.length = j - i + 2 := by
  let r := pathInterval p i j hij.le
  have hr : r.IsPath := pathInterval_isPath p hp i j hij.le
  have hxr : x ∉ r.support := fun h ↦ hx (pathInterval_support_subset p i j hij.le h)
  have hPath : (Walk.cons hxi r).IsPath := hr.cons hxr
  have hrlen : r.length = j - i := pathInterval_length p i j hij.le hj
  refine ⟨Walk.cons hxj.symm (Walk.cons hxi r), ?_, ?_⟩
  · apply cycle_of_path_and_edge (Walk.cons hxi r) hPath hxj.symm
    simp only [Walk.length_cons]
    omega
  · simp only [Walk.length_cons, hrlen]

/-- Opposite-parity neighbor positions yield the corresponding original
odd simple-cycle length. -/
theorem fan_odd_cycle_length (p : G.Walk a b) (hp : p.IsPath)
    (hx : x ∉ p.support) {i j : ℕ} (hij : i < j) (hj : j ≤ p.length)
    (hxi : G.Adj x (p.getVert i)) (hxj : G.Adj x (p.getVert j))
    (hParity : i % 2 ≠ j % 2) : j - i + 2 ∈ G.oddCycleLengths := by
  obtain ⟨q, hq, hlen⟩ := fan_cycle_witness p hp hx hij hj hxi hxj
  exact mem_oddCycleLengths_intro hq hlen (by
    rw [Nat.odd_iff]
    have hi := Nat.mod_two_eq_zero_or_one i
    have hj := Nat.mod_two_eq_zero_or_one j
    omega)

/-! ## The main bound -/

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- The DFS counting argument gives the exact original chromatic bound once
normal depth data has been constructed. -/
theorem colorable_of_normalDepth [Finite V] (D : NormalDepth G) (k : ℕ)
    (hG : G.oddCycleLengths.Finite) (hk : G.oddCycleLengths.ncard ≤ k) :
    G.Colorable (2 * k + 2) := by
  apply colorable_of_earlier_same_parity_neighbors G D.depth k D.edge_ne
  intro v
  exact (earlier_parity_neighbors_bound D hG v).trans hk

/-- The original Erdős #58 chromatic bound for every finite graph. -/
theorem finite_chromatic_bound [Finite V] (k : ℕ)
    (hG : G.oddCycleLengths.Finite) (hk : G.oddCycleLengths.ncard ≤ k) :
    G.chromaticNumber ≤ ((2 * k + 2 : ℕ) : ℕ∞) := by
  obtain ⟨D⟩ := normalDepth_exists G
  exact (colorable_of_normalDepth G D k hG hk).chromaticNumber_le

/-- The original chromatic bound, with no finiteness assumption on vertices. -/
theorem erdos_58_bound (k : ℕ)
    (hG : G.oddCycleLengths.Finite) (hk : G.oddCycleLengths.ncard ≤ k) :
    G.chromaticNumber ≤ (2 * k + 2 : ℕ∞) := by
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
    chromatic_bound_of_finite
      (fun H k hH hcard => finite_chromatic_bound H k hH hcard) G k hG hk

/-- A complete graph copy attains the bound. The converse for positive k
is the remaining part of the full upstream theorem. -/
theorem erdos_58_clique_imp_equality (k : ℕ)
    (hG : G.oddCycleLengths.Finite) (hk : G.oddCycleLengths.ncard ≤ k)
    (hclique : (completeGraph (Fin (2 * k + 2))).IsContained G) :
    G.chromaticNumber = (2 * k + 2 : ℕ∞) := by
  apply le_antisymm (erdos_58_bound G k hG hk)
  have hle := chromaticNumber_mono_of_hom hclique.some.toHom
  simpa only [completeGraph_eq_top, chromaticNumber_top, Fintype.card_fin,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hle

end Erdos58

