module

public import CycleGenericHamiltonianV3
public import PathCliqueTwoLeavesRainbow
public import Batteries.Tactic.OpenPrivate
public import Mathlib.Tactic

@[expose] public section

/-!
original-color auxiliary with a SUPPLIED actual selected-core degree
bound and two actual selected spokes. The full S1-container deficit/window
caller and the universal original path upper bound are not supplied by this file.
-/

namespace ErdosProblems.PathDenseCoreTwoLeaves

open SimpleGraph
open ErdosProblems.PathUpperReduction
open ErdosProblems.AntiRamseyCycleGenericHamiltonian

open ErdosProblems.PathCliqueTwoLeaves

theorem degree_after_one_owner_deletion {n m : ℕ}
    (G : SimpleGraph (Fin n)) (core : Fin m → Fin n)
    (hcore : Function.Injective core) (old : Sym2 (Fin n)) (i : Fin m) :
    (G.comap core).degree i ≤ ((G.deleteEdges {old}).comap core).degree i + 1 := by
  classical
  let C := G.comap core
  let D := (G.deleteEdges {old}).comap core
  let X := C.neighborFinset i
  let Y := D.neighborFinset i
  have hYX : Y ⊆ X := by
    intro x hx
    apply (C.mem_neighborFinset i x).mpr
    have hadj := (D.mem_neighborFinset i x).mp hx
    change (G.deleteEdges {old}).Adj (core i) (core x) at hadj
    exact (SimpleGraph.deleteEdges_adj.mp hadj).1
  have hlost : (X \ Y).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have howner (z : Fin m) (hz : z ∈ X \ Y) : s(core i, core z) = old := by
      have hparts := Finset.mem_sdiff.mp hz
      have hadj : G.Adj (core i) (core z) :=
        (C.mem_neighborFinset i z).mp hparts.1
      by_contra hne
      apply hparts.2
      apply (D.mem_neighborFinset i z).mpr
      exact SimpleGraph.deleteEdges_adj.mpr ⟨hadj, by simpa using hne⟩
    apply hcore
    exact (Sym2.mkEmbedding (core i)).injective
      ((howner x hx).trans (howner y hy).symm)
  have hcard := Finset.card_sdiff_add_card_eq_card hYX
  change (X \ Y).card + Y.card = X.card at hcard
  change X.card ≤ Y.card + 1
  omega

theorem connected_of_distinct_degree_sum {m : ℕ} (hm : 1 ≤ m)
    (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (hpair : ∀ x y : Fin m, x ≠ y → m ≤ G.degree x + G.degree y) :
    G.Connected := by
  classical
  apply (SimpleGraph.connected_iff G).mpr
  refine ⟨?_, ⟨⟨0, by omega⟩⟩⟩
  intro x y
  by_cases hxy : x = y
  · subst y
    exact ⟨Walk.nil⟩
  by_cases hadj : G.Adj x y
  · exact hadj.reachable
  let S : Finset (Fin m) := Finset.univ.erase x
  have hxS : G.neighborFinset x ⊆ S := by
    intro z hz
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ z⟩
    intro heq
    subst z
    exact G.irrefl ((G.mem_neighborFinset x x).mp hz)
  have hyS : G.neighborFinset y ⊆ S := by
    intro z hz
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ z⟩
    intro heq
    subst z
    exact hadj ((G.mem_neighborFinset y x).mp hz).symm
  have hScard : S.card = m - 1 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_erase_of_mem (Finset.mem_univ x)
  have hsum := hpair x y hxy
  have hcards : S.card < (G.neighborFinset x).card + (G.neighborFinset y).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨z, hz⟩ := Finset.inter_nonempty_of_card_lt_card_add_card hxS hyS hcards
  have hxz := (G.mem_neighborFinset x z).mp (Finset.mem_inter.mp hz).1
  have hyz := (G.mem_neighborFinset y z).mp (Finset.mem_inter.mp hz).2
  exact hxz.reachable.trans hyz.symm.reachable

/-- A supplied dense ACTUAL selected core and two jointly distinct selected
spokes at its first hub give a rainbow path for the SAME original coloring.
The actual chord-color owner is arbitrary and is deleted before Hamiltonicity. -/
theorem rainbow_path_of_dense_representative_core_and_two_spokes {n q m : ℕ}
    (hm : 4 ≤ m) (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (core : Fin m → Fin n) (a b : Fin n)
    (hu : Function.Injective (Fin.cons a (Fin.cons b core)))
    (hdegree : ∀ i : Fin m, m + 2 ≤ 2 * ((selectedGraph χ r).comap core).degree i)
    (ha : (selectedGraph χ r).Adj a (core ⟨0, by omega⟩))
    (hb : (selectedGraph χ r).Adj b (core ⟨0, by omega⟩)) :
    ∃ f : (pathGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  classical
  let z : Fin m := ⟨0, by omega⟩
  have hz : z.val = 0 := rfl
  change (selectedGraph χ r).Adj a (core z) at ha
  change (selectedGraph χ r).Adj b (core z) at hb
  have haRange : a ∉ Set.range (Fin.cons b core) :=
    (Fin.cons_injective_iff.mp hu).1
  have htail : Function.Injective (Fin.cons b core) :=
    (Fin.cons_injective_iff.mp hu).2
  have hbRange : b ∉ Set.range core := (Fin.cons_injective_iff.mp htail).1
  have hcore : Function.Injective core := (Fin.cons_injective_iff.mp htail).2
  have hab : a ≠ b := by
    intro heq
    exact haRange ⟨0, by simpa using heq.symm⟩
  have hacore (i : Fin m) : a ≠ core i := by
    intro heq
    exact haRange ⟨i.succ, by simpa using heq.symm⟩
  have hbcore (i : Fin m) : b ≠ core i := by
    intro heq
    exact hbRange ⟨i, heq.symm⟩
  let e : HostEdge n :=
    ⟨s(a, b), (SimpleGraph.mem_edgeSet (⊤ : SimpleGraph (Fin n))).mpr
      ((SimpleGraph.top_adj _ _).mpr hab)⟩
  let old : Sym2 (Fin n) := (r.edge (χ e)).val
  let L := selectedGraph χ r
  let D := (L.deleteEdges {old}).comap core
  have hDpair : ∀ i j : Fin m, i ≠ j → m ≤ D.degree i + D.degree j := by
    intro i j _hij
    have hi := hdegree i
    have hj := hdegree j
    have hdi := degree_after_one_owner_deletion L core hcore old i
    have hdj := degree_after_one_owner_deletion L core hcore old j
    change m + 2 ≤ 2 * (L.comap core).degree i at hi
    change m + 2 ≤ 2 * (L.comap core).degree j at hj
    change (L.comap core).degree i ≤ D.degree i + 1 at hdi
    change (L.comap core).degree j ≤ D.degree j + 1 at hdj
    omega
  have hDconn : D.Connected := connected_of_distinct_degree_sum (by omega) D hDpair
  let oldNeighbors (i : Fin m) : Fintype (D.neighborSet i) := inferInstance
  let : DecidableRel D.Adj := fun i j => Classical.propDecidable (D.Adj i j)
  let (i : Fin m) : Fintype (D.neighborSet i) :=
    Subtype.fintype (Membership.mem (D.neighborSet i))
  have hDpairCanonical : ∀ i j : Fin m, i ≠ j → m ≤ D.degree i + D.degree j := by
    intro i j hij
    have hbound := hDpair i j hij
    have hnormal (x : Fin m) :
        @SimpleGraph.degree _ D x (oldNeighbors x) = D.degree x :=
      congrArg (fun f : Fintype (D.neighborSet x) => @SimpleGraph.degree _ D x f)
        (Subsingleton.elim _ _)
    change m ≤ @SimpleGraph.degree _ D i (oldNeighbors i) +
      @SimpleGraph.degree _ D j (oldNeighbors j) at hbound
    rw [hnormal i, hnormal j] at hbound
    exact hbound
  obtain ⟨u, c, hc⟩ := exists_hamiltonian_cycle_of_degree_sum D hDconn
    (by simpa only [Fintype.card_fin] using (show 3 ≤ m by omega))
    (by simpa only [Fintype.card_fin] using hDpairCanonical)
  let c' := c.rotate z (hc.mem_support z)
  have hc' : c'.IsHamiltonianCycle := hc.rotate (hc.mem_support z)
  let w := c'.tail.reverse
  have hw : w.IsPath := hc'.isHamiltonian_tail.isPath.reverse
  have hlength : w.length + 1 = m := by
    have htailLength := hc'.isHamiltonian_tail.length_eq
    rw [Fintype.card_fin] at htailLength
    simp only [w, Walk.length_reverse, htailLength]
    omega
  let order : Fin m → Fin m := fun i => w.getVert i.val
  have horder : Function.Injective order := by
    intro i j hij
    apply Fin.ext
    have hi : i.val ≤ w.length := by have := i.isLt; omega
    have hj : j.val ≤ w.length := by have := j.isLt; omega
    exact hw.getVert_injOn hi hj hij
  have hzero : order z = z := by
    change w.getVert 0 = z
    exact w.getVert_zero
  have horderSteps (i j : Fin m) (hij : (pathGraph m).Adj i j) :
      D.Adj (order i) (order j) := by
    rcases pathGraph_adj.mp hij with hij | hji
    · have hadj := w.adj_getVert_succ (i := i.val) (by have := j.isLt; omega)
      rw [hij] at hadj
      exact hadj
    · have hadj := w.adj_getVert_succ (i := j.val) (by have := i.isLt; omega)
      rw [hji] at hadj
      exact hadj.symm
  let r' := r.replace e
  let L' := selectedGraph χ r'
  have hle : L.deleteEdges {old} ≤ L' := by
    simpa [L, L', r', old] using delete_selectedEdge_le_replace χ r e
  have hretain {x y : Fin n} (hadj : L.Adj x y) (hne : old ≠ s(x, y)) :
      L'.Adj x y := by
    apply hle
    exact SimpleGraph.deleteEdges_adj.mpr ⟨hadj, by simpa using hne.symm⟩
  have hchord : L'.Adj a b := by
    simpa [L', r', e] using replacedEdge_mem χ r e
  let p : Fin m → Fin n := core ∘ order
  have hp : Function.Injective p := hcore.comp horder
  have hpz : p z = core z := by simp only [p, Function.comp_apply, hzero]
  have hsteps (i j : Fin m) (hij : (pathGraph m).Adj i j) :
      L'.Adj (p i) (p j) := hle (horderSteps i j hij)
  have haP (i : Fin m) : a ≠ p i := hacore (order i)
  have hbP (i : Fin m) : b ≠ p i := hbcore (order i)
  by_cases holdb : old = s(b, core z)
  · have holda : old ≠ s(a, core z) := by
      intro heq
      have hedge : s(b, core z) = s(a, core z) := holdb.symm.trans heq
      rcases Sym2.eq_iff.mp hedge with ⟨hba, _⟩ | ⟨_, hza⟩
      · exact hab hba.symm
      · exact hacore z hza.symm
    have hspoke : L'.Adj a (p z) := by
      rw [hpz]
      exact hretain ha holda
    let f : (pathGraph (m + 2)).Copy L' :=
      prefix_two_copy L' p b a
        (two_prefix_injective p hp b a hab.symm hbP haP)
        z hz hchord.symm hspoke hsteps
    refine ⟨(Copy.ofLE L' (⊤ : SimpleGraph (Fin n)) le_top).comp f, ?_⟩
    simpa [L', r'] using copy_in_selectedGraph_isRainbow χ (r.replace e) f
  · have hspoke : L'.Adj b (p z) := by
      rw [hpz]
      exact hretain hb holdb
    let f : (pathGraph (m + 2)).Copy L' :=
      prefix_two_copy L' p a b
        (two_prefix_injective p hp a b hab haP hbP)
        z hz hchord hspoke hsteps
    refine ⟨(Copy.ofLE L' (⊤ : SimpleGraph (Fin n)) le_top).comp f, ?_⟩
    simpa [L', r'] using copy_in_selectedGraph_isRainbow χ (r.replace e) f

end ErdosProblems.PathDenseCoreTwoLeaves
