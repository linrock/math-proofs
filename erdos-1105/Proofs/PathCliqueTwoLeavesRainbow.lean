module

public import PathUpperRainbowBridge
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Logic.Equiv.Basic

@[expose] public section

/-!
an actual selected clique of order m≥5 with two additional
distinct vertices having selected spokes to its first vertex forces a rainbow
(m+2)-vertex path for the SAME original coloring. Additional edges are allowed. The actual leaf-chord color owner is avoided by a literal hub-fixing swap,
not by a favorable-owner hypothesis or a supplied rainbow/core-path premise.
-/

namespace ErdosProblems.PathCliqueTwoLeaves

open SimpleGraph
open ErdosProblems.PathUpperReduction

/-- Move the larger endpoint of a natural-order edge to a far nonzero vertex.
The swap fixes every vertex at position zero and destroys that adjacency. -/
theorem swap_breaks_ordered_edge {m : ℕ} (hm : 5 ≤ m)
    (a b : Fin m) (hab : a.val + 1 = b.val) :
    ∃ π : Equiv.Perm (Fin m),
      (∀ z : Fin m, z.val = 0 → π z = z) ∧
      (∀ i : Fin m, π (π i) = i) ∧
      ¬ (pathGraph m).Adj (π a) (π b) := by
  let c : Fin m :=
    ⟨if a.val = 0 then 3 else if a.val ≤ 2 then 4 else 1,
      by split_ifs <;> omega⟩
  have hc0 : c.val ≠ 0 := by
    change (if a.val = 0 then 3 else if a.val ≤ 2 then 4 else 1) ≠ (0 : ℕ)
    split_ifs <;> decide
  have habne : a ≠ b := by
    intro heq
    have hv := congrArg Fin.val heq
    omega
  have hac : a ≠ c := by
    intro heq
    have hv := congrArg Fin.val heq
    dsimp [c] at hv
    split_ifs at hv <;> omega
  let π : Equiv.Perm (Fin m) := Equiv.swap b c
  refine ⟨π, ?_, ?_, ?_⟩
  · intro z hz
    apply Equiv.swap_apply_of_ne_of_ne
    · intro heq
      have hv := congrArg Fin.val heq
      omega
    · intro heq
      have hv := congrArg Fin.val heq
      exact hc0 (hv.symm.trans hz)
  · intro i
    exact Equiv.swap_apply_self b c i
  · change ¬ (pathGraph m).Adj (Equiv.swap b c a) (Equiv.swap b c b)
    rw [Equiv.swap_apply_of_ne_of_ne habne hac, Equiv.swap_apply_left,
      pathGraph_adj]
    dsimp [c]
    split_ifs <;> omega

theorem avoid_ordered_owner {V : Type*} {m : ℕ}
    (hm : 5 ≤ m) (core : Fin m → V) (hcore : Function.Injective core)
    (z : Fin m) (hz : z.val = 0) (old : Sym2 V)
    (a b : Fin m) (hab : a.val + 1 = b.val)
    (howner : old = s(core a, core b)) :
    ∃ π : Equiv.Perm (Fin m), π z = z ∧
      ∀ i j : Fin m, (pathGraph m).Adj i j →
        old ≠ s(core (π i), core (π j)) := by
  obtain ⟨π, hzero, hinv, hnon⟩ := swap_breaks_ordered_edge hm a b hab
  refine ⟨π, hzero z hz, ?_⟩
  intro i j hij heq
  have hpairs : s(π i, π j) = s(a, b) := by
    apply Sym2.map.injective hcore
    simpa only [Sym2.map_mk] using heq.symm.trans howner
  rcases Sym2.eq_iff.mp hpairs with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · have hi' : i = π a := by
      simpa only [hinv] using congrArg π hi
    have hj' : j = π b := by
      simpa only [hinv] using congrArg π hj
    exact hnon (by simpa only [hi', hj'] using hij)
  · have hi' : i = π b := by
      simpa only [hinv] using congrArg π hi
    have hj' : j = π a := by
      simpa only [hinv] using congrArg π hj
    exact hnon (by simpa only [hi', hj'] using hij.symm)

/-- The actual owner is arbitrary. If absent from the natural core path,
use that path; otherwise the explicit far-vertex swap avoids it. -/
theorem core_order_avoids_one {V : Type*} {m : ℕ}
    (hm : 5 ≤ m) (core : Fin m → V) (hcore : Function.Injective core)
    (z : Fin m) (hz : z.val = 0) (old : Sym2 V) :
    ∃ π : Equiv.Perm (Fin m), π z = z ∧
      ∀ i j : Fin m, (pathGraph m).Adj i j →
        old ≠ s(core (π i), core (π j)) := by
  classical
  by_cases hex : ∃ a b : Fin m,
      (pathGraph m).Adj a b ∧ old = s(core a, core b)
  · obtain ⟨a, b, hab, howner⟩ := hex
    rcases pathGraph_adj.mp hab with hab | hba
    · exact avoid_ordered_owner hm core hcore z hz old a b hab howner
    · apply avoid_ordered_owner hm core hcore z hz old b a hba
      exact howner.trans Sym2.eq_swap
  · refine ⟨Equiv.refl _, rfl, ?_⟩
    intro i j hij heq
    exact hex ⟨i, j, hij, heq⟩

theorem two_prefix_injective {V : Type*} {m : ℕ}
    (p : Fin m → V) (hp : Function.Injective p) (c d : V)
    (hcd : c ≠ d) (hc : ∀ i, c ≠ p i) (hd : ∀ i, d ≠ p i) :
    Function.Injective (Fin.cons c (Fin.cons d p)) := by
  apply Fin.cons_injective_of_injective
  · rintro ⟨i, hi⟩
    cases i using Fin.cases with
    | zero => exact hcd (by simpa using hi.symm)
    | succ i => exact hc i (by simpa using hi.symm)
  · apply Fin.cons_injective_of_injective
    · rintro ⟨i, hi⟩
      exact hd i hi.symm
    · exact hp

/-- The literal Copy adapter uses actual pathGraph adjacency and two cons
steps. Its adjacency premises are derived inside the coloring caller. -/
def prefix_two_copy {V : Type*} {m : ℕ}
    (G : SimpleGraph V) (p : Fin m → V) (c d : V)
    (hw : Function.Injective (Fin.cons c (Fin.cons d p)))
    (z : Fin m) (hz : z.val = 0)
    (hcd : G.Adj c d) (hdz : G.Adj d (p z))
    (hsteps : ∀ i j : Fin m, (pathGraph m).Adj i j → G.Adj (p i) (p j)) :
    (pathGraph (m + 2)).Copy G := by
  let w : Fin (m + 2) → V := Fin.cons c (Fin.cons d p)
  have hnext (i j : Fin (m + 2)) (hij : i.val + 1 = j.val) :
      G.Adj (w i) (w j) := by
    cases i using Fin.cases with
    | zero =>
      have hj : j = (0 : Fin (m + 1)).succ := by
        apply Fin.ext
        simpa using hij.symm
      rw [hj]
      simpa [w] using hcd
    | succ i =>
      cases i using Fin.cases with
      | zero =>
        have hj : j = z.succ.succ := by
          apply Fin.ext
          simp only [Fin.val_succ, Fin.val_zero] at hij ⊢
          omega
        rw [hj]
        simpa [w] using hdz
      | succ i =>
        have hjbound := j.isLt
        let j' : Fin m := ⟨j.val - 2, by
          simp only [Fin.val_succ] at hij
          omega⟩
        have hj : j = j'.succ.succ := by
          apply Fin.ext
          simp only [Fin.val_succ]
          dsimp [j']
          simp only [Fin.val_succ] at hij
          omega
        have hbase : (pathGraph m).Adj i j' := by
          apply pathGraph_adj.mpr
          left
          dsimp [j']
          simp only [Fin.val_succ] at hij
          omega
        rw [hj]
        simpa [w] using hsteps i j' hbase
  let φ : (pathGraph (m + 2)) →g G :=
    ⟨w, by
      intro i j hij
      rcases pathGraph_adj.mp hij with hij | hji
      · exact hnext i j hij
      · exact (hnext j i hji).symm⟩
  exact ⟨φ, hw⟩

/-- A selected clique of order m≥5 and two distinct extra vertices with
selected spokes to the same core hub force an original rainbow P_(m+2).
No owner, rainbow path, inducedness or full-graph S1 premise is supplied. -/
theorem rainbow_path_of_representative_clique_and_two_leaves {n q m : ℕ}
    (hm : 5 ≤ m) (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (core : Fin m → Fin n) (a b : Fin n)
    (hu : Function.Injective (Fin.cons a (Fin.cons b core)))
    (hK : ∀ i j : Fin m, i ≠ j →
      (selectedGraph χ r).Adj (core i) (core j))
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
    apply haRange
    exact ⟨0, by simpa using heq.symm⟩
  have hacore (i : Fin m) : a ≠ core i := by
    intro heq
    apply haRange
    exact ⟨i.succ, by simpa using heq.symm⟩
  have hbcore (i : Fin m) : b ≠ core i := by
    intro heq
    exact hbRange ⟨i, heq.symm⟩
  let e : HostEdge n :=
    ⟨s(a, b), (SimpleGraph.mem_edgeSet (⊤ : SimpleGraph (Fin n))).mpr
      ((top_adj _ _).mpr hab)⟩
  let old : Sym2 (Fin n) := (r.edge (χ e)).val
  let r' : RepresentativeChoice χ := r.replace e
  let L : SimpleGraph (Fin n) := selectedGraph χ r
  let L' : SimpleGraph (Fin n) := selectedGraph χ r'
  have hle : L.deleteEdges {old} ≤ L' := by
    simpa [L, L', r', old] using delete_selectedEdge_le_replace χ r e
  have hretain {x y : Fin n} (hadj : L.Adj x y) (hne : old ≠ s(x, y)) :
      L'.Adj x y := by
    have he : s(x, y) ∈ L.edgeSet := hadj
    have hed : s(x, y) ∈ (L.deleteEdges {old}).edgeSet := by
      rw [SimpleGraph.edgeSet_deleteEdges]
      exact ⟨he, by simpa using hne.symm⟩
    exact SimpleGraph.edgeSet_mono hle hed
  have hchord : L'.Adj a b := by
    have he := replacedEdge_mem χ r e
    simpa [L', r', e] using he
  obtain ⟨π, hfix, havoid⟩ := core_order_avoids_one hm core hcore z hz old
  let p : Fin m → Fin n := core ∘ π
  have hp : Function.Injective p := hcore.comp π.injective
  have hpz : p z = core z := by simp only [p, Function.comp_apply, hfix]
  have hsteps (i j : Fin m) (hij : (pathGraph m).Adj i j) :
      L'.Adj (p i) (p j) := by
    have hne : i ≠ j := hij.ne
    exact hretain (hK (π i) (π j) (π.injective.ne hne)) (havoid i j hij)
  have haP (i : Fin m) : a ≠ p i := hacore (π i)
  have hbP (i : Fin m) : b ≠ p i := hbcore (π i)
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

end ErdosProblems.PathCliqueTwoLeaves
