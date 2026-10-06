module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

/-!
The graph and every deletion component are actual supplied objects; there is
no favorable rooted path, cycle, extremal family, or classification oracle.
-/

namespace ErdosProblems.PathUpperReduction.PathEightDeletedComponentThree1105

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Ambient image of an actual component of the actual vertex deletion. -/
def deletedComponentVertices (G : SimpleGraph V) (c : V)
    (D : (G.induce {v : V | v ≠ c}).ConnectedComponent) : Set V :=
  Subtype.val '' D.supp

omit [Fintype V] [DecidableEq V] in
theorem deletedComponentVertices_ne (G : SimpleGraph V) (c : V)
    (D : (G.induce {v : V | v ≠ c}).ConnectedComponent) {v : V}
    (hv : v ∈ deletedComponentVertices G c D) : v ≠ c := by
  rcases hv with ⟨u, _, rfl⟩
  exact u.property

omit [Fintype V] [DecidableEq V] in
theorem deletedComponentVertices_adj_closed (G : SimpleGraph V) (c : V)
    (D : (G.induce {v : V | v ≠ c}).ConnectedComponent) {u v : V}
    (hu : u ∈ deletedComponentVertices G c D) (huv : G.Adj u v)
    (hv : v ≠ c) : v ∈ deletedComponentVertices G c D := by
  rcases hu with ⟨u', hu', rfl⟩
  refine ⟨⟨v, hv⟩, ?_, rfl⟩
  exact D.mem_supp_of_adj_mem_supp hu' huv

omit [Fintype V] [DecidableEq V] in
theorem deletedComponentVertices_disjoint (G : SimpleGraph V) (c : V)
    (D E : (G.induce {v : V | v ≠ c}).ConnectedComponent) (hDE : D ≠ E) :
    Disjoint (deletedComponentVertices G c D) (deletedComponentVertices G c E) := by
  apply Set.disjoint_left.mpr
  intro v hvD hvE
  rcases hvD with ⟨d, hd, rfl⟩
  rcases hvE with ⟨e, he, hval⟩
  have hde : d = e := Subtype.ext hval.symm
  have hd' := (D.mem_supp_iff d).mp hd
  have he' := (E.mem_supp_iff e).mp he
  exact hDE (hd'.symm.trans (hde.symm ▸ he'))

omit [DecidableEq V] in
theorem exists_root_neighbor_in_deleted_component (G : SimpleGraph V) (c : V)
    (D : (G.induce {v : V | v ≠ c}).ConnectedComponent) (hconn : G.Connected) :
    ∃ a ∈ deletedComponentVertices G c D, G.Adj c a := by
  classical
  by_contra hnone
  push Not at hnone
  obtain ⟨d, hd⟩ := D.nonempty_supp
  have hstart : d.val ∈ deletedComponentVertices G c D := ⟨d, hd, rfl⟩
  have hclosed : ∀ {u v : V}, u ∈ deletedComponentVertices G c D →
      G.Adj u v → v ∈ deletedComponentVertices G c D := by
    intro u v hu huv
    have hv : v ≠ c := by
      intro heq
      exact hnone u hu (heq ▸ huv.symm)
    exact deletedComponentVertices_adj_closed G c D hu huv hv
  have hwalk : ∀ {u v : V}, (p : G.Walk u v) →
      u ∈ deletedComponentVertices G c D → v ∈ deletedComponentVertices G c D := by
    intro u v p
    induction p with
    | nil => exact id
    | @cons u w v huw p ih => exact fun hu => ih (hclosed hu huw)
  obtain ⟨p⟩ := hconn.preconnected d.val c
  exact deletedComponentVertices_ne G c D (hwalk p hstart) rfl

theorem exists_neighbor_outside_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v : V, 3 ≤ G.degree v) (v x y : V) :
    ∃ w, G.Adj v w ∧ w ≠ x ∧ w ≠ y := by
  classical
  have hnot : ¬ G.neighborFinset v ⊆ ({x, y} : Finset V) := by
    intro hsub
    have hcard := Finset.card_le_card hsub
    have htwo : ({x, y} : Finset V).card ≤ 2 := Finset.card_le_two
    have hthree := hmin v
    change 3 ≤ (G.neighborFinset v).card at hthree
    omega
  obtain ⟨w, hw, hout⟩ := Finset.not_subset.mp hnot
  refine ⟨w, (G.mem_neighborFinset v w).mp hw, ?_, ?_⟩ <;>
    intro heq <;> subst w <;> simp at hout

theorem exists_rooted_four_in_deleted_component (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : V)
    (D : (G.induce {v : V | v ≠ c}).ConnectedComponent)
    (hconn : G.Connected) (hmin : ∀ v : V, 3 ≤ G.degree v) :
    ∃ a b d : V, a ∈ deletedComponentVertices G c D ∧
      b ∈ deletedComponentVertices G c D ∧ d ∈ deletedComponentVertices G c D ∧
      [c, a, b, d].Nodup ∧ G.Adj c a ∧ G.Adj a b ∧ G.Adj b d := by
  classical
  obtain ⟨a, ha, hca⟩ := exists_root_neighbor_in_deleted_component G c D hconn
  obtain ⟨b, hab, hbc, hba⟩ := exists_neighbor_outside_pair G hmin a c a
  have hb := deletedComponentVertices_adj_closed G c D ha hab hbc
  obtain ⟨d, hbd, hdc, hda⟩ := exists_neighbor_outside_pair G hmin b c a
  have hd := deletedComponentVertices_adj_closed G c D hb hbd hdc
  have hac := deletedComponentVertices_ne G c D ha
  have hdb : d ≠ b := hbd.ne.symm
  refine ⟨a, b, d, ha, hb, hd, ?_, hca, hab, hbd⟩
  simp only [List.nodup_cons, List.nodup_nil, List.mem_cons, List.not_mem_nil,
    not_or, and_true]
  grind

/-- Literal joined rooted P5 and P4 contradict P8-freeness on the SAME graph. -/
theorem no_rooted_five_in_deleted_component (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : V)
    (D E : (G.induce {v : V | v ≠ c}).ConnectedComponent)
    (hconn : G.Connected) (hmin : ∀ v : V, 3 ≤ G.degree v)
    (hfree : (pathGraph 8).Free G) (hDE : D ≠ E)
    (a b d w : V)
    (ha : a ∈ deletedComponentVertices G c D)
    (hb : b ∈ deletedComponentVertices G c D)
    (hd : d ∈ deletedComponentVertices G c D)
    (hw : w ∈ deletedComponentVertices G c D)
    (hnodup : [c, a, b, d, w].Nodup)
    (hca : G.Adj c a) (hab : G.Adj a b) (hbd : G.Adj b d)
    (hdw : G.Adj d w) : False := by
  classical
  obtain ⟨p, q, s, hp, hq, hs, hE, hcp, hpq, hqs⟩ :=
    exists_rooted_four_in_deleted_component G c E hconn hmin
  have hdis := Set.disjoint_left.mp (deletedComponentVertices_disjoint G c D E hDE)
  have hcross : ∀ x ∈ ({a, b, d, w} : Finset V),
      ∀ y ∈ ({p, q, s} : Finset V), x ≠ y := by
    intro x hx y hy hxy
    have hxD : x ∈ deletedComponentVertices G c D := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have hyE : y ∈ deletedComponentVertices G c E := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl <;> assumption
    exact hdis hxD (hxy.symm ▸ hyE)
  let joined : G.Walk w s :=
    Walk.cons hdw.symm (Walk.cons hbd.symm (Walk.cons hab.symm
      (Walk.cons hca.symm (Walk.cons hcp (Walk.cons hpq (Walk.cons hqs Walk.nil))))))
  have hpath : joined.IsPath := by
    apply Walk.IsPath.mk'
    change [w, d, b, a, c, p, q, s].Nodup
    simp only [List.nodup_cons, List.nodup_nil, List.mem_cons, List.not_mem_nil,
      not_or, and_true] at hnodup hE ⊢
    have hap := hcross a (by simp) p (by simp)
    have haq := hcross a (by simp) q (by simp)
    have has := hcross a (by simp) s (by simp)
    have hbp := hcross b (by simp) p (by simp)
    have hbq := hcross b (by simp) q (by simp)
    have hbs := hcross b (by simp) s (by simp)
    have hdp := hcross d (by simp) p (by simp)
    have hdq := hcross d (by simp) q (by simp)
    have hds := hcross d (by simp) s (by simp)
    have hwp := hcross w (by simp) p (by simp)
    have hwq := hcross w (by simp) q (by simp)
    have hws := hcross w (by simp) s (by simp)
    grind
  apply hfree
  exact ⟨by simpa only [joined, Walk.length_cons, Walk.length_nil] using hpath.pathGraphCopy⟩

/-- Every actual deletion component is a triangle when a second component exists.
The conclusion counts the explicit deleted-support carrier, without a carrier
identification or a supplied favorable rooted path. -/
theorem deleted_component_card_eq_three_of_distinct_component
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hmin : ∀ v : V, 3 ≤ G.degree v) (hfree : (pathGraph 8).Free G)
    (c : V) (D E : (G.induce {v : V | v ≠ c}).ConnectedComponent)
    (hDE : D ≠ E) :
    Nat.card {v : {x : V // x ≠ c} // v ∈ D.supp} = 3 := by
  classical
  obtain ⟨a, b, d, ha, hb, hd, hfour, hca, hab, hbd⟩ :=
    exists_rooted_four_in_deleted_component G c D hconn hmin
  have hac := deletedComponentVertices_ne G c D ha
  have hbc := deletedComponentVertices_ne G c D hb
  have hdc := deletedComponentVertices_ne G c D hd
  have habne : a ≠ b := hab.ne
  have hadne : a ≠ d := by
    have hh := hfour
    simp only [List.nodup_cons, List.nodup_nil, List.mem_cons, List.not_mem_nil,
      not_or, and_true] at hh
    grind
  have hbdne : b ≠ d := hbd.ne
  have hterminal : ∀ w : V, G.Adj d w → w = c ∨ w = a ∨ w = b := by
    intro w hdw
    by_contra hout
    have hwc : w ≠ c := by grind
    have hwa : w ≠ a := by grind
    have hwb : w ≠ b := by grind
    have hwd : w ≠ d := hdw.ne.symm
    have hw := deletedComponentVertices_adj_closed G c D hd hdw hwc
    have hfive : [c, a, b, d, w].Nodup := by
      have hh := hfour
      simp only [List.nodup_cons, List.nodup_nil, List.mem_cons, List.not_mem_nil,
        not_or, and_true] at hh ⊢
      grind
    exact no_rooted_five_in_deleted_component G c D E hconn hmin hfree hDE
      a b d w ha hb hd hw hfive hca hab hbd hdw
  have hNsub : G.neighborFinset d ⊆ ({c, a, b} : Finset V) := by
    intro w hw
    have hcases := hterminal w ((G.mem_neighborFinset d w).mp hw)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hcases
  have hNcard : ({c, a, b} : Finset V).card ≤ (G.neighborFinset d).card := by
    have hsmall : ({c, a, b} : Finset V).card ≤ 3 := Finset.card_le_three
    exact hsmall.trans (hmin d)
  have hNeq := Finset.eq_of_subset_of_card_le hNsub hNcard
  have hdcAdj : G.Adj d c := (G.mem_neighborFinset d c).mp (by rw [hNeq]; simp)
  have hdaAdj : G.Adj d a := (G.mem_neighborFinset d a).mp (by rw [hNeq]; simp)
  let T : Set V := {a, b, d}
  have hTsub : T ⊆ deletedComponentVertices G c D := by
    intro u hu
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl <;> assumption
  have hclosedT : ∀ {u v : V}, u ∈ T →
      v ∈ deletedComponentVertices G c D → G.Adj u v → v ∈ T := by
    intro u v hu hv huv
    by_contra hvout
    have hvc := deletedComponentVertices_ne G c D hv
    have hvne : v ≠ a ∧ v ≠ b ∧ v ≠ d := by simpa [T] using hvout
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with hua | hub | hud
    · subst u
      have hfive : [c, d, b, a, v].Nodup := by
        simp only [List.nodup_cons, List.nodup_nil, List.mem_cons, List.not_mem_nil,
          not_or, and_true]
        grind
      exact no_rooted_five_in_deleted_component G c D E hconn hmin hfree hDE
        d b a v hd hb ha hv hfive hdcAdj.symm hbd.symm hab.symm huv
    · subst u
      have hfive : [c, a, d, b, v].Nodup := by
        simp only [List.nodup_cons, List.nodup_nil, List.mem_cons, List.not_mem_nil,
          not_or, and_true]
        grind
      exact no_rooted_five_in_deleted_component G c D E hconn hmin hfree hDE
        a d b v ha hd hb hv hfive hca hdaAdj.symm hbd.symm huv
    · subst u
      have hfive : [c, a, b, d, v].Nodup := by
        simp only [List.nodup_cons, List.nodup_nil, List.mem_cons, List.not_mem_nil,
          not_or, and_true]
        grind
      exact no_rooted_five_in_deleted_component G c D E hconn hmin hfree hDE
        a b d v ha hb hd hv hfive hca hab hbd huv
  have hwalkT : ∀ {u v : {x : V // x ≠ c}},
      (p : (G.induce {x : V | x ≠ c}).Walk u v) → u.val ∈ T → v.val ∈ T := by
    intro u v p
    induction p with
    | nil => exact id
    | @cons u w v huw p ih =>
      intro hu
      have hwD := deletedComponentVertices_adj_closed G c D (hTsub hu) huw w.property
      exact ih (hclosedT hu hwD huw)
  have hS : deletedComponentVertices G c D = T := by
    apply Set.Subset.antisymm
    · intro v hv
      rcases ha with ⟨a', ha', haval⟩
      rcases hv with ⟨v', hv', hvval⟩
      obtain ⟨p⟩ := D.reachable_of_mem_supp ha' hv'
      have haT : a'.val ∈ T := by rw [haval]; simp [T]
      have hvT := hwalkT p haT
      simpa only [hvval] using hvT
    · exact hTsub
  let project : {v : {x : V // x ≠ c} // v ∈ D.supp} →
      deletedComponentVertices G c D :=
    fun v => ⟨v.val.val, ⟨v.val, v.property, rfl⟩⟩
  have hproject : Function.Bijective project := by
    constructor
    · intro u v huv
      apply Subtype.ext
      apply Subtype.ext
      have hval := congrArg (fun z : deletedComponentVertices G c D => z.val) huv
      change u.val.val = v.val.val at hval
      exact hval
    · intro v
      rcases v.property with ⟨u, hu, huv⟩
      refine ⟨⟨u, hu⟩, ?_⟩
      apply Subtype.ext
      exact huv
  have hcardS : Nat.card (deletedComponentVertices G c D) = 3 := by
    rw [Nat.card_eq_card_toFinset]
    have hfin : (deletedComponentVertices G c D).toFinset = ({a, b, d} : Finset V) := by
      ext v
      simp [hS, T]
    rw [hfin]
    simp [habne, hadne, hbdne]
  exact (Nat.card_congr (Equiv.ofBijective project hproject)).trans hcardS

end ErdosProblems.PathUpperReduction.PathEightDeletedComponentThree1105
