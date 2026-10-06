module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Data.Fintype.Card
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Nodup
public import Mathlib.Tactic

@[expose] public section

/-!
This Mathlib-only Lean4.35.0-rc2 adapter retains
two prescribed distinct outside contacts. Unlike its existential-contact API, the statement exposes the fixed first and
last attachment edges and derives length>=3 from distinct actual contacts. No clique, finiteness, saturation, favorable path or rainbow premise is used.
-/

namespace ErdosProblems.PathUpperReduction.FixedContactEar1105
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {S : Set V}

/-- Two fixed distinct contacts in one actual outside component give a simple
ear with all internal vertices outside S and at least three actual edges. -/
theorem exists_fixed_contact_ear
    (C : (G.induce Sᶜ).ConnectedComponent)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y)
    (v w : ↥(Sᶜ)) (hvC : v ∈ C.supp) (hwC : w ∈ C.supp)
    (hvw : v ≠ w) (hxv : G.Adj x v.val) (hwy : G.Adj w.val y) :
    ∃ q : G.Walk x y, q.IsPath ∧ 3 ≤ q.length ∧
      (∀ z, z ∈ q.support → z ≠ x → z ≠ y →
        z ∈ (Subtype.val : ↥(Sᶜ) → V) '' C.supp) ∧
      (∀ z, z ∈ q.support → z ≠ x → z ≠ y → z ∉ S) ∧
      (∀ z, z ∈ q.support → z ∈ S → z = x ∨ z = y) ∧
      ∃ middle : G.Walk v.val w.val, middle.IsPath ∧
        (∀ z, z ∈ middle.support →
          z ∈ (Subtype.val : ↥(Sᶜ) → V) '' C.supp) ∧
        q = (Walk.cons hxv middle).concat hwy ∧
        (∀ z, z ∈ q.support ↔ z = x ∨ z = y ∨ z ∈ middle.support) := by
  classical
  obtain ⟨inside, hinside⟩ :=
    C.connected_toSimpleGraph.exists_isPath ⟨v, hvC⟩ ⟨w, hwC⟩
  let middle : G.Walk v.val w.val :=
    (inside.map C.toSimpleGraph_hom).map (Embedding.induce Sᶜ).toHom
  have hmiddle : middle.IsPath :=
    Walk.IsPath.map (f := (Embedding.induce Sᶜ).toHom) Subtype.val_injective
      (Walk.IsPath.map (f := C.toSimpleGraph_hom) Subtype.val_injective hinside)
  have hcomponent : ∀ z, z ∈ middle.support →
      z ∈ (Subtype.val : ↥(Sᶜ) → V) '' C.supp := by
    intro z hz
    change z ∈ ((inside.map C.toSimpleGraph_hom).map
      (Embedding.induce Sᶜ).toHom).support at hz
    rw [Walk.support_map, Walk.support_map] at hz
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hu
    exact ⟨t.val, t.property, rfl⟩
  have havoids : ∀ z, z ∈ middle.support → z ∉ S := by
    intro z hz
    obtain ⟨u, _, rfl⟩ := hcomponent z hz
    exact u.property
  have hxnot : x ∉ middle.support := fun hz => havoids x hz hx
  let left : G.Walk x w.val := Walk.cons hxv middle
  have hleft : left.IsPath := hmiddle.cons hxnot
  have hynot : y ∉ left.support := by
    intro hz
    have hcases : y = x ∨ y ∈ middle.support := by
      simpa only [left, Walk.support_cons, List.mem_cons] using hz
    rcases hcases with h | h
    · exact hxy h.symm
    · exact havoids y h hy
  let q : G.Walk x y := left.concat hwy
  have hq : q.IsPath := hleft.concat hynot hwy
  have hpositive : 0 < middle.length := Nat.pos_of_ne_zero (by
    intro hzero
    exact hvw (Subtype.ext (Walk.eq_of_length_eq_zero hzero)))
  have hsupport : ∀ z, z ∈ q.support ↔
      z = x ∨ z = y ∨ z ∈ middle.support := by
    intro z
    simp only [q, left, Walk.support_concat, Walk.support_cons,
      List.mem_append, List.mem_cons]
    aesop
  have hcomponentInternal : ∀ z, z ∈ q.support → z ≠ x → z ≠ y →
      z ∈ (Subtype.val : ↥(Sᶜ) → V) '' C.supp := by
    intro z hz hzx hzy
    rcases (hsupport z).mp hz with h | h | h
    · exact (hzx h).elim
    · exact (hzy h).elim
    · exact hcomponent z h
  refine ⟨q, hq, ?_, hcomponentInternal, ?_, ?_, middle, hmiddle,
    hcomponent, ?_, hsupport⟩
  · simp only [q, left, Walk.length_concat, Walk.length_cons]
    omega
  · intro z hz hzx hzy
    obtain ⟨u, _, rfl⟩ := hcomponentInternal z hz hzx hzy
    exact u.property
  · intro z hz hzS
    rcases (hsupport z).mp hz with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (havoids z h hzS).elim
  · rfl

end ErdosProblems.PathUpperReduction.FixedContactEar1105
/-!
Generic prescribed-endpoint
path on the SAME actual clique. The order is constructed internally from
the actual finset with its endpoints erased; no supplied path/order oracle.
-/

namespace ErdosProblems.PathUpperReduction.CliqueSpanningPath1105

open SimpleGraph

theorem exists_clique_spanning_path {V : Type*} (G : SimpleGraph V)
    (S : Finset V) (hclique : G.IsClique (S : Set V))
    {a b : V} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    ∃ P : G.Walk a b, P.IsPath ∧ P.length = S.card - 1 ∧
      (∀ z, z ∈ P.support ↔ z ∈ S) := by
  classical
  let T : Finset V := (S.erase a).erase b
  let L : List V := a :: (T.toList ++ [b])
  have haT : a ∉ T := by simp [T]
  have hbT : b ∉ T := by simp [T]
  have hTsub : T ⊆ S := by
    intro z hz
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz)
  have happ : (T.toList ++ [b]).Nodup := by
    apply List.Nodup.append T.nodup_toList (by simp)
    rw [List.disjoint_left]
    intro z hz hz'
    have hzb : z = b := List.mem_singleton.mp hz'
    subst z
    exact hbT (Finset.mem_toList.mp hz)
  have hLnodup : L.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, happ⟩
    intro hz
    rcases List.mem_append.mp hz with h | h
    · exact haT (Finset.mem_toList.mp h)
    · exact hab (List.mem_singleton.mp h)
  have hmem (z : V) : z ∈ L ↔ z ∈ S := by
    constructor
    · intro hz
      rcases List.mem_cons.mp hz with h | h
      · exact h.symm ▸ ha
      · rcases List.mem_append.mp h with h | h
        · exact hTsub (Finset.mem_toList.mp h)
        · exact (List.mem_singleton.mp h).symm ▸ hb
    · intro hz
      by_cases hza : z = a
      · exact List.mem_cons.mpr (Or.inl hza)
      by_cases hzb : z = b
      · exact List.mem_cons.mpr
          (Or.inr (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr hzb))))
      have hzT : z ∈ T := by
        exact Finset.mem_erase.mpr ⟨hzb, Finset.mem_erase.mpr ⟨hza, hz⟩⟩
      exact List.mem_cons.mpr
        (Or.inr (List.mem_append.mpr (Or.inl (Finset.mem_toList.mpr hzT))))
  have hchain : L.IsChain G.Adj := by
    apply List.Pairwise.isChain
    exact hLnodup.pairwise_of_forall_ne
      (fun x hx y hy hxy => hclique ((hmem x).mp hx) ((hmem y).mp hy) hxy)
  have hne : L ≠ [] := by simp [L]
  have hhead : L.head hne = a := by simp [L]
  have hlast : L.getLast hne = b := by
    change ((a :: T.toList) ++ [b]).getLast _ = b
    exact List.getLast_append_singleton (a :: T.toList)
  have hbErase : b ∈ S.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  have hTcard : T.card + 1 = (S.erase a).card :=
    Finset.card_erase_add_one hbErase
  have hScard : (S.erase a).card + 1 = S.card :=
    Finset.card_erase_add_one ha
  have hLlength : L.length = S.card := by
    have hTL : T.toList.length = T.card := Finset.length_toList T
    simp only [L, List.length_cons, List.length_append, List.length_nil, hTL]
    omega
  let P : G.Walk a b := (Walk.ofSupport L hne hchain).copy hhead hlast
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [Walk.isPath_def]
    simpa only [P, Walk.support_copy, Walk.support_ofSupport]
      using hLnodup
  · simp only [P, Walk.length_copy, Walk.length_ofSupport, hLlength]
  · intro z
    simpa only [P, Walk.support_copy, Walk.support_ofSupport] using hmem z

end ErdosProblems.PathUpperReduction.CliqueSpanningPath1105

namespace ErdosProblems.PathUpperReduction.LargeCoreStructure1105
open SimpleGraph

/-- The first vertex of a simple path does not recur in its support tail. -/
theorem path_start_notMem_tail {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : p.IsPath) : a ∉ p.support.tail := by
  have hn := hp.support_nodup
  rw [← Walk.cons_tail_support] at hn
  exact (List.nodup_cons.mp hn).1

/-- An actual clique-spanning path and an outside ear yield an actual long cycle.
The ear is an auxiliary input here; the component caller constructs it internally. -/
theorem long_cycle_of_clique_ear {V : Type*} (G : SimpleGraph V)
    (S : Finset V) {K : ℕ} {a b : V}
    (hK : 5 ≤ K) (hcard : S.card = K - 2)
    (hclique : G.IsClique (S : Set V))
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (Q : G.Walk a b) (hQ : Q.IsPath) (hQL : 3 ≤ Q.length)
    (hcontact : ∀ z, z ∈ Q.support → z ∈ S → z = a ∨ z = b) :
    ∃ m : ℕ, K ≤ m ∧ cycleGraph m ⊑ G := by
  classical
  obtain ⟨P, hP, hPlength, hPsupport⟩ :=
    ErdosProblems.PathUpperReduction.CliqueSpanningPath1105.exists_clique_spanning_path
      G S hclique ha hb hab
  have hcycle : (P.append Q.reverse).IsCycle := by
    apply hP.isCycle_append hQ.reverse
    · intro z hzP hzQ
      have hzPs : z ∈ P.support := List.mem_of_mem_tail hzP
      have hzQs : z ∈ Q.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using List.mem_of_mem_tail hzQ
      rcases hcontact z hzQs ((hPsupport z).mp hzPs) with hza | hzb
      · exact path_start_notMem_tail P hP (hza ▸ hzP)
      · exact path_start_notMem_tail Q.reverse hQ.reverse (hzb ▸ hzQ)
    · right
      simp only [Walk.length_reverse]
      omega
  have hlength : K ≤ (P.append Q.reverse).length := by
    simp only [Walk.length_append, Walk.length_reverse]
    omega
  refine ⟨(P.append Q.reverse).length, hlength, ?_⟩
  exact (cycleGraph_isContained_iff (by omega)).mpr
    ⟨a, P.append Q.reverse, hcycle, rfl⟩

/-- Under actual ALL-long-cycle freedom, two distinct contacts of one actual
outside component cannot attach to distinct clique anchors. The ear and the
clique-spanning path are constructed from the SAME graph, not supplied. -/
theorem distinct_component_contacts_have_same_anchor {V : Type*}
    (G : SimpleGraph V) (S : Finset V) {K : ℕ}
    (hK : 5 ≤ K) (hcard : S.card = K - 2)
    (hclique : G.IsClique (S : Set V))
    (hfree : ∀ m : ℕ, K ≤ m → (cycleGraph m).Free G)
    (C : (G.induce (S : Set V)ᶜ).ConnectedComponent)
    {a b : V} (ha : a ∈ S) (hb : b ∈ S)
    (v w : ↥((S : Set V)ᶜ)) (hvC : v ∈ C.supp) (hwC : w ∈ C.supp)
    (hvw : v ≠ w) (hav : G.Adj a v.val) (hwb : G.Adj w.val b) : a = b := by
  by_contra hab
  obtain ⟨Q, hQ, hQL, _, _, hcontact, _⟩ :=
    ErdosProblems.PathUpperReduction.FixedContactEar1105.exists_fixed_contact_ear
      C ha hb hab v w hvC hwC hvw hav hwb
  obtain ⟨m, hm, hcycle⟩ :=
    long_cycle_of_clique_ear G S hK hcard hclique ha hb hab Q hQ hQL hcontact
  exact hfree m hm hcycle

end ErdosProblems.PathUpperReduction.LargeCoreStructure1105

/-! All contacts below are constructed from ACTUAL vertex-deletion connectivity. No ear, attachment, component singleton, or desired edge bound is premised. -/

namespace ErdosProblems.PathUpperReduction.LargeCoreStructure1105
open SimpleGraph

/-- An actual connected deletion graph crosses the actual boundary of T. -/
theorem deletion_connected_boundary {V : Type*} (G : SimpleGraph V)
    (T : Set V) {a u v : V}
    (hdelete : (G.induce {z : V | z ≠ a}).Connected)
    (hu : u ∈ T) (hua : u ≠ a) (hv : v ∉ T) (hva : v ≠ a) :
    ∃ x : V, x ∈ T ∧ x ≠ a ∧
      ∃ y : V, y ∉ T ∧ y ≠ a ∧ G.Adj x y := by
  let u' : {z : V // z ≠ a} := ⟨u, hua⟩
  let v' : {z : V // z ≠ a} := ⟨v, hva⟩
  obtain ⟨p, _⟩ := hdelete.exists_isPath u' v'
  obtain ⟨d, _, hdx, hdy⟩ :=
    p.exists_boundary_dart {z | z.val ∈ T} hu hv
  exact ⟨d.fst.val, hdx, d.fst.property,
    d.snd.val, hdy, d.snd.property, d.adj⟩

/-- An edge leaving a whole outside component must end in the actual core. -/
theorem component_boundary_lands_in_core {V : Type*} (G : SimpleGraph V)
    (S : Finset V) (C : (G.induce (S : Set V)ᶜ).ConnectedComponent)
    {x y : V}
    (hx : x ∈ (Subtype.val : ↥((S : Set V)ᶜ) → V) '' C.supp)
    (hy : y ∉ (Subtype.val : ↥((S : Set V)ᶜ) → V) '' C.supp)
    (hxy : G.Adj x y) : y ∈ S := by
  classical
  by_contra hyS
  obtain ⟨v, hvC, rfl⟩ := hx
  let w : ↥((S : Set V)ᶜ) := ⟨y, hyS⟩
  have hwC : w ∈ C.supp :=
    C.mem_supp_of_adj_mem_supp hvC
      (show (G.induce (S : Set V)ᶜ).Adj v w from hxy)
  exact hy ⟨w, hwC, rfl⟩

/-- Delete any actual core vertex: the whole outside component still has an
actual core contact whose anchor avoids that deleted vertex. -/
theorem component_contact_avoiding_core_vertex {V : Type*}
    (G : SimpleGraph V) (S : Finset V) (hcard : 1 < S.card)
    (hdelete : ∀ a : V, (G.induce {z : V | z ≠ a}).Connected)
    (C : (G.induce (S : Set V)ᶜ).ConnectedComponent)
    {a : V} (ha : a ∈ S) :
    ∃ w : ↥((S : Set V)ᶜ), w ∈ C.supp ∧
      ∃ b : V, b ∈ S ∧ b ≠ a ∧ G.Adj w.val b := by
  classical
  obtain ⟨u, huC⟩ := C.nonempty_supp
  obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne hcard a
  have hua : u.val ≠ a := by
    intro h
    exact u.property (h.symm ▸ ha)
  have hboutside : b ∉ (Subtype.val : ↥((S : Set V)ᶜ) → V) '' C.supp := by
    rintro ⟨z, _, hz⟩
    exact z.property (hz.symm ▸ hb)
  obtain ⟨x, hx, _, y, hy, hya, hxy⟩ :=
    deletion_connected_boundary G
      ((Subtype.val : ↥((S : Set V)ᶜ) → V) '' C.supp)
      (hdelete a) ⟨u, huC, rfl⟩ hua hboutside hba
  have hyS := component_boundary_lands_in_core G S C hx hy hxy
  obtain ⟨w, hwC, rfl⟩ := hx
  exact ⟨w, hwC, y, hyS, hya, hxy⟩

/-- Actual deletion connectivity and ALL-long-cycle freedom force every
outside component of the actual (K-2)-clique to contain one vertex. -/
theorem outside_component_subsingleton {V : Type*}
    (G : SimpleGraph V) (S : Finset V) {K : ℕ}
    (hK : 5 ≤ K) (hcard : S.card = K - 2)
    (hclique : G.IsClique (S : Set V))
    (hfree : ∀ m : ℕ, K ≤ m → (cycleGraph m).Free G)
    (hdelete : ∀ a : V, (G.induce {z : V | z ≠ a}).Connected)
    (C : (G.induce (S : Set V)ᶜ).ConnectedComponent) :
    ∀ v w : ↥((S : Set V)ᶜ), v ∈ C.supp → w ∈ C.supp → v = w := by
  classical
  have hScard : 1 < S.card := by omega
  obtain ⟨a₀, ha₀⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  obtain ⟨w₁, hw₁C, a₁, ha₁, _, hw₁a₁⟩ :=
    component_contact_avoiding_core_vertex G S hScard hdelete C ha₀
  obtain ⟨w₂, hw₂C, a₂, ha₂, ha₂a₁, hw₂a₂⟩ :=
    component_contact_avoiding_core_vertex G S hScard hdelete C ha₁
  have hw₁₂ : w₁ = w₂ := by
    by_contra hne
    have ha₁₂ := distinct_component_contacts_have_same_anchor
      G S hK hcard hclique hfree C ha₁ ha₂
      w₁ w₂ hw₁C hw₂C hne hw₁a₁.symm hw₂a₂
    exact ha₂a₁ ha₁₂.symm
  subst w₂
  have hno_other_contact : ∀ u : ↥((S : Set V)ᶜ), u ∈ C.supp →
      u ≠ w₁ → ∀ b : V, b ∈ S → ¬G.Adj u.val b := by
    intro u huC huw b hb hub
    have hb₁ := distinct_component_contacts_have_same_anchor
      G S hK hcard hclique hfree C hb ha₁
      u w₁ huC hw₁C huw hub.symm hw₁a₁
    have hb₂ := distinct_component_contacts_have_same_anchor
      G S hK hcard hclique hfree C hb ha₂
      u w₁ huC hw₁C huw hub.symm hw₂a₂
    exact ha₂a₁ (hb₂.symm.trans hb₁)
  have hevery : ∀ u : ↥((S : Set V)ᶜ), u ∈ C.supp → u = w₁ := by
    intro u huC
    by_contra huw
    have huwVal : u.val ≠ w₁.val := fun h => huw (Subtype.ext h)
    have ha₁w : a₁ ≠ w₁.val := by
      intro h
      exact w₁.property (h ▸ ha₁)
    have ha₁outside :
        a₁ ∉ (Subtype.val : ↥((S : Set V)ᶜ) → V) '' C.supp := by
      rintro ⟨z, _, hz⟩
      exact z.property (hz.symm ▸ ha₁)
    obtain ⟨x, hx, hxw, y, hy, _, hxy⟩ :=
      deletion_connected_boundary G
        ((Subtype.val : ↥((S : Set V)ᶜ) → V) '' C.supp)
        (hdelete w₁.val) ⟨u, huC, rfl⟩ huwVal ha₁outside ha₁w
    have hyS := component_boundary_lands_in_core G S C hx hy hxy
    obtain ⟨z, hzC, rfl⟩ := hx
    have hzw : z ≠ w₁ := by
      intro h
      exact hxw (congrArg Subtype.val h)
    exact hno_other_contact z hzC hzw y hyS hxy
  intro v w hvC hwC
  exact (hevery v hvC).trans (hevery w hwC).symm

/-- The actual graph outside the (K-2)-clique is edgeless. This is an ordinary
structural theorem; no original coloring or anti-Ramsey conclusion is asserted. -/
theorem outside_independent {V : Type*}
    (G : SimpleGraph V) (S : Finset V) {K : ℕ}
    (hK : 5 ≤ K) (hcard : S.card = K - 2)
    (hclique : G.IsClique (S : Set V))
    (hfree : ∀ m : ℕ, K ≤ m → (cycleGraph m).Free G)
    (hdelete : ∀ a : V, (G.induce {z : V | z ≠ a}).Connected) :
    G.induce (S : Set V)ᶜ = ⊥ := by
  apply SimpleGraph.eq_bot_iff_forall_not_adj.mpr
  intro v w hvw
  let C := (G.induce (S : Set V)ᶜ).connectedComponentMk v
  have hvC : v ∈ C.supp := rfl
  have hwC : w ∈ C.supp := C.mem_supp_of_adj_mem_supp hvC hvw
  have heq := outside_component_subsingleton
    G S hK hcard hclique hfree hdelete C v w hvC hwC
  exact hvw.ne heq

end ErdosProblems.PathUpperReduction.LargeCoreStructure1105

/-!
The explicit share and disjoint ears avoid a Hamilton-cycle-extension oracle. All vertex distinction follows from actual S membership and u,v outside S. These exact-cycle auxiliaries accept selected neighbor pairs; the final
classification must choose those pairs from actual neighborhoods, and apply
the all-long-cycle freedom of the SAME graph.
-/

namespace ErdosProblems.PathUpperReduction.CommonAnchors1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CliqueSpanningPath1105
open ErdosProblems.PathUpperReduction.LargeCoreStructure1105

theorem exact_cycle_of_clique_ear {V : Type*} (G : SimpleGraph V)
    (S : Finset V) {a b : V} (hclique : G.IsClique (S : Set V))
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (Q : G.Walk a b) (hQ : Q.IsPath) (hQL : 3 ≤ Q.length)
    (hcontact : ∀ z, z ∈ Q.support → z ∈ S → z = a ∨ z = b) :
    cycleGraph (Q.length + (S.card - 1)) ⊑ G := by
  classical
  obtain ⟨P, hP, hPlength, hPsupport⟩ :=
    exists_clique_spanning_path G S hclique ha hb hab
  have hcycle : (P.append Q.reverse).IsCycle := by
    apply hP.isCycle_append hQ.reverse
    · intro z hzP hzQ
      have hzPs : z ∈ P.support := List.mem_of_mem_tail hzP
      have hzQs : z ∈ Q.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using List.mem_of_mem_tail hzQ
      rcases hcontact z hzQs ((hPsupport z).mp hzPs) with hza | hzb
      · exact path_start_notMem_tail P hP (hza ▸ hzP)
      · exact path_start_notMem_tail Q.reverse hQ.reverse (hzb ▸ hzQ)
    · right
      simp only [Walk.length_reverse]
      omega
  apply (cycleGraph_isContained_iff (by omega)).mpr
  refine ⟨a, P.append Q.reverse, hcycle, ?_⟩
  simp only [Walk.length_append, Walk.length_reverse, hPlength, Nat.add_comm]

theorem cycle_of_shared_neighbor_pairs {V : Type*} (G : SimpleGraph V)
    (S : Finset V) {K : ℕ} (hK : 5 ≤ K) (hcard : S.card = K - 2)
    (hclique : G.IsClique (S : Set V))
    {u v a b c : V} (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hau : G.Adj a u) (hub : G.Adj u b)
    (hbv : G.Adj b v) (hvc : G.Adj v c) :
    cycleGraph K ⊑ G := by
  classical
  let R : Finset V := S.erase b
  have hRclique : G.IsClique (R : Set V) :=
    SimpleGraph.IsClique.subset (by
      intro z hz
      exact Finset.mem_of_mem_erase hz) hclique
  have haR : a ∈ R := Finset.mem_erase.mpr ⟨hab, ha⟩
  have hcR : c ∈ R := Finset.mem_erase.mpr ⟨hbc.symm, hc⟩
  have hxu (x : V) (hx : x ∈ S) : x ≠ u := fun h => hu (h ▸ hx)
  have hxv (x : V) (hx : x ∈ S) : x ≠ v := fun h => hv (h ▸ hx)
  let Q : G.Walk a c := Walk.cons hau
    (Walk.cons hub (Walk.cons hbv (Walk.cons hvc Walk.nil)))
  have hQ : Q.IsPath := by
    rw [Walk.isPath_def]
    change [a, u, b, v, c].Nodup
    simp only [List.nodup_cons, List.mem_cons,
      List.not_mem_nil, not_false_eq_true]
    grind
  have hQL : Q.length = 4 := by simp [Q]
  have hcontact : ∀ z, z ∈ Q.support → z ∈ R → z = a ∨ z = c := by
    intro z hzQ hzR
    have hzCases : z = a ∨ z = u ∨ z = b ∨ z = v ∨ z = c := by
      simpa only [Q, Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] using hzQ
    rcases hzCases with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact (hu (Finset.mem_of_mem_erase hzR)).elim
    · exact ((Finset.mem_erase.mp hzR).1 rfl).elim
    · exact (hv (Finset.mem_of_mem_erase hzR)).elim
    · exact Or.inr rfl
  have hRcard : R.card + 1 = S.card := Finset.card_erase_add_one hb
  have horder : Q.length + (R.card - 1) = K := by omega
  have hcopy := exact_cycle_of_clique_ear G R hRclique haR hcR hac
    Q hQ (by omega) hcontact
  rw [horder] at hcopy
  exact hcopy

theorem cycle_of_disjoint_neighbor_pairs {V : Type*} (G : SimpleGraph V)
    (S : Finset V) {K : ℕ} (hK : 5 ≤ K) (hcard : S.card = K - 2)
    (hclique : G.IsClique (S : Set V))
    {u v a b c d : V} (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hau : G.Adj a u) (hub : G.Adj u b)
    (hcv : G.Adj c v) (hvd : G.Adj v d) :
    cycleGraph K ⊑ G := by
  classical
  let R : Finset V := (S.erase b).erase c
  have hRclique : G.IsClique (R : Set V) :=
    SimpleGraph.IsClique.subset (by
      intro z hz
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz)) hclique
  have haR : a ∈ R :=
    Finset.mem_erase.mpr ⟨hac, Finset.mem_erase.mpr ⟨hab, ha⟩⟩
  have hdR : d ∈ R :=
    Finset.mem_erase.mpr ⟨hcd.symm, Finset.mem_erase.mpr ⟨hbd.symm, hd⟩⟩
  have hxu (x : V) (hx : x ∈ S) : x ≠ u := fun h => hu (h ▸ hx)
  have hxv (x : V) (hx : x ∈ S) : x ≠ v := fun h => hv (h ▸ hx)
  have hbcAdj : G.Adj b c := hclique hb hc hbc
  let Q : G.Walk a d := Walk.cons hau
    (Walk.cons hub (Walk.cons hbcAdj (Walk.cons hcv (Walk.cons hvd Walk.nil))))
  have hQ : Q.IsPath := by
    rw [Walk.isPath_def]
    change [a, u, b, c, v, d].Nodup
    simp only [List.nodup_cons, List.mem_cons,
      List.not_mem_nil, not_false_eq_true]
    grind
  have hQL : Q.length = 5 := by simp [Q]
  have hcontact : ∀ z, z ∈ Q.support → z ∈ R → z = a ∨ z = d := by
    intro z hzQ hzR
    have hzCases : z = a ∨ z = u ∨ z = b ∨ z = c ∨ z = v ∨ z = d := by
      simpa only [Q, Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] using hzQ
    rcases hzCases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact (hu (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hzR))).elim
    · exact ((Finset.mem_erase.mp (Finset.mem_of_mem_erase hzR)).1 rfl).elim
    · exact ((Finset.mem_erase.mp hzR).1 rfl).elim
    · exact (hv (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hzR))).elim
    · exact Or.inr rfl
  have hcErase : c ∈ S.erase b := Finset.mem_erase.mpr ⟨hbc.symm, hc⟩
  have hRcard : R.card + 1 = (S.erase b).card := Finset.card_erase_add_one hcErase
  have hScard : (S.erase b).card + 1 = S.card := Finset.card_erase_add_one hb
  have horder : Q.length + (R.card - 1) = K := by omega
  have hcopy := exact_cycle_of_clique_ear G R hRclique haR hdR had
    Q hQ (by omega) hcontact
  rw [horder] at hcopy
  exact hcopy

end ErdosProblems.PathUpperReduction.CommonAnchors1105

/-!
Actual contacts are derived from deletion connectivity with `T = {u}`;
the final endpoint supplies no contacts, ears, or desired pair. The two
distinct outside vertices are essential to the exact-neighborhood argument.
-/

namespace ErdosProblems.PathUpperReduction.CommonAnchors1105
open SimpleGraph
open ErdosProblems.PathUpperReduction.LargeCoreStructure1105

theorem outside_contact_avoiding {V : Type*} (G : SimpleGraph V)
    (S : Finset V) (hcard : 1 < S.card)
    (hind : G.induce (S : Set V)ᶜ = ⊥)
    (hdelete : ∀ a : V, (G.induce {z : V | z ≠ a}).Connected)
    {u a : V} (hu : u ∉ S) (ha : a ∈ S) :
    ∃ b : V, b ∈ S ∧ b ≠ a ∧ G.Adj u b := by
  classical
  obtain ⟨c, hc, hca⟩ := Finset.exists_mem_ne hcard a
  have hua : u ≠ a := fun h => hu (h.symm ▸ ha)
  have hcu : c ∉ ({u} : Set V) := by
    intro h
    have hcu : c = u := h
    exact hu (hcu ▸ hc)
  obtain ⟨x, hx, _, y, _, hya, hxy⟩ :=
    deletion_connected_boundary G ({u} : Set V)
      (hdelete a) (by simp) hua hcu hca
  have hxu : x = u := hx
  subst x
  have hyS : y ∈ S := by
    by_contra hyS
    have hbad : (G.induce (S : Set V)ᶜ).Adj ⟨u, hu⟩ ⟨y, hyS⟩ := hxy
    rw [hind] at hbad
    exact hbad
  exact ⟨y, hyS, hya, hxy⟩

theorem outside_two_core_neighbors {V : Type*} (G : SimpleGraph V)
    (S : Finset V) (hcard : 1 < S.card)
    (hind : G.induce (S : Set V)ᶜ = ⊥)
    (hdelete : ∀ a : V, (G.induce {z : V | z ≠ a}).Connected)
    {u : V} (hu : u ∉ S) :
    ∃ a b : V, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ G.Adj u a ∧ G.Adj u b := by
  classical
  obtain ⟨c, hc⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  obtain ⟨a, ha, _, hua⟩ := outside_contact_avoiding G S hcard hind hdelete hu hc
  obtain ⟨b, hb, hba, hub⟩ := outside_contact_avoiding G S hcard hind hdelete hu ha
  exact ⟨a, b, ha, hb, hba.symm, hua, hub⟩

/-- One anchor from a second actual neighbor pair lies in the first pair:
otherwise an explicit shared or disjoint pair cycle has forbidden order K. -/
theorem neighbor_pair_member {V : Type*} (G : SimpleGraph V)
    (S : Finset V) {K : ℕ} (hK : 5 ≤ K) (hcard : S.card = K - 2)
    (hclique : G.IsClique (S : Set V))
    (hfree : ∀ m : ℕ, K ≤ m → (cycleGraph m).Free G)
    {u v a b c d : V} (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hau : G.Adj a u) (hub : G.Adj u b)
    (hcv : G.Adj c v) (hvd : G.Adj v d) : c = a ∨ c = b := by
  classical
  by_contra hnot
  have hac : a ≠ c := fun h => hnot (Or.inl h.symm)
  have hbc : b ≠ c := fun h => hnot (Or.inr h.symm)
  by_cases had : a = d
  · subst d
    exact hfree K le_rfl (cycle_of_shared_neighbor_pairs G S hK hcard hclique
      hu hv huv hb ha hc hab.symm hbc hac
      hub.symm hau.symm hvd.symm hcv.symm)
  by_cases hbd : b = d
  · subst d
    exact hfree K le_rfl (cycle_of_shared_neighbor_pairs G S hK hcard hclique
      hu hv huv ha hb hc hab hac hbc
      hau hub hvd.symm hcv.symm)
  exact hfree K le_rfl (cycle_of_disjoint_neighbor_pairs G S hK hcard hclique
    hu hv huv ha hb hc hd hab hac had hbc hbd hcd hau hub hcv hvd)

/-- Every actual neighbor of u belongs to the distinct actual neighbor pair
at v. The extra distinct neighbor at u is constructed, not supplied. -/
theorem neighbors_covered_by_other_pair {V : Type*} (G : SimpleGraph V)
    (S : Finset V) {K : ℕ} (hK : 5 ≤ K) (hcard : S.card = K - 2)
    (hclique : G.IsClique (S : Set V))
    (hfree : ∀ m : ℕ, K ≤ m → (cycleGraph m).Free G)
    (hind : G.induce (S : Set V)ᶜ = ⊥)
    (hdelete : ∀ a : V, (G.induce {z : V | z ≠ a}).Connected)
    {u v a b : V} (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hva : G.Adj v a) (hvb : G.Adj v b) :
    ∀ z : V, G.Adj u z → z = a ∨ z = b := by
  classical
  have hScard : 1 < S.card := by omega
  intro z huz
  have hzS : z ∈ S := by
    by_contra hzS
    have hbad : (G.induce (S : Set V)ᶜ).Adj ⟨u, hu⟩ ⟨z, hzS⟩ := huz
    rw [hind] at hbad
    exact hbad
  obtain ⟨t, ht, htz, hut⟩ := outside_contact_avoiding G S hScard hind hdelete hu hzS
  exact neighbor_pair_member G S hK hcard hclique hfree
    hv hu huv.symm ha hb hzS ht hab htz.symm hva.symm hvb huz.symm hut

/-- Under the literal large-core and ALL-cycle hypotheses, two distinct actual
outside vertices force one COMMON exact two-anchor neighborhood for every
outside vertex. In particular all outside vertices are independent. -/
theorem exists_common_exact_two_anchors {V : Type*} (G : SimpleGraph V)
    (S : Finset V) {K : ℕ} (hK : 5 ≤ K) (hcard : S.card = K - 2)
    (hclique : G.IsClique (S : Set V))
    (hfree : ∀ m : ℕ, K ≤ m → (cycleGraph m).Free G)
    (hdelete : ∀ a : V, (G.induce {z : V | z ≠ a}).Connected)
    (houtside : ∃ u v : V, u ∉ S ∧ v ∉ S ∧ u ≠ v) :
    G.induce (S : Set V)ᶜ = ⊥ ∧
      ∃ a b : V, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
        ∀ u : V, u ∉ S → ∀ z : V, G.Adj u z ↔ z = a ∨ z = b := by
  classical
  have hind := outside_independent G S hK hcard hclique hfree hdelete
  have hScard : 1 < S.card := by omega
  obtain ⟨u₀, v₀, hu₀, hv₀, hu₀v₀⟩ := houtside
  obtain ⟨a, b, ha, hb, hab, hu₀a, hu₀b⟩ :=
    outside_two_core_neighbors G S hScard hind hdelete hu₀
  obtain ⟨c, d, hc, hd, hcd, hv₀c, hv₀d⟩ :=
    outside_two_core_neighbors G S hScard hind hdelete hv₀
  have hcoverV := neighbors_covered_by_other_pair G S hK hcard hclique hfree
    hind hdelete hv₀ hu₀ hu₀v₀.symm ha hb hab hu₀a hu₀b
  have hcAB : c = a ∨ c = b := hcoverV c hv₀c
  have hdAB : d = a ∨ d = b := hcoverV d hv₀d
  have hsubset : ∀ u : V, u ∉ S → ∀ z : V, G.Adj u z → z = a ∨ z = b := by
    intro u hu z huz
    by_cases huu₀ : u = u₀
    · subst u
      have hzCD := neighbors_covered_by_other_pair G S hK hcard hclique hfree
        hind hdelete hu₀ hv₀ hu₀v₀ hc hd hcd hv₀c hv₀d z huz
      rcases hzCD with rfl | rfl
      · exact hcAB
      · exact hdAB
    · exact neighbors_covered_by_other_pair G S hK hcard hclique hfree
        hind hdelete hu hu₀ huu₀ ha hb hab hu₀a hu₀b z huz
  refine ⟨hind, a, b, ha, hb, hab, ?_⟩
  intro u hu z
  have hboth : G.Adj u a ∧ G.Adj u b := by
    obtain ⟨e, f, _, _, hef, hue, huf⟩ :=
      outside_two_core_neighbors G S hScard hind hdelete hu
    have he := hsubset u hu e hue
    have hf := hsubset u hu f huf
    rcases he with rfl | rfl <;> rcases hf with rfl | rfl
    · exact (hef rfl).elim
    · exact ⟨hue, huf⟩
    · exact ⟨huf, hue⟩
    · exact (hef rfl).elim
  constructor
  · exact hsubset u hu z
  · rintro (rfl | rfl)
    · exact hboth.1
    · exact hboth.2

end ErdosProblems.PathUpperReduction.CommonAnchors1105

/-!
The new namespace
keeps attribution and makes the actual Option cone explicit.
-/

namespace ErdosProblems.PathUpperReduction.ConeCoreApplication1105
open SimpleGraph
open ErdosProblems.PathUpperReduction.CommonAnchors1105

/-- Literal `Option` cone adding a universal apex `none`. -/
def cone {V : Type*} (G : SimpleGraph V) : SimpleGraph (Option V) where
  Adj a b := match a, b with
    | some u, some v => G.Adj u v
    | none, some _ => True
    | some _, none => True
    | none, none => False
  symm := ⟨by
    intro a b h
    cases a <;> cases b
    · exact h
    · trivial
    · trivial
    · exact h.symm⟩
  loopless := ⟨by
    intro a
    cases a
    · exact id
    · exact G.loopless.irrefl _⟩

/-- The universal apex is forced INTO the actual core and is one of the two
common anchors. The other actual anchor is an original vertex. -/
theorem cone_common_anchor {V : Type*} (G : SimpleGraph V)
    (S : Finset (Option V)) {K : ℕ} (hK : 5 ≤ K) (hcard : S.card = K - 2)
    (hclique : (cone G).IsClique (S : Set (Option V)))
    (hfree : ∀ m : ℕ, K ≤ m → (cycleGraph m).Free (cone G))
    (hdelete : ∀ a : Option V,
      ((cone G).induce {z : Option V | z ≠ a}).Connected)
    (houtside : ∃ u v : Option V, u ∉ S ∧ v ∉ S ∧ u ≠ v) :
    none ∈ S ∧ ∃ b : V, some b ∈ S ∧
      ∀ u : Option V, u ∉ S → ∀ z : Option V,
        (cone G).Adj u z ↔ z = none ∨ z = some b := by
  classical
  obtain ⟨_, a, b, ha, hb, hab, hneighbors⟩ :=
    exists_common_exact_two_anchors (cone G) S hK hcard hclique hfree hdelete houtside
  have hnoneS : (none : Option V) ∈ S := by
    by_contra hnoneS
    have hsubset : S ⊆ ({a, b} : Finset (Option V)) := by
      intro z hz
      have hadj : (cone G).Adj none z := by
        cases z with
        | none => exact (hnoneS hz).elim
        | some z => trivial
      have hcases := (hneighbors none hnoneS z).mp hadj
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hcases
    have hsmall : S.card ≤ 2 := (Finset.card_le_card hsubset).trans Finset.card_le_two
    omega
  have hnonePair : (none : Option V) = a ∨ none = b := by
    obtain ⟨u, _, hu, _, _⟩ := houtside
    cases u with
    | none => exact (hu hnoneS).elim
    | some u => exact (hneighbors (some u) hu none).mp (by trivial)
  refine ⟨hnoneS, ?_⟩
  rcases hnonePair with hna | hnb
  · subst a
    cases b with
    | none => exact (hab rfl).elim
    | some b =>
      exact ⟨b, hb, hneighbors⟩
  · subst b
    cases a with
    | none => exact (hab rfl).elim
    | some a =>
      refine ⟨a, ha, ?_⟩
      intro u hu z
      exact (hneighbors u hu z).trans or_comm

/-- Pull the actual cone core back to original vertices. It is an actual
clique, and every original outside vertex has exactly the ONE original anchor
as its full neighborhood. No finite count or graph isomorphism is supplied. -/
theorem cone_core_partition {V : Type*} (G : SimpleGraph V)
    (S : Finset (Option V)) {K : ℕ} (hK : 5 ≤ K) (hcard : S.card = K - 2)
    (hclique : (cone G).IsClique (S : Set (Option V)))
    (hfree : ∀ m : ℕ, K ≤ m → (cycleGraph m).Free (cone G))
    (hdelete : ∀ a : Option V,
      ((cone G).induce {z : Option V | z ≠ a}).Connected)
    (houtside : ∃ u v : Option V, u ∉ S ∧ v ∉ S ∧ u ≠ v) :
    let T : Set V := {v : V | some v ∈ S}
    none ∈ S ∧ G.IsClique T ∧
      ∃ b : V, b ∈ T ∧ ∀ u : V, u ∉ T → ∀ z : V, G.Adj u z ↔ z = b := by
  classical
  dsimp only
  obtain ⟨hnoneS, b, hb, hneighbors⟩ :=
    cone_common_anchor G S hK hcard hclique hfree hdelete houtside
  have hTclique : G.IsClique {v : V | some v ∈ S} := by
    intro u hu v hv huv
    exact hclique hu hv (fun h => huv (Option.some.inj h))
  refine ⟨hnoneS, hTclique, b, hb, ?_⟩
  intro u hu z
  have h := hneighbors (some u) hu (some z)
  change G.Adj u z ↔ some z = none ∨ some z = some b at h
  simpa only [Option.some_ne_none, false_or, Option.some.injEq] using h

end ErdosProblems.PathUpperReduction.ConeCoreApplication1105

/-!
No local imports. The generic enumeration takes an actual clique/hub partition; the final literal
cone caller DERIVES that partition and all cardinal guards internally.
-/

namespace ErdosProblems.PathUpperReduction.ConeFiniteContainer1105
open SimpleGraph
open ErdosProblems.PathUpperReduction.ConeCoreApplication1105

theorem finite_pullback_cardinality {n K : ℕ} (S : Finset (Option (Fin n)))
    (hK : 5 ≤ K) (hcard : S.card = K - 2) (hnone : none ∈ S)
    (houtside : ∃ u v : Option (Fin n), u ∉ S ∧ v ∉ S ∧ u ≠ v) :
    let T : Set (Fin n) := {v | some v ∈ S}
    Fintype.card T = K - 3 ∧
      Fintype.card (Tᶜ : Set (Fin n)) = n - (K - 3) ∧
      2 ≤ K - 3 ∧ 2 ≤ n - (K - 3) ∧
      (K - 3) + (n - (K - 3)) = n := by
  classical
  dsimp only
  let A : Finset (Fin n) := Finset.univ.filter (fun v => some v ∈ S)
  have hS : S = insert none (A.image some) := by
    ext z
    cases z <;> simp [A, hnone]
  have hnoneImage : (none : Option (Fin n)) ∉ A.image some := by simp
  have himageCard : (A.image some).card = A.card :=
    Finset.card_image_of_injective A (fun _ _ h => Option.some.inj h)
  have hAcard : A.card = K - 3 := by
    have hScard := congrArg Finset.card hS
    rw [Finset.card_insert_of_notMem hnoneImage, himageCard] at hScard
    omega
  have hTcard : Fintype.card {v : Fin n | some v ∈ S} = K - 3 := by
    exact (Fintype.card_of_subtype A (by intro v; simp [A])).trans hAcard
  have hTcCard : Fintype.card ({v : Fin n | some v ∈ S}ᶜ : Set (Fin n)) =
      n - (K - 3) := by
    rw [Fintype.card_compl_set, Fintype.card_fin, hTcard]
  have hAcCard : Aᶜ.card = n - (K - 3) := by
    rw [Finset.card_compl, Fintype.card_fin, hAcard]
  have hlargeOutside : 2 ≤ n - (K - 3) := by
    obtain ⟨u, v, hu, hv, huv⟩ := houtside
    cases u with
    | none => exact (hu hnone).elim
    | some u =>
      cases v with
      | none => exact (hv hnone).elim
      | some v =>
        have huv' : u ≠ v := fun h => huv (congrArg some h)
        have hpair : ({u, v} : Finset (Fin n)) ⊆ Aᶜ := by
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz
          · simp [A, hu]
          · have hzv : z = v := Finset.mem_singleton.mp hz
            subst z
            simp [A, hv]
        have hle := Finset.card_le_card hpair
        rw [Finset.card_pair huv', hAcCard] at hle
        exact hle
  have hAn : K - 3 ≤ n := by
    have hle := Finset.card_le_card (Finset.subset_univ A)
    simpa only [hAcard, Finset.card_univ, Fintype.card_fin] using hle
  exact ⟨hTcard, hTcCard, by omega, hlargeOutside, by omega⟩

/-- A finite actual clique/hub partition has a full spanning enumeration whose
first core vertex is the actual hub and whose full adjacency is exact. -/
theorem finite_clique_hub_enumeration {n m l : ℕ}
    (G : SimpleGraph (Fin n)) (T : Set (Fin n)) [DecidablePred (· ∈ T)] (hm : 0 < m)
    (hTcard : Fintype.card T = m)
    (hTcCard : Fintype.card (Tᶜ : Set (Fin n)) = l)
    (hclique : G.IsClique T) (b : Fin n) (hb : b ∈ T)
    (hneighbors : ∀ u : Fin n, u ∉ T → ∀ z : Fin n, G.Adj u z ↔ z = b) :
    ∃ e : (Fin m ⊕ Fin l) ≃ Fin n,
      e (Sum.inl ⟨0, hm⟩) = b ∧
      Set.range (fun i : Fin m => e (Sum.inl i)) = T ∧
      Set.range (fun j : Fin l => e (Sum.inr j)) = Tᶜ ∧
      ∀ x y : Fin m ⊕ Fin l, G.Adj (e x) (e y) ↔
        match x, y with
        | Sum.inl i, Sum.inl j => i ≠ j
        | Sum.inl i, Sum.inr _ => i.val = 0
        | Sum.inr _, Sum.inl j => j.val = 0
        | Sum.inr _, Sum.inr _ => False := by
  classical
  let e₀ : Fin m ≃ T := (Fintype.equivFinOfCardEq hTcard).symm
  let eL : Fin m ≃ T :=
    (Equiv.swap ⟨0, hm⟩ (e₀.symm ⟨b, hb⟩)).trans e₀
  let eR : Fin l ≃ (Tᶜ : Set (Fin n)) := (Fintype.equivFinOfCardEq hTcCard).symm
  let e : (Fin m ⊕ Fin l) ≃ Fin n :=
    (Equiv.sumCongr eL eR).trans (Equiv.Set.sumCompl T)
  have hzero : (eL ⟨0, hm⟩).val = b := by
    dsimp only [eL, Equiv.trans_apply]
    rw [Equiv.swap_apply_left]
    simp only [Equiv.apply_symm_apply]
  have hhub (i : Fin m) : (eL i).val = b ↔ i.val = 0 := by
    constructor
    · intro h
      have hi : i = ⟨0, hm⟩ :=
        eL.injective (Subtype.ext (h.trans hzero.symm))
      exact congrArg Fin.val hi
    · intro hi
      have hiz : i = ⟨0, hm⟩ := Fin.ext hi
      simpa only [hiz] using hzero
  have hleft (i : Fin m) : e (Sum.inl i) = (eL i).val := rfl
  have hright (j : Fin l) : e (Sum.inr j) = (eR j).val := rfl
  have hleftRange : Set.range (fun i : Fin m => e (Sum.inl i)) = T := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (eL i).property
    · intro hx
      refine ⟨eL.symm ⟨x, hx⟩, ?_⟩
      change (eL (eL.symm ⟨x, hx⟩)).val = x
      simp only [Equiv.apply_symm_apply]
  have hrightRange : Set.range (fun j : Fin l => e (Sum.inr j)) = Tᶜ := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact (eR j).property
    · intro hx
      refine ⟨eR.symm ⟨x, hx⟩, ?_⟩
      change (eR (eR.symm ⟨x, hx⟩)).val = x
      simp only [Equiv.apply_symm_apply]
  refine ⟨e, hzero, hleftRange, hrightRange, ?_⟩
  intro x y
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      change G.Adj (eL i).val (eL j).val ↔ i ≠ j
      constructor
      · intro h hij
        exact h.ne (congrArg (fun t : Fin m => (eL t).val) hij)
      · intro hij
        exact hclique (eL i).property (eL j).property
          (fun h => hij (eL.injective (Subtype.ext h)))
    | inr j =>
      change G.Adj (eL i).val (eR j).val ↔ i.val = 0
      constructor
      · intro h
        exact (hhub i).mp ((hneighbors _ (eR j).property _).mp h.symm)
      · intro hi
        exact ((hneighbors _ (eR j).property _).mpr ((hhub i).mpr hi)).symm
  | inr i =>
    cases y with
    | inl j =>
      change G.Adj (eR i).val (eL j).val ↔ j.val = 0
      exact (hneighbors _ (eR i).property _).trans (hhub j)
    | inr j =>
      change G.Adj (eR i).val (eR j).val ↔ False
      constructor
      · intro h
        have hval := (hneighbors _ (eR i).property _).mp h
        exact (eR j).property (hval.symm ▸ hb)
      · exact False.elim

/-- Literal actual-cone caller: the finite cardinalities, hub, spanning
equivalence and full original adjacency are all conclusions. -/
theorem cone_finite_container {n K : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Option (Fin n))) (hK : 5 ≤ K) (hcard : S.card = K - 2)
    (hclique : (cone G).IsClique (S : Set (Option (Fin n))))
    (hfree : ∀ r : ℕ, K ≤ r → (cycleGraph r).Free (cone G))
    (hdelete : ∀ a : Option (Fin n),
      ((cone G).induce {z : Option (Fin n) | z ≠ a}).Connected)
    (houtside : ∃ u v : Option (Fin n), u ∉ S ∧ v ∉ S ∧ u ≠ v) :
    let m := K - 3
    let l := n - m
    let T : Set (Fin n) := {v | some v ∈ S}
    2 ≤ m ∧ 2 ≤ l ∧ m + l = n ∧ Fintype.card T = m ∧
      ∃ b : Fin n, ∃ e : (Fin m ⊕ Fin l) ≃ Fin n,
        b ∈ T ∧ e (Sum.inl ⟨0, by omega⟩) = b ∧
        Set.range (fun i : Fin m => e (Sum.inl i)) = T ∧
        Set.range (fun j : Fin l => e (Sum.inr j)) = Tᶜ ∧
        ∀ x y : Fin m ⊕ Fin l, G.Adj (e x) (e y) ↔
          match x, y with
          | Sum.inl i, Sum.inl j => i ≠ j
          | Sum.inl i, Sum.inr _ => i.val = 0
          | Sum.inr _, Sum.inl j => j.val = 0
          | Sum.inr _, Sum.inr _ => False := by
  classical
  dsimp only
  obtain ⟨hnone, hTclique, b, hb, hneighbors⟩ :=
    cone_core_partition G S hK hcard hclique hfree hdelete houtside
  obtain ⟨hTcard, hTcCard, hm, hl, hsum⟩ :=
    finite_pullback_cardinality S hK hcard hnone houtside
  obtain ⟨e, hezero, heleft, heright, headj⟩ :=
    finite_clique_hub_enumeration G {v : Fin n | some v ∈ S}
      (by omega : 0 < K - 3) hTcard hTcCard hTclique b hb hneighbors
  exact ⟨hm, hl, hsum, hTcard, b, e, hb, hezero, heleft, heright, headj⟩

end ErdosProblems.PathUpperReduction.ConeFiniteContainer1105
