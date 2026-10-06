module

public import CyclePathOre
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Option.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
The cone is on Option (Fin k), with none
its single apex; the final Ore graph is on Fin (k+1), transported along the
derived bijective spanning path order.
-/

namespace ErdosProblems.PathSpanningNonedgeDeficit

open SimpleGraph Finset

noncomputable instance neighbor_fintype {V : Type*} [Finite V]
    (G : SimpleGraph V) (v : V) : Fintype (G.neighborSet v) :=
  Fintype.ofFinite _

/-- Add precisely the one unordered pair; copies remain non-induced. -/
def augment {k : ℕ} (G : SimpleGraph (Fin k)) (u v : Fin k) :
    SimpleGraph (Fin k) := G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}

/-- The one-apex cone, with all old edges unchanged. -/
def cone {k : ℕ} (G : SimpleGraph (Fin k)) : SimpleGraph (Option (Fin k)) where
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

theorem cone_degree_some {k : ℕ} (G : SimpleGraph (Fin k))
    (u : Fin k) : (cone G).degree (some u) = G.degree u + 1 := by
  classical
  have hset : (cone G).neighborFinset (some u) =
      insert none ((G.neighborFinset u).image some) := by
    ext w
    rw [SimpleGraph.mem_neighborFinset]
    cases w <;> simp [SimpleGraph.mem_neighborFinset, cone]
  change ((cone G).neighborFinset (some u)).card = G.degree u + 1
  rw [hset]
  calc
    _ = ((G.neighborFinset u).image some).card + 1 :=
      Finset.card_insert_of_notMem (by simp)
    _ = G.degree u + 1 := congrArg (fun t : ℕ => t + 1)
      (Finset.card_image_of_injective _ (Option.some_injective _))

/-- Deleting the unique apex from a spanning ordinary cycle produces an
ordinary spanning path, by the literal cyclic rotation after that apex. -/
theorem cone_cycle_free_of_path_free {k : ℕ}
    (G : SimpleGraph (Fin k)) (hfree : (pathGraph k).Free G) :
    (cycleGraph (k + 1)).Free (cone G) := by
  classical
  intro hcopy
  obtain ⟨f⟩ := hcopy
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨f.injective, by simp⟩
  obtain ⟨j, hj⟩ := hbij.2 none
  let q : Fin k → Fin (k + 1) := fun i => j + Fin.succ i
  have hq : Function.Injective q := by
    intro a b h
    apply Fin.succ_injective k
    exact add_left_cancel h
  have hsome (i : Fin k) : ∃ v : Fin k, f (q i) = some v := by
    cases he : f (q i) with
    | none =>
        have hi : q i = j := f.injective (he.trans hj.symm)
        have hz : Fin.succ i = (0 : Fin (k + 1)) := by
          apply add_left_cancel (a := j)
          simpa only [q, add_zero] using hi
        exact (Fin.succ_ne_zero i hz).elim
    | some v => exact ⟨v, rfl⟩
  let p : Fin k → Fin k := fun i => Classical.choose (hsome i)
  have hp_eq (i : Fin k) : f (q i) = some (p i) :=
    Classical.choose_spec (hsome i)
  have hp : Function.Injective p := by
    intro a b h
    apply hq
    apply f.injective
    change f (q a) = f (q b)
    rw [hp_eq a, hp_eq b, h]
  have hstep {a b : Fin k} (hab : a.val + 1 = b.val) :
      G.Adj (p a) (p b) := by
    have hle : Fin.succ a ≤ Fin.succ b := by
      simpa only [Fin.le_iff_val_le_val, Fin.val_succ] using (by omega :
        a.val + 1 ≤ b.val + 1)
    have hsub : ((Fin.succ b : Fin (k + 1)) - Fin.succ a).val = 1 := by
      rw [Fin.sub_val_of_le hle]
      simp only [Fin.val_succ]
      omega
    have hrot : (q b - q a).val = 1 := by
      have heq : q b - q a = Fin.succ b - Fin.succ a := by
        dsimp [q]
        abel
      rw [heq]
      exact hsub
    have hc : (cycleGraph (k + 1)).Adj (q a) (q b) :=
      cycleGraph_adj'.mpr (Or.inr hrot)
    have hm := f.toHom.map_adj hc
    change (cone G).Adj (f (q a)) (f (q b)) at hm
    rw [hp_eq a, hp_eq b] at hm
    exact hm
  let φ : (pathGraph k) →g G := ⟨p, by
    intro a b hab
    rcases pathGraph_adj.mp hab with h | h
    · exact hstep h
    · exact (hstep h).symm⟩
  exact hfree ⟨φ.toCopy hp⟩

/-- An ordinary augmented spanning path must contain the added pair, at a
literal consecutive position. No favorable orientation is assumed. -/
theorem added_pair_occurs {k : ℕ} (G : SimpleGraph (Fin k))
    (hfree : (pathGraph k).Free G) (u v : Fin k)
    (p : (pathGraph k).Copy (augment G u v)) :
    ∃ j : Fin k, ∃ hj : j.val + 1 < k,
      s(p j, p ⟨j.val + 1, hj⟩) = s(u, v) := by
  classical
  have hex : ∃ a b : Fin k, (pathGraph k).Adj a b ∧
      ¬ G.Adj (p a) (p b) := by
    by_contra! h
    let φ : (pathGraph k) →g G := ⟨p, by
      intro a b hab
      exact h a b hab⟩
    exact hfree ⟨φ.toCopy p.injective⟩
  obtain ⟨a, b, hab, hnot⟩ := hex
  have hnew : s(p a, p b) = s(u, v) := by
    have hm := p.toHom.map_adj hab
    change (G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Adj (p a) (p b) at hm
    rcases (SimpleGraph.sup_adj _ _ _ _).mp hm with h | h
    · exact (hnot h).elim
    · exact Set.mem_singleton_iff.mp ((SimpleGraph.fromEdgeSet_adj _).mp h).1
  rcases pathGraph_adj.mp hab with hab | hba
  · have hj : a.val + 1 < k := by omega
    have hn : (⟨a.val + 1, hj⟩ : Fin k) = b := Fin.ext hab
    exact ⟨a, hj, by simpa only [hn] using hnew⟩
  · have hj : b.val + 1 < k := by omega
    have hn : (⟨b.val + 1, hj⟩ : Fin k) = a := Fin.ext hba
    refine ⟨b, hj, ?_⟩
    rw [hn]
    exact Sym2.eq_swap.trans hnew

def splitOrder {k : ℕ} (p : Fin k → Fin k)
    (j : Fin k) (hj : j.val + 1 < k) (i : Fin (k + 1)) : Option (Fin k) :=
  if h : i.val ≤ j.val then
    some (p ⟨j.val - i.val,
      lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_succ_lt hj)⟩)
  else if h' : i.val = j.val + 1 then none
  else some (p ⟨k + j.val + 1 - i.val, by omega⟩)

theorem splitOrder_injective {k : ℕ} (p : Fin k → Fin k)
    (hp : Function.Injective p) (j : Fin k) (hj : j.val + 1 < k) :
    Function.Injective (splitOrder p j hj) := by
  intro a b hab
  by_cases ha : a.val ≤ j.val
  · by_cases hb : b.val ≤ j.val
    · simp only [splitOrder, dite_eq_left ha, dite_eq_left hb] at hab
      have hv := congrArg Fin.val (hp (Option.some.inj hab))
      dsimp at hv
      apply Fin.ext
      omega
    · by_cases hb' : b.val = j.val + 1
      · simp only [splitOrder, dite_eq_left ha, dite_eq_right hb, dite_eq_left hb'] at hab
        cases hab
      · simp only [splitOrder, dite_eq_left ha, dite_eq_right hb, dite_eq_right hb'] at hab
        have hv := congrArg Fin.val (hp (Option.some.inj hab))
        dsimp at hv
        have hblt := b.isLt
        omega
  · by_cases ha' : a.val = j.val + 1
    · by_cases hb : b.val ≤ j.val
      · simp only [splitOrder, dite_eq_right ha, dite_eq_left ha', dite_eq_left hb] at hab
        cases hab
      · by_cases hb' : b.val = j.val + 1
        · apply Fin.ext
          omega
        · simp only [splitOrder, dite_eq_right ha, dite_eq_left ha', dite_eq_right hb,
            dite_eq_right hb'] at hab
          cases hab
    · by_cases hb : b.val ≤ j.val
      · simp only [splitOrder, dite_eq_right ha, dite_eq_right ha', dite_eq_left hb] at hab
        have hv := congrArg Fin.val (hp (Option.some.inj hab))
        dsimp at hv
        have halt := a.isLt
        omega
      · by_cases hb' : b.val = j.val + 1
        · simp only [splitOrder, dite_eq_right ha, dite_eq_right ha', dite_eq_right hb,
            dite_eq_left hb'] at hab
          cases hab
        · simp only [splitOrder, dite_eq_right ha, dite_eq_right ha', dite_eq_right hb,
            dite_eq_right hb'] at hab
          have hv := congrArg Fin.val (hp (Option.some.inj hab))
          dsimp at hv
          have halt := a.isLt
          have hblt := b.isLt
          apply Fin.ext
          omega

theorem splitOrder_zero {k : ℕ} (p : Fin k → Fin k)
    (j : Fin k) (hj : j.val + 1 < k) :
    splitOrder p j hj 0 = some (p j) := by
  simp [splitOrder]

theorem splitOrder_last {k : ℕ} (p : Fin k → Fin k)
    (j : Fin k) (hj : j.val + 1 < k) :
    splitOrder p j hj (Fin.last k) = some (p ⟨j.val + 1, hj⟩) := by
  have h1 : ¬ (Fin.last k).val ≤ j.val := by simp only [Fin.val_last]; omega
  have h2 : ¬ (Fin.last k).val = j.val + 1 := by simp only [Fin.val_last]; omega
  simp only [splitOrder, dite_eq_right h1, dite_eq_right h2]
  congr 2
  apply Fin.ext
  simp only [Fin.val_last]
  omega

/-- The split order uses the reversed prefix, the single apex, then the
reversed suffix. Every old edge avoids the unique removed added pair. -/
theorem splitOrder_path {k : ℕ} (G : SimpleGraph (Fin k))
    (u v : Fin k) (p : (pathGraph k).Copy (augment G u v))
    (j : Fin k) (hj : j.val + 1 < k)
    (hpair : s(p j, p ⟨j.val + 1, hj⟩) = s(u, v)) :
    ∀ a b : Fin (k + 1), a.val + 1 = b.val →
      (cone G).Adj (splitOrder p j hj a) (splitOrder p j hj b) := by
  have hnormal (a b : Fin k) (hab : (pathGraph k).Adj a b)
      (hne : s(a, b) ≠ s(j, ⟨j.val + 1, hj⟩)) : G.Adj (p a) (p b) := by
    have hm := p.toHom.map_adj hab
    change (G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Adj (p a) (p b) at hm
    rcases (SimpleGraph.sup_adj _ _ _ _).mp hm with h | h
    · exact h
    · have he := Set.mem_singleton_iff.mp ((SimpleGraph.fromEdgeSet_adj _).mp h).1
      rw [← hpair] at he
      apply False.elim
      apply hne
      rcases Sym2.eq_iff.mp he with h | h
      · exact Sym2.eq_iff.mpr (Or.inl ⟨p.injective h.1, p.injective h.2⟩)
      · exact Sym2.eq_iff.mpr (Or.inr ⟨p.injective h.1, p.injective h.2⟩)
  intro a b hab
  by_cases ha : a.val ≤ j.val
  · by_cases hb : b.val ≤ j.val
    · simp only [splitOrder, dite_eq_left ha, dite_eq_left hb, cone]
      apply hnormal
      · apply pathGraph_adj.mpr
        right
        dsimp
        omega
      · intro he
        rcases Sym2.eq_iff.mp he with h | h
        · have hv := congrArg Fin.val h.2
          dsimp at hv
          omega
        · have hv := congrArg Fin.val h.1
          dsimp at hv
          omega
    · have hb' : b.val = j.val + 1 := by omega
      simp only [splitOrder, dite_eq_left ha, dite_eq_right hb, dite_eq_left hb', cone]
  · by_cases ha' : a.val = j.val + 1
    · have hb : ¬ b.val ≤ j.val := by omega
      have hb' : ¬ b.val = j.val + 1 := by omega
      simp only [splitOrder, dite_eq_right ha, dite_eq_left ha', dite_eq_right hb,
        dite_eq_right hb', cone]
    · have hb : ¬ b.val ≤ j.val := by omega
      have hb' : ¬ b.val = j.val + 1 := by omega
      simp only [splitOrder, dite_eq_right ha, dite_eq_right ha', dite_eq_right hb,
        dite_eq_right hb', cone]
      apply hnormal
      · apply pathGraph_adj.mpr
        right
        dsimp
        have halt := a.isLt
        have hblt := b.isLt
        omega
      · intro he
        rcases Sym2.eq_iff.mp he with h | h
        · have hv := congrArg Fin.val h.1
          dsimp at hv
          have halt := a.isLt
          omega
        · have hv := congrArg Fin.val h.2
          dsimp at hv
          have hblt := b.isLt
          omega

/-- Spanning non-induced path augmentation at one missing unordered pair
forces the ordinary endpoint degree deficit. The literal pair premises are
retained; the Copy and Free hypotheses themselves force its actual use. -/
theorem degree_sum_le_of_spanning_path_augmentation {k : ℕ} (hk : 3 ≤ k)
    (G : SimpleGraph (Fin k)) (hfree : (pathGraph k).Free G)
    (u v : Fin k) (_huv : u ≠ v) (_hmissing : ¬ G.Adj u v)
    (hcopy : Nonempty ((pathGraph k).Copy (augment G u v))) :
    G.degree u + G.degree v ≤ k - 2 := by
  classical
  obtain ⟨p⟩ := hcopy
  obtain ⟨j, hj, hpair⟩ := added_pair_occurs G hfree u v p
  let q := splitOrder p j hj
  have hq : Function.Injective q := splitOrder_injective p p.injective j hj
  have hbij : Function.Bijective q :=
    (Fintype.bijective_iff_injective_and_card q).mpr ⟨hq, by simp⟩
  let e : Fin (k + 1) ≃ Option (Fin k) := Equiv.ofBijective q hbij
  let K : SimpleGraph (Fin (k + 1)) := (cone G).comap e
  have hKfree : (cycleGraph (k + 1)).Free K := by
    intro hc
    obtain ⟨f⟩ := hc
    exact cone_cycle_free_of_path_free G hfree
      ⟨(SimpleGraph.Iso.comap e (cone G)).toCopy.comp f⟩
  have hpath : ∀ a b : Fin (k + 1), a.val + 1 = b.val → K.Adj a b := by
    intro a b hab
    exact splitOrder_path G u v p j hj hpair a b hab
  have hbound := ErdosProblems.AntiRamseyCyclePathOre.path_endpoint_degree_sum_lt
    (by omega : 2 ≤ k) K hpath hKfree
  have hdeg0 := (SimpleGraph.Iso.comap e (cone G)).degree_eq (0 : Fin (k + 1))
  have hdeglast := (SimpleGraph.Iso.comap e (cone G)).degree_eq (Fin.last k)
  change (cone G).degree (q 0) = K.degree 0 at hdeg0
  change (cone G).degree (q (Fin.last k)) = K.degree (Fin.last k) at hdeglast
  rw [← hdeg0, ← hdeglast] at hbound
  change (cone G).degree (splitOrder p j hj 0) +
    (cone G).degree (splitOrder p j hj (Fin.last k)) < k + 1 at hbound
  rw [splitOrder_zero, splitOrder_last, cone_degree_some, cone_degree_some] at hbound
  have hpair' : (p j = u ∧ p ⟨j.val + 1, hj⟩ = v) ∨
      (p j = v ∧ p ⟨j.val + 1, hj⟩ = u) := Sym2.eq_iff.mp hpair
  have hD : G.degree (p j) + G.degree (p ⟨j.val + 1, hj⟩) ≤ k - 2 := by omega
  rcases hpair' with h | h
  · rw [h.1, h.2] at hD
    exact hD
  · rw [h.1, h.2] at hD
    simpa only [Nat.add_comm] using hD

end ErdosProblems.PathSpanningNonedgeDeficit
