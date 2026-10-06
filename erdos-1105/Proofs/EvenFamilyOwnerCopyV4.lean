module

public import SaturatedEvenHOrderV8
public import EvenExceptionOrdinaryCopyV3
public import EvenOwnerBEmbedding

@[expose] public section

/-! Uniform ordinary actual-owner exceptional-family copy. This does not classify arbitrary representatives or prove a numeric upper. -/
namespace ErdosProblems.EvenExceptionExchange
open SimpleGraph

def aPlacement (a : ℕ) : Fin (a + 1 - 1) ↪ Fin a where
  toFun i := ⟨i.val, by
    have hpred : a + 1 - 1 = a := by omega
    simpa only [hpred] using i.isLt⟩
  inj' := by
    intro i j h
    apply Fin.ext
    exact congrArg Fin.val h

def motifPlacement {a b : ℕ} (f : Fin (a + 1) ↪ Fin b) :
    ErdosProblems.SaturatedEvenH.MotifVertex (a + 1) ↪ Vertex a b :=
  Function.Embedding.sumMap (aPlacement a)
    (Function.Embedding.sumMap (Function.Embedding.refl (Fin 3)) f)

theorem placement_adj_iff {a b : ℕ} (f : Fin (a + 1) ↪ Fin b)
    (x y : ErdosProblems.SaturatedEvenH.MotifVertex (a + 1)) :
    (familyGraph a b).Adj (motifPlacement f x) (motifPlacement f y) ↔
      (ErdosProblems.SaturatedEvenH.motifGraph (a + 1)).Adj x y := by
  constructor
  · intro h
    refine ⟨fun heq => h.1 (congrArg (motifPlacement f) heq), ?_⟩
    rcases x with ax | (cx | bx) <;> rcases y with ay | (cy | by')
    all_goals exact h.2
  · intro h
    refine ⟨(motifPlacement f).injective.ne h.1, ?_⟩
    rcases x with ax | (cx | bx) <;> rcases y with ay | (cy | by')
    all_goals exact h.2

theorem placement_preimage {a b : ℕ} (f : Fin (a + 1) ↪ Fin b)
    (x : Vertex a b)
    (hB : ∀ z : Fin b, x = Sum.inr (Sum.inr z) → z ∈ Set.range f) :
    ∃ x0 : ErdosProblems.SaturatedEvenH.MotifVertex (a + 1),
      motifPlacement f x0 = x := by
  rcases x with i | (c | z)
  · let j : Fin (a + 1 - 1) := ⟨i.val, by
      have hpred : a + 1 - 1 = a := by omega
      simpa only [hpred] using i.isLt⟩
    refine ⟨Sum.inl j, ?_⟩
    change Sum.inl (aPlacement a j) = Sum.inl i
    apply congrArg Sum.inl
    apply Fin.ext
    rfl
  · exact ⟨Sum.inr (Sum.inl c), rfl⟩
  · obtain ⟨j,hj⟩ := hB z rfl
    refine ⟨Sum.inr (Sum.inr j), ?_⟩
    change Sum.inr (Sum.inr (f j)) = Sum.inr (Sum.inr z)
    rw [hj]

/-- On the actual full exceptional family, any one actual old owner can be
deleted and any prescribed distinct B pair inserted, yielding ordinary P_(2a+4).
The owner is pulled back through an injective placement, never assumed favorable. -/
noncomputable def path_copy_after_actual_owner_exchange
    (a b : ℕ) (ha : 2 ≤ a) (hab : a + 1 ≤ b)
    (owner : (familyGraph a b).edgeSet) (u v : Fin b) (huv : u ≠ v) :
    (pathGraph (2 * a + 4)).Copy
      ((familyGraph a b).deleteEdges {owner.val} ⊔
        SimpleGraph.fromEdgeSet
          {s((Sum.inr (Sum.inr u) : Vertex a b), Sum.inr (Sum.inr v))}) := by
  classical
  apply Classical.choice
  obtain ⟨e,he⟩ := owner
  induction e using Sym2.inductionOn with
  | _ x y =>
    have hxy : (familyGraph a b).Adj x y := (SimpleGraph.mem_edgeSet _).mp he
    let w : Fin b := match x, y with
      | Sum.inr (Sum.inr z), _ => z
      | _, Sum.inr (Sum.inr z) => z
      | _, _ => u
    obtain ⟨f,hf0,hf1,hw,_⟩ :=
      exists_b_embedding_with_owner a b ha hab u v w huv
    have hxB : ∀ z : Fin b, x = Sum.inr (Sum.inr z) → z ∈ Set.range f := by
      intro z hz
      subst x
      simpa only [w] using hw
    have hyB : ∀ z : Fin b, y = Sum.inr (Sum.inr z) → z ∈ Set.range f := by
      intro z hz
      subst y
      rcases x with ax | (cx | bx)
      · simpa only [w] using hw
      · simpa only [w] using hw
      · rcases hxy.2 with hA | hA | ⟨hC,hC'⟩
        · cases hA
        · cases hA
        · cases hC
    obtain ⟨x0,hx0⟩ := placement_preimage f x hxB
    obtain ⟨y0,hy0⟩ := placement_preimage f y hyB
    have h0 : (ErdosProblems.SaturatedEvenH.motifGraph (a + 1)).Adj x0 y0 := by
      apply (placement_adj_iff f x0 y0).mp
      rw [hx0,hy0]
      exact hxy
    let owner0 : (ErdosProblems.SaturatedEvenH.motifGraph (a + 1)).edgeSet :=
      ⟨s(x0,y0), (SimpleGraph.mem_edgeSet _).mpr h0⟩
    have howner : Sym2.map (motifPlacement f) owner0.val = s(x,y) := by
      change s(motifPlacement f x0, motifPlacement f y0) = s(x,y)
      rw [hx0,hy0]
    let hell : 2 ≤ a + 1 := by omega
    have horder : ∃ p : Fin (2 * a + 4) →
          ErdosProblems.SaturatedEvenH.MotifVertex (a + 1),
        Function.Injective p ∧
        ∀ i : Fin (2 * a + 3),
          s(p (Fin.castSucc i),p (Fin.succ i)) =
            ErdosProblems.SaturatedEvenH.chord hell ∨
          ((ErdosProblems.SaturatedEvenH.motifGraph (a + 1)).Adj
            (p (Fin.castSucc i)) (p (Fin.succ i)) ∧
            s(p (Fin.castSucc i),p (Fin.succ i)) ≠ owner0.val) := by
      have hraw := ErdosProblems.SaturatedEvenH.saturated_even_h_avoid_edge hell owner0
      have hmul : 2 * (a + 1) = 2 * a + 2 := by omega
      rw [hmul] at hraw
      exact hraw
    obtain ⟨p,hp,havoid⟩ := horder
    let q : Fin (2 * a + 4) → Vertex a b := motifPlacement f ∘ p
    have hq : Function.Injective q := (motifPlacement f).injective.comp hp
    have hchord : Sym2.map (motifPlacement f)
        (ErdosProblems.SaturatedEvenH.chord hell) =
          s((Sum.inr (Sum.inr u) : Vertex a b), Sum.inr (Sum.inr v)) := by
      change s((Sum.inr (Sum.inr (f (ErdosProblems.SaturatedEvenH.bZero hell))) :
          Vertex a b),
        Sum.inr (Sum.inr (f (ErdosProblems.SaturatedEvenH.bOne hell)))) =
          s(Sum.inr (Sum.inr u),Sum.inr (Sum.inr v))
      have hf0' : f (ErdosProblems.SaturatedEvenH.bZero hell) = u := hf0
      have hf1' : f (ErdosProblems.SaturatedEvenH.bOne hell) = v := hf1
      rw [hf0',hf1']
    have hqavoid : ∀ i : Fin (2 * a + 3),
        s(q (Fin.castSucc i),q (Fin.succ i)) =
          s((Sum.inr (Sum.inr u) : Vertex a b), Sum.inr (Sum.inr v)) ∨
        ((familyGraph a b).Adj (q (Fin.castSucc i)) (q (Fin.succ i)) ∧
          s(q (Fin.castSucc i),q (Fin.succ i)) ≠ s(x,y)) := by
      intro i
      rcases havoid i with hnew | ⟨hold,hne⟩
      · left
        change Sym2.map (motifPlacement f)
          s(p (Fin.castSucc i),p (Fin.succ i)) =
            s(Sum.inr (Sum.inr u),Sum.inr (Sum.inr v))
        rw [hnew]
        exact hchord
      · right
        refine ⟨(placement_adj_iff f _ _).mpr hold, ?_⟩
        intro heq
        apply hne
        apply Sym2.map.injective (motifPlacement f).injective
        change s(q (Fin.castSucc i),q (Fin.succ i)) =
          Sym2.map (motifPlacement f) owner0.val
        rw [howner]
        exact heq
    exact ⟨copy_of_avoiding_order (familyGraph a b) ⟨s(x,y),he⟩
      (Sum.inr (Sum.inr u)) (Sum.inr (Sum.inr v)) q hq hqavoid⟩

end ErdosProblems.EvenExceptionExchange
