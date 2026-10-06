module

public import CyclePathEndpointExtension
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-! first ordered extension for Choi Claim 2. The endpoint OR, original color and arbitrary NewChoice are preserved. The finite D is explicitly closed under selected adjacency. -/

namespace ErdosProblems.AntiRamseyCycleFirstPathExtension

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange

variable {n : ℕ} {C : Type*} [DecidableEq C]

theorem snoc_with_new_terminal
    {t : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (p : Fin (t + 1) → Fin n) (hp : Function.Injective p)
    (hstep : ∀ i : Fin t,
      (selectedGraph χ r).Adj (p (Fin.castSucc i)) (p (Fin.succ i)))
    (D : Finset (Fin n)) (hpD : ∀ i : Fin (t + 1), p i ∈ D)
    (w : Fin n) (hw : w ∉ Set.range p) (hwD : w ∈ D)
    (e : HostEdge n)
    (hadj : (selectedGraph χ r).Adj (p (Fin.last t)) w)
    (he : e.val = s(p (Fin.last t), w))
    (hnew : χ e ∈ newColors χ (p (Fin.last t))) :
    ∃ q : Fin (t + 2) → Fin n,
      ∃ hqpath : ∀ i : Fin (t + 1),
        (selectedGraph χ r).Adj (q (Fin.castSucc i)) (q (Fin.succ i)),
      Function.Injective q ∧
      (∀ i : Fin (t + 2), q i ∈ D) ∧
      restrictedColor χ r
        (⟨s(q (Fin.castSucc (Fin.last t)), q (Fin.succ (Fin.last t))),
          hqpath (Fin.last t)⟩ : (selectedGraph χ r).edgeSet) ∈
        newColors χ (q (Fin.castSucc (Fin.last t))) := by
  classical
  let q : Fin (t + 2) → Fin n := Fin.snoc p w
  have hq : Function.Injective q := Fin.snoc_injective_of_injective hp hw
  have hqD : ∀ i : Fin (t + 2), q i ∈ D := by
    intro i
    induction i using Fin.lastCases with
    | last => simpa only [q, Fin.snoc_last] using hwD
    | cast j => simpa only [q, Fin.snoc_castSucc] using hpD j
  have hqpath : ∀ i : Fin (t + 1),
      (selectedGraph χ r).Adj (q (Fin.castSucc i)) (q (Fin.succ i)) := by
    intro i
    induction i using Fin.lastCases with
    | last =>
      simpa only [q, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last] using hadj
    | cast j =>
      simpa only [q, Fin.succ_castSucc, Fin.snoc_castSucc] using hstep j
  have htailColor : restrictedColor χ r
      (⟨s(q (Fin.castSucc (Fin.last t)), q (Fin.succ (Fin.last t))),
        hqpath (Fin.last t)⟩ : (selectedGraph χ r).edgeSet) = χ e := by
    change χ ⟨s(q (Fin.castSucc (Fin.last t)), q (Fin.succ (Fin.last t))),
      SimpleGraph.edgeSet_mono
        (show selectedGraph χ r ≤ (⊤ : SimpleGraph (Fin n)) from le_top)
        (hqpath (Fin.last t))⟩ = χ e
    apply congrArg χ
    apply Subtype.ext
    simpa only [q, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last] using he.symm
  refine ⟨q, hqpath, hq, hqD, ?_⟩
  rw [htailColor]
  simpa only [q, Fin.snoc_castSucc] using hnew

/-- Reverse when the first endpoint is chosen, then append its outside NEW
neighbor. The literal witness edge is terminal and NEW at the inner endpoint.
The local cycle exclusion and endpoint pair bound are passed unchanged. -/
theorem exists_inward_new_ordered_path_extension
    {t : ℕ} (ht : 2 ≤ t)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (p : Fin (t + 1) → Fin n) (hp : Function.Injective p)
    (hpath : ∀ a b : Fin (t + 1), a.val + 1 = b.val →
      (selectedGraph χ r).Adj (p a) (p b))
    (D : Finset (Fin n)) (hpD : ∀ i : Fin (t + 1), p i ∈ D)
    (hnoD : ∀ f : (cycleGraph (t + 1)).Copy (selectedGraph χ r),
      ¬∀ i : Fin (t + 1), f i ∈ D)
    (hpair : t + 1 ≤
      (newColors χ (p 0)).card + (newColors χ (p (Fin.last t))).card)
    (hclosed : ∀ v : Fin n, v ∈ D → ∀ w : Fin n,
      (selectedGraph χ r).Adj v w → w ∈ D) :
    ∃ q : Fin (t + 2) → Fin n,
      ∃ hqpath : ∀ i : Fin (t + 1),
        (selectedGraph χ r).Adj (q (Fin.castSucc i)) (q (Fin.succ i)),
      Function.Injective q ∧
      (∀ i : Fin (t + 2), q i ∈ D) ∧
      restrictedColor χ r
        (⟨s(q (Fin.castSucc (Fin.last t)), q (Fin.succ (Fin.last t))),
          hqpath (Fin.last t)⟩ : (selectedGraph χ r).edgeSet) ∈
        newColors χ (q (Fin.castSucc (Fin.last t))) := by
  classical
  have hstep : ∀ i : Fin t,
      (selectedGraph χ r).Adj (p (Fin.castSucc i)) (p (Fin.succ i)) := by
    intro i
    exact hpath (Fin.castSucc i) (Fin.succ i) rfl
  rcases
    ErdosProblems.AntiRamseyCyclePathEndpointExtension.exists_endpoint_newColor_edge_outside_path
      ht χ r p hp hpath D hpD hnoD hpair with hleft | hright
  · obtain ⟨w, e, hwImage, hadj, he, hnew⟩ := hleft
    let b : Fin (t + 1) → Fin n := fun i => p i.rev
    have hb : Function.Injective b := hp.comp Fin.rev_injective
    have hbD : ∀ i : Fin (t + 1), b i ∈ D := by
      intro i
      exact hpD i.rev
    have hbstep : ∀ i : Fin t,
        (selectedGraph χ r).Adj (b (Fin.castSucc i)) (b (Fin.succ i)) := by
      intro i
      simpa only [b, Fin.rev_castSucc, Fin.rev_succ] using (hstep i.rev).symm
    have hwRange : w ∉ Set.range b := by
      rintro ⟨i, hi⟩
      exact hwImage (Finset.mem_image.mpr ⟨i.rev, Finset.mem_univ _, hi⟩)
    have hwD : w ∈ D := hclosed (p 0) (hpD 0) w hadj
    have hbAdj : (selectedGraph χ r).Adj (b (Fin.last t)) w := by
      simpa only [b, Fin.rev_last] using hadj
    have hbEdge : e.val = s(b (Fin.last t), w) := by
      simpa only [b, Fin.rev_last] using he
    have hbNew : χ e ∈ newColors χ (b (Fin.last t)) := by
      simpa only [b, Fin.rev_last] using hnew
    exact snoc_with_new_terminal χ r b hb hbstep D hbD w hwRange hwD e hbAdj hbEdge hbNew
  · obtain ⟨w, e, hwImage, hadj, he, hnew⟩ := hright
    have hwRange : w ∉ Set.range p := by
      rintro ⟨i, hi⟩
      exact hwImage (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
    have hwD : w ∈ D := hclosed (p (Fin.last t)) (hpD (Fin.last t)) w hadj
    exact snoc_with_new_terminal χ r p hp hstep D hpD w hwRange hwD e hadj he hnew

end ErdosProblems.AntiRamseyCycleFirstPathExtension
