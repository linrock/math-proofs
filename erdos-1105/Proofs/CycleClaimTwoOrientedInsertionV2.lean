module

public import CycleClaimOneFirstInsertion
public import CycleOrderedEdges
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
For Choi Claim 2's inward-oriented host insertion. The path and attachment belong to an arbitrary valid NEW choice. Only the
closing edge is a complete-host edge without selected membership. No witness rotation or component-order assertion is made here.
-/

namespace ErdosProblems.AntiRamseyCycleClaimTwoOrientedInsertion

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleOrderedEdges
open ErdosProblems.AntiRamseyCycleClaimOneFirstInsertion

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- The arbitrary-choice selected-plus-closing edge palette.
The two orientations are discharged in the concrete path theorem below. -/
def selectedPlusClosingColor {β : Type*}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (chain : β → (selectedGraph χ r).edgeSet)
    (closing : HostEdge n) : Option β → C
  | none => χ closing
  | some i => restrictedColor χ r (chain i)

theorem selectedPlusClosingColor_injective {β : Type*}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (chain : β → (selectedGraph χ r).edgeSet)
    (hchain : Function.Injective chain) (closing : HostEdge n)
    (hne : ∀ i, restrictedColor χ r (chain i) ≠ χ closing) :
    Function.Injective (selectedPlusClosingColor χ r chain closing) := by
  intro i j hij
  cases i with
  | none =>
      cases j with
      | none => rfl
      | some j => exact False.elim (hne j hij.symm)
  | some i =>
      cases j with
      | none => exact False.elim (hne i hij)
      | some j =>
          exact congrArg Option.some
            (hchain (restrictedColor_injective χ r hij))

/-- No induced-copy premise is used. -/
theorem ordered_selected_chain_closes_rainbow
    {t : ℕ} (hs : 2 ≤ t)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (p : Fin (t + 1) → Fin n) (hp : Function.Injective p)
    (chain : Fin t → (selectedGraph χ r).edgeSet)
    (hchain : ∀ i : Fin t,
      (chain i).val = s(p (Fin.castSucc i), p (Fin.succ i)))
    (closing : HostEdge n)
    (hclosing : closing.val = s(p 0, p (Fin.last t)))
    (hne : ∀ i, restrictedColor χ r (chain i) ≠ χ closing) :
    ∃ f : (cycleGraph (t + 1)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  let φ : (cycleGraph (t + 1)) →g (⊤ : SimpleGraph (Fin n)) :=
    ⟨p, by
      intro a b hab
      exact (top_adj _ _).mpr (hp.ne ((cycleGraph (t + 1)).ne_of_adj hab))⟩
  let f : (cycleGraph (t + 1)).Copy (⊤ : SimpleGraph (Fin n)) := ⟨φ, hp⟩
  have hchainInj : Function.Injective chain := by
    intro i j hij
    have hv := congrArg Subtype.val hij
    rw [hchain i, hchain j] at hv
    change Sym2.map p (sourceStep i).val =
      Sym2.map p (sourceStep j).val at hv
    have hsource : sourceStep i = sourceStep j :=
      Subtype.ext (Sym2.map.injective hp hv)
    exact sourceStep_injective hsource
  have hpalette :=
    selectedPlusClosingColor_injective χ r chain hchainInj closing hne
  have hstep (i : Fin t) :
      (EdgeLabeling.pullback χ f.toHom) (sourceStep i) =
        restrictedColor χ r (chain i) := by
    change χ (f.toHom.mapEdgeSet (sourceStep i)) =
      χ ⟨(chain i).val, SimpleGraph.edgeSet_mono le_top (chain i).property⟩
    apply congrArg χ
    apply Subtype.ext
    change Sym2.map p (sourceStep i).val = (chain i).val
    simp only [sourceStep, Sym2.map_mk, hchain]
  have hclose :
      (EdgeLabeling.pullback χ f.toHom) (sourceClosing t hs) =
        χ closing := by
    change χ (f.toHom.mapEdgeSet (sourceClosing t hs)) = χ closing
    apply congrArg χ
    apply Subtype.ext
    change Sym2.map p (sourceClosing t hs).val = closing.val
    simp only [sourceClosing, Sym2.map_mk, hclosing]
  refine ⟨f, ?_⟩
  intro e₁ e₂ heq
  rcases sourceEdge_cases hs e₁ with ⟨i, hi⟩ | hi <;>
    rcases sourceEdge_cases hs e₂ with ⟨j, hj⟩ | hj
  · subst e₁
    subst e₂
    have hsome : (some i : Option (Fin t)) = some j :=
      hpalette (by simpa only [selectedPlusClosingColor, hstep] using heq)
    have hij : i = j := by injection hsome with h
    subst j
    rfl
  · subst e₁
    subst e₂
    have hbad : (some i : Option (Fin t)) = none :=
      hpalette (by simpa only [selectedPlusClosingColor, hstep, hclose] using heq)
    cases hbad
  · subst e₁
    subst e₂
    have hbad : (none : Option (Fin t)) = some j :=
      hpalette (by simpa only [selectedPlusClosingColor, hstep, hclose] using heq)
    cases hbad
  · subst e₁
    subst e₂
    rfl

/-- Selected consecutive edge in an injectively ordered path. -/
noncomputable def selectedPathStep {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (p : Fin (m + 2) → Fin n)
    (hpath : ∀ i : Fin (m + 1),
      (selectedGraph χ r).Adj (p (Fin.castSucc i)) (p (Fin.succ i)))
    (i : Fin (m + 1)) : (selectedGraph χ r).edgeSet :=
  ⟨s(p (Fin.castSucc i), p (Fin.succ i)), hpath i⟩

/-- Positive host insertion with exactly the two inward NEW orientations.
There are m+2 selected path vertices and one outside vertex, hence a
literal host cycle on m+3 vertices. The bound m≥1 is the requested
k≥4 Claim 2 range. No color inequality is assumed in this statement. -/
theorem inward_oriented_path_insertion_rainbow
    {m : ℕ} (_hm : 1 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (p : Fin (m + 2) → Fin n) (hp : Function.Injective p)
    (hpath : ∀ i : Fin (m + 1),
      (selectedGraph χ r).Adj (p (Fin.castSucc i)) (p (Fin.succ i)))
    (u : Fin n) (hu : u ∉ Set.range p)
    (attachment : (selectedGraph χ r).edgeSet)
    (hattachment : attachment.val = s(u, p 0))
    (hnewFirst : restrictedColor χ r attachment ∈ newColors χ (p 0))
    (hnewLast : restrictedColor χ r
      (selectedPathStep χ r p hpath (Fin.last m)) ∈
      newColors χ (p (Fin.castSucc (Fin.last m)))) :
    ∃ f : (cycleGraph (m + 3)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  let q : Fin ((m + 2) + 1) → Fin n := Fin.cons u p
  have hq : Function.Injective q := Fin.cons_injective_of_injective hu hp
  let chain : Fin (m + 2) → (selectedGraph χ r).edgeSet :=
    Fin.cons attachment (selectedPathStep χ r p hpath)
  let closing : HostEdge n :=
    ⟨s(u, p (Fin.last (m + 1))), (top_adj _ _).mpr (by
      intro h
      exact hu ⟨Fin.last (m + 1), h.symm⟩)⟩
  have hchain : ∀ i : Fin (m + 2),
      (chain i).val = s(q (Fin.castSucc i), q (Fin.succ i)) := by
    intro i
    cases i using Fin.cases with
    | zero =>
        simpa only [chain, q, Fin.cons_zero, Fin.castSucc_zero,
          Fin.cons_succ] using hattachment
    | succ j =>
        simp only [chain, q, Fin.cons_succ, ← Fin.succ_castSucc,
          selectedPathStep]
  have hclosing : closing.val = s(q 0, q (Fin.last (m + 2))) := by
    simp only [closing, q, Fin.cons_zero, Fin.cons_last]
  have houtsideClosing (i : Fin (m + 2))
      (hi : i ≠ Fin.last (m + 1)) : p i ∉ closing.val := by
    intro hin
    change p i ∈ s(u, p (Fin.last (m + 1))) at hin
    rcases Sym2.mem_iff.mp hin with h | h
    · exact hu ⟨i, h⟩
    · exact hi (hp h)
  have hcastLastNe (i : Fin (m + 1)) :
      Fin.castSucc i ≠ Fin.last (m + 1) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_last] at hv
    have hil := i.isLt
    omega
  have hzeroNe : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at hv
    omega
  have hne : ∀ i, restrictedColor χ r (chain i) ≠ χ closing := by
    intro i
    cases i using Fin.cases with
    | zero =>
        change restrictedColor χ r attachment ≠ χ closing
        intro heq
        have hinc := newColor_every_edge_incident χ (p 0)
          hnewFirst closing heq.symm
        exact houtsideClosing 0 hzeroNe hinc
    | succ j =>
        change restrictedColor χ r (selectedPathStep χ r p hpath j) ≠ χ closing
        by_cases hj : j = Fin.last m
        · subst j
          intro heq
          have hinc := newColor_every_edge_incident χ
            (p (Fin.castSucc (Fin.last m))) hnewLast closing heq.symm
          exact houtsideClosing _ (hcastLastNe (Fin.last m)) hinc
        · have hsuccNe : Fin.succ j ≠ Fin.last (m + 1) := by
            intro h
            apply hj
            apply Fin.ext
            have hv := congrArg Fin.val h
            simp only [Fin.val_succ, Fin.val_last] at hv ⊢
            omega
          apply arbitrary_selected_edge_ne_disjoint_host_edge χ r
            (selectedPathStep χ r p hpath j) closing
          intro v hv
          change v ∈ s(p (Fin.castSucc j), p (Fin.succ j)) at hv
          rcases Sym2.mem_iff.mp hv with h | h
          · rw [h]
            exact houtsideClosing _ (hcastLastNe j)
          · rw [h]
            exact houtsideClosing _ hsuccNe
  exact ordered_selected_chain_closes_rainbow (t := m + 2) (by omega)
    χ r q hq chain hchain closing hclosing hne

/-- Literal no-rainbow host premise forbids that oriented selected configuration.
This does not select or rotate a path. -/
theorem no_inward_oriented_path_insertion
    {m : ℕ} (hm : 1 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (p : Fin (m + 2) → Fin n) (hp : Function.Injective p)
    (hpath : ∀ i : Fin (m + 1),
      (selectedGraph χ r).Adj (p (Fin.castSucc i)) (p (Fin.succ i)))
    (u : Fin n) (hu : u ∉ Set.range p)
    (attachment : (selectedGraph χ r).edgeSet)
    (hattachment : attachment.val = s(u, p 0))
    (hnewFirst : restrictedColor χ r attachment ∈ newColors χ (p 0))
    (hnewLast : restrictedColor χ r
      (selectedPathStep χ r p hpath (Fin.last m)) ∈
      newColors χ (p (Fin.castSucc (Fin.last m))))
    (hno : ∀ f : (cycleGraph (m + 3)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ) : False := by
  obtain ⟨f, hf⟩ := inward_oriented_path_insertion_rainbow hm χ r p hp
    hpath u hu attachment hattachment hnewFirst hnewLast
  exact hno f hf

end ErdosProblems.AntiRamseyCycleClaimTwoOrientedInsertion
