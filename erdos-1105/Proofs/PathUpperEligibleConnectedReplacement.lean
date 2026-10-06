module

public import PathUpperEligibleOutgoingCommonBridge

@[expose] public section

/-!
All color values and `χ` are original; the entire inside palette excludes `U`,
and initial-slot deletions and current connectedness are retained.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- A same-original-color interior replacement retains the deletion of the
current induced nonbridge and supplies a connected next interior choice. -/
theorem exists_connected_eligible_interior_choice_of_nonbridge_replace
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q))
    (r : RepresentativeChoice χ) (X : Set (Fin n))
    (s : EligibleInteriorRepresentativeChoice χ U X)
    (hconn : ((eligibleInteriorSelectedGraph χ U X s).induce X).Connected)
    (f : HostEdge n) (hf : EdgeInside X f.val)
    (hc : χ f ∈ eligibleInteriorColors χ U X)
    (a b : X) (hold : (s.edge ⟨χ f, hc⟩).val = s(a.val, b.val))
    (hnb : ¬ ((eligibleInteriorSelectedGraph χ U X s).induce X).IsBridge s(a, b)) :
    ∃ t : EligibleInteriorRepresentativeChoice χ U X,
      t.edge ⟨χ f, hc⟩ = f ∧
      (∀ c : {c : Fin q // c ∈ eligibleInteriorColors χ U X},
        c.val ≠ χ f → t.edge c = s.edge c) ∧
      ((eligibleInteriorSelectedGraph χ U X s).induce X).deleteEdges {s(a, b)} ≤
        (eligibleInteriorSelectedGraph χ U X t).induce X ∧
      ((eligibleInteriorSelectedGraph χ U X t).induce X).Connected := by
  classical
  let F : RepresentativeChoice χ := (s.extend r).replace f
  have hsame : F.edge (χ f) = f := (s.extend r).replace_edge_same f
  have hother : ∀ c : {c : Fin q // c ∈ eligibleInteriorColors χ U X},
      c.val ≠ χ f → F.edge c.val = s.edge c := by
    intro c hne
    change ((s.extend r).replace f).edge c.val = s.edge c
    rw [(s.extend r).replace_edge_other f hne]
    exact s.extend_edge_eligible r c
  let t : EligibleInteriorRepresentativeChoice χ U X :=
    { edge := fun c => F.edge c.val
      color_eq := fun c => F.color_eq c.val
      inside := by
        intro c
        by_cases he : c.val = χ f
        · rw [he, hsame]
          exact hf
        · rw [hother c he]
          exact s.inside c }
  have hle : ((eligibleInteriorSelectedGraph χ U X s).induce X).deleteEdges {s(a, b)} ≤
      (eligibleInteriorSelectedGraph χ U X t).induce X := by
    intro z w hzw
    have hcurrent : (eligibleInteriorSelectedGraph χ U X s).Adj z.val w.val :=
      (SimpleGraph.deleteEdges_adj.mp hzw).1
    have hdeleted : s(z, w) ≠ s(a, b) := by
      simpa using (SimpleGraph.deleteEdges_adj.mp hzw).2
    change s(z.val, w.val) ∈ Set.range
      (fun c : {c : Fin q // c ∈ eligibleInteriorColors χ U X} => (s.edge c).val) ∧
      z.val ≠ w.val at hcurrent
    obtain ⟨c, hedge⟩ := hcurrent.1
    change (s.edge c).val = s(z.val, w.val) at hedge
    have hne : c.val ≠ χ f := by
      intro he
      have hcEq : c = ⟨χ f, hc⟩ := Subtype.ext he
      apply hdeleted
      apply Sym2.map.injective (f := fun x : X => x.val) Subtype.val_injective
      change s(z.val, w.val) = s(a.val, b.val)
      calc
        s(z.val, w.val) = (s.edge c).val := hedge.symm
        _ = (s.edge ⟨χ f, hc⟩).val := by rw [hcEq]
        _ = s(a.val, b.val) := hold
    change s(z.val, w.val) ∈ Set.range
      (fun c : {c : Fin q // c ∈ eligibleInteriorColors χ U X} => (t.edge c).val) ∧
      z.val ≠ w.val
    refine ⟨⟨c, ?_⟩, hcurrent.2⟩
    change (F.edge c.val).val = s(z.val, w.val)
    rw [hother c hne]
    exact hedge
  have hdelete :
      (((eligibleInteriorSelectedGraph χ U X s).induce X).deleteEdges {s(a, b)}).Connected :=
    SimpleGraph.Preconnected.connected_deleteEdges_of_not_isBridge hconn.preconnected hnb
  refine ⟨t, ?_, ?_, hle, SimpleGraph.Connected.mono hle hdelete⟩
  · exact hsame
  · intro c hne
    exact hother c hne

/-- ALL eligible choices keep EVERY removed original prefix slot unchanged.
This is available before any current-graph or residual maximum use. -/
theorem EligibleInteriorRepresentativeChoice.extend_prefix_eq
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {U : Set (Fin q)} {X : Set (Fin n)}
    (s : EligibleInteriorRepresentativeChoice χ U X) (r : RepresentativeChoice χ)
    (c : Fin q) (hc : c ∈ U) :
    (s.extend r).edge c = r.edge c := by
  have hnot : c ∉ eligibleInteriorColors χ U X := by
    intro hmem
    exact ((mem_eligibleInteriorColors χ U X c).mp hmem).1 hc
  exact s.extend_edge_noneligible r hnot

end ErdosProblems.PathUpperReduction
