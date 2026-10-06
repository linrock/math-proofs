module

public import PathUpperFilteredInteriorPalette
public import Mathlib.Data.Finset.Max

@[expose] public section

/-!
for ONE finite residual greedy stage. All choices retain the same original complete-host coloring and every original
color slot. No maximum, interior saturation, bridge or closure is assumed. The recursive existence of one final representative is outside this module.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- Exactly the original colors whose selected owner is inside this WHOLE
actual component; this is not the unfiltered host interior palette. -/
def residualSelectedComponentColors
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (x : Fin n) : Set (Fin q) :=
  {c | EdgeInside (componentSupport χ r x) (r.edge c).val}

theorem reachable_stays_in_of_adj_closed
    (G : SimpleGraph (Fin n)) (X : Set (Fin n))
    (hstep : ∀ a b, a ∈ X → G.Adj a b → b ∈ X)
    {a b : Fin n} (ha : a ∈ X) (hab : G.Reachable a b) : b ∈ X := by
  have hwalk : ∀ {u v : Fin n}, G.Walk u v → u ∈ X → v ∈ X := by
    intro u v p
    induction p with
    | nil => exact fun hu => hu
    | cons huv p ih =>
      intro hu
      exact ih (hstep _ _ hu huv)
  obtain ⟨p⟩ := hab
  exact hwalk p ha

theorem reachable_transfer_on_adj_closed
    (G H : SimpleGraph (Fin n)) (X : Set (Fin n))
    (hclosed : ∀ a b, a ∈ X → G.Adj a b → b ∈ X)
    (hstep : ∀ a b, a ∈ X → G.Adj a b → H.Adj a b)
    {a b : Fin n} (ha : a ∈ X) (hab : G.Reachable a b) :
    H.Reachable a b := by
  have hwalk : ∀ {u v : Fin n}, G.Walk u v → u ∈ X → H.Reachable u v := by
    intro u v p
    induction p with
    | nil =>
      intro _hu
      exact SimpleGraph.Reachable.refl _
    | cons huv p ih =>
      intro hu
      exact (hstep _ _ hu huv).reachable.trans (ih (hclosed _ _ hu huv))
  obtain ⟨p⟩ := hab
  exact hwalk p ha

/-- Admissible original full choices inherit the exact original boundary. -/
theorem residualSlotPartition_of_admissibleChoice
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (s : OriginalResidualChoice χ r U W) :
    ResidualSlotPartition χ s.choice U W := by
  refine ⟨?_, s.eligible_inside⟩
  intro c hc
  rw [s.prefix_eq c hc]
  exact hpartition.removed_outside c hc

/-- A whole actual component rooted in the remaining vertices stays there. -/
theorem componentSupport_subset_of_residualSlotPartition
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hx : x ∈ W) :
    componentSupport χ r x ⊆ W := by
  have hstep : ∀ a b, a ∈ W → (selectedGraph χ r).Adj a b → b ∈ W := by
    intro a b ha hab
    have hmem : s(a, b) ∈ (selectedGraph χ r).edgeSet := hab
    rw [selectedGraph_edgeSet χ r] at hmem
    obtain ⟨c, hc⟩ := hmem
    change (r.edge c).val = s(a, b) at hc
    have haOwner : a ∈ (r.edge c).val := by
      rw [hc]
      exact Sym2.mem_mk_left a b
    have hbOwner : b ∈ (r.edge c).val := by
      rw [hc]
      exact Sym2.mem_mk_right a b
    by_cases hremoved : c ∈ U
    · exact ((hpartition.removed_outside c hremoved a haOwner) ha).elim
    · exact hpartition.eligible_inside c hremoved b hbOwner
  intro v hv
  exact reachable_stays_in_of_adj_closed (selectedGraph χ r) W hstep hx
    ((mem_componentSupport χ r x v).mp hv)

/-- Two finite scalar maxima give the exact residual maximum, with an
ACTUAL admissible chosen full representative; no maximum is a premise. -/
theorem exists_residualLexMaximum
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W) (hW : W.Nonempty) :
    ∃ (s : OriginalResidualChoice χ r U W) (x : Fin n),
      x ∈ W ∧ ResidualLexMaximum χ s.choice U W x ∧
      ResidualSlotPartition χ s.choice U W := by
  classical
  let : Fintype (HostEdge n) :=
    SimpleGraph.fintypeEdgeSet (⊤ : SimpleGraph (Fin n))
  have hchoiceInj : Function.Injective (fun a : RepresentativeChoice χ => a.edge) := by
    intro a b hab
    cases a with
    | mk ae ap =>
      cases b with
      | mk be bp =>
        cases hab
        rfl
  have : Finite (RepresentativeChoice χ) := Finite.of_injective _ hchoiceInj
  have hadmissibleInj :
      Function.Injective (fun s : OriginalResidualChoice χ r U W => s.choice) := by
    intro a b hab
    cases a with
    | mk ac ap ae =>
      cases b with
      | mk bc bp be =>
        cases hab
        rfl
  have : Finite (OriginalResidualChoice χ r U W) :=
    Finite.of_injective _ hadmissibleInj
  let : Fintype (OriginalResidualChoice χ r U W × Fin n) := Fintype.ofFinite _
  let S : Finset (OriginalResidualChoice χ r U W × Fin n) :=
    Finset.univ.filter (fun p => p.2 ∈ W)
  let s₀ : OriginalResidualChoice χ r U W :=
    { choice := r
      prefix_eq := fun _ _ => rfl
      eligible_inside := hpartition.eligible_inside }
  obtain ⟨x₀, hx₀⟩ := hW
  have hS : S.Nonempty :=
    ⟨(s₀, x₀), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx₀⟩⟩
  obtain ⟨⟨sSize, xSize⟩, hsizeMem, hsizeMax⟩ :=
    Finset.exists_max_image S
      (fun p => (componentSupport χ p.1.choice p.2).ncard) hS
  let T : Finset (OriginalResidualChoice χ r U W × Fin n) :=
    S.filter (fun p => (componentSupport χ p.1.choice p.2).ncard =
      (componentSupport χ sSize.choice xSize).ncard)
  have hT : T.Nonempty :=
    ⟨(sSize, xSize), Finset.mem_filter.mpr ⟨hsizeMem, rfl⟩⟩
  obtain ⟨⟨s, x⟩, hsT, hedgeMax⟩ :=
    Finset.exists_max_image T
      (fun p => (internalSelectedEdges χ p.1.choice
        (componentSupport χ p.1.choice p.2)).card) hT
  have hsS : (s, x) ∈ S := (Finset.mem_filter.mp hsT).1
  have hx : x ∈ W := (Finset.mem_filter.mp hsS).2
  have hchosenSize : (componentSupport χ s.choice x).ncard =
      (componentSupport χ sSize.choice xSize).ncard := (Finset.mem_filter.mp hsT).2
  have hmax : ResidualLexMaximum χ s.choice U W x := by
    constructor
    · intro t z hz
      let tOld : OriginalResidualChoice χ r U W :=
        { choice := t.choice
          prefix_eq := fun c hc => (t.prefix_eq c hc).trans (s.prefix_eq c hc)
          eligible_inside := t.eligible_inside }
      have htS : (tOld, z) ∈ S :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
      change (componentSupport χ t.choice z).ncard ≤
        (componentSupport χ s.choice x).ncard
      rw [hchosenSize]
      exact hsizeMax (tOld, z) htS
    · intro t z hz hsize
      let tOld : OriginalResidualChoice χ r U W :=
        { choice := t.choice
          prefix_eq := fun c hc => (t.prefix_eq c hc).trans (s.prefix_eq c hc)
          eligible_inside := t.eligible_inside }
      have htT : (tOld, z) ∈ T := Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩,
          hsize.trans hchosenSize⟩
      exact hedgeMax (tOld, z) htT
  exact ⟨s, x, hx, hmax, residualSlotPartition_of_admissibleChoice
    χ r U W hpartition s⟩

theorem selected_owner_inside_component_of_endpoint
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (x : Fin n) (c : Fin q) (a : Fin n)
    (ha : a ∈ componentSupport χ r x) (haOwner : a ∈ (r.edge c).val) :
    EdgeInside (componentSupport χ r x) (r.edge c).val := by
  obtain ⟨⟨u, v⟩, hpair⟩ := Sym2.mk_surjective ((r.edge c).val)
  change s(u, v) = (r.edge c).val at hpair
  have hadj : (selectedGraph χ r).Adj u v := by
    have hmem : s(u, v) ∈ (selectedGraph χ r).edgeSet := by
      rw [selectedGraph_edgeSet χ r]
      exact ⟨c, hpair.symm⟩
    exact hmem
  have haPair : a = u ∨ a = v := Sym2.mem_iff.mp (by
    rw [hpair]
    exact haOwner)
  have hu : u ∈ componentSupport χ r x := by
    rcases haPair with hau | hav
    · exact hau ▸ ha
    · exact (mem_componentSupport χ r x u).mpr
        (((mem_componentSupport χ r x v).mp (hav ▸ ha)).trans hadj.symm.reachable)
  have hv : v ∈ componentSupport χ r x :=
    (mem_componentSupport χ r x v).mpr
      (((mem_componentSupport χ r x u).mp hu).trans hadj.reachable)
  intro w hw
  rw [← hpair] at hw
  rcases Sym2.mem_iff.mp hw with rfl | rfl
  · exact hu
  · exact hv

/-- Freezing WHOLE component owners preserves the next partition and its
literal graph for EVERY next admissible choice, including an empty palette. -/
theorem residual_component_freeze_invariants
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hx : x ∈ W) :
    let X := componentSupport χ r x
    let P := residualSelectedComponentColors χ r x
    X ⊆ W ∧ Disjoint P U ∧
    ResidualSlotPartition χ r (U ∪ P) (W \ X) ∧
    (W \ X).ncard < W.ncard ∧
    ∀ t : OriginalResidualChoice χ r (U ∪ P) (W \ X),
      (∃ old : OriginalResidualChoice χ r U W, old.choice = t.choice) ∧
      componentSupport χ t.choice x = X ∧
      (selectedGraph χ t.choice).induce X = (selectedGraph χ r).induce X ∧
      internalSelectedEdges χ t.choice X = internalSelectedEdges χ r X ∧
      ∀ c ∈ P, t.choice.edge c = r.edge c := by
  let X := componentSupport χ r x
  let P := residualSelectedComponentColors χ r x
  have hX : X ⊆ W :=
    componentSupport_subset_of_residualSlotPartition χ r U W hpartition x hx
  have hxX : x ∈ X := (mem_componentSupport χ r x x).mpr
    (SimpleGraph.Reachable.refl x)
  have hdisjoint : Disjoint P U := by
    apply Set.disjoint_left.mpr
    intro c hcP hcU
    obtain ⟨⟨a, b⟩, hpair⟩ := Sym2.mk_surjective ((r.edge c).val)
    have haOwner : a ∈ (r.edge c).val := by
      rw [← hpair]
      exact Sym2.mem_mk_left a b
    exact (hpartition.removed_outside c hcU a haOwner) (hX (hcP a haOwner))
  have hnext : ResidualSlotPartition χ r (U ∪ P) (W \ X) := by
    constructor
    · intro c hc v hv hvNext
      rcases hc with hcU | hcP
      · exact (hpartition.removed_outside c hcU v hv) hvNext.1
      · exact hvNext.2 (hcP v hv)
    · intro c hc v hv
      have hcU : c ∉ U := fun hcU => hc (Or.inl hcU)
      have hcP : c ∉ P := fun hcP => hc (Or.inr hcP)
      refine ⟨hpartition.eligible_inside c hcU v hv, ?_⟩
      intro hvX
      exact hcP (selected_owner_inside_component_of_endpoint χ r x c v hvX hv)
  have hdecrease : (W \ X).ncard < W.ncard := by
    have hsub : W \ X ⊆ W := fun _ hv => hv.1
    have hnot : x ∉ W \ X := fun hxNext => hxNext.2 hxX
    exact Set.ncard_lt_ncard (hsub.ssubset_of_mem_notMem hx hnot) (Set.toFinite W)
  refine ⟨hX, hdisjoint, hnext, hdecrease, ?_⟩
  intro t
  have hnested : ∃ old : OriginalResidualChoice χ r U W, old.choice = t.choice := by
    refine ⟨{ choice := t.choice
              prefix_eq := fun c hc => t.prefix_eq c (Or.inl hc)
              eligible_inside := ?_ }, rfl⟩
    intro c hc
    by_cases hcP : c ∈ P
    · rw [t.prefix_eq c (Or.inr hcP)]
      exact fun v hv => hX (hcP v hv)
    · have hcNext : c ∉ U ∪ P := by
        intro hcUnion
        rcases hcUnion with hcU | hcP'
        · exact hc hcU
        · exact hcP hcP'
      exact fun v hv => (t.eligible_inside c hcNext v hv).1
  have hslots : ∀ c ∈ P, t.choice.edge c = r.edge c :=
    fun c hc => t.prefix_eq c (Or.inr hc)
  have hlocal : ∀ a b, a ∈ X →
      ((selectedGraph χ t.choice).Adj a b ↔ (selectedGraph χ r).Adj a b) := by
    intro a b haX
    constructor
    · intro hab
      have hmem : s(a, b) ∈ (selectedGraph χ t.choice).edgeSet := hab
      rw [selectedGraph_edgeSet χ t.choice] at hmem
      obtain ⟨c, hc⟩ := hmem
      change (t.choice.edge c).val = s(a, b) at hc
      by_cases hfixed : c ∈ U ∪ P
      · have hval : (r.edge c).val = s(a, b) := by
          rw [← t.prefix_eq c hfixed]
          exact hc
        have hmemOld : s(a, b) ∈ (selectedGraph χ r).edgeSet := by
          rw [selectedGraph_edgeSet χ r]
          exact ⟨c, hval⟩
        exact hmemOld
      · have haOwner : a ∈ (t.choice.edge c).val := by
          rw [hc]
          exact Sym2.mem_mk_left a b
        exact ((t.eligible_inside c hfixed a haOwner).2 haX).elim
    · intro hab
      have hmem : s(a, b) ∈ (selectedGraph χ r).edgeSet := hab
      rw [selectedGraph_edgeSet χ r] at hmem
      obtain ⟨c, hc⟩ := hmem
      change (r.edge c).val = s(a, b) at hc
      have haOwner : a ∈ (r.edge c).val := by
        rw [hc]
        exact Sym2.mem_mk_left a b
      have hcP : c ∈ P :=
        selected_owner_inside_component_of_endpoint χ r x c a haX haOwner
      have hmemNew : s(a, b) ∈ (selectedGraph χ t.choice).edgeSet := by
        rw [selectedGraph_edgeSet χ t.choice]
        refine ⟨c, ?_⟩
        change (t.choice.edge c).val = s(a, b)
        rw [hslots c hcP]
        exact hc
      exact hmemNew
  have hclosedOld : ∀ a b, a ∈ X → (selectedGraph χ r).Adj a b → b ∈ X := by
    intro a b ha hab
    exact (mem_componentSupport χ r x b).mpr
      (((mem_componentSupport χ r x a).mp ha).trans hab.reachable)
  have hclosedNew : ∀ a b, a ∈ X →
      (selectedGraph χ t.choice).Adj a b → b ∈ X :=
    fun a b ha hab => hclosedOld a b ha ((hlocal a b ha).mp hab)
  have hsupport : componentSupport χ t.choice x = X := by
    ext v
    constructor
    · intro hv
      exact reachable_stays_in_of_adj_closed (selectedGraph χ t.choice) X
        hclosedNew hxX ((mem_componentSupport χ t.choice x v).mp hv)
    · intro hv
      apply (mem_componentSupport χ t.choice x v).mpr
      exact reachable_transfer_on_adj_closed (selectedGraph χ r)
        (selectedGraph χ t.choice) X hclosedOld
        (fun a b ha hab => (hlocal a b ha).mpr hab) hxX
        ((mem_componentSupport χ r x v).mp hv)
  have hgraph : (selectedGraph χ t.choice).induce X =
      (selectedGraph χ r).induce X := by
    ext a b
    exact hlocal a.val b.val a.property
  have hinternal : internalSelectedEdges χ t.choice X = internalSelectedEdges χ r X := by
    classical
    ext f
    obtain ⟨a, b⟩ := f
    rw [mem_internalSelectedEdges χ t.choice X s(a, b),
      mem_internalSelectedEdges χ r X s(a, b)]
    constructor
    · rintro ⟨hab, hinside⟩
      exact ⟨(hlocal a b (hinside a (Sym2.mem_mk_left a b))).mp hab, hinside⟩
    · rintro ⟨hab, hinside⟩
      exact ⟨(hlocal a b (hinside a (Sym2.mem_mk_left a b))).mpr hab, hinside⟩
  exact ⟨hnested, hsupport, hgraph, hinternal, hslots⟩

/-- ONE complete greedy stage for the original full-color residual family.
Every next admissible choice nests into the ORIGINAL input stage, while the
chosen whole component's literal graph/support/slots remain fixed. -/
theorem exists_residual_greedy_stage
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W) (hW : W.Nonempty) :
    ∃ (s : OriginalResidualChoice χ r U W) (x : Fin n),
      x ∈ W ∧ ResidualLexMaximum χ s.choice U W x ∧
      ResidualSlotPartition χ s.choice U W ∧
      let X := componentSupport χ s.choice x
      let P := residualSelectedComponentColors χ s.choice x
      X ⊆ W ∧ Disjoint P U ∧
      ResidualSlotPartition χ s.choice (U ∪ P) (W \ X) ∧
      (W \ X).ncard < W.ncard ∧
      ∀ t : OriginalResidualChoice χ s.choice (U ∪ P) (W \ X),
        (∃ old : OriginalResidualChoice χ r U W, old.choice = t.choice) ∧
        componentSupport χ t.choice x = X ∧
        (selectedGraph χ t.choice).induce X = (selectedGraph χ s.choice).induce X ∧
        internalSelectedEdges χ t.choice X = internalSelectedEdges χ s.choice X ∧
        ∀ c ∈ P, t.choice.edge c = s.choice.edge c := by
  obtain ⟨s, x, hx, hmax, hpartitionS⟩ :=
    exists_residualLexMaximum χ r U W hpartition hW
  obtain ⟨hX, hdisjoint, hnext, hdecrease, hforall⟩ :=
    residual_component_freeze_invariants χ s.choice U W hpartitionS x hx
  refine ⟨s, x, hx, hmax, hpartitionS, hX, hdisjoint, hnext, hdecrease, ?_⟩
  intro t
  obtain ⟨⟨old, hold⟩, hsupport, hgraph, hinternal, hslots⟩ := hforall t
  let originalOld : OriginalResidualChoice χ r U W :=
    { choice := old.choice
      prefix_eq := fun c hc => (old.prefix_eq c hc).trans (s.prefix_eq c hc)
      eligible_inside := old.eligible_inside }
  exact ⟨⟨originalOld, hold⟩, hsupport, hgraph, hinternal, hslots⟩

end ErdosProblems.PathUpperReduction
