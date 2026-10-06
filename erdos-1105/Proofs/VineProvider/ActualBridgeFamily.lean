module

public import FamilyProvider.PathCutDetour
public import FamilyProvider.ComponentDetour
public import FamilyProvider.IntervalVine

@[expose] public section

/-! Actual finite labels contain no arbitrary walk or endpoint-choice parameter. -/
namespace ErdosProblems.PathUpperReduction.ActualBridgeFamily
open SimpleGraph ComponentDetour
variable {V : Type*} {G : SimpleGraph V} {s : ℕ}

def Chord (p : Fin (s + 1) → V) :=
  {ij : Fin (s + 1) × Fin (s + 1) // ij.1 < ij.2 ∧ G.Adj (p ij.1) (p ij.2)}

def Wide (p : Fin (s + 1) → V) :=
  {C : (G.induce (Set.range p)ᶜ).ConnectedComponent //
    ∃ i j : Fin (s + 1), i < j ∧ Attaches C (p i) ∧ Attaches C (p j)}

def Label (p : Fin (s + 1) → V) := Chord (G := G) p ⊕ Wide (G := G) p

def Data (p : Fin (s + 1) → V)
    (L R : Label (G := G) p → Fin (s + 1))
    (Q : ∀ l, G.Walk (p (L l)) (p (R l))) : Prop :=
      (∀ l, L l < R l) ∧
      (∀ l, (Q l).IsPath ∧ ∀ j, p j ∈ (Q l).support → j = L l ∨ j = R l) ∧
      (∀ c : Chord (G := G) p, L (.inl c) = c.val.1 ∧ R (.inl c) = c.val.2 ∧
        (Q (.inl c)).length = 1) ∧
      (∀ C : Wide (G := G) p, ∀ j, Attaches C.val (p j) →
        L (.inr C) ≤ j ∧ j ≤ R (.inr C)) ∧
      (∀ C : Wide (G := G) p, Attaches C.val (p (L (.inr C))) ∧
        Attaches C.val (p (R (.inr C))) ∧ 2 ≤ (Q (.inr C)).length ∧
        (∀ z, z ∈ (Q (.inr C)).support → z ≠ p (L (.inr C)) →
          z ≠ p (R (.inr C)) → z ∈ componentSupport C.val) ∧
        (∃ z, z ∈ (Q (.inr C)).support ∧ z ∈ componentSupport C.val)) ∧
      (∀ l r, R l < R r →
        Disjoint {z | z ∈ (Q l).support ∧ z ≠ p (L l) ∧ z ≠ p (R l)}
          {z | z ∈ (Q r).support ∧ z ≠ p (L r) ∧ z ≠ p (R r)})

/-- One fixed pair and actual walk for every actual chord/component label.
Strictly different right endpoints force disjoint ordinary internal supports. -/
theorem exists_bridge_data (p : Fin (s + 1) → V) (hp : Function.Injective p) :
    ∃ L R : Label (G := G) p → Fin (s + 1),
    ∃ Q : ∀ l, G.Walk (p (L l)) (p (R l)), Data p L R Q := by
  classical
  have hex := fun C : Wide (G := G) p =>
    exists_extreme_component_detour p hp C.val C.property
  choose LC RC hlt hAL hAR hbound QC hpath hlen hinside hcontact hnonempty using hex
  let L : Label (G := G) p → Fin (s + 1) := Sum.elim (fun c => c.val.1) LC
  let R : Label (G := G) p → Fin (s + 1) := Sum.elim (fun c => c.val.2) RC
  let Q : ∀ l : Label (G := G) p, G.Walk (p (L l)) (p (R l)) := fun l =>
    match l with
    | .inl c => Walk.cons c.property.2 Walk.nil
    | .inr C => QC C
  have hchord : ∀ c : Chord (G := G) p, ∀ z,
      z ∈ (Q (.inl c)).support → z = p c.val.1 ∨ z = p c.val.2 := by
    intro c z hz
    change z ∈ [p c.val.1, p c.val.2] at hz
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using hz
  have hempty : ∀ c : Chord (G := G) p,
      {z | z ∈ (Q (.inl c)).support ∧ z ≠ p (L (.inl c)) ∧
        z ≠ p (R (.inl c))} = ∅ := by
    intro c
    ext z
    constructor
    · rintro ⟨hz, hx, hy⟩
      rcases hchord c z hz with h | h
      · exact (hx h).elim
      · exact (hy h).elim
    · intro hz
      exact hz.elim
  refine ⟨L, R, Q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l
    cases l with
    | inl c => exact c.property.1
    | inr C => exact hlt C
  · intro l
    cases l with
    | inl c =>
      change (Walk.cons c.property.2 Walk.nil).IsPath ∧ _
      refine ⟨Walk.IsPath.nil.cons ?_, ?_⟩
      · simp only [Walk.support_nil, List.mem_singleton]
        exact fun h => (ne_of_lt c.property.1) (hp h)
      · intro j hj
        rcases hchord c (p j) hj with h | h
        · exact Or.inl (hp h)
        · exact Or.inr (hp h)
    | inr C => exact ⟨hpath C, hcontact C⟩
  · intro c
    exact ⟨rfl, rfl, rfl⟩
  · intro C j hj
    exact hbound C j hj
  · intro C
    exact ⟨hAL C, hAR C, hlen C, hinside C, hnonempty C⟩
  · intro l r hprogress
    cases l with
    | inl c => rw [hempty c]; exact Set.empty_disjoint _
    | inr C =>
      cases r with
      | inl c => rw [hempty c]; exact Set.disjoint_empty _
      | inr D =>
        have hCD : C.val ≠ D.val := by
          intro h
          have heq : C = D := Subtype.ext h
          subst D
          exact (lt_irrefl _ hprogress)
        exact internal_supports_disjoint hCD (QC C) (QC D) (hinside C) (hinside D)

/-- Every internal deletion cut is covered by the actual finite image family.
No boundary chord or consecutive-order adjacency is assumed in this theorem. -/
theorem exists_cut_covered_family [Finite V] (p : Fin (s + 1) → V)
    (hp : Function.Injective p)
    (hdel : ∀ i : Fin (s + 1), 0 < i → i < Fin.last s →
      (G.induce {w | w ≠ p i}).Connected) :
    ∃ L R : Label (G := G) p → Fin (s + 1),
    ∃ Q : ∀ l, G.Walk (p (L l)) (p (R l)), Data p L R Q ∧
    ∃ F : Finset IntervalVine.Interval,
      (∀ I, I ∈ F ↔ ∃ l, ((L l).val, (R l).val) = I) ∧
      IntervalVine.Valid F s ∧ IntervalVine.Cuts F s := by
  classical
  obtain ⟨L, R, Q, hd⟩ := exists_bridge_data (G := G) p hp
  rcases hd with ⟨hlt, hpath, hchord, hextreme, hinside, hdisjoint⟩
  have : Finite (Label (G := G) p) := by
    dsimp [Label, Chord, Wide]
    infer_instance
  let : Fintype (Label (G := G) p) := Fintype.ofFinite _
  let F : Finset IntervalVine.Interval :=
    Finset.univ.image (fun l => ((L l).val, (R l).val))
  have hmem : ∀ I, I ∈ F ↔ ∃ l, ((L l).val, (R l).val) = I := by
    intro I
    simp only [F, Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨L, R, Q, ⟨hlt, hpath, hchord, hextreme, hinside, hdisjoint⟩,
    F, hmem, ?_, ?_⟩
  · intro I hI
    obtain ⟨l, rfl⟩ := (hmem I).mp hI
    exact ⟨hlt l, Nat.le_of_lt_succ (R l).isLt⟩
  · intro c hc0 hcs
    let i : Fin (s + 1) := ⟨c, by omega⟩
    have hi0 : (0 : Fin (s + 1)) < i := hc0
    have his : i < Fin.last s := hcs
    obtain ⟨a, b, hai, hib, q, hq, _havoid, _hcontacts, hcontact⟩ :=
      exists_internal_cut_detour p hp i hi0 his (hdel i hi0 his)
    have hab : a < b := lt_trans hai hib
    have hpa : p a ∈ Set.range p := ⟨a, rfl⟩
    have hpb : p b ∈ Set.range p := ⟨b, rfl⟩
    have hpab : p a ≠ p b := fun h => (ne_of_lt hab) (hp h)
    rcases path_is_chord_or_component q hpa hpb hpab hq hcontact with hadj | hcomponent
    · let l : Label (G := G) p := .inl ⟨(a, b), hab, hadj⟩
      have hleft : L l = a := (hchord ⟨(a, b), hab, hadj⟩).1
      have hright : R l = b := (hchord ⟨(a, b), hab, hadj⟩).2.1
      refine ⟨((L l).val, (R l).val), (hmem _).mpr ⟨l, rfl⟩, ?_, ?_⟩
      · rw [hleft]
        exact hai
      · rw [hright]
        exact hib
    · obtain ⟨C, hCa, hCb⟩ := hcomponent
      let D : Wide (G := G) p := ⟨C, a, b, hab, hCa, hCb⟩
      let l : Label (G := G) p := .inr D
      have hLa : L l ≤ a := (hextreme D a hCa).1
      have hbR : b ≤ R l := (hextreme D b hCb).2
      refine ⟨((L l).val, (R l).val), (hmem _).mpr ⟨l, rfl⟩, ?_, ?_⟩
      · exact lt_of_le_of_lt hLa hai
      · exact lt_of_lt_of_le hib hbR

/-- Construct the actual labelled vine from deletion connectivity and two actual
boundary edges. Image duplicates do not require interval-map injectivity. -/
theorem exists_actual_interval_vine [Finite V] (p : Fin (s + 1) → V)
    (hp : Function.Injective p) (hs : 2 ≤ s)
    (hdel : ∀ i : Fin (s + 1), 0 < i → i < Fin.last s →
      (G.induce {w | w ≠ p i}).Connected)
    (a b : Fin (s + 1)) (ha : 0 < a) (hb : b < Fin.last s)
    (hfirstEdge : G.Adj (p 0) (p a)) (hlastEdge : G.Adj (p b) (p (Fin.last s))) :
    ∃ L R : Label (G := G) p → Fin (s + 1),
    ∃ Q : ∀ l, G.Walk (p (L l)) (p (R l)), Data p L R Q ∧
    ∃ F : Finset IntervalVine.Interval, ∃ first rest, ∃ labels : List (Label (G := G) p),
      (∀ I, I ∈ F ↔ ∃ l, ((L l).val, (R l).val) = I) ∧
      IntervalVine.Valid F s ∧ IntervalVine.Cuts F s ∧
      first ∈ F ∧ first.1 = 0 ∧ a.val ≤ first.2 ∧
      (∀ I ∈ F, I.1 = 0 → I.2 ≤ first.2) ∧
      IntervalVine.GreedyTail F s 1 first.2 rest ∧
      labels.map (fun l => ((L l).val, (R l).val)) = first :: rest ∧
      labels ≠ [] ∧ labels.Pairwise (fun l r => R l < R r) ∧
      labels.Pairwise (fun l r =>
        Disjoint {z | z ∈ (Q l).support ∧ z ≠ p (L l) ∧ z ≠ p (R l)}
          {z | z ∈ (Q r).support ∧ z ≠ p (L r) ∧ z ≠ p (R r)}) ∧
      IntervalVine.endRight 0 (labels.map (fun l => ((L l).val, (R l).val))) = s ∧
      labels.length ≤ s ∧ (∀ l ∈ labels, (R l).val = s → (L l).val ≤ b.val) := by
  classical
  obtain ⟨L, R, Q, hd, F, hmem, hvalid, hcuts⟩ :=
    exists_cut_covered_family (G := G) p hp hdel
  have hchord := hd.2.2.1
  have hfirst : (0, a.val) ∈ F := by
    let c : Chord (G := G) p := ⟨(0, a), ha, hfirstEdge⟩
    apply (hmem _).mpr
    refine ⟨.inl c, ?_⟩
    rw [(hchord c).1, (hchord c).2.1]
    rfl
  have hlast : (b.val, s) ∈ F := by
    let c : Chord (G := G) p := ⟨(b, Fin.last s), hb, hlastEdge⟩
    apply (hmem _).mpr
    refine ⟨.inl c, ?_⟩
    rw [(hchord c).1, (hchord c).2.1]
    rfl
  obtain ⟨first, rest, hfirstF, hzero, hreach, hmax, htail, hstrict,
    hend, hlength, hselected, hterminal⟩ :=
    IntervalVine.exists_interval_vine F s a.val b.val hs hvalid hcuts hfirst hlast
  have hpre : ∀ I : {I : IntervalVine.Interval // I ∈ F},
      ∃ l : Label (G := G) p, ((L l).val, (R l).val) = I.val := by
    intro I
    exact (hmem I.val).mp I.property
  choose select hselect using hpre
  let seq := first :: rest
  let lift : {I : IntervalVine.Interval // I ∈ seq} → Label (G := G) p :=
    fun I => select ⟨I.val, hselected I.val I.property⟩
  let labels := seq.attach.map lift
  have hmap : labels.map (fun l => ((L l).val, (R l).val)) = seq := by
    change (seq.attach.map lift).map _ = seq
    rw [List.map_map]
    calc
      _ = seq.attach.map Subtype.val := by
        apply List.map_congr_left
        intro I _hI
        exact hselect ⟨I.val, hselected I.val I.property⟩
      _ = seq := List.attach_map_subtype_val seq
  have hlabelstrict : labels.Pairwise (fun l r => R l < R r) := by
    have h := hstrict
    change seq.Pairwise (fun p q => p.2 < q.2) at h
    rw [← hmap, List.pairwise_map] at h
    exact h
  have hnonempty : labels ≠ [] := by
    intro hnil
    simp [hnil, seq] at hmap
  refine ⟨L, R, Q, hd, F, first, rest, labels, hmem, hvalid, hcuts,
    hfirstF, hzero, hreach, hmax, htail, hmap, hnonempty, hlabelstrict,
    hlabelstrict.imp (fun {l r} h => hd.2.2.2.2.2 l r h), ?_, ?_, ?_⟩
  · rw [hmap]
    exact hend
  · have hlen : (labels.map (fun l => ((L l).val, (R l).val))).length = labels.length :=
      List.length_map _
    rw [hmap] at hlen
    rw [← hlen]
    exact hlength
  · intro l hl hRl
    have hin : ((L l).val, (R l).val) ∈ seq := by
      rw [← hmap]
      exact List.mem_map.mpr ⟨l, hl, rfl⟩
    exact hterminal _ hin hRl

end ErdosProblems.PathUpperReduction.ActualBridgeFamily
