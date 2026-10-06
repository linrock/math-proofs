module

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
This is a path-cover concatenation proof candidate,
not the last-block classification. The carrier is SAME Fin (2*d+3). The core has size d+3. Actual outsider paths belong to ORIGINAL G; only the
attachment edges are required in the augmented graph F. A cover is supplied
as actual nonempty disjoint path lists, not as a cycle or favorable placement. Distinct anchors, their order, unused-core order and the spanning cycle are
constructed internally.
-/

namespace ErdosProblems.PathUpperReduction.EvenLastBlockRigidity1105

open SimpleGraph

/-- Interleave one anchor before each covering path, retaining the last anchor.
The length guard used by the lemmas is anchors.length = paths.length + 1. -/
def stitch {V : Type*} : List V → List (List V) → List V
  | [], _ => []
  | a :: as, [] => a :: as
  | a :: as, p :: ps => a :: (p ++ stitch as ps)

theorem stitch_head? {V : Type*} (as : List V) (ps : List (List V)) :
    (stitch as ps).head? = as.head? := by
  cases as <;> cases ps <;> rfl

theorem stitch_ne_nil {V : Type*} (as : List V) (ps : List (List V))
    (hlen : as.length = ps.length + 1) : stitch as ps ≠ [] := by
  cases as with
  | nil => simp only [List.length_nil] at hlen; omega
  | cons a as => cases ps <;> simp [stitch]

theorem stitch_mem {V : Type*} (as : List V) (ps : List (List V))
    (hlen : as.length = ps.length + 1) (z : V) :
    z ∈ stitch as ps ↔ z ∈ as ∨ z ∈ ps.flatten := by
  induction ps generalizing as z with
  | nil => cases as <;> simp [stitch]
  | cons p ps ih =>
    cases as with
    | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons a as =>
      have hrest : as.length = ps.length + 1 := by
        simp only [List.length_cons] at hlen
        omega
      simp only [stitch, List.mem_cons, List.mem_append, List.flatten_cons,
        ih (as := as) (z := z) hrest]
      aesop

theorem stitch_getLast? {V : Type*} (as : List V) (ps : List (List V))
    (hlen : as.length = ps.length + 1) :
    (stitch as ps).getLast? = as.getLast? := by
  induction ps generalizing as with
  | nil => cases as <;> rfl
  | cons p ps ih =>
    cases as with
    | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons a as =>
      have hrest : as.length = ps.length + 1 := by
        simp only [List.length_cons] at hlen
        omega
      cases as with
      | nil => simp only [List.length_nil] at hrest; omega
      | cons b bs =>
        have htail : stitch (b :: bs) ps ≠ [] := stitch_ne_nil _ _ hrest
        calc
          (stitch (a :: b :: bs) (p :: ps)).getLast? =
              (stitch (b :: bs) ps).getLast? := by
            change ((a :: p) ++ stitch (b :: bs) ps).getLast? = _
            exact List.getLast?_append_of_ne_nil _ htail
          _ = (b :: bs).getLast? := ih _ hrest
          _ = (a :: b :: bs).getLast? := by rw [List.getLast?_cons_cons]

theorem stitch_nodup {V : Type*} (as : List V) (ps : List (List V))
    (hlen : as.length = ps.length + 1) (ha : as.Nodup)
    (hp : ps.flatten.Nodup)
    (hsep : ∀ z, z ∈ as → z ∈ ps.flatten → False) :
    (stitch as ps).Nodup := by
  induction ps generalizing as with
  | nil => cases as <;> simpa only [stitch] using ha
  | cons p ps ih =>
    cases as with
    | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons a as =>
      have hrest : as.length = ps.length + 1 := by
        simp only [List.length_cons] at hlen
        omega
      rcases List.nodup_cons.mp ha with ⟨hanot, has⟩
      have hpapp : (p ++ ps.flatten).Nodup := by
        simpa only [List.flatten_cons] using hp
      rcases List.nodup_append'.mp hpapp with ⟨hpn, hpsn, hpsep⟩
      have hseprest : ∀ z, z ∈ as → z ∈ ps.flatten → False := by
        intro z hz hzp
        exact hsep z (List.mem_cons.mpr (Or.inr hz))
          (by simpa only [List.flatten_cons, List.mem_append] using
            (Or.inr hzp : z ∈ p ∨ z ∈ ps.flatten))
      have htail := ih as hrest has hpsn hseprest
      have hpTail : p.Disjoint (stitch as ps) := by
        rw [List.disjoint_left]
        intro z hzp hzt
        rcases (stitch_mem as ps hrest z).mp hzt with hza | hzps
        · exact hsep z (List.mem_cons.mpr (Or.inr hza))
            (by simpa only [List.flatten_cons, List.mem_append] using
              (Or.inl hzp : z ∈ p ∨ z ∈ ps.flatten))
        · exact List.disjoint_left.mp hpsep hzp hzps
      have happ : (p ++ stitch as ps).Nodup := hpn.append htail hpTail
      have hanotAll : a ∉ p ++ stitch as ps := by
        intro hz
        rcases List.mem_append.mp hz with hzp | hzt
        · exact hsep a (by simp)
            (by simpa only [List.flatten_cons, List.mem_append] using
              (Or.inl hzp : a ∈ p ∨ a ∈ ps.flatten))
        · rcases (stitch_mem as ps hrest a).mp hzt with hza | hzps
          · exact hanot hza
          · exact hsep a (by simp)
              (by simpa only [List.flatten_cons, List.mem_append] using
                (Or.inr hzps : a ∈ p ∨ a ∈ ps.flatten))
      exact List.nodup_cons.mpr ⟨hanotAll, happ⟩

theorem stitch_chain {V : Type*} (F : SimpleGraph V)
    (C O : Set V) (as : List V) (ps : List (List V))
    (hlen : as.length = ps.length + 1)
    (ha : ∀ a, a ∈ as → a ∈ C)
    (hp : ∀ p, p ∈ ps → p ≠ [] ∧ p.IsChain F.Adj ∧
      ∀ x, x ∈ p → x ∈ O)
    (hcross : ∀ x, x ∈ O → ∀ a, a ∈ C → F.Adj x a) :
    (stitch as ps).IsChain F.Adj := by
  induction ps generalizing as with
  | nil =>
    cases as with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons a as =>
      have has : as = [] := by
        have hzero : as.length = 0 := by
          simp only [List.length_cons, List.length_nil] at hlen
          omega
        exact List.length_eq_zero_iff.mp hzero
      subst as
      simpa only [stitch] using List.IsChain.singleton (R := F.Adj) a
  | cons p ps ih =>
    cases as with
    | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons a as =>
      have hrest : as.length = ps.length + 1 := by
        simp only [List.length_cons] at hlen
        omega
      have hastail : ∀ b, b ∈ as → b ∈ C := by
        intro b hb
        exact ha b (List.mem_cons.mpr (Or.inr hb))
      have hpstail : ∀ q, q ∈ ps → q ≠ [] ∧ q.IsChain F.Adj ∧
          ∀ x, x ∈ q → x ∈ O := by
        intro q hq
        exact hp q (List.mem_cons.mpr (Or.inr hq))
      have htail := ih as hrest hastail hpstail
      rcases hp p (by simp) with ⟨hpne, hpchain, hpO⟩
      have hjoin : (p ++ stitch as ps).IsChain F.Adj := by
        apply hpchain.append htail
        intro x hx b hb
        have hxO : x ∈ O := hpO x (List.mem_of_mem_getLast? hx)
        have hbhead : b ∈ as.head? := by
          simpa only [stitch_head?] using hb
        exact hcross x hxO b (hastail b (List.mem_of_mem_head? hbhead))
      change (a :: (p ++ stitch as ps)).IsChain F.Adj
      apply hjoin.cons
      intro x hx
      have hxhead : x ∈ p.head? := by
        simpa only [List.head?_append_of_ne_nil _ hpne] using hx
      exact (hcross x (hpO x (List.mem_of_mem_head? hxhead)) a
        (ha a (by simp))).symm

/-- Actual original outsider paths covering the SAME carrier, with enough
complete contacted-core anchors in F, yield an injective spanning cycle in F.
The cover has no placement, anchor-order or desired-cycle premise. -/
theorem cycle_of_actual_outsider_path_cover {d : ℕ} (hd : 1 ≤ d)
    (G F : SimpleGraph (Fin (2 * d + 3))) (hGF : G ≤ F)
    (S C : Finset (Fin (2 * d + 3))) (_hScard : S.card = d + 3)
    (hclique : G.IsClique (S : Set (Fin (2 * d + 3)))) (hCS : C ⊆ S)
    (cover : List (List (Fin (2 * d + 3))))
    (hnonempty : ∀ p, p ∈ cover → p ≠ [])
    (hpaths : ∀ p, p ∈ cover → p.IsChain G.Adj)
    (hdisjoint : cover.flatten.Nodup)
    (hcovers : ∀ z, z ∈ cover.flatten ↔ z ∉ S)
    (hcapacity : cover.length + 1 ≤ C.card)
    (hfilled : ∀ x, x ∉ S → ∀ a, a ∈ C → F.Adj x a) :
    cycleGraph (2 * d + 3) ⊑ F := by
  classical
  obtain ⟨A, hAC, hAcard⟩ := Finset.exists_subset_card_eq hcapacity
  have hAS : A ⊆ S := fun z hz => hCS (hAC hz)
  let anchors : List (Fin (2 * d + 3)) := A.toList
  have halign : anchors.length = cover.length + 1 := by
    simpa only [anchors, Finset.length_toList] using hAcard
  have hAnchorCover : ∀ z, z ∈ anchors → z ∈ cover.flatten → False := by
    intro z hz hzO
    exact (hcovers z).mp hzO (hAS (Finset.mem_toList.mp hz))
  let B : List (Fin (2 * d + 3)) := stitch anchors cover
  have hBne : B ≠ [] := stitch_ne_nil anchors cover halign
  have hBn : B.Nodup := stitch_nodup anchors cover halign
    A.nodup_toList hdisjoint hAnchorCover
  have hBmem : ∀ z, z ∈ B ↔ z ∈ A ∨ z ∉ S := by
    intro z
    simpa only [B, anchors, Finset.mem_toList, hcovers z] using
      stitch_mem anchors cover halign z
  have hBhead : B.head? = anchors.head? := stitch_head? _ _
  have hBlast : B.getLast? = anchors.getLast? := stitch_getLast? _ _ halign
  have hBlastA : ∀ z, z ∈ B.getLast? → z ∈ A := by
    intro z hz
    rw [hBlast] at hz
    exact Finset.mem_toList.mp (List.mem_of_mem_getLast? hz)
  have hBchain : B.IsChain F.Adj := by
    apply stitch_chain F (C : Set (Fin (2 * d + 3)))
      ((S : Set (Fin (2 * d + 3)))ᶜ) anchors cover halign
    · intro a ha
      exact hAC (Finset.mem_toList.mp ha)
    · intro p hp
      refine ⟨hnonempty p hp, (hpaths p hp).imp (fun {_x _y} h => hGF h), ?_⟩
      intro x hx
      exact (hcovers x).mp (List.mem_flatten.mpr ⟨p, hp, hx⟩)
    · exact hfilled
  let R : Finset (Fin (2 * d + 3)) := S \ A
  have hRS : R ⊆ S := fun z hz => (Finset.mem_sdiff.mp hz).1
  have hBR : B.Disjoint R.toList := by
    rw [List.disjoint_left]
    intro z hzB hzR
    have hzR' := Finset.mem_sdiff.mp (Finset.mem_toList.mp hzR)
    rcases (hBmem z).mp hzB with hzA | hzO
    · exact hzR'.2 hzA
    · exact hzO hzR'.1
  have hRchain : R.toList.IsChain F.Adj := by
    apply List.Pairwise.isChain
    exact R.nodup_toList.pairwise_of_forall_ne
      (fun x hx y hy hxy => hGF (hclique
        (hRS (Finset.mem_toList.mp hx)) (hRS (Finset.mem_toList.mp hy)) hxy))
  let L : List (Fin (2 * d + 3)) := B ++ R.toList
  have hLn : L.Nodup := hBn.append R.nodup_toList hBR
  have hLchain : L.IsChain F.Adj := by
    apply hBchain.append hRchain
    intro x hx y hy
    have hxA : x ∈ A := hBlastA x hx
    have hyR : y ∈ R := Finset.mem_toList.mp (List.mem_of_mem_head? hy)
    have hxy : x ≠ y := by
      intro hxy
      exact (Finset.mem_sdiff.mp hyR).2 (hxy ▸ hxA)
    exact hGF (hclique (hAS hxA) (hRS hyR) hxy)
  have hLmem : ∀ z, z ∈ L := by
    intro z
    by_cases hzS : z ∈ S
    · by_cases hzA : z ∈ A
      · exact List.mem_append.mpr (Or.inl ((hBmem z).mpr (Or.inl hzA)))
      · exact List.mem_append.mpr (Or.inr (Finset.mem_toList.mpr
          (Finset.mem_sdiff.mpr ⟨hzS, hzA⟩)))
    · exact List.mem_append.mpr (Or.inl ((hBmem z).mpr (Or.inr hzS)))
  have hLfin : L.toFinset = Finset.univ := by
    ext z
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact hLmem z
  have hLlength : L.length = 2 * d + 3 := by
    rw [← List.toFinset_card_of_nodup hLn, hLfin, Finset.card_univ,
      Fintype.card_fin]
  have hLne : L ≠ [] := by
    intro hnil
    simp only [hnil, List.length_nil] at hLlength
    omega
  have hheadS : L.head hLne ∈ S := by
    have hz : L.head hLne ∈ L.head? := List.head_mem_head? hLne
    have hh : L.head? = anchors.head? := by
      change (B ++ R.toList).head? = anchors.head?
      rw [List.head?_append_of_ne_nil _ hBne, hBhead]
    rw [hh] at hz
    exact hAS (Finset.mem_toList.mp (List.mem_of_mem_head? hz))
  have hlastS : L.getLast hLne ∈ S := by
    have hz : L.getLast hLne ∈ L.getLast? := List.getLast_mem_getLast? hLne
    by_cases hRnil : R.toList = []
    · have hh : L.getLast? = B.getLast? := by simp only [L, hRnil, List.append_nil]
      rw [hh] at hz
      exact hAS (hBlastA _ hz)
    · have hh : L.getLast? = R.toList.getLast? :=
        List.getLast?_append_of_ne_nil _ hRnil
      rw [hh] at hz
      exact hRS (Finset.mem_toList.mp (List.mem_of_mem_getLast? hz))
  have hendpoints : L.head hLne ≠ L.getLast hLne := by
    intro heq
    obtain ⟨x, hsingle⟩ := (List.Nodup.head_eq_getLast_iff hLne hLn).mp heq
    have hone : L.length = 1 := by simp only [hsingle, List.length_cons, List.length_nil]
    omega
  let P : F.Walk (L.head hLne) (L.getLast hLne) := Walk.ofSupport L hLne hLchain
  have hP : P.IsPath := by
    rw [Walk.isPath_def]
    simpa only [P, Walk.support_ofSupport] using hLn
  have hPlength : P.length = 2 * d + 2 := by
    simp only [P, Walk.length_ofSupport, hLlength]
    omega
  have hclose : F.Adj (L.getLast hLne) (L.head hLne) :=
    hGF (hclique hlastS hheadS hendpoints.symm)
  have hPtail : L.head hLne ∉ P.support.tail := by
    have hn := hP.support_nodup
    rw [← Walk.cons_tail_support] at hn
    exact (List.nodup_cons.mp hn).1
  have hcycle : (P.append hclose.toWalk).IsCycle := by
    apply hP.isCycle_append hclose.isPath_toWalk
    · rw [List.disjoint_left]
      intro z hzP hzClose
      have hz : z = L.head hLne := by
        simpa only [SimpleGraph.Adj.support_toWalk, List.tail_cons,
          List.mem_singleton] using hzClose
      exact hPtail (hz ▸ hzP)
    · left
      omega
  apply (cycleGraph_isContained_iff (by omega)).mpr
  refine ⟨L.head hLne, P.append hclose.toWalk, hcycle, ?_⟩
  simp only [Walk.length_append, SimpleGraph.Adj.length_toWalk, hPlength]

end ErdosProblems.PathUpperReduction.EvenLastBlockRigidity1105
