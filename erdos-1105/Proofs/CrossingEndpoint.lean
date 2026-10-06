module

public import CrossingProvider.VineCycle
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

open SimpleGraph
namespace ErdosProblems.PathUpperReduction.CrossingEndpoint
open VineCycle
variable {V : Type*} {G : SimpleGraph V} {u v : V}

theorem crossing_cycle (P : G.Walk u v) (hp : P.IsPath) (i j : ℕ)
    (hj : 0 < j) (hji : j < i) (hi : i < P.length)
    (ha : G.Adj (P.getVert 0) (P.getVert i))
    (hb : G.Adj (P.getVert j) (P.getVert P.length)) :
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧
      C.length = P.length + 2 - (i - j) ∧
      ∀ z, z ∈ C.support ↔
        (∃ k, k ≤ j ∧ P.getVert k = z) ∨
        (∃ k, i ≤ k ∧ k ≤ P.length ∧ P.getVert k = z) := by
  let S := Erdos58.pathInterval P 0 j (Nat.zero_le j)
  let T := Erdos58.pathInterval P i P.length hi.le
  let A := S.append hb.toWalk
  let B := ha.toWalk.append T
  have hS : S.IsPath := Erdos58.pathInterval_isPath P hp 0 j (Nat.zero_le j)
  have hT : T.IsPath := Erdos58.pathInterval_isPath P hp i P.length hi.le
  have hA : A.IsPath := by
    apply Erdos58.path_append_of_meet_only S hb.toWalk hS hb.isPath_toWalk
    intro z hz hzE
    simp only [SimpleGraph.Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] at hzE
    rcases hzE with he | he
    · exact he
    · have hcontact := interval_contacts P hp 0 j (Nat.zero_le j) (by omega)
        P.length le_rfl (he ▸ hz)
      omega
  have hB : B.IsPath := by
    apply Erdos58.path_append_of_meet_only ha.toWalk T ha.isPath_toWalk hT
    intro z hzE hz
    simp only [SimpleGraph.Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] at hzE
    rcases hzE with he | he
    · have hcontact := interval_contacts P hp i P.length hi.le le_rfl 0
        (Nat.zero_le _) (he ▸ hz)
      omega
    · exact he
  have hmeet : ∀ z, z ∈ A.support → z ∈ B.support →
      z = P.getVert 0 ∨ z = P.getVert P.length := by
    intro z hzA hzB
    rcases (Walk.mem_support_append_iff _ _).mp hzA with hzS | hzE
    · rcases (Walk.mem_support_append_iff _ _).mp hzB with hzE | hzT
      · simp only [SimpleGraph.Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] at hzE
        rcases hzE with he | he
        · exact Or.inl he
        · have := interval_contacts P hp 0 j (Nat.zero_le j) (by omega) i hi.le (he ▸ hzS)
          omega
      · obtain ⟨a, _, haj, haz⟩ := (interval_support P 0 j (Nat.zero_le j) (by omega) z).mp hzS
        obtain ⟨b, hib, hbl, hbz⟩ := (interval_support P i P.length hi.le le_rfl z).mp hzT
        have he := hp.getVert_injOn (show a ≤ P.length from by omega) hbl (haz.trans hbz.symm)
        omega
    · simp only [SimpleGraph.Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] at hzE
      rcases hzE with he | he
      · have := interval_contacts P hp i P.length hi.le le_rfl j (by omega)
          (he ▸ ((Walk.mem_support_append_iff _ _).mp hzB).resolve_left (by
            intro hmem
            simp only [SimpleGraph.Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] at hmem
            rcases hmem with h0 | hi0
            · have := hp.getVert_injOn (show j ≤ P.length from by omega) (Nat.zero_le _)
                (he.symm.trans h0)
              omega
            · have := hp.getVert_injOn (show j ≤ P.length from by omega) hi.le
                (he.symm.trans hi0)
              omega))
        omega
      · exact Or.inr he
  have hAlen : A.length = j + 1 := by
    simp [A, S, Erdos58.pathInterval_length P 0 j (Nat.zero_le j) (by omega)]
  have hBlen : B.length = 1 + (P.length - i) := by
    simp [B, T, Erdos58.pathInterval_length P i P.length hi.le le_rfl, Nat.add_comm]
  refine ⟨A.append B.reverse, Erdos58.cycle_of_two_paths A B hA hB hmeet (by omega), ?_, ?_⟩
  · rw [Erdos58.two_paths_cycle_length, hAlen, hBlen]
    omega
  · intro z
    simp only [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse,
      A, B, S, T, SimpleGraph.Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false]
    rw [interval_support P 0 j (Nat.zero_le j) (by omega) z,
      interval_support P i P.length hi.le le_rfl z]
    have h0 : ∃ k, k ≤ j ∧ P.getVert k = P.getVert 0 := ⟨0, Nat.zero_le _, rfl⟩
    have hjj : ∃ k, k ≤ j ∧ P.getVert k = P.getVert j := ⟨j, le_rfl, rfl⟩
    have his : ∃ k, i ≤ k ∧ k ≤ P.length ∧ P.getVert k = P.getVert P.length :=
      ⟨P.length, hi.le, le_rfl, rfl⟩
    have hii : ∃ k, i ≤ k ∧ k ≤ P.length ∧ P.getVert k = P.getVert i :=
      ⟨i, le_rfl, hi.le, rfl⟩
    aesop

theorem minimal_gap_count (A B : Finset ℕ) (s i j : ℕ)
    (hA : ∀ a ∈ A, 0 < a ∧ a < s) (hB : ∀ b ∈ B, 0 < b ∧ b < s)
    (hi : i ∈ A) (hj : j ∈ B) (hg : 2 ≤ i - j)
    (hmin : ∀ a ∈ A, ∀ b ∈ B, b < a → i - j ≤ a - b) :
    A.card + B.card ≤ s + 2 - (i - j) := by
  classical
  let M := A.image (fun a => a - 1)
  have hM : M.card = A.card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb he
    have := (hA a ha).1
    have := (hA b hb).1
    change a - 1 = b - 1 at he
    omega
  have hdisj : Disjoint M B := by
    apply Finset.disjoint_left.mpr
    intro x hxM hxB
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hxM
    have hpos := (hA a ha).1
    have := hmin a ha x hxB (by omega)
    omega
  have hsnot : s ∉ M ∪ B := by
    intro hmem
    rcases Finset.mem_union.mp hmem with hm | hb
    · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hm
      have := (hA a ha).2
      omega
    · have := (hB s hb).2
      omega
  let T := (M ∪ B) ∪ {s}
  have hT : T.card = A.card + B.card + 1 := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hsnot),
      Finset.card_union_of_disjoint hdisj, hM, Finset.card_singleton]
  have hiM : i - 1 ∈ T := by
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hErase : (T.erase (i - 1)).card = A.card + B.card := by
    rw [Finset.card_erase_of_mem hiM, hT]
    omega
  have hsub : T.erase (i - 1) ⊆ Finset.Icc 0 j ∪ Finset.Icc i s := by
    intro x hx
    obtain ⟨hne, hxT⟩ := Finset.mem_erase.mp hx
    rcases Finset.mem_union.mp hxT with hxMB | hxS
    · rcases Finset.mem_union.mp hxMB with hxM | hxB
      · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hxM
        have hap := hA a ha
        by_cases haj : a ≤ j
        · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩)
        · have hno : i ≤ a := by
            by_contra hn
            have := hmin a ha j hj (by omega)
            omega
          exact Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      · have hxp := hB x hxB
        by_cases hxj : x ≤ j
        · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨Nat.zero_le _, hxj⟩)
        · have hno : i ≤ x := by
            by_contra hn
            have := hmin i hi x hxB (by omega)
            omega
          exact Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨hno, by omega⟩)
    · have he : x = s := Finset.mem_singleton.mp hxS
      exact Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨by have := (hA i hi).2; omega, by omega⟩)
  have hd : Disjoint (Finset.Icc 0 j) (Finset.Icc i s) := by
    apply Finset.disjoint_left.mpr
    intro x hxj hxi
    have := (Finset.mem_Icc.mp hxj).2
    have := (Finset.mem_Icc.mp hxi).1
    omega
  have hc := Finset.card_le_card hsub
  rw [hErase, Finset.card_union_of_disjoint hd, Nat.card_Icc, Nat.card_Icc] at hc
  have := hA i hi
  have := hB j hj
  omega

noncomputable def LeftNeighbors (P : G.Walk u v) : Finset ℕ := by
  classical
  exact (Finset.Icc 0 P.length).filter (fun k => G.Adj (P.getVert 0) (P.getVert k))

noncomputable def RightNeighbors (P : G.Walk u v) : Finset ℕ := by
  classical
  exact (Finset.Icc 0 P.length).filter (fun k => G.Adj (P.getVert P.length) (P.getVert k))

theorem mem_left (P : G.Walk u v) (k : ℕ) :
    k ∈ LeftNeighbors P ↔ k ≤ P.length ∧ G.Adj (P.getVert 0) (P.getVert k) := by
  classical
  simp [LeftNeighbors, Finset.mem_Icc]

theorem mem_right (P : G.Walk u v) (k : ℕ) :
    k ∈ RightNeighbors P ↔ k ≤ P.length ∧ G.Adj (P.getVert P.length) (P.getVert k) := by
  classical
  simp [RightNeighbors, Finset.mem_Icc]

theorem neighbors_internal (P : G.Walk u v)
    (hne : ¬ G.Adj (P.getVert 0) (P.getVert P.length)) :
    (∀ a ∈ LeftNeighbors P, 0 < a ∧ a < P.length) ∧
    (∀ b ∈ RightNeighbors P, 0 < b ∧ b < P.length) := by
  constructor
  · intro a ha
    obtain ⟨hab, hadj⟩ := (mem_left P a).mp ha
    have ha0 : a ≠ 0 := by
      intro he
      subst a
      exact G.irrefl hadj
    have hal : a ≠ P.length := by
      intro he
      exact hne (he ▸ hadj)
    omega
  · intro b hb
    obtain ⟨hbb, hadj⟩ := (mem_right P b).mp hb
    have hb0 : b ≠ 0 := by
      intro he
      subst b
      exact hne hadj.symm
    have hbl : b ≠ P.length := by
      intro he
      exact G.irrefl (he ▸ hadj)
    omega

theorem exists_min_crossing (A B : Finset ℕ)
    (hex : ∃ i ∈ A, ∃ j ∈ B, j < i) :
    ∃ i ∈ A, ∃ j ∈ B, j < i ∧
      ∀ a ∈ A, ∀ b ∈ B, b < a → i - j ≤ a - b := by
  classical
  let F := (A.product B).filter (fun p => p.2 < p.1)
  have hF : F.Nonempty := by
    obtain ⟨i, hi, j, hj, hji⟩ := hex
    exact ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi, hj⟩, hji⟩⟩
  obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image F (fun p => p.1 - p.2) hF
  obtain ⟨hpAB, hcross⟩ := Finset.mem_filter.mp hp
  obtain ⟨hi, hj⟩ := Finset.mem_product.mp hpAB
  refine ⟨p.1, hi, p.2, hj, hcross, ?_⟩
  intro a ha b hb hba
  exact hmin (a, b) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hba⟩)

theorem crossing_threshold (P : G.Walk u v) (hp : P.IsPath)
    (hne : ¬ G.Adj (P.getVert 0) (P.getVert P.length))
    (hex : ∃ i ∈ LeftNeighbors P, ∃ j ∈ RightNeighbors P, j < i) :
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧
      min (P.length + 1) ((LeftNeighbors P).card + (RightNeighbors P).card) ≤ C.length := by
  obtain ⟨i, hi, j, hj, hji, hmin⟩ := exists_min_crossing (LeftNeighbors P) (RightNeighbors P) hex
  obtain ⟨hA, hB⟩ := neighbors_internal P hne
  have hib := hA i hi
  have hjb := hB j hj
  have hai := ((mem_left P i).mp hi).2
  have hbj := ((mem_right P j).mp hj).2.symm
  obtain ⟨C, hC, hlen, _⟩ := crossing_cycle P hp i j hjb.1 hji hib.2 hai hbj
  refine ⟨C, hC, ?_⟩
  by_cases hg : i - j = 1
  · rw [hlen, hg]
    have := Nat.min_le_left (P.length + 1) ((LeftNeighbors P).card + (RightNeighbors P).card)
    omega
  · have hgap : 2 ≤ i - j := by omega
    have hcount := minimal_gap_count (LeftNeighbors P) (RightNeighbors P) P.length i j hA hB hi hj hgap hmin
    have := Nat.min_le_right (P.length + 1) ((LeftNeighbors P).card + (RightNeighbors P).card)
    omega

theorem adjacent_endpoint_cycle (P : G.Walk u v) (hp : P.IsPath) (hs : 2 ≤ P.length)
    (he : G.Adj (P.getVert 0) (P.getVert P.length)) :
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧ C.length = P.length + 1 := by
  let W := P.copy (Walk.getVert_zero P).symm (Walk.getVert_length P).symm
  have hW : W.IsPath := by simpa only [W, Walk.isPath_copy] using hp
  have hlen : W.length = P.length := by simp [W]
  refine ⟨Walk.cons he W.reverse, ?_, ?_⟩
  · exact Erdos58.cycle_of_path_and_edge W.reverse hW.reverse he (by simp only [Walk.length_reverse]; omega)
  · simp [hlen]

theorem endpoint_crossing_branch (P : G.Walk u v) (hp : P.IsPath)
    (K : ℕ) (hK : 5 ≤ K) (hKs : K ≤ P.length + 1)
    (hKD : K ≤ (LeftNeighbors P).card + (RightNeighbors P).card)
    (hcase : G.Adj (P.getVert 0) (P.getVert P.length) ∨
      ∃ i ∈ LeftNeighbors P, ∃ j ∈ RightNeighbors P, j < i) :
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧ K ≤ C.length := by
  classical
  by_cases he : G.Adj (P.getVert 0) (P.getVert P.length)
  · obtain ⟨C, hC, hlen⟩ := adjacent_endpoint_cycle P hp (by omega) he
    exact ⟨C, hC, by omega⟩
  · obtain ⟨C, hC, hlen⟩ := crossing_threshold P hp he (hcase.resolve_left he)
    exact ⟨C, hC, le_trans (Nat.le_min.mpr ⟨hKs, hKD⟩) hlen⟩

theorem path_neighbor_count (P : G.Walk u v) (hp : P.IsPath) (x : V) :
    letI := Classical.decEq V
    letI := Classical.propDecidable
    ((Finset.Icc 0 P.length).filter (fun k => G.Adj x (P.getVert k))).card =
      (P.support.toFinset.filter (fun z => G.Adj x z)).card := by
  classical
  let N := (Finset.Icc 0 P.length).filter (fun k => G.Adj x (P.getVert k))
  have himage : N.image P.getVert = P.support.toFinset.filter (fun z => G.Adj x z) := by
    ext z
    constructor
    · intro hz
      obtain ⟨k, hk, hkz⟩ := Finset.mem_image.mp hz
      obtain ⟨hki, hadj⟩ := Finset.mem_filter.mp hk
      apply Finset.mem_filter.mpr
      refine ⟨List.mem_toFinset.mpr ?_, hkz ▸ hadj⟩
      exact hkz ▸ Walk.getVert_mem_support P k
    · intro hz
      obtain ⟨hzP, hadj⟩ := Finset.mem_filter.mp hz
      obtain ⟨k, hkz, hkl⟩ := Walk.mem_support_iff_exists_getVert.mp (List.mem_toFinset.mp hzP)
      apply Finset.mem_image.mpr
      refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hkl⟩, ?_⟩, hkz⟩
      exact hkz.symm ▸ hadj
  have hcard : (N.image P.getVert).card = N.card := by
    apply Finset.card_image_of_injOn
    intro i hi j hj he
    have hiP := (Finset.mem_Icc.mp (Finset.mem_filter.mp hi).1).2
    have hjP := (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).2
    exact hp.getVert_injOn hiP hjP he
  rw [himage] at hcard
  exact hcard.symm

theorem left_neighbor_count (P : G.Walk u v) (hp : P.IsPath) :
    letI := Classical.decEq V
    letI := Classical.propDecidable
    (LeftNeighbors P).card =
      (P.support.toFinset.filter (fun z => G.Adj (P.getVert 0) z)).card := by
  classical
  simpa only [LeftNeighbors] using path_neighbor_count P hp (P.getVert 0)

theorem right_neighbor_count (P : G.Walk u v) (hp : P.IsPath) :
    letI := Classical.decEq V
    letI := Classical.propDecidable
    (RightNeighbors P).card =
      (P.support.toFinset.filter (fun z => G.Adj (P.getVert P.length) z)).card := by
  classical
  simpa only [RightNeighbors] using path_neighbor_count P hp (P.getVert P.length)

theorem endpoint_crossing_vertex_count (P : G.Walk u v) (hp : P.IsPath)
    (K : ℕ) (hK : 5 ≤ K) (hKs : K ≤ P.length + 1)
    (hcase : G.Adj (P.getVert 0) (P.getVert P.length) ∨
      ∃ i ∈ LeftNeighbors P, ∃ j ∈ RightNeighbors P, j < i) :
    letI := Classical.decEq V
    letI := Classical.propDecidable
    K ≤ (P.support.toFinset.filter (fun z => G.Adj (P.getVert 0) z)).card +
      (P.support.toFinset.filter (fun z => G.Adj (P.getVert P.length) z)).card →
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧ K ≤ C.length := by
  classical
  intro hKD
  apply endpoint_crossing_branch P hp K hK hKs ?_ hcase
  rw [left_neighbor_count P hp, right_neighbor_count P hp]
  exact hKD

end ErdosProblems.PathUpperReduction.CrossingEndpoint
