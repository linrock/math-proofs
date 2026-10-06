module

public import BoundaryEndpoint

@[expose] public section

open SimpleGraph
namespace ErdosProblems.PathUpperReduction.EndpointCapture

variable {V : Type*} {G : SimpleGraph V} {x y : V}

/-- A maximum in the actual nonadjacent endpoint family captures its left neighbors. -/
theorem left_neighbors_on_path (A B : Finset V) (P : G.Walk x y)
    (hp : P.IsPath) (hy : y ∈ B) {K : ℕ} (hK : 5 ≤ K)
    (hKP : K ≤ P.length + 1)
    (noLong : ∀ q (C : G.Walk q q), C.IsCycle → C.length < K)
    (hmax : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b →
      ∀ Q : G.Walk a b, Q.IsPath → Q.length ≤ P.length) :
    ∀ z ∈ A, G.Adj x z → z ∈ P.support := by
  intro z hz hxz
  by_contra hzOutside
  let Q := Walk.cons hxz.symm P
  have hQ : Q.IsPath := hp.cons hzOutside
  by_cases hzy : G.Adj z y
  · have htwo : 2 ≤ Q.length := by
      simp only [Q, Walk.length_cons]
      omega
    let C := Walk.cons hzy.symm Q
    have hC : C.IsCycle := Erdos58.cycle_of_path_and_edge Q hQ hzy.symm htwo
    have hshort := noLong y C hC
    simp only [C, Q, Walk.length_cons] at hshort
    omega
  · have hbound := hmax z hz y hy hzy Q hQ
    simp only [Q, Walk.length_cons] at hbound
    omega

/-- Reversal derives the exact right-endpoint family rather than fixing endpoints. -/
theorem neighbors_on_path (A B : Finset V) (P : G.Walk x y)
    (hp : P.IsPath) (hx : x ∈ A) (hy : y ∈ B) {K : ℕ} (hK : 5 ≤ K)
    (hKP : K ≤ P.length + 1)
    (noLong : ∀ q (C : G.Walk q q), C.IsCycle → C.length < K)
    (hmax : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b →
      ∀ Q : G.Walk a b, Q.IsPath → Q.length ≤ P.length) :
    (∀ z ∈ A, G.Adj x z → z ∈ P.support) ∧
      (∀ z ∈ B, G.Adj y z → z ∈ P.support) := by
  constructor
  · exact left_neighbors_on_path A B P hp hy hK hKP noLong hmax
  · have hrevmax : ∀ a ∈ B, ∀ b ∈ A, ¬ G.Adj a b →
        ∀ Q : G.Walk a b, Q.IsPath → Q.length ≤ P.reverse.length := by
      intro a ha b hb hab Q hQ
      have hba : ¬ G.Adj b a := fun h ↦ hab h.symm
      simpa using hmax b hb a ha hba Q.reverse hQ.reverse
    have hc := left_neighbors_on_path B A P.reverse hp.reverse hx hK
      (by simpa using hKP) noLong hrevmax
    intro z hz hyz
    simpa using hc z hz hyz

/-- A finite actual endpoint family containing P has an actual maximum at least as long. -/
theorem exists_family_maximum [Finite V] (A B : Finset V) (P : G.Walk x y)
    (hp : P.IsPath) (hx : x ∈ A) (hy : y ∈ B) (hxy : ¬ G.Adj x y) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ Q : G.Walk a b, Q.IsPath ∧ ¬ G.Adj a b ∧
      P.length ≤ Q.length ∧
      (∀ c ∈ A, ∀ d ∈ B, ¬ G.Adj c d →
        ∀ R : G.Walk c d, R.IsPath → R.length ≤ Q.length) := by
  classical
  let _ := Fintype.ofFinite V
  let s : Set ℕ := {n | ∃ a ∈ A, ∃ b ∈ B, ∃ Q : G.Walk a b,
    Q.IsPath ∧ ¬ G.Adj a b ∧ Q.length = n}
  have hs : s.Finite := Set.Finite.subset (Set.finite_le_nat (Fintype.card V))
    (by
      intro n hn
      obtain ⟨a, ha, b, hb, Q, hQ, hab, hlen⟩ := hn
      exact hlen ▸ hQ.length_lt.le)
  have hseed : P.length ∈ s := ⟨x, hx, y, hy, P, hp, hxy, rfl⟩
  obtain ⟨n, ⟨hn, hmax⟩⟩ := hs.exists_maximal ⟨P.length, hseed⟩
  obtain ⟨a, ha, b, hb, Q, hQ, hab, hlen⟩ := hn
  have hbound : ∀ c ∈ A, ∀ d ∈ B, ¬ G.Adj c d →
      ∀ R : G.Walk c d, R.IsPath → R.length ≤ Q.length := by
    intro c hc d hd hcd R hR
    have hm := hmax (show R.length ∈ s from ⟨c, hc, d, hd, R, hR, hcd, rfl⟩)
    omega
  exact ⟨a, ha, b, hb, Q, hQ, hab, hbound x hx y hy hxy P hp, hbound⟩

/-- The maximum and both neighbor-capture facts are derived from one initial actual path. -/
theorem exists_captured_family_maximum [Finite V] (A B : Finset V)
    (P : G.Walk x y) (hp : P.IsPath) (hx : x ∈ A) (hy : y ∈ B)
    (hxy : ¬ G.Adj x y) {K : ℕ} (hK : 5 ≤ K) (hKP : K ≤ P.length + 1)
    (noLong : ∀ q (C : G.Walk q q), C.IsCycle → C.length < K) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ Q : G.Walk a b, Q.IsPath ∧ ¬ G.Adj a b ∧
      P.length ≤ Q.length ∧
      (∀ c ∈ A, ∀ d ∈ B, ¬ G.Adj c d →
        ∀ R : G.Walk c d, R.IsPath → R.length ≤ Q.length) ∧
      (∀ z ∈ A, G.Adj a z → z ∈ Q.support) ∧
      (∀ z ∈ B, G.Adj b z → z ∈ Q.support) := by
  obtain ⟨a, ha, b, hb, Q, hQ, hab, hlen, hmax⟩ :=
    exists_family_maximum A B P hp hx hy hxy
  have hKQ : K ≤ Q.length + 1 := by omega
  obtain ⟨hleft, hright⟩ := neighbors_on_path A B Q hQ ha hb hK hKQ noLong hmax
  exact ⟨a, ha, b, hb, Q, hQ, hab, hlen, hmax, hleft, hright⟩

end ErdosProblems.PathUpperReduction.EndpointCapture
