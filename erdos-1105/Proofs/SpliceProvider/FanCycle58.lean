module

public import SpliceProvider.BackEdge58

@[expose] public section

/-!
Actual fan cycles, indexed by positions on a simple graph path. Every
witness consists of the interval path and two edges from a vertex outside
the path; the resulting length is exact, and the vertices remain distinct.
-/

namespace Erdos58

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {a b x : V}

def cycleWithoutRoot (c : G.Walk x x) (_hc : c.IsCycle) :
    G.Walk c.snd c.tail.penultimate := c.tail.dropLast

theorem cycleWithoutRoot_isPath (c : G.Walk x x) (hc : c.IsCycle) :
    (cycleWithoutRoot c hc).IsPath := hc.isPath_tail.dropLast

theorem cycleWithoutRoot_tail_notNil (c : G.Walk x x) (hc : c.IsCycle) :
    ¬c.tail.Nil := by
  rw [Walk.not_nil_iff_lt_length, Walk.length_tail]
  have := hc.three_le_length
  omega

theorem cycleWithoutRoot_root_notMem (c : G.Walk x x) (hc : c.IsCycle) :
    x ∉ (cycleWithoutRoot c hc).support := by
  have ht := cycleWithoutRoot_tail_notNil c hc
  have hNodup : ((cycleWithoutRoot c hc).support ++ [x]).Nodup := by
    rw [cycleWithoutRoot, Walk.support_dropLast_concat ht]
    exact hc.isPath_tail.support_nodup
  intro hx
  exact (List.nodup_append.mp hNodup).2.2 x hx x (by simp) rfl

theorem cycleWithoutRoot_length (c : G.Walk x x) (hc : c.IsCycle) :
    (cycleWithoutRoot c hc).length = c.length - 2 := by
  simp [cycleWithoutRoot, Walk.length_dropLast, Walk.length_tail, Nat.sub_sub]

theorem cycleWithoutRoot_first_edge (c : G.Walk x x) (hc : c.IsCycle) :
    G.Adj x c.snd := c.adj_snd hc.not_nil

theorem cycleWithoutRoot_last_edge (c : G.Walk x x) (hc : c.IsCycle) :
    G.Adj x c.tail.penultimate :=
  (c.tail.adj_penultimate (cycleWithoutRoot_tail_notNil c hc)).symm

theorem cycleWithoutRoot_mem_of_ne (c : G.Walk x x) (hc : c.IsCycle)
    {u : V} (hux : u ≠ x) (hu : u ∈ c.support) :
    u ∈ (cycleWithoutRoot c hc).support := by
  rw [← Walk.cons_support_tail hc.not_nil] at hu
  rcases List.mem_cons.mp hu with hEq | hu
  · exact (hux hEq).elim
  · rw [← Walk.support_dropLast_concat (cycleWithoutRoot_tail_notNil c hc)] at hu
    simpa [cycleWithoutRoot, hux] using hu

theorem cycleWithoutRoot_covers_neighbors (c : G.Walk x x) (hc : c.IsCycle)
    (hcover : ∀ u, G.Adj x u → u ∈ c.support) :
    ∀ u, G.Adj x u → u ∈ (cycleWithoutRoot c hc).support := by
  intro u hu
  exact cycleWithoutRoot_mem_of_ne c hc hu.ne.symm (hcover u hu)

/-- All path positions adjacent to an external vertex. -/
noncomputable def pathNeighborPositions (p : G.Walk a b) (x : V) : Finset ℕ := by
  classical
  exact (Finset.range (p.length + 1)).filter (fun i ↦ G.Adj x (p.getVert i))

@[simp] theorem mem_pathNeighborPositions (p : G.Walk a b) (x : V) (i : ℕ) :
    i ∈ pathNeighborPositions p x ↔ i ≤ p.length ∧ G.Adj x (p.getVert i) := by
  classical
  simp [pathNeighborPositions]

/-- Covering the entire neighborhood by a simple path preserves its exact
cardinality when vertices are replaced by their unique path positions. -/
theorem pathNeighborPositions_card (p : G.Walk a b) (hp : p.IsPath)
    (hcover : ∀ u, G.Adj x u → u ∈ p.support) :
    (pathNeighborPositions p x).card = (G.neighborSet x).ncard := by
  have hBij : Set.BijOn p.getVert (pathNeighborPositions p x : Set ℕ)
      (G.neighborSet x) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      exact (mem_pathNeighborPositions p x i).mp hi |>.2
    · intro i hi j hj hEq
      exact hp.getVert_injOn
        ((mem_pathNeighborPositions p x i).mp hi).1
        ((mem_pathNeighborPositions p x j).mp hj).1 hEq
    · intro u hu
      obtain ⟨i, hGet, hi⟩ := Walk.mem_support_iff_exists_getVert.mp (hcover u hu)
      refine ⟨i, (mem_pathNeighborPositions p x i).mpr ⟨hi, ?_⟩, hGet⟩
      simpa [hGet] using hu
  simpa using hBij.ncard_eq

/-- The interval from position i to position j, with the original endpoint
vertices rather than endpoints of an intermediate take/drop operation. -/
def pathInterval (p : G.Walk a b) (i j : ℕ) (hij : i ≤ j) :
    G.Walk (p.getVert i) (p.getVert j) :=
  ((p.take j).drop i).copy
    (by simp [Walk.take_getVert, Nat.min_eq_right hij]) rfl

theorem pathInterval_isPath (p : G.Walk a b) (hp : p.IsPath)
    (i j : ℕ) (hij : i ≤ j) : (pathInterval p i j hij).IsPath := by
  exact (Walk.isPath_copy _ _ _).mpr ((hp.take j).drop i)

theorem pathInterval_length (p : G.Walk a b) (i j : ℕ) (hij : i ≤ j)
    (hj : j ≤ p.length) : (pathInterval p i j hij).length = j - i := by
  simp [pathInterval, Walk.drop_length, Walk.take_length, Nat.min_eq_left hj]

theorem pathInterval_support_subset (p : G.Walk a b) (i j : ℕ) (hij : i ≤ j) :
    (pathInterval p i j hij).support ⊆ p.support := by
  intro y hy
  simp only [pathInterval, Walk.support_copy, Walk.drop_support_eq_support_drop_min,
    Walk.support_take] at hy
  exact List.mem_of_mem_take (List.mem_of_mem_drop hy)

/-- Two neighbors of an outside vertex, at distinct path positions,
give an actual simple cycle of length j-i+2. -/
theorem fan_cycle_witness (p : G.Walk a b) (hp : p.IsPath)
    (hx : x ∉ p.support) {i j : ℕ} (hij : i < j) (hj : j ≤ p.length)
    (hxi : G.Adj x (p.getVert i)) (hxj : G.Adj x (p.getVert j)) :
    ∃ q : G.Walk (p.getVert j) (p.getVert j),
      q.IsCycle ∧ q.length = j - i + 2 := by
  let r := pathInterval p i j hij.le
  have hr : r.IsPath := pathInterval_isPath p hp i j hij.le
  have hxr : x ∉ r.support := fun h ↦ hx (pathInterval_support_subset p i j hij.le h)
  have hPath : (Walk.cons hxi r).IsPath := hr.cons hxr
  have hrlen : r.length = j - i := pathInterval_length p i j hij.le hj
  refine ⟨Walk.cons hxj.symm (Walk.cons hxi r), ?_, ?_⟩
  · apply cycle_of_path_and_edge (Walk.cons hxi r) hPath hxj.symm
    simp only [Walk.length_cons]
    omega
  · simp only [Walk.length_cons, hrlen]

/-- Opposite-parity neighbor positions yield the corresponding original
odd simple-cycle length. -/
theorem fan_odd_cycle_length (p : G.Walk a b) (hp : p.IsPath)
    (hx : x ∉ p.support) {i j : ℕ} (hij : i < j) (hj : j ≤ p.length)
    (hxi : G.Adj x (p.getVert i)) (hxj : G.Adj x (p.getVert j))
    (hParity : i % 2 ≠ j % 2) : j - i + 2 ∈ G.oddCycleLengths := by
  obtain ⟨q, hq, hlen⟩ := fan_cycle_witness p hp hx hij hj hxi hxj
  refine ⟨⟨p.getVert j, q, hq, hlen⟩, ?_⟩
  rw [Nat.odd_iff]
  omega

end Erdos58
