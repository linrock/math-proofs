module

public import SpliceProvider.FanCycle58

@[expose] public section

/-! Simple-path and cycle splicing with explicit support intersections. -/

namespace Erdos58

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {a b c : V}

theorem path_start_notMem_tail (p : G.Walk a b) (hp : p.IsPath) :
    a ∉ p.support.tail := by
  have hn := hp.support_nodup
  rw [← Walk.cons_tail_support] at hn
  exact (List.nodup_cons.mp hn).1

theorem path_append_of_meet_only (p : G.Walk a b) (q : G.Walk b c)
    (hp : p.IsPath) (hq : q.IsPath)
    (hmeet : ∀ z, z ∈ p.support → z ∈ q.support → z = b) :
    (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append]
  apply hp.support_nodup.append hq.support_nodup.tail
  intro z hz₁ hz₂
  have hzb := hmeet z hz₁ (List.mem_of_mem_tail hz₂)
  exact path_start_notMem_tail q hq (hzb ▸ hz₂)

theorem cycle_of_two_paths (p q : G.Walk a b) (hp : p.IsPath) (hq : q.IsPath)
    (hmeet : ∀ z, z ∈ p.support → z ∈ q.support → z = a ∨ z = b)
    (hlen : 3 ≤ p.length + q.length) :
    (p.append q.reverse).IsCycle := by
  apply hp.isCycle_append hq.reverse
  · intro z hz₁ hz₂
    have hzp := List.mem_of_mem_tail hz₁
    have hzq : z ∈ q.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using List.mem_of_mem_tail hz₂
    rcases hmeet z hzp hzq with hza | hzb
    · exact path_start_notMem_tail p hp (hza ▸ hz₁)
    · exact path_start_notMem_tail q.reverse hq.reverse (hzb ▸ hz₂)
  · rw [Walk.length_reverse]
    omega

theorem two_paths_cycle_length (p q : G.Walk a b) :
    (p.append q.reverse).length = p.length + q.length := by simp

end Erdos58
