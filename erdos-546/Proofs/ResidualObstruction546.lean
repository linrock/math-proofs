module

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

public import CopyGlue546
public import RamseyBasics546
public import DegreeDeletion546


@[expose] public section

/-! The exact high-degree deletion/copy obstruction in Sudakov Lemma 3.1.
The sparse-subset extraction and quantitative amplification are separate. -/

namespace Erdos546

open SimpleGraph Finset

theorem monoPair_card_lt_of_no_copy {V W : Type*} [Fintype V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) {X Y : Finset W}
    (hp : MonoPair H X Y) (hfree : ¬ G.IsContained H) :
    X.card < Fintype.card V := by
  by_contra hn
  exact hfree (isContained_of_clique G H X hp.2.1 (Nat.le_of_not_gt hn))

/-- In a graph-free monochromatic pair, choose as many deleted target vertices
as the pair's clique size. The remainder has small degree and cannot occur
inside the pair's reservoir, since such a copy would extend to the target. -/
theorem residual_obstruction_of_monoPair {V W : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W)
    {X Y : Finset W} (hp : MonoPair H X Y) (hfree : ¬ G.IsContained H) :
    ∃ A : Finset V, A.card = X.card ∧
      (∀ v : ↥((A : Set V)ᶜ),
        (X.card + 1) * (G.induce ((A : Set V)ᶜ)).degree v ≤ 2 * G.edgeFinset.card) ∧
      ¬ (G.induce ((A : Set V)ᶜ)).IsContained (H.induce (Y : Set W)) := by
  have hcard := monoPair_card_lt_of_no_copy G H hp hfree
  obtain ⟨A, hAcard, hdegree⟩ := exists_delete_card_induced_degree_bound G hcard.le
  refine ⟨A, hAcard, ?_, ?_⟩
  · simpa only [← hAcard] using hdegree
  · intro hcopy
    exact hfree (isContained_of_monoPair_deleted_copy G H A X Y hp hAcard.le hcopy)

end Erdos546
