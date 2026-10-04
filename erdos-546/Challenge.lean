module

/-
Copyright 2026 The Formal Conjectures Authors.
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

Adaptation notice: Linmiao Xu adapted the Erdős 546 definitions and statement
from google-deepmind/formal-conjectures (`FormalConjectures/ErdosProblems/546.lean`
and `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Ramsey.lean`) and
added the explicit uniform `C = 4000` bound, genuine forcing witness, and
rounded Sudakov sparse-cut, low-density pair, and amplification targets for
this standalone Lean 4.35.0-rc2 benchmark in 2026. This file imports only
Mathlib.
-/

public import Mathlib


@[expose] public section

/-!
# Independent statements for Erdős Problem 546: sparse graph Ramsey numbers

For a finite simple graph $G$, write $R(G) = R(G, G)$ (`SimpleGraph.diagonalGraphRamsey G`)
for the minimum host order $n$ such that every $2$-coloring of $K_n$ contains a
monochromatic (not necessarily induced) copy of $G$. Erdős Problem 546 asks
whether there is an absolute constant $C > 0$ such that every finite graph $G$
with $m$ edges and no isolated vertices satisfies
$$R(G) \le 2^{C \sqrt{m}}.$$

Benny Sudakov (*Advances in Mathematics* 227 (2011), 601–609; arXiv:1002.0095)
proved this conjecture in the affirmative.

This Mathlib-only Challenge file reproduces the exact definitions
(`SimpleGraph.graphRamsey`, `SimpleGraph.diagonalGraphRamsey`) and statement from
`google-deepmind/formal-conjectures` (`FormalConjectures/ErdosProblems/546.lean`,
commit `6fbb54f24ccc2e64dcfaffc28c58950e377110d2`, SHA-256
`453e2ce29dc7533852d714ecf915da00d76fe8f242e5e9e627dff400a56caf1c`), together
with seven theorem targets:
1. `erdos_546_original_statement`: the literal Formal Conjectures `True ↔`
   theorem at root scope over arbitrary `V : Type` with `[Fintype V]`.
2. `Erdos546.erdos_546`: `True ↔ Erdos546.SparseRamseyStatement`.
3. `Erdos546.sudakov_sparse_bound`: the uniform explicit bound
   $R(G) \le 2^{4000 \sqrt{m}}$ across all finite simple graphs $G$ on any
   `V : Type*` without isolated vertices and with $m$ edges (including $m = 0$).
4. `Erdos546.sparse_graph_ramsey_witness`: the genuine forcing witness
   (`GraphRamseyWitness G G ⌈2^{2000\sqrt{m}}⌉₊`) for any finite graph $G$ on
   $V$ with $m \ge 64$ edges (`G.edgeSet.ncard = m`) and $|V| \le 2m$, ruling
   out vacuous `sInf ∅ = 0` collapse.
5. `Erdos546.boundedDegree_sparse_cut`: the rounded Sudakov Lemma 2.4
   bounded-degree embedding contrapositive: for $0 < \varepsilon \le 1/2$, if
   every vertex of $G$ has degree $\le \Delta$, the host $W$ satisfies the
   large-host condition $2(\Delta + 1)|V| \le \varepsilon^\Delta |W|$, and $H$
   contains no copy of $G$ (`¬ Nonempty (SimpleGraph.Copy G H)`), then $W$
   contains disjoint equal-cardinality sets $X, Y$ of size
   $\ge \varepsilon^\Delta |W| / (2(\Delta + 1))$ with interedge count
   $\le \varepsilon |X| |Y|$.
6. `Erdos546.exists_monoPair_of_low_edgeDensity`: the rounded Sudakov Lemma 2.3
   low-density monochromatic-pair theorem: for $0 < \varepsilon \le 1/8$ and
   $t \in \mathbb{N}$ with $1 \le \varepsilon t$, if a vertex subset
   $U \subseteq V$ satisfies the size condition
   $t \le \varepsilon^{40\varepsilon t} |U|$ and has edge density
   $\operatorname{edgeDensity}_H(U, U) \le \varepsilon$, then $U$ contains a
   monochromatic pair $(X, Y)$ in $H$ or $H^c$ with $|X| = t$ and
   $|Y| \ge \varepsilon^{40\varepsilon t} |U|$.
7. `Erdos546.quantitative_monoPair_amplification`: the Sudakov Section 3
   quantitative clique/reservoir amplification step: for $m \ge 64$, a graph
   $G$ with $m$ edges and $|V| \le 2m$, an integer scale
   $3 \le a \le \lfloor \frac{1}{2}\log_2 m \rfloor$, and a monochromatic pair
   $(X, Y)$ in a $G$-free host $H$ with $|X| \ge a^3\sqrt{m}$ and
   $|Y| \ge 2^{500\sqrt{m}/a}$, there exists a monochromatic pair $(P, Q)$ in
   $Y$ (in $H$ or $H^c$) with $|P| \ge 2^{2a}\sqrt{m}$ and
   $|Q| \ge |Y| \cdot 2^{-400\sqrt{m}/a}$.

The seven intentional `sorry` placeholders below are matched by proved
declarations in `Solution.lean`; `Solution.lean` does not import this module.
-/

namespace SimpleGraph

/-- The two-color Ramsey number `graphRamsey G H`: the minimum number of vertices `n`
such that every 2-coloring of the edges of `K_n` contains a copy of `G` in the first
color (`C`) or a copy of `H` in the second color (`Cᶜ`). -/
noncomputable def graphRamsey {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  sInf { n : ℕ | ∀ (C : SimpleGraph (Fin n)), G.IsContained C ∨ H.IsContained Cᶜ }

/-- The diagonal graph Ramsey number `R(G) = R(G, G)`. -/
noncomputable def diagonalGraphRamsey {α : Type*} [Fintype α] (G : SimpleGraph α) : ℕ :=
  graphRamsey G G

end SimpleGraph

namespace Erdos546

open SimpleGraph Finset

/-- All edges within `X` and from `X` to its disjoint reservoir `Y` belong to `H`. -/
def MonoPair {V : Type*} (H : SimpleGraph V) (X Y : Finset V) : Prop :=
  Disjoint X Y ∧ H.IsClique (X : Set V) ∧ ∀ x ∈ X, ∀ y ∈ Y, H.Adj x y

/-- The exact property whose least natural witness is `graphRamsey G H`. -/
def GraphRamseyWitness {α β : Type*} (G : SimpleGraph α) (H : SimpleGraph β)
    (n : ℕ) : Prop :=
  ∀ C : SimpleGraph (Fin n), G.IsContained C ∨ H.IsContained Cᶜ

/-- The exact quantifiers requested in the Formal Conjectures #546 theorem. -/
def SparseRamseyStatement : Prop :=
  ∃ C > (0 : ℝ), ∀ (m : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v, 0 < G.degree v) → G.edgeSet.ncard = m →
      (SimpleGraph.diagonalGraphRamsey G : ℝ) ≤ 2 ^ (C * Real.sqrt m)

/-- The final integer amplification parameter $\lfloor \frac{1}{2} \log_2 m \rfloor$. -/
def finalAmplificationParameter546 (m : ℕ) : ℕ := Nat.log2 m / 2

/-- Genuine forcing witness on $\lceil 2^{2000\sqrt{m}} \rceil$ vertices for all $m \ge 64$
when $G$ has $m$ edges and $|V| \le 2m$. -/
theorem sparse_graph_ramsey_witness {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) (hm : 64 ≤ m)
    (hedges : G.edgeSet.ncard = m) (hvertices : Fintype.card V ≤ 2 * m) :
    GraphRamseyWitness G G (Nat.ceil ((2 : ℝ) ^ (2000 * Real.sqrt m))) := by
  sorry

/-- Uniform explicit sparse graph Ramsey bound with absolute constant $C = 4000$. -/
theorem sudakov_sparse_bound {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ)
    (hno : ∀ v, 0 < G.degree v) (hedges : G.edgeSet.ncard = m) :
    (SimpleGraph.diagonalGraphRamsey G : ℝ) ≤ (2 : ℝ) ^ (4000 * Real.sqrt m) := by
  sorry

/-- The original uniform quantifiers (`True ↔ SparseRamseyStatement`). -/
theorem erdos_546 : True ↔ SparseRamseyStatement := by
  sorry

open scoped Classical in
/-- Rounded Sudakov Lemma 2.4 bounded-degree embedding contrapositive: for
$0 < \varepsilon \le 1/2$, maximum degree $\le \Delta$, large host size
$2(\Delta + 1)|V| \le \varepsilon^\Delta |W|$, and no copy of $G$ in $H$, there
exist disjoint equal-size subsets $X, Y \subseteq W$ of cardinality
$\ge \varepsilon^\Delta |W| / (2(\Delta + 1))$ with at most
$\varepsilon |X| |Y|$ cross edges. -/
theorem boundedDegree_sparse_cut {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (Δ : ℕ) (ε : ℝ) (hε : 0 < ε) (hhalf : ε ≤ 1 / 2)
    (hdegree : ∀ v, G.degree v ≤ Δ)
    (hlarge : 2 * (Δ + 1 : ℝ) * Fintype.card V ≤ ε ^ Δ * Fintype.card W)
    (hfree : ¬ Nonempty (SimpleGraph.Copy G H)) :
    ∃ X Y : Finset W, Disjoint X Y ∧ X.card = Y.card ∧
      ε ^ Δ * Fintype.card W / (2 * (Δ + 1 : ℝ)) ≤ (X.card : ℝ) ∧
      ε ^ Δ * Fintype.card W / (2 * (Δ + 1 : ℝ)) ≤ (Y.card : ℝ) ∧
      ((H.interedges X Y).card : ℝ) ≤ ε * X.card * Y.card := by
  sorry

/-- Rounded Sudakov Lemma 2.3 low-density monochromatic-pair theorem: for
$0 < \varepsilon \le 1/8$, $1 \le \varepsilon t$, set size
$t \le \varepsilon^{40\varepsilon t}|U|$, and edge density
$\operatorname{edgeDensity}_H(U, U) \le \varepsilon$, there exists a
monochromatic pair $(X, Y)$ in $U$ (in $H$ or $H^c$) with $|X| = t$ and
$|Y| \ge \varepsilon^{40\varepsilon t}|U|$. -/
theorem exists_monoPair_of_low_edgeDensity {V : Type*} [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (U : Finset V) (ε : ℝ) (t : ℕ)
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 8) (hεt : 1 ≤ ε * t)
    (hsize : (t : ℝ) ≤ Real.rpow ε (40 * ε * t) * U.card)
    (hdensity : (H.edgeDensity U U : ℝ) ≤ ε) :
    ∃ X Y : Finset V, X ⊆ U ∧ Y ⊆ U ∧
      (MonoPair H X Y ∨ MonoPair Hᶜ X Y) ∧ X.card = t ∧
      Real.rpow ε (40 * ε * t) * U.card ≤ (Y.card : ℝ) := by
  sorry

/-- Quantitative monochromatic-pair amplification step (Sudakov Section 3): for
$m \ge 64$, $|E(G)| = m$, $|V| \le 2m$, and scale
$3 \le a \le \lfloor \frac{1}{2}\log_2 m \rfloor$, a monochromatic pair
$(X, Y)$ in a $G$-free host $H$ with $|X| \ge a^3\sqrt{m}$ and
$|Y| \ge 2^{500\sqrt{m}/a}$ yields a monochromatic pair $(P, Q)$ inside $Y$
(in $H$ or $H^c$) with $|P| \ge 2^{2a}\sqrt{m}$ and
$|Q| \ge |Y| \cdot 2^{-400\sqrt{m}/a}$. -/
theorem quantitative_monoPair_amplification {V W : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W)
    (m a : ℕ) (hm : 64 ≤ m) (hedges : G.edgeSet.ncard = m)
    (hvertices : Fintype.card V ≤ 2 * m)
    (ha : 3 ≤ a) (haA : a ≤ finalAmplificationParameter546 m)
    {X Y : Finset W} (hp : MonoPair H X Y)
    (hfree : ¬ G.IsContained H)
    (hX : (a : ℝ) ^ 3 * Real.sqrt m ≤ X.card)
    (hY : Real.rpow 2 (500 * Real.sqrt m / a) ≤ Y.card) :
    ∃ P Q : Finset W, P ⊆ Y ∧ Q ⊆ Y ∧
      (MonoPair H P Q ∨ MonoPair Hᶜ P Q) ∧
      (2 : ℝ) ^ (2 * a) * Real.sqrt m ≤ P.card ∧
      (Y.card : ℝ) * Real.rpow 2 (-400 * Real.sqrt m / a) ≤ Q.card := by
  sorry

end Erdos546

/-- Literal statement check against `FormalConjectures/ErdosProblems/546.lean`,
with `answer(True)` elaborated as `True`. -/
theorem erdos_546_original_statement : True ↔
    ∃ C > (0 : ℝ), ∀ (m : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V)
      [DecidableRel G.Adj],
      (∀ v, 0 < G.degree v) →
      G.edgeSet.ncard = m →
      (SimpleGraph.diagonalGraphRamsey G : ℝ) ≤ 2 ^ (C * Real.sqrt m) := by
  sorry
