# Erdős 501: Erdős–Hajnal finite independent sets for small outer measure

This standalone Lean 4 (`leanprover/lean4:v4.35.0-rc2`) package formalizes the Erdős–Hajnal (1960)
finite independent-set theorem for Erdős Problem 501 (`Erdos501.erdos_501.variants.erdosHajnal_finite`
in `FormalConjectures/ErdosProblems/501.lean`):

For every $n \in \mathbb{N}$ and every family $A : \mathbb{R} \to \mathcal{P}(\mathbb{R})$ of bounded
subsets of $\mathbb{R}$ with Lebesgue outer measure $< 1$, there exists a finite set
$X \subseteq \mathbb{R}$ with $|X| \ge n$ that is pairwise independent for $A$ ($x \notin A(y)$ for
all distinct $x, y \in X$).

## Package Structure

- [Challenge.lean](Challenge.lean): Target theorem statement with `sorry` body.
- [Solution.lean](Solution.lean): Proved target theorem matching [Challenge.lean](Challenge.lean).
- [AxiomAudit.lean](AxiomAudit.lean): `#print axioms` check for the exported theorem.
- [Proofs/ErdosHajnalFinite501.lean](Proofs/ErdosHajnalFinite501.lean): Complete finite-induction proof.
- [BUILD.md](BUILD.md): Build and verification instructions (`./verify.sh`).
- [THIRD_PARTY.md](THIRD_PARTY.md): Attribution and license notices.
