# Erdős Problem 338 — standalone Palomar proof package

This package proves the Hegyvári–Hennecart–Plagne (2007) construction for Erdős Problem 338 on
restricted additive bases. The exported statement matches the declaration in the Formal
Conjectures file for the problem.

For every `k ≥ 2` there is a basis `A` of exact order `k` whose restricted order is
`2 ^ (k - 2) + k - 1`. The construction takes a finite dyadic core together with two residue
classes modulo `3 * 2 ^ (k - 2)`. The modular excess obstruction in the proof shows that no
smaller restricted order works.

## Files

- [Challenge.lean](Challenge.lean): the statement, with the order and restricted-order
  definitions and `sorry` proofs.
- [Solution.lean](Solution.lean): the same declaration, proved.
- [Proofs/Erdos338Unified435.lean](Proofs/Erdos338Unified435.lean): the proof development.
- [AxiomAudit.lean](AxiomAudit.lean): `#print axioms` for the exported theorem.
- [comparator.json](comparator.json), [formalization.yaml](formalization.yaml): manifest metadata.
- [BUILD.md](BUILD.md): build and verification commands.
- [THIRD_PARTY.md](THIRD_PARTY.md): attribution for Mathlib and Formal Conjectures.

## Verification

Run `./verify.sh` from this directory. It builds the package and confirms that both exported
theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`.
