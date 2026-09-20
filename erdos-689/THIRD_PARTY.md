# Provenance and licenses for Erdős 689

The locally authored material in this repository is released under the MIT
license in the repository-root `LICENSE`. This grant does not claim authorship
of prior mathematics or change the licenses of third-party sources.

Mathlib and its dependencies are obtained through the committed Git pins.
Their own licenses and attribution remain applicable.

The statement in `Challenge.lean`, `Solution.lean`, and
`Proofs/ActualOfficialSolution433.lean` restates the right-hand proposition of
[Formal Conjectures' Erdős #689 file](https://github.com/google-deepmind/formal-conjectures/blob/f19cf7f60d9bc650ff58462f540e236caf3a6a67/FormalConjectures/ErdosProblems/689.lean)
at revision `f19cf7f60d9bc650ff58462f540e236caf3a6a67`, with changed Lean syntax
and a proved positive theorem. The upstream source credits Copyright 2025 The
Formal Conjectures Authors and uses Apache-2.0. Its license is retained in
`third_party/FORMAL-CONJECTURES-LICENSE.txt`. The upstream statement is a
conjecture source, not an imported proof.

- architect: https://github.com/hanwenzhu/LeanArchitect at `78dd66840d3efe8c824c699fc03381cec817c271`, Apache-2.0.
  Full license: `third_party/ARCHITECT-LICENSE.txt`.
- blair: https://github.com/williamjblair/lean-proofs at `5d10b4d91f257cfbe8c563cf927f543a868845e0`, MIT.
  Full license: `third_party/BLAIR-LICENSE.txt`.
  Its NOTICE is retained. No Lindstrom.lean, Star Fleet archive, or other excluded proof is included.
- pnt: https://github.com/ajirving/PrimeNumberTheoremAnd at `769d3b81fbff001d9fa7028df0168a8e546cf692`, Apache-2.0.
  Full license: `third_party/PNT-LICENSE.txt`.
- principia: https://github.com/antoshashakov/Principia-Math-Solutions at `c9910942522fbd3a07c034ac57947f56df6f0f6d`, Apache-2.0.
  Full license: `third_party/PRINCIPIA-LICENSE.txt`.
  The included file is `Proofs/GoldbachChainMaster.lean`, a Lean 4.33.1
  compatibility port. Its analytic lemmas are reused in the Erdős 689
  three-prime development. The original and ported digests and patch are
  retained. The selected Erdős 689 result does not use the final almost-all
  Goldbach theorem.

Every `Proofs/` module has an individual origin and SHA-256 binding in
`source-manifest.json`. These are provenance hashes, not proof certificates.

The included upstream Wiener source contains two lemmas with `sorry`
placeholders: `prelim_decay_2` and `prelim_decay_3`. Neither is used by the
completed Erdős 689 proof. Its transitive axiom audit contains only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`. Local Comparator,
NanoDa, and Lean kernel checks have passed. [BUILD.md](BUILD.md) documents
their scope and the remaining official Palomar verification requirements.
