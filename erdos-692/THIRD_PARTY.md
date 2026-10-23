# Third-party notices

The files listed here are included under their original Apache-2.0 terms. All
other material in this package is Copyright 2026 Linmiao Xu and released under
the included [Apache-2.0 license](LICENSE).

| Included source | Upstream | License |
| --- | --- | --- |
| `Proofs/PlbyErdos692.lean` | [Pietro Monticone, *Lean proof of Erdős Problem 692*](https://gist.githubusercontent.com/pitmonticone/96516af9100a37a1da81908dc0b0410c/raw/a1d6ca7f3835c58b257e5e715c8fdf3a224e1bd0/Erdos692.lean), a gist linked as the `formal_proof` of `erdos_692.parts.i` in Formal Conjectures | Apache-2.0, original copyright notice retained |
| Definitions and target statement in `Statement.lean`, `Challenge.lean` and `Solution.lean` | [`FormalConjectures/ErdosProblems/692.lean`](https://github.com/google-deepmind/formal-conjectures/blob/0214b275653a2aa8fe5e44f01a0954723516801f/FormalConjectures/ErdosProblems/692.lean) at commit `0214b2756` | Apache-2.0, original copyright header retained |
| `Mathlib` | [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4) at `065356127b1dc0016f66b7283ce0ce2c4055aa55` | Apache-2.0, resolved by Lake |

`PlbyErdos692.lean` is a lightly adapted copy of the gist. It gains a `module`
header, `public import Mathlib`, the package's Apache-2.0 notice, and an enclosing
`namespace Erdos692`; the three Mathlib imports are consolidated into `Mathlib`.
The final theorem is renamed from `delta1_not_unimodal` to `erdos_692` so the
package namespace is consistent, and one docstring drops the year from
`(Cambie 2025)` to `(Cambie)`. The `#print axioms` line is removed because it
belongs in an audit rather than a library module; `AxiomAudit.lean` performs that
check. Monticone's copyright and authorship notice is retained verbatim,
including its credit for Lean proof assistance from Aristotle (Harmonic).

The main proof module, the density bridge from the Formal Conjectures definition
to the periodic residue counts, the uniqueness argument, and the small-`n`
endpoint results are not derived from any of the sources above.
