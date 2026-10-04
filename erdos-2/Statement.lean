module

public import CoveringSystem2
public import Mathlib.RingTheory.Ideal.Span


@[expose] public section

/-!
The exact Erdős #2 statement, using the Apache-2.0 Formal Conjectures covering
structures in `CoveringSystem2`. This is a proposition definition, with no
admitted theorem. The elaborated `answer(False)` is written as `False`.
-/

namespace Erdos2.Challenge

def statement : Prop :=
  False ↔
    ∀ B : ℕ, ∃ c : StrictCoveringSystem ℤ, ∀ i, ∃ m : ℕ,
      c.moduli i = Ideal.span {(m : ℤ)} ∧ B < m

end Erdos2.Challenge
