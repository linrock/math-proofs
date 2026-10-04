module

public import ActualLeftVertexFinal433
public import ActualMajorArcPrimeMinor433

@[expose] public section


/-!
# Exact original covering reduced to its sole remaining major-arc theorem

The complete original three-coordinate graph-degree bound is unconditional:
fixed-left degree `455`, fixed-right degree `243`, and prime-label degree
`122`.  The actual coefficient-summed prime-only minor arcs are also
unconditionally negligible.  Consequently the original Erdős #689 covering
statement now depends on exactly ONE mathematical input: positivity of the
actual full coefficient-summed prime-only major region, equivalently the
localized three-prime lower bound.  No sieve, determinant, selector,
degree, minor, matching, reserve, or deficiency premise survives.
-/

namespace Erdos689

/-- The original prime-congruence covering statement follows solely from
the genuine localized three-prime lower bound; the entire original graph
degree theorem is inserted from its unconditional Lean proof. -/
theorem officialStatement_of_localized_major_arcs
    (hmajor : UniformLocalizedThreePrimeMajorArcLowerBound) :
    OfficialStatement := by
  exact officialStatement_of_weighted_prime_patterns_and_two_form_degree
    (uniformWeightedPrimePatternLowerBound_of_localized_major_arcs hmajor)
    fixedModulusTwoFormDegreeBound_unconditional

/-- EXACT SINGLE-INPUT FINAL REDUCTION: the original Erdős #689 statement
follows from positivity of its actual coefficient-summed prime-only major
arcs alone.  All original minor-arc and graph-degree obligations are proved. -/
theorem officialStatement_of_actual_summed_major_positivity
    (hmajor : UniformActualCoefficientSummedMajorArcPositivity) :
    OfficialStatement := by
  exact officialStatement_of_localized_major_arcs
    (uniformLocalizedThreePrimeMajorArcLowerBound_of_actual_summed_major_positivity
      hmajor)

#print axioms Erdos689.officialStatement_of_localized_major_arcs
#print axioms Erdos689.officialStatement_of_actual_summed_major_positivity

end Erdos689
