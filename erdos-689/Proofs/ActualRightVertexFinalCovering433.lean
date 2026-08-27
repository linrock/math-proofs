import ActualRightVertexReduction433
import ThreePrimeMajorArcReduction433

/-!
# Original Erdős #689 covering from exactly its two remaining obligations

The actual fixed-right manuscript graph degree and prime-label degree are
already unconditional Lean theorems.  This combined PNT/AP-and-Selberg module
therefore derives the exact original covering statement from only the
genuine localized three-prime lower bound and the actual fixed-left graph
degree bound.  No right-degree, label-degree, sieve, seed, remainder,
matching, deficiency, or reserve hypothesis remains.
-/

namespace Erdos689

/-- The original prime-congruence covering problem follows from exactly
its remaining global localized three-prime major-arc theorem and actual
fixed-left vertex-degree theorem.  The other two graph-degree coordinates
are inserted from their complete unconditional kernel-checked proofs. -/
theorem officialStatement_of_localized_major_arcs_and_left_vertex_degree
    (hmajor : UniformLocalizedThreePrimeMajorArcLowerBound)
    (hleft : FixedModulusLeftVertexDegreeBound) :
    OfficialStatement := by
  exact officialStatement_of_weighted_prime_patterns_and_two_form_degree
    (uniformWeightedPrimePatternLowerBound_of_localized_major_arcs hmajor)
    (fixedModulusTwoFormDegreeBound_of_left_vertex_degree hleft)

#print axioms Erdos689.officialStatement_of_localized_major_arcs_and_left_vertex_degree

end Erdos689
