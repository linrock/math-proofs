module

public import Solution
public import Statement

@[expose] public section


/-!
Full statement, fidelity, and transitive-axiom checks for the submitted
Erdős #1054 endpoints. Only `propext`, `Classical.choice`, and `Quot.sound`
are permitted.
-/

namespace Erdos1054.Palomar

/-- The separately stated Part (i) target in `Statement.lean` is definitionally the proved proposition. -/
theorem statement_i_fidelity : Erdos1054.Challenge.statement_i :=
  Erdos1054.Palomar.official_answer_i

/-- The separately stated Part (ii) target in `Statement.lean` is definitionally the proved proposition. -/
theorem statement_ii_fidelity : Erdos1054.Challenge.statement_ii :=
  Erdos1054.Palomar.official_answer_ii

/-- The separately stated Part (iii) target in `Statement.lean` is definitionally the proved proposition. -/
theorem statement_iii_fidelity : Erdos1054.Challenge.statement_iii :=
  Erdos1054.Palomar.official_answer_iii

end Erdos1054.Palomar

#print Erdos1054.Palomar.answer_i
#print Erdos1054.Palomar.answer_ii
#print Erdos1054.Palomar.answer_iii
#print Erdos1054.Palomar.official_answer_i
#print Erdos1054.Palomar.official_answer_ii
#print Erdos1054.Palomar.official_answer_iii
#print Erdos1054.Palomar.limsup_on_every_density_one
#print Erdos1054.Palomar.quantitative_odd_sharp_second_moment_logarithmic_endpoint
#print Erdos1054.Palomar.littleO_on_subtype_imp_represented_density_zero
#print Erdos1054.Palomar.cofactor_two_lower_density_eq_even_aliquot
#print axioms Erdos1054.Palomar.answer_i
#print axioms Erdos1054.Palomar.answer_ii
#print axioms Erdos1054.Palomar.answer_iii
#print axioms Erdos1054.Palomar.official_answer_i
#print axioms Erdos1054.Palomar.official_answer_ii
#print axioms Erdos1054.Palomar.official_answer_iii
#print axioms Erdos1054.Palomar.limsup_on_every_density_one
#print axioms Erdos1054.Palomar.odd_subtype_limsup
#print axioms Erdos1054.Palomar.f_undefined_at_2
#print axioms Erdos1054.Palomar.f_undefined_at_5
#print axioms Erdos1054.Palomar.quantitative_odd_sharp_second_moment_logarithmic_endpoint
#print axioms Erdos1054.Palomar.quantitative_odd_sharp_second_moment_logarithmic_endpoint_eventual_count
#print axioms Erdos1054.Palomar.quantitative_odd_almost_full_three_plus_epsilon
#print axioms Erdos1054.Palomar.quantitative_odd_pure_power_six
#print axioms Erdos1054.Palomar.small_ratio_count_le_cubic
#print axioms Erdos1054.Palomar.small_ratio_upper_density_le_cubic
#print axioms Erdos1054.Palomar.littleO_on_subtype_imp_represented_density_zero
#print axioms Erdos1054.Palomar.f_sigma_le
#print axioms Erdos1054.Palomar.frequently_represented_small_ratio
#print axioms Erdos1054.Palomar.cofactor_two_lower_density_eq_even_aliquot
#print axioms Erdos1054.Palomar.cofactor_two_upper_density_eq_even_aliquot
#print axioms Erdos1054.Palomar.statement_i_fidelity
#print axioms Erdos1054.Palomar.statement_ii_fidelity
#print axioms Erdos1054.Palomar.statement_iii_fidelity
