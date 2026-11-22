import MathInfra.FormalizedElsewhere.EulerianNumber

/-!
# Axiom audit for `MathInfra.FormalizedElsewhere.EulerianNumber`

Every public theorem, with the axioms it depends on. `#guard_msgs` turns each line into a
check, so the build fails if any theorem starts depending on anything else (for example
`sorryAx`). Nothing here uses an axiom beyond Lean's three standard ones.
-/

set_option linter.style.longLine false

/-- info: 'eulerian_zero_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms eulerian_zero_zero

/-- info: 'eulerian_zero_succ' does not depend on any axioms -/
#guard_msgs in
#print axioms eulerian_zero_succ

/-- info: 'eulerian_succ_succ' does not depend on any axioms -/
#guard_msgs in
#print axioms eulerian_succ_succ

/-- info: 'eulerian_zero_right' does not depend on any axioms -/
#guard_msgs in
#print axioms eulerian_zero_right

/-- info: 'eulerian_eq_zero_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eulerian_eq_zero_of_le

/-- info: 'sum_eulerian_succ_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_eulerian_succ_smul

/-- info: 'eulerian_symm_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eulerian_symm_aux

/-- info: 'eulerian_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eulerian_symm

/-- info: 'eulerian_self_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eulerian_self_sub_one

/-- info: 'sum_eulerian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_eulerian

/-- info: 'eulerian_one_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eulerian_one_right

/-- info: 'mul_choose_add_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mul_choose_add_eq

/-- info: 'sum_eulerian_mul_choose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_eulerian_mul_choose

/-- info: 'coeff_eulerianPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms coeff_eulerianPoly

/-- info: 'eulerianPoly_eval_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eulerianPoly_eval_one

/-- info: 'coe_eulerianPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms coe_eulerianPoly

/-- info: 'eulerianPoly_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eulerianPoly_succ

/-- info: 'mk_pow_mul_one_sub_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mk_pow_mul_one_sub_pow

/-- info: 'PowerSeries.coeff_one_sub_X_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PowerSeries.coeff_one_sub_X_pow

/-- info: 'eulerian_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eulerian_eq_sum

/-- info: 'numDescents_nil' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in
#print axioms numDescents_nil

/-- info: 'numDescents_singleton' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in
#print axioms numDescents_singleton

/-- info: 'numDescents_cons_cons' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in
#print axioms numDescents_cons_cons

/-- info: 'numDescents_cons_of_lt' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in
#print axioms numDescents_cons_of_lt

/-- info: 'numDescents_permutations'Aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numDescents_permutations'Aux

/-- info: 'countP_permutations'Aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms countP_permutations'Aux

/-- info: 'countP_permutations'_reverse_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms countP_permutations'_reverse_range

/-- info: 'countP_permutations_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms countP_permutations_range

/-- info: 'card_perm_numDescents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_perm_numDescents
