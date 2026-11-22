import MathInfra.FormalizedElsewhere.Wolstenholme

/-!
# Axiom audit for `MathInfra.FormalizedElsewhere.Wolstenholme`

Every public theorem, with the axioms it depends on. `#guard_msgs` turns each line into a
check, so the build fails if any theorem starts depending on anything else (for example
`sorryAx`). Nothing here uses an axiom beyond Lean's three standard ones.
-/

set_option linter.style.longLine false

/-- info: 'choose_prime_sub_one_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choose_prime_sub_one_cast

/-- info: 'choose_prime_div_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choose_prime_div_mul

/-- info: 'choose_prime_div_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choose_prime_div_cast

/-- info: 'sum_Ico_eq_sum_units' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_Ico_eq_sum_units

/-- info: 'sum_Ico_inv_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_Ico_inv_pow

/-- info: 'coeff_chooseDivPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms coeff_chooseDivPoly

/-- info: 'one_add_X_pow_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms one_add_X_pow_prime

/-- info: 'choose_mul_modEq_choose_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choose_mul_modEq_choose_sq

/-- info: 'choose_mul_modEq_choose_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choose_mul_modEq_choose_cube

/-- info: 'choose_two_mul_sub_one_modEq_one_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choose_two_mul_sub_one_modEq_one_sq

/-- info: 'choose_two_mul_sub_one_modEq_one_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choose_two_mul_sub_one_modEq_one_cube

/-- info: 'sum_Ico_inv_sq_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_Ico_inv_sq_eq_zero

/-- info: 'sum_Ico_inv_eq_zero_zmod_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_Ico_inv_eq_zero_zmod_sq

/-- info: 'sq_dvd_num_harmonic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sq_dvd_num_harmonic

/-- info: 'mul_fermatQuotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mul_fermatQuotient

/-- info: 'fermatQuotient_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fermatQuotient_mul

/-- info: 'fermatQuotient_mul_modEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fermatQuotient_mul_modEq

/-- info: 'fermatQuotient_add_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fermatQuotient_add_mul

/-- info: 'dvd_fermatQuotient_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dvd_fermatQuotient_iff

/-- info: 'two_mul_fermatQuotient_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_mul_fermatQuotient_two

/-- info: 'two_mul_fermatQuotient_two_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_mul_fermatQuotient_two_cast

/-- info: 'two_mul_fermatQuotient_two_eq_neg_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_mul_fermatQuotient_two_eq_neg_sum
