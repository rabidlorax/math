import MathInfra.DedekindSum

/-!
# Axiom audit for `MathInfra.DedekindSum`

Every public theorem, with the axioms it depends on. `#guard_msgs` turns each line into a
check, so the build fails if any theorem starts depending on anything else (for example
`sorryAx`). Nothing here uses an axiom beyond Lean's three standard ones.
-/

set_option linter.style.longLine false

/-- info: 'sawtooth_add_intCast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sawtooth_add_intCast

/-- info: 'sawtooth_intCast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sawtooth_intCast

/-- info: 'sawtooth_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sawtooth_zero

/-- info: 'sawtooth_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sawtooth_neg

/-- info: 'sawtooth_eq_ite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sawtooth_eq_ite

/-- info: 'abs_sawtooth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_sawtooth_le

/-- info: 'sawtooth_natCast_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sawtooth_natCast_div

/-- info: 'sum_sawtooth_add_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_sawtooth_add_div

/-- info: 'sawtoothZMod_intCast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sawtoothZMod_intCast

/-- info: 'dedekindSum_zero_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dedekindSum_zero_right

/-- info: 'dedekindSum_one_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dedekindSum_one_right

/-- info: 'dedekindSum_zero_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dedekindSum_zero_left

/-- info: 'dedekindSum_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dedekindSum_neg

/-- info: 'dedekindSum_eq_sum_zmod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dedekindSum_eq_sum_zmod

/-- info: 'dedekindSum_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dedekindSum_congr

/-- info: 'dedekindSum_of_mul_modEq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dedekindSum_of_mul_modEq_one

/-- info: 'dedekindSum_eq_zero_of_sq_modEq_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dedekindSum_eq_zero_of_sq_modEq_neg_one

/-- info: 'dedekindSum_mul_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dedekindSum_mul_mul

/-- info: 'dedekindSum_eq_sum_mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dedekindSum_eq_sum_mod

/-- info: 'dedekindSum_reciprocity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dedekindSum_reciprocity

/-- info: 'exists_six_mul_dedekindSum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_six_mul_dedekindSum_eq

/-- info: 'exists_twelve_mul_dedekindSum_modEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_twelve_mul_dedekindSum_modEq

/-- info: 'dedekindSum_one_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dedekindSum_one_left

/-- info: 'dedekindSum_two_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dedekindSum_two_left

/-- info: 'abs_dedekindSum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_dedekindSum_le
