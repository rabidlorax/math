import MathInfra.FormalizedElsewhere.QAnalog

/-!
# Axiom audit for `MathInfra.FormalizedElsewhere.QAnalog`

Every public theorem, with the axioms it depends on. `#guard_msgs` turns each line into a
check, so the build fails if any theorem starts depending on anything else (for example
`sorryAx`). Three theorems hold by definition and use no axioms at all.
-/

set_option linter.style.longLine false

/-- info: 'qNat_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qNat_zero

/-- info: 'qNat_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qNat_one

/-- info: 'qNat_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qNat_succ

/-- info: 'qNat_succ'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qNat_succ'

/-- info: 'qNat_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qNat_add

/-- info: 'qNat_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qNat_mul

/-- info: 'qNat_one_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qNat_one_left

/-- info: 'qNat_zero_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qNat_zero_left

/-- info: 'map_qNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms map_qNat

/-- info: 'sub_one_mul_qNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sub_one_mul_qNat

/-- info: 'qFactorial_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qFactorial_zero

/-- info: 'qFactorial_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qFactorial_succ

/-- info: 'qFactorial_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qFactorial_one

/-- info: 'qFactorial_one_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qFactorial_one_left

/-- info: 'qFactorial_zero_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qFactorial_zero_left

/-- info: 'map_qFactorial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms map_qFactorial

/-- info: 'gaussBinom_zero_right' does not depend on any axioms -/
#guard_msgs in
#print axioms gaussBinom_zero_right

/-- info: 'gaussBinom_zero_succ' does not depend on any axioms -/
#guard_msgs in
#print axioms gaussBinom_zero_succ

/-- info: 'gaussBinom_succ_succ' does not depend on any axioms -/
#guard_msgs in
#print axioms gaussBinom_succ_succ

/-- info: 'gaussBinom_eq_zero_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gaussBinom_eq_zero_of_lt

/-- info: 'gaussBinom_succ_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gaussBinom_succ_self

/-- info: 'gaussBinom_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gaussBinom_self

/-- info: 'gaussBinom_one_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gaussBinom_one_right

/-- info: 'gaussBinom_one_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gaussBinom_one_left

/-- info: 'gaussBinom_zero_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gaussBinom_zero_left

/-- info: 'map_gaussBinom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms map_gaussBinom

/-- info: 'gaussBinom_succ_succ'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gaussBinom_succ_succ'

/-- info: 'gaussBinom_symm_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gaussBinom_symm_add

/-- info: 'gaussBinom_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gaussBinom_symm

/-- info: 'gaussBinom_succ_self_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gaussBinom_succ_self_right

/-- info: 'qNat_succ_mul_gaussBinom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qNat_succ_mul_gaussBinom

/-- info: 'qNat_succ_mul_gaussBinom_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qNat_succ_mul_gaussBinom_succ

/-- info: 'add_gaussBinom_mul_qFactorial_mul_qFactorial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms add_gaussBinom_mul_qFactorial_mul_qFactorial

/-- info: 'gaussBinom_mul_qFactorial_mul_qFactorial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gaussBinom_mul_qFactorial_mul_qFactorial

/-- info: 'gaussBinom_eq_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gaussBinom_eq_div

/-- info: 'prod_one_add_pow_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prod_one_add_pow_mul

/-- info: 'one_add_pow_eq_sum_choose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms one_add_pow_eq_sum_choose

/-- info: 'gaussBinom_X_monic_and_natDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gaussBinom_X_monic_and_natDegree

/-- info: 'gaussBinom_X_monic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gaussBinom_X_monic

/-- info: 'gaussBinom_X_natDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gaussBinom_X_natDegree

/-- info: 'aeval_gaussBinom_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aeval_gaussBinom_X

/-- info: 'aeval_qNat_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aeval_qNat_X

/-- info: 'aeval_qFactorial_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aeval_qFactorial_X

/-- info: 'eval_gaussBinom_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_gaussBinom_X

/-- info: 'eval_qNat_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_qNat_X

/-- info: 'eval_qFactorial_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_qFactorial_X

/-- info: 'Nat.cast_qNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Nat.cast_qNat

/-- info: 'Int.cast_qNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Int.cast_qNat

/-- info: 'Nat.cast_qFactorial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Nat.cast_qFactorial

/-- info: 'Int.cast_qFactorial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Int.cast_qFactorial

/-- info: 'Nat.cast_gaussBinom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Nat.cast_gaussBinom

/-- info: 'Int.cast_gaussBinom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Int.cast_gaussBinom
