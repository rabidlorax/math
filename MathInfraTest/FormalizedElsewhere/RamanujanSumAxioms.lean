import MathInfra.FormalizedElsewhere.RamanujanSum

/-!
# Axiom audit for `MathInfra.FormalizedElsewhere.RamanujanSum`

Every public theorem, with the axioms it depends on. `#guard_msgs` turns each line into a
check, so the build fails if any theorem starts depending on anything else (for example
`sorryAx`). Nothing here uses an axiom beyond Lean's three standard ones.
-/

set_option linter.style.longLine false

/-- info: 'ramanujanSum_zero_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ramanujanSum_zero_left

/-- info: 'ramanujanSum_one_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ramanujanSum_one_left

/-- info: 'ramanujanSum_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ramanujanSum_congr

/-- info: 'ramanujanSum_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ramanujanSum_neg

/-- info: 'ramanujanSum_eq_sum_divisorsAntidiagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ramanujanSum_eq_sum_divisorsAntidiagonal

/-- info: 'sum_ramanujanSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_ramanujanSum

/-- info: 'eq_ramanujanSum_of_sum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq_ramanujanSum_of_sum_eq

/-- info: 'ramanujanSum_zero_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ramanujanSum_zero_right

/-- info: 'ramanujanSum_of_isCoprime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ramanujanSum_of_isCoprime

/-- info: 'ramanujanSum_one_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ramanujanSum_one_right

/-- info: 'ramanujanSum_prime_pow_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ramanujanSum_prime_pow_succ

/-- info: 'ramanujanSum_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ramanujanSum_prime

/-- info: 'ramanujanSum_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ramanujanSum_mul

/-- info: 'ramanujanSum_mul_totient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ramanujanSum_mul_totient

/-- info: 'ramanujanSum_eq_moebius_mul_totient_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ramanujanSum_eq_moebius_mul_totient_div

/-- info: 'IsPrimitiveRoot.sum_nthRootsFinset_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsPrimitiveRoot.sum_nthRootsFinset_pow

/-- info: 'IsPrimitiveRoot.sum_primitiveRoots_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsPrimitiveRoot.sum_primitiveRoots_pow

/-- info: 'IsPrimitiveRoot.sum_pow_coprime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsPrimitiveRoot.sum_pow_coprime

/-- info: 'ramanujanSum_eq_sum_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ramanujanSum_eq_sum_exp
