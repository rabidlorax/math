import MathInfra.FormalizedElsewhere.KloostermanSum

/-!
# Axiom audit for `MathInfra.FormalizedElsewhere.KloostermanSum`

Every public theorem, with the axioms it depends on. `#guard_msgs` turns each line into a
check, so the build fails if any theorem starts depending on anything else (for example
`sorryAx`). Nothing here uses an axiom beyond Lean's three standard ones.
-/

set_option linter.style.longLine false

/-- info: 'kloostermanSum_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kloostermanSum_comm

/-- info: 'kloostermanSum_units_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kloostermanSum_units_mul

/-- info: 'kloostermanSum_units_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kloostermanSum_units_left

/-- info: 'kloostermanSum_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kloostermanSum_neg

/-- info: 'kloostermanSum_mulShift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kloostermanSum_mulShift

/-- info: 'kloostermanSum_zero_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kloostermanSum_zero_right

/-- info: 'kloostermanSum_zero_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kloostermanSum_zero_zero

/-- info: 'ZMod.mulCofactor_intCast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZMod.mulCofactor_intCast

/-- info: 'ZMod.castHom_mulCofactor_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZMod.castHom_mulCofactor_self

/-- info: 'ZMod.castHom_mulCofactor_of_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZMod.castHom_mulCofactor_of_dvd

/-- info: 'kloostermanSum_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kloostermanSum_mul

/-- info: 'kloostermanSum_stdAddChar_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kloostermanSum_stdAddChar_mul

/-- info: 'AddChar.IsPrimitive.isPrimitiveRoot_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AddChar.IsPrimitive.isPrimitiveRoot_one

/-- info: 'kloostermanSum_zero_right_eq_ramanujanSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kloostermanSum_zero_right_eq_ramanujanSum

/-- info: 'sum_kloostermanSum_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_kloostermanSum_left

/-- info: 'conj_kloostermanSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms conj_kloostermanSum

/-- info: 'kloostermanSum_im' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kloostermanSum_im

/-- info: 'AddChar.IsPrimitive.sum_mul_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AddChar.IsPrimitive.sum_mul_conj

/-- info: 'AddChar.IsPrimitive.sum_mul_conj_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AddChar.IsPrimitive.sum_mul_conj_sum

/-- info: 'sum_norm_kloostermanSum_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_norm_kloostermanSum_sq

/-- info: 'sum_norm_kloostermanSum_pow_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_norm_kloostermanSum_pow_four

/-- info: 'hyperbolaEnergy_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hyperbolaEnergy_le

/-- info: 'norm_kloostermanSum_pow_four_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_kloostermanSum_pow_four_le

/-- info: 'norm_kloostermanSum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_kloostermanSum_le
