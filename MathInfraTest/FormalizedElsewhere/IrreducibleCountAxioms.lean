import MathInfra.FormalizedElsewhere.IrreducibleCount

/-!
# Axiom audit for `MathInfra.FormalizedElsewhere.IrreducibleCount`

Every public theorem, with the axioms it depends on. `#guard_msgs` turns each line into a
check, so the build fails if any theorem starts depending on anything else (for example
`sorryAx`). Nothing here uses an axiom beyond Lean's three standard ones.
-/

set_option linter.style.longLine false

/-- info: 'finite_setOf_monic_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finite_setOf_monic_irreducible

/-- info: 'mem_monicIrreducibles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_monicIrreducibles

/-- info: 'monicIrreducibles_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms monicIrreducibles_zero

/-- info: 'separable_X_pow_card_pow_sub_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms separable_X_pow_card_pow_sub_X

/-- info: 'prod_prod_monicIrreducibles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prod_prod_monicIrreducibles

/-- info: 'sum_mul_card_monicIrreducibles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_mul_card_monicIrreducibles

/-- info: 'mul_card_monicIrreducibles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mul_card_monicIrreducibles

/-- info: 'card_monicIrreducibles_eq_necklace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_monicIrreducibles_eq_necklace

/-- info: 'card_monicIrreducibles_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_monicIrreducibles_one

/-- info: 'card_monicIrreducibles_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_monicIrreducibles_prime

/-- info: 'mul_card_monicIrreducibles_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mul_card_monicIrreducibles_le

/-- info: 'Nat.le_div_two_of_mem_properDivisors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Nat.le_div_two_of_mem_properDivisors

/-- info: 'lt_mul_card_monicIrreducibles_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lt_mul_card_monicIrreducibles_add

/-- info: 'card_monicIrreducibles_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_monicIrreducibles_pos

/-- info: 'exists_monic_irreducible_natDegree_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_monic_irreducible_natDegree_eq
