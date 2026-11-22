import MathInfra.FormalizedElsewhere.ZetaSeries

/-!
# Axiom audit for `MathInfra.FormalizedElsewhere.ZetaSeries`

Every public theorem, with the axioms it depends on. `#guard_msgs` turns each line into a
check, so the build fails if any theorem starts depending on anything else (for example
`sorryAx`). Nothing here uses an axiom beyond Lean's three standard ones.
-/

set_option linter.style.longLine false

/-- info: 'isZetaSeries_iff_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isZetaSeries_iff_coeff

/-- info: 'isZetaSeries_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isZetaSeries_zero

/-- info: 'IsZetaSeries.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsZetaSeries.mul

/-- info: 'IsZetaSeries.of_mul_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsZetaSeries.of_mul_eq_one

/-- info: 'IsZetaSeries.pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsZetaSeries.pow

/-- info: 'IsZetaSeries.prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsZetaSeries.prod

/-- info: 'isZetaSeries_geometric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isZetaSeries_geometric

/-- info: 'one_sub_X_pow_mul_cycInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms one_sub_X_pow_mul_cycInv

/-- info: 'ghostSeries_cycGhost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ghostSeries_cycGhost

/-- info: 'isZetaSeries_one_sub_X_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isZetaSeries_one_sub_X_pow

/-- info: 'isZetaSeries_cycInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isZetaSeries_cycInv

/-- info: 'isZetaSeries_cycFactor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isZetaSeries_cycFactor

/-- info: 'isZetaSeries_wittProd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isZetaSeries_wittProd

/-- info: 'Nat.filter_Icc_dvd_eq_divisors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Nat.filter_Icc_dvd_eq_divisors

/-- info: 'Nat.filter_Icc_dvd_succ_eq_properDivisors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Nat.filter_Icc_dvd_succ_eq_properDivisors

/-- info: 'IsZetaSeries.coeff_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsZetaSeries.coeff_eq

/-- info: 'IsZetaSeries.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsZetaSeries.unique

/-- info: 'exists_isZetaSeries_of_forall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_isZetaSeries_of_forall

/-- info: 'IsZetaSeries.dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsZetaSeries.dvd

/-- info: 'isGaussSeq_iff_exists_isZetaSeries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isGaussSeq_iff_exists_isZetaSeries

/-- info: 'one_sub_X_smul_mul_resolventSeries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms one_sub_X_smul_mul_resolventSeries

/-- info: 'trace_resolventSeries_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trace_resolventSeries_mul

/-- info: 'coe_charpolyRev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms coe_charpolyRev

/-- info: 'isZetaSeries_charpolyRev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isZetaSeries_charpolyRev

/-- info: 'isZetaSeries_trace_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isZetaSeries_trace_pow

/-- info: 'isGaussSeq_trace_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isGaussSeq_trace_pow

/-- info: 'trace_pow_modEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trace_pow_modEq

/-- info: 'trace_lucasMatrix_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trace_lucasMatrix_pow

/-- info: 'isGaussSeq_lucasV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isGaussSeq_lucasV

/-- info: 'exists_isZetaSeries_card_fixedPoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_isZetaSeries_card_fixedPoints

/-- info: 'coeff_wittProd_necklace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms coeff_wittProd_necklace
