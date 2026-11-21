import MathInfra.GaussSeq

/-!
# Axiom audit for `MathInfra.GaussSeq`

Every public theorem, with the axioms it depends on. `#guard_msgs` turns each line into a
check, so the build fails if any theorem starts depending on anything else (for example
`sorryAx`). Nothing here uses an axiom beyond Lean's three standard ones.
-/

set_option linter.style.longLine false

/-- info: 'sum_sum_moebius_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_sum_moebius_mul

/-- info: 'sum_moebius_mul_eq_of_sum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_moebius_mul_eq_of_sum_eq

/-- info: 'orbitCount_eq_of_sum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms orbitCount_eq_of_sum_eq

/-- info: 'IsGaussSeq.mul_orbitCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsGaussSeq.mul_orbitCount

/-- info: 'IsGaussSeq.sum_mul_orbitCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsGaussSeq.sum_mul_orbitCount

/-- info: 'isGaussSeq_iff_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isGaussSeq_iff_exists

/-- info: 'Nat.Prime.pow_dvd_of_dvd_mul_of_not_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Nat.Prime.pow_dvd_of_dvd_mul_of_not_dvd

/-- info: 'isGaussSeq_iff_modEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isGaussSeq_iff_modEq

/-- info: 'mem_gaussSubring' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_gaussSubring

/-- info: 'isGaussSeq_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isGaussSeq_const

/-- info: 'IsGaussSeq.add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsGaussSeq.add

/-- info: 'IsGaussSeq.neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsGaussSeq.neg

/-- info: 'IsGaussSeq.sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsGaussSeq.sub

/-- info: 'IsGaussSeq.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsGaussSeq.mul

/-- info: 'IsGaussSeq.comp_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsGaussSeq.comp_mul

/-- info: 'IsGaussSeq.sum_totient_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsGaussSeq.sum_totient_mul

/-- info: 'isGaussSeq_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isGaussSeq_pow

/-- info: 'card_toFinset_periodicOrbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_toFinset_periodicOrbit

/-- info: 'card_minimalPeriod_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_minimalPeriod_eq

/-- info: 'card_fixedPoints_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_fixedPoints_iterate

/-- info: 'sum_mul_card_periodicOrbits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_mul_card_periodicOrbits

/-- info: 'isGaussSeq_card_fixedPoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isGaussSeq_card_fixedPoints

/-- info: 'orbitCount_card_fixedPoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms orbitCount_card_fixedPoints

/-- info: 'mul_necklace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mul_necklace

/-- info: 'sum_mul_necklace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_mul_necklace

/-- info: 'necklace_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms necklace_one

/-- info: 'necklace_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms necklace_prime

/-- info: 'sum_totient_mul_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_totient_mul_pow
