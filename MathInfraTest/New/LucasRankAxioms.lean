import MathInfra.New.LucasRank

/-!
# Axiom audit for `MathInfra.New.LucasRank`

Every public theorem, with the axioms it depends on. `#guard_msgs` turns each line into a
check, so the build fails if any theorem starts depending on anything else (for example
`sorryAx`). Nothing here uses an axiom beyond Lean's three standard ones.
-/

set_option linter.style.longLine false

/-- info: 'IsLucasRec.add_of_lucasU_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsLucasRec.add_of_lucasU_eq_zero

/-- info: 'IsLucasRec.add_mul_of_lucasU_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsLucasRec.add_mul_of_lucasU_eq_zero

/-- info: 'lucasU_succ_sq_of_lucasU_eq_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lucasU_succ_sq_of_lucasU_eq_zero

/-- info: 'isUnit_lucasU_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isUnit_lucasU_succ

/-- info: 'lucasU_lucasRank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasU_lucasRank

/-- info: 'lucasRank_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasRank_eq_zero_iff

/-- info: 'lucasU_ne_zero_of_lt_lucasRank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasU_ne_zero_of_lt_lucasRank

/-- info: 'lucasRank_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasRank_eq

/-- info: 'lucasU_eq_zero_iff_lucasRank_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasU_eq_zero_iff_lucasRank_dvd

/-- info: 'lucasRank_map_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasRank_map_dvd

/-- info: 'lucasRank_map_of_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasRank_map_of_injective

/-- info: 'lucasU_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasU_prod

/-- info: 'lucasRank_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasRank_prod

/-- info: 'IsLucasRec.periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsLucasRec.periodic

/-- info: 'periodic_lucasU_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms periodic_lucasU_iff

/-- info: 'lucasRank_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasRank_pos

/-- info: 'lucasPeriod_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasPeriod_pos

/-- info: 'ZMod.lucasRank_dvd_sub_legendreSym' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZMod.lucasRank_dvd_sub_legendreSym

/-- info: 'ZMod.lucasRank_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZMod.lucasRank_le

/-- info: 'lucasU_primality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasU_primality

/-- info: 'Nat.Prime.isLucasProbablePrime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Nat.Prime.isLucasProbablePrime
