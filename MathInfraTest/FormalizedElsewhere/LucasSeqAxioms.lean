import MathInfra.New.LucasSeq

/-!
# Axiom audit for `MathInfra.New.LucasSeq`

Every public theorem, with the axioms it depends on. `#guard_msgs` turns each line into a
check, so the build fails if any theorem starts depending on anything else (for example
`sorryAx`). Nothing here uses an axiom beyond Lean's three standard ones.
-/

set_option linter.style.longLine false

/-- info: 'lucasU_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms lucasU_zero

/-- info: 'lucasU_one' does not depend on any axioms -/
#guard_msgs in
#print axioms lucasU_one

/-- info: 'lucasU_add_two' does not depend on any axioms -/
#guard_msgs in
#print axioms lucasU_add_two

/-- info: 'lucasU_two' depends on axioms: [propext] -/
#guard_msgs in
#print axioms lucasU_two

/-- info: 'lucasU_three' depends on axioms: [propext] -/
#guard_msgs in
#print axioms lucasU_three

/-- info: 'lucasV_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms lucasV_zero

/-- info: 'lucasV_one' depends on axioms: [propext] -/
#guard_msgs in
#print axioms lucasV_one

/-- info: 'lucasV_add_two' depends on axioms: [propext] -/
#guard_msgs in
#print axioms lucasV_add_two

/-- info: 'lucasV_two' depends on axioms: [propext] -/
#guard_msgs in
#print axioms lucasV_two

/-- info: 'map_lucasU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms map_lucasU

/-- info: 'map_lucasV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms map_lucasV

/-- info: 'isLucasRec_lucasU' does not depend on any axioms -/
#guard_msgs in
#print axioms isLucasRec_lucasU

/-- info: 'isLucasRec_lucasV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms isLucasRec_lucasV

/-- info: 'IsLucasRec.add_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms IsLucasRec.add_succ

/-- info: 'IsLucasRec.eq_lucasU' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms IsLucasRec.eq_lucasU

/-- info: 'IsLucasRec.ext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms IsLucasRec.ext

/-- info: 'IsLucasRec.add_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsLucasRec.add_two_mul

/-- info: 'lucasV_eq_two_mul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lucasV_eq_two_mul

/-- info: 'lucasV_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lucasV_succ

/-- info: 'lucasV_succ'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lucasV_succ'

/-- info: 'two_mul_lucasU_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms two_mul_lucasU_succ

/-- info: 'two_mul_lucasV_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms two_mul_lucasV_succ

/-- info: 'lucasU_add_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lucasU_add_succ

/-- info: 'two_mul_lucasU_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms two_mul_lucasU_add

/-- info: 'two_mul_lucasV_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms two_mul_lucasV_add

/-- info: 'lucasU_cassini' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lucasU_cassini

/-- info: 'lucasV_sq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lucasV_sq

/-- info: 'lucasU_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasU_two_mul

/-- info: 'lucasV_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasV_two_mul

/-- info: 'lucasU_two_mul_add_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lucasU_two_mul_add_one

/-- info: 'lucasU_add_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasU_add_two_mul

/-- info: 'lucasV_add_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasV_add_two_mul

/-- info: 'lucasU_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasU_mul

/-- info: 'lucasV_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasV_mul

/-- info: 'lucasU_dvd_lucasU_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasU_dvd_lucasU_mul

/-- info: 'lucasU_dvd_lucasU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasU_dvd_lucasU

/-- info: 'isDvdSequence_lucasU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isDvdSequence_lucasU

/-- info: 'pow_succ_eq_lucasU' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pow_succ_eq_lucasU

/-- info: 'lucasU_binet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lucasU_binet

/-- info: 'lucasV_binet' depends on axioms: [propext] -/
#guard_msgs in
#print axioms lucasV_binet

/-- info: 'lucasV_eq_pow_add_pow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lucasV_eq_pow_add_pow

/-- info: 'two_mul_add_pow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms two_mul_add_pow

/-- info: 'lucasU_two_one' depends on axioms: [propext] -/
#guard_msgs in
#print axioms lucasU_two_one

/-- info: 'lucasV_two_one' depends on axioms: [propext] -/
#guard_msgs in
#print axioms lucasV_two_one

/-- info: 'lucasU_one_neg_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lucasU_one_neg_one

/-- info: 'lucasV_one_neg_one_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lucasV_one_neg_one_succ

/-- info: 'lucasU_add_one_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasU_add_one_self

/-- info: 'lucasV_add_one_self' depends on axioms: [propext] -/
#guard_msgs in
#print axioms lucasV_add_one_self

/-- info: 'lucasU_three_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lucasU_three_two

/-- info: 'lucasV_three_two' depends on axioms: [propext] -/
#guard_msgs in
#print axioms lucasV_three_two

/-- info: 'lucasV_X_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasV_X_C

/-- info: 'lucasU_succ_X_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasU_succ_X_C

/-- info: 'lucasV_eq_eval_dickson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasV_eq_eval_dickson

/-- info: 'lucasU_succ_eq_eval_dickson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasU_succ_eq_eval_dickson

/-- info: 'lucasV_X_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasV_X_one

/-- info: 'lucasU_succ_X_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasU_succ_X_one

/-- info: 'isCoprime_lucasU_succ_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isCoprime_lucasU_succ_right

/-- info: 'isCoprime_lucasU_lucasU_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isCoprime_lucasU_lucasU_succ

/-- info: 'dvd_lucasU_add_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dvd_lucasU_add_iff

/-- info: 'dvd_lucasU_add_mul_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dvd_lucasU_add_mul_iff

/-- info: 'dvd_lucasU_gcd_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dvd_lucasU_gcd_iff

/-- info: 'Int.gcd_lucasU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Int.gcd_lucasU

/-- info: 'ZMod.lucasV_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZMod.lucasV_prime

/-- info: 'ZMod.lucasU_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZMod.lucasU_prime

/-- info: 'lucasV_prime_modEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasV_prime_modEq

/-- info: 'lucasU_prime_modEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lucasU_prime_modEq

/-- info: 'prime_dvd_lucasU_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prime_dvd_lucasU_self

/-- info: 'prime_dvd_lucasU_add_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prime_dvd_lucasU_add_one

/-- info: 'prime_dvd_lucasU_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prime_dvd_lucasU_sub_one

/-- info: 'prime_dvd_lucasU_sub_legendreSym' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prime_dvd_lucasU_sub_legendreSym
