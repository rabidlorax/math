import MathInfra.New.LucasRank

/-!
# Checks for `MathInfra.New.LucasRank`

Known Fibonacci ranks of apparition, the Pisano period modulo `10`, the rank of `6` through the
Chinese remainder theorem, `127` proved prime by the `N + 1` test, and the Lucas pseudoprime
`323` for `(1, -1)`. The axiom audit is in `MathInfraTest/New/LucasRankAxioms.lean`. Both files
are part of `lake build`.
-/

/-! ### Fibonacci entry points and Pisano periods -/

/-- `10` first divides a Fibonacci number at `F₁₅ = 610`. -/
theorem fib_rank_ten : lucasRank (1 : ZMod 10) (-1) = 15 :=
  lucasRank_eq _ _ (by norm_num) (by decide) (by decide)

/-- The Fibonacci numbers divisible by `10` are exactly the `F_n` with `15 ∣ n`. -/
example (n : ℕ) : 10 ∣ Nat.fib n ↔ 15 ∣ n := by
  rw [← ZMod.natCast_eq_zero_iff, ← lucasU_one_neg_one, ← fib_rank_ten]
  exact lucasU_eq_zero_iff_lucasRank_dvd isUnit_one.neg

/-- The Pisano period of `10` is `60`: `15 * orderOf (F₁₆ mod 10) = 15 * orderOf 7 = 60`. -/
theorem fib_period_ten : lucasPeriod (1 : ZMod 10) (-1) = 60 := by
  have h16 : lucasU (1 : ZMod 10) (-1) 16 = 7 := by decide
  have h7 : orderOf (7 : ZMod 10) = 4 := orderOf_eq_iff (by norm_num) |>.mpr ⟨by decide, by decide⟩
  rw [lucasPeriod, fib_rank_ten, h16, h7]

/-- The periods of the Fibonacci numbers modulo `10` are exactly the multiples of `60`. -/
example (T : ℕ) : Function.Periodic (fun n => (Nat.fib n : ZMod 10)) T ↔ 60 ∣ T := by
  rw [← fib_period_ten, ← periodic_lucasU_iff isUnit_one.neg, funext (lucasU_one_neg_one)]

/-- Primes: `5 ∣ D = 5` gives rank `5`; `(5 / 7) = -1` gives rank `8 = 7 + 1`; `(5 / 11) = 1`
gives rank `10 = 11 - 1`. -/
example : lucasRank (1 : ZMod 5) (-1) = 5 := lucasRank_eq _ _ (by norm_num) (by decide) (by decide)
example : lucasRank (1 : ZMod 7) (-1) = 8 := lucasRank_eq _ _ (by norm_num) (by decide) (by decide)
example : lucasRank (1 : ZMod 11) (-1) = 10 :=
  lucasRank_eq _ _ (by norm_num) (by decide) (by decide)

/-! ### Products: the rank of `6` is `lcm 3 4 = 12` -/

example : lucasRank (1 : ZMod 6) (-1) = 12 := by
  let e : ZMod (2 * 3) ≃+* ZMod 2 × ZMod 3 := ZMod.chineseRemainder (by norm_num)
  have h2 : lucasRank (1 : ZMod 2) (-1) = 3 :=
    lucasRank_eq _ _ (by norm_num) (by decide) (by decide)
  have h3 : lucasRank (1 : ZMod 3) (-1) = 4 :=
    lucasRank_eq _ _ (by norm_num) (by decide) (by decide)
  have h := lucasRank_map_of_injective (1 : ZMod (2 * 3)) (-1) e.toRingHom e.injective
  rw [map_one, map_neg, map_one, Prod.one_eq_mk, Prod.neg_mk,
    lucasRank_prod isUnit_one.neg isUnit_one.neg, h2, h3] at h
  exact h.symm

/-! ### The `N + 1` test: `127 = 2 ^ 7 - 1` is prime -/

/-- With `(P, Q) = (2, -2)`: `U 128 ≡ 0` and `U 64 ≡ 46`, a unit (`46 * 58 ≡ 1`), modulo `127`.
The only prime factor of `128` is `2`. -/
example : Nat.Prime 127 := by
  refine lucasU_primality (by norm_num) (2 : ZMod 127) (-2) (IsUnit.of_mul_eq_one 63 (by decide))
    (by decide +kernel) fun q hq hqd => ?_
  have hq2 : q = 2 :=
    (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow (n := 7) hqd)
  subst hq2
  exact IsUnit.of_mul_eq_one 58 (by decide +kernel)

/-! ### Lucas probable primes -/

example : IsLucasProbablePrime 1 (-1) 101 :=
  (by norm_num : Nat.Prime 101).isLucasProbablePrime (by norm_num) 1 (by norm_num)

/-- `323 = 17 * 19` is the smallest Lucas pseudoprime for `(1, -1)`: `323 ∣ F₃₂₄`, as for a
prime with `(5 / 323) = -1`. -/
example : IsLucasPsp 1 (-1) 323 := by
  refine ⟨?_, by norm_num, by norm_num, Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num)⟩
  have hJ : jacobiSym (1 ^ 2 - 4 * -1) 323 = -1 := by norm_num
  rw [IsLucasProbablePrime, hJ, show ((323 : ℕ) - -1 : ℤ).toNat = 324 by norm_num,
    lucasU_one_neg_one]
  exact Int.natCast_dvd_natCast.mpr (by norm_num)
