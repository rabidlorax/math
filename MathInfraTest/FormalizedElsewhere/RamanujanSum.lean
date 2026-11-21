import MathInfra.FormalizedElsewhere.RamanujanSum

/-!
# Checks for `MathInfra.FormalizedElsewhere.RamanujanSum`

Known values, and the general theorems specialised to classical facts about the Möbius and
totient functions and roots of unity. The axiom audit is in
`MathInfraTest/FormalizedElsewhere/RamanujanSumAxioms.lean`. Both files are part of `lake build`.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius Nat

/-! ### Known values -/

-- `c_5(n)` is `4` on multiples of `5` and `-1` elsewhere.
example : ramanujanSum 5 10 = 4 := by
  rw [ramanujanSum_prime 10 Nat.prime_five]; norm_num
example : ramanujanSum 5 7 = -1 := by
  rw [ramanujanSum_prime 7 Nat.prime_five]; norm_num

-- `c_8(n)` for `n = 4, 2`: `-4` and `0`.
example : ramanujanSum 8 4 = -4 := by
  rw [show 8 = 2 ^ (2 + 1) by rfl, ramanujanSum_prime_pow_succ 4 Nat.prime_two]; norm_num
example : ramanujanSum 8 2 = 0 := by
  rw [show 8 = 2 ^ (2 + 1) by rfl, ramanujanSum_prime_pow_succ 2 Nat.prime_two]; norm_num

-- `c_12(4) = c_4(4) * c_3(4) = φ(4) * μ(3) = -2`, by multiplicativity and periodicity.
example : ramanujanSum 12 4 = -2 := by
  rw [show 12 = 4 * 3 by rfl, ramanujanSum_mul 4 (by norm_num : Nat.Coprime 4 3),
    ramanujanSum_congr 4 4 (by decide : (4 : ℤ) ≡ 0 [ZMOD 4]),
    ramanujanSum_congr 3 4 (by decide : (4 : ℤ) ≡ 1 [ZMOD 3]),
    ramanujanSum_zero_right, ramanujanSum_one_right, moebius_apply_prime Nat.prime_three]
  decide

-- Hölder's formula at `q = 12`, `n = 4`: `g = 4`, so `c_12(4) * φ(3) = μ(3) * φ(12)`.
example : ramanujanSum 12 4 * 2 = -1 * 4 := by
  simpa [show Int.gcd 12 4 = 4 by rfl, moebius_apply_prime Nat.prime_three,
    Nat.totient_prime Nat.prime_three, show φ 12 = 4 by decide] using
    ramanujanSum_mul_totient 12 4

/-! ### The general theorems in use -/

/-- Gauss: `∑_{d ∣ q} φ(d) = q`, the case `n = 0` of `sum_ramanujanSum`. -/
example (q : ℕ) : ∑ d ∈ q.divisors, (φ d : ℤ) = q := by
  simpa using sum_ramanujanSum q 0

/-- `∑_{d ∣ q} μ(d)` is `1` for `q = 1` and `0` otherwise, the case `n = 1`. -/
example (q : ℕ) : ∑ d ∈ q.divisors, μ d = if q = 1 then 1 else 0 := by
  rw [← sum_congr rfl fun d _ => ramanujanSum_one_right d, sum_ramanujanSum]
  by_cases h : q = 1 <;> simp [h, Int.natCast_dvd]

/-- The primitive `q`-th roots of unity sum to `μ(q)`. -/
example {K : Type*} [Field K] {ζ : K} {q : ℕ} (hζ : IsPrimitiveRoot ζ q) :
    ∑ η ∈ primitiveRoots q K, η = μ q := by
  simpa using hζ.sum_primitiveRoots_pow 1

/-- Their number is `φ(q)` in `K`: the case `n = 0`. -/
example {K : Type*} [Field K] {ζ : K} {q : ℕ} (hζ : IsPrimitiveRoot ζ q) :
    ((primitiveRoots q K).card : K) = φ q := by
  simpa using hζ.sum_primitiveRoots_pow 0

/-- For a prime `p` and a primitive `p`-th root `ζ`: `ζ + ζ ^ 2 + ⋯ + ζ ^ (p - 1) = -1`. -/
example {K : Type*} [Field K] {ζ : K} {p : ℕ} (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p) :
    ∑ k ∈ range p with k.Coprime p, ζ ^ k = -1 := by
  simpa [ramanujanSum_prime 1 hp, Int.natCast_dvd, hp.ne_one] using hζ.sum_pow_coprime 1

/-- In `ℂ`: the sum of `exp(2πik/q)` over `k < q` coprime to `q` is `μ(q)`. -/
example (q : ℕ) :
    ∑ k ∈ range q with k.Coprime q, Complex.exp (2 * Real.pi * Complex.I * k / q) = μ q := by
  simpa using (ramanujanSum_eq_sum_exp q 1).symm

/-- `c_q(n)` is an integer although the roots of unity are not: in `ℂ`, the sum for `q = 6`,
`n = 2` is `c_6(2) = c_2(2) * c_3(2) = 1 * (-1) = -1`. -/
example : ∑ k ∈ range 6 with k.Coprime 6,
    Complex.exp (2 * Real.pi * Complex.I * k * 2 / 6) = -1 := by
  have h := ramanujanSum_eq_sum_exp 6 2
  push_cast at h
  rw [← h, show 6 = 2 * 3 by rfl, ramanujanSum_mul _ (by norm_num : Nat.Coprime 2 3),
    ramanujanSum_prime _ Nat.prime_two, ramanujanSum_prime _ Nat.prime_three]
  norm_num
