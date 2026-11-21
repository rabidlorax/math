import MathInfra.QAnalog

/-!
# Checks for `MathInfra.QAnalog`

Known values, the q-Pascal triangle, and worked uses of the main theorems. The axiom audit
is in `MathInfraTest/Axioms.lean`. Both files are part of `lake build`.
-/

open Polynomial

/-! ### Known values -/

-- Classically: 35 planes in 𝔽₂⁴, 13 lines in 𝔽₃³, 1395 three-dimensional subspaces of 𝔽₂⁶.
example : gaussBinom (2 : ℕ) 4 2 = 35 := by decide
example : gaussBinom (3 : ℕ) 3 1 = 13 := by decide
example : gaussBinom (2 : ℕ) 6 3 = 1395 := by decide
-- `q = 1` gives the binomial coefficient, `q = -1` is allowed too.
example : gaussBinom (1 : ℕ) 6 3 = 20 := by decide
example : gaussBinom (-1 : ℤ) 4 2 = 2 := by decide
example : qNat (2 : ℕ) 5 = 31 := by decide
example : qFactorial (2 : ℕ) 4 = 1 * 3 * 7 * 15 := by decide

/-! ### The q-Pascal triangle, rows 2 to 4, for every `q` in every commutative semiring -/

section Triangle

variable {R : Type*} [CommSemiring R] (q : R)

/-- Unfold a small Gaussian binomial by the q-Pascal rule and normalise. -/
local macro "triangle" : tactic =>
  `(tactic| (simp [gaussBinom_succ_succ, qNat_succ] <;> ring))

example : gaussBinom q 2 1 = 1 + q := by triangle
example : gaussBinom q 3 1 = 1 + q + q ^ 2 := by triangle
example : gaussBinom q 3 2 = 1 + q + q ^ 2 := by triangle
example : gaussBinom q 4 1 = 1 + q + q ^ 2 + q ^ 3 := by triangle
example : gaussBinom q 4 2 = 1 + q + 2 * q ^ 2 + q ^ 3 + q ^ 4 := by triangle
example : gaussBinom q 4 3 = 1 + q + q ^ 2 + q ^ 3 := by triangle

end Triangle

/-! ### The theorems in use -/

-- A value computed in ℕ moves to any ring through the cast lemmas.
example : gaussBinom (2 : ℚ) 4 2 = 35 := by
  have h : gaussBinom (2 : ℕ) 4 2 = 35 := by decide
  exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) h

-- The quotient formula at q = 2 over ℚ: 35 = [4]! / ([2]! [2]!) = 315 / 9.
example : gaussBinom (2 : ℚ) 4 2 = 35 := by
  rw [gaussBinom_eq_div 2 (by norm_num) (by norm_num [qFactorial_succ, qNat_succ])]
  norm_num [qFactorial_succ, qNat_succ]

-- The quotient formula really needs its hypothesis: at q = -1 the denominator [2]! is 0,
-- and the formula fails (the left side is 2, the right side is 0 / 0 = 0 in Lean).
example : qFactorial (-1 : ℚ) 2 = 0 := by norm_num [qFactorial_succ, qNat_succ]
example : gaussBinom (-1 : ℚ) 4 2
    ≠ qFactorial (-1 : ℚ) 4 / (qFactorial (-1 : ℚ) 2 * qFactorial (-1 : ℚ) 2) := by
  norm_num [gaussBinom_succ_succ, qFactorial_succ, qNat_succ]

-- The q-binomial theorem for n = 3.
example {R : Type*} [CommSemiring R] (q x : R) :
    ∏ i ∈ Finset.range 3, (1 + q ^ i * x)
      = 1 + (1 + q + q ^ 2) * x + q * (1 + q + q ^ 2) * x ^ 2 + q ^ 3 * x ^ 3 := by
  rw [prod_one_add_pow_mul]
  simp [Finset.sum_range_succ, Nat.choose, qNat_succ]

-- The sum of the coefficients of the polynomial `G_X(n, k)` is the binomial coefficient.
example (n k : ℕ) : (gaussBinom (X : ℕ[X]) n k).eval 1 = n.choose k := by
  simp

-- Universality: the value at any q comes from the one polynomial in ℕ[X].
example {R : Type*} [CommSemiring R] (q : R) :
    gaussBinom q 5 2 = aeval q (gaussBinom (X : ℕ[X]) 5 2) :=
  (aeval_gaussBinom_X q 5 2).symm

-- The transfer recipe: an identity known in ℕ[X] (here absorption) moves to every `q` in
-- every commutative semiring by applying `aeval q` and simplifying.
example {R : Type*} [CommSemiring R] (q : R) (n k : ℕ) :
    qNat q (k + 1) * gaussBinom q (n + 1) (k + 1) = qNat q (n + 1) * gaussBinom q n k := by
  simpa using congrArg (aeval q) (qNat_succ_mul_gaussBinom_succ (X : ℕ[X]) n k)
