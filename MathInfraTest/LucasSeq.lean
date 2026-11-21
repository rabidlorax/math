import MathInfra.LucasSeq

/-!
# Checks for `MathInfra.LucasSeq`

Known values, and the general theorems specialised to Fibonacci numbers, Mersenne numbers,
`q`-numbers and the Lucas–Lehmer sequence. The axiom audit is in
`MathInfraTest/LucasSeqAxioms.lean`. Both files are part of `lake build`.
-/

/-! ### Known values -/

-- Fibonacci and Lucas numbers: `F 10 = 55`, `L 10 = 123`.
example : lucasU (1 : ℤ) (-1) 10 = 55 := by decide
example : lucasV (1 : ℤ) (-1) 10 = 123 := by decide
-- Pell numbers `0, 1, 2, 5, 12, 29, 70` and their companions.
example : lucasU (2 : ℤ) (-1) 6 = 70 := by decide
example : lucasV (2 : ℤ) (-1) 6 = 198 := by decide
-- Mersenne numbers, and `2 ^ n + 1`.
example : lucasU (3 : ℤ) 2 10 = 1023 := by decide
example : lucasV (3 : ℤ) 2 10 = 1025 := by decide
-- The Pell-type equation `V ^ 2 - D * U ^ 2 = 4 * Q ^ n` at `(P, Q) = (2, -1)`, `n = 6`.
example : (198 : ℤ) ^ 2 - 8 * 70 ^ 2 = 4 := by decide
-- The law of apparition for Fibonacci numbers: `7 ∣ F 8` and `11 ∣ F 10`.
example : (7 : ℤ) ∣ lucasU 1 (-1) 8 := by decide
example : (11 : ℤ) ∣ lucasU 1 (-1) 10 := by decide

/-! ### The general theorems in use -/

/-- Cassini's identity for Fibonacci numbers. -/
example (n : ℕ) :
    (Nat.fib (n + 1) : ℤ) ^ 2 - Nat.fib n * Nat.fib (n + 2) = (-1) ^ n := by
  simpa [lucasU_one_neg_one] using lucasU_cassini (1 : ℤ) (-1) n

/-- `F m ∣ F (m * n)`. -/
example (m n : ℕ) : Nat.fib m ∣ Nat.fib (m * n) :=
  Int.natCast_dvd_natCast.mp
    (by simpa [lucasU_one_neg_one] using lucasU_dvd_lucasU_mul (1 : ℤ) (-1) m n)

/-- `2 ^ m - 1 ∣ 2 ^ (m * n) - 1`. -/
example (m n : ℕ) : (2 : ℤ) ^ m - 1 ∣ 2 ^ (m * n) - 1 := by
  simpa [lucasU_three_two] using lucasU_dvd_lucasU_mul (3 : ℤ) 2 m n

/-- `gcd (2 ^ m - 1) (2 ^ n - 1) = 2 ^ gcd m n - 1`. -/
example (m n : ℕ) :
    Int.gcd ((2 : ℤ) ^ m - 1) (2 ^ n - 1) = ((2 : ℤ) ^ Nat.gcd m n - 1).natAbs := by
  simpa [lucasU_three_two] using
    Int.gcd_lucasU (P := 3) (Q := 2) ⟨1, -1, by norm_num⟩ m n

/-- `[m]_q ∣ [m * n]_q` in any commutative ring. -/
example {R : Type*} [CommRing R] (q : R) (m n : ℕ) : qNat q m ∣ qNat q (m * n) := by
  simpa [lucasU_add_one_self] using lucasU_dvd_lucasU_mul (q + 1) q m n

/-- The squaring step of the Lucas–Lehmer test, `s ↦ s ^ 2 - 2`, is doubling of the index
of `V` at `(P, Q) = (4, 1)`. -/
example (n : ℕ) : lucasV (4 : ℤ) 1 (2 * n) = lucasV 4 1 n ^ 2 - 2 := by
  simpa using lucasV_two_mul (4 : ℤ) 1 n

/-- Fermat's little theorem for the base `2` is `V p ≡ P` at `(P, Q) = (3, 2)`. -/
example (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : (2 : ℤ) ^ p ≡ 2 [ZMOD p] := by
  have h := lucasV_prime_modEq p hp 3 2
  rw [lucasV_three_two] at h
  exact Int.ModEq.add_right_cancel' 1 (by simpa using h)

/-- Every odd prime `p` divides the Fibonacci number with index `p - (5 / p)`. -/
example (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (p : ℤ) ∣ Nat.fib ((p : ℤ) - legendreSym p 5).toNat := by
  have hQ : ¬ (p : ℤ) ∣ -1 := by
    rw [Int.dvd_neg]
    intro h
    have h1 : (p : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) h
    exact (Fact.out : p.Prime).one_lt.ne' (by exact_mod_cast h1)
  have h := prime_dvd_lucasU_sub_legendreSym p hp 1 (-1) hQ
  rw [lucasU_one_neg_one] at h
  norm_num at h
  exact h
