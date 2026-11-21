import MathInfra.DedekindSum

/-!
# Checks for `MathInfra.DedekindSum`

Known values computed straight from the definition, the same values recovered from the
general theorems, and classical consequences. The axiom audit is in
`MathInfraTest/DedekindSumAxioms.lean`. Both files are part of `lake build`.
-/

open Finset

/-! ### Known values, from the definition -/

example : sawtooth (7 / 4 : ℚ) = 1 / 4 := by norm_num [sawtooth]
example : sawtooth (-7 / 4 : ℚ) = -1 / 4 := by norm_num [sawtooth]
example : sawtooth (5 / 2 : ℚ) = 0 := by norm_num [sawtooth]
example : sawtooth (3 : ℚ) = 0 := by norm_num [sawtooth]

example : dedekindSum 1 7 = 5 / 14 := by norm_num [dedekindSum, sawtooth, sum_range_succ]
example : dedekindSum 3 7 = -1 / 14 := by norm_num [dedekindSum, sawtooth, sum_range_succ]
example : dedekindSum 5 17 = 1 / 17 := by norm_num [dedekindSum, sawtooth, sum_range_succ]
example : dedekindSum 2 9 = 4 / 27 := by norm_num [dedekindSum, sawtooth, sum_range_succ]

/-! ### The same values, from the theorems -/

-- `s(1, 7) = 6 * 5 / 84`.
example : dedekindSum 1 7 = 5 / 14 := by rw [dedekindSum_one_left]; norm_num

-- The integer formula: `∑_{r < 7} r (3 r mod 7) = 70`, and `70 / 49 - 6 / 4 = -1/14`.
example : dedekindSum 3 7 = -1 / 14 := by
  rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by rfl, dedekindSum_eq_sum_mod (by norm_num) (by norm_num)]
  norm_num [sum_range_succ]

-- Reciprocity and periodicity: `s(3, 7) = -1/63 - s(7, 3) = -1/63 - s(1, 3) = -1/14`.
example : dedekindSum 3 7 = -1 / 14 := by
  have R := dedekindSum_reciprocity (h := 3) (k := 7) (by norm_num) (by norm_num) (by norm_num)
  push_cast at R
  rw [dedekindSum_congr (h := 7) (h' := 1) (k := 3) (by decide), dedekindSum_one_left] at R
  linarith

-- The Euclidean algorithm: `17 ≡ 2 (mod 5)` and `2² ≡ -1 (mod 5)`, so `s(17, 5) = 0` and
-- `s(5, 17) = (25 + 289 + 1) / (12 * 85) - 1/4 = 1/17`.
example : dedekindSum 5 17 = 1 / 17 := by
  have R := dedekindSum_reciprocity (h := 5) (k := 17) (by norm_num) (by norm_num) (by norm_num)
  push_cast at R
  rw [dedekindSum_congr (h := 17) (h' := 2) (k := 5) (by decide),
    dedekindSum_eq_zero_of_sq_modEq_neg_one (h := 2) (k := 5) (by decide)] at R
  linarith

-- `s(2, k) = (k - 1)(k - 5) / (24 k)` for odd `k`.
example : dedekindSum 2 9 = 4 / 27 := by rw [dedekindSum_two_left (by decide)]; norm_num
example : dedekindSum 2 5 = 0 := by rw [dedekindSum_two_left (by decide)]; norm_num

/-! ### Symmetries -/

-- `3 * 5 ≡ 1 (mod 7)`, so `s(5, 7) = s(3, 7)`.
example : dedekindSum 5 7 = -1 / 14 := by
  rw [dedekindSum_of_mul_modEq_one (h := 3) (by decide)]
  norm_num [dedekindSum, sawtooth, sum_range_succ]

-- `4 ≡ -3 (mod 7)`, so `s(4, 7) = -s(3, 7)`.
example : dedekindSum 4 7 = 1 / 14 := by
  rw [dedekindSum_congr (h' := -3) (by decide), dedekindSum_neg]
  norm_num [dedekindSum, sawtooth, sum_range_succ]

-- `4² ≡ -1 (mod 17)`.
example : dedekindSum 4 17 = 0 := dedekindSum_eq_zero_of_sq_modEq_neg_one (by decide)

-- Homogeneity: `s(6, 14) = s(3, 7)`.
example : dedekindSum 6 14 = dedekindSum 3 7 := by
  simpa using dedekindSum_mul_mul 3 7 (d := 2) (by norm_num)

/-! ### The general theorems in use -/

/-- The distribution relation for `n = 2`: `((x)) + ((x + 1/2)) = ((2x))`. -/
example (x : ℝ) : sawtooth x + sawtooth (x + 1 / 2) = sawtooth (2 * x) := by
  simpa [sum_range_succ] using sum_sawtooth_add_div x (n := 2) (by norm_num)

/-- `|s(h, 7)| ≤ 5/14` for every `h` prime to `7`. -/
example (h : ℤ) (hc : IsCoprime h 7) : |dedekindSum h 7| ≤ 5 / 14 := by
  have := abs_dedekindSum_le (k := 7) (by exact_mod_cast hc)
  rw [dedekindSum_one_left] at this
  norm_num at this
  exact this

/-- `s(h, k) = s(1, k)` when `h ≡ 1 (mod k)`, so the bound is attained. -/
example (k : ℕ) : dedekindSum (1 + k) k = dedekindSum 1 k :=
  dedekindSum_congr (Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩)

/-- The integrality and congruence at `(h, k) = (3, 7)`: `6 * 7 * s(3, 7) = -3`, and
`12 * 3 * 7 * s(3, 7) = -18 ≡ 3² + 1 (mod 7)`. -/
example : ∃ z : ℤ, 12 * 3 * 7 * dedekindSum 3 7 = z ∧ z ≡ 3 ^ 2 + 1 [ZMOD 7] := by
  simpa using exists_twelve_mul_dedekindSum_modEq (h := 3) (k := 7) (by norm_num) (by norm_num)
    (by norm_num)

/-- `6 k s(1, k) = (k - 1)(k - 2) / 2` is an integer. -/
example (k : ℕ) (hk : k ≠ 0) : ∃ z : ℤ, 6 * k * dedekindSum 1 k = z := by
  simpa using exists_six_mul_dedekindSum_eq (h := 1) hk (Nat.coprime_one_left k)
