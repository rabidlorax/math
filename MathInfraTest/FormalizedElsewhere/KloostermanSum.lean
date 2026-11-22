import MathInfra.FormalizedElsewhere.KloostermanSum

/-!
# Checks for `MathInfra.FormalizedElsewhere.KloostermanSum`

Known values, computed exactly (Kloosterman sums with a character valued in `ZMod 11`, and
hyperbola energies), and the general theorems specialised to the standard complex characters. The
axiom audit is in `MathInfraTest/FormalizedElsewhere/KloostermanSumAxioms.lean`. Both files are
part of `lake build`.
-/

open Finset AddChar ZMod
open scoped Nat

/-! ### Exact values

`3` is a primitive fifth root of unity in `ZMod 11`, so `x ↦ 3 ^ x` is a primitive character of
`ZMod 5` with values in `ZMod 11`, and its Kloosterman sums can be computed by `decide`. -/

/-- `x ↦ 3 ^ x`, a primitive character of `ZMod 5` with values in `ZMod 11`. -/
def ψ₅ : AddChar (ZMod 5) (ZMod 11) := zmodChar 5 (by decide : (3 : ZMod 11) ^ 5 = 1)

-- With `ζ = 3`, `S(ψ₅; 1, 1) = ζ² + ζ³ + 2`: the terms `x = 1, 4` give `ζ²` and `ζ³`, and
-- `x = 2, 3` give `1`.
example : kloostermanSum ψ₅ 1 1 = 3 ^ 2 + 3 ^ 3 + 2 := by decide

-- Symmetry and the dependence on `m n` alone: `S(2, 3) = S(3, 2) = S(1, 6) = S(1, 1)`.
example : kloostermanSum ψ₅ 2 3 = kloostermanSum ψ₅ 1 1 := by decide
example : kloostermanSum ψ₅ 2 3 = kloostermanSum ψ₅ 3 2 := kloostermanSum_comm ψ₅ 2 3

-- `S(m, 0)` is the Ramanujan sum: `S(1, 0) = c_5(1) = μ(5) = -1` and
-- `S(0, 0) = c_5(0) = φ(5) = 4`.
example : kloostermanSum ψ₅ 1 0 = -1 := by decide
example : kloostermanSum ψ₅ 0 0 = 4 := by decide

-- Summing over the first argument gives `0`.
example : ∑ m, kloostermanSum ψ₅ m 1 = 0 := by decide

/-! ### The hyperbola energy

For an odd prime `p` the energy is `3 (p − 1)(p − 2)`: the `(p − 1)²` solutions with
`x₁ + x₂ = 0`, and two (or one, if `x₁ = x₂`) for each of the other pairs. -/

example : hyperbolaEnergy 3 = 6 := by decide
example : hyperbolaEnergy 5 = 36 := by decide

-- The bound `3 (p − 1)²` of `hyperbolaEnergy_le`.
example : hyperbolaEnergy 5 ≤ 48 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  simpa using hyperbolaEnergy_le (p := 5)

/-! ### Complex Kloosterman sums -/

-- Complex Kloosterman sums are real.
example : (kloostermanSum (stdAddChar (N := 7)) 1 1).im = 0 := kloostermanSum_im _ 1 1

-- `S(m, 0; q)` with the standard character is the Ramanujan sum: `S(2, 0; 5) = c_5(2) = -1`.
example : kloostermanSum (stdAddChar (N := 5)) 2 0 = -1 := by
  have := kloostermanSum_zero_right_eq_ramanujanSum (isPrimitive_stdAddChar 5) 2
  rw [ramanujanSum_prime 2 Nat.prime_five] at this
  norm_num at this
  exact_mod_cast this

-- The second moment at `q = 6`: `∑_m |S(m, 1; 6)|² = 6 φ(6) = 12`.
example : ∑ m, ‖kloostermanSum (stdAddChar (N := 6)) m 1‖ ^ 2 = 12 := by
  rw [sum_norm_kloostermanSum_sq (isPrimitive_stdAddChar 6)]
  norm_num [show φ 6 = 2 by decide]

-- The fourth moment at `p = 5`: `∑_{m, n} |S(m, n; 5)|⁴ = 25 · 36 = 900`.
example : ∑ m, ∑ n, ‖kloostermanSum (stdAddChar (N := 5)) m n‖ ^ 4 = 900 := by
  rw [sum_norm_kloostermanSum_pow_four (isPrimitive_stdAddChar 5),
    show hyperbolaEnergy 5 = 36 by decide]
  norm_num

-- Kloosterman's bound at `p = 101`: `|S(m, n; 101)|⁴ ≤ 3 · 101³`, so `|S| < 42`, whereas the
-- trivial bound is `|S| ≤ 100`.
example (m n : ZMod 101) (h : m ≠ 0 ∨ n ≠ 0) :
    ‖kloostermanSum (stdAddChar (N := 101)) m n‖ ^ 4 ≤ 3 * 101 ^ 3 := by
  have : Fact (Nat.Prime 101) := ⟨by norm_num⟩
  exact_mod_cast norm_kloostermanSum_pow_four_le (isPrimitive_stdAddChar 101) h

/-! ### Twisted multiplicativity -/

-- `S(m, n; 15) = S(2m, 2n; 3) · S(2m, 2n; 5)`: modulo `3` and modulo `5`, the inverses of `5`
-- and of `3` are both `2`.
example (m n : ZMod 15) :
    kloostermanSum stdAddChar m n =
      kloostermanSum stdAddChar (2 * castHom (by norm_num : 3 ∣ 15) (ZMod 3) m)
          (2 * castHom (by norm_num : 3 ∣ 15) (ZMod 3) n) *
        kloostermanSum stdAddChar (2 * castHom (by norm_num : 5 ∣ 15) (ZMod 5) m)
          (2 * castHom (by norm_num : 5 ∣ 15) (ZMod 5) n) := by
  have h := kloostermanSum_stdAddChar_mul (q₁ := 3) (q₂ := 5) (by norm_num) m n
  rwa [ZMod.inv_eq_of_mul_eq_one 3 _ 2 (by decide),
    ZMod.inv_eq_of_mul_eq_one 5 _ 2 (by decide)] at h

