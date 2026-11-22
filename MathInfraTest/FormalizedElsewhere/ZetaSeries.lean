import MathInfra.FormalizedElsewhere.ZetaSeries

/-!
# Checks for `MathInfra.FormalizedElsewhere.ZetaSeries`

Known values, and the general theorems specialised to traces, Lucas numbers, the cyclotomic
identity and a sequence with no integral zeta series. The axiom audit is in
`MathInfraTest/FormalizedElsewhere/ZetaSeriesAxioms.lean`. Both files are part of `lake build`.
-/

open Finset PowerSeries ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-! ### Known values -/

-- The Lucas numbers `V_n(1, -1)`: `2, 1, 3, 4, 7, 11, 18`.
example : (List.range 7).map (lucasV (1 : ℤ) (-1)) = [2, 1, 3, 4, 7, 11, 18] := by
  decide +kernel

-- The cyclotomic identity in degree `3`: the coefficient of `X ^ 3` in
-- `(1 - X) ^ (-2) * (1 - X ^ 2) ^ (-1) * (1 - X ^ 3) ^ (-2)` is `2 ^ 3`.
example : coeff 3 (wittProd (necklace 2) 3) = 8 := coeff_wittProd_necklace 2 le_rfl

/-! ### The general theorems in use -/

/-- `1 / (1 - 2X)` is the zeta series of `2ⁿ`, and the only one over `ℤ`. -/
example {P : ℤ⟦X⟧} (hP : IsZetaSeries (2 ^ ·) P) : P = mk (2 ^ ·) :=
  hP.unique (isZetaSeries_geometric 2)

/-- `exp(X)` does not have integer coefficients: the sequence `f(1) = 1`, `f(n) = 0` otherwise,
fails the Gauss congruence at `n = 2`. -/
example : ¬∃ P : ℤ⟦X⟧, IsZetaSeries (fun n => if n = 1 then 1 else 0) P := by
  intro h
  have h2 := isGaussSeq_iff_exists_isZetaSeries.mpr h 2
  rw [Nat.prime_two.divisors, sum_pair (by norm_num)] at h2
  simp [moebius_apply_prime Nat.prime_two] at h2

/-- Fermat's little theorem for traces: `tr(Aᵖ) ≡ tr(A) [ZMOD p]`. -/
example {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℤ) {p : ℕ} (hp : p.Prime) :
    (A ^ p).trace ≡ A.trace [ZMOD p] := by
  simpa using trace_pow_modEq A hp 0 1

/-- The Euler congruence `tr(A ^ (p ^ 2)) ≡ tr(Aᵖ) [ZMOD p ^ 2]`. -/
example {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℤ) {p : ℕ} (hp : p.Prime) :
    (A ^ p ^ 2).trace ≡ (A ^ p).trace [ZMOD p ^ 2] := by
  simpa using trace_pow_modEq A hp 1 1

/-- `6 ∣ L₆ - L₃ - L₂ + L₁` for the Lucas numbers, here `18 - 4 - 3 + 1 = 12`. -/
example : (6 : ℤ) ∣ lucasV 1 (-1) 6 - lucasV 1 (-1) 3 - lucasV 1 (-1) 2 + lucasV 1 (-1) 1 := by
  have h := isGaussSeq_lucasV 1 (-1) 6
  rw [show Nat.divisors 6 = {1, 2, 3, 6} by decide] at h
  have h6 : μ 6 = 1 := by decide +kernel
  convert h using 1
  simp [moebius_apply_prime Nat.prime_two, moebius_apply_prime Nat.prime_three, h6]
  ring

/-- The trace of `Aⁿ` for the Fibonacci matrix `!![1, 1; 1, 0]` is the Lucas number `Lₙ`. -/
example (n : ℕ) : (!![(1 : ℤ), 1; 1, 0] ^ n).trace = lucasV 1 (-1) n := by
  simpa [lucasMatrix] using trace_lucasMatrix_pow (1 : ℤ) (-1) n

/-- The rotation of `ZMod 5` has an integral Artin–Mazur zeta function. -/
example : ∃ P : ℤ⟦X⟧, IsZetaSeries (fun n => (#{x : ZMod 5 | (· + 1)^[n] x = x} : ℤ)) P :=
  exists_isZetaSeries_card_fixedPoints _
