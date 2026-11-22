import MathInfra.FormalizedElsewhere.EulerianNumber

/-!
# Checks for `MathInfra.FormalizedElsewhere.EulerianNumber`

Known values, a brute-force check of the descent count, and the general theorems in use. The
axiom audit is in `MathInfraTest/FormalizedElsewhere/EulerianNumberAxioms.lean`. Both files are
part of `lake build`.
-/

open Finset
open scoped Nat

/-! ### Known values -/

-- `A(n, k)` for `k < n ≤ 6`: the rows of OEIS A008292. Row `0` (`A(0, 0) = 1`) is checked next.
example : (List.range 7).map (fun n ↦ (List.range n).map (eulerian n)) =
    [[], [1], [1, 1], [1, 4, 1], [1, 11, 11, 1], [1, 26, 66, 26, 1],
      [1, 57, 302, 302, 57, 1]] := by
  decide +kernel
example : eulerian 0 0 = 1 := rfl
-- `A(10, 4) = 1310354`.
example : eulerian 10 4 = 1310354 := by decide +kernel

/-! ### Descents counted directly -/

example : numDescents [3, 1, 2, 0] = 2 := rfl
example : numDescents [0, 1, 2, 3] = 0 := rfl

/-- Among the `24` permutations of `0, 1, 2, 3`, the numbers with `0, 1, 2, 3` descents are
`1, 11, 11, 1`, computed by listing them (with `List.permutations'`, which the kernel can
evaluate). -/
example : (List.range 4).map (fun k ↦ (List.range 4).permutations'.countP
    (fun l ↦ numDescents l = k)) = [1, 11, 11, 1] := by
  decide +kernel
example (k : ℕ) : (List.range 4).permutations.countP (fun l ↦ numDescents l = k) =
    eulerian 4 k :=
  countP_permutations_range 4 k

/-- The same for the permutations of `Fin 4`. -/
example : (List.range 4).map (fun k ↦
    #{σ : Equiv.Perm (Fin 4) | numDescents (List.ofFn fun i ↦ (σ i : ℕ)) = k}) =
      [1, 11, 11, 1] := by
  simp only [card_perm_numDescents]
  decide +kernel

/-! ### The general theorems in use -/

/-- `n = 5`: `1 + 26 + 66 + 26 + 1 = 120 = 5!`. -/
example : ∑ k ∈ range 6, eulerian 5 k = 120 := sum_eulerian 5

/-- `A(n, 1) = 2ⁿ - n - 1`: `A(5, 1) = 26`. -/
example : eulerian 5 1 = 26 := by rw [eulerian_one_right]; rfl

/-- Symmetry: `A(7, 5) = A(7, 1) = 2⁷ - 8`. -/
example : eulerian 7 5 = 120 := by
  have h := eulerian_symm (show 1 < 7 by norm_num)
  rw [eulerian_one_right] at h
  exact h

/-- Worpitzky for `n = 3`: `x³ = C(x, 3) + 4 * C(x + 1, 3) + C(x + 2, 3)`. -/
example (x : ℕ) : x.choose 3 + 4 * (x + 1).choose 3 + (x + 2).choose 3 = x ^ 3 := by
  have h := sum_eulerian_mul_choose 3 x
  have h0 : eulerian 3 0 = 1 := rfl
  have h1 : eulerian 3 1 = 4 := rfl
  have h2 : eulerian 3 2 = 1 := rfl
  have h3 : eulerian 3 3 = 0 := rfl
  simpa [sum_range_succ, h0, h1, h2, h3, add_assoc] using h

/-- The explicit formula: `A(4, 1) = 2⁴ - 5 * 1⁴ = 11`. -/
example : (eulerian 4 1 : ℤ) = 11 := by
  rw [eulerian_eq_sum]
  decide +kernel

/-- `A_3(t) = 1 + 4t + t²`, and its value at `t = 1` is `3! = 6`. -/
example : eulerianPoly ℤ 3 = 1 + 4 * Polynomial.X + Polynomial.X ^ 2 := by
  ext k
  rw [coeff_eulerianPoly]
  rcases k with _ | _ | _ | k
  · simp
  · simp [Polynomial.coeff_X, Polynomial.coeff_one]; rfl
  · simp [Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_X_pow]; rfl
  · rw [eulerian_eq_zero_of_le (by omega) (by omega)]
    simp [Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_X_pow]
example : (eulerianPoly ℚ 3).eval 1 = 6 := by
  rw [eulerianPoly_eval_one]; rfl

open PowerSeries in
/-- The generating function for `n = 1`: `∑ₘ (m + 1) tᵐ = 1 / (1 - t)²`. -/
example : (mk fun m : ℕ ↦ (m + 1 : ℚ)) * (1 - X) ^ 2 = 1 := by
  have h11 : eulerian 1 1 = 0 := rfl
  simpa [eulerianPoly, sum_range_succ, h11] using mk_pow_mul_one_sub_pow (R := ℚ) 1
