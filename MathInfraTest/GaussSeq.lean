import MathInfra.GaussSeq

/-!
# Checks for `MathInfra.GaussSeq`

Known values, and the general theorems specialised to Fermat's little theorem, Euler-type
congruences, divisor sums, necklace counts and periodic points. The axiom audit is in
`MathInfraTest/GaussSeqAxioms.lean`. Both files are part of `lake build`.
-/

open Finset ArithmeticFunction Function
open scoped ArithmeticFunction.Moebius Nat

/-! ### Known values -/

-- Binary aperiodic necklaces of length `1, …, 6` (classically also the monic irreducible
-- polynomials of these degrees over `𝔽₂`): `2, 1, 2, 3, 6, 9`.
example : (List.range 6).map (fun n => necklace 2 (n + 1)) = [2, 1, 2, 3, 6, 9] := by
  decide +kernel
-- Ternary: `3, 3, 8, 18, 48`.
example : (List.range 5).map (fun n => necklace 3 (n + 1)) = [3, 3, 8, 18, 48] := by
  decide +kernel
-- Negative `a` is allowed: `M(-1, 2) = ((-1) ^ 2 - (-1)) / 2 = 1`.
example : necklace (-1) 2 = 1 := by decide +kernel

/-! ### The general theorems in use -/

/-- Fermat's little theorem. -/
example (a : ℤ) {p : ℕ} (hp : p.Prime) : (p : ℤ) ∣ a ^ p - a :=
  necklace_prime a hp ▸ dvd_mul_right _ _

/-- The Euler-type congruence `a ^ (p ^ 2) ≡ a ^ p [ZMOD p ^ 2]`. -/
example (a : ℤ) {p : ℕ} (hp : p.Prime) : a ^ p ^ 2 ≡ a ^ p [ZMOD p ^ 2] := by
  simpa using isGaussSeq_iff_modEq.mp (isGaussSeq_pow a) p 1 1 hp

/-- `n ∣ ∑_{d ∣ n} μ(d) * a ^ (n / d)`: for `n = 6`, `6 ∣ a⁶ - a³ - a² + a`. -/
example (a : ℤ) : (6 : ℤ) ∣ a ^ 6 - a ^ 3 - a ^ 2 + a := by
  have h := isGaussSeq_pow a 6
  rw [show Nat.divisors 6 = {1, 2, 3, 6} by decide] at h
  have h6 : μ 6 = 1 := by decide +kernel
  convert h using 1
  simp [moebius_apply_prime Nat.prime_two, moebius_apply_prime Nat.prime_three, h6]
  ring

/-- Burnside: there are `14` binary necklaces of length `6`, since
`∑_{d ∣ 6} φ(d) * 2 ^ (6 / d) = 84 = 6 * 14`. -/
example : ∑ d ∈ Nat.divisors 6, (φ d : ℤ) * 2 ^ (6 / d) = 6 * 14 := by
  rw [sum_totient_mul_pow]; decide +kernel

/-- `σ(n) = ∑_{d ∣ n} d` satisfies the Gauss congruences, with orbit count `1`. -/
example : IsGaussSeq fun n => ∑ d ∈ n.divisors, (d : ℤ) :=
  isGaussSeq_iff_exists.mpr ⟨1, fun n _ => by simp⟩

/-- `n ↦ 2 ^ n + 3 ^ (2 * n)` and `n ↦ 2 ^ n * 5 ^ n - 7` satisfy the Gauss congruences. -/
example : IsGaussSeq fun n => 2 ^ n + 3 ^ (2 * n) :=
  (isGaussSeq_pow 2).add ((isGaussSeq_pow 3).comp_mul 2)
example : IsGaussSeq fun n => 2 ^ n * 5 ^ n - 7 :=
  ((isGaussSeq_pow 2).mul (isGaussSeq_pow 5)).sub (isGaussSeq_const 7)

/-- For a self-map `T` of a finite set and a prime `p`, the number of points of exact
period `p` is divisible by `p`: `p ∣ #Fix(T^[p]) - #Fix(T)`. -/
example {α : Type*} [Fintype α] [DecidableEq α] (T : α → α) {p : ℕ} (hp : p.Prime) :
    (p : ℤ) ∣ #{x | T^[p] x = x} - #{x | T x = x} := by
  have h := isGaussSeq_card_fixedPoints T p
  rw [hp.divisors, sum_pair hp.one_lt.ne, moebius_apply_prime hp, Nat.div_one,
    Nat.div_self hp.pos] at h
  simpa [sub_eq_add_neg] using h

/-- The rotation `x ↦ x + 1` of `ZMod 6` has exactly one periodic orbit of length `6`. -/
example : #(periodicOrbits (fun x : ZMod 6 => x + 1) 6) = 1 := by
  have h : orbitCount (fun n => (#{x : ZMod 6 | (· + 1)^[n] x = x} : ℤ)) 6 = 1 := by
    decide +kernel
  rw [orbitCount_card_fixedPoints _ (by norm_num)] at h
  exact_mod_cast h
