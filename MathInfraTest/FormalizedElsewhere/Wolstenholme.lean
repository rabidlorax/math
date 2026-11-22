import MathInfra.FormalizedElsewhere.Wolstenholme

/-!
# Checks for `MathInfra.FormalizedElsewhere.Wolstenholme`

Known values, the bounds `p ≥ 5` and `p ≠ 2` shown to be needed, and the general theorems in
use. The axiom audit is in `MathInfraTest/FormalizedElsewhere/WolstenholmeAxioms.lean`. Both
files are part of `lake build`.
-/

open Finset

/-! ### Known values -/

-- `C(2p - 1, p - 1)` for `p = 5, 7`: `126 = 1 + 5³` and `1716 = 1 + 5 * 7³`.
example : Nat.choose 9 4 = 1 + 5 ^ 3 := by decide
example : Nat.choose 13 6 = 1 + 5 * 7 ^ 3 := by decide

-- `p = 3` satisfies Babbage but not Wolstenholme: `C(5, 2) = 10 = 1 + 9`.
example : Nat.choose 5 2 ≡ 1 [MOD 3 ^ 2] := by decide
example : ¬Nat.choose 5 2 ≡ 1 [MOD 3 ^ 3] := by decide

-- Ljunggren for `p = 3`: `C(6, 3) = 20 ≡ C(2, 1)` modulo `9` but not modulo `27`.
example : ¬Nat.choose 6 3 ≡ Nat.choose 2 1 [MOD 3 ^ 3] := by decide

-- `H₄ = 25 / 12` and `H₆ = 49 / 20`.
example : harmonic 4 = 25 / 12 := by simp [harmonic, sum_range_succ]; norm_num
example : harmonic 6 = 49 / 20 := by simp [harmonic, sum_range_succ]; norm_num

-- Fermat quotients of `2`: `q₅(2) = 3`, `q₇(2) = 9`.
example : fermatQuotient 5 2 = 3 := by decide
example : fermatQuotient 7 2 = 9 := by decide

-- Eisenstein's formula fails for `p = 2`: `2 q₂(2) = 0` but `C(2, 1) / 2 = 1`.
example : 2 * fermatQuotient 2 2 ≠ ∑ k ∈ Ico 1 2, ((Nat.choose 2 k / 2 : ℕ) : ℤ) := by decide

/-! ### The general theorems in use -/

/-- Wolstenholme's theorem for `p = 13`: `C(25, 12) ≡ 1 (mod 13³)`. -/
example : Nat.choose 25 12 ≡ 1 [MOD 13 ^ 3] :=
  choose_two_mul_sub_one_modEq_one_cube (p := 13) (by norm_num) (by norm_num)

/-- Ljunggren: `C(3p, p) ≡ 3 (mod p³)` for every prime `p ≥ 5`. -/
example {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : (3 * p).choose p ≡ 3 [MOD p ^ 3] := by
  simpa using choose_mul_modEq_choose_cube hp h5 3 1

/-- Ljunggren modulo `p²` holds for `p = 2`: `C(2a, 2b) ≡ C(a, b) (mod 4)`. -/
example (a b : ℕ) : (a * 2).choose (b * 2) ≡ a.choose b [MOD 2 ^ 2] :=
  choose_mul_modEq_choose_sq Nat.prime_two a b

/-- `5²` divides the numerator of `H₄ = 25 / 12`. -/
example : (5 : ℤ) ^ 2 ∣ (harmonic 4).num :=
  sq_dvd_num_harmonic (p := 5) (by norm_num) le_rfl

/-- `∑_{0 < k < 7} 1 / k² ≡ 0 (mod 7)`. -/
example : ∑ k ∈ Ico (1 : ℕ) 7, ((k : ZMod 7)⁻¹) ^ 2 = 0 :=
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  sum_Ico_inv_sq_eq_zero 7 (by norm_num)

/-- `1093` is a Wieferich prime: `1093 ∣ q₁₀₉₃(2)`. -/
example : (1093 : ℤ) ∣ fermatQuotient 1093 2 :=
  (dvd_fermatQuotient_iff (by norm_num) (by norm_num)).mpr (by unfold Int.ModEq; decide +kernel)

/-- `q_p(4) ≡ 2 q_p(2) (mod p)` for every odd prime `p`. -/
example {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    fermatQuotient p 4 ≡ 2 * fermatQuotient p 2 [ZMOD p] := by
  have h2 : ¬(p : ℤ) ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (by exact_mod_cast h))
  simpa [two_mul] using fermatQuotient_mul_modEq hp h2 h2

/-- Eisenstein for `p = 7`: `2 q₇(2) = 18 ≡ -(1 + 1 / 2 + 1 / 3) (mod 7)`. -/
example : 2 * (fermatQuotient 7 2 : ZMod 7) = -∑ j ∈ Icc (1 : ℕ) 3, (j : ZMod 7)⁻¹ :=
  two_mul_fermatQuotient_two_eq_neg_sum (p := 7) (by norm_num) (by norm_num)
