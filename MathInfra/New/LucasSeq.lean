module

public import Mathlib
public import MathInfra.FormalizedElsewhere.QAnalog

/-!
# Lucas sequences

For `P Q` in a commutative ring `R`, the Lucas sequences of the first and second kind are the
two basic solutions of the linear recurrence `W (n + 2) = P * W (n + 1) - Q * W n`:

* `lucasU P Q` starts `0, 1, P, P ^ 2 - Q, …`,
* `lucasV P Q` starts `2, P, P ^ 2 - 2 * Q, …`.

Mathlib has special cases (Fibonacci numbers, Chebyshev and Dickson polynomials) and this
project has `q`-numbers, but neither has the general theory. Having it once means that
addition and doubling formulas, divisibility and the behaviour modulo a prime are proved a
single time and specialise to Fibonacci and Mersenne numbers, `q`-numbers, and Dickson and
Chebyshev polynomials. The last section is the starting point for Lucas-type primality tests.

Write `D = P ^ 2 - 4 * Q` for the discriminant.

## Main definitions

* `lucasU P Q n`, `lucasV P Q n` : the two Lucas sequences.
* `IsLucasRec P Q W`            : `W : ℕ → R` satisfies the recurrence.

## Main results

Algebra, in any commutative ring:

* `IsLucasRec.add_succ`     : `W (m + n + 1) = U (n + 1) * W (m + 1) - Q * U n * W m`.
* `IsLucasRec.add_two_mul`  : `W (k + 2 * m) = V m * W (k + m) - Q ^ m * W k`.
* `lucasU_add_succ`, `two_mul_lucasU_add`, `two_mul_lucasV_add` : addition formulas.
* `lucasU_two_mul`, `lucasV_two_mul`, `lucasU_two_mul_add_one` : doubling formulas.
* `lucasU_cassini`, `lucasV_sq`   : `U (n + 1) ^ 2 - U n * U (n + 2) = Q ^ n` and
  `V n ^ 2 = D * U n ^ 2 + 4 * Q ^ n`.
* `lucasU_mul`, `lucasV_mul`      : composition, `U (m * n) = U m * U' n` and `V (m * n) = V' n`
  where `U'`, `V'` have parameters `(V m, Q ^ m)`.
* `lucasU_dvd_lucasU`             : `m ∣ n → U m ∣ U n`.
* `lucasU_binet`, `lucasV_binet`  : Binet formulas, without division.
* `pow_succ_eq_lucasU`, `two_mul_add_pow` : powers of a root of `x ^ 2 - P * x + Q`, and of
  `P + s` where `s ^ 2 = D`.

Special cases:

* `lucasU_one_neg_one` (Fibonacci), `lucasU_add_one_self` (`q`-numbers), `lucasU_two_one`,
  `lucasU_three_two` (Mersenne), `lucasV_X_C`, `lucasU_succ_X_C` (Dickson polynomials),
  `lucasV_X_one`, `lucasU_succ_X_one` (Chebyshev polynomials).

Arithmetic, when `P` and `Q` are coprime:

* `isCoprime_lucasU_lucasU_succ`  : consecutive terms are coprime.
* `dvd_lucasU_gcd_iff`            : `d ∣ U (gcd m n) ↔ d ∣ U m ∧ d ∣ U n`.
* `Int.gcd_lucasU`                : over `ℤ`, `gcd (U m) (U n) = |U (gcd m n)|`.

Modulo an odd prime `p` (integers `P`, `Q`):

* `lucasV_prime_modEq`            : `V p ≡ P`.
* `lucasU_prime_modEq`            : `U p ≡ (D / p)`, the Legendre symbol.
* `prime_dvd_lucasU_sub_legendreSym` : the law of apparition, `p ∣ U (p - (D / p))` if `p ∤ Q`.
-/

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S] (P Q : R)

/-! ### Definitions and first values -/

/-- The Lucas sequence of the first kind: `U 0 = 0`, `U 1 = 1` and
`U (n + 2) = P * U (n + 1) - Q * U n`. -/
def lucasU : ℕ → R
  | 0 => 0
  | 1 => 1
  | n + 2 => P * lucasU (n + 1) - Q * lucasU n

/-- The Lucas sequence of the second kind: `V 0 = 2`, `V 1 = P` and
`V (n + 2) = P * V (n + 1) - Q * V n`. -/
def lucasV : ℕ → R
  | 0 => 2
  | 1 => P
  | n + 2 => P * lucasV (n + 1) - Q * lucasV n

@[simp] theorem lucasU_zero : lucasU P Q 0 = 0 := rfl

@[simp] theorem lucasU_one : lucasU P Q 1 = 1 := rfl

theorem lucasU_add_two (n : ℕ) :
    lucasU P Q (n + 2) = P * lucasU P Q (n + 1) - Q * lucasU P Q n := rfl

@[simp] theorem lucasU_two : lucasU P Q 2 = P := by simp [lucasU_add_two]

theorem lucasU_three : lucasU P Q 3 = P ^ 2 - Q := by simp [lucasU_add_two]; ring

@[simp] theorem lucasV_zero : lucasV P Q 0 = 2 := rfl

@[simp] theorem lucasV_one : lucasV P Q 1 = P := rfl

theorem lucasV_add_two (n : ℕ) :
    lucasV P Q (n + 2) = P * lucasV P Q (n + 1) - Q * lucasV P Q n := rfl

theorem lucasV_two : lucasV P Q 2 = P ^ 2 - 2 * Q := by simp [lucasV_add_two]; ring

theorem map_lucasU (f : R →+* S) (n : ℕ) : f (lucasU P Q n) = lucasU (f P) (f Q) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 => simp [lucasU_add_two, ih1, ih2]

theorem map_lucasV (f : R →+* S) (n : ℕ) : f (lucasV P Q n) = lucasV (f P) (f Q) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [map_ofNat]
  | one => simp
  | more n ih1 ih2 => simp [lucasV_add_two, ih1, ih2]

/-- Put index arithmetic such as `m + (n + 1) + 2` into the form `m + (n + 3)` everywhere, so
that equal terms of a sequence are syntactically equal. -/
local macro "norm_idx" : tactic =>
  `(tactic| simp only [Nat.add_assoc, Nat.reduceAdd] at *)

/-! ### General solutions of the recurrence -/

/-- `W` satisfies the Lucas recurrence `W (n + 2) = P * W (n + 1) - Q * W n`. -/
def IsLucasRec (W : ℕ → R) : Prop := ∀ n, W (n + 2) = P * W (n + 1) - Q * W n

theorem isLucasRec_lucasU : IsLucasRec P Q (lucasU P Q) := lucasU_add_two P Q

theorem isLucasRec_lucasV : IsLucasRec P Q (lucasV P Q) := lucasV_add_two P Q

variable {P Q}

/-- The shift formula: any solution, shifted by `m`, is a combination of `W (m + 1)` and
`W m` with coefficients from `lucasU`. -/
theorem IsLucasRec.add_succ {W : ℕ → R} (h : IsLucasRec P Q W) (m n : ℕ) :
    W (m + n + 1) = lucasU P Q (n + 1) * W (m + 1) - Q * lucasU P Q n * W m := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simpa using h m
  | more n ih1 ih2 =>
    have e := h (m + n + 1)
    have u1 := lucasU_add_two P Q (n + 1)
    have u0 := lucasU_add_two P Q n
    norm_idx
    linear_combination e + P * ih2 - Q * ih1 - W (m + 1) * u1 + Q * W m * u0

/-- A solution is determined by its first two values. -/
theorem IsLucasRec.eq_lucasU {W : ℕ → R} (h : IsLucasRec P Q W) (n : ℕ) :
    W (n + 1) = W 1 * lucasU P Q (n + 1) - Q * W 0 * lucasU P Q n := by
  have := h.add_succ 0 n
  simp only [zero_add] at this
  linear_combination this

theorem IsLucasRec.ext {W W' : ℕ → R} (h : IsLucasRec P Q W) (h' : IsLucasRec P Q W')
    (h0 : W 0 = W' 0) (h1 : W 1 = W' 1) : W = W' := by
  funext n
  cases n with
  | zero => exact h0
  | succ n => rw [h.eq_lucasU, h'.eq_lucasU, h0, h1]

/-- For any solution `W`: `W (k + 2 * m) = V m * W (k + m) - Q ^ m * W k`. -/
theorem IsLucasRec.add_two_mul {W : ℕ → R} (h : IsLucasRec P Q W) (k m : ℕ) :
    W (k + 2 * m) = lucasV P Q m * W (k + m) - Q ^ m * W k := by
  induction m using Nat.twoStepInduction generalizing k with
  | zero => simp; ring
  | one => simpa using h k
  | more m ih1 ih2 =>
    have a := ih2 (k + 1)
    have b := ih1 (k + 2)
    have c := h (k + 2 * m + 2)
    have d := h k
    have v := lucasV_add_two P Q m
    rw [show k + 1 + 2 * (m + 1) = k + 2 * m + 3 by omega,
      show k + 1 + (m + 1) = k + m + 2 by omega] at a
    rw [show k + 2 + 2 * m = k + 2 * m + 2 by omega, show k + 2 + m = k + m + 2 by omega] at b
    rw [show k + 2 * (m + 2) = k + 2 * m + 4 by omega, show k + (m + 2) = k + m + 2 by omega]
    norm_idx
    linear_combination c + P * a - Q * b - W (k + (m + 2)) * v + Q ^ (m + 1) * d

variable (P Q)

/-! ### Relations between `U` and `V` -/

theorem lucasV_eq_two_mul (n : ℕ) :
    lucasV P Q n = 2 * lucasU P Q (n + 1) - P * lucasU P Q n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp; ring
  | more n ih1 ih2 =>
    have v := lucasV_add_two P Q n
    have u1 := lucasU_add_two P Q (n + 1)
    have u0 := lucasU_add_two P Q n
    norm_idx
    linear_combination v + P * ih2 - Q * ih1 - 2 * u1 + P * u0

/-- `V (n + 1) = U (n + 2) - Q * U n`. -/
theorem lucasV_succ (n : ℕ) :
    lucasV P Q (n + 1) = lucasU P Q (n + 2) - Q * lucasU P Q n := by
  have t := lucasV_eq_two_mul P Q (n + 1)
  have u0 := lucasU_add_two P Q n
  norm_idx
  linear_combination t + u0

/-- `V (n + 1) = P * U (n + 1) - 2 * Q * U n`. -/
theorem lucasV_succ' (n : ℕ) :
    lucasV P Q (n + 1) = P * lucasU P Q (n + 1) - 2 * Q * lucasU P Q n := by
  have t := lucasV_eq_two_mul P Q (n + 1)
  have u0 := lucasU_add_two P Q n
  norm_idx
  linear_combination t + 2 * u0

theorem two_mul_lucasU_succ (n : ℕ) :
    2 * lucasU P Q (n + 1) = P * lucasU P Q n + lucasV P Q n := by
  linear_combination -lucasV_eq_two_mul P Q n

theorem two_mul_lucasV_succ (n : ℕ) :
    2 * lucasV P Q (n + 1) = P * lucasV P Q n + (P ^ 2 - 4 * Q) * lucasU P Q n := by
  linear_combination 2 * lucasV_succ' P Q n - P * lucasV_eq_two_mul P Q n

/-! ### Addition formulas -/

/-- `U (m + n + 1) = U (m + 1) * U (n + 1) - Q * U m * U n`. -/
theorem lucasU_add_succ (m n : ℕ) :
    lucasU P Q (m + n + 1)
      = lucasU P Q (m + 1) * lucasU P Q (n + 1) - Q * lucasU P Q m * lucasU P Q n := by
  linear_combination (isLucasRec_lucasU P Q).add_succ m n

/-- `2 * U (m + n) = U m * V n + U n * V m`. -/
theorem two_mul_lucasU_add (m n : ℕ) :
    2 * lucasU P Q (m + n) = lucasU P Q m * lucasV P Q n + lucasU P Q n * lucasV P Q m := by
  cases n with
  | zero => simp; ring
  | succ n =>
    have a := lucasU_add_succ P Q m n
    have t := lucasV_succ' P Q n
    have t' := lucasV_eq_two_mul P Q m
    norm_idx
    linear_combination 2 * a - lucasU P Q m * t - lucasU P Q (n + 1) * t'

/-- `2 * V (m + n) = V m * V n + D * U m * U n`. -/
theorem two_mul_lucasV_add (m n : ℕ) :
    2 * lucasV P Q (m + n)
      = lucasV P Q m * lucasV P Q n + (P ^ 2 - 4 * Q) * lucasU P Q m * lucasU P Q n := by
  cases n with
  | zero => simp; ring
  | succ n =>
    have b := (isLucasRec_lucasV P Q).add_succ m n
    have s := two_mul_lucasV_succ P Q m
    have t := lucasV_succ' P Q n
    norm_idx
    linear_combination 2 * b + lucasU P Q (n + 1) * s - lucasV P Q m * t

/-! ### Quadratic identities -/

/-- Cassini's identity for Lucas sequences. -/
theorem lucasU_cassini (n : ℕ) :
    lucasU P Q (n + 1) ^ 2 - lucasU P Q n * lucasU P Q (n + 2) = Q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have u1 := lucasU_add_two P Q (n + 1)
    have u0 := lucasU_add_two P Q n
    norm_idx
    linear_combination Q * ih - lucasU P Q (n + 1) * u1 + lucasU P Q (n + 2) * u0

/-- `V n ^ 2 = D * U n ^ 2 + 4 * Q ^ n`: the pair `(V n, U n)` solves a Pell-type equation. -/
theorem lucasV_sq (n : ℕ) :
    lucasV P Q n ^ 2 = (P ^ 2 - 4 * Q) * lucasU P Q n ^ 2 + 4 * Q ^ n := by
  have t := lucasV_eq_two_mul P Q n
  have c := lucasU_cassini P Q n
  have u0 := lucasU_add_two P Q n
  linear_combination (lucasV P Q n + 2 * lucasU P Q (n + 1) - P * lucasU P Q n) * t + 4 * c
    + 4 * lucasU P Q n * u0

/-! ### Doubling formulas -/

/-- `U (2 * n) = U n * V n`. -/
theorem lucasU_two_mul (n : ℕ) : lucasU P Q (2 * n) = lucasU P Q n * lucasV P Q n := by
  cases n with
  | zero => simp
  | succ n =>
    have a := lucasU_add_succ P Q n (n + 1)
    have t := lucasV_succ P Q n
    rw [show 2 * (n + 1) = n + (n + 1) + 1 by omega]
    norm_idx
    linear_combination a - lucasU P Q (n + 1) * t

/-- `V (2 * n) = V n ^ 2 - 2 * Q ^ n`. -/
theorem lucasV_two_mul (n : ℕ) : lucasV P Q (2 * n) = lucasV P Q n ^ 2 - 2 * Q ^ n := by
  have := (isLucasRec_lucasV P Q).add_two_mul 0 n
  simp only [zero_add, lucasV_zero] at this
  linear_combination this

/-- `U (2 * n + 1) = U (n + 1) ^ 2 - Q * U n ^ 2`. -/
theorem lucasU_two_mul_add_one (n : ℕ) :
    lucasU P Q (2 * n + 1) = lucasU P Q (n + 1) ^ 2 - Q * lucasU P Q n ^ 2 := by
  rw [two_mul]
  linear_combination lucasU_add_succ P Q n n

/-- `U (k + 2 * m) + Q ^ m * U k = V m * U (k + m)`. -/
theorem lucasU_add_two_mul (k m : ℕ) :
    lucasU P Q (k + 2 * m) + Q ^ m * lucasU P Q k = lucasV P Q m * lucasU P Q (k + m) := by
  linear_combination (isLucasRec_lucasU P Q).add_two_mul k m

/-- `V (k + 2 * m) + Q ^ m * V k = V m * V (k + m)`. -/
theorem lucasV_add_two_mul (k m : ℕ) :
    lucasV P Q (k + 2 * m) + Q ^ m * lucasV P Q k = lucasV P Q m * lucasV P Q (k + m) := by
  linear_combination (isLucasRec_lucasV P Q).add_two_mul k m

/-! ### Composition and divisibility -/

/-- Composition: `U (m * n)` for `(P, Q)` is `U m` times `U n` for `(V m, Q ^ m)`. -/
theorem lucasU_mul (m n : ℕ) :
    lucasU P Q (m * n) = lucasU P Q m * lucasU (lucasV P Q m) (Q ^ m) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
    have a := (isLucasRec_lucasU P Q).add_two_mul (m * n) m
    rw [mul_add_one] at ih2
    rw [show m * (n + 2) = m * n + 2 * m by ring, a, ih2, ih1,
      lucasU_add_two (lucasV P Q m) (Q ^ m)]
    ring

/-- Composition: `V (m * n)` for `(P, Q)` is `V n` for `(V m, Q ^ m)`. -/
theorem lucasV_mul (m n : ℕ) :
    lucasV P Q (m * n) = lucasV (lucasV P Q m) (Q ^ m) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
    have a := (isLucasRec_lucasV P Q).add_two_mul (m * n) m
    rw [mul_add_one] at ih2
    rw [show m * (n + 2) = m * n + 2 * m by ring, a, ih2, ih1,
      lucasV_add_two (lucasV P Q m) (Q ^ m)]

theorem lucasU_dvd_lucasU_mul (m n : ℕ) : lucasU P Q m ∣ lucasU P Q (m * n) :=
  Dvd.intro _ (lucasU_mul P Q m n).symm

/-- `lucasU P Q` is a divisibility sequence. -/
theorem lucasU_dvd_lucasU {m n : ℕ} (h : m ∣ n) : lucasU P Q m ∣ lucasU P Q n := by
  obtain ⟨k, rfl⟩ := h
  exact lucasU_dvd_lucasU_mul P Q m k

theorem isDvdSequence_lucasU : IsDvdSequence (lucasU P Q) :=
  fun _ _ h => lucasU_dvd_lucasU P Q h

/-! ### Binet formulas and powers of roots -/

/-- If `a` is a root of `x ^ 2 - P * x + Q` then `a ^ (n + 1) = U (n + 1) * a - Q * U n`. -/
theorem pow_succ_eq_lucasU {a : R} (ha : a ^ 2 = P * a - Q) (n : ℕ) :
    a ^ (n + 1) = lucasU P Q (n + 1) * a - Q * lucasU P Q n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have u0 := lucasU_add_two P Q n
    norm_idx
    linear_combination a * ih + lucasU P Q (n + 1) * ha - a * u0

/-- Binet's formula for `U`, without division: `(a - b) * U n = a ^ n - b ^ n` when
`P = a + b` and `Q = a * b`. -/
theorem lucasU_binet (a b : R) (n : ℕ) : (a - b) * lucasU (a + b) (a * b) n = a ^ n - b ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
    have u0 := lucasU_add_two (a + b) (a * b) n
    linear_combination (a - b) * u0 + (a + b) * ih2 - a * b * ih1

/-- Binet's formula for `V`: `V n = a ^ n + b ^ n` when `P = a + b` and `Q = a * b`. -/
theorem lucasV_binet (a b : R) (n : ℕ) : lucasV (a + b) (a * b) n = a ^ n + b ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp; norm_num
  | one => simp
  | more n ih1 ih2 =>
    have v0 := lucasV_add_two (a + b) (a * b) n
    linear_combination v0 + (a + b) * ih2 - a * b * ih1

/-- If `a` is a root of `x ^ 2 - P * x + Q` then `V n = a ^ n + (P - a) ^ n`. -/
theorem lucasV_eq_pow_add_pow {a : R} (ha : a ^ 2 = P * a - Q) (n : ℕ) :
    lucasV P Q n = a ^ n + (P - a) ^ n := by
  have := lucasV_binet a (P - a) n
  rwa [show a + (P - a) = P by ring, show a * (P - a) = Q by linear_combination -ha] at this

/-- If `s` is a square root of the discriminant then
`2 * (P + s) ^ n = 2 ^ n * (V n + U n * s)`; informally
`((P + √D) / 2) ^ n = (V n + U n √D) / 2`. -/
theorem two_mul_add_pow {s : R} (hs : s ^ 2 = P ^ 2 - 4 * Q) (n : ℕ) :
    2 * (P + s) ^ n = 2 ^ n * (lucasV P Q n + lucasU P Q n * s) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have sU := two_mul_lucasU_succ P Q n
    have sV := two_mul_lucasV_succ P Q n
    linear_combination (P + s) * ih + 2 ^ n * lucasU P Q n * hs - 2 ^ n * sV - 2 ^ n * s * sU

/-! ### Special cases -/

/-- `P = 2`, `Q = 1` (a double root): `U n = n`. -/
@[simp] theorem lucasU_two_one (n : ℕ) : lucasU (2 : R) 1 n = n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
    have u0 := lucasU_add_two (2 : R) 1 n
    push_cast at ih2 ⊢
    linear_combination u0 + 2 * ih2 - ih1

@[simp] theorem lucasV_two_one (n : ℕ) : lucasV (2 : R) 1 n = 2 := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
    have v0 := lucasV_add_two (2 : R) 1 n
    linear_combination v0 + 2 * ih2 - ih1

/-- `P = 1`, `Q = -1`: the Fibonacci numbers. -/
theorem lucasU_one_neg_one (n : ℕ) : lucasU (1 : R) (-1) n = (Nat.fib n : R) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
    have u0 := lucasU_add_two (1 : R) (-1) n
    rw [Nat.fib_add_two]
    push_cast
    linear_combination u0 + ih2 + ih1

/-- `P = 1`, `Q = -1`: the Lucas numbers `L (n + 1) = F (n + 2) + F n`. -/
theorem lucasV_one_neg_one_succ (n : ℕ) :
    lucasV (1 : R) (-1) (n + 1) = (Nat.fib (n + 2) : R) + (Nat.fib n : R) := by
  rw [lucasV_succ, lucasU_one_neg_one, lucasU_one_neg_one]
  ring

/-- `P = q + 1`, `Q = q` (roots `q` and `1`): the `q`-numbers of
`MathInfra.FormalizedElsewhere.QAnalog`. -/
theorem lucasU_add_one_self (q : R) (n : ℕ) : lucasU (q + 1) q n = qNat q n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
    have u0 := lucasU_add_two (q + 1) q n
    have k1 := qNat_succ q (n + 1)
    have k0 := qNat_succ q n
    norm_idx
    linear_combination u0 + (q + 1) * ih2 - q * ih1 - k1 + q * k0

theorem lucasV_add_one_self (q : R) (n : ℕ) : lucasV (q + 1) q n = q ^ n + 1 := by
  simpa using lucasV_binet q 1 n

/-- `P = 3`, `Q = 2`: the Mersenne numbers. -/
theorem lucasU_three_two (n : ℕ) : lucasU (3 : R) 2 n = 2 ^ n - 1 := by
  have h := lucasU_binet (2 : R) 1 n
  norm_num at h
  exact h

theorem lucasV_three_two (n : ℕ) : lucasV (3 : R) 2 n = 2 ^ n + 1 := by
  have h := lucasV_binet (2 : R) 1 n
  norm_num at h
  exact h

section Polynomial

open Polynomial

/-- With `P = X` and `Q` constant, `V` is the Dickson polynomial of the first kind. -/
theorem lucasV_X_C (a : R) (n : ℕ) : lucasV (X : R[X]) (C a) n = dickson 1 a n := by
  induction n using Nat.twoStepInduction with
  | zero => simp; norm_num
  | one => simp
  | more n ih1 ih2 => rw [lucasV_add_two, dickson_add_two, ih1, ih2]

/-- With `P = X` and `Q` constant, `U` is the Dickson polynomial of the second kind. -/
theorem lucasU_succ_X_C (a : R) (n : ℕ) : lucasU (X : R[X]) (C a) (n + 1) = dickson 2 a n := by
  induction n using Nat.twoStepInduction with
  | zero => simp; norm_num
  | one => simp
  | more n ih1 ih2 =>
    change lucasU (X : R[X]) (C a) (n + 1 + 2) = _
    rw [lucasU_add_two, dickson_add_two, ih1, ih2]

/-- Every `V n` is a Dickson polynomial in `P`. -/
theorem lucasV_eq_eval_dickson (n : ℕ) : lucasV P Q n = (dickson 1 Q n).eval P := by
  rw [← lucasV_X_C]
  simpa using (map_lucasV (X : R[X]) (C Q) (evalRingHom P) n).symm

theorem lucasU_succ_eq_eval_dickson (n : ℕ) : lucasU P Q (n + 1) = (dickson 2 Q n).eval P := by
  rw [← lucasU_succ_X_C]
  simpa using (map_lucasU (X : R[X]) (C Q) (evalRingHom P) (n + 1)).symm

/-- With `P = X`, `Q = 1`, `V` is the rescaled Chebyshev polynomial `C n` (`= 2 T n (X / 2)`). -/
theorem lucasV_X_one (n : ℕ) : lucasV (X : R[X]) 1 n = Chebyshev.C R n := by
  rw [← dickson_one_one_eq_chebyshev_C, ← lucasV_X_C, map_one]

/-- With `P = X`, `Q = 1`, `U` is the rescaled Chebyshev polynomial `S n` (`= U n (X / 2)`). -/
theorem lucasU_succ_X_one (n : ℕ) : lucasU (X : R[X]) 1 (n + 1) = Chebyshev.S R n := by
  rw [← dickson_two_one_eq_chebyshev_S, ← lucasU_succ_X_C, map_one]

end Polynomial

/-! ### Coprimality and strong divisibility -/

section Coprime

variable {P Q} (h : IsCoprime P Q)
include h

/-- If `P` and `Q` are coprime then every `U (n + 1)` is coprime to `Q`. -/
theorem isCoprime_lucasU_succ_right (n : ℕ) : IsCoprime (lucasU P Q (n + 1)) Q := by
  induction n with
  | zero => simpa using isCoprime_one_left
  | succ n ih =>
    have := (h.mul_left ih).add_mul_left_left (-lucasU P Q n)
    rw [lucasU_add_two]
    convert this using 1
    ring

/-- If `P` and `Q` are coprime then consecutive terms of `U` are coprime. -/
theorem isCoprime_lucasU_lucasU_succ (n : ℕ) :
    IsCoprime (lucasU P Q n) (lucasU P Q (n + 1)) := by
  induction n with
  | zero => simpa using isCoprime_one_right
  | succ n ih =>
    have c : IsCoprime (lucasU P Q (n + 1)) (Q * lucasU P Q n) :=
      (isCoprime_lucasU_succ_right h n).mul_right ih.symm
    have := c.neg_right.add_mul_left_right P
    rw [lucasU_add_two]
    convert this using 1
    ring

theorem dvd_lucasU_add_iff {d : R} {m : ℕ} (hd : d ∣ lucasU P Q m) (n : ℕ) :
    d ∣ lucasU P Q (n + m) ↔ d ∣ lucasU P Q n := by
  cases m with
  | zero => simp
  | succ k =>
    have c : IsCoprime d (Q * lucasU P Q k) :=
      IsCoprime.of_isCoprime_of_dvd_left
        ((isCoprime_lucasU_succ_right h k).mul_right (isCoprime_lucasU_lucasU_succ h k).symm) hd
    rw [show n + (k + 1) = k + n + 1 by omega, lucasU_add_succ, dvd_sub_right (hd.mul_right _)]
    constructor
    · intro h'
      exact c.dvd_of_dvd_mul_left (by convert h' using 1)
    · intro h'
      exact dvd_mul_of_dvd_right h' _

theorem dvd_lucasU_add_mul_iff {d : R} {m : ℕ} (hd : d ∣ lucasU P Q m) (n k : ℕ) :
    d ∣ lucasU P Q (n + k * m) ↔ d ∣ lucasU P Q n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show n + (k + 1) * m = n + k * m + m by ring, dvd_lucasU_add_iff h hd, ih]

/-- **Strong divisibility.** If `P` and `Q` are coprime, the common divisors of `U m` and
`U n` are exactly the divisors of `U (gcd m n)`. -/
theorem dvd_lucasU_gcd_iff (d : R) (m n : ℕ) :
    d ∣ lucasU P Q (Nat.gcd m n) ↔ d ∣ lucasU P Q m ∧ d ∣ lucasU P Q n := by
  induction m, n using Nat.gcd.induction with
  | H0 n => simp
  | H1 m n _ ih =>
    rw [Nat.gcd_rec, ih]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2, ?_⟩
      have := (dvd_lucasU_add_mul_iff h h2 (n % m) (n / m)).mpr h1
      rwa [Nat.mod_add_div'] at this
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h1⟩
      rw [← Nat.mod_add_div' n m] at h2
      exact (dvd_lucasU_add_mul_iff h h1 (n % m) (n / m)).mp h2

omit h in
/-- Strong divisibility over `ℤ`: `gcd (U m) (U n) = |U (gcd m n)|` for coprime `P`, `Q`. -/
theorem Int.gcd_lucasU {P Q : ℤ} (h : IsCoprime P Q) (m n : ℕ) :
    Int.gcd (lucasU P Q m) (lucasU P Q n) = (lucasU P Q (Nat.gcd m n)).natAbs := by
  apply Nat.dvd_antisymm
  · exact Int.natCast_dvd.mp
      ((dvd_lucasU_gcd_iff h _ m n).mpr ⟨Int.gcd_dvd_left _ _, Int.gcd_dvd_right _ _⟩)
  · obtain ⟨h1, h2⟩ := (dvd_lucasU_gcd_iff h _ m n).mp dvd_rfl
    exact Nat.dvd_gcd (Int.natAbs_dvd_natAbs.mpr h1) (Int.natAbs_dvd_natAbs.mpr h2)

end Coprime

/-! ### Lucas sequences modulo a prime -/

section Prime

variable (p : ℕ) [Fact p.Prime]

private theorem ZMod.two_ne_zero_of_ne_two (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h2
  have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h2)
  exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)

/-- Both congruences at once: work in `(ZMod p)[s] / (s ^ 2 - D)`, where
`2 * (P + s) ^ p = 2 ^ p * (V p + U p * s)` and the left side is `2 * (P + D ^ (p / 2) * s)`
because `p`-th powers are additive; then compare coordinates. -/
private theorem ZMod.lucas_prime_aux (hp : p ≠ 2) (P Q D : ZMod p) (hD : D = P ^ 2 - 4 * Q) :
    lucasV P Q p = P ∧ lucasU P Q p = D ^ (p / 2) := by
  have : CharP (QuadraticAlgebra (ZMod p) D 0) p :=
    charP_of_injective_algebraMap QuadraticAlgebra.algebraMap_injective p
  obtain ⟨c, hc⟩ : ∃ c : ZMod p →+* QuadraticAlgebra (ZMod p) D 0,
      c = algebraMap (ZMod p) (QuadraticAlgebra (ZMod p) D 0) := ⟨_, rfl⟩
  obtain ⟨s, hs0⟩ : ∃ s : QuadraticAlgebra (ZMod p) D 0, s = ⟨0, 1⟩ := ⟨_, rfl⟩
  have hs2 : s ^ 2 = c D := by
    subst hs0 hc
    ext <;> simp [pow_two]
  have hs : s ^ 2 = c P ^ 2 - 4 * c Q := by
    rw [hs2, ← map_pow, ← map_ofNat c 4, ← map_mul, ← map_sub]
    exact congrArg c hD
  have key := two_mul_add_pow (c P) (c Q) hs p
  have hodd : p = 2 * (p / 2) + 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd' with h | h
    · exact absurd h hp
    · have := Nat.odd_iff.mp h; omega
  have hsp : s ^ p = c (D ^ (p / 2)) * s := by
    have e : s ^ p = s ^ (2 * (p / 2) + 1) := congrArg (s ^ ·) hodd
    rw [e, pow_succ, pow_mul, hs2, map_pow]
  have h2p : (2 : QuadraticAlgebra (ZMod p) D 0) ^ p = 2 := by
    rw [← map_ofNat c 2, ← map_pow, ZMod.pow_card]
  have hPp : c P ^ p = c P := by rw [← map_pow, ZMod.pow_card]
  have hmk : ∀ x y : ZMod p, c x + c y * s = ⟨x, y⟩ := by
    intro x y
    subst hs0 hc
    ext <;> simp
  rw [add_pow_char, hsp, h2p, hPp, ← map_lucasV, ← map_lucasU, hmk, hmk] at key
  have h2 := ZMod.two_ne_zero_of_ne_two p hp
  have hre := congrArg QuadraticAlgebra.re key
  have him := congrArg QuadraticAlgebra.im key
  simp [QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] at hre him
  exact ⟨(hre.resolve_right h2).symm, (him.resolve_right h2).symm⟩

/-- For an odd prime `p`, `V p = P` in `ZMod p`. -/
theorem ZMod.lucasV_prime (hp : p ≠ 2) (P Q : ZMod p) : lucasV P Q p = P :=
  (ZMod.lucas_prime_aux p hp P Q _ rfl).1

/-- For an odd prime `p`, `U p = D ^ (p / 2)` in `ZMod p`, where `p / 2 = (p - 1) / 2`
(Euler's criterion turns this into the Legendre symbol of `D`). -/
theorem ZMod.lucasU_prime (hp : p ≠ 2) (P Q : ZMod p) :
    lucasU P Q p = (P ^ 2 - 4 * Q) ^ (p / 2) :=
  (ZMod.lucas_prime_aux p hp P Q _ rfl).2

private theorem intCast_lucasU (P Q : ℤ) (n : ℕ) :
    ((lucasU P Q n : ℤ) : ZMod p) = lucasU (P : ZMod p) (Q : ZMod p) n := by
  simpa using map_lucasU P Q (Int.castRingHom (ZMod p)) n

private theorem intCast_lucasV (P Q : ℤ) (n : ℕ) :
    ((lucasV P Q n : ℤ) : ZMod p) = lucasV (P : ZMod p) (Q : ZMod p) n := by
  simpa using map_lucasV P Q (Int.castRingHom (ZMod p)) n

private theorem intCast_lucasU_prime (hp : p ≠ 2) (P Q : ℤ) :
    lucasU (P : ZMod p) (Q : ZMod p) p = (legendreSym p (P ^ 2 - 4 * Q) : ZMod p) := by
  rw [ZMod.lucasU_prime p hp, legendreSym.eq_pow]
  push_cast
  rfl

/-- For an odd prime `p` and integers `P`, `Q`: `V p ≡ P (mod p)`. -/
theorem lucasV_prime_modEq (hp : p ≠ 2) (P Q : ℤ) : lucasV P Q p ≡ P [ZMOD p] := by
  rw [← ZMod.intCast_eq_intCast_iff, intCast_lucasV, ZMod.lucasV_prime p hp]

/-- For an odd prime `p` and integers `P`, `Q`: `U p ≡ (D / p) (mod p)`, the Legendre symbol
of the discriminant. -/
theorem lucasU_prime_modEq (hp : p ≠ 2) (P Q : ℤ) :
    lucasU P Q p ≡ legendreSym p (P ^ 2 - 4 * Q) [ZMOD p] := by
  rw [← ZMod.intCast_eq_intCast_iff, intCast_lucasU, intCast_lucasU_prime p hp]

/-- If `p` divides the discriminant then `p ∣ U p`. -/
theorem prime_dvd_lucasU_self (hp : p ≠ 2) (P Q : ℤ) (hD : (p : ℤ) ∣ P ^ 2 - 4 * Q) :
    (p : ℤ) ∣ lucasU P Q p := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, intCast_lucasU, intCast_lucasU_prime p hp,
    (legendreSym.eq_zero_iff p _).mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hD)]
  simp

/-- If the discriminant is a non-residue modulo `p` then `p ∣ U (p + 1)`. -/
theorem prime_dvd_lucasU_add_one (hp : p ≠ 2) (P Q : ℤ)
    (hD : legendreSym p (P ^ 2 - 4 * Q) = -1) : (p : ℤ) ∣ lucasU P Q (p + 1) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, intCast_lucasU]
  have hU := intCast_lucasU_prime p hp P Q
  have hV := ZMod.lucasV_prime p hp (P : ZMod p) (Q : ZMod p)
  have e := two_mul_lucasU_succ (P : ZMod p) (Q : ZMod p) p
  rw [hU, hV, hD] at e
  have e' : (2 : ZMod p) * lucasU (P : ZMod p) (Q : ZMod p) (p + 1) = 0 := by
    rw [e]; push_cast; ring
  exact (mul_eq_zero.mp e').resolve_left (ZMod.two_ne_zero_of_ne_two p hp)

/-- If the discriminant is a nonzero residue modulo `p` and `p ∤ Q` then `p ∣ U (p - 1)`. -/
theorem prime_dvd_lucasU_sub_one (hp : p ≠ 2) (P Q : ℤ) (hQ : ¬ (p : ℤ) ∣ Q)
    (hD : legendreSym p (P ^ 2 - 4 * Q) = 1) : (p : ℤ) ∣ lucasU P Q (p - 1) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, intCast_lucasU]
  have hQ' : (Q : ZMod p) ≠ 0 := fun h0 => hQ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0)
  have hU := intCast_lucasU_prime p hp P Q
  have hV := ZMod.lucasV_prime p hp (P : ZMod p) (Q : ZMod p)
  have e := lucasV_succ' (P : ZMod p) (Q : ZMod p) (p - 1)
  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).one_le
  rw [hp1, hU, hV, hD] at e
  have e' : (2 * (Q : ZMod p)) * lucasU (P : ZMod p) (Q : ZMod p) (p - 1) = 0 := by
    push_cast at e
    linear_combination e
  exact (mul_eq_zero.mp e').resolve_left
    (mul_ne_zero (ZMod.two_ne_zero_of_ne_two p hp) hQ')

/-- **Law of apparition.** For an odd prime `p` not dividing `Q`, `p` divides the term of
`U` with index `p - (D / p)`, where `(D / p)` is the Legendre symbol of the discriminant. In
particular every such prime divides some term `U n` with `0 < n ≤ p + 1`. -/
theorem prime_dvd_lucasU_sub_legendreSym (hp : p ≠ 2) (P Q : ℤ) (hQ : ¬ (p : ℤ) ∣ Q) :
    (p : ℤ) ∣ lucasU P Q ((p : ℤ) - legendreSym p (P ^ 2 - 4 * Q)).toNat := by
  by_cases h0 : ((P ^ 2 - 4 * Q : ℤ) : ZMod p) = 0
  · rw [(legendreSym.eq_zero_iff p _).mpr h0]
    simpa using prime_dvd_lucasU_self p hp P Q ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0)
  · rcases legendreSym.eq_one_or_neg_one p h0 with h1 | h1
    · rw [h1, show ((p : ℤ) - 1).toNat = p - 1 by omega]
      exact prime_dvd_lucasU_sub_one p hp P Q hQ h1
    · rw [h1, show ((p : ℤ) - -1).toNat = p + 1 by omega]
      exact prime_dvd_lucasU_add_one p hp P Q h1

end Prime
