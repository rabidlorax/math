module

public import Mathlib

/-!
# Eulerian numbers

The Eulerian number `A(n, k)` is the number of permutations of `n` letters with exactly `k`
descents, that is, positions `i` with `σ(i + 1) < σ(i)`. The rows begin

`1;  1;  1, 1;  1, 4, 1;  1, 11, 11, 1;  1, 26, 66, 26, 1`.

Here `A(n, k)` is defined by its recurrence, and the main theorem is that it counts permutations
by descents. The polynomials `A_n(t) = ∑_k A(n, k) * tᵏ` are the Eulerian polynomials. Other
names: Euler–Frobenius numbers and polynomials. They are unrelated to the Euler numbers (secant
and tangent numbers). Some authors shift `k` by one, so that `A(n, k)` counts permutations with
`k - 1` descents; here `k` is the number of descents.

The polynomials encode the sums `∑ₘ mⁿ tᵐ`, so they appear in sums of powers, in the values of
the polylogarithm at negative integers, and as the `h*`-polynomials of hypercubes in Ehrhart
theory. Worpitzky's identity expresses `xⁿ` in the binomial basis `C(x + k, n)`.

## Main definitions

* `eulerian n k`     : the Eulerian number `A(n, k)`.
* `eulerianPoly R n` : the Eulerian polynomial `A_n(t) = ∑_k A(n, k) * tᵏ` over a commutative
  semiring `R`.
* `numDescents l`    : the number of descents of a list `l` of natural numbers.

## Main results

* `eulerian_symm`           : `A(n, n - 1 - k) = A(n, k)` for `k < n`.
* `sum_eulerian`            : `∑_k A(n, k) = n!`.
* `eulerian_one_right`      : `A(n, 1) = 2ⁿ - (n + 1)`.
* `sum_eulerian_mul_choose` : **Worpitzky's identity** `xⁿ = ∑_k A(n, k) * C(x + k, n)`.
* `eulerianPoly_succ`       : `A_{n+1}(t) = (1 + n t) A_n(t) + t (1 - t) A_n'(t)`.
* `mk_pow_mul_one_sub_pow`  : the generating function `∑ₘ (m + 1)ⁿ tᵐ = A_n(t) / (1 - t)ⁿ⁺¹`.
* `eulerian_eq_sum`         : `A(n, k) = ∑_{j ≤ k} (-1)ʲ * C(n + 1, j) * (k + 1 - j)ⁿ` in `ℤ`.
* `countP_permutations_range`, `card_perm_numDescents` : `A(n, k)` is the number of permutations
  of `0, …, n - 1` (or of `Fin n`) with exactly `k` descents.

## Prior art

As of November 2026 Mathlib (checked against `master` of 2026-11-21) has no Eulerian numbers,
and no open pull request adds them. The Isabelle AFP entry *Linear_Recurrences* (theory
`Eulerian_Polynomials`, by Manuel Eberl) defines the polynomials by the recurrence of
`eulerianPoly_succ` and proves `A_n(1) = n!` and the generating function. The descent count,
Worpitzky's identity, the symmetry and the explicit formula were not found elsewhere (the
libraries searched are listed in `EulerianNumber-proofs.md`).
-/
@[expose] public section

open Finset
open scoped Nat

/-! ### The recurrence -/

/-- The Eulerian number `A(n, k)`: `A(0, k) = 1` if `k = 0` and `0` otherwise, and
`A(n + 1, k) = (k + 1) * A(n, k) + (n + 1 - k) * A(n, k - 1)`, the last term being absent for
`k = 0`. -/
def eulerian : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => eulerian n 0
  | n + 1, k + 1 => (k + 2) * eulerian n (k + 1) + (n - k) * eulerian n k

@[simp] theorem eulerian_zero_zero : eulerian 0 0 = 1 := rfl

@[simp] theorem eulerian_zero_succ (k : ℕ) : eulerian 0 (k + 1) = 0 := rfl

theorem eulerian_succ_succ (n k : ℕ) :
    eulerian (n + 1) (k + 1) = (k + 2) * eulerian n (k + 1) + (n - k) * eulerian n k := rfl

@[simp] theorem eulerian_zero_right (n : ℕ) : eulerian n 0 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- `A(n, k) = 0` for `k ≥ n`, except `A(0, 0) = 1`. -/
theorem eulerian_eq_zero_of_le {n k : ℕ} (hk : n ≤ k) (h : 0 < k) : eulerian n k = 0 := by
  induction n generalizing k with
  | zero => obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'; rfl
  | succ n ih =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
    rw [eulerian_succ_succ, ih (by omega) (by omega), Nat.sub_eq_zero_of_le (by omega)]
    simp

/-- The recurrence, summed against any `f`:
`∑_k A(n + 1, k) • f(k) = ∑_k A(n, k) • ((k + 1) • f(k) + (n - k) • f(k + 1))`. -/
theorem sum_eulerian_succ_smul {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ k ∈ range (n + 2), eulerian (n + 1) k • f k =
      ∑ k ∈ range (n + 1), eulerian n k • ((k + 1) • f k + (n - k) • f (k + 1)) := by
  set g : ℕ → M := fun k ↦ ((k + 1) * eulerian n k) • f k
  have h : ∑ k ∈ range (n + 1), g k = ∑ k ∈ range (n + 1), g (k + 1) + g 0 := by
    rw [← sum_range_succ' g, sum_range_succ _ (n + 1)]
    simp [g, eulerian_eq_zero_of_le (Nat.le_succ n) n.succ_pos]
  have hR : ∑ k ∈ range (n + 1), eulerian n k • ((k + 1) • f k + (n - k) • f (k + 1)) =
      ∑ k ∈ range (n + 1), g k +
        ∑ k ∈ range (n + 1), ((n - k) * eulerian n k) • f (k + 1) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun k _ ↦ ?_
    simp only [g, smul_add, mul_smul, smul_comm (eulerian n k)]
  rw [hR, h, sum_range_succ', eulerian_zero_right]
  simp only [eulerian_succ_succ, add_smul, sum_add_distrib, g]
  simp [add_comm, add_left_comm]

/-! ### Symmetry and special values -/

/-- Symmetry in the form proved by induction: `A(n, i) = A(n, j)` when `i + j + 1 = n`. -/
theorem eulerian_symm_aux : ∀ n i j : ℕ, i + j + 1 = n → eulerian n i = eulerian n j
  | 0, _, _, h => by omega
  | n + 1, 0, 0, _ => rfl
  | n + 1, 0, j + 1, h => by
    rw [eulerian_succ_succ, eulerian_eq_zero_of_le (n := n) (k := j + 1) (by omega) (by omega),
      ← eulerian_symm_aux n 0 j (by omega)]
    simp [show n - j = 1 by omega]
  | n + 1, i + 1, 0, h => by
    rw [eulerian_succ_succ, eulerian_eq_zero_of_le (n := n) (k := i + 1) (by omega) (by omega),
      ← eulerian_symm_aux n 0 i (by omega)]
    simp [show n - i = 1 by omega]
  | n + 1, i + 1, j + 1, h => by
    rw [eulerian_succ_succ, eulerian_succ_succ, eulerian_symm_aux n (i + 1) j (by omega),
      eulerian_symm_aux n i (j + 1) (by omega), show i + 2 = n - j by omega,
      show n - i = j + 2 by omega, add_comm]

/-- **Symmetry**: `A(n, n - 1 - k) = A(n, k)` for `k < n`. -/
theorem eulerian_symm {n k : ℕ} (h : k < n) : eulerian n (n - 1 - k) = eulerian n k :=
  (eulerian_symm_aux n k (n - 1 - k) (by omega)).symm

/-- `A(n, n - 1) = 1` for `n > 0`: only the decreasing permutation has `n - 1` descents. -/
theorem eulerian_self_sub_one {n : ℕ} (h : 0 < n) : eulerian n (n - 1) = 1 := by
  simpa using eulerian_symm h

/-- The Eulerian numbers of each row add up to `n!`. -/
theorem sum_eulerian (n : ℕ) : ∑ k ∈ range (n + 1), eulerian n k = n ! := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := sum_eulerian_succ_smul n (fun _ ↦ 1)
    simp only [smul_eq_mul, mul_one] at this
    rw [this, Nat.factorial_succ, ← ih, mul_sum]
    refine sum_congr rfl fun k hk ↦ ?_
    rw [mem_range] at hk
    rw [mul_comm, show k + 1 + (n - k) = n + 1 by omega]

/-- `A(n, 1) = 2ⁿ - (n + 1)`. -/
theorem eulerian_one_right (n : ℕ) : eulerian n 1 = 2 ^ n - (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [eulerian_succ_succ, ih, eulerian_zero_right]
    have := Nat.lt_two_pow_self (n := n)
    rw [pow_succ]
    omega

/-! ### Worpitzky's identity -/

/-- The binomial identity behind Worpitzky's identity: for `k ≤ n`,
`x * C(x + k, n) = (k + 1) * C(x + k, n + 1) + (n - k) * C(x + k + 1, n + 1)`. -/
theorem mul_choose_add_eq {x k n : ℕ} (hk : k ≤ n) :
    x * (x + k).choose n =
      (k + 1) * (x + k).choose (n + 1) + (n - k) * (x + k + 1).choose (n + 1) := by
  rcases lt_or_ge (x + k) n with h | h
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega),
      Nat.choose_eq_zero_of_lt (by omega)]
    simp
  · obtain ⟨a, rfl⟩ : ∃ a, n = k + a := ⟨n - k, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, x = a + b := ⟨x - a, by omega⟩
    have h1 := Nat.choose_succ_right_eq (a + b + k) (k + a)
    rw [show a + b + k - (k + a) = b by omega] at h1
    rw [Nat.choose_succ_succ', show k + a - k = a by omega]
    linarith

/-- **Worpitzky's identity**: `xⁿ = ∑_k A(n, k) * C(x + k, n)`. -/
theorem sum_eulerian_mul_choose (n x : ℕ) :
    ∑ k ∈ range (n + 1), eulerian n k * (x + k).choose n = x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := sum_eulerian_succ_smul n (fun k ↦ (x + k).choose (n + 1))
    simp only [smul_eq_mul] at this
    rw [this, pow_succ, ← ih, sum_mul]
    refine sum_congr rfl fun k hk ↦ ?_
    rw [mem_range] at hk
    rw [mul_assoc, mul_comm _ x, mul_choose_add_eq (by omega), ← add_assoc]

/-! ### Eulerian polynomials and the generating function -/

section Poly

variable (R : Type*)

/-- The Eulerian polynomial `A_n(t) = ∑_k A(n, k) * tᵏ`. -/
noncomputable def eulerianPoly [CommSemiring R] (n : ℕ) : Polynomial R :=
  ∑ k ∈ range (n + 1), Polynomial.C (eulerian n k : R) * Polynomial.X ^ k

variable {R}

/-- The coefficients of `A_n(t)` are the Eulerian numbers. -/
@[simp] theorem coeff_eulerianPoly [CommSemiring R] (n k : ℕ) :
    (eulerianPoly R n).coeff k = eulerian n k := by
  simp only [eulerianPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, sum_ite_eq,
    mem_range]
  split_ifs with h
  · rfl
  · rw [eulerian_eq_zero_of_le (by omega) (by omega), Nat.cast_zero]

/-- `A_n(1) = n!`. -/
theorem eulerianPoly_eval_one [CommSemiring R] (n : ℕ) : (eulerianPoly R n).eval 1 = n ! := by
  simp [eulerianPoly, Polynomial.eval_finsetSum, ← sum_eulerian n]

open PowerSeries in
/-- `A_n(t)` as a power series. -/
theorem coe_eulerianPoly [CommSemiring R] (n : ℕ) :
    (eulerianPoly R n : R⟦X⟧) = ∑ k ∈ range (n + 1), (eulerian n k : R) • X ^ k := by
  rw [eulerianPoly, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
  simp only [map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C,
    Polynomial.coe_X, smul_eq_C_mul]

open Polynomial in
/-- `A_{n+1}(t) = (1 + n t) A_n(t) + t (1 - t) A_n'(t)`. This recurrence defines the Eulerian
polynomials in the AFP entry *Linear_Recurrences*. -/
theorem eulerianPoly_succ [CommRing R] (n : ℕ) :
    eulerianPoly R (n + 1) = (1 + (n : R[X]) * X) * eulerianPoly R n +
      X * (1 - X) * derivative (eulerianPoly R n) := by
  ext k
  rcases k with _ | k
  · simp [mul_coeff_zero]
  · have h2 : (X * (1 - X) * derivative (eulerianPoly R n)).coeff (k + 1) =
        ((k + 1 : ℕ) : R) * eulerian n (k + 1) - (k : R) * eulerian n k := by
      rw [mul_sub, mul_one, sub_mul, coeff_sub, coeff_X_mul, ← pow_two, coeff_X_pow_mul',
        coeff_derivative, coeff_eulerianPoly]
      rcases k with _ | k
      · simp
      · simp [coeff_derivative]
        ring
    rw [coeff_add, h2, add_mul, one_mul, coeff_add, mul_assoc, coeff_natCast_mul, coeff_X_mul,
      coeff_eulerianPoly, coeff_eulerianPoly, coeff_eulerianPoly, eulerian_succ_succ]
    rcases le_or_gt k n with hk | hk
    · push_cast [hk]
      ring
    · rw [eulerian_eq_zero_of_le (n := n) (k := k) (by omega) (by omega),
        Nat.sub_eq_zero_of_le hk.le]
      push_cast
      ring

open PowerSeries in
/-- **The generating function**: `(∑_m (m + 1)ⁿ tᵐ) * (1 - t)ⁿ⁺¹ = A_n(t)`, that is,
`∑_m (m + 1)ⁿ tᵐ = A_n(t) / (1 - t)ⁿ⁺¹`. -/
theorem mk_pow_mul_one_sub_pow [CommRing R] (n : ℕ) :
    (mk fun m : ℕ ↦ (m + 1 : R) ^ n) * (1 - X) ^ (n + 1) = (eulerianPoly R n : R⟦X⟧) := by
  rw [coe_eulerianPoly]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [← Pi.one_def, mk_one_mul_one_sub_eq_one]
  have hW : (mk fun m : ℕ ↦ (m + 1 : R) ^ n) =
      ∑ k ∈ range (n + 1),
        (eulerian n k : R) • mk fun m : ℕ ↦ ((m + 1 + k).choose n : R) := by
    ext m
    have := congrArg (Nat.cast : ℕ → R) (sum_eulerian_mul_choose n (m + 1))
    push_cast at this
    simp only [coeff_mk, map_sum, coeff_smul, smul_eq_mul, this]
  have hk (k : ℕ) (hk : k < n) :
      (mk fun m : ℕ ↦ ((m + 1 + k).choose n : R)) * (1 - X) ^ (n + 1) = X ^ (n - 1 - k) := by
    have : (mk fun m : ℕ ↦ ((m + 1 + k).choose n : R)) =
        X ^ (n - 1 - k) * (invOneSubPow R (n + 1)).val := by
      ext m
      rw [invOneSubPow_val_succ_eq_mk_add_choose, coeff_X_pow_mul', coeff_mk]
      split_ifs with h
      · rw [coeff_mk, show m + 1 + k = n + (m - (n - 1 - k)) by omega]
      · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    rw [this, mul_assoc, ← invOneSubPow_inv_eq_one_sub_pow, Units.val_inv, mul_one]
  rw [hW, sum_mul, sum_range_succ, sum_range_succ, eulerian_eq_zero_of_le le_rfl hn]
  simp only [Nat.cast_zero, zero_smul, add_zero, smul_mul_assoc]
  rw [sum_congr rfl (g := fun k ↦ (eulerian n k : R) • X ^ (n - 1 - k)) fun k hk' ↦ by
    rw [hk k (mem_range.mp hk')],
    ← sum_range_reflect (fun k ↦ (eulerian n k : R) • X ^ (n - 1 - k))]
  rw [zero_mul, add_zero]
  refine sum_congr rfl fun k hk' ↦ ?_
  rw [mem_range] at hk'
  rw [eulerian_symm hk', show n - 1 - (n - 1 - k) = k by omega]

end Poly

/-! ### The explicit formula -/

open PowerSeries in
/-- The coefficients of `(1 - t)ᵐ`: `(-1)ʲ * C(m, j)`. -/
theorem PowerSeries.coeff_one_sub_X_pow {R : Type*} [CommRing R] (m j : ℕ) :
    coeff j ((1 - X : R⟦X⟧) ^ m) = (-1) ^ j * m.choose j := by
  induction m generalizing j with
  | zero => cases j <;> simp [coeff_one]
  | succ m ih =>
    rw [pow_succ, mul_sub, mul_one, map_sub]
    cases j with
    | zero => simp [ih]
    | succ j =>
      rw [coeff_succ_mul_X, ih, ih, Nat.choose_succ_succ']
      push_cast
      ring

open PowerSeries in
/-- **The explicit formula**: `A(n, k) = ∑_{j ≤ k} (-1)ʲ * C(n + 1, j) * (k + 1 - j)ⁿ` in `ℤ`. -/
theorem eulerian_eq_sum (n k : ℕ) :
    (eulerian n k : ℤ) =
      ∑ j ∈ range (k + 1),
        (-1) ^ j * ((n + 1).choose j : ℤ) * ((k - j + 1 : ℕ) : ℤ) ^ n := by
  have h := congrArg (coeff k) (mk_pow_mul_one_sub_pow (R := ℤ) n)
  rw [Polynomial.coeff_coe, coeff_eulerianPoly, coeff_mul,
    Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦
      coeff i (mk fun m : ℕ ↦ (m + 1 : ℤ) ^ n) * coeff j ((1 - X : ℤ⟦X⟧) ^ (n + 1)))] at h
  rw [← h, ← sum_range_reflect]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [mem_range] at hj
  rw [coeff_mk, PowerSeries.coeff_one_sub_X_pow, show k + 1 - 1 - j = k - j by omega,
    show k - (k - j) = j by omega]
  push_cast
  ring

/-! ### Descents -/

/-- The number of descents of a list `l`: the positions `i` with `l[i + 1] < l[i]`. For a
permutation `σ` of `0, …, n - 1` written as the list `σ(0), …, σ(n - 1)`, these are the descents
of `σ`. -/
def numDescents : List ℕ → ℕ
  | a :: b :: l => (if b < a then 1 else 0) + numDescents (b :: l)
  | _ => 0

@[simp] theorem numDescents_nil : numDescents [] = 0 := rfl

@[simp] theorem numDescents_singleton (a : ℕ) : numDescents [a] = 0 := rfl

theorem numDescents_cons_cons (a b : ℕ) (l : List ℕ) :
    numDescents (a :: b :: l) = (if b < a then 1 else 0) + numDescents (b :: l) := rfl

/-- Putting a larger number in front of a nonempty list adds a descent. -/
theorem numDescents_cons_of_lt {m : ℕ} {l : List ℕ} (hl : ∀ x ∈ l, x < m) (h : l ≠ []) :
    numDescents (m :: l) = numDescents l + 1 := by
  obtain ⟨b, t, rfl⟩ := List.exists_cons_of_ne_nil h
  rw [numDescents_cons_cons, ite_eq_left (hl b (by simp)), add_comm]

/-- Inserting a number `m` larger than every entry of `l` keeps the number of descents or raises
it by one, and keeps it for exactly `numDescents l + 1` of the `l.length + 1` positions. -/
theorem numDescents_permutations'Aux {m : ℕ} {l : List ℕ} (hl : ∀ x ∈ l, x < m) :
    (∀ x ∈ l.permutations'Aux m, numDescents x = numDescents l ∨
      numDescents x = numDescents l + 1) ∧
    (l.permutations'Aux m).countP (fun x ↦ numDescents x = numDescents l) =
      numDescents l + 1 := by
  induction l with
  | nil => simp [List.permutations'Aux]
  | cons y t ih =>
    cases t with
    | nil =>
      have hy : y < m := hl y (by simp)
      simp [List.permutations'Aux, numDescents_cons_cons, hy, Nat.not_lt.mpr hy.le]
    | cons z zs =>
      have hm : ∀ x ∈ z :: zs, x < m := fun x hx ↦ hl x (by simp [hx])
      obtain ⟨ih1, ih2⟩ := ih hm
      have hy : y < m := hl y (by simp)
      have hmz : numDescents (m :: z :: zs) = numDescents (z :: zs) + 1 :=
        numDescents_cons_of_lt hm (by simp)
      have hsz : (z :: zs).permutations'Aux m =
          (m :: z :: zs) :: (zs.permutations'Aux m).map (z :: ·) := rfl
      have hsy : (y :: z :: zs).permutations'Aux m =
          (m :: y :: z :: zs) :: (y :: m :: z :: zs) ::
            (zs.permutations'Aux m).map (fun x ↦ y :: z :: x) := by
        simp [List.permutations'Aux, List.map_map, Function.comp_def]
      rw [hsz] at ih1 ih2
      have h1 (x : List ℕ) (hx : x ∈ zs.permutations'Aux m) :
          numDescents (z :: x) = numDescents (z :: zs) ∨
            numDescents (z :: x) = numDescents (z :: zs) + 1 :=
        ih1 _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hx))
      have h2 : (zs.permutations'Aux m).countP
          (fun x ↦ numDescents (z :: x) = numDescents (z :: zs)) = numDescents (z :: zs) + 1 := by
        rw [List.countP_cons, hmz, List.countP_map] at ih2
        simpa [Function.comp_def] using ih2
      have hyz (x : List ℕ) : numDescents (y :: z :: x) =
          (if z < y then 1 else 0) + numDescents (z :: x) := rfl
      have hfirst : numDescents (m :: y :: z :: zs) = numDescents (y :: z :: zs) + 1 :=
        numDescents_cons_of_lt hl (by simp)
      have hsecond : numDescents (y :: m :: z :: zs) = numDescents (z :: zs) + 1 := by
        rw [numDescents_cons_cons, ite_eq_right (Nat.not_lt.mpr hy.le), zero_add, hmz]
      rw [hsy]
      refine ⟨?_, ?_⟩
      · simp only [List.forall_mem_cons, List.forall_mem_map]
        refine ⟨Or.inr hfirst, ?_, fun x hx ↦ ?_⟩
        · rw [hsecond, hyz]
          split_ifs <;> omega
        · rw [hyz, hyz]
          rcases h1 x hx with h | h <;> split_ifs <;> omega
      · have h3 : (zs.permutations'Aux m).countP
            (fun x ↦ numDescents (y :: z :: x) = numDescents (y :: z :: zs)) =
              numDescents (z :: zs) + 1 := by
          rw [← h2]
          congr 1
          funext x
          simp [hyz]
        rw [List.countP_cons, List.countP_cons, List.countP_map, hfirst, hsecond]
        simp only [Function.comp_def, h3, Nat.succ_ne_self, decide_false, Bool.false_eq_true,
          ite_false, add_zero]
        rw [hyz]
        simp only [decide_eq_true_eq]
        split_ifs <;> omega

/-- For `m` larger than every entry of `l`, how many of the insertions of `m` into `l` have `k`
descents: `numDescents l + 1` of them if `k = numDescents l`, the other
`l.length - numDescents l` if `k = numDescents l + 1`, and none otherwise. -/
theorem countP_permutations'Aux {m : ℕ} {l : List ℕ} (hl : ∀ x ∈ l, x < m) (k : ℕ) :
    (l.permutations'Aux m).countP (fun x ↦ numDescents x = k) =
      (if numDescents l = k then k + 1 else 0) +
        (if numDescents l + 1 = k then l.length + 1 - k else 0) := by
  obtain ⟨h1, h2⟩ := numDescents_permutations'Aux hl
  have hc := List.length_eq_countP_add_countP (fun x ↦ decide (numDescents x = numDescents l))
    (l := l.permutations'Aux m)
  rw [List.length_permutations'Aux, h2] at hc
  have hnot : (l.permutations'Aux m).countP (fun x ↦ ¬decide (numDescents x = numDescents l)) =
      (l.permutations'Aux m).countP (fun x ↦ numDescents x = numDescents l + 1) := by
    refine List.countP_congr fun x hx ↦ ?_
    rcases h1 x hx with h | h <;> simp [h]
  rw [hnot] at hc
  by_cases hk : numDescents l = k
  · subst hk
    simp [h2]
  by_cases hk' : numDescents l + 1 = k
  · subst hk'
    simp only [hk, ite_false, zero_add, ite_true]
    omega
  simp only [hk, hk', ite_false, add_zero]
  refine List.countP_eq_zero.mpr fun x hx ↦ ?_
  rcases h1 x hx with h | h <;> simp [h] <;> omega

private theorem sum_map_ite_const {α : Type*} (l : List α) (p : α → Prop) [DecidablePred p]
    (c : ℕ) : (l.map fun x ↦ if p x then c else 0).sum = c * l.countP (fun x ↦ p x) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
    by_cases h : p a <;> simp [h, mul_add, add_comm]

/-- `A(n, k)` is the number of lists with `k` descents in `List.permutations'` of
`n - 1, …, 1, 0` (which inserts `n - 1` last). -/
theorem countP_permutations'_reverse_range (n k : ℕ) :
    (List.range n).reverse.permutations'.countP (fun l ↦ numDescents l = k) = eulerian n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [List.permutations']
  | succ n ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.permutations', List.countP_flatMap]
    have hf : ∀ L ∈ (List.range n).reverse.permutations',
        (L.permutations'Aux n).countP (fun l ↦ numDescents l = k) =
          (if numDescents L = k then k + 1 else 0) +
            (if numDescents L + 1 = k then n + 1 - k else 0) := by
      intro L hL
      have hp := List.mem_permutations'.mp hL
      rw [countP_permutations'Aux (fun x hx ↦ by simpa using hp.mem_iff.mp hx), hp.length_eq,
        List.length_reverse, List.length_range]
    rw [Function.comp_def, List.map_congr_left (fun L hL ↦ hf L hL), List.sum_map_add,
      sum_map_ite_const, sum_map_ite_const, ih]
    cases k with
    | zero => simp
    | succ k =>
      have : (List.range n).reverse.permutations'.countP (fun x ↦ numDescents x + 1 = k + 1) =
          eulerian n k := by
        rw [← ih k]
        exact List.countP_congr fun x _ ↦ by simp
      rw [this, eulerian_succ_succ, show n + 1 - (k + 1) = n - k by omega]

/-- **The Eulerian number `A(n, k)` counts the permutations of `0, 1, …, n - 1` with exactly `k`
descents.** -/
theorem countP_permutations_range (n k : ℕ) :
    (List.range n).permutations.countP (fun l ↦ numDescents l = k) = eulerian n k := by
  rw [(List.permutations_perm_permutations' _).countP_eq,
    ← (List.perm_permutations'_iff.mpr (List.reverse_perm _)).countP_eq,
    countP_permutations'_reverse_range]

/-- The same count for the permutations `σ` of `Fin n`, read as the words
`σ(0), σ(1), …, σ(n - 1)`. -/
theorem card_perm_numDescents (n k : ℕ) :
    #{σ : Equiv.Perm (Fin n) | numDescents (List.ofFn fun i ↦ (σ i : ℕ)) = k} =
      eulerian n k := by
  classical
  set f : Equiv.Perm (Fin n) → List ℕ := fun σ ↦ List.ofFn fun i ↦ (σ i : ℕ)
  have hf : Function.Injective f := fun σ τ h ↦
    Equiv.ext fun i ↦ Fin.ext (congrFun (List.ofFn_injective h) i)
  have hrange : List.ofFn (fun i : Fin n ↦ (i : ℕ)) = List.range n :=
    List.ext_getElem (by simp) (by simp)
  have hnodup : (List.range n).permutations.Nodup := List.nodup_permutations _ List.nodup_range
  have himage : univ.image f = (List.range n).permutations.toFinset := by
    refine eq_of_subset_of_card_le (fun l hl ↦ ?_) ?_
    · obtain ⟨σ, -, rfl⟩ := mem_image.mp hl
      rw [List.mem_toFinset, List.mem_permutations, ← hrange]
      exact σ.ofFn_comp_perm (fun i : Fin n ↦ (i : ℕ))
    · rw [card_image_of_injective _ hf, card_univ, Fintype.card_perm, Fintype.card_fin,
        List.toFinset_card_of_nodup hnodup, List.length_permutations, List.length_range]
  rw [← countP_permutations_range, ← card_image_of_injective _ hf,
    ← filter_image (f := f) (p := fun l ↦ numDescents l = k), himage,
    List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hnodup.filter _),
    List.toFinset_filter]
  simp only [decide_eq_true_eq]
