module

public import Mathlib

/-!
# q-analogues: q-numbers, q-factorials and Gaussian binomial coefficients

Mathlib lists "q-factorials, q-binomials, q-Pochhammer" as a TODO
(`Mathlib/RingTheory/Polynomial/Pochhammer.lean`). This file supplies the first layer.

Everything is defined for an arbitrary element `q` of a commutative semiring `R`, so the
same lemmas serve the polynomial case (`q = X` in `ℕ[X]` or `ℤ[X]`), the classical case
(`q = 1`), prime powers (`q = p ^ f` in `ℕ`, where classically `gaussBinom q n k` counts
subspaces over a finite field; that count is not proved here) and roots of unity (`q = ζ` in `ℂ`).

## Main definitions

* `qNat q n`       : the q-number `[n]_q = 1 + q + ⋯ + q ^ (n - 1)`.
* `qFactorial q n` : the q-factorial `[n]_q ! = [1]_q * [2]_q * ⋯ * [n]_q`.
* `gaussBinom q n k` : the Gaussian binomial coefficient, defined by the q-Pascal rule
  `gaussBinom q (n + 1) (k + 1) = gaussBinom q n k + q ^ (k + 1) * gaussBinom q n (k + 1)`.

## Main results

* `qNat_add`, `qNat_mul`            : `[m + n] = [m] + q ^ m * [n]` and
  `[m * n]_q = [m]_q * [n]_{q ^ m}`.
* `gaussBinom_succ_succ'`           : the second q-Pascal rule.
* `gaussBinom_symm`                 : `gaussBinom q n (n - k) = gaussBinom q n k` for `k ≤ n`.
* `qNat_succ_mul_gaussBinom_succ`   : absorption, `[k + 1] * G (n + 1) (k + 1) = [n + 1] * G n k`.
* `add_gaussBinom_mul_qFactorial_mul_qFactorial`, `gaussBinom_mul_qFactorial_mul_qFactorial` :
  `G (a + b) a * [a]! * [b]! = [a + b]!` and, for `k ≤ n`, `G n k * [k]! * [n - k]! = [n]!`.
* `gaussBinom_eq_div`               : the quotient formula in a semifield, for `k ≤ n` and a
  nonzero denominator.
* `gaussBinom_one_left`             : at `q = 1` it is `Nat.choose`.
* `map_gaussBinom`, `Nat.cast_gaussBinom` : compatibility with ring homomorphisms and casts.
* `prod_one_add_pow_mul`            : the q-binomial theorem (Gauss, Rothe),
  `∏ i < n, (1 + q ^ i * x) = ∑ k ≤ n, q ^ (k choose 2) * gaussBinom q n k * x ^ k`.
* `one_add_pow_eq_sum_choose`       : at `q = 1` the q-binomial theorem is the binomial theorem.
* `gaussBinom_X_monic`, `gaussBinom_X_natDegree` : for `k ≤ n`, as a polynomial in `q` it is
  monic, and of degree `k * (n - k)` when `R` is nontrivial.
* `aeval_gaussBinom_X`              : universality, `gaussBinom q n k` is the value at `q` of
  one polynomial in `ℕ[X]`, the tool for transferring identities proved there to every `R`.
-/

@[expose] public section

open Finset

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (q : R)

/-! ### q-numbers -/

/-- The q-analogue `[n]_q = 1 + q + ⋯ + q ^ (n - 1)` of the natural number `n`. This is the
geometric sum `∑ i ∈ range n, q ^ i`, so Mathlib's `geom_sum` lemmas (`mul_geom_sum`,
`geom_sum_eq`, …) apply after `rw [qNat]`. -/
def qNat (n : ℕ) : R := ∑ i ∈ range n, q ^ i

@[simp] theorem qNat_zero : qNat q 0 = 0 := by simp [qNat]

@[simp] theorem qNat_one : qNat q 1 = 1 := by simp [qNat]

theorem qNat_succ (n : ℕ) : qNat q (n + 1) = qNat q n + q ^ n := sum_range_succ _ _

theorem qNat_succ' (n : ℕ) : qNat q (n + 1) = 1 + q * qNat q n := by
  rw [qNat, sum_range_succ', qNat, mul_sum, add_comm]
  simp [pow_succ']

theorem qNat_add (m n : ℕ) : qNat q (m + n) = qNat q m + q ^ m * qNat q n := by
  induction n with
  | zero => simp
  | succ n ih => rw [← add_assoc, qNat_succ, ih, qNat_succ, pow_add]; ring

theorem qNat_mul (m n : ℕ) : qNat q (m * n) = qNat q m * qNat (q ^ m) n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, qNat_add, ih, qNat_succ, ← pow_mul]; ring

/-- At `q = 1` the q-number `[n]_q` is `n`. -/
@[simp] theorem qNat_one_left (n : ℕ) : qNat (1 : R) n = n := by simp [qNat]

@[simp] theorem qNat_zero_left (n : ℕ) : qNat (0 : R) (n + 1) = 1 := by simp [qNat_succ']

theorem map_qNat {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F) (n : ℕ) :
    f (qNat q n) = qNat (f q) n := by
  simp [qNat]

@[simp, norm_cast] theorem Nat.cast_qNat (q n : ℕ) :
    ((qNat q n : ℕ) : R) = qNat (q : R) n :=
  map_qNat q (Nat.castRingHom R) n

@[simp, norm_cast] theorem Int.cast_qNat {R : Type*} [CommRing R] (q : ℤ) (n : ℕ) :
    ((qNat q n : ℤ) : R) = qNat (q : R) n :=
  map_qNat q (Int.castRingHom R) n

/-- The closed form `(q - 1) * [n]_q = q ^ n - 1`, in a ring. -/
theorem sub_one_mul_qNat {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    (q - 1) * qNat q n = q ^ n - 1 := by
  rw [qNat, mul_geom_sum]

/-! ### q-factorials -/

/-- The q-factorial `[n]_q ! = [1]_q * [2]_q * ⋯ * [n]_q`. -/
def qFactorial (n : ℕ) : R := ∏ i ∈ range n, qNat q (i + 1)

@[simp] theorem qFactorial_zero : qFactorial q 0 = 1 := by simp [qFactorial]

theorem qFactorial_succ (n : ℕ) : qFactorial q (n + 1) = qFactorial q n * qNat q (n + 1) :=
  prod_range_succ _ _

@[simp] theorem qFactorial_one : qFactorial q 1 = 1 := by simp [qFactorial_succ]

/-- At `q = 1` the q-factorial is the factorial. -/
@[simp] theorem qFactorial_one_left (n : ℕ) : qFactorial (1 : R) n = n.factorial := by
  simp [qFactorial, ← prod_range_add_one_eq_factorial]

/-- At `q = 0` the q-factorial is `1`. -/
@[simp] theorem qFactorial_zero_left (n : ℕ) : qFactorial (0 : R) n = 1 := by
  simp [qFactorial]

theorem map_qFactorial {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F) (n : ℕ) :
    f (qFactorial q n) = qFactorial (f q) n := by
  simp [qFactorial, map_qNat]

@[simp, norm_cast] theorem Nat.cast_qFactorial (q n : ℕ) :
    ((qFactorial q n : ℕ) : R) = qFactorial (q : R) n :=
  map_qFactorial q (Nat.castRingHom R) n

@[simp, norm_cast] theorem Int.cast_qFactorial {R : Type*} [CommRing R] (q : ℤ) (n : ℕ) :
    ((qFactorial q n : ℤ) : R) = qFactorial (q : R) n :=
  map_qFactorial q (Int.castRingHom R) n

/-! ### Gaussian binomial coefficients -/

/-- The Gaussian binomial coefficient (q-binomial coefficient) `n` choose `k` at `q`,
defined by the q-Pascal recursion. (Classically, for `q` a prime power it counts the
`k`-dimensional subspaces of an `n`-dimensional space over the field with `q` elements; that
is not proved in this file.) -/
def gaussBinom : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => gaussBinom n k + q ^ (k + 1) * gaussBinom n (k + 1)

@[simp] theorem gaussBinom_zero_right (n : ℕ) : gaussBinom q n 0 = 1 := by
  cases n <;> rfl

@[simp] theorem gaussBinom_zero_succ (k : ℕ) : gaussBinom q 0 (k + 1) = 0 := rfl

/-- The first q-Pascal rule (this is the defining recursion). -/
theorem gaussBinom_succ_succ (n k : ℕ) :
    gaussBinom q (n + 1) (k + 1) = gaussBinom q n k + q ^ (k + 1) * gaussBinom q n (k + 1) :=
  rfl

theorem gaussBinom_eq_zero_of_lt {n k : ℕ} (h : n < k) : gaussBinom q n k = 0 := by
  induction n generalizing k with
  | zero => obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'; rfl
  | succ n ih =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt h)
    rw [gaussBinom_succ_succ, ih (by omega), ih (by omega)]; simp

@[simp] theorem gaussBinom_succ_self (n : ℕ) : gaussBinom q n (n + 1) = 0 :=
  gaussBinom_eq_zero_of_lt q n.lt_succ_self

@[simp] theorem gaussBinom_self (n : ℕ) : gaussBinom q n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [gaussBinom_succ_succ, ih]

@[simp] theorem gaussBinom_one_right (n : ℕ) : gaussBinom q n 1 = qNat q n := by
  induction n with
  | zero => simp
  | succ n ih => rw [gaussBinom_succ_succ, ih, qNat_succ']; simp

/-- At `q = 1` the Gaussian binomial coefficient is the binomial coefficient. -/
@[simp] theorem gaussBinom_one_left (n k : ℕ) : gaussBinom (1 : R) n k = n.choose k := by
  induction n generalizing k with
  | zero => cases k <;> simp
  | succ n ih => cases k <;> simp [gaussBinom_succ_succ, ih, Nat.choose_succ_succ]

/-- At `q = 0` every Gaussian binomial coefficient with `k ≤ n` is `1`. -/
theorem gaussBinom_zero_left {n k : ℕ} (h : k ≤ n) : gaussBinom (0 : R) n k = 1 := by
  induction n generalizing k with
  | zero =>
    obtain rfl : k = 0 := by omega
    simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k => simp [gaussBinom_succ_succ, ih (Nat.le_of_succ_le_succ h)]

theorem map_gaussBinom {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F) (n k : ℕ) :
    f (gaussBinom q n k) = gaussBinom (f q) n k := by
  induction n generalizing k with
  | zero => cases k <;> simp
  | succ n ih => cases k <;> simp [gaussBinom_succ_succ, ih]

@[simp, norm_cast] theorem Nat.cast_gaussBinom (q n k : ℕ) :
    ((gaussBinom q n k : ℕ) : R) = gaussBinom (q : R) n k :=
  map_gaussBinom q (Nat.castRingHom R) n k

@[simp, norm_cast] theorem Int.cast_gaussBinom {R : Type*} [CommRing R] (q : ℤ) (n k : ℕ) :
    ((gaussBinom q n k : ℤ) : R) = gaussBinom (q : R) n k :=
  map_gaussBinom q (Int.castRingHom R) n k

/-! ### The second q-Pascal rule and symmetry -/

/-- The second q-Pascal rule. -/
theorem gaussBinom_succ_succ' (n k : ℕ) :
    gaussBinom q (n + 1) (k + 1) = q ^ (n - k) * gaussBinom q n k + gaussBinom q n (k + 1) := by
  induction n generalizing k with
  | zero => cases k <;> simp [gaussBinom_succ_succ]
  | succ n ih =>
    cases k with
    | zero => simpa [add_comm (q ^ (n + 1))] using qNat_succ q (n + 1)
    | succ k =>
      rw [gaussBinom_succ_succ]
      conv_lhs => rw [ih k, ih (k + 1)]
      conv_rhs => rw [gaussBinom_succ_succ q n k, gaussBinom_succ_succ q n (k + 1)]
      have e1 : n + 1 - (k + 1) = n - k := by omega
      rw [e1]
      rcases Nat.lt_or_ge n (k + 1) with h | h
      · rw [gaussBinom_eq_zero_of_lt q h]; simp
      · have e2 : q ^ (k + 1 + 1) * q ^ (n - (k + 1)) = q ^ (n - k) * q ^ (k + 1) := by
          rw [← pow_add, ← pow_add]; congr 1; omega
        rw [mul_add, ← mul_assoc, e2]; ring

/-- Symmetry of Gaussian binomial coefficients, in sum form. -/
theorem gaussBinom_symm_add (a b : ℕ) : gaussBinom q (a + b) a = gaussBinom q (a + b) b := by
  suffices H : ∀ n a b, a + b = n → gaussBinom q n a = gaussBinom q n b from H _ a b rfl
  intro n
  induction n with
  | zero =>
    intro a b h
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    rfl
  | succ n ih =>
    intro a b h
    cases a with
    | zero =>
      obtain rfl : b = n + 1 := by omega
      simp
    | succ a =>
      cases b with
      | zero =>
        obtain rfl : a = n := by omega
        simp
      | succ b =>
        have e : n - b = a + 1 := by omega
        rw [gaussBinom_succ_succ q n a, gaussBinom_succ_succ' q n b, ih a (b + 1) (by omega),
          ih (a + 1) b (by omega), e, add_comm]

/-- Symmetry of Gaussian binomial coefficients. -/
theorem gaussBinom_symm {n k : ℕ} (h : k ≤ n) : gaussBinom q n (n - k) = gaussBinom q n k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, gaussBinom_symm_add]

@[simp] theorem gaussBinom_succ_self_right (n : ℕ) :
    gaussBinom q (n + 1) n = qNat q (n + 1) :=
  (gaussBinom_symm_add q n 1).trans (gaussBinom_one_right q _)

/-! ### Absorption identities -/

private theorem qNat_succ_split {n k : ℕ} (h : k ≤ n) :
    qNat q (n + 1) = qNat q (k + 1) + q ^ (k + 1) * qNat q (n - k) := by
  rw [← qNat_add]; congr 1; omega

private theorem absorb_aux (n : ℕ)
    (hB : ∀ k, qNat q (k + 1) * gaussBinom q n (k + 1) = qNat q (n - k) * gaussBinom q n k)
    (k : ℕ) :
    qNat q (k + 1) * gaussBinom q (n + 1) (k + 1) = qNat q (n + 1) * gaussBinom q n k := by
  rcases Nat.lt_or_ge n k with h | h
  · rw [gaussBinom_eq_zero_of_lt q (Nat.succ_lt_succ h), gaussBinom_eq_zero_of_lt q h]; simp
  · rw [gaussBinom_succ_succ, mul_add, mul_left_comm, hB, qNat_succ_split q h]; ring

/-- `[k + 1] * G n (k + 1) = [n - k] * G n k`. -/
theorem qNat_succ_mul_gaussBinom (n k : ℕ) :
    qNat q (k + 1) * gaussBinom q n (k + 1) = qNat q (n - k) * gaussBinom q n k := by
  induction n generalizing k with
  | zero => cases k <;> simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      have e1 : n + 1 - (k + 1) = n - k := by omega
      rw [absorb_aux q n ih (k + 1), e1]
      rcases Nat.lt_or_ge n (k + 1) with h | h
      · rw [gaussBinom_eq_zero_of_lt q h, show n - k = 0 by omega]; simp
      · rw [gaussBinom_succ_succ q n k, mul_add, mul_left_comm (qNat q (n - k)), ← ih k,
          qNat_succ_split q (Nat.le_of_succ_le h)]
        ring

/-- Absorption: `[k + 1] * G (n + 1) (k + 1) = [n + 1] * G n k`. -/
theorem qNat_succ_mul_gaussBinom_succ (n k : ℕ) :
    qNat q (k + 1) * gaussBinom q (n + 1) (k + 1) = qNat q (n + 1) * gaussBinom q n k :=
  absorb_aux q n (qNat_succ_mul_gaussBinom q n) k

/-! ### The factorial formula -/

/-- The q-factorial formula `G (a + b) a * [a]! * [b]! = [a + b]!`, stated without division
so that it holds in every commutative semiring. -/
theorem add_gaussBinom_mul_qFactorial_mul_qFactorial (a b : ℕ) :
    gaussBinom q (a + b) a * qFactorial q a * qFactorial q b = qFactorial q (a + b) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.add_right_comm, qFactorial_succ q a, qFactorial_succ q (a + b), ← ih]
    calc _ = qNat q (a + 1) * gaussBinom q (a + b + 1) (a + 1)
              * (qFactorial q a * qFactorial q b) := by ring
      _ = _ := by rw [qNat_succ_mul_gaussBinom_succ]; ring

/-- The q-factorial formula `G n k * [k]! * [n - k]! = [n]!` for `k ≤ n`. -/
theorem gaussBinom_mul_qFactorial_mul_qFactorial {n k : ℕ} (h : k ≤ n) :
    gaussBinom q n k * qFactorial q k * qFactorial q (n - k) = qFactorial q n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, add_gaussBinom_mul_qFactorial_mul_qFactorial]

/-- The quotient formula `G n k = [n]! / ([k]! * [n - k]!)` in a semifield, valid for
`k ≤ n` whenever the denominator is nonzero. (It can vanish even in a field: `q = 1` in
positive characteristic, or `q ≠ 1` a root of unity.) -/
theorem gaussBinom_eq_div {K : Type*} [Semifield K] (q : K) {n k : ℕ} (h : k ≤ n)
    (h0 : qFactorial q k * qFactorial q (n - k) ≠ 0) :
    gaussBinom q n k = qFactorial q n / (qFactorial q k * qFactorial q (n - k)) := by
  rw [eq_div_iff h0, ← mul_assoc, gaussBinom_mul_qFactorial_mul_qFactorial q h]

/-! ### The q-binomial theorem -/

/-- The **q-binomial theorem** (Gauss, Rothe):
`∏ i < n, (1 + q ^ i * x) = ∑ k ≤ n, q ^ (k choose 2) * G n k * x ^ k`. -/
theorem prod_one_add_pow_mul (x : R) (n : ℕ) :
    ∏ i ∈ range n, (1 + q ^ i * x)
      = ∑ k ∈ range (n + 1), q ^ k.choose 2 * gaussBinom q n k * x ^ k := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hc (k : ℕ) : (k + 1).choose 2 = k.choose 2 + k := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
    -- the sum at `q * x`, with its `k = 0` term split off and a vanishing top term added
    have hA : ∑ k ∈ range (n + 1), q ^ k.choose 2 * gaussBinom q n k * (q * x) ^ k
        = ∑ k ∈ range (n + 1),
            q ^ (k + 1).choose 2 * gaussBinom q n (k + 1) * (q * x) ^ (k + 1) + 1 := by
      have h := sum_range_succ (fun k => q ^ k.choose 2 * gaussBinom q n k * (q * x) ^ k) (n + 1)
      rw [sum_range_succ'] at h
      simpa using h.symm
    have hx (i : ℕ) : 1 + q ^ (i + 1) * x = 1 + q ^ i * (q * x) := by ring
    rw [prod_range_succ', sum_range_succ']
    simp only [hx, ih (q * x), pow_zero, one_mul, Nat.choose_zero_succ, gaussBinom_zero_right,
      mul_one]
    rw [mul_add, mul_one, sum_mul]
    nth_rewrite 1 [hA]
    rw [add_right_comm, ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    rw [gaussBinom_succ_succ, hc, pow_add]
    ring

/-- At `q = 1` the q-binomial theorem is the binomial theorem. Mathlib already has this as a
case of `add_pow`; it is recorded here as a consistency check on `prod_one_add_pow_mul`. -/
theorem one_add_pow_eq_sum_choose (x : R) (n : ℕ) :
    (1 + x) ^ n = ∑ k ∈ range (n + 1), (n.choose k : R) * x ^ k := by
  simpa using prod_one_add_pow_mul (1 : R) x n

/-! ### The Gaussian binomial coefficient as a polynomial in `q` -/

section Polynomial

open Polynomial

variable (R) in
/-- For `k ≤ n` and `R` nontrivial, the Gaussian binomial coefficient, as a polynomial in
`q`, is monic of degree `k * (n - k)`. -/
theorem gaussBinom_X_monic_and_natDegree [Nontrivial R] (n k : ℕ) (h : k ≤ n) :
    (gaussBinom (X : R[X]) n k).Monic ∧ (gaussBinom (X : R[X]) n k).natDegree = k * (n - k) := by
  induction n generalizing k with
  | zero =>
    obtain rfl : k = 0 := by omega
    simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      rcases Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ h) with rfl | hk
      · simp
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
        obtain ⟨hm1, hd1⟩ := ih k (by omega)
        obtain ⟨hm2, hd2⟩ := ih (k + 1) (by omega)
        have hmon : (X ^ (k + 1) * gaussBinom (X : R[X]) (k + 1 + m) (k + 1)).Monic :=
          (monic_X_pow _).mul hm2
        have hdeg : (X ^ (k + 1) * gaussBinom (X : R[X]) (k + 1 + m) (k + 1)).natDegree
            = (k + 1) * (m + 1) := by
          rw [(monic_X_pow _).natDegree_mul hm2, natDegree_X_pow, hd2, Nat.add_sub_cancel_left]
          ring
        have hlt : (gaussBinom (X : R[X]) (k + 1 + m) k).degree
            < (X ^ (k + 1) * gaussBinom (X : R[X]) (k + 1 + m) (k + 1)).degree := by
          apply degree_lt_degree
          rw [hd1, hdeg, show k + 1 + m - k = m + 1 by omega]
          nlinarith
        rw [gaussBinom_succ_succ]
        refine ⟨hmon.add_of_right hlt, ?_⟩
        rw [natDegree_add_eq_right_of_degree_lt hlt, hdeg,
          show k + 1 + m + 1 - (k + 1) = m + 1 by omega]

/-- For `k ≤ n` the Gaussian binomial coefficient is a monic polynomial in `q` (over any `R`;
over the trivial ring this says nothing). -/
theorem gaussBinom_X_monic {n k : ℕ} (h : k ≤ n) : (gaussBinom (X : R[X]) n k).Monic := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Subsingleton.elim _ _
  · exact (gaussBinom_X_monic_and_natDegree R n k h).1

/-- For `k ≤ n` and `R` nontrivial, the Gaussian binomial coefficient has degree
`k * (n - k)` as a polynomial in `q`. -/
theorem gaussBinom_X_natDegree [Nontrivial R] {n k : ℕ} (h : k ≤ n) :
    (gaussBinom (X : R[X]) n k).natDegree = k * (n - k) :=
  (gaussBinom_X_monic_and_natDegree R n k h).2

/-- **Universality.** For any commutative base semiring `A` over which `R` is an algebra,
the Gaussian binomial coefficient at `q : R` is the value at `q` of the universal polynomial
`gaussBinom X n k : A[X]`.

With `A = ℕ` this applies to every commutative semiring `R`, and with `A = ℤ` to every
commutative ring. This is the tool for transferring identities (the transfer itself is a
recipe, not a theorem here): apply `aeval q` to an identity in the one variable `X` proved
in `ℕ[X]` (or in `ℤ[X]`, where subtraction and cancellation are available) and simplify
with this lemma, `aeval_qNat_X` and `aeval_qFactorial_X`. -/
@[simp] theorem aeval_gaussBinom_X {A : Type*} [CommSemiring A] [Algebra A R] (n k : ℕ) :
    aeval q (gaussBinom (X : A[X]) n k) = gaussBinom q n k := by
  rw [map_gaussBinom, aeval_X]

@[simp] theorem aeval_qNat_X {A : Type*} [CommSemiring A] [Algebra A R] (n : ℕ) :
    aeval q (qNat (X : A[X]) n) = qNat q n := by
  rw [map_qNat, aeval_X]

@[simp] theorem aeval_qFactorial_X {A : Type*} [CommSemiring A] [Algebra A R] (n : ℕ) :
    aeval q (qFactorial (X : A[X]) n) = qFactorial q n := by
  rw [map_qFactorial, aeval_X]

/-- The case `A = R` of `aeval_gaussBinom_X`. -/
@[simp] theorem eval_gaussBinom_X (n k : ℕ) :
    (gaussBinom (X : R[X]) n k).eval q = gaussBinom q n k :=
  aeval_gaussBinom_X (A := R) q n k

@[simp] theorem eval_qNat_X (n : ℕ) : (qNat (X : R[X]) n).eval q = qNat q n :=
  aeval_qNat_X (A := R) q n

@[simp] theorem eval_qFactorial_X (n : ℕ) :
    (qFactorial (X : R[X]) n).eval q = qFactorial q n :=
  aeval_qFactorial_X (A := R) q n

end Polynomial
