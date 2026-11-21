module

public import Mathlib

/-!
# Ramanujan sums

For `q : ℕ` and `n : ℤ` the Ramanujan sum is

`c_q(n) = ∑_{d ∣ q, d ∣ n} μ(q / d) * d`.

In any integral domain with a primitive `q`-th root of unity `ζ`, and for `n ≥ 0`, it is the
sum of the `n`-th powers of the primitive `q`-th roots of unity,
`c_q(n) = ∑_{k < q, gcd(k, q) = 1} ζ ^ (k * n)`. So `c_q(1) = μ(q)` is the sum of the primitive
roots themselves and `c_q(0) = φ(q)` counts them.

Ramanujan sums are the basic exponential sums of elementary number theory: they appear in
Ramanujan expansions of arithmetic functions, in the singular series of the circle method, and
as the degenerate case of Kloosterman and Gauss sums. Mathlib has the Möbius function and
primitive roots of unity but not these sums.

## Main definitions

* `ramanujanSum q n` : the Ramanujan sum `c_q(n)`, an integer.

## Main results

* `sum_ramanujanSum`         : `∑_{d ∣ q} c_d(n) = q` if `q ∣ n`, and `0` otherwise.
* `eq_ramanujanSum_of_sum_eq` : for `q > 0`, this property determines `c_q(n)`.
* `ramanujanSum_zero_right`, `ramanujanSum_one_right`, `ramanujanSum_of_isCoprime` :
  `c_q(0) = φ(q)`, and `c_q(n) = μ(q)` when `q` and `n` are coprime.
* `ramanujanSum_congr`, `ramanujanSum_neg` : `c_q(n)` depends on `n` only modulo `q` and up to
  sign.
* `ramanujanSum_mul`         : `c_{q r}(n) = c_q(n) * c_r(n)` for coprime `q`, `r`.
* `ramanujanSum_prime_pow_succ`, `ramanujanSum_prime` : the values at prime powers.
* `ramanujanSum_mul_totient`, `ramanujanSum_eq_moebius_mul_totient_div` : **Hölder's
  formula**, `c_q(n) * φ(q / g) = μ(q / g) * φ(q)` with `g = gcd(q, n)`.
* `IsPrimitiveRoot.sum_nthRootsFinset_pow` : the `n`-th powers of the `d`-th roots of unity
  sum to `d` if `d ∣ n` and to `0` otherwise.
* `IsPrimitiveRoot.sum_primitiveRoots_pow`, `IsPrimitiveRoot.sum_pow_coprime` : `c_q(n)` as
  a sum of roots of unity, in any integral domain.
* `ramanujanSum_eq_sum_exp`  : `c_q(n) = ∑_{k < q, gcd(k, q) = 1} exp(2πikn/q)` in `ℂ`.
-/

@[expose] public section

open Finset ArithmeticFunction Polynomial
open scoped ArithmeticFunction.Moebius Nat

/-- The Ramanujan sum `c_q(n) = ∑_{d ∣ q, d ∣ n} μ(q / d) * d`. -/
def ramanujanSum (q : ℕ) (n : ℤ) : ℤ :=
  ∑ d ∈ q.divisors with ((d : ℕ) : ℤ) ∣ n, μ (q / d) * d

variable (q : ℕ) (n : ℤ)

@[simp] theorem ramanujanSum_zero_left : ramanujanSum 0 n = 0 := by simp [ramanujanSum]

@[simp] theorem ramanujanSum_one_left : ramanujanSum 1 n = 1 := by
  simp [ramanujanSum, filter_singleton]

/-- `c_q(n)` only depends on `n` modulo `q`. -/
theorem ramanujanSum_congr {m : ℤ} (h : n ≡ m [ZMOD q]) :
    ramanujanSum q n = ramanujanSum q m := by
  unfold ramanujanSum
  rw [filter_congr fun d hd => (h.of_dvd (Int.natCast_dvd_natCast.mpr
    (Nat.dvd_of_mem_divisors hd))).dvd_iff]

@[simp] theorem ramanujanSum_neg : ramanujanSum q (-n) = ramanujanSum q n := by
  simp [ramanujanSum]

/-! ### Möbius inversion -/

/-- `c_q(n)` is the Möbius transform of `d ↦ d` if `d ∣ n`, `d ↦ 0` otherwise. -/
theorem ramanujanSum_eq_sum_divisorsAntidiagonal :
    ramanujanSum q n =
      ∑ x ∈ q.divisorsAntidiagonal, μ x.1 * if (x.2 : ℤ) ∣ n then (x.2 : ℤ) else 0 := by
  rw [Nat.sum_divisorsAntidiagonal' (fun a b => μ a * if (b : ℤ) ∣ n then (b : ℤ) else 0),
    ramanujanSum, sum_filter]
  refine sum_congr rfl fun d _ => ?_
  split_ifs <;> simp

/-- `∑_{d ∣ q} c_d(n)` is `q` if `q ∣ n` and `0` otherwise. -/
theorem sum_ramanujanSum :
    ∑ d ∈ q.divisors, ramanujanSum d n = if (q : ℤ) ∣ n then (q : ℤ) else 0 := by
  rcases q.eq_zero_or_pos with rfl | hq
  · simp
  refine (sum_eq_iff_sum_mul_moebius_eq (f := fun d => ramanujanSum d n)
    (g := fun d => if (d : ℤ) ∣ n then (d : ℤ) else 0)).mpr (fun d _ => ?_) q hq
  simp [ramanujanSum_eq_sum_divisorsAntidiagonal]

/-- Uniqueness: a function whose divisor sums are those of `sum_ramanujanSum`, for the divisors
of `q`, takes the value `c_q(n)` at `q`. -/
theorem eq_ramanujanSum_of_sum_eq {R : Type*} [Ring R] {f : ℕ → R} {q : ℕ} (hq : 0 < q)
    (hf : ∀ d, d ∣ q → ∑ e ∈ d.divisors, f e = if (d : ℤ) ∣ n then (d : R) else 0) :
    f q = ramanujanSum q n := by
  have hs : ∀ a b, a ∣ b → b ∈ {d | d ∣ q} → a ∈ {d | d ∣ q} := fun _ _ h h' => h.trans h'
  have h1 := (sum_eq_iff_sum_mul_moebius_eq_on (f := f)
    (g := fun d => if (d : ℤ) ∣ n then (d : R) else 0) _ hs).mp
    (fun d _ hd => hf d hd) q hq dvd_rfl
  have h2 := (sum_eq_iff_sum_mul_moebius_eq_on (f := fun d => (ramanujanSum d n : R))
    (g := fun d => if (d : ℤ) ∣ n then (d : R) else 0) _ hs).mp
    (fun d _ _ => by rw [← Int.cast_sum, sum_ramanujanSum]; split_ifs <;> simp) q hq dvd_rfl
  rw [← h1, ← h2]

/-! ### Values -/

@[simp] theorem ramanujanSum_zero_right : ramanujanSum q 0 = φ q := by
  rcases q.eq_zero_or_pos with rfl | hq
  · simp
  exact (eq_ramanujanSum_of_sum_eq (f := fun d => (φ d : ℤ)) 0 hq fun d _ => by
    simp [← Nat.cast_sum, Nat.sum_totient]).symm

/-- `c_q(n) = μ(q)` when `q` and `n` are coprime. -/
theorem ramanujanSum_of_isCoprime (h : IsCoprime (q : ℤ) n) : ramanujanSum q n = μ q := by
  unfold ramanujanSum
  rw [sum_eq_single 1]
  · simp
  · intro d hd hd1
    simp only [mem_filter, Nat.mem_divisors] at hd
    have := h.isUnit_of_dvd' (Int.natCast_dvd_natCast.mpr hd.1.1) hd.2
    exact absurd (by simpa using Int.isUnit_iff_natAbs_eq.mp this) hd1
  · intro h1
    have : q = 0 := by simpa using h1
    simp [this]

@[simp] theorem ramanujanSum_one_right : ramanujanSum q 1 = μ q :=
  ramanujanSum_of_isCoprime q 1 isCoprime_one_right

/-- The values at prime powers:
`c_{p^(k+1)}(n) = p^(k+1) * [p^(k+1) ∣ n] - p^k * [p^k ∣ n]`. -/
theorem ramanujanSum_prime_pow_succ {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ramanujanSum (p ^ (k + 1)) n =
      (if (p : ℤ) ^ (k + 1) ∣ n then (p : ℤ) ^ (k + 1) else 0) -
        (if (p : ℤ) ^ k ∣ n then (p : ℤ) ^ k else 0) := by
  have h1 := sum_ramanujanSum (p ^ (k + 1)) n
  have h0 := sum_ramanujanSum (p ^ k) n
  rw [Nat.sum_divisors_prime_pow hp, sum_range_succ] at h1
  rw [Nat.sum_divisors_prime_pow hp] at h0
  push_cast at h0 h1
  linear_combination h1 - h0

theorem ramanujanSum_prime {p : ℕ} (hp : p.Prime) :
    ramanujanSum p n = if (p : ℤ) ∣ n then (p : ℤ) - 1 else -1 := by
  have := ramanujanSum_prime_pow_succ n hp 0
  simp only [zero_add, pow_one, pow_zero, one_dvd, ite_true] at this
  rw [this]
  split_ifs <;> ring

/-! ### Multiplicativity -/

/-- `d ↦ d` if `d ∣ n`, and `d ↦ 0` otherwise. -/
private def dvdId (n : ℤ) : ArithmeticFunction ℤ :=
  ⟨fun d => if (d : ℤ) ∣ n then (d : ℤ) else 0, by simp⟩

private theorem isMultiplicative_dvdId : (dvdId n).IsMultiplicative := by
  refine ⟨by simp [dvdId], fun {a b} hab => ?_⟩
  simp only [dvdId, coe_mk, Int.natCast_dvd]
  have : a * b ∣ n.natAbs ↔ a ∣ n.natAbs ∧ b ∣ n.natAbs :=
    ⟨fun h => ⟨(dvd_mul_right a b).trans h, (dvd_mul_left b a).trans h⟩,
      fun h => hab.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
  by_cases ha : a ∣ n.natAbs <;> by_cases hb : b ∣ n.natAbs <;> simp [ha, hb, this]

private theorem ramanujanSum_eq_apply : ramanujanSum q n = (μ * dvdId n) q := by
  rw [ramanujanSum_eq_sum_divisorsAntidiagonal, ArithmeticFunction.mul_apply]
  rfl

/-- `c_q(n)` is multiplicative in `q`. -/
theorem ramanujanSum_mul {q r : ℕ} (h : q.Coprime r) :
    ramanujanSum (q * r) n = ramanujanSum q n * ramanujanSum r n := by
  simp only [ramanujanSum_eq_apply]
  exact (isMultiplicative_moebius.mul (isMultiplicative_dvdId n)).map_mul_of_coprime h

/-! ### Hölder's formula -/

/-- `q ↦ f (q / gcd(q, N))` is multiplicative when `f` is. -/
private def compDivGcd (f : ArithmeticFunction ℤ) (N : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun q => f (q / q.gcd N), by simp⟩

private theorem isMultiplicative_compDivGcd {f : ArithmeticFunction ℤ} (hf : f.IsMultiplicative)
    (N : ℕ) : (compDivGcd f N).IsMultiplicative := by
  refine ⟨by simp [compDivGcd, hf.map_one], fun {a b} hab => ?_⟩
  simp only [compDivGcd, coe_mk]
  rw [Nat.gcd_comm, Nat.Coprime.gcd_mul N hab, Nat.gcd_comm N a, Nat.gcd_comm N b,
    Nat.mul_div_mul_comm (Nat.gcd_dvd_left a N) (Nat.gcd_dvd_left b N)]
  exact hf.map_mul_of_coprime ((hab.coprime_dvd_left (Nat.div_dvd_of_dvd
    (Nat.gcd_dvd_left a N))).coprime_dvd_right (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left b N)))

private def totientFun : ArithmeticFunction ℤ := ⟨fun q => (φ q : ℤ), by simp⟩

private theorem isMultiplicative_totientFun : totientFun.IsMultiplicative :=
  ⟨by simp [totientFun], fun h => by simp [totientFun, Nat.totient_mul h]⟩

private theorem holder_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ramanujanSum (p ^ (k + 1)) n * φ (p ^ (k + 1) / (p ^ (k + 1)).gcd n.natAbs) =
      μ (p ^ (k + 1) / (p ^ (k + 1)).gcd n.natAbs) * φ (p ^ (k + 1)) := by
  obtain ⟨j, hj, hg⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_left (p ^ (k + 1)) n.natAbs)
  have hjN : p ^ j ∣ n.natAbs := hg ▸ Nat.gcd_dvd_right _ _
  have hmax : j < k + 1 → ¬ p ^ (j + 1) ∣ n.natAbs := fun hjk h => by
    have := Nat.le_of_dvd (pow_pos hp.pos _)
      (hg ▸ Nat.dvd_gcd (pow_dvd_pow p (by omega : j + 1 ≤ k + 1)) h)
    exact absurd this (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by omega)))
  have e : ∀ i, (p : ℤ) ^ i ∣ n ↔ p ^ i ∣ n.natAbs := fun i => by
    rw [← Nat.cast_pow, Int.natCast_dvd]
  rw [hg, Nat.pow_div hj hp.pos, ramanujanSum_prime_pow_succ n hp k,
    Nat.totient_prime_pow_succ hp]
  simp only [e]
  rcases lt_trichotomy j k with hjk | rfl | hjk
  · have h1 : ¬ p ^ (k + 1) ∣ n.natAbs := fun h =>
      hmax (by omega) ((pow_dvd_pow p (by omega)).trans h)
    have h0 : ¬ p ^ k ∣ n.natAbs := fun h => hmax (by omega) ((pow_dvd_pow p (by omega)).trans h)
    rw [moebius_apply_prime_pow hp (by omega)]
    simp [h1, h0, show k + 1 - j ≠ 1 by omega]
  · simp only [hmax (by omega), hjN, ↓reduceIte]
    rw [show j + 1 - j = 1 by omega, pow_one, moebius_apply_prime hp, Nat.totient_prime hp]
    push_cast [hp.one_le]
    ring
  · obtain rfl : j = k + 1 := by omega
    simp only [hjN, (pow_dvd_pow p k.le_succ).trans hjN, ↓reduceIte, Nat.sub_self, pow_zero,
      Nat.totient_one, moebius_apply_one]
    push_cast [hp.one_le]
    ring

/-- **Hölder's formula.** With `g = gcd(q, n)`: `c_q(n) * φ(q / g) = μ(q / g) * φ(q)`. -/
theorem ramanujanSum_mul_totient :
    ramanujanSum q n * φ (q / Int.gcd q n) = μ (q / Int.gcd q n) * φ q := by
  let A := pmul (μ * dvdId n) (compDivGcd totientFun n.natAbs)
  let B := pmul (compDivGcd μ n.natAbs) totientFun
  have hA : A.IsMultiplicative := (isMultiplicative_moebius.mul (isMultiplicative_dvdId n)).pmul
    (isMultiplicative_compDivGcd isMultiplicative_totientFun _)
  have hB : B.IsMultiplicative :=
    (isMultiplicative_compDivGcd isMultiplicative_moebius _).pmul isMultiplicative_totientFun
  have hAB : A = B := by
    refine (IsMultiplicative.eq_iff_eq_on_prime_powers A hA B hB).mpr fun p i hp => ?_
    cases i with
    | zero => simp [hA.map_one, hB.map_one]
    | succ k =>
      change (μ * dvdId n) _ * _ = _
      rw [← ramanujanSum_eq_apply]
      exact holder_prime_pow n hp k
  rw [ramanujanSum_eq_apply]
  exact congrArg (· q) hAB

/-- Hölder's formula with the division carried out: with `g = gcd(q, n)`,
`c_q(n) = μ(q / g) * (φ(q) / φ(q / g))`, the quotient being exact. -/
theorem ramanujanSum_eq_moebius_mul_totient_div :
    ramanujanSum q n = μ (q / Int.gcd q n) * (φ q / φ (q / Int.gcd q n) : ℕ) := by
  rcases q.eq_zero_or_pos with rfl | hq
  · simp
  have hg : Int.gcd q n ∣ q := Nat.gcd_dvd_left q n.natAbs
  have hm : φ (q / Int.gcd q n) ≠ 0 := Nat.totient_pos.mpr
    (Nat.div_pos (Nat.le_of_dvd hq hg) (Nat.pos_of_dvd_of_pos hg hq)) |>.ne'
  refine mul_right_cancel₀ (Int.natCast_ne_zero.mpr hm) ?_
  rw [ramanujanSum_mul_totient, mul_assoc, ← Nat.cast_mul,
    Nat.div_mul_cancel (Nat.totient_dvd_of_dvd (Nat.div_dvd_of_dvd hg))]

/-! ### Roots of unity -/

section RootsOfUnity

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The `n`-th powers of the `d`-th roots of unity sum to `d` if `d ∣ n` and to `0`
otherwise. -/
theorem IsPrimitiveRoot.sum_nthRootsFinset_pow {ξ : R} {d : ℕ} (hξ : IsPrimitiveRoot ξ d)
    (n : ℕ) : ∑ η ∈ nthRootsFinset d (1 : R), η ^ n = if d ∣ n then (d : R) else 0 := by
  rcases d.eq_zero_or_pos with rfl | hd
  · simp
  have mem : ∀ η, η ∈ nthRootsFinset d (1 : R) ↔ η ^ d = 1 := fun _ =>
    Polynomial.mem_nthRootsFinset hd 1
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [sum_congr rfl fun η hη => by rw [pow_mul, (mem η).mp hη, one_pow], sum_const,
      hξ.card_nthRootsFinset, nsmul_one]
  · have hS : ξ ^ n * ∑ η ∈ nthRootsFinset d (1 : R), η ^ n =
        ∑ η ∈ nthRootsFinset d (1 : R), η ^ n := by
      rw [mul_sum]
      refine sum_nbij' (ξ * ·) (ξ ^ (d - 1) * ·) (fun η hη => ?_) (fun η hη => ?_)
        (fun η _ => ?_) (fun η _ => ?_) (fun η _ => by rw [mul_pow])
      · rw [mem] at hη ⊢; rw [mul_pow, hξ.pow_eq_one, hη, one_mul]
      · rw [mem] at hη ⊢; rw [mul_pow, ← pow_mul, mul_comm (d - 1) d, pow_mul, hξ.pow_eq_one,
          one_pow, hη, one_mul]
      · rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hd, hξ.pow_eq_one, one_mul]
      · rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hd, hξ.pow_eq_one, one_mul]
    have hne : ξ ^ n - 1 ≠ 0 := sub_ne_zero.mpr fun h1 => h ((hξ.pow_eq_one_iff_dvd n).mp h1)
    exact (mul_eq_zero.mp (by linear_combination hS : (ξ ^ n - 1) * _ = 0)).resolve_left hne

/-- `c_q(n)` is the sum of the `n`-th powers of the primitive `q`-th roots of unity. -/
theorem IsPrimitiveRoot.sum_primitiveRoots_pow {ζ : R} {q : ℕ} (hζ : IsPrimitiveRoot ζ q)
    (n : ℕ) : ∑ η ∈ primitiveRoots q R, η ^ n = ramanujanSum q n := by
  classical
  rcases q.eq_zero_or_pos with rfl | hq
  · simp
  refine eq_ramanujanSum_of_sum_eq (f := fun d => ∑ η ∈ primitiveRoots d R, η ^ n) n hq
    fun d hd => ?_
  rw [← sum_biUnion (fun a _ b _ hab => IsPrimitiveRoot.disjoint hab),
    ← nthRoots_one_eq_biUnion_primitiveRoots]
  obtain ⟨e, rfl⟩ := hd
  have hξ := hζ.pow_of_dvd (right_ne_zero_of_mul hq.ne') (dvd_mul_left e d)
  rw [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (right_ne_zero_of_mul hq.ne'))] at hξ
  rw [hξ.sum_nthRootsFinset_pow]
  simp [Int.natCast_dvd_natCast]

/-- `c_q(n) = ∑_{k < q, gcd(k, q) = 1} ζ ^ (k * n)` for a primitive `q`-th root of unity `ζ`. -/
theorem IsPrimitiveRoot.sum_pow_coprime {ζ : R} {q : ℕ} (hζ : IsPrimitiveRoot ζ q) (n : ℕ) :
    ∑ k ∈ range q with k.Coprime q, ζ ^ (k * n) = ramanujanSum q n := by
  rw [← hζ.sum_primitiveRoots_pow n]
  rcases q.eq_zero_or_pos with rfl | hq
  · simp
  have : NeZero q := ⟨hq.ne'⟩
  refine sum_nbij (ζ ^ ·) (fun k hk => ?_) (fun i hi j hj h => ?_) (fun η hη => ?_)
    (fun k _ => pow_mul ζ k n)
  · rw [mem_filter, mem_range] at hk
    exact (mem_primitiveRoots hq).mpr (hζ.pow_of_coprime k hk.2)
  · rw [mem_coe, mem_filter, mem_range] at hi hj
    exact hζ.pow_inj hi.1 hj.1 h
  · rw [mem_coe, mem_primitiveRoots hq, hζ.isPrimitiveRoot_iff] at hη
    obtain ⟨i, hi, hc, rfl⟩ := hη
    exact ⟨i, by simpa using ⟨hi, hc⟩, rfl⟩

end RootsOfUnity

open Complex in
/-- `c_q(n) = ∑_{k < q, gcd(k, q) = 1} exp(2πikn/q)`. -/
theorem ramanujanSum_eq_sum_exp (q n : ℕ) :
    (ramanujanSum q n : ℂ) =
      ∑ k ∈ range q with k.Coprime q, exp (2 * Real.pi * I * k * n / q) := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  rw [← (isPrimitiveRoot_exp q hq).sum_pow_coprime n]
  refine sum_congr rfl fun k _ => ?_
  rw [← exp_natCast_mul]
  push_cast
  ring_nf
