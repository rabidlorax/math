module

public import Mathlib
public import MathInfra.New.GaussSeq
public import MathInfra.FormalizedElsewhere.LucasSeq

/-!
# Zeta series of integer sequences

For a sequence `f : ℕ → R`, a power series `P` with constant coefficient `1` is a *zeta series*
of `f` if

`P' = P * ∑_{n ≥ 0} f(n + 1) * Xⁿ`.

Over `ℚ` the unique such series is `exp(∑_{n ≥ 1} f(n) * Xⁿ / n)`. When `f(n)` counts the fixed
points of the `n`-th iterate of a map, this is the Artin–Mazur zeta function; when `f(n)` counts
the points of a variety over `𝔽_(qⁿ)`, it is the Hasse–Weil zeta function. The definition uses no
division, so it makes sense over any commutative ring.

The question is when `f : ℕ → ℤ` has a zeta series with *integer* coefficients. **Dold's
criterion** answers it: exactly when `f` satisfies the Gauss congruences of
`MathInfra.New.GaussSeq`. The proof approximates the series by finite Witt products
`∏_{d ≤ N} (1 - X ^ d) ^ (-h(d))`, where `f(n) = ∑_{d ∣ n} d * h(d)`.

The main application is to traces. For a square matrix `A` over a commutative ring,
`det(1 - X • A)` is a zeta series of `n ↦ -tr(Aⁿ)` (Jacobi's formula, or Newton's identities).
So for an integer matrix, `n ↦ tr(Aⁿ)` satisfies the Gauss congruences. In particular
`tr(A ^ (p ^ (k + 1) * m)) ≡ tr(A ^ (p ^ k * m)) (mod p ^ (k + 1))`, which extends
`tr(Aᵖ) ≡ tr(A) ^ p (mod p)`, Mathlib's `ZMod.trace_pow_card`. The Lucas sequence
`V_n(P, Q)` is the trace of the `n`-th power of a `2 × 2` matrix, so it satisfies them as well.

Sequences satisfying the Gauss congruences are also called Dold or Fermat sequences; those with
`orbitCount f ≥ 0` are the realizable sequences. `ghostSeries f` is the logarithmic derivative
`P' / P` of the zeta series.

## Main definitions

* `ghostSeries f`    : `∑_{n ≥ 0} f(n + 1) * Xⁿ`.
* `IsZetaSeries f P` : `P(0) = 1` and `P' = P * ghostSeries f`.
* `cycInv d`, `cycGhost d` : `1 / (1 - X ^ d)`, and the sequence it is the zeta series of,
  `n ↦ d` if `d ∣ n`, else `0`.
* `cycFactor d k`    : `(1 - X ^ d) ^ (-k)` for `k : ℤ`.
* `wittProd h N`     : the Witt product `∏_{d = 1}^{N} (1 - X ^ d) ^ (-h(d))` over `ℤ`.
* `resolventSeries A`: `∑ Aⁿ Xⁿ`, the inverse of `1 - X • A`.
* `lucasMatrix P Q`  : `!![P, -Q; 1, 0]`.

## Main results

* `IsZetaSeries.mul`, `IsZetaSeries.of_mul_eq_one`, `IsZetaSeries.prod` : zeta series turn sums and
  negatives of sequences into products and inverses of series.
* `IsZetaSeries.unique`, `IsZetaSeries.coeff_eq` : over `ℤ` there is at most one zeta series, and
  sequences that agree on `1, …, N` have zeta series that agree up to degree `N`.
* `isZetaSeries_wittProd` : the Witt product is a zeta series of `n ↦ ∑_{d ∣ n, d ≤ N} d * h(d)`.
* `isGaussSeq_iff_exists_isZetaSeries` : **Dold's criterion**.
* `isZetaSeries_charpolyRev`, `isZetaSeries_trace_pow` : **Jacobi's formula**: `det(1 - X • A)` is
  a zeta series of `n ↦ -tr(Aⁿ)`, and its inverse one of `n ↦ tr(Aⁿ)`.
* `isGaussSeq_trace_pow`, `trace_pow_modEq` : the Gauss congruences for `tr(Aⁿ)`.
* `isGaussSeq_lucasV` : the Gauss congruences for `V_n(P, Q)`.
* `exists_isZetaSeries_card_fixedPoints` : the Artin–Mazur zeta function of a self-map of a finite
  set has integer coefficients.
* `coeff_wittProd_necklace` : the cyclotomic identity `1 / (1 - aX) = ∏_d (1 - X ^ d) ^ (-M(a, d))`,
  degree by degree, with `M(a, d)` the necklace numbers.

## Prior art

Checked in November 2026. Mathlib (2026-11-19) has `tr(Aᵖ) = tr(A) ^ p` over finite fields
(`FiniteField.trace_pow_card`, `ZMod.trace_pow_card`), which over `ZMod p` is equivalent by
Fermat to the case `k = 0`, `m = 1` of `trace_pow_modEq`, and the degree-1 coefficient of
`det(1 - X • A)` (`Matrix.coeff_charpolyRev_eq_neg_trace`). Jacobi's formula for
`det(1 - X • A)` was proposed in the closed, unmerged Mathlib PR #44901. The direction "Gauss
congruences imply an integral zeta series" is formalized, via the Dieudonné–Dwork criterion over
`ℚ`, as `integral_exp_of_dold` in the Lean project `the-omega-institute/trureturing`.
The converse, the Witt products and the trace and Lucas applications were not found formalized.
-/

@[expose] public section

open Finset PowerSeries ArithmeticFunction
open scoped ArithmeticFunction.Moebius

variable {R : Type*} [CommRing R]

/-! ### Zeta series -/

/-- `ghostSeries f = ∑_{n ≥ 0} f(n + 1) * Xⁿ`. -/
noncomputable def ghostSeries (f : ℕ → R) : R⟦X⟧ := mk fun n => f (n + 1)

/-- `P` is a zeta series of `f`: `P(0) = 1` and `P' = P * ∑_{n ≥ 0} f(n + 1) * Xⁿ`. Over `ℚ`
this says `P = exp(∑_{n ≥ 1} f(n) * Xⁿ / n)`. -/
def IsZetaSeries (f : ℕ → R) (P : R⟦X⟧) : Prop :=
  constantCoeff P = 1 ∧ d⁄dX P = P * ghostSeries f

@[simp] theorem coeff_ghostSeries (f : ℕ → R) (n : ℕ) : coeff n (ghostSeries f) = f (n + 1) :=
  coeff_mk _ _

@[simp] theorem ghostSeries_add (f g : ℕ → R) :
    ghostSeries (f + g) = ghostSeries f + ghostSeries g := by ext; simp

@[simp] theorem ghostSeries_neg (f : ℕ → R) : ghostSeries (-f) = -ghostSeries f := by ext; simp

@[simp] theorem ghostSeries_zero : ghostSeries (0 : ℕ → R) = 0 := by ext; simp

variable {f g : ℕ → R} {P Q : R⟦X⟧}

/-- The zeta series condition, coefficient by coefficient:
`(n + 1) * a(n + 1) = ∑_{i + j = n} a(i) * f(j + 1)`, where `a(n)` is the `n`-th coefficient. -/
theorem isZetaSeries_iff_coeff :
    IsZetaSeries f P ↔ constantCoeff P = 1 ∧
      ∀ n, coeff (n + 1) P * (n + 1) = ∑ x ∈ antidiagonal n, coeff x.1 P * f (x.2 + 1) := by
  unfold IsZetaSeries
  refine and_congr_right fun _ => ?_
  rw [PowerSeries.ext_iff]
  simp [coeff_derivative, coeff_mul]

theorem isZetaSeries_zero : IsZetaSeries (0 : ℕ → R) 1 := by
  simp [IsZetaSeries]

/-- Zeta series turn sums into products. -/
theorem IsZetaSeries.mul (hP : IsZetaSeries f P) (hQ : IsZetaSeries g Q) :
    IsZetaSeries (f + g) (P * Q) := by
  refine ⟨by simp [hP.1, hQ.1], ?_⟩
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hP.2, hQ.2, ghostSeries_add]
  ring

/-- If `P * Q = 1`, then `Q` is the zeta series of `-f`. -/
theorem IsZetaSeries.of_mul_eq_one (hP : IsZetaSeries f P) (h : P * Q = 1) :
    IsZetaSeries (-f) Q := by
  have hQ : constantCoeff Q = 1 := by
    simpa [hP.1] using congrArg (constantCoeff (R := R)) h
  refine ⟨hQ, ?_⟩
  have h0 := congrArg (d⁄dX) h
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hP.2, derivative_one] at h0
  rw [ghostSeries_neg]
  linear_combination Q * h0 - (d⁄dX Q + Q * ghostSeries f) * h

theorem IsZetaSeries.pow (hP : IsZetaSeries f P) (n : ℕ) : IsZetaSeries (n • f) (P ^ n) := by
  induction n with
  | zero => simpa using isZetaSeries_zero
  | succ n ih => rw [pow_succ, succ_nsmul]; exact ih.mul hP

theorem IsZetaSeries.prod {ι : Type*} (s : Finset ι) {f : ι → ℕ → R} {P : ι → R⟦X⟧}
    (h : ∀ i ∈ s, IsZetaSeries (f i) (P i)) : IsZetaSeries (∑ i ∈ s, f i) (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isZetaSeries_zero
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    exact (h a (mem_insert_self a s)).mul (ih fun i hi => h i (mem_insert_of_mem hi))

/-- `1 / (1 - aX) = ∑ aⁿ Xⁿ` is a zeta series of `n ↦ aⁿ`. -/
theorem isZetaSeries_geometric (a : R) : IsZetaSeries (a ^ ·) (mk (a ^ ·)) := by
  refine isZetaSeries_iff_coeff.mpr ⟨by simp, fun n => ?_⟩
  rw [sum_congr rfl fun x hx => by
    rw [coeff_mk, ← pow_add, (mem_antidiagonal.mp hx ▸ rfl : x.1 + (x.2 + 1) = n + 1)]]
  simp [Finset.Nat.card_antidiagonal, mul_comm]

/-! ### Cyclotomic factors -/

/-- `cycInv d = ∑_{d ∣ n} Xⁿ`, which is `1 / (1 - X ^ d)` for `d ≠ 0`. -/
noncomputable def cycInv (d : ℕ) : R⟦X⟧ := mk fun n => if d ∣ n then 1 else 0

/-- `cycGhost d n = d` if `d ∣ n` and `0` otherwise: the sequence of which `cycInv d` is a zeta
series. -/
def cycGhost (d n : ℕ) : R := if d ∣ n then (d : R) else 0

theorem one_sub_X_pow_mul_cycInv {d : ℕ} (hd : d ≠ 0) : (1 - X ^ d : R⟦X⟧) * cycInv d = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul', coeff_one]
  simp only [cycInv, coeff_mk]
  rcases lt_or_ge n d with hn | hn
  · have : d ∣ n ↔ n = 0 := ⟨fun h => Nat.eq_zero_of_dvd_of_lt h hn, fun h => h ▸ dvd_zero d⟩
    simp [this, not_le.mpr hn]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    simp [Nat.dvd_add_self_right, hd]

theorem ghostSeries_cycGhost {d : ℕ} (hd : d ≠ 0) :
    ghostSeries (cycGhost d) = C (d : R) * X ^ (d - 1) * cycInv d := by
  ext n
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_ghostSeries]
  simp only [cycGhost, cycInv, coeff_mk]
  rcases lt_or_ge (n + 1) d with hn | hn
  · have : ¬d ∣ n + 1 := fun h => (Nat.le_of_dvd n.succ_pos h).not_gt hn
    simp [this, show ¬d - 1 ≤ n by omega]
  · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' hn
    rw [ite_eq_left (by omega : d - 1 ≤ n), show n - (d - 1) = m by omega, hm]
    simp only [Nat.dvd_add_self_right]
    split_ifs <;> simp

theorem isZetaSeries_one_sub_X_pow {d : ℕ} (hd : d ≠ 0) :
    IsZetaSeries (-cycGhost d) (1 - X ^ d : R⟦X⟧) := by
  refine ⟨by simp [hd], ?_⟩
  rw [map_sub, derivative_one, derivative_X_pow, ghostSeries_neg, ghostSeries_cycGhost hd]
  linear_combination (C (d : R) * X ^ (d - 1)) * one_sub_X_pow_mul_cycInv (R := R) hd

/-- `1 / (1 - X ^ d)` is a zeta series of `n ↦ d` if `d ∣ n`, `0` otherwise. -/
theorem isZetaSeries_cycInv {d : ℕ} (hd : d ≠ 0) : IsZetaSeries (cycGhost d) (cycInv d : R⟦X⟧) :=
  by simpa using
    (isZetaSeries_one_sub_X_pow (R := R) hd).of_mul_eq_one (one_sub_X_pow_mul_cycInv hd)

/-! ### Witt products and Dold's criterion -/

/-- `cycFactor d k = (1 - X ^ d) ^ (-k)` for `k : ℤ` and `d ≠ 0`. -/
noncomputable def cycFactor (d : ℕ) (k : ℤ) : ℤ⟦X⟧ :=
  if 0 ≤ k then cycInv d ^ k.toNat else (1 - X ^ d) ^ (-k).toNat

theorem isZetaSeries_cycFactor {d : ℕ} (hd : d ≠ 0) (k : ℤ) :
    IsZetaSeries (fun n => k * cycGhost d n) (cycFactor d k) := by
  unfold cycFactor
  split_ifs with hk
  · convert (isZetaSeries_cycInv hd).pow k.toNat using 1
    ext n; simp [Int.toNat_of_nonneg hk]
  · convert (isZetaSeries_one_sub_X_pow hd).pow (-k).toNat using 1
    ext n; simp [Int.toNat_of_nonneg (by omega : 0 ≤ -k)]

/-- The Witt product `∏_{d = 1}^{N} (1 - X ^ d) ^ (-h(d))`. -/
noncomputable def wittProd (h : ℕ → ℤ) (N : ℕ) : ℤ⟦X⟧ := ∏ d ∈ Icc 1 N, cycFactor d (h d)

/-- The Witt product is a zeta series of `n ↦ ∑_{d ∣ n, d ≤ N} d * h(d)`. -/
theorem isZetaSeries_wittProd (h : ℕ → ℤ) (N : ℕ) :
    IsZetaSeries (fun n => ∑ d ∈ Icc 1 N with d ∣ n, (d : ℤ) * h d) (wittProd h N) := by
  unfold wittProd
  convert IsZetaSeries.prod (Icc 1 N) (f := fun d n => h d * cycGhost d n)
    (fun d hd => isZetaSeries_cycFactor (by simp at hd; omega) (h d)) using 1
  ext n
  rw [Finset.sum_apply, sum_filter]
  refine sum_congr rfl fun d _ => ?_
  simp only [cycGhost]
  split_ifs <;> ring

theorem Nat.filter_Icc_dvd_eq_divisors {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    {d ∈ Icc 1 N | d ∣ n} = n.divisors := by
  ext d
  simp only [mem_filter, mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨-, h⟩; exact ⟨h, hn.ne'⟩
  · rintro ⟨h, -⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos h hn, (Nat.le_of_dvd hn h).trans hnN⟩, h⟩

theorem Nat.filter_Icc_dvd_succ_eq_properDivisors (N : ℕ) :
    {d ∈ Icc 1 N | d ∣ N + 1} = (N + 1).properDivisors := by
  ext d
  simp only [mem_filter, mem_Icc, Nat.mem_properDivisors]
  constructor
  · rintro ⟨⟨-, h⟩, hd⟩; exact ⟨hd, by omega⟩
  · rintro ⟨hd, h⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd N.succ_pos, by omega⟩, hd⟩

/-- Two zeta series over `ℤ` of sequences that agree on `1, …, N` agree up to degree `N`. -/
theorem IsZetaSeries.coeff_eq {f g : ℕ → ℤ} {P Q : ℤ⟦X⟧} (hP : IsZetaSeries f P)
    (hQ : IsZetaSeries g Q) {N : ℕ} (hfg : ∀ n, 0 < n → n ≤ N → f n = g n) :
    ∀ n ≤ N, coeff n P = coeff n Q := by
  rw [isZetaSeries_iff_coeff] at hP hQ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  rcases n with _ | m
  · simp only [coeff_zero_eq_constantCoeff_apply, hP.1, hQ.1]
  · have hsum : ∑ x ∈ antidiagonal m, coeff x.1 P * f (x.2 + 1) =
        ∑ x ∈ antidiagonal m, coeff x.1 Q * g (x.2 + 1) := sum_congr rfl fun x hx => by
      have := mem_antidiagonal.mp hx
      rw [ih x.1 (by omega) (by omega), hfg (x.2 + 1) (by omega) (by omega)]
    exact mul_right_cancel₀ (by positivity) ((hP.2 m).trans (hsum.trans (hQ.2 m).symm))

/-- Over `ℤ` a sequence has at most one zeta series. -/
theorem IsZetaSeries.unique {f : ℕ → ℤ} {P Q : ℤ⟦X⟧} (hP : IsZetaSeries f P)
    (hQ : IsZetaSeries f Q) : P = Q :=
  PowerSeries.ext fun n => hP.coeff_eq hQ (N := n) (fun _ _ _ => rfl) n le_rfl

/-- If, for every `N`, `g N` agrees with `f` on `1, …, N` and has a zeta series over `ℤ`, then
so does `f`. -/
theorem exists_isZetaSeries_of_forall {f : ℕ → ℤ} {g : ℕ → ℕ → ℤ} {P : ℕ → ℤ⟦X⟧}
    (hP : ∀ N, IsZetaSeries (g N) (P N)) (hg : ∀ N n, 0 < n → n ≤ N → g N n = f n) :
    ∃ Q, IsZetaSeries f Q := by
  have key : ∀ M n, n ≤ M → coeff n (P n) = coeff n (P M) := fun M n hn =>
    (hP n).coeff_eq (hP M) (fun k hk hkn => (hg n k hk hkn).trans (hg M k hk (hkn.trans hn)).symm)
      n le_rfl
  refine ⟨mk fun n => coeff n (P n), isZetaSeries_iff_coeff.mpr ⟨?_, fun n => ?_⟩⟩
  · simpa [coeff_zero_eq_constantCoeff_apply] using (hP 0).1
  · simp only [coeff_mk]
    rw [(isZetaSeries_iff_coeff.mp (hP (n + 1))).2 n]
    refine sum_congr rfl fun x hx => ?_
    have := mem_antidiagonal.mp hx
    rw [key (n + 1) x.1 (by omega), hg (n + 1) (x.2 + 1) (by omega) (by omega)]

/-- If `f` has a zeta series over `ℤ` and vanishes on `1, …, N`, then `N + 1 ∣ f(N + 1)`. -/
theorem IsZetaSeries.dvd {f : ℕ → ℤ} {P : ℤ⟦X⟧} (hP : IsZetaSeries f P) {N : ℕ}
    (hf : ∀ n, 0 < n → n ≤ N → f n = 0) : ((N + 1 : ℕ) : ℤ) ∣ f (N + 1) := by
  have h1 := hP.coeff_eq isZetaSeries_zero (N := N) (fun n hn hnN => by simp [hf n hn hnN])
  have h := (isZetaSeries_iff_coeff.mp hP).2 N
  rw [sum_eq_single (0, N)] at h
  · rw [coeff_zero_eq_constantCoeff_apply, hP.1, one_mul] at h
    exact ⟨coeff (N + 1) P, by push_cast; linear_combination -h⟩
  · rintro ⟨i, j⟩ hx hne
    have := mem_antidiagonal.mp hx
    have hi : i ≠ 0 := by rintro rfl; simp_all
    rw [h1 i (by omega), coeff_one, ite_eq_right hi, zero_mul]
  · intro h; simp at h

/-- **Dold's criterion**: `f` satisfies the Gauss congruences if and only if it has a zeta series
with integer coefficients. -/
theorem isGaussSeq_iff_exists_isZetaSeries {f : ℕ → ℤ} :
    IsGaussSeq f ↔ ∃ P : ℤ⟦X⟧, IsZetaSeries f P := by
  constructor
  · intro hf
    refine exists_isZetaSeries_of_forall (fun N => isZetaSeries_wittProd (orbitCount f) N)
      fun N n hn hnN => ?_
    rw [Nat.filter_Icc_dvd_eq_divisors hn hnN]
    exact hf.sum_mul_orbitCount hn
  · rintro ⟨P, hP⟩
    suffices ∀ N n : ℕ, n ≤ N → (n : ℤ) ∣ ∑ d ∈ n.divisors, μ d * f (n / d) from
      fun n => this n n le_rfl
    intro N
    induction N with
    | zero => intro n hn; simp [Nat.le_zero.mp hn]
    | succ N ih =>
      intro n hn
      rcases hn.lt_or_eq with hn | rfl
      · exact ih n (by omega)
      have hmul : ∀ d ≤ N, (d : ℤ) * orbitCount f d = ∑ e ∈ d.divisors, μ e * f (d / e) :=
        fun d hd => Int.mul_ediv_cancel' (ih d hd)
      have hQ := hP.mul (isZetaSeries_wittProd (-orbitCount f) N)
      have := hQ.dvd (N := N) fun n hn hnN => by
        simp only [Pi.add_apply, Pi.neg_apply, mul_neg, sum_neg_distrib,
          Nat.filter_Icc_dvd_eq_divisors hn hnN]
        rw [sum_congr rfl fun d hd => hmul d ((Nat.divisor_le hd).trans hnN),
          sum_sum_moebius_mul f hn, add_neg_cancel]
      simp only [Pi.add_apply, Pi.neg_apply, mul_neg, sum_neg_distrib,
        Nat.filter_Icc_dvd_succ_eq_properDivisors] at this
      rw [sum_congr rfl fun d hd => hmul d (by have := Nat.mem_properDivisors.mp hd; omega)] at this
      have hsum := sum_sum_moebius_mul f (n := N + 1) (by omega)
      rw [← Nat.insert_self_properDivisors (by omega), sum_insert Nat.self_notMem_properDivisors]
        at hsum
      convert this using 1
      rw [← hsum]
      abel

/-! ### Traces of matrix powers -/

section Trace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The resolvent `∑ Aⁿ Xⁿ` of `A`, the inverse of `1 - X • A`. -/
noncomputable def resolventSeries (A : Matrix ι ι R) : Matrix ι ι R⟦X⟧ :=
  Matrix.of fun i j => mk fun n => (A ^ n) i j

theorem one_sub_X_smul_mul_resolventSeries (A : Matrix ι ι R) :
    (1 - (X : R⟦X⟧) • A.map C) * resolventSeries A = 1 := by
  ext i j n
  rw [sub_mul, one_mul, Matrix.smul_mul, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    map_sub]
  rcases n with _ | m
  · simp [resolventSeries, Matrix.one_apply]
  · rw [coeff_succ_X_mul]
    simp only [resolventSeries, Matrix.of_apply, coeff_mk, Matrix.mul_apply, map_sum,
      pow_succ', Matrix.one_apply]
    split_ifs <;> simp [coeff_one]

theorem trace_resolventSeries_mul (A : Matrix ι ι R) :
    (resolventSeries A * A.map C).trace = mk fun n => (A ^ (n + 1)).trace := by
  ext n
  simp [Matrix.trace, Matrix.mul_apply, resolventSeries, map_sum, coeff_mul_C, pow_succ]

theorem coe_charpolyRev (A : Matrix ι ι R) :
    (A.charpolyRev : R⟦X⟧) = (1 - (X : R⟦X⟧) • A.map C).det := by
  rw [Matrix.charpolyRev, ← Polynomial.coeToPowerSeries.ringHom_apply, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h] <;> ring

/-- **Jacobi's formula** for `det (1 - X • A)`: it is a zeta series of `n ↦ -tr(Aⁿ)`, that is,
`(det (1 - X • A))' = -det (1 - X • A) * ∑ tr(Aⁿ⁺¹) Xⁿ`. -/
theorem isZetaSeries_charpolyRev (A : Matrix ι ι R) :
    IsZetaSeries (fun n => -(A ^ n).trace) (A.charpolyRev : R⟦X⟧) := by
  refine ⟨by rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
    Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev], ?_⟩
  -- Shift the variable: `ψ` sends `X` to `Y + X`, where `Y` is the variable of `R⟦X⟧[Y]`.
  let ψ : Polynomial R →+* Polynomial R⟦X⟧ :=
    Polynomial.eval₂RingHom (Polynomial.C.comp C) (Polynomial.X + Polynomial.C X)
  have h1 : (ψ A.charpolyRev).coeff 1 = (Polynomial.derivative A.charpolyRev : R⟦X⟧) := by
    rw [← Polynomial.eval₂_C_X_eq_coe, ← Polynomial.eval_map, ← Polynomial.derivative_map,
      ← Polynomial.taylor_coeff_one]
    congr 1
    simp only [ψ, Polynomial.coe_eval₂RingHom, Polynomial.taylor_apply, Polynomial.comp,
      Polynomial.eval₂_map]
  set M := 1 - (X : R⟦X⟧) • A.map C with hM
  have h2 : ψ A.charpolyRev = (M.map Polynomial.C * (1 + (Polynomial.X : Polynomial R⟦X⟧) •
      (-(resolventSeries A * A.map C)).map Polynomial.C)).det := by
    rw [Matrix.charpolyRev, RingHom.map_det, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
      Matrix.map_neg (hf := map_neg Polynomial.C), Matrix.mul_neg, ← Matrix.map_mul,
      ← Matrix.mul_assoc, one_sub_X_smul_mul_resolventSeries, Matrix.one_mul]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [ψ, hM, h] <;> ring
  rw [derivative_coe, ← h1, h2, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    Polynomial.coeff_C_mul, Matrix.coeff_det_one_add_X_smul_one, Matrix.trace_neg,
    trace_resolventSeries_mul, coe_charpolyRev, ← hM]
  congr 1

/-- `1 / det (1 - X • A)` is a zeta series of `n ↦ tr(Aⁿ)`. -/
theorem isZetaSeries_trace_pow (A : Matrix ι ι R) :
    IsZetaSeries (fun n => (A ^ n).trace) (invOfUnit (A.charpolyRev : R⟦X⟧) 1) := by
  have h := isZetaSeries_charpolyRev A
  convert h.of_mul_eq_one (mul_invOfUnit _ _ (by rw [Units.val_one]; exact h.1)) using 1
  ext n
  simp

/-- **Gauss congruences for traces**: for every square integer matrix `A`,
`n ∣ ∑_{d ∣ n} μ(d) * tr(A ^ (n / d))`. -/
theorem isGaussSeq_trace_pow (A : Matrix ι ι ℤ) : IsGaussSeq fun n => (A ^ n).trace :=
  isGaussSeq_iff_exists_isZetaSeries.mpr ⟨_, isZetaSeries_trace_pow A⟩

/-- `tr(A ^ (p ^ (k + 1) * m)) ≡ tr(A ^ (p ^ k * m)) [ZMOD p ^ (k + 1)]` for every prime `p`. -/
theorem trace_pow_modEq (A : Matrix ι ι ℤ) {p : ℕ} (hp : p.Prime) (k m : ℕ) :
    (A ^ (p ^ (k + 1) * m)).trace ≡ (A ^ (p ^ k * m)).trace [ZMOD p ^ (k + 1)] :=
  isGaussSeq_iff_modEq.mp (isGaussSeq_trace_pow A) p k m hp

end Trace

/-! ### Lucas sequences -/

/-- The companion matrix `!![P, -Q; 1, 0]` of `x ^ 2 - P * x + Q`. -/
def lucasMatrix (P Q : R) : Matrix (Fin 2) (Fin 2) R := !![P, -Q; 1, 0]

theorem trace_lucasMatrix_pow (P Q : R) (n : ℕ) : (lucasMatrix P Q ^ n).trace = lucasV P Q n := by
  have hsq : lucasMatrix P Q ^ 2 = P • lucasMatrix P Q - Q • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lucasMatrix, sq, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]
  have hrec : IsLucasRec P Q fun n => (lucasMatrix P Q ^ n).trace := fun n => by
    change (lucasMatrix P Q ^ (n + 2)).trace =
      P * (lucasMatrix P Q ^ (n + 1)).trace - Q * (lucasMatrix P Q ^ n).trace
    rw [pow_add, hsq, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, ← pow_succ,
      Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
  exact congrFun (hrec.ext (isLucasRec_lucasV P Q) (by simp [Matrix.trace])
    (by simp [lucasMatrix, Matrix.trace, Fin.sum_univ_two])) n

/-- The Lucas sequence `V_n(P, Q)` satisfies the Gauss congruences. -/
theorem isGaussSeq_lucasV (P Q : ℤ) : IsGaussSeq (lucasV P Q) := by
  simpa [trace_lucasMatrix_pow] using isGaussSeq_trace_pow (lucasMatrix P Q)

/-! ### Applications to the examples of `GaussSeq` -/

/-- The zeta series of the fixed-point counts of a self-map of a finite set (its Artin–Mazur zeta
function) has integer coefficients. -/
theorem exists_isZetaSeries_card_fixedPoints {α : Type*} [Fintype α] [DecidableEq α]
    (T : α → α) : ∃ P : ℤ⟦X⟧, IsZetaSeries (fun n => (#{x | T^[n] x = x} : ℤ)) P :=
  isGaussSeq_iff_exists_isZetaSeries.mp (isGaussSeq_card_fixedPoints T)

/-- **The cyclotomic identity**, truncated: `∏_{d = 1}^{N} (1 - X ^ d) ^ (-M(a, d))` agrees with
`1 / (1 - aX)` up to degree `N`, where `M(a, d)` is the necklace number. -/
theorem coeff_wittProd_necklace (a : ℤ) {n N : ℕ} (hn : n ≤ N) :
    coeff n (wittProd (necklace a) N) = a ^ n := by
  rw [(isZetaSeries_wittProd (necklace a) N).coeff_eq (isZetaSeries_geometric a)
    (fun k hk hkN => by rw [Nat.filter_Icc_dvd_eq_divisors hk hkN]; exact sum_mul_necklace a hk)
    n hn, coeff_mk]
