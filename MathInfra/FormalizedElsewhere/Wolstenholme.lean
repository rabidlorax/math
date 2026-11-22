module

public import Mathlib

/-!
# Wolstenholme's theorem

For a prime `p ≥ 5`, **Wolstenholme's theorem** says

`C(2p - 1, p - 1) ≡ 1 (mod p³)`  and  `1 + 1 / 2 + ⋯ + 1 / (p - 1) ≡ 0 (mod p²)`.

This file proves the first, and the congruences around it, from a single fact about the
polynomial `(1 + X) ^ p`: **Babbage's** `C(2p - 1, p - 1) ≡ 1 (mod p²)` for odd `p`, and
**Ljunggren's** `C(ap, bp) ≡ C(a, b)`, modulo `p²` for every prime and modulo `p³` for
`p ≥ 5` (also called Jacobsthal's congruence; modulo `p` it is a case of Lucas's theorem). The
second follows by pairing `1 / k` with `1 / (p - k)` modulo `p²`. The last section is about
**Fermat quotients** `q_p(a) = (a ^ (p - 1) - 1) / p`: they turn products into sums modulo `p`,
and **Eisenstein's congruence** expresses `q_p(2)` as a harmonic sum.

Write `c_k = C(p, k) / p` for `0 < k < p`, an integer. The binomial congruences rest on two facts:

* `c_k ≡ (-1) ^ (k - 1) / k (mod p)`, from `k * c_k = C(p - 1, k - 1)`;
* `(1 + X) ^ p = 1 + X ^ p + p * G` with `G = ∑_{0 < k < p} c_k * X ^ k`.

Expanding `(1 + X) ^ (ap) = (1 + X ^ p + p * G) ^ a` and reading off the coefficient of
`X ^ (bp)` gives `C(a, b) + p² x + p³ s`. The term linear in `p` contributes nothing, and for
`p ≥ 5`, `p ∣ x` because the coefficient of `G²` involved is
`∑_{0 < k < p} c_k * c_(p - k) ≡ ∑_{0 < k < p} 1 / k² ≡ 0 (mod p)`.

## Main definitions

* `chooseDivPoly p`    : the polynomial `G = ∑_{0 < k < p} c_k * X ^ k`.
* `fermatQuotient p a` : the Fermat quotient `(a ^ (p - 1) - 1) / p`.

## Main results

* `choose_prime_div_cast`  : `c_k ≡ (-1) ^ (k - 1) / k (mod p)`.
* `sum_Ico_inv_pow`        : `∑_{0 < k < p} 1 / k ^ m` is `-1` modulo `p` if `p - 1 ∣ m`, else `0`.
* `one_add_X_pow_prime`    : `(1 + X) ^ p = 1 + X ^ p + p * G`.
* `choose_mul_modEq_choose_sq`, `choose_mul_modEq_choose_cube` : Ljunggren's congruence modulo
  `p²` (every `p`) and `p³` (`p ≥ 5`).
* `choose_two_mul_sub_one_modEq_one_sq`, `choose_two_mul_sub_one_modEq_one_cube` : Babbage's
  and Wolstenholme's theorems.
* `sum_Ico_inv_eq_zero_zmod_sq`, `sq_dvd_num_harmonic` : `∑_{0 < k < p} 1 / k = 0` in
  `ZMod (p ^ 2)`, and `p²` divides the numerator of `H_(p - 1)`.
* `fermatQuotient_mul`, `fermatQuotient_add_mul`, `dvd_fermatQuotient_iff` : products, shifts
  by multiples of `p`, and the Wieferich condition.
* `two_mul_fermatQuotient_two`, `two_mul_fermatQuotient_two_cast`,
  `two_mul_fermatQuotient_two_eq_neg_sum` : Eisenstein's formula `2 q_p(2) = ∑_{0 < k < p} c_k`, and
  `2 q_p(2) ≡ ∑_{0 < k < p} (-1) ^ (k - 1) / k ≡ -∑_{0 < j ≤ (p - 1) / 2} 1 / j (mod p)`.

## Prior art (checked November 2026)

Not in Mathlib (pinned 2026-11-19 and `master` of 2026-11-21). Mathlib PR
[#29675](https://github.com/leanprover-community/mathlib4/pull/29675), closed unmerged in
September 2026, proved `C(2p - 1, p - 1) ≡ 1 (mod p³)` alone. Elsewhere in Lean:
[atlas-lean](https://github.com/facebookresearch/atlas-lean) proves the harmonic form in
`ZMod (p ^ 2)` (its `wolstenholme`, the same statement as `sum_Ico_inv_eq_zero_zmod_sq`), defines
`fermatQuotient`, and has the `p³` congruence for `C(c pᵏ, d pᵏ)` as a private lemma; an
AlphaProof proof of the binomial form is linked from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures). No other proof
assistant has Wolstenholme's theorem. Not found elsewhere: Babbage's theorem, Ljunggren's congruence
modulo `p²` for all primes, `fermatQuotient_mul`, `fermatQuotient_add_mul` and Eisenstein's
congruence.
-/

@[expose] public section

open Finset Polynomial

/-! ### `C(p, k) / p` modulo `p` -/

section Choose

variable {p : ℕ}

/-- `C(p - 1, j) ≡ (-1) ^ j (mod p)` for `j < p`. -/
theorem choose_prime_sub_one_cast (hp : p.Prime) {j : ℕ} (hj : j < p) :
    ((p - 1).choose j : ZMod p) = (-1) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e := Nat.choose_succ_succ' (p - 1) j
    rw [Nat.sub_add_cancel hp.one_le] at e
    have h0 : ((p.choose (j + 1) : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (hp.dvd_choose_self j.succ_ne_zero hj)
    rw [e, Nat.cast_add, ih (by omega)] at h0
    rw [pow_succ]
    linear_combination h0

/-- `C(p, k) / p * k = C(p - 1, k - 1)` for `0 < k < p`. -/
theorem choose_prime_div_mul (hp : p.Prime) {k : ℕ} (hk : k ≠ 0) (hkp : k < p) :
    p.choose k / p * k = (p - 1).choose (k - 1) := by
  have e := Nat.add_one_mul_choose_eq (p - 1) (k - 1)
  rw [Nat.sub_add_cancel hp.one_le, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk)] at e
  obtain ⟨m, hm⟩ := hp.dvd_choose_self hk hkp
  rw [hm, Nat.mul_div_cancel_left _ hp.pos]
  rw [hm, mul_assoc] at e
  exact (Nat.eq_of_mul_eq_mul_left hp.pos e).symm

/-- `C(p, k) / p ≡ (-1) ^ (k - 1) / k (mod p)` for `0 < k < p`. -/
theorem choose_prime_div_cast (hp : p.Prime) {k : ℕ} (hk : k ≠ 0) (hkp : k < p) :
    ((p.choose k / p : ℕ) : ZMod p) = (-1) ^ (k - 1) * (k : ZMod p)⁻¹ := by
  have := Fact.mk hp
  have hk0 : (k : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) h) (by omega)
  rw [eq_mul_inv_iff_mul_eq₀ hk0, ← choose_prime_sub_one_cast hp (by omega : k - 1 < p),
    ← choose_prime_div_mul hp hk hkp]
  push_cast
  ring

end Choose

/-! ### Power sums of inverses modulo `p` -/

section PowerSum

variable (p : ℕ) [Fact p.Prime]

private theorem natCast_ne_zero_of_mem_Ico {k : ℕ} (hk : k ∈ Ico 1 p) : (k : ZMod p) ≠ 0 := by
  rw [mem_Ico] at hk
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact fun h => absurd (Nat.le_of_dvd hk.1 h) (by omega)

/-- A sum over `0 < k < p` is a sum over the units of `ZMod p`. -/
theorem sum_Ico_eq_sum_units {M : Type*} [AddCommMonoid M] (g : ZMod p → M) :
    ∑ k ∈ Ico 1 p, g k = ∑ u : (ZMod p)ˣ, g u := by
  refine Finset.sum_bij' (fun k hk => Units.mk0 (k : ZMod p) (natCast_ne_zero_of_mem_Ico p hk))
    (fun u _ => (u : ZMod p).val) (fun _ _ => mem_univ _) (fun u _ => ?_) (fun k hk => ?_)
    (fun u _ => ?_) (fun _ _ => rfl)
  · rw [mem_Ico]
    refine ⟨Nat.one_le_iff_ne_zero.mpr ?_, ZMod.val_lt _⟩
    rw [Ne, ZMod.val_eq_zero]
    exact u.ne_zero
  · exact ZMod.val_cast_of_lt (mem_Ico.mp hk).2
  · ext
    simp

/-- `∑_{0 < k < p} 1 / k ^ m` is `-1` in `ZMod p` if `p - 1 ∣ m` and `0` otherwise. -/
theorem sum_Ico_inv_pow (m : ℕ) :
    ∑ k ∈ Ico 1 p, ((k : ZMod p)⁻¹) ^ m = if p - 1 ∣ m then -1 else 0 := by
  rw [sum_Ico_eq_sum_units p (fun x => (x⁻¹) ^ m)]
  have e : ∑ u : (ZMod p)ˣ, ((u : ZMod p)⁻¹) ^ m = ∑ u : (ZMod p)ˣ, (u : ZMod p) ^ m :=
    Fintype.sum_equiv (Equiv.inv _) _ _ (fun u => by rw [Equiv.inv_apply, Units.val_inv_eq_inv_val])
  rw [e]
  have := FiniteField.sum_pow_units (K := ZMod p) m
  rwa [ZMod.card] at this

/-- `∑_{0 < k < p} 1 / k² ≡ 0 (mod p)` for every prime `p ≥ 5`. -/
theorem sum_Ico_inv_sq_eq_zero (h5 : 5 ≤ p) :
    ∑ k ∈ Ico 1 p, ((k : ZMod p)⁻¹) ^ 2 = 0 := by
  rw [sum_Ico_inv_pow, ite_eq_right_iff]
  intro h
  have := Nat.le_of_dvd two_pos h
  omega

end PowerSum

/-! ### Ljunggren's congruence -/

section Ljunggren

variable {p : ℕ}

/-- The polynomial `∑_{0 < k < p} (C(p, k) / p) * X ^ k`. -/
noncomputable def chooseDivPoly (p : ℕ) : ℤ[X] :=
  ∑ k ∈ Ico 1 p, C ((p.choose k / p : ℕ) : ℤ) * X ^ k

/-- The coefficients of `chooseDivPoly p` are `C(p, n) / p` for `0 < n < p`, and `0`
otherwise. -/
theorem coeff_chooseDivPoly (p n : ℕ) :
    (chooseDivPoly p).coeff n = if n ∈ Ico 1 p then ((p.choose n / p : ℕ) : ℤ) else 0 := by
  simp only [chooseDivPoly, finsetSum_coeff, coeff_C_mul_X_pow]
  exact Finset.sum_ite_eq _ _ _

/-- `(1 + X) ^ p = 1 + X ^ p + p * chooseDivPoly p`, writing `1 + X ^ p` as `expand p (1 + X)`. -/
theorem one_add_X_pow_prime (hp : p.Prime) :
    (1 + X : ℤ[X]) ^ p = expand ℤ p (1 + X) + C (p : ℤ) * chooseDivPoly p := by
  ext n
  rw [coeff_one_add_X_pow, coeff_add, coeff_C_mul, coeff_chooseDivPoly, map_add, map_one,
    expand_X, coeff_add, coeff_one, coeff_X_pow]
  rcases Nat.lt_trichotomy n p with h | rfl | h
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using hp.ne_zero.symm
    · have hmem : n ∈ Ico 1 p := mem_Ico.mpr ⟨hn, h⟩
      simp only [hmem, ite_true, hn.ne', h.ne, ite_false, zero_add]
      exact_mod_cast (Nat.mul_div_cancel' (hp.dvd_choose_self hn.ne' h)).symm
  · simp [hp.pos.ne']
  · have : n ∉ Ico 1 p := fun hm => by rw [mem_Ico] at hm; omega
    simp [Nat.choose_eq_zero_of_lt h, this, h.ne', (hp.pos.trans h).ne']

/-- `(x + y) ^ (n + 2)` up to terms divisible by `y ^ 3`. -/
private theorem add_pow_add_two {R : Type*} [CommRing R] (x y : R) (n : ℕ) :
    ∃ r, (x + y) ^ (n + 2) = x ^ (n + 2) + y * (((n + 2 : ℕ) : R) * x ^ (n + 1)) +
      y ^ 2 * (((n + 2).choose 2 : ℕ) * x ^ n) + y ^ 3 * r := by
  induction n with
  | zero => exact ⟨0, by simp; ring⟩
  | succ n ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨((n + 2).choose 2 : ℕ) * x ^ n + x * r + y * r, ?_⟩
    have hc : (n + 1 + 2).choose 2 = (n + 2) + (n + 2).choose 2 :=
      (Nat.choose_succ_succ' (n + 2) 1).trans (by rw [Nat.choose_one_right])
    rw [pow_succ, hr, hc]
    push_cast
    ring

/-- If `d` divides the coefficients of `H` at multiples of `p`, then it divides those of
`expand p F * H`, since `expand p F` only has terms `X ^ (i * p)`. -/
private theorem dvd_coeff_expand_mul {d : ℤ} {H : ℤ[X]}
    (hH : ∀ j, d ∣ H.coeff (j * p)) (F : ℤ[X]) (j : ℕ) :
    d ∣ (expand ℤ p F * H).coeff (j * p) := by
  induction F using Polynomial.induction_on' with
  | add f g hf hg => rw [map_add, add_mul, coeff_add]; exact dvd_add hf hg
  | monomial n c =>
    rw [expand_monomial, ← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
    split_ifs with h
    · rw [← Nat.sub_mul]
      exact dvd_mul_of_dvd_right (hH _) _
    · simp

private theorem coeff_chooseDivPoly_mul_prime (j : ℕ) : (chooseDivPoly p).coeff (j * p) = 0 := by
  rw [coeff_chooseDivPoly, ite_eq_right_iff]
  intro hm
  rw [mem_Ico] at hm
  rcases j with _ | j
  · simp at hm
  · have : p ≤ (j + 1) * p := Nat.le_mul_of_pos_left p (by omega)
    omega

/-- The coefficients of `G²` at multiples of `p` vanish modulo `p` when `p ≥ 5`: the only
nonzero one is `∑_{0 < k < p} c_k * c_(p - k) ≡ ∑_{0 < k < p} 1 / k²`. -/
private theorem coeff_chooseDivPoly_sq_mul_prime (hp : p.Prime) (h5 : 5 ≤ p) (j : ℕ) :
    (p : ℤ) ∣ (chooseDivPoly p ^ 2).coeff (j * p) := by
  have := Fact.mk hp
  have hodd : Odd (p - 2) := by
    rcases hp.eq_two_or_odd' with h | h
    · omega
    · exact Nat.Odd.sub_even (by omega) h even_two
  have hj3 : j = 0 ∧ j * p = 0 ∨ j = 1 ∧ j * p = p ∨ 2 * p ≤ j * p := by
    rcases j with _ | _ | j
    · simp
    · simp
    · right; right; exact Nat.mul_le_mul_right _ (by omega)
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, pow_two, coeff_mul,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk, Int.cast_sum]
  have hterm : ∀ i ∈ range (j * p + 1),
      (((chooseDivPoly p).coeff i * (chooseDivPoly p).coeff (j * p - i) : ℤ) : ZMod p) =
        if j = 1 ∧ i ∈ Ico 1 p then ((i : ZMod p)⁻¹) ^ 2 else 0 := by
    intro i hi
    rw [mem_range] at hi
    rw [coeff_chooseDivPoly, coeff_chooseDivPoly]
    by_cases h1 : i ∈ Ico 1 p <;> by_cases h2 : j * p - i ∈ Ico 1 p <;>
      simp only [h1, h2, ite_true, ite_false, mul_zero, zero_mul, Int.cast_zero, and_true,
        and_false] <;> rw [mem_Ico] at h1 h2
    · have hj : j = 1 := by omega
      subst hj
      rw [one_mul] at h2 ⊢
      rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast,
        choose_prime_div_cast hp (by omega) h1.2, choose_prime_div_cast hp (by omega) h2.2,
        Nat.cast_sub h1.2.le, ZMod.natCast_self, zero_sub, inv_neg]
      have : (-1 : ZMod p) ^ (i - 1) * (-1) ^ (p - i - 1) = -1 := by
        rw [← pow_add, show i - 1 + (p - i - 1) = p - 2 by omega, hodd.neg_one_pow]
      simp only [ite_true]
      linear_combination (-(i : ZMod p)⁻¹ ^ 2) * this
    · split_ifs with hj
      · subst hj; omega
      · rfl
  rw [sum_congr rfl hterm]
  by_cases hj : j = 1
  · subst hj
    simp only [true_and]
    rw [sum_ite_mem, inter_eq_right.mpr, sum_Ico_inv_sq_eq_zero p h5]
    intro i hi
    rw [mem_Ico] at hi
    rw [mem_range]
    omega
  · simp [hj]

/-- `C((a + 2) p, b p) = C(a + 2, b) + p² x + p³ s`, where `p ∣ x` if `p ≥ 5`. -/
private theorem choose_mul_add_two (hp : p.Prime) (a b : ℕ) : ∃ x s : ℤ,
    (((a + 2) * p).choose (b * p) : ℤ) = (a + 2).choose b + p ^ 2 * x + p ^ 3 * s ∧
      (5 ≤ p → (p : ℤ) ∣ x) := by
  obtain ⟨r, hr⟩ := add_pow_add_two (expand ℤ p (1 + X)) (C (p : ℤ) * chooseDivPoly p) a
  set G := chooseDivPoly p
  refine ⟨(expand ℤ p ((((a + 2).choose 2 : ℕ) : ℤ[X]) * (1 + X) ^ a) * G ^ 2).coeff (b * p),
    (G ^ 3 * r).coeff (b * p), ?_, fun h5 => dvd_coeff_expand_mul
      (coeff_chooseDivPoly_sq_mul_prime hp h5) _ _⟩
  rw [← coeff_one_add_X_pow ℤ, mul_comm, pow_mul, one_add_X_pow_prime hp, hr]
  have e1 : expand ℤ p (1 + X) ^ (a + 2) = expand ℤ p ((1 + X) ^ (a + 2)) := (map_pow _ _ _).symm
  have e2 : (((a + 2 : ℕ) : ℤ[X]) * expand ℤ p (1 + X) ^ (a + 1)) =
      expand ℤ p (((a + 2 : ℕ) : ℤ[X]) * (1 + X) ^ (a + 1)) := by
    rw [map_mul, map_pow, map_natCast]
  have e3 : ((((a + 2).choose 2 : ℕ) : ℤ[X]) * expand ℤ p (1 + X) ^ a) =
      expand ℤ p ((((a + 2).choose 2 : ℕ) : ℤ[X]) * (1 + X) ^ a) := by
    rw [map_mul, map_pow, map_natCast]
  rw [e1, e2, e3]
  simp only [coeff_add, mul_pow, ← C_pow, mul_assoc, coeff_C_mul, coeff_expand_mul hp.pos,
    coeff_one_add_X_pow]
  rw [mul_comm G, (zero_dvd_iff.mp (dvd_coeff_expand_mul
    (fun j => (zero_dvd_iff.mpr (coeff_chooseDivPoly_mul_prime j))) _ b)), mul_comm (G ^ 2)]
  ring

private theorem choose_mul_of_le_one (hp : p.Prime) {a : ℕ} (ha : a ≤ 1) (b : ℕ) :
    (a * p).choose (b * p) = a.choose b := by
  interval_cases a
  · rcases b with _ | b
    · simp
    · simp [Nat.choose_eq_zero_of_lt, Nat.mul_pos (Nat.succ_pos b) hp.pos]
  · rcases b with _ | _ | b
    · simp
    · simp
    · rw [Nat.choose_eq_zero_of_lt, Nat.choose_eq_zero_of_lt] <;>
        nlinarith [hp.pos]

/-- **Ljunggren's congruence modulo `p²`**: `C(ap, bp) ≡ C(a, b) (mod p²)` for every prime `p`. -/
theorem choose_mul_modEq_choose_sq (hp : p.Prime) (a b : ℕ) :
    (a * p).choose (b * p) ≡ a.choose b [MOD p ^ 2] := by
  rcases le_or_gt a 1 with ha | ha
  · rw [choose_mul_of_le_one hp ha]
  obtain ⟨a, rfl⟩ : ∃ c, a = c + 2 := ⟨a - 2, by omega⟩
  obtain ⟨x, s, h, -⟩ := choose_mul_add_two hp a b
  rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd]
  push_cast
  rw [h]
  exact ⟨-(x + p * s), by ring⟩

/-- **Ljunggren's congruence**: `C(ap, bp) ≡ C(a, b) (mod p³)` for every prime `p ≥ 5`. -/
theorem choose_mul_modEq_choose_cube (hp : p.Prime) (h5 : 5 ≤ p) (a b : ℕ) :
    (a * p).choose (b * p) ≡ a.choose b [MOD p ^ 3] := by
  rcases le_or_gt a 1 with ha | ha
  · rw [choose_mul_of_le_one hp ha]
  obtain ⟨a, rfl⟩ : ∃ c, a = c + 2 := ⟨a - 2, by omega⟩
  obtain ⟨x, s, h, hx⟩ := choose_mul_add_two hp a b
  obtain ⟨y, rfl⟩ := hx h5
  rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd]
  push_cast
  rw [h]
  exact ⟨-(y + s), by ring⟩

end Ljunggren

/-! ### Wolstenholme's and Babbage's theorems -/

section Wolstenholme

variable {p : ℕ}

private theorem choose_two_mul (hp : 0 < p) :
    (2 * p).choose p = 2 * (2 * p - 1).choose (p - 1) := by
  have e := Nat.add_one_mul_choose_eq (2 * p - 1) (p - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * p), Nat.sub_add_cancel hp] at e
  refine Nat.eq_of_mul_eq_mul_right hp ?_
  rw [← e]
  ring

private theorem choose_two_mul_sub_one_modEq (hp : p.Prime) (hp2 : p ≠ 2) {k : ℕ}
    (h : (2 * p).choose (1 * p) ≡ (2 : ℕ).choose 1 [MOD p ^ k]) :
    (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ k] := by
  rw [one_mul, choose_two_mul hp.pos, Nat.choose_one_right] at h
  exact Nat.ModEq.cancel_left_of_coprime
    (Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)) h

/-- **Babbage's theorem**: `C(2p - 1, p - 1) ≡ 1 (mod p²)` for every odd prime `p`. -/
theorem choose_two_mul_sub_one_modEq_one_sq (hp : p.Prime) (hp2 : p ≠ 2) :
    (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 2] :=
  choose_two_mul_sub_one_modEq hp hp2 (choose_mul_modEq_choose_sq hp 2 1)

/-- **Wolstenholme's theorem**: `C(2p - 1, p - 1) ≡ 1 (mod p³)` for every prime `p ≥ 5`. -/
theorem choose_two_mul_sub_one_modEq_one_cube (hp : p.Prime) (h5 : 5 ≤ p) :
    (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3] :=
  choose_two_mul_sub_one_modEq hp (by omega) (choose_mul_modEq_choose_cube hp h5 2 1)

end Wolstenholme

/-! ### Harmonic numbers -/

section Harmonic

variable {p : ℕ}

private theorem mul_eq_zero_of_castHom_eq_zero (hp : p.Prime) {x : ZMod (p ^ 2)}
    (hx : ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) x = 0) :
    (p : ZMod (p ^ 2)) * x = 0 := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x, map_natCast, ZMod.natCast_eq_zero_iff] at hx
  obtain ⟨m, hm⟩ := hx
  rw [← ZMod.natCast_zmod_val x, hm,
    show (p : ZMod (p ^ 2)) * ((p * m : ℕ) : ZMod (p ^ 2)) = ((p ^ 2 : ℕ) : ZMod (p ^ 2)) * m by
      push_cast; ring, ZMod.natCast_self, zero_mul]

/-- **Wolstenholme's theorem**, harmonic form: `∑_{0 < k < p} 1 / k ≡ 0 (mod p²)` for every
prime `p ≥ 5`. -/
theorem sum_Ico_inv_eq_zero_zmod_sq (hp : p.Prime) (h5 : 5 ≤ p) :
    ∑ k ∈ Ico 1 p, (k : ZMod (p ^ 2))⁻¹ = 0 := by
  have := Fact.mk hp
  set u : ℕ → ZMod (p ^ 2) := fun k => (k : ZMod (p ^ 2))⁻¹ with hu_def
  have hu : ∀ k ∈ Ico 1 p, (k : ZMod (p ^ 2)) * u k = 1 := fun k hk =>
    ZMod.coe_mul_inv_eq_one k (Nat.Coprime.pow_right 2 (Nat.coprime_comm.mp
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr
        (Nat.not_dvd_of_pos_of_lt (mem_Ico.mp hk).1 (mem_Ico.mp hk).2))))
  have hmem : ∀ k ∈ Ico 1 p, p - k ∈ Ico 1 p := by
    intro k hk
    rw [mem_Ico] at *
    omega
  have hpp : (p : ZMod (p ^ 2)) * p = 0 := by
    rw [← Nat.cast_mul, ← sq, ZMod.natCast_self]
  -- `1 / k + 1 / (p - k) = p / (k (p - k))`, and so `p / (p - k) = -p / k`
  have pair : ∀ k ∈ Ico 1 p, u k + u (p - k) = p * (u k * u (p - k)) := by
    intro k hk
    have h1 := hu k hk
    have h2 := hu (p - k) (hmem k hk)
    rw [Nat.cast_sub (mem_Ico.mp hk).2.le] at h2
    linear_combination (-u (p - k)) * h1 + (-u k) * h2
  have neg : ∀ k ∈ Ico 1 p, p * (u k * u (p - k)) = -(p * u k ^ 2) := by
    intro k hk
    linear_combination (p * u k : ZMod (p ^ 2)) * pair k hk + (u k ^ 2 * u (p - k)) * hpp
  have hrefl : ∑ k ∈ Ico 1 p, u (p - k) = ∑ k ∈ Ico 1 p, u k :=
    Finset.sum_nbij' (fun k => p - k) (fun k => p - k) hmem hmem
      (fun k hk => by rw [mem_Ico] at hk; omega) (fun k hk => by rw [mem_Ico] at hk; omega)
      (fun _ _ => rfl)
  -- `∑ 1 / k² ≡ 0 (mod p)`, so `p * ∑ 1 / k² ≡ 0 (mod p²)`
  have hT : (p : ZMod (p ^ 2)) * ∑ k ∈ Ico 1 p, u k ^ 2 = 0 := by
    apply mul_eq_zero_of_castHom_eq_zero hp
    rw [map_sum, ← sum_Ico_inv_sq_eq_zero p h5]
    refine sum_congr rfl fun k hk => ?_
    rw [map_pow]
    congr 1
    have h := congrArg (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)) (hu k hk)
    rw [map_mul, map_natCast, map_one] at h
    exact eq_inv_of_mul_eq_one_right h
  have h2S : 2 * ∑ k ∈ Ico 1 p, u k = 0 := by
    calc 2 * ∑ k ∈ Ico 1 p, u k = ∑ k ∈ Ico 1 p, (u k + u (p - k)) := by
          rw [sum_add_distrib, hrefl]; ring
      _ = ∑ k ∈ Ico 1 p, -(p * u k ^ 2) :=
          sum_congr rfl fun k hk => (pair k hk).trans (neg k hk)
      _ = 0 := by rw [sum_neg_distrib, ← mul_sum, hT, neg_zero]
  have h2 : ((2 : ℕ) : ZMod (p ^ 2)) * ((2 : ℕ) : ZMod (p ^ 2))⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one 2 (Nat.Coprime.pow_right 2
      ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega)))
  rw [Nat.cast_ofNat] at h2
  linear_combination (2 : ZMod (p ^ 2))⁻¹ * h2S - (∑ k ∈ Ico 1 p, u k) * h2

/-- **Wolstenholme's theorem**, harmonic form: for every prime `p ≥ 5`, `p²` divides the
numerator of `H_(p - 1) = 1 + 1 / 2 + ⋯ + 1 / (p - 1)`. -/
theorem sq_dvd_num_harmonic (hp : p.Prime) (h5 : 5 ≤ p) :
    (p : ℤ) ^ 2 ∣ (harmonic (p - 1)).num := by
  have := Fact.mk hp
  set F := (p - 1).factorial
  have hdvd : ∀ k ∈ Ico 1 p, k ∣ F := fun k hk =>
    Nat.dvd_factorial (mem_Ico.mp hk).1 (by have := (mem_Ico.mp hk).2; omega)
  set N : ℕ := ∑ k ∈ Ico 1 p, F / k
  have hH : harmonic (p - 1) * F = N := by
    rw [harmonic, sum_mul, Nat.cast_sum, sum_Ico_eq_sum_range]
    refine sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    rw [Nat.cast_div (hdvd (1 + i) (mem_Ico.mpr ⟨by omega, by omega⟩)) (by positivity)]
    push_cast
    ring
  have hN : (p : ℤ) ^ 2 ∣ N := by
    have : ((N : ℕ) : ZMod (p ^ 2)) = 0 := by
      rw [Nat.cast_sum, ← mul_zero (F : ZMod (p ^ 2)), ← sum_Ico_inv_eq_zero_zmod_sq hp h5, mul_sum]
      refine sum_congr rfl fun k hk => ?_
      have hk1 : (k : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹ = 1 :=
        ZMod.coe_mul_inv_eq_one k (Nat.Coprime.pow_right 2 (Nat.coprime_comm.mp
          ((Nat.Prime.coprime_iff_not_dvd hp).mpr
            (Nat.not_dvd_of_pos_of_lt (mem_Ico.mp hk).1 (mem_Ico.mp hk).2))))
      have hFk : ((F / k : ℕ) : ZMod (p ^ 2)) * k = F := by
        rw [← Nat.cast_mul, Nat.div_mul_cancel (hdvd k hk)]
      linear_combination (k : ZMod (p ^ 2))⁻¹ * hFk - ((F / k : ℕ) : ZMod (p ^ 2)) * hk1
    rw [ZMod.natCast_eq_zero_iff] at this
    exact_mod_cast this
  have hnum : (harmonic (p - 1)).num * F = N * (harmonic (p - 1)).den := by
    have := congrArg (· * ((harmonic (p - 1)).den : ℚ)) hH
    rw [mul_right_comm, Rat.mul_den_eq_num] at this
    exact_mod_cast this
  have hcop : IsCoprime ((p : ℤ) ^ 2) (F : ℤ) := by
    rw [← Nat.cast_pow, Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr
      (by rw [hp.dvd_factorial]; omega))
  exact hcop.dvd_of_dvd_mul_right (hnum ▸ dvd_mul_of_dvd_left hN _)

end Harmonic

/-! ### Fermat quotients -/

section FermatQuotient

/-- The Fermat quotient `q_p(a) = (a ^ (p - 1) - 1) / p`, using integer division. For a prime `p`
not dividing `a` the division is exact (`mul_fermatQuotient`). -/
def fermatQuotient (p : ℕ) (a : ℤ) : ℤ :=
  (a ^ (p - 1) - 1) / p

variable {p : ℕ} {a b : ℤ}

/-- `p * q_p(a) = a ^ (p - 1) - 1` when `p ∤ a`, by Fermat's little theorem. -/
theorem mul_fermatQuotient (hp : p.Prime) (ha : ¬(p : ℤ) ∣ a) :
    p * fermatQuotient p a = a ^ (p - 1) - 1 := by
  have := Fact.mk hp
  refine Int.mul_ediv_cancel' ?_
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.pow_card_sub_one_eq_one, sub_self]
  rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- `q_p(a b) = q_p(a) + q_p(b) + p q_p(a) q_p(b)` when `p ∤ a` and `p ∤ b`. -/
theorem fermatQuotient_mul (hp : p.Prime) (ha : ¬(p : ℤ) ∣ a) (hb : ¬(p : ℤ) ∣ b) :
    fermatQuotient p (a * b) =
      fermatQuotient p a + fermatQuotient p b + p * fermatQuotient p a * fermatQuotient p b := by
  have hab : ¬(p : ℤ) ∣ a * b := fun h =>
    (Int.Prime.dvd_mul' hp h).elim ha hb
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  apply mul_left_cancel₀ hp0
  have h1 := mul_fermatQuotient hp ha
  have h2 := mul_fermatQuotient hp hb
  rw [mul_fermatQuotient hp hab, mul_pow]
  linear_combination (-(p * fermatQuotient p b + 1)) * h1 + (-(a ^ (p - 1))) * h2

/-- `q_p(a b) ≡ q_p(a) + q_p(b) (mod p)` when `p ∤ a` and `p ∤ b`. -/
theorem fermatQuotient_mul_modEq (hp : p.Prime) (ha : ¬(p : ℤ) ∣ a) (hb : ¬(p : ℤ) ∣ b) :
    fermatQuotient p (a * b) ≡ fermatQuotient p a + fermatQuotient p b [ZMOD p] := by
  rw [fermatQuotient_mul hp ha hb, Int.modEq_iff_dvd]
  exact ⟨-(fermatQuotient p a * fermatQuotient p b), by ring⟩

/-- `q_p(a + p k) ≡ q_p(a) - k / a (mod p)` when `p ∤ a`. -/
theorem fermatQuotient_add_mul (hp : p.Prime) (ha : ¬(p : ℤ) ∣ a) (k : ℤ) :
    (fermatQuotient p (a + p * k) : ZMod p) = fermatQuotient p a - k * (a : ZMod p)⁻¹ := by
  have := Fact.mk hp
  have ha' : ¬(p : ℤ) ∣ a + p * k := fun h => ha ((dvd_add_left (dvd_mul_right _ _)).mp h)
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨t, ht⟩ := sq_dvd_add_pow_sub_sub (p * k) a (p - 1)
  have hq : fermatQuotient p (a + p * k) =
      fermatQuotient p a + a ^ (p - 1 - 1) * k * (p - 1 : ℕ) + p * k ^ 2 * t := by
    apply mul_left_cancel₀ hp0
    rw [mul_add, mul_add, mul_fermatQuotient hp ha', mul_fermatQuotient hp ha]
    linear_combination ht
  have ha0 : (a : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hinv : (a : ZMod p) ^ (p - 1 - 1) = (a : ZMod p)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, Nat.sub_add_cancel (by have := hp.two_le; omega),
      ZMod.pow_card_sub_one_eq_one ha0]
  rw [hq]
  push_cast
  rw [hinv, Nat.cast_sub hp.one_le, ZMod.natCast_self]
  ring

/-- `p ∣ q_p(a)` exactly when `a ^ (p - 1) ≡ 1 (mod p²)`; for `a = 2` these are the Wieferich
primes. -/
theorem dvd_fermatQuotient_iff (hp : p.Prime) (ha : ¬(p : ℤ) ∣ a) :
    (p : ℤ) ∣ fermatQuotient p a ↔ a ^ (p - 1) ≡ 1 [ZMOD p ^ 2] := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [Int.modEq_comm, Int.modEq_iff_dvd, ← mul_fermatQuotient hp ha, pow_two,
    mul_dvd_mul_iff_left hp0]

/-- **Eisenstein's formula**, exact form: `2 q_p(2) = ∑_{0 < k < p} C(p, k) / p` for an odd
prime `p`. -/
theorem two_mul_fermatQuotient_two (hp : p.Prime) (hp2 : p ≠ 2) :
    2 * fermatQuotient p 2 = ∑ k ∈ Ico 1 p, ((p.choose k / p : ℕ) : ℤ) := by
  have h2 : ¬(p : ℤ) ∣ 2 := by
    intro h
    have := Int.le_of_dvd two_pos h
    have := hp.two_le
    omega
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have e := congrArg (eval 1) (one_add_X_pow_prime hp)
  simp only [eval_pow, eval_add, eval_one, eval_X, expand_eval, one_pow, eval_mul, eval_C,
    chooseDivPoly, eval_finsetSum, mul_one] at e
  apply mul_left_cancel₀ hp0
  rw [mul_left_comm, mul_fermatQuotient hp h2]
  have hp1 : (2 : ℤ) ^ p = 2 * 2 ^ (p - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hp.one_le]
  linear_combination e - hp1

/-- **Eisenstein's congruence**: `2 q_p(2) ≡ ∑_{0 < k < p} (-1) ^ (k - 1) / k (mod p)` for an
odd prime `p`. -/
theorem two_mul_fermatQuotient_two_cast (hp : p.Prime) (hp2 : p ≠ 2) :
    2 * (fermatQuotient p 2 : ZMod p) = ∑ k ∈ Ico 1 p, (-1) ^ (k - 1) * (k : ZMod p)⁻¹ := by
  have := congrArg (Int.cast : ℤ → ZMod p) (two_mul_fermatQuotient_two hp hp2)
  rw [Int.cast_mul, Int.cast_ofNat, Int.cast_sum] at this
  rw [this]
  refine sum_congr rfl fun k hk => ?_
  rw [Int.cast_natCast, choose_prime_div_cast hp (by have := (mem_Ico.mp hk).1; omega)
    (mem_Ico.mp hk).2]

private theorem sum_range_one_add_neg_one_pow {R : Type*} [CommRing R] (g : ℕ → R) (n : ℕ) :
    ∑ k ∈ range (2 * n + 1), (1 + (-1 : R) ^ k) * g k = ∑ j ∈ range (n + 1), 2 * g (2 * j) := by
  induction n with
  | zero => simp [one_add_one_eq_two]
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ (n := n + 1), show 2 * n + 1 + 1 = 2 * (n + 1) by ring]
    simp [pow_succ, pow_mul, one_add_one_eq_two]

/-- **Eisenstein's congruence**, half-harmonic form:
`2 q_p(2) ≡ -(1 + 1 / 2 + ⋯ + 1 / ((p - 1) / 2)) (mod p)` for an odd prime `p`. -/
theorem two_mul_fermatQuotient_two_eq_neg_sum (hp : p.Prime) (hp2 : p ≠ 2) :
    2 * (fermatQuotient p 2 : ZMod p) = -∑ j ∈ Icc 1 (p / 2), (j : ZMod p)⁻¹ := by
  have := Fact.mk hp
  have hodd : p = 2 * (p / 2) + 1 := by
    rcases hp.eq_two_or_odd' with h | h
    · exact absurd h hp2
    · have := Nat.odd_iff.mp h; omega
  set g : ℕ → ZMod p := fun k => (k : ZMod p)⁻¹
  -- extend sums over `0 < k < p` to `0 ≤ k < p`, using `1 / 0 = 0`
  have hext : ∀ f : ℕ → ZMod p, ∑ k ∈ Ico 1 p, f k * g k = ∑ k ∈ range p, f k * g k := by
    intro f
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hp.pos]
    simp [g]
  have hsum : ∑ k ∈ range p, g k = 0 := by
    have h := sum_Ico_inv_pow p 1
    rw [ite_eq_right_iff.mpr (fun h => absurd (Nat.le_of_dvd one_pos h) (by
      have := hp.two_le; omega))] at h
    simpa [g] using (hext (fun _ => 1)).symm.trans (by simpa using h)
  have h2 : (2 : ZMod p) ≠ 0 := by
    have : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    simpa using this
  have hsign : ∀ k ∈ range p,
      (-1 : ZMod p) ^ (k - 1) * g k = -((1 + (-1) ^ k) * g k) + g k := by
    intro k _
    rcases k with _ | k
    · simp [g]
    · rw [Nat.add_sub_cancel, pow_succ]
      ring
  have hr : range p = range (2 * (p / 2) + 1) := congrArg range hodd
  rw [two_mul_fermatQuotient_two_cast hp hp2, hext, sum_congr rfl hsign, sum_add_distrib,
    sum_neg_distrib, hsum, add_zero, hr, sum_range_one_add_neg_one_pow, range_eq_Ico,
    sum_eq_sum_Ico_succ_bot (Nat.succ_pos _), ← Ico_add_one_right_eq_Icc]
  simp only [g, mul_zero, Nat.cast_zero, inv_zero, zero_add]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [Nat.cast_mul, Nat.cast_ofNat, mul_inv, ← mul_assoc, mul_inv_cancel₀ h2, one_mul]

end FermatQuotient
