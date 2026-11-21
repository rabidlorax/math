module

public import Mathlib

/-!
# Dedekind sums

The sawtooth function is `((x)) = x - (⌊x⌋ + ⌈x⌉) / 2`: it is `fract x - 1/2` when `x` is not
an integer and `0` when it is. For `h : ℤ` and `k : ℕ` the Dedekind sum is

`s(h, k) = ∑_{r < k} ((r / k)) * ((h r / k))`.

Dedekind sums appear in the transformation law of the Dedekind eta function, in Rademacher's
formula for the partition function, in lattice point counts and in the signature defects of
lens spaces. The central fact is the **reciprocity law**: for coprime `h, k > 0`,

`s(h, k) + s(k, h) = (h² + k² + 1) / (12 h k) - 1/4`.

Together with periodicity in `h` it evaluates `s(h, k)` along the Euclidean algorithm. Mathlib
has Hermite's identity for the floor function but neither the sawtooth function nor these sums.

## Main definitions

* `sawtooth x` : the sawtooth function `((x))`, in any linearly ordered floor field.
* `sawtoothZMod k a` : `((a / k))` for a residue `a` modulo `k`.
* `dedekindSum h k` : the Dedekind sum `s(h, k)`, a rational number.

## Main results

* `sawtooth_add_intCast`, `sawtooth_neg`, `sawtooth_eq_ite`, `abs_sawtooth_le` : `((x))` is
  `1`-periodic, odd, `fract x - 1/2` off the integers and bounded by `1/2`.
* `sum_sawtooth_add_div` : the distribution relation `∑_{i < n} ((x + i / n)) = ((n x))`.
* `dedekindSum_congr`, `dedekindSum_neg` : `s(h, k)` depends on `h` only modulo `k`, and is odd
  in `h`.
* `dedekindSum_of_mul_modEq_one` : `s(h', k) = s(h, k)` when `h h' ≡ 1 (mod k)`.
* `dedekindSum_eq_zero_of_sq_modEq_neg_one` : `s(h, k) = 0` when `h² ≡ -1 (mod k)`.
* `dedekindSum_mul_mul` : `s(d h, d k) = s(h, k)` for `d > 0`.
* `dedekindSum_eq_sum_mod` : for coprime `h, k` with `k > 0`,
  `s(h, k) = (∑_{r < k} r (h r mod k)) / k² - (k - 1) / 4`.
* `dedekindSum_one_left`, `dedekindSum_two_left` : `s(1, k) = (k - 1)(k - 2) / (12 k)`, and
  `s(2, k) = (k - 1)(k - 5) / (24 k)` for odd `k`.
* `abs_dedekindSum_le` : `|s(h, k)| ≤ s(1, k)` for `h` coprime to `k`.
* `dedekindSum_reciprocity` : the **reciprocity law**.
* `exists_six_mul_dedekindSum_eq`, `exists_twelve_mul_dedekindSum_modEq` : for coprime
  `h, k` with `k > 0`, `6 k s(h, k)` is an integer; if also `h > 0`, then
  `12 h k s(h, k)` is an integer `≡ h² + 1 (mod k)`.
-/

@[expose] public section

open Finset

/-! ### Finite sums used below -/

private theorem sum_range_natCast {K : Type*} [Field K] [CharZero K] (n : ℕ) :
    ∑ i ∈ range n, (i : K) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

private theorem sum_range_natCast_sq (n : ℕ) :
    ∑ i ∈ range n, (i : ℚ) ^ 2 = n * (n - 1) * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

/-- A sum over `r < k` is a sum over the residues modulo `k`. -/
private theorem sum_range_eq_sum_zmod {M : Type*} [AddCommMonoid M] (k : ℕ) [NeZero k]
    (f : ℕ → M) : ∑ r ∈ range k, f r = ∑ a : ZMod k, f a.val := by
  cases k with
  | zero => exact absurd rfl (NeZero.ne 0)
  | succ m => exact (Fin.sum_univ_eq_sum_range f (m + 1)).symm

/-- Multiplication by a unit permutes the residues modulo `k`. -/
private theorem sum_zmod_mul {M : Type*} [AddCommMonoid M] {k : ℕ} [NeZero k] {u v : ZMod k}
    (huv : u * v = 1) (f : ZMod k → M) : ∑ a, f (u * a) = ∑ a, f a :=
  Fintype.sum_equiv (Units.mulLeft ⟨u, v, huv, by rw [mul_comm, huv]⟩) _ _ fun _ => rfl

/-- For `h` coprime to `k`, `r ↦ h r mod k` permutes `{0, …, k - 1}`. -/
private theorem sum_mul_mod {M : Type*} [AddCommMonoid M] {h k : ℕ} (hc : h.Coprime k)
    (f : ℕ → M) : ∑ r ∈ range k, f (h * r % k) = ∑ r ∈ range k, f r := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have : NeZero k := ⟨hk⟩
  rw [sum_range_eq_sum_zmod, sum_range_eq_sum_zmod]
  have e : ∀ a : ZMod k, h * a.val % k = ((h : ZMod k) * a).val := fun a => by
    rw [← ZMod.val_natCast, Nat.cast_mul, ZMod.natCast_zmod_val]
  simp_rw [e]
  exact Fintype.sum_equiv (Units.mulLeft (ZMod.unitOfCoprime h hc)) _ _ fun a => by simp

/-- Splitting `r < k d` as `r = j + k i` with `j < k`, `i < d`. -/
private theorem sum_range_mul {M : Type*} [AddCommMonoid M] (k d : ℕ) (f : ℕ → M) :
    ∑ r ∈ range (k * d), f r = ∑ j ∈ range k, ∑ i ∈ range d, f (j + k * i) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.mul_succ, sum_range_add, ih]
    simp only [sum_range_succ, sum_add_distrib]
    exact congrArg _ (sum_congr rfl fun j _ => by rw [add_comm])

/-! ### The sawtooth function -/

section Sawtooth

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/-- The sawtooth function `((x)) = x - (⌊x⌋ + ⌈x⌉) / 2`. -/
def sawtooth (x : K) : K := x - ((⌊x⌋ : K) + ⌈x⌉) / 2

theorem sawtooth_add_intCast (x : K) (m : ℤ) : sawtooth (x + m) = sawtooth x := by
  simp only [sawtooth, Int.floor_add_intCast, Int.ceil_add_intCast]; push_cast; ring

omit [IsStrictOrderedRing K] in
@[simp] theorem sawtooth_intCast (m : ℤ) : sawtooth (m : K) = 0 := by
  simp only [sawtooth, Int.floor_intCast, Int.ceil_intCast]; ring

omit [IsStrictOrderedRing K] in
@[simp] theorem sawtooth_zero : sawtooth (0 : K) = 0 := by
  simpa using sawtooth_intCast (K := K) 0

@[simp] theorem sawtooth_neg (x : K) : sawtooth (-x) = -sawtooth x := by
  simp only [sawtooth, Int.floor_neg, Int.ceil_neg]; push_cast; ring

omit [IsStrictOrderedRing K] in
/-- `((x))` is `0` at the integers and `fract x - 1/2` elsewhere. -/
theorem sawtooth_eq_ite (x : K) :
    sawtooth x = if Int.fract x = 0 then 0 else Int.fract x - 1 / 2 := by
  split_ifs with h
  · obtain ⟨m, rfl⟩ := Int.fract_eq_zero_iff.mp h
    exact sawtooth_intCast m
  · rw [sawtooth, (Int.ceil_eq_floor_add_one_iff_notMem x).mpr
      fun hx => h (Int.fract_eq_zero_iff.mpr hx), ← Int.self_sub_floor]
    push_cast; ring

theorem abs_sawtooth_le (x : K) : |sawtooth x| ≤ 1 / 2 := by
  rw [sawtooth_eq_ite]
  split_ifs
  · norm_num
  · exact abs_le.mpr ⟨by linarith [Int.fract_nonneg x], by linarith [Int.fract_lt_one x]⟩

/-- For `n ≠ 0`, `((m / n))` is `0` if `n ∣ m` and `(m mod n) / n - 1/2` otherwise. -/
theorem sawtooth_natCast_div {m n : ℕ} (hn : n ≠ 0) :
    sawtooth ((m : K) / n) = if n ∣ m then 0 else ((m % n : ℕ) : K) / n - 1 / 2 := by
  have : ((m % n : ℕ) : K) / n = 0 ↔ n ∣ m := by
    simp [div_eq_zero_iff, hn, Nat.dvd_iff_mod_eq_zero]
  simp only [sawtooth_eq_ite, Int.fract_div_natCast_eq_div_natCast_mod, this]

private theorem sum_ceil_add_div (x : K) {n : ℕ} (hn : n ≠ 0) :
    ∑ i ∈ range n, ⌈x + i / n⌉ = ⌈n * x⌉ + n - 1 := by
  have hK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h := Int.sum_floor_add_div (-x - (n - 1) / n) n
  rw [← sum_range_reflect] at h
  have e : ∀ j ∈ range n, ⌊-x - (n - 1) / n + ((n - 1 - j : ℕ) : K) / n⌋ = -⌈x + j / n⌉ := by
    intro j hj
    have hj : j + 1 ≤ n := mem_range.mp hj
    rw [Nat.sub_sub, Nat.cast_sub (by omega), ← Int.floor_neg]
    congr 1
    push_cast
    field_simp
    ring
  rw [sum_congr rfl e, sum_neg_distrib,
    show (n : K) * (-x - (n - 1) / n) = -(n * x) + ((1 - n : ℤ) : K) by
      push_cast; field_simp; ring,
    Int.floor_add_intCast, Int.floor_neg] at h
  linarith

/-- The **distribution relation** `∑_{i < n} ((x + i / n)) = ((n x))`. -/
theorem sum_sawtooth_add_div (x : K) {n : ℕ} (hn : n ≠ 0) :
    ∑ i ∈ range n, sawtooth (x + i / n) = sawtooth (n * x) := by
  have hK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h1 : ∑ i ∈ range n, (⌊x + i / n⌋ : K) = ⌊n * x⌋ := by
    rw [← Int.cast_sum, Int.sum_floor_add_div]
  have h2 : ∑ i ∈ range n, (⌈x + i / n⌉ : K) = ⌈n * x⌉ + n - 1 := by
    rw [← Int.cast_sum, sum_ceil_add_div x hn]; push_cast; ring
  have h3 : ∑ i ∈ range n, (x + i / n) = n * x + (n - 1) / 2 := by
    rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← sum_div, sum_range_natCast]
    field_simp
  simp only [sawtooth]
  rw [sum_sub_distrib, h3, ← sum_div, sum_add_distrib, h1, h2]
  ring

end Sawtooth

/-! ### Dedekind sums -/

/-- `((a / k))` for a residue `a` modulo `k`. -/
def sawtoothZMod (k : ℕ) (a : ZMod k) : ℚ := sawtooth ((a.val : ℚ) / k)

theorem sawtoothZMod_intCast {k : ℕ} [NeZero k] (n : ℤ) :
    sawtoothZMod k n = sawtooth ((n : ℚ) / k) := by
  have hk : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne k)
  have e : (n : ℚ) = ((n : ZMod k).val : ℚ) + k * ((n / k : ℤ) : ℚ) := by
    have := Int.emod_add_mul_ediv n k
    rw [← ZMod.val_intCast] at this
    exact_mod_cast this.symm
  rw [sawtoothZMod, e, add_div, mul_div_cancel_left₀ _ hk, sawtooth_add_intCast]

/-- The Dedekind sum `s(h, k) = ∑_{r < k} ((r / k)) ((h r / k))`. -/
def dedekindSum (h : ℤ) (k : ℕ) : ℚ :=
  ∑ r ∈ range k, sawtooth ((r : ℚ) / k) * sawtooth ((h * r : ℚ) / k)

@[simp] theorem dedekindSum_zero_right (h : ℤ) : dedekindSum h 0 = 0 := by simp [dedekindSum]

@[simp] theorem dedekindSum_one_right (h : ℤ) : dedekindSum h 1 = 0 := by simp [dedekindSum]

@[simp] theorem dedekindSum_zero_left (k : ℕ) : dedekindSum 0 k = 0 := by simp [dedekindSum]

@[simp] theorem dedekindSum_neg (h : ℤ) (k : ℕ) : dedekindSum (-h) k = -dedekindSum h k := by
  simp [dedekindSum, neg_div]

/-- `s(h, k)` as a sum over the residues modulo `k`. -/
theorem dedekindSum_eq_sum_zmod (h : ℤ) (k : ℕ) [NeZero k] :
    dedekindSum h k = ∑ a : ZMod k, sawtoothZMod k a * sawtoothZMod k (h * a) := by
  rw [dedekindSum, sum_range_eq_sum_zmod]
  refine Fintype.sum_congr _ _ fun a => ?_
  rw [show (h : ZMod k) * a = ((h * a.val : ℤ) : ZMod k) by
    push_cast; rw [ZMod.natCast_zmod_val], sawtoothZMod_intCast]
  push_cast
  rfl

/-- `s(h, k)` depends on `h` only modulo `k`. -/
theorem dedekindSum_congr {h h' : ℤ} {k : ℕ} (hh : h ≡ h' [ZMOD k]) :
    dedekindSum h k = dedekindSum h' k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have : NeZero k := ⟨hk⟩
  rw [dedekindSum_eq_sum_zmod, dedekindSum_eq_sum_zmod, (ZMod.intCast_eq_intCast_iff h h' k).mpr hh]

/-- `s(h', k) = s(h, k)` when `h h' ≡ 1 (mod k)`. -/
theorem dedekindSum_of_mul_modEq_one {h h' : ℤ} {k : ℕ} (hh : h * h' ≡ 1 [ZMOD k]) :
    dedekindSum h' k = dedekindSum h k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have : NeZero k := ⟨hk⟩
  have e : (h : ZMod k) * h' = 1 := by
    have := (ZMod.intCast_eq_intCast_iff _ _ k).mpr hh
    push_cast at this
    exact this
  rw [dedekindSum_eq_sum_zmod, dedekindSum_eq_sum_zmod,
    ← sum_zmod_mul e (fun a => sawtoothZMod k a * sawtoothZMod k (h' * a))]
  refine Fintype.sum_congr _ _ fun a => ?_
  rw [← mul_assoc, mul_comm (h' : ZMod k), e, one_mul, mul_comm]

/-- `s(h, k) = 0` when `h² ≡ -1 (mod k)`. -/
theorem dedekindSum_eq_zero_of_sq_modEq_neg_one {h : ℤ} {k : ℕ} (hh : h ^ 2 ≡ -1 [ZMOD k]) :
    dedekindSum h k = 0 := by
  have := dedekindSum_of_mul_modEq_one (h' := -h) (by convert hh.neg using 1 <;> ring)
  rw [dedekindSum_neg] at this
  linarith

/-- Homogeneity: `s(d h, d k) = s(h, k)` for `d ≠ 0`. -/
theorem dedekindSum_mul_mul (h : ℤ) (k : ℕ) {d : ℕ} (hd : d ≠ 0) :
    dedekindSum (d * h) (d * k) = dedekindSum h k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have hd' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  rw [dedekindSum, mul_comm d k, sum_range_mul, dedekindSum]
  refine sum_congr rfl fun j _ => ?_
  have e : ∀ i ∈ range d,
      sawtooth (((j + k * i : ℕ) : ℚ) / ((k * d : ℕ) : ℚ)) *
        sawtooth (((d * h : ℤ) : ℚ) * ((j + k * i : ℕ) : ℚ) / ((k * d : ℕ) : ℚ)) =
      sawtooth ((j : ℚ) / (k * d) + i / d) * sawtooth ((h * j : ℚ) / k) := by
    intro i _
    congr 1
    · congr 1; push_cast; field_simp
    · rw [show ((d * h : ℤ) : ℚ) * ((j + k * i : ℕ) : ℚ) / ((k * d : ℕ) : ℚ) =
          h * j / k + ((h * i : ℤ) : ℚ) by push_cast; field_simp, sawtooth_add_intCast]
  rw [sum_congr rfl e, ← sum_mul, sum_sawtooth_add_div _ hd]
  congr 2
  field_simp

/-! ### The integer formula -/

section Coprime

variable {h k : ℕ}

/-- For coprime `h, k` with `k > 0`,
`s(h, k) = (∑_{r < k} r (h r mod k)) / k² - (k - 1) / 4`. -/
theorem dedekindSum_eq_sum_mod (hk : k ≠ 0) (hc : h.Coprime k) :
    dedekindSum h k = (∑ r ∈ range k, r * (h * r % k) : ℕ) / k ^ 2 - (k - 1) / 4 := by
  have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have e : ∀ r ∈ range k, sawtooth ((r : ℚ) / k) * sawtooth (((h : ℤ) : ℚ) * r / k) =
      ((r : ℚ) / k - 1 / 2) * (((h * r % k : ℕ) : ℚ) / k - 1 / 2) -
        if r = 0 then 1 / 4 else 0 := by
    intro r hr
    rcases eq_or_ne r 0 with rfl | hr0
    · norm_num
    have hrk := mem_range.mp hr
    have h1 : ¬ k ∣ r := fun hd => hr0 (Nat.eq_zero_of_dvd_of_lt hd hrk)
    have h2 : ¬ k ∣ h * r := fun hd => h1 (hc.symm.dvd_of_dvd_mul_left hd)
    rw [Int.cast_natCast, ← Nat.cast_mul, sawtooth_natCast_div hk, sawtooth_natCast_div hk,
      ite_eq_right h1, ite_eq_right h2, Nat.mod_eq_of_lt hrk, ite_eq_right hr0, sub_zero]
  have hperm : ∑ r ∈ range k, ((h * r % k : ℕ) : ℚ) = ∑ r ∈ range k, (r : ℚ) :=
    sum_mul_mod hc fun n => (n : ℚ)
  have e' : ∀ r ∈ range k, ((r : ℚ) / k - 1 / 2) * (((h * r % k : ℕ) : ℚ) / k - 1 / 2) =
      (r : ℚ) * ((h * r % k : ℕ) : ℚ) / k ^ 2 - (r : ℚ) / (2 * k) -
        ((h * r % k : ℕ) : ℚ) / (2 * k) + 1 / 4 := by
    intros; field_simp; ring
  rw [dedekindSum, sum_congr rfl e, sum_sub_distrib, sum_congr rfl e', sum_add_distrib,
    sum_sub_distrib, sum_sub_distrib, ← sum_div, ← sum_div, ← sum_div, hperm, sum_const,
    card_range, sum_ite_eq' _ 0, ite_eq_left (mem_range.mpr (Nat.pos_of_ne_zero hk)),
    sum_range_natCast]
  push_cast
  field_simp
  ring

/-- The facts behind the reciprocity law. Write `q_r = ⌊h r / k⌋`. Then
`s(h, k) = (h ∑ r² - k ∑ r q_r) / k² - (k - 1) / 4`, `k ∑ q_r = (h - 1) ∑ r` and
`k² ∑ q_r² - 2 h k ∑ r q_r + (h² - 1) ∑ r² = 0`, all sums over `r < k`. -/
private theorem dedekindSum_aux (hk : k ≠ 0) (hc : h.Coprime k) :
    dedekindSum h k = (h * ∑ r ∈ range k, (r : ℚ) ^ 2 -
        k * ∑ r ∈ range k, (r : ℚ) * (h * r / k : ℕ)) / k ^ 2 - (k - 1) / 4 ∧
      k * ∑ r ∈ range k, ((h * r / k : ℕ) : ℚ) = (h - 1) * ∑ r ∈ range k, (r : ℚ) ∧
      k ^ 2 * ∑ r ∈ range k, ((h * r / k : ℕ) : ℚ) ^ 2 -
        2 * h * k * ∑ r ∈ range k, (r : ℚ) * (h * r / k : ℕ) +
        (h ^ 2 - 1) * ∑ r ∈ range k, (r : ℚ) ^ 2 = 0 := by
  -- `h r = k q_r + ρ_r` with `ρ_r = h r mod k`
  have hρ : ∀ r, ((h * r % k : ℕ) : ℚ) = h * r - k * (h * r / k : ℕ) := fun r => by
    have := Nat.mod_add_div (h * r) k
    rw [eq_sub_iff_add_eq]
    exact_mod_cast this
  have s1 : ∑ r ∈ range k, ((h * r % k : ℕ) : ℚ) = ∑ r ∈ range k, (r : ℚ) :=
    sum_mul_mod hc fun n => (n : ℚ)
  have s2 : ∑ r ∈ range k, ((h * r % k : ℕ) : ℚ) ^ 2 = ∑ r ∈ range k, (r : ℚ) ^ 2 :=
    sum_mul_mod hc fun n => (n : ℚ) ^ 2
  have x1 : ∑ r ∈ range k, ((h * r % k : ℕ) : ℚ) =
      h * ∑ r ∈ range k, (r : ℚ) - k * ∑ r ∈ range k, ((h * r / k : ℕ) : ℚ) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun r _ => hρ r
  have x2 : ∑ r ∈ range k, ((h * r % k : ℕ) : ℚ) ^ 2 =
      h ^ 2 * ∑ r ∈ range k, (r : ℚ) ^ 2 -
        2 * h * k * ∑ r ∈ range k, (r : ℚ) * (h * r / k : ℕ) +
        k ^ 2 * ∑ r ∈ range k, ((h * r / k : ℕ) : ℚ) ^ 2 := by
    rw [mul_sum, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun r _ => by rw [hρ]; ring
  have x3 : ∑ r ∈ range k, (r : ℚ) * ((h * r % k : ℕ) : ℚ) =
      h * ∑ r ∈ range k, (r : ℚ) ^ 2 - k * ∑ r ∈ range k, (r : ℚ) * (h * r / k : ℕ) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun r _ => by rw [hρ]; ring
  refine ⟨?_, by linear_combination x1 - s1, by linear_combination s2 - x2⟩
  rw [dedekindSum_eq_sum_mod hk hc]
  push_cast
  rw [x3]

/-- Counting the points `(x, y)` with `x < k`, `y < h` on either side of the line
`y k = h x`, weighted by `y`. -/
private theorem lattice (hh : h ≠ 0) (hk : k ≠ 0) (hc : h.Coprime k) :
    ∑ x ∈ range k, ∑ y ∈ range (h * x / k + 1), y + ∑ y ∈ range h, y * (k * y / h + 1) =
      k * ∑ y ∈ range h, y := by
  have hk0 := Nat.pos_of_ne_zero hk
  have hh0 := Nat.pos_of_ne_zero hh
  have below : ∀ x ∈ range k, ∑ y ∈ range h with y * k ≤ h * x, y =
      ∑ y ∈ range (h * x / k + 1), y := by
    intro x hx
    have hx := mem_range.mp hx
    congr 1
    ext y
    simp only [mem_filter, mem_range, Nat.lt_succ_iff, Nat.le_div_iff_mul_le hk0]
    refine ⟨And.right, fun hy => ⟨?_, hy⟩⟩
    by_contra hy'
    push Not at hy'
    nlinarith
  have above : ∀ y ∈ range h, ∑ x ∈ range k with ¬ y * k ≤ h * x, y = y * (k * y / h + 1) := by
    intro y hy
    have hy := mem_range.mp hy
    rw [sum_const, smul_eq_mul, mul_comm _ (k * y / h + 1)]
    rcases eq_or_ne y 0 with rfl | hy0
    · simp
    congr 1
    rw [← card_range (k * y / h + 1)]
    congr 1
    ext x
    simp only [mem_filter, mem_range, Nat.lt_succ_iff, Nat.le_div_iff_mul_le hh0, not_le]
    constructor
    · rintro ⟨-, hx⟩; nlinarith
    · intro hx
      have hne : x * h ≠ k * y := fun he =>
        hy0 (Nat.eq_zero_of_dvd_of_lt (hc.dvd_of_dvd_mul_left ⟨x, by rw [← he, mul_comm]⟩) hy)
      refine ⟨?_, by
        rcases lt_or_eq_of_le hx with hlt | heq
        · nlinarith
        · exact absurd heq hne⟩
      by_contra hxk
      push Not at hxk
      nlinarith
  have split : ∀ x ∈ range k, ∑ y ∈ range h, y =
      ∑ y ∈ range (h * x / k + 1), y + ∑ y ∈ range h with ¬ y * k ≤ h * x, y := fun x hx => by
    rw [← below x hx, sum_filter_add_sum_filter_not]
  have swap : ∑ x ∈ range k, ∑ y ∈ range h with ¬ y * k ≤ h * x, y =
      ∑ y ∈ range h, ∑ x ∈ range k with ¬ y * k ≤ h * x, y := by
    simp only [sum_filter]
    exact sum_comm
  rw [show k * ∑ y ∈ range h, y = ∑ x ∈ range k, ∑ y ∈ range h, y by
    rw [sum_const, card_range, smul_eq_mul], sum_congr rfl split, sum_add_distrib, swap,
    sum_congr rfl above]

/-- The **reciprocity law** for Dedekind sums. -/
theorem dedekindSum_reciprocity (hh : h ≠ 0) (hk : k ≠ 0) (hc : h.Coprime k) :
    dedekindSum h k + dedekindSum k h = (h ^ 2 + k ^ 2 + 1) / (12 * h * k) - 1 / 4 := by
  have hh' : (h : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hh
  have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  obtain ⟨s1, f1, g1⟩ := dedekindSum_aux hk hc
  obtain ⟨s2, -, -⟩ := dedekindSum_aux hh hc.symm
  have L := congrArg (Nat.cast : ℕ → ℚ) (lattice hh hk hc)
  push_cast [sum_range_natCast] at L
  have e1 : ∑ x ∈ range k, (((h * x / k : ℕ) : ℚ) + 1) * (((h * x / k : ℕ) : ℚ) + 1 - 1) / 2 =
      (∑ x ∈ range k, ((h * x / k : ℕ) : ℚ) ^ 2 + ∑ x ∈ range k, ((h * x / k : ℕ) : ℚ)) / 2 := by
    rw [← sum_add_distrib, sum_div]
    exact sum_congr rfl fun _ _ => by ring
  have e2 : ∑ y ∈ range h, (y : ℚ) * (((k * y / h : ℕ) : ℚ) + 1) =
      ∑ y ∈ range h, (y : ℚ) * ((k * y / h : ℕ) : ℚ) + h * (h - 1) / 2 := by
    rw [← sum_range_natCast, ← sum_add_distrib]
    exact sum_congr rfl fun _ _ => by ring
  rw [e1, e2] at L
  rw [s1, s2, sum_range_natCast_sq, sum_range_natCast_sq]
  rw [sum_range_natCast] at f1
  rw [sum_range_natCast_sq] at g1
  linear_combination (norm := skip) (-1 / h : ℚ) * L + (1 / (2 * h * k ^ 2) : ℚ) * g1 +
    (1 / (2 * h * k) : ℚ) * f1
  field_simp
  ring

/-- `6 k s(h, k)` is an integer, for coprime `h, k` with `k > 0`. -/
theorem exists_six_mul_dedekindSum_eq (hk : k ≠ 0) (hc : h.Coprime k) :
    ∃ z : ℤ, 6 * k * dedekindSum h k = z := by
  have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  obtain ⟨s, -, -⟩ := dedekindSum_aux hk hc
  refine ⟨h * (k - 1) * (2 * k - 1) - 6 * ((∑ r ∈ range k, r * (h * r / k) : ℕ) : ℤ) -
    3 * ((∑ r ∈ range k, r : ℕ) : ℤ), ?_⟩
  rw [s, sum_range_natCast_sq]
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, Int.cast_one,
    Nat.cast_sum, Nat.cast_mul, Int.cast_sum, sum_range_natCast]
  field_simp
  ring

/-- For coprime `h, k > 0`, `12 h k s(h, k)` is an integer congruent to `h² + 1` modulo `k`. -/
theorem exists_twelve_mul_dedekindSum_modEq (hh : h ≠ 0) (hk : k ≠ 0) (hc : h.Coprime k) :
    ∃ z : ℤ, 12 * h * k * dedekindSum h k = z ∧ z ≡ h ^ 2 + 1 [ZMOD k] := by
  have hh' : (h : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hh
  have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  obtain ⟨w, hw⟩ := exists_six_mul_dedekindSum_eq hh hc.symm
  have R := dedekindSum_reciprocity hh hk hc
  refine ⟨h ^ 2 + k ^ 2 + 1 - 3 * h * k - 2 * k * w, ?_,
    Int.modEq_iff_dvd.mpr ⟨3 * h - k + 2 * w, by ring⟩⟩
  push_cast
  linear_combination (norm := skip) (12 * h * k : ℚ) * R - 2 * k * hw
  field_simp
  ring

end Coprime

/-! ### Values and bounds -/

theorem dedekindSum_one_left (k : ℕ) : dedekindSum 1 k = (k - 1) * (k - 2) / (12 * k) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have h := dedekindSum_eq_sum_mod hk (Nat.coprime_one_left k)
  have e : ∑ r ∈ range k, r * (1 * r % k) = ∑ r ∈ range k, r ^ 2 :=
    sum_congr rfl fun r hr => by rw [one_mul, Nat.mod_eq_of_lt (mem_range.mp hr), sq]
  rw [Nat.cast_one, e] at h
  rw [h]
  push_cast
  rw [sum_range_natCast_sq]
  field_simp
  ring

theorem dedekindSum_two_left {k : ℕ} (hk : Odd k) :
    dedekindSum 2 k = (k - 1) * (k - 5) / (24 * k) := by
  have hk0 : k ≠ 0 := by rintro rfl; exact absurd hk (by decide)
  have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
  have R := dedekindSum_reciprocity two_ne_zero hk0 (Nat.coprime_two_left.mpr hk)
  have h2 : dedekindSum k 2 = 0 := by
    rw [dedekindSum_congr (h' := 1) (by simp only [Int.ModEq]; have := Nat.odd_iff.mp hk; omega),
      dedekindSum_one_left]
    norm_num
  rw [h2] at R
  push_cast at R
  linear_combination (norm := skip) R
  field_simp
  ring

/-- `|s(h, k)| ≤ s(1, k)` for `h` coprime to `k`. -/
theorem abs_dedekindSum_le {h : ℤ} {k : ℕ} (hc : IsCoprime h k) :
    |dedekindSum h k| ≤ dedekindSum 1 k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have : NeZero k := ⟨hk⟩
  obtain ⟨u, v, huv⟩ := hc
  have e : (h : ZMod k) * u = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod k) huv
    push_cast [ZMod.natCast_self] at this
    linear_combination this
  rw [dedekindSum_eq_sum_zmod, dedekindSum_eq_sum_zmod]
  simp only [Int.cast_one, one_mul]
  calc |∑ a, sawtoothZMod k a * sawtoothZMod k (h * a)|
      ≤ ∑ a, |sawtoothZMod k a * sawtoothZMod k (h * a)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, (sawtoothZMod k a ^ 2 + sawtoothZMod k (h * a) ^ 2) / 2 := by
        gcongr with a
        have := two_mul_le_add_sq |sawtoothZMod k a| |sawtoothZMod k (h * a)|
        rw [sq_abs, sq_abs] at this
        rw [abs_mul]
        linarith
    _ = ∑ a, sawtoothZMod k a * sawtoothZMod k a := by
        rw [← sum_div, sum_add_distrib, sum_zmod_mul e fun a => sawtoothZMod k a ^ 2]
        simp only [sq]
        ring
