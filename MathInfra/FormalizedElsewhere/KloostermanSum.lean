module

public import MathInfra.FormalizedElsewhere.RamanujanSum

/-!
# Kloosterman sums

For a character `ψ` of the additive group of `ZMod q`, with values in a commutative ring, the
Kloosterman sum is

`S(ψ; m, n) = ∑_{x ∈ (ZMod q)ˣ} ψ(m x + n x⁻¹)`.

For the standard character `ψ(x) = exp(2πi x/q)` this is the classical `S(m, n; q)`, introduced by
Kloosterman (1926) to represent integers by quaternary quadratic forms. Kloosterman sums appear in
the Fourier coefficients of Poincaré series, in the Petersson and Kuznetsov trace formulas and, with
the multiplier of the eta function, in Rademacher's formula for the partition function. With `n = 0`
they reduce to Ramanujan sums. For prime `q` and `a ≠ 0`, `S(ψ; 1, a)` is Katz's rank-two
Kloosterman sum `Kl₂(ψ; a)`. Twisted by a quadratic character, Kloosterman sums become Salié sums.

Kloosterman sums are twisted multiplicative in `q`, which reduces them to prime powers; complex
Kloosterman sums are real; and over a prime `p` the fourth moment gives Kloosterman's bound
`|S(m, n; p)| ≤ 3^(1/4) p^(3/4)` for `(m, n) ≠ (0, 0)`, the first improvement on the exponent of the
trivial bound `p − 1`. Weil's bound `|S(m, n; p)| ≤ 2√p` for `mn ≠ 0` rests on the Riemann
hypothesis for curves (or Stepanov's method) and is not proved here.

## Prior art

Checked in November 2026. Mathlib (2026-11-19) has additive characters, primitivity and the standard
character `ZMod.stdAddChar`, but no Kloosterman sums, and no Mathlib PR or issue mentions them. The
Lean 4 project `jieun38-kim/Kloosterman` (2023, supervised by Kevin Buzzard) defines `S(a, b; q)`
over `ℂ` and proves invariance modulo `q`, `S(a, b) = S(b, a)` and `S(a, b) = S(1, ab)` for `a`, `b`
coprime to `q`; `S(u m, n) = S(m, u n)` for a unit `u` and twisted multiplicativity appear only as
commented-out statements with `sorry`. Open TauCeti roadmap PRs
(`KloostermanSheavesAndBesselIsocrystals`, `KloostermanMomentsAndPotentialAutomorphy`) and the
project `BrandonMYates/kklab` define Kloosterman sums over finite fields but prove none of the
results here. Nothing was found in the Isabelle AFP, Rocq or HOL.

## Main definitions

* `kloostermanSum ψ m n` : the Kloosterman sum `S(ψ; m, n)`.
* `ZMod.mulCofactor b h` : for `a * b = n`, the additive map `ZMod a → ZMod n`, `x ↦ b x`.
* `hyperbolaEnergy q` : the number of `(x₁, x₂, y₁, y₂) ∈ ((ZMod q)ˣ)⁴` with
  `x₁ + x₂ = y₁ + y₂` and `x₁⁻¹ + x₂⁻¹ = y₁⁻¹ + y₂⁻¹`.

## Main results

* `kloostermanSum_comm`, `kloostermanSum_neg`, `kloostermanSum_units_mul`,
  `kloostermanSum_units_left` : `S(m, n) = S(n, m) = S(−m, −n)`, `S(u m, n) = S(m, u n)` for a
  unit `u`, so `S(u, n) = S(1, u n)`.
* `kloostermanSum_mul`, `kloostermanSum_stdAddChar_mul` : **twisted multiplicativity**: for
  coprime `q₁`, `q₂`, `S(ψ; m, n) = S(ψ₁; q̄₂ m, q̄₂ n) · S(ψ₂; q̄₁ m, q̄₁ n)` with the induced
  characters `ψ₁`, `ψ₂`, and so `S(m, n; q₁ q₂) = S(q̄₂ m, q̄₂ n; q₁) · S(q̄₁ m, q̄₁ n; q₂)`.
* `kloostermanSum_zero_right_eq_ramanujanSum` : `S(ψ; m, 0) = c_q(m)` for an integer `m` and a
  primitive `ψ` with values in an integral domain.
* `sum_kloostermanSum_left` : `∑_m S(ψ; m, n) = 0` for such `ψ` and `q ≠ 1`.
* `conj_kloostermanSum`, `kloostermanSum_im` : complex Kloosterman sums are real.
* `sum_norm_kloostermanSum_sq` : `∑_m |S(ψ; m, n)|² = q φ(q)` for primitive `ψ`.
* `sum_norm_kloostermanSum_pow_four` : `∑_{m, n} |S(ψ; m, n)|⁴ = q² · hyperbolaEnergy q` for
  primitive `ψ`.
* `hyperbolaEnergy_le` : `hyperbolaEnergy p ≤ 3 (p − 1)²` for prime `p`.
* `norm_kloostermanSum_pow_four_le`, `norm_kloostermanSum_le` : **Kloosterman's bound**
  `|S(ψ; m, n)|⁴ ≤ 3p³`, so `|S(ψ; m, n)| ≤ 3^(1/4) p^(3/4)`, for a prime `p`, primitive `ψ` and
  `(m, n) ≠ (0, 0)`.
-/

@[expose] public section

open Finset AddChar
open scoped Nat

section Basic

variable {q : ℕ} [NeZero q] {R : Type*} [CommRing R] (ψ : AddChar (ZMod q) R)

/-- The Kloosterman sum `S(ψ; m, n) = ∑_{x ∈ (ZMod q)ˣ} ψ(m x + n x⁻¹)`. -/
def kloostermanSum (m n : ZMod q) : R :=
  ∑ x : (ZMod q)ˣ, ψ (m * x + n * ↑x⁻¹)

variable (m n : ZMod q)

/-- `S(ψ; m, n) = S(ψ; n, m)`: substitute `x ↦ x⁻¹`. -/
theorem kloostermanSum_comm : kloostermanSum ψ m n = kloostermanSum ψ n m :=
  Fintype.sum_equiv (Equiv.inv _) _ _ fun x => by simp [add_comm]

/-- `S(ψ; u m, n) = S(ψ; m, u n)` for a unit `u`: substitute `x ↦ u x`. -/
theorem kloostermanSum_units_mul (u : (ZMod q)ˣ) :
    kloostermanSum ψ (u * m) n = kloostermanSum ψ m (u * n) :=
  Fintype.sum_equiv (Equiv.mulLeft u) _ _ fun x => by
    congr 1
    simp only [Equiv.coe_mulLeft, Units.val_mul, mul_inv_rev]
    linear_combination (-(n * ↑x⁻¹)) * Units.mul_inv u

/-- For a unit `u`, `S(ψ; u, n) = S(ψ; 1, u n)`: a Kloosterman sum with a unit argument depends
only on the product of its arguments. -/
theorem kloostermanSum_units_left (u : (ZMod q)ˣ) :
    kloostermanSum ψ u n = kloostermanSum ψ 1 (u * n) := by
  simpa using kloostermanSum_units_mul ψ 1 n u

/-- `S(ψ; −m, −n) = S(ψ; m, n)`: substitute `x ↦ −x`. -/
theorem kloostermanSum_neg : kloostermanSum ψ (-m) (-n) = kloostermanSum ψ m n :=
  Fintype.sum_equiv (Equiv.neg _) _ _ fun x => by simp

/-- Scaling the character: `S(ψ_a; m, n) = S(ψ; a m, a n)`, where `ψ_a(x) = ψ(a x)`. -/
theorem kloostermanSum_mulShift (a : ZMod q) :
    kloostermanSum (ψ.mulShift a) m n = kloostermanSum ψ (a * m) (a * n) := by
  simp [kloostermanSum, mul_add, mul_assoc]

/-- `S(ψ; m, 0) = ∑_{x ∈ (ZMod q)ˣ} ψ(m x)`. -/
theorem kloostermanSum_zero_right : kloostermanSum ψ m 0 = ∑ x : (ZMod q)ˣ, ψ (m * x) := by
  simp [kloostermanSum]

/-- `S(ψ; 0, 0) = φ(q)`. -/
@[simp] theorem kloostermanSum_zero_zero : kloostermanSum ψ 0 0 = φ q := by
  simp [kloostermanSum, ZMod.card_units_eq_totient]

end Basic

/-! ### Twisted multiplicativity -/

namespace ZMod

/-- For `a * b = n`, multiplication by `b` as an additive map `ZMod a → ZMod n`. -/
def mulCofactor {a n : ℕ} (b : ℕ) (h : a * b = n) : ZMod a →+ ZMod n :=
  ZMod.lift a ⟨(AddMonoidHom.mulLeft (b : ZMod n)).comp (Int.castAddHom (ZMod n)), by
    simp only [AddMonoidHom.comp_apply, Int.coe_castAddHom, Int.cast_natCast,
      AddMonoidHom.coe_mulLeft]
    rw [← Nat.cast_mul, mul_comm, h, ZMod.natCast_self]⟩

variable {a n : ℕ} (b : ℕ) (h : a * b = n)

/-- On an integer `k`, `mulCofactor b h` is `k ↦ b k`. -/
theorem mulCofactor_intCast (k : ℤ) : mulCofactor b h k = b * k :=
  ZMod.lift_coe _ _ _

/-- Reduced modulo `a`, `mulCofactor b h x` is `b x` computed in `ZMod a`. -/
theorem castHom_mulCofactor_self (x : ZMod a) :
    castHom (Dvd.intro b h) (ZMod a) (mulCofactor b h x) = b * x := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  rw [mulCofactor_intCast, map_mul, map_natCast, map_intCast]

/-- Reduced modulo a common divisor `c` of `n` and `b`, `mulCofactor b h x` is `0`. -/
theorem castHom_mulCofactor_of_dvd {c : ℕ} (hc : c ∣ n) (hb : c ∣ b) (x : ZMod a) :
    castHom hc (ZMod c) (mulCofactor b h x) = 0 := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  rw [mulCofactor_intCast, map_mul, map_natCast, (ZMod.natCast_eq_zero_iff b c).mpr hb,
    zero_mul]

end ZMod

section Multiplicative

open ZMod

variable {R : Type*} [CommRing R] {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]

/-- **Twisted multiplicativity**: for coprime `q₁`, `q₂`,
`S(ψ; m, n) = S(ψ₁; q̄₂ m, q̄₂ n) · S(ψ₂; q̄₁ m, q̄₁ n)`, where `ψ₁(x) = ψ(q₂ x)` and
`ψ₂(y) = ψ(q₁ y)` are the characters of `ZMod q₁` and `ZMod q₂` induced by `ψ`, `q̄₂` is the
inverse of `q₂` modulo `q₁`, `q̄₁` that of `q₁` modulo `q₂`, and `m`, `n` are reduced modulo `q₁`
in the first factor and modulo `q₂` in the second. -/
theorem kloostermanSum_mul (hq : q₁.Coprime q₂) (ψ : AddChar (ZMod (q₁ * q₂)) R)
    (m n : ZMod (q₁ * q₂)) :
    kloostermanSum ψ m n =
      kloostermanSum (ψ.compAddMonoidHom (mulCofactor q₂ rfl))
          ((q₂ : ZMod q₁)⁻¹ * castHom (dvd_mul_right q₁ q₂) _ m)
          ((q₂ : ZMod q₁)⁻¹ * castHom (dvd_mul_right q₁ q₂) _ n) *
        kloostermanSum (ψ.compAddMonoidHom (mulCofactor q₁ (mul_comm q₂ q₁)))
          ((q₁ : ZMod q₂)⁻¹ * castHom (dvd_mul_left q₂ q₁) _ m)
          ((q₁ : ZMod q₂)⁻¹ * castHom (dvd_mul_left q₂ q₁) _ n) := by
  set π₁ := castHom (dvd_mul_right q₁ q₂) (ZMod q₁)
  set π₂ := castHom (dvd_mul_left q₂ q₁) (ZMod q₂)
  set ι₁ := mulCofactor (a := q₁) q₂ rfl
  set ι₂ := mulCofactor (a := q₂) q₁ (mul_comm q₂ q₁)
  -- An element of `ZMod (q₁ q₂)` is determined by its residues modulo `q₁` and `q₂`.
  have hinj : ∀ z w, π₁ z = π₁ w → π₂ z = π₂ w → z = w := fun z w h₁ h₂ => by
    apply (chineseRemainder hq).injective
    have e₁ : ∀ z, (chineseRemainder hq z).1 = π₁ z := fun z =>
      congrArg (fun f : ZMod (q₁ * q₂) →+* ZMod q₁ => f z)
        (RingHom.ext_zmod ((RingHom.fst _ _).comp (chineseRemainder hq).toRingHom) π₁)
    have e₂ : ∀ z, (chineseRemainder hq z).2 = π₂ z := fun z =>
      congrArg (fun f : ZMod (q₁ * q₂) →+* ZMod q₂ => f z)
        (RingHom.ext_zmod ((RingHom.snd _ _).comp (chineseRemainder hq).toRingHom) π₂)
    exact Prod.ext (by rw [e₁, e₁, h₁]) (by rw [e₂, e₂, h₂])
  -- The decomposition `w = q₂ · (q̄₂ w mod q₁) + q₁ · (q̄₁ w mod q₂)`.
  have hdec : ∀ w, w = ι₁ ((q₂ : ZMod q₁)⁻¹ * π₁ w) + ι₂ ((q₁ : ZMod q₂)⁻¹ * π₂ w) := by
    intro w
    refine hinj _ _ ?_ ?_
    · rw [map_add, castHom_mulCofactor_self, castHom_mulCofactor_of_dvd _ _ _ dvd_rfl,
        add_zero, ← mul_assoc, ZMod.coe_mul_inv_eq_one _ hq.symm, one_mul]
    · rw [map_add, castHom_mulCofactor_self, castHom_mulCofactor_of_dvd _ _ _ dvd_rfl,
        zero_add, ← mul_assoc, ZMod.coe_mul_inv_eq_one _ hq, one_mul]
  -- The units of `ZMod (q₁ q₂)` are the pairs of units modulo `q₁` and modulo `q₂`.
  let f : (ZMod (q₁ * q₂))ˣ →* (ZMod q₁)ˣ × (ZMod q₂)ˣ :=
    (Units.map π₁.toMonoidHom).prod (Units.map π₂.toMonoidHom)
  have hf : Function.Bijective f := by
    refine (Fintype.bijective_iff_injective_and_card f).mpr ⟨fun z w h => ?_, ?_⟩
    · exact Units.ext (hinj _ _ (congrArg (fun u => (u.1 : ZMod q₁)) h)
        (congrArg (fun u => (u.2 : ZMod q₂)) h))
    · rw [Fintype.card_prod, ZMod.card_units_eq_totient, ZMod.card_units_eq_totient,
        ZMod.card_units_eq_totient, Nat.totient_mul hq]
  rw [kloostermanSum, kloostermanSum, kloostermanSum, Fintype.sum_mul_sum,
    ← Fintype.sum_prod_type']
  refine Fintype.sum_bijective f hf _ _ fun z => ?_
  rw [compAddMonoidHom_apply, compAddMonoidHom_apply, ← map_add_eq_mul]
  conv_lhs => rw [hdec (m * z + n * ↑z⁻¹)]
  congr 3 <;> simp [f, map_add, map_mul, mul_add, mul_assoc]

/-- Twisted multiplicativity for the standard characters `x ↦ exp(2πi x/q)`: for coprime `q₁`,
`q₂`, `S(m, n; q₁ q₂) = S(q̄₂ m, q̄₂ n; q₁) · S(q̄₁ m, q̄₁ n; q₂)`, with `q̄₁`, `q̄₂` as in
`kloostermanSum_mul`. -/
theorem kloostermanSum_stdAddChar_mul (hq : q₁.Coprime q₂) (m n : ZMod (q₁ * q₂)) :
    kloostermanSum stdAddChar m n =
      kloostermanSum stdAddChar
          ((q₂ : ZMod q₁)⁻¹ * castHom (dvd_mul_right q₁ q₂) _ m)
          ((q₂ : ZMod q₁)⁻¹ * castHom (dvd_mul_right q₁ q₂) _ n) *
        kloostermanSum stdAddChar
          ((q₁ : ZMod q₂)⁻¹ * castHom (dvd_mul_left q₂ q₁) _ m)
          ((q₁ : ZMod q₂)⁻¹ * castHom (dvd_mul_left q₂ q₁) _ n) := by
  have key : ∀ {a b n : ℕ} [NeZero a] [NeZero n] (h : a * b = n),
      (stdAddChar (N := n)).compAddMonoidHom (mulCofactor b h) = stdAddChar := by
    intro a b n _ _ h
    subst h
    have : (b : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (right_ne_zero_of_mul (NeZero.ne (a * b)))
    ext x
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
    rw [compAddMonoidHom_apply, mulCofactor_intCast, ← Int.cast_natCast, ← Int.cast_mul,
      stdAddChar_coe, stdAddChar_coe]
    congr 1
    push_cast
    field_simp
  rw [kloostermanSum_mul hq, key, key]

end Multiplicative

/-! ### Primitive characters -/

section Primitive

variable {q : ℕ} [NeZero q] {R : Type*} [CommRing R] [IsDomain R] {ψ : AddChar (ZMod q) R}

omit [IsDomain R] in
/-- For a primitive character `ψ` of `ZMod q`, `ψ(1)` is a primitive `q`-th root of unity. -/
theorem AddChar.IsPrimitive.isPrimitiveRoot_one (hψ : ψ.IsPrimitive) :
    IsPrimitiveRoot (ψ 1) q := by
  have key : ∀ l : ℕ, ψ 1 ^ l = 1 ↔ q ∣ l := fun l => by
    rw [← map_nsmul_eq_pow, nsmul_one, hψ.zmod_char_eq_one_iff, ZMod.natCast_eq_zero_iff]
  exact ⟨(key q).mpr dvd_rfl, fun l => (key l).mp⟩

/-- `S(ψ; m, 0)` is the Ramanujan sum `c_q(m)` when `ψ` is primitive. -/
theorem kloostermanSum_zero_right_eq_ramanujanSum (hψ : ψ.IsPrimitive) (m : ℤ) :
    kloostermanSum ψ m 0 = ramanujanSum q m := by
  set N := (m : ZMod q).val
  have hm : (N : ZMod q) = m := ZMod.natCast_zmod_val _
  rw [ramanujanSum_congr q m (m := N) ((ZMod.intCast_eq_intCast_iff _ _ _).mp (by simp [hm])),
    ← hψ.isPrimitiveRoot_one.sum_pow_coprime N, kloostermanSum_zero_right]
  refine sum_bij (fun x _ => (x : ZMod q).val) (fun x _ => ?_) (fun x _ y _ h => ?_)
    (fun k hk => ?_) (fun x _ => ?_)
  · simpa using ⟨ZMod.val_lt _, ZMod.val_coe_unit_coprime x⟩
  · exact Units.ext (ZMod.val_injective q h)
  · rw [mem_filter, mem_range] at hk
    exact ⟨ZMod.unitOfCoprime k hk.2, mem_univ _, by simp [ZMod.val_natCast_of_lt hk.1]⟩
  · rw [← map_nsmul_eq_pow, nsmul_one, Nat.cast_mul, ZMod.natCast_zmod_val, hm, mul_comm]

/-- Summing over the first argument: `∑_m S(ψ; m, n) = 0` for primitive `ψ` and `q ≠ 1`. -/
theorem sum_kloostermanSum_left (hψ : ψ.IsPrimitive) (hq : q ≠ 1) (n : ZMod q) :
    ∑ m, kloostermanSum ψ m n = 0 := by
  have : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr hq
  unfold kloostermanSum
  rw [sum_comm]
  refine sum_eq_zero fun x _ => ?_
  simp_rw [map_add_eq_mul, ← sum_mul, sum_mulShift _ hψ]
  simp [x.ne_zero]

end Primitive

/-! ### Complex Kloosterman sums -/

section Complex

open ComplexConjugate

variable {q : ℕ} [NeZero q] (ψ : AddChar (ZMod q) ℂ)

/-- Complex Kloosterman sums are real: `conj S(ψ; m, n) = S(ψ; m, n)`. -/
theorem conj_kloostermanSum (m n : ZMod q) :
    conj (kloostermanSum ψ m n) = kloostermanSum ψ m n := by
  conv_rhs => rw [← kloostermanSum_neg]
  rw [kloostermanSum, kloostermanSum, map_sum]
  simp_rw [← map_neg_eq_conj, neg_add, neg_mul]

/-- The imaginary part of a complex Kloosterman sum is `0`. -/
theorem kloostermanSum_im (m n : ZMod q) : (kloostermanSum ψ m n).im = 0 :=
  Complex.conj_eq_iff_im.mp (conj_kloostermanSum ψ m n)

variable {ψ}

/-- Orthogonality: `∑_a ψ(a s) · conj ψ(a t)` is `q` if `s = t` and `0` otherwise. -/
theorem AddChar.IsPrimitive.sum_mul_conj (hψ : ψ.IsPrimitive) (s t : ZMod q) :
    ∑ a, ψ (a * s) * conj (ψ (a * t)) = if s = t then (q : ℂ) else 0 := by
  simp_rw [← map_neg_eq_conj, ← map_add_eq_mul, ← mul_neg, ← mul_add, ← sub_eq_add_neg,
    sum_mulShift _ hψ, sub_eq_zero, ZMod.card, Nat.cast_ite, Nat.cast_zero]

/-- The identity behind the moments: for a primitive `ψ`,
`∑_a |∑_i w(i) ψ(a u(i))|² = q ∑_{u(i) = u(j)} w(i) conj w(j)`. -/
theorem AddChar.IsPrimitive.sum_mul_conj_sum (hψ : ψ.IsPrimitive) {ι : Type*} [Fintype ι]
    (u : ι → ZMod q) (w : ι → ℂ) :
    ∑ a, (∑ i, w i * ψ (a * u i)) * conj (∑ i, w i * ψ (a * u i)) =
      q * ∑ i, ∑ j, if u i = u j then w i * conj (w j) else 0 := by
  simp_rw [map_sum, map_mul, sum_mul_sum, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  have := hψ.sum_mul_conj (u i) (u j)
  simp_rw [show ∀ a, w i * ψ (a * u i) * (conj (w j) * conj (ψ (a * u j))) =
    w i * conj (w j) * (ψ (a * u i) * conj (ψ (a * u j))) from fun a => by ring, ← mul_sum, this]
  split_ifs <;> ring

/-- The second moment: `∑_m |S(ψ; m, n)|² = q φ(q)` for primitive `ψ`. -/
theorem sum_norm_kloostermanSum_sq (hψ : ψ.IsPrimitive) (n : ZMod q) :
    ∑ m, ‖kloostermanSum ψ m n‖ ^ 2 = q * φ q := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj']
  have h := hψ.sum_mul_conj_sum (fun x : (ZMod q)ˣ => (x : ZMod q)) (fun x => ψ (n * ↑x⁻¹))
  simp_rw [Units.val_inj] at h
  simp only [kloostermanSum, map_add_eq_mul, mul_comm (ψ (_ * _)) (ψ (n * _))]
  rw [h]
  simp [← map_neg_eq_conj, ← map_add_eq_mul, ZMod.card_units_eq_totient]

/-- The additive energy of the hyperbola `{(x, x⁻¹) : x ∈ (ZMod q)ˣ}`: the number of
`((x₁, x₂), (y₁, y₂))` in `((ZMod q)ˣ)⁴` with `x₁ + x₂ = y₁ + y₂` and
`x₁⁻¹ + x₂⁻¹ = y₁⁻¹ + y₂⁻¹`. -/
def hyperbolaEnergy (q : ℕ) [NeZero q] : ℕ :=
  #{x : ((ZMod q)ˣ × (ZMod q)ˣ) × ((ZMod q)ˣ × (ZMod q)ˣ) |
    (x.1.1 : ZMod q) + x.1.2 = x.2.1 + x.2.2 ∧
      ((x.1.1⁻¹ : (ZMod q)ˣ) : ZMod q) + ↑x.1.2⁻¹ = ↑x.2.1⁻¹ + ↑x.2.2⁻¹}

/-- The fourth moment: `∑_{m, n} |S(ψ; m, n)|⁴ = q² E(q)` for primitive `ψ`, where `E(q)` is
`hyperbolaEnergy q`. -/
theorem sum_norm_kloostermanSum_pow_four (hψ : ψ.IsPrimitive) :
    ∑ m, ∑ n, ‖kloostermanSum ψ m n‖ ^ 4 = q ^ 2 * hyperbolaEnergy q := by
  have hS : ∀ m n, kloostermanSum ψ m n ^ 2 = ∑ x : (ZMod q)ˣ × (ZMod q)ˣ,
      ψ (n * (↑x.1⁻¹ + ↑x.2⁻¹)) * ψ (m * (↑x.1 + ↑x.2)) := fun m n => by
    rw [sq, kloostermanSum, Fintype.sum_mul_sum, ← Fintype.sum_prod_type']
    refine sum_congr rfl fun x _ => ?_
    rw [← map_add_eq_mul, ← map_add_eq_mul]
    ring_nf
  simp_rw [show ∀ z : ℂ, ‖z‖ ^ 4 = ‖z ^ 2‖ ^ 2 from fun z => by rw [norm_pow, ← pow_mul]]
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj', hS]
  rw [sum_comm]
  simp_rw [hψ.sum_mul_conj_sum, ← mul_sum]
  rw [sum_comm]
  have key : ∀ y j : (ZMod q)ˣ × (ZMod q)ˣ, (∑ x : ZMod q,
      if (y.1 : ZMod q) + y.2 = j.1 + j.2 then
        ψ (x * (↑y.1⁻¹ + ↑y.2⁻¹)) * conj (ψ (x * (↑j.1⁻¹ + ↑j.2⁻¹))) else 0) =
      if (y.1 : ZMod q) + y.2 = j.1 + j.2 ∧
        ((y.1⁻¹ : (ZMod q)ˣ) : ZMod q) + ↑y.2⁻¹ = ↑j.1⁻¹ + ↑j.2⁻¹ then (q : ℂ) else 0 := by
    intro y j
    split_ifs with h h' h'
    · rw [hψ.sum_mul_conj, ite_eq_left h'.2]
    · rw [hψ.sum_mul_conj, ite_eq_right fun h'' => h' ⟨h, h''⟩]
    · exact absurd h'.1 h
    · exact sum_const_zero
  simp_rw [sum_comm (s := (univ : Finset (ZMod q))), key, ← Fintype.sum_prod_type', sum_ite,
    sum_const_zero, add_zero, sum_const, nsmul_eq_mul, hyperbolaEnergy]
  ring

end Complex

/-! ### Kloosterman's bound -/

section Prime

variable {p : ℕ} [Fact p.Prime]

/-- Over a prime `p`, the hyperbola has additive energy at most `3 (p − 1)²`: given `(x₁, x₂)`,
the first coordinate of `(y₁, y₂)` determines the second, and it is `x₁` or `x₂` unless
`x₁ + x₂ = 0`. -/
theorem hyperbolaEnergy_le : hyperbolaEnergy p ≤ 3 * (p - 1) ^ 2 := by
  have hU : Fintype.card (ZMod p)ˣ = p - 1 := ZMod.card_units p
  -- The solutions `y` for a given `x`.
  let S : (ZMod p)ˣ × (ZMod p)ˣ → Finset ((ZMod p)ˣ × (ZMod p)ˣ) := fun x =>
    {y | (x.1 : ZMod p) + x.2 = y.1 + y.2 ∧
      ((x.1⁻¹ : (ZMod p)ˣ) : ZMod p) + ↑x.2⁻¹ = ↑y.1⁻¹ + ↑y.2⁻¹}
  have hinj : ∀ x, Set.InjOn (fun y : (ZMod p)ˣ × (ZMod p)ˣ => y.1) (S x) := by
    intro x y hy y' hy' h
    simp only [S, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy hy'
    refine Prod.ext h (Units.ext ?_)
    have : (y.1 : ZMod p) = y'.1 := congrArg _ h
    linear_combination hy'.1 - hy.1 - this
  have hcard : ∀ x, #(S x) ≤ (if (x.1 : ZMod p) + x.2 = 0 then p - 1 else 0) + 2 := by
    intro x
    split_ifs with hs
    · exact (card_le_card_of_injOn _ (fun _ _ => mem_univ _) (hinj x)).trans
        (by rw [card_univ, hU]; omega)
    · refine (card_le_card_of_injOn (t := {x.1, x.2}) _ (fun y hy => ?_) (hinj x)).trans
        (by simpa using card_le_two)
      obtain ⟨-, h1, h2⟩ := mem_filter.mp hy
      have ha := x.1.ne_zero; have hb := x.2.ne_zero; have hc := y.1.ne_zero
      have hd := y.2.ne_zero
      simp only [Units.val_inv_eq_inv_val] at h2
      field_simp at h2
      have : ((y.1 : ZMod p) - x.1) * (y.1 - x.2) * (x.1 + x.2) = 0 := by
        linear_combination ((x.1 * x.2 : ZMod p) - (x.1 + x.2) * y.1) * h1 - h2
      rcases mul_eq_zero.mp this with h | h
      · rcases mul_eq_zero.mp h with h | h
        · simp [Units.ext (sub_eq_zero.mp h)]
        · simp [Units.ext (sub_eq_zero.mp h)]
      · exact absurd h hs
  have hzero : #{x : (ZMod p)ˣ × (ZMod p)ˣ | (x.1 : ZMod p) + x.2 = 0} ≤ p - 1 := by
    refine (card_le_card_of_injOn (fun x => x.1) (fun _ _ => mem_univ _) ?_).trans
      (by rw [card_univ, hU])
    intro x hx x' hx' h
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx hx'
    refine Prod.ext h (Units.ext ?_)
    have : (x.1 : ZMod p) = x'.1 := congrArg _ h
    linear_combination hx - hx' - this
  calc hyperbolaEnergy p = ∑ x : (ZMod p)ˣ × (ZMod p)ˣ, #(S x) := by
        rw [hyperbolaEnergy, card_filter, Fintype.sum_prod_type]
        simp only [S, card_filter]
    _ ≤ ∑ x : (ZMod p)ˣ × (ZMod p)ˣ, ((if (x.1 : ZMod p) + x.2 = 0 then p - 1 else 0) + 2) :=
        sum_le_sum fun x _ => hcard x
    _ = #{x : (ZMod p)ˣ × (ZMod p)ˣ | (x.1 : ZMod p) + x.2 = 0} * (p - 1) +
          2 * (p - 1) ^ 2 := by
        rw [sum_add_distrib, sum_ite, sum_const_zero, add_zero, sum_const, sum_const, card_univ,
          Fintype.card_prod, hU, smul_eq_mul, smul_eq_mul]
        ring
    _ ≤ (p - 1) * (p - 1) + 2 * (p - 1) ^ 2 := by gcongr
    _ = 3 * (p - 1) ^ 2 := by ring

/-- **Kloosterman's bound** (1926): `|S(ψ; m, n)|⁴ ≤ 3p³` for a prime `p`, a primitive `ψ` and
`(m, n) ≠ (0, 0)`. By symmetry take `m ≠ 0`; then the `p − 1` pairs `(a, a⁻¹ m n)` with `a ≠ 0` all
have the Kloosterman sum `S(ψ; m, n)`, so the fourth moment is at least `(p − 1) |S(ψ; m, n)|⁴`; it
is `p² · hyperbolaEnergy p ≤ 3p² (p − 1)²`. -/
theorem norm_kloostermanSum_pow_four_le {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive)
    {m n : ZMod p} (h : m ≠ 0 ∨ n ≠ 0) :
    ‖kloostermanSum ψ m n‖ ^ 4 ≤ 3 * p ^ 3 := by
  wlog hm : m ≠ 0 generalizing m n
  · rw [kloostermanSum_comm]
    have hn := h.resolve_left hm
    exact this (Or.inl hn) hn
  have hp := (Fact.out : p.Prime)
  have hconst : ∀ a : ZMod p, a ≠ 0 →
      kloostermanSum ψ a (a⁻¹ * (m * n)) = kloostermanSum ψ m n := fun a ha => by
    rw [show a = (Units.mk0 a ha : ZMod p) from rfl, kloostermanSum_units_left,
      show m = (Units.mk0 m hm : ZMod p) from rfl, kloostermanSum_units_left]
    simp [ha]
  have hlow : (p - 1 : ℝ) * ‖kloostermanSum ψ m n‖ ^ 4 ≤
      ∑ a, ∑ b, ‖kloostermanSum ψ a b‖ ^ 4 :=
    calc (p - 1 : ℝ) * ‖kloostermanSum ψ m n‖ ^ 4
        = ∑ a ∈ univ.erase 0, ‖kloostermanSum ψ a (a⁻¹ * (m * n))‖ ^ 4 := by
          rw [sum_congr rfl fun a ha => by rw [hconst a (ne_of_mem_erase ha)], sum_const,
            card_erase_of_mem (mem_univ _), card_univ, ZMod.card, nsmul_eq_mul,
            Nat.cast_sub hp.one_le, Nat.cast_one]
      _ ≤ ∑ a, ‖kloostermanSum ψ a (a⁻¹ * (m * n))‖ ^ 4 :=
          sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun _ _ _ => by positivity
      _ ≤ ∑ a, ∑ b, ‖kloostermanSum ψ a b‖ ^ 4 :=
          sum_le_sum fun a _ => single_le_sum (f := fun b => ‖kloostermanSum ψ a b‖ ^ 4)
            (fun _ _ => by positivity) (mem_univ _)
  have hE : (hyperbolaEnergy p : ℝ) ≤ 3 * (p - 1) ^ 2 := by
    have := hyperbolaEnergy_le (p := p)
    rw [← Nat.cast_le (α := ℝ)] at this
    push_cast [hp.one_le] at this
    exact this
  rw [sum_norm_kloostermanSum_pow_four hψ] at hlow
  have hp1 : (0 : ℝ) < p - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  nlinarith [norm_nonneg (kloostermanSum ψ m n), sq_nonneg ((p : ℝ) - 1),
    mul_le_mul_of_nonneg_left hE (sq_nonneg (p : ℝ))]

/-- Kloosterman's bound in the form `|S(ψ; m, n)| ≤ 3^(1/4) p^(3/4)`. -/
theorem norm_kloostermanSum_le {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive)
    {m n : ZMod p} (h : m ≠ 0 ∨ n ≠ 0) :
    ‖kloostermanSum ψ m n‖ ≤ 3 ^ (1 / 4 : ℝ) * p ^ (3 / 4 : ℝ) := by
  calc ‖kloostermanSum ψ m n‖ = (‖kloostermanSum ψ m n‖ ^ 4) ^ (1 / 4 : ℝ) := by
        rw [show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num,
          Real.pow_rpow_inv_natCast (norm_nonneg _) (by norm_num)]
    _ ≤ (3 * p ^ 3 : ℝ) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (norm_kloostermanSum_pow_four_le hψ h)
          (by norm_num)
    _ = 3 ^ (1 / 4 : ℝ) * p ^ (3 / 4 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
          ← Real.rpow_mul (Nat.cast_nonneg _)]
        norm_num

end Prime
