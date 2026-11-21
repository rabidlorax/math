module

public import Mathlib

/-!
# Gauss congruences

A sequence `f : ℕ → ℤ` satisfies the **Gauss congruences** if

`n ∣ ∑_{d ∣ n} μ(d) * f(n / d)` for every `n`.

The model example is `f(n) = aⁿ`: for `n = p` prime the condition is Fermat's little theorem
`p ∣ aᵖ - a`, so the Gauss congruences for `aⁿ` extend it to every modulus. Another example is
the number of fixed points of the `n`-th iterate of a self-map of a finite set. Such sequences
are also called Dold sequences or Fermat sequences. They appear in dynamics, in the theory of
Witt vectors and necklace rings, and in counting irreducible polynomials over finite fields.
Mathlib has none of this.

## Main definitions

* `IsGaussSeq f`   : `f` satisfies the Gauss congruences.
* `orbitCount f n` : `(∑_{d ∣ n} μ(d) * f(n / d)) / n`. For fixed-point counts and `n > 0`,
  the number of periodic orbits of length `n`.
* `gaussSubring`   : the subring of `ℕ → ℤ` of sequences satisfying the Gauss congruences.
* `periodicOrbits T n` : the periodic orbits of length `n` of a self-map `T`.
* `necklace a n`   : the necklace number `(∑_{d ∣ n} μ(d) * a ^ (n / d)) / n`.

## Main results

* `isGaussSeq_iff_exists` : `f` satisfies the Gauss congruences if and only if
  `f(n) = ∑_{d ∣ n} d * h(d)` for some `h : ℕ → ℤ` and all `n > 0`; then
  `h(n) = orbitCount f n` for `n > 0` (`orbitCount_eq_of_sum_eq`).
* `isGaussSeq_iff_modEq`  : `f` satisfies them if and only if
  `f(p ^ (k + 1) * m) ≡ f(p ^ k * m) [ZMOD p ^ (k + 1)]` for all primes `p` and all `k`, `m`.
* `gaussSubring`, `IsGaussSeq.comp_mul` : closure under sums, products and `n ↦ f(r * n)`.
* `IsGaussSeq.sum_totient_mul` : `∑_{d ∣ n} φ(d) * f(n / d) = n * ∑_{d ∣ n} orbitCount f d`.
* `isGaussSeq_pow` : `n ∣ ∑_{d ∣ n} μ(d) * a ^ (n / d)` for every integer `a`.
* `isGaussSeq_card_fixedPoints`, `orbitCount_card_fixedPoints` : the fixed-point counts of the
  iterates of a self-map of a finite set satisfy the Gauss congruences, and their `orbitCount`
  is the number of periodic orbits of each length `n > 0`.
* `sum_mul_necklace`, `necklace_prime`, `sum_totient_mul_pow` : the necklace numbers.
-/
@[expose] public section

open Finset ArithmeticFunction Function
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta Nat

/-- `f` satisfies the Gauss congruences: `n ∣ ∑_{d ∣ n} μ(d) * f(n / d)` for every `n`. -/
def IsGaussSeq (f : ℕ → ℤ) : Prop :=
  ∀ n : ℕ, (n : ℤ) ∣ ∑ d ∈ n.divisors, μ d * f (n / d)

/-- `orbitCount f n = (∑_{d ∣ n} μ(d) * f(n / d)) / n`, using integer division. The division is
exact when `f` satisfies the Gauss congruences. -/
def orbitCount (f : ℕ → ℤ) (n : ℕ) : ℤ :=
  (∑ d ∈ n.divisors, μ d * f (n / d)) / n

variable {f g : ℕ → ℤ}

/-! ### Two characterisations -/

/-- Möbius inversion: for `n > 0`, `∑_{d ∣ n} ∑_{e ∣ d} μ(e) * f(d / e) = f(n)`. -/
theorem sum_sum_moebius_mul (f : ℕ → ℤ) {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, ∑ e ∈ d.divisors, μ e * f (d / e) = f n := by
  refine (sum_eq_iff_sum_mul_moebius_eq (f := fun d => ∑ e ∈ d.divisors, μ e * f (d / e))
    (g := f)).mpr (fun d _ => ?_) n hn
  simp [Nat.sum_divisorsAntidiagonal (fun a b => (μ a : ℤ) * f b)]

/-- Möbius inversion: if `f(n) = ∑_{d ∣ n} d * h(d)` for all `n > 0`, then
`∑_{d ∣ n} μ(d) * f(n / d) = n * h(n)` for all `n`. -/
theorem sum_moebius_mul_eq_of_sum_eq {h : ℕ → ℤ}
    (hh : ∀ n, 0 < n → ∑ d ∈ n.divisors, d * h d = f n) (n : ℕ) :
    ∑ d ∈ n.divisors, μ d * f (n / d) = n * h n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have := (sum_eq_iff_sum_mul_moebius_eq (f := fun d => (d : ℤ) * h d) (g := f)).mp hh n hn
  simpa [Nat.sum_divisorsAntidiagonal (fun a b => (μ a : ℤ) * f b)] using this

/-- If `f(n) = ∑_{d ∣ n} d * h(d)` for all `n > 0`, then `orbitCount f n = h(n)` for `n > 0`. -/
theorem orbitCount_eq_of_sum_eq {h : ℕ → ℤ}
    (hh : ∀ n, 0 < n → ∑ d ∈ n.divisors, d * h d = f n) {n : ℕ} (hn : 0 < n) :
    orbitCount f n = h n := by
  rw [orbitCount, sum_moebius_mul_eq_of_sum_eq hh,
    Int.mul_ediv_cancel_left _ (by exact_mod_cast hn.ne')]

/-- For a sequence satisfying the Gauss congruences the division in `orbitCount` is exact. -/
theorem IsGaussSeq.mul_orbitCount (hf : IsGaussSeq f) (n : ℕ) :
    n * orbitCount f n = ∑ d ∈ n.divisors, μ d * f (n / d) :=
  Int.mul_ediv_cancel' (hf n)

/-- `f(n) = ∑_{d ∣ n} d * orbitCount f d` for `n > 0`. -/
theorem IsGaussSeq.sum_mul_orbitCount (hf : IsGaussSeq f) {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, d * orbitCount f d = f n := by
  simp_rw [hf.mul_orbitCount]
  exact sum_sum_moebius_mul f hn

/-- `f` satisfies the Gauss congruences if and only if `f(n) = ∑_{d ∣ n} d * h(d)` for some
`h : ℕ → ℤ` and all `n > 0`. Then `h = orbitCount f` on positive integers
(`orbitCount_eq_of_sum_eq`). -/
theorem isGaussSeq_iff_exists :
    IsGaussSeq f ↔ ∃ h : ℕ → ℤ, ∀ n, 0 < n → ∑ d ∈ n.divisors, d * h d = f n := by
  refine ⟨fun hf => ⟨orbitCount f, fun n hn => hf.sum_mul_orbitCount hn⟩, fun ⟨h, hh⟩ n => ?_⟩
  exact ⟨h n, sum_moebius_mul_eq_of_sum_eq hh n⟩

/-- If `d ∣ p * m` but `d ∤ m` for a prime `p`, then every power of `p` dividing `p * m`
divides `d`. -/
theorem Nat.Prime.pow_dvd_of_dvd_mul_of_not_dvd {p m d k : ℕ} (hp : p.Prime) (hd : d ∣ p * m)
    (hdm : ¬d ∣ m) (hk : p ^ k ∣ p * m) : p ^ k ∣ d := by
  obtain ⟨c, hc⟩ := hd
  have hpc : ¬p ∣ c := by
    rintro ⟨c', rfl⟩
    exact hdm ⟨c', Nat.eq_of_mul_eq_mul_left hp.pos (by rw [hc]; ring)⟩
  exact (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpc)).dvd_of_dvd_mul_right
    (hc ▸ hk)

/-- **Euler congruences**: `f` satisfies the Gauss congruences if and only if
`f(p ^ (k + 1) * m) ≡ f(p ^ k * m) [ZMOD p ^ (k + 1)]` for every prime `p` and all `k`, `m`. -/
theorem isGaussSeq_iff_modEq :
    IsGaussSeq f ↔
      ∀ p k m : ℕ, p.Prime → f (p ^ (k + 1) * m) ≡ f (p ^ k * m) [ZMOD p ^ (k + 1)] := by
  constructor
  · intro hf p k m hp
    rcases m.eq_zero_or_pos with rfl | hm
    · simp
    have := hp.pos
    have hM : p ^ k * m ≠ 0 := by positivity
    have hN : p ^ (k + 1) * m = p * (p ^ k * m) := by ring
    refine (Int.modEq_iff_dvd.mpr ?_).symm
    rw [← hf.sum_mul_orbitCount (by positivity : 0 < p ^ (k + 1) * m),
      ← hf.sum_mul_orbitCount (Nat.pos_of_ne_zero hM), hN,
      ← sum_sdiff (Nat.divisors_subset_of_dvd (by positivity) (dvd_mul_left _ _)),
      add_sub_cancel_right]
    refine dvd_sum fun d hd => ?_
    rw [mem_sdiff, Nat.mem_divisors, Nat.mem_divisors] at hd
    have := hp.pow_dvd_of_dvd_mul_of_not_dvd hd.1.1 (fun h => hd.2 ⟨h, hM⟩)
      (hN ▸ dvd_mul_right _ _)
    exact Dvd.dvd.mul_right (by exact_mod_cast this) _
  · intro H n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    rcases n.eq_zero_or_pos with rfl | hn
    · simp
    rw [Int.natCast_dvd, Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpk
    rw [← Int.natCast_dvd, Nat.cast_pow]
    rcases k with _ | k
    · simp
    obtain ⟨m, rfl⟩ := hpk
    have hm : m ≠ 0 := by rintro rfl; simp at hn
    have hM : p ^ k * m ≠ 0 := by have := hp.pos; positivity
    have hN : p ^ (k + 1) * m = p * (p ^ k * m) := by ring
    have hdvd : p ^ k * m ∣ p ^ (k + 1) * m := ⟨p, by ring⟩
    have hlt : p ^ k * m < p ^ (k + 1) * m :=
      hN ▸ lt_mul_left (Nat.pos_of_ne_zero hM) hp.one_lt
    have hmem : p ^ (k + 1) * m ∈ (p ^ (k + 1) * m).divisors \ (p ^ k * m).divisors := by
      simp only [mem_sdiff, Nat.mem_divisors, dvd_refl, ne_eq, true_and, not_and, not_not]
      exact ⟨hn.ne', fun h => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) h) hlt.not_ge⟩
    have key := (H p k m hp).symm.dvd
    rw [← sum_sum_moebius_mul f hn, ← sum_sum_moebius_mul f (Nat.pos_of_ne_zero hM),
      ← sum_sdiff (Nat.divisors_subset_of_dvd hn.ne' hdvd),
      add_sub_cancel_right, ← add_sum_erase _ _ hmem] at key
    refine (dvd_add_left (dvd_sum fun d hd => ?_)).mp key
    simp only [mem_erase, mem_sdiff, Nat.mem_divisors] at hd
    obtain ⟨hne, ⟨hdN, -⟩, hdM⟩ := hd
    have hpd := hp.pow_dvd_of_dvd_mul_of_not_dvd (hN ▸ hdN) (fun h => hdM ⟨h, hM⟩)
      (⟨m, by ring⟩ : p ^ (k + 1) ∣ p * (p ^ k * m))
    have := (Int.natCast_dvd_natCast.mpr hpd).trans
      (ih d (lt_of_le_of_ne (Nat.le_of_dvd hn hdN) hne))
    push_cast at this
    exact this

/-! ### Closure properties -/

/-- The sequences satisfying the Gauss congruences form a subring of `ℕ → ℤ`. -/
def gaussSubring : Subring (ℕ → ℤ) where
  carrier := {f | IsGaussSeq f}
  mul_mem' hf hg := isGaussSeq_iff_modEq.mpr fun p k m hp =>
    (isGaussSeq_iff_modEq.mp hf p k m hp).mul (isGaussSeq_iff_modEq.mp hg p k m hp)
  one_mem' := isGaussSeq_iff_modEq.mpr fun _ _ _ _ => rfl
  add_mem' hf hg := isGaussSeq_iff_modEq.mpr fun p k m hp =>
    (isGaussSeq_iff_modEq.mp hf p k m hp).add (isGaussSeq_iff_modEq.mp hg p k m hp)
  zero_mem' := isGaussSeq_iff_modEq.mpr fun _ _ _ _ => rfl
  neg_mem' hf := isGaussSeq_iff_modEq.mpr fun p k m hp =>
    (isGaussSeq_iff_modEq.mp hf p k m hp).neg

@[simp] theorem mem_gaussSubring : f ∈ gaussSubring ↔ IsGaussSeq f := Iff.rfl

theorem isGaussSeq_const (c : ℤ) : IsGaussSeq fun _ => c :=
  isGaussSeq_iff_modEq.mpr fun _ _ _ _ => rfl

theorem IsGaussSeq.add (hf : IsGaussSeq f) (hg : IsGaussSeq g) : IsGaussSeq (f + g) :=
  gaussSubring.add_mem hf hg

theorem IsGaussSeq.neg (hf : IsGaussSeq f) : IsGaussSeq (-f) :=
  gaussSubring.neg_mem hf

theorem IsGaussSeq.sub (hf : IsGaussSeq f) (hg : IsGaussSeq g) : IsGaussSeq (f - g) :=
  gaussSubring.sub_mem hf hg

theorem IsGaussSeq.mul (hf : IsGaussSeq f) (hg : IsGaussSeq g) : IsGaussSeq (f * g) :=
  gaussSubring.mul_mem hf hg

/-- If `f` satisfies the Gauss congruences, so does `n ↦ f(r * n)`. -/
theorem IsGaussSeq.comp_mul (hf : IsGaussSeq f) (r : ℕ) : IsGaussSeq fun n => f (r * n) :=
  isGaussSeq_iff_modEq.mpr fun p k m hp => by
    simpa only [mul_left_comm r] using isGaussSeq_iff_modEq.mp hf p k (r * m) hp

/-! ### Burnside's formula -/

/-- `∑_{d ∣ n} φ(d) * f(n / d) = n * ∑_{d ∣ n} orbitCount f d`. So `n` divides the left side. -/
theorem IsGaussSeq.sum_totient_mul (hf : IsGaussSeq f) (n : ℕ) :
    ∑ d ∈ n.divisors, (φ d : ℤ) * f (n / d) = n * ∑ d ∈ n.divisors, orbitCount f d := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  let O : ArithmeticFunction ℤ := ⟨fun d => d * orbitCount f d, by simp⟩
  let Φ : ArithmeticFunction ℤ := ⟨fun d => φ d, by simp⟩
  have h : (Φ * ζ * O) n = (Φ * (ζ * O)) n := by rw [mul_assoc]
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply] at h
  rw [← Nat.sum_divisorsAntidiagonal (fun a b => (φ a : ℤ) * f b), mul_sum,
    ← Nat.sum_divisorsAntidiagonal' (fun _ b => (n : ℤ) * orbitCount f b)]
  calc _ = ∑ x ∈ n.divisorsAntidiagonal, Φ x.1 * (ζ * O) x.2 := by
        refine sum_congr rfl fun x hx => ?_
        rw [coe_zeta_mul_apply]
        simp only [O, Φ, coe_mk]
        rw [hf.sum_mul_orbitCount
          (Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx))]
    _ = ∑ x ∈ n.divisorsAntidiagonal, (Φ * ζ) x.1 * O x.2 := h.symm
    _ = _ := by
        refine sum_congr rfl fun x hx => ?_
        rw [coe_mul_zeta_apply]
        have : ∑ i ∈ x.1.divisors, Φ i = x.1 := by
          simp only [Φ, coe_mk]; exact_mod_cast Nat.sum_totient x.1
        rw [this, ← (Nat.mem_divisorsAntidiagonal.mp hx).1]
        simp only [O, coe_mk]
        push_cast; ring

/-! ### Powers -/

/-- `n ∣ ∑_{d ∣ n} μ(d) * a ^ (n / d)` for every integer `a`. For `n = p` prime this is
Fermat's little theorem `p ∣ a ^ p - a`. -/
theorem isGaussSeq_pow (a : ℤ) : IsGaussSeq (a ^ ·) := by
  refine isGaussSeq_iff_modEq.mpr fun p k m hp => ?_
  rw [show p ^ (k + 1) * m = m * p * p ^ k by ring, show p ^ k * m = m * p ^ k by ring,
    pow_mul, pow_mul, pow_mul]
  exact (Int.modEq_iff_dvd.mpr (by
    simpa using dvd_sub_pow_of_dvd_sub (Int.ModEq.pow_prime_eq_self hp (a ^ m)).symm.dvd k)).symm

/-! ### Periodic points -/

section PeriodicPts

variable {α : Type*} [Fintype α] [DecidableEq α] (T : α → α)

/-- The periodic orbits of `T` of length `n`. For `n = 0` this is `{Cycle.nil}` if some point
is not periodic, and `∅` otherwise. -/
noncomputable def periodicOrbits (n : ℕ) : Finset (Cycle α) :=
  (univ.filter fun x => minimalPeriod T x = n).image (periodicOrbit T)

omit [Fintype α] in
/-- The orbit of `x` has `minimalPeriod T x` elements (none if `x` is not periodic). -/
theorem card_toFinset_periodicOrbit (x : α) :
    #(periodicOrbit T x).toFinset = minimalPeriod T x := by
  rw [periodicOrbit_def, Cycle.coe_toFinset, List.toFinset_card_of_nodup, List.length_map,
    List.length_range]
  exact Cycle.nodup_coe_iff.mp nodup_periodicOrbit

omit [Fintype α] in
/-- Membership in the orbit as a `Finset`. -/
private theorem mem_toFinset_periodicOrbit {x y : α} :
    x ∈ (periodicOrbit T y).toFinset ↔ x ∈ periodicOrbit T y := by
  rw [periodicOrbit_def, Cycle.coe_toFinset, List.mem_toFinset, Cycle.mem_coe_iff]

/-- The points of minimal period `n > 0` fall into `#(periodicOrbits T n)` orbits of size `n`. -/
theorem card_minimalPeriod_eq {n : ℕ} (hn : 0 < n) :
    #{x | minimalPeriod T x = n} = n * #(periodicOrbits T n) := by
  rw [card_eq_sum_card_fiberwise (f := periodicOrbit T) (t := periodicOrbits T n)
    (fun x hx => mem_image_of_mem _ hx), mul_comm]
  refine sum_const_nat fun c hc => ?_
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hc
  rw [mem_filter_univ y] at hy
  have hyp : y ∈ periodicPts T := minimalPeriod_pos_iff_mem_periodicPts.mp (hy ▸ hn)
  refine (congrArg card ?_).trans ((card_toFinset_periodicOrbit T y).trans hy)
  ext x
  simp only [mem_filter, mem_univ, true_and, mem_toFinset_periodicOrbit, mem_periodicOrbit_iff hyp]
  constructor
  · rintro ⟨hx, hxy⟩
    have hxp : x ∈ periodicPts T := minimalPeriod_pos_iff_mem_periodicPts.mp (hx ▸ hn)
    rw [← mem_periodicOrbit_iff hyp, ← hxy]
    exact self_mem_periodicOrbit hxp
  · rintro ⟨k, rfl⟩
    exact ⟨(minimalPeriod_apply_iterate hyp k).trans hy, periodicOrbit_apply_iterate_eq hyp k⟩

/-- For `n > 0`, `#{x | T^[n] x = x} = ∑_{d ∣ n} #{x | minimalPeriod T x = d}`, since the fixed
points of `T^[n]` are the points whose minimal period divides `n`. -/
theorem card_fixedPoints_iterate {n : ℕ} (hn : 0 < n) :
    #{x | T^[n] x = x} = ∑ d ∈ n.divisors, #{x | minimalPeriod T x = d} := by
  rw [card_eq_sum_card_fiberwise (f := minimalPeriod T) (s := {x | T^[n] x = x})
    (t := n.divisors) fun x hx => Nat.mem_divisors.mpr
      ⟨IsPeriodicPt.minimalPeriod_dvd ((mem_filter_univ x).mp hx), hn.ne'⟩]
  refine sum_congr rfl fun d hd => ?_
  rw [filter_filter]
  refine congrArg card (filter_congr fun x _ => ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩)
  exact isPeriodicPt_iff_minimalPeriod_dvd.mpr (h ▸ Nat.dvd_of_mem_divisors hd)

/-- `#{x | T^[n] x = x} = ∑_{d ∣ n} d * #(periodicOrbits T d)` for `n > 0`. -/
theorem sum_mul_card_periodicOrbits {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, (d : ℤ) * #(periodicOrbits T d) = #{x | T^[n] x = x} := by
  rw [card_fixedPoints_iterate T hn]
  push_cast
  exact sum_congr rfl fun d hd => by
    rw [card_minimalPeriod_eq T (Nat.pos_of_mem_divisors hd)]; push_cast; rfl

/-- **Dold's congruences** for finite sets: the numbers of fixed points of the iterates of a
self-map of a finite set satisfy the Gauss congruences. -/
theorem isGaussSeq_card_fixedPoints : IsGaussSeq fun n => (#{x | T^[n] x = x} : ℤ) :=
  isGaussSeq_iff_exists.mpr ⟨_, fun _ hn => sum_mul_card_periodicOrbits T hn⟩

/-- `orbitCount` of the fixed-point counts is the number of periodic orbits of length `n`, for
`n > 0`. -/
theorem orbitCount_card_fixedPoints {n : ℕ} (hn : 0 < n) :
    orbitCount (fun n => (#{x | T^[n] x = x} : ℤ)) n = #(periodicOrbits T n) :=
  orbitCount_eq_of_sum_eq (fun _ hn => sum_mul_card_periodicOrbits T hn) hn

end PeriodicPts

/-! ### Necklace numbers -/

/-- The necklace number `M(a, n) = (∑_{d ∣ n} μ(d) * a ^ (n / d)) / n`, an exact division.
For `a ≥ 0` it classically counts the aperiodic necklaces of `n` beads in `a` colours, and for
`a` a prime power the monic irreducible polynomials of degree `n` over the field with `a`
elements. -/
def necklace (a : ℤ) (n : ℕ) : ℤ := orbitCount (a ^ ·) n

variable (a : ℤ)

/-- `n * M(a, n) = ∑_{d ∣ n} μ(d) * a ^ (n / d)`. -/
theorem mul_necklace (n : ℕ) : n * necklace a n = ∑ d ∈ n.divisors, μ d * a ^ (n / d) :=
  (isGaussSeq_pow a).mul_orbitCount n

/-- `∑_{d ∣ n} d * M(a, d) = a ^ n` for `n > 0`. -/
theorem sum_mul_necklace {n : ℕ} (hn : 0 < n) : ∑ d ∈ n.divisors, d * necklace a d = a ^ n :=
  (isGaussSeq_pow a).sum_mul_orbitCount hn

@[simp] theorem necklace_one : necklace a 1 = a := by simp [necklace, orbitCount]

/-- `p * M(a, p) = a ^ p - a` for a prime `p`. -/
theorem necklace_prime {p : ℕ} (hp : p.Prime) : p * necklace a p = a ^ p - a := by
  rw [mul_necklace, hp.divisors, sum_pair hp.one_lt.ne, moebius_apply_prime hp, Nat.div_one,
    Nat.div_self hp.pos]
  simp [sub_eq_add_neg]

/-- `∑_{d ∣ n} φ(d) * a ^ (n / d) = n * ∑_{d ∣ n} M(a, d)`. For `a ≥ 0` and `n > 0`, dividing by
`n` gives the classical count of all necklaces of `n` beads in `a` colours. -/
theorem sum_totient_mul_pow (n : ℕ) :
    ∑ d ∈ n.divisors, (φ d : ℤ) * a ^ (n / d) = n * ∑ d ∈ n.divisors, necklace a d :=
  (isGaussSeq_pow a).sum_totient_mul n
