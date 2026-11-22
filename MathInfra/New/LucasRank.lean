module

public import MathInfra.FormalizedElsewhere.LucasSeq

/-!
# The rank of apparition of a Lucas sequence

For `P Q` in a commutative ring `R`, the **rank of apparition** of the Lucas sequence
`U = lucasU P Q` is the least `r > 0` with `U r = 0`, or `0` if there is none. Taking
`R = ZMod m` gives the rank of apparition of the integer `m`: the least `n > 0` with `m ∣ U n`
(or `0`). The literature also calls it the rank of appearance, the order of appearance or
the entry point (for Fibonacci numbers, the Fibonacci entry point, called `cofibonacci` in
agda-unimath).

Write `D = P ^ 2 - 4 * Q` for the discriminant.

When `Q` is a unit the rank behaves like the order of an element of a group: `U n = 0` exactly when
the rank divides `n`, and modulo an odd prime `p` the rank divides `p - (D / p)`. This turns the law
of apparition of `MathInfra.FormalizedElsewhere.LucasSeq` into the **Lucas `N + 1` primality test**
(Lehmer 1930, after Lucas 1878), the `N + 1` counterpart of Mathlib's `lucas_primality`: if `N > 1`,
`Q` is prime to `N`, `N ∣ U (N + 1)`, and `U ((N + 1) / q)` is prime to `N` for every prime
`q ∣ N + 1`, then `N` is prime. When `Q` is a unit, every solution over a finite ring is purely
periodic, and the least period of `U` is the rank `r` times the multiplicative order of `U (r + 1)`;
for Fibonacci numbers modulo `m` this is the Pisano period.

## Main definitions

* `lucasRank P Q` : the rank of apparition.
* `lucasPeriod P Q` : `lucasRank P Q * orderOf (U (lucasRank P Q + 1))`, the period of `U`.
* `IsLucasProbablePrime P Q N`, `IsLucasPsp P Q N` : `N ∣ U (N - (D / N))` with the Jacobi
  symbol, and the composite `N` prime to `2 * Q * D` that satisfy it (Lucas pseudoprimes).

## Main results

* `IsLucasRec.add_of_lucasU_eq_zero` : if `U r = 0` then every solution `W` of the recurrence
  satisfies `W (n + r) = U (r + 1) * W n`.
* `lucasU_eq_zero_iff_lucasRank_dvd` : if `Q` is a unit, `U n = 0 ↔ lucasRank P Q ∣ n`.
* `lucasRank_map_dvd`, `lucasRank_map_of_injective`, `lucasRank_prod` : behaviour under ring
  homomorphisms and products, so the rank of `m * n` is the `lcm` for coprime `m`, `n` prime to `Q`.
* `lucasRank_pos`, `lucasPeriod_pos` : over a finite ring with `Q` a unit, the rank and the
  period are positive.
* `IsLucasRec.periodic`, `periodic_lucasU_iff` : every solution has period `lucasPeriod P Q`,
  and when `Q` is a unit the periods of `U` are exactly its multiples.
* `ZMod.lucasRank_dvd_sub_legendreSym`, `ZMod.lucasRank_le` : modulo an odd prime `p ∤ Q`
  the rank divides `p - (D / p)`, and modulo any prime `p ∤ Q` it is at most `p + 1`.
* `lucasU_primality` : the Lucas `N + 1` primality test.
* `Nat.Prime.isLucasProbablePrime` : odd primes `p ∤ Q` are Lucas probable primes.
-/

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S] (P Q : R)

/-! ### A zero of `U` -/

variable {P Q} in
/-- If `U r = 0`, shifting any solution of the recurrence by `r` multiplies it by `U (r + 1)`. -/
theorem IsLucasRec.add_of_lucasU_eq_zero {W : ℕ → R} (h : IsLucasRec P Q W) {r : ℕ}
    (hr : lucasU P Q r = 0) (n : ℕ) : W (n + r) = lucasU P Q (r + 1) * W n := by
  cases n with
  | zero =>
    cases r with
    | zero => simp
    | succ r =>
      have e := h.eq_lucasU r
      have u := lucasU_add_two P Q r
      rw [zero_add, show r + 1 + 1 = r + 2 from rfl]
      rw [hr] at e u
      linear_combination e - W 0 * u
  | succ k =>
    rw [show k + 1 + r = k + r + 1 by omega, h.add_succ k r, hr]
    ring

variable {P Q} in
/-- If `U r = 0`, then `W (n + k * r) = U (r + 1) ^ k * W n` for every solution `W`. -/
theorem IsLucasRec.add_mul_of_lucasU_eq_zero {W : ℕ → R} (h : IsLucasRec P Q W) {r : ℕ}
    (hr : lucasU P Q r = 0) (n k : ℕ) : W (n + k * r) = lucasU P Q (r + 1) ^ k * W n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show n + (k + 1) * r = n + k * r + r by ring, h.add_of_lucasU_eq_zero hr, ih]
    ring

/-- If `U r = 0` then `U (r + 1) ^ 2 = Q ^ r`, by Cassini's identity. -/
theorem lucasU_succ_sq_of_lucasU_eq_zero {r : ℕ} (hr : lucasU P Q r = 0) :
    lucasU P Q (r + 1) ^ 2 = Q ^ r := by
  simpa [hr] using lucasU_cassini P Q r

variable {P Q} in
/-- If `Q` is a unit and `U r = 0`, then `U (r + 1)` is a unit. -/
theorem isUnit_lucasU_succ (hQ : IsUnit Q) {r : ℕ} (hr : lucasU P Q r = 0) :
    IsUnit (lucasU P Q (r + 1)) :=
  (isUnit_pow_iff two_ne_zero).mp (lucasU_succ_sq_of_lucasU_eq_zero P Q hr ▸ hQ.pow r)

/-! ### The rank of apparition -/

/-- The **rank of apparition**: the least `r > 0` with `U r = 0`, or `0` if there is none. -/
noncomputable def lucasRank : ℕ := sInf {r | 0 < r ∧ lucasU P Q r = 0}

@[simp] theorem lucasU_lucasRank : lucasU P Q (lucasRank P Q) = 0 := by
  rcases Nat.eq_zero_or_pos (lucasRank P Q) with h | h
  · rw [h, lucasU_zero]
  · exact (Nat.sInf_mem (Nat.nonempty_of_pos_sInf h)).2

/-- The rank is `0` exactly when `U n ≠ 0` for every `n > 0`. -/
theorem lucasRank_eq_zero_iff : lucasRank P Q = 0 ↔ ∀ n, 0 < n → lucasU P Q n ≠ 0 := by
  rw [lucasRank, Nat.sInf_eq_zero, Set.eq_empty_iff_forall_notMem]
  simp only [Set.mem_ofPred_eq, lt_irrefl, false_and, false_or, not_and]

theorem lucasU_ne_zero_of_lt_lucasRank {n : ℕ} (hn : 0 < n) (h : n < lucasRank P Q) :
    lucasU P Q n ≠ 0 :=
  fun h0 => Nat.notMem_of_lt_sInf h ⟨hn, h0⟩

/-- The rank is `r` if `r > 0`, `U r = 0` and `U m ≠ 0` for `0 < m < r`. -/
theorem lucasRank_eq {r : ℕ} (hr : 0 < r) (h : lucasU P Q r = 0)
    (hmin : ∀ m < r, 0 < m → lucasU P Q m ≠ 0) : lucasRank P Q = r := by
  refine le_antisymm (Nat.sInf_le ⟨hr, h⟩) (le_of_not_gt fun hlt => ?_)
  have hpos : 0 < lucasRank P Q :=
    Nat.pos_of_ne_zero fun h0 => (lucasRank_eq_zero_iff P Q).mp h0 r hr h
  exact hmin _ hlt hpos (lucasU_lucasRank P Q)

variable {P Q} in
/-- **The rank of apparition divides every zero.** If `Q` is a unit then `U n = 0` if and
only if `lucasRank P Q ∣ n`. -/
theorem lucasU_eq_zero_iff_lucasRank_dvd (hQ : IsUnit Q) {n : ℕ} :
    lucasU P Q n = 0 ↔ lucasRank P Q ∣ n := by
  set r := lucasRank P Q
  have hU := (isLucasRec_lucasU P Q).add_mul_of_lucasU_eq_zero (lucasU_lucasRank P Q)
  have hc := (isUnit_lucasU_succ hQ (lucasU_lucasRank P Q)).pow (n / r)
  have key : lucasU P Q n = lucasU P Q (r + 1) ^ (n / r) * lucasU P Q (n % r) := by
    conv_lhs => rw [← Nat.mod_add_div' n r]
    exact hU _ _
  rw [key, hc.mul_right_eq_zero, Nat.dvd_iff_mod_eq_zero]
  rcases Nat.eq_zero_or_pos r with hr | hr
  · rw [hr, Nat.mod_zero]
    refine ⟨fun h0 => ?_, fun h0 => by rw [h0, lucasU_zero]⟩
    by_contra hn
    exact (lucasRank_eq_zero_iff P Q).mp hr n (Nat.pos_of_ne_zero hn) h0
  · constructor
    · intro h0
      by_contra hn
      exact lucasU_ne_zero_of_lt_lucasRank P Q (Nat.pos_of_ne_zero hn) (Nat.mod_lt n hr) h0
    · intro h0; rw [h0, lucasU_zero]

/-! ### Ring homomorphisms and products -/

variable {P Q} in
/-- Zeros of `U` survive a ring homomorphism `f`, so if `f Q` is a unit then the rank after
`f` divides the rank before. -/
theorem lucasRank_map_dvd (f : R →+* S) (hQ : IsUnit (f Q)) :
    lucasRank (f P) (f Q) ∣ lucasRank P Q :=
  (lucasU_eq_zero_iff_lucasRank_dvd hQ).mp (by rw [← map_lucasU, lucasU_lucasRank, map_zero])

/-- An injective ring homomorphism does not change the rank. -/
theorem lucasRank_map_of_injective (f : R →+* S) (hf : Function.Injective f) :
    lucasRank (f P) (f Q) = lucasRank P Q := by
  simp only [lucasRank, ← map_lucasU, map_eq_zero_iff f hf]

theorem lucasU_prod {P' Q' : S} (n : ℕ) :
    lucasU ((P, P') : R × S) (Q, Q') n = (lucasU P Q n, lucasU P' Q' n) := by
  ext
  · simpa using map_lucasU ((P, P') : R × S) (Q, Q') (RingHom.fst R S) n
  · simpa using map_lucasU ((P, P') : R × S) (Q, Q') (RingHom.snd R S) n

variable {P Q} in
/-- If `Q` and `Q'` are units, the rank in `R × S` is the `lcm` of the ranks. -/
theorem lucasRank_prod {P' Q' : S} (hQ : IsUnit Q) (hQ' : IsUnit Q') :
    lucasRank ((P, P') : R × S) (Q, Q') = Nat.lcm (lucasRank P Q) (lucasRank P' Q') := by
  have hQQ : IsUnit ((Q, Q') : R × S) := Prod.isUnit_iff.mpr ⟨hQ, hQ'⟩
  refine Nat.dvd_right_iff_eq.mp fun n => ?_
  rw [← lucasU_eq_zero_iff_lucasRank_dvd hQQ, Nat.lcm_dvd_iff,
    ← lucasU_eq_zero_iff_lucasRank_dvd hQ, ← lucasU_eq_zero_iff_lucasRank_dvd hQ', lucasU_prod,
    Prod.mk_eq_zero]

/-! ### Periodicity -/

/-- The **period** of `U`: `lucasRank P Q * orderOf (U (lucasRank P Q + 1))`. For Fibonacci
numbers modulo `m` this is the Pisano period. -/
noncomputable def lucasPeriod : ℕ := lucasRank P Q * orderOf (lucasU P Q (lucasRank P Q + 1))

variable {P Q} in
/-- Every solution of the recurrence has period `lucasPeriod P Q`. -/
theorem IsLucasRec.periodic {W : ℕ → R} (h : IsLucasRec P Q W) :
    Function.Periodic W (lucasPeriod P Q) := fun n => by
  rw [lucasPeriod, mul_comm, h.add_mul_of_lucasU_eq_zero (lucasU_lucasRank P Q),
    pow_orderOf_eq_one, one_mul]

variable {P Q} in
/-- If `Q` is a unit, the periods of `U` are exactly the multiples of `lucasPeriod P Q`. -/
theorem periodic_lucasU_iff (hQ : IsUnit Q) {T : ℕ} :
    Function.Periodic (lucasU P Q) T ↔ lucasPeriod P Q ∣ T := by
  refine ⟨fun hT => ?_, fun ⟨k, hk⟩ => ?_⟩
  · obtain ⟨k, rfl⟩ := (lucasU_eq_zero_iff_lucasRank_dvd hQ).mp (by simpa using hT 0)
    have h1 := hT 1
    rw [mul_comm, (isLucasRec_lucasU P Q).add_mul_of_lucasU_eq_zero (lucasU_lucasRank P Q),
      lucasU_one, mul_one] at h1
    exact mul_dvd_mul_left _ (orderOf_dvd_of_pow_eq_one h1)
  · simpa [hk, mul_comm] using (isLucasRec_lucasU P Q).periodic.nat_mul k

/-- If `Q` is a unit, the map `(a, b) ↦ (b, P * b - Q * a)` that advances the pair
`(U n, U (n + 1))` is injective. -/
private theorem step_injective (hQ : IsUnit Q) :
    Function.Injective fun x : R × R => (x.2, P * x.2 - Q * x.1) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  exact Prod.ext (hQ.mul_left_cancel (by linear_combination -h)) rfl

variable {P Q} in
/-- Over a finite ring with `Q` a unit, the rank is positive: `U` has a zero `r > 0`. -/
theorem lucasRank_pos [Finite R] (hQ : IsUnit Q) : 0 < lucasRank P Q := by
  have hinj := step_injective P Q hQ
  let σ : Equiv.Perm (R × R) := Equiv.ofBijective _ ⟨hinj, Finite.surjective_of_injective hinj⟩
  have hσ : ∀ n, (σ ^ n) (0, 1) = (lucasU P Q n, lucasU P Q (n + 1)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih]
      rfl
  have h0 : lucasU P Q (orderOf σ) = 0 := by
    have := hσ (orderOf σ)
    rw [pow_orderOf_eq_one] at this
    exact (congrArg Prod.fst this).symm
  refine Nat.pos_of_ne_zero fun hr => (orderOf_pos σ).ne' ?_
  simpa [hr] using (lucasU_eq_zero_iff_lucasRank_dvd hQ).mp h0

variable {P Q} in
/-- Over a finite ring with `Q` a unit, `lucasPeriod P Q > 0`, so every solution is purely
periodic. -/
theorem lucasPeriod_pos [Finite R] (hQ : IsUnit Q) : 0 < lucasPeriod P Q := by
  have hc := isUnit_lucasU_succ hQ (lucasU_lucasRank P Q)
  refine Nat.mul_pos (lucasRank_pos hQ) ?_
  rw [← hc.unit_spec, orderOf_units]
  exact orderOf_pos _

/-! ### Modulo a prime -/

section Prime

variable (p : ℕ) [Fact p.Prime]

/-- Modulo an odd prime `p ∤ Q`, the rank divides `p - (D / p)` (law of apparition). -/
theorem ZMod.lucasRank_dvd_sub_legendreSym (hp : p ≠ 2) (P Q : ℤ) (hQ : ¬ (p : ℤ) ∣ Q) :
    lucasRank (P : ZMod p) (Q : ZMod p) ∣ ((p : ℤ) - legendreSym p (P ^ 2 - 4 * Q)).toNat := by
  have hQ' : IsUnit (Q : ZMod p) :=
    isUnit_iff_ne_zero.mpr fun h => hQ ((ZMod.intCast_zmod_eq_zero_iff_dvd Q p).mp h)
  rw [← lucasU_eq_zero_iff_lucasRank_dvd hQ']
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr
    (prime_dvd_lucasU_sub_legendreSym p hp P Q hQ)
  rw [← h]
  simpa using (map_lucasU P Q (Int.castRingHom (ZMod p)) _).symm

private theorem zmod_two_aux :
    ∀ P Q : ZMod 2, Q ≠ 0 → lucasU P Q 2 = 0 ∨ lucasU P Q 3 = 0 := by
  decide

/-- Modulo a prime `p`, if `Q ≠ 0` the rank is at most `p + 1`. -/
theorem ZMod.lucasRank_le (P Q : ZMod p) (hQ : Q ≠ 0) : lucasRank P Q ≤ p + 1 := by
  have hQ' : IsUnit Q := isUnit_iff_ne_zero.mpr hQ
  obtain rfl | hp := eq_or_ne p 2
  · rcases zmod_two_aux P Q hQ with h | h <;>
      exact (Nat.le_of_dvd (by norm_num) ((lucasU_eq_zero_iff_lucasRank_dvd hQ').mp h)).trans
        (by norm_num)
  · have h := ZMod.lucasRank_dvd_sub_legendreSym p hp P.cast Q.cast
      (fun h => hQ (by rw [← ZMod.intCast_zmod_cast Q, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact h))
    simp only [ZMod.intCast_zmod_cast] at h
    have hp3 : 3 ≤ p := lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp)
    have hL : -1 ≤ legendreSym p ((P.cast : ℤ) ^ 2 - 4 * Q.cast) ∧
        legendreSym p ((P.cast : ℤ) ^ 2 - 4 * Q.cast) ≤ 1 := by
      by_cases h0 : (((P.cast : ℤ) ^ 2 - 4 * Q.cast : ℤ) : ZMod p) = 0
      · rw [(legendreSym.eq_zero_iff p _).mpr h0]; norm_num
      · rcases legendreSym.eq_one_or_neg_one p h0 with h1 | h1 <;> rw [h1] <;> norm_num
    exact (Nat.le_of_dvd (by omega) h).trans (by omega)

end Prime

/-! ### The Lucas `N + 1` primality test -/

/-- If `r ∣ n` but `r ∤ n / q` for every prime `q ∣ n`, then `r = n`. -/
private theorem eq_of_dvd_of_not_dvd_div {r n : ℕ} (hr : r ∣ n)
    (h : ∀ q, q.Prime → q ∣ n → ¬ r ∣ n / q) : r = n := by
  obtain ⟨k, rfl⟩ := hr
  by_contra hne
  have hk : k ≠ 1 := fun hk => hne (by rw [hk, mul_one])
  refine h k.minFac (Nat.minFac_prime hk) (dvd_mul_of_dvd_right (Nat.minFac_dvd k) r) ?_
  rw [Nat.mul_div_assoc r (Nat.minFac_dvd k)]
  exact dvd_mul_right _ _

/-- **The Lucas `N + 1` primality test.** Let `N > 1` and `P, Q ∈ ZMod N` with `Q` a unit. If
`U (N + 1) = 0` and `U ((N + 1) / q)` is a unit for every prime `q ∣ N + 1`, then `N` is prime. -/
theorem lucasU_primality {N : ℕ} (hN : 1 < N) (P Q : ZMod N) (hQ : IsUnit Q)
    (hU : lucasU P Q (N + 1) = 0)
    (hq : ∀ q : ℕ, q.Prime → q ∣ N + 1 → IsUnit (lucasU P Q ((N + 1) / q))) : N.Prime := by
  have hp : N.minFac.Prime := Nat.minFac_prime hN.ne'
  have := Fact.mk hp
  let f : ZMod N →+* ZMod N.minFac := ZMod.castHom (Nat.minFac_dvd N) _
  have hfQ : IsUnit (f Q) := hQ.map f
  have hr : lucasRank (f P) (f Q) = N + 1 := by
    refine eq_of_dvd_of_not_dvd_div ?_ fun q hq' hqd hdvd => ?_
    · rw [← lucasU_eq_zero_iff_lucasRank_dvd hfQ, ← map_lucasU, hU, map_zero]
    · rw [← lucasU_eq_zero_iff_lucasRank_dvd hfQ, ← map_lucasU] at hdvd
      exact ((hq q hq' hqd).map f).ne_zero hdvd
  have hle := ZMod.lucasRank_le N.minFac (f P) (f Q) hfQ.ne_zero
  rw [hr] at hle
  rwa [← le_antisymm (Nat.minFac_le (by omega)) (by omega : N ≤ N.minFac)]

/-! ### Lucas probable primes -/

/-- `N` is a **Lucas probable prime** for `(P, Q)` if `N ∣ U (N - (D / N))`, with the Jacobi
symbol `(D / N)`. -/
def IsLucasProbablePrime (P Q : ℤ) (N : ℕ) : Prop :=
  (N : ℤ) ∣ lucasU P Q ((N : ℤ) - jacobiSym (P ^ 2 - 4 * Q) N).toNat

/-- A **Lucas pseudoprime** for `(P, Q)`: a composite Lucas probable prime `N` prime to
`2 * Q * D`. (Without the last condition, every power `p ^ k` with `k ≥ 2` of an odd prime `p ∣ D`
would count, since `p ^ k ∣ U (p ^ k)`.) -/
def IsLucasPsp (P Q : ℤ) (N : ℕ) : Prop :=
  IsLucasProbablePrime P Q N ∧ ¬ N.Prime ∧ 1 < N ∧ IsCoprime (N : ℤ) (2 * Q * (P ^ 2 - 4 * Q))

/-- Every odd prime `p ∤ Q` is a Lucas probable prime for `(P, Q)`. -/
theorem Nat.Prime.isLucasProbablePrime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (P : ℤ) {Q : ℤ}
    (hQ : ¬ (p : ℤ) ∣ Q) : IsLucasProbablePrime P Q p := by
  have := Fact.mk hp
  rw [IsLucasProbablePrime, ← jacobiSym.legendreSym.to_jacobiSym]
  exact prime_dvd_lucasU_sub_legendreSym p hp2 P Q hQ
