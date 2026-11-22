module

public import Mathlib
public import MathInfra.New.GaussSeq

/-!
# Counting irreducible polynomials over a finite field

Let `K` be a finite field with `q` elements. **Gauss's formula** counts the monic irreducible
polynomials of degree `n` over `K`:

`n * #(monic irreducibles of degree n) = ∑_{d ∣ n} μ(d) * q ^ (n / d)`.

The proof factors `X ^ q ^ n - X` for `n > 0`: it is separable, and its monic irreducible
factors are exactly the monic irreducibles whose degree divides `n`. Comparing degrees gives
`∑_{d ∣ n} d * #(monicIrreducibles K d) = q ^ n`, which Möbius inversion turns into Gauss's
formula. The count is the necklace number `necklace q n` of `MathInfra.New.GaussSeq`, also
called the necklace polynomial evaluated at `q`. The bounds below are the prime polynomial
theorem, the function-field analogue of the prime number theorem.

Mathlib (2026-11-19) has the divisibility criterion
`Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X` but no count, and neither has the open
PR #45947 (Rabin's test). The multiplicity of each monic irreducible in `X ^ q ^ n - X`, Gauss's
formula, the degree-1 and degree-2 counts, the bound `q ^ n / (2 * n) ≤ #(monicIrreducibles K n)`
for `n > 0` and the existence of irreducibles of every positive degree are in the Isabelle AFP
entry *Finite_Fields* (Karayel, theory `Card_Irreducible_Polynomials`).

## Main definitions

* `monicIrreducibles K n` : the finite set of monic irreducible polynomials of degree `n`
  over `K`.

## Main results

Write `q = Nat.card K`.

* `prod_prod_monicIrreducibles` : for `n > 0`, `X ^ q ^ n - X` is the product of the monic
  irreducible polynomials whose degree divides `n`.
* `sum_mul_card_monicIrreducibles` : for `n > 0`,
  `∑_{d ∣ n} d * #(monicIrreducibles K d) = q ^ n`.
* `mul_card_monicIrreducibles`, `card_monicIrreducibles_eq_necklace` : Gauss's formula.
* `card_monicIrreducibles_one`, `card_monicIrreducibles_prime` : there are `q` of degree `1`,
  and `p` times the number of degree `p` is `q ^ p - q` for `p` prime.
* `mul_card_monicIrreducibles_le`, `lt_mul_card_monicIrreducibles_add` : the prime polynomial
  theorem `n * #(monicIrreducibles K n) ≤ q ^ n`, and
  `q ^ n < n * #(monicIrreducibles K n) + 2 * q ^ (n / 2)` for `n > 0`.
* `card_monicIrreducibles_pos`, `exists_monic_irreducible_natDegree_eq` : there is a monic
  irreducible polynomial of every degree `n > 0`.
-/
@[expose] public section

open Finset Polynomial UniqueFactorizationMonoid ArithmeticFunction
open scoped ArithmeticFunction.Moebius

variable (K : Type*) [Field K] [Finite K]

/-- There are finitely many monic irreducible polynomials of each degree: each one of degree
`n` is a factor of `X ^ q ^ n - X`. -/
theorem finite_setOf_monic_irreducible (n : ℕ) :
    {f : K[X] | f.Monic ∧ Irreducible f ∧ f.natDegree = n}.Finite := by
  classical
  refine (normalizedFactors (X ^ Nat.card K ^ n - X : K[X])).toFinset.finite_toSet.subset ?_
  rintro f ⟨hm, hi, rfl⟩
  have hq : 1 < Nat.card K ^ f.natDegree :=
    Nat.one_lt_pow hi.natDegree_pos.ne' Finite.one_lt_card
  rw [Finset.mem_coe, Multiset.mem_toFinset]
  exact (Polynomial.mem_normalizedFactors_iff (X_pow_sub_X_ne_zero hq)).mpr
    ⟨hi, hm, hi.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp dvd_rfl⟩

/-- The monic irreducible polynomials of degree `n` over `K`. -/
noncomputable def monicIrreducibles (n : ℕ) : Finset K[X] :=
  (finite_setOf_monic_irreducible K n).toFinset

variable {K} in
@[simp]
theorem mem_monicIrreducibles {n : ℕ} {f : K[X]} :
    f ∈ monicIrreducibles K n ↔ f.Monic ∧ Irreducible f ∧ f.natDegree = n := by
  simp [monicIrreducibles]

@[simp]
theorem monicIrreducibles_zero : monicIrreducibles K 0 = ∅ :=
  eq_empty_of_forall_notMem fun _ hf => (mem_monicIrreducibles.mp hf).2.1.natDegree_pos.ne'
    (mem_monicIrreducibles.mp hf).2.2

variable {K} in
/-- For `n ≠ 0`, `X ^ q ^ n - X` is separable: its derivative is `-1`. -/
theorem separable_X_pow_card_pow_sub_X {n : ℕ} (hn : n ≠ 0) :
    (X ^ Nat.card K ^ n - X : K[X]).Separable := by
  have := Fintype.ofFinite K
  obtain ⟨p, hp⟩ := CharP.exists K
  refine galois_poly_separable p _ (dvd_pow ?_ hn)
  rw [← CharP.cast_eq_zero_iff K p, Nat.card_eq_fintype_card]
  exact FiniteField.cast_card_eq_zero K

/-- **Gauss.** For `n > 0`, `X ^ q ^ n - X` is the product of the monic irreducible
polynomials whose degree divides `n`. -/
theorem prod_prod_monicIrreducibles {n : ℕ} (hn : 0 < n) :
    ∏ d ∈ n.divisors, ∏ f ∈ monicIrreducibles K d, f = X ^ Nat.card K ^ n - X := by
  classical
  set P : K[X] := X ^ Nat.card K ^ n - X
  have hq : 1 < Nat.card K ^ n := Nat.one_lt_pow hn.ne' Finite.one_lt_card
  have hP : P ≠ 0 := X_pow_sub_X_ne_zero hq
  have hnodup : (normalizedFactors P).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hP).mp
      (separable_X_pow_card_pow_sub_X hn.ne').squarefree
  have hfac : (normalizedFactors P).toFinset = n.divisors.biUnion (monicIrreducibles K) := by
    ext f
    simp only [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff hP, mem_biUnion,
      Nat.mem_divisors, mem_monicIrreducibles]
    constructor
    · rintro ⟨hi, hm, hd⟩
      exact ⟨_, ⟨hi.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hd, hn.ne'⟩, hm, hi, rfl⟩
    · rintro ⟨_, ⟨hd, -⟩, hm, hi, rfl⟩
      exact ⟨hi, hm, hi.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp hd⟩
  rw [← prod_biUnion, ← hfac, prod_eq_multiset_prod, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr hnodup, Multiset.map_id', prod_normalizedFactors_eq hP]
  · exact (monic_X_pow_sub (degree_X_le.trans_lt (by exact_mod_cast hq))).normalize_eq_self
  · intro d _ e _ hde
    simp only [Function.onFun, disjoint_left, mem_monicIrreducibles]
    rintro f ⟨-, -, rfl⟩ ⟨-, -, h⟩
    exact hde h

/-- Comparing degrees in `prod_prod_monicIrreducibles`: for `n > 0`,
`∑_{d ∣ n} d * #(monicIrreducibles K d) = q ^ n`. -/
theorem sum_mul_card_monicIrreducibles {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, d * #(monicIrreducibles K d) = Nat.card K ^ n := by
  have h := congrArg natDegree (prod_prod_monicIrreducibles K hn)
  have hmonic (d : ℕ) : ∀ f ∈ monicIrreducibles K d, f.Monic :=
    fun f hf => (mem_monicIrreducibles.mp hf).1
  rw [natDegree_X_pow_sub_X (Nat.one_lt_pow hn.ne' Finite.one_lt_card),
    natDegree_prod_of_monic _ _ fun d _ => monic_prod_of_monic _ _ (hmonic d)] at h
  rw [← h]
  refine sum_congr rfl fun d _ => ?_
  rw [natDegree_prod_of_monic _ _ (hmonic d),
    sum_congr rfl fun f hf => (mem_monicIrreducibles.mp hf).2.2, sum_const, smul_eq_mul, mul_comm]

private theorem sum_mul_card_monicIrreducibles_int {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, (d : ℤ) * #(monicIrreducibles K d) = (Nat.card K : ℤ) ^ n := by
  exact_mod_cast sum_mul_card_monicIrreducibles K hn

/-- **Gauss's formula**: `n * #(monicIrreducibles K n) = ∑_{d ∣ n} μ(d) * q ^ (n / d)`. -/
theorem mul_card_monicIrreducibles (n : ℕ) :
    n * (#(monicIrreducibles K n) : ℤ) = ∑ d ∈ n.divisors, μ d * (Nat.card K : ℤ) ^ (n / d) :=
  (sum_moebius_mul_eq_of_sum_eq (fun _ hn => sum_mul_card_monicIrreducibles_int K hn) n).symm

/-- The number of monic irreducible polynomials of degree `n` is the necklace number
`necklace q n`. -/
theorem card_monicIrreducibles_eq_necklace (n : ℕ) :
    #(monicIrreducibles K n) = necklace (Nat.card K) n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [necklace, orbitCount]
  exact (orbitCount_eq_of_sum_eq (fun _ hn => sum_mul_card_monicIrreducibles_int K hn) hn).symm

/-- There are `q` monic irreducible polynomials of degree `1`. -/
theorem card_monicIrreducibles_one : #(monicIrreducibles K 1) = Nat.card K := by
  simpa using sum_mul_card_monicIrreducibles K one_pos

/-- For a prime `p`, `p * #(monicIrreducibles K p) = q ^ p - q`. -/
theorem card_monicIrreducibles_prime {p : ℕ} (hp : p.Prime) :
    p * #(monicIrreducibles K p) = Nat.card K ^ p - Nat.card K := by
  rw [← sum_mul_card_monicIrreducibles K hp.pos, hp.divisors, sum_pair hp.one_lt.ne,
    card_monicIrreducibles_one, one_mul, Nat.add_sub_cancel_left]

/-- The upper bound `n * #(monicIrreducibles K n) ≤ q ^ n`. -/
theorem mul_card_monicIrreducibles_le (n : ℕ) :
    n * #(monicIrreducibles K n) ≤ Nat.card K ^ n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  rw [← sum_mul_card_monicIrreducibles K hn]
  exact single_le_sum (f := fun d => d * #(monicIrreducibles K d)) (fun _ _ => Nat.zero_le _)
    (Nat.mem_divisors_self n hn.ne')

/-- A proper divisor of `n` is at most `n / 2`. -/
theorem Nat.le_div_two_of_mem_properDivisors {n d : ℕ} (hd : d ∈ n.properDivisors) : d ≤ n / 2 := by
  obtain ⟨⟨k, rfl⟩, hlt⟩ := Nat.mem_properDivisors.mp hd
  have hk : 2 ≤ k := by
    rcases k with _ | _ | k
    · simp at hlt
    · simp at hlt
    · omega
  exact (Nat.le_div_iff_mul_le two_pos).mpr (Nat.mul_le_mul_left d hk)

/-- The lower bound `q ^ n < n * #(monicIrreducibles K n) + 2 * q ^ (n / 2)` for `n > 0`. In
`sum_mul_card_monicIrreducibles`, each proper divisor `d` of `n` is at most `n / 2` and
contributes at most `q ^ d`, and `∑_{d ≤ n / 2} q ^ d < 2 * q ^ (n / 2)`. -/
theorem lt_mul_card_monicIrreducibles_add {n : ℕ} (hn : 0 < n) :
    Nat.card K ^ n < n * #(monicIrreducibles K n) + 2 * Nat.card K ^ (n / 2) := by
  set q := Nat.card K
  have hq : 2 ≤ q := Finite.one_lt_card
  rw [← sum_mul_card_monicIrreducibles K hn, ← Nat.cons_self_properDivisors hn.ne', sum_cons,
    add_lt_add_iff_left]
  calc ∑ d ∈ n.properDivisors, d * #(monicIrreducibles K d)
      ≤ ∑ d ∈ n.properDivisors, q ^ d := sum_le_sum fun d _ => mul_card_monicIrreducibles_le K d
    _ ≤ ∑ d ∈ range (n / 2 + 1), q ^ d := sum_le_sum_of_subset fun d hd =>
        mem_range.mpr (Nat.lt_succ_of_le (Nat.le_div_two_of_mem_properDivisors hd))
    _ = ∑ d ∈ range (n / 2), q ^ d + q ^ (n / 2) := sum_range_succ _ _
    _ < q ^ (n / 2) + q ^ (n / 2) :=
        Nat.add_lt_add_right (Nat.geomSum_lt hq fun _ hk => mem_range.mp hk) _
    _ = 2 * q ^ (n / 2) := (two_mul _).symm

/-- For `n > 0`, `#(monicIrreducibles K n)` is positive: otherwise the lower bound would give
`q ^ n < 2 * q ^ (n / 2)`, but `2 * q ^ (n / 2) ≤ q ^ (n / 2 + 1) ≤ q ^ n`. -/
theorem card_monicIrreducibles_pos {n : ℕ} (hn : 0 < n) : 0 < #(monicIrreducibles K n) := by
  have h := lt_mul_card_monicIrreducibles_add K hn
  set q := Nat.card K
  have hq : 2 ≤ q := Finite.one_lt_card
  have : 2 * q ^ (n / 2) ≤ q ^ n :=
    calc 2 * q ^ (n / 2) ≤ q * q ^ (n / 2) := Nat.mul_le_mul_right _ hq
      _ = q ^ (n / 2 + 1) := by ring
      _ ≤ q ^ n := Nat.pow_le_pow_right (by omega) (by omega)
  refine Nat.pos_of_ne_zero fun h0 => ?_
  rw [h0, mul_zero, zero_add] at h
  omega

/-- There is a monic irreducible polynomial of every degree `n > 0`. -/
theorem exists_monic_irreducible_natDegree_eq {n : ℕ} (hn : 0 < n) :
    ∃ f : K[X], f.Monic ∧ Irreducible f ∧ f.natDegree = n := by
  obtain ⟨f, hf⟩ := card_pos.mp (card_monicIrreducibles_pos K hn)
  exact ⟨f, mem_monicIrreducibles.mp hf⟩
