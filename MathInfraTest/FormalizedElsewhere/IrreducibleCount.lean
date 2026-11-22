import MathInfra.FormalizedElsewhere.IrreducibleCount

/-!
# Checks for `MathInfra.FormalizedElsewhere.IrreducibleCount`

Known counts over `𝔽₂`, `𝔽₃` and `𝔽₄`, the unique irreducible quadratic over `𝔽₂`, and the
general theorems in use. The axiom audit is in
`MathInfraTest/FormalizedElsewhere/IrreducibleCountAxioms.lean`. Both files are part of
`lake build`.
-/

open Finset Polynomial

/-- Read off a count from a necklace number. -/
theorem card_monicIrreducibles_of_necklace {K : Type*} [Field K] [Finite K] {q n m : ℕ}
    (hq : Nat.card K = q) (h : necklace q n = m) : #(monicIrreducibles K n) = m := by
  have := card_monicIrreducibles_eq_necklace K n
  rw [hq, h] at this
  exact_mod_cast this

/-! ### Known values -/

-- Over `𝔽₂` the counts in degrees `1, …, 6` are `2, 1, 2, 3, 6, 9`; degrees `1`, `4`, `6` are
-- checked here and degree `2` below.
example : #(monicIrreducibles (ZMod 2) 1) = 2 := by
  simpa using card_monicIrreducibles_one (ZMod 2)
example : #(monicIrreducibles (ZMod 2) 4) = 3 :=
  card_monicIrreducibles_of_necklace (Nat.card_zmod 2) (by decide +kernel)
example : #(monicIrreducibles (ZMod 2) 6) = 9 :=
  card_monicIrreducibles_of_necklace (Nat.card_zmod 2) (by decide +kernel)

-- Over `𝔽₃`, degree `4`: `(81 - 9) / 4 = 18`.
example : #(monicIrreducibles (ZMod 3) 4) = 18 :=
  card_monicIrreducibles_of_necklace (Nat.card_zmod 3) (by decide +kernel)

-- Over `𝔽₄ = GaloisField 2 2`, degree `2`: `(16 - 4) / 2 = 6`.
example : #(monicIrreducibles (GaloisField 2 2) 2) = 6 :=
  card_monicIrreducibles_of_necklace (GaloisField.card 2 2 (by norm_num)) (by decide +kernel)

/-- `X² + X + 1` is the only monic irreducible quadratic over `𝔽₂`. -/
example : monicIrreducibles (ZMod 2) 2 = {X ^ 2 + X + 1} := by
  have hm : (X ^ 2 + X + 1 : (ZMod 2)[X]).Monic := by monicity!
  have hd : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by compute_degree!
  have hf : X ^ 2 + X + 1 ∈ monicIrreducibles (ZMod 2) 2 := by
    refine mem_monicIrreducibles.mpr ⟨hm, ?_, hd⟩
    refine (hm.irreducible_iff_roots_eq_zero_of_degree_le_three hd.ge
      (hd.le.trans (by norm_num))).mpr (Multiset.eq_zero_of_forall_notMem fun a ha => ?_)
    have := (mem_roots hm.ne_zero).mp ha
    simp only [IsRoot.def, eval_add, eval_pow, eval_X, eval_one] at this
    fin_cases a <;> exact absurd this (by decide)
  have h1 : #(monicIrreducibles (ZMod 2) 2) = 1 := by
    have := card_monicIrreducibles_prime (ZMod 2) Nat.prime_two
    rw [Nat.card_zmod] at this
    omega
  exact eq_singleton_iff_unique_mem.mpr ⟨hf, fun g hg => card_le_one.mp h1.le g hg _ hf⟩

/-! ### The general theorems in use -/

variable (K : Type*) [Field K] [Finite K]

/-- Over a field with `q` elements, `2 * #(degree 2) = q² - q`. -/
example : 2 * #(monicIrreducibles K 2) = Nat.card K ^ 2 - Nat.card K :=
  card_monicIrreducibles_prime K Nat.prime_two

/-- `4 * #(degree 4) = q⁴ - q²`: the divisor sums for `n = 4` and `n = 2` differ by
`4 * #(degree 4)`. -/
example : 4 * #(monicIrreducibles K 4) = Nat.card K ^ 4 - Nat.card K ^ 2 := by
  have h4 := sum_mul_card_monicIrreducibles K (n := 4) (by norm_num)
  have h2 := sum_mul_card_monicIrreducibles K (n := 2) (by norm_num)
  rw [show Nat.divisors 4 = {1, 2, 4} by decide] at h4
  rw [show Nat.divisors 2 = {1, 2} by decide] at h2
  simp only [sum_insert (by decide : (1 : ℕ) ∉ ({2, 4} : Finset ℕ)), sum_pair (by decide : 2 ≠ 4),
    sum_pair (by decide : 1 ≠ 2)] at h4 h2
  omega

/-- Over `𝔽₂` there are more than `96` irreducibles of degree `10` (in fact `99`):
`1024 < 10 * #(degree 10) + 2 * 2⁵`. -/
example : 96 < #(monicIrreducibles (ZMod 2) 10) := by
  have := lt_mul_card_monicIrreducibles_add (ZMod 2) (n := 10) (by norm_num)
  rw [Nat.card_zmod] at this
  omega

/-- The upper bound: there are at most `q ^ n / n` monic irreducibles of degree `n`. -/
example (n : ℕ) : #(monicIrreducibles K n) ≤ Nat.card K ^ n / n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  exact (Nat.le_div_iff_mul_le hn).mpr (by linarith [mul_card_monicIrreducibles_le K n])

/-- Every finite field has an irreducible polynomial of degree `100`. -/
example : ∃ f : K[X], f.Monic ∧ Irreducible f ∧ f.natDegree = 100 :=
  exists_monic_irreducible_natDegree_eq K (by norm_num)
