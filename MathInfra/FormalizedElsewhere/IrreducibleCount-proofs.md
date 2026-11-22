# Counting irreducible polynomials: the proofs in ordinary language

This is the human-readable companion to `MathInfra/FormalizedElsewhere/IrreducibleCount.lean`.
Each numbered statement names the Lean theorem that checks it, and the proofs follow the same
route as the Lean proofs.

Throughout, `K` is a finite field with `q` elements, `n`, `d`, `m` are natural numbers, `p` is a
prime and `μ` is the Möbius function. `n/d` is division of natural numbers, and sums over the
divisors of `0` are `0` (Lean's convention). Write `P_n = X^(q^n) − X`. From Mathlib we use the
criterion: an irreducible `f` divides `P_n` if and only if `deg f ∣ n`.

## Prior art

Checked in November 2026.

- **Mathlib** (pinned at 2026-11-19, and `master` on 2026-11-21) has the criterion used in §1
  and §2 (`Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X`), the separability of `P_n`
  (`galois_poly_separable`) and an irreducibility criterion over all proper divisors of the
  degree (`Polynomial.irreducible_iff_dvd_X_pow_card_pow_sub_X_and_isCoprime`), but no count of
  irreducible polynomials. The open PR
  [#45947](https://github.com/leanprover-community/mathlib4/pull/45947) (Rabin's test, over the
  prime divisors only) does not count either.
- **Isabelle AFP**, entry [*Finite_Fields*](https://www.isa-afp.org/entries/Finite_Fields.html)
  (Karayel), theory `Card_Irreducible_Polynomials`: the multiplicity of each monic irreducible
  in `P_n`, the formulas 3.1 and 3.2, the counts `q` and `(q² − q)/2` in degrees `1` and `2`, the
  bound `q^n/(2n) ≤ M(n)`, and existence in every positive degree (5.1).
- Not found elsewhere: the product formula 2.2 stated as an identity (the AFP multiplicity
  statement is equivalent to it), the count in prime degree 3.3, the upper bound 4.1, and the
  lower bound 4.3, which is sharper than `q^n/(2n) ≤ M(n)` for `n ≥ 3`. Nothing was found on
  the Lean Zulip, in other Lean projects, or in HOL4, HOL Light or Coq/Rocq.

The count is also called the necklace polynomial evaluated at `q`, and the bounds of §4 are
the prime polynomial theorem.

## 1. Definitions

**Definition** (`monicIrreducibles`). `I_n` is the set of monic irreducible polynomials of degree
`n` over `K`, and `M(n) = |I_n|`.

**1.1** (`finite_setOf_monic_irreducible`, `mem_monicIrreducibles`). `I_n` is finite. Each
element `f` divides `P_n` by the criterion, and `P_n` is nonzero since `n = deg f > 0`, so it
has finitely many monic irreducible factors.

**1.2** (`monicIrreducibles_zero`). `I_0` is empty: irreducible polynomials have positive
degree.

## 2. The factorisation of `X^(q^n) − X`

**2.1** (`separable_X_pow_card_pow_sub_X`). For `n > 0`, `P_n` is separable.

*Proof.* `q^n` is zero in `K`, so the derivative of `P_n` is `q^n·X^(q^n − 1) − 1 = −1`. ∎

**2.2** (`prod_prod_monicIrreducibles`, Gauss). For `n > 0`,

`X^(q^n) − X = Π_{d ∣ n} Π_{f ∈ I_d} f`.

*Proof.* `P_n` is monic and nonzero, so it is the product of its monic irreducible factors,
counted with multiplicity. It is separable by 2.1, hence squarefree, so each factor occurs
once. By the criterion above, a monic irreducible `f` divides `P_n` exactly when `deg f ∣ n`, so
the factors are the elements of the sets `I_d` for `d ∣ n`. These sets are disjoint for
different `d`. ∎

## 3. Gauss's formula

**3.1** (`sum_mul_card_monicIrreducibles`). For `n > 0`, `Σ_{d ∣ n} d·M(d) = q^n`.

*Proof.* Compare degrees in 2.2. The degree of a product of monic polynomials is the sum of the
degrees, and `I_d` contributes `M(d)` factors of degree `d`. ∎

**3.2** (`mul_card_monicIrreducibles`, `card_monicIrreducibles_eq_necklace`). For every `n`,

`n·M(n) = Σ_{d ∣ n} μ(d)·q^(n/d)`,

and `M(n) = M(q, n)`, the necklace number of `GaussSeq` §8.

*Proof.* Möbius inversion of 3.1 (`GaussSeq` 2.2 and 2.3, with `f(n) = q^n` and
`h(d) = M(d)`). For `n = 0`, both `M(0)` (by 1.2) and `M(q, 0)` are `0`. ∎

**3.3** (`card_monicIrreducibles_one`, `card_monicIrreducibles_prime`). `M(1) = q`, and
`p·M(p) = q^p − q`. In particular `2·M(2) = q² − q`.

*Proof.* 3.1 for `n = 1` is `M(1) = q`. The divisors of `p` are `1` and `p`, so
`M(1) + p·M(p) = q^p`. ∎

## 4. The prime polynomial theorem

**4.1** (`mul_card_monicIrreducibles_le`). `n·M(n) ≤ q^n`. For `n > 0`, `n·M(n)` is the term
`d = n` of the sum in 3.1, whose terms are nonnegative. For `n = 0` the left side is `0`.

**4.2** (`Nat.le_div_two_of_mem_properDivisors`). A proper divisor `d` of `n` satisfies
`d ≤ n/2`.

*Proof.* Write `n = dk`. Since `d < n`, `k ≥ 2`, so `2d ≤ n`. ∎

**4.3** (`lt_mul_card_monicIrreducibles_add`). For `n > 0`, with `m = ⌊n/2⌋`,

`q^n < n·M(n) + 2q^m`.

*Proof.* Split off the term `d = n` in 3.1:
`q^n = n·M(n) + Σ_{d ∣ n, d < n} d·M(d)`. By 4.1 and 4.2, the remaining sum is at most
`Σ_{d ≤ m} q^d = Σ_{d < m} q^d + q^m`. Since `q ≥ 2`, `Σ_{d < m} q^d = (q^m − 1)/(q − 1) < q^m`. ∎

Together, 4.1 and 4.3 give `0 ≤ q^n − n·M(n) < 2q^m`, so `M(n) ~ q^n/n`.

## 5. Existence

**5.1** (`card_monicIrreducibles_pos`, `exists_monic_irreducible_natDegree_eq`). For `n > 0`
there is a monic irreducible polynomial of degree `n` over `K`.

*Proof.* Since `q ≥ 2` and `m + 1 ≤ n`, `2q^m ≤ q^(m+1) ≤ q^n`. If `M(n) = 0`, then 4.3 would
give `q^n < 2q^m`. ∎
