# Zeta series: the proofs in ordinary language

This is the human-readable companion to `MathInfra/FormalizedElsewhere/ZetaSeries.lean`. Each
numbered statement names the Lean theorem that checks it, and the proofs follow the same route
as the Lean proofs.

Throughout, `R` is a commutative ring, `f`, `g` are sequences `ℕ → R` (or `ℕ → ℤ` where stated),
`P`, `Q` are power series in `R⟦X⟧`, `a(n)` is the coefficient of `Xⁿ` in `P`, `μ` is the
Möbius function, and, as in `GaussSeq`, `S_f(n) = Σ_{d ∣ n} μ(d)·f(n/d)` and `O_f(n) = S_f(n)/n`
(`orbitCount`). The value `f(0)` never matters.

## Prior art

Checked in November 2026.

- **Mathlib** (pinned at 2026-11-19) has `tr(Aᵖ) = tr(A)ᵖ` over finite fields
  (`FiniteField.trace_pow_card`, `ZMod.trace_pow_card`), which over `ZMod p` is equivalent by
  Fermat to the case `k = 0`, `m = 1` of 5.5, and the degree-1 coefficient of `det(1 − X·A)`
  (`Matrix.coeff_charpolyRev_eq_neg_trace`). Jacobi's formula for
  `det(1 − X·A)` (5.3) was proposed in the closed, unmerged PR
  [#44901](https://github.com/leanprover-community/mathlib4/pull/44901). There is nothing on
  zeta series of sequences, Dold's criterion or products `Π (1 − X^d)^(−h(d))`.
- **Other Lean projects.** The direction "Gauss congruences ⇒ integral zeta series" of 4.5 is
  `integral_exp_of_dold` in
  [the-omega-institute/trureturing](https://github.com/the-omega-institute/trureturing)
  (`D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.lean`), proved over `ℚ` via the
  Dieudonné–Dwork criterion and adapted from CBirkbeck/AINTLIB. The same project has trace
  recurrences for `2 × 2` matrices.
- **Isabelle AFP, Rocq, HOL.** Nothing found on Dold sequences, Gauss congruences for traces or
  products `Π (1 − X^d)^(−h(d))`.

New here: the converse of Dold's criterion, its formulation in `ℤ⟦X⟧` without division, Witt
products, the Gauss congruences for traces of all square integer matrices, and the Lucas
corollary.

Other names: Gauss congruences are also called Dold or Fermat congruences; the sequences with
`O_f ≥ 0` are the realizable sequences. The zeta series is `exp(Σ f(n)·Xⁿ/n)`; for fixed-point
counts it is the Artin–Mazur zeta function.

## 1. Zeta series

**Definition** (`ghostSeries`, `coeff_ghostSeries`, `IsZetaSeries`). Let
`G_f = Σ_{n ≥ 0} f(n+1)·Xⁿ`. `P` is a *zeta series* of `f` if `P(0) = 1` and `P' = P·G_f`.

Over `ℚ` the unique such `P` is `exp(Σ_{n ≥ 1} f(n)·Xⁿ/n)`, since `G_f` is the derivative of
the exponent. The definition needs no division.

**1.1** (`isZetaSeries_iff_coeff`). `P` is a zeta series of `f` if and only if `a(0) = 1` and

`(n+1)·a(n+1) = Σ_{i+j=n} a(i)·f(j+1)` for all `n`.

This compares the coefficients of `Xⁿ` in `P'` and `P·G_f`.

**1.2** (`isZetaSeries_zero`, `ghostSeries_zero`, `ghostSeries_add`, `IsZetaSeries.mul`,
`IsZetaSeries.pow`, `IsZetaSeries.prod`). `1` is a zeta series of `0`. If `P` is one of `f` and
`Q` one of `g`, then `PQ` is one of `f + g`. Hence `Pⁿ` is one of `n·f`, and finite products
correspond to finite sums.

*Proof.* `G_0 = 0` and `G_f + G_g = G_(f+g)`, and `(PQ)' = P'Q + PQ' = PQ·(G_f + G_g)`. ∎

**1.3** (`IsZetaSeries.of_mul_eq_one`, `ghostSeries_neg`). If `P` is a zeta series of `f` and
`PQ = 1`, then `Q` is one of `−f`.

*Proof.* Differentiating `PQ = 1` gives `PQ' + Q·P·G_f = 0`. Multiply by `Q` and use `QP = 1`:
`Q' = −Q·G_f = Q·G_(−f)`. Also `P(0)Q(0) = 1` with `P(0) = 1`. ∎

**1.4** (`isZetaSeries_geometric`). `Σ aⁿXⁿ = 1/(1 − aX)` is a zeta series of `n ↦ aⁿ`.

*Proof.* By 1.1: `Σ_{i+j=n} aⁱ·a^(j+1)` has `n + 1` terms, each `a^(n+1)`. ∎

## 2. Cyclotomic factors

For `d ≥ 1` let `C_d = Σ_{d ∣ n} Xⁿ` (`cycInv`) and `c_d(n) = d` if `d ∣ n`, `0` otherwise
(`cycGhost`).

**2.1** (`one_sub_X_pow_mul_cycInv`). `(1 − X^d)·C_d = 1`.

*Proof.* The coefficient of `Xⁿ` is `[d ∣ n] − [d ∣ n − d] = 0` for `n ≥ d`, and
`[d ∣ n] = [n = 0]` for `n < d`; these are the coefficients of `1`. ∎

**2.2** (`ghostSeries_cycGhost`). `G_(c_d) = d·X^(d−1)·C_d`.

*Proof.* Both sides have coefficient `d` at `Xⁿ` exactly when `d ∣ n + 1`: write `n + 1 = m + d`
and note `d ∣ m + d ⟺ d ∣ m`. ∎

**2.3** (`isZetaSeries_one_sub_X_pow`, `isZetaSeries_cycInv`). `1 − X^d` is a zeta series of
`−c_d`, and `C_d = 1/(1 − X^d)` is one of `c_d`.

*Proof.* `(1 − X^d)' = −d·X^(d−1) = −(1 − X^d)·d·X^(d−1)·C_d` by 2.1, which is
`(1 − X^d)·G_(−c_d)` by 2.2. The second claim follows by 1.3 and 2.1. ∎

## 3. Witt products

In sections 3 and 4, sequences are integer-valued and series have integer coefficients.

**Definition** (`cycFactor`, `wittProd`). For `k ∈ ℤ`, `(1 − X^d)^(−k)` means `C_d^k` if `k ≥ 0`
and `(1 − X^d)^|k|` if `k < 0`. For `h : ℕ → ℤ`, the *Witt product* is

`W_N(h) = Π_{d=1}^{N} (1 − X^d)^(−h(d))`.

**3.1** (`isZetaSeries_cycFactor`, `isZetaSeries_wittProd`). `(1 − X^d)^(−k)` is a zeta series of
`k·c_d`, so `W_N(h)` is one of `n ↦ Σ_{d ∣ n, d ≤ N} d·h(d)`.

*Proof.* 2.3 and 1.2. ∎

**3.2** (`Nat.filter_Icc_dvd_eq_divisors`, `Nat.filter_Icc_dvd_succ_eq_properDivisors`). For
`0 < n ≤ N`, every divisor of `n` is at most `N`, and the divisors `d ≤ N` of `N + 1` are exactly
its proper divisors.

## 4. Dold's criterion

**4.1** (`IsZetaSeries.coeff_eq`). Let `P`, `Q` be zeta series of `f`, `g`. If `f(n) = g(n)` for
`0 < n ≤ N`, then `P` and `Q` agree up to degree `N`.

*Proof.* Strong induction on the degree `n ≤ N`, with `a(0) = 1` for both. In 1.1 for degree
`n + 1`, the right side only uses coefficients of degree `≤ n` and values `f(j+1)` with
`j + 1 ≤ n + 1 ≤ N`, which agree. Cancel the factor `n + 1 ≠ 0` in `ℤ`. ∎

**4.2** (`IsZetaSeries.unique`). Over `ℤ` a sequence has at most one zeta series. Take `g = f` in
4.1 for every `N`.

**4.3** (`exists_isZetaSeries_of_forall`). Suppose that for every `N` the sequence `g_N` agrees
with `f` on `1, …, N` and has a zeta series `P_N`. Then `f` has a zeta series.

*Proof.* Let `Q` have coefficient `a_n(n)` at `Xⁿ`, where `a_N` are the coefficients of `P_N`.
By 4.1, `a_n(n) = a_M(n)` whenever `n ≤ M`. So the relation 1.1 for `Q` in degree `n + 1` is the
relation for `P_(n+1)`, whose values `g_(n+1)(j+1)` equal `f(j+1)`. ∎

**4.4** (`IsZetaSeries.dvd`). If `f` has a zeta series and `f(n) = 0` for `0 < n ≤ N`, then
`N + 1 ∣ f(N+1)`.

*Proof.* By 4.1 against the zeta series `1` of `0`, `a(i) = 0` for `0 < i ≤ N`. In 1.1 for degree
`N + 1` only the term `i = 0` survives: `(N+1)·a(N+1) = f(N+1)`. ∎

**4.5** (`isGaussSeq_iff_exists_isZetaSeries`). **Dold's criterion.** `f` satisfies the Gauss
congruences if and only if it has a zeta series with integer coefficients.

*Proof.* (⇒) Let `h = O_f` (`orbitCount`). By `GaussSeq` 2.4, `f(n) = Σ_{d ∣ n} d·h(d)` for
`n > 0`, so by 3.1 and 3.2 the Witt product `W_N(h)` is a zeta series of a sequence that agrees
with `f` on `1, …, N`. Apply 4.3.

(⇐) Let `P` be a zeta series of `f`. We show `n ∣ S_f(n)` for `n ≤ N` by induction on `N`; the
case `N = 0` is trivial. Suppose it holds up to `N`, and let `h = O_f`. Then `d·h(d) = S_f(d)`
for `d ≤ N`. By 1.2 and 3.1, `P·W_N(−h)` is a zeta series of

`F(n) = f(n) − Σ_{d ∣ n, d ≤ N} S_f(d)`.

For `0 < n ≤ N` this is `f(n) − Σ_{d ∣ n} S_f(d) = 0` by 3.2 and Möbius inversion (`GaussSeq`
2.1). So `N + 1 ∣ F(N+1)` by 4.4, and by 3.2 and Möbius inversion again
`F(N+1) = f(N+1) − Σ_{d ∣ N+1, d < N+1} S_f(d) = S_f(N+1)`. ∎

## 5. Traces of matrix powers

Here `A` is a square matrix over `R`, and `det(1 − X·A)` is the polynomial `charpolyRev A`,
read as a power series.

**5.1** (`resolventSeries`, `one_sub_X_smul_mul_resolventSeries`). The matrix
`R_A = Σ Aⁿ Xⁿ` of power series satisfies `(1 − X·A)·R_A = 1`. The coefficient of `Xⁿ` in the
product is `Aⁿ − A·A^(n−1) = 0` for `n ≥ 1`, and `A⁰ = 1` for `n = 0`.

**5.2** (`trace_resolventSeries_mul`, `coe_charpolyRev`). `tr(R_A·A) = Σ tr(A^(n+1))·Xⁿ`, and the
power series `det(1 − X·A)` is the determinant of the matrix `1 − X·A` of power series.

**5.3** (`isZetaSeries_charpolyRev`). **Jacobi's formula.** `D = det(1 − X·A)` is a zeta series
of `n ↦ −tr(Aⁿ)`; that is, `D' = −D·Σ tr(A^(n+1))·Xⁿ`.

*Proof.* `D(0) = 1`. Let `U = 1 − X·A` over `R⟦X⟧` and let `Y` be a new variable. Substituting
`X + Y` for the variable of the polynomial `D` gives a polynomial in `Y` whose coefficient of `Y`
is `D'` (Taylor's formula). The substitution turns `1 − X·A` into
`U − Y·A = U·(1 + Y·B)` with `B = −R_A·A`, by 5.1. So it turns `D` into `det U·det(1 + Y·B)`,
whose coefficient of `Y` is `det U·tr B` (Mathlib, `Matrix.coeff_det_one_add_X_smul_one`). By 5.2,
`det U = D` and `tr B = −Σ tr(A^(n+1))·Xⁿ`. ∎

**5.4** (`isZetaSeries_trace_pow`, `isGaussSeq_trace_pow`). `1/det(1 − X·A)` is a zeta series of
`n ↦ tr(Aⁿ)`. So for an integer matrix `A`, `n ↦ tr(Aⁿ)` satisfies the Gauss congruences:

`n ∣ Σ_{d ∣ n} μ(d)·tr(A^(n/d))`.

*Proof.* `D` has constant coefficient `1`, so it is a unit; apply 1.3 to 5.3. Its inverse has
integer coefficients, so 4.5 applies. ∎

**5.5** (`trace_pow_modEq`). For an integer matrix `A` and a prime `p`,

`tr(A^(p^(k+1)·m)) ≡ tr(A^(p^k·m)) (mod p^(k+1))`.

This is 5.4 combined with `GaussSeq` 3.2.

## 6. Lucas sequences

Here `P`, `Q` are elements of `R`.

**6.1** (`lucasMatrix`, `trace_lucasMatrix_pow`). For `L = [[P, −Q], [1, 0]]`,
`tr(Lⁿ) = V_n(P, Q)`.

*Proof.* `L² = P·L − Q` (Cayley–Hamilton, checked entry by entry), so
`L^(n+2) = P·L^(n+1) − Q·Lⁿ`, and the traces satisfy the Lucas recurrence. They start with
`tr(1) = 2` and `tr(L) = P`, as `V` does. ∎

**6.2** (`isGaussSeq_lucasV`). For integers `P`, `Q`, `V_n(P, Q)` satisfies the Gauss
congruences. This is 5.4 and 6.1.

## 7. Applications to `GaussSeq`

**7.1** (`exists_isZetaSeries_card_fixedPoints`). For a self-map `T` of a finite set, the
Artin–Mazur zeta function `exp(Σ #Fix(Tⁿ)·Xⁿ/n)` has integer coefficients. This is 4.5 and
`GaussSeq` 7.4.

**7.2** (`coeff_wittProd_necklace`). **The cyclotomic identity**, degree by degree: for `n ≤ N`,
the coefficient of `Xⁿ` in `Π_{d=1}^{N} (1 − X^d)^(−M(a, d))` is `aⁿ`. Hence, informally (the
limit is not stated in Lean), `1/(1 − aX) = Π_{d ≥ 1} (1 − X^d)^(−M(a, d))`.

*Proof.* By 3.1, 3.2 and `GaussSeq` 8.1 the product is a zeta series of a sequence that agrees
with `n ↦ aⁿ` on `1, …, N`. Compare it with 1.4 using 4.1. ∎
