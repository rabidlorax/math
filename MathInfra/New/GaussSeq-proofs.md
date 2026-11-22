# Gauss congruences: the proofs in ordinary language

This is the human-readable companion to `MathInfra/New/GaussSeq.lean`. Each numbered statement
names the Lean theorem that checks it, and the proofs follow the same route as the Lean
proofs.

Throughout, `f`, `g`, `h` are functions `ℕ → ℤ`, `n`, `m`, `d`, `e`, `k`, `r` are natural
numbers, `p` is a prime, `μ` is the Möbius function and `φ` is Euler's totient. `n/d` is division
of natural numbers. Lean's convention is that `0` has no divisors, so sums over the divisors of
`0` are `0`.

## 1. Definitions

**Definition** (`IsGaussSeq`). `f` satisfies the *Gauss congruences* if for every `n`

`n ∣ S_f(n)`, where `S_f(n) = Σ_{d ∣ n} μ(d)·f(n/d)`.

For `n = 0` this holds trivially, since `S_f(0) = 0`.

**Definition** (`orbitCount`). `O_f(n) = S_f(n)/n`, using integer division, with Lean's convention
`x/0 = 0`, so `O_f(0) = 0`. The division is exact when `f` satisfies the Gauss congruences.

## 2. Möbius inversion

**2.1** (`sum_sum_moebius_mul`). For `n > 0`, `Σ_{d ∣ n} S_f(d) = f(n)`. This is Möbius
inversion.

**2.2** (`sum_moebius_mul_eq_of_sum_eq`). If `f(n) = Σ_{d ∣ n} d·h(d)` for all `n > 0`, then
`S_f(n) = n·h(n)` for all `n`.

*Proof.* For `n = 0` both sides are `0`. For `n > 0` this is Möbius inversion. ∎

**2.3** (`orbitCount_eq_of_sum_eq`). In the same situation, `O_f(n) = h(n)` for `n > 0`. Divide
2.2 by `n`.

**2.4** (`IsGaussSeq.mul_orbitCount`, `IsGaussSeq.sum_mul_orbitCount`). If `f` satisfies the
Gauss congruences, then `n·O_f(n) = S_f(n)`, and so `f(n) = Σ_{d ∣ n} d·O_f(d)` for `n > 0`
by 2.1.

**2.5** (`isGaussSeq_iff_exists`). `f` satisfies the Gauss congruences if and only if
`f(n) = Σ_{d ∣ n} d·h(d)` for some `h` and all `n > 0`. Then `h(n) = O_f(n)` for `n > 0`.

*Proof.* If `f` satisfies them, take `h = O_f` (2.4). Conversely `S_f(n) = n·h(n)` by 2.2. The
last claim is 2.3. ∎

## 3. Euler congruences

**3.1** (`Nat.Prime.pow_dvd_of_dvd_mul_of_not_dvd`). If `d ∣ pm` and `d ∤ m`, then every power
of `p` dividing `pm` divides `d`.

*Proof.* Write `pm = dc`. If `p ∣ c`, say `c = pc'`, then `m = dc'`, which is excluded. So `p`
is coprime to `c`, and hence so is every power `p^k`. If `p^k ∣ pm = dc`, then `p^k ∣ d`. ∎

**3.2** (`isGaussSeq_iff_modEq`). `f` satisfies the Gauss congruences if and only if, for every
prime `p` and all `k`, `m`,

`f(p^(k+1)·m) ≡ f(p^k·m) (mod p^(k+1))`.

*Proof.* Put `N = p^(k+1)·m` and `M = p^k·m`, so `N = pM`. Every divisor of `M` divides `N`, so
for any `g`

`Σ_{d ∣ N} g(d) − Σ_{d ∣ M} g(d) = Σ_{d ∣ N, d ∤ M} g(d)`,   (∗)

and by 3.1 (with `M` for `m`) every `d` in the last sum is divisible by `p^(k+1)`, since
`p^(k+1) ∣ N = pM`.

(⇒) For `m = 0` both sides are `f(0)`. For `m > 0`, apply (∗) to `g(d) = d·O_f(d)`. By 2.4 the
left side is `f(N) − f(M)`, and every term on the right is divisible by `p^(k+1)`.

(⇐) We show `n ∣ S_f(n)` by strong induction on `n`. For `n = 0` there is nothing to prove. For
`n > 0` it suffices to show that `p^(k+1) ∣ S_f(n)` whenever `p^(k+1) ∣ n`. Write `n = N` as
above, with `m > 0`. Apply (∗) to `g = S_f`: by 2.1 the left side is `f(N) − f(M)`, which is
divisible by `p^(k+1)` by hypothesis. On the right, `d = N` occurs, because `M < N`. Every
other `d` is smaller than `N`, so `d ∣ S_f(d)` by induction, and `p^(k+1) ∣ d`. Hence
`p^(k+1) ∣ S_f(N)`. ∎

## 4. Closure properties

**4.1** (`gaussSubring`, `mem_gaussSubring`, `isGaussSeq_const`, `IsGaussSeq.add`, `.neg`,
`.sub`, `.mul`). The sequences satisfying the Gauss congruences form a subring of `ℕ → ℤ`, and
it contains the constant sequences.

*Proof.* By 3.2, membership is a family of congruences, one for each `(p, k, m)`, between two
values of `f`. Constant sequences satisfy each one trivially, and congruences modulo a fixed
number survive sums, negatives and products. ∎

**4.2** (`IsGaussSeq.comp_mul`). If `f` satisfies the Gauss congruences, so does
`n ↦ f(rn)`. This is 3.2 for `f` with `rm` in place of `m`.

## 5. Burnside's formula

**5.1** (`IsGaussSeq.sum_totient_mul`). If `f` satisfies the Gauss congruences, then
`Σ_{d ∣ n} φ(d)·f(n/d) = n·Σ_{d ∣ n} O_f(d)`. So `n` divides the left side.

*Proof.* For `n = 0` both sides are `0`. Let `n > 0` and write `∗` for Dirichlet convolution.
Let `ζ(d) = 1` for `d > 0` and `ψ(d) = d·O_f(d)`. Then `f = ζ ∗ ψ` at positive arguments
(2.4), and `(φ ∗ ζ)(d) = Σ_{e ∣ d} φ(e) = d` by Gauss's identity. By associativity,

`Σ_{de = n} φ(d)·f(e) = (φ ∗ (ζ ∗ ψ))(n) = ((φ ∗ ζ) ∗ ψ)(n) = Σ_{de = n} d·e·O_f(e)
= n·Σ_{e ∣ n} O_f(e)`. ∎

## 6. Powers

**6.1** (`isGaussSeq_pow`). For every integer `a`, `n ↦ aⁿ` satisfies the Gauss congruences:
`n ∣ Σ_{d ∣ n} μ(d)·a^(n/d)`. For `n = p` this is Fermat's little theorem `p ∣ aᵖ − a`.

*Proof.* We check 3.2. Put `x = a^m`. Then `a^(p^(k+1)·m) = (xᵖ)^(p^k)` and `a^(p^k·m) = x^(p^k)`.
By Fermat's little theorem `p ∣ xᵖ − x`. Now if `p ∣ y − z`, then `p^(k+1) ∣ y^(p^k) − z^(p^k)`.
This is induction on `k`: if `p^j ∣ Y − Z` with `j ≥ 1`, then
`Yᵖ − Zᵖ = (Y − Z)·Σ_{i<p} Y^i·Z^(p−1−i)`, and the sum is `≡ p·Z^(p−1) ≡ 0 (mod p)`, so
`p^(j+1) ∣ Yᵖ − Zᵖ`. Apply this with `y = xᵖ`, `z = x`. ∎

## 7. Periodic points

Here `T` is a map from a finite set `X` to itself. The *minimal period* of `x` is the least
`d > 0` with `T^d(x) = x`, or `0` if there is none. If `x` has minimal period `d`, its
*orbit* is the cycle `(x, Tx, …, T^(d−1)x)`, which is empty if `d = 0`. Let `P_n` be the set
of orbits of points of minimal period `n` (`periodicOrbits`).

**7.1** (`card_toFinset_periodicOrbit`). The orbit of `x` has exactly `d` distinct elements, where
`d` is the minimal period of `x`.

**7.2** (`card_minimalPeriod_eq`). For `n > 0` there are `n·|P_n|` points of minimal period `n`.

*Proof.* Sort the points of minimal period `n` by their orbit. If `y` has minimal period `n`,
the points `x` of minimal period `n` with the same orbit as `y` are exactly the points of that
orbit: such `x` lies on its own orbit, and conversely every `x = T^i(y)` has the same minimal
period and the same orbit as `y`. So each orbit in `P_n` accounts for `n` points by 7.1. ∎

**7.3** (`card_fixedPoints_iterate`). For `n > 0`, the number of fixed points of `Tⁿ` is
`Σ_{d ∣ n} |{x : x has minimal period d}|`.

*Proof.* `Tⁿ(x) = x` if and only if the minimal period of `x` divides `n`, and then it is a
positive divisor of `n`. Sort the fixed points of `Tⁿ` by their minimal period. ∎

**7.4** (`sum_mul_card_periodicOrbits`, `isGaussSeq_card_fixedPoints`,
`orbitCount_card_fixedPoints`). Let `F(n)` be the number of fixed points of `Tⁿ`. Then
`F(n) = Σ_{d ∣ n} d·|P_d|` for `n > 0`. So `F` satisfies the Gauss congruences, and
`O_F(n) = |P_n|` is the number of periodic orbits of length `n`, for `n > 0`.

*Proof.* The formula is 7.3 combined with 7.2. Then apply 2.5 and 2.3 with `h(d) = |P_d|`. ∎

## 8. Necklace numbers

**Definition** (`necklace`). `M(a, n) = O_f(n)` for `f(n) = aⁿ`, that is,
`M(a, n) = (Σ_{d ∣ n} μ(d)·a^(n/d))/n`, an exact division by 6.1. Classically, for `a ≥ 0`
this counts the aperiodic necklaces of `n` beads in `a` colours, and for `a` a prime power the
monic irreducible polynomials of degree `n` over the field with `a` elements. The first fact is
not proved here. The second is `card_monicIrreducibles_eq_necklace` in
`MathInfra/FormalizedElsewhere/IrreducibleCount.lean`.

By 6.1, the results of §2 and §5 apply.

**8.1** (`mul_necklace`, `sum_mul_necklace`). `n·M(a, n) = Σ_{d ∣ n} μ(d)·a^(n/d)`, and
`Σ_{d ∣ n} d·M(a, d) = aⁿ` for `n > 0`.

**8.2** (`necklace_one`, `necklace_prime`). `M(a, 1) = a` and `p·M(a, p) = aᵖ − a`.

*Proof.* `M(a, 1) = μ(1)·a¹/1 = a`. The divisors of `p` are `1` and `p`, with
`μ(1) = 1` and `μ(p) = −1`, so `p·M(a, p) = aᵖ − a` by 8.1. ∎

**8.3** (`sum_totient_mul_pow`). `Σ_{d ∣ n} φ(d)·a^(n/d) = n·Σ_{d ∣ n} M(a, d)`. This is 5.1. For
`a ≥ 0` and `n > 0`, the left side divided by `n` is, classically, Burnside's count of all
necklaces of `n` beads in `a` colours.
