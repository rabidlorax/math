# Ramanujan sums: the proofs in ordinary language

This is the human-readable companion to `MathInfra/FormalizedElsewhere/RamanujanSum.lean`. Each numbered
statement names the Lean theorem that checks it, and the proofs follow the same route as the
Lean proofs.

Throughout, `q`, `r`, `d`, `e` are natural numbers, `n` and `m` are integers, `μ` is the
Möbius function and `φ` is Euler's totient. Write

`δₙ(d) = d` if `d ∣ n`, and `δₙ(d) = 0` otherwise.

Lean's convention is that `0` has no divisors and that the sets of `0`-th roots of unity and of
primitive `0`-th roots of unity are empty, so sums over these are `0`.

## 1. Definition

**Definition** (`ramanujanSum`). `c_q(n) = Σ_{d ∣ q, d ∣ n} μ(q/d)·d`.

So `c_0(n) = 0` and `c_1(n) = 1` (`ramanujanSum_zero_left`, `ramanujanSum_one_left`).

**1.1** (`ramanujanSum_congr`, `ramanujanSum_neg`). If `n ≡ m (mod q)` then
`c_q(n) = c_q(m)`, and `c_q(−n) = c_q(n)`.

*Proof.* Only divisors `d` of `q` occur, and for those `d ∣ n ⟺ d ∣ m`, because `d` divides
`q`, hence `n − m`. Likewise `d ∣ −n ⟺ d ∣ n`. ∎

## 2. Möbius inversion

**2.1** (`ramanujanSum_eq_sum_divisorsAntidiagonal`). `c_q(n) = Σ_{ab = q} μ(a)·δₙ(b)`, so
`c_q(n)` is the Dirichlet convolution `(μ ∗ δₙ)(q)`. This is the definition with `a = q/d`,
`b = d`.

**2.2** (`sum_ramanujanSum`). `Σ_{d ∣ q} c_d(n) = δₙ(q)`.

*Proof.* For `q = 0` both sides are `0`. For `q > 0` this is Möbius inversion applied
to 2.1. ∎

**2.3 Uniqueness** (`eq_ramanujanSum_of_sum_eq`). Let `q > 0` and let `f` take values in any
ring. If `Σ_{e ∣ d} f(e) = δₙ(d)` for every `d ∣ q`, then `f(q) = c_q(n)`.

*Proof.* The divisors of `q` form a set closed under taking divisors, and Möbius inversion
holds on such a set. So `f(q) = Σ_{ab = q} μ(a)·δₙ(b)`, which is `c_q(n)` by 2.1. ∎

## 3. Values

**3.1** (`ramanujanSum_zero_right`). `c_q(0) = φ(q)`.

*Proof.* For `q = 0` both sides are `0`. Otherwise apply 2.3 with `f = φ`: by Gauss's identity,
`Σ_{e ∣ d} φ(e) = d = δ₀(d)` for every `d`. ∎

**3.2** (`ramanujanSum_of_isCoprime`, `ramanujanSum_one_right`). If `gcd(q, n) = 1` then
`c_q(n) = μ(q)`. In particular `c_q(1) = μ(q)`.

*Proof.* For `q = 0` both sides are `0`. Otherwise only `d = 1` divides both `q` and `n`, and
its term is `μ(q)`. ∎

**3.3 Prime powers** (`ramanujanSum_prime_pow_succ`). For a prime `p`,
`c_{p^(k+1)}(n) = δₙ(p^(k+1)) − δₙ(p^k)`.

*Proof.* The divisors of `p^(k+1)` are those of `p^k` together with `p^(k+1)`. Subtract 2.2
for `p^k` from 2.2 for `p^(k+1)`. ∎

**3.4** (`ramanujanSum_prime`). For a prime `p`: `c_p(n) = p − 1` if `p ∣ n`, and `−1`
otherwise. This is 3.3 with `k = 0`.

## 4. Multiplicativity

**4.1** (`ramanujanSum_mul`). If `gcd(q, r) = 1` then `c_{qr}(n) = c_q(n)·c_r(n)`.

*Proof.* For coprime `a`, `b`: `ab ∣ n ⟺ a ∣ n and b ∣ n`, so `δₙ(ab) = δₙ(a)·δₙ(b)`. Thus
`δₙ` is multiplicative, and so is `μ`. A Dirichlet convolution of multiplicative functions is
multiplicative, and `c_q(n) = (μ ∗ δₙ)(q)` by 2.1. ∎

## 5. Hölder's formula

**5.1** (`ramanujanSum_mul_totient`). Let `g = gcd(q, n)`. Then
`c_q(n)·φ(q/g) = μ(q/g)·φ(q)`.

*Proof.* Fix `n`. For `q = 0` both sides are `0`. For coprime `a`, `b` we have
`gcd(ab, n) = gcd(a, n)·gcd(b, n)`, so `q ↦ q/gcd(q, n)` sends `ab` to the product of the
images of `a` and `b`, which are coprime. Composing a multiplicative function with this map
therefore gives a multiplicative function. With 4.1, both sides are pointwise products of
multiplicative functions of `q`, hence multiplicative, so it suffices to check prime powers.

For `q = 1` both sides are `1`. Let `q = p^(k+1)`. Then `g = p^j` with `j ≤ k + 1`, and
`p^j ∣ n`, but `p^(j+1) ∤ n` when `j ≤ k`. Use 3.3 and `φ(p^(k+1)) = p^k(p − 1)`:

- `j = k + 1`: `c_q(n) = p^(k+1) − p^k` and `q/g = 1`. Both sides are `p^k(p − 1)`.
- `j = k`: `c_q(n) = −p^k` and `q/g = p`. Both sides are `−p^k(p − 1)`.
- `j < k`: neither `p^k` nor `p^(k+1)` divides `n`, so `c_q(n) = 0`. And
  `q/g = p^(k+1−j)` has exponent at least `2`, so `μ(q/g) = 0`. Both sides are `0`. ∎

**5.2** (`ramanujanSum_eq_moebius_mul_totient_div`). `c_q(n) = μ(q/g)·(φ(q)/φ(q/g))`, and the
division is exact.

*Proof.* For `q = 0` both sides are `0`. Otherwise `q/g` divides `q`, so `φ(q/g)` divides
`φ(q)`, and `φ(q/g) > 0`. Divide 5.1 by `φ(q/g)`. ∎

So `c_q(n)` depends on `n` only through `gcd(q, n)`, and it vanishes unless `q/gcd(q, n)` is
squarefree.

## 6. Roots of unity

Here `R` is an integral domain, and `n` is a natural number.

**6.1** (`IsPrimitiveRoot.sum_nthRootsFinset_pow`). If `ξ` is a primitive `d`-th root of unity
in `R`, then `Σ_{η^d = 1} η^n` is `d` if `d ∣ n`, and `0` otherwise.

*Proof.* For `d = 0` the sum is empty. If `d ∣ n`, every term is `1`, and there are `d`
roots. Otherwise let `S` be the sum. Multiplication by `ξ` permutes the `d`-th roots of unity,
with inverse multiplication by `ξ^(d−1)`. So `S = Σ (ξη)^n = ξ^n·S`, that is
`(ξ^n − 1)·S = 0`. Since `d ∤ n` we have `ξ^n ≠ 1`, so `S = 0`. ∎

**6.2** (`IsPrimitiveRoot.sum_primitiveRoots_pow`). If `R` has a primitive `q`-th root of unity
`ζ`, then the sum of `η^n` over the primitive `q`-th roots of unity `η` is `c_q(n)`.

*Proof.* For `q = 0` both sides are `0`. For `q > 0`, let `F(d)` be the sum of `η^n` over the
primitive `d`-th roots `η`. For `d ∣ q`, the `d`-th roots of unity are the disjoint union, over
`e ∣ d`, of the primitive `e`-th roots. So `Σ_{e ∣ d} F(e) = Σ_{η^d = 1} η^n`. Since `ζ^(q/d)`
is a primitive `d`-th root, this is `δₙ(d)` by 6.1. Now apply 2.3. ∎

**6.3** (`IsPrimitiveRoot.sum_pow_coprime`). In the same situation,
`c_q(n) = Σ_{k < q, gcd(k, q) = 1} ζ^(kn)`.

*Proof.* `k ↦ ζ^k` is a bijection from the `k < q` coprime to `q` onto the primitive `q`-th
roots of unity, and `ζ^(kn) = (ζ^k)^n`. Apply 6.2. ∎

**6.4** (`ramanujanSum_eq_sum_exp`). In `ℂ`: `c_q(n) = Σ_{k < q, gcd(k, q) = 1} e^(2πikn/q)`.
For `q = 0` both sides are `0`; otherwise this is 6.3 with `ζ = e^(2πi/q)`.

With `n = 1` and `n = 0`, 6.2 recovers two classical facts. The primitive `q`-th roots of unity
sum to `μ(q)`, and (in characteristic `0`) there are `φ(q)` of them.
