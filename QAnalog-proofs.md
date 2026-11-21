# q-analogues: the proofs in ordinary language

This is the human-readable companion to `MathInfra/QAnalog.lean`. Each numbered statement
names the Lean theorem that checks it; the definitions in section 1 are `qNat`,
`qFactorial` and `gaussBinom`. The proofs follow the same route as the Lean proofs.

Throughout, `R` is a commutative semiring (so there is no subtraction and no division unless
stated) and `q` is any element of `R`. Subtraction of natural numbers is truncated: `n − k = 0`
when `k > n`.

## 1. Definitions

- **q-number** (`qNat`). `[n] = 1 + q + q² + ⋯ + q^(n−1)`, the sum of `q^i` over `i < n`. So
  `[0] = 0` and `[1] = 1` (`qNat_zero`, `qNat_one`).
- **q-factorial** (`qFactorial`). `[n]! = [1]·[2]·⋯·[n]`, so `[0]! = 1`, `[1]! = 1` and
  `[n+1]! = [n]!·[n+1]` (`qFactorial_zero`, `qFactorial_one`, `qFactorial_succ`).
- **Gaussian binomial coefficient** (`gaussBinom`). `G(n, k)` is defined by recursion:
  - `G(n, 0) = 1` (`gaussBinom_zero_right`),
  - `G(0, k+1) = 0` (`gaussBinom_zero_succ`),
  - `G(n+1, k+1) = G(n, k) + q^(k+1)·G(n, k+1)` (`gaussBinom_succ_succ`).
    **(P1, first q-Pascal rule)**

When `q` matters we write `[n]_q` and `G_q(n, k)`.

### The q-Pascal triangle

The first rows of `G(n, k)`, computed from P1 (the interior entries of rows 2 to 4 are
checked in `MathInfraTest/QAnalog.lean`):

```
n = 0:   1
n = 1:   1    1
n = 2:   1    1+q    1
n = 3:   1    1+q+q²    1+q+q²    1
n = 4:   1    1+q+q²+q³    1+q+2q²+q³+q⁴    1+q+q²+q³    1
```

Several of the results below can be seen here in miniature. Setting `q = 1` gives Pascal's
triangle (3.4). Each row reads the same in both directions (5.1). The entry `G(4, 2)` has
degree `2·2 = 4` and leading coefficient `1` (9.1), and its value at `q = 2` is `35`, the
classical count of planes in a 4-dimensional space over the field with two elements (a fact
not proved here).

## 2. q-numbers and q-factorials

**2.1** (`qNat_succ`, `qNat_succ'`). `[n+1] = [n] + q^n` and `[n+1] = 1 + q·[n]`.

*Proof.* The first splits off the last term of the sum, the second splits off the first term
and factors `q` out of the rest. ∎

**2.2** (`qNat_add`). `[m+n] = [m] + q^m·[n]`.

*Proof.* Induction on `n`. For `n = 0` both sides are `[m]`. For the step, by 2.1 and the
induction hypothesis,

```
[m+n+1] = [m+n] + q^(m+n) = [m] + q^m·[n] + q^m·q^n = [m] + q^m·([n] + q^n) = [m] + q^m·[n+1].  ∎
```

**2.3** (`qNat_mul`). `[m·n]_q = [m]_q · [n]_{q^m}`.

*Proof.* Induction on `n`. For `n = 0` both sides are `0`. For the step, by 2.2, the induction
hypothesis and 2.1 (for `q^m`),

```
[m·n + m]_q = [m·n]_q + q^(m·n)·[m]_q = [m]_q·[n]_{q^m} + [m]_q·(q^m)^n = [m]_q·[n+1]_{q^m}.  ∎
```

**2.4** (`qNat_one_left`, `qNat_zero_left`, `sub_one_mul_qNat`). At `q = 1`, `[n] = n`. At
`q = 0`, `[n+1] = 1`. If `R` is a ring, `(q − 1)·[n] = q^n − 1`.

*Proof.* At `q = 1` every term of the sum is `1`. At `q = 0`, 2.1 gives
`[n+1] = 1 + 0·[n] = 1`. The third is the telescoping geometric sum. ∎

**2.5** (`qFactorial_one_left`, `qFactorial_zero_left`). At `q = 1`, `[n]! = n!`. At `q = 0`,
`[n]! = 1`.

*Proof.* By 2.4 every factor `[i+1]` of `[n]!` is `i+1` at `q = 1`, and is `1` at `q = 0`. ∎

## 3. First properties of `G`

**3.1** (`gaussBinom_eq_zero_of_lt`, `gaussBinom_succ_self`). If `n < k` then `G(n, k) = 0`.
In particular `G(n, n+1) = 0`.

*Proof.* Induction on `n`, for all `k`. If `n = 0` then `k ≥ 1` and `G(0, k) = 0` by
definition. For `n+1 < k`, write `k = j+1` with `n < j`; by P1,
`G(n+1, j+1) = G(n, j) + q^(j+1)·G(n, j+1)`, and both terms vanish by the induction
hypothesis. ∎

**3.2** (`gaussBinom_self`). `G(n, n) = 1`.

*Proof.* Induction: `G(n+1, n+1) = G(n, n) + q^(n+1)·G(n, n+1) = 1 + 0` by 3.1. ∎

**3.3** (`gaussBinom_one_right`). `G(n, 1) = [n]`.

*Proof.* Induction: `G(n+1, 1) = G(n, 0) + q·G(n, 1) = 1 + q·[n] = [n+1]` by 2.1. ∎

**3.4** (`gaussBinom_one_left`, `gaussBinom_zero_left`). At `q = 1`, `G(n, k)` is the ordinary
binomial coefficient. At `q = 0`, `G(n, k) = 1` whenever `k ≤ n`.

*Proof.* At `q = 1`, P1 is Pascal's rule with the same boundary values. At `q = 0`, P1 reads
`G(n+1, k+1) = G(n, k)`, so induction on `n` gives `1`. ∎

**3.5** (`map_gaussBinom`, `map_qNat`, `map_qFactorial`). For a semiring homomorphism
`f : R → S` into a commutative semiring `S`, `f(G_q(n, k)) = G_{f(q)}(n, k)`. Likewise for
`[n]` and `[n]!`. In particular the casts `ℕ → R`, and `ℤ → R` for a commutative ring `R`,
commute with all three (`Nat.cast_qNat`, `Nat.cast_qFactorial`, `Nat.cast_gaussBinom`,
`Int.cast_qNat`, `Int.cast_qFactorial`, `Int.cast_gaussBinom`).

*Proof.* `G` is built from `q` using only `0`, `1`, `+`, `·`, which `f` preserves; formally,
induction along the recursion. For `[n]` and `[n]!`, `f` commutes with finite sums and
products. The casts are semiring homomorphisms. ∎

## 4. The second q-Pascal rule

**Theorem 4.1** (`gaussBinom_succ_succ'`). For all `n, k`,
`G(n+1, k+1) = q^(n−k)·G(n, k) + G(n, k+1)`. **(P2)**

*Proof.* Induction on `n`, for all `k` at once.

*Base `n = 0`.* If `k = 0`: `G(1, 1) = 1` and the right side is `q⁰·1 + 0 = 1`. If `k ≥ 1`:
every term is `0` by 3.1.

*Step.* Assume P2 for `n` and all `k`. We show
`G(n+2, k+1) = q^(n+1−k)·G(n+1, k) + G(n+1, k+1)`.

*Case `k = 0`.* By 3.3 and `G(n+1, 0) = 1`, the left side is `[n+2]` and the right side is
`q^(n+1) + [n+1]`, which is `[n+2]` by 2.1. (The induction hypothesis is not needed here.)

*Case `k = j+1`.* Start with P1, then apply the induction hypothesis to both terms:

```
G(n+2, j+2) = G(n+1, j+1) + q^(j+2)·G(n+1, j+2)
            = q^(n−j)·G(n, j) + G(n, j+1)
              + q^(j+2)·( q^(n−j−1)·G(n, j+1) + G(n, j+2) ).
```

The target right side, with P1 applied to both of its terms, is

```
q^(n−j)·( G(n, j) + q^(j+1)·G(n, j+1) ) + G(n, j+1) + q^(j+2)·G(n, j+2).
```

The two expressions agree term by term, except that one has `q^(j+2)·q^(n−j−1)·G(n, j+1)`
where the other has `q^(n−j)·q^(j+1)·G(n, j+1)`. If `j+1 ≤ n` both exponents equal `n+1`. If
`j+1 > n` then `G(n, j+1) = 0` by 3.1 and both terms vanish. ∎

## 5. Symmetry

**Theorem 5.1** (`gaussBinom_symm_add`, `gaussBinom_symm`). `G(a+b, a) = G(a+b, b)`.
Equivalently `G(n, n−k) = G(n, k)` for `k ≤ n`.

*Proof.* Induction on `n = a+b`, for all splittings. If `a = 0` or `b = 0`, both sides are
`1` (one by definition, the other by 3.2). Otherwise write `a = a'+1`, `b = b'+1`, `n = m+1`
with `a' + b' + 1 = m`. Apply P1 on the left and P2 on the right, noting `m − b' = a'+1`:

```
G(m+1, a'+1) = G(m, a') + q^(a'+1)·G(m, a'+1),
G(m+1, b'+1) = q^(a'+1)·G(m, b') + G(m, b'+1).
```

Since `m = a' + (b'+1) = (a'+1) + b'`, the induction hypothesis gives `G(m, a') = G(m, b'+1)`
and `G(m, a'+1) = G(m, b')`. The two right sides are therefore equal. ∎

**Corollary 5.2** (`gaussBinom_succ_self_right`). `G(n+1, n) = [n+1]`, by 5.1 and 3.3.

## 6. Absorption

**Theorem 6.1** (`qNat_succ_mul_gaussBinom`, `qNat_succ_mul_gaussBinom_succ`). For all `n, k`:

- **(B)** `[k+1]·G(n, k+1) = [n−k]·G(n, k)`,
- **(A)** `[k+1]·G(n+1, k+1) = [n+1]·G(n, k)`.

*Proof.* First, **B for a given `n` (all `k`) implies A for that `n`.** If `k > n` both sides
of A are `0`. If `k ≤ n` then `[n+1] = [k+1] + q^(k+1)·[n−k]` by 2.2, and by P1 and B,

```
[k+1]·G(n+1, k+1) = [k+1]·G(n, k) + q^(k+1)·[k+1]·G(n, k+1)
                  = [k+1]·G(n, k) + q^(k+1)·[n−k]·G(n, k) = [n+1]·G(n, k).
```

Now prove B by induction on `n`. For `n = 0`: if `k = 0` the right side has the factor
`[0] = 0` and the left has `G(0, 1) = 0`; if `k ≥ 1` both `G` values vanish.

For `n+1`: if `k = 0` the claim is `G(n+1, 1) = [n+1]`, which is 3.3. If `k = j+1`, we must
show `[j+2]·G(n+1, j+2) = [n−j]·G(n+1, j+1)`. By A for `n` (available from the induction
hypothesis), the left side is `[n+1]·G(n, j+1)`. If `j ≥ n` both sides are `0`. If `j < n`,
by P1, B for `n`, and `[n+1] = [j+1] + q^(j+1)·[n−j]` (2.2, as `j ≤ n`),

```
[n−j]·G(n+1, j+1) = [n−j]·G(n, j) + q^(j+1)·[n−j]·G(n, j+1)
                  = [j+1]·G(n, j+1) + q^(j+1)·[n−j]·G(n, j+1) = [n+1]·G(n, j+1).
```

This proves B for all `n`, and A follows by the first step. ∎

## 7. The factorial formula

Classically one writes `G(n, k) = [n]! / ([k]!·[n−k]!)`. In a general semiring `[k]!` may
be zero or a zero divisor, and it may be zero even in a field once `k` is large enough (for
instance `q = 1` in characteristic 2 with `k ≥ 2`, or `q ≠ 1` a root of unity of order at
most `k`). So the main statement is made without division, and the quotient form is
Corollary 7.2.

**Theorem 7.1** (`add_gaussBinom_mul_qFactorial_mul_qFactorial`).
`G(a+b, a)·[a]!·[b]! = [a+b]!`.

*Proof.* Induction on `a`. For `a = 0` the claim is `[b]! = [b]!`, since `G(b, 0) = 1`. For
the step, use `[a+1]! = [a]!·[a+1]`, then absorption (6.1 A, with `n = a+b` and `k = a`),
then the induction hypothesis:

```
G(a+b+1, a+1)·[a+1]!·[b]! = [a+1]·G(a+b+1, a+1)·[a]!·[b]!
                          = [a+b+1]·G(a+b, a)·[a]!·[b]!
                          = [a+b+1]·[a+b]! = [a+b+1]!.  ∎
```

**Corollary 7.2** (`gaussBinom_mul_qFactorial_mul_qFactorial`, `gaussBinom_eq_div`). For
`k ≤ n`, `G(n, k)·[k]!·[n−k]! = [n]!`. If moreover `R` is a semifield and
`[k]!·[n−k]! ≠ 0`, then `G(n, k) = [n]! / ([k]!·[n−k]!)`.

*Proof.* Put `a = k`, `b = n − k` in 7.1, then divide by the nonzero denominator. ∎

## 8. The q-binomial theorem

**Theorem 8.1** (`prod_one_add_pow_mul`; Gauss, Rothe). For every `x` in `R` and every `n`,

```
(1 + x)(1 + q·x)(1 + q²·x)⋯(1 + q^(n−1)·x) = Σ_{k=0}^{n} q^(k(k−1)/2)·G(n, k)·x^k.
```

(Lean writes the exponent `k(k−1)/2` as `k.choose 2`.)

*Proof.* Write `c(k) = k(k−1)/2`, so `c(k+1) = c(k) + k`. Induction on `n`, for all `x`. For
`n = 0` both sides are `1`.

For `n+1`, pull out the factor `1 + x` and note `q^(i+1)·x = q^i·(q·x)`, so the remaining
product is the `n`-fold product at `q·x`. By the induction hypothesis the left side is

```
(1 + x) · Σ_{k=0}^{n} q^c(k)·G(n, k)·q^k·x^k.
```

Expand and collect the terms by power of `x` (here `x` is an element of `R`, so "the
coefficient of `x^k`" just means the factor multiplying `x^k` after this regrouping of a
finite sum). The coefficient of `x^0` is `1`. For `0 ≤ k ≤ n`, the coefficient of `x^(k+1)` is

```
q^c(k+1)·q^(k+1)·G(n, k+1)  +  q^c(k)·q^k·G(n, k)
  = q^c(k+1)·( q^(k+1)·G(n, k+1) + G(n, k) ) = q^c(k+1)·G(n+1, k+1)
```

using `c(k) + k = c(k+1)` and P1. (For `k = n` the first term is absent, consistent with
`G(n, n+1) = 0`.) These are exactly the coefficients on the right side for `n+1`. ∎

**Corollary 8.2** (`one_add_pow_eq_sum_choose`). `(1 + x)^n = Σ_{k=0}^{n} C(n, k)·x^k`, where
`C(n, k)` is the ordinary binomial coefficient.

*Proof.* Put `q = 1` in 8.1: every factor on the left is `1 + x`, and on the right
`q^c(k) = 1` and `G_1(n, k) = C(n, k)` by 3.4. ∎

This is the binomial theorem for `(1 + x)^n`, already in Mathlib as a case of `add_pow`. It
is recorded as a consistency check on 8.1, not as a new result.

## 9. `G` as a polynomial in `q`

**Theorem 9.1** (`gaussBinom_X_monic`, `gaussBinom_X_natDegree`). Take `q = X` in `R[X]` and
let `k ≤ n`. The polynomial `G_X(n, k)` is monic, and if `R` is nontrivial its degree is
`k(n−k)`. (Lean states the degree as `natDegree`, which is the degree here because the
polynomial is nonzero. The joint statement used in the induction is
`gaussBinom_X_monic_and_natDegree`.)

*Proof.* If `R` is trivial, every polynomial is monic and there is nothing to prove. Let `R`
be nontrivial. Induction on `n`, for all `k ≤ n`. `G(n, 0) = 1` and `G(n, n) = 1` are monic
of degree `0`. For the remaining case `G(n+1, k+1)` with `k < n`, P1 gives

```
G(n+1, k+1) = G(n, k) + X^(k+1)·G(n, k+1).
```

By induction the first summand has degree `k(n−k)`, and the second is monic of degree
`(k+1) + (k+1)(n−k−1) = (k+1)(n−k)`. Since `n − k ≥ 1`, the second degree is strictly
larger, so the sum is monic of degree `(k+1)(n−k) = (k+1)((n+1) − (k+1))`. ∎

**Theorem 9.2, universality** (`aeval_gaussBinom_X`, `aeval_qNat_X`, `aeval_qFactorial_X`;
special cases `eval_gaussBinom_X`, `eval_qNat_X`, `eval_qFactorial_X`). Let `A` be a
commutative semiring and `R` an `A`-algebra. For every `q` in `R`, evaluating the polynomial
`G_X(n, k)` in `A[X]` at `q` gives `G_q(n, k)`. Likewise for `[n]` and `[n]!`.

*Proof.* Evaluation at `q` is a semiring homomorphism `A[X] → R` sending `X` to `q`; apply
3.5. The case `A = R` is ordinary evaluation of a polynomial over `R`. ∎

Every commutative semiring is an `ℕ`-algebra and every commutative ring is a `ℤ`-algebra, so
there is a single polynomial `G_X(n, k)` in `ℕ[X]` whose values are all the Gaussian binomials.
That much is the theorem. What follows is a recipe, not a Lean theorem: an equation in the one
variable `q`, built from Gaussian binomials, q-numbers, q-factorials, natural-number constants
and powers of `q` using `+` and `·`, and proved once in `ℕ[X]`, holds for every `q` in every
commutative semiring (apply evaluation at `q` to both sides), and one proved in `ℤ[X]`, where
subtraction and cancellation are available, holds for every `q` in every commutative ring. It
does not cover identities with a second element such as the `x` of 8.1, or non-equational facts
such as 9.1; terms with another base, such as `[n]_{q^m}`, need 3.5 as well.
