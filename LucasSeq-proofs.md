# Lucas sequences: the proofs in ordinary language

This is the human-readable companion to `MathInfra/LucasSeq.lean`. Each numbered statement
names the Lean theorem that checks it, and the proofs follow the same route as the Lean
proofs.

Throughout, `R` is a commutative ring, `P` and `Q` are elements of `R`, and
`D = P² − 4Q` is the discriminant of `x² − Px + Q`. Nothing is ever divided by `2`, by `D`
or by a difference of roots, so everything in sections 1 to 8 (except 8.5, which is over `ℤ`)
holds in every commutative ring, including characteristic 2 and rings with zero divisors.

## 1. Definitions

- **A solution** (`IsLucasRec`) is a sequence `W(0), W(1), …` in `R` with
  `W(n+2) = P·W(n+1) − Q·W(n)` for all `n`. **(Rec)**
- **First kind** (`lucasU`). `U` is the solution with `U(0) = 0`, `U(1) = 1` (`lucasU_zero`,
  `lucasU_one`, `lucasU_add_two`, `isLucasRec_lucasU`). So `U(2) = P`, `U(3) = P² − Q`
  (`lucasU_two`, `lucasU_three`).
- **Second kind** (`lucasV`). `V` is the solution with `V(0) = 2`, `V(1) = P` (`lucasV_zero`,
  `lucasV_one`, `lucasV_add_two`, `isLucasRec_lucasV`). So `V(2) = P² − 2Q` (`lucasV_two`).

"Two-step induction" below means: prove the statement for `n = 0` and `n = 1`, and derive it
for `n + 2` from `n` and `n + 1`.

A ring homomorphism `f` sends `U(n)` for `(P, Q)` to `U(n)` for `(f P, f Q)`, and likewise
for `V` (`map_lucasU`, `map_lucasV`), by two-step induction.

## 2. General solutions

**2.1 Shift formula** (`IsLucasRec.add_succ`). For every solution `W`,
`W(m+n+1) = U(n+1)·W(m+1) − Q·U(n)·W(m)`.

*Proof.* Two-step induction on `n`. For `n = 0` it reads `W(m+1) = W(m+1)`, for `n = 1` it is
(Rec). For `n + 2`, expand `W(m+n+3)` by (Rec), apply the two induction hypotheses, and
collect the coefficients of `W(m+1)` and `W(m)`: they are `P·U(n+2) − Q·U(n+1) = U(n+3)` and
`−Q·(P·U(n+1) − Q·U(n)) = −Q·U(n+2)`. ∎

**2.2** (`IsLucasRec.eq_lucasU`, `IsLucasRec.ext`). Taking `m = 0`:
`W(n+1) = W(1)·U(n+1) − Q·W(0)·U(n)`. So a solution is determined by `W(0)` and `W(1)`.

**2.3 Step-`m` recurrence** (`IsLucasRec.add_two_mul`). For every solution `W`,
`W(k+2m) = V(m)·W(k+m) − Q^m·W(k)`.

*Proof.* Two-step induction on `m`, for all `k` at once. `m = 0`: `W(k) = 2W(k) − W(k)`.
`m = 1` is (Rec). For `m + 2`: by (Rec), `W(k+2m+4) = P·W(k+2m+3) − Q·W(k+2m+2)`. Apply the
hypothesis for `m + 1` at `k + 1` and for `m` at `k + 2`:

`W(k+2m+4) = (P·V(m+1) − Q·V(m))·W(k+m+2) − Q^(m+1)·(P·W(k+1) − W(k+2))`.

The first bracket is `V(m+2)`, and `P·W(k+1) − W(k+2) = Q·W(k)` by (Rec). ∎

For `W = U` and `W = V` this is `lucasU_add_two_mul` and `lucasV_add_two_mul` (stated as
`W(k+2m) + Q^m·W(k) = V(m)·W(k+m)`). In words: the subsequence `W(k), W(k+m), W(k+2m), …` is
again a solution, with parameters `(V(m), Q^m)`.

## 3. Relations between `U` and `V`

**3.1** (`lucasV_eq_two_mul`). `V(n) = 2U(n+1) − P·U(n)`.

*Proof.* Two-step induction. `n = 0`: `2 = 2·1 − P·0`. `n = 1`: `P = 2P − P`. The step holds
because both sides satisfy (Rec). ∎

- **3.2** (`lucasV_succ`). `V(n+1) = U(n+2) − Q·U(n)`.
- **3.3** (`lucasV_succ'`). `V(n+1) = P·U(n+1) − 2Q·U(n)`.
- **3.4** (`two_mul_lucasU_succ`). `2U(n+1) = P·U(n) + V(n)`.
- **3.5** (`two_mul_lucasV_succ`). `2V(n+1) = P·V(n) + D·U(n)`.

*Proof.* Applying 3.1 at `n + 1` and substituting `U(n+2) = P·U(n+1) − Q·U(n)` gives 3.2 and
3.3; 3.4 is 3.1 rearranged; 3.5 follows from 3.3 and 3.1:
`2V(n+1) − P·V(n) = (2P·U(n+1) − 4Q·U(n)) − (2P·U(n+1) − P²·U(n)) = D·U(n)`. ∎

## 4. Addition, doubling, and the quadratic identities

**4.1** (`lucasU_add_succ`). `U(m+n+1) = U(m+1)·U(n+1) − Q·U(m)·U(n)`. This is 2.1 for `W = U`.

**4.2** (`two_mul_lucasU_add`). `2U(m+n) = U(m)·V(n) + U(n)·V(m)`.

*Proof.* For `n = 0` both sides are `2U(m)`. For `n + 1`, 4.1 gives the left side as
`2U(m+1)U(n+1) − 2Q·U(m)U(n)`; on the right replace `V(n+1)` by 3.3 and `V(m)` by 3.1 and
the `P`-terms cancel. ∎

**4.3** (`two_mul_lucasV_add`). `2V(m+n) = V(m)·V(n) + D·U(m)·U(n)`.

*Proof.* Same pattern: 2.1 for `W = V` on the left; on the right use 3.3 for `V(n+1)` and
3.5 for `D·U(m)`. ∎

**4.4 Cassini** (`lucasU_cassini`). `U(n+1)² − U(n)·U(n+2) = Q^n`.

*Proof.* Induction. `n = 0`: `1 − 0 = 1`. Step:
`U(n+2)² − U(n+1)U(n+3) = U(n+2)(U(n+2) − P·U(n+1)) + Q·U(n+1)² = Q·(U(n+1)² − U(n)U(n+2))`. ∎

**4.5** (`lucasV_sq`). `V(n)² = D·U(n)² + 4Q^n`.

*Proof.* By 3.1,
`V(n)² − D·U(n)² = 4(U(n+1)² − P·U(n)U(n+1) + Q·U(n)²) = 4(U(n+1)² − U(n)U(n+2))`,
which is `4Q^n` by 4.4. ∎

**4.6 Doubling** (`lucasU_two_mul`, `lucasV_two_mul`, `lucasU_two_mul_add_one`).

- `U(2n) = U(n)·V(n)`: trivial for `n = 0`; for `n = k + 1`, 4.1 gives
  `U(2k+2) = U(k+1)·(U(k+2) − Q·U(k))`, and the bracket is `V(k+1)` by 3.2. (Not from 4.2,
  which would need division by 2.)
- `V(2n) = V(n)² − 2Q^n`: 2.3 with `W = V`, `k = 0`.
- `U(2n+1) = U(n+1)² − Q·U(n)²`: 4.1 with `m = n`.

## 5. Composition and divisibility

**5.1** (`lucasU_mul`, `lucasV_mul`). Write `U'`, `V'` for the Lucas sequences with parameters
`(V(m), Q^m)`. Then `U(mn) = U(m)·U'(n)` and `V(mn) = V'(n)`.

*Proof.* Two-step induction on `n`. The cases `n = 0, 1` are immediate. By 2.3 with `k = mn`,
`U(mn+2m) = V(m)·U(mn+m) − Q^m·U(mn)`, which is exactly the recurrence of `U'` multiplied by
`U(m)`; the same for `V`. ∎

**5.2** (`lucasU_dvd_lucasU_mul`, `lucasU_dvd_lucasU`, `isDvdSequence_lucasU`).
`U(m) ∣ U(mn)`; that is, if `m ∣ n` then `U(m) ∣ U(n)`. Immediate from 5.1.

## 6. Binet formulas and roots

**6.1** (`pow_succ_eq_lucasU`). If `a² = P·a − Q` then `a^(n+1) = U(n+1)·a − Q·U(n)`.

*Proof.* Induction: multiply by `a`, replace `a²`, and use (Rec). ∎

**6.2** (`lucasU_binet`, `lucasV_binet`). For any `a`, `b` in `R`, with `P = a + b` and
`Q = ab`: `(a − b)·U(n) = a^n − b^n` and `V(n) = a^n + b^n`.

*Proof.* Two-step induction, using
`(a + b)(a^(n+1) ∓ b^(n+1)) − ab(a^n ∓ b^n) = a^(n+2) ∓ b^(n+2)`. ∎

If `a² = P·a − Q`, put `b = P − a`; then `a + b = P` and `ab = Q`, so 6.2 gives
`V(n) = a^n + (P − a)^n` (`lucasV_eq_pow_add_pow`).

**6.3** (`two_mul_add_pow`). If `s² = D` then `2(P + s)^n = 2^n·(V(n) + U(n)·s)`.
Informally, `((P + √D)/2)^n = (V(n) + U(n)√D)/2`.

*Proof.* Induction. Multiply the hypothesis by `P + s`:
`(V(n) + U(n)s)(P + s) = (P·V(n) + D·U(n)) + (P·U(n) + V(n))·s = 2V(n+1) + 2U(n+1)·s`
by 3.5 and 3.4. ∎

## 7. Special cases

| `(P, Q)` | `U` | `V` | Lean |
|---|---|---|---|
| `(2, 1)` | `U(n) = n` | `V(n) = 2` | `lucasU_two_one`, `lucasV_two_one` |
| `(1, −1)` | `U(n) = F(n)`, the Fibonacci numbers | `V(n+1) = F(n+2) + F(n)`, the Lucas numbers | `lucasU_one_neg_one`, `lucasV_one_neg_one_succ` |
| `(q+1, q)` | `U(n) = [n]_q = 1 + q + ⋯ + q^(n−1)`, the q-number | `V(n) = q^n + 1` | `lucasU_add_one_self`, `lucasV_add_one_self` |
| `(3, 2)` | `U(n) = 2^n − 1` | `V(n) = 2^n + 1` | `lucasU_three_two`, `lucasV_three_two` |
| `(X, a)` in `R[X]` | `U(n+1)` is the `n`-th Dickson polynomial of the second kind | `V(n)` is the `n`-th Dickson polynomial of the first kind | `lucasU_succ_X_C`, `lucasV_X_C` |
| `(X, 1)` in `R[X]` | `U(n+1) = S_n` | `V(n) = C_n` | `lucasU_succ_X_one`, `lucasV_X_one` |

Here the Dickson polynomials have parameter `a`, and `C_n`, `S_n` are the rescaled Chebyshev
polynomials `C_n(X) = 2T_n(X/2)` and `S_n(X) = U_n(X/2)` (with `T_n`, `U_n` the Chebyshev
polynomials of the first and second kind).

The `U` entries of the first three rows, `V` for `(2, 1)`, and the Dickson row are two-step
inductions comparing recurrences. `V` for `(q+1, q)` and both entries for `(3, 2)` are 6.2
with roots `q, 1` and `2, 1`. The Lucas-number entry is 3.2 applied to the Fibonacci row, and
the Chebyshev row is the Dickson row at `a = 1`.

Applying the evaluation homomorphism `X ↦ P` (`map_lucasV`, `map_lucasU`) to the Dickson row:
for any `P`, `Q` in `R`, `V(n)` is the `n`-th first-kind Dickson polynomial with parameter
`Q`, evaluated at `P`, and `U(n+1)` is the second-kind one (`lucasV_eq_eval_dickson`,
`lucasU_succ_eq_eval_dickson`).

## 8. Coprimality and strong divisibility

Now assume `P` and `Q` are coprime in the sense that `xP + yQ = 1` for some `x`, `y`
(`IsCoprime`; over `ℤ` this is the usual notion).

**8.1** (`isCoprime_lucasU_succ_right`). `U(n+1)` is coprime to `Q`.

*Proof.* Induction: `U(n+2) = P·U(n+1) − Q·U(n)` differs by a multiple of `Q` from
`P·U(n+1)`, a product of two elements coprime to `Q`. ∎

**8.2** (`isCoprime_lucasU_lucasU_succ`). `U(n)` and `U(n+1)` are coprime.

*Proof.* Induction. `U(n+1)` is coprime to `Q` (8.1) and to `U(n)` (hypothesis), hence to
`Q·U(n)`, hence to `P·U(n+1) − Q·U(n) = U(n+2)`. ∎

**8.3** (`dvd_lucasU_add_iff`, `dvd_lucasU_add_mul_iff`). If `d ∣ U(m)` then
`d ∣ U(n+m) ⟺ d ∣ U(n)`, and so `d ∣ U(n+km) ⟺ d ∣ U(n)`.

*Proof.* `m = 0` is trivial. For `m = j + 1`, 4.1 gives
`U(n+j+1) = U(j+1)·U(n+1) − Q·U(j)·U(n)`. Since `d ∣ U(j+1)`,
`d ∣ U(n+j+1) ⟺ d ∣ Q·U(j)·U(n)`. And `d` divides `U(j+1)`, which is coprime to `Q·U(j)` by
8.1 and 8.2, so `d` is coprime to `Q·U(j)` and that factor can be cancelled. The second
statement follows by induction on `k`. ∎

**8.4 Strong divisibility** (`dvd_lucasU_gcd_iff`).
`d ∣ U(gcd(m, n)) ⟺ d ∣ U(m) and d ∣ U(n)`.

*Proof.* Induction along the Euclidean algorithm. For `m = 0`: `gcd(0, n) = n` and everything
divides `U(0) = 0`. For `m > 0`, `gcd(m, n) = gcd(n mod m, m)` and, by 8.3 with
`n = (n mod m) + (n / m)·m`, a divisor of `U(m)` divides `U(n)` iff it divides `U(n mod m)`. ∎

**8.5** (`Int.gcd_lucasU`). Over `ℤ`: `gcd(U(m), U(n)) = |U(gcd(m, n))|`. Both sides are
natural numbers with the same divisors by 8.4.

## 9. Lucas sequences modulo a prime

Let `p` be an odd prime.

**9.1** (`ZMod.lucasV_prime`, `ZMod.lucasU_prime`). For `P`, `Q` in `𝔽_p`:
`V(p) = P` and `U(p) = D^((p−1)/2)`.

*Proof.* Let `A = 𝔽_p[s]/(s² − D)`, which has basis `1, s` over `𝔽_p` and characteristic
`p`. By 6.3 in `A`,

`2(P + s)^p = 2^p·(V(p) + U(p)·s)`.

In characteristic `p` the `p`-th power is additive, so `(P + s)^p = P^p + s^p`. Here
`P^p = P` (Fermat) and `s^p = (s²)^((p−1)/2)·s = D^((p−1)/2)·s`; also `2^p = 2`. So

`2·(P + D^((p−1)/2)·s) = 2·(V(p) + U(p)·s)`.

Compare the coefficients of `1` and of `s`, and cancel `2` (nonzero as `p` is odd). ∎

**9.2** (`lucasV_prime_modEq`, `lucasU_prime_modEq`). For integers `P`, `Q`:
`V(p) ≡ P` and `U(p) ≡ (D/p) (mod p)`, where `(D/p)` is the Legendre symbol.

*Proof.* Reduce modulo `p` and apply 9.1 with Euler's criterion `(D/p) ≡ D^((p−1)/2)`. ∎

**9.3 Law of apparition** (`prime_dvd_lucasU_self`, `prime_dvd_lucasU_add_one`,
`prime_dvd_lucasU_sub_one`, `prime_dvd_lucasU_sub_legendreSym`). For integers `P`, `Q`:

- if `p ∣ D` then `p ∣ U(p)`;
- if `(D/p) = −1` then `p ∣ U(p+1)`;
- if `(D/p) = 1` and `p ∤ Q` then `p ∣ U(p−1)`.

So if `p ∤ Q` then `p ∣ U(p − (D/p))`.

*Proof.* Work modulo `p` with 9.2. The first case is 9.2 itself. By 3.4,
`2U(p+1) = P·U(p) + V(p) ≡ P·(D/p) + P`, which is `0` when `(D/p) = −1`; cancel `2`. By 3.3,
`2Q·U(p−1) = P·U(p) − V(p) ≡ P·(D/p) − P`, which is `0` when `(D/p) = 1`; cancel `2Q`, a
unit modulo `p` since `p` is odd and `p ∤ Q`. ∎

For `(P, Q) = (1, −1)` this says every odd prime `p` divides the Fibonacci number
`F(p − (5/p))`; for `(P, Q) = (3, 2)`, 9.2 is Fermat's little theorem for the base `2`. Both
are checked in `MathInfraTest/LucasSeq.lean`.
