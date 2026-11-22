# Wolstenholme's theorem: the proofs in ordinary language

This is the human-readable companion to `MathInfra/FormalizedElsewhere/Wolstenholme.lean`.
Each numbered statement names the Lean theorem that checks it, and the proofs follow the same
route as the Lean proofs.

Throughout, `p` is a prime, `a`, `b`, `j`, `k`, `m`, `n` are natural numbers (in §7, `a`, `b`, `k`
are integers), and `C(n, k)` is a binomial coefficient. Fractions `1/k` modulo `p` or `p²` are
inverses there. In Lean `1/0 = 0` in `ZMod p`. For `0 < k < p` put

`c_k = C(p, k)/p`,

an integer because `p ∣ C(p, k)`.

## Prior art

Checked in November 2026.

- **Mathlib** (pinned at 2026-11-19, and `master` on 2026-11-21) has none of this. The PR
  [#29675](https://github.com/leanprover-community/mathlib4/pull/29675), closed unmerged in
  September 2026, proved 5.3 alone.
- **atlas-lean** ([facebookresearch/atlas-lean](https://github.com/facebookresearch/atlas-lean),
  a Lean 4 library) proves 6.1 (its `wolstenholme`) and defines the Fermat quotient (its
  `fermatQuotient`, with a primality argument). It also proves the `p³` congruence for
  `C(c·pᵏ, d·pᵏ)`, which includes 4.8, as a private lemma in a file outside its build.
- **formal-conjectures** ([google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures))
  links an AlphaProof proof of 5.3.
- The Isabelle AFP, HOL4, HOL Light, Coq/Rocq, Metamath and Mizar have nothing on
  Wolstenholme's theorem.
- Not found elsewhere: Babbage's theorem 5.2, Ljunggren's congruence modulo `p²` for every
  prime (4.7), and 7.2, 7.4 and 7.6–7.8.

Other names: Wolstenholme's congruence (5.3, 6.1), Babbage's congruence (5.2), and Jacobsthal's
congruence for Ljunggren's (4.8; modulo `p` it is a case of Lucas's theorem).

## 1. `C(p, k)/p` modulo `p`

**1.1** (`choose_prime_sub_one_cast`). `C(p − 1, j) ≡ (−1)^j (mod p)` for `j < p`.

*Proof.* Induction on `j`, starting from `C(p − 1, 0) = 1`. Pascal's rule gives
`C(p − 1, j) + C(p − 1, j + 1) = C(p, j + 1)`, which is `≡ 0` because `0 < j + 1 < p`. So
`C(p − 1, j + 1) ≡ −(−1)^j`. ∎

**1.2** (`choose_prime_div_mul`). `c_k·k = C(p − 1, k − 1)` for `0 < k < p`.

*Proof.* `p·C(p − 1, k − 1) = C(p, k)·k`. Write `C(p, k) = p·c_k` and cancel `p`. ∎

**1.3** (`choose_prime_div_cast`). `c_k ≡ (−1)^(k−1)/k (mod p)` for `0 < k < p`.

*Proof.* `k` is invertible modulo `p`, and `c_k·k ≡ (−1)^(k−1)` by 1.2 and 1.1. ∎

## 2. Power sums of inverses modulo `p`

**2.1** (`sum_Ico_eq_sum_units`). A sum over `0 < k < p` is a sum over the units of `ℤ/p`.
Reduction modulo `p` is a bijection onto the units, with inverse "the representative in
`[0, p)`".

**2.2** (`sum_Ico_inv_pow`). `Σ_{0<k<p} 1/k^m` is `−1` modulo `p` if `p − 1 ∣ m`, and `0`
otherwise.

*Proof.* By 2.1 it is `Σ_u (u⁻¹)^m` over the units `u`. Since `u ↦ u⁻¹` permutes the units, this
equals `Σ_u u^m`, which is `−1` if `p − 1 ∣ m` and `0` otherwise (Mathlib's
`FiniteField.sum_pow_units`). ∎

**2.3** (`sum_Ico_inv_sq_eq_zero`). `Σ_{0<k<p} 1/k² ≡ 0 (mod p)` for `p ≥ 5`, since then
`p − 1 > 2`.

## 3. The polynomial identity

**Definition** (`chooseDivPoly`, `coeff_chooseDivPoly`). `G = Σ_{0<k<p} c_k·X^k`, a polynomial
with integer coefficients. Its coefficient of `X^n` is `c_n` for `0 < n < p`, and `0`
otherwise.

**3.1** (`one_add_X_pow_prime`). `(1 + X)^p = 1 + X^p + p·G`.

*Proof.* Compare the coefficients of `X^n`. On the left it is `C(p, n)`. For `n = 0` and
`n = p` both sides give `1`. For `0 < n < p` the right side gives `p·c_n = C(p, n)`. For
`n > p` both sides give `0`. ∎

In Lean, `1 + X^p` is written `expand p (1 + X)`, and `F(X^p)` in 4.2 is `expand p F`.

## 4. Ljunggren's congruence

**4.1** (`add_pow_add_two`). In any commutative ring, for some `r`,

`(x + y)^(n+2) = x^(n+2) + (n + 2)·x^(n+1)·y + C(n + 2, 2)·x^n·y² + y³·r`.

*Proof.* Induction on `n`. For `n = 0` take `r = 0`. For the step, multiply by `x + y` and
use `C(n + 3, 2) = C(n + 2, 2) + (n + 2)`. ∎

**4.2** (`dvd_coeff_expand_mul`). Let `d` be an integer that divides every coefficient of `H`
at a power `X^(jp)`. Then, for every polynomial `F`, `d` also divides every coefficient of
`F(X^p)·H` at a power `X^(jp)`.

*Proof.* The coefficient is additive in `F`, so it suffices to take `F = c·X^n`. The coefficient
of `X^(jp)` in `c·X^(np)·H` is `c` times the coefficient of `X^((j−n)p)` in `H` if `n ≤ j`, and
`0` otherwise. ∎

**4.3** (`coeff_chooseDivPoly_mul_prime`). `G` has no term `X^(jp)`, because `0 < jp < p` is
impossible.

**4.4** (`coeff_chooseDivPoly_sq_mul_prime`). For `p ≥ 5`, `p` divides the coefficient of
`X^(jp)` in `G²`.

*Proof.* This coefficient is `Σ_{0≤i≤jp} g_i·g_(jp−i)`, where `g_i` is the coefficient of `X^i`
in `G`. A term can be nonzero only if `0 < i < p` and `0 < jp − i < p`. Then `0 < jp < 2p`, so
`j = 1`. Hence for `j ≠ 1` every term is `0`. For `j = 1`, by 1.3 and `p − i ≡ −i`,

`c_i·c_(p−i) ≡ (−1)^(i−1)·(1/i)·(−1)^(p−i−1)·(−1/i) = −(−1)^(p−2)/i² = 1/i²`,

because `p − 2` is odd. So the coefficient is `≡ Σ_{0<i<p} 1/i² ≡ 0` by 2.3. ∎

**4.5** (`choose_mul_add_two`). `C((a + 2)p, bp) = C(a + 2, b) + p²·x + p³·s` for integers `x`,
`s`, and `p ∣ x` if `p ≥ 5`.

*Proof.* `C((a + 2)p, bp)` is the coefficient of `X^(bp)` in
`(1 + X)^((a+2)p) = ((1 + X)^p)^(a+2) = (A + pG)^(a+2)` by 3.1, where `A = 1 + X^p`. Expand by
4.1, with `A` for `x` and `pG` for `y`, and take the coefficient of `X^(bp)` of each term.

- `A^(a+2) = (1 + Y)^(a+2)` with `Y = X^p`, whose coefficient of `Y^b` is `C(a + 2, b)`.
- `pG·(a + 2)·A^(a+1)` contributes `0`, by 4.2 with `d = 0`, `H = G` and 4.3.
- `p²G²·C(a + 2, 2)·A^a` contributes `p²·x`, where `x` is the coefficient of `X^(bp)` in
  `C(a + 2, 2)·A^a·G²`. For `p ≥ 5`, `p ∣ x` by 4.2 with `d = p`, `H = G²` and 4.4.
- `p³G³·r` contributes `p³·s`, where `s` is the coefficient of `X^(bp)` in `G³·r`. ∎

**4.6** (`choose_mul_of_le_one`). For `a ≤ 1`, `C(ap, bp) = C(a, b)` exactly. Both sides are
`1` when `b ≤ a`, and `0` otherwise.

**4.7** (`choose_mul_modEq_choose_sq`). **Ljunggren's congruence modulo `p²`.** For every prime
`p`, `C(ap, bp) ≡ C(a, b) (mod p²)`. For `a ≤ 1` use 4.6; otherwise 4.5.

**4.8** (`choose_mul_modEq_choose_cube`). **Ljunggren's congruence.** For `p ≥ 5`,
`C(ap, bp) ≡ C(a, b) (mod p³)`. For `a ≤ 1` use 4.6; otherwise 4.5 with `p ∣ x`.

For `p = 3` it fails: `C(6, 3) = 20 ≡ 2 (mod 9)` but not modulo `27`.

## 5. Wolstenholme's and Babbage's theorems

**5.1** (`choose_two_mul`). `C(2p, p) = 2·C(2p − 1, p − 1)`. This follows from
`2p·C(2p − 1, p − 1) = C(2p, p)·p`.

**5.2** (`choose_two_mul_sub_one_modEq_one_sq`). **Babbage's theorem.** For an odd prime `p`,
`C(2p − 1, p − 1) ≡ 1 (mod p²)`.

*Proof.* By 4.7 with `a = 2`, `b = 1` and by 5.1, `2·C(2p − 1, p − 1) ≡ 2 (mod p²)`. Cancel `2`,
which is coprime to `p²`. ∎

**5.3** (`choose_two_mul_sub_one_modEq_one_cube`). **Wolstenholme's theorem.** For `p ≥ 5`,
`C(2p − 1, p − 1) ≡ 1 (mod p³)`. The proof is the same as 5.2, using 4.8.

For `p = 3`: `C(5, 2) = 10 ≡ 1 (mod 9)` but not modulo `27`.

## 6. Harmonic numbers

**6.1** (`sum_Ico_inv_eq_zero_zmod_sq`). **Wolstenholme's theorem, harmonic form.** For `p ≥ 5`,
`Σ_{0<k<p} 1/k ≡ 0 (mod p²)`.

*Proof.* Work in `ℤ/p²`, where every `0 < k < p` is invertible. Put `u_k = 1/k` and
`S = Σ_{0<k<p} u_k`. For `0 < k < p`, also `0 < p − k < p`.

(a) `u_k + u_(p−k) = p·u_k·u_(p−k)`, because `k + (p − k) = p`.

(b) `p·u_k·u_(p−k) = −p·u_k²`. Multiply (a) by `p·u_k` and use `p² = 0`.

(c) `Σ_k u_(p−k) = S`, since `k ↦ p − k` permutes `{1, …, p − 1}`.

(d) `p·Σ_k u_k² = 0`. Modulo `p`, `u_k` reduces to `1/k`, and `Σ_k 1/k² ≡ 0` by 2.3. So
`Σ_k u_k² = p·m` for some `m`, and `p·p·m = 0`.

By (c), (a), (b) and (d), `2S = Σ_k (u_k + u_(p−k)) = −p·Σ_k u_k² = 0`. Since `p` is odd, `2` is
invertible modulo `p²`, so `S = 0`. ∎

**6.2** (`sq_dvd_num_harmonic`). For `p ≥ 5`, `p²` divides the numerator of
`H_(p−1) = 1 + 1/2 + ⋯ + 1/(p − 1)`.

*Proof.* Let `F = (p − 1)!` and `N = Σ_{0<k<p} F/k`, a sum of integers, so that `H_(p−1)·F = N`.
Modulo `p²`, `F/k ≡ F·u_k`, so `N ≡ F·S ≡ 0` by 6.1. Writing `H_(p−1) = num/den` in lowest
terms, we get `num·F = N·den`. So `p² ∣ num·F`, and `p²` is coprime to `F`, so `p² ∣ num`. ∎

For example `H₄ = 25/12` and `H₆ = 49/20`.

## 7. Fermat quotients

**Definition** (`fermatQuotient`). `q_p(a) = (a^(p−1) − 1)/p` for an integer `a`, using integer
division. The division is exact when `p ∤ a` (7.1).

**7.1** (`mul_fermatQuotient`). If `p ∤ a` then `p·q_p(a) = a^(p−1) − 1`. This is Fermat's
little theorem, `p ∣ a^(p−1) − 1`.

**7.2** (`fermatQuotient_mul`). If `p ∤ a` and `p ∤ b`, then

`q_p(ab) = q_p(a) + q_p(b) + p·q_p(a)·q_p(b)`.

*Proof.* `p ∤ ab`. Multiply both sides by `p` and use 7.1:
`(ab)^(p−1) − 1 = (p·q_p(a) + 1)(p·q_p(b) + 1) − 1`. Then cancel `p`. ∎

**7.3** (`fermatQuotient_mul_modEq`). Hence `q_p(ab) ≡ q_p(a) + q_p(b) (mod p)`.

**7.4** (`fermatQuotient_add_mul`). If `p ∤ a`, then `q_p(a + pk) ≡ q_p(a) − k/a (mod p)` for
every integer `k`.

*Proof.* By Mathlib's `sq_dvd_add_pow_sub_sub`,
`(a + pk)^(p−1) = a^(p−1) + a^(p−2)·pk·(p − 1) + (pk)²·t` for some integer `t`. Since
`p ∤ a + pk`, 7.1 applies to both `a` and `a + pk`; dividing by `p` gives exactly
`q_p(a + pk) = q_p(a) + a^(p−2)·k·(p − 1) + p·k²·t`. Modulo `p`, `p − 1 ≡ −1` and
`a^(p−2) ≡ 1/a`, because `a^(p−2)·a = a^(p−1) ≡ 1`. ∎

**7.5** (`dvd_fermatQuotient_iff`). If `p ∤ a`, then `p ∣ q_p(a)` if and only if
`a^(p−1) ≡ 1 (mod p²)`. By 7.1, the second condition says `p² ∣ p·q_p(a)`. For `a = 2` these
`p` are the Wieferich primes, such as `1093`.

**7.6** (`two_mul_fermatQuotient_two`). **Eisenstein's formula.** For an odd prime `p`,
`2·q_p(2) = Σ_{0<k<p} c_k`.

*Proof.* Put `X = 1` in 3.1: `2^p = 2 + p·Σ_{0<k<p} c_k`. By 7.1 (`p ∤ 2`),
`p·2·q_p(2) = 2·(2^(p−1) − 1) = 2^p − 2`. Cancel `p`. ∎

For `p = 2` it fails: `2·q₂(2) = 0` but `c₁ = 1`.

**7.7** (`two_mul_fermatQuotient_two_cast`). **Eisenstein's congruence.** For an odd prime `p`,
`2·q_p(2) ≡ Σ_{0<k<p} (−1)^(k−1)/k (mod p)`. Apply 1.3 to each `c_k` in 7.6.

**7.8** (`two_mul_fermatQuotient_two_eq_neg_sum`). For an odd prime `p`,

`2·q_p(2) ≡ −(1 + 1/2 + ⋯ + 1/((p − 1)/2)) (mod p)`.

The Lean statement writes `(p − 1)/2` as `p/2`, which is equal for odd `p`.

*Proof.* Work modulo `p` with `1/0 = 0`, and write `p = 2n + 1`. Adding the term `k = 0`
changes none of the sums below, so all of them run over `0 ≤ k < p`.

- For `k ≥ 1`, `(−1)^(k−1)/k = −(1 + (−1)^k)/k + 1/k`. For `k = 0` both sides are `0`.
- `Σ_{k<p} 1/k = 0`, by 2.2 with `m = 1` (`p − 1 ∤ 1` since `p ≥ 3`).
- `Σ_{k<2n+1} (1 + (−1)^k)/k = Σ_{j≤n} 2/(2j)`, by induction on `n`. The factor `1 + (−1)^k`
  is `0` for odd `k` and `2` for even `k = 2j`.
- `2/(2j) = 1/j`, since `2` is invertible modulo `p`. The term `j = 0` is `0`.

Combining these with 7.7, `2·q_p(2) ≡ −Σ_{j≤n} 1/j = −Σ_{0<j≤n} 1/j`. ∎

For example `p = 7`: `q₇(2) = 9`, and `2·9 = 18 ≡ 4 ≡ −(1 + 1/2 + 1/3) (mod 7)`.
