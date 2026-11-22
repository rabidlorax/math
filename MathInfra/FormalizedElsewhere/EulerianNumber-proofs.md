# Eulerian numbers: the proofs in ordinary language

This is the human-readable companion to `MathInfra/FormalizedElsewhere/EulerianNumber.lean`.
Each numbered statement names the Lean theorem that checks it, and the proofs follow the same
route as the Lean proofs.

Throughout, `n`, `k`, `j`, `m`, `x` are natural numbers, `C(a, b)` is a binomial coefficient
(`0` if `b > a`), and `[P]` is `1` if `P` holds and `0` otherwise. Subtraction of natural numbers
is truncated at `0`; where a difference can be negative, this is said. A
sum over `k ≤ n` runs over `k = 0, 1, …, n`.

## Prior art

Checked in November 2026.

- **Mathlib** (pinned at 2026-11-19, and `master` on 2026-11-21) has no Eulerian numbers,
  Eulerian polynomials or descents of permutations (only descents in Coxeter groups), and no
  open or closed pull request mentions them.
- **Isabelle AFP**, entry [*Linear_Recurrences*](https://www.isa-afp.org/entries/Linear_Recurrences.html)
  (Eberl), theory `Eulerian_Polynomials`: the polynomials, defined by the recurrence 4.2, their
  values `A_n(0) = 1` and `A_n(1) = n!` (1.1, 2.3, 4.1), and over fields the generating
  function 4.3 and `Σ_m mⁿ·tᵐ = t·A_n(t)/(1 − t)ⁿ⁺¹` for `n > 0` (`eulerian_poly''`).
- Not found elsewhere: the descent count (§6), Worpitzky's identity (3.2), the symmetry (2.1)
  and the explicit formula (5.2). Nothing was found in other Lean projects (LeanPool),
  MathComp, Coq-Combi (which has descent sets of compositions only), HOL Light or HOL4. The
  Lean Zulip could not be searched without an account.

Other names: Euler–Frobenius numbers and polynomials. They are not the Euler (secant and
tangent) numbers. Some authors shift `k` by one, so that their `A(n, k)` counts permutations
with `k − 1` descents.

## 1. The definition and the recurrence

**Definition** (`eulerian`). `A(0, 0) = 1`, `A(0, k) = 0` for `k > 0`, `A(n + 1, 0) = A(n, 0)`,
and

`A(n + 1, k + 1) = (k + 2)·A(n, k + 1) + (n − k)·A(n, k)` (`eulerian_succ_succ`).

Here `n − k` is truncated: for `k > n` it is `0`. Equivalently,
`A(n + 1, k) = (k + 1)·A(n, k) + (n + 1 − k)·A(n, k − 1)`, the last term being absent for `k = 0`.

**1.1** (`eulerian_zero_right`). `A(n, 0) = 1`. Induction on `n`.

**1.2** (`eulerian_eq_zero_of_le`). If `n ≤ k` and `k > 0`, then `A(n, k) = 0`.

*Proof.* Induction on `n`. For `n = 0` this is the definition. For `n + 1 ≤ k + 1`,
`A(n, k + 1) = 0` by induction and `n − k = 0`. ∎

**1.3** (`sum_eulerian_succ_smul`). For any `f` with values in an additive commutative monoid,

`Σ_{k ≤ n+1} A(n + 1, k)·f(k) = Σ_{k ≤ n} A(n, k)·((k + 1)·f(k) + (n − k)·f(k + 1))`.

*Proof.* Put `g(k) = (k + 1)·A(n, k)·f(k)`. Since `A(n, n + 1) = 0`,
`Σ_{k ≤ n} g(k) = g(0) + Σ_{k ≤ n} g(k + 1)`, and `g(0) = f(0)`. So the right side is
`f(0) + Σ_{k ≤ n} ((k + 2)·A(n, k + 1) + (n − k)·A(n, k))·f(k + 1)`. Splitting off `k = 0` on the
left and using the recurrence gives the same. ∎

2.3 and 3.2 use 1.3 for their induction steps.

## 2. Symmetry and special values

**2.1 Symmetry** (`eulerian_symm_aux`, `eulerian_symm`). If `i + j + 1 = n`, then
`A(n, i) = A(n, j)`. That is, `A(n, n − 1 − k) = A(n, k)` for `k < n`.

*Proof.* Induction on `n`; the case `n = 0` cannot occur. Let `i + j = n`, so that the claim is
`A(n + 1, i) = A(n + 1, j)`.

- `i = j = 0`: trivial.
- `i = 0`, `j = j' + 1`: then `j' + 1 = n`, and
  `A(n + 1, j' + 1) = (j' + 2)·A(n, n) + 1·A(n, j') = A(n, j')` by 1.2. By induction
  (`0 + j' + 1 = n`) this is `A(n, 0) = A(n + 1, 0)`. The case `j = 0` is the same.
- `i = i' + 1`, `j = j' + 1`: then `i' + j' + 2 = n`. By induction `A(n, i' + 1) = A(n, j')` and
  `A(n, i') = A(n, j' + 1)`, and the coefficients match: `i' + 2 = n − j'` and `n − i' = j' + 2`.
  So the recurrences for `A(n + 1, i' + 1)` and `A(n + 1, j' + 1)` have the same two terms. ∎

**2.2** (`eulerian_self_sub_one`). `A(n, n − 1) = 1` for `n > 0`. This is 2.1 with `k = 0`.

**2.3** (`sum_eulerian`). `Σ_{k ≤ n} A(n, k) = n!`.

*Proof.* Induction on `n`. By 1.3 with `f = 1`, `Σ_{k ≤ n+1} A(n + 1, k)` is
`Σ_{k ≤ n} A(n, k)·((k + 1) + (n − k)) = (n + 1)·n!`. ∎

**2.4** (`eulerian_one_right`). `A(n, 1) = 2ⁿ − (n + 1)`.

*Proof.* Induction on `n`: `A(n + 1, 1) = 2·A(n, 1) + n·A(n, 0) = 2·(2ⁿ − n − 1) + n`, which is
`2ⁿ⁺¹ − (n + 2)`. The subtractions are exact since `n < 2ⁿ`. ∎

## 3. Worpitzky's identity

**3.1** (`mul_choose_add_eq`). For `k ≤ n`,

`x·C(x + k, n) = (k + 1)·C(x + k, n + 1) + (n − k)·C(x + k + 1, n + 1)`.

*Proof.* If `x + k < n`, every binomial coefficient is `0`. Otherwise write `n = k + a` and
`x = a + b`, so that `x + k − n = b`. Put `c = C(x + k, n)` and `d = C(x + k, n + 1)`. Then
`(n + 1)·d = b·c` (`Nat.choose_succ_right_eq`), and Pascal's rule gives
`C(x + k + 1, n + 1) = c + d`. The right side is
`(k + 1)·d + a·(c + d) = a·c + (n + 1)·d = a·c + b·c = x·c`. ∎

**3.2 Worpitzky's identity** (`sum_eulerian_mul_choose`).
`xⁿ = Σ_{k ≤ n} A(n, k)·C(x + k, n)`.

*Proof.* Induction on `n`; for `n = 0` both sides are `1`. By 1.3 with `f(k) = C(x + k, n + 1)`
and then 3.1,

`Σ_{k ≤ n+1} A(n + 1, k)·C(x + k, n + 1) = Σ_{k ≤ n} A(n, k)·x·C(x + k, n) = x·xⁿ`. ∎

## 4. Eulerian polynomials and the generating function

**Definition** (`eulerianPoly`). `A_n(t) = Σ_{k ≤ n} A(n, k)·tᵏ`, over any commutative semiring.

**4.1** (`coeff_eulerianPoly`, `eulerianPoly_eval_one`, `coe_eulerianPoly`). The coefficient of
`tᵏ` in `A_n(t)` is `A(n, k)` for every `k` (by 1.2 for `k > n`), and `A_n(1) = n!` by 2.3.
`coe_eulerianPoly` is the same sum read as a power series.

**4.2** (`eulerianPoly_succ`). Over a commutative ring,

`A_{n+1}(t) = (1 + n·t)·A_n(t) + t·(1 − t)·A_n'(t)`.

*Proof.* Compare coefficients. At `t⁰` both sides are `1`. At `tᵏ⁺¹`, `t·A_n'` contributes
`(k + 1)·A(n, k + 1)` and `t²·A_n'` contributes `k·A(n, k)`, so the right side has
`A(n, k + 1) + n·A(n, k) + (k + 1)·A(n, k + 1) − k·A(n, k)`. For `k ≤ n` this is
`(k + 2)·A(n, k + 1) + (n − k)·A(n, k) = A(n + 1, k + 1)`. For `k > n` the same
holds because `A(n, k) = 0` by 1.2, so the truncation of `n − k` does not matter. ∎

**4.3 The generating function** (`mk_pow_mul_one_sub_pow`). Over a commutative ring, as power
series,

`(Σ_{m ≥ 0} (m + 1)ⁿ·tᵐ)·(1 − t)ⁿ⁺¹ = A_n(t)`.

*Proof.* For `n = 0` this is `(Σ tᵐ)·(1 − t) = 1`. Let `n > 0`. By 3.2 with `x = m + 1`,
`Σ_m (m + 1)ⁿ·tᵐ = Σ_{k ≤ n} A(n, k)·G_k`, where `G_k = Σ_m C(m + 1 + k, n)·tᵐ`. The term
`k = n` vanishes since `A(n, n) = 0`. For `k < n`,

`G_k = t^(n−1−k)·Σ_i C(n + i, n)·tⁱ`.

To see this, compare the coefficients of `tᵐ`. If `m ≥ n − 1 − k`, put `i = m − (n − 1 − k)`; then
`n + i = m + 1 + k`. If `m < n − 1 − k`, then `m + 1 + k < n`, so `C(m + 1 + k, n) = 0`. Since
`(Σ_i C(n + i, n)·tⁱ)·(1 − t)ⁿ⁺¹ = 1` (Mathlib's `invOneSubPow`), `G_k·(1 − t)ⁿ⁺¹ = t^(n−1−k)`.
So the left side is `Σ_{k < n} A(n, k)·t^(n−1−k)`. Reversing the order (`k ↦ n − 1 − k`) and using
the symmetry 2.1 turns this into `Σ_{k < n} A(n, k)·tᵏ = A_n(t)`. ∎

## 5. The explicit formula

**5.1** (`PowerSeries.coeff_one_sub_X_pow`). The coefficient of `tʲ` in `(1 − t)ᵐ` is
`(−1)ʲ·C(m, j)`. Induction on `m`, multiplying by `1 − t` and using Pascal's rule.

**5.2** (`eulerian_eq_sum`). In the integers,

`A(n, k) = Σ_{j ≤ k} (−1)ʲ·C(n + 1, j)·(k + 1 − j)ⁿ`.

*Proof.* Take the coefficient of `tᵏ` on both sides of 4.3 over `ℤ`. On the right it is
`A(n, k)` (4.1). On the left it is `Σ_{i + j = k} (i + 1)ⁿ·(−1)ʲ·C(n + 1, j)` by 5.1, and
`i + 1 = k + 1 − j`. ∎

## 6. Descents

**Definition** (`numDescents`). The number of descents of a list of natural numbers:
`des([]) = des([a]) = 0` and `des(a :: b :: l) = [b < a] + des(b :: l)` (`numDescents_cons_cons`).
So `des(l)` counts the positions `i` with `l[i + 1] < l[i]`. For a permutation `σ` of
`0, …, n − 1`, the descents of the list `σ(0), …, σ(n − 1)` are those of `σ`.

**6.1** (`numDescents_cons_of_lt`). If `m` is larger than every entry of a nonempty list `l`,
then `des(m :: l) = des(l) + 1`, since `m` is larger than the first entry of `l`.

Mathlib's `permutations'Aux m l` lists the `length(l) + 1` ways of inserting `m` into `l`:
inserting into `[]` gives `[m]`, and the insertions into `y :: l` are `m :: y :: l` followed by
`y :: x` for each insertion `x` of `m` into `l`.

**6.2** (`numDescents_permutations'Aux`). Let `m` be larger than every entry of `l`, and
`D = des(l)`. Every insertion of `m` into `l` has `D` or `D + 1` descents, and exactly `D + 1` of
them have `D`.

*Proof.* Induction on `l`. For `[]` the only insertion is `[m]`, with `0` descents. For `[y]` the
insertions are `[m, y]` and `[y, m]`, with `1` and `0` descents.

For `l = y :: z :: zs`, put `D' = des(z :: zs)`, so `D = [z < y] + D'`. The insertions into `l`
are:

- `m :: y :: z :: zs`, with `D + 1` descents by 6.1;
- `y :: m :: z :: zs`, with `0 + des(m :: z :: zs) = D' + 1` descents (6.1). That is `D` if
  `z < y`, and `D + 1` otherwise;
- `y :: z :: x` for each insertion `x` of `m` into `zs`, with `[z < y] + des(z :: x)` descents.

The lists `z :: x` are the insertions of `m` into `z :: zs` other than the first,
`m :: z :: zs`, which has `D' + 1` descents. By induction each has `D'` or `D' + 1` descents, and
`D' + 1` of them have `D'`. So each `y :: z :: x` has `D` or `D + 1` descents, and `D' + 1` of
them have `D`. Counting the second item, `[z < y] + D' + 1 = D + 1` insertions have `D`
descents. ∎

**6.3** (`countP_permutations'Aux`). In the same situation, the number of insertions with `k`
descents is

`[D = k]·(k + 1) + [D + 1 = k]·(length(l) + 1 − k)`.

*Proof.* By 6.2, `D + 1` of the `length(l) + 1` insertions have `D` descents, the other
`length(l) + 1 − (D + 1)` have `D + 1`, and none has any other number. ∎

**6.4** (`countP_permutations'_reverse_range`). Let `P_n` be Mathlib's `permutations'` of the
list `n − 1, …, 1, 0`. The number of lists in `P_n` with `k` descents is `A(n, k)`.

*Proof.* Induction on `n`. `P_0 = [[]]`, and `[]` has `0` descents, matching
`A(0, k) = [k = 0]`. By definition, `P_{n+1}` consists of the insertions of `n` into each
`L ∈ P_n`. Each such `L` is a permutation of `0, …, n − 1`, so it has length `n` and entries
less than `n`. Let `c(k)` be the number of lists in `P_n` with `k` descents. Summing 6.3 over
`L ∈ P_n`, the number of lists in `P_{n+1}` with `k` descents is

`(k + 1)·c(k) + (n + 1 − k)·c(k − 1)`, the second term being absent for `k = 0`.

By induction `c(k) = A(n, k)`, so this is the recurrence for `A(n + 1, k)`. ∎

**6.5** (`countP_permutations_range`). **`A(n, k)` is the number of permutations of
`0, 1, …, n − 1` with exactly `k` descents.** Precisely, it is the number of lists with `k`
descents in `List.permutations (List.range n)`.

*Proof.* `List.permutations l` lists the same permutations as `List.permutations' l`, only in
a different order, and `permutations'` of `n − 1, …, 0` lists the same ones as `permutations'`
of `0, …, n − 1` (both from Mathlib). Counting does not depend on the order, so 6.4 applies. ∎

**6.6** (`card_perm_numDescents`). The number of permutations `σ` of `Fin n` whose word
`σ(0), σ(1), …, σ(n − 1)` has `k` descents is `A(n, k)`.

*Proof.* The map from `σ` to its word, a list of natural numbers, is injective. Its values are
permutations of `0, …, n − 1`, since the word of `σ` rearranges the word `0, 1, …, n − 1` of the
identity. There are `n!` permutations `σ`, and `List.permutations (List.range n)` has `n!`
entries, none repeated. So the map is a bijection onto these lists, and 6.5 gives the count. ∎
