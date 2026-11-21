# Dedekind sums: the proofs in ordinary language

This is the human-readable companion to `MathInfra/FormalizedElsewhere/DedekindSum.lean`. Each numbered
statement names the Lean theorem that checks it, and the proofs follow the same route as the
Lean proofs.

Throughout, `⌊x⌋` and `⌈x⌉` are the floor and ceiling of `x`, `{x} = x − ⌊x⌋` is its fractional
part, and for natural numbers `m mod k` is the remainder. A sum over `r < k` runs over
`r = 0, 1, …, k − 1`.

## 1. The sawtooth function

**Definition** (`sawtooth`). `((x)) = x − (⌊x⌋ + ⌈x⌉)/2`, for `x` in any linearly ordered field
with a floor function, such as `ℚ` or `ℝ`.

**1.1** (`sawtooth_eq_ite`, `sawtooth_intCast`, `sawtooth_zero`). `((x)) = 0` if `x` is an
integer, and `((x)) = {x} − 1/2` otherwise.

*Proof.* At an integer `⌊x⌋ = ⌈x⌉ = x`. Otherwise `⌈x⌉ = ⌊x⌋ + 1`, so `((x)) = x − ⌊x⌋ − 1/2`. ∎

**1.2** (`sawtooth_add_intCast`, `sawtooth_neg`, `abs_sawtooth_le`). For every integer `m`,
`((x + m)) = ((x))` and `((−x)) = −((x))`. Moreover `|((x))| ≤ 1/2`.

*Proof.* `⌊x + m⌋ = ⌊x⌋ + m` and `⌈x + m⌉ = ⌈x⌉ + m`, while `⌊−x⌋ = −⌈x⌉` and `⌈−x⌉ = −⌊x⌋`.
The bound follows from 1.1, since `0 ≤ {x} < 1`. ∎

**1.3** (`sawtooth_natCast_div`). For natural numbers `m` and `n > 0`: `((m/n)) = 0` if `n ∣ m`,
and `((m/n)) = (m mod n)/n − 1/2` otherwise. This is 1.1, since `{m/n} = (m mod n)/n`.

**1.4 Distribution relation** (`sum_sawtooth_add_div`). For `n > 0`,
`Σ_{i<n} ((x + i/n)) = ((nx))`.

*Proof.* Hermite's identity, which is in Mathlib, says `Σ_{i<n} ⌊y + i/n⌋ = ⌊ny⌋`. For the
ceilings, `⌈x + i/n⌉ = −⌊−x − i/n⌋`. Reversing the order of summation (`i ↦ n − 1 − i`) turns
`−x − i/n` into `y + i/n` with `y = −x − (n − 1)/n`, so Hermite's identity gives
`Σ_{i<n} ⌊−x − i/n⌋ = ⌊ny⌋ = ⌊−nx⌋ + 1 − n`. Hence `Σ_{i<n} ⌈x + i/n⌉ = ⌈nx⌉ + n − 1`. Since
`Σ_{i<n} (x + i/n) = nx + (n − 1)/2`,

`Σ_{i<n} ((x + i/n)) = nx + (n − 1)/2 − (⌊nx⌋ + ⌈nx⌉ + n − 1)/2 = ((nx))`. ∎

## 2. Dedekind sums and their symmetries

**Definition** (`dedekindSum`). For an integer `h` and a natural number `k`,
`s(h, k) = Σ_{r<k} ((r/k))·((hr/k))`, a rational number.

So `s(h, 0) = s(h, 1) = s(0, k) = 0` (`dedekindSum_zero_right`, `dedekindSum_one_right`,
`dedekindSum_zero_left`): the sum is empty, or every term contains a factor `((0)) = 0`.

**2.1** (`dedekindSum_neg`). `s(−h, k) = −s(h, k)`, because `((−x)) = −((x))` by 1.2.

**2.2** (`sawtoothZMod`, `sawtoothZMod_intCast`, `dedekindSum_eq_sum_zmod`). Let `k > 0`. By 1.2,
`((n/k))` depends only on `n` modulo `k`, so `((a/k))` makes sense for a residue `a` modulo `k`,
and `s(h, k) = Σ_{a mod k} ((a/k))·((ha/k))`.

**2.3** (`dedekindSum_congr`). If `h ≡ h' (mod k)` then `s(h, k) = s(h', k)`. For `k = 0` both
sides are `0`; otherwise this is immediate from 2.2.

**2.4** (`dedekindSum_of_mul_modEq_one`). If `hh' ≡ 1 (mod k)` then `s(h', k) = s(h, k)`.

*Proof.* For `k = 0` both sides are `0`. Otherwise `b ↦ hb` permutes the residues modulo `k`,
with inverse `a ↦ h'a`. Substituting `a = hb` in 2.2,
`s(h', k) = Σ_b ((hb/k))·((h'hb/k)) = Σ_b ((hb/k))·((b/k)) = s(h, k)`. ∎

**2.5** (`dedekindSum_eq_zero_of_sq_modEq_neg_one`). If `h² ≡ −1 (mod k)` then `s(h, k) = 0`.

*Proof.* `h·(−h) ≡ 1`, so `s(−h, k) = s(h, k)` by 2.4, while `s(−h, k) = −s(h, k)` by 2.1. ∎

**2.6 Homogeneity** (`dedekindSum_mul_mul`). For `d > 0`, `s(dh, dk) = s(h, k)`.

*Proof.* For `k = 0` both sides are `0`. Write each `r < dk` uniquely as `r = j + ki` with
`j < k` and `i < d`. Then `dh·r/(dk) = hj/k + hi`, so by 1.2 the second factor is `((hj/k))`,
and `r/(dk) = j/(dk) + i/d`. Summing over `i` first, 1.4 with `n = d` gives
`Σ_{i<d} ((j/(dk) + i/d)) = ((j/k))`. What remains is `Σ_{j<k} ((j/k))·((hj/k)) = s(h, k)`. ∎

## 3. An integer formula

From here on `h` and `k` are natural numbers, except in 3.3.

**3.1** (`dedekindSum_eq_sum_mod`). Let `k > 0` and `gcd(h, k) = 1`, and write
`ρ_r = hr mod k`. Then

`s(h, k) = (Σ_{r<k} r·ρ_r)/k² − (k − 1)/4`.

*Proof.* For `0 < r < k`, neither `r` nor `hr` is divisible by `k`, the latter because
`gcd(h, k) = 1`. So by 1.3 the term for `r` is `(r/k − 1/2)(ρ_r/k − 1/2)`. The term for `r = 0`
is `0`, which is this expression minus `1/4`. Hence

`s(h, k) = Σ_{r<k} (r/k − 1/2)(ρ_r/k − 1/2) − 1/4
= (Σ r·ρ_r)/k² − (Σ r + Σ ρ_r)/(2k) + (k − 1)/4`.

Since `gcd(h, k) = 1`, `r ↦ ρ_r` permutes `{0, …, k − 1}`, so `Σ ρ_r = Σ r = k(k − 1)/2`. ∎

**3.2** (`dedekindSum_one_left`). `s(1, k) = (k − 1)(k − 2)/(12k)`.

*Proof.* For `k = 0` both sides are `0` (in Lean, division by `0` gives `0`). Otherwise apply
3.1 with `h = 1`, so `ρ_r = r`. With `Σ_{r<k} r² = (k − 1)k(2k − 1)/6` this gives
`s(1, k) = (k − 1)(2k − 1)/(6k) − (k − 1)/4 = (k − 1)(k − 2)/(12k)`. ∎

**3.3** (`abs_dedekindSum_le`). If the integer `h` is coprime to `k`, then
`|s(h, k)| ≤ s(1, k)`.

*Proof.* For `k = 0` both sides are `0`. Otherwise write `x_a = ((a/k))` for residues `a`. By
2.2, `|s(h, k)| ≤ Σ_a |x_a·x_{ha}| ≤ Σ_a (x_a² + x_{ha}²)/2`. Since `h` is invertible modulo
`k`, `a ↦ ha` permutes the residues, so `Σ_a x_{ha}² = Σ_a x_a²` and the bound is
`Σ_a x_a² = s(1, k)`, again by 2.2. ∎

## 4. The reciprocity law

Fix coprime `h` and `k` with `k > 0`. For `r < k` write `q_r = ⌊hr/k⌋` and `ρ_r = hr mod k`,
so that `hr = k·q_r + ρ_r`. Let

`A = Σ_{r<k} r`, `B = Σ_{r<k} r²`, `F = Σ_{r<k} q_r`, `G = Σ_{r<k} r·q_r`,
`Q = Σ_{r<k} q_r²`.

**4.1** (private `dedekindSum_aux`).

- (a) `s(h, k) = (hB − kG)/k² − (k − 1)/4`;
- (b) `kF = (h − 1)A`;
- (c) `k²Q − 2hkG + (h² − 1)B = 0`.

*Proof.* Substituting `ρ_r = hr − kq_r` in 3.1 gives `Σ r·ρ_r = hB − kG`, which is (a).
Since `r ↦ ρ_r` permutes `{0, …, k − 1}`, `Σ ρ_r = A` and `Σ ρ_r² = B`. Expanding,
`Σ ρ_r = hA − kF` and `Σ ρ_r² = h²B − 2hkG + k²Q`, which give (b) and (c). ∎

**4.2 Lattice points** (private `lattice`). Let `h > 0`, and for `y < h` write
`q'_y = ⌊ky/h⌋`. Then

`Σ_{x<k} q_x(q_x + 1)/2 + Σ_{y<h} y·(q'_y + 1) = k·Σ_{y<h} y`.

*Proof.* The right side is the sum of `y` over the points `(x, y)` with `x < k` and `y < h`.
Split these points according to whether `yk ≤ hx`.

For fixed `x`, the `y < h` with `yk ≤ hx` are exactly the `y ≤ q_x` (every such `y` is below
`h`, since `yk ≤ hx < hk`). They contribute `0 + 1 + ⋯ + q_x = q_x(q_x + 1)/2`.

For fixed `y`, consider the `x < k` with `hx < yk`. If `y = 0` there are none. If `0 < y < h`,
then `hx = ky` is impossible, since then `h ∣ ky`, so `h ∣ y`. Hence `hx < yk` if and only if
`x ≤ q'_y`, and every such `x` is below `k`, since `xh ≤ ky < kh`. So there are `q'_y + 1` of
them, each contributing `y`. ∎

**4.3 Reciprocity** (`dedekindSum_reciprocity`). For coprime `h, k > 0`,

`s(h, k) + s(k, h) = (h² + k² + 1)/(12hk) − 1/4`.

*Proof.* Apply 4.1(a) to `(h, k)` and to `(k, h)`. For the latter write `A' = Σ_{y<h} y`,
`B' = Σ_{y<h} y²` and `G' = Σ_{y<h} y·q'_y`, so that

`s(h, k) + s(k, h) = hB/k² − G/k + kB'/h² − G'/h − (h + k − 2)/4`.

In this notation 4.2 reads `(Q + F)/2 + G' + A' = kA'`. Use it to eliminate `G'`, then 4.1(c)
to eliminate `Q`, which cancels `G`, and 4.1(b) to eliminate `F`. What remains is

`hB/k² + kB'/h² − (k − 1)A'/h − (h² − 1)B/(2hk²) + (h − 1)A/(2hk) − (h + k − 2)/4`,

and with `A = k(k − 1)/2`, `B = (k − 1)k(2k − 1)/6` and likewise for `A'`, `B'`, this equals
the right side. ∎

Together with 2.3, reciprocity computes `s(h, k)` along the Euclidean algorithm. For example
`17 ≡ 2 (mod 5)` and `2² ≡ −1 (mod 5)`, so `s(17, 5) = 0` by 2.3 and 2.5, and then 4.3 gives
`s(5, 17) = 315/1020 − 1/4 = 1/17`.

**4.4** (`dedekindSum_two_left`). For odd `k`, `s(2, k) = (k − 1)(k − 5)/(24k)`.

*Proof.* `k > 0` and `gcd(2, k) = 1`. As `k ≡ 1 (mod 2)`, `s(k, 2) = s(1, 2) = 0` by 2.3 and
3.2. So 4.3 gives `s(2, k) = (k² + 5)/(24k) − 1/4 = (k − 1)(k − 5)/(24k)`. ∎

## 5. Integrality

**5.1** (`exists_six_mul_dedekindSum_eq`). If `k > 0` and `gcd(h, k) = 1`, then `6k·s(h, k)` is
an integer.

*Proof.* By 4.1(a) and the formulas for `A` and `B`,
`6k·s(h, k) = h(k − 1)(2k − 1) − 6G − 3A`, and `A`, `G` are integers. ∎

**5.2** (`exists_twelve_mul_dedekindSum_modEq`). For coprime `h, k > 0`, `12hk·s(h, k)` is an
integer congruent to `h² + 1` modulo `k`.

*Proof.* By 5.1 for `(k, h)`, `w = 6h·s(k, h)` is an integer. Multiplying 4.3 by `12hk`,
`12hk·s(h, k) = h² + k² + 1 − 3hk − 2kw ≡ h² + 1 (mod k)`. ∎
