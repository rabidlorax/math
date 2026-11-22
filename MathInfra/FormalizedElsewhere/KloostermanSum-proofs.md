# Kloosterman sums: the proofs in ordinary language

This is the human-readable companion to `MathInfra/FormalizedElsewhere/KloostermanSum.lean`.
Each numbered statement names the Lean theorem that checks it, and the proofs follow the same
route as the Lean proofs.

Throughout, `q > 0`, `ψ` is an additive character of `ℤ/q` (a map with `ψ(0) = 1` and
`ψ(x + y) = ψ(x)ψ(y)`) with values in a commutative ring, and `Σ_x` is a sum over the units `x` of
`ℤ/q`; sums over `m`, `n` or `a` run over all of `ℤ/q`. The character `ψ` is *primitive* if
`x ↦ ψ(ax)` is nontrivial for every `a ≠ 0`; the standard character `e_q(x) = exp(2πix/q)` is
primitive. Write `φ` for Euler's totient.

## Prior art

Checked in November 2026. Mathlib (2026-11-19) has additive characters, primitivity and
`ZMod.stdAddChar`, but no Kloosterman sums, and no Mathlib PR or issue mentions them. The Lean 4
project [jieun38-kim/Kloosterman](https://github.com/jieun38-kim/Kloosterman) (2023, supervised by
Kevin Buzzard) defines `S(a, b; q)` over `ℂ` and proves invariance modulo `q`, the first half of
1.1, and `S(a, b) = S(1, ab)` for `a`, `b` both coprime to `q`. The first half of 1.2 and twisted
multiplicativity (2.2) appear only as commented-out statements with `sorry`. Its main result is a
stationary-phase formula for character sums modulo `p^(2α)`, which is not done here. Two open
TauCeti roadmap PRs ([#2289](https://github.com/TauCetiProject/TauCetiRoadmap/pull/2289),
[#2301](https://github.com/TauCetiProject/TauCetiRoadmap/pull/2301)) and the project
[BrandonMYates/kklab](https://github.com/BrandonMYates/kklab) define Kloosterman sums over finite
fields, but prove none of the results below. Nothing was found in the Isabelle AFP (the entry
*Gauss_Sums* has Ramanujan and Gauss sums only), Rocq or HOL. New here: the general character, and
every result below except the first half of 1.1, the case of 1.2 where both arguments are units, and
the orthogonality relation 4.2, a form of Mathlib's `AddChar.sum_mulShift`.

## 1. Definition and symmetries

**Definition** (`kloostermanSum`). `S(ψ; m, n) = Σ_x ψ(mx + nx⁻¹)` for `m, n ∈ ℤ/q`. For
`ψ = e_q` this is the classical `S(m, n; q)`.

**1.1** (`kloostermanSum_comm`, `kloostermanSum_neg`). `S(ψ; m, n) = S(ψ; n, m)` and
`S(ψ; −m, −n) = S(ψ; m, n)`.

*Proof.* Substitute `x ↦ x⁻¹`, respectively `x ↦ −x`. ∎

**1.2** (`kloostermanSum_units_mul`, `kloostermanSum_units_left`). For a unit `u`,
`S(ψ; um, n) = S(ψ; m, un)`. In particular `S(ψ; u, n) = S(ψ; 1, un)`: when one argument is a
unit, `S` depends only on the product of the arguments.

*Proof.* `ψ(umx + nx⁻¹) = ψ(m(ux) + un(ux)⁻¹)`, and `ux` runs over the units as `x` does. ∎

**1.3** (`kloostermanSum_mulShift`). If `ψ_a(x) = ψ(ax)`, then `S(ψ_a; m, n) = S(ψ; am, an)`.

*Proof.* `ψ_a(mx + nx⁻¹) = ψ(amx + anx⁻¹)`. ∎

**1.4** (`kloostermanSum_zero_right`, `kloostermanSum_zero_zero`). `S(ψ; m, 0) = Σ_x ψ(mx)`, and
`S(ψ; 0, 0) = φ(q)`, the number of units: every term of `S(ψ; 0, 0)` is `ψ(0) = 1`.

## 2. Twisted multiplicativity

For `ab = c`, multiplication by `b` is a well-defined additive map `ℤ/a → ℤ/c`
(`ZMod.mulCofactor`), since `b·a = c ≡ 0`. On an integer `k` it is `k ↦ b·k`
(`ZMod.mulCofactor_intCast`). Reduced modulo `a`, the image of `x` is `b·x` computed in `ℤ/a`;
reduced modulo any common divisor of `b` and `c` it is `0` (`ZMod.castHom_mulCofactor_self`,
`ZMod.castHom_mulCofactor_of_dvd`).

**2.1** (`kloostermanSum_mul`). Let `q₁`, `q₂` be coprime, `ψ` a character of `ℤ/q₁q₂`, and
`ψ₁(x) = ψ(q₂x)`, `ψ₂(y) = ψ(q₁y)` the characters it induces on `ℤ/q₁` and `ℤ/q₂`. Let `q̄₂` be
the inverse of `q₂` modulo `q₁`, and `q̄₁` that of `q₁` modulo `q₂`. Then, with `m` and `n`
reduced modulo `q₁` in the first factor and modulo `q₂` in the second,

`S(ψ; m, n) = S(ψ₁; q̄₂m, q̄₂n) · S(ψ₂; q̄₁m, q̄₁n)`.

*Proof.* By the Chinese remainder theorem an element of `ℤ/q₁q₂` is determined by its residues
modulo `q₁` and `q₂`. So every `w` satisfies

`w = q₂·(q̄₂w mod q₁) + q₁·(q̄₁w mod q₂)`,

since both sides agree modulo `q₁` (where `q₂q̄₂ = 1` and `q₁ = 0`) and modulo `q₂`. Hence
`ψ(w) = ψ₁(q̄₂w) ψ₂(q̄₁w)`, with `w` reduced modulo `q₁` and `q₂`. Reduction also maps the units of
`ℤ/q₁q₂` injectively to the pairs `(x₁, x₂)` of units modulo `q₁` and `q₂`, hence bijectively, as
both sets have `φ(q₁q₂) = φ(q₁)φ(q₂)` elements; it maps `x⁻¹` to `(x₁⁻¹, x₂⁻¹)`. Applying this to
`w = mx + nx⁻¹` gives

`S(ψ; m, n) = Σ_{x₁, x₂} ψ₁(q̄₂mx₁ + q̄₂nx₁⁻¹) ψ₂(q̄₁mx₂ + q̄₁nx₂⁻¹)`,

which is the product. ∎

**2.2** (`kloostermanSum_stdAddChar_mul`). For the standard characters,
`S(m, n; q₁q₂) = S(q̄₂m, q̄₂n; q₁) · S(q̄₁m, q̄₁n; q₂)`.

*Proof.* `e_{q₁q₂}(q₂x) = exp(2πiq₂x/q₁q₂) = e_{q₁}(x)`, so `ψ₁ = e_{q₁}` and `ψ₂ = e_{q₂}`
in 2.1. ∎

So Kloosterman sums reduce to prime-power moduli. By 1.2 the first factor is also
`S(m, q̄₂²n; q₁)`.

## 3. Primitive characters

Here `ψ` is primitive with values in an integral domain.

**3.1** (`AddChar.IsPrimitive.isPrimitiveRoot_one`). `ζ = ψ(1)` is a primitive `q`-th root of
unity. This holds in any commutative ring.

*Proof.* `ζ^l = ψ(l)`, and a primitive character takes the value `1` only at `0`. So `ζ^l = 1`
exactly when `l ≡ 0 (mod q)`. ∎

**3.2** (`kloostermanSum_zero_right_eq_ramanujanSum`). For an integer `m`,
`S(ψ; m, 0) = c_q(m)`, the Ramanujan sum of `RamanujanSum`.

*Proof.* Let `N` be the residue of `m` modulo `q`, so that `c_q(m) = c_q(N)` by 1.1 of
`RamanujanSum`. The map `x ↦ k`, where `0 ≤ k < q` represents `x`, is a bijection from the units
onto the `k < q` coprime to `q`, and `ψ(mx) = ζ^(kN)`. So
`S(ψ; m, 0) = Σ_{k < q, gcd(k, q) = 1} ζ^(kN) = c_q(N)` by 6.3 of `RamanujanSum`
(`IsPrimitiveRoot.sum_pow_coprime`), which applies by 3.1. ∎

So `S(ψ; m, 0) = μ(q)` for `m` coprime to `q`, by 3.2 of `RamanujanSum`.

**3.3** (`sum_kloostermanSum_left`). If `q ≠ 1`, then `Σ_m S(ψ; m, n) = 0`.

*Proof.* `Σ_m S(ψ; m, n) = Σ_x ψ(nx⁻¹) Σ_m ψ(mx)`. Each unit `x` is nonzero, as `q ≠ 1`, and for
a primitive `ψ` with values in an integral domain, `Σ_m ψ(mb) = 0` whenever `b ≠ 0`
(`AddChar.sum_mulShift` in Mathlib). ∎

## 4. Complex Kloosterman sums and moments

Here `ψ` takes complex values. Its values are roots of unity, so `conj ψ(t) = ψ(−t)`.

**4.1** (`conj_kloostermanSum`, `kloostermanSum_im`). `S(ψ; m, n)` is real.

*Proof.* `conj S(ψ; m, n) = Σ_x ψ(−mx − nx⁻¹) = S(ψ; −m, −n) = S(ψ; m, n)` by 1.1. ∎

From now on `ψ` is primitive.

**4.2** (`AddChar.IsPrimitive.sum_mul_conj`). `Σ_a ψ(as)·conj ψ(at)` is `q` if `s = t`, and `0`
otherwise.

*Proof.* The term is `ψ(a(s − t))`, and `Σ_a ψ(ab)` is `q` if `b = 0` and, as in 3.3, `0` if
`b ≠ 0`. ∎

**4.3** (`AddChar.IsPrimitive.sum_mul_conj_sum`). For a finite family of points `u(i) ∈ ℤ/q`
with complex weights `w(i)`,

`Σ_a |Σ_i w(i) ψ(a u(i))|² = q · Σ_{u(i) = u(j)} w(i) conj w(j)`.

*Proof.* Expand `|z|² = z·conj z` as a double sum over `i` and `j`, sum over `a` first and apply
4.2 with `s = u(i)`, `t = u(j)`. ∎

**4.4 Second moment** (`sum_norm_kloostermanSum_sq`). `Σ_m |S(ψ; m, n)|² = q·φ(q)`.

*Proof.* `S(ψ; m, n) = Σ_x ψ(nx⁻¹) ψ(mx)`. Apply 4.3 with the units `x` as index set, `u(x) = x`
and `w(x) = ψ(nx⁻¹)`. Since `u` is injective, only the `φ(q)` pairs `(x, x)` contribute, each with
`|ψ(nx⁻¹)|² = 1`. ∎

For a prime `p` and `n ≠ 0`, 1.1 and 3.2 give `S(ψ; 0, n) = c_p(n)`, which is `−1` by 3.4 of
`RamanujanSum`. So `Σ_{m ≠ 0} |S(ψ; m, n)|² = p² − p − 1`: the mean of `|S|²` over `m ≠ 0` is about
`p`.

**Definition** (`hyperbolaEnergy`). `E(q)` is the number of quadruples `(x₁, x₂, y₁, y₂)` of units
with `x₁ + x₂ = y₁ + y₂` and `x₁⁻¹ + x₂⁻¹ = y₁⁻¹ + y₂⁻¹`: the additive energy of the hyperbola
`{(x, x⁻¹)}` in `(ℤ/q)²`.

**4.5 Fourth moment** (`sum_norm_kloostermanSum_pow_four`). `Σ_{m, n} |S(ψ; m, n)|⁴ = q²·E(q)`.

*Proof.* `|S|⁴ = |S²|²`, and
`S(ψ; m, n)² = Σ_{x₁, x₂} ψ(n(x₁⁻¹ + x₂⁻¹)) ψ(m(x₁ + x₂))`. Apply 4.3 over `m`, with `i = (x₁, x₂)`,
`u(i) = x₁ + x₂` and `w(i) = ψ(n(x₁⁻¹ + x₂⁻¹))`. This gives `q` times the sum, over pairs
`(x₁, x₂)` and `(y₁, y₂)` with `x₁ + x₂ = y₁ + y₂`, of `ψ(n(x₁⁻¹ + x₂⁻¹))·conj ψ(n(y₁⁻¹ + y₂⁻¹))`.
Summing over `n` by 4.2 leaves `q` for each such quadruple that also satisfies
`x₁⁻¹ + x₂⁻¹ = y₁⁻¹ + y₂⁻¹`, and `0` for the others, so the total is `q·q·E(q)`. ∎

## 5. Kloosterman's bound

Here `q = p` is prime, so `ℤ/p` is a field and there are `p − 1` units.

**5.1** (`hyperbolaEnergy_le`). `E(p) ≤ 3(p − 1)²`.

*Proof.* Fix `(x₁, x₂)` and let `s = x₁ + x₂`. A solution `(y₁, y₂)` is determined by `y₁`, since
`y₂ = s − y₁`. So there are at most `p − 1` solutions. Clearing denominators in
`y₁⁻¹ + y₂⁻¹ = x₁⁻¹ + x₂⁻¹` gives `s·y₁y₂ = s·x₁x₂`, as `y₁ + y₂ = s`, and with `y₂ = s − y₁` this
yields

`(y₁ − x₁)(y₁ − x₂)·s = 0`.

So if `s ≠ 0`, then `y₁ ∈ {x₁, x₂}`: at most `2` solutions. The pairs `(x₁, x₂)` with
`x₁ + x₂ = 0` are determined by `x₁`, so there are at most `p − 1` of them. Hence
`E(p) ≤ (p − 1)·(p − 1) + 2·(p − 1)²`. ∎

(For odd `p`, `E(p) = 3(p − 1)(p − 2)`.)

**5.2 Kloosterman's bound** (`norm_kloostermanSum_pow_four_le`, `norm_kloostermanSum_le`). If
`m ≠ 0` or `n ≠ 0`, then `|S(ψ; m, n)|⁴ ≤ 3p³`, so `|S(ψ; m, n)| ≤ 3^(1/4)·p^(3/4)`.

*Proof.* By 1.1 we may assume `m ≠ 0`. For each of the `p − 1` units `a`, 1.2 gives
`S(ψ; a, a⁻¹mn) = S(ψ; 1, mn) = S(ψ; m, n)`. Keeping only the terms `(a, a⁻¹mn)` of the fourth
moment, 4.5 and 5.1 give

`(p − 1)·|S(ψ; m, n)|⁴ ≤ p²·E(p) ≤ 3p²(p − 1)²`.

Divide by `p − 1 > 0`: `|S(ψ; m, n)|⁴ ≤ 3p²(p − 1) ≤ 3p³`. Take fourth roots. ∎

The trivial bound is `p − 1`; the exponent `3/4` was the first improvement (Kloosterman, 1926).
Weil's bound `|S(ψ; m, n)| ≤ 2√p` for `mn ≠ 0` is far deeper and is not proved here.
