# MathInfra

Machine-checked mathematical infrastructure in Lean 4 on top of Mathlib.

## Layout

Topics are split by whether they had already been formalized elsewhere when checked
(November 2026, against Mathlib of 2026-11-19, open Mathlib PRs, other Lean projects and the
Isabelle AFP):

- `New/`: no existing formalization found in any proof assistant.
- `FormalizedElsewhere/`: already formalized in another library or in an open Mathlib PR.
  None of these are in Mathlib itself yet.

Each topic `X` has four files:

- `MathInfra/<folder>/X.lean`: the definitions and theorems.
- `MathInfra/<folder>/X-proofs.md`: the same results and proofs in ordinary language, each
  tagged with the Lean theorem that checks it.
- `MathInfraTest/<folder>/X.lean`: known values and the theorems in use.
- `MathInfraTest/<folder>/XAxioms.lean`: every public theorem with the axioms it depends
  on, as a check that fails the build if that ever changes.

`.elan/` holds the Lean toolchain, kept on this drive (not on PATH, nothing on C:).

### New

- `GaussSeq`: the Gauss congruences `n ∣ Σ_{d ∣ n} μ(d)·f(n/d)` (also called Dold
  congruences; such sequences are also called realizable sequences): two characterisations
  (divisor sums of `d·h(d)`, and congruences modulo prime powers), the subring of sequences
  satisfying them, Burnside's formula, the two basic examples `aⁿ` (Fermat's little theorem
  for every modulus) and fixed-point counts of a self-map of a finite set, and necklace
  numbers. Closest prior art: the necklace proof of Fermat's little theorem in HOL4 (Chan and
  Norrish, 2013).
- `LucasRank`: the rank of apparition of a Lucas sequence (also called the rank of appearance or
  entry point): the least `r > 0` with `U_r = 0` in any commutative ring. When `Q` is a unit,
  `U_n = 0` exactly when `r ∣ n`; the rank behaves well under ring homomorphisms and is the
  `lcm` over a product of rings. Over a finite ring with `Q` a unit every Lucas sequence is
  purely periodic, and the periods of `U` are exactly the multiples of `r·ord(U_(r+1))` (for
  Fibonacci numbers, the Pisano period). Modulo an odd prime `p ∤ Q` the rank divides
  `p − (D/p)`, and modulo any prime `p ∤ Q` it is at most `p + 1`. This gives the Lucas `N + 1`
  primality test. Also Lucas probable primes and pseudoprimes (the smallest for `(1, −1)` is
  `323`). Mathlib of 2026-11-19 has the `N − 1` test `lucas_primality` and the Lucas–Lehmer test
  but no rank of apparition, nor has the Lean project TauCeti, which has Lucas sequences. Weaker
  forms exist elsewhere: some period exists in the AFP theory `Lucas_Sequences` (`Q = 1`), and
  agda-unimath has the Fibonacci Pisano period and entry point, with one direction of
  `m ∣ F_n ↔ r ∣ n`. Open Mathlib PR
  [#44020](https://github.com/leanprover-community/mathlib4/pull/44020) has the Fibonacci law of
  apparition, which `LucasSeq` generalises.

### FormalizedElsewhere

- `LucasSeq`: Lucas sequences `U_n(P, Q)`, `V_n(P, Q)` over any commutative ring: addition,
  doubling and composition formulas, Binet formulas, strong divisibility, and the behaviour
  modulo a prime (law of apparition). Mathlib (2026-11-19) has only special cases (Fibonacci,
  Chebyshev, Dickson, the Pell solutions of `PellMatiyasevic`, the Lucas–Lehmer sequence); this
  file proves the first three are special cases. Formalized in the Lean project
  [TauCeti](https://github.com/TauCetiProject/TauCeti) (`TauCeti/NumberTheory/LucasSequence/`,
  checked 2026-11-21: the same names `lucasU`, `lucasV`, the addition, doubling and composition
  formulas, Cassini, Binet, strong divisibility and the Fibonacci, Mersenne, Lucas–Lehmer, Dickson
  and Chebyshev cases). Not there: the `q`-number case and everything modulo a prime (`V_p ≡ P`,
  `U_p ≡ (D/p)`, the law of apparition, whose Fibonacci case is in the open Mathlib PR
  [#44020](https://github.com/leanprover-community/mathlib4/pull/44020)). The AFP entry
  *Diophantine_Universal_Pairs* has the one-parameter `U`-only theory `Lucas_Sequences`.
- `QAnalog`: q-numbers, q-factorials, Gaussian binomial coefficients, the q-binomial theorem
  and universality. Mathlib lists q-factorials and q-binomials as a TODO. Formalized in
  open Mathlib PR [#43780](https://github.com/leanprover-community/mathlib4/pull/43780)
  (same names `qNat`, `qFactorial`; also q-Pochhammer and the count of subspaces of `𝔽_q^n`)
  and in the AFP entry *Combinatorial_Q_Analogues* (also q-Vandermonde).
- `RamanujanSum`: Ramanujan sums `c_q(n)`: the divisor-sum characterisation, values,
  periodicity, multiplicativity in `q`, Hölder's formula, and `c_q(n)` as a sum of powers of
  the primitive `q`-th roots of unity in any integral domain that has one. Formalized in the
  AFP entry *Gauss_Sums* (theory `Ramanujan_Sums`, Apostol chapter 8) and in the Lean project
  [TauCeti](https://github.com/TauCetiProject/TauCeti)
  (`TauCeti/NumberTheory/CircleMethod/RamanujanSum.lean`, also `|c_q(n)| ≤ gcd(q, n)`).
- `DedekindSum`: the sawtooth function `((x))` and its distribution relation; Dedekind sums
  `s(h, k)`: symmetries, homogeneity, an integer formula, the bound `|s(h, k)| ≤ s(1, k)`, the
  reciprocity law, and the integrality of `6k·s(h, k)` with the congruence
  `12hk·s(h, k) ≡ h² + 1 (mod k)`. Formalized in the AFP entry *Dedekind_Sums* (Apostol,
  *Modular Functions and Dirichlet Series*, chapter 3) and in the Lean project
  [TauCeti](https://github.com/TauCetiProject/TauCeti) (`TauCeti/NumberTheory/DedekindSum.lean`,
  used there for the multiplier of the Dedekind eta function).
- `Wolstenholme`: Wolstenholme's theorem `C(2p − 1, p − 1) ≡ 1 (mod p³)` for primes `p ≥ 5`,
  Babbage's `C(2p − 1, p − 1) ≡ 1 (mod p²)` for odd `p`, and Ljunggren's (Jacobsthal's)
  congruence `C(ap, bp) ≡ C(a, b)` modulo `p²` for every prime and modulo `p³` for `p ≥ 5`, all
  from `(1 + X)^p = 1 + X^p + p·G`, and the harmonic form `p² ∣ num(H_(p−1))` for `p ≥ 5`. Also
  `C(p, k)/p ≡ (−1)^(k−1)/k`, power sums of inverses modulo `p`, and Fermat quotients `q_p(a)`:
  `q_p(ab) ≡ q_p(a) + q_p(b)`, `q_p(a + pk) ≡ q_p(a) − k/a`, the Wieferich condition, and
  Eisenstein's `2q_p(2) ≡ Σ_{0<k<p} (−1)^(k−1)/k ≡ −H_((p−1)/2) (mod p)` for odd `p`. Not in
  Mathlib (2026-11-19); the closed, unmerged Mathlib PR
  [#29675](https://github.com/leanprover-community/mathlib4/pull/29675) had the `p³` binomial
  congruence alone. The Lean library
  [atlas-lean](https://github.com/facebookresearch/atlas-lean) has the harmonic form in
  `ZMod (p ^ 2)`, a `fermatQuotient` definition and, as a private lemma, the `p³` form of
  Ljunggren's congruence; an AlphaProof proof of the binomial form is linked from
  formal-conjectures. Babbage's theorem, the `p²` congruence for all primes, the formulas for
  `q_p(ab)` and `q_p(a + pk)`, and Eisenstein's congruence were not found elsewhere.
- `ZetaSeries`: zeta series `exp(Σ f(n)·Xⁿ/n)` of sequences, defined without division by
  `P(0) = 1` and `P' = P·Σ f(n+1)·Xⁿ`, and Witt products `Π_d (1 − X^d)^(−h(d))`. Dold's
  criterion: `f : ℕ → ℤ` satisfies the Gauss congruences of `GaussSeq` if and only if its zeta
  series has integer coefficients. Jacobi's formula: `det(1 − X·A)` is a zeta series of
  `n ↦ −tr(Aⁿ)`. Hence `tr(Aⁿ)`, for every square integer matrix `A`, and Lucas `V_n(P, Q)`,
  for integers `P`, `Q`, satisfy the Gauss congruences; in particular
  `tr(A^(p^(k+1)·m)) ≡ tr(A^(p^k·m)) (mod p^(k+1))`. Also: the Artin–Mazur zeta function of a
  self-map of a finite set has integer coefficients, and the cyclotomic identity
  `1/(1 − aX) = Π_d (1 − X^d)^(−M(a, d))` holds degree by degree. Mathlib (2026-11-19) has
  `tr(Aᵖ) = tr(A)ᵖ` over finite fields and the degree-1 coefficient of `det(1 − X·A)`; Jacobi's
  formula was proposed in the closed, unmerged Mathlib PR
  [#44901](https://github.com/leanprover-community/mathlib4/pull/44901). The direction "Gauss
  congruences ⇒ integral zeta series" is `integral_exp_of_dold` in the Lean project
  `the-omega-institute/trureturing`. The converse, the Witt products and the trace and Lucas
  results were not found elsewhere.
- `IrreducibleCount`: the number `M(n)` of monic irreducible polynomials of degree `n` over a
  finite field with `q` elements. For `n > 0`, `X^(q^n) − X` is the product of those whose
  degree divides `n`. From this follow Gauss's formula `n·M(n) = Σ_{d ∣ n} μ(d)·q^(n/d)` (so
  `M(n)` is the necklace number `M(q, n)` of `GaussSeq`), the counts in degree `1` and in prime
  degree, the prime polynomial theorem `q^n − 2q^⌊n/2⌋ < n·M(n) ≤ q^n` for `n > 0`, and
  existence in every positive degree. Mathlib (2026-11-19) has the divisibility criterion used
  for the factorisation but no count, and neither has the open PR
  [#45947](https://github.com/leanprover-community/mathlib4/pull/45947) (Rabin's test).
  Gauss's formula, the counts in degrees `1` and `2`, the bound `q^n/(2n) ≤ M(n)`, existence
  and the multiplicity of each factor of `X^(q^n) − X` are in the AFP entry *Finite_Fields*
  (Karayel, theory `Card_Irreducible_Polynomials`). The product identity as stated, the
  prime-degree count, the upper bound and the lower bound (sharper for `n ≥ 3`) were not found
  elsewhere.
- `EulerianNumber`: Eulerian numbers `A(n, k)` and Eulerian polynomials `A_n(t)` (also called
  Euler–Frobenius numbers and polynomials; not the Euler numbers). `A(n, k)` counts the
  permutations of `n` letters with `k` descents. Also: symmetry, `Σ_k A(n, k) = n!`,
  `A(n, 1) = 2ⁿ − n − 1`, Worpitzky's identity `xⁿ = Σ_k A(n, k)·C(x + k, n)`, the recurrence
  `A_{n+1} = (1 + nt)·A_n + t(1 − t)·A_n'`, the generating function
  `Σ_m (m + 1)ⁿ·tᵐ = A_n(t)/(1 − t)ⁿ⁺¹`, and the explicit formula
  `A(n, k) = Σ_{j ≤ k} (−1)ʲ·C(n + 1, j)·(k + 1 − j)ⁿ`. Not in Mathlib (2026-11-21, no PR). The
  polynomials, `A_n(1) = n!` and the generating function are in the AFP entry
  *Linear_Recurrences* (Eberl, theory `Eulerian_Polynomials`). The descent count, Worpitzky's
  identity, the symmetry and the explicit formula were not found elsewhere.
- `KloostermanSum`: Kloosterman sums `S(ψ; m, n) = Σ_{x ∈ (ℤ/q)ˣ} ψ(mx + nx⁻¹)` for any additive
  character `ψ` with values in a commutative ring: symmetries, `S(um, n) = S(m, un)` and so
  `S(u, n) = S(1, un)` for a unit `u`, twisted multiplicativity
  `S(m, n; q₁q₂) = S(q̄₂m, q̄₂n; q₁)·S(q̄₁m, q̄₁n; q₂)` for coprime `q₁`, `q₂`, where `q̄₂` is the
  inverse of `q₂` modulo `q₁` and `q̄₁` that of `q₁` modulo `q₂`, and `S(ψ; m, 0) = c_q(m)` (the
  Ramanujan sums of `RamanujanSum`) for primitive `ψ` with values in an integral domain. Over `ℂ`
  the sums are real, and for primitive `ψ`, `Σ_m |S(ψ; m, n)|² = q·φ(q)` and the fourth moment
  `Σ_{m, n} |S(ψ; m, n)|⁴` is `q²` times the additive energy of the hyperbola `{(x, x⁻¹)}`. For a
  prime `p` that energy is at most `3(p − 1)²`, which gives Kloosterman's bound
  `|S(ψ; m, n)| ≤ 3^(1/4)·p^(3/4)` for `(m, n) ≠ (0, 0)`. Not in Mathlib (2026-11-19, no PR). The
  Lean 4 project [jieun38-kim/Kloosterman](https://github.com/jieun38-kim/Kloosterman) (2023) has
  the definition over `ℂ`, invariance modulo `q`, `S(a, b) = S(b, a)` and `S(a, b) = S(1, ab)` for
  `a`, `b` coprime to `q`, but leaves `S(um, n) = S(m, un)` and twisted multiplicativity as
  commented-out statements with `sorry`. Open TauCeti roadmap PRs and the project
  `BrandonMYates/kklab` define Kloosterman sums over finite fields but prove none of the results
  here. Nothing in the AFP, Rocq or HOL. The general character, the proofs of `S(um, n) = S(m, un)`
  and of twisted multiplicativity, the Ramanujan-sum case, the moments and Kloosterman's bound were
  not found elsewhere.

## Running

Lean is not on PATH. In PowerShell, from this folder:

```powershell
$env:ELAN_HOME = 'E:\math\.elan'; $env:PATH = "E:\math\.elan\bin;$env:PATH"
lake build
```

`lake build` checks the library and all test files. A successful build with no warnings
means every proof, every example and the axiom audit passed.

## Where this leads

None of the following is done here; these are the natural next steps.

- Counting `k`-dimensional subspaces of `𝔽_q^n` (`gaussBinom q n k` with `q` a prime power).
- q-Vandermonde and q-Lucas, cyclic sieving (`q` a root of unity).
- q-Pochhammer symbols, Euler's partition identities, Jacobi triple product.
- q-exponentials and the quantum plane (`yx = q xy`); needs a noncommutative variant.

From Lucas sequences:

- Primitive divisors (Carmichael's theorem; Zsigmondy for the case `(a + b, ab)`, which TauCeti
  has for coprime natural `a > b > 0`).
- Solutions of Pell-type equations `x² − D y² = 4 Qⁿ` via `lucasV_sq`.

From Ramanujan sums:

- The bound `|c_q(n)| ≤ gcd(q, n)`, from Hölder's formula (TauCeti has the bound).
- Orthogonality: for `r, s ∣ q`, `Σ_{n mod q} c_r(n)·c_s(n)` is `q·φ(r)` if `r = s` and `0`
  otherwise.
- Ramanujan expansions, such as `σ(n)/n = (π²/6)·Σ_{q ≥ 1} c_q(n)/q²` for `n ≥ 1`.
- The singular series of the circle method.

From Dedekind sums:

- The transformation law of the Dedekind eta function under `SL₂(ℤ)`, whose root of unity is
  expressed through `s(d, c)`, and the Rademacher function `Φ` (TauCeti has the transformation
  law).
- The cotangent formula `s(h, k) = (1/(4k))·Σ_{0<r<k} cot(πr/k)·cot(πhr/k)` for coprime
  `h, k`, from a finite Fourier expansion of `((r/k))`.
- Rademacher's three-term reciprocity, and Dedekind–Rademacher sums with shifts.
- Rademacher's exact formula for the partition function, whose Kloosterman-type sums have
  phases `e^(πi·s(h, k))`.

From the rank of apparition:

- The Lucas–Lehmer test as a corollary of the `N + 1` test, and its relatives for
  `N = k·2^n − 1` (Lucas–Lehmer–Riesel).
- The converse of the `N + 1` test (for prime `N` some `(P, Q)` has rank `N + 1`), strong
  Lucas probable primes, and the Baillie–PSW test.
- Pisano periods: `π(p^k) ∣ p^(k−1)·π(p)`, `π(m) ≤ 6m`, Wall–Sun–Sun primes.
- Primality certificates from partial factorisations of `N + 1` (the analogue of Pocklington).

From Gauss congruences:

- Lyndon words, counted by `M(a, n)`, and the Chen–Fox–Lyndon factorisation.
- The big Witt vectors and the necklace ring, whose ghost components are these sequences.

From zeta series:

- The infinite Witt product: every `P ∈ 1 + Xℤ⟦X⟧` is `Π_{d ≥ 1} (1 − X^d)^(−h(d))` for a unique
  `h`, which identifies `1 + Xℤ⟦X⟧` with the big Witt vectors `W(ℤ)`.
- Subshifts of finite type: `tr(Aⁿ)` counts the closed walks of length `n` in a graph, so the
  Bowen–Lanford formula `ζ(t) = 1/det(1 − tA)` follows from Jacobi's formula.
- The Gauss congruences for the traces `Tr(αⁿ)` of an algebraic integer `α`, using the integer
  matrix of multiplication by `α`.
- Which linear recurrence sequences satisfy the Gauss congruences (Minton's theorem).

From counting irreducible polynomials:

- The zeta function of `𝔽_q[X]`: `Π_f (1 − t^(deg f))⁻¹ = 1/(1 − qt)` over monic irreducible `f`,
  as an identity of power series.
- Primes in arithmetic progressions in `𝔽_q[X]` (Dirichlet's theorem for polynomials).
- The number of elements of `𝔽_(qⁿ)` of degree exactly `n` over `𝔽_q`, which is `n·M(n)`, and
  the irreducible factors of cyclotomic polynomials over `𝔽_q`.
- The count `q^n − q^(n−1)` of monic squarefree polynomials of degree `n ≥ 2`, and the factorisation
  statistics behind the analysis of Berlekamp's and Rabin's algorithms.

From Wolstenholme's theorem:

- Glaisher's `H_(p−1) ≡ −p²·B_(p−3)/3 (mod p³)`, which ties the Wolstenholme primes
  (`C(2p − 1, p − 1) ≡ 1 (mod p⁴)`) to Bernoulli numbers, and the Kummer congruences.
- Jacobsthal's sharpening of Ljunggren's congruence, whose modulus grows with
  `v_p(ab(a − b))`, and supercongruences for Apéry numbers.
- Lerch's formula for `q_p(a)` and the Wieferich criterion for the first case of Fermat's
  last theorem.

From Eulerian numbers:

- Sums of powers `Σ_{m<N} mⁿ` and the values `Li_(−n)(t) = t·A_n(t)/(1 − t)ⁿ⁺¹` of the
  polylogarithm (the power-series identity is in the AFP entry), and Frobenius's formula
  `A_n(t) = Σ_k k!·S(n, k)·(t − 1)ⁿ⁻ᵏ` with Stirling numbers of the second kind.
- Ehrhart theory: `A_n(t)` is the `h*`-polynomial of the cube `[0, 1]ⁿ`, and `A(n, k)/n!` is the
  volume of the slice `k ≤ x₁ + ⋯ + xₙ ≤ k + 1` of the cube (Laplace), a hypersimplex.
- Real-rootedness of `A_n(t)`, hence log-concavity and the central limit theorem for descents.
- Major index and `q`-Eulerian polynomials (MacMahon's equidistribution), and type-`B`
  Eulerian numbers for signed permutations.

From Kloosterman sums:

- Weil's bound `|S(m, n; p)| ≤ 2√p` for `mn ≠ 0`, through the Riemann hypothesis for curves or
  Stepanov's method, and its extension `|S(m, n; q)| ≤ τ(q)·gcd(m, n, q)^(1/2)·q^(1/2)`
  (Weil–Estermann), by twisted multiplicativity and the prime-power case.
- Explicit evaluation at prime powers `p^k`, `k ≥ 2` (stationary phase), and Salié sums, which
  have a closed form.
- Selberg's identity `S(m, n; q) = Σ_{d ∣ (m, n, q)} d·S(mn/d², 1; q/d)`.
- The Fourier coefficients of Poincaré series (series of Kloosterman sums), and the Petersson and
  Kuznetsov formulas.
