# MathInfra

Machine-checked mathematical infrastructure in Lean 4 on top of Mathlib.

## Layout

Topics are split by whether they had already been formalized elsewhere when checked
(November 2026, against Mathlib of 2026-11-19, open Mathlib PRs and the Isabelle AFP):

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

- `LucasSeq`: Lucas sequences `U_n(P, Q)`, `V_n(P, Q)` over any commutative ring: addition,
  doubling and composition formulas, Binet formulas, strong divisibility, and the behaviour
  modulo a prime (law of apparition). Mathlib has only special cases (Fibonacci, Chebyshev,
  Dickson, the Pell solutions of `PellMatiyasevic`, the Lucas–Lehmer sequence); this file
  proves the first three are special cases. Closest prior art: the one-parameter `U`-only
  theory `Lucas_Sequences` in the AFP entry *Diophantine_Universal_Pairs*.
- `GaussSeq`: the Gauss congruences `n ∣ Σ_{d ∣ n} μ(d)·f(n/d)` (also called Dold
  congruences; such sequences are also called realizable sequences): two characterisations
  (divisor sums of `d·h(d)`, and congruences modulo prime powers), the subring of sequences
  satisfying them, Burnside's formula, the two basic examples `aⁿ` (Fermat's little theorem
  for every modulus) and fixed-point counts of a self-map of a finite set, and necklace
  numbers. Closest prior art: the necklace proof of Fermat's little theorem in HOL4 (Chan and
  Norrish, 2013).

### FormalizedElsewhere

- `QAnalog`: q-numbers, q-factorials, Gaussian binomial coefficients, the q-binomial theorem
  and universality. Mathlib lists q-factorials and q-binomials as a TODO. Formalized in
  open Mathlib PR [#43780](https://github.com/leanprover-community/mathlib4/pull/43780)
  (same names `qNat`, `qFactorial`; also q-Pochhammer and the count of subspaces of `𝔽_q^n`)
  and in the AFP entry *Combinatorial_Q_Analogues* (also q-Vandermonde).
- `RamanujanSum`: Ramanujan sums `c_q(n)`: the divisor-sum characterisation, values,
  periodicity, multiplicativity in `q`, Hölder's formula, and `c_q(n)` as a sum of powers of
  the primitive `q`-th roots of unity in any integral domain that has one. Formalized in the
  AFP entry *Gauss_Sums* (theory `Ramanujan_Sums`, Apostol chapter 8).
- `DedekindSum`: the sawtooth function `((x))` and its distribution relation; Dedekind sums
  `s(h, k)`: symmetries, homogeneity, an integer formula, the bound `|s(h, k)| ≤ s(1, k)`, the
  reciprocity law, and the integrality of `6k·s(h, k)` with the congruence
  `12hk·s(h, k) ≡ h² + 1 (mod k)`. Formalized in the AFP entry *Dedekind_Sums* (Apostol,
  *Modular Functions and Dirichlet Series*, chapter 3).

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

- Lucas pseudoprimes and the Lucas `n + 1` primality test; the Lucas–Lehmer test as a
  corollary.
- The rank of apparition as a definition, and periodicity modulo `m` (Pisano periods).
- Primitive divisors (Carmichael's theorem; Zsigmondy for the case `(a + b, ab)`).
- Solutions of Pell-type equations `x² − D y² = 4 Qⁿ` via `lucasV_sq`.

From Ramanujan sums:

- The bound `|c_q(n)| ≤ gcd(q, n)`, from Hölder's formula.
- Orthogonality: for `r, s ∣ q`, `Σ_{n mod q} c_r(n)·c_s(n)` is `q·φ(r)` if `r = s` and `0`
  otherwise.
- Ramanujan expansions, such as `σ(n)/n = (π²/6)·Σ_{q ≥ 1} c_q(n)/q²` for `n ≥ 1`.
- Kloosterman sums `S(m, n; q)`, which reduce to `c_q(m)` when `n = 0`, and the singular series
  of the circle method.

From Dedekind sums:

- The transformation law of the Dedekind eta function under `SL₂(ℤ)`, whose root of unity is
  expressed through `s(d, c)`, and the Rademacher function `Φ`.
- The cotangent formula `s(h, k) = (1/(4k))·Σ_{0<r<k} cot(πr/k)·cot(πhr/k)` for coprime
  `h, k`, from a finite Fourier expansion of `((r/k))`.
- Rademacher's three-term reciprocity, and Dedekind–Rademacher sums with shifts.
- Rademacher's exact formula for the partition function, whose Kloosterman-type sums have
  phases `e^(πi·s(h, k))`.

From Gauss congruences:

- Gauss's count `M(q, n)` of the monic irreducible polynomials of degree `n` over `𝔽_q`, from
  the fixed points of the Frobenius map on `𝔽_(qⁿ)`.
- Lyndon words, counted by `M(a, n)`, and the Chen–Fox–Lyndon factorisation.
- Traces `tr(Aⁿ)` of the powers of an integer matrix, hence Lucas `V_n(P, Q)`, satisfy the
  Gauss congruences. In general, `f` satisfies them if and only if `exp(Σ f(n)·tⁿ/n)` has
  integer coefficients (for fixed-point counts, the Artin–Mazur zeta function).
- The big Witt vectors and the necklace ring, whose ghost components are these sequences.
