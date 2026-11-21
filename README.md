# MathInfra

Machine-checked mathematical infrastructure in Lean 4 on top of Mathlib.

## Layout

- `MathInfra/QAnalog.lean`: q-numbers, q-factorials, Gaussian binomial coefficients, the
  q-binomial theorem and universality. Mathlib lists q-factorials and q-binomials as a TODO;
  this is the first layer.
- `QAnalog-proofs.md`: the same results and proofs in ordinary language, each tagged with
  the Lean theorem that checks it.
- `MathInfraTest/QAnalog.lean`: known values, the q-Pascal triangle, the theorems in use.
- `MathInfraTest/Axioms.lean`: every public theorem with the axioms it depends on, as a
  check that fails the build if that ever changes.
- `MathInfra/LucasSeq.lean`: Lucas sequences `U_n(P, Q)`, `V_n(P, Q)` over any commutative
  ring: addition, doubling and composition formulas, Binet formulas, strong divisibility,
  and the behaviour modulo a prime (law of apparition). Mathlib has only special cases
  (Fibonacci, Chebyshev, Dickson); this file proves they are special cases.
- `LucasSeq-proofs.md`: the same in ordinary language.
- `MathInfraTest/LucasSeq.lean`, `MathInfraTest/LucasSeqAxioms.lean`: checks and axiom audit
  for Lucas sequences.
- `MathInfra/RamanujanSum.lean`: Ramanujan sums `c_q(n)`: the divisor-sum characterisation,
  values, periodicity, multiplicativity in `q`, Hölder's formula, and `c_q(n)` as a sum of
  powers of the primitive `q`-th roots of unity in any integral domain that has one. Not in
  Mathlib.
- `RamanujanSum-proofs.md`: the same in ordinary language.
- `MathInfraTest/RamanujanSum.lean`, `MathInfraTest/RamanujanSumAxioms.lean`: checks and axiom
  audit for Ramanujan sums.
- `MathInfra/DedekindSum.lean`: the sawtooth function `((x))` and its distribution relation;
  Dedekind sums `s(h, k)`: symmetries, homogeneity, an integer formula, the bound
  `|s(h, k)| ≤ s(1, k)`, the reciprocity law, and the integrality of `6k·s(h, k)` with the
  congruence `12hk·s(h, k) ≡ h² + 1 (mod k)`. Not in Mathlib.
- `DedekindSum-proofs.md`: the same in ordinary language.
- `MathInfraTest/DedekindSum.lean`, `MathInfraTest/DedekindSumAxioms.lean`: checks and axiom
  audit for Dedekind sums.
- `.elan/`: the Lean toolchain, kept on this drive (not on PATH, nothing on C:).

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
