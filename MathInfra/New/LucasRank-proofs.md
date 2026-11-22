# The rank of apparition: the proofs in ordinary language

This is the human-readable companion to `MathInfra/New/LucasRank.lean`. Each numbered statement
names the Lean theorem that checks it, and the proofs follow the same route as the Lean proofs.
Numbers such as "LucasSeq 2.1" refer to `MathInfra/New/LucasSeq-proofs.md`.

Throughout, `R` and `S` are commutative rings, `P`, `Q` are in `R`, `U = U(P, Q)` is the Lucas
sequence of the first kind, and `D = P² − 4Q`. A *solution* is any `W : ℕ → R` with
`W(n+2) = P·W(n+1) − Q·W(n)`.

## Prior art

Checked in November 2026 against Mathlib of 2026-11-19, open and closed Mathlib PRs, the Lean
Zulip, the Isabelle AFP, Coq (including Coqprime), HOL4, HOL Light and Mizar. None of them has the
rank of apparition of a general Lucas sequence, the bound `r(p) ≤ p + 1`, the `N + 1` test or
Lucas pseudoprimes. Mathlib has Lucas's `N − 1` test (`lucas_primality`), Lucas–Lehmer and Fermat
pseudoprimes. The Lean project TauCeti has Lucas sequences and their strong divisibility
(`TauCeti/NumberTheory/LucasSequence`), and for `aⁿ − bⁿ` the analogue of 2.2,
`p ∣ aᵏ − bᵏ ↔ ord_p(a/b) ∣ k`, but no rank of a Lucas sequence. There are weak forms of §2 and
§4: the AFP entry *Diophantine_Universal_Pairs* (theory `Lucas_Sequences`, `Q = 1` only) shows
that some period modulo `N` exists, and agda-unimath defines the Pisano period and the entry point
(`cofibonacci`) of the Fibonacci numbers, with one direction of 2.2 (if `cofibonacci m ∣ n` then
`m ∣ F(n)`; the converse is left unproved there). Open Mathlib PR
[#44020](https://github.com/leanprover-community/mathlib4/pull/44020) proves the law of apparition
(LucasSeq 9.3) for Fibonacci numbers.

Other names: the rank of apparition is also called the rank of appearance, order of appearance or
entry point; agda-unimath calls the Fibonacci entry point the *cofibonacci* sequence.

## 1. A zero of `U`

**1.1** (`IsLucasRec.add_of_lucasU_eq_zero`). If `U(r) = 0`, every solution satisfies
`W(n + r) = U(r+1)·W(n)`.

*Proof.* For `n = k + 1`, the shift formula (LucasSeq 2.1) gives
`W(k + r + 1) = U(r+1)·W(k+1) − Q·U(r)·W(k) = U(r+1)·W(k+1)`. For `n = 0` and `r = 0` there is
nothing to prove. For `n = 0` and `r = s + 1`, LucasSeq 2.2 gives
`W(s+1) = W(1)·U(s+1) − Q·W(0)·U(s) = −Q·W(0)·U(s)`, while `U(s+2) = P·U(s+1) − Q·U(s) = −Q·U(s)`;
so `W(r) = U(r+1)·W(0)`. ∎

**1.2** (`IsLucasRec.add_mul_of_lucasU_eq_zero`). If `U(r) = 0` then `W(n + kr) = U(r+1)^k·W(n)`.
Induction on `k` with 1.1.

**1.3** (`lucasU_succ_sq_of_lucasU_eq_zero`, `isUnit_lucasU_succ`). If `U(r) = 0` then
`U(r+1)² = Q^r`, by Cassini's identity (LucasSeq 4.4). So `U(r+1)` is a unit when `Q` is.

## 2. The rank of apparition

**Definition** (`lucasRank`). The *rank of apparition* `r = r(P, Q)` is the least `n > 0` with
`U(n) = 0`, or `0` if there is none. Taking `R = ℤ/m`, it is the least `n > 0` with `m ∣ U(n)` (or
`0`).

**2.1** (`lucasU_lucasRank`, `lucasRank_eq_zero_iff`, `lucasU_ne_zero_of_lt_lucasRank`,
`lucasRank_eq`). `U(r) = 0`. `r = 0` exactly when `U(n) ≠ 0` for all `n > 0`. `U(n) ≠ 0` for
`0 < n < r`. Conversely, if `U(s) = 0` for some `s > 0` and `U(m) ≠ 0` for `0 < m < s`, then
`r = s`. These hold by definition.

**2.2** (`lucasU_eq_zero_iff_lucasRank_dvd`). If `Q` is a unit, then `U(n) = 0` if and only if
`r ∣ n`.

*Proof.* Write `n = (n mod r) + (n div r)·r`. By 1.2 and 2.1,
`U(n) = U(r+1)^(n div r)·U(n mod r)`, and `U(r+1)` is a unit by 1.3. So `U(n) = 0` exactly when
`U(n mod r) = 0`. If `r > 0`, then `n mod r < r`, and by 2.1 this happens only when `n mod r = 0`.
If `r = 0`, then `n mod r = n`, and by 2.1 `U(n) = 0` only when `n = 0`. ∎

## 3. Ring homomorphisms and products

**3.1** (`lucasRank_map_dvd`). If `f : R → S` is a ring homomorphism and `f(Q)` is a unit, then
`r(f(P), f(Q)) ∣ r(P, Q)`. Indeed `f` maps `U(P, Q)` to `U(f(P), f(Q))` and `0` to `0`; apply 2.2
in `S`. In particular, if `d ∣ m` and `Q` is prime to `d`, the rank modulo `d` divides the rank
modulo `m`.

**3.2** (`lucasRank_map_of_injective`). If `f` is injective, the ranks are equal, since then
`f(U(n)) = 0` exactly when `U(n) = 0`.

**3.3** (`lucasU_prod`, `lucasRank_prod`). In `R × S`,
`U((P, P'), (Q, Q'))(n) = (U(P, Q)(n), U(P', Q')(n))`. If `Q` and `Q'` are units, the rank is the
`lcm` of the two ranks.

*Proof.* The first claim holds because both projections are ring homomorphisms. For the second, by
2.2 a natural number `n` is divisible by the rank in `R × S` exactly when `U(n) = 0` in both
factors, which holds exactly when both ranks divide `n`, that is, when their `lcm` divides `n`.
Two natural numbers with the same multiples are equal. ∎

With the Chinese remainder theorem `ℤ/mn ≅ ℤ/m × ℤ/n` and 3.2, this gives
`r(mn) = lcm(r(m), r(n))` for coprime `m`, `n` prime to `Q`.

## 4. Periodicity

**Definition** (`lucasPeriod`). `π = r·ord(U(r+1))`, where `ord` is the multiplicative order (`0`
if infinite). For Fibonacci numbers modulo `m` this is the Pisano period.

**4.1** (`IsLucasRec.periodic`). Every solution satisfies `W(n + π) = W(n)`. By 1.2 with
`k = ord(U(r+1))`, `W(n + kr) = U(r+1)^k·W(n) = W(n)`.

**4.2** (`periodic_lucasU_iff`). If `Q` is a unit, `U(n + T) = U(n)` for all `n` if and only if
`π ∣ T`.

*Proof.* If `T` is a period, `U(T) = U(0) = 0`, so `T = rk` by 2.2. By 1.2,
`1 = U(1) = U(1 + kr) = U(r+1)^k`, so `ord(U(r+1)) ∣ k` and `π ∣ rk`. Conversely, multiples of a
period are periods (4.1). ∎

**4.3** (`lucasRank_pos`). If `R` is finite and `Q` is a unit, then `r > 0`.

*Proof.* The map `σ(a, b) = (b, P·b − Q·a)` on `R × R` is injective, because `Q` cancels. An
injective self-map of a finite set is a bijection, so `σ` is a permutation of some finite order
`k > 0`. By induction `σⁿ(0, 1) = (U(n), U(n+1))`, so `U(k) = 0` and `r ∣ k` by 2.2. As `k > 0`,
`r ≠ 0`. ∎

**4.4** (`lucasPeriod_pos`). If `R` is finite and `Q` is a unit, then `π > 0`: `r > 0` by 4.3, and
`U(r+1)` is a unit (1.3) of the finite group `R^×`, so it has positive order. So over a finite
ring with `Q` a unit every solution is purely periodic with period `π` (4.1), and by 4.2 `π` is
the least period of `U`.

## 5. Modulo a prime

Let `p` be a prime.

**5.1** (`ZMod.lucasRank_dvd_sub_legendreSym`). If `p` is odd, `P`, `Q` are integers and `p ∤ Q`,
then the rank modulo `p` divides `p − (D/p)`. This is the law of apparition (LucasSeq 9.3)
together with 2.2.

**5.2** (`ZMod.lucasRank_le`). For `P`, `Q` in `𝔽_p` with `Q ≠ 0`: `r ≤ p + 1`. (And `r > 0` by
4.3.)

*Proof.* For `p = 2`, `Q = 1` and a direct check shows `U(2) = 0` (if `P = 0`) or `U(3) = 0` (if
`P = 1`), so `r ∣ 2` or `r ∣ 3` by 2.2, and `r ≤ 3`. For odd `p`, lift `P`, `Q` to integers. By
5.1, `r` divides `p − (D/p)`, which is positive since `p ≥ 3` and at most `p + 1`. ∎

## 6. The Lucas `N + 1` primality test

**6.1** (private `eq_of_dvd_of_not_dvd_div`). If `r ∣ n` and `r ∤ n/q` for every prime `q ∣ n`,
then `r = n`.

*Proof.* Write `n = rk`. If `k ≠ 1`, let `q` be the least prime factor of `k`; then `q ∣ n` and
`r ∣ r·(k/q) = n/q`, a contradiction. So `k = 1`. ∎

**6.2** (`lucasU_primality`). Let `N > 1`, and let `P`, `Q` be in `ℤ/N` with `Q` a unit. If
`U(N+1) = 0`, and `U((N+1)/q)` is a unit for every prime `q ∣ N+1`, then `N` is prime.

*Proof.* Let `p` be the least prime factor of `N`, and reduce modulo `p`. Then `Q` stays a unit,
`U(N+1) = 0`, and every `U((N+1)/q)` stays a unit, hence nonzero. By 2.2 the rank `r` modulo `p`
divides `N + 1` but no `(N+1)/q`, so `r = N + 1` by 6.1. By 5.2, `N + 1 ≤ p + 1`. So `p ≥ N`, and
as `p ∣ N`, `p = N`. ∎

This is the `N + 1` counterpart of Lucas's `N − 1` test (Mathlib's `lucas_primality`). The test
needs the prime factors of `N + 1`. For example, for a Mersenne prime `N = 2^k − 1 > 3` the rank
for `(P, Q) = (2, −2)` is `N + 1` (a consequence of the Lucas–Lehmer test, not proved here), so
the test proves `N` prime, and only `q = 2` needs checking. For `N = 127` this is checked in
`MathInfraTest/New/LucasRank.lean`.

## 7. Lucas probable primes

**Definition** (`IsLucasProbablePrime`, `IsLucasPsp`). For integers `P`, `Q`, the number `N` is a
*Lucas probable prime* if `N ∣ U(N − (D/N))`, with the Jacobi symbol `(D/N)`. A *Lucas
pseudoprime* is a composite Lucas probable prime `N` with `gcd(N, 2QD) = 1`. Without the last
condition every power `p^k` with `k ≥ 2` of an odd prime `p ∣ D` would qualify, since
`p^k ∣ U(p^k)`.

**7.1** (`Nat.Prime.isLucasProbablePrime`). Every odd prime `p ∤ Q` is a Lucas probable prime. For
prime `p` the Jacobi symbol is the Legendre symbol; apply the law of apparition (LucasSeq 9.3).

For `(P, Q) = (1, −1)` the smallest Lucas pseudoprime is `323 = 17·19`: `(5/323) = −1` and
`323 ∣ F(324)`.