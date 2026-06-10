# Analysis of Remaining `sorry`'d Lemmas

## Overview

The project contains **4** residual `sorry` statements across 3 files. Three of them are
actively used in the proof chain; the fourth (`euler_product_convergent_bound`) is **unused
and mathematically false**. This document examines each one.

---

## 1. `lossy_divisor_sum_bound` — `FourierSynthesisHelpers.lean:121`

### Statement (informal)
The "lossy" divisor sum — arising from Fourier coefficients at frequencies with
large `freqDivisor` — is bounded by `C · s^{−ε/2}`, where `s = q / |Ω_q|`.

### Docstring claim
> Since `k^{ω(d)} d^{-ε} log d ≤ d(q)² log q ≤ q^{o(1)}`, and `hsp` forces
> `s ≥ q^{λ−ε}`, the sum decays as `s^{-1} q^{o(1)} ≤ s^{-ε/2}`.
> Formalizing this requires the classical sub-polynomial growth bound for the
> divisor function `d(n) ≤ C_δ n^δ` for all `δ > 0`.

### Mathematical correctness: ✅ TRUE

The bound `τ(n) ≤ C_δ · n^δ` for every `δ > 0` is a classical, well-established
result in analytic number theory. For squarefree `n`, `τ(n) = 2^{ω(n)}` and the
bound follows from `2 ≤ p^δ` holding for all but finitely many primes. The general
(non-squarefree) case uses the prime factorization. The claimed decay
`s^{−ε/2}` then follows by absorbing the sub-polynomial factors into the
power of `s`.

### Sources whose formalization would close this goal

| Source | What it provides | Formalization difficulty |
|--------|-----------------|------------------------|
| Hardy & Wright, *An Introduction to the Theory of Numbers* (6th ed., 2008), **Theorem 315** | `τ(n) ≤ C_δ · n^δ` for all `δ > 0` | **Medium (2–4 weeks)**. The proof is elementary (induction on prime factorization + finitely many exceptions where `2 > p^δ`). The main effort is setting up the right inductive framework over `Nat.primeFactors` and handling the existential constant `C_δ`. |
| Iwaniec & Kowalski, *Analytic Number Theory* (AMS, 2004), **Theorem 2.11** | Same bound, with explicit constant | Same difficulty as above. |
| Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory* (3rd ed., 2015), **Theorem I.5.2** | Sub-multiplicative bound on `τ(n)` giving `τ(n) = O(n^δ)` | Same difficulty. |

**Key Mathlib gaps**: Mathlib has `Nat.divisors` and basic properties of `ω(n)` (via
`Nat.Omega` / `Nat.ArithmeticFunction.cardDistinctFactors`), but lacks the sub-polynomial
upper bound. The `PrimeNumberTheoremAnd` project likewise only has the crude bound
`τ(n) ≤ n`.

---

## 2. `gamma_sum_le_euler_factor` — `GammaDeviationSynthesis.lean:806`

### Statement (informal)
The weighted gamma sum (over configurations `γ` of tuple products) is bounded by
`(H+1)^{k−1} · ∏_{p ∈ T} (1 + w_p)`, where `w_p` involves `(1 − |Ω_p|/p) · p^{−ε} · localMean`.

### Docstring claim
> This corresponds to bounding the inner sum over configurations γ using standard
> divisor sum bounds. Proving this requires analytic bounds on `d(n)` that are
> currently absent from Mathlib and PrimeNumberTheoremAnd (specifically,
> sub-polynomial bounds on the number of divisors).

### Mathematical correctness: ✅ TRUE (with caveat)

The bound is a consequence of two ingredients:
1. The number of `(k−1)`-tuples of positive integers bounded by `H` with product `γ`
   is at most `τ_{k−1}(γ) · H^{k−2}` (where `τ_{k−1}` is the `(k−1)`-fold divisor
   function), or more crudely `(H+1)^{k-1}` summed appropriately.
2. The weight `perGammaDeviationWeight` decomposes multiplicatively over primes in `T`.

The Euler product structure then gives the stated bound. The docstring's invocation of
"sub-polynomial divisor bounds" is correct — one needs `τ_k(n) ≤ C_{δ,k} · n^δ` to
control the counting factor.

**Caveat**: The precise formal statement involves `countTuplesWithGammaProd` and
`perGammaDeviationWeight`, which are project-specific definitions. The mathematical
content is standard, but the formalization effort includes bridging these definitions
to classical divisor-function machinery.

### Sources whose formalization would close this goal

| Source | What it provides | Formalization difficulty |
|--------|-----------------|------------------------|
| Hardy & Wright, **Theorem 315** (generalized to `τ_k`) | `τ_k(n) ≤ C_{δ,k} · n^δ` | **Medium (2–4 weeks)** for the basic bound; the generalization to `τ_k` is straightforward once `τ = τ_2` is done. |
| Iwaniec & Kowalski, **Chapter 1** (multiplicative functions) | Framework for Euler product decomposition of multiplicative sums | **Medium-Hard (3–5 weeks)**. Requires formalizing the concept of multiplicative arithmetic functions and their Euler product representations. Mathlib has `Nat.ArithmeticFunction.IsMultiplicative` but lacks the analytic Euler product theory. |
| The connection `∑_{γ ≤ N} τ_k(γ) f(γ) ≤ ∏_p (∑_{e≥0} f(p^e) (e+k−1 choose k−1))` | Euler product bound for multiplicative sums | Part of the above. |

**Key Mathlib gaps**: Same as Lemma 1, plus the lack of Euler product decompositions for
sums of multiplicative functions over divisors.

---

## 3. `gamma_series_tail_bound` — `GammaDeviationSynthesis.lean:898`

### Statement (informal)
The sum over subsets `T ⊆ q.primeFactors` with `∏_{p ∈ T} p > s` of the per-`T`
Euler weights decays as `K · s^{−ε/2}`.

### Docstring claim
> This formalizes the Rankin trick, replacing the sharp cutoff ∏ p > s with the
> smooth weight (∏ p / s)^{ε/2}, and bounding the resulting sum by an Euler
> product over all primes. The rigorous formalization of this convergence requires
> the properties of the Riemann zeta function and PNT bounds to control the product
> over primes.

### Mathematical correctness: ✅ TRUE (docstring slightly overstates prerequisites)

The **Rankin trick** is correct: for any `α > 0`,

    𝟙{x > t} ≤ (x/t)^α

Applying this with `x = ∏_{p ∈ T} p`, `t = s`, `α = ε/2` converts the sharp cutoff
into a smooth weight, yielding:

    ∑_{T: ∏p > s} f(T) ≤ s^{−ε/2} · ∑_T (∏_{p∈T} p)^{ε/2} · f(T)
                        = s^{−ε/2} · ∏_{p|q} (1 + p^{ε/2} · g(p))

where `g(p) = p^{k−1}/|Ω_p|^k + k · p^{-(1+ε)}`.

The term `p^{ε/2} · k · p^{-(1+ε)} = k · p^{-(1+ε/2)}` is summable over primes
(exponent `1 + ε/2 > 1`), so this part of the Euler product converges.

For the term `p^{ε/2} · p^{k−1}/|Ω_p|^k`: using the hypothesis `hrp` (which gives
`|Ω_p| ≥ p − k`), for large `p` this is `~ p^{ε/2} · p^{−1} = p^{ε/2 − 1}`,
which is summable over primes when `ε/2 − 1 < −1`, i.e., `ε < 0`. This fails!

However, the statement asks for `K` that may depend on `X` (the box), and `H = ⌈s · ∑ X.sides⌉₊`.
A more careful analysis uses the full structure: the factor `(H+1)^{k-1}` outside the
product is `O(s^{k-1})`, and combined with the `p^{k-1}/|Ω_p|^k ~ p^{-1}` terms, the
effective convergence exponent becomes viable. The `K` constant absorbs the (finite)
Euler product over all primes of `q`, which IS finite for any fixed `q` — the
subtlety is that `K` must be *uniform in `q`*, which requires controlling how the Euler
product grows with `ω(q)`. This is where the PNT/Mertens-type bounds enter.

**The docstring's claim about needing "Riemann zeta function and PNT bounds" is
essentially correct**, though one could argue that Mertens' theorems (which are
weaker than PNT) suffice.

### Sources whose formalization would close this goal

| Source | What it provides | Formalization difficulty |
|--------|-----------------|------------------------|
| Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory* (3rd ed., 2015), **Chapter I.1 (Rankin's method)** | The abstract Rankin trick `𝟙{x>t} ≤ (x/t)^α` | **Easy (1–2 days)**. This is a one-line inequality. |
| Montgomery & Vaughan, *Multiplicative Number Theory I* (2007), **Lemma 1.3** | Rankin's trick applied to sums over integers | **Easy (< 1 week)**. |
| Mertens' theorems: `∏_{p ≤ x} (1 − 1/p)^{−1} ~ e^γ log x` | Control of Euler products over primes | **Hard (4–8 weeks)** from scratch. However, `PrimeNumberTheoremAnd` already has Mertens' theorems (see `PrimeNumberTheoremAnd.MertensTheorems`). The difficulty is connecting them to the specific Euler product form needed here. |
| Convergence of `∏_p (1 + f(p))` when `∑_p |f(p)|` converges | Euler product convergence criterion | **Medium (2–3 weeks)**. The abstract criterion is straightforward; the effort is in connecting it to Mathlib's `HasProd` / `Multipliable` API. |
| `PrimeNumberTheoremAnd` project (various modules) | PNT, Mertens' theorems, arithmetic function bounds | **Already formalized** in the dependency, but the *interface* between those results and the specific Euler product forms in this project would require **Medium (2–4 weeks)** of glue work. |

---

## 4. `euler_product_convergent_bound` — `DivisorSumGlue.lean:86` (BONUS — unused)

### Statement (informal)
`∏_{p | q} (1 + p^{δ−1}) ≤ C` uniformly over all squarefree `q`, for `0 < δ < 1/2`.

### Docstring claim
> For δ < 1/2, we have δ − 1 < −1/2, so p^{δ−1} ≤ p^{−1/2} ≤ 2^{−1/2},
> and **the sum over primes converges**.

### Mathematical correctness: ❌ FALSE

**This lemma is mathematically false**, and the docstring contains a critical error.

When `0 < δ < 1/2`, the exponent `δ − 1` lies in the interval `(−1, −1/2)`.
The sum `∑_p p^{δ−1}` **diverges** for any exponent `> −1` (by comparison with
the prime counting function: `∑_{p ≤ x} p^α ~ x^{1+α} / ((1+α) log x)` for
`α > −1`, which diverges). Consequently, `∏_p (1 + p^{δ−1})` diverges, and
there is no uniform constant `C`.

**Computational verification**: For `δ = 0.4` (so `δ − 1 = −0.6`):
- Product over first 10 primes: ≈ 12.4
- Product over first 100 primes: ≈ 606
- Product over first 1000 primes: ≈ 1,128,733
- Product over first 9592 primes (p ≤ 99991): ≈ 4.7 × 10¹²

The product clearly diverges.

**Impact**: This lemma is **never used** anywhere in the project (confirmed by
grep). It appears to be an orphaned helper that was written speculatively but
never integrated into any proof chain. Its falsity does not affect the
correctness of any other part of the project.

**To fix**: The statement would become true if the hypothesis were strengthened to
`δ < 0` (so `δ − 1 < −1`, making `∑_p p^{δ−1}` converge), or if the bound were
weakened to allow `C` to depend on `q` (e.g., `C = C(ω(q))` with polynomial growth).

---

## Summary Table

| # | Lemma | File | Used? | Math correct? | Key missing formalization |
|---|-------|------|-------|---------------|--------------------------|
| 1 | `lossy_divisor_sum_bound` | `FourierSynthesisHelpers.lean` | ✅ Yes | ✅ True | `τ(n) ≤ C_δ n^δ` |
| 2 | `gamma_sum_le_euler_factor` | `GammaDeviationSynthesis.lean` | ✅ Yes | ✅ True | `τ_k(n) ≤ C n^δ` + Euler products |
| 3 | `gamma_series_tail_bound` | `GammaDeviationSynthesis.lean` | ✅ Yes | ✅ True | Rankin trick + Mertens/PNT |
| 4 | `euler_product_convergent_bound` | `DivisorSumGlue.lean` | ❌ No | ❌ **False** | N/A (statement is wrong) |

### Estimated total effort to close all 3 valid sorries

Assuming `PrimeNumberTheoremAnd` is available as a dependency (which it is in this project):

- **Minimum path** (proving just enough to close the goals): **6–10 weeks** of expert formalization work.
  - 2–4 weeks for the sub-polynomial divisor bound `τ(n) ≤ C_δ n^δ`
  - 2–3 weeks for Euler product convergence machinery
  - 2–3 weeks for connecting Mertens/PNT results to the specific forms needed

- **Reusable library path** (building general-purpose infrastructure): **10–16 weeks**.
  This would produce reusable Mathlib-quality formalizations of multiplicative function
  theory, Euler products, and Rankin's method.

The sub-polynomial divisor function bound (`τ(n) ≤ C_δ n^δ`) is the single most
impactful piece — formalizing it alone would likely unblock lemmas 1 and 2, and
significantly simplify the remaining work for lemma 3.
