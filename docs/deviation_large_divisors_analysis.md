# Analysis of the `deviation_large_divisors` sorry

## Status
The sorry on `deviation_large_divisors` (MobiusSynthesis.lean, line 461) **cannot be closed** with the current proof infrastructure. The obstacle is mathematical, not a tooling limitation.

## Mathematical Analysis

### What `deviation_large_divisors` claims
For every squarefree q:
```
∑_{T: ∏_T p > s} |∑_h f(h,T)| ≤ K₂ · s^{−ε/2}
```
where s = q/|Ω_q| and the sum is over subsets T ⊆ primeFactors(q) with prime product > s.

### Why the existing proof strategy fails

The codebase contains two key tools:
1. **`large_divisor_per_T_bound`**: Bounds each |∑_h f(h,T)| individually using the triangle inequality (pushing |·| inside ∑_h). For primes > B_max, it connects to `combinedEulerWeight`; for primes ≤ B_max, it gives a crude bound of `p · μ_p⁻¹`.

2. **`large_divisor_series_bound`** (= `tail_sum_decay`): Bounds ∑_T ∏_T combinedEulerWeight ≤ K · s^{−ε/2} via the Rankin trick.

The gap: For subsets T containing primes p ≤ B_max ("small" primes), `large_divisor_per_T_bound` gives the factor `p · μ_p⁻¹ = p^k / |Ω_p|^k`, which is much larger than `combinedEulerWeight(p)`. This prevents connecting the per-T bound to the `combinedEulerWeight` tail sum.

Specifically, summing the per-T bounds over all T with ∏_T p > s gives:
```
∑_T [bound] ≤ C · ∑_T ∏_{T_large} cEW_p · ∏_{T_small} (p^k/|Ω_p|^k)
```
The factor ∏_{T_small} (p^k/|Ω_p|^k) grows polynomially in each p (for k ≥ 3), and the exponentially many T_small subsets make the sum **diverge**. No Rankin trick argument can rescue this.

### Why `gamma_weighted_series_bound` is false

The intermediate lemma `gamma_weighted_series_bound` (GammaDeviationSynthesis.lean:845) is **mathematically false**. Numerical evidence: for q = primorial(29) and q = primorial(97), the singleton contributions to the LHS are ~27 and ~51 (respectively), while s^{−ε/2} ≈ 0.99 in both cases. The ratio grows without bound as q grows.

The root cause: `gamma_weighted_series_bound` pushes |·| inside ∑_h via `deviation_sum_le_gamma_sum`, losing cancellation. The resulting bound has H^{k−1} terms, each contributing at most p (via `weight_le_prod_T`), for a total of H^{k−1} · ∏_T p. After combining with the prefactor μ_p⁻¹, the sum over T grows like (log q)^C, overwhelming any s^{−ε/2} decay.

### Why `deviation_large_divisors` IS true (but needs a different proof)

Numerical computation confirms the statement is true. For k=3, Ω_p = {1,...,p−1}:
- primorial(29): actual LHS ≈ 0.108, s^{−0.005} ≈ 0.991
- primorial(97): actual LHS ≈ 0.062, s^{−0.005} ≈ 0.989

The LHS *decreases* as q grows, consistent with a uniform bound K₂ · s^{−ε/2}.

The key: the sum ∑_h ∏_T(N_p − μ_p) has **cancellation** that the triangle inequality destroys. For example, with Ω_p = {1,...,p−1} and p > H, every tuple h gives the same deviation N_p − μ_p = −1/p, so ∑_h(N_p−μ_p) = −H^{k−1}/p — much smaller than ∑_h|N_p−μ_p| = H^{k−1}/p.

### The correct proof approach (GK08 §3.1)

Granville–Kurlberg prove the analogous bound using the **second moment method**:
1. Bound E_h[|∏_T(N_p−μ_p)|²] using gamma-structure counting
2. Apply Cauchy–Schwarz or Markov to convert the variance bound to a pointwise bound
3. The variance bound naturally exploits CRT independence and collision counting

This approach avoids the triangle inequality entirely, preserving the cancellation in ∑_h.

### What infrastructure is needed

To close this sorry, one would need to build:
1. A **CRT equidistribution** lemma: the distribution of h mod ∏_T p over a box is approximately uniform, with lattice point error O(H^{k−2}/P_T^{k−2}).
2. A **mean-zero product** lemma: since ∑_{r mod p} (N_p(r)−μ_p) = 0 for each p, the product ∑_r ∏_T f_p(r_p) = 0 by CRT independence (the leading term vanishes).
3. An **error term** analysis that bounds the residual by C · H^{k−2} · P_T · ∏_T(cEW_p · μ_p), which sums to O(s^{−ε/2}) via the Rankin trick.

This is a substantial piece of analytic number theory (the core of GK08 §3) that would require 500–1000+ lines of new Lean code.

## Import added
The import `import PoissonViaCRT.GammaRangeSum` was added to `MobiusSynthesis.lean` as requested, making the gamma-structure counting machinery available. This import compiles successfully but is not sufficient to close the sorry.

## Remaining sorries in the project
1. `MobiusSynthesis.lean:461` — `deviation_large_divisors` (this analysis)
2. `GammaDeviationSynthesis.lean:845` — `gamma_weighted_series_bound` (**false** as stated)
3. `SmallDivisorHelpers.lean:1133` — `small_divisor_series_bound`
