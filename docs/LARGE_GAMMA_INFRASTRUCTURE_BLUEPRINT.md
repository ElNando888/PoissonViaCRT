# Implementation Blueprint: Large-γ Infrastructure (GK08 §4)

## 1. Goal Description

Our current architecture for `deviation_large_divisors` is mathematically blocked by an explosion in the Euler product. Specifically, applying the "mean-collapse" algebra (which is required to normalize the box volume $H^{k-1}$ and extract the $s^{-(k-1)}$ factor) transforms the weight of collision primes in $\gamma$ from $p$ to $(p / |\Omega_p|)^k \approx k^k > 1$. 

Because our current `gamma_sum_le_euler_factor_small_gamma` uses the trivial bound $M_\gamma(H) \le H^{k-1}$, it provides no suppression for large $\gamma$. As a result, the Euler product over $T$ accumulates these $k^k$ factors and diverges like $k^{k|T|}$, entirely destroying the $s^{-\varepsilon/2}$ Rankin decay.

To tame this explosion, we must implement the full Granville-Kurlberg Section 4 tuple-counting infrastructure. This machinery partitions the $\gamma$-sum into regimes indexed by tuple graphs $\tau$, applying sharp counting bounds ($M_\gamma(H) \ll H^{c} \gamma^{-\alpha}$) to supply the negative powers of $\gamma$ needed to neutralize the $k^k$ growth.

## 2. User Review Required

> [!WARNING]
> This is a substantial formalization effort. It will replace the simplistic `gk08_prop42_large_divisors` proof with a segmented sum over $\tau$-regimes (Line 3 of `gk08_proposition_4_2`). I am fully committed to this path, but want to ensure you agree with the structural decomposition before I begin coding.

## 3. Proposed Changes

### `PoissonViaCRT/GammaDeviationSynthesis.lean`

#### [NEW] `gamma_sum_le_euler_factor_large_gamma`
We will introduce a new "large-$\gamma$ engine" parallel to the existing small-$\gamma$ engine. 
- **Domain**: Bounding the sum over $\gamma \in (H^{w(\tau-1)}, H^{w(\tau)}]$.
- **Mechanism**: It will invoke `countTuplesWithGammaProd_large_gamma_sharp` to bound the tuple count by $C_\tau H^{n+1/2} / \gamma^{\alpha(\tau)}$.
- **Rankin Trick**: To extend the sum to all $\gamma \mid \prod T$ and decouple it into an Euler product, it will apply the Rankin trick weight $(\gamma / H^{w(\tau-1)})^{\beta(\tau)} \ge 1$.
- **Resulting Euler Factor**: The weight of a collision prime $p \mid \gamma$ will become $p \cdot p^{\beta(\tau) - \alpha(\tau)}$. By setting $\alpha(\tau) = 1$ (or close to it), this simplifies to $p^{\beta(\tau)}$, precisely matching the Euler factor required in Line 3 of `gk08_proposition_4_2`.

#### [MODIFY] `gk08_prop42_large_divisors`
We will rewrite this lemma entirely. Instead of bounding the whole $\gamma$ sum with the small-$\gamma$ engine, it will:
1. Split the sum over $\gamma \le H^{k(k-1)/2}$ into the small-$\gamma$ regime ($\gamma \le H^{w(0)}$) and the various large-$\gamma$ regimes ($\tau = 1, \dots, \tau_{max}$).
2. Apply `gamma_sum_le_euler_factor_small_gamma` to the first regime.
3. Apply `gamma_sum_le_euler_factor_large_gamma` to each $\tau$-regime.
4. Sum the resulting Euler products to exactly match the sum in Line 3 of `gk08_proposition_4_2`.

### `PoissonViaCRT/AnalyticInputs.lean` (or similar)

#### [MODIFY] `euler_product_converges`
We need to ensure that our analytic inputs can handle the convergence of these new $\tau$-parameterized Euler products. The product $\prod_p (1 + C p^{\beta(\tau)} (1 + A_p))$ converges provided $\beta(\tau) < -1$ (which follows from the specific choices of $\alpha, \beta$ in GK08 Lemma 6). We will ensure the bounds accommodate this.

## 4. Verification Plan

1. **Compilation**: Ensure `GammaDeviationSynthesis.lean` compiles with the new lemmas fully proved (no `sorry`s in the algebraic rearrangements).
2. **Integration**: Plug the new, corrected `gk08_prop42_large_divisors` into `deviation_large_divisors` in `MobiusSynthesis.lean`.
3. **Decay Check**: Verify that the mean-collapse algebra successfully leaves behind only the Rankin decay $s^{-\varepsilon/2}$ now that the $k^k$ growth has been neutralized by the $\tau$-graph suppression.
