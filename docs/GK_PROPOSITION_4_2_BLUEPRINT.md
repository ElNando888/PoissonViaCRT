# Formalizing Proposition 4.2 of Granville-Kurlberg (2008)

## 1. Background and Mathematical Correction
The previous formalization attempt failed because it relied on the informal sketch presented in Section 3.2 of the paper. That sketch applied a uniform Rankin trick to the collision constraint $\prod_{p\in T} p > s$, which introduced a factor of $\gamma^{\varepsilon/2}$ and caused the resulting series to mathematically diverge. 

The actual, rigorous proof in the paper avoids this divergence by splitting the sum over $d$ (which corresponds to our $\gamma$, the product of collision primes) into two distinct regimes: "Small $d$" and "Large $d$". By applying different Rankin weights to the different regimes, the authors ensure that the Euler products converge strictly.

This blueprint outlines the architecture to formalize **Proposition 4.2** precisely as stated in the text.

## 2. Core Theorem Statement

We will formalize Proposition 4.2 as a bound on the sum over $T$ of the error term:

```lean
lemma gk08_proposition_4_2 (k : ℕ) (hk : 2 ≤ k)
    (Ω : ∀ p, Finset (ZMod p)) (q : ℕ) (hq : Squarefree q)
    (R : ℝ) (hR : 0 ≤ R ∧ R ≤ 1) 
    (α_0 α_1 β_1 : ℝ) (α β : ℕ → ℝ) :
    ...
```

The error is bounded by three terms corresponding to the three lines of the Proposition:
1. **Line 1 (Small $d$, uniform bound):** $s_q^{\alpha_0 R - 1} \prod_{p|q} \Big(1 + O\big(p^{1-\alpha_0}(A_{p,k} + \frac{s_p-1}{p})\big)\Big)$
2. **Line 2 (Large $d$, tail bound):** $s_q^{\alpha_1 - \beta_1 R} \prod_{p|q} \Big(1 + O\big(p^{\beta_1}(A_{p,k} + \frac{s_p-1}{p^{1+\alpha_1}})\big)\Big)$
3. **Line 3 (Tuple counting sum):** $\sum_{\tau} s_q^{v(\tau) + \alpha(\tau)w(\tau) - (k-1) - \beta(\tau)R} \prod_{p|q} \Big(1 + p^{\beta(\tau)}O\big(A_{p,k} + \frac{s_p-1}{p^{\alpha(\tau)}}\big)\Big)$

## 3. The Implementation Steps

### Step A: The Divisor Splitting
Instead of using a generic Rankin sum swap over the entire set $T$, we must explicitly split the sum over divisors $d$ (our $\gamma$) at the boundary $d \le s_q^R$ and $d > s_q^R$. 
We will introduce a lemma `split_divisor_sum` that partitions `Finset.Icc 1 H` into these two regimes.

### Step B: The Rankin Tricks
The Rankin trick must **only** be applied to the "Large $d$" and the tail of the tuple counting regimes.
- For $d > s_q^R$, we use the inequality $1 \le (d / s_q^R)^{\beta_1}$.
- We **do not** apply the Rankin trick to $d$ when $d \le s_q^R$.

### Step C: The Euler Product Convergence
Because we apply the Rankin tricks carefully, the resulting per-prime factors will always look like:
$$1 + O(p^{\beta}) A_{p,k} + O(p^{\beta-\alpha}) (s_p - 1)$$
Since $A_{p,k} \ll p^{-1-\varepsilon}$ and $(s_p - 1) \approx p^{-1}$ in the worst-case ($\Omega_p = \text{univ}$), the exponent of $p$ is strictly less than $-1$, guaranteeing that the Euler product converges to a constant independent of $q$.

### Step D: Regime Balance and $\lambda_k$
The final step will be to select the parameters $R, \alpha_0, \alpha_1, \beta_1, \alpha(\tau), \beta(\tau)$ exactly as done in **Lemma 6** of the paper. This specific choice of parameters is what forces the $s_q$ exponents in all three terms to be strictly negative (bounded by $s_q^{-\varepsilon}$), completing the proof.
