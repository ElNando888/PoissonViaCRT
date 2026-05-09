# Fourier ANOVA Blueprint

## Overview

This document outlines the mathematical and Lean 4 structural path to proving the uniform
deviation bound for Proposition 3.6 of Granville–Kurlberg (arXiv:math/0412135v2) using
Fourier analysis on the finite abelian group
$G = (\mathbb{Z}/q\mathbb{Z})^{k-1}$.

The strategy replaces the combinatorial Gamma-structure approach with a clean
**Fourier ANOVA** (Analysis of Variance) decomposition: we expand the deviation
$N_k(h, \Omega_q) - \mu$ in terms of discrete Fourier coefficients, factor them
multiplicatively via CRT, and bound the resulting sum using exponential-sum
estimates from the `WellDistributed` hypothesis.

---

## 1. DFT Definition

### Mathematics

Let $G = (\mathbb{Z}/q\mathbb{Z})^m$ where $m = k - 1$. The **dual group**
$\widehat{G}$ is isomorphic to $G$ itself. A character $\chi \in \widehat{G}$
is indexed by a frequency vector $\xi \in G$ and acts as

$$\chi_\xi(x) = \exp\!\Bigl(\frac{2\pi i}{q}\,\langle \xi, x \rangle\Bigr)
  = \prod_{j=1}^{m} \exp\!\Bigl(\frac{2\pi i\, \xi_j x_j}{q}\Bigr),$$

where $\langle \xi, x \rangle = \sum_j \xi_j x_j$ is evaluated in $\mathbb{Z}/q\mathbb{Z}$
and then lifted to $\mathbb{Z}$.

The **discrete Fourier transform** of $f : G \to \mathbb{C}$ is

$$\widehat{f}(\xi) = \frac{1}{|G|} \sum_{x \in G} f(x)\,\overline{\chi_\xi(x)}
  = \frac{1}{q^m} \sum_{x \in G} f(x)\,
    \exp\!\Bigl(-\frac{2\pi i}{q}\,\langle \xi, x \rangle\Bigr).$$

### Lean 4 Structure

```
noncomputable def rootOfUnity (q : ℕ) [NeZero q] (a : ZMod q) : ℂ
noncomputable def dft (q m : ℕ) [NeZero q]
    (f : (Fin m → ZMod q) → ℂ) (ξ : Fin m → ZMod q) : ℂ
```

Key properties to formalize:
- `dft_zero`: $\widehat{f}(0) = \frac{1}{q^m}\sum_{x} f(x)$ (the mean of $f$).
- `dft_inversion`: $f(x) = \sum_{\xi} \widehat{f}(\xi)\,\chi_\xi(x)$ (Fourier inversion).
- Orthogonality of characters: $\sum_{x \in G} \chi_\xi(x)\,\overline{\chi_\eta(x)} = |G|\,\delta_{\xi,\eta}$.

---

## 2. Parseval's / Plancherel's Identity

### Mathematics

The Plancherel identity on $G$ states:

$$\frac{1}{|G|}\sum_{x \in G} |f(x)|^2 = \sum_{\xi \in \widehat{G}} |\widehat{f}(\xi)|^2.$$

More generally, for two functions $f, g : G \to \mathbb{C}$:

$$\frac{1}{|G|}\sum_{x \in G} f(x)\,\overline{g(x)}
  = \sum_{\xi \in \widehat{G}} \widehat{f}(\xi)\,\overline{\widehat{g}(\xi)}.$$

**Application.** Let $f = N_k(\cdot, \Omega_q) - \mu$ be the deviation function and let
$g = \mathbf{1}_S$ be the indicator of the scaled box $S = s_q \cdot X \cap \mathbb{Z}^{k-1}$.
Then the total deviation over the box is

$$\sum_{h \in S} \bigl(N_k(h) - \mu\bigr)
  = |G| \sum_{\xi \neq 0} \widehat{f}(\xi)\,\overline{\widehat{g}(\xi)},$$

where the $\xi = 0$ term vanishes if $\widehat{f}(0) = 0$ (which it does, since the mean
deviation is zero).

### Lean 4 Structure

```
theorem plancherel_identity (q m : ℕ) [NeZero q]
    (f g : (Fin m → ZMod q) → ℂ) :
    (1 / (q : ℂ) ^ m) * ∑ x : Fin m → ZMod q, f x * starRingEnd ℂ (g x) =
    ∑ ξ : Fin m → ZMod q, dft q m f ξ * starRingEnd ℂ (dft q m g ξ)
```

---

## 3. CRT Factorization

### Mathematics

For squarefree $q = \prod_{p | q} p$, the CRT isomorphism

$$(\mathbb{Z}/q\mathbb{Z})^m \cong \prod_{p | q} (\mathbb{Z}/p\mathbb{Z})^m$$

decomposes both the counting function and the characters. Writing
$\xi = (\xi_p)_{p | q}$ with $\xi_p \in (\mathbb{Z}/p\mathbb{Z})^m$:

$$\widehat{f}(\xi) = \prod_{p | q} \widehat{f_p}(\xi_p),$$

where $f_p(x_p) = N_k(x_p, \Omega_p)$ is the local counting function. This product
factorization is the Fourier-space manifestation of the CRT multiplicativity already
proved in `CRTMultiplicativity.lean`.

### Lean 4 Structure

The key theorem to state:

```
theorem dft_crt_factorization (q : ℕ) [NeZero q] (hq : Squarefree q)
    (Ω : ∀ p : ℕ, Finset (ZMod p)) (k : ℕ)
    (ξ : Fin (k - 1) → ZMod q) :
    dft q (k - 1) (fun h => (tupleCount (crtSubset q Ω) (Fin.cons 0 h) : ℂ)) ξ =
    ∏ p ∈ q.primeFactors,
      dft p (k - 1) (fun h_p => (tupleCount (Ω p) (Fin.cons 0 h_p) : ℂ))
        (fun j => ZMod.castHom (Nat.dvd_of_mem_primeFactors ‹_›) (ZMod p) (ξ j))
```

This will rely on `counting_function_multiplicative` and the character factorization
through CRT.

---

## 4. Primitive Character Sieve

### Mathematics

Define the **deviation function** at prime $p$:

$$\operatorname{dev}_p(x_p) = N_k(x_p, \Omega_p) - \mu_p,$$

where $\mu_p = |\Omega_p|^k / p^{k-1}$. Taking the Fourier transform:

$$\widehat{\operatorname{dev}}_p(\xi_p)
  = \widehat{f_p}(\xi_p) - \mu_p \cdot \delta_{\xi_p, 0}.$$

In particular, $\widehat{\operatorname{dev}}_p(0) = 0$ since the mean deviation is zero:

$$\sum_{x_p \in (\mathbb{Z}/p\mathbb{Z})^m} \operatorname{dev}_p(x_p) = 0.$$

This means the Fourier expansion of the global deviation restricts to
**non-trivial frequencies** $\xi \neq 0$, i.e., frequencies where at least one
local component $\xi_p \neq 0$. This "sieve" eliminates the dominant term and
leaves only the oscillatory contributions.

### Lean 4 Structure

```
noncomputable def localDeviation (k : ℕ) (Ω : ∀ p : ℕ, Finset (ZMod p))
    (p : ℕ) [NeZero p] (h : Fin (k - 1) → ZMod p) : ℂ

theorem localDeviation_sum_zero (k : ℕ) (p : ℕ) [NeZero p]
    (Ω : ∀ p : ℕ, Finset (ZMod p)) :
    ∑ h : Fin (k - 1) → ZMod p, localDeviation k Ω p h = 0

theorem localDeviation_dft_zero (k : ℕ) (p : ℕ) [NeZero p]
    (Ω : ∀ p : ℕ, Finset (ZMod p)) :
    dft p (k - 1) (localDeviation k Ω p) 0 = 0
```

---

## 5. Exponential Sum Bounds

### Mathematics

The `WellDistributed` hypothesis (Hypothesis (1) of Theorem 1.1) gives:

$$|N_k(h, \Omega_p) - \mu_p| \leq (1 - r_p)\, p^{-\varepsilon}\, \mu_p$$

for injective $h$, where $r_p = |\Omega_p| / p$. This translates to a pointwise bound
on $|\operatorname{dev}_p(x_p)|$.

By Parseval, the $L^2$-norm of the Fourier coefficients is controlled:

$$\sum_{\xi_p \neq 0} |\widehat{\operatorname{dev}}_p(\xi_p)|^2
  = \frac{1}{p^m} \sum_{x_p} |\operatorname{dev}_p(x_p)|^2
  \leq (1 - r_p)^2\, p^{-2\varepsilon}\, \mu_p^2.$$

For the $L^1$-type bound needed in the synthesis, we define the **local weight**:

$$W_p = \frac{1}{p^m} \sum_{h_p \in (\mathbb{Z}/p\mathbb{Z})^m}
  |\operatorname{dev}_p(h_p)|$$

and show $W_p \leq (1 - r_p)\, p^{-\varepsilon}\, \mu_p$ using `WellDistributed`.

### Lean 4 Structure

```
theorem local_deviation_fourier_bound (ε : ℝ) (hε : 0 < ε)
    (p : ℕ) [hp : Fact p.Prime] (Ω : ∀ p : ℕ, Finset (ZMod p))
    (k : ℕ) (hk : 2 ≤ k)
    (hwd : WellDistributed ε p (Ω p) k) :
    ∑ ξ : Fin (k - 1) → ZMod p,
      Complex.abs (dft p (k - 1) (localDeviation k Ω p) ξ) ≤
    (1 - (Ω p).card / (p : ℝ)) * (p : ℝ) ^ (-ε) *
      ((Ω p).card : ℝ) ^ k / (p : ℝ) ^ (k - 1)
```

---

## 6. Box Transform Decay

### Mathematics

Let $I_S : G \to \mathbb{C}$ be the indicator function of the scaled box
$S = s_q \cdot X \cap \mathbb{Z}^{k-1}$ (mod $q$). The Fourier transform of
$I_S$ is a product of geometric sums:

$$\widehat{I}_S(\xi) = \prod_{j=1}^{m}
  \frac{1}{q}\sum_{n_j = 1}^{\lfloor s_q b_j \rfloor}
  \exp\!\Bigl(-\frac{2\pi i\, \xi_j n_j}{q}\Bigr).$$

Each factor is a truncated geometric series, and for $\xi_j \neq 0$:

$$\Bigl|\frac{1}{q}\sum_{n=1}^{N} e^{-2\pi i \xi_j n/q}\Bigr|
  \leq \frac{1}{q\,|\!\sin(\pi \xi_j/q)|} \leq \frac{1}{2\|\xi_j/q\|},$$

where $\|x\|$ denotes the distance of $x$ to the nearest integer.

The $L^1$-norm of the box transform satisfies:

$$\sum_{\xi \in G} |\widehat{I}_S(\xi)| \ll (\log q)^m.$$

This follows from the classical estimate
$\sum_{1 \leq n \leq q/2} 1/n \leq 1 + \log(q/2) \ll \log q$
applied to each coordinate.

### Lean 4 Structure

```
theorem box_fourier_l1_bound (q : ℕ) [NeZero q] (k : ℕ) (hk : 2 ≤ k)
    (B : Box (k - 1)) (s : ℝ) (hs : 0 < s) :
    ∑ ξ : Fin (k - 1) → ZMod q,
      Complex.abs (dft q (k - 1) (boxIndicator q (k - 1) B s) ξ) ≤
    C_box * (Real.log q) ^ (k - 1)
```

where `C_box` is a constant depending only on the box $X$.

---

## 7. Synthesis: The Final Deviation Bound

### Mathematics

Combining the ingredients:

1. Expand the total deviation over the box using Plancherel (§2).
2. Factor the Fourier coefficients via CRT (§3).
3. Apply the primitive character sieve to restrict to $\xi \neq 0$ (§4).
4. Bound the deviation coefficients using `WellDistributed` (§5).
5. Bound the box transform using the $L^1$-norm estimate (§6).

The final result:

$$\Bigl|\sum_{h \in S} \bigl(N_k(h) - \mu\bigr)\Bigr|
  \leq \bigl(\text{box $L^1$ bound}\bigr)
      \cdot \prod_{p | q} \bigl(1 + W_p\bigr)
  \ll (\log q)^m \cdot \prod_{p | q}
      \bigl(1 + (1-r_p)\, p^{-\varepsilon}\bigr).$$

When $\sum_p (1-r_p)\, p^{-\varepsilon} < \infty$ (which follows from the density
assumptions), the Euler product converges and provides a $q$-independent bound.

### Lean 4 Structure

This connects to the existing `deviation_expression_uniform_bound` in
`MobiusSynthesis.lean`. The Fourier ANOVA approach replaces the combinatorial
Gamma-structure route with a cleaner analytic argument.

---

## 8. Dependency Graph

```
FourierANOVA.lean
├── imports Defs.lean           (tupleCount, crtSubset, WellDistributed, Box)
├── imports CRTMultiplicativity.lean  (counting_function_multiplicative)
├── imports DeviationBoundHelper.lean (localMean, localCount)
└── imports Mathlib              (Complex, Finset, BigOperators)
```

The file is self-contained in the sense that it does not depend on the
Gamma-structure machinery (`Combinatorics.lean`, `GammaRangeSum.lean`, etc.),
providing a parallel path to the same uniform bound.

---

## 9. Formalization Roadmap

| Step | Lean Declaration | Difficulty | Dependencies |
|------|-----------------|------------|--------------|
| 1 | `rootOfUnity` | Easy | Mathlib `Complex.exp` |
| 2 | `dft` | Easy | `rootOfUnity` |
| 3 | `character_orthogonality` | Medium | Geometric series |
| 4 | `dft_inversion` | Medium | `character_orthogonality` |
| 5 | `plancherel_identity` | Medium | `character_orthogonality` |
| 6 | `localDeviation` | Easy | `localCount`, `localMean` |
| 7 | `localDeviation_dft_zero` | Easy | `dft`, sum of deviations = 0 |
| 8 | `dft_crt_factorization` | Hard | CRT iso + character factorization |
| 9 | `local_deviation_fourier_bound` | Medium | `WellDistributed` + Parseval |
| 10 | `boxIndicator` | Easy | `Box`, `inScaledBox` |
| 11 | `box_fourier_l1_bound` | Hard | Geometric series + harmonic sum |
| 12 | `deviation_fourier_synthesis` | Hard | Steps 5–11 |
