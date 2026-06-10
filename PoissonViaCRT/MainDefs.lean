/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.ZMod.Defs
import Mathlib.Order.Interval.Finset.Defs

/-!
# Poisson Statistics via the Chinese Remainder Theorem — Definitions

Formalization of key definitions from "Poisson statistics via the Chinese remainder theorem"
by Andrew Granville and Pär Kurlberg (arXiv:math/0412135v2).

## Main Definitions

* `PoissonCRT.tupleCount`: The counting function `N_k(h, Ω)` for `k`-tuples.
* `PoissonCRT.crtSubset`: The CRT subset `Ω_q` constructed from local subsets `Ω_p`.
* `PoissonCRT.Box`: Boxes in `ℝ^{k-1}` used to define `k`-level correlations.
* `PoissonCRT.kCorrelation`: The `k`-level correlation `R_k(X, Ω_q)`.
* `PoissonCRT.WellDistributed`: The well-distributed hypothesis used Theorem 1.1.
* `PoissonCRT.lambdaExponent`: The critical exponent `λ_k` defined in §3.2.

## References

* [A. Granville, P. Kurlberg, *Poisson statistics via the Chinese remainder theorem*]
  [arXiv:math/0412135v2]
-/

open Finset BigOperators Classical

namespace PoissonCRT

/-! ### The counting function `N_k` -/

/-- The counting function for `k`-tuples mod `q` (Definition from §1).
Given `Ω ⊆ ℤ/qℤ` and offsets `h : Fin k → ℤ/qℤ`,
$$N_k(\mathbf{h}, \Omega) = \#\{ t \in \mathbb{Z}/q\mathbb{Z} :
  t + h_i \in \Omega \text{ for all } 0 \le i \le k-1 \}.$$
The paper convention is `h 0 = 0`, so that the condition includes `t ∈ Ω`. -/
@[expose]
public def tupleCount {q : ℕ} [NeZero q] (Ω : Finset (ZMod q)) (h : Fin k → ZMod q) : ℕ :=
  (univ.filter fun t : ZMod q => ∀ i, t + h i ∈ Ω).card

/-! ### The CRT subset -/

/-- The CRT subset construction (§1). Given a family of subsets `Ω p ⊆ ℤ/pℤ` for each prime `p`,
the CRT subset `Ω_q ⊆ ℤ/qℤ` for squarefree `q` consists of those `x` whose reduction
modulo `p` lies in `Ω p` for every prime factor `p` of `q`. -/
@[expose]
public noncomputable def crtSubset (q : ℕ) [NeZero q] (Ω : ∀ p : ℕ, Finset (ZMod p)) :
    Finset (ZMod q) :=
  univ.filter fun x =>
    ∀ p, ∀ hp : p ∈ q.primeFactors,
      ZMod.castHom (Nat.dvd_of_mem_primeFactors hp) (ZMod p) x ∈ Ω p

/-! ### Boxes in `ℝ^{k-1}` (§2)

A box `B(b₁, …, bₖ₋₁) ⊂ ℝ^{k-1}` is defined as:
$$B(b_1, \ldots, b_{k-1}) = \{ x \in \mathbb{R}^{k-1} :
  0 < x_i - x_{i-1} \le b_i, \, i = 1, \ldots, k-1 \}$$
where `x₀ = 0`. We represent a box by its side lengths. -/

/-- A box `B(b₁, …, bₖ₋₁) ⊂ ℝ^{k-1}` with positive side lengths. -/
public structure Box (k : ℕ) where
  /-- The side lengths `b₁, …, bₖ₋₁`. -/
  sides : Fin k → ℝ
  /-- All side lengths are positive. -/
  sides_pos : ∀ i, 0 < sides i

/-- The volume of a box `B(b₁, …, bₖ₋₁)` is `∏ᵢ bᵢ`. -/
@[expose]
public noncomputable def Box.volume {k : ℕ} (B : Box k) : ℝ :=
  ∏ i, B.sides i

/-- A lattice point `h ∈ ℤ^{k-1}` belongs to the scaled box `s · X` if
`0 < h_i - h_{i-1} ≤ s · b_i` for all `i`, where `h₀ = 0`. -/
@[expose]
public def inScaledBox {k : ℕ} (B : Box k) (s : ℝ) (v : Fin k → ℝ) (h : Fin k → ℤ) : Prop :=
  ∀ i : Fin k,
    let prev : ℝ := if (i : ℕ) = 0 then 0 else (h ⟨i - 1, by omega⟩ : ℝ) - v ⟨i - 1, by omega⟩
    (0 : ℝ) < (h i : ℝ) - v i - prev ∧ (h i : ℝ) - v i - prev ≤ s * B.sides i

/-! ### The `k`-level correlation `R_k` (§2)

$$R_k(X, \Omega_q) = \frac{1}{|\Omega_q|}
  \sum_{\mathbf{h} \in s_q X \cap \mathbb{Z}^{k-1}} N_k(\mathbf{h}, \Omega_q)$$

We define the correlation using a sum over integer tuples `h` satisfying box constraints.
-/

/-- The `k`-level correlation `R_k(X, Ω_q)` for a box `X` and subset `Ω ⊆ ℤ/qℤ` (§2).
`R_k(X, Ω_q) = (1/|Ω_q|) ∑_{h ∈ s_q X ∩ ℤ^{k-1}} N_{k+1}((0, h₁,…,hₖ), Ω_q)`

We express the correlation as a sum over integer tuples `h` lying in the scaled box `s_q · X`,
where `s_q = q / |Ω|` is the average spacing. The tuple count uses `Fin.cons 0 h` to
incorporate the implicit `h₀ = 0` from the paper's convention, so that `N_{k+1}` counts
`t ∈ Ω` with `t + hᵢ ∈ Ω` for all `i`. -/
@[expose]
public noncomputable def kCorrelation {q : ℕ} [NeZero q]
    (Ω : Finset (ZMod q)) (X : Box k) : ℝ :=
  let s := (q : ℝ) / Ω.card
  let bound := ⌈s * ∑ i, X.sides i⌉₊
  (1 / (Ω.card : ℝ)) *
    ∑ h ∈ (Fintype.piFinset fun _ : Fin k => Finset.Icc 1 (bound : ℤ)).filter
      (fun h => inScaledBox X s (fun _ => 0) h),
      (tupleCount Ω (Fin.cons (0 : ZMod q) fun i => (h i : ZMod q)) : ℝ)

/-! ### Hypothesis (1) from Theorem 1.1 -/

/-- **Hypothesis (1)** from Theorem 1.1: For each integer `k`, the `k`-tuple counting function
satisfies `N_k(h, Ω_p) = r_p^k · p · (1 + O_k((1-r_p) · p^{-ε}))` provided that
`0, h₁, …, h_{k-1}` are distinct mod `p`.

Formally: `|N_k(h, Ω_p) - |Ω_p|^k / p^{k-1}| ≤ C_k · (1 - |Ω_p|/p) · p^{-ε} ·
|Ω_p|^k / p^{k-1}` for all injective `h`. -/
@[expose]
public def WellDistributed (ε : ℝ) (p : ℕ) [Fact p.Prime] (Ω : Finset (ZMod p)) (k : ℕ) : Prop :=
  (∀ (h : Fin k → ZMod p), Function.Injective h →
    |(tupleCount Ω h : ℝ) - (Ω.card : ℝ) ^ k / (p : ℝ) ^ (k - 1)|
    ≤ (1 - Ω.card / p : ℝ) * (p : ℝ) ^ (-ε) * ((Ω.card : ℝ) ^ k / (p : ℝ) ^ (k - 1))) ∧
  (∑ r : Fin (k - 1) → ZMod p,
    |(tupleCount Ω (Fin.cons 0 r) : ℝ) - (Ω.card : ℝ) ^ k / (p : ℝ) ^ (k - 1)|
    ≤ (p : ℝ) ^ (k - 1) * (1 - Ω.card / p : ℝ) * (p : ℝ) ^ (-ε)
      * ((Ω.card : ℝ) ^ k / (p : ℝ) ^ (k - 1)))

/-- The critical exponent `λ_k = min_τ (k-1-v(τ))/w(τ)` from §3.2.
For `k ≥ 4`, `λ_k = 1/(k-1)`.-/
@[expose]
public noncomputable def lambdaExponent (k : ℕ) : ℝ :=
  if k ≤ 1 then 1
  else if k = 2 then (Real.sqrt 17 - 3) / 2
  else if k = 3 then 1 / 3
  else 1 / (k - 1 : ℝ)

end PoissonCRT
