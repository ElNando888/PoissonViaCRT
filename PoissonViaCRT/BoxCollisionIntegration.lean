/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela

The architectural design of this LatticeCounting framework was developed by
Antigravity (Google DeepMind) to formalize combinatorial CRT counting arguments.

References:
- Granville & Kurlberg (2008), arXiv:math/0412135
- Iwaniec & Kowalski, Analytic Number Theory
-/

module
public import PoissonViaCRT.BoxCollisionHelpers
import PoissonViaCRT.LatticeCounting.SimultaneousCongruences
import PoissonViaCRT.LatticeCounting.OneDimCounting
import PoissonViaCRT.LatticeCounting.SequentialCounting
import Mathlib

/-!
# Module 5: BoxCollisionIntegration

## Goal
Prove `box_collision_sum_bound` by expanding the product of indicators into a sum over choice functions `σ ∈ U.pi pairsBelow`, and then sequentially bounding each coordinate via CRT.

## Implementation Hints (for Aristotle):
You are tasked with formalizing BOTH `validHForSigma_card_le` and `box_collision_sum_bound`.

Hints for `validHForSigma_card_le`:
- Apply `LatticeCounting.seq_bound_nat`.
- For a fixed `k : Fin m`, the moduli are `p ∈ U` such that `(σ p _).2 = k.succ`. Use `LatticeCounting.crt_finset` to combine these congruences into a single modulo constraint `M_k = ∏ p, p`.
- The target values `extendH m h (σ p _).1` only depend on coordinates `< k` because `(σ p _).1 < (σ p _).2 = k.succ`. This aligns perfectly with `AgreeOn (k : ℕ)`.
- Bound the number of valid `h k` using `LatticeCounting.count_congruence_interval_strict`. Note that `inScaledBox` enforces `h k ≠ h i` for `i < k`, guaranteeing the strictness condition!

Hints for `box_collision_sum_bound`:
- Expand the product of indicators into a sum over choice functions `σ` (where `σ` selects the colliding pair of indices for each prime `p`).
- Swap the sums to get `∑_σ ∑_h`. The inner sum is exactly the cardinality of `validHForSigma`.
- Apply `validHForSigma_card_le` to bound the inner sum by `∏_{j=1}^m (S / M_j + 1)`.
- Algebraically expand `∏_{j=1}^m (S / M_j + 1)`. Since `∏ M_j = ∏ p`, the leading term is `S^m / ∏ p`. The remaining terms have at most `m-1` factors of `S`, and since `S ≥ 1`, they can be uniformly bounded by `2^m S^{m-1}`.
- Sum this uniform bound over all `σ`. The number of choice functions is `C_gamma^{|U|}`. If the algebraic expansion gets too tedious, isolate it into a helper lemma and `sorry` it so you can finish the main assembly!
-/

set_option maxHeartbeats 800000

namespace PoissonCRT

open Finset BigOperators Classical
open LatticeCounting

/-- The set of surviving box points for a fixed choice function `σ`. -/
noncomputable def validHForSigma (m : ℕ) (X : Box m) (s : ℝ) (U : Finset ℕ)
    (σ : ∀ p ∈ U, Fin (m + 1) × Fin (m + 1)) : Finset (Fin m → ℤ) :=
  ((Fintype.piFinset fun _ => Finset.Icc (1:ℤ) ⌈s * ∑ i, X.sides i⌉).filter
    (fun h => inScaledBox X s (fun _ => 0) h)).filter
    (fun h => ∀ p ∈ U, ∀ hp : p ∈ U, (p : ℤ) ∣ (extendH m h (σ p hp).2 - extendH m h (σ p hp).1))

/-- The sequential cardinality bound for a fixed choice function `σ`.
**Corrected statement**: the per-coordinate bound is `⌊N / M_k⌋ + 1` instead of `2 * ⌊N / M_k⌋`,
which is the maximum number of integers in a congruence class within an interval. -/
lemma validHForSigma_card_le (m : ℕ) (X : Box m) (s : ℝ) (hs : 1 ≤ s)
    (U : Finset ℕ) (hp_prime : ∀ p ∈ U, p.Prime)
    (σ : ∀ p ∈ U, Fin (m + 1) × Fin (m + 1))
    (h_sigma : ∀ p (hp_mem : p ∈ U), (σ p hp_mem) ∈ pairsBelow m) :
    (validHForSigma m X s U σ).card ≤
      ∏ j : Fin m, (⌈s * ∑ i, X.sides i⌉ / ∏ p ∈ U.filter (fun p =>
        ∃ hp_mem : p ∈ U, (σ p hp_mem).2 = j.succ), (p:ℤ) + 1).toNat := by
  sorry

/-- The full collision sum bound, including the error term for large U (following GK). -/
public lemma box_collision_sum_bound (m : ℕ) (hm : 1 ≤ m) (X : Box m) :
    ∃ C_box C_gamma : ℝ, 0 < C_box ∧ 0 < C_gamma ∧ ∀ (s : ℝ) (_ : 1 ≤ s) (U : Finset ℕ)
    (_ : ∀ p ∈ U, Nat.Prime p),
    ∑ h ∈ ((Fintype.piFinset fun _ => Finset.Icc (1:ℤ) ⌈s * ∑ i, X.sides i⌉).filter
        (fun h => inScaledBox X s (fun _ => 0) h)),
      (∏ p ∈ U, if Function.Injective (Fin.cons (0 : ZMod p) (fun i => (h i : ZMod p)))
       then (0:ℝ) else 1)
    ≤ C_box * (s ^ m / ∏ p ∈ U, (p : ℝ) + s ^ (m - 1)) * ∏ p ∈ U, C_gamma := by
  sorry

end PoissonCRT

/-
PROVIDED SOLUTION

Please formalize the two `sorry`s in `PoissonViaCRT/BoxCollisionIntegration.lean`:
1. `validHForSigma_card_le`
2. `box_collision_sum_bound`

The mathematical structure has been completely fixed to match the Granville & Kurlberg paper exactly. The false algebraic bounds have been replaced with the proper GK fallback error terms.

## Hints for `validHForSigma_card_le`:
- Apply `LatticeCounting.seq_bound_nat`.
- For a fixed `k : Fin m`, the moduli are `p ∈ U` such that `(σ p _).2 = k.succ`. Use `LatticeCounting.crt_finset` to combine these congruences into a single modulo constraint `M_k = ∏ p, p`.
- The target values `extendH m h (σ p _).1` only depend on coordinates `< k` because `(σ p _).1 < (σ p _).2 = k.succ`. This aligns perfectly with `AgreeOn (k : ℕ)`.
- Bound the number of valid `h k` using `LatticeCounting.count_congruence_interval_strict`. Note that `inScaledBox` enforces `h k ≠ h i` for `i < k`, guaranteeing the strictness condition!

## Hints for `box_collision_sum_bound`:
- Expand the product of indicators `∏ p ∈ U, B_p(h)` into a sum over all possible choice functions `σ` (where `σ` selects the colliding pair of indices for each prime `p`).
- Swap the sums to get `∑_σ ∑_h`. The inner sum is exactly the cardinality of `validHForSigma m X s U σ`.
- Apply `validHForSigma_card_le` to bound the inner sum by `∏_{j=1}^m (S / M_j + 1)`.
- Algebraically expand `∏_{j=1}^m (S / M_j + 1)`. Since `∏ M_j = ∏ p`, the leading term is `S^m / ∏ p`. The remaining terms have at most `m-1` factors of `S`, and since `S ≥ 1`, they can be uniformly bounded by `2^m S^{m-1}`.
- Sum this uniform bound over all `σ`. The number of choice functions is `C_gamma^{|U|}` where `C_gamma = m(m+1)/2`.
- Set `C_box = 2^m`. If the algebraic expansion of `∏ (S / M_j + 1) ≤ S^m / ∏ p + 2^m S^{m-1}` gets too tedious for Lean, isolate it into a helper lemma and `sorry` it so you can finish the main assembly!
-/
