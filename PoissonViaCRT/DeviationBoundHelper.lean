/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela
-/
import PoissonViaCRT.ConvergentEulerBound

/-!
# Deviation Bound Helpers

Helper lemmas for closing the final `calc` step in `deviation_bound_k_ge_3`.

## Main Results

* `PoissonCRT.small_partition_bound`: The small-divisor partition sum is bounded by
  `C * convergentEulerBoundConstant k ε Ω`.
* `PoissonCRT.one_le_prod_primes`: The product of primes in a nonempty set is at least 1.
* `PoissonCRT.large_divisor_per_term_bound`: Per-term bound for the large-divisor case.
* `PoissonCRT.large_partition_bound`: The large-divisor partition sum is bounded by
  `C * largeEulerBoundConstant k ε Ω`.
-/

set_option linter.unusedVariables false

open Finset BigOperators Classical

namespace PoissonCRT

/-- The small-divisor partition sum bound: factoring out `C` and bounding a subset sum
by the full powerset sum, then applying the Euler product bound. -/
theorem small_partition_bound {k : ℕ} (hk : 3 ≤ k) {ε : ℝ} (hε : 0 < ε)
    (Ω : ∀ p : ℕ, Finset (ZMod p))
    (Q : Finset ℕ) (S_sub : Finset (Finset ℕ))
    (hS : S_sub ⊆ Q.powerset)
    (C : ℝ) (hC : 0 ≤ C)
    (hΩle : ∀ p, (Ω p).card ≤ p)
    (h_summable : Summable (convergentEulerLocalWeight ε Ω)) :
    ∑ T ∈ S_sub, C * ∏ p ∈ T, convergentEulerLocalWeight ε Ω p ≤
      C * convergentEulerBoundConstant k ε Ω := by
  rw [← Finset.mul_sum]
  gcongr
  calc ∑ T ∈ S_sub, ∏ p ∈ T, convergentEulerLocalWeight ε Ω p
      ≤ ∑ T ∈ Q.powerset, ∏ p ∈ T, convergentEulerLocalWeight ε Ω p :=
        Finset.sum_le_sum_of_subset_of_nonneg hS fun _ _ _ =>
          Finset.prod_nonneg fun p _ => convergentEulerLocalWeight_nonneg ε Ω p (hΩle p)
    _ = convergentEulerPartitionSum ε Ω Q :=
        powerset_prod_eq_convergentEulerPartitionSum ε Ω Q
    _ ≤ convergentEulerBoundConstant k ε Ω :=
        convergentEulerPartitionSum_le_bound hk hε Ω Q h_summable hΩle

/-- For `T` nonempty with all elements prime, `1 ≤ ∏ p ∈ T, (p : ℝ)`. -/
theorem one_le_prod_primes (T : Finset ℕ) (hT : T.Nonempty)
    (hprimes : ∀ p ∈ T, p.Prime) :
    1 ≤ ∏ p ∈ T, (p : ℝ) :=
  Finset.prod_le_prod (fun _ _ => by positivity)
    (fun p hp => Nat.one_le_cast.mpr (hprimes p hp).pos) |>.trans' (by norm_num)

/-- Per-term bound for the large-divisor case:
`(s * V + C) * ∏ w ≤ (V + C) * ∏ (p * w)` when `s ≤ ∏ p` and `1 ≤ ∏ p`. -/
theorem large_divisor_per_term_bound (T : Finset ℕ)
    (w : ℕ → ℝ) (hw : ∀ p ∈ T, 0 ≤ w p)
    (s V C : ℝ) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hs_le : s ≤ ∏ p ∈ T, (p : ℝ))
    (h1_le : 1 ≤ ∏ p ∈ T, (p : ℝ)) :
    (s * V + C) * ∏ p ∈ T, w p ≤
      (V + C) * ∏ p ∈ T, ((p : ℝ) * w p) := by
  rw [Finset.prod_mul_distrib]
  nlinarith [mul_le_mul_of_nonneg_right hs_le hV,
    mul_le_mul_of_nonneg_right h1_le hV,
    mul_le_mul_of_nonneg_right hs_le hC,
    mul_le_mul_of_nonneg_right h1_le hC,
    show 0 ≤ ∏ p ∈ T, w p from Finset.prod_nonneg hw]

/-- The large-divisor partition sum bound: bounding a subset sum
by the full powerset sum, then applying the large Euler product bound. -/
theorem large_partition_bound {k : ℕ} (hk : 3 ≤ k) {ε : ℝ} (hε : 0 < ε)
    (Ω : ∀ p : ℕ, Finset (ZMod p))
    (Q : Finset ℕ) (S_sub : Finset (Finset ℕ))
    (hS : S_sub ⊆ Q.powerset)
    (C : ℝ) (hC : 0 ≤ C)
    (hΩle : ∀ p, (Ω p).card ≤ p)
    (h_summable : Summable (largeEulerLocalWeight ε Ω)) :
    ∑ T ∈ S_sub, C * ∏ p ∈ T, largeEulerLocalWeight ε Ω p ≤
      C * largeEulerBoundConstant k ε Ω := by
  rw [← Finset.mul_sum]
  gcongr
  calc ∑ T ∈ S_sub, ∏ p ∈ T, largeEulerLocalWeight ε Ω p
      ≤ ∑ T ∈ Q.powerset, ∏ p ∈ T, largeEulerLocalWeight ε Ω p :=
        Finset.sum_le_sum_of_subset_of_nonneg hS fun _ _ _ =>
          Finset.prod_nonneg fun _ _ => largeEulerLocalWeight_nonneg ε Ω _ (hΩle _)
    _ = largeEulerPartitionSum ε Ω Q :=
        powerset_prod_eq_largeEulerPartitionSum ε Ω Q
    _ ≤ largeEulerBoundConstant k ε Ω :=
        largeEulerPartitionSum_le_bound hk hε Ω Q h_summable hΩle

end PoissonCRT
