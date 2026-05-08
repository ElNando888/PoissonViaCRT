/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela
-/
import Mathlib
import PoissonViaCRT.ConvergentEulerBound
import PoissonViaCRT.TupleCount

/-!
# Deviation Bound Helpers

Helper lemmas for closing the final `calc` step in `deviation_bound_k_ge_3`.

The partition bounds here bound subset sums by the **finite** Euler product
`∏_{p ∈ Q} (1 + w(p))` rather than by an infinite constant, aligning with the
Granville–Kurlberg `s^η`-trick (arXiv:math/0412135v1, §3).

## Main Results

* `PoissonCRT.small_partition_bound`: The small-divisor partition sum is bounded by
  `C * convergentEulerPartitionSum ε Ω Q`.
* `PoissonCRT.one_le_prod_primes`: The product of primes in a nonempty set is at least 1.
* `PoissonCRT.large_divisor_per_term_bound`: Per-term bound for the large-divisor case.
* `PoissonCRT.large_partition_bound`: The large-divisor partition sum is bounded by
  `C * largeEulerPartitionSum ε Ω Q`.
* `PoissonCRT.localMean`: The local expected value `μ_p = |Ω_p|^k / p^{k-1}`.
* `PoissonCRT.localCount`: The local counting function at prime `p`.
* `PoissonCRT.abs_localCount_sub_localMean_le`: Uniform bound
  `|localCount - localMean| ≤ p ^ k` for `k ≥ 1`.
-/

set_option linter.unusedVariables false

open Finset BigOperators Classical

namespace PoissonCRT

/-- The small-divisor partition sum bound: factoring out `C` and bounding a subset sum
by the full powerset sum, then applying the finite Euler product identity. -/
theorem small_partition_bound {ε : ℝ} (hε : 0 < ε)
    (Ω : ∀ p : ℕ, Finset (ZMod p))
    (Q : Finset ℕ) (S_sub : Finset (Finset ℕ))
    (hS : S_sub ⊆ Q.powerset)
    (C : ℝ) (hC : 0 ≤ C)
    (hΩle : ∀ p ∈ Q, (Ω p).card ≤ p) :
    ∑ T ∈ S_sub, C * ∏ p ∈ T, convergentEulerLocalWeight ε Ω p ≤
      C * convergentEulerPartitionSum ε Ω Q := by
  rw [← Finset.mul_sum]
  gcongr
  calc ∑ T ∈ S_sub, ∏ p ∈ T, convergentEulerLocalWeight ε Ω p
      ≤ ∑ T ∈ Q.powerset, ∏ p ∈ T, convergentEulerLocalWeight ε Ω p :=
        Finset.sum_le_sum_of_subset_of_nonneg hS fun T hT _ =>
          Finset.prod_nonneg fun p hp =>
            convergentEulerLocalWeight_nonneg ε Ω p (hΩle p (Finset.mem_powerset.mp hT hp))
    _ = convergentEulerPartitionSum ε Ω Q :=
        powerset_prod_eq_convergentEulerPartitionSum ε Ω Q

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
by the full powerset sum, then applying the finite Euler product identity. -/
theorem large_partition_bound {ε : ℝ} (hε : 0 < ε)
    (Ω : ∀ p : ℕ, Finset (ZMod p))
    (Q : Finset ℕ) (S_sub : Finset (Finset ℕ))
    (hS : S_sub ⊆ Q.powerset)
    (C : ℝ) (hC : 0 ≤ C)
    (hΩle : ∀ p ∈ Q, (Ω p).card ≤ p) :
    ∑ T ∈ S_sub, C * ∏ p ∈ T, largeEulerLocalWeight ε Ω p ≤
      C * largeEulerPartitionSum ε Ω Q := by
  rw [← Finset.mul_sum]
  gcongr
  calc ∑ T ∈ S_sub, ∏ p ∈ T, largeEulerLocalWeight ε Ω p
      ≤ ∑ T ∈ Q.powerset, ∏ p ∈ T, largeEulerLocalWeight ε Ω p :=
        Finset.sum_le_sum_of_subset_of_nonneg hS fun T hT _ =>
          Finset.prod_nonneg fun p hp =>
            largeEulerLocalWeight_nonneg ε Ω p (hΩle p (Finset.mem_powerset.mp hT hp))
    _ = largeEulerPartitionSum ε Ω Q :=
        powerset_prod_eq_largeEulerPartitionSum ε Ω Q

/-! ## Local deviation definitions and bounds -/

/-- The local expected value (mean) for the counting function at prime `p`:
`μ_p = |Ω_p|^k / p^{k-1}`. -/
noncomputable def localMean (k : ℕ) (Ω : ∀ p : ℕ, Finset (ZMod p)) (p : ℕ) : ℝ :=
  ((Ω p).card : ℝ) ^ k / (p : ℝ) ^ (k - 1)

/-- The local counting function value at prime `p`, projected from `ZMod q`.
For `p ∈ q.primeFactors`, this is `N_k(h mod p, Ω_p)`.
For `p ∉ q.primeFactors`, this is defined as `1` (a neutral element for products). -/
noncomputable def localCount {m : ℕ} (Ω : ∀ p : ℕ, Finset (ZMod p))
    (q : ℕ) [NeZero q] (h : Fin m → ZMod q) (p : ℕ) : ℝ :=
  if hp : p ∈ q.primeFactors then
    haveI : NeZero p := ⟨(Nat.mem_primeFactors.mp hp).1.ne_zero⟩
    (tupleCount (Ω p)
      (fun i => ZMod.castHom (Nat.dvd_of_mem_primeFactors hp) (ZMod p) (h i)) : ℝ)
  else 1

/-- `localCount` is nonneg (it is a natural number cast to `ℝ`). -/
lemma localCount_nonneg {Ω : ∀ p : ℕ, Finset (ZMod p)} {q : ℕ} [NeZero q]
    {h : Fin k → ZMod q} {p : ℕ} :
    0 ≤ localCount Ω q h p := by
  unfold localCount; split_ifs <;> norm_cast ;
  exact Nat.zero_le _

/-- `localCount` at a prime factor is at most `p`. -/
lemma localCount_le {q : ℕ} [NeZero q]
    (p : ℕ) (hp : p ∈ q.primeFactors) (Ω : ∀ p : ℕ, Finset (ZMod p))
    (h : Fin k → ZMod q) :
    localCount Ω q h p ≤ (p : ℝ) := by
  unfold localCount;
  simp +zetaDelta at *;
  split_ifs;
  haveI := Fact.mk hp.1; exact_mod_cast le_trans ( Finset.card_filter_le _ _ ) ( by norm_num ) ;

/-- `localMean` is nonneg. -/
lemma localMean_nonneg (k : ℕ) (Ω : ∀ p : ℕ, Finset (ZMod p)) (p : ℕ) :
    0 ≤ localMean k Ω p := by
  exact div_nonneg ( pow_nonneg ( Nat.cast_nonneg _ ) _ ) ( pow_nonneg ( Nat.cast_nonneg _ ) _ )

/-- `localMean` is at most `p` when `k ≥ 1` and `p` is prime. -/
lemma localMean_le (k : ℕ) (hk : 1 ≤ k) (Ω : ∀ p : ℕ, Finset (ZMod p)) (p : ℕ)
    (hp : p.Prime) :
    localMean k Ω p ≤ (p : ℝ) := by
  unfold localMean;
  rcases p with ( _ | _ | p ) <;> norm_num at *;
  rw [ div_le_iff₀ ] <;> norm_cast <;> norm_num;
  exact le_trans ( Nat.pow_le_pow_left ( show Finset.card ( Ω ( p + 1 + 1 ) ) ≤ p + 1 + 1 from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) _ ) ( by cases k <;> simp_all +decide [ pow_succ' ] )

/-- Uniform bound on the absolute local deviation: `|N_k(h mod p, Ω_p) - μ_p| ≤ p ^ k`.

The bound follows from the triangle inequality. Both `localCount` and `localMean` lie
in `[0, p]`:
- `localCount` is a `tupleCount`, hence a natural number at most `p`
  (it counts a subset of `ZMod p`).
- `localMean = |Ω_p|^k / p^{k-1} ≤ p^k / p^{k-1} = p`.

Thus `|localCount - localMean| ≤ p ≤ p ^ k` (for `k ≥ 1` and `p ≥ 2`). -/
lemma abs_localCount_sub_localMean_le_p {k : ℕ} (hk : 1 ≤ k) (q : ℕ) [NeZero q]
    (p : ℕ) (hp : p ∈ q.primeFactors) (Ω : ∀ p : ℕ, Finset (ZMod p))
    (h : Fin k → ZMod q) :
    |localCount Ω q h p - localMean k Ω p| ≤ (p : ℝ) := by
  refine' abs_sub_le_iff.mpr _
  constructor
  · refine' le_trans ( sub_le_self _ <| localMean_nonneg _ _ _ ) _
    exact localCount_le _ hp _ _
  · refine' le_trans ( sub_le_self _ ( localCount_nonneg ) ) _
    exact localMean_le k hk Ω p ( Nat.prime_of_mem_primeFactors hp )

lemma abs_localCount_sub_localMean_le {k : ℕ} (hk : 1 ≤ k) (q : ℕ) [NeZero q]
    (p : ℕ) (hp : p ∈ q.primeFactors) (Ω : ∀ p : ℕ, Finset (ZMod p))
    (h : Fin k → ZMod q) :
    |localCount Ω q h p - localMean k Ω p| ≤ (p : ℝ) ^ k := by
  exact le_trans ( abs_localCount_sub_localMean_le_p hk q p hp Ω h ) ( mod_cast Nat.le_self_pow ( by linarith ) _ )

end PoissonCRT
