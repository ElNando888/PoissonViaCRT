/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import PoissonViaCRT.Defs
import PoissonViaCRT.TupleCount

/-!
# Poisson Statistics Primer (§2)

Formalization of Section 2 of "Poisson statistics via the Chinese remainder theorem"
by Granville–Kurlberg, which provides the probabilistic framework for the paper.

## Main Results

* `PoissonCRT.density_nonneg`, `PoissonCRT.density_le_one`: Basic density properties.
* `PoissonCRT.density_eq_inv_avgSpacing`: The reciprocal relation `r_q = 1 / s_q`.
* `PoissonCRT.condExpectation_indicator`: Combinatorial core of Lemma 2.1.

The full Lemma 2.1 (expected correlation for random subsets) requires probability-theoretic
infrastructure not formalized here; the statement is recorded for reference.

## References

* [A. Granville, P. Kurlberg, *Poisson statistics via the Chinese remainder theorem*]
  [arXiv:math/0412135v2], §2
-/

open Finset BigOperators

namespace PoissonCRT

/-! ### Characterization of Poisson distribution via correlations

The spacings of elements in `Ω_{qₙ}` become Poisson as `n → ∞` if and only if
for each integer `k ≥ 2` and box `X ∈ 𝔹_k`,
$$R_k(X, \Omega_{q_n}) \to \operatorname{vol}(X) \text{ as } n \to \infty.$$

This characterization is from Appendix A of Kurlberg–Rudnick (cited in §2 of the paper).
The definition `IsPoissonDistributed` directly encodes this characterization.
-/

/-! ### Correlations for randomly selected sets (§2.1)

Let `X₁, X₂, …, X_q` be independent Bernoulli random variables with parameter `1/σ ∈ (0,1)`.
Given an outcome, define `Ω_q ⊆ ℤ/qℤ` by `i ∈ Ω_q` iff `Xᵢ = 1`.
The expected average gap is `σ`.

**Lemma 2.1**: Expected correlation for random subsets:
$$\mathbb{E}(R_k(X, q)) = \operatorname{vol}(X) + O_k(1/\sigma + \sigma/q)$$
and the variance satisfies:
$$\mathbb{E}\left((R_k(X, q) - \operatorname{vol}(X))^2\right) \ll_k 1/\sigma + \sigma/q.$$

The proof uses conditional expectations. The core combinatorial identity is:
$$\mathbb{E}(x_i x_{i+h_1} \cdots x_{i+h_{k-1}} \mid |Ω| = r) =
  \binom{q-k}{r-k} / \binom{q}{r}.$$

Full formalization requires probability theory infrastructure (Bernoulli measures on subsets
of `ℤ/qℤ`). We record the combinatorial core below.
-/

/-- The conditional expectation of the indicator product: the probability that specific
`k` positions are all in a random subset of `{1, …, q}` of size `r` is `C(q-k, r-k) / C(q, r)`.
This equals `∏_{i=0}^{k-1} (r-i)/(q-i)`, proved by induction on `k`. -/
theorem condExpectation_indicator (q k r : ℕ) (hk : k ≤ q) (hr : k ≤ r) (hrq : r ≤ q) :
    (Nat.choose (q - k) (r - k) : ℚ) / Nat.choose q r =
      ∏ i ∈ Finset.range k, ((r - i : ℚ) / (q - i)) := by
  by_cases hqr : r = q;
  · simp_all +decide [Finset.prod_eq_zero_iff, sub_eq_zero];
  · induction' k with k ih generalizing r q <;> simp_all +decide [ Finset.prod_range_succ ];
    · exact ne_of_gt <| Nat.choose_pos hrq;
    · rw [ mul_div_mul_comm, ← ih ];
      · rw [ div_mul_div_comm, div_eq_div_iff ] <;> norm_cast;
        · rw [ Int.subNatNat_of_le hk.le, Int.subNatNat_of_le hr.le ];
          rw [ show q - k = ( q - ( k + 1 ) ) + 1 by omega, show r - k = ( r - ( k + 1 ) ) + 1 by omega ] ; norm_cast ; simp +decide [ Nat.add_one_mul_choose_eq, mul_assoc, mul_comm ] ;
        · exact Nat.ne_of_gt <| Nat.choose_pos hrq;
        · exact mul_ne_zero ( Nat.cast_ne_zero.mpr ( Nat.ne_of_gt ( Nat.choose_pos hrq ) ) ) ( by rw [ Int.subNatNat_eq_coe ] ; linarith );
      · grind;
      · lia;
      · linarith;
      · assumption

/-! ### Properties of the average spacing and density -/

private theorem card_le_q {q : ℕ} [NeZero q] (Ω : Finset (ZMod q)) :
    (Ω.card : ℚ) ≤ q := by
  have := Finset.card_le_univ Ω
  simp [ZMod.card] at this
  exact_mod_cast this

/-- The density satisfies `0 ≤ r_q`. -/
theorem density_nonneg {q : ℕ} [NeZero q] (Ω : Finset (ZMod q)) :
    0 ≤ density Ω := by
  unfold density; positivity

/-- The density satisfies `r_q ≤ 1`. -/
theorem density_le_one {q : ℕ} [NeZero q] (Ω : Finset (ZMod q)) :
    density Ω ≤ 1 := by
  exact div_le_one_of_le₀ (card_le_q Ω) (Nat.cast_nonneg _)

/-- `density Ω = 1 / avgSpacing Ω` when `Ω` is nonempty. -/
theorem density_eq_inv_avgSpacing {q : ℕ} [NeZero q] (Ω : Finset (ZMod q))
    (_ : (Ω.card : ℚ) ≠ 0) :
    density Ω = 1 / avgSpacing Ω := by
  simp [density, avgSpacing, one_div, inv_div]

/-- The average spacing is at least 1 for nonempty subsets. -/
theorem avgSpacing_ge_one {q : ℕ} [NeZero q] (Ω : Finset (ZMod q)) (hΩ : Ω.Nonempty) :
    1 ≤ avgSpacing Ω := by
  unfold avgSpacing
  rw [le_div_iff₀ (by exact_mod_cast hΩ.card_pos)]
  simp only [one_mul]
  exact card_le_q Ω

end PoissonCRT