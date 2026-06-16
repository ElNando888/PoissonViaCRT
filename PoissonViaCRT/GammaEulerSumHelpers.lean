/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela, Aristotle (Harmonic)
-/

import PoissonViaCRT.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Data.Pi.Interval

set_option linter.unusedVariables false

/-!
# Euler-product summation helpers for the gamma-weighted bound

This file collects the pure number-theoretic summation estimates underlying the
Granville–Kurlberg gamma-weighted Euler-product bounds (used in
`GammaDeviationSynthesis.lean`).

The central estimate is the "radical regrouping" bound: for a finite set `T` of
primes and a nonnegative weight `weil`, the sum
`∑_{γ ≤ N, primeFactors γ ⊆ T} (rad γ / γ) · B^{ω(γ)} · ∏_{p ∈ T \ pf γ} weil p`
factorises as an Euler product `≤ ∏_{p ∈ T} (2·B + weil p)`.  The heart of the
proof is the smooth-number harmonic bound
`∑_{n ≤ N, pf n ⊆ R} 1/n ≤ ∏_{p ∈ R} p/(p-1)`.
-/

open Finset BigOperators

namespace PoissonCRT

/-- `∏_{p ∈ R} p/(p-1) ≤ 2^{|R|}` for a finite set of primes `R`, since each
factor `p/(p-1) ≤ 2`. -/
lemma prod_p_div_sub_one_le_pow_two (R : Finset ℕ) (hR : ∀ p ∈ R, Nat.Prime p) :
    ∏ p ∈ R, (p : ℝ) / ((p : ℝ) - 1) ≤ 2 ^ R.card := by
  rw [show (2 : ℝ) ^ R.card = ∏ _p ∈ R, (2 : ℝ) by rw [Finset.prod_const]]
  apply Finset.prod_le_prod
  · intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast (hR p hp).two_le
    apply div_nonneg <;> linarith
  · intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast (hR p hp).two_le
    rw [div_le_iff₀ (by linarith)]; linarith

/-
**Smooth-number harmonic bound.** For a finite set of primes `R`, the sum of
`1/n` over `R`-smooth numbers `n ≤ N` (i.e. `primeFactors n ⊆ R`) is bounded by
the Euler product `∏_{p ∈ R} p/(p-1)`.
-/
lemma sum_inv_smooth_le (R : Finset ℕ) (hR : ∀ p ∈ R, Nat.Prime p) (N : ℕ) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.primeFactors ⊆ R), (1 : ℝ) / (n : ℝ) ≤
    ∏ p ∈ R, (p : ℝ) / ((p : ℝ) - 1) := by
  have h_sum_le_prod : ∀ N : ℕ, (∑ n ∈ Finset.filter (fun n => n.primeFactors ⊆ R) (Finset.Icc 1 N), (1 : ℝ) / n) ≤ (∏ p ∈ R, (∑ j ∈ Finset.range (Nat.log p N + 1), (1 : ℝ) / p ^ j)) := by
    intro N
    have h_sum_le_prod : Finset.filter (fun n => n.primeFactors ⊆ R) (Finset.Icc 1 N) ⊆ Finset.image (fun f : R → ℕ => ∏ p : R, p.val ^ f p) (Finset.Icc 0 (fun p : R => Nat.log p.val N)) := by
      intro n hn
      obtain ⟨hn_pos, hn_subset⟩ := Finset.mem_filter.mp hn;
      rw [Finset.mem_Icc] at hn_pos
      refine Finset.mem_image.mpr ⟨fun p => Nat.factorization n p.val, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        refine ⟨fun p => Nat.zero_le _, fun p => ?_⟩
        exact Nat.le_log_of_pow_le (Nat.Prime.one_lt (hR _ p.2))
          (Nat.le_trans (Nat.le_of_dvd hn_pos.1 (Nat.ordProj_dvd _ _)) hn_pos.2)
      · have hs : (n.factorization).support ⊆ R := by
          rw [Nat.support_factorization]; exact hn_subset
        have key : n = ∏ p ∈ R, p ^ n.factorization p := by
          conv_lhs => rw [← Nat.prod_factorization_pow_eq_self (show n ≠ 0 by omega)]
          rw [Finsupp.prod_of_support_subset _ hs (fun p k => p ^ k) (fun i _ => pow_zero i)]
        rw [Finset.prod_coe_sort R fun p => p ^ n.factorization p]
        exact key.symm
    refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg h_sum_le_prod fun _ _ _ => by positivity ) _;
    rw [ Finset.sum_image ];
    · erw [ Finset.prod_sum ];
      refine' le_of_eq _;
      refine' Finset.sum_bij ( fun f hf => fun p hp => f ⟨ p, hp ⟩ ) _ _ _ _ <;> simp +decide [ Finset.mem_Icc ];
      · exact fun f hf p hp => hf ⟨ p, hp ⟩;
      · simp +contextual [ funext_iff ];
      · exact fun b hb => ⟨ fun p => b p p.2, fun p => hb p p.2, rfl ⟩;
    · intro f hf g hg hfg; simp_all +decide ;
      ext ⟨ p, hp ⟩ ; replace hfg := congr_arg ( fun x : ℕ => x.factorization p ) hfg ; simp_all +decide ;
      rw [ Nat.factorization_prod, Nat.factorization_prod ] at hfg <;> simp_all +decide [ Nat.Prime.ne_zero ];
      rw [ Finset.sum_eq_single ⟨ p, hp ⟩, Finset.sum_eq_single ⟨ p, hp ⟩ ] at hfg <;> aesop;
  have h_prod_le_prod : ∀ p ∈ R, (∑ j ∈ Finset.range (Nat.log p N + 1), (1 : ℝ) / p ^ j) ≤ (p : ℝ) / (p - 1) := by
    intro p hp; have := hR p hp; have := this.two_le; norm_num [ div_eq_mul_inv ];
    have h_geo_sum : ∑ x ∈ Finset.range (Nat.log p N + 1), (p : ℝ)⁻¹ ^ x ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
      rw [ ← tsum_geometric_of_lt_one ( by positivity ) ( inv_lt_one_of_one_lt₀ ( by norm_cast ) ) ] ; exact Summable.sum_le_tsum ( Finset.range _ ) ( fun _ _ => by positivity ) ( by exact summable_geometric_of_lt_one ( by positivity ) ( inv_lt_one_of_one_lt₀ ( by norm_cast ) ) ) ;
    convert h_geo_sum using 1 <;> norm_num [ show p ≠ 0 by linarith ];
    field_simp;
  simpa using le_trans ( h_sum_le_prod N ) ( Finset.prod_le_prod ( fun _ _ => Finset.sum_nonneg fun _ _ => by positivity ) h_prod_le_prod )

/-
**Radical regrouping (single fibre).** For a finite set of primes `R`, the sum
of `rad γ / γ` over `γ ≤ N` with `primeFactors γ = R` is bounded by `2^{|R|}`.
The proof maps `γ ↦ γ / rad γ` onto the `R`-smooth numbers and applies
`sum_inv_smooth_le`.
-/
lemma sum_rad_div_eq_le_pow_two (R : Finset ℕ) (hR : ∀ p ∈ R, Nat.Prime p) (N : ℕ) :
    ∑ γ ∈ (Finset.Icc 1 N).filter (fun γ => γ.primeFactors = R),
      (radical γ : ℝ) / (γ : ℝ) ≤ 2 ^ R.card := by
  -- Applying the bound from `sum_inv_smooth_le` and `prod_p_div_sub_one_le_pow_two`.
  have h_bound : ∑ γ ∈ (Finset.Icc 1 N).filter (fun γ => γ.primeFactors = R), (radical γ : ℝ) / γ ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.primeFactors ⊆ R), (1 : ℝ) / n := by
    refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ _ );
    case refine'_2 => exact Finset.image ( fun γ => γ / radical γ ) ( Finset.filter ( fun γ => γ.primeFactors = R ) ( Finset.Icc 1 N ) );
    · rw [ Finset.sum_image ];
      · refine' Finset.sum_le_sum fun x hx => _;
        rw [ Nat.cast_div_charZero ( show radical x ∣ x from Nat.prod_primeFactors_dvd _ ) ] ; ring_nf ; norm_num;
        linarith;
      · intro x hx y hy; have := Nat.div_mul_cancel ( show radical x ∣ x from ?_ ) ; have := Nat.div_mul_cancel ( show radical y ∣ y from ?_ ) ; simp_all +decide [ radical ] ;
        · grind;
        · exact Nat.prod_primeFactors_dvd _;
        · exact Nat.prod_primeFactors_dvd _;
    · intro;
      simp +zetaDelta at *;
      rintro x hx₁ hx₂ hx₃ rfl; refine' ⟨ ⟨ Nat.div_pos _ _, Nat.div_le_self _ _ |> le_trans <| hx₂ ⟩, _ ⟩;
      · exact Nat.le_of_dvd hx₁ ( Nat.prod_primeFactors_dvd _ );
      · exact Finset.prod_pos fun p hp => Nat.Prime.pos ( hR p ( hx₃ ▸ hp ) );
      · exact Nat.primeFactors_mono ( Nat.div_dvd_of_dvd <| Nat.prod_primeFactors_dvd _ ) ( by aesop ) |> fun h => h.trans <| by aesop;
    · exact fun _ _ _ => by positivity;
  exact h_bound.trans ( le_trans ( sum_inv_smooth_le R hR N ) ( prod_p_div_sub_one_le_pow_two R hR ) )

/-
**Core Euler-product summation bound.** For a finite set of primes `T`, a
base `B ≥ 1`, and a nonnegative weight `weil`, the radical-weighted sum
factorises as an Euler product. This is the analytic engine behind both the
small- and large-γ gamma-sum bounds.
-/
lemma core_gamma_euler_sum (T : Finset ℕ) (hT : ∀ p ∈ T, Nat.Prime p) (N : ℕ)
    (B : ℝ) (hB : 1 ≤ B) (weil : ℕ → ℝ) (hweil : ∀ p ∈ T, 0 ≤ weil p) :
    ∑ γ ∈ (Finset.Icc 1 N).filter (fun γ => γ.primeFactors ⊆ T),
      (radical γ : ℝ) / (γ : ℝ) * B ^ γ.primeFactors.card *
        ∏ p ∈ T \ γ.primeFactors, weil p ≤
    ∏ p ∈ T, (2 * B + weil p) := by
  -- By definition of radical, we can rewrite the sum as a product.
  have h_sum_prod : ∑ γ ∈ (Finset.Icc 1 N).filter (fun γ => γ.primeFactors ⊆ T), (radical γ : ℝ) / (γ : ℝ) * B ^ (γ.primeFactors.card : ℕ) * (∏ p ∈ T \ γ.primeFactors, weil p) = ∑ R ∈ T.powerset, (∑ γ ∈ (Finset.Icc 1 N).filter (fun γ => γ.primeFactors = R), (radical γ : ℝ) / (γ : ℝ)) * B ^ R.card * (∏ p ∈ T \ R, weil p) := by
    simp +decide only [sum_filter, sum_mul];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
  -- Apply the bound from `sum_rad_div_eq_le_pow_two` to each term in the sum.
  have h_bound : ∀ R ∈ T.powerset, (∑ γ ∈ (Finset.Icc 1 N).filter (fun γ => γ.primeFactors = R), (radical γ : ℝ) / (γ : ℝ)) ≤ 2 ^ R.card := by
    intro R hR
    apply sum_rad_div_eq_le_pow_two R (fun p hp => hT p (Finset.mem_powerset.mp hR hp)) N;
  rw [ h_sum_prod ];
  refine' le_trans ( Finset.sum_le_sum fun R hR => mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( h_bound R hR ) ( by positivity ) ) ( Finset.prod_nonneg fun x hx => hweil x (Finset.mem_sdiff.mp hx).1 ) ) _;
  simp +decide [ ← mul_pow, Finset.prod_add ]

end PoissonCRT
