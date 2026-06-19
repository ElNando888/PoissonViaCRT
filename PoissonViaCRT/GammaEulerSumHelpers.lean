/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela, Aristotle (Harmonic)
-/

import PoissonViaCRT.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Data.Pi.Interval
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

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

/-
**Fractional smooth-number harmonic bound.** For a finite set of primes `R` and
`0 < α`, the sum of `n^{-α}` over `R`-smooth numbers `n ≤ N` is bounded by the
Euler product `∏_{p ∈ R} 1/(1 - p^{-α})`.  This is the fractional analogue of
`sum_inv_smooth_le` (geometric sum with ratio `p^{-α}` instead of `p^{-1}`).
-/
lemma sum_rpow_smooth_le (R : Finset ℕ) (hR : ∀ p ∈ R, Nat.Prime p) (N : ℕ)
    (α : ℝ) (hα0 : 0 < α) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.primeFactors ⊆ R), (n : ℝ) ^ (-α) ≤
    ∏ p ∈ R, 1 / (1 - (p : ℝ) ^ (-α)) := by
  -- The sum over smooth numbers is a subset of the product of geometric sums.
  have h_subset : (∑ n ∈ Finset.filter (fun n => n.primeFactors ⊆ R) (Finset.Icc 1 N), (n : ℝ) ^ (-α)) ≤ (∏ p ∈ R, (∑ j ∈ Finset.range (Nat.log p N + 1), (p : ℝ) ^ (-α * j))) := by
    -- By definition of $R$-smooth numbers, we can write each $n$ as a product of primes in $R$.
    have h_factor : Finset.filter (fun n => n.primeFactors ⊆ R) (Finset.Icc 1 N) ⊆ Finset.image (fun f : R → ℕ => ∏ p : R, (p : ℕ) ^ (f p)) (Finset.Icc 0 (fun p : R => Nat.log p N)) := by
      intro n hn;
      refine' Finset.mem_image.mpr ⟨ fun p => Nat.factorization n p, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
      · intro p; exact Nat.le_log_of_pow_le ( Nat.Prime.one_lt ( hR _ ( by aesop ) ) ) ( Nat.le_trans ( Nat.le_of_dvd hn.1.1 ( Nat.ordProj_dvd _ _ ) ) hn.1.2 ) ;
      · have hs : (Nat.factorization n).support ⊆ R := by
          rw [Nat.support_factorization]; intro p hp
          exact hn.2 (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
            (Nat.one_le_iff_ne_zero.mp hn.1.1)
        conv_rhs => rw [ ← Nat.prod_factorization_pow_eq_self ( by linarith : n ≠ 0 ) ] ;
        rw [ Finsupp.prod_of_support_subset _ hs (fun p k => p ^ k) (fun i _ => pow_zero i) ];
    refine le_trans ( Finset.sum_le_sum_of_subset_of_nonneg h_factor fun _ _ _ => by positivity ) ?_;
    rw [ Finset.sum_image ];
    · erw [ Finset.prod_sum ];
      refine' le_of_eq _;
      refine' Finset.sum_bij ( fun f hf => fun p hp => f ⟨ p, hp ⟩ ) _ _ _ _ <;> simp +decide [ Real.rpow_neg, Real.rpow_mul ];
      · exact fun f hf p hp => hf ⟨ p, hp ⟩;
      · simp +contextual [ funext_iff ];
      · exact fun b hb => ⟨ fun p => b p p.2, fun p => hb p p.2, rfl ⟩;
      · intro a ha; rw [ Real.rpow_neg ( Finset.prod_nonneg fun _ _ => by positivity ) ] ; simp +decide [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ) ] ;
        rw [ ← Real.finsetProd_rpow _ _ fun x hx => by positivity, Finset.prod_congr rfl ] ; intros ; rw [ ← Real.rpow_mul ( Nat.cast_nonneg _ ) ] ; ring_nf;
    · intro f hf g hg hfg; ext p; replace hfg := congr_arg ( fun x : ℕ => x.factorization p ) hfg; simp_all +decide ;
      rw [ Nat.factorization_prod, Nat.factorization_prod ] at hfg <;> simp_all +decide [ Nat.Prime.ne_zero ];
      simp_all +decide [ Finsupp.single_apply ];
  refine le_trans h_subset <| Finset.prod_le_prod ?_ ?_ <;> norm_num;
  · exact fun p hp => Finset.sum_nonneg fun _ _ => Real.rpow_nonneg ( Nat.cast_nonneg _ ) _;
  · intro p hp; rw [ ← tsum_geometric_of_lt_one ( by positivity ) ( by simpa using Real.rpow_lt_rpow_of_exponent_lt ( Nat.one_lt_cast.mpr ( hR p hp |> Nat.Prime.one_lt ) ) ( neg_lt_zero.mpr hα0 ) ) ] ;
    norm_num [ Real.rpow_neg, Real.rpow_mul ];
    exact Summable.sum_le_tsum ( Finset.range ( Nat.log p N + 1 ) ) ( fun _ _ => by positivity ) ( by simpa using summable_geometric_of_lt_one ( by positivity ) ( inv_lt_one_of_one_lt₀ ( Real.one_lt_rpow ( Nat.one_lt_cast.mpr ( hR p hp |> Nat.Prime.one_lt ) ) hα0 ) ) )

/-
**Per-prime factor bound.** Since every prime `p ∈ R` satisfies `p ≥ 2`, the
Euler factor `1/(1 - p^{-α})` is bounded by `1/(1 - 2^{-α})`, hence the product
over `R` is at most `(1/(1 - 2^{-α}))^{|R|}`.  Fractional analogue of
`prod_p_div_sub_one_le_pow_two`.
-/
lemma prod_one_div_one_sub_rpow_le_pow (R : Finset ℕ) (hR : ∀ p ∈ R, Nat.Prime p)
    (α : ℝ) (hα0 : 0 < α) :
    ∏ p ∈ R, 1 / (1 - (p : ℝ) ^ (-α)) ≤ (1 / (1 - (2:ℝ)^(-α))) ^ R.card := by
  have h_euler_prod : ∀ p ∈ R, (1 : ℝ) / (1 - (p : ℝ) ^ (-α)) ≤ (1 : ℝ) / (1 - (2 : ℝ) ^ (-α)) := by
    intro p hp
    have h_le : (p : ℝ) ^ (-α) ≤ (2 : ℝ) ^ (-α) := by
      rw [ Real.rpow_le_rpow_iff_of_neg ] <;> norm_num <;> linarith [ Nat.Prime.two_le ( hR p hp ) ];
    gcongr;
    exact sub_pos_of_lt ( by simpa using Real.rpow_lt_rpow_of_exponent_lt ( by norm_num ) ( neg_lt_zero.mpr hα0 ) );
  convert Finset.prod_le_prod ?_ h_euler_prod using 2 <;> norm_num;
  exact fun p hp => by simpa using Real.rpow_le_rpow_of_exponent_le ( Nat.one_le_cast.mpr ( Nat.Prime.pos ( hR p hp ) ) ) ( neg_nonpos.mpr hα0.le ) ;

/-
Fractional radical-regrouping (single fibre).
-/
lemma sum_rad_div_rpow_le_pow (R : Finset ℕ) (hR : ∀ p ∈ R, Nat.Prime p)
    (N : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∑ γ ∈ (Finset.Icc 1 N).filter (fun γ => γ.primeFactors = R),
        (radical γ : ℝ) / (γ : ℝ) ^ α
      ≤ (1 / (1 - (2:ℝ)^(-α))) ^ R.card * ∏ p ∈ R, (p : ℝ) ^ (1 - α) := by
  -- Apply the radical-regrouping (single fibre) lemma to rewrite the sum.
  have h_sum_rewrite : ∑ γ ∈ (Finset.Icc 1 N).filter (fun γ => γ.primeFactors = R), (radical γ : ℝ) / (γ : ℝ) ^ α = (∏ p ∈ R, (p : ℝ) ^ (1 - α)) * ∑ γ ∈ (Finset.Icc 1 N).filter (fun γ => γ.primeFactors = R), (γ / radical γ : ℝ) ^ (-α) := by
    rw [ Finset.mul_sum _ _ _ ];
    refine Finset.sum_congr rfl fun x hx => ?_;
    rw [ Real.div_rpow ( by positivity ) ( by positivity ), Real.rpow_neg ( by positivity ) ];
    rw [ div_eq_mul_inv, mul_comm ];
    rw [ show ( radical x : ℝ ) = ∏ p ∈ R, ( p : ℝ ) from ?_, Real.finsetProd_rpow _ _ fun p hp => Nat.cast_nonneg _ ] ; ring_nf;
    · rw [ mul_assoc, ← Real.rpow_neg ( Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _ ), ← Real.rpow_add ( Finset.prod_pos fun _ _ => Nat.cast_pos.mpr ( Nat.Prime.pos ( hR _ ‹_› ) ) ) ] ; norm_num;
    · unfold radical; aesop;
  -- Apply the smooth-number harmonic bound to the inner sum.
  have h_inner_sum_bound : ∑ γ ∈ (Finset.Icc 1 N).filter (fun γ => γ.primeFactors = R), (γ / radical γ : ℝ) ^ (-α) ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.primeFactors ⊆ R), (n : ℝ) ^ (-α) := by
    have h_inner_sum_bound : (Finset.image (fun γ => γ / radical γ) ((Finset.Icc 1 N).filter (fun γ => γ.primeFactors = R))) ⊆ (Finset.Icc 1 N).filter (fun n => n.primeFactors ⊆ R) := by
      intro n hn
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hn
      have h_div : γ / radical γ ∈ Finset.Icc 1 N := by
        exact Finset.mem_Icc.mpr ⟨ Nat.div_pos ( Nat.le_of_dvd ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hγ |>.1 ) |>.1 ) ( Nat.prod_primeFactors_dvd _ ) ) ( Finset.prod_pos fun p hp => Nat.Prime.pos ( by aesop ) ), Nat.le_trans ( Nat.div_le_self _ _ ) ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hγ |>.1 ) |>.2 ) ⟩
      have h_prime_factors : (γ / radical γ).primeFactors ⊆ R := by
        exact Nat.primeFactors_mono ( Nat.div_dvd_of_dvd <| Nat.prod_primeFactors_dvd _ ) ( by aesop ) |> Finset.Subset.trans <| by aesop;
      exact Finset.mem_filter.mpr ⟨h_div, h_prime_factors⟩;
    refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg h_inner_sum_bound fun _ _ _ => Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ );
    rw [ Finset.sum_image ];
    · refine' Finset.sum_le_sum fun x hx => _;
      rw [ Nat.cast_div_charZero ( show radical x ∣ x from Nat.prod_primeFactors_dvd _ ) ];
    · intro x hx y hy; have := Nat.prod_primeFactors_dvd x; have := Nat.prod_primeFactors_dvd y; simp_all +decide [ radical ] ;
  convert mul_le_mul_of_nonneg_left ( h_inner_sum_bound.trans <| sum_rpow_smooth_le R hR N α hα0 |> le_trans <| prod_one_div_one_sub_rpow_le_pow R hR α hα0 ) <| show 0 ≤ ( ∏ p ∈ R, ( p : ℝ ) ^ ( 1 - α ) ) by exact Finset.prod_nonneg fun p hp => Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ using 1 ; ring

/-
Fractional-exponent core Euler engine.
-/
lemma core_gamma_euler_sum_frac (T : Finset ℕ) (hT : ∀ p ∈ T, Nat.Prime p)
    (N : ℕ) (B : ℝ) (hB : 1 ≤ B) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (weil : ℕ → ℝ) (hweil : ∀ p ∈ T, 0 ≤ weil p) :
    ∑ γ ∈ (Finset.Icc 1 N).filter (fun γ => γ.primeFactors ⊆ T),
        (radical γ : ℝ) / (γ : ℝ) ^ α * B ^ γ.primeFactors.card *
          ∏ p ∈ T \ γ.primeFactors, weil p
      ≤ ∏ p ∈ T, ((1 / (1 - (2:ℝ)^(-α))) * B * (p : ℝ) ^ (1 - α) + weil p) := by
  -- Apply the regrouping step `h_sum_prod` to rewrite the LHS.
  have h_sum_prod : ∑ γ ∈ (Finset.Icc 1 N).filter (fun γ => γ.primeFactors ⊆ T),
        (radical γ : ℝ) / (γ : ℝ) ^ α * B ^ γ.primeFactors.card *
          ∏ p ∈ T \ γ.primeFactors, weil p
      = ∑ R ∈ Finset.powerset T, (∑ γ ∈ (Finset.Icc 1 N).filter (fun γ => γ.primeFactors = R), (radical γ : ℝ) / (γ : ℝ) ^ α) * B ^ R.card *
          ∏ p ∈ T \ R, weil p := by
            simp +decide only [sum_filter, sum_mul];
            rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
  rw [ h_sum_prod, Finset.prod_add ];
  refine Finset.sum_le_sum fun R hR => ?_;
  refine' mul_le_mul_of_nonneg_right _ ( Finset.prod_nonneg fun p hp => hweil p <| Finset.mem_sdiff.mp hp |>.1 );
  refine' le_trans ( mul_le_mul_of_nonneg_right ( sum_rad_div_rpow_le_pow R ( fun p hp => hT p ( Finset.mem_powerset.mp hR hp ) ) N α hα0 hα1 ) ( by positivity ) ) _;
  simp +decide [ mul_comm, mul_left_comm, Finset.prod_mul_distrib ]

/-!
## Granville–Kurlberg §4 large-divisor helpers

The two lemmas below are the elementary engines of the §4 large-divisor regime
(the regime where the sharp tuple count is *not* used).  The first inserts a
genuine `1/γ^α` decay factor into a crude count bound; the second absorbs the
resulting (super-polynomially divergent) Euler product into a `s_q^η` factor.
-/

/-- **Trivial γ-insertion.** In a band where `1 ≤ γ ≤ H^w`, a crude nonnegative
bound `A ≤ H^v` can be upgraded to a bound carrying a genuine `1/γ^α` decay,
`A ≤ H^(v + α·w) / γ^α`, for any `0 ≤ α`. The cost is inflating the `H`-exponent
by `α·w`. This is the elementary inequality `1 ≤ (H^w / γ)^α` used in
Granville–Kurlberg §4 to feed the *crude* tuple counts (e.g.
`countTuplesWithGammaProd_med_gamma`, `countTuplesWithGammaProd_large_gamma`)
into the fractional radical Euler engine `core_gamma_euler_sum_frac`. -/
lemma insert_gamma_denominator (γ H : ℕ) (hγ : 0 < γ) (hH : 0 < H)
    (v w α : ℝ) (hα : 0 ≤ α)
    (hbound : (γ : ℝ) ≤ (H : ℝ) ^ w) (A : ℝ) (hA : A ≤ (H : ℝ) ^ v) :
    A ≤ (H : ℝ) ^ (v + α * w) / (γ : ℝ) ^ α := by
  have hγ1 : (1 : ℝ) ≤ (γ : ℝ) := by exact_mod_cast hγ
  have hγ0 : (0 : ℝ) < (γ : ℝ) := by linarith
  have hH0 : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hHw_pos : (0 : ℝ) < (H : ℝ) ^ w := Real.rpow_pos_of_pos hH0 w
  have hratio : (1 : ℝ) ≤ (H : ℝ) ^ w / (γ : ℝ) := by
    rw [le_div_iff₀ hγ0]; linarith
  have hpow : (1 : ℝ) ≤ ((H : ℝ) ^ w / (γ : ℝ)) ^ α := Real.one_le_rpow hratio hα
  have hpoww : ((H : ℝ) ^ w) ^ α = (H : ℝ) ^ (α * w) := by
    rw [← Real.rpow_mul hH0.le, mul_comm]
  have key : (H : ℝ) ^ (v + α * w) / (γ : ℝ) ^ α
      = (H : ℝ) ^ v * ((H : ℝ) ^ w / (γ : ℝ)) ^ α := by
    rw [Real.div_rpow hHw_pos.le hγ0.le, hpoww, Real.rpow_add hH0]; ring
  rw [key]
  calc A ≤ (H : ℝ) ^ v := hA
    _ = (H : ℝ) ^ v * 1 := by ring
    _ ≤ (H : ℝ) ^ v * ((H : ℝ) ^ w / (γ : ℝ)) ^ α :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hH0.le v)

/-- **Sub-polynomial growth of a (possibly divergent) Euler product.**
If every factor of a finite product over primes `p ∈ S` is dominated by the
`η`-th power of an auxiliary quantity `sp p`, i.e. `1 + f p ≤ (sp p)^η`, then the
whole product is dominated by `(∏ sp)^η`. Applied with `sp p = s_p = p/|Ω_p|`
and `∏ sp = s_q`, this is the Granville–Kurlberg §4 absorption step: the (possibly
divergent) collision Euler product is bounded by `s_q^η` once each factor has been
reduced to `s_p^η` (e.g. via `1 + x ≤ exp x` together with `s_p ≤ 2` for all but
finitely many primes). -/
lemma euler_product_subpoly_growth (S : Finset ℕ) (f sp : ℕ → ℝ) (η : ℝ)
    (hsp : ∀ p ∈ S, 0 ≤ sp p) (hf0 : ∀ p ∈ S, 0 ≤ 1 + f p)
    (hf : ∀ p ∈ S, 1 + f p ≤ (sp p) ^ η) :
    ∏ p ∈ S, (1 + f p) ≤ (∏ p ∈ S, sp p) ^ η := by
  rw [← Real.finsetProd_rpow S sp hsp η]
  exact Finset.prod_le_prod hf0 hf

end PoissonCRT