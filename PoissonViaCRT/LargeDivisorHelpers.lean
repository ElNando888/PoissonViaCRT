/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela
-/

import PoissonViaCRT.MobiusInfra
import PoissonViaCRT.CRTMultiplicativity
import PoissonViaCRT.ProductDifference
import PoissonViaCRT.MobiusBounds
import PoissonViaCRT.HardCaseSynthesis
import PoissonViaCRT.ScaledBoxVariation
import PoissonViaCRT.MobiusOptimization
import PoissonViaCRT.MobiusTauIntegration
import PoissonViaCRT.FourierANOVA

set_option linter.unusedVariables false

/-!
# Helper lemmas for `large_divisor_per_T_bound`

This file provides the main technical ingredients used to close the per-`T`
pointwise bound in `MobiusSynthesis.lean`:

1. `scaled_box_card_le` — lattice-point counting bound for the box `S`.
2. `inScaledBox_strictMono` — elements of the box form a strictly increasing
   sequence starting above 0.
3. `inScaledBox_le_sum_sides` — every coordinate is bounded by `s · ∑ b_i`.
4. `fin_cons_castHom_injective` — the `Fin.cons 0 h` tuple is injective modulo
   any prime `p` larger than the ceiling bound.
5. `localCount_deviation_weil` — the Weil-type bound on `|N_p − μ_p|` for large
   primes, obtained from the `WellDistributed` hypothesis.
6. `deviation_prod_pointwise_le` — per-`h` pointwise bound on the product of
   deviations over `T`, splitting `T` into small and large primes.
-/

open Finset BigOperators Classical

namespace PoissonCRT

/-! ## 1. Box cardinality bound -/

/-
The number of lattice points in the scaled box `S` is at most
`(X.volume + C_lp) * s ^ (k - 1)` for `s ≥ 1` and `k ≥ 2`.
-/
lemma scaled_box_card_le {k : ℕ} (hk : 2 ≤ k) (X : Box (k - 1)) (C_lp : ℝ)
    (hC_lp_pos : 0 < C_lp)
    (hC_lp : ∀ (v : Fin (k - 1) → ℝ), (∀ i, 0 ≤ v i ∧ v i ≤ 1) → ∀ (s : ℝ), 1 ≤ s →
      |(((Fintype.piFinset fun _ : Fin (k - 1) =>
          Finset.Icc (1 : ℤ) ⌈s * ∑ i, X.sides i⌉).filter
        (fun h => inScaledBox X s v h)).card : ℝ) - s ^ (k - 1 : ℕ) * X.volume| ≤
        C_lp * s ^ (((k - 1 : ℕ) : ℤ) - 1))
    (s : ℝ) (hs : 1 ≤ s) :
    (((Fintype.piFinset fun _ : Fin (k - 1) =>
        Finset.Icc (1 : ℤ) ⌈s * ∑ i, X.sides i⌉).filter
      (fun h => inScaledBox X s (fun _ => 0) h)).card : ℝ) ≤
    (X.volume + C_lp) * s ^ (k - 1 : ℕ) := by
  -- Apply the lemma hC_lp with v = 0 and s ≥ 1.
  have h_card : |((#({h ∈ Fintype.piFinset fun x => Icc 1 ⌈s * ∑ i, X.sides i⌉ | inScaledBox X s (fun _ => 0) h}) : ℝ) - s ^ (k - 1) * X.volume)| ≤ C_lp * s ^ ((k - 1 : ℕ) - 1 : ℤ) := by
    exact hC_lp _ ( fun _ => ⟨ by norm_num, by norm_num ⟩ ) _ hs;
  rcases k with ( _ | _ | k ) <;> norm_num at *;
  norm_num [ pow_succ, abs_le ] at *;
  nlinarith [ pow_le_pow_right₀ hs k.zero_le, show 0 ≤ X.volume from Finset.prod_nonneg fun _ _ => le_of_lt ( X.sides_pos _ ) ]

/-! ## 2. Box monotonicity and bounds -/

/-
Elements of the scaled box (with offset `v = 0`) form a strictly increasing
sequence of positive integers: `0 < h 0 < h 1 < ⋯ < h (n-1)`.
-/
lemma inScaledBox_strictMono {n : ℕ} (hn : 1 ≤ n) (X : Box n) (s : ℝ) (h : Fin n → ℤ)
    (hbox : inScaledBox X s (fun _ => 0) h) :
    StrictMono h ∧ (0 : ℤ) < h ⟨0, by omega⟩ := by
  refine' ⟨ fun i j hij => _, _ ⟩;
  · induction' j with j hj generalizing i;
    induction' j with j hj generalizing i;
    · tauto;
    · have := hbox ⟨ j + 1, by linarith ⟩ ; norm_num at *;
      grind;
  · have := hbox ⟨ 0, hn ⟩ ; aesop;

/-
Every coordinate of an element of the scaled box is bounded by
`s * ∑ i, X.sides i`.
-/
lemma inScaledBox_le_sum_sides {n : ℕ} (hn : 1 ≤ n) (X : Box n) (s : ℝ) (hs : 0 < s)
    (h : Fin n → ℤ) (hbox : inScaledBox X s (fun _ => 0) h) (i : Fin n) :
    (h i : ℝ) ≤ s * ∑ j, X.sides j := by
  have h_le_sum : ∀ i : Fin n, (h i : ℝ) ≤ s * ∑ j ∈ Finset.Iic i, X.sides j := by
    intro i
    induction' i with i ih;
    induction' i with i ih;
    · have := hbox ⟨ 0, ih ⟩ ; simp_all +decide only [sub_zero, ↓reduceIte, Int.cast_pos, ge_iff_le];
      exact le_trans this.2 ( mul_le_mul_of_nonneg_left ( Finset.single_le_sum ( fun a _ => le_of_lt ( X.sides_pos a ) ) ( by simp ) ) hs.le );
    · have := hbox ⟨ i + 1, ih ⟩;
      rw [ show ( Finset.Iic ⟨ i + 1, ih ⟩ : Finset ( Fin n ) ) = Finset.Iic ⟨ i, by linarith ⟩ ∪ { ⟨ i + 1, ih ⟩ } from ?_, Finset.sum_union ] <;> norm_num at *;
      · linarith [ ‹∀ ( ih : i < n ), ( h ⟨ i, ih ⟩ : ℝ ) ≤ s * ∑ j ∈ Iic ⟨ i, ih ⟩, X.sides j› ( Nat.lt_of_succ_lt ih ) ];
      · grind;
  exact le_trans ( h_le_sum i ) ( mul_le_mul_of_nonneg_left ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_univ _ ) fun _ _ _ => le_of_lt ( X.sides_pos _ ) ) hs.le )

/-! ## 3. Injectivity of Fin.cons 0 h modulo large primes -/

/-
When `p` exceeds `⌈s * ∑ sides⌉` and `h` is in the scaled box, the tuple
`Fin.cons 0 (fun i => (h i : ZMod q))` projected to `ZMod p` is injective.
Uses `inScaledBox_strictMono` and `inScaledBox_le_sum_sides`.
-/
lemma fin_cons_castHom_injective {n : ℕ} (hn : 1 ≤ n) (q : ℕ) [NeZero q]
    (X : Box n) (s : ℝ) (hs : 0 < s) (p : ℕ) (hp : Nat.Prime p)
    (hp_dvd : p ∣ q)
    (hp_large : (⌈s * ∑ i, X.sides i⌉₊ : ℕ) < p)
    (h : Fin n → ℤ)
    (hbox : inScaledBox X s (fun _ => 0) h) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    let g : Fin (n + 1) → ZMod q :=
      Fin.cons (0 : ZMod q) (fun j : Fin n => (h j : ZMod q))
    Function.Injective (fun i : Fin (n + 1) =>
      ZMod.castHom hp_dvd (ZMod p) (g i)) := by
  intro i j hij
  simp at hij ⊢;
  -- Since $p$ is prime and $p > \lceil s \sum_{i} X.sides i \rceil$, the values $h_i$ are distinct modulo $p$.
  have h_distinct_mod_p : ∀ i j : Fin n, i ≠ j → ¬(h i : ZMod p) = (h j : ZMod p) := by
    have h_distinct_mod_p : ∀ i j : Fin n, i ≠ j → ¬(h i : ℤ) ≡ (h j : ℤ) [ZMOD p] := by
      intros i j hij h_eq_mod_p
      have h_eq : h i = h j := by
        have h_eq : |(h i : ℤ) - (h j : ℤ)| < p := by
          have h_eq : ∀ i : Fin n, 0 < h i ∧ h i ≤ ⌈s * ∑ i, X.sides i⌉₊ := by
            intros i
            have h_pos : 0 < h i := by
              have := inScaledBox_strictMono hn X s h hbox; exact this.2.trans_le ( this.1.monotone ( Nat.zero_le _ ) ) ;
            have h_le : h i ≤ ⌈s * ∑ i, X.sides i⌉₊ := by
              have h_le : (h i : ℝ) ≤ s * ∑ i, X.sides i := by
                exact inScaledBox_le_sum_sides hn X s hs h hbox i;
              exact_mod_cast h_le.trans ( Nat.le_ceil _ )
            exact ⟨h_pos, h_le⟩;
          exact abs_sub_lt_iff.mpr ⟨ by linarith [ h_eq i, h_eq j ], by linarith [ h_eq i, h_eq j ] ⟩;
        exact eq_of_sub_eq_zero ( by simpa [ sub_eq_iff_eq_add ] using Int.modEq_iff_dvd.mp h_eq_mod_p.symm |> fun ⟨ k, hk ⟩ => by nlinarith [ show k = 0 by nlinarith [ abs_lt.mp h_eq ] ] );
      -- Since $h$ is strictly monotone, if $h i = h j$, then $i = j$, contradicting $hij$.
      have h_strict_mono : StrictMono h := by
        exact inScaledBox_strictMono hn X s h hbox |>.1;
      exact hij ( h_strict_mono.injective h_eq );
    simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ];
  rcases j with ⟨ _ | j, hj ⟩ <;> rcases hij with ⟨ _ | hij, hij ⟩ <;> norm_num at *;
  · have h_pos : 0 < h ⟨‹_›, by linarith⟩ := by
      exact inScaledBox_strictMono hn X s h hbox |>.2.trans_le ( inScaledBox_strictMono hn X s h hbox |>.1.monotone ( Nat.zero_le _ ) );
    have h_lt_p : (h ⟨‹_›, by linarith⟩ : ℤ) < p := by
      have h_lt_p : (h ⟨‹_›, by linarith⟩ : ℝ) ≤ s * ∑ i, X.sides i := by
        apply inScaledBox_le_sum_sides hn X s hs h hbox ⟨_, by linarith⟩;
      exact_mod_cast h_lt_p.trans_lt ( Nat.lt_of_ceil_lt hp_large );
    have h_cast_ne_zero : ∀ (x : ℤ), 0 < x → x < p → (x : ZMod p) ≠ 0 := by
      intro x hx_pos hx_lt_p hx_zero; haveI := Fact.mk hp; simp_all +decide [ ZMod.intCast_zmod_eq_zero_iff_dvd ] ;
      linarith [ Int.le_of_dvd hx_pos hx_zero ];
    simp +zetaDelta at *;
    erw [ Fin.cons ] ; aesop;
  · have h_cast_ne_zero : ¬(h ⟨j, by linarith⟩ : ZMod p) = 0 := by
      have h_cast_ne_zero : 0 < h ⟨j, by linarith⟩ ∧ h ⟨j, by linarith⟩ < p := by
        have := inScaledBox_strictMono hn X s h hbox;
        exact ⟨ this.1.monotone ( Nat.zero_le _ ) |> lt_of_lt_of_le this.2, by have := inScaledBox_le_sum_sides hn X s hs h hbox ⟨ j, by linarith ⟩ ; exact_mod_cast this.trans_lt ( Nat.lt_of_ceil_lt hp_large ) ⟩;
      rw [ ZMod.intCast_zmod_eq_zero_iff_dvd ] ; exact fun h => by linarith [ Int.le_of_dvd ( by linarith ) h ] ;
    simp +decide [ i ];
    simp +decide [ Fin.cons ] ; aesop;
  · have h_cast : ∀ (x : ℤ), (x : ZMod q).cast = (x : ZMod p) := by
      cases q <;> cases p <;> aesop;
    exact fun h => Classical.not_not.1 fun h' => h_distinct_mod_p ⟨ j, by linarith ⟩ ⟨ _, by linarith ⟩ ( by simpa [ Fin.ext_iff ] using h' ) <| h_cast _ ▸ h_cast _ ▸ h

/-! ## 4. Weil bound for large primes -/

/-
For a large prime `p > ⌈s * ∑ sides⌉` and `h` in the scaled box, the local
counting function satisfies the Weil-type bound
  `|localCount − localMean| ≤ (1 − |Ω_p|/p) · p^{−ε} · localMean`.
This follows from the `WellDistributed` hypothesis applied to the injective
tuple from `fin_cons_castHom_injective`.
-/
lemma localCount_deviation_weil (ε : ℝ) {n : ℕ} (hn : 1 ≤ n)
    (Ω : ∀ p : ℕ, Finset (ZMod p)) (q : ℕ) [NeZero q]
    (X : Box n) (s : ℝ) (hs : 0 < s)
    (p : ℕ) (hp_prime : Nat.Prime p) (hp_factor : p ∈ q.primeFactors)
    (hp_large : (⌈s * ∑ i, X.sides i⌉₊ : ℕ) < p)
    (hWD : @WellDistributed ε p ⟨hp_prime⟩ (Ω p) (n + 1))
    (h : Fin n → ℤ)
    (hbox : inScaledBox X s (fun _ => 0) h) :
    |localCount Ω q (Fin.cons (0 : ZMod q) (fun i => (h i : ZMod q))) p -
      localMean (n + 1) Ω p| ≤
    (1 - (Ω p).card / (p : ℝ)) * (p : ℝ) ^ (-ε) * localMean (n + 1) Ω p := by
  unfold localCount localMean; simp +decide [ *, Fin.cons ] ;
  convert hWD.1 _ _ using 1;
  convert fin_cons_castHom_injective hn q X s hs p hp_prime ( Nat.dvd_of_mem_primeFactors hp_factor ) ( mod_cast hp_large ) h hbox using 1

/-! ## 5. Per-`h` pointwise bound on the deviation product -/

/-
For each lattice point `h` in the box, the absolute value of the product
`∏_{p ∈ T} (localCount − localMean)` is bounded by the product of the trivial
bound over small primes times the Weil bound over large primes.
-/
lemma deviation_prod_pointwise_le (ε : ℝ) {n : ℕ} (hn : 1 ≤ n)
    (Ω : ∀ p : ℕ, Finset (ZMod p)) (q : ℕ) [NeZero q]
    (X : Box n) (s : ℝ) (hs : 0 < s)
    (hWD : ∀ (p : ℕ) [Fact p.Prime], WellDistributed ε p (Ω p) (n + 1))
    (T : Finset ℕ) (hT : T ⊆ q.primeFactors)
    (B_max : ℕ) (hB : B_max = ⌈s * ∑ i, X.sides i⌉₊)
    (h : Fin n → ℤ)
    (hbox : inScaledBox X s (fun _ => 0) h) :
    |∏ p ∈ T, (localCount Ω q (Fin.cons (0 : ZMod q) (fun i => (h i : ZMod q))) p -
        localMean (n + 1) Ω p)| ≤
    (∏ p ∈ T.filter (· ≤ B_max), (p : ℝ)) *
    (∏ p ∈ T.filter (B_max < ·),
      (1 - (Ω p).card / (p : ℝ)) * (p : ℝ) ^ (-ε) * localMean (n + 1) Ω p) := by
  -- Split the product into two parts: one over primes in T that are less than or equal to B_max, and the other over primes in T that are greater than B_max.
  have h_split : ∏ p ∈ T, (localCount Ω q (Fin.cons 0 (fun i => (h i : ZMod q))) p - localMean (n + 1) Ω p) = (∏ p ∈ T.filter (fun p => p ≤ B_max), (localCount Ω q (Fin.cons 0 (fun i => (h i : ZMod q))) p - localMean (n + 1) Ω p)) * (∏ p ∈ T.filter (fun p => B_max < p), (localCount Ω q (Fin.cons 0 (fun i => (h i : ZMod q))) p - localMean (n + 1) Ω p)) := by
    rw [ ← Finset.prod_union ( Finset.disjoint_filter.mpr fun _ _ _ => by linarith ) ] ; congr ; ext ; by_cases h : ‹ℕ› ≤ B_max <;> aesop;
  -- Apply the bounds to each part of the product.
  have h_bounds : ∀ p ∈ T.filter (fun p => p ≤ B_max), |localCount Ω q (Fin.cons 0 (fun i => (h i : ZMod q))) p - localMean (n + 1) Ω p| ≤ (p : ℝ) := by
    intros p hp
    apply abs_localCount_sub_localMean_le_p (by linarith) q p (hT (Finset.mem_filter.mp hp).left) Ω (Fin.cons 0 (fun i => (h i : ZMod q)));
  have h_bounds_large : ∀ p ∈ T.filter (fun p => B_max < p), |localCount Ω q (Fin.cons 0 (fun i => (h i : ZMod q))) p - localMean (n + 1) Ω p| ≤ (1 - (Ω p).card / (p : ℝ)) * (p : ℝ) ^ (-ε) * localMean (n + 1) Ω p := by
    intro p hp;
    convert localCount_deviation_weil ε hn Ω q X s hs p ( Nat.prime_of_mem_primeFactors ( hT ( Finset.mem_filter.mp hp |>.1 ) ) ) ( hT ( Finset.mem_filter.mp hp |>.1 ) ) _ _ h hbox using 1;
    · grind;
    · grind;
  rw [ h_split, abs_mul, Finset.abs_prod, Finset.abs_prod ];
  exact mul_le_mul ( Finset.prod_le_prod ( fun _ _ => abs_nonneg _ ) h_bounds ) ( Finset.prod_le_prod ( fun _ _ => abs_nonneg _ ) h_bounds_large ) ( Finset.prod_nonneg fun _ _ => abs_nonneg _ ) ( Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _ )

end PoissonCRT
