import PoissonViaCRT.FourierANOVABasic
import PoissonViaCRT.FourierANOVA
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset BigOperators Classical Real

namespace PoissonCRT

/--
The `m`-dimensional DFT of a box indicator factors as a product of `1`-dimensional DFTs.

This is the analogue of `dft_boxIndicator_eq_prod` for an integer-sided box indicator
`fun x => if (∀ i, (x i).val ∈ Finset.Icc 1 (X_sides i)) then 1 else 0`, which is realised as
`boxIndicator q m B 1` for the box with sides `X_sides i + 1/2`
(so that `⌊1 * (X_sides i + 1/2)⌋₊ = X_sides i`).
-/
lemma dft_intBox_eq_prod (q : ℕ) [NeZero q] (m : ℕ)
    (X_sides : Fin m → ℕ) (ξ : Fin m → ZMod q) :
    dft q m (fun x => if (∀ i, (x i).val ∈ Finset.Icc 1 (X_sides i)) then (1 : ℂ) else 0) ξ
    = ∏ j : Fin m, dft q 1
        (fun x => if (x 0).val ∈ Finset.Icc 1 (X_sides j) then (1 : ℂ) else 0)
        (fun _ => ξ j) := by
  set B : Box m := ⟨fun i => (X_sides i : ℝ) + 1 / 2, fun i => by positivity⟩ with hB
  have hfloor : ∀ i, ⌊(1 : ℝ) * B.sides i⌋₊ = X_sides i := by
    intro i
    rw [hB, one_mul, Nat.floor_eq_iff (by positivity)]
    refine ⟨by push_cast; linarith, by push_cast; linarith⟩
  have hfun : (fun x => if (∀ i, (x i).val ∈ Finset.Icc 1 (X_sides i)) then (1 : ℂ) else 0)
      = boxIndicator q m B 1 := by
    funext x
    unfold boxIndicator
    simp only [hfloor]
  rw [hfun, dft_boxIndicator_eq_prod]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  simp only [hfloor]

/--
The $L^1$-norm of the $m$-dimensional box indicator Fourier transform over a subgrid of spacing $q/d$.
For $d | q$, this bounds the sum over $\xi \in (ZMod d)^m$ of the DFT of the box indicator.

The hypothesis `h_sides : ∀ i, X_sides i ≤ q` is part of the requested interface but turns out to be
unnecessary for the bound, which holds for arbitrary side lengths.
-/
public lemma box_fourier_l1_bound (q d : ℕ) [NeZero q] [NeZero d] (hd : d ∣ q) (m : ℕ)
    (X_sides : Fin m → ℕ) (h_sides : ∀ i, X_sides i ≤ q) :
    ∑ a : Fin m → ZMod d, ‖dft q m (fun x => if (∀ i, (x i).val ∈ Finset.Icc 1 (X_sides i)) then (1 : ℂ) else 0)
      (fun i => (((a i).val * (q / d) : ℕ) : ZMod q))‖
    ≤ ∏ i : Fin m, ((X_sides i : ℝ) / q + (d : ℝ) / q * Real.log d + (d : ℝ) / q) := by
  -- Abbreviate the 1D summand.
  set f : Fin m → ZMod d → ℝ := fun j a =>
    ‖dft q 1 (fun x => if (x 0).val ∈ Finset.Icc 1 (X_sides j) then (1 : ℂ) else 0)
      (fun _ => (((a.val * (q / d) : ℕ) : ZMod q)))‖
  have key : ∑ a : Fin m → ZMod d, ‖dft q m
      (fun x => if (∀ i, (x i).val ∈ Finset.Icc 1 (X_sides i)) then (1 : ℂ) else 0)
      (fun i => (((a i).val * (q / d) : ℕ) : ZMod q))‖
      = ∏ j : Fin m, ∑ a : ZMod d, f j a := by
    rw [Finset.prod_univ_sum, ← Fintype.piFinset_univ (α := Fin m) (β := fun _ => ZMod d)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [dft_intBox_eq_prod, norm_prod]
  rw [key]
  refine Finset.prod_le_prod (fun j _ => ?_) (fun j _ => ?_)
  · exact Finset.sum_nonneg (fun a _ => norm_nonneg _)
  · exact dft_interval_subgrid_bound q d hd (X_sides j)

end PoissonCRT
