import PoissonViaCRT.FourierANOVABasic
import PoissonViaCRT.FourierANOVA
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset BigOperators Classical Real

namespace PoissonCRT

/--
The $L^1$-norm of the $m$-dimensional box indicator Fourier transform over a subgrid of spacing $q/d$.
For $d | q$, this bounds the sum over $\xi \in (ZMod d)^m$ of the DFT of the box indicator.
-/
public lemma box_fourier_l1_bound (q d : ℕ) [NeZero q] [NeZero d] (hd : d ∣ q) (m : ℕ)
    (X_sides : Fin m → ℕ) (h_sides : ∀ i, X_sides i ≤ q) :
    ∑ a : Fin m → ZMod d, ‖dft q m (fun x => if (∀ i, (x i).val ∈ Finset.Icc 1 (X_sides i)) then (1 : ℂ) else 0)
      (fun i => (((a i).val * (q / d) : ℕ) : ZMod q))‖
    ≤ ∏ i : Fin m, ((X_sides i : ℝ) / q + (d : ℝ) / q * Real.log d + (d : ℝ) / q) := by
  sorry

end PoissonCRT
