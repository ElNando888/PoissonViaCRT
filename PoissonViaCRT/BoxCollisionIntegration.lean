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
import PoissonViaCRT.LatticeCounting.ProdSumExpansion
import PoissonViaCRT.LatticeCounting.SimultaneousCongruences
import PoissonViaCRT.LatticeCounting.OneDimCounting
import PoissonViaCRT.LatticeCounting.SequentialCounting
import Mathlib

/-!
# Module 5: BoxCollisionIntegration

## Goal
Tie the previous modules together to prove `box_collision_sum_bound`.

## Proof Path:
1. Apply `collision_indicator_le_sum_pairs` to bound the product of indicators.
2. Apply `prod_sum_choice` (Module 1) to convert the product-of-sums into a sum over choice functions $\sigma : U \to \text{pairsBelow}$.
3. For a fixed $\sigma$, use `crt_partition` (Module 2) to group primes into $M_j$, establishing a single congruence constraint for each $h_j$.
4. Apply `count_congruence_interval_strict` (Module 3), leveraging `inScaledBox_cons_strictMono` to ensure $h_j \neq h_i$, to bound the choices for $h_j$ by $2S/M_j$.
5. Use `seq_bound` (Module 4) to multiply these 1D bounds sequentially, yielding the multi-dimensional bound $(2S)^m / \prod p$.
6. Sum over the choice functions to get the final result $C_{\text{box}} s^m \prod (C_\gamma / p)$.
-/
