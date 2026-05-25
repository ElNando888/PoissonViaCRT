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
import PoissonViaCRT.LatticeCounting.SimultaneousCongruences
import PoissonViaCRT.LatticeCounting.OneDimCounting
import PoissonViaCRT.LatticeCounting.SequentialCounting
import Mathlib

/-!
# Module 5: BoxCollisionIntegration

## Goal
Tie the previous modules together to prove `box_collision_sum_bound` from `BoxCollisionHelpers.lean`.

## Implementation Hints (for Aristotle):
To prove `box_collision_sum_bound`, please follow this exact roadmap:

1. **Indicator Bound**: Apply `Finset.prod_le_prod` with `collision_indicator_le_sum_pairs` to bound the product of indicators by a product of sums.
2. **Expansion**: Use `Finset.prod_sum` (Mathlib) to convert the product of sums into a sum over choice functions `σ ∈ U.pi (fun _ => pairsBelow m)`.
3. **Swap Sums**: Use `Finset.sum_comm` to push the sum over `h` to the inside.
4. **CRT Grouping**: For a fixed `σ`, group the primes `p ∈ U` by their target coordinate `j = (σ p).2`. Apply `LatticeCounting.crt_partition` to convert the multiple prime congruences into a single congruence modulo `M_j = ∏_{p ∈ U.filter (fun p => (σ p).2 = j)} p`.
5. **Sequential Counting**: Apply `LatticeCounting.seq_bound_nat` to count the valid tuples `h`.
6. **1D Bound**: For each coordinate `j`, apply `LatticeCounting.count_congruence_interval_strict` to bound the number of valid choices for `h j` by `2S / M_j`.
   *(Note: The strictness condition `h j ≠ h i` is guaranteed by `inScaledBox_cons_strictMono`, which forbids equality between coordinates).*
7. **Re-collapse**: The resulting product over `j` is bounded by `(2S)^m / ∏_{p ∈ U} p`. Pull this out of the `σ` sum, and use `Finset.sum_const` or `Finset.prod_sum` in reverse to see that the sum over `σ` contributes a factor of `(pairsBelow m).card` per prime, which defines `C_gamma`.
-/

namespace PoissonCRT

end PoissonCRT

/-
PROVIDED SOLUTION

Please formalize `Module 5: BoxCollisionIntegration` in `PoissonViaCRT/BoxCollisionIntegration.lean`.
The goal is to provide the proof of `box_collision_sum_bound` which currently resides as a `sorry` in `BoxCollisionHelpers.lean`.

To keep the repository structure clean:
1. Provide the proof of `box_collision_sum_bound` directly inside `BoxCollisionIntegration.lean`.
2. Remove the `sorry` definition of `box_collision_sum_bound` from `BoxCollisionHelpers.lean` entirely.

The docstring in `BoxCollisionIntegration.lean` has been updated with a very precise 7-step roadmap. It explicitly names the Mathlib theorems (e.g., `Finset.prod_sum`, `Finset.sum_comm`) and the custom `LatticeCounting` lemmas (`crt_partition`, `seq_bound_nat`, etc.) you should string together.

Take your time to map the intermediate sums carefully. Good luck!
-/
