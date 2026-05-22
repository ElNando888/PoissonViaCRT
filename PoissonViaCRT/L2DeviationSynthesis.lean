/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela
-/

module
import PoissonViaCRT.Defs
import PoissonViaCRT.GammaDeviationHelpers
import PoissonViaCRT.GammaRangeSum

/-!
# Second Moment Method for Large Divisors (L2 Deviation Synthesis)

This file implements the Cauchy-Schwarz/Variance bounds needed to control the
large-divisor tail in the error term of the Granville–Kurlberg theorem (GK08 §3.1).

## Main Results

* `deviation_L2_variance_bound`: Uses Gamma-structure collision counting to bound
  the variance `∑_h (∏_T (N_p(h) - μ_p))^2`.
* `deviation_L1_le_L2`: The Cauchy-Schwarz step converting the L1 deviation to the
  L2 variance: `|∑_h f(h)| ≤ (∑_h 1)^{1/2} · (∑_h f(h)^2)^{1/2}`.
* `deviation_large_divisors_L2`: The final per-T pointwise bound.

## Motivation

An earlier attempt in `GammaDeviationSynthesis.lean` failed because it applied the
triangle inequality *before* the Gamma-counting, bounding `∑_h ∏_T |N_p(h) - μ_p|`.
This lost the essential cancellation in the $h$-sum and led to an exponentially divergent
sum. By instead squaring the sum (where terms are inherently non-negative) and applying
Gamma-counting to the variance, we preserve the cancellation.
-/

open Finset BigOperators Classical

namespace PoissonCRT

/-! ## 1. Squared Local Deviation -/

/- Define the squared terms and prove their basic properties. -/

-- (Aristotle will fill in the definitions and lemmas here)

end PoissonCRT
