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

import Mathlib

/-!
# Module 1: ProdSumExpansion

## Goal
Provide ergonomic lemmas for expanding products of sums into sums over choice functions.

While Mathlib has `Finset.prod_sum`, it is often clunky because it maps into `Fintype.pi` over the entire type. We need a version localized to `Finset`s.

## Key Definitions & Lemmas:
- `def ChoiceFun (U : Finset α) (I : Finset β) := { f : α → β // ∀ x ∈ U, f x ∈ I }`
- **`prod_sum_choice`**:
  $$ \prod_{p \in U} \sum_{i \in I} f(p, i) = \sum_{\sigma \in \text{ChoiceFun}(U, I)} \prod_{p \in U} f(p, \sigma(p)) $$
- **`sum_swap_choice`**: Bounding the swapped sums:
  $$ \sum_{h \in X} \sum_{\sigma} \prod_{p} f(h, p, \sigma(p)) = \sum_{\sigma} \sum_{h \in X} \prod_{p} f(h, p, \sigma(p)) $$
-/

namespace LatticeCounting

end LatticeCounting
