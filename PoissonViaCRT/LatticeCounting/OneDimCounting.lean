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
# Module 3: OneDimCounting

## Goal
Formalize bounds on the number of solutions to 1D congruences within intervals, specifically handling the "zero-exclusion" boundary condition.

## Key Definitions & Lemmas:
- **`count_congruence_interval`**: The number of $x \in [A, A+S]$ such that $x \equiv c \pmod M$ is bounded by $\lfloor S/M \rfloor + 1$.
- **`count_congruence_interval_strict`** *(Crucial for the $+1$ elimination)*: If we strictly restrict to solutions where $x \neq c$, and $c \in [A, A+S]$, then any valid $x$ satisfies $0 < |x - c| \le S$. Since $M \mid (x - c)$, this requires $M \le S$.
  The number of such solutions is strictly bounded by $2 \lfloor S/M \rfloor \le 2S/M$.
  *(This lemma formally decouples the boundary error from the main counting term).*
-/

namespace LatticeCounting

end LatticeCounting
