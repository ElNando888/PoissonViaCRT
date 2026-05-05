# Poisson Statistics via the Chinese Remainder Theorem

A formalization in Lean 4 of the paper **"Poisson statistics via the Chinese remainder theorem"** by Andrew Granville and Pär Kurlberg.

## Overview

This repository contains a formalization of the main results from the paper [arXiv:math/0412135v2](https://arxiv.org/abs/math/0412135). The project focuses on the $k$-level correlation of subsets of integers constructed via the Chinese Remainder Theorem (CRT) and proving they exhibit Poisson statistics under certain well-distribution hypotheses.

### Key Results Formalized
- **Main Theorem 1.1 (Theorem 3.7):** Precise bound on the $k$-level correlation $R_k(X, \Omega_q)$.
- **Lemma 3.5:** Average of the error term $\epsilon_k$ is zero.
- **CRT Multiplicativity:** The counting function $N_k$ behaves multiplicatively over squarefree $q$.
- **Möbius Synthesis:** The decomposition of the total deviation into local prime contributions.

**Note:** This effort doesn't aspire to be *the* Lean formalization of the paper. It was born of the need to provide supporting evidence to my original work in [BeyondCramer](https://github.com/ElNando888/BeyondCramer). I will keep improving the implementation as far as I can, and hopefully, some of this work will prove useful when someone attempts to formalize the paper in a more comprehensive (and mathlib-compliant) way.

## Tools and Methodology

This formalization was developed using a tandem approach between human mathematicians and AI agents:
- **Gemini 3.1 Pro:** Utilized for the high-level blueprinting of the formalization strategy and complex prompt design.
- **Claude Opus 4.6:** Utilized for code review and complex prompt design.
- **Aristotle:** An AI coding assistant by [Harmonic](https://aristotle.harmonic.fun) that co-authored the Lean source code, assisting with tactic automation, proof synthesis, and infrastructure maintenance.

## Project Status

### Scope Limitations
- **Corollary 1.2:** The formalization of Corollary 1.2 (regarding $d$-th powers) was ultimately removed from the project scope. The `RiemannHypothesisCurves` repository, which was intended to provide the necessary hyperelliptic curve machinery, proved to be ill-equipped for this specific application at the current stage.

### Remaining Tasks (TODOs)
Several components are marked with `TODO` in the codebase, indicating areas requiring further infrastructure or proof refinement:
- **Algebraic Cancellation:** Refining the cancellation argument to support the general $s^{-\delta}$ error form in `MainTheorem.lean`.
- **Discrete Geometry:** Implementing Davenport's Principle for lattice point counts in boxes where the period $d$ exceeds the scale $s$ (`MobiusSynthesis.lean`).
- **Fourier Analysis:** Integrating $L_2$ variance bounds (Fourier ANOVA) to close the $k=2$ case, where pointwise estimates are insufficient (`MobiusSynthesis.lean`).
- **Euler Weights:** Generalizing convergent Euler product bounds for the $k \ge 3$ synthesis.
- **Iwaniec-Kowalski Integration:** Chapters 3 & 4 of Iwaniec-Kowalski are required for certain character sum estimates. We are currently deferring this effort to wait for [Alex Kontorovich's ongoing project](https://leanprover.zulipchat.com/#narrow/channel/423402-PrimeNumberTheorem.2B/topic/IwaniecKowalski) on the Prime Number Theorem.

## Repository Structure
- `PoissonViaCRT/Defs.lean`: Core definitions ($N_k$, $\Omega_q$, $R_k$).
- `PoissonViaCRT/MainTheorem.lean`: Precise versions of Theorem 1.1 and supporting lemmas.
- `PoissonViaCRT/MobiusSynthesis.lean`: The primary framework for the deviation synthesis.
- `PoissonViaCRT/LatticePointBound.lean`: Counting lattice points in rescaled boxes.

## References
- Granville, A., & Kurlberg, P. (2004). *Poisson statistics via the Chinese remainder theorem*. arXiv:math/0412135.
- Iwaniec, H., & Kowalski, E. (2004). *Analytic Number Theory*. American Mathematical Society.
