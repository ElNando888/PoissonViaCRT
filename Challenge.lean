import PoissonViaCRT.MainDefs

open PoissonCRT

public theorem mainTheorem
    (ε : ℝ) (hε : 0 < ε) (K : ℕ) (hK : 2 ≤ K)
    (Ω : ∀ p : ℕ, Finset (ZMod p))
    (hΩ : ∀ p, p.Prime → (Ω p).Nonempty)
    (hWD : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), k ≤ K →
      WellDistributed ε p (Ω p) k)
    (hsp : ∀ (p : ℕ), p.Prime →
      (p : ℝ) / (Ω p).card ≤ (p : ℝ) ^ (lambdaExponent K - ε))
    (hrp : ∀ (k : ℕ), 2 ≤ k → k ≤ K → ∀ (p : ℕ), p.Prime → 1 - (Ω p).card / (p : ℝ) ≤ k / (p : ℝ)) :
    ∀ (k : ℕ), 2 ≤ k → k ≤ K → ∀ (X : Box (k - 1)),
      ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (_hq_sq : Squarefree q),
        |kCorrelation (crtSubset q Ω) X - X.volume| ≤
          C * ((q : ℝ) / (crtSubset q Ω).card) ^ (-δ) := by
  sorry
