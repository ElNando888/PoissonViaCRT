import PoissonViaCRT.MainDefs
import PoissonViaCRT.MainTheorem

open Classical
open PoissonCRT

lemma GK08_prop_11_lpbb (m : ℕ) (X : Box m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Fin m → ℝ), (∀ i, 0 ≤ v i ∧ v i ≤ 1) → ∀ (s : ℝ), 1 ≤ s →
      |(((Fintype.piFinset fun _ : Fin m =>
          Finset.Icc (1 : ℤ) ⌈s * ∑ i, X.sides i⌉).filter
        (fun h => inScaledBox X s v h)).card : ℝ) - s ^ m * X.volume| ≤
        C * s ^ ((m : ℤ) - 1) := by
  exact lattice_point_box_bound m X

theorem GK08_thm_12
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
  exact PoissonCRT.mainTheorem_precise ε hε K hK Ω hΩ hWD hsp hrp
