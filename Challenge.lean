import PoissonViaCRT.MainDefs

open Classical
open PoissonCRT

lemma GK08_prop_11_lpbb (m : ℕ) (X : Box m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Fin m → ℝ), (∀ i, 0 ≤ v i ∧ v i ≤ 1) → ∀ (s : ℝ), 1 ≤ s →
      |(((Fintype.piFinset fun _ : Fin m =>
          Finset.Icc (1 : ℤ) ⌈s * ∑ i, X.sides i⌉).filter
        (fun h => inScaledBox X s v h)).card : ℝ) - s ^ m * X.volume| ≤
        C * s ^ ((m : ℤ) - 1) := by
  sorry

lemma GK08_prop_11_sfell (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 2 ≤ k)
    (Ω : ∀ p : ℕ, Finset (ZMod p))
    (hΩ : ∀ p, p.Prime → (Ω p).Nonempty)
    (hsp : ∀ (p : ℕ), p.Prime →
      (p : ℝ) / (Ω p).card ≤ (p : ℝ) ^ (lambdaExponent k - ε)) :
    ε ≤ lambdaExponent k := by
  sorry

lemma GK08_prop_11_afoeel (ε : ℝ) (k : ℕ) (hk : 2 ≤ k)
    (Ω : ∀ p : ℕ, Finset (ZMod p))
    (hΩ : ∀ p, p.Prime → (Ω p).Nonempty)
    (hsp : ∀ (p : ℕ), p.Prime →
      (p : ℝ) / (Ω p).card ≤ (p : ℝ) ^ (lambdaExponent k - ε))
    (heq : ε = lambdaExponent k) :
    ∀ (p : ℕ), p.Prime → (Ω p).card = p := by
  sorry

lemma GK08_prop_11_cfoaf (q : ℕ) [NeZero q]
    (Ω : ∀ p : ℕ, Finset (ZMod p))
    (hall : ∀ (p : ℕ), p.Prime → (Ω p).card = p) :
    (crtSubset q Ω).card = q := by
  sorry

lemma GK08_prop_11_dzoceq {k : ℕ} (hk : 2 ≤ k) (q : ℕ) [NeZero q]
    (Ω : ∀ p : ℕ, Finset (ZMod p)) (X : Box (k - 1))
    (hfull : (crtSubset q Ω).card = q) :
    let Ω_q := crtSubset q Ω
    let s := (q : ℝ) / Ω_q.card
    |(1 / (Ω_q.card : ℝ)) *
      ∑ h ∈ ((Fintype.piFinset fun _ : Fin (k - 1) =>
          Finset.Icc (1 : ℤ) ⌈s * ∑ i, X.sides i⌉).filter
        (fun h => inScaledBox X s (fun _ => 0) h)),
      ((tupleCount Ω_q (Fin.cons (0 : ZMod q) fun i => (h i : ZMod q)) : ℝ) -
        (Ω_q.card : ℝ) ^ k / (q : ℝ) ^ (k - 1))| * s = 0 := by
  sorry

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
  sorry
