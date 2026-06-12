import Mathlib

open Classical


namespace PoissonCRT

/-- The counting function for `k`-tuples mod `q` (Definition from §1).
Given `Ω ⊆ ℤ/qℤ` and offsets `h : Fin k → ℤ/qℤ`,
$$N_k(\mathbf{h}, \Omega) = \#\{ t \in \mathbb{Z}/q\mathbb{Z} :
  t + h_i \in \Omega \text{ for all } 0 \le i \le k-1 \}.$$
The paper convention is `h 0 = 0`, so that the condition includes `t ∈ Ω`. -/
def tupleCount {q : ℕ} [NeZero q] (Ω : Finset (ZMod q)) (h : Fin k → ZMod q) : ℕ :=
  sorry

/-- The CRT subset construction (§1). Given a family of subsets `Ω p ⊆ ℤ/pℤ` for each prime `p`,
the CRT subset `Ω_q ⊆ ℤ/qℤ` for squarefree `q` consists of those `x` whose reduction
modulo `p` lies in `Ω p` for every prime factor `p` of `q`. -/
noncomputable def crtSubset (q : ℕ) [NeZero q] (Ω : ∀ p : ℕ, Finset (ZMod p)) :
    Finset (ZMod q) :=
  sorry

/-! ### Boxes in `ℝ^{k-1}` (§2)

A box `B(b₁, …, bₖ₋₁) ⊂ ℝ^{k-1}` is defined as:
$$B(b_1, \ldots, b_{k-1}) = \{ x \in \mathbb{R}^{k-1} :
  0 < x_i - x_{i-1} \le b_i, \, i = 1, \ldots, k-1 \}$$
where `x₀ = 0`. We represent a box by its side lengths. -/

/-- A box `B(b₁, …, bₖ₋₁) ⊂ ℝ^{k-1}` with positive side lengths. -/
structure Box (k : ℕ) where
  /-- The side lengths `b₁, …, bₖ₋₁`. -/
  sides : Fin k → ℝ
  /-- All side lengths are positive. -/
  sides_pos : ∀ i, 0 < sides i

/-- The volume of a box `B(b₁, …, bₖ₋₁)` is `∏ᵢ bᵢ`. -/
noncomputable def Box.volume {k : ℕ} (B : Box k) : ℝ :=
  sorry

/-- A lattice point `h ∈ ℤ^{k-1}` belongs to the scaled box `s · X` if
`0 < h_i - h_{i-1} ≤ s · b_i` for all `i`, where `h₀ = 0`. -/
def inScaledBox {k : ℕ} (B : Box k) (s : ℝ) (v : Fin k → ℝ) (h : Fin k → ℤ) : Prop :=
  sorry

/-- The `k`-level correlation `R_k(X, Ω_q)` for a box `X` and subset `Ω ⊆ ℤ/qℤ` (§2).
`R_k(X, Ω_q) = (1/|Ω_q|) ∑_{h ∈ s_q X ∩ ℤ^{k-1}} N_{k+1}((0, h₁,…,hₖ), Ω_q)`

We express the correlation as a sum over integer tuples `h` lying in the scaled box `s_q · X`,
where `s_q = q / |Ω|` is the average spacing. The tuple count uses `Fin.cons 0 h` to
incorporate the implicit `h₀ = 0` from the paper's convention, so that `N_{k+1}` counts
`t ∈ Ω` with `t + hᵢ ∈ Ω` for all `i`. -/
noncomputable def kCorrelation {q : ℕ} [NeZero q]
    (Ω : Finset (ZMod q)) (X : Box k) : ℝ :=
  sorry

/-- **Hypothesis (1)** from Theorem 1: For each integer `k`, the `k`-tuple counting function
satisfies `N_k(h, Ω_p) = r_p^k · p · (1 + O_k((1-r_p) · p^{-ε}))` provided that
`0, h₁, …, h_{k-1}` are distinct mod `p`.

Formally: `|N_k(h, Ω_p) - |Ω_p|^k / p^{k-1}| ≤ C_k · (1 - |Ω_p|/p) · p^{-ε} ·
|Ω_p|^k / p^{k-1}` for all injective `h`. -/
def WellDistributed (ε : ℝ) (p : ℕ) [Fact p.Prime] (Ω : Finset (ZMod p)) (k : ℕ) : Prop :=
  sorry

/-- The critical exponent `λ_k = min_τ (k-1-v(τ))/w(τ)` from §3.2.
For `k ≥ 4`, `λ_k = 1/(k-1)`.-/
noncomputable def lambdaExponent (k : ℕ) : ℝ :=
  sorry


lemma lattice_point_box_bound (m : ℕ) (X : Box m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Fin m → ℝ), (∀ i, 0 ≤ v i ∧ v i ≤ 1) → ∀ (s : ℝ), 1 ≤ s →
      |(((Fintype.piFinset fun _ : Fin m =>
          Finset.Icc (1 : ℤ) ⌈s * ∑ i, X.sides i⌉).filter
        (fun h => inScaledBox X s v h)).card : ℝ) - s ^ m * X.volume| ≤
        C * s ^ ((m : ℤ) - 1) := by
  sorry

lemma spacing_forces_eps_le_lambda (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 2 ≤ k)
    (Ω : ∀ p : ℕ, Finset (ZMod p))
    (hΩ : ∀ p, p.Prime → (Ω p).Nonempty)
    (hsp : ∀ (p : ℕ), p.Prime →
      (p : ℝ) / (Ω p).card ≤ (p : ℝ) ^ (lambdaExponent k - ε)) :
    ε ≤ lambdaExponent k := by
  sorry

lemma all_full_of_eps_eq_lambda (ε : ℝ) (k : ℕ) (hk : 2 ≤ k)
    (Ω : ∀ p : ℕ, Finset (ZMod p))
    (hΩ : ∀ p, p.Prime → (Ω p).Nonempty)
    (hsp : ∀ (p : ℕ), p.Prime →
      (p : ℝ) / (Ω p).card ≤ (p : ℝ) ^ (lambdaExponent k - ε))
    (heq : ε = lambdaExponent k) :
    ∀ (p : ℕ), p.Prime → (Ω p).card = p := by
  sorry

lemma crtSubset_full_of_all_full (q : ℕ) [NeZero q]
    (Ω : ∀ p : ℕ, Finset (ZMod p))
    (hall : ∀ (p : ℕ), p.Prime → (Ω p).card = p) :
    (crtSubset q Ω).card = q := by
  sorry

lemma deviation_zero_of_card_eq_q {k : ℕ} (hk : 2 ≤ k) (q : ℕ) [NeZero q]
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

theorem mainTheorem_precise
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

end PoissonCRT
