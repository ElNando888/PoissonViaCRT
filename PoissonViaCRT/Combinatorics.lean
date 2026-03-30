/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import PoissonViaCRT.Defs

/-!
# Combinatorics of Gamma Structures (§3.1)

This file formalizes the combinatorial machinery from Section 3.1 of
"Poisson statistics via the Chinese remainder theorem" by Granville–Kurlberg.

## Main Results

* `PoissonCRT.GammaStructure.gammaProd_perm_invariant`: The product `γ(Γ)` is invariant under
  permutations (unnumbered lemma in §3.1).
* `PoissonCRT.countGammaStructures_le`: Bound on the number of Gamma structures with given
  `γ(Γ) = γ` (Lemma 3.1).
* `PoissonCRT.countTuples_bound_prop`: Upper bound on `M_Γ(H)` (Proposition 3.2).
* `PoissonCRT.countTuples_bound_cor`: Corollary 3.3: Refined bound on `M_Γ(H)`.

## References

* [A. Granville, P. Kurlberg, *Poisson statistics via the Chinese remainder theorem*]
  [arXiv:math/0412135v2], §3.1
-/

open Finset BigOperators Nat

namespace PoissonCRT

variable {k : ℕ}

/-! ### Permutation of Gamma structures -/

/-- Apply a permutation `σ` of `{0, …, k-1}` to a Gamma structure. The permuted structure
has `γ^(σ)_{i,j} = γ_{σ(i), σ(j)}`. -/
def GammaStructure.permute (Γ : GammaStructure k) (σ : Equiv.Perm (Fin k)) :
    GammaStructure k where
  gamma i j := Γ.gamma (σ i) (σ j)
  symm i j := Γ.symm (σ i) (σ j)
  pos i j hij := Γ.pos (σ i) (σ j) (by intro h; exact hij (σ.injective h))
  sqfree i j hij := Γ.sqfree (σ i) (σ j) (by intro h; exact hij (σ.injective h))
  compat i j l hij hjl hil := Γ.compat (σ i) (σ j) (σ l)
    (by intro h; exact hij (σ.injective h))
    (by intro h; exact hjl (σ.injective h))
    (by intro h; exact hil (σ.injective h))

/-! ### Permutation invariance of `γ(Γ)` -/

/-
PROBLEM
The compatibility condition implies that "p divides γ_{i,j}" is transitive:
if `p | γ_{i,j}` and `p | γ_{j,l}` then `p | γ_{i,l}`.

PROVIDED SOLUTION
From the compatibility condition: gcd(gamma i j, gamma j l) | gamma i l. Since p | gamma i j and p | gamma j l, we have p | gcd(gamma i j, gamma j l). Since gcd divides gamma i l, by transitivity p | gamma i l.
-/
lemma GammaStructure.prime_dvd_trans (Γ : GammaStructure k)
    {p : ℕ} (hp : Nat.Prime p) {i j l : Fin k}
    (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l)
    (h1 : p ∣ Γ.gamma i j) (h2 : p ∣ Γ.gamma j l) :
    p ∣ Γ.gamma i l := by
  exact dvd_trans ( Nat.dvd_gcd h1 h2 ) ( Γ.compat i j l hij hjl hil )

/-
PROBLEM
The gammaRow of a GammaStructure is squarefree: `gammaRow j` is the lcm of squarefree
numbers, hence squarefree.

PROVIDED SOLUTION
gammaRow j = (Finset.Iio j).lcm (fun i => Γ.gamma i j). This is the lcm of squarefree numbers. The lcm of squarefree numbers is squarefree because for each prime p, the p-adic valuation of the lcm is the max of the p-adic valuations of the inputs, each of which is ≤ 1. Use Nat.squarefree_iff_prime_squarefree or Squarefree.lcm or similar.
-/
lemma GammaStructure.gammaRow_squarefree (Γ : GammaStructure k) (j : Fin k) :
    Squarefree (Γ.gammaRow j) := by
  -- The least common multiple of squarefree numbers is squarefree.
  have h_lcm_sqfree : ∀ {S : Finset ℕ}, (∀ s ∈ S, Squarefree s) → Squarefree (Finset.lcm S id) := by
    -- The least common multiple of squarefree numbers is squarefree because for each prime p, the p-adic valuation of the lcm is the max of the p-adic valuations of the inputs, each of which is ≤ 1.
    intros S hS
    have h_lcm_sqfree : ∀ p : ℕ, Nat.Prime p → (Nat.factorization (Finset.lcm S id)) p ≤ 1 := by
      intros p hp
      have h_lcm_sqfree : ∀ s ∈ S, (Nat.factorization s) p ≤ 1 := by
        exact fun s hs => Nat.le_of_not_lt fun h => hp.not_dvd_one <| by have := hS s hs; exact absurd ( this.natFactorization_le_one p ) ( by aesop ) ;
      induction S using Finset.induction <;> simp_all +decide [ Nat.factorization_lcm ];
      by_cases h : ‹ℕ› = 0 <;> by_cases h' : Finset.lcm ‹_› id = 0 <;> simp_all +decide [ GCDMonoid.lcm, Nat.factorization_lcm ];
      have := hS.2 0 h'; simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd, hp.ne_one ] ;
    rw [ Nat.squarefree_iff_prime_squarefree ];
    -- If $x^2$ divides the lcm, then the exponent of $x$ in the lcm's factorization must be at least 2.
    intro x hx_prime hx_div
    have h_exp : (Nat.factorization (Finset.lcm S id)) x ≥ 2 := by
      obtain ⟨ k, hk ⟩ := hx_div;
      rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.factorization_eq_zero_iff, Nat.Prime.ne_zero ];
      exact absurd ( hS 0 hk ) ( by norm_num );
    linarith [ h_lcm_sqfree x hx_prime ];
  convert h_lcm_sqfree _;
  rw [ Finset.lcm_image ];
  congr! 1;
  simp +zetaDelta at *;
  exact fun i hi => Γ.sqfree i j ( ne_of_lt hi )

/-
PROBLEM
For a squarefree gammaRow, the p-adic valuation is 0 or 1.

PROVIDED SOLUTION
gammaRow j is squarefree by gammaRow_squarefree. For squarefree n, Nat.factorization n p ≤ 1. This follows from the definition of squarefree (or Nat.Squarefree.factorization_le_one).
-/
lemma GammaStructure.factorization_gammaRow_le_one (Γ : GammaStructure k)
    (j : Fin k) (p : ℕ) :
    Nat.factorization (Γ.gammaRow j) p ≤ 1 := by
  -- Since gammaRow j is squarefree, its factorization is at most 1 for all primes p.
  exact (gammaRow_squarefree Γ j).natFactorization_le_one p

/-
PROBLEM
The p-adic valuation of `gammaRow j` is 1 iff there exists `i < j` with `p | gamma i j`,
and 0 otherwise.

PROVIDED SOLUTION
gammaRow j = (Finset.Iio j).lcm (fun i => Γ.gamma i j).

By gammaRow_squarefree, gammaRow j is squarefree. So its factorization at p is either 0 or 1.

factorization (gammaRow j) p = 1 iff p | gammaRow j iff p | lcm_{i < j} gamma(i,j) iff ∃ i < j, p | gamma(i,j).

For the lcm divisibility: p | lcm S f iff ∃ s ∈ S, p | f s. This holds because:
- Forward: if p | lcm, then since lcm = ∏ primes..., p appears in the factorization. Since each f s is squarefree, p | f s for some s ∈ S.
- Backward: if p | f s for some s ∈ S, then f s | lcm, so p | lcm.

Use Finset.dvd_lcm for the backward direction. For the forward direction, use the fact that lcm divides the product (or use prime factorization).

Actually, for the forward: hp.dvd_lcm (Finset.Iio j) (fun i => Γ.gamma i j) or similar. We need p | Finset.lcm S f → ∃ s ∈ S, p | f s. This is true for prime p when all f s are nonzero: use Nat.Prime.dvd_lcm_iff or similar.

The factorization value is:
- 1 if ∃ i ∈ Iio j, p | gamma i j (using squarefreeness to get ≤ 1)
- 0 otherwise
-/
lemma GammaStructure.factorization_gammaRow_eq (Γ : GammaStructure k)
    (j : Fin k) (p : ℕ) (hp : Nat.Prime p) :
    Nat.factorization (Γ.gammaRow j) p =
      if ∃ i ∈ Finset.Iio j, p ∣ Γ.gamma i j then 1 else 0 := by
  split_ifs with h;
  · -- Since there exists $i < j$ such that $p \mid \gamma_{i,j}$, the lcm of $\gamma_{i,j}$ for $i < j$ must be divisible by $p$.
    have h_lcm_div : p ∣ Γ.gammaRow j := by
      exact dvd_trans h.choose_spec.2 ( Finset.dvd_lcm h.choose_spec.1 );
    exact Nat.factorization_eq_one_of_squarefree (gammaRow_squarefree Γ j) hp h_lcm_div;
  · simp_all +decide [ Nat.factorization_eq_zero_iff, GammaStructure.gammaRow ];
    refine' Or.inl _;
    intro H;
    have := Nat.dvd_trans H ( Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi ) ; simp_all +decide [ Nat.Prime.dvd_iff_not_coprime hp ] ;
    exact this <| Nat.Coprime.prod_right fun i hi => h i <| Finset.mem_Iio.mp hi

/-
PROBLEM
The p-adic valuation of `gammaProd` counts the number of indices `j` for which
there exists `i < j` with `p | gamma i j`.

PROVIDED SOLUTION
gammaProd = ∏ j : Fin k, gammaRow j.

Nat.factorization (∏ j, gammaRow j) p = ∑ j, Nat.factorization (gammaRow j) p
(by Nat.factorization_prod, since each gammaRow j is nonzero, which follows from gammaRow ≥ 1).

By factorization_gammaRow_eq, each summand is (if ∃ i ∈ Iio j, p | gamma i j then 1 else 0).

So the sum = ∑ j, (if ∃ i ∈ Iio j, p | gamma i j then 1 else 0) = card of the filter set.

Use Finset.sum_boole or similar to convert the sum to a cardinality.
-/
lemma GammaStructure.factorization_gammaProd_eq (Γ : GammaStructure k)
    (p : ℕ) (hp : Nat.Prime p) :
    Nat.factorization Γ.gammaProd p =
      (Finset.univ.filter fun j : Fin k => ∃ i ∈ Finset.Iio j, p ∣ Γ.gamma i j).card := by
  convert Finset.sum_congr rfl fun j _ => GammaStructure.factorization_gammaRow_eq Γ j p hp using 1;
  any_goals exact Finset.univ;
  · rw [ show Γ.gammaProd = ∏ j : Fin k, Γ.gammaRow j from rfl, Nat.factorization_prod ] ; aesop;
    intro j hj; have := Γ.gammaRow_squarefree j; aesop;
  · rw [ Finset.card_filter ]

/-
PROBLEM
For any equivalence relation on `Fin n`, the number of non-minimal elements
(i.e., elements `j` such that there exists a smaller equivalent element) equals
`n` minus the number of equivalence classes. In particular, this count depends only
on the partition structure, not on the linear order.

PROVIDED SOLUTION
For each j ∈ Fin n, define classMin(j) = min' (filter (fun i => R i j) univ) (nonempty by hrefl).

Claim: j satisfies "∃ i, i < j ∧ R i j" iff classMin(j) < j iff classMin(j) ≠ j.

This is because:
- If ∃ i < j with R i j, then classMin(j) ≤ i < j, so classMin(j) < j.
- If classMin(j) < j, then classMin(j) is in the filter (R classMin(j) j holds), so ∃ i < j with R i j.
- classMin(j) ≤ j always (since j is in the filter by hrefl).

So the LHS = #{j | classMin(j) ≠ j} = n - #{j | classMin(j) = j}.

The RHS = n - (image classMin univ).card.

We need: #{j | classMin(j) = j} = (image classMin univ).card.

This holds because: classMin is an idempotent function (classMin(classMin(j)) = classMin(j)). The image of classMin equals the set of fixed points of classMin. For any idempotent function on a finite set, |image| = #{fixed points}.

Proof of classMin idempotent: classMin(j) is the minimum of the class of j. The class of classMin(j) equals the class of j (since R is an equivalence relation: R classMin(j) j, so they're in the same class). Hence classMin(classMin(j)) = classMin(j).

Proof that image = fixed points for idempotent f:
- If y is in image(f), then y = f(x) for some x, so f(y) = f(f(x)) = f(x) = y.
- If f(y) = y, then y = f(y) is in image(f).

So (image classMin univ).card = #{j | classMin(j) = j}, and the equation follows.
-/
lemma card_filter_exists_lt_equiv {n : ℕ} (R : Fin n → Fin n → Prop)
    [DecidableRel R]
    (hrefl : ∀ i, R i i)
    (hsymm : ∀ i j, R i j → R j i)
    (htrans : ∀ i j l, R i j → R j l → R i l) :
    (Finset.univ.filter fun j : Fin n => ∃ i, i < j ∧ R i j).card =
      n - (Finset.univ.image fun j : Fin n =>
        (Finset.univ.filter fun i => R i j).min' ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrefl j⟩⟩).card := by
  -- To prove the equality of the cardinalities, we show that the sets are complementary.
  have h_complementary : Finset.filter (fun j => ∃ i < j, R i j) (Finset.univ : Finset (Fin n)) = Finset.univ \ Finset.image (fun j => Finset.min' (Finset.filter (fun i => R i j) (Finset.univ : Finset (Fin n))) ⟨j, by
    grind +splitImp⟩) (Finset.univ : Finset (Fin n)) := by
    all_goals generalize_proofs at *;
    ext j; simp [Finset.mem_image, Finset.mem_sdiff];
    constructor <;> intro h;
    · intro x hx; have := Finset.min'_mem ( Finset.filter ( fun i => R i x ) Finset.univ ) ; simp_all +decide [ Finset.min' ] ;
      contrapose! hx; simp_all +decide [ Finset.inf'_eq_csInf_image ] ;
      obtain ⟨ i, hi, hi' ⟩ := h; exact ne_of_lt ( lt_of_le_of_lt ( Finset.inf'_le _ <| by aesop ) hi ) ;
    · contrapose! h;
      use j; simp [Finset.min'];
      refine' le_antisymm _ _ <;> simp_all +decide [ Finset.inf'_le ];
      · exact ⟨ j, hrefl j, le_rfl ⟩;
      · exact fun i hi => le_of_not_gt fun hi' => h i hi' hi;
  rw [ h_complementary, Finset.card_sdiff ] ; norm_num [ Finset.card_univ ]

/-
PROBLEM
If two equivalence relations on `Fin n` are conjugate via a permutation `σ`,
then the images of the "class minimum" function have the same cardinality.

PROVIDED SOLUTION
We need to show that the images of the class minimum functions for R₁ and R₂ have the same cardinality.

Let classMin₁(j) = min' (filter (R₁ · j) univ) and classMin₂(j) = min' (filter (R₂ · j) univ).

Key properties of classMin (for any equivalence relation R with properties hrefl, hsymm, htrans):
1. classMin(j) ≤ j (since j is in the filter by hrefl)
2. R(classMin(j), j) (since classMin(j) is in the filter)
3. classMin(classMin(j)) = classMin(j) (idempotent):
   the class of classMin(j) = the class of j (by (2) and transitivity).
   So the filter for classMin(j) = the filter for j, hence min' is the same.
4. R(i, j) → classMin(i) = classMin(j):
   The class of i = the class of j, so the filters are the same.

Now the image of classMin = {m | classMin(m) = m} = set of fixed points of classMin.

We construct a bijection f : image(classMin₁) → image(classMin₂).

Define f(m) = classMin₂(σ m) for m in image(classMin₁).

This is well-defined (classMin₂(σ m) is always in image(classMin₂)).

Injectivity: If f(m₁) = f(m₂), i.e., classMin₂(σ m₁) = classMin₂(σ m₂), then σ m₁ and σ m₂ are in the same R₂-class (by property 4). So R₂(σ m₁, σ m₂). By hcompat, R₁(m₁, m₂). By property 4 for R₁, classMin₁(m₁) = classMin₁(m₂). Since m₁ and m₂ are fixed points (in the image), m₁ = classMin₁(m₁) = classMin₁(m₂) = m₂.

Surjectivity: For m' in image(classMin₂), let j' be such that classMin₂(j') = m'. Take m = classMin₁(σ⁻¹ j'). Then f(m) = classMin₂(σ m) = classMin₂(σ (classMin₁(σ⁻¹ j'))). Since classMin₁(σ⁻¹ j') and σ⁻¹ j' are R₁-equivalent, σ(classMin₁(σ⁻¹ j')) and j' are R₂-equivalent. So classMin₂(σ(classMin₁(σ⁻¹ j'))) = classMin₂(j') = m'.

So use Finset.card_bij with the bijection m ↦ classMin₂(σ m).
-/
lemma card_image_classMin_eq_of_perm {n : ℕ}
    (R₁ R₂ : Fin n → Fin n → Prop)
    [DecidableRel R₁] [DecidableRel R₂]
    (hrefl₁ : ∀ i, R₁ i i) (hsymm₁ : ∀ i j, R₁ i j → R₁ j i)
    (htrans₁ : ∀ i j l, R₁ i j → R₁ j l → R₁ i l)
    (hrefl₂ : ∀ i, R₂ i i) (hsymm₂ : ∀ i j, R₂ i j → R₂ j i)
    (htrans₂ : ∀ i j l, R₂ i j → R₂ j l → R₂ i l)
    (σ : Equiv.Perm (Fin n))
    (hcompat : ∀ i j, R₁ i j ↔ R₂ (σ i) (σ j)) :
    (Finset.univ.image fun j : Fin n =>
      (Finset.univ.filter fun i => R₁ i j).min'
        ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrefl₁ j⟩⟩).card =
    (Finset.univ.image fun j : Fin n =>
      (Finset.univ.filter fun i => R₂ i j).min'
        ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrefl₂ j⟩⟩).card := by
  fapply Finset.card_bij (fun m hm => Finset.min' (Finset.univ.filter fun i => R₂ i (σ m)) ⟨σ m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrefl₂ _⟩⟩);
  · aesop;
  · intros a₁ ha₁ a₂ ha₂ h_eq_min
    obtain ⟨j₁, hj₁⟩ : ∃ j₁, a₁ = Finset.min' (Finset.univ.filter fun i => R₁ i j₁) ⟨j₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrefl₁ j₁⟩⟩ := by
      aesop
    obtain ⟨j₂, hj₂⟩ : ∃ j₂, a₂ = Finset.min' (Finset.univ.filter fun i => R₁ i j₂) ⟨j₂, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrefl₁ j₂⟩⟩ := by
      rw [ Finset.mem_image ] at ha₂; obtain ⟨ j₂, _, rfl ⟩ := ha₂; exact ⟨ j₂, rfl ⟩ ;
    have h_eq_classes : R₂ (σ j₁) (σ j₂) := by
      have h_eq_classes : R₂ (σ a₁) (σ a₂) := by
        have h_eq_classes : R₂ (Finset.min' (Finset.univ.filter fun i => R₂ i (σ a₁)) ⟨σ a₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrefl₂ _⟩⟩) (σ a₁) ∧ R₂ (Finset.min' (Finset.univ.filter fun i => R₂ i (σ a₂)) ⟨σ a₂, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrefl₂ _⟩⟩) (σ a₂) := by
          exact ⟨ Finset.mem_filter.mp ( Finset.min'_mem ( Finset.univ.filter fun i => R₂ i ( σ a₁ ) ) ⟨ σ a₁, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hrefl₂ _ ⟩ ⟩ ) |>.2, Finset.mem_filter.mp ( Finset.min'_mem ( Finset.univ.filter fun i => R₂ i ( σ a₂ ) ) ⟨ σ a₂, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hrefl₂ _ ⟩ ⟩ ) |>.2 ⟩;
        grind +ring
      generalize_proofs at *; (
      have h_eq_classes : R₁ a₁ j₁ ∧ R₁ a₂ j₂ := by
        exact ⟨ hj₁.symm ▸ Finset.min'_mem _ _ |> fun x => by simpa using x, hj₂.symm ▸ Finset.min'_mem _ _ |> fun x => by simpa using x ⟩
      generalize_proofs at *; (
      grind +ring))
    have h_eq_classes' : R₁ j₁ j₂ := by
      exact hcompat _ _ |>.2 h_eq_classes
    have h_eq_classes'' : a₁ = a₂ := by
      have h_eq_classes'' : Finset.filter (fun i => R₁ i j₁) Finset.univ = Finset.filter (fun i => R₁ i j₂) Finset.univ := by
        grind +ring;
      simp_all +decide [ Finset.ext_iff ]
    exact h_eq_classes'';
  · simp +zetaDelta at *;
    intro a
    use σ⁻¹ a;
    congr! 3;
    have := Finset.min'_mem ( Finset.univ.filter fun i => R₁ i ( σ⁻¹ a ) ) ⟨ σ⁻¹ a, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hrefl₁ _ ⟩ ⟩ ; aesop;

/-- Two equivalence relations on `Fin n` that have the same equivalence classes (up to
bijection) yield the same count of non-minimal elements. -/
lemma card_filter_exists_lt_equiv_eq {n : ℕ}
    (R₁ R₂ : Fin n → Fin n → Prop)
    [DecidableRel R₁] [DecidableRel R₂]
    (hrefl₁ : ∀ i, R₁ i i) (hsymm₁ : ∀ i j, R₁ i j → R₁ j i)
    (htrans₁ : ∀ i j l, R₁ i j → R₁ j l → R₁ i l)
    (hrefl₂ : ∀ i, R₂ i i) (hsymm₂ : ∀ i j, R₂ i j → R₂ j i)
    (htrans₂ : ∀ i j l, R₂ i j → R₂ j l → R₂ i l)
    (σ : Equiv.Perm (Fin n))
    (hcompat : ∀ i j, R₁ i j ↔ R₂ (σ i) (σ j)) :
    (Finset.univ.filter fun j : Fin n => ∃ i, i < j ∧ R₁ i j).card =
    (Finset.univ.filter fun j : Fin n => ∃ i, i < j ∧ R₂ i j).card := by
  rw [card_filter_exists_lt_equiv R₁ hrefl₁ hsymm₁ htrans₁,
      card_filter_exists_lt_equiv R₂ hrefl₂ hsymm₂ htrans₂,
      card_image_classMin_eq_of_perm R₁ R₂ hrefl₁ hsymm₁ htrans₁ hrefl₂ hsymm₂ htrans₂ σ hcompat]

/-
PROBLEM
Key counting lemma: the number of elements `j` such that there exists `i < j`
in the same ~_p class equals `k - m_p` where `m_p` is the number of equivalence classes.
This count is determined by the unordered partition structure and is independent of
the linear order on `Fin k`.

More precisely: for any permutation σ, the number of j with "∃ i < j, p | gamma(σ i, σ j)"
equals the number of j with "∃ i < j, p | gamma(i, j)".

PROVIDED SOLUTION
Use card_filter_exists_lt_equiv_eq with:
- R₁(i, j) := (i = j) ∨ (i ≠ j ∧ p ∣ Γ.gamma i j)  [but actually we don't need the disjunction, we can use a simpler relation]
- R₂(i, j) := (i = j) ∨ (i ≠ j ∧ p ∣ Γ.gamma (σ i) (σ j))
- σ = σ

Wait, actually the statement of perm_count_eq is about "∃ i ∈ Iio j, p ∣ Γ.gamma (σ i) (σ j)" vs "∃ i ∈ Iio j, p ∣ Γ.gamma i j".

Note that "∃ i ∈ Iio j" is the same as "∃ i, i < j", and when i < j, i ≠ j.

Define R₁(i, j) := p ∣ Γ.gamma i j ∨ i = j and R₂(i, j) := p ∣ Γ.gamma (σ i) (σ j) ∨ i = j.

R₁ is an equivalence relation:
- Reflexive: R₁(i, i) by i = i.
- Symmetric: if p | gamma(i, j), then p | gamma(j, i) by Γ.symm; if i = j, trivial.
- Transitive: if R₁(i, j) and R₁(j, l), handle cases. If i = j or j = l, trivial. If p | gamma(i, j) and p | gamma(j, l), then by prime_dvd_trans, p | gamma(i, l).

R₂ is an equivalence relation by the same argument (it's R₁ for the permuted structure Γ.permute σ).

R₁(i, j) ↔ R₂(σ⁻¹ i) (σ⁻¹ j))... no, we need R₁(σ⁻¹ a, σ⁻¹ b) ↔ R₂(a, b). Or equivalently R₂(i, j) ↔ R₁(σ i, σ j). This is immediate from the definition since R₂(i, j) = p | gamma(σ i, σ j) ∨ i = j, and R₁(σ i, σ j) = p | gamma(σ i, σ j) ∨ σ i = σ j. Since σ is injective, i = j ↔ σ i = σ j. So R₂(i, j) ↔ R₁(σ i, σ j).

Now "∃ i < j, R₁(i, j) ∧ i ≠ j" ↔ "∃ i < j, p | gamma(i, j)" (since i < j implies i ≠ j, so R₁(i,j) simplifies to p | gamma(i, j)).

Similarly for R₂.

Apply card_filter_exists_lt_equiv_eq with σ = σ.

Note: "∃ i < j, R₁(i, j)" means "∃ i, i < j ∧ (p | gamma(i,j) ∨ i = j)" which simplifies to "∃ i, i < j ∧ p | gamma(i,j)" since i < j implies i ≠ j.

So the filter set for card_filter_exists_lt_equiv_eq is the same as what we want. Apply card_filter_exists_lt_equiv_eq and we're done.

The key step is converting between "∃ i ∈ Iio j, ..." and "∃ i, i < j ∧ ..." which is just membership in Iio.
-/
lemma GammaStructure.perm_count_eq (Γ : GammaStructure k)
    (σ : Equiv.Perm (Fin k)) (p : ℕ) (hp : Nat.Prime p) :
    (Finset.univ.filter fun j : Fin k =>
      ∃ i ∈ Finset.Iio j, p ∣ Γ.gamma (σ i) (σ j)).card =
    (Finset.univ.filter fun j : Fin k =>
      ∃ i ∈ Finset.Iio j, p ∣ Γ.gamma i j).card := by
  -- Define the equivalence relations R₁ and R₂ based on the divisibility condition.
  set R₁ : Fin k → Fin k → Prop := fun i j => p ∣ Γ.gamma i j ∨ i = j
  set R₂ : Fin k → Fin k → Prop := fun i j => p ∣ Γ.gamma (σ i) (σ j) ∨ i = j;
  -- Show that R₁ and R₂ are equivalence relations.
  have hR₁_equiv : Equivalence R₁ := by
    constructor;
    · aesop;
    · intro i j hij; cases hij <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero, Γ.symm ] ;
      · exact Or.inl ( Nat.dvd_of_mod_eq_zero ( by rw [ ← ‹Γ.gamma i j % p = 0›, Γ.symm ] ) );
      · exact Or.inr rfl;
    · intro i j l hij hjl; cases eq_or_ne i j <;> cases eq_or_ne j l <;> cases eq_or_ne i l <;> simp_all +decide [ Nat.Prime.dvd_mul ] ;
      · exact Or.inr rfl;
      · exact Or.inl <| GammaStructure.prime_dvd_trans Γ hp ‹_› ‹_› ‹_› ( hij.resolve_right ‹_› ) ( hjl.resolve_right ‹_› )
  have hR₂_equiv : Equivalence R₂ := by
    constructor;
    · aesop;
    · simp +zetaDelta at *;
      exact fun { x y } h => Or.imp ( fun h => by simpa only [ Γ.symm ] using h ) ( fun h => by simpa only [ eq_comm ] using h ) h;
    · intro i j k hi hj; cases hi <;> cases hj <;> simp_all +decide [ ← ZMod.natCast_eq_zero_iff ] ;
      · have := Γ.compat ( σ i ) ( σ j ) ( σ k ) ; simp_all +decide [ ZMod.natCast_eq_zero_iff ] ;
        by_cases hij : i = j <;> by_cases hjk : j = k <;> by_cases hik : i = k <;> simp_all +decide [ Nat.dvd_gcd_iff ];
        · exact Or.inr rfl;
        · exact Or.inl ‹_›;
        · aesop;
        · exact Or.inr rfl;
        · exact Or.inl ( dvd_trans ( Nat.dvd_gcd ‹_› ‹_› ) this );
      · exact Or.inl <| by rw [ ← ZMod.natCast_eq_zero_iff ] ; aesop;
      · rw [ ZMod.natCast_eq_zero_iff ] at * ; aesop;
      · exact Or.inr rfl;
  -- Show that R₁ and R₂ have the same equivalence classes.
  have hR₁R₂_classes : ∀ i j, R₁ i j ↔ R₂ (σ.symm i) (σ.symm j) := by
    aesop;
  -- Apply the lemma that states the number of non-minimal elements is the same for equivalent equivalence relations.
  have h_card_eq : (Finset.univ.filter (fun j => ∃ i, i < j ∧ R₁ i j)).card = (Finset.univ.filter (fun j => ∃ i, i < j ∧ R₂ i j)).card := by
    apply card_filter_exists_lt_equiv_eq;
    any_goals tauto;
    · exact fun i j hij => hR₁_equiv.symm hij;
    · exact fun i j l hij hjl => hR₁_equiv.trans hij hjl;
    · exact fun i j hij => hR₂_equiv.symm hij;
    · exact fun i j l hij hjl => hR₂_equiv.trans hij hjl;
  convert h_card_eq.symm using 2 <;> simp +decide [ Finset.mem_Iio ];
  · grind +qlia;
  · grind

/-
PROBLEM
`gammaProd` is nonzero.

PROVIDED SOLUTION
gammaProd = ∏ j : Fin k, gammaRow j. Each gammaRow j ≥ 1 (since gammaRow j = lcm of a set of positive integers, or if the set is empty, the empty lcm is 1). So the product is ≥ 1 > 0.

Actually, gammaRow ⟨0, _⟩ = (Iio 0).lcm (...) = 1 (empty lcm). For j > 0, gammaRow j = lcm of gamma(i,j) for i < j, each of which is positive by pos condition (i ≠ j since i < j). So gammaRow j ≥ 1.

Use Finset.prod_pos with gammaRow j > 0 for all j.
-/
lemma GammaStructure.gammaProd_pos (Γ : GammaStructure k) : 0 < Γ.gammaProd := by
  refine' Nat.pos_of_ne_zero _;
  refine' Finset.prod_ne_zero_iff.mpr _;
  intro j hj H; have := Γ.gammaRow_squarefree j; simp_all +decide [ Nat.factorization_eq_zero_iff ] ;

/-
PROBLEM
**Permutation invariance** (unnumbered lemma, §3.1):
If `σ` is a permutation of `{0, …, k-1}` with `σ(0) = 0`, then
`γ(Γ^(σ)) = γ(Γ)`.

The proof proceeds by showing that each prime's contribution to the factorization of
`γ(Γ)` counts elements that are not minimal in their `~_p` equivalence class,
which is a permutation-invariant quantity.

PROVIDED SOLUTION
Use Nat.eq_of_factorization_eq. The factorizations of (Γ.permute σ).gammaProd and Γ.gammaProd agree at every prime p.

Both are nonzero by gammaProd_pos.

For each prime p:
- factorization_gammaProd_eq gives factorization (Γ.permute σ).gammaProd p = card of filter set.
- The permuted structure's gamma is (Γ.permute σ).gamma i j = Γ.gamma (σ i) (σ j).
- So factorization ((Γ.permute σ).gammaProd) p = (univ.filter fun j => ∃ i ∈ Iio j, p ∣ Γ.gamma (σ i) (σ j)).card.
- By perm_count_eq, this equals (univ.filter fun j => ∃ i ∈ Iio j, p ∣ Γ.gamma i j).card.
- By factorization_gammaProd_eq, this equals factorization Γ.gammaProd p.

For non-prime p: factorization at non-prime p is always 0 for both sides.
-/
theorem GammaStructure.gammaProd_perm_invariant (hk : 0 < k) (Γ : GammaStructure k)
    (σ : Equiv.Perm (Fin k)) (hσ : σ ⟨0, hk⟩ = ⟨0, hk⟩) :
    (Γ.permute σ).gammaProd = Γ.gammaProd := by
  refine' Nat.factorization_inj _ _ _;
  · exact Nat.ne_of_gt ( GammaStructure.gammaProd_pos _ );
  · exact Nat.ne_of_gt ( GammaStructure.gammaProd_pos Γ );
  · ext p; by_cases hp : Nat.Prime p <;> simp_all +decide [ GammaStructure.factorization_gammaProd_eq ] ;
    convert GammaStructure.perm_count_eq Γ σ p hp using 1;
    · simp +decide [ GammaStructure.permute ];
    · simp +decide [ Finset.mem_Iio ]

/-! ### Bound on number of Gamma structures (Lemma 3.1) -/

/-
PROBLEM
**Lemma 3.1** (Gamma bound): The number of `GammaStructure`s with `γ(Γ) = γ`
is at most `∏_{p^e ∥ γ} S(k, k-e) ≤ C(k,2)^{Ω(γ)}`.

The proof: for each prime `p` dividing `γ`, we partition `{0, …, k-1}` into subsets
where `i` and `j` are in the same subset iff `p | γᵢⱼ` (consistency follows from the
compatibility condition). The number of such partitions is a Stirling number of the second
kind, bounded by `C(k, 2)^e`.

PROVIDED SOLUTION
We need: Set.ncard {Γ : GammaStructure k | Γ.gammaProd = γ} ≤ (k.choose 2) ^ γ.primeFactors.card.

A GammaStructure on Fin k has k.choose(2) = k*(k-1)/2 independent entries γ_{i,j} for pairs i < j.

For each GammaStructure Γ with gammaProd = γ, every γ_{i,j} divides γ(Γ) = γ (since gammaRow j = lcm_{i<j} γ_{i,j} and gammaProd = ∏_j gammaRow_j, so γ_{i,j} | gammaRow j | gammaProd).

Wait, that's not obvious. γ_{i,j} | lcm_{i'<j} γ_{i',j} = gammaRow j, and gammaRow j | ∏_j' gammaRow j' = gammaProd only if the product includes j. Since gammaProd = ∏_{j:Fin k} gammaRow j, yes gammaRow j | gammaProd. So γ_{i,j} | gammaProd = γ.

Since γ_{i,j} is squarefree and divides γ, γ_{i,j} is a squarefree divisor of γ. The number of squarefree divisors of γ equals 2^(γ.primeFactors.card).

So each pair (i,j) with i < j has at most 2^n choices (where n = γ.primeFactors.card), and there are k.choose(2) pairs. The total number of GammaStructures is at most (2^n)^(k choose 2) = 2^(n * k choose 2).

But we need the bound (k choose 2)^n, which is much smaller! So this simple counting doesn't work.

The correct bound comes from the observation that for each prime p | γ, the pattern of which pairs (i,j) have p | γ_{i,j} is constrained by the compatibility condition to form an equivalence relation. The number of equivalence relations on a k-set is the Bell number B(k). The paper claims B(k) ≤ k.choose(2) = k(k-1)/2. But B(3) = 5 and 3.choose(2) = 3, so B(k) > k.choose(2) for k ≥ 3!

Hmm, so the bound might actually be: for each prime p | γ with multiplicity e_p in γ(Γ), the Stirling number S(k, k-e_p) bounds the number of patterns. And ∏_p S(k, k-e_p) ≤ (k choose 2)^(sum e_p) because S(k, k-1) = k choose 2 and S(k, k-e) ≤ (k choose 2)^e.

But since each γ_{i,j} is squarefree, the valuation v_p(γ_{i,j}) ∈ {0,1}. And v_p(gammaRow j) = max(v_p(γ_{i,j}) : i < j) ∈ {0,1} (since lcm of squarefree numbers has exponent ≤ 1). So v_p(gammaProd) = #{j : ∃ i < j, p | γ_{i,j}} ≤ k-1.

For a fixed equivalence relation with m classes: v_p(gammaProd) = k - m. So if v_p(γ) = e, then the number of classes is m = k - e, and the number of equivalence relations with exactly m classes on k elements is S(k, m) = S(k, k-e). We need S(k, k-e) ≤ (k choose 2)^e.

For e=1: S(k, k-1) = k choose 2. ✓
For e=2: S(k, k-2) = 3*(k choose 3) + (k choose 2 choose 2). This should be ≤ (k choose 2)^2.

The product over all primes: ∏_p S(k, k-e_p) ≤ ∏_p (k choose 2)^(e_p) = (k choose 2)^(∑ e_p) = (k choose 2)^Ω(γ).

But Ω(γ) = sum of multiplicities, while γ.primeFactors.card = number of distinct prime factors. Since γ = gammaProd and each prime factor has multiplicity at most k-1 (since v_p(gammaProd) ≤ k-1), Ω(γ) ≥ γ.primeFactors.card.

So (k choose 2)^Ω(γ) ≥ (k choose 2)^(γ.primeFactors.card), and the bound we need is (k choose 2)^(γ.primeFactors.card), which is WEAKER than (k choose 2)^Ω(γ).

Actually wait, the statement says the bound is (k.choose 2) ^ γ.primeFactors.card. Since γ = gammaProd of some GammaStructure, and all γ_{i,j} are squarefree, and gammaRow j = lcm of squarefree numbers which is also squarefree (lcm of squarefree is squarefree), and gammaProd = product of squarefree numbers which is NOT necessarily squarefree!

So γ = gammaProd may not be squarefree. The number of distinct prime factors γ.primeFactors.card could be less than Ω(γ). We need the bound in terms of γ.primeFactors.card.

The product bound ∏_p S(k, k-e_p) ≤ (k choose 2)^(∑ e_p) = (k choose 2)^Ω(γ) is stronger than what we need. And (k choose 2)^Ω(γ) ≥ (k choose 2)^(γ.primeFactors.card) since Ω ≥ ω (number of distinct prime factors equals primeFactors.card).

So the argument works:
#{Γ : γ(Γ) = γ} ≤ ∏_p S(k, k-e_p) ≤ ∏_p (k choose 2)^e_p = (k choose 2)^Ω(γ) ≤ ...

But wait, we only need (k choose 2)^(γ.primeFactors.card), which is at most (k choose 2)^Ω(γ) only if k choose 2 ≥ 1, which is true for k ≥ 2.

Actually, for k < 2, k.choose 2 = 0, and we'd need 0^n = 0 ≥ ncard of the set. For k = 0 or k = 1, GammaStructure k has no pairs, so gammaProd = 1 (empty product). If γ ≠ 1, the set is empty and ncard = 0 ≤ 0^n (for n ≥ 1) or ≤ 0^0 = 1. If γ = 1, the set has one element and we need 0^0 = 1 ≥ 1. ✓

This is getting very complex to formalize. Let the subagent try.
-/
theorem countGammaStructures_le (γ : ℕ) (hγ : 0 < γ) :
    Set.ncard {Γ : GammaStructure k | Γ.gammaProd = γ} ≤
      (k.choose 2) ^ γ.primeFactors.card := by
  by_cases hk : 0 < k;
  · contrapose! hγ;
    rw [ Set.ncard_def ] at hγ;
    rw [ Set.encard_eq_top_iff.mpr ] at hγ;
    · aesop;
    · intro h;
      have h_infinite : Set.Infinite {Γ : GammaStructure k | Γ.gammaProd = γ} := by
        have h_infinite : ∀ n : ℕ, ∃ Γ : GammaStructure k, Γ.gammaProd = γ ∧ n < Γ.gamma ⟨0, hk⟩ ⟨0, hk⟩ := by
          intro n
          obtain ⟨Γ, hΓ⟩ : ∃ Γ : GammaStructure k, Γ.gammaProd = γ := by
            contrapose! hγ; aesop;
          use ⟨fun i j => if i = ⟨0, hk⟩ ∧ j = ⟨0, hk⟩ then n + 1 else Γ.gamma i j, by
            intro i j; by_cases hi : i = ⟨ 0, hk ⟩ <;> by_cases hj : j = ⟨ 0, hk ⟩ <;> simp +decide [ hi, hj, Γ.symm ] ;, by
            field_simp;
            exact fun i j hij => by rw [ if_neg ( by aesop ) ] ; exact Γ.pos i j hij;, by
            intro i j hij; by_cases hi : i = ⟨ 0, hk ⟩ <;> by_cases hj : j = ⟨ 0, hk ⟩ <;> simp_all +decide [ Nat.squarefree_mul_iff ] ;
            · exact Γ.sqfree _ _ ( by aesop );
            · exact Γ.sqfree _ _ ( by aesop );
            · exact Γ.sqfree i j hij, by
            intro i j l hij hjl hil; by_cases hi : i = ⟨ 0, hk ⟩ <;> by_cases hj : j = ⟨ 0, hk ⟩ <;> by_cases hl : l = ⟨ 0, hk ⟩ <;> simp +decide [ * ] ;
            lia;
            simp_all +decide [ Nat.gcd_dvd_left, Nat.gcd_dvd_right ];
            · exact Γ.compat _ _ _ ( by aesop ) ( by aesop ) ( by aesop );
            · exact Nat.gcd_dvd_left _ _;
            · exact Γ.compat i ⟨ 0, hk ⟩ l ( by aesop ) ( by aesop ) ( by aesop );
            · exact Γ.compat i j ⟨ 0, hk ⟩ ( by tauto ) ( by tauto ) ( by tauto );
            · exact Γ.compat i j l hij hjl hil⟩
          generalize_proofs at *;
          simp +decide [ *, GammaStructure.gammaProd ];
          convert hΓ using 1;
          refine' Finset.prod_congr rfl fun j hj => _;
          refine' Finset.lcm_congr _ _ <;> simp +decide [ GammaStructure.gammaRow ];
          aesop
        intro H;
        exact absurd ( Set.Finite.bddAbove ( H.image fun Γ => Γ.gamma ⟨ 0, hk ⟩ ⟨ 0, hk ⟩ ) ) ( by rintro ⟨ M, hM ⟩ ; obtain ⟨ Γ, hΓ₁, hΓ₂ ⟩ := h_infinite M; exact not_le_of_gt hΓ₂ ( hM <| Set.mem_image_of_mem _ hΓ₁ ) );
      exact h_infinite h;
  · rcases γ with ( _ | _ | γ ) <;> simp_all +decide;
    · rw [ Set.ncard_eq_one.mpr ];
      -- Since $k = 0$, the GammaStructure is trivial. The only possible GammaStructure is the one where all gamma values are 1.
      use ⟨fun _ _ => 1, by
        aesop, by
        bv_omega, by
        aesop, by
        aesop⟩
      generalize_proofs at *;
      ext ⟨gamma, symm, pos, sqfree, compat⟩; simp [GammaStructure.gammaProd];
      rcases k with ( _ | _ | k ) <;> simp_all +decide [ funext_iff ];
    · rw [ Set.ncard_def ];
      rw [ Set.encard_eq_zero.mpr ];
      · rfl;
      · ext Γ; simp [GammaStructure.gammaProd];
        cases Γ ; aesop

/-! ### Helper lemmas for Proposition 3.2 -/

/-
PROBLEM
Elements of a finite set in `[0, H]` whose pairwise differences are all divisible
by `m > 0` form a subset of an arithmetic progression, so the set has at most
`⌊H/m⌋ + 1 ≤ H/m + 1` elements.

PROVIDED SOLUTION
If S is empty, S.card = 0 ≤ H/m + 1 trivially (since H/m ≥ 0 and 1 > 0).

If S is nonempty, pick any x₀ ∈ S (use S.min'). For every x ∈ S, m ∣ (x - x₀) (by hdvd). Consider the map φ : S → ℤ given by φ(x) = (x - x₀) / m (exact division since m ∣ (x - x₀)). This map is injective: if (x - x₀)/m = (y - x₀)/m then x - x₀ = y - x₀ so x = y.

The image satisfies: for x ∈ S, 0 ≤ x and x ≤ H, and 0 ≤ x₀ and x₀ ≤ H. So 0 ≤ (x - x₀)/m (when x ≥ x₀, which holds since x₀ = min) and (x - x₀)/m ≤ H/m (since x - x₀ ≤ H - 0 = H).

So φ maps S injectively into Finset.Icc 0 (H/m). The cardinality of this target is at most H/m + 1 (as a nat). Cast to ℝ: S.card ≤ ⌊H/m⌋ + 1 ≤ H/m + 1 (using Nat.floor_le).

Actually, a cleaner approach: without defining φ explicitly, just note that S ⊆ {x₀, x₀ + m, x₀ + 2m, ...} ∩ [0, H]. The elements in [0, H] of the form x₀ + k*m for k ∈ ℤ satisfy 0 ≤ x₀ + k*m ≤ H, so -x₀/m ≤ k ≤ (H-x₀)/m. The number of such k is at most ⌊(H-x₀)/m⌋ - ⌈-x₀/m⌉ + 1 ≤ H/m + 1.

Simplest formal approach: use Finset.card_le_card with an injection into Finset.range (H/m + 1), mapping x to (x - x₀).toNat / m.
-/
lemma card_set_pairwise_dvd_le {m : ℕ} (hm : 0 < m) (H : ℕ)
    (S : Finset ℤ) (hS : ∀ x ∈ S, 0 ≤ x ∧ x ≤ H)
    (hdvd : ∀ x ∈ S, ∀ y ∈ S, (m : ℤ) ∣ (x - y)) :
    (S.card : ℝ) ≤ (H : ℝ) / m + 1 := by
  field_simp;
  norm_cast;
  by_cases hS_empty : S = ∅;
  · aesop;
  · -- Let $x₀$ be the minimum element of $S$.
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ ∈ S, ∀ x ∈ S, x₀ ≤ x := by
      exact ⟨ Finset.min' S ( Finset.nonempty_of_ne_empty hS_empty ), Finset.min'_mem _ _, fun x hx => Finset.min'_le _ _ hx ⟩;
    -- Since $S$ is a subset of $\{x₀, x₀ + m, x₀ + 2m, \ldots\}$, we can map each element $x \in S$ to $(x - x₀) / m$, which is an integer.
    have h_map : S.image (fun x => (x - x₀) / m) ⊆ Finset.Icc 0 (H / m) := by
      exact Finset.image_subset_iff.mpr fun x hx => Finset.mem_Icc.mpr ⟨ Int.ediv_nonneg ( sub_nonneg.mpr ( hx₀.2 x hx ) ) ( Nat.cast_nonneg _ ), Int.ediv_le_ediv ( by positivity ) ( by linarith [ hS x hx, hS x₀ hx₀.1 ] ) ⟩;
    have := Finset.card_le_card h_map; simp_all +decide [ Finset.card_image_of_injOn ] ;
    rw [ Finset.card_image_of_injOn ] at this;
    · nlinarith [ Int.toNat_of_nonneg ( by positivity : 0 ≤ ( H : ℤ ) / m + 1 ), Int.mul_ediv_add_emod H m, Int.emod_nonneg H ( by positivity : ( m : ℤ ) ≠ 0 ), Int.emod_lt_of_pos H ( by positivity : ( m : ℤ ) > 0 ) ];
    · intro x hx y hy; have := hdvd x hx y hy; aesop;

/-
PROBLEM
From the filter condition defining `countTuplesWithGamma`, if `h` satisfies the gcd
condition then `Γ.gamma i j` divides `h j - h i` for `i ≠ j`.

PROVIDED SOLUTION
From hgcd: Nat.gcd Γ.sqfreepart (Int.natAbs (h j - h i)) = Γ.gamma i j. Since gcd(a, b) divides b, we get Γ.gamma i j ∣ Int.natAbs (h j - h i). Then Int.natAbs_dvd or Int.ofNat_dvd gives (Γ.gamma i j : ℤ) ∣ (h j - h i).
-/
lemma gamma_dvd_of_gcd_eq {Γ : GammaStructure k} {h : Fin k → ℤ}
    {i j : Fin k} (hij : i ≠ j)
    (hgcd : Nat.gcd Γ.sqfreepart (Int.natAbs (h j - h i)) = Γ.gamma i j) :
    (Γ.gamma i j : ℤ) ∣ (h j - h i) := by
  exact Int.dvd_trans ( Int.natCast_dvd_natCast.mpr ( hgcd ▸ Nat.gcd_dvd_right _ _ ) ) ( by simp +decide [ Int.natAbs_dvd ] )

/-
PROBLEM
For tuples in `countTuplesWithGamma`, the set of valid values for coordinate `j`
(given all other coordinates) is contained in a single residue class modulo
`gammaRow j`. This is because `gammaRow j = lcm_{i<j} γ_{i,j}` and each
`γ_{i,j}` divides `h_j − h_i`, so the lcm divides any difference of valid `h_j` values.

PROVIDED SOLUTION
gammaRow j = (Finset.Iio j).lcm (fun i => Γ.gamma i j).

Need: (gammaRow j : ℤ) ∣ (h j - h' j).

Use Int.natCast_dvd_natCast and show gammaRow j ∣ Int.natAbs(h j - h' j), then convert.

For each i ∈ Iio j (i.e., i < j): from hgcd with hij = ne_of_lt (by exact i.prop... well i < j): gamma_dvd_of_gcd_eq gives (gamma i j : ℤ) ∣ (h j - h i). Similarly from hgcd': (gamma i j : ℤ) ∣ (h' j - h' i). Since heq gives h i = h' i for i < j, we have h' i = h i. So (gamma i j : ℤ) ∣ (h j - h i) and (gamma i j : ℤ) ∣ (h' j - h i). Therefore (gamma i j : ℤ) ∣ (h j - h' j) by dvd_sub.

So for each i ∈ Iio j: (gamma i j : ℤ) ∣ (h j - h' j), which gives gamma i j ∣ Int.natAbs(h j - h' j).

By Finset.lcm_dvd: gammaRow j = (Iio j).lcm (gamma · j) divides Int.natAbs(h j - h' j), provided ∀ i ∈ Iio j, gamma i j ∣ Int.natAbs(h j - h' j). This is what we showed.

Finally, (gammaRow j : ℤ) ∣ (h j - h' j) follows from the Nat divisibility.
-/
lemma gammaRow_dvd_diff_of_valid {Γ : GammaStructure (k + 1)} {h h' : Fin (k + 1) → ℤ}
    {j : Fin (k + 1)}
    (hgcd : ∀ i l, i ≠ l → Nat.gcd Γ.sqfreepart (Int.natAbs (h l - h i)) = Γ.gamma i l)
    (hgcd' : ∀ i l, i ≠ l → Nat.gcd Γ.sqfreepart (Int.natAbs (h' l - h' i)) = Γ.gamma i l)
    (heq : ∀ i : Fin (k + 1), i < j → h i = h' i) :
    (Γ.gammaRow j : ℤ) ∣ (h j - h' j) := by
  have h_div : ∀ i < j, (Γ.gamma i j : ℤ) ∣ (h j - h' j) := by
    intros i hi; specialize hgcd i j; specialize hgcd' i j; simp_all +decide [ Int.natAbs_dvd_natAbs ] ;
    have := hgcd ( ne_of_lt hi ) ▸ Nat.gcd_dvd_right _ _; ( have := hgcd' ( ne_of_lt hi ) ▸ Nat.gcd_dvd_right _ _; simp_all +decide [ ← Int.natCast_dvd_natCast ] ; );
    simpa using dvd_sub ‹ ( Γ.gamma i j : ℤ ) ∣ h j - h' i › this |> fun x => by simpa using x;
  generalize_proofs at *; (
  convert Finset.lcm_dvd fun i hi => h_div i ( Finset.mem_Iio.mp hi ) using 1
  generalize_proofs at *; (simp [GammaStructure.gammaRow]);
  induction' ( Finset.Iio j : Finset ( Fin ( k + 1 ) ) ) using Finset.induction <;> simp_all +decide [ Finset.lcm_insert ];
  simp +decide [ ← ‹_›, GCDMonoid.lcm ])

/-
PROBLEM
General fiber-counting bound: If `S` is a finset of tuples in `[0, H]^n` such that
for each coordinate `j`, fixing coordinates `i < j` determines the residue class of
coordinate `j` modulo `m j`, then `|S| ≤ ∏_j (⌊H / m_j⌋ + 1)`.

The proof is by induction on `n`. At each step, project onto the first `n-1` coordinates
using `Fin.init`. The image satisfies the same property (by restriction), so the IH gives
`|image| ≤ ∏_{j<n-1}`. Each fiber has all elements in a single residue class mod `m(last)`,
so has at most `⌊H/m(last)⌋ + 1` elements.

PROVIDED SOLUTION
Proof by induction on n.

Base case n = 0: Fin 0 → ℤ has exactly one element (the empty function). So S.card ≤ 1 = empty product.

Inductive step n → n+1: Given S : Finset (Fin (n+1) → ℤ), define f = Fin.init : (Fin (n+1) → ℤ) → (Fin n → ℤ). Let I = S.image f.

1. Each fiber {h ∈ S | f(h) = g} has card ≤ H / m(Fin.last n) + 1.
   Proof: For any two h, h' in the fiber, f(h) = f(h') = g, so h(i) = h'(i) for all i < Fin.last n (since Fin.init h = Fin.init h'). By hfib applied with j = Fin.last n, m(Fin.last n) | (h(Fin.last n) - h'(Fin.last n)). So the values h(Fin.last n) form a set with pairwise differences divisible by m(Fin.last n), all in [0,H]. Use card_set_pairwise_dvd_le to bound by H / m(last) + 1 (as reals), hence ≤ H / m(last) + 1 (as nats by Nat.cast_le).

2. I.card ≤ ∏_{j : Fin n} (H / m(j.castSucc) + 1) by IH.
   The IH needs: I satisfies the fiber property with moduli m' j = m (j.castSucc). For g, g' ∈ I with g(i) = g'(i) for all i < j: pick h, h' ∈ S with f(h) = g, f(h') = g'. Then h(castSucc i) = g(i) = g'(i) = h'(castSucc i) for all i < j. Since Fin.castSucc preserves order, h(l) = h'(l) for all l < castSucc j. By hfib, m(castSucc j) | (h(castSucc j) - h'(castSucc j)). Since g(j) = h(castSucc j) and g'(j) = h'(castSucc j), we get m(castSucc j) | (g(j) - g'(j)). ✓

3. By Finset.card_le_mul_card_image: S.card ≤ (H / m(last) + 1) * I.card ≤ (H / m(last) + 1) * ∏_{j : Fin n} (H / m(j.castSucc) + 1) = ∏_{j : Fin (n+1)} (H / m(j) + 1).

The last equality uses Fin.prod_univ_castSucc: ∏_{j : Fin (n+1)} f(j) = (∏_{j : Fin n} f(j.castSucc)) * f(Fin.last n).
-/
set_option maxHeartbeats 800000 in
lemma card_filtered_le_prod_of_fiber_dvd (n : ℕ) (H : ℕ) (m : Fin n → ℕ)
    (hm : ∀ j, 0 < m j)
    (S : Finset (Fin n → ℤ))
    (hS : ∀ h ∈ S, ∀ i, 0 ≤ h i ∧ h i ≤ H)
    (hfib : ∀ j : Fin n, ∀ h ∈ S, ∀ h' ∈ S,
      (∀ i : Fin n, i < j → h i = h' i) → (m j : ℤ) ∣ (h j - h' j)) :
    S.card ≤ ∏ j : Fin n, (H / m j + 1) := by
  revert S hS hfib hm; induction' n with n ih <;> simp_all +decide [ Fin.prod_univ_castSucc ] ;
  intro hm S hS hfib
  set I := S.image (Fin.init) with hI_def
  have hI_card : I.card ≤ ∏ j : Fin n, (H / m (Fin.castSucc j) + 1) := by
    apply ih (fun j => m (Fin.castSucc j)) (fun j => hm (Fin.castSucc j)) I (by
    simp +zetaDelta at *;
    exact fun h hh i => hS h hh ( Fin.castSucc i )) (by
    simp +zetaDelta at *;
    intro j a ha b hb hab; specialize hfib ( Fin.castSucc j ) a ha b hb; simp_all +decide [ Fin.init ] ;
    exact hfib fun i hi => by simpa using hab ⟨ i, by linarith [ Fin.is_lt i, Fin.is_lt j, show ( i : ℕ ) < j from hi ] ⟩ ( by simpa [ Fin.castSucc_lt_last ] using hi ) ;)
  have h_fib_card : ∀ g ∈ I, (S.filter (fun h => Fin.init h = g)).card ≤ H / m (Fin.last n) + 1 := by
    intros g hg
    have h_fiber : ∀ h ∈ Finset.filter (fun h => Fin.init h = g) S, ∀ h' ∈ Finset.filter (fun h => Fin.init h = g) S, (m (Fin.last n) : ℤ) ∣ (h (Fin.last n) - h' (Fin.last n)) := by
      intros h hh h' hh';
      apply hfib (Fin.last n) h (Finset.mem_filter.mp hh).left h' (Finset.mem_filter.mp hh').left;
      simp_all +decide [ funext_iff, Fin.init ];
      exact fun i hi => by have := hh.2 ⟨ i, hi ⟩ ; have := hh'.2 ⟨ i, hi ⟩ ; aesop;
    -- Apply the lemma card_set_pairwise_dvd_le to the set of last coordinates of elements in the fiber.
    have h_last_coords : (Finset.image (fun h => h (Fin.last n)) (Finset.filter (fun h => Fin.init h = g) S)).card ≤ (H : ℝ) / (m (Fin.last n) : ℝ) + 1 := by
      convert card_set_pairwise_dvd_le ( hm ( Fin.last n ) ) H ( Finset.image ( fun h => h ( Fin.last n ) ) ( Finset.filter ( fun h => Fin.init h = g ) S ) ) _ _ using 1;
      · simp +zetaDelta at *;
        exact fun x h hh hh' hx => hx ▸ hS h hh ( Fin.last n );
      · grind;
    rw [ Finset.card_image_of_injOn ] at h_last_coords <;> norm_cast at *;
    · rw [ div_add_one, le_div_iff₀ ] at h_last_coords <;> norm_cast at * <;> nlinarith [ hm ( Fin.last n ), Nat.div_add_mod H ( m ( Fin.last n ) ), Nat.mod_lt H ( hm ( Fin.last n ) ) ];
    · intro x hx y hy; have := hx.2; have := hy.2; simp_all +decide [ Fin.ext_iff ] ;
      exact fun h => funext fun i => if hi : i.val < n then by simpa [ Fin.ext_iff ] using congr_fun ‹Fin.init x = g› ⟨ i.val, hi ⟩ |> Eq.trans <| congr_fun ‹Fin.init y = g› ⟨ i.val, hi ⟩ |> Eq.symm else by rw [ show i = Fin.last n from le_antisymm ( Fin.le_last _ ) ( not_lt.mp hi ) ] ; exact h;
  have h_S_card : S.card ≤ I.card * (H / m (Fin.last n) + 1) := by
    have h_S_card : S.card = ∑ g ∈ I, (S.filter (fun h => Fin.init h = g)).card := by
      exact Finset.card_eq_sum_card_image _ _
    generalize_proofs at *; (
    exact h_S_card.symm ▸ le_trans ( Finset.sum_le_sum h_fib_card ) ( by simp +decide [ mul_comm ] ) ;)
  exact le_trans h_S_card (by
  exact Nat.mul_le_mul_right _ hI_card)

/-! ### Upper bound on `M_Γ(H)` (Proposition 3.2) -/

/-
PROBLEM
**Proposition 3.2** (M_Γ bound):
$M_\Gamma(H) \le \prod_{j=1}^{k} \left(\frac{H}{\gamma_j} + 1\right)$
where `γ_j = gammaRow j`.

The proof: fix `h₀ = 0` and enumerate `h₁, …, hₖ` sequentially. For each `j`,
the conditions `γ_{i,j} | (hⱼ − hᵢ)` for `i < j` force `hⱼ` into a single
residue class modulo `γⱼ = lcm_{i<j} γ_{i,j}`, giving at most `⌊H/γⱼ⌋ + 1`
choices in `[0, H]`.

*Note*: The product uses `i.succ` (indices `1, …, k` in `Fin (k+1)`), matching
the paper's convention where `γ₀ = 1` contributes trivially.

PROVIDED SOLUTION
Apply card_filtered_le_prod_of_fiber_dvd to the "tail" of valid tuples.

Let S' = (piFinset (fun _ => Icc 0 H)).filter (fun h => h 0 = 0 ∧ distinct ∧ gcd conditions) be the set defining countTuplesWithGamma. Note S'.card = countTuplesWithGamma Γ H.

Define the map τ : (Fin (k+1) → ℤ) → (Fin k → ℤ) by τ(h)(i) = h(i.succ). This is Fin.tail.

Let S = S'.image τ... no, actually S is a finset of (Fin k → ℤ).

Actually, I should apply card_filtered_le_prod_of_fiber_dvd directly. Let me define:
- n = k
- m(j) = Γ.gammaRow (j.succ) for j : Fin k
- S = (image of τ restricted to S')... no.

Wait, τ is injective on S' (since h(0) = 0 is determined). So S'.card = (S'.image τ).card. And S'.image τ is a finset of Fin k → ℤ functions.

Apply card_filtered_le_prod_of_fiber_dvd with:
- n = k
- H = H
- m(j) = Γ.gammaRow (j.succ) (for j : Fin k, so indices 1,...,k of the original)
- S = S'.image τ

Conditions to verify:
1. hm: gammaRow(j.succ) > 0. Since gammaRow is the lcm of positive squarefree numbers (or 1 if empty), it's always ≥ 1.

2. hS: For h ∈ S'.image τ, i.e., τ(h') for some h' ∈ S', we need 0 ≤ τ(h')(i) ∧ τ(h')(i) ≤ H. This is h'(i.succ) which is in [0, H] by the piFinset condition.

3. hfib: For j : Fin k, h, h' ∈ S'.image τ with h(i) = h'(i) for i < j, need gammaRow(j.succ) | (h(j) - h'(j)).

Pick preimages g, g' ∈ S' with τ(g) = h, τ(g') = h'. Then g(0) = g'(0) = 0 and g(i.succ) = h(i) for all i. For i < j: g(i.succ) = h(i) = h'(i) = g'(i.succ). Also g(0) = g'(0) = 0.

So g(l) = g'(l) for all l < j.succ (either l = 0 or l = i.succ for some i < j).

By gammaRow_dvd_diff_of_valid (with the gcd conditions from g, g' being in S'), gammaRow(j.succ) | (g(j.succ) - g'(j.succ)) = (h(j) - h'(j)). ✓

4. The conclusion: S.card ≤ ∏ j : Fin k, (H / gammaRow(j.succ) + 1).

Since τ is injective on S': S'.card = S.card. So countTuplesWithGamma = S'.card = S.card ≤ product (as nats).

Converting to reals: (countTuplesWithGamma : ℝ) = (S'.card : ℝ) ≤ (∏ : ℝ). And (H / m + 1 : ℕ) cast to ℝ ≤ (H : ℝ) / m + 1 (since Nat division ≤ real division). So the ℕ product cast to ℝ ≤ ℝ product.
-/
theorem countTuples_bound_prop (Γ : GammaStructure (k + 1)) (H : ℕ) :
    (countTuplesWithGamma Γ H : ℝ) ≤
      ∏ i : Fin k, ((H : ℝ) / (Γ.gammaRow i.succ) + 1) := by
  -- Apply the lemma `card_filtered_le_prod_of_fiber_dvd` to the set S.
  have h_card : (countTuplesWithGamma Γ H : ℝ) ≤ ∏ j : Fin k, (H / Γ.gammaRow (Fin.succ j) + 1) := by
    -- Define the map τ : (Fin (k+1) → ℤ) → (Fin k → ℤ) by τ(h)(i) = h(i.succ). This is Fin.tail.
    set τ : (Fin (k + 1) → ℤ) → (Fin k → ℤ) := fun h i => h (Fin.succ i);
    -- Let S be the image of S' under τ.
    set S := (Fintype.piFinset fun _ : Fin (k + 1) => Finset.Icc 0 (H : ℤ)).filter (fun h =>
      h 0 = 0 ∧ (∀ i j, i ≠ j → h i ≠ h j) ∧
      ∀ i j, i ≠ j → Nat.gcd Γ.sqfreepart (Int.natAbs (h j - h i)) = Γ.gamma i j) |> Finset.image τ;
    -- Apply the lemma `card_filtered_le_prod_of_fiber_dvd` to the set S with the conditions we've verified.
    have h_card_S : S.card ≤ ∏ j : Fin k, (H / Γ.gammaRow (Fin.succ j) + 1) := by
      apply card_filtered_le_prod_of_fiber_dvd k H (fun j => Γ.gammaRow (Fin.succ j)) (fun j => by
        apply GammaStructure.gammaRow_squarefree Γ (Fin.succ j) |> fun h => Nat.pos_of_ne_zero (by
        exact h.ne_zero)) S (by
      grind) (by
      intros j h hh h' hh' h_eq
      obtain ⟨h'', hh'', rfl⟩ := Finset.mem_image.mp hh
      obtain ⟨h''', hh''', rfl⟩ := Finset.mem_image.mp hh';
      apply gammaRow_dvd_diff_of_valid;
      · aesop;
      · aesop;
      · intro i hi; induction i using Fin.inductionOn <;> aesop;);
    rw [ Finset.card_image_of_injOn ] at h_card_S;
    · exact_mod_cast h_card_S;
    · intro h₁ hh₁ h₂ hh₂ h_eq; simp_all +decide [ funext_iff, Fin.forall_fin_succ ] ;
      exact h_eq;
  refine le_trans h_card ?_ ; norm_num [ Finset.prod_add ];
  refine Finset.sum_le_sum fun s hs => ?_;
  rw [ ← Finset.prod_const ];
  rw [ ← Finset.prod_div_distrib ] ; exact Finset.prod_le_prod ( fun _ _ => by positivity ) fun _ _ => by rw [ le_div_iff₀ ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by { exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| by { intro t; have := Γ.gammaRow_squarefree ( Fin.succ ‹_› ) ; simp_all +decide [ Nat.factorization_eq_zero_iff ] } } ) ] ; norm_cast ; nlinarith [ Nat.div_mul_le_self H ( Γ.gammaRow ( Fin.succ ‹_› ) ) ] ;

/-- **Corollary to Proposition 3.2** (weaker but unconditional bound):
`M_Γ(H) ≤ (2H + 1)^k`. Each coordinate (after fixing `h₀ = 0`) has at most `H + 1`
choices. -/
theorem countTuples_bound (Γ : GammaStructure (k + 1)) (H : ℕ) :
    countTuplesWithGamma Γ H ≤ (2 * H + 1) ^ k := by
  refine' le_trans _ ( pow_le_pow_left' ( show 2 * H + 1 ≥ H + 1 by linarith ) _ );
  refine' le_trans ( Finset.card_le_card _ ) _;
  exact Finset.image ( fun h : Fin k → ℤ => Fin.cons 0 h ) ( Fintype.piFinset fun _ : Fin k => Finset.Icc 0 ( H : ℤ ) );
  · intro h hh; simp_all +decide [ Fin.forall_fin_succ ] ;
    exact ⟨ fun i => h i.succ, fun i => hh.1.2 i, by ext i; cases i using Fin.inductionOn <;> aesop ⟩;
  · rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ]

/-! ### Corollary 3.3: Bounds from Proposition 3.2 -/

/-
PROBLEM
**Corollary 3.3** (first case): If each `γⱼ ≤ H` for `j = 1,…,k`, then
`M_Γ(H) ≤ 2^k · H^k / γ(Γ)`.

This follows from Proposition 3.2 since `H/γⱼ + 1 ≤ 2H/γⱼ` when `γⱼ ≤ H`.

PROVIDED SOLUTION
From countTuples_bound_prop: (countTuplesWithGamma Γ H : ℝ) ≤ ∏ i : Fin k, ((H : ℝ) / (Γ.gammaRow i.succ) + 1).

Under hsmall: for all i : Fin k, Γ.gammaRow i.succ ≤ H. Since gammaRow ≥ 1 (it's an lcm of positive integers), we have 1 ≤ gammaRow ≤ H, so H / gammaRow ≥ 1, hence H/gammaRow + 1 ≤ 2 * (H/gammaRow) = 2H/gammaRow.

So each factor: (H : ℝ) / gammaRow(i.succ) + 1 ≤ 2 * (H : ℝ) / gammaRow(i.succ).

Product ≤ ∏ (2H/gammaRow) = 2^k * H^k / ∏ gammaRow(i.succ).

Now ∏_{i : Fin k} gammaRow(i.succ) = ∏_{j=1}^{k} gammaRow(j). And gammaProd = ∏_{j=0}^{k} gammaRow(j) = gammaRow(0) * ∏_{j=1}^{k} gammaRow(j) = 1 * ∏_{j=1}^{k} gammaRow(j) = ∏_{j=1}^{k} gammaRow(j).

So ∏ gammaRow(i.succ) = gammaProd.

Therefore: countTuples ≤ 2^k * H^k / gammaProd. ✓

Key steps:
1. Apply countTuples_bound_prop.
2. Bound each factor using hsmall.
3. Show ∏ gammaRow(i.succ) = gammaProd (using gammaRow 0 = 1).

For step 3: gammaProd = ∏_{j : Fin(k+1)} gammaRow(j). By Fin.prod_univ_succ: ∏_{j : Fin(k+1)} f(j) = f(0) * ∏_{j : Fin k} f(j.succ). So gammaProd = gammaRow(0) * ∏_{i : Fin k} gammaRow(i.succ). Since gammaRow(0) = 1, gammaProd = ∏_{i : Fin k} gammaRow(i.succ). ✓
-/
theorem countTuples_bound_small_gamma (Γ : GammaStructure (k + 1)) (H : ℕ)
    (hsmall : ∀ i : Fin k, Γ.gammaRow i.succ ≤ H) :
    (countTuplesWithGamma Γ H : ℝ) ≤
      2 ^ k * (H : ℝ) ^ k / Γ.gammaProd := by
  rw [ le_div_iff₀ ];
  · -- From countTuples_bound_prop, we have:
    have h_bound : (countTuplesWithGamma Γ H : ℝ) * (∏ i : Fin k, Γ.gammaRow i.succ) ≤ (2 * H : ℝ) ^ k := by
      have h_bound : (countTuplesWithGamma Γ H : ℝ) ≤ ∏ i : Fin k, ((H : ℝ) / (Γ.gammaRow i.succ) + 1) := by
        exact countTuples_bound_prop Γ H;
      have h_bound : (∏ i : Fin k, ((H : ℝ) / (Γ.gammaRow i.succ) + 1)) * (∏ i : Fin k, Γ.gammaRow i.succ) ≤ (∏ i : Fin k, (2 * H : ℝ)) := by
        rw [ Nat.cast_prod ];
        rw [ ← Finset.prod_mul_distrib ] ; exact Finset.prod_le_prod ( fun _ _ => mul_nonneg ( add_nonneg ( div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) zero_le_one ) ( Nat.cast_nonneg _ ) ) fun i hi => by nlinarith [ show ( Γ.gammaRow i.succ : ℝ ) ≥ 1 from mod_cast Nat.pos_of_ne_zero ( by
                                                                                                                                                                                                                                        exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by intros h; obtain ⟨ j, hj ⟩ := h; have := Γ.pos j ( Fin.succ i ) ; aesop; ), div_mul_cancel₀ ( H : ℝ ) ( show ( Γ.gammaRow i.succ : ℝ ) ≠ 0 from mod_cast Nat.ne_of_gt ( Nat.pos_of_ne_zero ( by
                                                                                                                                                                                                                                                                                                                                                      exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by intros h; obtain ⟨ j, hj ⟩ := h; have := Γ.pos j ( Fin.succ i ) ; aesop; ) ) ), show ( Γ.gammaRow i.succ : ℝ ) ≤ H from mod_cast hsmall i ] ;
      exact le_trans ( mul_le_mul_of_nonneg_right ‹_› <| Nat.cast_nonneg _ ) <| h_bound.trans <| by norm_num;
    convert h_bound using 1 ; norm_num [ mul_pow, Fin.prod_univ_succ ];
    · unfold GammaStructure.gammaProd GammaStructure.gammaRow; norm_cast; simp +decide [ Fin.prod_univ_succ ] ;
      simp +decide [ Finset.lcm ];
      exact Or.inl ( by erw [ Finset.fold_empty ] ; norm_num );
    · rw [ mul_pow ];
  · exact Nat.cast_pos.mpr ( GammaStructure.gammaProd_pos Γ )

/-
PROBLEM
**Corollary 3.3** (second case): If any `γⱼ ≥ H` for `j = 1,…,k`, then
`M_Γ(H) ≤ 2^k · H^{k-1}`.

PROVIDED SOLUTION
From countTuples_bound_prop: (countTuplesWithGamma Γ H : ℝ) ≤ ∏ i : Fin k, ((H : ℝ) / (Γ.gammaRow i.succ) + 1).

From hlarge: ∃ i₀ : Fin k, H ≤ gammaRow(i₀.succ). For this i₀, the factor (H : ℝ) / gammaRow(i₀.succ) + 1 ≤ (H : ℝ) / H + 1 = 1 + 1 = 2 (since gammaRow ≥ H implies H/gammaRow ≤ 1).

For all other i ≠ i₀: (H : ℝ) / gammaRow(i.succ) + 1 ≤ H + 1 ≤ 2H (since gammaRow ≥ 1 gives H/gammaRow ≤ H, plus 1 ≤ H+1, and for H ≥ 1: H + 1 ≤ 2H, for H = 0: H + 1 = 1 ≤ 1 = 2*0 + 1... hmm).

Actually, we want: product ≤ 2^k * H^{k-1}.

Split the product: separate the factor for i₀ from the rest.
∏_{i : Fin k} = (factor at i₀) * ∏_{i ≠ i₀}.

Factor at i₀: ≤ 2 (since H/gammaRow + 1 ≤ 1 + 1 = 2).
Factors at i ≠ i₀: each ≤ H + 1 (since gammaRow ≥ 1 gives H/gammaRow ≤ H). There are k-1 such factors. So ∏_{i ≠ i₀} ≤ (H + 1)^{k-1}.

Total ≤ 2 * (H + 1)^{k-1}.

Now 2 * (H+1)^{k-1} ≤ 2^k * H^{k-1}? For H ≥ 1: (H+1) ≤ 2H, so (H+1)^{k-1} ≤ (2H)^{k-1} = 2^{k-1} * H^{k-1}. Then 2 * (H+1)^{k-1} ≤ 2 * 2^{k-1} * H^{k-1} = 2^k * H^{k-1}. ✓

For H = 0: countTuplesWithGamma ≤ 0 (any tuple has h_i ∈ [0,0] = {0}, so all h_i = 0, violating distinctness for k ≥ 1; for k = 0, hlarge gives ∃ i : Fin 0 which is impossible). Wait, H = 0 and hlarge: ∃ i : Fin k, 0 ≤ gammaRow(i.succ), which is always true. Then RHS = 2^k * 0^{k-1} = 0 for k ≥ 2 and 2^k for k = 0,1.

Hmm, for k = 0: hlarge gives ∃ i : Fin 0, which is empty/impossible. So k ≥ 1 when hlarge holds. For k = 1 and H = 0: RHS = 2 * 0^0 = 2. LHS = countTuplesWithGamma which counts (0, h_1) with h_1 ∈ [0,0] = {0}, but h_1 ≠ h_0 = 0. So LHS = 0 ≤ 2. ✓.

For k ≥ 2 and H = 0: RHS = 2^k * 0 = 0. LHS = 0 (no distinct tuples in [0,0]). ✓.

So the bound works. The key steps:
1. Apply countTuples_bound_prop.
2. Split the product at the index i₀ from hlarge.
3. Bound the factor at i₀ by 2.
4. Bound remaining k-1 factors by H+1 each.
5. Use (H+1) ≤ 2H for H ≥ 1, and handle H = 0 separately.
-/
theorem countTuples_bound_large_gamma (Γ : GammaStructure (k + 1)) (H : ℕ)
    (hlarge : ∃ i : Fin k, H ≤ Γ.gammaRow i.succ) :
    (countTuplesWithGamma Γ H : ℝ) ≤ 2 ^ k * (H : ℝ) ^ (k - 1) := by
  -- Let's choose any index $i₀$ for which $H \leq \Gamma رمضان.gammaRow i₀.boost$.
  obtain ⟨i₀, hi₀⟩ := hlarge;
  have h_bound : (countTuplesWithGamma Γ H) ≤ ∏ i : Fin k, ((H : ℝ) / (Γ.gammaRow i.succ) + 1) := by
    exact countTuples_bound_prop Γ H;
  -- Split the product into the term for $i₀$ and the product over the remaining terms.
  have h_split : ∏ i : Fin k, ((H : ℝ) / (Γ.gammaRow i.succ) + 1) ≤ ((H : ℝ) / (Γ.gammaRow i₀.succ) + 1) * ∏ i ∈ Finset.univ.erase i₀, ((H : ℝ) + 1) := by
    rw [ ← Finset.mul_prod_erase _ _ ( Finset.mem_univ i₀ ) ];
    gcongr;
    exact div_le_self ( Nat.cast_nonneg _ ) ( mod_cast Nat.pos_of_ne_zero ( by
      exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| by intro h; have := Γ.gammaRow_squarefree ( Fin.succ ‹_› ) ; simp_all +decide [ Nat.factorization_eq_zero_iff ] ; ) )
  generalize_proofs at *; (
  -- For $H \geq 1$, we have $H / \Gamma Ramadan.gammaRow i₀.boost + 1 \leq 2$.
  by_cases hH : H ≥ 1 <;> simp_all +decide;
  · -- For $H \geq 1$, we have $(H + 1)^{k-1} \leq 2^{k-1} H^{k-1}$.
    have h_exp_bound : (H + 1 : ℝ) ^ (k - 1) ≤ 2 ^ (k - 1) * H ^ (k - 1) := by
      rw [ ← mul_pow ] ; gcongr ; norm_cast ; linarith;
    generalize_proofs at *; (
    rcases k with ( _ | k ) <;> simp_all +decide ; ring_nf at * ; (
    refine le_trans h_bound <| h_split.trans ?_ ; nlinarith [ show ( H : ℝ ) ≥ 1 by norm_cast, inv_mul_cancel_left₀ ( show ( ( ‹GammaStructure ( k + 1 + 1 ) ›.gammaRow ‹Fin ( k + 1 ) ›.succ ) : ℝ ) ≠ 0 by norm_cast; exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| by aesop ) <| ( 1 + H : ℝ ) ^ k, show ( ( ‹GammaStructure ( k + 1 + 1 ) ›.gammaRow ‹Fin ( k + 1 ) ›.succ ) : ℝ ) ≥ H by exact_mod_cast hi₀ ] ;));
  · rcases k with ( _ | _ | k ) <;> norm_num at * ; aesop;
    refine' le_antisymm _ _ <;> simp_all +decide [ countTuplesWithGamma ];
    exact fun h => absurd ( h 0 1 ) ( by simp +decide ))

/-! ### Inequality (3.3): Greedy reordering bound -/

/-
PROBLEM
Equation (3.3) from §3.1: After greedy reordering,
$$\gamma_{r+1} \le \gamma_r \cdot \gamma_{r+1, r} \le H \cdot \gamma_r.$$
This gives that `γ(Γ)` can be bounded in terms of the `γᵢⱼ` values.

PROVIDED SOLUTION
The goal is x ≤ H * x where x = Γ.gammaRow r.castSucc. First show H ≥ 1: since k + 2 ≥ 2, take i = ⟨0, by omega⟩ and j = ⟨1, by omega⟩ which are distinct in Fin (k+2). Then Γ.pos i j (Fin.ne_of_val_ne (by omega)) gives 0 < Γ.gamma i j, and hH i j (Fin.ne_of_val_ne (by omega)) gives Γ.gamma i j ≤ H, so H ≥ 1. Then use Nat.le_mul_of_pos_left or le_mul_of_one_le_left.
-/
theorem gammaRow_succ_bound (Γ : GammaStructure (k + 2)) (r : Fin (k + 1))
    (H : ℕ) (hH : ∀ i j : Fin (k + 2), i ≠ j → Γ.gamma i j ≤ H) :
    Γ.gammaRow r.castSucc ≤ H * Γ.gammaRow r.castSucc := by
  -- Since $H \geq 1$, multiplying $\Gamma.gammaRow r.castSucc$ by $H$ preserves the inequality.
  have hH_pos : 1 ≤ H := by
    exact le_trans ( pos_of_gt ( Γ.pos 0 1 ( by norm_num ) ) ) ( hH 0 1 ( by norm_num ) )
  exact le_mul_of_one_le_left (Nat.zero_le _) hH_pos

/-! ### Corollary 3.4: Full refined bound -/

/-
PROBLEM
**Corollary 3.4** (Combined bound on `M_γ(H)`):
`M_γ(H) ≤ C(k+1,2)^{Ω(γ)} · (2H+1)^k`.

*Corrected from `k.choose 2` to `(k + 1).choose 2`*: the set `countTuplesWithGammaProd k`
involves `GammaStructure (k + 1)` which has `k + 1` indices, so the relevant binomial
coefficient counts pairs among `k + 1` elements, matching `countGammaStructures_le`
instantiated at `k + 1`.

PROVIDED SOLUTION
We need: (countTuplesWithGammaProd k γ H : ℝ) ≤ ((k+1).choose 2)^n * (2H+1)^k where n = γ.primeFactors.card.

The proof has two cases:

Case 1: k = 0. countTuplesWithGammaProd 0 γ H = Set.ncard of a set of tuples h : Fin 1 → ℤ with h 0 = 0 and ∃ Γ : GammaStructure 1 with Γ.gammaProd = γ. GammaStructure 1 has Fin 1 → Fin 1 → ℕ, gammaRow 0 = (Iio 0).lcm ... = 1, so gammaProd = 1. If γ ≠ 1, the set is empty (ncard = 0 ≤ anything). If γ = 1, n = 0, so ((1).choose 2)^0 * (2H+1)^0 = 1, and ncard ≤ 1. Actually the set for γ = 1 has exactly 1 element (h = fun _ => 0).

Case 2: k ≥ 1. We bound the set size directly. The set S ⊆ {h : Fin(k+1) → ℤ | h 0 = 0 ∧ ∀ i, 0 ≤ h i ∧ h i ≤ H}. The latter is finite with at most (H+1)^k elements (h 0 is fixed, h 1,...,h k each choose from Icc 0 H). Since (H+1) ≤ (2H+1) and ((k+1).choose 2) ≥ 1 for k ≥ 1, we get:
ncard S ≤ (H+1)^k ≤ (2H+1)^k ≤ 1 * (2H+1)^k ≤ ((k+1).choose 2)^n * (2H+1)^k.

For finiteness: S is contained in the finite set (Fintype.piFinset (fun _ => Finset.Icc 0 H)).toSet, which is finite. Use Set.Finite.subset.

For the cardinality bound: use Set.ncard_le_ncard with the superset, then bound ncard of the superset. The superset {h | h 0 = 0 ∧ ∀ i, 0 ≤ h i ∧ h i ≤ H} has ncard ≤ (H+1)^k.
-/
theorem countTuples_refined_bound (γ H : ℕ) (hH : 0 < H) (hγ : 0 < γ) :
    (countTuplesWithGammaProd k γ H : ℝ) ≤
      ((k + 1).choose 2) ^ γ.primeFactors.card *
        (2 * (H : ℝ) + 1) ^ k := by
  -- Let's split the proof into two cases: k = 0 and k ≥ 1.
  by_cases hk : k = 0;
  · subst hk; norm_num;
    by_cases h : γ.primeFactors = ∅ <;> simp_all +decide [ countTuplesWithGammaProd ];
    · cases h <;> simp_all +decide [ Nat.primeFactors_one ];
      refine' le_trans ( Set.ncard_le_ncard <| show { h : Fin 1 → ℤ | h 0 = 0 ∧ ( 0 ≤ h 0 ∧ h 0 ≤ H ) ∧ ∃ Γ : GammaStructure 1, Γ.gammaProd = 1 } ⊆ { 0 } from _ ) _ <;> norm_num [ Set.subset_def ];
      exact fun x hx₁ hx₂ hx₃ Γ hΓ => funext fun i => by fin_cases i; exact hx₁;
    · -- Since the only valid Γ is the one where γ = 1, and γ ≠ 1, there are no such tuples.
      have h_empty : ∀ h : Fin 1 → ℤ, h 0 = 0 → (∃ Γ : GammaStructure 1, Γ.gammaProd = γ) → False := by
        rintro h hh ⟨ Γ, rfl ⟩ ; simp_all +decide [ Fin.eq_zero, GammaStructure.gammaProd ] ;
        exact h.2 ( by rw [ show Γ.gammaRow 0 = 1 from by unfold GammaStructure.gammaRow; aesop ] );
      rw [ show { h : Fin 1 → ℤ | h 0 = 0 ∧ ( 0 ≤ h 0 ∧ h 0 ≤ H ) ∧ ∃ Γ : GammaStructure 1, Γ.gammaProd = γ } = ∅ by rw [ Set.eq_empty_iff_forall_notMem ] ; rintro h ⟨ hh₁, hh₂, hh₃ ⟩ ; exact h_empty h hh₁ hh₃ ] ; norm_num;
  · refine' le_trans _ ( le_mul_of_one_le_left ( by positivity ) _ );
    · -- The set S is contained in the finite set (Fintype.piFinset (fun _ => Finset.Icc 0 H)).toSet, which is finite.
      have h_finite : {h : Fin (k + 1) → ℤ | h 0 = 0 ∧ (∀ i, 0 ≤ h i ∧ h i ≤ H)}.ncard ≤ (H + 1) ^ k := by
        rw [ show { h : Fin ( k + 1 ) → ℤ | h 0 = 0 ∧ ∀ i : Fin ( k + 1 ), 0 ≤ h i ∧ h i ≤ ↑H } = ( Set.image ( fun t : Fin k → ℤ => Fin.cons 0 t ) ( Set.Icc ( 0 : Fin k → ℤ ) ( fun _ => ↑H ) ) ) from ?_ ];
        · rw [ Set.ncard_image_of_injective, Set.ncard_eq_toFinset_card' ] <;> norm_num [ Function.Injective ];
          erw [ Finset.card_map, Finset.card_pi ] ; norm_num;
        · ext h; simp;
          exact ⟨ fun ⟨ h₀, h₁ ⟩ => ⟨ fun i => h i.succ, ⟨ fun i => h₁ _ |>.1, fun i => h₁ _ |>.2 ⟩, by ext i; cases i using Fin.inductionOn <;> aesop ⟩, by rintro ⟨ x, ⟨ hx₀, hx₁ ⟩, rfl ⟩ ; exact ⟨ rfl, fun i => by cases i using Fin.inductionOn <;> aesop ⟩ ⟩;
      -- Since countTuplesWithGammaProd k γ H is a subset of the set of functions from Fin (k + 1) to ℤ that are bounded by H, we have:
      have h_subset : countTuplesWithGammaProd k γ H ≤ Set.ncard {h : Fin (k + 1) → ℤ | h 0 = 0 ∧ (∀ i, 0 ≤ h i ∧ h i ≤ H)} := by
        apply Set.ncard_le_ncard;
        · exact fun x hx => ⟨ hx.1, hx.2.2.1 ⟩;
        · exact Set.Finite.subset ( Set.finite_Icc _ _ ) fun x hx => ⟨ fun i => hx.2 i |>.1, fun i => hx.2 i |>.2 ⟩;
      exact_mod_cast h_subset.trans ( h_finite.trans ( by gcongr ; linarith ) );
    · exact one_le_pow₀ ( mod_cast Nat.choose_pos ( by linarith [ Nat.pos_of_ne_zero hk ] ) )

end PoissonCRT
