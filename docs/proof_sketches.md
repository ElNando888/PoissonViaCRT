# Proof Sketches for Combinatorics.lean

This file contains the detailed problem statements and solution sketches
that were originally inline in `PoissonViaCRT/Combinatorics.lean`.

Moved during refactoring to improve readability of the Lean source.

---

## `lemma GammaStructure.prime_dvd_trans`

**Problem:**
The compatibility condition implies that "p divides γ_{i,j}" is transitive:
if `p | γ_{i,j}` and `p | γ_{j,l}` then `p | γ_{i,l}`.

**Solution sketch:**
From the compatibility condition: gcd(gamma i j, gamma j l) | gamma i l. Since p | gamma i j and p | gamma j l, we have p | gcd(gamma i j, gamma j l). Since gcd divides gamma i l, by transitivity p | gamma i l.

---

## `lemma GammaStructure.gammaRow_squarefree`

**Problem:**
The gammaRow of a GammaStructure is squarefree: `gammaRow j` is the lcm of squarefree
numbers, hence squarefree.

**Solution sketch:**
gammaRow j = (Finset.Iio j).lcm (fun i => Γ.gamma i j). This is the lcm of squarefree numbers. The lcm of squarefree numbers is squarefree because for each prime p, the p-adic valuation of the lcm is the max of the p-adic valuations of the inputs, each of which is ≤ 1. Use Nat.squarefree_iff_prime_squarefree or Squarefree.lcm or similar.

---

## `lemma GammaStructure.factorization_gammaRow_le_one`

**Problem:**
For a squarefree gammaRow, the p-adic valuation is 0 or 1.

**Solution sketch:**
gammaRow j is squarefree by gammaRow_squarefree. For squarefree n, Nat.factorization n p ≤ 1. This follows from the definition of squarefree (or Nat.Squarefree.factorization_le_one).

---

## `lemma GammaStructure.factorization_gammaRow_eq`

**Problem:**
The p-adic valuation of `gammaRow j` is 1 iff there exists `i < j` with `p | gamma i j`,
and 0 otherwise.

**Solution sketch:**
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

---

## `lemma GammaStructure.factorization_gammaProd_eq`

**Problem:**
The p-adic valuation of `gammaProd` counts the number of indices `j` for which
there exists `i < j` with `p | gamma i j`.

**Solution sketch:**
gammaProd = ∏ j : Fin k, gammaRow j.

Nat.factorization (∏ j, gammaRow j) p = ∑ j, Nat.factorization (gammaRow j) p
(by Nat.factorization_prod, since each gammaRow j is nonzero, which follows from gammaRow ≥ 1).

By factorization_gammaRow_eq, each summand is (if ∃ i ∈ Iio j, p | gamma i j then 1 else 0).

So the sum = ∑ j, (if ∃ i ∈ Iio j, p | gamma i j then 1 else 0) = card of the filter set.

Use Finset.sum_boole or similar to convert the sum to a cardinality.

---

## `lemma card_filter_exists_lt_equiv`

**Problem:**
For any equivalence relation on `Fin n`, the number of non-minimal elements
(i.e., elements `j` such that there exists a smaller equivalent element) equals
`n` minus the number of equivalence classes. In particular, this count depends only
on the partition structure, not on the linear order.

**Solution sketch:**
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

---

## `lemma card_image_classMin_eq_of_perm`

**Problem:**
If two equivalence relations on `Fin n` are conjugate via a permutation `σ`,
then the images of the "class minimum" function have the same cardinality.

**Solution sketch:**
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

---

## `lemma GammaStructure.perm_count_eq`

**Problem:**
Key counting lemma: the number of elements `j` such that there exists `i < j`
in the same ~_p class equals `k - m_p` where `m_p` is the number of equivalence classes.
This count is determined by the unordered partition structure and is independent of
the linear order on `Fin k`.

More precisely: for any permutation σ, the number of j with "∃ i < j, p | gamma(σ i, σ j)"
equals the number of j with "∃ i < j, p | gamma(i, j)".

**Solution sketch:**
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

---

## `-- gammaRow is always positive`

**Problem:**
`gammaProd` is nonzero.

**Solution sketch:**
gammaProd = ∏ j : Fin k, gammaRow j. Each gammaRow j ≥ 1 (since gammaRow j = lcm of a set of positive integers, or if the set is empty, the empty lcm is 1). So the product is ≥ 1 > 0.

Actually, gammaRow ⟨0, _⟩ = (Iio 0).lcm (...) = 1 (empty lcm). For j > 0, gammaRow j = lcm of gamma(i,j) for i < j, each of which is positive by pos condition (i ≠ j since i < j). So gammaRow j ≥ 1.

Use Finset.prod_pos with gammaRow j > 0 for all j.

---

## `theorem GammaStructure.gammaProd_perm_invariant`

**Problem:**
**Permutation invariance** (unnumbered lemma, §3.1):
If `σ` is a permutation of `{0, …, k-1}` with `σ(0) = 0`, then
`γ(Γ^(σ)) = γ(Γ)`.

The proof proceeds by showing that each prime's contribution to the factorization of
`γ(Γ)` counts elements that are not minimal in their `~_p` equivalence class,
which is a permutation-invariant quantity.

**Solution sketch:**
Use Nat.eq_of_factorization_eq. The factorizations of (Γ.permute σ).gammaProd and Γ.gammaProd agree at every prime p.

Both are nonzero by gammaProd_pos.

For each prime p:
- factorization_gammaProd_eq gives factorization (Γ.permute σ).gammaProd p = card of filter set.
- The permuted structure's gamma is (Γ.permute σ).gamma i j = Γ.gamma (σ i) (σ j).
- So factorization ((Γ.permute σ).gammaProd) p = (univ.filter fun j => ∃ i ∈ Iio j, p ∣ Γ.gamma (σ i) (σ j)).card.
- By perm_count_eq, this equals (univ.filter fun j => ∃ i ∈ Iio j, p ∣ Γ.gamma i j).card.
- By factorization_gammaProd_eq, this equals factorization Γ.gammaProd p.

For non-prime p: factorization at non-prime p is always 0 for both sides.

---

## `theorem countGammaStructures_le`

**Problem:**
**Lemma 3.1** (Gamma bound): The number of `GammaStructure`s with `γ(Γ) = γ`
is at most `∏_{p^e ∥ γ} S(k, k-e) ≤ C(k,2)^{Ω(γ)}`.

The proof: for each prime `p` dividing `γ`, we partition `{0, …, k-1}` into subsets
where `i` and `j` are in the same subset iff `p | γᵢⱼ` (consistency follows from the
compatibility condition). The number of such partitions is a Stirling number of the second
kind, bounded by `C(k, 2)^e`.

**Solution sketch:**
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

---

## `lemma card_set_pairwise_dvd_le`

**Problem:**
Elements of a finite set in `[0, H]` whose pairwise differences are all divisible
by `m > 0` form a subset of an arithmetic progression, so the set has at most
`⌊H/m⌋ + 1 ≤ H/m + 1` elements.

**Solution sketch:**
If S is empty, S.card = 0 ≤ H/m + 1 trivially (since H/m ≥ 0 and 1 > 0).

If S is nonempty, pick any x₀ ∈ S (use S.min'). For every x ∈ S, m ∣ (x - x₀) (by hdvd). Consider the map φ : S → ℤ given by φ(x) = (x - x₀) / m (exact division since m ∣ (x - x₀)). This map is injective: if (x - x₀)/m = (y - x₀)/m then x - x₀ = y - x₀ so x = y.

The image satisfies: for x ∈ S, 0 ≤ x and x ≤ H, and 0 ≤ x₀ and x₀ ≤ H. So 0 ≤ (x - x₀)/m (when x ≥ x₀, which holds since x₀ = min) and (x - x₀)/m ≤ H/m (since x - x₀ ≤ H - 0 = H).

So φ maps S injectively into Finset.Icc 0 (H/m). The cardinality of this target is at most H/m + 1 (as a nat). Cast to ℝ: S.card ≤ ⌊H/m⌋ + 1 ≤ H/m + 1 (using Nat.floor_le).

Actually, a cleaner approach: without defining φ explicitly, just note that S ⊆ {x₀, x₀ + m, x₀ + 2m, ...} ∩ [0, H]. The elements in [0, H] of the form x₀ + k*m for k ∈ ℤ satisfy 0 ≤ x₀ + k*m ≤ H, so -x₀/m ≤ k ≤ (H-x₀)/m. The number of such k is at most ⌊(H-x₀)/m⌋ - ⌈-x₀/m⌉ + 1 ≤ H/m + 1.

Simplest formal approach: use Finset.card_le_card with an injection into Finset.range (H/m + 1), mapping x to (x - x₀).toNat / m.

---

## `lemma gamma_dvd_of_gcd_eq`

**Problem:**
From the filter condition defining `countTuplesWithGamma`, if `h` satisfies the gcd
condition then `Γ.gamma i j` divides `h j - h i` for `i ≠ j`.

**Solution sketch:**
From hgcd: Nat.gcd Γ.sqfreepart (Int.natAbs (h j - h i)) = Γ.gamma i j. Since gcd(a, b) divides b, we get Γ.gamma i j ∣ Int.natAbs (h j - h i). Then Int.natAbs_dvd or Int.ofNat_dvd gives (Γ.gamma i j : ℤ) ∣ (h j - h i).

---

## `lemma gammaRow_dvd_diff_of_valid`

**Problem:**
For tuples in `countTuplesWithGamma`, the set of valid values for coordinate `j`
(given all other coordinates) is contained in a single residue class modulo
`gammaRow j`. This is because `gammaRow j = lcm_{i<j} γ_{i,j}` and each
`γ_{i,j}` divides `h_j − h_i`, so the lcm divides any difference of valid `h_j` values.

**Solution sketch:**
gammaRow j = (Finset.Iio j).lcm (fun i => Γ.gamma i j).

Need: (gammaRow j : ℤ) ∣ (h j - h' j).

Use Int.natCast_dvd_natCast and show gammaRow j ∣ Int.natAbs(h j - h' j), then convert.

For each i ∈ Iio j (i.e., i < j): from hgcd with hij = ne_of_lt (by exact i.prop... well i < j): gamma_dvd_of_gcd_eq gives (gamma i j : ℤ) ∣ (h j - h i). Similarly from hgcd': (gamma i j : ℤ) ∣ (h' j - h' i). Since heq gives h i = h' i for i < j, we have h' i = h i. So (gamma i j : ℤ) ∣ (h j - h i) and (gamma i j : ℤ) ∣ (h' j - h i). Therefore (gamma i j : ℤ) ∣ (h j - h' j) by dvd_sub.

So for each i ∈ Iio j: (gamma i j : ℤ) ∣ (h j - h' j), which gives gamma i j ∣ Int.natAbs(h j - h' j).

By Finset.lcm_dvd: gammaRow j = (Iio j).lcm (gamma · j) divides Int.natAbs(h j - h' j), provided ∀ i ∈ Iio j, gamma i j ∣ Int.natAbs(h j - h' j). This is what we showed.

Finally, (gammaRow j : ℤ) ∣ (h j - h' j) follows from the Nat divisibility.

---

## `set_option maxHeartbeats 800000 in
lemma card_filtered_le_prod_of_fiber_dvd`

**Problem:**
General fiber-counting bound: If `S` is a finset of tuples in `[0, H]^n` such that
for each coordinate `j`, fixing coordinates `i < j` determines the residue class of
coordinate `j` modulo `m j`, then `|S| ≤ ∏_j (⌊H / m_j⌋ + 1)`.

The proof is by induction on `n`. At each step, project onto the first `n-1` coordinates
using `Fin.init`. The image satisfies the same property (by restriction), so the IH gives
`|image| ≤ ∏_{j<n-1}`. Each fiber has all elements in a single residue class mod `m(last)`,
so has at most `⌊H/m(last)⌋ + 1` elements.

**Solution sketch:**
Proof by induction on n.

Base case n = 0: Fin 0 → ℤ has exactly one element (the empty function). So S.card ≤ 1 = empty product.

Inductive step n → n+1: Given S : Finset (Fin (n+1) → ℤ), define f = Fin.init : (Fin (n+1) → ℤ) → (Fin n → ℤ). Let I = S.image f.

1. Each fiber {h ∈ S | f(h) = g} has card ≤ H / m(Fin.last n) + 1.
   Proof: For any two h, h' in the fiber, f(h) = f(h') = g, so h(i) = h'(i) for all i < Fin.last n (since Fin.init h = Fin.init h'). By hfib applied with j = Fin.last n, m(Fin.last n) | (h(Fin.last n) - h'(Fin.last n)). So the values h(Fin.last n) form a set with pairwise differences divisible by m(Fin.last n), all in [0,H]. Use card_set_pairwise_dvd_le to bound by H / m(last) + 1 (as reals), hence ≤ H / m(last) + 1 (as nats by Nat.cast_le).

2. I.card ≤ ∏_{j : Fin n} (H / m(j.castSucc) + 1) by IH.
   The IH needs: I satisfies the fiber property with moduli m' j = m (j.castSucc). For g, g' ∈ I with g(i) = g'(i) for all i < j: pick h, h' ∈ S with f(h) = g, f(h') = g'. Then h(castSucc i) = g(i) = g'(i) = h'(castSucc i) for all i < j. Since Fin.castSucc preserves order, h(l) = h'(l) for all l < castSucc j. By hfib, m(castSucc j) | (h(castSucc j) - h'(castSucc j)). Since g(j) = h(castSucc j) and g'(j) = h'(castSucc j), we get m(castSucc j) | (g(j) - g'(j)). ✓

3. By Finset.card_le_mul_card_image: S.card ≤ (H / m(last) + 1) * I.card ≤ (H / m(last) + 1) * ∏_{j : Fin n} (H / m(j.castSucc) + 1) = ∏_{j : Fin (n+1)} (H / m(j) + 1).

The last equality uses Fin.prod_univ_castSucc: ∏_{j : Fin (n+1)} f(j) = (∏_{j : Fin n} f(j.castSucc)) * f(Fin.last n).

---

## `theorem countTuples_bound_prop`

**Problem:**
**Proposition 3.2** (M_Γ bound):
$M_\Gamma(H) \le \prod_{j=1}^{k} \left(\frac{H}{\gamma_j} + 1\right)$
where `γ_j = gammaRow j`.

The proof: fix `h₀ = 0` and enumerate `h₁, …, hₖ` sequentially. For each `j`,
the conditions `γ_{i,j} | (hⱼ − hᵢ)` for `i < j` force `hⱼ` into a single
residue class modulo `γⱼ = lcm_{i<j} γ_{i,j}`, giving at most `⌊H/γⱼ⌋ + 1`
choices in `[0, H]`.

*Note*: The product uses `i.succ` (indices `1, …, k` in `Fin (k+1)`), matching
the paper's convention where `γ₀ = 1` contributes trivially.

**Solution sketch:**
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

---

## `theorem countTuples_bound_small_gamma`

**Problem:**
**Corollary 3.3** (first case): If each `γⱼ ≤ H` for `j = 1,…,k`, then
`M_Γ(H) ≤ 2^k · H^k / γ(Γ)`.

This follows from Proposition 3.2 since `H/γⱼ + 1 ≤ 2H/γⱼ` when `γⱼ ≤ H`.

**Solution sketch:**
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

---

## `theorem countTuples_bound_large_gamma`

**Problem:**
**Corollary 3.3** (second case): If any `γⱼ ≥ H` for `j = 1,…,k`, then
`M_Γ(H) ≤ 2^k · H^{k-1}`.

**Solution sketch:**
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

---

## `theorem gammaRow_succ_bound`

**Problem:**
Equation (3.3) from §3.1: After greedy reordering,
$$\gamma_{r+1} \le \gamma_r \cdot \gamma_{r+1, r} \le H \cdot \gamma_r.$$
This gives that `γ(Γ)` can be bounded in terms of the `γᵢⱼ` values.

**Solution sketch:**
The goal is x ≤ H * x where x = Γ.gammaRow r.castSucc. First show H ≥ 1: since k + 2 ≥ 2, take i = ⟨0, by omega⟩ and j = ⟨1, by omega⟩ which are distinct in Fin (k+2). Then Γ.pos i j (Fin.ne_of_val_ne (by omega)) gives 0 < Γ.gamma i j, and hH i j (Fin.ne_of_val_ne (by omega)) gives Γ.gamma i j ≤ H, so H ≥ 1. Then use Nat.le_mul_of_pos_left or le_mul_of_one_le_left.

---

## `theorem countTuples_refined_bound`

**Problem:**
**Corollary 3.4** (Combined bound on `M_γ(H)`):
`M_γ(H) ≤ C(k+1,2)^{Ω(γ)} · (2H+1)^k`.

*Corrected from `k.choose 2` to `(k + 1).choose 2`*: the set `countTuplesWithGammaProd k`
involves `GammaStructure (k + 1)` which has `k + 1` indices, so the relevant binomial
coefficient counts pairs among `k + 1` elements, matching `countGammaStructures_le`
instantiated at `k + 1`.

**Solution sketch:**
We need: (countTuplesWithGammaProd k γ H : ℝ) ≤ ((k+1).choose 2)^n * (2H+1)^k where n = γ.primeFactors.card.

The proof has two cases:

Case 1: k = 0. countTuplesWithGammaProd 0 γ H = Set.ncard of a set of tuples h : Fin 1 → ℤ with h 0 = 0 and ∃ Γ : GammaStructure 1 with Γ.gammaProd = γ. GammaStructure 1 has Fin 1 → Fin 1 → ℕ, gammaRow 0 = (Iio 0).lcm ... = 1, so gammaProd = 1. If γ ≠ 1, the set is empty (ncard = 0 ≤ anything). If γ = 1, n = 0, so ((1).choose 2)^0 * (2H+1)^0 = 1, and ncard ≤ 1. Actually the set for γ = 1 has exactly 1 element (h = fun _ => 0).

Case 2: k ≥ 1. We bound the set size directly. The set S ⊆ {h : Fin(k+1) → ℤ | h 0 = 0 ∧ ∀ i, 0 ≤ h i ∧ h i ≤ H}. The latter is finite with at most (H+1)^k elements (h 0 is fixed, h 1,...,h k each choose from Icc 0 H). Since (H+1) ≤ (2H+1) and ((k+1).choose 2) ≥ 1 for k ≥ 1, we get:
ncard S ≤ (H+1)^k ≤ (2H+1)^k ≤ 1 * (2H+1)^k ≤ ((k+1).choose 2)^n * (2H+1)^k.

For finiteness: S is contained in the finite set (Fintype.piFinset (fun _ => Finset.Icc 0 H)).toSet, which is finite. Use Set.Finite.subset.

For the cardinality bound: use Set.ncard_le_ncard with the superset, then bound ncard of the superset. The superset {h | h 0 = 0 ∧ ∀ i, 0 ≤ h i ∧ h i ≤ H} has ncard ≤ (H+1)^k.

---

