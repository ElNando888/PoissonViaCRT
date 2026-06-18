# Evaluation of the Gemini large-γ proposal, and a detailed implementation blueprint

*Scope.* This document responds to two requests:
1. **Evaluate** the proposal in `LARGE_GAMMA_INFRASTRUCTURE_BLUEPRINT.md` (the
   Gemini sketch): is the strategy *sound* and *faithful to Granville–Kurlberg
   (GK08, arXiv:math/0412135v2, §4)?*
2. **Only if** the strategy is sound, produce a more detailed blueprint for the
   missing infrastructure.

The conclusion is that the **high-level strategy is sound and faithful**, so the
detailed blueprint is given in Parts IV–VI. However, the Gemini sketch is written
*as if the large-γ machinery does not yet exist*, whereas a large fraction of it
is already present and proved in the repository. The genuinely missing piece is
both **smaller and more specific** than the sketch suggests, and one of the
already-present "joint" lemmas is in fact the *wrong* tool for it. Part III
documents the true state of the code; Part IV pinpoints the real gap.

---

## Part I. Verdict

**The strategy is SOUND and FAITHFUL to GK08 §4**, subject to the corrections in
Parts III–IV. Concretely:

* The diagnosis is correct. The obstruction to `deviation_large_divisors`
  (`PoissonViaCRT/MobiusSynthesis.lean:230`, the *only* target `sorry` left in
  the project) is the explosion of the Euler product over collision primes: after
  the mean-collapse algebra the weight of a collision prime `p ∣ γ` becomes
  `(p/|Ω_p|)^k ≈ k^k > 1`, and the small-γ engine
  (`gamma_sum_le_euler_factor_small_gamma`) supplies no `γ`-decay to absorb it.

* The proposed cure — partition the `γ`-sum into GK Corollary 5 tuple-graph
  regimes `τ` and feed each band a *sharp* count `M_γ(H) ≪ H^{n+1/2}/γ^{α(τ)}`,
  so that the `1/γ^{α(τ)}` saving becomes a per-collision-prime weight
  `p^{β(τ)-α(τ)}` with `α(τ) ≈ 1` — is exactly the mechanism GK08 use in §4. This
  is the faithful route, and it is the route the repository's architecture has
  been built around (the `perGammaDeviationWeight` / `countTuplesWithGammaProd`
  fibering is the §3.1–§4 absolute-value-plus-counting method, **not** an L2 /
  second-moment method).

* The competing pessimistic analysis in
  `docs/deviation_large_divisors_analysis.md` ("the γ-route is doomed, use the L2
  second-moment method") is **stale and should not be followed**. Its numerical
  counterexample is against the *naive uniform Rankin trick* of the GK §3.2
  sketch — which GK themselves note diverges and repair in §4 by regime-splitting
  — not against the regime-split Proposition 4.2 route. Moreover the L2 /
  `FourierANOVA` route was already attempted and purged from the repository as
  incompatible with the spatial geometry (see `README.md`). So GK §4 tuple
  counting is the correct and faithful path, and Gemini points at it correctly.

**Caveat that changes the work plan (Parts III–IV).** Gemini proposes to *create*
`gamma_sum_le_euler_factor_large_gamma` and a sharp count. Both already exist and
are proved. The existing large-γ engine, however, routes the sharp count through
the **exponent-1 radical engine** `core_gamma_euler_sum`, which can only consume
`radical γ / γ` and therefore **discards the per-prime `γ^{-α}` saving**,
converting it into a global `H^{(1-α)·w(τ)}` inflation. That is precisely why it
does not cure the `k^k` explosion. The real missing infrastructure is a
**fractional-exponent Euler engine** that consumes `radical γ / γ^{α}` directly.

---

## Part II. Faithfulness check against GK08 §4

GK08 bound `∑_h |∏_{p∈T}(N_p(h)−μ_p)|` by fibering over the *gamma product*
`γ(h)` (the collision structure of the tuple `(0,h)`), giving
`∑_γ w(γ)·M_γ(H)` where `M_γ(H)` counts box tuples with that gamma product. The
repository mirrors this exactly:

| GK08 §3.1–§4 object | Repository declaration |
|---|---|
| gamma product `γ(h)` | `gammaProdOfBoxPoint` |
| per-γ weight `w(γ)` | `perGammaDeviationWeight` |
| tuple count `M_γ(H)` | `countTuplesWithGammaProd` |
| `∑_h|…| ≤ ∑_γ w(γ)M_γ(H)` | `deviation_sum_le_gamma_sum` |
| small-γ count `M_γ ≪ H^k/γ` | `countTuplesWithGammaProd_small_gamma` |
| Cor. 5 thresholds `w(τ)` | `tupleBoundWeight` |
| Cor. 5 sharp count `M_γ ≪ H^{n+1/2}/γ^α` | `countTuplesWithGammaProd_large_gamma_sharp` |
| Prop 4.2 three-line bound | `gk08_proposition_4_2` |
| §4 regime-split over `d=∏_{p∈T}p` | `split_divisor_sum` |

The three-line decomposition of Proposition 4.2 (small-`d` uniform / large-`d`
tail / tuple-counting `τ`-sum) is reproduced faithfully in the statements of
`gk08_proposition_4_2` (with two documented faithfulness corrections: an explicit
box-volume `(H+1)^{k-1}` and a `1 + C·p^β·(1+A_p)` per-prime factor instead of
`1 + C·p^β·A_p`). The Rankin trick is `rankin_powerset_bound`, and Euler-product
convergence is `euler_product_converges`. **Nothing in Gemini's strategy departs
from this faithful template.** The proposed `α(τ) ≈ 1`, `β(τ)` parameter balance
is GK08 Lemma 6.

**Conclusion of Part II.** The strategy is faithful. It does not introduce any
mechanism foreign to GK08, and it targets exactly the regime (large `γ`) that the
repository's Prop 4.2 has not yet genuinely covered (see Part III).

---

## Part III. The true current state (correcting the sketch's premises)

The Gemini sketch assumes the large-γ engine and sharp count must be *built*.
Here is what is **already present and `sorry`-free**:

1. **Sharp large-γ count — DONE.**
   `countTuplesWithGammaProd_large_gamma_sharp (n γ H α) :`
   `M_γ(H) ≤ C^{ω(γ)}·2^n·H^{n+1/2}/γ^{α}` for `0<γ≤H^{2/α²}`, `1<H`, `0<α`.

2. **A large-γ Euler engine already exists** —
   `gamma_sum_le_euler_factor_large_gamma`. **But it is the wrong shape.** It
   feeds the sharp count into `core_gamma_euler_sum`, which only accepts the
   exponent-1 weight `radical γ / γ`. To do so it rewrites
   `radical γ / γ^{α} = (radical γ/γ)·γ^{1-α}` and bounds `γ^{1-α} ≤
   H^{(1-α)·w(τ)}`. The honest output is therefore
   `2^{k-1}·H^{(k-1)+1/2+(1-α)w(τ)}·∏_{p∈T}(2·2^{C(k,2)} + A_p)` — the per-prime
   factor carries a **bare constant** on collision primes (no `p^{-α}`
   suppression), and the `γ`-decay has been spent on a *larger* `H`-power. This
   does **not** absorb the `k^k` mean-collapse growth. The in-file docstring of
   this lemma already admits the originally conjectured GK exponent
   `(k-1)-τ+α·w(τ)` "is not derivable from this radical-regrouping route."

3. **`gk08_proposition_4_2` is proved but covers the wrong γ-range.** Its
   sub-lemma `gk08_prop42_small_divisors` filters `γ ∈ Icc 1 H` (small γ only),
   and its proof discharges the left side by **Line 1 alone**, leaving the Line-3
   `τ`-sum as pure nonnegative slack (`le_add_of_le_of_nonneg`). Meanwhile the
   bridge `deviation_sum_le_gamma_sum` produces a sum over `γ ∈ Icc 1 (H^{k·k})`.
   So the large-γ band `(H, H^{k²}]` — the entire difficulty — is **not actually
   bounded** by the current Proposition 4.2, and `gamma_sum_le_euler_factor_large_gamma`
   is **dead code**: nothing consumes it.

4. **`gk08_proposition_4_2` is disconnected from `deviation_large_divisors`.**
   A project-wide search shows `gk08_proposition_4_2` has no consumers; the target
   `sorry` in `MobiusSynthesis.lean` is reached through a different (per-T L2)
   wiring that was never completed.

5. **A "joint" sharp count exists but is a trap for this purpose.**
   `countTuplesWithGammaProd_large_gamma_sharp_joint` gives
   `radical γ · M_γ(H) ≤ C^{ω}·2^n·H^{n+1/2}·∏_{p∣γ} p^{1-α}`. The factor
   `∏_{p∣γ}p^{1-α}` *depends only on the support* of `γ`, not on the
   multiplicities. Summed over all `γ` with a fixed prime support `R` (infinitely
   many multiplicities up to `N`), `∑_γ ∏_{p∈R}p^{1-α}` **diverges** (grows like
   `(log N)^{|R|}`). So this joint lemma has already thrown away the multiplicity
   decay that makes the `γ`-sum converge. It must **not** be used as the input to
   the new engine. The correct input keeps the denominator intact:
   `radical γ / γ^{α}` (whose multiplicity sum *does* converge — see Part IV).

**Net effect.** The work is *smaller* than Gemini imagines (the counting side is
done), but *different in shape*: one must build a **fractional-exponent Euler
engine** consuming `radical γ / γ^{α}`, rewire the large-γ engine through it, fix
the γ-range to `Icc 1 (H^{k·k})`, and then connect Prop 4.2 to
`deviation_large_divisors` through the mean-collapse algebra and the Lemma 6
parameter balance.

---

## Part IV. The genuine gap: a fractional-exponent radical Euler engine

The existing engine is built on
`sum_rad_div_eq_le_pow_two : ∑_{γ:pf=R} radical γ/γ ≤ 2^{|R|}`,
proved by mapping `γ ↦ γ/radical γ` onto the `R`-smooth numbers and summing
`∑_{R-smooth m} 1/m`. The fractional analogue is provable by the **same
technique**, and crucially it *converges*:

> Write `γ = radical(γ)·m` with `m := γ/radical γ` `R`-smooth. Then
> `radical γ / γ^{α} = radical(γ)^{1-α} / m^{α} = (∏_{p∈R}p)^{1-α} / m^{α}`, so
> `∑_{γ:pf=R, γ≤N} radical γ/γ^{α} ≤ (∏_{p∈R}p^{1-α})·∑_{R-smooth m} m^{-α}
> = ∏_{p∈R} p^{1-α}/(1-p^{-α}) ≤ C_α^{|R|}·∏_{p∈R} p^{1-α}`,
> with `C_α := 1/(1-2^{-α})` (since `p ≥ 2`).

This is finite for every `α ∈ (0,1]`, and the per-prime factor is exactly the
`p^{1-α}` collision weight GK08 §4 needs. The required new declarations:

```lean
/-- Fractional radical-regrouping (single fibre). -/
lemma sum_rad_div_rpow_le_pow (R : Finset ℕ) (hR : ∀ p ∈ R, Nat.Prime p)
    (N : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∑ γ ∈ (Finset.Icc 1 N).filter (fun γ => γ.primeFactors = R),
        (radical γ : ℝ) / (γ : ℝ) ^ α
      ≤ (1 / (1 - (2:ℝ)^(-α))) ^ R.card * ∏ p ∈ R, (p : ℝ) ^ (1 - α) := by
  sorry  -- smooth-number map + ∑_{R-smooth} m^{-α} = ∏_{p∈R} 1/(1-p^{-α})

/-- Fractional-exponent core Euler engine (generalises `core_gamma_euler_sum`
    from the exponent `1` to `α ≤ 1`). -/
lemma core_gamma_euler_sum_frac (T : Finset ℕ) (hT : ∀ p ∈ T, Nat.Prime p)
    (N : ℕ) (B : ℝ) (hB : 1 ≤ B) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (weil : ℕ → ℝ) (hweil : ∀ p ∈ T, 0 ≤ weil p) :
    ∑ γ ∈ (Finset.Icc 1 N).filter (fun γ => γ.primeFactors ⊆ T),
        (radical γ : ℝ) / (γ : ℝ) ^ α * B ^ γ.primeFactors.card *
          ∏ p ∈ T \ γ.primeFactors, weil p
      ≤ ∏ p ∈ T, ((1 / (1 - (2:ℝ)^(-α))) * B * (p : ℝ) ^ (1 - α) + weil p) := by
  sorry  -- copy `core_gamma_euler_sum`, swap in `sum_rad_div_rpow_le_pow`
```

These two are the **only mathematically new pieces**; everything below is
algebraic plumbing and parameter bookkeeping that follows the patterns already in
the file.

---

## Part V. Detailed blueprint (decomposed, with signatures)

All declarations live in `PoissonViaCRT/GammaDeviationSynthesis.lean` unless
noted. `n := k-1` throughout. Build bottom-up; each step is independently
provable and should be attempted as a focused lemma.

### Step 1 — Fractional engine (the only new mathematics)
* `sum_rad_div_rpow_le_pow` (in `GammaEulerSumHelpers.lean`, next to
  `sum_rad_div_eq_le_pow_two`). *Risk: medium.* Reuse the smooth-number injection
  already used for the `α=1` case; the new ingredient is
  `∑_{R-smooth m, m≤N} m^{-α} ≤ ∏_{p∈R} 1/(1-p^{-α})`, a finite Euler product
  bounded by `Summable`/geometric arguments analogous to the existing
  `h_geo_sum`.
* `core_gamma_euler_sum_frac` (in `GammaEulerSumHelpers.lean`). *Risk: low.*
  Structurally identical to `core_gamma_euler_sum`; only `sum_rad_div_eq_le_pow_two`
  is replaced by `sum_rad_div_rpow_le_pow`, and `Finset.prod_add` decouples the
  result.

### Step 2 — A *correct* per-band large-γ engine
Replace the radical-regrouping `gamma_sum_le_euler_factor_large_gamma` with a
version that keeps the per-prime saving:

```lean
private lemma gamma_band_euler_factor (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 2 ≤ k)
    (Ω : ∀ p, Finset (ZMod p)) (hΩle : ∀ p, p.Prime → (Ω p).card ≤ p)
    (T : Finset ℕ) (hT_prime : ∀ p ∈ T, Nat.Prime p) (H : ℕ) (hH : 1 < H)
    (τ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hαw : tupleBoundWeight (k-1) τ ≤ 2 / α ^ 2) :
    ∑ γ ∈ (Finset.Icc 1 (H ^ (k*k))).filter (fun γ => γ.primeFactors ⊆ T ∧
        (H:ℝ) ^ tupleBoundWeight (k-1) (τ-1) < (γ:ℝ) ∧
        (γ:ℝ) ≤ (H:ℝ) ^ tupleBoundWeight (k-1) τ),
      perGammaDeviationWeight ε k Ω T γ * (countTuplesWithGammaProd (k-1) γ H : ℝ)
    ≤ 2 ^ (k-1) * (H:ℝ) ^ ((k-1:ℝ) + 1/2) *
        ∏ p ∈ T, (Cα α * 2 ^ Nat.choose k 2 * (p:ℝ) ^ (1-α)
                  + (1 - (Ω p).card / (p:ℝ)) * (p:ℝ) ^ (-ε) * localMean k Ω p) := by
  sorry  -- multiply count by radical γ, feed `radical γ/γ^α` into
         -- `core_gamma_euler_sum_frac`; note the H-power is now (k-1)+1/2, with
         -- NO (1-α)·w(τ) inflation — the saving lives on the primes as p^{1-α}.
```

*Key difference from the current lemma:* the `H`-exponent is `(k-1)+1/2`
(independent of `τ`) and each collision prime carries `p^{1-α}`. With `α(τ)≈1`
this is `p^{0+}`, i.e. essentially bounded, and the Rankin step (Step 4) upgrades
it to `p^{β(τ)}`.

### Step 3 — Choosing `α(τ)` per band
* `def alphaOf (n τ : ℕ) : ℝ := Real.sqrt (2 / tupleBoundWeight n τ)` (or any
  value `≤ √(2/w(τ))` and `≤ 1`), so the band hypothesis
  `tupleBoundWeight n τ ≤ 2/α²` holds by construction.
* `alphaOf_pos`, `alphaOf_le_one`, `alphaOf_band_ok` — small real-analysis
  lemmas. *Risk: low.* (`tupleBoundWeight n τ = n+1-9/8+(τ-1/2)²/2 > 0`.)

### Step 4 — Selective Rankin on the large-`d` band and tail
Reuse `rankin_powerset_bound`. For the large-`d` regime apply the weight
`(∏_{p∈T}p / s^R)^{β}`; this attaches `p^{β}` to each prime and extracts
`s^{-βR}`, turning the Step-2 per-prime factor `c·p^{1-α}+A_p` into
`1 + C·p^{β-α}·(1+A_p)` after `Finset.prod_add`. Package as:
* `gk08_band_large_d (… τ α β …)` — Line-3 term for band `τ`.
* Keep `gk08_prop42_small_divisors` (Line 1) and `gk08_prop42_large_divisors`
  (Line 2) **but re-target their γ-range to `Icc 1 (H^{k·k})`**, splitting
  `Icc 1 (H^{k·k}) = Icc 1 H ⊎ ⋃_τ band(τ)` via `tupleBoundWeight` monotonicity.

### Step 5 — Reassemble `gk08_proposition_4_2` over the *full* range
Restate the three lines with the γ-filter `Icc 1 (H^{k*k})` (matching the bridge),
and prove it by:
`split γ-range → small-γ (Line 1+2) + ∑_τ band(τ) (Line 3)`. The Line-3 sum is
now *load-bearing*, not slack. *Risk: medium (bookkeeping).*

### Step 6 — Lemma 6 parameter balance (the decisive arithmetic)
Provide concrete `R, α₀, α₁, β₁` and functions `α(τ), β(τ)` (GK08 Lemma 6) and a
lemma:
```lean
lemma gk08_lemma6_exponents_neg (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 2 ≤ k) :
    ∃ R α₀ α₁ β₁ (α β : ℕ → ℝ), 0 ≤ R ∧ R ≤ 1 ∧ 0 < α₀ ∧ 0 < α₁ ∧ 0 < β₁ ∧
      (∀ τ, 0 < α τ) ∧ (∀ τ, 0 ≤ β τ) ∧
      -- every s-exponent appearing in Prop 4.2 (after mean-collapse) is ≤ -ε/2:
      (α₀ * R - 1 ≤ -(ε/2)) ∧ (α₁ - β₁ * R - 1 ≤ -(ε/2)) ∧
      (∀ τ ∈ Finset.range (tauOne (k-1) + 1),
        ((k:ℝ)-1) + 1/2 + (1 - α τ) * tupleBoundWeight (k-1) τ - β τ * R - 1
          ≤ -(ε/2)) := by
  sorry
```
This is the heart of GK08 §4 and the highest-risk step. *Numerically validate the
chosen parameters with `#eval`/`norm_num` for `k = 2,3,4` before attempting the
general proof.* The `-1` terms come from the mean-collapse normalisation in Step 7.

### Step 7 — Mean-collapse and connection to `deviation_large_divisors`
The target sum in `MobiusSynthesis.lean` carries the prefactor
`(1/|Ω_q|)·∏_{p∈q∖T} localMean`. Provide:
* `mean_collapse` — algebra showing
  `(1/|Ω_q|)·∏_{p∈q∖T} localMean · perGammaDeviationWeight …` equals the
  Prop 4.2 weight times `s^{-(k-1)}` (this contributes the `-1` shift and turns
  the box volume `(H+1)^{k-1} ≍ s^{k-1}` into the `s^{0}` after collapse; use
  `localMean_mul_inv_card`).
* `deviation_large_divisors_via_prop42` — bound each `|inner_T|` by
  `deviation_sum_le_gamma_sum`, sum over the large-`d` `T`'s, apply the
  full-range `gk08_proposition_4_2`, collapse, and invoke
  `gk08_lemma6_exponents_neg` plus `euler_product_converges` (with
  `combinedEulerWeight_le`) to bound the Euler products by an absolute constant.
  Conclude `≤ K₂·s^{-ε/2}`. *Risk: high (it is the capstone). Decompose by
  proving the three Prop-4.2 lines collapse to `s^{-ε/2}` separately first.*

### Step 8 — Cleanup
Delete the now-superseded radical-regrouping `gamma_sum_le_euler_factor_large_gamma`
and the unused `countTuplesWithGammaProd_large_gamma_sharp_joint` /
`radical_div_rpow_le_prod_primeFactors_rpow` (or repurpose the latter's proof
inside `sum_rad_div_rpow_le_pow`). Verify with `#print axioms` that only
`propext`, `Classical.choice`, `Quot.sound` (plus the deliberate
`AnalyticInputs.lean` `admit`-placeholders, which are out of scope) are used.

---

## Part VI. Risks, dependencies, and a recommended order

* **Lowest risk, do first:** Steps 1–3 (fractional engine + `α(τ)` choice). These
  are self-contained and reuse existing techniques; they also immediately fix the
  dead `gamma_sum_le_euler_factor_large_gamma`.
* **Medium:** Steps 4–5 (Rankin + range reassembly) — algebraic, pattern-matched
  to existing proofs.
* **Highest risk:** Step 6 (Lemma 6 balance) and Step 7 (mean-collapse capstone).
  Validate Step 6 numerically before formalising; decompose Step 7 line-by-line.
* **Do not** use `countTuplesWithGammaProd_large_gamma_sharp_joint` as the engine
  input (Part III.5) — it diverges over multiplicities.
* **Do not** revive the L2/`FourierANOVA`/second-moment route (Part I); it was
  purged as geometry-incompatible and is not what GK08 do here.

**Bottom line.** Gemini's strategy is the right one and is faithful to GK08 §4.
The actual remaining work is one genuinely new analytic engine
(`sum_rad_div_rpow_le_pow` + `core_gamma_euler_sum_frac`), a rewiring of the
already-present large-γ count through it, an honest reassembly of Proposition 4.2
over the full `Icc 1 (H^{k·k})` range, and the GK08 Lemma 6 parameter balance
feeding the mean-collapse capstone in `MobiusSynthesis.lean`.
