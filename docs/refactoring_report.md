# Refactoring Report: `Combinatorics.lean`

**File**: [Combinatorics.lean](file:///Users/nando/PoissonViaCRT/PoissonViaCRT/Combinatorics.lean)
**Lines**: 1063 | **Sorries**: 0 | **`maxHeartbeats` overrides**: 1 (line 724: 800000)

---

## Executive Summary

The file is **correct and sorry-free** — all proofs compile. The main refactoring opportunities are:

1. **Repeated inline proofs** — the same `gammaRow_pos` pattern appears ~5 times
2. **Massive comment blocks** — `PROBLEM`/`PROVIDED SOLUTION` blocks consume ~400 lines (38% of the file)
3. **Ultra-dense tactic lines** — several lines exceed 300 characters, hindering readability
4. **Equivalence-relation boilerplate** — `hR₁_equiv` / `hR₂_equiv` share structure
5. **`by exact` wrappers** — 13 occurrences flagged by `find_golfable.py`

---

## Opportunity 1: Extract `gammaRow_pos` helper ⭐ HIGH

**Pattern 1.3 (Repetitive structure)** — The same proof that `gammaRow` is positive appears at least 5 times with slight variations:

```diff
-- Lines 452, 838, 855, 912, 971 all prove variants of:
-  Nat.pos_of_ne_zero (by exact Nat.ne_of_gt ‹| Nat.pos_of_ne_zero ‹| 
-    mt Finset.lcm_eq_zero_iff.mp ‹| by intros h; obtain ⟨ j, hj ⟩ := h; 
-    have := Γ.pos j ...; aesop)
+  Γ.gammaRow_pos j
```

**Proposed helper** (place before `gammaProd_pos`, ~line 449):

```lean
-- gammaRow is always positive: it's an lcm of positive squarefree numbers (or 1 if empty).
lemma GammaStructure.gammaRow_pos (Γ : GammaStructure k) (j : Fin k) :
    0 < Γ.gammaRow j :=
  Nat.pos_of_ne_zero (Γ.gammaRow_squarefree j).ne_zero
```

**Impact**: Simplifies `gammaProd_pos` to a one-liner, and cleans up 4+ other call sites. Also enables replacing the `gammaRow ≠ 0` and `(gammaRow : ℝ) ≠ 0` patterns.

You could add a companion:

```lean
lemma GammaStructure.gammaRow_cast_ne_zero (Γ : GammaStructure k) (j : Fin k) :
    (Γ.gammaRow j : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Γ.gammaRow_pos j).ne'
```

---

## Opportunity 2: Comment block cleanup ⭐ HIGH (readability)

The file contains **~400 lines** of `PROBLEM` / `PROVIDED SOLUTION` comment blocks (lines 64–71, 79–86, 114–150, 166–182, 193–224, 250–282, 345–387, 438–447, 454–477, 491–547, 606–623, 644–678, 696–823, 871–898, 922–958, 987–995, 1006–1028).

These read like solver prompts, not documentation. **Proposed approach**:

- **Keep** a 2–3 line `-- Proof sketch:` comment before each theorem
- **Move** the full `PROBLEM`/`PROVIDED SOLUTION` text to a separate markdown file (e.g., `docs/proof_sketches.md`) or delete entirely

This would reduce the file by ~350 lines (~33%) with zero semantic change.

---

## Opportunity 3: Break ultra-dense lines ⭐ MEDIUM

Several lines exceed 300+ characters. The mathlib convention is 100 chars. Worst offenders:

| Line | Length (est.) | Content |
|------|---------------|---------|
| 96 | ~190 | `gammaRow_squarefree` inner proof |
| 98 | ~180 | `by_cases` chain in lcm induction |
| 308 | ~350 | `min'_mem` double extraction |
| 638 | ~300 | `h_map` subset proof |
| 641 | ~300 | `nlinarith` with 4 hypotheses |
| 855 | ~400 | Single line with nested `le_div_iff₀`, `Nat.cast_pos`, `Nat.ne_of_gt` |
| 912-913 | ~400 | Nested `show` with 3 levels of `Nat.ne_of_gt` |
| 980 | ~350 | `nlinarith` with `inv_mul_cancel_left₀` |

**Proposed**: Break each into multiple lines following mathlib's indentation style. Example for line 855:

```lean
-- Before (single line ~400 chars):
rw [ ← Finset.prod_const ]; rw [ ← Finset.prod_div_distrib ] ; exact Finset.prod_le_prod ...

-- After:
rw [← Finset.prod_const, ← Finset.prod_div_distrib]
exact Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => by
  rw [le_div_iff₀ (Γ.gammaRow_cast_ne_zero i.succ)]  -- uses new helper
  exact_mod_cast Nat.div_mul_le_self H (Γ.gammaRow i.succ)
```

---

## Opportunity 4: Reduce equivalence-relation boilerplate ⭐ MEDIUM

In `perm_count_eq` (lines 388–436), `hR₁_equiv` and `hR₂_equiv` are proved separately but share the same structure. You could:

1. **Extract a general constructor**: "given a GammaStructure and a function `f`, the relation `R(i,j) = p ∣ Γ.gamma (f i) (f j) ∨ i = j` is an equivalence relation."

```lean
private lemma prime_dvd_or_eq_equiv (Γ : GammaStructure k) (p : ℕ) (hp : Nat.Prime p)
    (f : Fin k → Fin k) (hf : Function.Injective f) :
    Equivalence (fun i j => p ∣ Γ.gamma (f i) (f j) ∨ i = j) := ...
```

Then `hR₁_equiv = prime_dvd_or_eq_equiv Γ p hp id Function.injective_id` and `hR₂_equiv = prime_dvd_or_eq_equiv Γ p hp σ σ.injective`.

---

## Opportunity 5: `by exact` wrapper elimination ⭐ LOW

The `find_golfable.py` script flagged 13 `by exact` wrappers. These are `have ... := by exact <term>` which can be simplified to `have ... := <term>`. Examples:

| Line | Current | Simplified |
|------|---------|------------|
| 77 | `exact dvd_trans (...) (...)` | Already clean — false positive (proof is term-mode `by exact`) |
| 125 | `exact (gammaRow_squarefree Γ j).natFactorization_le_one p` | Could be term-mode directly |
| 656 | `exact Int.dvd_trans ...` | Direct term |

Most of these are minor style improvements.

---

## Opportunity 6: Mathlib leverage ⭐ LOW

A few places could potentially use existing mathlib lemmas more directly:

- **`gammaRow_squarefree`** (lines 87–112): The proof that lcm of squarefree numbers is squarefree is 25 lines. Check if `Squarefree.lcm` or a factorization-based approach exists in newer mathlib.
- **`factorization_gammaRow_eq`** (lines 151–164): The backward direction (lines 160–164) is quite dense. `Nat.Prime.dvd_finset_lcm_iff` might simplify this if it exists.
- **`Nat.factorization_eq_one_of_squarefree`** (line 159): This is used cleanly — good.

---

## Recommended Execution Order

1. **Extract `gammaRow_pos`** + `gammaRow_cast_ne_zero` helpers → compile → commit
2. **Break ultra-dense lines** (top 5 worst) → compile → commit
3. **Extract `prime_dvd_or_eq_equiv`** → compile → commit
4. **Clean comment blocks** (move to separate file or trim) → compile → commit
5. **Minor: `by exact` cleanup** → compile → commit

> [!TIP]
> Each step should be validated with `lake build` before proceeding to the next.

---

## `maxHeartbeats` Note

Line 724 has `set_option maxHeartbeats 800000`. This is 4× the default (200000). The proof `card_filtered_le_prod_of_fiber_dvd` is an induction with heavy `simp_all` calls. Refactoring to break sub-goals into helpers could potentially reduce this, but it's low priority since it compiles.
