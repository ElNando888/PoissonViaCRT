/-
Copyright (c) 2026 Math Inc. All rights reserved.
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Real.Basic

lemma natCast_le_div (a b n : ℕ) (h : a ≤ b / n) :
    (a : ℝ) ≤ (b : ℝ) / n := by
  have h1 : (a : ℝ) ≤ ((b / n : ℕ) : ℝ) := by exact_mod_cast h
  have h2 : ((b / n : ℕ) : ℝ) ≤ (b : ℝ) / n := by
    simpa using (Nat.cast_div_le (α := ℝ) (m := b) (n := n))
  exact le_trans h1 h2

lemma card_sq_eq_le_two
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (a : F) :
    Fintype.card {y : F // y ^ 2 = a} ≤ 2 := by
  classical
  -- Inject the solution set into the finset of `nthRoots 2 a`.
  have h_inj :
      Fintype.card {y : F // y ^ 2 = a} ≤
        Fintype.card (↥(Polynomial.nthRoots 2 a).toFinset) :=
    Fintype.card_le_of_injective
      (fun y : {y : F // y ^ 2 = a} =>
        (⟨y.1, by
            have : (y.1 : F) ∈ Polynomial.nthRoots 2 a := by
              exact (Polynomial.mem_nthRoots (R := F) (a := a) (x := y.1)
                (by decide : 0 < 2)).2 y.2
            simpa using this⟩ :
          (Polynomial.nthRoots 2 a).toFinset))
      (by
        intro y₁ y₂ h
        apply Subtype.ext
        exact congrArg (Subtype.val : (↥((Polynomial.nthRoots 2 a).toFinset)) → F) h)
  have h_fin : Fintype.card (↥(Polynomial.nthRoots 2 a).toFinset) ≤ 2 := by
    let s : Finset F := (Polynomial.nthRoots 2 a).toFinset
    have hs : Fintype.card (↥s) = s.card := Fintype.card_coe s
    have hs' : s.card ≤ 2 :=
      (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 2 a)
    -- Avoid `simp` rewriting the subtype `↥s` back into `{x // x ^ 2 = a}`.
    rw [hs]
    exact hs'
  exact le_trans h_inj h_fin
