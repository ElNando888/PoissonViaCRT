/-
Copyright (c) 2026 Math Inc. All rights reserved.
-/

import PoissonViaCRT.RHC.StepanovPolynomial
import PoissonViaCRT.RHC.Utils
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.NormNum.RealSqrt

noncomputable def hyperellipticCurve (F : Type*) [Field F] (f : Polynomial F) : Set (F × F) :=
  {p | p.2 ^ 2 = Polynomial.eval p.1 f}

lemma hasse_vanishing_card_bound (F : Type*) [Field F] [DecidableEq F] (r : Polynomial F) (ℓ : ℕ) (S : Finset F)
    (hr : r ≠ 0) (hℓ_pos : 0 < ℓ) (hvan : ∀ x ∈ S, ∀ k < ℓ, (hasseDerivOp F k r).eval x = 0) :
    (S.card : ℝ) ≤ (r.natDegree : ℝ) / ℓ := by
  let s : F → Polynomial F := fun x => (Polynomial.X - Polynomial.C x) ^ ℓ
  have hpair_all : Pairwise fun x y : F => IsCoprime (s x) (s y) := by
    have hlin :
        Pairwise fun x y : F =>
          IsCoprime (Polynomial.X - Polynomial.C x)
            (Polynomial.X - Polynomial.C y) := by
      simpa [Function.onFun] using
        (Polynomial.pairwise_coprime_X_sub_C (K := F)
          (s := fun x : F => x) (H := fun {x} {y} h => h))
    exact hlin.mono fun x y hcop => by
      simpa [s] using (IsCoprime.pow hcop : _)
  have hprod_dvd : (∏ x ∈ S, s x) ∣ r := by
    refine
      Finset.prod_dvd_of_coprime (t := S) (s := s) (z := r) ?_ ?_
    · intro x hx y hy hxy
      simpa [Function.onFun] using hpair_all hxy
    · intro x hx
      simpa [s] using
        hasse_divisibility (F := F) (f := r) (a := x) (ℓ := ℓ) (hvan x hx)
  have hP_nat_eq :
      ((∏ x ∈ S, s x : Polynomial F).natDegree) = S.card * ℓ := by
    calc
      ((∏ x ∈ S, s x : Polynomial F).natDegree)
          = ∑ x ∈ S, (s x).natDegree := by
              simpa using
                (Polynomial.natDegree_prod_of_monic (s := S) (f := s)
                  (by
                    intro x hx
                    simpa [s] using (Polynomial.monic_X_sub_C x).pow ℓ))
      _ = ∑ x ∈ S, ℓ := by
            simp [s]
      _ = S.card * ℓ := by simp
  have h_nat' : S.card * ℓ ≤ r.natDegree := by
    have hnat_le :
        ((∏ x ∈ S, s x : Polynomial F).natDegree) ≤ r.natDegree :=
      (Polynomial.natDegree_le_iff_degree_le).2
        ((Polynomial.degree_le_of_dvd
            (p := ∏ x ∈ S, s x) (q := r) hprod_dvd hr).trans
          (Polynomial.degree_le_natDegree (p := r)))
    simpa [hP_nat_eq] using hnat_le
  have hℓ_pos' : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ_pos
  have h_real_mul : (S.card : ℝ) * (ℓ : ℝ) ≤ (r.natDegree : ℝ) := by
    exact_mod_cast h_nat'
  have hne : (ℓ : ℝ) ≠ 0 := ne_of_gt hℓ_pos'
  simpa [mul_comm, mul_left_comm, mul_assoc, hne, div_eq_mul_inv] using
    (mul_le_mul_of_nonneg_right h_real_mul (inv_nonneg.mpr hℓ_pos'.le))

lemma ceil_sqrt_le_div_three (q : ℕ) (hq : 15 ≤ q) : Nat.ceil (Real.sqrt q) ≤ q / 3 :=
by
  set k : ℕ := q / 3 with hk
  have hqR : (15 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq_le : q ≤ 3 * k + 2 := by
    have hmod : q % 3 ≤ 2 := Nat.lt_succ_iff.mp (Nat.mod_lt q (by decide : 0 < 3))
    have hdecomp : 3 * k + q % 3 = q := by
      simpa [hk, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using (Nat.div_add_mod q 3)
    have : 3 * k + q % 3 ≤ 3 * k + 2 := Nat.add_le_add_left hmod _
    simpa [hdecomp] using this
  have hk_le : (q : ℝ) / 3 - 1 ≤ (k : ℝ) := by
    have hq_leR : (q : ℝ) ≤ (3 : ℝ) * (k : ℝ) + 2 := by exact_mod_cast hq_le
    nlinarith [hq_leR]
  have hq_le_k2 : (q : ℝ) ≤ (k : ℝ) ^ 2 := by
    have hq_le_tmp : (q : ℝ) ≤ ((q : ℝ) / 3 - 1) ^ 2 := by nlinarith [hqR]
    have htmp_nonneg : 0 ≤ (q : ℝ) / 3 - 1 := by nlinarith [hqR]
    have hs : ((q : ℝ) / 3 - 1) ^ 2 ≤ (k : ℝ) ^ 2 := by
      simpa [pow_two] using mul_self_le_mul_self htmp_nonneg hk_le
    exact hq_le_tmp.trans hs
  have hsqrt_le : Real.sqrt (q : ℝ) ≤ (k : ℝ) := by
    refine (Real.sqrt_le_iff).2 ⟨by exact_mod_cast (Nat.zero_le k), ?_⟩
    simpa [pow_two] using hq_le_k2
  have : Nat.ceil (Real.sqrt (q : ℝ)) ≤ k := Nat.ceil_le.2 hsqrt_le
  simpa [hk] using this

lemma riemann_hypothesis_stepanov_bound (F : Type*) [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
    (f : Polynomial F) (q : ℕ) (a : F) (hq : q = Fintype.card F) (hm3 : 3 ≤ f.natDegree)
    (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F), g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
    (hq6m : q > 6 * f.natDegree) [DecidablePred (fun x : F => x ∈ S_a F f ((q - 1) / 2) a)] :
    (Fintype.card {x : F // x ∈ S_a F f ((q - 1) / 2) a} : ℝ) <
      (q : ℝ) / 2 + 2 * (f.natDegree : ℝ) * (Nat.ceil (Real.sqrt q) : ℝ) := by
  set m : ℕ := f.natDegree with hm_def
  have h18_lt_q : 18 < q := by
    have h18_le_6m : 18 ≤ 6 * m := by
      have hm3' : 3 ≤ m := by simpa [hm_def] using hm3
      simpa using Nat.mul_le_mul_left 6 hm3'
    exact lt_of_le_of_lt h18_le_6m (by simpa [hm_def] using hq6m)
  have h15_le_q : (15 : ℕ) ≤ q :=
    le_trans (by decide : (15 : ℕ) ≤ 19) (Nat.succ_le_of_lt h18_lt_q)
  have hq_pos_nat : 0 < q := lt_trans (by decide : 0 < 18) h18_lt_q
  set ℓ : ℕ := Nat.ceil (Real.sqrt q) with hℓ_def
  have hℓ_le_q_div3 : ℓ ≤ q / 3 := by
    simpa [ℓ, hℓ_def] using ceil_sqrt_le_div_three q h15_le_q
  have h_sqrt_le_ℓ : Real.sqrt q ≤ (ℓ : ℝ) := by simpa [ℓ, hℓ_def] using Nat.le_ceil (Real.sqrt q)
  have hℓ_pos_real : 0 < (ℓ : ℝ) :=
    lt_of_lt_of_le (Real.sqrt_pos.mpr (by exact_mod_cast hq_pos_nat)) h_sqrt_le_ℓ
  have hℓ_pos : 0 < ℓ := by exact_mod_cast hℓ_pos_real
  obtain ⟨R, hR_ne, hdegR, hvan⟩ :=
    stepanov_polynomial (F := F) (hF := hF) (f := f) (q := q) (ℓ := ℓ) (a := a)
      hq hm3 hnsq hq6m hℓ_pos hℓ_le_q_div3
  set Sfin : Finset F :=
      Finset.univ.filter (fun x : F => x ∈ S_a F f ((q - 1) / 2) a)
  have hvan_S : ∀ x ∈ Sfin, ∀ k < ℓ, (hasseDerivOp F k R).eval x = 0 := by
    intro x hx k hk
    rcases Finset.mem_filter.mp hx with ⟨_, hx_sa⟩
    exact hvan x hx_sa k hk
  have h_card_le :
      (Fintype.card {x : F // x ∈ S_a F f ((q - 1) / 2) a} : ℝ) ≤ (R.natDegree : ℝ) / (ℓ : ℝ) := by
    have h_card_Sfin_le :
        (Sfin.card : ℝ) ≤ (R.natDegree : ℝ) / (ℓ : ℝ) :=
      hasse_vanishing_card_bound (F := F) (r := R) (ℓ := ℓ) (S := Sfin) hR_ne hℓ_pos hvan_S
    have h_card_subtype_eq :
        (Fintype.card {x : F // x ∈ S_a F f ((q - 1) / 2) a} : ℝ) = (Sfin.card : ℝ) := by
      exact_mod_cast (by simp [Sfin] :
        Fintype.card {x : F // x ∈ S_a F f ((q - 1) / 2) a} = Sfin.card)
    simpa [h_card_subtype_eq] using h_card_Sfin_le
  have hdegR' :
      (R.natDegree : ℝ) < (m : ℝ) * (q : ℝ) + (ℓ : ℝ) * (q : ℝ) / 2 + (ℓ : ℝ) ^ 2 * (m : ℝ) := by
    simpa [m, hm_def, pow_two, mul_assoc, mul_left_comm, mul_comm] using hdegR
  have hdegR_upper :
      (R.natDegree : ℝ) < (ℓ : ℝ) * (q : ℝ) / 2 + 2 * (m : ℝ) * (ℓ : ℝ) ^ 2 := by
    have hq_le_ℓsq : (q : ℝ) ≤ (ℓ : ℝ) ^ 2 := by
      have h := mul_self_le_mul_self (Real.sqrt_nonneg (q : ℝ)) h_sqrt_le_ℓ
      simpa [pow_two,
        Real.mul_self_sqrt (by exact_mod_cast (Nat.zero_le q) : (0 : ℝ) ≤ (q : ℝ))] using h
    have hmq : (m : ℝ) * (q : ℝ) ≤ (m : ℝ) * (ℓ : ℝ) ^ 2 := by
      have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
      exact mul_le_mul_of_nonneg_left hq_le_ℓsq hm_nonneg
    nlinarith [hdegR', hmq]
  have hdeg_div_main :
      (R.natDegree : ℝ) / (ℓ : ℝ) < (q : ℝ) / 2 + 2 * (m : ℝ) * (ℓ : ℝ) := by
    have hℓ_ne : (ℓ : ℝ) ≠ 0 := ne_of_gt hℓ_pos_real
    have hdiv := div_lt_div_of_pos_right hdegR_upper hℓ_pos_real
    have hsimp :
        ((ℓ : ℝ) * (q : ℝ) / 2 + 2 * (m : ℝ) * (ℓ : ℝ) ^ 2) / (ℓ : ℝ)
          = (q : ℝ) / 2 + 2 * (m : ℝ) * (ℓ : ℝ) := by field_simp [hℓ_ne]
    simpa [hsimp] using hdiv
  have hmain :
      (Fintype.card {x : F // x ∈ S_a F f ((q - 1) / 2) a} : ℝ) < (q : ℝ) / 2 + 2 * (m : ℝ) * (ℓ : ℝ) :=
    lt_of_le_of_lt h_card_le hdeg_div_main
  simpa [m, hm_def, ℓ, hℓ_def] using hmain

lemma riemann_hypothesis_upper_bound (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (f : Polynomial F) (q : ℕ) (hq : q = Fintype.card F)
    (hm3 : 3 ≤ f.natDegree)
    (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
        g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
    (hq6m : q > 6 * f.natDegree) (hodd : ringChar F ≠ 2) :
    (Fintype.card {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f} : ℝ) <
      (q : ℝ) + 4 * (f.natDegree : ℝ) * (Nat.ceil (Real.sqrt q) : ℝ) :=
by
  classical
  set c := (q - 1) / 2 with hc_def
  set m := f.natDegree with hm_def
  have h_stepanov := riemann_hypothesis_stepanov_bound F hF f q 1 hq hm3 hnsq hq6m
  let curveSet := {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f}
  let S1_set := {x : F // x ∈ S_a F f c 1}
  have h_two_S1_bound :
      2 * (Fintype.card S1_set : ℝ) <
        (q : ℝ) + 4 * (m : ℝ) * (Nat.ceil (Real.sqrt q) : ℝ) := by
    simp [hm_def, hc_def, S1_set] at h_stepanov ⊢
    linarith [h_stepanov]
  have h_N_le_2S1 : (Fintype.card curveSet : ℝ) ≤ 2 * (Fintype.card S1_set : ℝ) := by
    have h_proj : ∀ p : curveSet, (p.val.1 : F) ∈ S_a F f c 1 := by
      intro ⟨⟨x, y⟩, hp⟩
      simp [S_a]
      by_cases hfx : Polynomial.eval x f = 0
      · left; exact hfx
      · right
        have hfx_sq : IsSquare (Polynomial.eval x f) :=
          ⟨y, by ring_nf; simpa using hp.symm⟩
        have hfx_ne : Polynomial.eval x f ≠ 0 := hfx
        rw [FiniteField.isSquare_iff hodd hfx_ne] at hfx_sq
        have hcard_eq : Fintype.card F / 2 = (Fintype.card F - 1) / 2 := by
          have hcard_pos : 0 < Fintype.card F := Fintype.card_pos
          have : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two hodd
          omega
        rw [hcard_eq] at hfx_sq
        simpa [hc_def, hq] using hfx_sq
    let proj : curveSet → S1_set := fun p => ⟨p.val.1, h_proj p⟩
    have h_fiber_le : ∀ y : S1_set, Fintype.card {p : curveSet // proj p = y} ≤ 2 := by
      intro y
      classical
      have h_inj :
          Fintype.card {p : curveSet // proj p = y} ≤
            Fintype.card {t : F // t ^ 2 = Polynomial.eval y.1 f} := by
        refine Fintype.card_le_of_injective
          (fun p : {p : curveSet // proj p = y} =>
            (⟨p.1.1.2, by
              have hx : p.1.1.1 = y.1 := by
                simpa [proj] using congrArg Subtype.val p.2
              simpa [hx] using p.1.2⟩ : {t : F // t ^ 2 = Polynomial.eval y.1 f}))
          (by
            intro p₁ p₂ h
            apply Subtype.ext
            apply Subtype.ext
            ext
            · have hx₁ : p₁.1.1.1 = y.1 := by
                simpa [proj] using congrArg Subtype.val p₁.2
              have hx₂ : p₂.1.1.1 = y.1 := by
                simpa [proj] using congrArg Subtype.val p₂.2
              simp [hx₁, hx₂]
            · exact congrArg Subtype.val h)
      exact le_trans h_inj (card_sq_eq_le_two (F := F) (a := Polynomial.eval y.1 f))
    have h_count : Fintype.card curveSet ≤ 2 * Fintype.card S1_set := by
      classical
      have hcard :
          Fintype.card curveSet = ∑ y : S1_set, Fintype.card {p : curveSet // proj p = y} := by
        simpa using
          (Fintype.card_congr (Equiv.sigmaFiberEquiv proj).symm).trans
            (Fintype.card_sigma (α := fun y : S1_set => {p : curveSet // proj p = y}))
      calc
        Fintype.card curveSet = ∑ y : S1_set, Fintype.card {p : curveSet // proj p = y} := hcard
        _ ≤ ∑ _y : S1_set, 2 := Finset.sum_le_sum (fun y _ => h_fiber_le y)
        _ = 2 * Fintype.card S1_set := by
              simp [Finset.sum_const, Finset.card_univ, mul_comm]
    exact_mod_cast h_count
  have h := lt_of_le_of_lt h_N_le_2S1 h_two_S1_bound
  simpa [curveSet, S1_set, hc_def, hm_def] using h

lemma curve_count_ge_two_times_N1 (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (f : Polynomial F) (q : ℕ) (hq : q = Fintype.card F) (hodd : ringChar F ≠ 2) :
    (Fintype.card {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f} : ℝ) ≥
      2 * (Fintype.card {x : F // (Polynomial.eval x f) ^ ((q - 1) / 2) = 1 ∧
        Polynomial.eval x f ≠ 0} : ℝ) :=
by
  classical
  subst hq
  set c := (Fintype.card F - 1) / 2 with hc_def
  let N1 := {x : F // (Polynomial.eval x f) ^ c = 1 ∧ Polynomial.eval x f ≠ 0}
  let C := {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f}
  have hcard_div : Fintype.card F / 2 = (Fintype.card F - 1) / 2 := by
    have _ := FiniteField.odd_card_of_char_ne_two hodd
    have _ : 0 < Fintype.card F := Fintype.card_pos
    omega
  have htwo_ne : (2 : F) ≠ 0 := by
    intro h2
    have := CharP.ringChar_of_prime_eq_zero (R := F) Nat.prime_two h2
    exact hodd this
  have hcard_div' : Fintype.card F / 2 = c := by
    simpa [hc_def] using hcard_div
  have hsq : ∀ x : N1, IsSquare (Polynomial.eval x.1 f) := by
    intro x
    have hx_ne : Polynomial.eval x.1 f ≠ 0 := x.2.2
    have h_euler := FiniteField.isSquare_iff hodd hx_ne
    rw [hcard_div'] at h_euler
    exact h_euler.mpr x.2.1
  let root : N1 → F := fun x => Classical.choose (hsq x)
  have hroot : ∀ x : N1, Polynomial.eval x.1 f = root x * root x := by
    intro x
    exact Classical.choose_spec (hsq x)
  let yval : N1 → Bool → F := fun x b => cond b (root x) (-root x)
  let φ : N1 × Bool → C := fun xb =>
    ⟨⟨xb.1.1, yval xb.1 xb.2⟩, by
      have : (root xb.1) ^ 2 = Polynomial.eval xb.1.1 f := by
        simpa [pow_two] using (hroot xb.1).symm
      cases xb.2 <;> simp [yval, this]⟩
  have hφ_inj : Function.Injective φ := by
    rintro ⟨x, b⟩ ⟨x', b'⟩ h
    have hx : x = x' := by
      apply Subtype.ext
      simpa using congrArg Prod.fst (congrArg Subtype.val h)
    subst hx
    have hy : yval x b = yval x b' := by
      simpa using congrArg Prod.snd (congrArg Subtype.val h)
    have hroot_ne : root x ≠ 0 := by
      intro h0
      have : Polynomial.eval x.1 f = 0 := by simpa [h0] using hroot x
      exact x.2.2 this
    have hroot_ne_neg : root x ≠ -root x := by
      intro hneg
      have hadd : root x + root x = 0 := by
        calc
          root x + root x = root x + (-root x) := by
            simpa using congrArg (fun t => root x + t) hneg
          _ = 0 := by simp
      have hmul : (2 : F) * root x = 0 := by simpa [two_mul] using hadd
      exact (mul_ne_zero htwo_ne hroot_ne) hmul
    cases b <;> cases b'
    · rfl
    ·
      exfalso
      have : -root x = root x := by simpa [yval] using hy
      exact hroot_ne_neg this.symm
    ·
      exfalso
      have : root x = -root x := by simpa [yval] using hy
      exact hroot_ne_neg this
    · rfl
  have hcount_real' : (2 : ℝ) * (Fintype.card N1 : ℝ) ≤ (Fintype.card C : ℝ) := by
    have : (Fintype.card (N1 × Bool) : ℝ) ≤ (Fintype.card C : ℝ) := by
      exact_mod_cast (Fintype.card_le_of_injective φ hφ_inj)
    simpa [Fintype.card_prod, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using this
  simpa [C, N1, hc_def, ge_iff_le, two_mul, mul_assoc, mul_left_comm, mul_comm] using hcount_real'

lemma partition_N1_eq_q_sub_S_neg1 (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (f : Polynomial F) (q : ℕ) (hq : q = Fintype.card F) (hodd : ringChar F ≠ 2)
    [DecidablePred (fun x : F => x ∈ S_a F f ((q - 1) / 2) (-1))] :
    (Fintype.card {x : F // (Polynomial.eval x f) ^ ((q - 1) / 2) = 1 ∧ Polynomial.eval x f ≠ 0} : ℝ) =
      (q : ℝ) - (Fintype.card {x : F // x ∈ S_a F f ((q - 1) / 2) (-1)} : ℝ) :=
by
  subst hq
  set c := (Fintype.card F - 1) / 2 with hc_def
  have hcard_div : Fintype.card F / 2 = (Fintype.card F - 1) / 2 := by
    have _ := FiniteField.odd_card_of_char_ne_two hodd
    have _ : 0 < Fintype.card F := Fintype.card_pos
    omega
  have h1_ne_neg1 : (1 : F) ≠ -1 := by
    intro h
    have h2 : (2 : F) = 0 := by
      calc
        (2 : F) = 1 - (-1) := by ring
        _ = 1 - 1 := by rw [← h]
        _ = 0 := by ring
    exact hodd (CharP.ringChar_of_prime_eq_zero (R := F) Nat.prime_two h2)
  let N1 :=
    Finset.univ.filter (fun x : F => (Polynomial.eval x f) ^ c = 1 ∧
      Polynomial.eval x f ≠ 0)
  let Sn1 := Finset.univ.filter (fun x : F => x ∈ S_a F f c (-1))
  have h_compl : N1 = Sn1ᶜ := by
    ext x
    simp [N1, Sn1, S_a]
    constructor
    · rintro ⟨h1, hne⟩
      refine ⟨hne, ?_⟩
      intro hm1
      exact h1_ne_neg1 (h1.symm.trans hm1)
    · intro h
      have h' : Polynomial.eval x f ≠ 0 ∧
          (Polynomial.eval x f) ^ c ≠ -1 := by
        simpa [not_or] using h
      have h_euler := FiniteField.pow_dichotomy hodd h'.1
      rw [hcard_div] at h_euler
      rcases h_euler with h1 | hm1'
      · exact ⟨h1, h'.1⟩
      · exact (h'.2 hm1').elim
  have hN1_card_real :
      (N1.card : ℝ) = (Fintype.card F : ℝ) - (Sn1.card : ℝ) := by
    have hN1_card : N1.card = Fintype.card F - Sn1.card := by
      simp [h_compl, Finset.card_compl]
    have hSn1_le : Sn1.card ≤ Fintype.card F :=
      Finset.card_le_card (Finset.subset_univ _)
    simp [hN1_card, Nat.cast_sub hSn1_le]
  have h_N1_eq :
      Fintype.card {x : F // (Polynomial.eval x f) ^ c = 1 ∧
        Polynomial.eval x f ≠ 0} = N1.card :=
    Fintype.card_subtype _
  have h_S_eq :
      Fintype.card {x : F // x ∈ S_a F f c (-1)} = Sn1.card :=
    Fintype.card_subtype _
  simp only [hc_def] at h_N1_eq h_S_eq
  convert
      (by
        simp only [h_N1_eq, h_S_eq, hN1_card_real] :
          (Fintype.card {x : F // (Polynomial.eval x f) ^
              ((Fintype.card F - 1) / 2) = 1 ∧
              Polynomial.eval x f ≠ 0} : ℝ) =
            (Fintype.card F : ℝ) -
              (Fintype.card {x : F // x ∈ S_a F f
                ((Fintype.card F - 1) / 2) (-1)} : ℝ)) using 4

lemma riemann_hypothesis_lower_bound (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (f : Polynomial F) (q : ℕ) (hq : q = Fintype.card F)
    (hm3 : 3 ≤ f.natDegree)
    (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
        g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
    (hq6m : q > 6 * f.natDegree) (hodd : ringChar F ≠ 2) :
    (Fintype.card {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f} : ℝ) >
      (q : ℝ) - 4 * (f.natDegree : ℝ) * (Nat.ceil (Real.sqrt q) : ℝ) :=
by
  classical
  linarith [ curve_count_ge_two_times_N1 F f q hq hodd,
            partition_N1_eq_q_sub_S_neg1 F f q hq hodd,
            riemann_hypothesis_stepanov_bound F hF f q (-1) hq hm3 hnsq hq6m ]

theorem riemann_hypothesis_hec (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (f : Polynomial F) (q : ℕ) (hq : q = Fintype.card F) (hm3 : 3 ≤ f.natDegree)
    (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
        g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
    (hq6m : q > 6 * f.natDegree) :
    |(q : ℝ) - (Fintype.card {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f} : ℝ)| <
      (5 : ℝ) * (f.natDegree : ℝ) * Real.sqrt (q : ℝ) :=
by
  have hdeg_pos : 0 < f.natDegree :=
    lt_of_lt_of_le (by decide : 0 < 3) hm3
  have hm_pos : (0 : ℝ) < (f.natDegree : ℝ) := by
    exact_mod_cast hdeg_pos
  have hq_pos : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast (lt_trans (Nat.mul_pos (by decide : 0 < 6) hdeg_pos) hq6m)
  by_cases hchar2 : ringChar F = 2
  · have hN_eq_q :
        Fintype.card {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f} = q := by
      haveI : CharP F 2 := hchar2 ▸ ringChar.charP F
      haveI : ExpChar F 2 := .prime Nat.prime_two
      let frob := frobeniusEquiv F 2
      simpa [hq] using
        (Fintype.card_congr {
          toFun := fun ⟨⟨x, _⟩, _⟩ => x
          invFun := fun x => ⟨(x, frob.symm (Polynomial.eval x f)), frob.apply_symm_apply _⟩
          left_inv := fun ⟨⟨_, _⟩, hy⟩ =>
            Subtype.ext (Prod.ext rfl (frob.injective
              (by
                simp only [frobeniusEquiv_def, hy, frob,
                  RingEquiv.apply_symm_apply])))
          right_inv := fun _ => rfl
        })
    simp [hN_eq_q, sub_self, abs_zero]
    nlinarith [hm_pos, Real.sqrt_pos.2 hq_pos]
  · set N : ℝ :=
      (Fintype.card {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f} : ℝ)
    have h_abs :
        |(q : ℝ) - N| <
          4 * (f.natDegree : ℝ) * (Nat.ceil (Real.sqrt q) : ℝ) := by
      have h_upper :=
        riemann_hypothesis_upper_bound F hchar2 f q hq hm3 hnsq hq6m hchar2
      have h_lower :=
        riemann_hypothesis_lower_bound F hchar2 f q hq hm3 hnsq hq6m hchar2
      rw [abs_sub_lt_iff]; constructor <;> linarith
    have h_ceil_bound : (Nat.ceil (Real.sqrt q) : ℝ) ≤ Real.sqrt q + 1 := by
      have := Nat.ceil_lt_add_one (Real.sqrt_nonneg q)
      linarith
    have h_q_ge_18 : (18 : ℕ) ≤ q := by
      have : 6 * 3 ≤ 6 * f.natDegree := Nat.mul_le_mul_left 6 hm3
      omega
    have h_sqrt_gt_4 : (4 : ℝ) < Real.sqrt q := by
      rw [show (4 : ℝ) = Real.sqrt 16 by norm_num]
      apply Real.sqrt_lt_sqrt (by norm_num)
      exact_mod_cast Nat.lt_of_lt_of_le (by norm_num : 16 < 18) h_q_ge_18
    calc
      |(q : ℝ) - N| <
          4 * (f.natDegree : ℝ) * (Nat.ceil (Real.sqrt q) : ℝ) := h_abs
      _ ≤ 4 * (f.natDegree : ℝ) * (Real.sqrt q + 1) := by
        nlinarith [h_ceil_bound]
      _ = 4 * (f.natDegree : ℝ) * Real.sqrt q +
            4 * (f.natDegree : ℝ) := by ring
        _ < 4 * (f.natDegree : ℝ) * Real.sqrt q +
              (f.natDegree : ℝ) * Real.sqrt q := by
          nlinarith [hm_pos, h_sqrt_gt_4]
        _ = 5 * (f.natDegree : ℝ) * Real.sqrt q := by ring
