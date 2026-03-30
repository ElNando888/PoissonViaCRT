import Mathlib
import PoissonViaCRT.RHC.StepanovDegreeBounds
import PoissonViaCRT.RHC.StepanovSystem

noncomputable def S_a (F : Type*) [Field F] (f : Polynomial F) (c : ℕ) (a : F) : Set F :=
  {x | Polynomial.eval x f = 0 ∨ (Polynomial.eval x f) ^ c = a}

theorem stepanov_polynomial (F : Type*) [Field F] [Fintype F] (hF : ringChar F ≠ 2)
    (f : Polynomial F) (q ℓ : ℕ) (a : F) (hq : q = Fintype.card F) (hm3 : 3 ≤ f.natDegree)
    (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
      g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
    (hq6m : q > 6 * f.natDegree) (hℓ_pos : 0 < ℓ) (hl : ℓ ≤ q / 3) :
    ∃ r : Polynomial F,
      r ≠ 0 ∧
        ((r.natDegree : ℝ) < ((f.natDegree * q : ℕ) : ℝ) + ((ℓ * q : ℕ) : ℝ) / 2 + ((ℓ * ℓ * f.natDegree : ℕ) : ℝ)) ∧
          (∀ x ∈ S_a F f ((q - 1) / 2) a, ∀ k < ℓ, (hasseDerivOp F k r).eval x = 0) := by
  set m : ℕ := f.natDegree with hm_def; have hfdeg : f.natDegree = m := by simp [hm_def]
  have hm3' : 3 ≤ m := by simpa [hm_def] using hm3
  have hm_pos : 0 < m := lt_of_lt_of_le (by decide : 0 < 3) hm3'
  have hm_ge_two : 2 ≤ m := le_trans (by decide : 2 ≤ 3) hm3'
  have h6mq : 6 * m < q := by simpa [hm_def] using hq6m
  have hq_pos_nat : 0 < q := lt_of_le_of_lt (Nat.zero_le _) h6mq
  let c : ℕ := (q - 1) / 2; let d : ℕ := Nat.ceil (((q : ℚ) - m) / 2) - 1
  set Jreal : ℚ := (ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ) with hJreal_def
  set J : ℕ := Nat.ceil Jreal with hJ_def
  have hJ_expr_pos :
      0 < (ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ) := by
    have hℓ_posQ : (0 : ℚ) < (ℓ : ℚ) := by exact_mod_cast hℓ_pos
    have hq_posQ : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq_pos_nat
    positivity
  have hJ_pos :
      1 ≤ Nat.ceil ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ)) :=
    Nat.one_le_ceil_iff.mpr hJ_expr_pos
  obtain ⟨rj, sj, hnz, hdeg, hvan⟩ := by
    simpa [d, J, hJ_def, Jreal, hJreal_def, c] using
      (stepanov_system_has_solution
        (F := F) (f := f) (q := q) (m := m) (ℓ := ℓ) (a := a)
        hq hfdeg hm_ge_two hm_pos hℓ_pos (by simpa [hm_def] using hq6m) hl hJ_pos)
  set R : Polynomial F :=
    f ^ ℓ *
      Finset.sum (Finset.range J)
        (fun j => ((rj j) + (sj j) * f ^ c) * Polynomial.X ^ (j * q)) with hR_def
  have hdegr : ∀ j < J, (rj j).natDegree ≤ d := fun j hj => (hdeg j hj).1
  have hdegs : ∀ j < J, (sj j).natDegree ≤ d := fun j hj => (hdeg j hj).2
  have hR_ne_zero : R ≠ 0 := by
    simpa [R, hR_def] using
      (stepanov_constructed_nonzero
        (F := F) (hF := hF) (f := f) (q := q) (m := m) (ℓ := ℓ)
        (J := J) (c := c) (d := d)
        hq hfdeg (by rfl) hm_pos (by simpa [hm_def] using hq6m) (by rfl) hnsq rj sj (by
          intro j hj; exact ⟨hdegr j hj, hdegs j hj⟩) hnz)
  have hdeg_nat_le :
      R.natDegree ≤ ℓ * m + d + c * m + (J - 1) * q := by
    simpa [R, hR_def] using
      (stepanov_polynomial_natDegree_le
        (F := F) (f := f) (q := q) (m := m) (ℓ := ℓ)
        (c := c) (d := d) (J := J)
        hfdeg rj sj hdegr hdegs)
  let Jm1 : ℕ := J - 1
  have hdeg_le_coreJ :
      (R.natDegree : ℚ)
        ≤ (ℓ : ℚ) * (m : ℚ) + (d : ℚ) + (c : ℚ) * (m : ℚ)
          + (Jm1 : ℚ) * (q : ℚ) := by
    have : (R.natDegree : ℚ) ≤ ((ℓ * m + d + c * m + Jm1 * q : ℕ) : ℚ) := by
      exact_mod_cast (by simpa [Jm1] using hdeg_nat_le)
    simpa [Nat.cast_add, Nat.cast_mul] using this
  set core : ℚ := (ℓ : ℚ) * (m : ℚ) + (d : ℚ) + (c : ℚ) * (m : ℚ) with hcore_def
  have hdeg_core_le :
      (R.natDegree : ℚ) ≤ core + (Jm1 : ℚ) * (q : ℚ) := by
    simpa [core, add_assoc] using hdeg_le_coreJ
  have hq_pos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq_pos_nat
  have hm_pos' : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm_pos
  have hℓ_le_q3 : (ℓ : ℚ) ≤ (q : ℚ) / 3 := by
    have : (ℓ : ℚ) ≤ ((q / 3 : ℕ) : ℚ) := by exact_mod_cast hl
    exact this.trans (by simpa using (Nat.cast_div_le (α := ℚ) (m := q) (n := 3)))
  have hℓm_le : (ℓ : ℚ) * (m : ℚ) ≤ (q : ℚ) / 3 * (m : ℚ) :=
    mul_le_mul_of_nonneg_right hℓ_le_q3 (le_of_lt hm_pos')
  have hd_le : (d : ℚ) ≤ (q : ℚ) / 2 + 1 := by
    have hx :
        Nat.ceil (((q : ℚ) - (m : ℚ)) / 2)
          ≤ Nat.ceil ((q : ℚ) / 2) := by
      refine Nat.ceil_le_ceil ?_
      nlinarith
    have hd_le_ceil : d ≤ Nat.ceil ((q : ℚ) / 2) := by
      have : d ≤ Nat.ceil (((q : ℚ) - (m : ℚ)) / 2) := by
        simpa [d] using (Nat.sub_le (Nat.ceil (((q : ℚ) - (m : ℚ)) / 2)) 1)
      exact this.trans hx
    have hx2_nonneg : (0 : ℚ) ≤ (q : ℚ) / 2 :=
      div_nonneg (le_of_lt hq_pos) (by norm_num)
    have : (d : ℚ) ≤ (Nat.ceil ((q : ℚ) / 2) : ℚ) := by exact_mod_cast hd_le_ceil
    exact this.trans (le_of_lt (Nat.ceil_lt_add_one hx2_nonneg))
  have hc_le : (c : ℚ) ≤ ((q : ℚ) - 1) / 2 := by
    have hq_ge_one : 1 ≤ q := Nat.succ_le_of_lt hq_pos_nat
    simpa [c, Nat.cast_sub hq_ge_one] using (Nat.cast_div_le (α := ℚ) (m := q - 1) (n := 2))
  have hcm_le : (c : ℚ) * (m : ℚ)
      ≤ ((q : ℚ) - 1) / 2 * (m : ℚ) :=
    mul_le_mul_of_nonneg_right hc_le (le_of_lt hm_pos')
  set B2 : ℚ :=
      (q : ℚ) / 3 * (m : ℚ) + (q : ℚ) / 2 + 1 + ((q : ℚ) - 1) / 2 * (m : ℚ) with hB2_def
  have hcore_le_B2 : core ≤ B2 := by
    have h1 : (ℓ : ℚ) * (m : ℚ) + (d : ℚ) ≤ (q : ℚ) / 3 * (m : ℚ) + ((q : ℚ) / 2 + 1) :=
      add_le_add hℓm_le hd_le
    have h2 :
        (ℓ : ℚ) * (m : ℚ) + (d : ℚ) + (c : ℚ) * (m : ℚ)
          ≤ (q : ℚ) / 3 * (m : ℚ) + ((q : ℚ) / 2 + 1) + ((q : ℚ) - 1) / 2 * (m : ℚ) :=
      add_le_add h1 hcm_le
    simpa [core, B2, hB2_def, add_assoc, add_left_comm, add_comm] using h2
  have hB2_lt : B2 < (m : ℚ) * (q : ℚ) := by
    have hm3Q : (3 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm3'
    nlinarith [hm3Q, hq_pos]
  have hcore_lt_mq : core < (m : ℚ) * (q : ℚ) := lt_of_le_of_lt hcore_le_B2 hB2_lt
  have hJreal_nonneg : (0 : ℚ) ≤ Jreal := by
    have :
        (0 : ℚ) ≤ (ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ) := by
      positivity
    simpa [Jreal, hJreal_def] using this
  have hJ_ge_one : 1 ≤ J := by
    simpa [Jreal, hJreal_def, hJ_def] using hJ_pos
  have hJm1_lt_Jreal : (Jm1 : ℚ) < Jreal := by
    have hJ_lt : (J : ℚ) < Jreal + 1 := by
      simpa [J, hJ_def] using (Nat.ceil_lt_add_one hJreal_nonneg)
    have hJm1_cast : (Jm1 : ℚ) = (J : ℚ) - 1 := by
      simpa [Jm1] using (Nat.cast_sub (R := ℚ) hJ_ge_one)
    linarith [hJ_lt, hJm1_cast]
  have hJm1q_le : (Jm1 : ℚ) * (q : ℚ) ≤ Jreal * (q : ℚ) :=
    le_of_lt (mul_lt_mul_of_pos_right hJm1_lt_Jreal hq_pos)
  have hJrealq :
      Jreal * (q : ℚ) =
        (ℓ : ℚ) * (q : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) := by
    simp [Jreal, div_eq_mul_inv, mul_add,
      mul_comm, mul_assoc, (ne_of_gt hq_pos)]
  have hJm1q_le_target :
      (Jm1 : ℚ) * (q : ℚ)
        ≤ (ℓ : ℚ) * (q : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) := by
    simpa [hJrealq] using hJm1q_le
  have hdeg_lt_target_Q :
      (R.natDegree : ℚ)
        < (m : ℚ) * (q : ℚ)
          + (ℓ : ℚ) * (q : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) := by
    have :
        (R.natDegree : ℚ) <
          (m : ℚ) * (q : ℚ) +
            ((ℓ : ℚ) * (q : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ)) :=
      lt_of_le_of_lt hdeg_core_le (add_lt_add_of_lt_of_le hcore_lt_mq hJm1q_le_target)
    simpa [add_assoc, add_left_comm, add_comm] using this
  have hdeg_lt_target_R :
      (R.natDegree : ℝ)
        < ((m * q : ℕ) : ℝ)
          + ((ℓ * q : ℕ) : ℝ) / 2
          + ((ℓ ^ 2 * m : ℕ) : ℝ) := by
    have h' :
        (R.natDegree : ℝ) <
          ((m : ℚ) * (q : ℚ)
            + (ℓ : ℚ) * (q : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) : ℝ) := by
      exact_mod_cast hdeg_lt_target_Q
    simpa [Nat.cast_mul, pow_two, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc] using h'
  refine ⟨R, hR_ne_zero, ?_, ?_⟩
  · simpa [hm_def, pow_two, Nat.mul_assoc] using hdeg_lt_target_R
  · intro x hx k hk
    rcases hx with hx_zero | hx_pow
    · simpa using
        (stepanov_vanishing_roots
          (F := F) (f := f)
          (g :=
            Finset.sum (Finset.range J)
              (fun j =>
                ((rj j) + (sj j) * f ^ c) * Polynomial.X ^ (j * q)))
          (ℓ := ℓ) (x := x) hx_zero k hk)
    · by_cases hx0 : f.eval x = 0
      · simpa using
          (stepanov_vanishing_roots
            (F := F) (f := f)
            (g :=
              Finset.sum (Finset.range J)
                (fun j =>
                  ((rj j) + (sj j) * f ^ c) * Polynomial.X ^ (j * q)))
            (ℓ := ℓ) (x := x) hx0 k hk)
      · have hvan_x :
            ∀ k' < ℓ,
              Finset.sum (Finset.range J)
                (fun j =>
                  (((hasseDerivOp F k' (f ^ ℓ * rj j)) /
                        f ^ (ℓ - k')).eval x
                      +
                      a *
                        ((hasseDerivOp F k' (f ^ (ℓ + c) * sj j)) /
                            f ^ (ℓ + c - k')).eval x) *
                    x ^ j) = 0 :=
          hvan x hx0 hx_pow
        have h_all_k :=
          stepanov_vanishing_nonzeros
            (F := F) (f := f) (ℓ := ℓ) (q := q)
            (c := c) (J := J) hq rj sj a x
            (fun k' hk' => lt_of_lt_of_le hk' (le_trans hl (Nat.div_le_self _ _)))
            hvan_x hx0 hx_pow
        exact h_all_k k hk
