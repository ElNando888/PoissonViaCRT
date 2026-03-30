import Mathlib
import PoissonViaCRT.RHC.StepanovAuxiliary
lemma stepanov_square_from_eq (F : Type*) [Field F] (f : Polynomial F) (r s : Polynomial F) (f₀ : F)
    (hf₀_ne_zero : f₀ ≠ 0) (hs_ne_zero : s ≠ 0) (heq : r * r * f = s * s * Polynomial.C f₀) :
    ∃ g : Polynomial (AlgebraicClosure F),
      g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f := by
  let K := AlgebraicClosure F
  let fK := Polynomial.map (algebraMap F K) f; let rK := Polynomial.map (algebraMap F K) r
  let sK := Polynomial.map (algebraMap F K) s
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_eq_mul_self (k := K) (algebraMap F K f₀)
  let L := FractionRing (Polynomial K)
  have heqK :
      rK * rK * fK = sK * sK * Polynomial.C (algebraMap F K f₀) := by
    simpa [fK, rK, sK, Polynomial.map_mul, Polynomial.map_C] using
      congrArg (Polynomial.map (algebraMap F K)) heq
  have hrK_ne : rK ≠ 0 := by
    intro hr0
    have h0 : sK * sK * Polynomial.C (algebraMap F K f₀) = 0 := by
      calc
        sK * sK * Polynomial.C (algebraMap F K f₀)
            = rK * rK * fK := heqK.symm
        _ = 0 := by simp [hr0]
    have hsK_ne : sK ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap F K).injective).2 hs_ne_zero
    have hCf0_ne : Polynomial.C (algebraMap F K f₀) ≠ 0 := by
      simp [hf₀_ne_zero]
    exact (mul_ne_zero (mul_ne_zero hsK_ne hsK_ne) hCf0_ne) h0
  let g : L :=
    algebraMap (Polynomial K) L sK / algebraMap (Polynomial K) L rK * algebraMap (Polynomial K) L (Polynomial.C α)
  have hrK_ne_alg : algebraMap (Polynomial K) L rK ≠ 0 :=
    (IsFractionRing.to_map_eq_zero_iff (R := Polynomial K) (K := L)
          (x := rK)).not.mpr hrK_ne
  have hCα_sq : Polynomial.C α * Polynomial.C α = Polynomial.C (algebraMap F K f₀) := by
    rw [← Polynomial.C_mul, ← hα]
  have hg_sq : g * g = algebraMap (Polynomial K) L fK := by
    have hr2_ne : algebraMap (Polynomial K) L (rK * rK) ≠ 0 := by
      simpa [map_mul] using mul_ne_zero hrK_ne_alg hrK_ne_alg
    have hnum : sK * Polynomial.C α * (sK * Polynomial.C α) = rK * rK * fK := by
      calc
        sK * Polynomial.C α * (sK * Polynomial.C α)
            = sK * sK * (Polynomial.C α * Polynomial.C α) := by ring
        _ = sK * sK * Polynomial.C (algebraMap F K f₀) := by simp [hCα_sq]
        _ = rK * rK * fK := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using heqK.symm
    calc
      g * g =
          algebraMap (Polynomial K) L (sK * Polynomial.C α * (sK * Polynomial.C α)) /
            algebraMap (Polynomial K) L (rK * rK) := by
          simp [g, map_mul, mul_assoc, mul_left_comm, mul_comm]
          ring
      _ =
          algebraMap (Polynomial K) L (rK * rK * fK) / algebraMap (Polynomial K) L (rK * rK) := by
          simp [hnum]
      _ = algebraMap (Polynomial K) L fK := by
          simpa [map_mul, mul_assoc] using
            (mul_div_cancel_left₀ (b := algebraMap (Polynomial K) L fK)
              (a := algebraMap (Polynomial K) L (rK * rK)) hr2_ne)
  obtain ⟨h, hh⟩ :=
    IsIntegrallyClosed.algebraMap_eq_of_integral <|
      IsIntegral.of_pow (by norm_num) ((sq g ▸ hg_sq) ▸ isIntegral_algebraMap)
  refine ⟨h, ?_⟩
  refine IsFractionRing.injective (Polynomial K) (FractionRing (Polynomial K)) ?_
  rw [map_mul, hh, hg_sq]
lemma stepanov_nonzero_shift_preserves (F : Type*) [Field F] (f : Polynomial F) (a : AlgebraicClosure F)
    (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
      g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f) :
    ¬ ∃ g : Polynomial (AlgebraicClosure F),
      g * g = (Polynomial.map (algebraMap F (AlgebraicClosure F)) f).comp (Polynomial.X + Polynomial.C a) := by
  rintro ⟨g, hg_sq⟩
  refine hnsq ⟨g.comp (Polynomial.X - Polynomial.C a), ?_⟩
  have h := congrArg (fun p => p.comp (Polynomial.X - Polynomial.C a)) hg_sq
  simpa [Polynomial.mul_comp, Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.X_comp,
    Polynomial.C_comp, sub_add_cancel, Polynomial.comp_X] using h
lemma coefficient_transformation_shift (F : Type*) [Field F] (a : F) (q J : ℕ) (A : ℕ → Polynomial F) :
    (∑ j ∈ Finset.range J, A j * (Polynomial.X ^ q + Polynomial.C a) ^ j) =
      ∑ k ∈ Finset.range J,
        (∑ j ∈ Finset.Ico k J, (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * A j) * Polynomial.X ^ (k * q) := by
  classical
  let B : ℕ → ℕ → Polynomial F := fun j k =>
    ((Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * A j) * Polynomial.X ^ (k * q)
  have h_expand :
      ∑ j ∈ Finset.range J, A j * (Polynomial.X ^ q + Polynomial.C a) ^ j =
        ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range (j + 1), B j k := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    simp [B, add_pow, Polynomial.smul_eq_C_mul, Finset.mul_sum, pow_mul, mul_comm, mul_left_comm] at hj ⊢
  have h_range (j : ℕ) (hj : j < J) :
      Finset.range (j + 1) = (Finset.range J).filter (fun k => k ≤ j) := by
    ext k; constructor <;> intro hk
    ·
      have hk_le : k ≤ j := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hk
      exact (Finset.mem_filter).2 ⟨Finset.mem_range.2 (lt_of_le_of_lt hk_le hj), hk_le⟩
    · rcases (Finset.mem_filter.1 hk) with ⟨_, hk_le⟩; exact Finset.mem_range.2 (Nat.lt_succ_of_le hk_le)
  have h_filter_Ico (k : ℕ) :
      (Finset.range J).filter (fun j => k ≤ j) = Finset.Ico k J := by
    ext j
    simp [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range, and_comm]
  calc
    ∑ j ∈ Finset.range J, A j * (Polynomial.X ^ q + Polynomial.C a) ^ j =
        ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range (j + 1), B j k := h_expand
    _ = ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J, if k ≤ j then B j k else 0 := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        have hj' : j < J := Finset.mem_range.1 hj
        simp [h_range j hj', Finset.sum_filter]
    _ = ∑ k ∈ Finset.range J, ∑ j ∈ Finset.range J, if k ≤ j then B j k else 0 := by
        simpa using
          (Finset.sum_comm :
            (∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J, if k ≤ j then B j k else 0) =
              ∑ k ∈ Finset.range J, ∑ j ∈ Finset.range J, if k ≤ j then B j k else 0)
    _ = ∑ k ∈ Finset.range J, ∑ j ∈ Finset.Ico k J, B j k := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        simpa [h_filter_Ico k] using
          (Finset.sum_filter (s := Finset.range J) (p := fun j => k ≤ j) (f := fun j => B j k)).symm
    _ = ∑ k ∈ Finset.range J,
          (∑ j ∈ Finset.Ico k J, (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * A j) *
            Polynomial.X ^ (k * q) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        simpa [B, mul_assoc, mul_left_comm, mul_comm] using
          (Finset.sum_mul (s := Finset.Ico k J)
            (f := fun j => (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * A j)
            (a := Polynomial.X ^ (k * q))).symm
lemma triangular_inversion_shift (F : Type*) [Field F]
    (a : F) (J : ℕ) (A : ℕ → Polynomial F)
    (hR : ∀ k < J,
      ∑ j ∈ Finset.Ico k J,
        (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * A j = 0) :
    ∀ j < J, A j = 0 :=
by
  revert A hR
  induction J with
  | zero =>
      intro A hR j hj
      exact (Nat.not_lt_zero _ hj).elim
  | succ J IH =>
      intro A hR j hj
      have hA_J : A J = 0 := by
        simpa [Nat.Ico_succ_singleton] using hR J (Nat.lt_succ_self J)
      have hR' :
          ∀ k < J,
            ∑ j ∈ Finset.Ico k J,
              (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * A j = 0 := by
        intro k hk
        have hIco : Finset.Ico k J.succ = insert J (Finset.Ico k J) := by
          simpa using
            (Finset.insert_Ico_right_eq_Ico_succ (a := k) (b := J)
              (Nat.le_of_lt_succ (Nat.lt_succ_of_lt hk))).symm
        simpa [hIco, Finset.sum_insert, Finset.mem_Ico, hA_J] using
          hR k (Nat.lt_succ_of_lt hk)
      by_cases h_eq : j = J
      · simpa [h_eq] using hA_J
      · exact IH A hR' j (lt_of_le_of_ne (Nat.le_of_lt_succ hj) h_eq)
lemma stepanov_nonzero_minimal_congruence
    (F : Type*) [Field F]
    (f : Polynomial F) (ℓ c q J : ℕ)
    (rj sj : ℕ → Polynomial F)
    (hf : f ≠ 0)
    (hsum : f ^ ℓ *
      (Finset.sum (Finset.range J)
        (fun j => ((rj j) + (sj j) * f ^ c) *
          (Polynomial.X) ^ (j * q))) = 0)
    (k : ℕ) (hk : k < J)
    (hk_min : ∀ j < k, rj j = 0 ∧ sj j = 0) :
    Polynomial.X ^ q ∣ (rj k + sj k * f ^ c) :=
by
  have hsum_zero :
      ∑ j ∈ Finset.range J,
        (rj j + sj j * f ^ c) * Polynomial.X ^ (j * q) = 0 := by
    simpa using
      (mul_eq_zero.mp hsum).resolve_left (pow_ne_zero _ hf)
  rw [
    Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le k) (Nat.le_of_lt hk),
    Finset.sum_eq_zero (by
      intro j hj
      obtain ⟨hrj, hsj⟩ := hk_min j (Finset.mem_Ico.mp hj).2
      simp [hrj, hsj]),
    zero_add,
    ← Finset.insert_Ico_succ_left_eq_Ico hk,
    Finset.sum_insert (by simp [Finset.mem_Ico])
  ] at hsum_zero
  have h_dvd_term :
      Polynomial.X ^ ((k + 1) * q) ∣
        (rj k + sj k * f ^ c) * Polynomial.X ^ (k * q) := by
    rw [add_eq_zero_iff_eq_neg.mp hsum_zero]
    refine dvd_neg.mpr ?_
    refine Finset.dvd_sum ?_
    intro x hx
    exact dvd_mul_of_dvd_right
      (pow_dvd_pow Polynomial.X
        (Nat.mul_le_mul_right q (Finset.mem_Ico.mp hx).1)) _
  refine
    (mul_dvd_mul_iff_left (a := Polynomial.X ^ (k * q))
        (pow_ne_zero _ Polynomial.X_ne_zero)).mp ?_
  have hkq : (k + 1) * q = k * q + q := by ring
  simpa [pow_add, hkq, mul_comm, mul_left_comm, mul_assoc] using h_dvd_term
lemma stepanov_nonzero_frobenius_mod (F : Type*) [Field F] [Fintype F]
    (f : Polynomial F) (q : ℕ) (hq : q = Fintype.card F) :
    Polynomial.X ^ q ∣ (f ^ q - Polynomial.C (f.eval 0)) :=
by
  rw [show f ^ q = Polynomial.expand F q f from
        by simpa [hq] using (FiniteField.expand_card f).symm,
      Polynomial.X_pow_dvd_iff]
  intro d hd
  rw [Polynomial.coeff_sub,
      Polynomial.coeff_expand
        (by simpa [hq] using (Fintype.card_pos (α := F)))]
  by_cases hd0 : d = 0
  · subst hd0
    simp [Polynomial.eval, Polynomial.eval₂_at_zero]
  · simp [Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hd0) hd,
      hd0, Polynomial.coeff_C]
lemma stepanov_nonzero_polynomial_equality
  (F : Type*) [Field F] [Fintype F] (hF : ringChar F ≠ 2)
  (f r s : Polynomial F) (q m c : ℕ)
  (hq : q = Fintype.card F) (hfdeg : f.natDegree = m)
  (hc : c = (q - 1) / 2)
  (hrdeg : 2 * r.natDegree + m < q) (hsdeg : 2 * s.natDegree + m < q)
  (hcong : Polynomial.X ^ q ∣ (r + s * f ^ c)) :
  r * r * f = s * s * Polynomial.C (f.eval 0) :=
by
  obtain ⟨k, hk⟩ : ∃ k, q = 2 * k + 1 := by
    refine (Nat.odd_iff.mpr ?_)
    simpa [hq] using (FiniteField.odd_card_of_char_ne_two (F := F) hF)
  have h2c1 : 2 * c + 1 = q := by
    have hq_pos : 0 < q := by simpa [hq] using (Fintype.card_pos (α := F))
    have h2_dvd : 2 ∣ q - 1 := by
      refine ⟨k, ?_⟩
      have := congrArg (fun n => n - 1) hk
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
    have h2c : 2 * c = q - 1 := by
      simpa [hc, Nat.mul_comm] using
        (Nat.div_two_mul_two_of_even ((even_iff_two_dvd).2 h2_dvd))
    simpa [h2c, Nat.add_comm] using (Nat.sub_add_cancel (Nat.succ_le_of_lt hq_pos))
  have hdiv1 : Polynomial.X ^ q ∣ r * r - (s * f ^ c) * (s * f ^ c) := by
    have htmp : Polynomial.X ^ q ∣ (r + s * f ^ c) * (r - s * f ^ c) :=
      dvd_mul_of_dvd_left hcong (r - s * f ^ c)
    have hdsq :
        (r + s * f ^ c) * (r - s * f ^ c) =
          r * r - (s * f ^ c) * (s * f ^ c) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
        (mul_self_sub_mul_self (a := r) (b := s * f ^ c)).symm
    simpa [hdsq] using htmp
  have hpow : f ^ c * f ^ c * f = f ^ (2 * c + 1) := by
    have : f ^ c * f ^ c * f = f ^ (c + c + 1) := by simp [pow_add, pow_succ, mul_comm]
    simpa [two_mul, Nat.add_assoc] using this
  have hdiv2 : Polynomial.X ^ q ∣ r * r * f - s * s * f ^ (2 * c + 1) := by
    have htmp : Polynomial.X ^ q ∣ f * (r * r - (s * f ^ c) * (s * f ^ c)) :=
      dvd_mul_of_dvd_right hdiv1 f
    have hrewrite :
        f * (r * r - (s * f ^ c) * (s * f ^ c)) =
          r * r * f - s * s * f ^ (2 * c + 1) := by
      calc
        f * (r * r - (s * f ^ c) * (s * f ^ c)) =
            f * (r * r) - f * ((s * f ^ c) * (s * f ^ c)) := by simp [mul_sub]
        _ = r * r * f - s * s * (f ^ c * f ^ c * f) := by
              simp [mul_assoc, mul_left_comm, mul_comm]
        _ = r * r * f - s * s * f ^ (2 * c + 1) := by
              simp [hpow, mul_assoc]
    simpa [hrewrite] using htmp
  have hdiv2' : Polynomial.X ^ q ∣ r * r * f - s * s * f ^ q := by
    simpa [h2c1] using hdiv2
  have hdiv3 : Polynomial.X ^ q ∣ s * s * f ^ q - s * s * Polynomial.C (f.eval 0) := by
    simpa [mul_sub, mul_comm, mul_left_comm, mul_assoc] using
      (dvd_mul_of_dvd_right
        (stepanov_nonzero_frobenius_mod (F := F) (f := f) (q := q) hq) (s * s))
  have hdiv_final : Polynomial.X ^ q ∣ r * r * f - s * s * Polynomial.C (f.eval 0) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      dvd_add hdiv2' hdiv3
  have hdeg_r2f_lt : (r * r * f).natDegree < q := by
    refine lt_of_le_of_lt ?_ hrdeg
    have h2 : (r * r).natDegree ≤ 2 * r.natDegree := by
      simpa [two_mul] using (Polynomial.natDegree_mul_le (p := r) (q := r))
    have hle : (r * r * f).natDegree ≤ 2 * r.natDegree + m := by
      have :=
        (Polynomial.natDegree_mul_le (p := r * r) (q := f)).trans
          (Nat.add_le_add_right h2 _)
      simpa [hfdeg, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
    exact hle
  have h2s_lt_q : 2 * s.natDegree < q :=
    lt_of_le_of_lt (Nat.le_add_right (2 * s.natDegree) m) hsdeg
  have hdeg_s2C_lt : (s * s * Polynomial.C (f.eval 0)).natDegree < q := by
    refine lt_of_le_of_lt ?_ h2s_lt_q
    have h2 : (s * s).natDegree ≤ 2 * s.natDegree := by
      simpa [two_mul] using (Polynomial.natDegree_mul_le (p := s) (q := s))
    simpa [Polynomial.natDegree_C, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (Polynomial.natDegree_mul_le (p := s * s) (q := Polynomial.C (f.eval 0))).trans
        (Nat.add_le_add_right h2 _)
  have hdeg_diff_lt :
      (r * r * f - s * s * Polynomial.C (f.eval 0)).natDegree < q := by
    have hle :
        (r * r * f - s * s * Polynomial.C (f.eval 0)).natDegree ≤
          max (r * r * f).natDegree (s * s * Polynomial.C (f.eval 0)).natDegree := by
      simpa [sub_eq_add_neg] using
        (Polynomial.natDegree_add_le (p := r * r * f) (q := -(s * s * Polynomial.C (f.eval 0))))
    exact lt_of_le_of_lt hle (max_lt_iff.mpr ⟨hdeg_r2f_lt, hdeg_s2C_lt⟩)
  have hdiff_zero : r * r * f - s * s * Polynomial.C (f.eval 0) = 0 := by
    refine Polynomial.eq_zero_of_dvd_of_natDegree_lt hdiv_final ?_
    simpa [Polynomial.natDegree_X_pow] using hdeg_diff_lt
  exact sub_eq_zero.mp hdiff_zero
lemma degree_bound_implies_two_mul_add_lt (q m n : ℕ) (hqm : m < q)
    (hn : n ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1) : 2 * n + m < q :=
by
  have hx_pos : (0 : ℚ) < ((q : ℚ) - m) / 2 :=
    div_pos (sub_pos.mpr (by exact_mod_cast hqm)) (by norm_num)
  have hn_lt : (n : ℚ) < ((q : ℚ) - m) / 2 :=
    Nat.lt_ceil.mp <| Nat.lt_of_le_pred (Nat.ceil_pos.mpr hx_pos) hn
  exact_mod_cast
    (show (2 : ℚ) * n + m < (q : ℚ) from by nlinarith [hn_lt])
lemma stepanov_nonzero_eval_zero (F : Type*) [Field F] [Fintype F] (hF : ringChar F ≠ 2)
    (f : Polynomial F) (q m ℓ J c : ℕ) (hc : c = (q - 1) / 2)
    (hq : q = Fintype.card F) (hfdeg : f.natDegree = m)
    (hm_pos : 0 < m)
    (hq6m : q > 6 * m)
    (hf0 : f.eval 0 ≠ 0)
    (rj sj : ℕ → Polynomial F)
    (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
      g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
    (hdeg : ∀ j < J,
      (rj j).natDegree ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1 ∧
      (sj j).natDegree ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1) :
  (f ^ ℓ *
      (Finset.sum (Finset.range J)
        (fun j => ((rj j) + (sj j) * f ^ c) * (Polynomial.X) ^ (j * q)))) = 0 ↔
    (∀ j < J, rj j = 0 ∧ sj j = 0) :=
by
  classical
  constructor
  · intro hsum
    by_contra h
    push_neg at h
    obtain ⟨j₀, hj₀_lt, hj₀_ne⟩ := h
    have hj₀_or : rj j₀ ≠ 0 ∨ sj j₀ ≠ 0 := by
      by_cases hrj : rj j₀ = 0
      · right; exact hj₀_ne hrj
      · left; exact hrj
    have hP_exists : ∃ k, k < J ∧ (rj k ≠ 0 ∨ sj k ≠ 0) :=
      ⟨j₀, hj₀_lt, hj₀_or⟩
    let k := Nat.find hP_exists
    obtain ⟨hk, hk_nonzero⟩ := Nat.find_spec hP_exists
    have hk_min : ∀ j < k, rj j = 0 ∧ sj j = 0 := fun j hj => by
      have h' : j < J → rj j = 0 ∧ sj j = 0 := by
        simpa [not_and, not_or, not_not] using
          (Nat.find_min hP_exists hj :
            ¬ (j < J ∧ (rj j ≠ 0 ∨ sj j ≠ 0)))
      exact h' (Nat.lt_trans hj hk)
    have heq :=
      stepanov_nonzero_polynomial_equality F hF f (rj k) (sj k) q m c hq hfdeg hc
        (degree_bound_implies_two_mul_add_lt q m (rj k).natDegree (by linarith)
          (hdeg k hk).1)
        (degree_bound_implies_two_mul_add_lt q m (sj k).natDegree (by linarith)
          (hdeg k hk).2)
        (stepanov_nonzero_minimal_congruence F f ℓ c q J rj sj
          (by intro hf; simp [hf] at hf0) hsum k hk hk_min)
    by_cases hsk : sj k = 0
    · have heq' : rj k * rj k * f = 0 := by simpa [hsk] using heq
      have hr_eq_zero : rj k = 0 := by
        rcases mul_eq_zero.mp heq' with hr2 | hf
        · exact mul_self_eq_zero.mp hr2
        · exact (False.elim <| by simp [hf] at hf0)
      exact hk_nonzero.elim (fun hr => hr hr_eq_zero) (fun hs => hs hsk)
    · exact
        hnsq
          (stepanov_square_from_eq F f (rj k) (sj k) (f.eval 0)
            hf0 hsk heq)
  · intro hall
    have hsum_zero : Finset.sum (Finset.range J)
        (fun j => ((rj j) + (sj j) * f ^ c) * Polynomial.X ^ (j * q)) = 0 :=
      Finset.sum_eq_zero fun j hj => by
        obtain ⟨hrj, hsj⟩ := hall j (Finset.mem_range.mp hj)
        simp [hrj, hsj]
    simp [hsum_zero]
lemma coefficient_transformation_degree_bound
    (F : Type*) [Field F]
    (a : F) (J d : ℕ) (A : ℕ → Polynomial F)
    (hdeg : ∀ j < J, (A j).natDegree ≤ d) :
    ∀ k < J,
      (∑ j ∈ Finset.Ico k J,
         (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * A j).natDegree ≤ d :=
by
  intro k _
  refine Polynomial.natDegree_sum_le_of_forall_le
    (s := Finset.Ico k J)
    (f := fun j =>
      (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * A j)
    (n := d) ?_
  intro j hj
  refine
    ((Polynomial.natDegree_mul_le
          (p := (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k))
          (q := A j)).trans ?_).trans
      (hdeg j (Finset.mem_Ico.1 hj).2)
  have hconst :
      ((Nat.choose j k : F) • (Polynomial.C a) ^ (j - k)).natDegree ≤ 0 :=
    (Polynomial.natDegree_smul_le
        (a := (Nat.choose j k : F))
        (p := (Polynomial.C a) ^ (j - k))).trans
      ((Polynomial.natDegree_pow_le (p := Polynomial.C a) (n := j - k)).trans
        (by simp))
  simpa [Nat.zero_add]
    using Nat.add_le_add_right hconst (A j).natDegree
lemma stepanov_nonzero (F : Type*) [Field F] [Fintype F] (hF : ringChar F ≠ 2) (f : Polynomial F)
    (q m ℓ J c : ℕ) (hc : c = (q - 1) / 2) (hq : q = Fintype.card F) (hfdeg : f.natDegree = m)
    (hm_pos : 0 < m) (hq6m : q > 6 * m) (rj sj : ℕ → Polynomial F)
    (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
      g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
    (hdeg : ∀ j < J,
      (rj j).natDegree ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1 ∧ (sj j).natDegree ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1) :
    (f ^ ℓ * Finset.sum (Finset.range J) (fun j => (rj j + sj j * f ^ c) * Polynomial.X ^ (j * q))) = 0 ↔
      (∀ j < J, rj j = 0 ∧ sj j = 0) := by
  constructor
  · intro hsum
    by_cases hf0 : f.eval 0 ≠ 0
    · exact
        (stepanov_nonzero_eval_zero (F := F) (hF := hF)
          (f := f) (q := q) (m := m) (ℓ := ℓ) (J := J) (c := c)
          (hc := hc) (hq := hq) (hfdeg := hfdeg) (hm_pos := hm_pos)
          (hq6m := hq6m) (hf0 := hf0)
          (rj := rj) (sj := sj) (hnsq := hnsq) (hdeg := hdeg)).mp hsum
    · have hqm : q > m :=
        lt_of_le_of_lt (Nat.le_mul_of_pos_left m (by decide : 0 < 6)) (by simpa [Nat.mul_comm] using hq6m)
      obtain ⟨a, hfa_ne⟩ :=
        Polynomial.exists_eval_ne_zero_of_natDegree_lt_card f
          (by
            intro hf
            simp [hf] at hfdeg
            omega)
          (by
            rw [Cardinal.mk_fintype, hfdeg, ← hq]
            exact_mod_cast hqm)
      let shift : Polynomial F := Polynomial.X + Polynomial.C a; let g : Polynomial F := f.comp shift
      let rj' : ℕ → Polynomial F := fun j => (rj j).comp shift; let sj' : ℕ → Polynomial F := fun j => (sj j).comp shift
      have hg0_ne : g.eval 0 ≠ 0 := by simpa [g, shift] using hfa_ne
      have hgdeg : g.natDegree = m := by simp [g, shift, hfdeg, Polynomial.natDegree_comp]
      have hnsq_g :
          ¬ ∃ h : Polynomial (AlgebraicClosure F),
              h * h = Polynomial.map (algebraMap F (AlgebraicClosure F)) g := by
        simpa [g, shift, Polynomial.map_comp] using
          (stepanov_nonzero_shift_preserves (F := F) (f := f)
            (a := algebraMap F (AlgebraicClosure F) a) hnsq)
      have hdeg_shifted :
          ∀ j < J,
            (rj' j).natDegree ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1 ∧
            (sj' j).natDegree ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1 := by
        intro j hj
        simpa [rj', sj', shift, Polynomial.natDegree_comp] using hdeg j hj
      have hg1 :
          g ^ ℓ *
              Finset.sum (Finset.range J)
                (fun j => ((rj' j) + (sj' j) * g ^ c) * shift ^ (j * q)) = 0 := by
        simpa [shift, g, rj', sj'] using congrArg (fun p : Polynomial F => p.comp shift) hsum
      let t : Polynomial F := Polynomial.X ^ q + Polynomial.C a
      have hshift_q : shift ^ q = t := by
        have hexpand : Polynomial.expand F q shift = t := by
          simpa [t, shift] using (map_add (Polynomial.expand F q) Polynomial.X (Polynomial.C a))
        have h' : shift ^ q = Polynomial.expand F q shift := by
          simpa [hq.symm, shift] using (FiniteField.expand_card (shift : Polynomial F)).symm
        exact h'.trans hexpand
      have hg2' :
          g ^ ℓ *
              (∑ j ∈ Finset.range J, ((rj' j) + (sj' j) * g ^ c) * t ^ j) = 0 := by
        simpa [t, Nat.mul_comm, pow_mul, hshift_q] using hg1
      let R : ℕ → Polynomial F := fun k =>
        ∑ j ∈ Finset.Ico k J,
          (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * rj' j
      let S : ℕ → Polynomial F := fun k =>
        ∑ j ∈ Finset.Ico k J,
          (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * sj' j
      have hsum_total_eq :
          (∑ j ∈ Finset.range J, ((rj' j) + (sj' j) * g ^ c) * t ^ j) =
            ∑ k ∈ Finset.range J,
              (R k + S k * g ^ c) * Polynomial.X ^ (k * q) := by
        classical
        have hr :
            (∑ j ∈ Finset.range J, rj' j * t ^ j) =
              ∑ k ∈ Finset.range J, R k * Polynomial.X ^ (k * q) := by
          unfold R t; simpa using
            (coefficient_transformation_shift (F := F) (a := a) (q := q) (J := J) (A := rj'))
        have hs :
            (∑ j ∈ Finset.range J, sj' j * t ^ j) =
              ∑ k ∈ Finset.range J, S k * Polynomial.X ^ (k * q) := by
          unfold S t; simpa using
            (coefficient_transformation_shift (F := F) (a := a) (q := q) (J := J) (A := sj'))
        calc
          (∑ j ∈ Finset.range J, ((rj' j) + (sj' j) * g ^ c) * t ^ j)
              = (∑ j ∈ Finset.range J, rj' j * t ^ j) +
                  g ^ c * (∑ j ∈ Finset.range J, sj' j * t ^ j) := by
                  simp [Finset.mul_sum, Finset.sum_add_distrib, add_mul, mul_add, mul_assoc, mul_left_comm, mul_comm]
          _ = (∑ k ∈ Finset.range J, R k * Polynomial.X ^ (k * q)) +
                g ^ c * (∑ k ∈ Finset.range J, S k * Polynomial.X ^ (k * q)) := by
                simp [hr, hs]
          _ = ∑ k ∈ Finset.range J, (R k + S k * g ^ c) * Polynomial.X ^ (k * q) := by
                simp [Finset.mul_sum, Finset.sum_add_distrib, add_mul, mul_add, mul_assoc, mul_left_comm, mul_comm]
      have hg3 :
          g ^ ℓ *
              Finset.sum (Finset.range J)
                (fun k =>
                  (R k + S k * g ^ c) * Polynomial.X ^ (k * q)) = 0 := by
        simpa [hsum_total_eq] using hg2'
      have hdeg_RS :
          ∀ k < J, (R k).natDegree ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1 ∧ (S k).natDegree ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1 := by
        intro k hk; refine ⟨?_, ?_⟩
        · simpa [R] using
            coefficient_transformation_degree_bound (F := F) (a := a) (J := J) (d := Nat.ceil (((q : ℚ) - m) / 2) - 1)
              (A := rj') (hdeg := fun j hj => (hdeg_shifted j hj).1) k hk
        · simpa [S] using
            coefficient_transformation_degree_bound (F := F) (a := a) (J := J) (d := Nat.ceil (((q : ℚ) - m) / 2) - 1)
              (A := sj') (hdeg := fun j hj => (hdeg_shifted j hj).2) k hk
      have hstep_g : ∀ k < J, R k = 0 ∧ S k = 0 :=
        (stepanov_nonzero_eval_zero (F := F) (hF := hF) (f := g) (q := q) (m := m) (ℓ := ℓ) (J := J) (c := c)
            (hc := hc) (hq := hq) (hfdeg := hgdeg) (hm_pos := hm_pos) (hq6m := hq6m) (hf0 := hg0_ne)
            (rj := R) (sj := S) (hnsq := hnsq_g) (hdeg := hdeg_RS)).mp hg3
      have hrj'_zero : ∀ j < J, rj' j = 0 :=
        triangular_inversion_shift (F := F) (a := a) (J := J) (A := rj') (fun k hk => by simpa [R] using (hstep_g k hk).1)
      have hsj'_zero : ∀ j < J, sj' j = 0 :=
        triangular_inversion_shift (F := F) (a := a) (J := J) (A := sj') (fun k hk => by simpa [S] using (hstep_g k hk).2)
      intro j hj
      have hrj_comp_zero : (rj j).comp (Polynomial.X + Polynomial.C a) = 0 := by simpa [rj', shift] using hrj'_zero j hj
      have hsj_comp_zero : (sj j).comp (Polynomial.X + Polynomial.C a) = 0 := by simpa [sj', shift] using hsj'_zero j hj
      exact ⟨(Polynomial.comp_X_add_C_eq_zero_iff (p := rj j) (t := a)).mp hrj_comp_zero,
        (Polynomial.comp_X_add_C_eq_zero_iff (p := sj j) (t := a)).mp hsj_comp_zero⟩
  · intro hall
    have : Finset.sum (Finset.range J) (fun j => (rj j + sj j * f ^ c) * Polynomial.X ^ (j * q)) = 0 :=
      Finset.sum_eq_zero fun j hj => by obtain ⟨hrj, hsj⟩ := hall j (Finset.mem_range.mp hj); simp [hrj, hsj]
    simp [this]
