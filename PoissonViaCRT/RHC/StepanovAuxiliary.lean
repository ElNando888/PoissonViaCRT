import Mathlib
import PoissonViaCRT.RHC.HasseDerivatives

lemma auxiliary_derivatives (F : Type*) [Field F] (f : Polynomial F) (m d ℓ c : ℕ)
    (hfdeg : f.natDegree = m) (rj sj : Polynomial F) (hr : rj.natDegree ≤ d) (hs : sj.natDegree ≤ d)
    (k : ℕ) (hk : k ≤ ℓ) :
    ∃ rjk sjk : Polynomial F,
      hasseDerivOp F k (f ^ ℓ * rj) = rjk * f ^ (ℓ - k) ∧
        hasseDerivOp F k (f ^ (ℓ + c) * sj) = sjk * f ^ (ℓ + c - k) ∧
          rjk.natDegree ≤ d + k * (m - 1) ∧ sjk.natDegree ≤ d + k * (m - 1) := by
  by_cases hf0 : f = 0
  · subst hf0
    have hm0 : m = 0 := by simpa [Polynomial.natDegree_zero] using hfdeg.symm
    by_cases hk0 : k = 0
    · subst hk0
      refine ⟨rj, sj, ?_, ?_, ?_, ?_⟩
      · simp [hasseDerivOp, mul_comm]
      · simp [hasseDerivOp, mul_comm]
      · simpa [hm0] using hr
      · simpa [hm0] using hs
    · have hℓpos : 0 < ℓ := lt_of_lt_of_le (Nat.pos_of_ne_zero hk0) hk
      have hℓcpos : 0 < ℓ + c := Nat.add_pos_left hℓpos _
      refine ⟨0, 0, ?_, ?_, ?_, ?_⟩
      · simp [hasseDerivOp, zero_pow (Nat.ne_of_gt hℓpos)]
      · simp [hasseDerivOp, zero_pow (Nat.ne_of_gt hℓcpos)]
      · simp [hm0]
      · simp [hm0]
  · have hdeg_f_eq : Polynomial.degree f = (m : WithBot ℕ) := by
      simpa [hfdeg] using Polynomial.degree_eq_natDegree hf0
    obtain ⟨_, hℓ⟩ := hasse_formulas F k ℓ hk
    rcases hℓ rj f with ⟨hdiv_rj_core, hdeg_rj_core⟩
    have hdiv_rj : f ^ (ℓ - k) ∣ hasseDerivOp F k (f ^ ℓ * rj) := by
      simpa [mul_comm] using hdiv_rj_core
    have hkℓc : k ≤ ℓ + c := le_trans hk (Nat.le_add_right _ _)
    obtain ⟨_, hℓc⟩ := hasse_formulas F k (ℓ + c) hkℓc
    rcases hℓc sj f with ⟨hdiv_sj_core, hdeg_sj_core⟩
    have hdiv_sj : f ^ (ℓ + c - k) ∣ hasseDerivOp F k (f ^ (ℓ + c) * sj) := by
      simpa [mul_comm] using hdiv_sj_core
    set rjk : Polynomial F :=
      hasseDerivOp F k (f ^ ℓ * rj) / f ^ (ℓ - k) with hrjk_def
    set sjk : Polynomial F :=
      hasseDerivOp F k (f ^ (ℓ + c) * sj) / f ^ (ℓ + c - k) with hsjk_def
    have hr_eq : hasseDerivOp F k (f ^ ℓ * rj) = rjk * f ^ (ℓ - k) := by
      simpa [hrjk_def, mul_comm] using
        (EuclideanDomain.mul_div_cancel'
          (R := Polynomial F)
          (a := hasseDerivOp F k (f ^ ℓ * rj))
          (b := f ^ (ℓ - k)) (pow_ne_zero _ hf0) hdiv_rj).symm
    have hs_eq : hasseDerivOp F k (f ^ (ℓ + c) * sj) = sjk * f ^ (ℓ + c - k) := by
      simpa [hsjk_def, mul_comm] using
        (EuclideanDomain.mul_div_cancel'
          (R := Polynomial F)
          (a := hasseDerivOp F k (f ^ (ℓ + c) * sj))
          (b := f ^ (ℓ + c - k)) (pow_ne_zero _ hf0) hdiv_sj).symm
    have hdeg_rjk_match :
        Polynomial.degree rjk ≤
          (match
              Polynomial.degree rj + (k : WithBot ℕ) * Polynomial.degree f with
            | ⊥ => ⊥
            | some n => some (n - k)) := by
      simpa [hrjk_def, mul_comm] using hdeg_rj_core
    have hdeg_sjk_match :
        Polynomial.degree sjk ≤
          (match
              Polynomial.degree sj + (k : WithBot ℕ) * Polynomial.degree f with
            | ⊥ => ⊥
            | some n => some (n - k)) := by
      simpa [hsjk_def, mul_comm] using hdeg_sj_core
    have hnat_le_of_degree_match (t q : Polynomial F) (ht : t.natDegree ≤ d)
        (hdeg_match :
          Polynomial.degree q ≤
            (match Polynomial.degree t + (k : WithBot ℕ) * Polynomial.degree f with
              | ⊥ => ⊥
              | some n => some (n - k))) :
        q.natDegree ≤ d + k * m - k := by
      have htdeg : Polynomial.degree t ≤ (d : WithBot ℕ) := (Polynomial.natDegree_le_iff_degree_le).1 ht
      have hfdeg' : Polynomial.degree f = (m : WithBot ℕ) := by simpa [hfdeg] using Polynomial.degree_eq_natDegree hf0
      have hsum_le :
          Polynomial.degree t + (k : WithBot ℕ) * Polynomial.degree f ≤ ((d + k * m : ℕ) : WithBot ℕ) := by
        simpa [hfdeg', add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
          add_le_add_right htdeg ((k : WithBot ℕ) * Polynomial.degree f)
      cases hs : Polynomial.degree t + (k : WithBot ℕ) * Polynomial.degree f using WithBot.recBotCoe with
      | bot =>
          have hq0 : q = 0 := by
            have : Polynomial.degree q = (⊥ : WithBot ℕ) :=
              (le_bot_iff.mp (by simpa [hs] using hdeg_match))
            exact (Polynomial.degree_eq_bot.mp this)
          simp [hq0]
      | coe n =>
          have hn_le : n ≤ d + k * m := by
            have : ((n : ℕ) : WithBot ℕ) ≤ ((d + k * m : ℕ) : WithBot ℕ) := by simpa [hs] using hsum_le
            exact WithBot.coe_le_coe.mp this
          have hdegq : Polynomial.degree q ≤ ((n - k : ℕ) : WithBot ℕ) := by simpa [hs] using hdeg_match
          have : n - k ≤ d + k * m - k := Nat.sub_le_sub_right hn_le k
          exact (Polynomial.natDegree_le_iff_degree_le).2 (le_trans hdegq (WithBot.coe_le_coe.2 this))
    have hnat_rjk_le : rjk.natDegree ≤ d + k * m - k := hnat_le_of_degree_match rj rjk hr hdeg_rjk_match
    have hnat_sjk_le : sjk.natDegree ≤ d + k * m - k := hnat_le_of_degree_match sj sjk hs hdeg_sjk_match
    have h_nat_ineq : d + k * m - k ≤ d + k * (m - 1) := by
      cases m with
      | zero =>
          simpa using Nat.sub_le d k
      | succ m' =>
          simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    refine ⟨rjk, sjk, hr_eq, hs_eq, ?_, ?_⟩
    · exact le_trans hnat_rjk_le h_nat_ineq
    · exact le_trans hnat_sjk_le h_nat_ineq

lemma hasseDerivOp_mul_Xqpow (F : Type*) [Field F] [Fintype F] (q k : ℕ) (hq : q = Fintype.card F) (hkq : k < q)
    (P : Polynomial F) (j : ℕ) :
    hasseDerivOp F k (P * (Polynomial.X : Polynomial F) ^ (j * q)) = hasseDerivOp F k P * (Polynomial.X : Polynomial F) ^ (j * q) := by
  classical
  have choose_mul_card_pow_cast_eq_zero (q j i : ℕ) (hq : q = Fintype.card F) (hi_pos : 0 < i) (hi_lt : i < q) :
      (Nat.choose (j * q) i : F) = 0 := by
    have hfrob :
        (1 + (Polynomial.X : Polynomial F)) ^ q =
          (1 : Polynomial F) + (Polynomial.X : Polynomial F) ^ q := by
      simpa [hq, FiniteField.coe_frobeniusAlgHom, one_pow] using
        (FiniteField.frobeniusAlgHom F (Polynomial F)).map_add
          (1 : Polynomial F) (Polynomial.X : Polynomial F)
    have hpow :
        (1 + (Polynomial.X : Polynomial F)) ^ (j * q) =
          (1 + (Polynomial.X : Polynomial F) ^ q) ^ j := by
      simp [mul_comm, pow_mul, hfrob]
    have hcoeff_right_zero :
        ((1 + (Polynomial.X : Polynomial F) ^ q) ^ j).coeff i = 0 := by
      have hi_ne : i ≠ 0 := ne_of_gt hi_pos
      have hcoeff : ∀ n : ℕ, ((1 + (Polynomial.X : Polynomial F) ^ q) ^ n).coeff i = 0 := by
        intro n
        induction n with
        | zero =>
            simp [Polynomial.coeff_one, hi_ne]
        | succ n ih =>
            have hmul :
                (((1 + (Polynomial.X : Polynomial F) ^ q) ^ n) *
                    (Polynomial.X : Polynomial F) ^ q).coeff i = 0 := by
              simpa [Nat.not_le.mpr hi_lt] using
                (Polynomial.coeff_mul_X_pow'
                  (p := (1 + (Polynomial.X : Polynomial F) ^ q) ^ n) (n := q) (d := i))
            simp [pow_succ, mul_add, Polynomial.coeff_add, ih, hmul]
      exact hcoeff j
    have hcoeff_left_zero :
        ((1 + (Polynomial.X : Polynomial F)) ^ (j * q)).coeff i = 0 := by
      simpa [hpow] using hcoeff_right_zero
    simpa [Polynomial.coeff_one_add_X_pow (R := F) (n := j * q) (k := i)] using hcoeff_left_zero

  cases k with
  | zero =>
      simp [hasseDerivOp, mul_comm]
  | succ k' =>
      have hmul :
          hasseDerivOp F (Nat.succ k')
              (P * (Polynomial.X : Polynomial F) ^ (j * q)) =
            ∑ p ∈ Finset.antidiagonal (Nat.succ k'),
              hasseDerivOp F p.1 P *
                hasseDerivOp F p.2 ((Polynomial.X : Polynomial F) ^ (j * q)) := by
        simpa [hasseDerivOp, mul_comm, mul_left_comm, mul_assoc] using
          (Polynomial.hasseDeriv_mul (R := F) (k := Nat.succ k')
            (f := P) (g := (Polynomial.X : Polynomial F) ^ (j * q)))
      have hsum :
          (∑ p ∈ Finset.antidiagonal (Nat.succ k'),
              hasseDerivOp F p.1 P *
                hasseDerivOp F p.2 ((Polynomial.X : Polynomial F) ^ (j * q))) =
            hasseDerivOp F (Nat.succ k') P * (Polynomial.X : Polynomial F) ^ (j * q) := by
        have :
            (∑ p ∈ Finset.antidiagonal (Nat.succ k'),
                hasseDerivOp F p.1 P *
                  hasseDerivOp F p.2 ((Polynomial.X : Polynomial F) ^ (j * q))) =
              hasseDerivOp F (Nat.succ k') P *
                hasseDerivOp F 0 ((Polynomial.X : Polynomial F) ^ (j * q)) := by
          refine
            Finset.sum_eq_single_of_mem (a := (Nat.succ k', 0))
              (Finset.mem_antidiagonal.mpr (by simp))
              ?_
          intro p hp_mem hp_ne
          rcases p with ⟨a, b⟩
          have hab : a + b = Nat.succ k' := Finset.mem_antidiagonal.mp hp_mem
          have hb0 : b ≠ 0 := by
            intro hb0
            have ha' : a = Nat.succ k' := by simpa [hb0] using hab
            apply hp_ne
            ext <;> simp [ha', hb0]
          have hb_pos : 0 < b := Nat.pos_of_ne_zero hb0
          have hb_le : b ≤ Nat.succ k' := by
            have : b ≤ a + b := Nat.le_add_left _ _
            simpa [hab] using this
          have hb_ltq : b < q := lt_of_le_of_lt hb_le hkq
          have hderiv_zero :
              hasseDerivOp F b ((Polynomial.X : Polynomial F) ^ (j * q)) = 0 := by
            have hchoose_zero :
                (Nat.choose (j * q) b : F) = 0 :=
              choose_mul_card_pow_cast_eq_zero q j b hq hb_pos hb_ltq
            simp [hasseDerivOp, Polynomial.X_pow_eq_monomial, hchoose_zero]
          simp [hderiv_zero]
        simpa [hasseDerivOp] using this
      simpa using (hmul.trans hsum)

lemma stepanov_form (F : Type*) [Field F] [Fintype F] (f : Polynomial F) (ℓ q c J k : ℕ) (hk : k < ℓ)
    (hq : q = Fintype.card F) (hkq : k < q) (rj sj : ℕ → Polynomial F) :
    ∃ rjk sjk : ℕ → Polynomial F,
      (∀ j, hasseDerivOp F k (f ^ ℓ * rj j) = rjk j * f ^ (ℓ - k)) ∧
        (∀ j, hasseDerivOp F k (f ^ (ℓ + c) * sj j) = sjk j * f ^ (ℓ + c - k)) ∧
          hasseDerivOp F k (f ^ ℓ * Finset.sum (Finset.range J) (fun j => (rj j + sj j * f ^ c) * Polynomial.X ^ (j * q))) =
            f ^ (ℓ - k) * Finset.sum (Finset.range J) (fun j => (rjk j + sjk j * f ^ c) * Polynomial.X ^ (j * q)) := by
  classical
  have h_ex :
      ∀ j : ℕ, ∃ rjk_j sjk_j : Polynomial F,
        hasseDerivOp F k (f ^ ℓ * rj j) = rjk_j * f ^ (ℓ - k) ∧
        hasseDerivOp F k (f ^ (ℓ + c) * sj j) = sjk_j * f ^ (ℓ + c - k) := by
    intro j
    let d := Nat.max (rj j).natDegree (sj j).natDegree
    rcases
        auxiliary_derivatives (F := F) (f := f) (m := f.natDegree) (d := d) (ℓ := ℓ) (c := c)
          (hfdeg := rfl) (rj := rj j) (sj := sj j) (Nat.le_max_left _ _) (Nat.le_max_right _ _)
          k hk.le with
      ⟨rjk_j, sjk_j, hr_eq, hs_eq, -, -⟩
    exact ⟨rjk_j, sjk_j, hr_eq, hs_eq⟩
  choose rjk sjk hrjk hsjk using h_ex
  refine ⟨rjk, sjk, hrjk, hsjk, ?_⟩
  have hpow : f ^ (ℓ + c - k) = f ^ (ℓ - k) * f ^ c := by
    have h : ℓ + c - k = (ℓ - k) + c := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (Nat.add_sub_assoc hk.le c)
    simpa [h] using (pow_add f (ℓ - k) c)
  have hP_factor (j : ℕ) :
      hasseDerivOp F k (f ^ ℓ * (rj j + sj j * f ^ c)) =
        f ^ (ℓ - k) * (rjk j + sjk j * f ^ c) := by
    calc
      hasseDerivOp F k (f ^ ℓ * (rj j + sj j * f ^ c))
          = hasseDerivOp F k (f ^ ℓ * rj j + f ^ (ℓ + c) * sj j) := by
              simp [mul_add, pow_add, mul_left_comm, mul_comm]
      _ = hasseDerivOp F k (f ^ ℓ * rj j) + hasseDerivOp F k (f ^ (ℓ + c) * sj j) := by
              simp [hasseDerivOp]
      _ = rjk j * f ^ (ℓ - k) + sjk j * f ^ (ℓ + c - k) := by
              simp [hrjk j, hsjk j]
      _ = f ^ (ℓ - k) * (rjk j + sjk j * f ^ c) := by
              simp [hpow, add_mul, mul_add, mul_assoc, mul_left_comm, mul_comm]
  calc
    hasseDerivOp F k
        (f ^ ℓ *
          Finset.sum (Finset.range J)
            (fun j => (rj j + sj j * f ^ c) * Polynomial.X ^ (j * q)))
        =
        Finset.sum (Finset.range J)
          (fun j =>
            hasseDerivOp F k ((f ^ ℓ * (rj j + sj j * f ^ c)) * Polynomial.X ^ (j * q))) := by
          simp [hasseDerivOp, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm, _root_.map_sum]
    _ =
        Finset.sum (Finset.range J)
          (fun j =>
            (f ^ (ℓ - k) * (rjk j + sjk j * f ^ c)) * Polynomial.X ^ (j * q)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simpa [hP_factor j, mul_assoc] using
            (hasseDerivOp_mul_Xqpow (F := F) (q := q) (k := k) (hq := hq) (hkq := hkq)
              (P := f ^ ℓ * (rj j + sj j * f ^ c)) (j := j))
    _ =
        f ^ (ℓ - k) *
          Finset.sum (Finset.range J)
            (fun j => (rjk j + sjk j * f ^ c) * Polynomial.X ^ (j * q)) := by
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
