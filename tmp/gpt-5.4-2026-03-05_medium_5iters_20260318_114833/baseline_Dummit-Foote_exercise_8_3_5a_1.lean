import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_8_3_5a {n : ℤ} (hn0 : n > 3) (hn1 : Squarefree n) :
  Irreducible (2 : Zsqrtd $ -n) ∧
  Irreducible (⟨0, 1⟩ : Zsqrtd $ -n) ∧
  Irreducible (1 + ⟨0, 1⟩ : Zsqrtd $ -n) := by
  have hn : 0 < n := by
    linarith
  have hfour : 4 ≤ n := by
    linarith
  have sq_ne_two : ∀ a : ℤ, a ^ 2 ≠ 2 := by
    intro a h
    have hle : a ≤ 1 := by
      have h' : 2 * a ≤ 3 := by
        nlinarith [sq_nonneg (a - 1), h]
      omega
    have hge : -1 ≤ a := by
      have h' : -3 ≤ 2 * a := by
        nlinarith [sq_nonneg (a + 1), h]
      omega
    interval_cases a <;> norm_num at h
  have norm_ne_two : ∀ a b : ℤ, a ^ 2 + n * b ^ 2 ≠ 2 := by
    intro a b h
    by_cases hb : b = 0
    · subst b
      exact sq_ne_two a (by simpa using h)
    · have hb2ge1 : 1 ≤ b ^ 2 := by
        have hb2pos : 0 < b ^ 2 := by
          simpa [pow_two] using (mul_self_pos.mpr hb)
        linarith
      have : 2 < a ^ 2 + n * b ^ 2 := by
        nlinarith [sq_nonneg a, hfour, hb2ge1]
      linarith
  have unit_of_norm_one : ∀ z : Zsqrtd (-n), z.re ^ 2 + n * z.im ^ 2 = 1 → IsUnit z := by
    intro z hz
    cases z with
    | mk a b =>
        dsimp at hz
        have hb0 : b = 0 := by
          by_contra hb
          have hb2ge1 : 1 ≤ b ^ 2 := by
            have hb2pos : 0 < b ^ 2 := by
              simpa [pow_two] using (mul_self_pos.mpr hb)
            linarith
          have : 1 < a ^ 2 + n * b ^ 2 := by
            nlinarith [sq_nonneg a, hfour, hb2ge1]
          linarith
        subst b
        have hs : a ^ 2 = 1 := by
          simpa using hz
        have hle : a ≤ 1 := by
          have h' : 2 * a ≤ 2 := by
            nlinarith [sq_nonneg (a - 1), hs]
          omega
        have hge : -1 ≤ a := by
          have h' : -2 ≤ 2 * a := by
            nlinarith [sq_nonneg (a + 1), hs]
          omega
        interval_cases a
        · change IsUnit (-1 : Zsqrtd (-n))
          exact isUnit_neg.mpr isUnit_one
        · exfalso
          norm_num at hs
        · change IsUnit (1 : Zsqrtd (-n))
          exact isUnit_one
  have hnotunit2 : ¬ IsUnit (2 : Zsqrtd (-n)) := by
    intro h
    rcases isUnit_iff_exists_inv.mp h with ⟨b, hb⟩
    cases b with
    | mk b1 b2 =>
        have hRe := congrArg Zsqrtd.re hb
        have hIm := congrArg Zsqrtd.im hb
        simp [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] at hRe hIm
        have hb20 : b2 = 0 := by
          linarith
        subst b2
        linarith
  have hnotunitS : ¬ IsUnit (⟨0, 1⟩ : Zsqrtd (-n)) := by
    intro h
    rcases isUnit_iff_exists_inv.mp h with ⟨b, hb⟩
    cases b with
    | mk b1 b2 =>
        have hRe := congrArg Zsqrtd.re hb
        have hIm := congrArg Zsqrtd.im hb
        simp [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] at hRe hIm
        have hb10 : b1 = 0 := by
          linarith
        subst b1
        have hdiv : n ∣ 1 := by
          refine ⟨-b2, ?_⟩
          linarith
        have hpm := Int.eq_one_or_neg_one_of_dvd_one hdiv
        omega
  have hnotunit1S : ¬ IsUnit (1 + ⟨0, 1⟩ : Zsqrtd (-n)) := by
    intro h
    rcases isUnit_iff_exists_inv.mp h with ⟨b, hb⟩
    cases b with
    | mk b1 b2 =>
        have hRe := congrArg Zsqrtd.re hb
        have hIm := congrArg Zsqrtd.im hb
        simp [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] at hRe hIm
        have hb1 : b1 = -b2 := by
          linarith
        subst b1
        have hdiv : n + 1 ∣ 1 := by
          refine ⟨b2, ?_⟩
          linarith
        have hpm := Int.eq_one_or_neg_one_of_dvd_one hdiv
        omega
  have hirr2 : Irreducible (2 : Zsqrtd (-n)) := by
    refine ⟨hnotunit2, ?_⟩
    intro a b hab
    cases a with
    | mk a1 a2 =>
        cases b with
        | mk b1 b2 =>
            have hRe := congrArg Zsqrtd.re hab
            have hIm := congrArg Zsqrtd.im hab
            simp [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] at hRe hIm
            let Na : ℤ := a1 ^ 2 + n * a2 ^ 2
            let Nb : ℤ := b1 ^ 2 + n * b2 ^ 2
            have hnorm : Na * Nb = 4 := by
              dsimp [Na, Nb]
              have hRe2 := congrArg (fun z : ℤ => z ^ 2) hRe
              have hIm2 := congrArg (fun z : ℤ => n * z ^ 2) hIm
              nlinarith
            by_cases hAu : IsUnit (⟨a1, a2⟩ : Zsqrtd (-n))
            · exact Or.inl hAu
            · by_cases hBu : IsUnit (⟨b1, b2⟩ : Zsqrtd (-n))
              · exact Or.inr hBu
              · have hNa_nonneg : 0 ≤ Na := by
                  dsimp [Na]
                  nlinarith [sq_nonneg a1, sq_nonneg a2]
                have hNb_nonneg : 0 ≤ Nb := by
                  dsimp [Nb]
                  nlinarith [sq_nonneg b1, sq_nonneg b2]
                have hNa_ne1 : Na ≠ 1 := by
                  intro h1
                  exact hAu (unit_of_norm_one ⟨a1, a2⟩ (by simpa [Na] using h1))
                have hNb_ne1 : Nb ≠ 1 := by
                  intro h1
                  exact hBu (unit_of_norm_one ⟨b1, b2⟩ (by simpa [Nb] using h1))
                have hNa_ne0 : Na ≠ 0 := by
                  intro h0
                  simp [Na, h0] at hnorm
                have hNb_ne0 : Nb ≠ 0 := by
                  intro h0
                  simp [Nb, h0] at hnorm
                have hNa_pos : 0 < Na := by
                  omega
                have hNb_pos : 0 < Nb := by
                  omega
                have hNa_ge2 : 2 ≤ Na := by
                  omega
                have hNb_ge2 : 2 ≤ Nb := by
                  omega
                have hNa_le2 : Na ≤ 2 := by
                  nlinarith [hnorm, hNb_ge2]
                have hNa_eq2 : Na = 2 := by
                  omega
                have hNa_ne2 : Na ≠ 2 := by
                  dsimp [Na]
                  exact norm_ne_two a1 a2
                exact False.elim (hNa_ne2 hNa_eq2)
  have hirrS : Irreducible (⟨0, 1⟩ : Zsqrtd (-n)) := by
    refine ⟨hnotunitS, ?_⟩
    intro a b hab
    cases a with
    | mk a1 a2 =>
        cases b with
        | mk b1 b2 =>
            have hRe := congrArg Zsqrtd.re hab
            have hIm := congrArg Zsqrtd.im hab
            simp [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] at hRe hIm
            by_cases ha20 : a2 = 0
            · subst a2
              have hdiv : a1 ∣ 1 := by
                refine ⟨b2, ?_⟩
                linarith
              have ha : a1 = 1 ∨ a1 = -1 := Int.eq_one_or_neg_one_of_dvd_one hdiv
              cases ha with
              | inl ha =>
                  left
                  subst a1
                  change IsUnit (1 : Zsqrtd (-n))
                  exact isUnit_one
              | inr ha =>
                  left
                  subst a1
                  change IsUnit (-1 : Zsqrtd (-n))
                  exact isUnit_neg.mpr isUnit_one
            · let Na : ℤ := a1 ^ 2 + n * a2 ^ 2
              let Nb : ℤ := b1 ^ 2 + n * b2 ^ 2
              have hnorm : Na * Nb = n := by
                dsimp [Na, Nb]
                have hRe2 := congrArg (fun z : ℤ => z ^ 2) hRe
                have hIm2 := congrArg (fun z : ℤ => n * z ^ 2) hIm
                nlinarith
              have hNa_nonneg : 0 ≤ Na := by
                dsimp [Na]
                nlinarith [sq_nonneg a1, sq_nonneg a2]
              have hNb_nonneg : 0 ≤ Nb := by
                dsimp [Nb]
                nlinarith [sq_nonneg b1, sq_nonneg b2]
              have hNb_ne0 : Nb ≠ 0 := by
                intro h0
                simp [Nb, h0] at hnorm
              have hNb_pos : 0 < Nb := by
                omega
              have hNb_ge1 : 1 ≤ Nb := by
                omega
              have ha2sq_ge1 : 1 ≤ a2 ^ 2 := by
                have hpos : 0 < a2 ^ 2 := by
                  simpa [pow_two] using (mul_self_pos.mpr ha20)
                linarith
              have hNa_ge_n : n ≤ Na := by
                dsimp [Na]
                nlinarith [sq_nonneg a1, ha2sq_ge1]
              have hNa_le_n : Na ≤ n := by
                nlinarith [hnorm, hNb_ge1, hNa_nonneg]
              have hNa_eq_n : Na = n := by
                omega
              have hNb_eq1 : Nb = 1 := by
                nlinarith [hnorm, hNa_eq_n]
              exact Or.inr (unit_of_norm_one ⟨b1, b2⟩ (by simpa [Nb] using hNb_eq1))
  have hirr1S : Irreducible (1 + ⟨0, 1⟩ : Zsqrtd (-n)) := by
    refine ⟨hnotunit1S, ?_⟩
    intro a b hab
    cases a with
    | mk a1 a2 =>
        cases b with
        | mk b1 b2 =>
            have hRe := congrArg Zsqrtd.re hab
            have hIm := congrArg Zsqrtd.im hab
            simp [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] at hRe hIm
            by_cases ha20 : a2 = 0
            · subst a2
              have hdiv : a1 ∣ 1 := by
                refine ⟨b2, ?_⟩
                linarith
              have ha : a1 = 1 ∨ a1 = -1 := Int.eq_one_or_neg_one_of_dvd_one hdiv
              cases ha with
              | inl ha =>
                  left
                  subst a1
                  change IsUnit (1 : Zsqrtd (-n))
                  exact isUnit_one
              | inr ha =>
                  left
                  subst a1
                  change IsUnit (-1 : Zsqrtd (-n))
                  exact isUnit_neg.mpr isUnit_one
            · let Na : ℤ := a1 ^ 2 + n * a2 ^ 2
              let Nb : ℤ := b1 ^ 2 + n * b2 ^ 2
              have hnorm : Na * Nb = n + 1 := by
                dsimp [Na, Nb]
                have hRe2 := congrArg (fun z : ℤ => z ^ 2) hRe
                have hIm2 := congrArg (fun z : ℤ => n * z ^ 2) hIm
                nlinarith
              have hNa_nonneg : 0 ≤ Na := by
                dsimp [Na]
                nlinarith [sq_nonneg a1, sq_nonneg a2]
              have hNb_nonneg : 0 ≤ Nb := by
                dsimp [Nb]
                nlinarith [sq_nonneg b1, sq_nonneg b2]
              have hNb_ne0 : Nb ≠ 0 := by
                intro h0
                simp [Nb, h0] at hnorm
              have hNb_pos : 0 < Nb := by
                omega
              have hNb_ge1 : 1 ≤ Nb := by
                omega
              have hNa_le : Na ≤ n + 1 := by
                nlinarith [hnorm, hNb_ge1, hNa_nonneg]
              have ha2sq_ge1 : 1 ≤ a2 ^ 2 := by
                have hpos : 0 < a2 ^ 2 := by
                  simpa [pow_two] using (mul_self_pos.mpr ha20)
                linarith
              have ha2sq_le1 : a2 ^ 2 ≤ 1 := by
                by_contra hgt
                have hge2 : 2 ≤ a2 ^ 2 := by
                  omega
                have : n + 1 < Na := by
                  dsimp [Na]
                  nlinarith [sq_nonneg a1, hge2, hn]
                linarith
              have ha2sq_eq1 : a2 ^ 2 = 1 := by
                omega
              by_cases ha10 : a1 = 0
              · subst a1
                have hNa_eq : Na = n := by
                  dsimp [Na]
                  nlinarith [ha2sq_eq1]
                have hdiv : n ∣ n + 1 := by
                  refine ⟨Nb, ?_⟩
                  simpa [hNa_eq, mul_comm] using hnorm.symm
                have hdiv1 : n ∣ 1 := by
                  simpa using dvd_sub hdiv dvd_rfl
                have hpm := Int.eq_one_or_neg_one_of_dvd_one hdiv1
                omega
              · have ha1sq_ge1 : 1 ≤ a1 ^ 2 := by
                  have hpos : 0 < a1 ^ 2 := by
                    simpa [pow_two] using (mul_self_pos.mpr ha10)
                  linarith
                have ha1sq_le1 : a1 ^ 2 ≤ 1 := by
                  dsimp [Na] at hNa_le
                  nlinarith [ha2sq_eq1]
                have ha1sq_eq1 : a1 ^ 2 = 1 := by
                  omega
                have hNa_eq : Na = n + 1 := by
                  dsimp [Na]
                  nlinarith [ha1sq_eq1, ha2sq_eq1]
                have hNb_eq1 : Nb = 1 := by
                  nlinarith [hnorm, hNa_eq]
                exact Or.inr (unit_of_norm_one ⟨b1, b2⟩ (by simpa [Nb] using hNb_eq1))
  exact ⟨hirr2, hirrS, hirr1S⟩
