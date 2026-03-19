import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_8_3_5a {n : ℤ} (hn0 : n > 3) (hn1 : Squarefree n) :
  Irreducible (2 : Zsqrtd $ -n) ∧
  Irreducible (⟨0, 1⟩ : Zsqrtd $ -n) ∧
  Irreducible (1 + ⟨0, 1⟩ : Zsqrtd $ -n) := by
  let N : Zsqrtd (-n) → ℤ := fun z => z.re ^ 2 + n * z.im ^ 2
  have hn : 0 < n := by
    linarith
  have hfour : 4 ≤ n := by
    linarith
  have N_nonneg : ∀ z : Zsqrtd (-n), 0 ≤ N z := by
    intro z
    cases z with
    | mk a b =>
        dsimp [N]
        nlinarith [sq_nonneg a, sq_nonneg b, hn]
  have norm_mul : ∀ x y : Zsqrtd (-n), N (x * y) = N x * N y := by
    intro x y
    cases x with
    | mk a b =>
        cases y with
        | mk c d =>
            dsimp [N]
            ring
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
  have unit_of_norm_one : ∀ z : Zsqrtd (-n), N z = 1 → IsUnit z := by
    intro z hz
    cases z with
    | mk a b =>
        dsimp [N] at hz
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
          exact isUnit_iff_exists_inv.mpr ⟨(-1 : Zsqrtd (-n)), by norm_num⟩
        · exfalso
          norm_num at hs
        · change IsUnit (1 : Zsqrtd (-n))
          exact isUnit_one
  have norm_eq_one_of_unit : ∀ z : Zsqrtd (-n), IsUnit z → N z = 1 := by
    intro z hz
    rcases isUnit_iff_exists_inv.mp hz with ⟨w, hw⟩
    have hprod : N z * N w = 1 := by
      have h := congrArg N hw
      simpa [N, norm_mul] using h
    have hz_nonneg : 0 ≤ N z := N_nonneg z
    have hw_nonneg : 0 ≤ N w := N_nonneg w
    have hz_ne0 : N z ≠ 0 := by
      intro h0
      simpa [h0] using hprod
    have hw_ne0 : N w ≠ 0 := by
      intro h0
      simpa [h0] using hprod
    have hz_pos : 0 < N z := by
      omega
    have hw_pos : 0 < N w := by
      omega
    have hz_le1 : N z ≤ 1 := by
      by_contra hgt
      have hz_ge2 : 2 ≤ N z := by
        omega
      have hw_ge1 : 1 ≤ N w := by
        omega
      nlinarith [hprod, hz_ge2, hw_ge1]
    omega
  have hnotunit2 : ¬ IsUnit (2 : Zsqrtd (-n)) := by
    intro h
    have hz : N (2 : Zsqrtd (-n)) = 1 := norm_eq_one_of_unit _ h
    norm_num [N] at hz
  have hnotunitS : ¬ IsUnit (⟨0, 1⟩ : Zsqrtd (-n)) := by
    intro h
    have hz : N (⟨0, 1⟩ : Zsqrtd (-n)) = 1 := norm_eq_one_of_unit _ h
    have : n = 1 := by
      simpa [N] using hz
    linarith
  have hnotunit1S : ¬ IsUnit (1 + ⟨0, 1⟩ : Zsqrtd (-n)) := by
    intro h
    have hz : N (1 + ⟨0, 1⟩ : Zsqrtd (-n)) = 1 := norm_eq_one_of_unit _ h
    have : n + 1 = 1 := by
      simpa [N] using hz
    linarith
  have hirr2 : Irreducible (2 : Zsqrtd (-n)) := by
    refine ⟨hnotunit2, ?_⟩
    intro a b hab
    cases a with
    | mk a1 a2 =>
        cases b with
        | mk b1 b2 =>
            let Na : ℤ := N (⟨a1, a2⟩ : Zsqrtd (-n))
            let Nb : ℤ := N (⟨b1, b2⟩ : Zsqrtd (-n))
            have hnorm : Na * Nb = 4 := by
              simpa [Na, Nb, N, norm_mul] using (congrArg N hab).symm
            by_cases hAu : IsUnit (⟨a1, a2⟩ : Zsqrtd (-n))
            · exact Or.inl hAu
            · by_cases hBu : IsUnit (⟨b1, b2⟩ : Zsqrtd (-n))
              · exact Or.inr hBu
              · have hNa_nonneg : 0 ≤ Na := by
                  dsimp [Na]
                  exact N_nonneg _
                have hNb_nonneg : 0 ≤ Nb := by
                  dsimp [Nb]
                  exact N_nonneg _
                have hNa_ne1 : Na ≠ 1 := by
                  intro h1
                  exact hAu (unit_of_norm_one _ (by simpa [Na] using h1))
                have hNb_ne1 : Nb ≠ 1 := by
                  intro h1
                  exact hBu (unit_of_norm_one _ (by simpa [Nb] using h1))
                have hNa_ne0 : Na ≠ 0 := by
                  intro h0
                  simpa [h0] using hnorm
                have hNb_ne0 : Nb ≠ 0 := by
                  intro h0
                  simpa [h0] using hnorm
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
                  simpa [Na, N] using norm_ne_two a1 a2
                exact False.elim (hNa_ne2 hNa_eq2)
  have hirrS : Irreducible (⟨0, 1⟩ : Zsqrtd (-n)) := by
    refine ⟨hnotunitS, ?_⟩
    intro a b hab
    cases a with
    | mk a1 a2 =>
        cases b with
        | mk b1 b2 =>
            have hIm := congrArg Zsqrtd.im hab
            simp [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] at hIm
            by_cases ha20 : a2 = 0
            · subst a2
              have him' : a1 * b2 = 1 := by
                linarith
              left
              refine isUnit_iff_exists_inv.mpr ?_
              refine ⟨(⟨b2, 0⟩ : Zsqrtd (-n)), ?_⟩
              ext <;> simp [him']
            · let Na : ℤ := N (⟨a1, a2⟩ : Zsqrtd (-n))
              let Nb : ℤ := N (⟨b1, b2⟩ : Zsqrtd (-n))
              have hnorm : Na * Nb = n := by
                simpa [Na, Nb, N, norm_mul] using (congrArg N hab).symm
              have hNa_nonneg : 0 ≤ Na := by
                dsimp [Na]
                exact N_nonneg _
              have hNb_nonneg : 0 ≤ Nb := by
                dsimp [Nb]
                exact N_nonneg _
              have hNb_ne0 : Nb ≠ 0 := by
                intro h0
                have : n = 0 := by
                  simpa [h0] using hnorm.symm
                linarith
              have hNb_pos : 0 < Nb := by
                omega
              have hNb_ge1 : 1 ≤ Nb := by
                omega
              have ha2sq_ge1 : 1 ≤ a2 ^ 2 := by
                have hpos : 0 < a2 ^ 2 := by
                  simpa [pow_two] using (mul_self_pos.mpr ha20)
                linarith
              have hNa_ge_n : n ≤ Na := by
                dsimp [Na, N]
                nlinarith [sq_nonneg a1, ha2sq_ge1]
              have hNa_le_n : Na ≤ n := by
                nlinarith [hnorm, hNb_ge1, hNa_nonneg]
              have hNa_eq_n : Na = n := by
                omega
              have hNb_eq1 : Nb = 1 := by
                nlinarith [hnorm, hNa_eq_n]
              exact Or.inr (unit_of_norm_one _ (by simpa [Nb] using hNb_eq1))
  have hirr1S : Irreducible (1 + ⟨0, 1⟩ : Zsqrtd (-n)) := by
    refine ⟨hnotunit1S, ?_⟩
    intro a b hab
    cases a with
    | mk a1 a2 =>
        cases b with
        | mk b1 b2 =>
            have hIm := congrArg Zsqrtd.im hab
            simp [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] at hIm
            by_cases ha20 : a2 = 0
            · subst a2
              have him' : a1 * b2 = 1 := by
                linarith
              left
              refine isUnit_iff_exists_inv.mpr ?_
              refine ⟨(⟨b2, 0⟩ : Zsqrtd (-n)), ?_⟩
              ext <;> simp [him']
            · let Na : ℤ := N (⟨a1, a2⟩ : Zsqrtd (-n))
              let Nb : ℤ := N (⟨b1, b2⟩ : Zsqrtd (-n))
              have hnorm : Na * Nb = n + 1 := by
                simpa [Na, Nb, N, norm_mul] using (congrArg N hab).symm
              have hNa_nonneg : 0 ≤ Na := by
                dsimp [Na]
                exact N_nonneg _
              have hNb_nonneg : 0 ≤ Nb := by
                dsimp [Nb]
                exact N_nonneg _
              have hNb_ne0 : Nb ≠ 0 := by
                intro h0
                have : n + 1 = 0 := by
                  simpa [h0] using hnorm.symm
                linarith
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
                  dsimp [Na, N]
                  nlinarith [sq_nonneg a1, hge2, hn]
                linarith
              have ha2sq_eq1 : a2 ^ 2 = 1 := by
                omega
              by_cases ha10 : a1 = 0
              · subst a1
                have hNa_eq : Na = n := by
                  dsimp [Na, N]
                  nlinarith [ha2sq_eq1]
                have hNb_eq1_or_ge2 : Nb = 1 ∨ 2 ≤ Nb := by
                  omega
                cases hNb_eq1_or_ge2 with
                | inl hNb_eq1 =>
                    have : n = n + 1 := by
                      nlinarith [hnorm, hNa_eq, hNb_eq1]
                    linarith
                | inr hNb_ge2 =>
                    have : n + 1 < Na * Nb := by
                      nlinarith [hNa_eq, hNb_ge2, hn]
                    linarith
              · have ha1sq_ge1 : 1 ≤ a1 ^ 2 := by
                  have hpos : 0 < a1 ^ 2 := by
                    simpa [pow_two] using (mul_self_pos.mpr ha10)
                  linarith
                have ha1sq_le1 : a1 ^ 2 ≤ 1 := by
                  dsimp [Na, N] at hNa_le
                  nlinarith [ha2sq_eq1]
                have ha1sq_eq1 : a1 ^ 2 = 1 := by
                  omega
                have hNa_eq : Na = n + 1 := by
                  dsimp [Na, N]
                  nlinarith [ha1sq_eq1, ha2sq_eq1]
                have hNb_eq1 : Nb = 1 := by
                  nlinarith [hnorm, hNa_eq]
                exact Or.inr (unit_of_norm_one _ (by simpa [Nb] using hNb_eq1))
  exact ⟨hirr2, hirrS, hirr1S⟩
