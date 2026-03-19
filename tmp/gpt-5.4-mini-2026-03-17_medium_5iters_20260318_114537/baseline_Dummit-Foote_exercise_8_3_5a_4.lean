import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_8_3_5a {n : ℤ} (hn0 : n > 3) (hn1 : Squarefree n) :
  Irreducible (2 : Zsqrtd $ -n) ∧
  Irreducible (⟨0, 1⟩ : Zsqrtd $ -n) ∧
  Irreducible (1 + ⟨0, 1⟩ : Zsqrtd $ -n) := by
  classical
  let N : Zsqrtd (-n) → ℤ := fun z => z.re ^ 2 + n * z.im ^ 2
  have hmul : ∀ x y : Zsqrtd (-n), N (x * y) = N x * N y := by
    intro x y
    rcases x with ⟨a, b⟩
    rcases y with ⟨c, d⟩
    simp [N, pow_two, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]
    ring
  constructor
  · refine ⟨?_, ?_⟩
    · intro h
      rcases (isUnit_iff_exists_inv.mp h) with ⟨u, hu⟩
      rcases u with ⟨a, b⟩
      have hRe := congrArg Zsqrtd.re hu
      simp at hRe
      omega
    · intro x y hxy
      rcases x with ⟨a, b⟩
      rcases y with ⟨c, d⟩
      have hRe0 := congrArg Zsqrtd.re hxy
      have hIm0 := congrArg Zsqrtd.im hxy
      simp at hRe0 hIm0
      have hRe : a * c - n * b * d = 2 := by
        simpa using hRe0.symm
      have hIm : a * d + b * c = 0 := by
        simpa using hIm0.symm
      by_cases hb : b = 0
      · subst hb
        have hRe' : a * c = 2 := by
          simpa using hRe
        have hIm' : a * d = 0 := by
          simpa using hIm
        by_cases hd : d = 0
        · subst hd
          have hc0 : c ≠ 0 := by
            intro hc0
            subst hc0
            simp at hRe'
          have hc2 : 1 ≤ c ^ 2 := by
            have hpos : 0 < c ^ 2 := by positivity
            omega
          have ha2 : a ^ 2 ≤ 4 := by
            have hEq : a ^ 2 * c ^ 2 = 4 := by
              nlinarith [hRe']
            nlinarith [hEq, hc2]
          have haL : -2 ≤ a := by
            nlinarith [ha2, sq_nonneg (a + 2)]
          have haU : a ≤ 2 := by
            nlinarith [ha2, sq_nonneg (a - 2)]
          interval_cases a
          · have hc : c = -1 := by omega
            exact Or.inr (by subst hc; infer_instance)
          · exact Or.inl inferInstance
          · have : False := by
              simp at hRe'
              omega
            exact False.elim this
          · exact Or.inl inferInstance
          · have hc : c = 1 := by omega
            exact Or.inr (by subst hc; infer_instance)
        · have ha0 : a = 0 := by
            have hzero := mul_eq_zero.mp hIm'
            cases hzero with
            | inl ha0 => exact ha0
            | inr hd0 => exact False.elim (hd hd0)
          subst ha0
          have : False := by
            simp at hRe
            omega
          exact False.elim this
      · by_cases hd : d = 0
        · subst hd
          have hIm' : b * c = 0 := by
            simpa using hIm
          have hc0 : c = 0 := by
            have hzero := mul_eq_zero.mp hIm'
            cases hzero with
            | inl hb0 => exact False.elim (hb hb0)
            | inr hc0 => exact hc0
          subst hc0
          have : False := by
            simp at hRe
            omega
          exact False.elim this
        · have hb2 : 1 ≤ b ^ 2 := by
            have hpos : 0 < b ^ 2 := by positivity
            omega
          have hd2 : 1 ≤ d ^ 2 := by
            have hpos : 0 < d ^ 2 := by positivity
            omega
          have hN0 := congrArg N hxy
          simp [N, hmul] at hN0
          have hN : (a ^ 2 + n * b ^ 2) * (c ^ 2 + n * d ^ 2) = 4 := hN0.symm
          have hxge : n ≤ a ^ 2 + n * b ^ 2 := by
            nlinarith [hn0, hb2, sq_nonneg a]
          have hyge : n ≤ c ^ 2 + n * d ^ 2 := by
            nlinarith [hn0, hd2, sq_nonneg c]
          have : False := by
            nlinarith [hN, hxge, hyge, hn0]
          exact False.elim this
  · constructor
    · refine ⟨?_, ?_⟩
      · intro h
        rcases (isUnit_iff_exists_inv.mp h) with ⟨u, hu⟩
        rcases u with ⟨a, b⟩
        have hRe := congrArg Zsqrtd.re hu
        simp at hRe
        omega
      · intro x y hxy
        rcases x with ⟨a, b⟩
        rcases y with ⟨c, d⟩
        have hIm0 := congrArg Zsqrtd.im hxy
        simp at hIm0
        have hIm : a * d + b * c = 1 := by
          simpa using hIm0.symm
        have hN0 := congrArg N hxy
        simp [N, hmul] at hN0
        have hN : (a ^ 2 + n * b ^ 2) * (c ^ 2 + n * d ^ 2) = n := hN0.symm
        by_cases hb : b = 0
        · subst hb
          have hIm' : a * d = 1 := by
            simpa using hIm
          have haDiv : a ∣ 1 := ⟨d, hIm'⟩
          have ha : a = 1 ∨ a = -1 := by
            exact Int.dvd_one.mp haDiv
          rcases ha with rfl | rfl
          · exact Or.inl inferInstance
          · exact Or.inl inferInstance
        · by_cases hd : d = 0
          · subst hd
            have hIm' : b * c = 1 := by
              simpa using hIm
            have hcDiv : c ∣ 1 := ⟨b, by simpa [mul_comm] using hIm'⟩
            have hc : c = 1 ∨ c = -1 := by
              exact Int.dvd_one.mp hcDiv
            rcases hc with rfl | rfl
            · exact Or.inr inferInstance
            · exact Or.inr inferInstance
          · have hb2 : 1 ≤ b ^ 2 := by
              have hpos : 0 < b ^ 2 := by positivity
              omega
            have hd2 : 1 ≤ d ^ 2 := by
              have hpos : 0 < d ^ 2 := by positivity
              omega
            have hxge : n ≤ a ^ 2 + n * b ^ 2 := by
              nlinarith [hn0, hb2, sq_nonneg a]
            have hyge : n ≤ c ^ 2 + n * d ^ 2 := by
              nlinarith [hn0, hd2, sq_nonneg c]
            have : False := by
              nlinarith [hN, hxge, hyge, hn0]
            exact False.elim this
    · constructor
      · refine ⟨?_, ?_⟩
        · intro h
          rcases (isUnit_iff_exists_inv.mp h) with ⟨u, hu⟩
          rcases u with ⟨a, b⟩
          have hRe := congrArg Zsqrtd.re hu
          have hIm := congrArg Zsqrtd.im hu
          simp at hRe hIm
          nlinarith [hn0, hRe, hIm]
        · intro x y hxy
          rcases x with ⟨a, b⟩
          rcases y with ⟨c, d⟩
          have hIm0 := congrArg Zsqrtd.im hxy
          simp at hIm0
          have hIm : a * d + b * c = 1 := by
            simpa using hIm0.symm
          have hN0 := congrArg N hxy
          simp [N, hmul] at hN0
          have hN : (a ^ 2 + n * b ^ 2) * (c ^ 2 + n * d ^ 2) = n + 1 := hN0.symm
          by_cases hb : b = 0
          · subst hb
            have hIm' : a * d = 1 := by
              simpa using hIm
            have haDiv : a ∣ 1 := ⟨d, hIm'⟩
            have ha : a = 1 ∨ a = -1 := by
              exact Int.dvd_one.mp haDiv
            rcases ha with rfl | rfl
            · exact Or.inl inferInstance
            · exact Or.inl inferInstance
          · by_cases hd : d = 0
            · subst hd
              have hIm' : b * c = 1 := by
                simpa using hIm
              have hcDiv : c ∣ 1 := ⟨b, by simpa [mul_comm] using hIm'⟩
              have hc : c = 1 ∨ c = -1 := by
                exact Int.dvd_one.mp hcDiv
              rcases hc with rfl | rfl
              · exact Or.inr inferInstance
              · exact Or.inr inferInstance
            · have hb2 : 1 ≤ b ^ 2 := by
                have hpos : 0 < b ^ 2 := by positivity
                omega
              have hd2 : 1 ≤ d ^ 2 := by
                have hpos : 0 < d ^ 2 := by positivity
                omega
              have hxge : n ≤ a ^ 2 + n * b ^ 2 := by
                nlinarith [hn0, hb2, sq_nonneg a]
              have hyge : n ≤ c ^ 2 + n * d ^ 2 := by
                nlinarith [hn0, hd2, sq_nonneg c]
              have : False := by
                nlinarith [hN, hxge, hyge, hn0]
              exact False.elim this
