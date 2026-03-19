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
  have hunit_of_Neq1 : ∀ {z : Zsqrtd (-n)}, N z = 1 → IsUnit z := by
    intro z hz
    rcases z with ⟨a, b⟩
    have hz' : a ^ 2 + n * b ^ 2 = 1 := by
      simpa [N] using hz
    have hb0 : b = 0 := by
      by_contra hb0
      have hb2 : 1 ≤ b ^ 2 := by
        have hpos : 0 < b ^ 2 := by positivity
        omega
      nlinarith [hz', hn0, hb2]
    subst hb0
    have ha2 : a ^ 2 = 1 := by
      nlinarith [hz']
    have haL : -1 ≤ a := by
      nlinarith [ha2, sq_nonneg (a + 1)]
    have haU : a ≤ 1 := by
      nlinarith [ha2, sq_nonneg (a - 1)]
    have haCases : a = -1 ∨ a = 0 ∨ a = 1 := by
      omega
    rcases haCases with rfl | rfl | rfl
    · simpa using (isUnit_neg_one : IsUnit (-1 : Zsqrtd (-n)))
    · omega
    · simpa using (isUnit_one : IsUnit (1 : Zsqrtd (-n)))
  constructor
  · refine ⟨?_, ?_⟩
    · intro h
      have hN := congrArg N h
      norm_num [N] at hN
    · intro x y hxy
      by_cases hx : IsUnit x
      · exact Or.inl hx
      · by_cases hy : IsUnit y
        · exact Or.inr hy
        · rcases x with ⟨a, b⟩
          rcases y with ⟨c, d⟩
          have hN : (a ^ 2 + n * b ^ 2) * (c ^ 2 + n * d ^ 2) = 4 := by
            simpa [N, hmul] using congrArg N hxy
          by_cases hb : b = 0
          · subst hb
            have hN' : a ^ 2 * (c ^ 2 + n * d ^ 2) = 4 := by
              simpa [pow_two] using hN
            have hNypos : 1 ≤ c ^ 2 + n * d ^ 2 := by
              by_cases hc : c = 0
              · subst hc
                have hd : d ≠ 0 := by
                  intro hd
                  subst hd
                  simp at hxy
                have hd2 : 1 ≤ d ^ 2 := by
                  have hpos : 0 < d ^ 2 := by positivity
                  omega
                nlinarith [hn0, hd2]
              · have hc2 : 1 ≤ c ^ 2 := by
                  have hpos : 0 < c ^ 2 := by positivity
                  omega
                nlinarith [hc2]
            have haSqLe : a ^ 2 ≤ 4 := by
              nlinarith [hN', hNypos]
            have haL : -2 ≤ a := by
              nlinarith [haSqLe, sq_nonneg (a + 2)]
            have haU : a ≤ 2 := by
              nlinarith [haSqLe, sq_nonneg (a - 2)]
            have haCases : a = -2 ∨ a = -1 ∨ a = 0 ∨ a = 1 ∨ a = 2 := by
              omega
            rcases haCases with rfl | rfl | rfl | rfl | rfl
            · have hNy : c ^ 2 + n * d ^ 2 = 1 := by
                nlinarith [hN']
              exact hy (hunit_of_Neq1 hNy)
            · exact hx (by simpa using (isUnit_neg_one : IsUnit (-1 : Zsqrtd (-n))))
            · omega
            · exact hx (by simpa using (isUnit_one : IsUnit (1 : Zsqrtd (-n))))
            · have hNy : c ^ 2 + n * d ^ 2 = 1 := by
                nlinarith [hN']
              exact hy (hunit_of_Neq1 hNy)
          · have hb2 : 1 ≤ b ^ 2 := by
              have hpos : 0 < b ^ 2 := by
                positivity
              omega
            have hNxge : n + 1 ≤ a ^ 2 + n * b ^ 2 := by
              nlinarith [hn0, hb2, sq_nonneg a]
            have hNypos : 1 ≤ c ^ 2 + n * d ^ 2 := by
              by_cases hc : c = 0
              · subst hc
                have hd : d ≠ 0 := by
                  intro hd
                  subst hd
                  simp at hxy
                have hd2 : 1 ≤ d ^ 2 := by
                  have hpos : 0 < d ^ 2 := by positivity
                  omega
                nlinarith [hn0, hd2]
              · have hc2 : 1 ≤ c ^ 2 := by
                  have hpos : 0 < c ^ 2 := by positivity
                  omega
                nlinarith [hc2]
            have : False := by
              nlinarith [hN, hNxge, hNypos, hn0]
            exact False.elim this
  · constructor
    · refine ⟨?_, ?_⟩
      · intro h
        have hN := congrArg N h
        norm_num [N] at hN
      · intro x y hxy
        by_cases hx : IsUnit x
        · exact Or.inl hx
        · by_cases hy : IsUnit y
          · exact Or.inr hy
          · rcases x with ⟨a, b⟩
            rcases y with ⟨c, d⟩
            have hN : (a ^ 2 + n * b ^ 2) * (c ^ 2 + n * d ^ 2) = n := by
              simpa [N, hmul] using congrArg N hxy
            by_cases hb : b = 0
            · subst hb
              have hA : a * d = 1 := by
                simpa using congrArg Zsqrtd.im hxy
              have hxunit : IsUnit x := by
                refine ⟨⟨d, 0⟩, ?_⟩
                ext <;> simp [hA]
              exact (hx hxunit).elim
            · have hb2 : 1 ≤ b ^ 2 := by
                have hpos : 0 < b ^ 2 := by
                  positivity
                omega
              have hNxge : n + 1 ≤ a ^ 2 + n * b ^ 2 := by
                nlinarith [hn0, hb2, sq_nonneg a]
              have hNypos : 1 ≤ c ^ 2 + n * d ^ 2 := by
                by_cases hc : c = 0
                · subst hc
                  have hd : d ≠ 0 := by
                    intro hd
                    subst hd
                    simp at hxy
                  have hd2 : 1 ≤ d ^ 2 := by
                    have hpos : 0 < d ^ 2 := by positivity
                    omega
                  nlinarith [hn0, hd2]
                · have hc2 : 1 ≤ c ^ 2 := by
                    have hpos : 0 < c ^ 2 := by positivity
                    omega
                  nlinarith [hc2]
              have : False := by
                nlinarith [hN, hNxge, hNypos, hn0]
              exact False.elim this
    · constructor
      · refine ⟨?_, ?_⟩
        · intro h
          have hN := congrArg N h
          norm_num [N] at hN
        · intro x y hxy
          by_cases hx : IsUnit x
          · exact Or.inl hx
          · by_cases hy : IsUnit y
            · exact Or.inr hy
            · rcases x with ⟨a, b⟩
              rcases y with ⟨c, d⟩
              have hN : (a ^ 2 + n * b ^ 2) * (c ^ 2 + n * d ^ 2) = n + 1 := by
                simpa [N, hmul] using congrArg N hxy
              by_cases hb : b = 0
              · subst hb
                have hA : a * c = 1 := by
                  simpa using congrArg Zsqrtd.re hxy
                have hxunit : IsUnit x := by
                  refine ⟨⟨c, 0⟩, ?_⟩
                  ext <;> simp [hA]
                exact (hx hxunit).elim
              · have hb2 : 1 ≤ b ^ 2 := by
                  have hpos : 0 < b ^ 2 := by
                    positivity
                  omega
                have hNxge : n + 1 ≤ a ^ 2 + n * b ^ 2 := by
                  nlinarith [hn0, hb2, sq_nonneg a]
                have hNypos : 1 ≤ c ^ 2 + n * d ^ 2 := by
                  by_cases hc : c = 0
                  · subst hc
                    have hd : d ≠ 0 := by
                      intro hd
                      subst hd
                      simp at hxy
                    have hd2 : 1 ≤ d ^ 2 := by
                      have hpos : 0 < d ^ 2 := by positivity
                      omega
                    nlinarith [hn0, hd2]
                  · have hc2 : 1 ≤ c ^ 2 := by
                      have hpos : 0 < c ^ 2 := by positivity
                      omega
                    nlinarith [hc2]
                have hNyle : c ^ 2 + n * d ^ 2 ≤ 1 := by
                  nlinarith [hN, hNxge, hn0]
                have hNyEq : c ^ 2 + n * d ^ 2 = 1 := le_antisymm hNyle hNypos
                exact hy (hunit_of_Neq1 hNyEq)
