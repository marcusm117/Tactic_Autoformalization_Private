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
    simp [N, pow_two, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
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
      nlinarith [hz', hn0, hb2, sq_nonneg a]
    subst hb0
    have ha2 : a ^ 2 = 1 := by
      nlinarith [hz']
    have hsq : a * a = 1 := by
      simpa [pow_two] using ha2
    have ha : a = 1 ∨ a = -1 := by
      rcases Int.mul_eq_one_iff.mp hsq with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
    rcases ha with rfl | rfl
    · simpa using (show IsUnit (1 : Zsqrtd (-n)) from inferInstance)
    · simpa using ((show IsUnit (1 : Zsqrtd (-n)) from inferInstance).neg)
  constructor
  · intro h
    rcases (isUnit_iff_exists_inv.mp h) with ⟨u, hu⟩
    have hN := congrArg N hu
    have hN' : 4 * N u = 1 := by
      simpa [N, hmul] using hN
    have hbad := Int.mul_eq_one_iff.mp hN'
    rcases hbad with ⟨h4, _⟩ | ⟨h4, _⟩ <;> omega
  · constructor
    · intro x y hxy
      rcases x with ⟨a, b⟩
      rcases y with ⟨c, d⟩
      have hN : (a ^ 2 + n * b ^ 2) * (c ^ 2 + n * d ^ 2) = 4 := by
        simpa [N, hmul] using congrArg N hxy
      by_cases hb : b = 0
      · subst hb
        have hre : a * c = 2 := by
          simpa using congrArg Zsqrtd.re hxy
        have him : a * d = 0 := by
          simpa using congrArg Zsqrtd.im hxy
        have hc0 : c ≠ 0 := by
          intro hc0
          subst hc0
          simp at hre
        have hc2 : 1 ≤ c ^ 2 := by
          have hpos : 0 < c ^ 2 := by positivity
          omega
        have ha2 : a ^ 2 ≤ 4 := by
          nlinarith [hre, hc2, sq_nonneg a]
        have haL : -2 ≤ a := by
          omega
        have haU : a ≤ 2 := by
          omega
        have haCases : a = -2 ∨ a = -1 ∨ a = 0 ∨ a = 1 ∨ a = 2 := by
          omega
        rcases haCases with rfl | rfl | rfl | rfl | rfl
        · simp at hre
        · exact Or.inl (by simpa using ((show IsUnit (1 : Zsqrtd (-n)) from inferInstance).neg))
        · simp at hre
        · exact Or.inl (by simpa using (show IsUnit (1 : Zsqrtd (-n)) from inferInstance))
        ·
          have hc : c = 1 := by omega
          have hd : d = 0 := by omega
          exact Or.inr (by
            subst hc
            subst hd
            simpa using (show IsUnit (1 : Zsqrtd (-n)) from inferInstance))
      · have hb2 : 1 ≤ b ^ 2 := by
          have hpos : 0 < b ^ 2 := by
            positivity
          omega
        have hNxge : n ≤ a ^ 2 + n * b ^ 2 := by
          nlinarith [hn0, hb2, sq_nonneg a]
        have hNyge : 1 ≤ c ^ 2 + n * d ^ 2 := by
          by_cases hc : c = 0
          · subst hc
            have hdne : d ≠ 0 := by
              intro hd0
              subst hd0
              simp at hxy
            have hd2 : 1 ≤ d ^ 2 := by
              have hpos : 0 < d ^ 2 := by positivity
              omega
            nlinarith [hn0, hd2]
          · have hc2 : 1 ≤ c ^ 2 := by
              have hpos : 0 < c ^ 2 := by positivity
              omega
            nlinarith [hc2]
        have hNxle : a ^ 2 + n * b ^ 2 ≤ n := by
          nlinarith [hN, hNyge]
        have hNxEq : a ^ 2 + n * b ^ 2 = n := le_antisymm hNxle hNxge
        have hNyEq : c ^ 2 + n * d ^ 2 = 1 := by
          nlinarith [hN, hNxEq]
        exact Or.inr (hunit_of_Neq1 hNyEq)
    · constructor
      · intro h
        rcases (isUnit_iff_exists_inv.mp h) with ⟨u, hu⟩
        have hN := congrArg N hu
        have hN' : n * N u = 1 := by
          simpa [N, hmul] using hN
        have hbad := Int.mul_eq_one_iff.mp hN'
        rcases hbad with ⟨hn, _⟩ | ⟨hn, _⟩ <;> omega
      · intro x y hxy
        rcases x with ⟨a, b⟩
        rcases y with ⟨c, d⟩
        have hN : (a ^ 2 + n * b ^ 2) * (c ^ 2 + n * d ^ 2) = n := by
          simpa [N, hmul] using congrArg N hxy
        by_cases hb : b = 0
        · subst hb
          have hre : a * c = 0 := by
            simpa using congrArg Zsqrtd.re hxy
          have him : a * d = 1 := by
            simpa using congrArg Zsqrtd.im hxy
          have hmul1 := Int.mul_eq_one_iff.mp him
          rcases hmul1 with ⟨ha, hd⟩ | ⟨ha, hd⟩
          · exact Or.inl (by simpa [ha, hd] using (show IsUnit (1 : Zsqrtd (-n)) from inferInstance))
          · exact Or.inl (by simpa [ha, hd] using ((show IsUnit (1 : Zsqrtd (-n)) from inferInstance).neg))
        · have hb2 : 1 ≤ b ^ 2 := by
            have hpos : 0 < b ^ 2 := by
              positivity
            omega
          have hNxge : n ≤ a ^ 2 + n * b ^ 2 := by
            nlinarith [hn0, hb2, sq_nonneg a]
          have hNyge : 1 ≤ c ^ 2 + n * d ^ 2 := by
            by_cases hc : c = 0
            · subst hc
              have hdne : d ≠ 0 := by
                intro hd0
                subst hd0
                simp at hxy
              have hd2 : 1 ≤ d ^ 2 := by
                have hpos : 0 < d ^ 2 := by positivity
                omega
              nlinarith [hn0, hd2]
            · have hc2 : 1 ≤ c ^ 2 := by
                have hpos : 0 < c ^ 2 := by positivity
                omega
              nlinarith [hc2]
          have hNxle : a ^ 2 + n * b ^ 2 ≤ n := by
            nlinarith [hN, hNyge]
          have hNxEqOr : a ^ 2 + n * b ^ 2 = n ∨ a ^ 2 + n * b ^ 2 = n + 1 := by
            omega
          rcases hNxEqOr with hNxEq | hNxEq
          · have hbad : n * (c ^ 2 + n * d ^ 2 - 1) = 1 := by
              nlinarith [hN, hNxEq]
            have hbad2 := Int.mul_eq_one_iff.mp hbad
            rcases hbad2 with ⟨hn1, _⟩ | ⟨hn1, _⟩ <;> omega
          · have hNyEq : c ^ 2 + n * d ^ 2 = 1 := by
              nlinarith [hN, hNxEq]
            exact Or.inr (hunit_of_Neq1 hNyEq)
    · intro x y hxy
      rcases x with ⟨a, b⟩
      rcases y with ⟨c, d⟩
      have hN : (a ^ 2 + n * b ^ 2) * (c ^ 2 + n * d ^ 2) = n + 1 := by
        simpa [N, hmul] using congrArg N hxy
      by_cases hb : b = 0
      · subst hb
        have hre : a * c = 1 := by
          simpa using congrArg Zsqrtd.re hxy
        have hmul1 := Int.mul_eq_one_iff.mp hre
        rcases hmul1 with ⟨ha, hc⟩ | ⟨ha, hc⟩
        · exact Or.inl (by simpa [ha, hc] using (show IsUnit (1 : Zsqrtd (-n)) from inferInstance))
        · exact Or.inl (by simpa [ha, hc] using ((show IsUnit (1 : Zsqrtd (-n)) from inferInstance).neg))
      · have hb2 : 1 ≤ b ^ 2 := by
          have hpos : 0 < b ^ 2 := by
            positivity
          omega
        have hNxge : n ≤ a ^ 2 + n * b ^ 2 := by
          nlinarith [hn0, hb2, sq_nonneg a]
        have hNyge : 1 ≤ c ^ 2 + n * d ^ 2 := by
          by_cases hc : c = 0
          · subst hc
            have hdne : d ≠ 0 := by
              intro hd0
              subst hd0
              simp at hxy
            have hd2 : 1 ≤ d ^ 2 := by
              have hpos : 0 < d ^ 2 := by positivity
              omega
            nlinarith [hn0, hd2]
          · have hc2 : 1 ≤ c ^ 2 := by
              have hpos : 0 < c ^ 2 := by positivity
              omega
            nlinarith [hc2]
        have hNxle : a ^ 2 + n * b ^ 2 ≤ n + 1 := by
          nlinarith [hN, hNyge]
        have hNxEqOr : a ^ 2 + n * b ^ 2 = n ∨ a ^ 2 + n * b ^ 2 = n + 1 := by
          omega
        rcases hNxEqOr with hNxEq | hNxEq
        · have hbad : n * (c ^ 2 + n * d ^ 2 - 1) = 1 := by
            nlinarith [hN, hNxEq]
          have hbad2 := Int.mul_eq_one_iff.mp hbad
          rcases hbad2 with ⟨hn1, _⟩ | ⟨hn1, _⟩ <;> omega
        · have hNyEq : c ^ 2 + n * d ^ 2 = 1 := by
            nlinarith [hN, hNxEq]
          exact Or.inr (hunit_of_Neq1 hNyEq)
