import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_8_3_5a {n : ℤ} (hn0 : n > 3) (hn1 : Squarefree n) :
  Irreducible (2 : Zsqrtd $ -n) ∧
  Irreducible (⟨0, 1⟩ : Zsqrtd $ -n) ∧
  Irreducible (1 + ⟨0, 1⟩ : Zsqrtd $ -n) := by
  constructor
  · refine ⟨?_, ?_⟩
    · intro h
      have hnorm := (Zsqrtd.isUnit_iff_normSq_eq_one.mp h)
      norm_num at hnorm
    · intro x y hxy
      rcases x with ⟨a, b⟩
      rcases y with ⟨c, d⟩
      have hnorm : (a ^ 2 + n * b ^ 2) * (c ^ 2 + n * d ^ 2) = 4 := by
        have := congrArg Zsqrtd.normSq hxy
        simp [Zsqrtd.normSq, pow_two, mul_comm, mul_left_comm, mul_assoc] at this
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using this
      by_cases hb : b = 0
      · subst hb
        have hnorm' : a ^ 2 * (c ^ 2 + n * d ^ 2) = 4 := by
          simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hnorm
        have hypos : 1 ≤ c ^ 2 + n * d ^ 2 := by
          positivity
        have ha2le : a ^ 2 ≤ 4 := by
          nlinarith
        interval_cases a <;> simp [pow_two] at hnorm' <;> try
          (first
            | exact Or.inl (by
                refine (Zsqrtd.isUnit_iff_normSq_eq_one).2 ?_
                norm_num [Zsqrtd.normSq])
            | exact Or.inr (by
                refine (Zsqrtd.isUnit_iff_normSq_eq_one).2 ?_
                norm_num [Zsqrtd.normSq])
            | omega)
      · have hb2 : 1 ≤ b ^ 2 := by
          have hpos : 0 < b ^ 2 := by
            positivity
          omega
        have hge : 4 ≤ a ^ 2 + n * b ^ 2 := by
          nlinarith [sq_nonneg a, hn0, hb2]
        have hle : a ^ 2 + n * b ^ 2 ≤ 4 := by
          have hypos : 1 ≤ c ^ 2 + n * d ^ 2 := by
            positivity
          nlinarith
        have hEq : a ^ 2 + n * b ^ 2 = 4 := le_antisymm hle hge
        have hyEq : c ^ 2 + n * d ^ 2 = 1 := by
          nlinarith [hnorm, hEq]
        exact Or.inr (Zsqrtd.isUnit_iff_normSq_eq_one.mpr hyEq)
  · constructor
    · refine ⟨?_, ?_⟩
      · intro h
        have hnorm := (Zsqrtd.isUnit_iff_normSq_eq_one.mp h)
        norm_num at hnorm
      · intro x y hxy
        rcases x with ⟨a, b⟩
        rcases y with ⟨c, d⟩
        have hnorm : (a ^ 2 + n * b ^ 2) * (c ^ 2 + n * d ^ 2) = n := by
          have := congrArg Zsqrtd.normSq hxy
          simp [Zsqrtd.normSq, pow_two, mul_comm, mul_left_comm, mul_assoc] at this
          simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using this
        by_cases hb : b = 0
        · subst hb
          have hxy' := hxy
          simp [pow_two] at hxy'
          rcases hxy' with ⟨h1, h2⟩
          exact Or.inl (by
            refine ⟨⟨d, 0⟩, ?_⟩ <;> ext <;> simp [h2, h1])
        · have hb2 : 1 ≤ b ^ 2 := by
            have hpos : 0 < b ^ 2 := by
              positivity
            omega
          have hge : n ≤ a ^ 2 + n * b ^ 2 := by
            nlinarith [sq_nonneg a, hn0, hb2]
          have hle : a ^ 2 + n * b ^ 2 ≤ n := by
            have hypos : 1 ≤ c ^ 2 + n * d ^ 2 := by
              positivity
            nlinarith
          have hEq : a ^ 2 + n * b ^ 2 = n := le_antisymm hle hge
          have hyEq : c ^ 2 + n * d ^ 2 = 1 := by
            nlinarith [hnorm, hEq]
          exact Or.inr (Zsqrtd.isUnit_iff_normSq_eq_one.mpr hyEq)
    · refine ⟨?_, ?_⟩
      · intro h
        have hnorm := (Zsqrtd.isUnit_iff_normSq_eq_one.mp h)
        norm_num at hnorm
      · intro x y hxy
        rcases x with ⟨a, b⟩
        rcases y with ⟨c, d⟩
        have hnorm : (a ^ 2 + n * b ^ 2) * (c ^ 2 + n * d ^ 2) = n + 1 := by
          have := congrArg Zsqrtd.normSq hxy
          simp [Zsqrtd.normSq, pow_two, mul_comm, mul_left_comm, mul_assoc] at this
          simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using this
        by_cases hb : b = 0
        · subst hb
          have hxy' := hxy
          simp [pow_two] at hxy'
          rcases hxy' with ⟨h1, h2⟩
          exact Or.inl (by
            refine ⟨⟨d, 0⟩, ?_⟩ <;> ext <;> simp [h2, h1])
        · have hb2 : 1 ≤ b ^ 2 := by
            have hpos : 0 < b ^ 2 := by
              positivity
            omega
          have hge : n ≤ a ^ 2 + n * b ^ 2 := by
            nlinarith [sq_nonneg a, hn0, hb2]
          have hle : a ^ 2 + n * b ^ 2 ≤ n + 1 := by
            have hypos : 1 ≤ c ^ 2 + n * d ^ 2 := by
              positivity
            nlinarith
          have hEq : a ^ 2 + n * b ^ 2 = n + 1 := by
            by_cases hEqn : a ^ 2 + n * b ^ 2 = n
            · exfalso
              have : n ∣ n + 1 := by
                refine ⟨c ^ 2 + n * d ^ 2, ?_⟩
                simpa [hEqn] using hnorm
              omega
            · omega
          have hyEq : c ^ 2 + n * d ^ 2 = 1 := by
            nlinarith [hnorm, hEq]
          exact Or.inr (Zsqrtd.isUnit_iff_normSq_eq_one.mpr hyEq)
