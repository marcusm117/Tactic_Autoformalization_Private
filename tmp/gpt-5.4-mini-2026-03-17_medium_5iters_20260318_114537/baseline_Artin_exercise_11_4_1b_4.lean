import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_4_1b :
  Irreducible (12 + 6 * X + X ^ 3 : Polynomial ℚ) := by
  have hE : (12 + 6 * X + X ^ 3 : Polynomial ℤ).IsEisensteinAt 3 := by
    refine ⟨by norm_num, ?_, ?_, ?_⟩
    · intro h
      norm_num at h
    · intro n hn
      fin_cases n <;> norm_num at hn ⊢
    · norm_num
  have hprim : (12 + 6 * X + X ^ 3 : Polynomial ℤ).IsPrimitive := by
    have hm : Monic (12 + 6 * X + X ^ 3 : Polynomial ℤ) := by
      simp
    exact hm.isPrimitive
  have hdeg : 0 < (12 + 6 * X + X ^ 3 : Polynomial ℤ).natDegree := by
    norm_num
  have hZ : Irreducible (12 + 6 * X + X ^ 3 : Polynomial ℤ) :=
    hE.irreducible (by norm_num) hprim hdeg
  simpa using hZ.map (Int.castRingHom ℚ)
