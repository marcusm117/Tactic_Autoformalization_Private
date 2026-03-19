import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_4_1b :
  Irreducible (12 + 6 * X + X ^ 3 : Polynomial ℚ) := by
  have hE : Polynomial.IsEisensteinAt (12 + 6 * X + X ^ 3 : Polynomial ℤ) 3 := by
    refine ⟨by norm_num, ?_, ?_, ?_⟩
    · intro n hn
      fin_cases n <;> norm_num at hn ⊢
    · norm_num
    · norm_num
  simpa using hE.irreducible.map (Int.castRingHom ℚ)
