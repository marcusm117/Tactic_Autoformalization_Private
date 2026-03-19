import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_4_1b :
  Irreducible (12 + 6 * X + X ^ 3 : Polynomial ℚ) := by
  have hZ : Irreducible (12 + 6 * X + X ^ 3 : Polynomial ℤ) := by
    apply irreducible_of_eisenstein
    refine ⟨by norm_num, ?_, ?_, ?_⟩
    · intro n hn
      fin_cases n <;> norm_num
    · norm_num
    · norm_num
  simpa using hZ.map (Int.castRingHom ℚ) Int.cast_injective
