import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_2a : Irreducible (X^4 - 4*X^3 + 6 : Polynomial ℤ) := by
  have hE : IsEisenstein (X ^ 4 - 4 * X ^ 3 + 6 : Polynomial ℤ) 2 := by
    refine ⟨by norm_num, ?_, ?_, ?_⟩
    · intro n hn
      interval_cases n <;> norm_num
    · norm_num
    · norm_num
  exact hE.irreducible
