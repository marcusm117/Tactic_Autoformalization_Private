import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_2c : Irreducible
  (X^4 + 4*X^3 + 6*X^2 + 2*X + 1 : Polynomial ℤ) := by
  have h : Irreducible ((X^4 - 2 * X + 2 : Polynomial ℤ)) := by
    apply Polynomial.irreducible_of_eisenstein (p := 2)
    · norm_num
    · intro n hn
      interval_cases n <;> norm_num
    · norm_num
    · norm_num
  simpa using h.comp_X_add_C (1 : ℤ)
