import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_2a : Irreducible (X^4 - 4*X^3 + 6 : Polynomial ℤ) := by
  have hq : Irreducible (X ^ 4 - 6 * X ^ 2 - 8 * X + 3 : Polynomial ℤ) := by
    apply irreducible_of_eisenstein (p := 2)
    · norm_num
    · intro n hn
      interval_cases n <;> norm_num
    · norm_num
    · norm_num
  simpa using (irreducible_comp_X_add_C (f := X ^ 4 - 6 * X ^ 2 - 8 * X + 3) (a := (-1 : ℤ)) hq)
