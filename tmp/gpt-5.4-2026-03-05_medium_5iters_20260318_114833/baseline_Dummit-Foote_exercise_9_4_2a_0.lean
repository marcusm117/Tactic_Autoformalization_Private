import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_2a : Irreducible (X^4 - 4*X^3 + 6 : Polynomial ℤ) := by
  have hdeg : (X ^ 4 - 4 * X ^ 3 + 6 : Polynomial ℤ).natDegree = 4 := by
    native_decide
  refine Polynomial.irreducible_of_eisenstein_criterion
    (f := (X ^ 4 - 4 * X ^ 3 + 6 : Polynomial ℤ)) (p := (2 : ℤ)) ?_ ?_ ?_ ?_
  · norm_num
  · native_decide
  · intro n hn
    have hn' : n < 4 := by simpa [hdeg] using hn
    interval_cases n <;> native_decide
  · native_decide
