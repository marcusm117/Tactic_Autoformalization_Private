import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_2a : Irreducible (X^4 - 4*X^3 + 6 : Polynomial ℤ) := by
  have hq : Irreducible (X ^ 4 + 4 * X ^ 3 - 16 * X - 10 : Polynomial ℤ) := by
    have hE : (X ^ 4 + 4 * X ^ 3 - 16 * X - 10 : Polynomial ℤ).IsEisenstein 2 := by
      refine ⟨by norm_num, ?_, ?_, ?_⟩
      · intro n hn
        interval_cases n <;> norm_num
      · norm_num
      · norm_num
    exact Polynomial.IsEisenstein.irreducible hE
  simpa using
    (Polynomial.irreducible_comp_X_add_C (f := X ^ 4 + 4 * X ^ 3 - 16 * X - 10) (a := (-2 : ℤ)) hq)
