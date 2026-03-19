import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_2a : Irreducible (X^4 - 4*X^3 + 6 : Polynomial ℤ) := by
  have hE : Polynomial.Eisenstein (p := (2 : ℤ)) (f := (X ^ 4 - 4 * X ^ 3 + 6 : Polynomial ℤ)) := by
    constructor <;> try (simp | norm_num)
    · intro n hn
      interval_cases n <;> norm_num
  exact hE.irreducible
