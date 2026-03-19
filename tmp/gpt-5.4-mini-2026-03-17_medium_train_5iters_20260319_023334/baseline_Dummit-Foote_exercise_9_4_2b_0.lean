import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_2b : Irreducible
  (X^6 + 30*X^5 - 15*X^3 + 6*X - 120 : Polynomial ℤ) := by
  have hE : Polynomial.Eisenstein (3 : ℤ) (X ^ 6 + 30 * X ^ 5 - 15 * X ^ 3 + 6 * X - 120) := by
    native_decide
  exact Polynomial.irreducible_of_eisenstein hE
