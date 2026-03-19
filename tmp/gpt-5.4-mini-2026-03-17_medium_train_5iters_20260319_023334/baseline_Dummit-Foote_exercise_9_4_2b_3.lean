import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_2b : Irreducible
  (X^6 + 30*X^5 - 15*X^3 + 6*X - 120 : Polynomial ℤ) := by
  have hE : Polynomial.IsEisenstein (3 : ℤ) (X ^ 6 + 30 * X ^ 5 - 15 * X ^ 3 + 6 * X - 120 : Polynomial ℤ) := by
    native_decide
  simpa using hE.irreducible
