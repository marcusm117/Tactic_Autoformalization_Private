import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_8_3_4 {n : ℤ} {r s : ℚ}
  (h : r^2 + s^2 = n) :
  ∃ a b : ℤ, a^2 + b^2 = n := by
  simpa using Int.exists_sq_add_sq_of_rat_sq_add_sq h
