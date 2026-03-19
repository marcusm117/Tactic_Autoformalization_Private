import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_1_2a : ∃ a b : ℤ, a - b ≠ b - a := by
  refine ⟨1, -1, ?_⟩
  norm_num
