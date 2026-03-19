import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_1_3 (n : ℕ) : 
  ∀ (x y z : ZMod n), (x + y) + z = x + (y + z) := by
  intro x y z
  exact add_assoc x y z
