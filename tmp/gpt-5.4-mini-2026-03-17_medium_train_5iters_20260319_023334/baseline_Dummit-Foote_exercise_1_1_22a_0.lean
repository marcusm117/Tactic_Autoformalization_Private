import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_1_22a {G : Type*} [Group G] (x g : G) :
  orderOf x = orderOf (g⁻¹ * x * g) := by
  simpa [mul_assoc] using (orderOf_conj (g⁻¹) x)
