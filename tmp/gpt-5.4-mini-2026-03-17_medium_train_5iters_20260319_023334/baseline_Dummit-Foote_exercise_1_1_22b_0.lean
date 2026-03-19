import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_1_22b {G: Type*} [Group G] (a b : G) :
  orderOf (a * b) = orderOf (b * a) := by simpa [mul_assoc] using (orderOf_conj (a⁻¹) (a * b)).symm
