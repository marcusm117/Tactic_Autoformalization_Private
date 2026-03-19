import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_1_22b {G: Type*} [Group G] (a b : G) :
  orderOf (a * b) = orderOf (b * a) := by
  have h : IsConj (a * b) (b * a) := by
    refine ⟨a⁻¹, ?_⟩
    simp [mul_assoc]
  exact h.orderOf_eq
