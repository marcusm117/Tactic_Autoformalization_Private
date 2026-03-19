import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_1_3a {A : Type*} [CommGroup A] (B : Subgroup A) :
  ∀ a b : A ⧸ B, a*b = b*a := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  simp [mul_comm]
