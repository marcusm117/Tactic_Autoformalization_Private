import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_6_11 {A B : Type*} [Group A] [Group B] :
  Nonempty (A × B ≃* B × A) := by
  refine ⟨
    { toFun := Prod.swap
      invFun := Prod.swap
      left_inv := by
        intro x
        cases x <;> rfl
      right_inv := by
        intro x
        cases x <;> rfl
      map_mul' := by
        intro x y
        cases x <;> cases y <;> rfl }⟩
