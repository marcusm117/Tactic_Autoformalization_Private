import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_1_18 {G : Type*} [Group G]
  (x y : G) : (x * y = y * x ↔ y⁻¹ * x * y = x) ∧ (y⁻¹ * x * y = x ↔ x⁻¹ * y⁻¹ * x * y = 1) := by
  constructor
  · constructor
    · intro h
      calc
        y⁻¹ * x * y = y⁻¹ * (x * y) := by simp [mul_assoc]
        _ = y⁻¹ * (y * x) := by rw [h]
        _ = x := by simp [mul_assoc]
    · intro h
      have h' := congrArg (fun z => y * z) h
      simpa [mul_assoc] using h'
  · constructor
    · intro h
      have h' := congrArg (fun z => x⁻¹ * z) h
      simpa [mul_assoc] using h'
    · intro h
      have h' := congrArg (fun z => x * z) h
      simpa [mul_assoc] using h'
