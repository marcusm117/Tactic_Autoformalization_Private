import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_1_18 {G : Type*} [Group G]
  (x y : G) : (x * y = y * x ↔ y⁻¹ * x * y = x) ∧ (y⁻¹ * x * y = x ↔ x⁻¹ * y⁻¹ * x * y = 1) := by
  constructor
  · constructor
    · intro h
      have := congrArg (fun z => y⁻¹ * z) h
      simpa [mul_assoc] using this
    · intro h
      have := congrArg (fun z => y * z) h
      simpa [mul_assoc] using this
  · constructor
    · intro h
      have := congrArg (fun z => x⁻¹ * z) h
      simpa [mul_assoc] using this
    · intro h
      have := congrArg (fun z => x * z) h
      simpa [mul_assoc] using this
