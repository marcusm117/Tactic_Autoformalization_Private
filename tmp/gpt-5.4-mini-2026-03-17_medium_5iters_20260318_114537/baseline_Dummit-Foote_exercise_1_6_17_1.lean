import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_6_17 {G : Type*} [Group G] (f : G → G)
  (hf : f = λ g => g⁻¹) :
  (∀ x y : G, f x * f y = f (x*y)) ↔ ∀ x y : G, x*y = y*x := by
  constructor
  · intro h x y
    rw [hf]
    calc
      x⁻¹ * y⁻¹ = y⁻¹ * x⁻¹ := by rw [h]
      _ = (x * y)⁻¹ := by rw [← mul_inv_rev]
  · intro h x y
    have hxy : x⁻¹ * y⁻¹ = (x * y)⁻¹ := by
      simpa [hf] using h x y
    have hxy' := congrArg (fun z : G => z⁻¹) hxy
    simpa [mul_inv_rev] using hxy'.symm
