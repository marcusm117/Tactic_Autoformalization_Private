import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_6_17 {G : Type*} [Group G] (f : G → G)
  (hf : f = λ g => g⁻¹) :
  (∀ x y : G, f x * f y = f (x*y)) ↔ ∀ x y : G, x*y = y*x := by
  have hf' : ∀ g : G, f g = g⁻¹ := by
    intro g
    rw [hf]
  constructor
  · intro h x y
    calc
      x * y = ((y⁻¹) * (x⁻¹))⁻¹ := by simp
      _ = f (y⁻¹ * x⁻¹) := by rw [hf']
      _ = f (y⁻¹) * f (x⁻¹) := by
        symm
        exact h _ _
      _ = y * x := by
        rw [hf', hf']
        simp
  · intro h x y
    calc
      f x * f y = x⁻¹ * y⁻¹ := by rw [hf', hf']
      _ = y⁻¹ * x⁻¹ := by exact h _ _
      _ = (x * y)⁻¹ := by simp
      _ = f (x * y) := by rw [hf']
