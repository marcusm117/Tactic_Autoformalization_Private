import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_2_4_19 {G : Type*} [Group G] {x : G}
  (hx : orderOf x = 2) (hx1 : ∀ y, orderOf y = 2 → y = x) :
  x ∈ center G := by
  change ∀ y : G, y * x = x * y
  intro y
  have horder : orderOf (y⁻¹ * x * y) = 2 := by
    simpa [hx] using (orderOf_conj (y⁻¹) x)
  have hxy : y⁻¹ * x * y = x := hx1 _ horder
  calc
    y * x = y * (y⁻¹ * x * y) := by rw [hxy]
    _ = x * y := by simp [mul_assoc]
