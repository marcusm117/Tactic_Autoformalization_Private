import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_1_22a {G : Type*} [Group G] (x g : G) :
  orderOf x = orderOf (g⁻¹ * x * g) := by
  let e : G ≃* G :=
  { toFun := fun a => g⁻¹ * a * g
    invFun := fun a => g * a * g⁻¹
    left_inv := by
      intro a
      simp [mul_assoc]
    right_inv := by
      intro a
      simp [mul_assoc]
    map_mul' := by
      intro a b
      simp [mul_assoc] }
  have h1 : orderOf x ∣ orderOf (e x) := by
    simpa using (e.symm.map_orderOf (e x))
  have h2 : orderOf (e x) ∣ orderOf x := by
    simpa using (e.map_orderOf x)
  exact Nat.dvd_antisymm h1 h2
